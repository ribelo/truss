(ns taoensso.truss.impl
  "Private implementation details."
  (:require
   [clojure.set :as set]
   [meander.epsilon :as m]
   [meander.strategy.epsilon :as m*])
  (:refer-clojure :exclude [some?])
  #?(:cljs
     (:require-macros
      [taoensso.truss.impl :as impl-macros
       :refer [compile-if catching -invar]])))

(comment (require '[taoensso.encore :as enc :refer [qb]]))

;;;; TODO
;; - Namespaced kw registry like clojure.spec, (truss/def <kw> <pred>)?
;; - Ideas for easier sharing of composed preds?

;;;; Manual Encore imports
;; A bit of a nuisance but:
;;   - Allows Encore to depend on Truss (esp. nb for back-compatibility wrappers).
;;   - Allows Truss to be entirely dependency free.

(def registry-ref (atom {}))

(defmacro if-cljs [then else] (if (:ns &env) then else))
(defmacro compile-if [test then else]
  (if (try (eval test) (catch Throwable _ false)) `(do ~then) `(do ~else)))

(defmacro catching "Cross-platform try/catch/finally."
  ;; We badly need something like http://dev.clojure.org/jira/browse/CLJ-1293
  ;; TODO js/Error instead of :default as temp workaround for http://goo.gl/UW7773
  ([try-expr                     ] `(catching ~try-expr ~'_ nil))
  ([try-expr error-sym catch-expr]
   `(if-cljs
      (try ~try-expr (catch js/Error  ~error-sym ~catch-expr))
      (try ~try-expr (catch Throwable ~error-sym ~catch-expr))))
  ([try-expr error-sym catch-expr finally-expr]
   `(if-cljs
      (try ~try-expr (catch js/Error  ~error-sym ~catch-expr) (finally ~finally-expr))
      (try ~try-expr (catch Throwable ~error-sym ~catch-expr) (finally ~finally-expr)))))

(defn rsome   [pred coll]       (reduce (fn [acc in] (when-let [p (pred in)] (reduced p))) nil coll))
(defn revery? [pred coll]       (reduce (fn [acc in] (if (pred in) true (reduced nil))) true coll))
(defn revery  [pred coll] (when (reduce (fn [acc in] (if (pred in) true (reduced nil))) true coll) coll))

(comment (revery integer? [1 2 3]) (revery integer? nil))

#?(:cljs (defn ^boolean some? [x] (if (nil? x) false true))
   :clj
   (defn some?
     {:inline (fn [x] `(if (identical? ~x nil) false true))}
     [x] (if (identical? x nil) false true)))

;;;; Truss

(defn default-error-fn [data_]
  (let [data @data_]
    (throw (ex-info @(:msg_ data) (dissoc data :msg_)))))

(def ^:dynamic *?data* nil)
(def ^:dynamic *error-fn* default-error-fn)

(def rewrite-spec
  (m*/fix
   (m*/bottom-up
    (m*/attempt
     (m*/match
       (m/and (m/keyword (m/some ?ns) _ :as ?k)
              (m/some (m/guard (@registry-ref ?k))))
       (@registry-ref ?k))))))

(defmacro ->meander [v spec]
  `(m/match ~v
     ~(rewrite-spec spec) true
     ~'_    false))

(defn- fmt-err-msg [x1 x2 x3 x4]
  ;; Cider unfortunately doesn't seem to print newlines in errors
  (str "Invariant violation in `" x1 ":" x2 "`. Test form `" x3 "` failed against input val `" x4 "`."))

#?(:clj
   (defn- fast-pr-str
     "Combination `with-out-str`, `pr`. Ignores *print-dup*."
     [x]
     (let [w (java.io.StringWriter.)]
       (print-method x w)
       (.toString      w))))

(comment (enc/qb 1e5 (pr-str {:a :A}) (fast-pr-str {:a :A})))

(deftype WrappedError [val])
(defn -assertion-error [msg] #?(:clj (AssertionError. msg) :cljs (js/Error. msg)))
(def  -dummy-error #?(:clj (Object.) :cljs (js-obj)))
(defn -invar-violation!
  ;; - http://dev.clojure.org/jira/browse/CLJ-865 would be handy for line numbers.
  [elidable? ns-str ?line form val ?err ?data-fn]
  (when-let [error-fn *error-fn*]
    (error-fn ; Nb consumer must deref while bindings are still active
     (delay
      (let [instant     #?(:clj (java.util.Date.) :cljs (js/Date.))
            line-str    (or ?line "?")
            form-str    (str form)
            undefn-val? (instance? WrappedError val)
            val-str
            (cond
              undefn-val? "<truss/undefined-val>"
              (nil? val)  "<truss/nil>"
              :else
              #_(str    val)
              #_(pr-str val)
              ;; Consider setting *print-length* for lazy seqs?
              #?(:clj  (fast-pr-str val)
                 :cljs (pr-str      val)))

            ?err
            (cond
              (identical? -dummy-error ?err) nil
              (instance?  WrappedError ?err)
              (.-val     ^WrappedError ?err)
              :else                    ?err)

            msg_
            (delay
             (let [;; Clj 1.7+ `pr-str` dumps a ton of error info that we don't want here
                   ?err-str (when-let [e ?err] (str ?err) #_(pr-str ?err))
                   msg (fmt-err-msg ns-str line-str form-str val-str)]
               (cond
                 (not ?err)       msg
                 undefn-val? (str msg " An error was thrown while evaluating input val: [" ?err-str "].")
                 :else       (str msg " An error was thrown while evaluating test form: [" ?err-str "]."))))

            ?data
            (when-let [data-fn ?data-fn]
              (catching (data-fn) e
                {:data-error e}))]

        {:dt        instant
         :msg_      msg_
         :ns-str    ns-str
         :?line     ?line
         ;; :?form  (when-not (string? form) form)
         :form-str  form-str
         :val       (if undefn-val? 'truss/undefined-val       val)
         :val-type  (if undefn-val? 'truss/undefined-val (type val))
         :?data      ?data  ; Arbitrary user data, handy for debugging
         :*?data*   *?data* ; ''
         :?err      ?err
         :*assert*  *assert*
         :elidable? elidable?})))))

(defmacro -invar
  "Written to maximize performance + minimize post Closure+gzip Cljs code size."
  [elidable? truthy? line pred x ?data-fn]
  (let [form #_(list pred x) (str (list pred x))
        non-throwing-x? (not (list? x)) ]
    (if non-throwing-x? ; Common case
      `(let [~'e (catching (if (->meander ~x ~pred) nil -dummy-error) ~'e ~'e)]
         (if (nil? ~'e)
           ~(if truthy? true x)
           (-invar-violation! ~elidable? ~(str *ns*) ~line ~form ~x ~'e ~?data-fn)))

      `(let [~'z (catching ~x ~'e (WrappedError. ~'e))
             ~'e (catching
                   (if (instance? WrappedError ~'z)
                     ~'z
                     (if (->meander ~'z ~pred) nil -dummy-error)) ~'e ~'e)]

         (if (nil? ~'e)
           ~(if truthy? true 'z)
           (-invar-violation! ~elidable? ~(str *ns*) ~line ~form ~'z ~'e ~?data-fn))))))

(comment
  (macroexpand '(-invar true false 1      string?    "foo"             nil)) ; Type 0
  (macroexpand '(-invar true false 1 [:or string?]   "foo"             nil)) ; Type 0
  (macroexpand '(-invar true false 1    #(string? %) "foo"             nil)) ; Type 1
  (macroexpand '(-invar true false 1      string?    (str "foo" "bar") nil)) ; Type 2
  (macroexpand '(-invar true false 1    #(string? %) (str "foo" "bar") nil)) ; Type 3
  (qb 1000000
      (string? "foo")                                                    ; Baseline
      (-invar true false 1  (m/pred string?)      "foo"             nil) ; Type 0
      (-invar true false 1  (m/pred #(string? %)) "foo"             nil) ; Type 1
      (-invar true false 1  (m/pred string?)      (str "foo" "bar") nil) ; Type 2
      (-invar true false 1  (m/pred #(string? %)) (str "foo" "bar") nil) ; Type 3
      (try
        (string? (try "foo" (catch Throwable _ nil)))
        (catch Throwable _ nil)))
  ;; [41.86 50.43 59.56 171.12 151.2 42.0]

  (-invar false false 1 (m/pred integer?) "foo"   nil) ; Pred failure example
  (-invar false false 1 (m/pred zero?)    "foo"   nil) ; Pred error example
  (-invar false false 1 (m/pred zero?)    (/ 5 0) nil) ; Form error example
  )

(defmacro -invariant [elidable? truthy? line & args]
  (let [elide?     (and elidable? (not *assert*))
        in?        (= (second args) :in) ; (have pred :in xs1 xs2 ...)
        args       (if in? (cons (first args) (nnext args)) args)

        data?      (and (> (count args) 2) ; Distinguish from `:data` pred
                        (= (last (butlast args)) :data))
        ?data-fn   (when data? `(fn [] ~(last args)))
        args       (if data? (butlast (butlast args)) args)

        auto-pred? (= (count args) 1)   ; Unique common case: (have ?x)
        pred       (if auto-pred? '(m/some) (first args))
        [?x1 ?xs]  (if auto-pred?
                     [(first args) nil]
                     (if (nnext args) [nil (next args)] [(second args) nil]))
        single-x?  (nil? ?xs)
        in-fn
        `(fn [~'__in]                    ; Will (necessarily) lose exact form
           (-invar ~elidable? ~truthy? ~line ~pred ~'__in ~?data-fn))]

    (if elide?
      (if truthy?
        true
        (if single-x? ?x1 (vec ?xs)))

      (if-not in?

        (if single-x?
          ;; (have pred x) -> x
          `(-invar ~elidable? ~truthy? ~line ~pred ~?x1 ~?data-fn)

          ;; (have pred x1 x2 ...) -> [x1 x2 ...]
          (if truthy?
            `(do ~@(mapv (fn [x] `(-invar ~elidable? ~truthy? ~line ~pred ~x ~?data-fn)) ?xs) true)
            (do    (mapv (fn [x] `(-invar ~elidable? ~truthy? ~line ~pred ~x ~?data-fn)) ?xs))))

        (if single-x?

          ;; (have? pred :in xs) -> bool
          ;; (have  pred :in xs) -> xs
          (if truthy?
            `(m/match ~?x1 (m/seqable (m/pred ~in-fn) ... :as ~'?x) true '_ false)
            `(m/match ~?x1 (m/seqable (m/pred ~in-fn) ... :as ~'?x) ~'?x '_ false))

          ;; (have? pred :in xs1 xs2 ...) -> [bool1 ...]
          ;; (have  pred :in xs1 xs2 ...) -> [xs1   ...]
          (if truthy?
            `(do ~@(mapv (fn [xs] `(taoensso.truss.impl/revery? ~in-fn ~xs)) ?xs) true)
            (do    (mapv (fn [xs] `(taoensso.truss.impl/revery  ~in-fn ~xs)) ?xs))))))))
