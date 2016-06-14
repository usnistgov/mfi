(ns gov.nist.mfi
  (:require [clojure.pprint :refer (cl-format pprint)]
            [clojure.string :as str]
            [edn-ld.core :refer :all] 
            [edn-ld.common :refer :all]
            [edn-ld.jena :refer :all])
  (:import (java.io StringReader StringWriter)
           (com.hp.hpl.jena.graph Node_URI Node_Blank Node_Literal) ; Triple 
           (com.hp.hpl.jena.sparql.core Quad)
           (org.apache.jena.riot.system StreamRDF)
           (com.hp.hpl.jena.rdf.model ModelFactory AnonId)
           (com.hp.hpl.jena.query DatasetFactory)
           (com.hp.hpl.jena.datatypes BaseDatatype)
           (org.apache.jena.riot RDFDataMgr RDFLanguages))) ;  Lang

(use 'clojure.repl)      ; POD Temporary. For use of doc.
(use 'clojure.inspector) ; POD Temporary

;;; Purpose: Parse latex mathematical expressions into OWL statements.

;;; ToDo:
;;;          - It may be that I'll need a stack to save variables, rather than just a atomic element on the map. 
;;;          - Write owl axioms for relations.
;;;          - Write results to in-memory jena.
;;;          - Write SPARQL to recover mathematical expressions.

(def ^:private +debug+ (atom nil))
(defrecord MathExp [content])

(defmacro ^:private defparse [tag [pstate & params] & body] 
  `(defmethod parse ~tag [~'tag ~pstate & {:keys [~@params]}]
     (reset! +debug+ (assoc ~pstate :tag ~tag))
     (if-let [err# (:error ~pstate)] ; Need to return a MathExp either way.
       {:tkn :eof :char-stream "" :peek-stream "" :error err# :tag ~tag}
       (do ~@body))))

;;; ============ Lexer ===============================================================
(defn- gather-whitesp ; POD this was borrowed from something that had /* */ comments. Overkill!
  "Gather whitespace at head, returning it; don't touch pstate."
  [s]
  (let [r (atom "")
        p (atom 0) 
        l (count s)]
    (if (empty? s) 
      ""
      (while (and (> l (inc @p))
                  (or (#{\space \newline \return \tab \formfeed} (nth s @p))
                      (= "/*" (subs s @p (+ @p 2)))
                      (= "//" (subs s @p (+ @p 2)))))
        (cond (#{\space \newline \return \tab \formfeed} (nth s @p))
              (loop [n @p]
                (when (#{\space \newline \return \tab \formfeed} (nth s n))
                  (swap! p inc)
                  (swap! r str (nth s n))
                  (recur (inc n)))),
              (= "/*" (subs s @p (+ @p 2)))
              (do (swap! r str (nth s @p))           (swap! p inc)
                  (swap! r str (nth s @p))           (swap! p inc)
                  (loop [i @p]
                    (if (and (= (get s @p) \*) (= (get s (inc @p)) \/))
                      (do (swap! r str (nth s @p))   (swap! p inc)
                          (swap! r str (nth s @p))   (swap! p inc))
                      (do (swap! r str (nth s @p))   (swap! p inc)
                          (recur (inc i)))))),
              (= "//" (subs s @p (+ @p 2)))
              (do (swap! r str (nth s @p))           (swap! p inc)
                  (swap! r str (nth s @p))           (swap! p inc)
                  (loop [i @p]
                    (swap! r str (nth s @p))         (swap! p inc) 
                    (when (not= \return (nth s (dec @p)))
                      (recur (inc i))))))))
    @r))

(defrecord Symbol [id greek?]) ; alphabetic symbols and latex greek letters. 
(defrecord LaTeX [name])

(def greek-alphabet
  #{"alpha" "beta" "gamma" "delta" "epsilon" "zeta" "eta" "theta" "iota" "kappa" "lambda" "mu"
    "Alpha" "Beta" "Gamma" "Delta" "Epsilon" "Zeta" "Eta" "Theta" "Iota" "Kappa" "Lambda" "Mu"
    "nu" "xi" "omnicron" "pi" "rho" "sigma" "tau" "upsilon" "phi" "chi" "psi" "omega"
    "Nu" "Xi" "Omnicron" "Pi" "Rho" "Sigma" "Tau" "Upsilon" "Phi" "Chi" "Psi" "Omega"})

(def latex-non-alpha ; POD lots more to come, https://oeis.org/wiki/List_of_LaTeX_mathematical_symbols
  ^:private
  #{"neq"  "lt" "gt" "le" "leq" "geq" "nless" "ngtr" "ngeq" "subset" "subseteq" "nabla"})

(defrecord Lexeme [raw ws token])

(defn- token-from-stream
  "Return a token object from the argument 'stream' (a string)."
  [stream]
  (let [ws (gather-whitesp stream)
        s (subs stream (count ws))
        c (first s)]
    (or (and (empty? s) (map->Lexeme {:ws ws :token :eof}))
        (and (= :eof c) (map->Lexeme {:ws ws :token :eof}))
        (and (#{\{, \}, \_, \^, \+, \-, \=, \<, \>, \(, \)} c)  (map->Lexeme {:ws ws :raw (str c) :token c}))
        (when-let [[_ num] (re-matches #"^([+-]?\d+\.?\d*(e[+-]?\d+)?).*" s)]
          (map->Lexeme {:ws ws :raw num :token (read-string num)})),
        (when-let [[_ esc symbol] (re-matches #"^(\\?)([a-zA-Z]+).*" s)]
          (map->Lexeme {:ws ws :raw (str esc symbol)
                        :token
                        (if (and esc (latex-non-alpha symbol))
                          (->LaTeX (keyword symbol))
                          (->Symbol symbol (and esc (greek-alphabet symbol))))}))
        {:error "Char starts no known token: " :raw c})))

(defn- check-for-errors
  [pstate lex]
  (if-let [err (:error lex)]
    (assoc pstate :error (:error lex))
    pstate))

(defn- read-token
  "Really read a token."
  [pstate]
  (if-let [plex (first (:peek-lexemes pstate))]
    (-> pstate
        (assoc :lex plex)
        (assoc :tkn (:token plex))
        (update-in [:peek-lexemes] #(vec (rest %)))
        (update-in [:char-stream] subs (+ (count (:raw plex)) (count (:ws plex)))))
    (let [lex (token-from-stream (:char-stream pstate))]
      (-> pstate
          (check-for-errors lex)
          (assoc :lex lex)
          (assoc :tkn (:token lex))
          (update-in [:char-stream] subs (+ (count (:raw lex)) (count (:ws lex))))
          (update-in [:peek-stream] subs (+ (count (:raw lex)) (count (:ws lex))))))))

(defn- peek-token
  "Return a lexeme without changing the :char-stream."
  ([pstate] (peek-token pstate 1))
  ([pstate n]
   (as-> pstate ?pstate
     (loop [cnt (- n (count (:peek-lexemes ?pstate)))
            ps ?pstate]
       (if (> cnt 0)
         (let [lex (token-from-stream (:peek-stream ps))]
           (recur (dec cnt)
                  (-> ps
                      (check-for-errors lex)
                      (update-in [:accum-str] str (:ws lex) (:raw lex)) 
                      (update-in [:peek-stream] subs (+ (count (:raw lex)) (count (:ws lex))))
                      (update-in [:peek-lexemes] conj lex))))
         ps))
     (assoc ?pstate :peek-lex (nth (:peek-lexemes ?pstate) (dec n)))
     (assoc ?pstate :peek (:token (:peek-lex ?pstate))))))

(defn look
  "Assumes that peek-token n has been executed."
  ([pstate]
   (look pstate 1))
  ([pstate n]
   (:token (nth (:peek-lexemes pstate) (dec n)))))

(defn- assert-token
  "Read a token and check that it is what was expected."
  [pstate tkn]
  (as-> pstate ?pstate
   (read-token ?pstate)
   (if (= tkn (:tkn ?pstate))
     ?pstate
     (assoc pstate :error (str "expected: " tkn " got: " (:tkn pstate))))))

;;; ============ Parser (doesn't care about lexemes, just :tkn and :peek)  =============
;(remove-all-methods parse)
;(ns-unmap *ns* 'parse)

(defn- parse-dispatch [tag & keys] tag)

(defmulti parse #'parse-dispatch)

(defn- relation-token-p [tkn]
  (contains? [\= :lt :le :gt :ge] tkn))

;;; math == relation | expression
(defparse :math
  [pstate]
  (as-> pstate ?pstate 
    (parse :expression ?pstate)
    (peek-token ?pstate)
    (if (= :eof (:peek ?pstate))
      (assoc ?pstate :math (->MathExp (:expression ?pstate)))
      (as-> ?pstate ?ps
        (parse :relation ?ps :lhs (:expression ?ps))
        (assoc ?ps :math (->MathExp (:relation ?ps)))))))

(defrecord Relation [lhs rel rhs])

;;;  relation == expression rel-tkn expression
(defparse :relation
  [pstate lhs]
  (as-> pstate ?pstate
    (if lhs
      (assoc ?pstate :lhs lhs)
      (as-> ?pstate ?ps
        (parse :expression ?ps) 
        (assoc ?ps :lhs (:expression ?ps))))
    (parse :rel-op ?pstate)
    (parse :expression ?pstate)
    (assoc ?pstate :rhs (:expression ?pstate))
    (assoc ?pstate :relation
           (->Relation (:lhs ?pstate) (:rel-op ?pstate) (:rhs ?pstate)))))

;;; rel-op == = | > | < | :leq | :geq
(defparse :rel-op
  [pstate]
  (as-> pstate ?pstate
    (read-token ?pstate)
    (let [tkn (get {\= :equal, \> :gt, \< :lt, :leq :leq, :geq :geq} (:tkn ?pstate) :error)]
      (if (= tkn :error)
        (assoc ?pstate :error {:expected "rel-op" :got (:tkn ?pstate)})
        (assoc ?pstate :rel-op tkn)))))
          
(defn- add-op-p [tkn]
  (#{\+ \-} tkn))

(defparse :add-op
  [pstate]
  (as-> pstate ?pstate
    (read-token ?pstate)
    (let [tkn (get {\+ :plus, \- :minus} (:tkn ?pstate) :error)]
      (if (= tkn :error)
        (assoc ?pstate :error {:expected "add-op" :got (:tkn ?pstate)})
        (assoc ?pstate :add-op tkn)))))

(defrecord Expression [term op exp])

;;; expression == term [add-op expression]+
(defparse :expression
  [pstate]
  (as-> pstate ?pstate
    (parse :term ?pstate)
    (peek-token ?pstate)
    (if (add-op-p (:peek ?pstate))
      (as-> ?pstate ?ps
        (parse :add-op ?ps)
        (parse :expression ?ps)
        (assoc ?ps :expression (map->Expression {:term (:term ?ps) :op (:add-op ?ps) :exp (:expression ?ps)})))
      (assoc ?pstate :expression (map->Expression {:term (:term ?pstate)})))))

(defn- unary-op-p
  [tkn]
  (= tkn \-))

(defparse :unary-op
  [pstate]
  (assert-token pstate \-))

(defrecord Term [unary-op factors])

;;; Example terms \\beta_3X_3  \\beta_{12}X_1X_2  123 X 
;;; term == (unary-op)? factor [factor]*
(defparse :term 
  [pstate]
  (as-> pstate ?pstate
    (assoc ?pstate :factors [])
    (peek-token ?pstate)
    (if (unary-op-p (:peek ?pstate))
      (parse :unary-op ?pstate)
      (assoc ?pstate :unary-op nil))
    (loop [ps (parse :factor ?pstate)]
      (as-> ps ?ps
        (update-in ?ps [:factors] conj (:factor ?ps))
        (peek-token ?ps)
        (if (= Symbol (type (:peek ?ps)))
          (recur (parse :factor ?ps))
          ?ps)))
    (assoc ?pstate :term (map->Term {:unary-op (:unary-op ?pstate)
                                     :factors (:factors ?pstate)}))))

(defrecord Factor [symbol subscript superscript])

;;; factor == symbol-number ( (subscript (superscript)?)? | (superscript (subscript)?)? )
(defparse :factor  
  [pstate]
  (as-> pstate ?pstate
    (assoc ?pstate :subscript nil)
    (assoc ?pstate :superscript nil)
    (parse :symbol-number ?pstate) ; can be a number
    (peek-token ?pstate)
    (if (#{\_ \^} (:peek ?pstate))
      (loop [ps ?pstate
             cnt 2]
        (if (and (> cnt 0) (#{\_ \^} (:peek ps)))
          (as-> ps ?ps
            (if (= (:peek ?ps) \_)
              (parse :subscript ?ps)
              (parse :superscript ?ps))
            (recur (peek-token ?ps) (dec cnt)))
          ps))
      ?pstate) 
    (assoc ?pstate :factor (->Factor (:symbol-number ?pstate) (:subscript ?pstate) (:superscript ?pstate)))))

(defparse :symbol-number
  [pstate]
  (as-> pstate ?pstate
    (read-token ?pstate)
    (if (or (number? (:tkn ?pstate)) (= Symbol (type (:tkn ?pstate))))
      (assoc ?pstate :symbol-number (:tkn ?pstate))
      (assoc ?pstate :error {:expected "symbol or number" :got (:tkn ?pstate)}))))
      
(defrecord Subscript [exp])
(defrecord Superscript [exp])

;;; subscript ==  _ expression | _ \{ expression \}
(defparse :subscript
  [pstate]
  (as-> pstate ?pstate
    (assert-token ?pstate \_)
    (peek-token ?pstate 3)
    (cond (number? (look ?pstate))
          (as-> ?pstate ?ps
            (read-token ?ps)
            (assoc ?ps :subscript (->Subscript (:tkn ?ps)))),
          (and (= \{ (look ?pstate)) (= \} (look ?pstate 3)))
          (as-> ?pstate ?ps
            (assert-token ?ps \{)
            (read-token ?ps)
            (assoc ?ps :subscript (->Subscript (:tkn ?ps)))
            (assert-token ?ps \}))
          (= \{ (look ?pstate))
          (as-> ?pstate ?ps
            (assert-token ?ps \{)
            (parse :expression ?ps)
            (assoc ?ps :subscript (->Subscript (:expression ?ps)))
            (assert-token ?ps \})))))


;;; superscript ==  ^ expression | ^ \{ expression \}
(defparse :superscript
  [pstate]
  (as-> pstate ?pstate
    (assert-token ?pstate \^)
    (peek-token ?pstate 3)
    (cond (number? (look ?pstate))
          (as-> ?pstate ?ps
            (read-token ?ps)
            (assoc ?ps :superscript (->Superscript (:tkn ?ps)))),
          (and (= \{ (look ?pstate)) (= \} (look ?pstate 3)))
          (as-> ?pstate ?ps
            (assert-token ?ps \{)
            (read-token ?ps)
            (assoc ?ps :superscript (->Superscript (:tkn ?ps)))
            (assert-token ?ps \}))
          (= \{ (look ?pstate))
          (as-> ?pstate ?ps
            (assert-token ?ps \{)
            (parse :expression ?ps)
            (assoc ?ps :superscript (->Superscript (:expression ?ps)))
            (assert-token ?ps \})))))

(defn preprocess-math 
  "Remove the outermost delimiters ($ or $$) from the expression, EXP."
  [exp]
  (let [[_ d1 math d2] (re-matches #"^\s*(\$+)(.+)(\1)\s*$" exp)
        math (and math (str/trim math))]
    (if (or (not d1) (not d2) (not= d1 d2) (= \$ (first math)) (= \$ (last math)))
      {:error "The input math expression must start with $ and end with $, or start with $$ and end with $$."}
      {:char-stream math
       :peek-stream math
       :peek-lexemes []
       :accum-str ""})))


;;;============= Conversion to OWL/Turtle ========================================
(defn new-blank-node  
  [name]
  (str "_:" (gensym name)))

(defn- math2owl-dispatch [elem & args] ; These are the arguments to the method.
  (cond (keyword? elem) elem ; This produces a value to match (e.g. the type MathExp), thus selecting a method.
        (char? elem) elem
        :else (type elem)))

(defmulti math2owl #'math2owl-dispatch)

(def +term-order+ (atom 0))
(def +factor-order+ (atom 0))
(def +triples+ (atom []))

(defn- add-triples
  [& trips]
  (swap! +triples+ into trips)
  (count @+triples+)) ; POD diagnostic

(def context {:mfi "http://modelmeth.nist.gov/mfi/", nil :mfi}) ; I thought (expand context nil) would give me same as :mfi. Nope. 
(def context+ (merge default-context context))
(def prefixes (assoc (get-prefixes context) :rdf rdf :xsd xsd))

;;;; This is top-level of the translation.
;;; (defrecord MathExp [content])
(defmethod math2owl MathExp
  [elem & {:keys []}]
  (reset! +term-order+ 0)
  (reset! +factor-order+ 0)
  (reset! +triples+ [])
  (math2owl (:content elem) :subj :realURI)
  @+triples+)

;;; (defrecord Relation [lhs rel rhs])
(defmethod math2owl Relation
  [elem & {:keys [subj]}]
  (if (:rel elem)
    (add-triples [subj :rdf:type :Relation]
                 [subj :hasLHS (math2owl (:lhs elem))]
                 [subj :hasRelationalOp (math2owl (:rel elem))]
                 [subj :hasRHS (math2owl (:rhs elem))])
    (do (add-triples [subj :rdf:type :Expression])
        (math2owl (:lhs elem) :subj subj))))

;;; (defrecord Expression [term op exp])
(defmethod math2owl Expression
  [elem & {:keys [subj]}]
  (let [subj (or subj (new-blank-node "exp"))
        term (math2owl (:term elem))]
    (add-triples
     [subj :rdf:type :Expression]
     [subj :hasTerm term]
     [term :rdf:type :Term]
     [term :hasPosition 
      {:value (str (swap! +term-order+ inc)) :type :xsd:nonNegativeInteger}]) 
    (when-let [op (:op elem)]
      (let [op (math2owl op)]
        (add-triples [op :hasLeftTerm term])
        (math2owl (:exp elem) :subj subj)))
    subj))

;;; (defrecord Term [unary-op factors])
(defmethod math2owl Term 
  [elem & {:keys []}]
  (let [term (new-blank-node "term")]
    (add-triples [term :rdf:type :Term])
    (when-let [uop (:unary-op elem)]
      (add-triples [term :hasUnaryOp (math2owl uop)]))
    (reset! +factor-order+ 0)
    (doseq [f (:factors elem)]
      (let [fname (math2owl f :subj term)]
        (add-triples [term :hasFactor fname]
                     [fname :rdf:type :Factor]
                     [fname :hasPosition 
                      {:value (str (swap! +factor-order+ inc)) :type :xsd:nonNegativeInteger}])))
    term))

;;; (defrecord Factor [symbol value subscript superscript])
(defmethod math2owl Factor
  [elem & {:keys [subj]}]
  (let [factor (new-blank-node "factor")]
    (add-triples [subj :hasFactor factor])
    (if-let [vn  (:symbol elem)] 
      (let [var (math2owl vn :subj factor)]
        (when-let [sub (:subscript   elem)] (add-triples [var :hasSubscript   (math2owl sub :subj factor)]))
        (when-let [sup (:superscript elem)] (add-triples [var :hasSuperscript (math2owl sup :subj factor)])))
      (when-let [val (:value elem)]       (add-triples [factor :hasValue (math2owl val :subj factor)])))
    factor))

(defmethod math2owl Symbol
  [elem & {:keys [subj]}]
  (let [var (new-blank-node "var")]
    (add-triples [subj :hasVar var]
                 [var :rdf:type :Variable]
                 [var :hasName {:value (:id elem) :type :xsd:string}])
    var))


(defmethod math2owl Subscript
  [elem & {:keys []}]
  (let [sub (new-blank-node "sub")]
    (add-triples [sub :rdf:type :Subscript]
                 [sub :hasExpression (if (number? (:exp elem))
                                       {:value (:exp elem) :type :xsd:decimal}
                                       (math2owl (:exp elem)))])
    sub))

(defmethod math2owl Superscript
  [elem & {:keys []}]
  (let [sup (new-blank-node "sup")]
    (add-triples [sup :rdf:type :Superscript]
                 [sup :hasExpression (if (number? (:exp elem))
                                       {:value (:exp elem) :type :xsd:decimal} 
                                       (math2owl (:exp elem)))])
    sup))

(defmethod math2owl :default
  [elem & {:keys []}]
  elem)

(defn error2owl
  [err]
  (reset! +triples+ [])
  (add-triples [:realURI :rdf:type :Error]
               [:realURI :hasMessage {:value (str err) :type :xsd:string}])
  @+triples+)

(defn process-math
  [input]
  "Toplevel form that takes a formula wrapped in dollar signs, e.g. $ y = 1 $"
  (let [result (->> input
                    (preprocess-math)
                    (parse :math))]
    (when-let [result (or (:error result) (:math result))]
      (->> result
           ((if (= (type result) MathExp) math2owl error2owl))
           (map #(expand-all context+ %))
           (edn-ld.jena/write-triple-string prefixes)
           (println)))))

(def i1 "$Y = \\beta_0$ ")
(def i2 "$Y = \\beta_1X_1$")
(def i3 "$Y = \\beta_0 + \\beta_1X_1$")
(def i4 "$ F_i = k_c V^{\\alpha_c} f^{\\beta_c} d_i^{\\gamma_c}(t_{w,i} + t)^{\\sigma_c}$")
(def i5 "$  V^{\\alpha} $")
(def i6 "$ (X) $")
(def i7 "$Y = \\beta_0 + \\beta_1X_1 + \\beta_2X_2 + \\beta_3X_3 + \\beta_{12}X_1X_2 + \\beta_{13}X_1X_3 + \\beta_{23}X_2X_3 + \\beta_{11}X_1^2 + \\beta_{22}X_2^2 + \\beta_{33}X_3^2 + experimental\\ error$")
    

