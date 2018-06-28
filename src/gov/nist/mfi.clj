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
;;; The parsing functions are 'internally' functional (using threading macros on parse state).
;;; This seems a little weird at times, but it really does make debugging easier. 

;;; ToDo:
;;;       - Simplify expression with cutoff. Go back and fix the subscripts and superscripts to just use expression.
;;;       - Consider a rewrite that uses clojure.spec. (Is that feasible?)
;;;       - Write results to in-memory jena.

(def ^:private +debug+ (atom nil))
(defrecord MathExp [content])

;;; POD As written pstate really has to be a variable! (Otherwise will need to substitute in @body tree.)
(defmacro ^:private defparse [tag [pstate & keys-form] & body]
  `(defmethod parse ~tag [~'tag ~pstate ~@(or keys-form '(& ignore))]
;     (println ~tag)
     (as-> ~pstate ~pstate
       (reset! +debug+ (update-in ~pstate [:tags] conj ~tag))
       (update-in ~pstate [:local] #(into [{}] %))
       (if (:error ~pstate) ; Stop things
         (assoc ~pstate :tkn :eof)
         (as-> ~pstate ~pstate
           ~@body))
       (reset! +debug+ (update-in ~pstate [:tags] pop))
       (update-in ~pstate [:local] #(vec (rest %))))))

;;; ============ Lexer ===============================================================
(defn- whitesp 
  "Evaluates to whitespace at head of string or empty string if none."
  [s]
  (if s (or (nth (re-matches #"(?m)(\s+).*$" s) 1) "") ""))

(def greek-alphabet
  ^:private
  #{"alpha" "beta" "gamma" "delta" "epsilon" "zeta" "eta" "theta" "iota" "kappa" "lambda" "mu"
    "Alpha" "Beta" "Gamma" "Delta" "Epsilon" "Zeta" "Eta" "Theta" "Iota" "Kappa" "Lambda" "Mu"
    "nu" "xi" "omnicron" "pi" "rho" "sigma" "tau" "upsilon" "phi" "chi" "psi" "omega"
    "Nu" "Xi" "Omnicron" "Pi" "Rho" "Sigma" "Tau" "Upsilon" "Phi" "Chi" "Psi" "Omega"
    "varepsilon" "vartheta" "varkappa" "varrho" "varsigma" "varphi"})

;;; POD lots more to come, https://oeis.org/wiki/List_of_LaTeX_mathematical_symbols
(def math-op
  ^:private
  #{"frac" "int" "sum" "prod" "nabla"})

(def math-annotation
  ^:private
  #{"bar" "hat" "limits"}) ; POD "limits" ought to be one of a new 'math-args'

(def math-rel-op 
  ^:private
    #{"neq"  "lt" "gt" "le" "leq" "geq" "nless" "ngtr" "ngeq" "subset" "subseteq"
      "leqslant" "nleq" "nleqslant" "prec" "preceq" "npreceq" "ll" "lll" "nsubseteq"
      "sqsubset" "sqsubseteq" "qeq" "qeqslant"  "ngeqslant" "succ" "nsucc" "succeq"
      "nsucceq" "gg" "ggg" "supset" "supseteq" "nsupseteq" "sqsupset" "sqsupseteq"
      "doteq" "equiv" "approx" "cong" "simeq" "sim" "propto" "ne"})

(def latex-any
  ^:private
  (set (concat math-op math-annotation math-rel-op)))

(defrecord Symbol [name greek?])  ; alphabetic symbols and latex greek letters. 
(defrecord LaTeX [name])          ; thing starting with \ other than greek letters.
(defrecord LaTeXRelOp [name])

(defn LaTeX? [x] (or (instance? LaTeX x) (instance? LaTeXRelOp x)))
(defn LaTeXRelOp? [x] (instance? LaTeXRelOp x))

(defn- token-from-string
  "Return a token object from the argument 'stream' (a string)."
  [stream]
  (let [ws (whitesp stream)
        s (subs stream (count ws))
        c (first s)]
    (or (and (empty? s) {:ws ws :raw "" :tkn :eof})
        (and (#{\{, \}, \_, \^, \(, \)} c) {:ws ws :raw (str c) :tkn c})
        (when-let [op ({\= "eq", \< "lt", \>, "gt"} c)]
          {:ws ws :raw (str c) :tkn (->LaTeXRelOp op)})
        (when-let [[_ num] (re-matches #"^([+-]?\d+\.?\d*(e[+-]?\d+)?).*" s)]
          {:ws ws :raw num :tkn (read-string num)}),
        (and (#{\+, \-} c) {:ws ws :raw (str c) :tkn c})
        (when-let [[_ esc symbol] (re-matches #"^(\\?)([a-zA-Z\,]+).*" s)] ; POD I added comma here. Example "c,i" Do I care?
          {:ws ws :raw (str esc symbol)
           :tkn
           (cond (and esc (math-rel-op symbol)) (->LaTeXRelOp symbol),
                 (and esc (latex-any symbol))   (->LaTeX symbol),
                 :default
                 (->Symbol symbol (and esc (greek-alphabet symbol))))})
        (throw (ex-info "Char starts no known token: " {:raw c})))))

;;; When done, get rid of Lexeme!
(defn tokenize
  "Return a list of tokens"
  [stream]
  (loop [s stream
         tkns []]
    (let [lex (token-from-string s)]
      (if (= :eof (:tkn lex))
        (conj tkns :eof)
        (recur
         (subs s (+ (count (:raw lex)) (count (:ws lex))))
         (conj tkns (:tkn lex)))))))

(defn- read-token
  "Consume a token, setting :tkn."
  [pstate]
  (-> pstate 
      (assoc :tkn (or (first (:tokens pstate)) :eof))
      (assoc :tokens (rest (:tokens pstate)))))

(defn look
  "Returns a token, not the pstate."
  ([pstate]
   (look pstate 1))
  ([pstate n]
   (if (> n (count (:tokens pstate)))
     :eof
     (nth (:tokens pstate) (dec n)))))

(defn- assert-token
  "Read a token and check that it is what was expected."
  [pstate tkn]
  (as-> pstate ?pstate
    (if (= tkn (look ?pstate))
      (read-token ?pstate)
      (as-> ?pstate ?ps
        (assoc ?ps :error (str "expected: " tkn " got: " (:tkn ?ps)))
        (assoc ?ps :debug-tokens (:tokens ?ps))
        (assoc ?ps :tokens [])))))

(defn- assert-LaTeX
  "Read a token and check that it is what was expected."
  [pstate tkn]
  (as-> pstate ?pstate
    (if (and (LaTeX? (look ?pstate))
             (= (:name (look ?pstate)) tkn))
      (read-token ?pstate)
      (assoc ?pstate :error (str "expected LaTeX: " tkn " got: " (:tkn pstate))))))

;;; ============ Parser =============
;(remove-all-methods parse)
;(ns-unmap *ns* 'parse)

(defn- parse-dispatch [tag & keys] tag)

(defmulti parse #'parse-dispatch)

;;; math == relation | expression
(defparse :math
  [pstate]
  (as-> pstate ?pstate 
    (parse :expression ?pstate)
    (if (= :eof (look ?pstate))
      (assoc ?pstate :math (->MathExp (:result ?pstate)))
      (as-> ?pstate ?ps
        (parse :relation ?ps :lhs (:result ?ps))
        (assoc ?ps :math (->MathExp (:result ?ps)))))))

(defrecord Relation [lhs rel rhs])

;;;  relation == expression rel-tkn expression
(defparse :relation
  [pstate & {:keys [lhs]}]
  (as-> pstate ?pstate
    (if lhs
      (assoc-in ?pstate [:local 0 :lhs] lhs)
      (as-> ?pstate ?ps
        (parse :expression ?ps)
        (assoc-in ?ps [:local 0 :lhs] (:result ?ps))))
    (parse :rel-op ?pstate)
    (assoc-in ?pstate [:local 0 :rel-op] (:result ?pstate))
    (parse :expression ?pstate)
    (assoc-in ?pstate [:local 0 :rhs] (:result ?pstate))
    (assoc ?pstate :result
           (->Relation (-> ?pstate :local first :lhs)
                       (-> ?pstate :local first :rel-op)
                       (-> ?pstate :local first :rhs)))))

;;; rel-op == = | > | < | :leq | :geq, etc. (see math-rel-op)
(defparse :rel-op
  [pstate]
  (as-> pstate ?pstate
    (read-token ?pstate) 
    (if (LaTeXRelOp? (:tkn ?pstate))
      (assoc ?pstate :result (:tkn ?pstate))
      (assoc ?pstate :error {:expected "rel-op" :got (:tkn ?pstate)}))))
          
(defn- add-op-p [tkn]
  (#{\+ \-} tkn))

(defparse :add-op
  [pstate]
  (as-> pstate ?pstate
    (read-token ?pstate)
    (let [tkn (get {\+ :plusOp, \- :minusOp} (:tkn ?pstate) :error)]
      (if (= tkn :error)
        (assoc ?pstate :error {:expected "add-op" :got (:tkn ?pstate)})
        (assoc ?pstate :result tkn)))))

(defrecord Expression [term op exp])

;;; expression == ( term [add-op expression]+ ) | symbol-number
;;; Note: allowing symbol-number here is a short-cut for simple expressions.
(defparse :expression
  [pstate & {:keys [torder] :or {torder 1}}]
  (let [p1 (look pstate)
        p2 (look pstate 2)
        p3 (look pstate 3)]
    (cond ;(and (or (number? p1) (instance? Symbol p1)) ; cutoff
          ;     (or (LaTeXRelOp? p2) (#{:eof \}} p2)))
          ;(parse :simple-factor pstate),
          :default
          (as-> pstate ?pstate
            (parse :term ?pstate :torder torder)
            (assoc-in ?pstate [:local 0 :term] (:result ?pstate))
            (if (add-op-p (look ?pstate))
              (as-> ?pstate ?ps
                (parse :add-op ?ps)
                (assoc-in ?ps [:local 0 :add-op] (:result ?ps))
                (parse :expression ?ps :torder (inc torder))
                (assoc-in ?ps [:local 0 :expression] (:result ?ps)))
              ?pstate)
            (assoc ?pstate :result (->Expression (-> ?pstate :local first :term)
                                                 (-> ?pstate :local first :add-op)
                                                 (-> ?pstate :local first :expression)))))))

;;; math-op = frac | sum | integral
(defparse :math-op
  [pstate]
  (let [name (:name (look pstate))]
    (cond (= "frac" name)
          (parse :frac pstate),
          (= "sum" name)
          (parse :sum pstate), 
          (= "int" name)
          (parse :integral pstate)))) ; nyi

(defrecord Fraction [numerator denominator])

;;; frac == \frac latex-arg latex-arg
(defparse :frac
  [pstate]
  (as-> pstate ?pstate
    (read-token ?pstate)
    (parse :latex-arg ?pstate)
    (assoc-in ?pstate [:local 0 :numerator] (:result ?pstate))
    (parse :latex-arg ?pstate)
    (assoc-in ?pstate [:local 0 :denominator] (:result ?pstate))
    (assoc ?pstate :result (->Fraction (-> ?pstate :local first :numerator)
                                       (-> ?pstate :local first :denominator)))))

(defn- unary-op?
  [tkn]
  (= tkn \-))

(defparse :unary-op
  [pstate]
  (assert-token pstate \-))

(defrecord Term [unary-op factors order])

;;; Example terms \\beta_3X_3  \\beta_{12}X_1X_2  123 X 
;;; term == (unary-op)? factor [factor]*
(defparse :term 
  [pstate & {:keys [torder]}]
  (as-> pstate ?pstate
    (assoc-in ?pstate [:local 0 :factors] [])
    (if (unary-op? (look ?pstate))
      (as-> ?pstate ?ps
        (parse :unary-op ?ps)
        (assoc-in ?ps [:local 0 :unary-op] (:result ?ps)))
      ?pstate)
    (loop [forder 1 
           ps (parse :factor ?pstate :forder forder)]
      (as-> ps ?ps
        (update-in ?ps [:local 0 :factors] conj (:result ?ps))
        (if (not (or (LaTeXRelOp? (look ?ps)) (#{\+ \- \} \) :eof} (look ?ps))))
          (recur (inc forder) (parse :factor ?ps :forder (inc forder)))
          ?ps)))
    (assoc ?pstate :result (->Term (-> ?pstate :local first :unary-op)
                                   (-> ?pstate :local first :factors)
                                   torder))))

(defrecord Factor [symbol subscript superscript order])

;;; factor ==   simple-factor | primary subsuper
(defparse :factor  
  [pstate & {:keys [forder]}]
  (if (or (= \( (look pstate)) (LaTeX? (look pstate)))
    (as-> pstate ?ps
      (parse :primary ?ps)
      (assoc-in ?ps [:local 0 :primary] (:result ?ps))
      (parse :subsupers ?ps)
      (assoc ?ps :result (->Factor (-> ?ps :local first :primary)
                                   (-> ?ps :result :subscript)
                                   (-> ?ps :result :superscript)
                                   forder)))
    (parse :simple-factor pstate :forder forder)))
    
;;; simple-factor ==   (number | symbol) subsuper
(defparse :simple-factor
  [pstate & {:keys [forder]}]
  (as-> pstate ?pstate
    (read-token ?pstate)
    (cond (instance? Symbol (:tkn ?pstate))
          (assoc ?pstate :result (:tkn ?pstate)),
          (number? (:tkn ?pstate))
          (assoc ?pstate :result (->Symbol (:tkn ?pstate) false)),
          :default
          (assoc ?pstate :error {:expected "symbol or number" :got (:tkn ?pstate)}))
    (assoc-in ?pstate [:local 0 :symbol-number] (:result ?pstate))
    (parse :subsupers ?pstate)
    (assoc ?pstate :result (->Factor (-> ?pstate :local first :symbol-number)
                                     (-> ?pstate :result :subscript)
                                     (-> ?pstate :result :superscript)
                                     forder))))

;;; subsupers == ( (subscript (superscript)?)? | (superscript (subscript)?)? )
;;;              ( (subscript (superscript)?)? | (superscript (subscript)?)? )
(defparse :subsupers
  [pstate & {:keys [rel-ok?]}]
  (as-> pstate ?pstate
    (loop [ps ?pstate
           cnt 2]
      (if (and (pos? cnt) (#{\_ \^} (look ps)))
        (as-> ps ?ps
          (if (= (look ?ps) \_)
            (as-> ?ps ?ps1
              (parse :subscript ?ps1 :rel-ok? rel-ok?)
              (assoc-in ?ps1 [:local 0 :subscript] (:result ?ps1)))
            (as-> ?ps ?ps1
              (parse :superscript ?ps1 :rel-ok? rel-ok?)
              (assoc-in ?ps1 [:local 0 :superscript] (:result ?ps1))))
          (recur ?ps (dec cnt)))
          ps))
    (assoc ?pstate :result {:subscript   (-> ?pstate :local first :subscript)
                            :superscript (-> ?pstate :local first :superscript)})))

;;; Primary == '(' expression ')' | math-op | annotated-exp  
(defparse :primary
  [pstate]
  (cond (= (look pstate) \()
        (as-> pstate ?pstate
          (assert-token ?pstate \()
          (parse :expression ?pstate)
          (assoc-in ?pstate [:local 0 :exp] (:result ?pstate))
          (assert-token ?pstate \))
          (assoc ?pstate :result (-> ?pstate :local first :exp))),
        (and (LaTeX? (look pstate))
             (math-op (:name (look pstate))))
        (parse :math-op pstate),
        (and (LaTeX? (look pstate))
             (math-annotation (:name (look pstate))))
        (parse :annotated-exp pstate)))

;;; sum == \sum ( \limits lower-limit ? upper-limit ?)? body
(defrecord Sum [body lower upper])

(defparse :sum
  [pstate]
  (as-> pstate ?pstate
    (assert-LaTeX ?pstate "sum")
    (if (and (LaTeX? (look ?pstate))
             (= (:name (look ?pstate)) "limits"))
      (as-> ?pstate ?ps
        (read-token ?ps)
        (parse :subsupers ?ps :rel-ok? true)
        (assoc-in ?ps [:local 0 :lowerlimit] (:subscript (:result ?ps)))
        (assoc-in ?ps [:local 0 :upperlimit] (:superscript (:result ?ps))))
      ?pstate)
    (parse :expression ?pstate)
    (assoc ?pstate :result (->Sum (:result ?pstate)
                                  (-> ?pstate :local first :lowerlimit)
                                  (-> ?pstate :local first :upperlimit)))))

(defrecord AnnotatedExp [exp annotation])

(defparse :annotated-exp
  [pstate]
  (as-> pstate ?pstate
    (read-token ?pstate)
    (assoc-in ?pstate [:local 0 :annotation] (:tkn ?pstate))
    (parse :latex-arg ?pstate)
    (assoc-in ?pstate [:local 0 :exp] (:result ?pstate))
    (assoc ?pstate :result (->AnnotatedExp (-> ?pstate :local first :exp)
                                           (-> ?pstate :local first :annotation)))))

;;; latex-arg == '{' expression '}'
(defparse :latex-arg
  [pstate]
  (as-> pstate ?pstate
    (assert-token ?pstate \{)
    (parse :expression ?pstate)
    (assoc-in ?pstate [:local 0 :exp] (:result ?pstate))
    (assert-token ?pstate \})
    (assoc ?pstate :result (-> ?pstate :local first :exp))))

(defn x-before-y
  "Return true if position of token matching test x 
   is before position of token matching test y."
   [x-test y-test ps & {:keys [limit] :or {limit 10}}]
  (loop [cnt 1]
    (let [tkn (look ps cnt)]
      (cond (> cnt limit) false
            (x-test tkn) true
            (y-test tkn) false
            :default
            (recur (dec cnt))))))

(defrecord Subscript [exp])
(defrecord Superscript [exp])

;;; subscript ==  _ expression | _ \{ expression \}
(defparse :subscript
  [pstate & {:keys [rel-ok?]}]
  (as-> pstate ?pstate
    (assert-token ?pstate \_)
    (if (= \{ (look ?pstate))
      (as-> ?pstate ?ps
        (assert-token ?ps \{)
        (parse (if (and rel-ok? (LaTeXRelOp? ?ps)) :relation :expression) ?ps)
        (assoc ?ps :result (->Subscript (:result ?ps)))
        (assert-token ?ps \}))
      (as-> ?pstate ?ps
        (parse :simple-factor ?ps)
        (assoc ?ps :result (->Subscript (:result ?ps)))))))

;;; superscript ==  ^ expression | ^ \{ expression \}
(defparse :superscript
  [pstate & {:keys [rel-ok?]}]
  (as-> pstate ?pstate
    (assert-token ?pstate \^)
    (if (= \{ (look ?pstate))
      (as-> ?pstate ?ps
        (assert-token ?ps \{)
        (parse (if (and rel-ok? (LaTeXRelOp? ?ps)) :relation :expression) ?ps)
        (assoc ?ps :result (->Superscript (:result ?ps)))
        (assert-token ?ps \}))
      (as-> ?pstate ?ps
        (parse :simple-factor ?ps)
        (assoc ?ps :result (->Superscript (:result ?ps)))))))

(defn preprocess-math 
  "Remove the outermost delimiters ($ or $$) from the expression, EXP."
  [s]
;;;  (let [[_ d1 math d2] (re-matches #"^\s*(\$+)(.+)(\1)\s*$" s)
;;;        s (and s (str/trim s))]
;;;    (if (or (not d1) (not d2) (not= d1 d2) (= \$ (first s)) (= \$ (last s)))
;;;      {:error "The input math expression must start with $ and end with $, or start with $$ and end with $$."}
  (let [tstream (tokenize s)]
    (let [tokens (tokenize s)]
      (if (pos? (.indexOf tokens nil))
        (throw (ex-info "String did not tokenize correctly." {:tokens tokens})))
      {:tokens tokens
       :tags []
       :local []})))

;;;============= Conversion to OWL/Turtle ========================================
(defn new-blank-node  
  [name]
  (str "_:" (gensym name)))

(defn- math2owl-dispatch [elem & args] ; These are the arguments to the method.
  (cond (keyword? elem) elem ; This produces a value to match (e.g. the type MathExp), thus selecting a method.
        (char? elem) elem
        :else (type elem)))

(defmulti math2owl #'math2owl-dispatch)

(def +triples+ (atom []))

(defn- add-triples
  [& trips]
  (swap! +triples+ into (remove nil? trips))
  (count @+triples+)) ; POD diagnostic

(def context {:mfi "http://modelmeth.nist.gov/mfi/", nil :mfi}) ; I thought (expand context nil) would give me same as :mfi. Nope. 
(def context+ (merge default-context context))
(def prefixes (assoc (get-prefixes context) :rdf rdf :xsd xsd))

;;;; This is top-level of the translation.
(defmethod math2owl MathExp
  [elem & {:keys [text]}]
  (reset! +triples+ [])
  (add-triples [:realURI :rdf:type :MathContent]
               [:realURI :hasLaTeXText {:value text :tpe :xsd:string}])
  (math2owl (:content elem) :parent :realURI)
  @+triples+)

(defmethod math2owl Relation
  [elem & {:keys [parent]}]
  (let [rel (new-blank-node "rel")]
    (add-triples (when parent [parent :hasRelation rel])
                 [rel :rdf:type :Relation]
                 [rel :hasLHS (math2owl (:lhs elem))]
                 [rel :hasRelationalOp (math2owl (:rel elem))]
                 [rel :hasRHS (math2owl (:rhs elem))])
    rel))

(defmethod math2owl Expression
  [elem & {:keys [parent]}]
  (let [exp (new-blank-node "exp")
        term (math2owl (:term elem))]
    (add-triples
     (when parent [parent :hasExpression exp])
     [exp :rdf:type :Expression]
     [exp :hasTerm term]) 
    (when-let [op (:op elem)]
      (let [op (math2owl op)]
        (add-triples [exp op term])
        (math2owl (:exp elem) :parent exp)))
    exp))

(defmethod math2owl AnnotatedExp
  [elem & {:keys [parent]}]
  (let [aexp (new-blank-node "aexp")
        exp (math2owl (:exp elem))]
  (add-triples
   (when parent [parent :hasAnnotationExp aexp])
   [aexp :rdf:type :AnnotatedExpression]
   [aexp :hasExpression exp]
   [aexp :hasAnnotation {:value (:name (:annotation elem)) :type :xsd:string}])
  aexp))

(defn new-rooted-term  
  []
  (str "http://gov.nist.modelmeth/" (gensym "term")))


(defmethod math2owl Term 
  [elem & {:keys [parent]}]
  (let [term (new-rooted-term) #_(new-blank-node "term")]
    (add-triples (when parent [parent :hasTerm term])
                 [term :rdf:type :Term]
                 [term :hasTermOrder {:value (:order elem) :type :xsd:nonNegativeInteger}])
    (when-let [uop (:unary-op elem)]
      (add-triples [term :hasUnaryOp (math2owl uop)]))
    (doseq [f (:factors elem)]
      (let [fname (math2owl f :parent term)]
        (add-triples [fname :rdf:type :Factor]
                     [fname :hasFactorOrder
                      {:value (:order f) :type :xsd:nonNegativeInteger}])))
    term))

(defmethod math2owl Factor
  [elem & {:keys [parent]}]
  (let [factor (new-blank-node "factor")
        vname  (math2owl (:symbol elem) :parent factor)]
    (when parent (add-triples [parent :hasFactor factor]))
    (when-let [sub (:subscript     elem)] (add-triples [vname :hasSubscript   (math2owl sub :parent factor)]))
    (if (number? (:name (:symbol elem)))
      (when-let [sup (:superscript   elem)] (add-triples [vname :hasExponent (math2owl sup :parent factor)]))
      (when-let [sup (:superscript   elem)] (add-triples [vname :hasSuperscript (math2owl sup :parent factor)])))
    factor))

(defmethod math2owl Symbol
  [elem & {:keys [parent]}]
  (let [sym (new-blank-node "sym")]
    (if (number? (:name elem))
      (add-triples (when parent [parent :hasValue sym])
                   [sym :rdf:type :LiteralNumber]
                   [sym :hasValue {:value (:name elem) :type :xsd:decimal}])
      (add-triples (when parent [parent :hasVariable sym])
                   [sym :rdf:type :Variable]
                   [sym :hasName {:value (:name elem) :type :xsd:string}]))
    sym))

(defmethod math2owl LaTeXRelOp
  [elem & _]
  (keyword
   (or (#{\+ "plus", \- "minus"} (:name elem))
       (:name elem))))

(defmethod math2owl Fraction
  [elem & {:keys [parent]}]
  (let [frac (new-blank-node "frac")
        num  (math2owl (:numerator elem))
        denom (math2owl (:denominator elem))]
    (add-triples (when parent [parent :hasFraction frac])
                 [frac :rdf:type :Fraction] ; POD in ontology, make this a subtype of Expression
                 [frac :hasNumerator num]
                 [frac :hasDenominator denom])
    frac))

(defmethod math2owl Subscript
  [elem & _]
  (let [sub (new-blank-node "sub")]
    (add-triples [sub :rdf:type :Subscript]
                 [sub :hasExpression (if (number? (:exp elem))
                                       {:value (:exp elem) :type :xsd:decimal}
                                       (math2owl (:exp elem) :parent sub))])
    sub))

(defmethod math2owl Superscript
  [elem & _]
  (let [sup (new-blank-node "sup")]
    (add-triples [sup :rdf:type :Superscript]
                 [sup :hasExpression (if (number? (:exp elem))
                                       {:value (:exp elem) :type :xsd:decimal} 
                                       (math2owl (:exp elem) :parent sup))])
    sup))

(defmethod math2owl Sum
  [elem & {:keys [parent]}] 
  (let [sum (new-blank-node "sum")]
    (add-triples [parent :hasSum sum]
                 [sum :rdf:type :Sum]
                 [sum :hasBody (math2owl (:body elem))])
    (when-let [low (:lower elem)]
      (add-triples [sum :hasLowerLimit (math2owl low)]))
    (when-let [up  (:upper elem)]
      (add-triples [sum :hasUpperLimit (math2owl up)]))
    parent))

(defmethod math2owl :default
  [elem & _]
  elem)

(defn error2owl
  [err & {:keys [text]}]
  (add-triples [:realURI :rdf:type :Error]
               [:realURI :hasLaTeXText {:value text :type :xsd:string}]
               [:realURI :hasMessage {:value (str err) :type :xsd:string}])
  @+triples+)

(defn process-math
  [input]
  "Toplevel form that takes a formula wrapped in dollar signs, e.g. $ y = 1 $"
  (reset! +triples+ [])
  (let [result (->> input
                    (preprocess-math)
                    (parse :math))]
    (when-let [result (or (:error result) (:math result))]
      (->> result
           (#((if (instance? MathExp result) math2owl error2owl) % :text input))
           (map #(expand-all context+ %))
           (edn-ld.jena/write-triple-string prefixes)
           (println)))))

(def i1 "Y = \\beta_0 ")
(def i2 "Y = \\beta_1X_1")
(def i3 "Y = \\beta_0 + \\beta_1X_1")
(def i4 " F_i = k_c V^{\\alpha_c} f^{\\beta_c} d_i^{\\gamma_c}(t_{w,i} + t)^{\\sigma_c}")
(def i5 "  V^{\\alpha} ")
(def i6 " (X) ")
(def i7 "Y = \\beta_0 + \\beta_1X_1 + \\beta_2X_2 + \\beta_3X_3 + \\beta_{12}X_1X_2 + \\beta_{13}X_1X_3 + \\beta_{23}X_2X_3 + \\beta_{11}X_1^2 + \\beta_{22}X_2^2 + \\beta_{33}X_3^2 + experimentalerror")
(def i8 "\\frac{1}{2}")
(def i9 "\\bar{x}")
(def i10 " x = \\frac{1}{2}")
(def i11 "t_{c,i} = \\frac{\\pi \\bar{D_i} L}{1000V f}") ; POD fix this so Vf works. (Need hints from table).
(def i12 " \\sum x")
(def i13 " y = \\sum \\limits_1^n x")

(def known-var ["DC" "QC"])

(def n1  " d_i = \\frac{D_0 - D}{2} + \\delta_i ")
(def n2  "\\bar{D_i} = ( D_0 - d_i )")
(def n3  " t_{c,i} = \\frac{\\pi \\bar{D_i} L}{1000Vf} ")
(def n4  "T_n = \\sum\\limits_{i=1}^n t_{c,i}")
(def n5  "w = k_wV^{\\alpha_w}f^{\\beta_w}d^{\\gamma_w}t^{\\sigma_w}")
(def n6  "w_i = k_w V^{\\alpha_w} f^{\\beta_w} d_i^{\\gamma_w} (t_{w,i} + t)^{\\sigma_w}")
(def n7  "0 \\le t \\le t_{c,i}")
(def n8  " t_{w,i} = (\\frac{1}{k_w} V^{-\\alpha_w} f^{-\\beta_w} d_i^{-\\gamma_w} W_{i-1})^{\\frac{1}{\\sigma_w}} ")
(def n9  "\\hat{N}")
(def n10 "\\hat{N} = argmax_{i=1,2...}(\\hat{W} - W_i) ")
(def n11 "\\hat{W} - W_i \\ge 0")
(def n12 "\\Delta_i = 2(w_i - W_{i-1})tan(\\Theta)")
(def n13 "0 \\le t \\le t_{c,i}")
(def n14 "\\Phi_i = k_r V^{\\alpha_r} f^{\\beta_r} d_i^{\\gamma_r}(t_{w,i} + t)^{\\sigma_r}")
(def n15 " F_i = k_c V^{\\alpha_c} f^{\\beta_c} d_i^{\\gamma_c}(t_{w,i} + t)^{\\sigma_c}")
(def n16 " DC = N C_h t_h + (C_w + C_z) T_N")
(def n17 "QC = \\sum\\limits_{i=1}^n \\ell_d\\int_{T_{i-1}}^{T_i} \\! (2\\delta_i - \\Delta_i)^2  \\, \\mathrm{d}t
          + \\sum\\limits_{i=1}^n \\ell_r\\int_{T_{i-1}}^{T_i} \\! (\\Phi_i - R)^2  \\, \\mathrm{d}t ")
(def n18 "P = E - (DC + GC + QC)")


;;;(map process-math [i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14])
;;;(map process-math [n1 n2 n3 n4 n5 n6 n7 n8 n9 #_n10 n11 n12 n13 n14 n15 n16 #_n17 n18])

