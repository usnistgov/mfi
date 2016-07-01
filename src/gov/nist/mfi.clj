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
;;; Strictly functional in parsing, as little weird, a little verbose, a little easier to debug.
;;; It was experimental. My mind is still not made up about it.

;;; ToDo:
;;;          - i7 looks botched.
;;;          - Change (parse :tag pstate) to (parse pstate :tag) and change every (as-> ...) to (-> ...)
;;;          - Consider a rewrite that uses clojure.spec. (Is that feasible?)
;;;          - Replace 'defparse named' atomic elements on map with a stack of such elements. (There is a bug otherwise!)
;;;          - Write owl axioms for relations.
;;;          - Write results to in-memory jena.
;;;          - Write SPARQL to recover mathematical expressions.

(def ^:private +debug+ (atom nil))
(defrecord MathExp [content])

;;; POD As written pstate really has to be a variable! (Otherwise will need to substitute in @body tree.)
(defmacro ^:private defparse [tag [pstate & keys-form] & body]
  `(defmethod parse ~tag [~'tag ~pstate ~@(or keys-form '(& ignore))]
     (as-> ~pstate ~pstate
       (reset! +debug+ (update-in ~pstate [:tags] conj ~tag))
       (update-in ~pstate [:local] conj {})
       (if (:error ~pstate) 
         (as-> ~pstate ~pstate ; Try to stop things, saving stream for debugging. 
           (assoc ~pstate :debug-stream (:char-stream ~pstate))
           (assoc ~pstate :char-stream "")
           (assoc ~pstate :tkn :eof))
         (as-> ~pstate ~pstate
           ~@body))
       (reset! +debug+ (update-in ~pstate [:tags] pop))
       (update-in ~pstate [:local] pop))))


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

(def greek-alphabet
  #{"alpha" "beta" "gamma" "delta" "epsilon" "zeta" "eta" "theta" "iota" "kappa" "lambda" "mu"
    "Alpha" "Beta" "Gamma" "Delta" "Epsilon" "Zeta" "Eta" "Theta" "Iota" "Kappa" "Lambda" "Mu"
    "nu" "xi" "omnicron" "pi" "rho" "sigma" "tau" "upsilon" "phi" "chi" "psi" "omega"
    "Nu" "Xi" "Omnicron" "Pi" "Rho" "Sigma" "Tau" "Upsilon" "Phi" "Chi" "Psi" "Omega"})

(def math-op #{"sum" "frac" "nabla"})

(def math-annotation #{"bar"})

(def math-rel-op ; POD lots more to come, https://oeis.org/wiki/List_of_LaTeX_mathematical_symbols
  ^:private
  #{"neq"  "lt" "gt" "le" "leq" "geq" "nless" "ngtr" "ngeq" "subset" "subseteq"})


(def latex-any
  (set (concat math-op math-annotation math-rel-op)))

(defrecord Symbol [name greek?])  ; alphabetic symbols and latex greek letters. 
(defrecord LaTeX [name])          ; thing starting with \ other than greek letters. 
(defrecord Lexeme [raw ws token]) ; container for Symbol/Latex and other info.

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
        (when-let [[_ esc symbol] (re-matches #"^(\\?)([a-zA-Z\,]+).*" s)] ; POD I added comma here. Example "c,i" Do I care?
          (map->Lexeme {:ws ws :raw (str esc symbol)
                        :token
                        (if (and esc (latex-any symbol))
                          (->LaTeX symbol)
                          (->Symbol symbol (and esc (greek-alphabet symbol))))}))
        {:error "Char starts no known token: " :raw (str c)}))) 

(defn- check-for-errors
  [pstate lex]
  (if-let [err (:error lex)]
    (assoc pstate :error (:error lex))
    pstate))

(defn- read-token
  "Consume a token, either from peek or the real stream."
  [pstate]
  (if-let [plex (first (:peek-lexemes pstate))]
    (as-> pstate ?pstate
      (assoc ?pstate :lex plex)
      (assoc ?pstate :tkn (:token plex))
      (update-in ?pstate [:peek-lexemes] #(vec (rest %)))
      (assoc ?pstate :peek-lex (first (:peek-lexemes ?pstate)))
      (assoc ?pstate :peek (:token (:peek-lex ?pstate))))
    (let [lex (token-from-stream (:char-stream pstate))]
      (-> pstate
          (check-for-errors lex)
          (assoc :lex lex)
          (assoc :tkn (:token lex))
          (update-in [:char-stream] subs (+ (count (:raw lex)) (count (:ws lex))))))))

(defn- peek-token
  "Return a lexeme."
  ([pstate] (peek-token pstate 1))
  ([pstate n]
   (as-> pstate ?pstate
     (loop [cnt (- n (count (:peek-lexemes ?pstate)))
            ps ?pstate]
       (if (> cnt 0)
         (let [lex (token-from-stream (:char-stream ps))]
           (recur (dec cnt)
                  (-> ps
                      (check-for-errors lex)
                      (update-in [:accum-str] str (:ws lex) (:raw lex)) 
                      (update-in [:char-stream] subs (+ (count (:raw lex)) (count (:ws lex))))
                      (update-in [:peek-lexemes] conj lex))))
         ps))
     (assoc ?pstate :peek-lex (nth (:peek-lexemes ?pstate) (dec n) nil))
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
   (peek-token ?pstate)
   (if (= tkn (:peek ?pstate))
     (read-token ?pstate)
     (assoc ?pstate :error (str "expected: " tkn " got: " (:tkn pstate))))))

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
    (assoc-in ?pstate [:local 0 :rhs]  (:result ?pstate))
    (assoc ?pstate :result
           (->Relation (-> ?pstate :local first :lhs)
                       (-> ?pstate :local first :rel-op)
                       (-> ?pstate :local first :rhs)))))

;;; rel-op == = | > | < | :leq | :geq
(defparse :rel-op
  [pstate]
  (as-> pstate ?pstate
    (read-token ?pstate)
    (let [tkn (get {\= :equal, \> :gt, \< :lt, :leq :leq, :geq :geq} (:tkn ?pstate) :error)]
      (if (= tkn :error)
        (assoc ?pstate :error {:expected "rel-op" :got (:tkn ?pstate)})
        (assoc ?pstate :result tkn)))))
          
(defn- add-op-p [tkn]
  (#{\+ \-} tkn))

(defparse :add-op
  [pstate]
  (as-> pstate ?pstate
    (read-token ?pstate)
    (let [tkn (get {\+ :plus, \- :minus} (:tkn ?pstate) :error)]
      (if (= tkn :error)
        (assoc ?pstate :error {:expected "add-op" :got (:tkn ?pstate)})
        (assoc ?pstate :result tkn)))))

(defrecord Expression [term op exp])

;;; Typical 
;;; <expression> ::= <term> | <expression> add-op" <term>
;;; <term>       ::= <factor> | <term>  <factor>
;;; <factor>     ::= <constant> | <variable> | "(" <expression> ")"


;;; expression == term [add-op expression]+ | primary
(defparse :expression
  [pstate]
  (peek-token pstate)
  (as-> pstate ?pstate
    (parse :term ?pstate)
    (assoc-in ?pstate [:local 0 :term] (:result ?pstate))
    (peek-token ?pstate)
    (if (add-op-p (:peek ?pstate))
      (as-> ?pstate ?ps
        (parse :add-op ?ps)
        (assoc-in ?ps [:local 0 :add-op] (:result ?ps))
        (parse :expression ?ps)
        (assoc-in ?ps [:local 0 :expression] (:result ?ps)))
      ?pstate)
    (assoc ?pstate :result (->Expression (-> ?pstate :local first :term)
                                         (-> ?pstate :local first :add-op)
                                         (-> ?pstate :local first :expression)))))

;;; math-op = frac | 
(defparse :math-op
  [pstate]
  (let [name (:name (:peek pstate))]
    (cond (= "frac" name)
          (parse :frac pstate),
          (= "sum" name)
          (parse :sum pstate), ; nyi
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

(defn- unary-op?
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
    (assoc-in ?pstate [:local 0 :factors] [])
    (peek-token ?pstate)
    (if (unary-op? (:peek ?pstate))
      (as-> ?pstate ?ps
        (parse :unary-op ?ps)
        (assoc-in ?ps [:local 0 :unary-op] (:result ?ps)))
      ?pstate)
    (loop [ps (parse :factor ?pstate)]
      (as-> ps ?ps
        (update-in ?ps [:local 0 :factors] conj (:result ?ps))
        (peek-token ?ps)
        (if (not (#{\= \< \> \+ \- \} \) :eof} (:peek ?ps)))
          (recur (parse :factor ?ps))
          ?ps)))
    (assoc ?pstate :result (->Term (-> ?pstate :local first :unary-op)
                                   (-> ?pstate :local first :factors)))))


(defrecord Factor [symbol-number subscript superscript])

;;; factor ==   symbol-number ( (subscript (superscript)?)? | (superscript (subscript)?)? )
;;;           | primary       ( (subscript (superscript)?)? | (superscript (subscript)?)? )
(defparse :factor  
  [pstate]
  (as-> pstate ?pstate
    (if (or (= \( (:peek ?pstate)) (= LaTeX (type (:peek ?pstate))))
      (as-> ?pstate ?ps
        (parse :primary ?ps)
        (assoc-in ?ps [:local 0 :symbol-number] (:result ?ps)))
      (as-> ?pstate ?ps
        (parse :symbol-number ?ps)
        (assoc-in ?ps [:local 0 :symbol-number] (:result ?ps))))
    (peek-token ?pstate)
    (if (#{\_ \^} (:peek ?pstate))
      (loop [ps ?pstate
             cnt 2]
        (if (and (> cnt 0) (#{\_ \^} (:peek ps)))
          (as-> ps ?ps
            (if (= (:peek ?ps) \_)
              (as-> ?ps ?ps1
                (parse :subscript ?ps1)
                (assoc-in ?ps1 [:local 0 :subscript] (:result ?ps1)))
              (as-> ?ps ?ps1
                (parse :superscript ?ps1)
                (assoc-in ?ps1 [:local 0 :superscript] (:result ?ps1))))
            (recur (peek-token ?ps) (dec cnt)))
          ps))
      ?pstate)
    (assoc ?pstate :result (->Factor (-> ?pstate :local first :symbol-number)
                                     (-> ?pstate :local first :subscript)
                                     (-> ?pstate :local first :superscript)))))

;;; Primary == '(' expression ')' | math-op | annotated-exp  
(defparse :primary
  [pstate]
  (peek-token pstate)
  (cond (= (:peek pstate) \()
        (as-> pstate ?pstate
          (assert-token ?pstate \()
          (parse :expression ?pstate)
          (assoc-in ?pstate [:local 0 :exp] (:result ?pstate))
          (assert-token ?pstate \))
          (assoc ?pstate :result (-> ?pstate :local first :exp))),
        (and (= LaTeX (type (:peek pstate)))
             (math-op (:name (:peek pstate))))
        (parse :math-op pstate),
        (and (= LaTeX (type (:peek pstate)))
             (math-annotation (:name (:peek pstate))))
        (parse :annotated-exp pstate)))

(defparse :symbol-number
  [pstate]
  (as-> pstate ?pstate
    (read-token ?pstate)
    (cond (= Symbol (type (:tkn ?pstate)))
          (assoc ?pstate :result (:tkn ?pstate)),
          (number? (:tkn ?pstate))
          (assoc ?pstate :result (map->Symbol {:name (:tkn ?pstate) :greek? false})),
          true 
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
            (assoc ?ps :result (->Subscript (:tkn ?ps)))),
          (= 1 (count (str (:name (look ?pstate))))) ; symbol of one letter!
          (as-> ?pstate ?ps
            (parse :symbol-number ?ps) ; FIX THIS I want cut the expression down to a single term ??? Maybe just check for subj in serialize??
            (assoc ?ps :result (->Subscript (:result ?ps))))
          (and (= \{ (look ?pstate)) (= \} (look ?pstate 3)))
          (as-> ?pstate ?ps
            (assert-token ?ps \{)
            (read-token ?ps)
            (assoc ?ps :result (->Subscript (:tkn ?ps)))
            (assert-token ?ps \})),
          (= \{ (look ?pstate))
          (as-> ?pstate ?ps
            (assert-token ?ps \{)
            (parse :expression ?ps)
            (assoc ?ps :result (->Subscript (:result ?ps)))
            (assert-token ?ps \})))))

;;; superscript ==  ^ expression | ^ \{ expression \}
(defparse :superscript
  [pstate]
  (as-> pstate ?pstate
    (assert-token ?pstate \^)
    (peek-token ?pstate 3)
    (cond (or (number? (look ?pstate)) (= 1 (count (str (:name (look ?pstate))))))
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
       :peek-lexemes []
       :tags []
       :local []
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

;;; (defrecord AnnotatedExpression [exp annotation])
(defmethod math2owl AnnotatedExp
  [elem & {:keys [subj]}]
  (let [subj (or subj (new-blank-node "aexp"))
        exp (math2owl (:exp elem))]
    (add-triples
     [subj :rdf:type :AnnotatedExpression]
     [subj :hasExpression exp]
     [subj :hasAnnotation {:value (:name (:annotation elem)) :type :xsd:string}])
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

;;; (defrecord Factor [symbol-number subscript superscript])
(defmethod math2owl Factor
  [elem & {:keys [subj]}]
  (let [factor (new-blank-node "factor")
        vname  (math2owl (:symbol-number elem) :subj factor)]
    (add-triples [subj :hasFactor factor]
                 [factor :hasSymbol vname])
    (when-let [sub (:subscript     elem)] (add-triples [vname :hasSubscript   (math2owl sub :subj factor)]))
    (if (number? (:name (:symbol-number elem)))
      (when-let [sup (:superscript   elem)] (add-triples [vname :hasExponent (math2owl sup :subj factor)]))
      (when-let [sup (:superscript   elem)] (add-triples [vname :hasSuperscript (math2owl sup :subj factor)])))
    factor))

; (defrecord Symbol [name greek?]) 
(defmethod math2owl Symbol
  [elem & {:keys [subj]}]
  (let [sym (new-blank-node "sym")]
    (if (number? (:name elem))
      (add-triples [subj :hasValue sym]
                   [sym :rdf:type :LiteralNumber]
                   [sym :hasValue {:value (:name elem) :type :xsd:decimal}])
        (add-triples [subj :hasVariable sym]
                     [sym :rdf:type :Variable]
                     [sym :hasName {:value (:name elem) :type :xsd:string}]))
    sym))

(defmethod math2owl Fraction
  [elem & {:keys [subj]}]
  (let [subj (or subj (new-blank-node "frac"))
        num   (math2owl (:numerator elem))
        denom (math2owl (:denominator elem))]
    (add-triples [subj :rdf:type :Fraction] ; POD in ontology, make this a subtype of Expression
                 [subj :hasNumerator num]
                 [subj :hasDenominator denom])
    subj))

(defmethod math2owl Subscript
  [elem & {:keys []}]
  (let [sub (new-blank-node "sub")]
    (add-triples [sub :rdf:type :Subscript]
                 [sub :hasExpression (if (number? (:exp elem))
                                       {:value (:exp elem) :type :xsd:decimal}
                                       (math2owl (:exp elem) :subj sub))])
    sub))

(defmethod math2owl Superscript
  [elem & {:keys []}]
  (let [sup (new-blank-node "sup")]
    (add-triples [sup :rdf:type :Superscript]
                 [sup :hasExpression (if (number? (:exp elem))
                                       {:value (:exp elem) :type :xsd:decimal} 
                                       (math2owl (:exp elem) :subj sup))])
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
(def i7 "$Y = \\beta_0 + \\beta_1X_1 + \\beta_2X_2 + \\beta_3X_3 + \\beta_{12}X_1X_2 + \\beta_{13}X_1X_3 + \\beta_{23}X_2X_3 + \\beta_{11}X_1^2 + \\beta_{22}X_2^2 + \\beta_{33}X_3^2 + experimentalerror$")
(def i8 "$\\frac{1}{2}$")
(def i9 "$\\bar{x}$")
(def i10 "$ x = \\frac{1}{2}$")
(def i11 "$t_{c,i} = \\frac{\\pi \\bar{D_i} L}{1000V f}$") ; POD fix this so Vf works. (Need hints from table). 
    

