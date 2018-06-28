(ns gov.nist.mfi-test
  (:require [clojure.test :refer :all]
            [edn-ld.core :refer :all]
            [edn-ld.common :refer :all]
            [edn-ld.jena :refer :all]
            [gov.nist.mfi :refer :all :as mfi])
  (:import (java.io StringReader StringWriter)
           (com.hp.hpl.jena.graph Node_URI Node_Blank Node_Literal)
           (com.hp.hpl.jena.sparql.core Quad)
           (org.apache.jena.riot.system StreamRDF)
           (com.hp.hpl.jena.rdf.model ModelFactory AnonId)
           (com.hp.hpl.jena.query DatasetFactory)
           (com.hp.hpl.jena.datatypes BaseDatatype)
           (org.apache.jena.riot RDFDataMgr RDFLanguages)
           (gov.nist.mfi MathExp)))

(def input1 "Y = \\beta_0 ")
(def input2 "Y = \\beta_1X_1")
(def input3 "Y = \\beta_0 + \\beta_1X_1")
(def input4 " F_i = k_c V^{\\alpha_c} f^{\\beta_c} d_i^{\\gamma_c}(t_{w,i} + t)^{\\sigma_c}")
(def input5 "  V^{\\alpha} ")
(def input6 " (X) ")
(def input7 "Y = \\beta_0 + \\beta_1X_1 + \\beta_2X_2 + \\beta_3X_3 + \\beta_{12}X_1X_2 + \\beta_{13}X_1X_3 + \\beta_{23}X_2X_3 + \\beta_{11}X_1^2 + \\beta_{22}X_2^2 + \\beta_{33}X_3^2 + experimentalerror")
(def input8 "\\frac{1}{2}")
(def input9 "\\bar{x}")
(def input10 " x = \\frac{1}{2}")
(def input11 "t_{c,i} = \\frac{\\pi \\bar{D_i} L}{1000V f}") ; POD fix this so Vf works. (Need hints from table).
(def input12 " \\sum x")
(def input13 " y = \\sum \\limits_1^n x")

            
(defn- simple-test
  [input]
  (let [result (->> input
                    (mfi/preprocess-math)
                    (mfi/parse :math))]
    (when-let [result (or (:error result) (:math result))]
      (->> result
           (#((if (instance? MathExp result) math2owl error2owl) % :text input))
           (map #(edn-ld.core/expand-all context+ %))
           (edn-ld.jena/write-triple-string prefixes)) ; Not used, but I'm interested in problems here.
      (count @+triples+))))

(deftest expected-triple-count
  (testing "Expected triple count from parsing"
    (is (= 27  (simple-test input1)))  ; 21
    (is (= 40  (simple-test input2)))  ; 30
    (is (= 59  (simple-test input3)))  ; 45
    (is (= 183 (simple-test input4)))  ; 174
    (is (= 20  (simple-test input5)))  ; 18
    (is (= 21  (simple-test input6)))  ; 20
    (is (= 380 (simple-test input7)))  ; 277 <--  but looks right
    (is (= 20  (simple-test input8)))  ; 33
    (is (= 17  (simple-test input9)))  ; 23
    (is (= 27  (simple-test input10))) ; 39
    (is (= 97  (simple-test input11))) ; 94
    (is (= 16  (simple-test input12))) ; 14
    (is (= 37  (simple-test input13))))) ; 29

