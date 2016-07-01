(ns gov.nist.mfi-test
  (:require [clojure.test :refer :all]
            [edn-ld.core :refer :all] 
            [edn-ld.common :refer :all]
            [edn-ld.jena :refer :all]
            [gov.nist.mfi :refer :all as mfi])
  (:import (java.io StringReader StringWriter)
           (com.hp.hpl.jena.graph Node_URI Node_Blank Node_Literal)
           (com.hp.hpl.jena.sparql.core Quad)
           (org.apache.jena.riot.system StreamRDF)
           (com.hp.hpl.jena.rdf.model ModelFactory AnonId)
           (com.hp.hpl.jena.query DatasetFactory)
           (com.hp.hpl.jena.datatypes BaseDatatype)
           (org.apache.jena.riot RDFDataMgr RDFLanguages)))

(def input1 "$Y = \\beta_0$ ")
(def input2 "$Y = \\beta_1X_1$")
(def input3 "$Y = \\beta_0 + \\beta_1X_1$")
(def input4 "$ F_i = k_c V^{\\alpha_c} f^{\\beta_c} d_i^{\\gamma_c}(t_{w,i} + t)^{\\sigma_c}$")
(def input5 "$  V^{\\alpha} $")
(def input6 "$ (X) $")
(def input7 "$Y = \\beta_0 + \\beta_1X_1 + \\beta_2X_2 + \\beta_3X_3 + \\beta_{12}X_1X_2 + \\beta_{13}X_1X_3 + \\beta_{23}X_2X_3 + \\beta_{11}X_1^2 + \\beta_{22}X_2^2 + \\beta_{33}X_3^2 + experimentalerror$")
(def input8 "$\\frac{1}{2}$")
(def input9 "$\\bar{x}$")
(def input10 "$ x = \\frac{1}{2}$")
(def input11 "$t_{c,i} = \\frac{\\pi \\bar{D_i} L}{1000V f}$") 
            
(defn- simple-test
  [input]
  (let [result (->> input
                    (preprocess-math)
                    (parse :math))]
    (when-let [result (or (:error result) (:math result))]
      (->> result
           ((if (= (type result) gov.nist.mfi.MathExp) math2owl error2owl))
           (map #(edn-ld.core/expand-all context+ %))
           (edn-ld.jena/write-triple-string prefixes)) ; Not used, but I'm interested in problems here.
      @+triples+)))

(deftest expected-triple-count
  (testing "Expected triple count from parsing"
    (is (= 29  (count (simple-test input1))))
    (is (= 39  (count (simple-test input2))))
    (is (= 54  (count (simple-test input3))))
    (is (= 170 (count (simple-test input4))))
    (is (= 15  (count (simple-test input5))))
    (is (= 19  (count (simple-test input6))))
    (is (= 305 (count (simple-test input7))))
    (is (= 33  (count (simple-test input8))))
    (is (= 22  (count (simple-test input9))))
    (is (= 48  (count (simple-test input10))))
    (is (= 99  (count (simple-test input11))))))
