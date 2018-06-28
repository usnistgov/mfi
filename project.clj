(defproject gov.nist/mfi "0.1.0-SNAPSHOT"
  :description "A library to create OWL statements from latex; MFI=mathematically formulated information"
  :url "https://github.com/usnistgov/mfi"
  :license {:name "Eclipse Public License"
            :url "http://www.eclipse.org/legal/epl-v10.html"}
  :profiles {:uberjar {:aot :all}}
  :plugins [[lein-bin "0.3.4"]
            [lein-cljfmt "0.5.3"]]
  :dependencies [[org.clojure/clojure "1.8.0"]
                 [edn-ld "0.2.1"]]
  :bin {:name "mfi"
        :bin-path "~/bin"
        :bootclasspath true}
  :main gov.nist.main)

  
