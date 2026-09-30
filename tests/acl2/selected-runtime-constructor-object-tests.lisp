(in-package "ACL2")
(include-book "../../books/assumptions-selected-runtime-constructor-objects")
(defthm fn-sroct-actual-object-rows
 (and (= (fn-sroc-object-request :pool-three) 48)
      (= (fn-sroc-object-request :rx-foundation) 48)
      (= (fn-sroc-object-request :native-job-twenty) 176)
      (= (fn-sroc-object-request :input-copy-ten) 96)
      (= (fn-sroc-object-request :digest-sixteen-with-frames) 672)
      (= (fn-sroc-object-request :extent-direct-16384) 16400))
 :rule-classes nil)
(defthm fn-sroct-exact-controller-coordinate
 (equal (fn-sroc-object-row-status :input-copy-ten
  "d2eb01cd26877ceca1ffa053dc74742e20124973f97a3fbbec72dbc249a4d62a"
  *fn-srp-selected-coordinate*) :object-row)
 :rule-classes nil)
; Metadata mutations, not counterexamples to an opaque physical assumption.
(defthm fn-sroct-old-job-is-unavailable
 (equal (fn-sroc-object-row-status :native-job-nineteen
  "old" *fn-srp-selected-coordinate*) :unavailable) :rule-classes nil)
(defthm fn-sroct-wrong-source-is-unavailable
 (equal (fn-sroc-object-row-status :input-copy-ten
  "old" *fn-srp-selected-coordinate*) :unavailable) :rule-classes nil)
(defthm fn-sroct-wrong-runtime-is-unavailable
 (equal (fn-sroc-object-row-status :input-copy-ten
  "d2eb01cd26877ceca1ffa053dc74742e20124973f97a3fbbec72dbc249a4d62a"
  nil) :unavailable) :rule-classes nil)
