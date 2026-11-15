; Checkpoint scratch capacity is an admission profile, not a stored-data cap.
(in-package "ACL2")
(include-book "checkpoint-catalog-kind")
(include-book "checkpoint-installed")
(include-book "checkpoint-construction")
(include-book "checkpoint-lifecycle")
(include-book "checkpoint-summary-authority-state")
(include-book "checkpoint-directory-rebase-state")
(fn2-book-layer :b)





(defcorechild fn2-core-checkpoint-publication fn2-checkpoint-publication
 :init (fn2-checkpoint-publication-init 1 fn2-checkpoint-publication)
 :profilep t
 :harvest (fn2-checkpoint-publication-harvest
           ((fn2-core-checkpoint-publication fn2-checkpoint-publication)))
 :why "One checkpoint bank writer keeps exact operation identities through physical harvest.")

(defcorechild fn2-core-checkpoint-lifecycle fn2-checkpoint-lifecycle
 :init (fn2-checkpoint-lifecycle-init 1 fn2-checkpoint-lifecycle) :profilep t
 :why "One physical completion/retention cursor binds the live checkpoint owner through publication and thaw.")
(include-book "checkpoint-writer")

(defcorechild fn2-core-checkpoint-summary-authority fn2-checkpoint-summary-authority
 :init (fn2-checkpoint-summary-authority-init 2 fn2-checkpoint-summary-authority)
 :profilep t :why "Exact cold/live sufficient-summary subject, retained frontier and predecessor after the real C consumer completes; distinct from selected-source projection provenance.")

(defcorechild fn2-core-checkpoint-directory-rebase fn2-directory-rebase
 :init (fn2-directory-rebase-init 1 fn2-directory-rebase) :profilep t
 :why "One owner-bound bounded scan joins actual summary consumption to the live directory base and preserved suffix.")
