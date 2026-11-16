; Exact canonical candidate/catalog closure-hold registration.
(in-package "ACL2")
(include-book "machines-b")
(include-book "checkpoint-cbase-state")
(fn2-book-layer :b)
(defcorechild fn2-core-checkpoint-cbase-holds fn2-checkpoint-cbase-holds
 :init (fn2-checkpoint-cbase-holds-init (fn2-b-checkpoint-capacity profile) fn2-checkpoint-cbase-holds)
 :profilep (unsigned-byte-p 32 (fn2-b-checkpoint-capacity profile))
 :why "One exact candidate/catalog C-source promise retains its actual closure through replacement and query drain.")
