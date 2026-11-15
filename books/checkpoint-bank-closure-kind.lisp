(in-package "ACL2")
(include-book "machines-b")
(include-book "checkpoint-bank-closure-state")
(fn2-book-layer :b)
(defcorechild fn2-core-checkpoint-bank-closures fn2-checkpoint-bank-closures
 :init (fn2-checkpoint-bank-closures-init (if (fn2-profile-get :image-boot profile) (fn2-b-capacity :extent-slots 16 profile) 0) fn2-checkpoint-bank-closures)
 :profilep (unsigned-byte-p 32 (* 4 (if (fn2-profile-get :image-boot profile) (fn2-b-capacity :extent-slots 16 profile) 0)))
 :why "Independent typed closure capture per physical anchor before investigation scratch reuse, sized by the actual extent profile.")
