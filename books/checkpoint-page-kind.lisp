; Central registration of the single shared physical page worker and carriers.
; Source producers never provision their own copy of these resources.
(in-package "ACL2")
(include-book "checkpoint-page-worker")
(fn2-book-layer :c)
(defcorechild fn2-core-checkpoint-page fn2-checkpoint-page
 :init (fn2-checkpoint-page-init 1 fn2-checkpoint-page) :profilep t
 :harvest (fn2-checkpoint-page-harvest
           ((fn2-core-checkpoint-page fn2-checkpoint-page)
            (fn2-core-csnapshot fn2-csnapshot)
            (fn2-core-checkpoint-construction fn2-checkpoint-construction)
            (fn2-core-extents fn2-extents)
            (fn2-core-checkpoint-page-verified fn2-checkpoint-page-verified)))
 :why "One generated owner retains exact physical page operation identities through validated harvest and handback.")
(defcorechild fn2-core-checkpoint-page-verified fn2-checkpoint-page-verified
 :init (fn2-checkpoint-page-verified-init (fn2-b-capacity :extent-slots 16 profile) fn2-checkpoint-page-verified)
 :profilep (unsigned-byte-p 32 (fn2-b-capacity :extent-slots 16 profile))
 :why "Verified identity, actual hash and physical completion for each actual allocator extent, shared by every root producer.")
