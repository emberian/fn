; Extend the actual core's pre-index registration with the canonical semantic
; singleton and extent-indexed DFS work. No alternate CORE or actor is declared.
(in-package "ACL2")
(include-book "checkpoint-restore-semantic-work")
(fn2-book-layer :c)
(defcorechild fn2-core-checkpoint-restore-semantic fn2-checkpoint-restore-semantic
 :init (fn2-checkpoint-restore-semantic-init 1 fn2-checkpoint-restore-semantic)
 :profilep t
 :why "The actual cold root1 reader retains descriptor, full page Ref and cursor across sector reads.")
(defcorechild fn2-core-checkpoint-restore-semantic-work fn2-checkpoint-restore-semantic-work
 :init (fn2-checkpoint-restore-semantic-work-init (fn2-b-capacity :extent-slots 16 profile) fn2-checkpoint-restore-semantic-work)
 :profilep (unsigned-byte-p 32 (fn2-b-capacity :extent-slots 16 profile))
 :why "One exact identity/color/parent cursor row per admitted extent; DFS closes only after descendants and payload.")
