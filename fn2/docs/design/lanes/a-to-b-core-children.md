Signature: `(defcorechild field stobj &key init profilep why (reference :state) (order :extension))`; `:environment` excludes difference and requires `:why`.
Include `fn2/books/core-children` in B's registration book; define the child stobj and its profile/init adapters there.
Add B's registration/kind book after `machines-all` in `fn2/books/assembly.lisp`, before `(fn2-machine-index-events)`; include B continuation event macros before final dispatch.
Example: `(defcorechild fn2-core-extents fn2-extents :init (fn2-extents-init-for profile fn2-extents) :profilep (fn2-extents-profilep profile) :why "Allocator state persists across commit yields.")`.
Init takes only profile and its child, returns that child, and is guard-verifiable from the combined profile predicate; continuations use `(stobj-let ((fn2-extents (fn2-core-extents fn2-core))) ...)`.
