; Selected-runtime cold executor allocation bound. A-COLD-RUNTIME is the
; explicit trust boundary; this arithmetic is not an SBCL allocator proof.
(in-package "ACL2")
(defun fn-crt-nth (n x)
  (declare (xargs :guard (natp n)))
  (if (atom x) nil (if (zp n) (car x) (fn-crt-nth (- n 1) (cdr x)))))

; Native facts only: brand/version/architecture/OS, actual persistent thread
; registry node count (including dead nodes), joinable corpses, active starts.
; The enclosing startup is serialized until the admitted workers are ready.
(defun fn-crt-selectedp (runtime)
  (declare (xargs :guard t))
  (and (true-listp runtime) (equal (len runtime) 7)
       (equal (fn-crt-nth 0 runtime) "SBCL")
       (equal (fn-crt-nth 1 runtime) "2.6.8")
       (equal (fn-crt-nth 2 runtime) "X86-64")
       (equal (fn-crt-nth 3 runtime) "Linux")
       (natp (fn-crt-nth 4 runtime))
       (equal (fn-crt-nth 5 runtime) 0)
       (equal (fn-crt-nth 6 runtime) 0)))

; 176 = slot64 + waitqueue32 + list16 + idle ledger row64.
; 64KiB/worker is a sourced conservative margin for thread, closures,
; semaphore/lock/queue, startup vector, signal mask, restart and FFI wrappers.
; Each persistent AVL update allocates <=6 nodes/path level including double
; rotations. Bound path by actual initial registry cardinality + new workers
; +1, retaining both old/new paths. No concurrent creator/CAS retry is assumed.
; Native stacks and runtime mappings are charged separately by fn-crv.
(defun fn-crt-executor-octets (workers runtime)
  (declare (xargs :guard t))
  (* (nfix workers)
     (+ 176 65536 (* 6 48 (+ (nfix (fn-crt-nth 4 runtime))
                             (nfix workers) 1)))))

(in-theory (disable fn-crt-nth fn-crt-selectedp fn-crt-executor-octets))
