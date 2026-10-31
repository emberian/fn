; Run: env FN_ACL2_SLOT_DIR="$PWD/build/fn2-b-acl2-slots" FN_ACL2_SLOTS=4 timeout -k 5 240 tools/acl2 < fn2/tests/alloc-random.lsp
(in-package "ACL2")
(set-prover-step-limit 5000000)
(set-cbd "fn2/tests/")
(ld "alloc-random.lisp" :ld-error-action :error)
:q
(handler-case
    (progn
      (let ((*hard-error-is-error* t) (*hard-error-returns-nilp* nil))
        (dolist (kind '(:counter))
          (assert (handler-case (progn (fn2-alloc-test-corruption kind) nil)
                    (cl:error () t))))
        (dolist (kind '(:saturated :zero))
          (assert (handler-case (progn (fn2-alloc-test-edge-corruption kind) nil)
                    (cl:error () t)))))
      (format t "ALLOC ASSERTIONS: accounting underflow and inconsistent edge counts fail loudly PASS~%")
      (assert (equal (fn2-alloc-random-all) t))
      (sb-ext:exit :code 0))
  (cl:error (condition)
    (format *error-output* "ALLOC RANDOM ERROR: ~A~%" condition)
    (sb-ext:exit :code 1)))
