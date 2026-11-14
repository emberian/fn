; Whole-state evidence for the production transaction child callback candidate.
(in-package "ACL2")
(include-book "../books/assembly-callbacks-d-txn-children")
(include-book "../books/square-evidence")
(include-book "core-snapshot-support")

(defconst *fn2-txn-child-wake-profile*
 (put-assoc-equal :posting-interim t
  (put-assoc-equal :large-upload-windows 1
   (put-assoc-equal :pool-classes '((8 . 1024) (16 . 4096) (8 . 65536))
                    *fn2-profile-tiny*))))
(defun fn2-txn-child-wake-setup (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (let* ((fn2-core (fn2-core-init *fn2-txn-child-wake-profile* fn2-core))
        (u (fn2-machine-kind-base *fn2-upload-kind* fn2-core))
        (tx (fn2-machine-kind-base *fn2-txn-kind* fn2-core))
        (gen (fn2-machine-generation tx fn2-core))
        (ugen (fn2-machine-generation u fn2-core))
        (fn2-core (fn2-upload-put-core u (phase *fn2-upload-state-draining*)
                                        (txn tx) (txn-gen gen)))
        (fn2-core (fn2-txn-put-core tx (phase *fn2-txn-state-draining*)
                                     (upload u) (upload-gen ugen))))
  (fn2-machine-set-wake-id *fn2-none* fn2-core)))
; Same actual source guard and ABI; the mutation drops the wake effect.
(defun fn2-txn-child-wake-drop (u id gen fn2-core)
 (declare (ignore u id gen)
          (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
 fn2-core)
(defun fn2-txn-child-wake-input ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (image fn2-core)
   (let* ((fn2-core (fn2-txn-child-wake-setup fn2-core))
          (u (fn2-machine-kind-base *fn2-upload-kind* fn2-core)))
    (let ((tx (fn2-machine-kind-base *fn2-txn-kind* fn2-core)))
     (mv (list u tx (fn2-machine-generation tx fn2-core)
               (fn2-test-core-snapshot fn2-core)) fn2-core)))
   image)))
(defconst *fn2-txn-child-wake-input* (fn2-txn-child-wake-input))

(defun fn2-txn-child-wake-observations ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (answer fn2-core)
   (let* ((fn2-core (fn2-txn-child-wake-setup fn2-core))
          (u (fn2-machine-kind-base *fn2-upload-kind* fn2-core))
          (tx (fn2-machine-kind-base *fn2-txn-kind* fn2-core))
          (gen (fn2-machine-generation tx fn2-core))
          (before (fn2-test-core-snapshot fn2-core))
          (pre (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                    (fn2-machine-idp u fn2-core)
                    (eq (fn2-upload-snapshot-read-code u fn2-core) :ok)
                    (equal (fn2-upload-row-txn u fn2-core) tx)
                    (equal (fn2-upload-row-txn-gen u fn2-core) gen)
                    (fn2-machine-idp tx fn2-core)
                    (equal (fn2-txn-row-upload tx fn2-core) u)))
          (fn2-core (fn2-txn-wake-upload u tx gen fn2-core))
          (source (fn2-test-core-snapshot fn2-core))
          (source-wake (fn2-machine-wake-id fn2-core))
          (fn2-core (fn2-txn-child-wake-setup fn2-core))
          (fn2-core (fn2-txn-wake-upload-child-core-face u tx gen fn2-core))
          (child (fn2-test-core-snapshot fn2-core))
          (child-wake (fn2-machine-wake-id fn2-core))
          (fn2-core (fn2-txn-child-wake-setup fn2-core))
          (fn2-core (fn2-txn-wake-upload-child-core-face u tx (if (zp gen) 1 (1- gen)) fn2-core))
          (refused (fn2-test-core-snapshot fn2-core))
          (fn2-core (fn2-txn-child-wake-setup fn2-core))
          (fn2-core (fn2-txn-child-wake-drop u tx gen fn2-core))
          (mutant (fn2-test-core-snapshot fn2-core)))
    (mv (list (and pre (equal source child) (equal source-wake u)
                   (equal child-wake u) (not (equal source before))
                   (equal refused before))
              (and pre (equal mutant before) (not (equal mutant source))))
        fn2-core))
   answer)))
(defun fn2-txn-child-wake-positive ()
 (declare (xargs :verify-guards nil))
 (car (fn2-txn-child-wake-observations)))
(defun fn2-txn-child-wake-negative ()
 (declare (xargs :verify-guards nil))
 (cadr (fn2-txn-child-wake-observations)))
(assert-event (equal (fn2-txn-child-wake-observations) '(t t)))

; Existing evidence API: constructor execution produces an ordinary value;
; the emitted bindings are quoted literals and the shared generator proves
; the actual live statement, guards and mutation. Runtime teeth stay separate.
(make-event
 (let* ((bindings (list (list 'u (list 'quote (car *fn2-txn-child-wake-input*)))
                       (list 'id (list 'quote (cadr *fn2-txn-child-wake-input*)))
                       (list 'gen (list 'quote (caddr *fn2-txn-child-wake-input*)))
                       (list 'fn2-core (list 'quote (cadddr *fn2-txn-child-wake-input*)))))
        (negative (list :kind :mutation
                        :at 'fn2-txn-wake-upload-child-exec-core-face
                        :replace 'fn2-txn-child-wake-drop :bindings bindings)))
  (value (fn2-square-evidence-events
           'fn2-txn-wake-upload-child-guarded-execution-refines-core
           bindings negative nil (w state)))))
(make-event
 (let* ((bindings (list (list 'u (list 'quote (car *fn2-txn-child-wake-input*)))
                       (list 'id (list 'quote (cadr *fn2-txn-child-wake-input*)))
                       (list 'gen (list 'quote (caddr *fn2-txn-child-wake-input*)))
                       (list 'fn2-core (list 'quote (cadddr *fn2-txn-child-wake-input*)))))
        (negative (list :kind :mutation
                        :at 'fn2-txn-wake-upload-child-core-face
                        :replace 'fn2-txn-child-wake-drop :bindings bindings)))
  (value (fn2-square-evidence-events
           'fn2-txn-wake-upload-child-refines-core
           bindings negative nil (w state)))))
(fn2-assert-square-evidence fn2-txn-wake-upload-child-guarded-execution-refines-core)
(fn2-assert-square-evidence fn2-txn-wake-upload-child-refines-core)
