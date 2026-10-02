; assumptions-recovery.lisp -- A-RECOVERED-OPEN, what the owner's install
; relies on about the checkpoint it opens from (lane raw-dispatch,
; 2026-10-01).  A named assumption is an encapsulate with a local witness
; (books/assumptions.lisp says why).
;
; THE BOUNDARY.  The owner installs from the Store open the host just ran:
; host/owner-host.lisp fn-owner-recover-from-store-open passes
; (fn-ock-install REPLAYED OPENED max-conns) for the pair the open kept in
; the global fn-store-sco-open (host/store-node-host.lisp
; fn-store-sn-open-classified: (list E REPLAYED OPENED), the classified open
; of the extended checkpoint E), and fn-owner-recover-extended passes
; (fn-ock-recover-extended E configs frontier max-conns).  The owner's
; invariant holds of either whenever E is a CAPTURE EXTENSION -- the capture
; of a prefix of the history extended over the rest (KEYSTONE
; fn-lgoc-recover-installs-invariant, books/owner-log-ocl.lisp).  What is
; assumed is that E is one: for a full replay it is so by construction (the
; capture of the empty prefix); from a checkpoint it is the recovery
; refinement's subject, not yet admitted for the store instance
; (PRF-1212/1216, RECOVERY-REFINEMENT-3; under A-CHECKPOINT-PUBLICATION the
; file's tables are a publication's, books/assumptions-publication.lisp),
; and for the pair it is also the host's wiring of the global, which no
; theorem states.  The pessimistic figure is A-CRYPTO-TRAILER's collision
; bound, about 2^-128 per chosen pair of frames, for a checkpoint file that
; verifies and is not the writer's.
;
; Neither predicate is empty: each holds of the empty history's checkpoint
; and its Store open (the last two constraints); and neither is everything:
; tests/acl2/owner-retain-carried-tests.lisp derives, from the producer
; theorems, that each FAILS on a forged checkpoint and on a crossed pair.
; Why it cannot be proved here: the checkpoint is read from a file the host
; did not just write; that its folds are the capture of the history it
; continues is the recovery refinement (open), and that the global holds the
; pair of the open the host ran is the host's wiring (no ACL2 subject).
;
; The theorems that rest on it name it: books/owner-retain-carried.lisp's
; produced premises (def-carried :produced, NAME-FN-P-produced), so raw
; dispatch over the owner row is a claim UNDER A-RECOVERED-OPEN.
;
; Registered: specs/failures.md's A-RECOVERED-OPEN row (this book is not
; included by books/assumptions.lisp: its signature mentions the Store
; open's checkpoint functions, outside that book's closure).

(in-package "ACL2")
(include-book "store-checkpoint-open")

(encapsulate
  (((fn-assume-capture-extensionp * *) => *)
   ((fn-assume-capture-prefix * *) => *)
   ((fn-assume-capture-suffix * *) => *)
   ((fn-assume-store-open-pairp * *) => *)
   ((fn-assume-store-open-e * *) => *)
   ((fn-assume-store-open-configs * *) => *)
   ((fn-assume-store-open-frontier * *) => *))

  (local (defun fn-assume-capture-extensionp (e configs)
           (equal e (fn-sco-extend (fn-sco-capture configs nil) configs nil))))
  (local (defun fn-assume-capture-prefix (e configs) (declare (ignore e configs)) nil))
  (local (defun fn-assume-capture-suffix (e configs) (declare (ignore e configs)) nil))
  (local (defun fn-assume-store-open-e (replayed opened)
           (declare (ignore replayed opened))
           (fn-sco-extend (fn-sco-capture (list *fn-cfg-default-record*) nil)
                          (list *fn-cfg-default-record*) nil)))
  (local (defun fn-assume-store-open-configs (replayed opened)
           (declare (ignore replayed opened))
           (list *fn-cfg-default-record*)))
  (local (defun fn-assume-store-open-frontier (replayed opened)
           (declare (ignore replayed opened))
           0))
  (local (defun fn-assume-store-open-pairp (replayed opened)
           (let ((pair (fn-sco-store-open
                        (fn-sco-extend (fn-sco-capture (list *fn-cfg-default-record*) nil)
                                       (list *fn-cfg-default-record*) nil)
                        (list *fn-cfg-default-record*) 0)))
             (and (equal replayed (car pair)) (equal opened (cadr pair))))))

  ; E is the capture of a prefix of the history, extended over the rest.
  (defthm fn-assume-capture-extension-is-one
    (implies (fn-assume-capture-extensionp e configs)
             (equal e (fn-sco-extend (fn-sco-capture configs (fn-assume-capture-prefix e configs))
                                     configs
                                     (fn-assume-capture-suffix e configs))))
    :rule-classes nil)

  ; The pair is the Store open of a capture extension.
  (defthm fn-assume-store-open-pair-is-an-open
    (implies (fn-assume-store-open-pairp replayed opened)
             (let ((e (fn-assume-store-open-e replayed opened))
                   (configs (fn-assume-store-open-configs replayed opened))
                   (frontier (fn-assume-store-open-frontier replayed opened)))
               (and (fn-assume-capture-extensionp e configs)
                    (equal replayed (car (fn-sco-store-open e configs frontier)))
                    (equal opened (cadr (fn-sco-store-open e configs frontier))))))
    :rule-classes nil)

  ; Not the empty predicate: the empty history's E (the capture of the
  ; empty prefix, extended over nothing) is a capture extension under every
  ; configuration history.
  (defthm fn-assume-capture-extension-of-the-empty-history
    (fn-assume-capture-extensionp (fn-sco-extend (fn-sco-capture configs nil) configs nil)
                                  configs)
    :rule-classes nil)

  ; Nor is the pair predicate empty (r29-F2: interpreted as constantly NIL it
  ; satisfied every other constraint, and the producer theorem over it was
  ; vacuous): the Store open of the empty history under the default
  ; configuration -- the open a fresh store's first start runs -- is a pair
  ; it holds of.  tests/acl2/owner-retain-carried-tests.lisp installs the
  ; owner from exactly this pair and evaluates the producer's conclusion.
  (defthm fn-assume-store-open-pair-of-the-empty-history
    (let ((pair (fn-sco-store-open
                 (fn-sco-extend (fn-sco-capture (list *fn-cfg-default-record*) nil)
                                (list *fn-cfg-default-record*) nil)
                 (list *fn-cfg-default-record*) 0)))
      (fn-assume-store-open-pairp (car pair) (cadr pair)))
    :rule-classes nil))
