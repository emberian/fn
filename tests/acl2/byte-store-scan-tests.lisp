; Teeth for K1 to K4 (crash model v2, section 3.3).
;
; This book retains the original K1/K2 negative witnesses. The concrete
; metadata attachments now supply a reachable positive witness in
; tests/acl2/byte-store-relation-tests.lisp: a complete first allocation
; reaches a related rename window, and legal old/new crash choices produce
; distinct, successfully scanned frontier images. A local constructor lemma
; connects its executable choice checks to the existential crash predicate.
; Nonempty-history executable witnesses still need the transaction-name
; attachment. The tests below use the early config-entry check and therefore
; do not require concrete codec attachments.
;
; The two hypotheses are (fn-bs-store-relation bs ks) and
; (fn-bs-crash-imagep bs image).  Each tooth below drops exactly one.

(in-package "ACL2")
(include-book "../../books/byte-store-keystones")
(include-book "../../books/byte-store-programs")
(include-book "../../books/byte-store-txn-name")
(include-book "../../books/codec-attach")

; The byte scanner consumes the shared Store-event dispatcher, so one
; immutable namespace may contain a legacy article followed by retention
; state.  These are real FNST frames, not already-decoded sibling values.
(defconst *bsk-event-article*
  (fn-record-make 0 0 0 "<byte-scan@example.invalid>" '(65)
                  '("fn.letters") "archive" "subject" "evidence" 1 841000000))
(defconst *bsk-event-retention*
  (fn-store-retention-event-make :undertake 1 1 1
                                 "obligation-1" "article-0" "local" 1))
; The frames and the stores that hold them are functions, not constants:
; fn-frame-digest and the Store-event record codec are constrained functions
; with executable attachments (books/crypto-attach, books/codec-attach), and
; ACL2 ignores attachments while it evaluates a defconst (the same reason
; tests/acl2/byte-store-relation-tests.lisp builds its witnesses as
; functions).  This book was red on that since the digest
; became constrained.
(defun bsk-event-article-frame ()
  (fn-frame-seal *fn-frame-magic-store* *fn-frame-version*
                 *fn-frame-store-kind*
                 (fn-store-event-encode *bsk-event-article*)))
(defun bsk-event-retention-frame ()
  (fn-frame-seal *fn-frame-magic-store* *fn-frame-version*
                 *fn-frame-store-kind*
                 (fn-store-event-encode *bsk-event-retention*)))
(defun bsk-mixed-event-store ()
  (fn-bs-make 4
              (list (cons 10 (bsk-event-article-frame))
                    (cons 11 (bsk-event-retention-frame)))
              (list (cons :transactions
                          (list (cons (fn-bs-txn-name 0) 10)
                                (cons (fn-bs-txn-name 1) 11))))
              nil 12))
(assert-event (fn-store-event-p *bsk-event-article*))
(assert-event (fn-store-event-p *bsk-event-retention*))
(assert-event
 (equal (fn-bs-read-records (bsk-mixed-event-store) 0 2)
        (list *bsk-event-article* *bsk-event-retention*)))

; Sequence checking is over the generic event accessor.  A valid retention
; event under the wrong immutable filename is rejected rather than silently
; interpreted as an article or accepted by record count alone.
(defconst *bsk-wrong-event-sequence*
  (fn-store-retention-event-make :undertake 7 1 1
                                 "obligation-1" "article-0" "local" 1))
(defun bsk-wrong-event-frame ()
  (fn-frame-seal *fn-frame-magic-store* *fn-frame-version*
                 *fn-frame-store-kind*
                 (fn-store-event-encode *bsk-wrong-event-sequence*)))
(defun bsk-wrong-event-store ()
  (fn-bs-make 4 (list (cons 10 (bsk-wrong-event-frame)))
              (list (cons :transactions
                          (list (cons (fn-bs-txn-name 0) 10)))) nil 11))
(assert-event
 (equal (fn-bs-read-records (bsk-wrong-event-store) 0 1) :fault))

; -----------------------------------------------------------------------------
; The anchor: the clause each tooth violates is TRUE of the store the
; programs run on, so neither tooth is a statement about an impossible
; store (tools/teeth_check.py's predicate-never-anchored).
(assert-event (fn-bs-statep *fn-bs-initialized-store*))
(assert-event (fn-bs-inop (fn-bs-lookup *fn-bs-initialized-store*
                                        :root *fn-bs-scan-config-name*)))
(assert-event (fn-bs-inop (fn-bs-lookup *fn-bs-initialized-store*
                                        :root *fn-bs-scan-frontier-name*)))
(assert-event (fn-bs-dir-quietp *fn-bs-initialized-store* :root))

; -----------------------------------------------------------------------------
; Tooth 1: without (fn-bs-store-relation bs ks).
;
; A store that holds the allocator frontier and an empty transaction
; directory but NO config entry.  It is a well-formed byte store, and
; (fn-bs-crash s nil) is an admissible image of it
; (fn-bs-lose-everything-is-an-admissible-image), so the crash-image
; hypothesis holds -- and the scan of that image faults at :config.  The
; relation's config clause is what K1 needs and nothing else supplies it.
(defconst *bsk-no-config*
  (fn-bs-make 4
              (list (cons 1 *fn-bs-sample-frontier*))
              (list (cons :root (list (cons *fn-bs-scan-frontier-name* 1)))
                    (cons :transactions nil))
              nil 2))
(assert-event (fn-bs-statep *bsk-no-config*))
(assert-event (not (fn-bs-store-relation *bsk-no-config* (fn-sf-initial-state))))
(defconst *bsk-no-config-image* (fn-bs-crash *bsk-no-config* nil))
(assert-event (equal (fn-bs-scan-store *bsk-no-config-image*)
                     (list :fault :config)))
(assert-event (not (fn-bs-scan-okp (fn-bs-scan-store *bsk-no-config-image*))))

; -----------------------------------------------------------------------------
; Tooth 2: without (fn-bs-crash-imagep bs image).
;
; The initialized store with the config entry removed from :root.  The
; store's :root is quiet, so by fn-bs-crash-keeps-quiet-directory every
; admissible image of it has :root's entries unchanged -- this image's do
; not, so no choice list produces it, which is exactly why the hypothesis
; is needed.  Its scan faults at :config.
(defconst *bsk-forged*
  (fn-bs-make (fn-bs-unit *fn-bs-initialized-store*)
              (fn-bs-inodes *fn-bs-initialized-store*)
              (list (cons :parent (list (cons "store" :root)))
                    (cons :root (list (cons *fn-bs-scan-frontier-name* 1)))
                    (cons :transactions nil)
                    (cons :staging nil))
              nil
              (fn-bs-next-ino *fn-bs-initialized-store*)))
(assert-event (fn-bs-statep *bsk-forged*))
(assert-event (not (equal (assoc-equal :root (fn-bs-dirs *bsk-forged*))
                          (assoc-equal :root (fn-bs-dirs
                                              *fn-bs-initialized-store*)))))
(assert-event (equal (fn-bs-scan-store *bsk-forged*) (list :fault :config)))
(assert-event (not (fn-bs-scan-okp (fn-bs-scan-store *bsk-forged*))))

; -----------------------------------------------------------------------------
; K4's scope.  fn-bs-acknowledged-record-survives-byte-crash has no
; reachable instance INSIDE the recovery window, because
; fn-bs-replay-matches-scan carries (equal (fn-sf-successes ks) nil) there
; and the theorem's fourth hypothesis is a member of that list; its live
; instances are the publish window, where the composed runs of
; tests/acl2/byte-store-tests.lisp reach an acknowledged state.  What
; covers the recovery window is fn-bs-crash-image-reopens, which carries no
; success hypothesis at all.  The two phase sets are disjoint and that is
; evaluable here.
(assert-event (not (fn-bs-replay-visiblep (fn-sf-initial-state))))
(assert-event (fn-bs-replay-visiblep
               (fn-sf-make :replaying 0 nil nil nil nil nil 0)))

; The native final-namespace observer consumes these ACL2-issued pairs.  It
; carries sequence 0..n-1 only when every sorted filename is exactly the scan
; codec's name; reordering one reachable two-entry observation is refused.
(assert-event
 (equal (fn-bs-txn-observation-pairs
         (list (fn-bs-txn-name 0) (fn-bs-txn-name 1)) 0)
        (list (list 0 (fn-bs-txn-name 0))
              (list 1 (fn-bs-txn-name 1)))))
(assert-event
 (equal (fn-bs-txn-observation-pairs
         (list (fn-bs-txn-name 1) (fn-bs-txn-name 0)) 0)
        :invalid))
