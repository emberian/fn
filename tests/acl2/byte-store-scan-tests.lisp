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
(include-book "../../books/byte-store-relation")
(include-book "../../books/byte-store-txn-name")
(include-book "../../books/byte-store-frame")
(include-book "../../books/codec-attach")
(include-book "consumer-store-invariants-tests")
(include-book "std/testing/must-fail" :dir :system)

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

; E2/K4: an initial byte image and its actual modeled death have a strict
; consumer replay at the host reopen entry.  The bridge proves this from the
; maintained completed-prefix relation and K2's scanned kernel image; no
; host-side consumer predicate is assumed over the observed record list.
(defun bsk-e2-initial-node () (fn-sn-initial nil 10))
(defun bsk-e2-initial-store ()
  (fn-bs-initial-image 4 (fn-bs-initial-config-octets)
                        (fn-bs-initial-frontier-octets)))
(defun bsk-e2-initial-crash ()
  (fn-bs-crash (bsk-e2-initial-store) nil))
(assert-event (fn-csi-full-relationp (bsk-e2-initial-node)))
(assert-event
 (fn-bs-store-relation (bsk-e2-initial-store)
                       (fn-sn-files (bsk-e2-initial-node))))
(defthm bsk-e2-initial-crash-admissible
  (fn-bs-crash-imagep (bsk-e2-initial-store)
                      (bsk-e2-initial-crash))
  :hints (("Goal"
           :use ((:instance fn-bs-lose-everything-is-an-admissible-image
                            (s (bsk-e2-initial-store)))))))
(assert-event
 (fn-sn-observed-consumer-okp
  (fn-bs-scan-records (fn-bs-scan-store (bsk-e2-initial-crash)))))
(assert-event
 (fn-sn-observed-topic-okp
  (fn-bs-scan-records (fn-bs-scan-store (bsk-e2-initial-crash)))))
(assert-event
 (fn-sn-open-okp
  (fn-sn-open-observed
   (fn-sn-groups (bsk-e2-initial-node))
   (fn-sn-capacity (bsk-e2-initial-node))
   (fn-bs-scan-frontier (fn-bs-scan-store (bsk-e2-initial-crash)))
   (fn-bs-scan-records (fn-bs-scan-store (bsk-e2-initial-crash))))))

; A nonempty consumer image: the same bootstrap event goes through the
; actual Store-node trace and the actual byte frontier/P-RECORD/finish
; programs.  The final byte image contains its FNST frame and reopens with
; a reconstructed consumer projection.
(defun bsk-e2-bootstrap-frame ()
  (fn-frame-seal *fn-frame-magic-store* *fn-frame-version*
                 *fn-frame-store-kind* (fn-store-event-encode *csnt-boot*)))
(defun bsk-e2-frontier-pair ()
  (car (last (fn-bs-run (bsk-e2-initial-store)
                        (fn-sn-files *csnt-initial*)
                        (fn-bs-frontier-program ".allocation-e2"
                                                (fn-bs-frontier-encode 1))
                        nil '("g") 32))))
(defun bsk-e2-bootstrap-record-pair ()
  (let ((pair (bsk-e2-frontier-pair)))
    (car (last
          (fn-bs-run (car pair)
                     (fn-sn-files
                      (fn-sn-prepare-consumer (csnt-reserve *csnt-initial*)
                                              *csnt-boot*))
                     (fn-bs-record-program ".stage-e2" (fn-bs-txn-name 0)
                                           (bsk-e2-bootstrap-frame))
                     nil '("g") 32)))))
(defun bsk-e2-bootstrap-finished-pair ()
  (let ((pair (bsk-e2-bootstrap-record-pair)))
    (car (last (fn-bs-run (car pair) (cdr pair)
                            (fn-bs-finish-program 0 0) nil '("g") 32)))))
(defun bsk-e2-bootstrap-image ()
  (fn-bs-crash (car (bsk-e2-bootstrap-finished-pair)) nil))
(assert-event
 (let* ((pair (bsk-e2-bootstrap-finished-pair))
        (s (fn-snrt-run *csnt-initial* *csit-boot-trace*))
        (scan (fn-bs-scan-store (bsk-e2-bootstrap-image))))
   (and (fn-csi-full-relationp s)
        (equal s *csnt-after-boot*)
        (equal (cdr pair) (fn-sn-files s))
        (fn-bs-store-relation (car pair) (fn-sn-files s))
        (fn-bs-crash-choicesp nil (fn-bs-pending (car pair))
                              (fn-bs-unit (car pair)))
        (equal (fn-bs-scan-records scan) (list *csnt-boot*))
        (fn-sn-observed-consumer-okp (fn-bs-scan-records scan))
        (fn-sn-observed-topic-okp (fn-bs-scan-records scan))
        (fn-sn-open-okp
         (fn-sn-open-observed '("g") 32
                              (fn-bs-scan-frontier scan)
                              (fn-bs-scan-records scan))))))

; Removing the maintained consumer-prefix relation is unsound even when
; the file kernel and byte store agree.  This old structurally framed
; registration is accepted by the file program, but E2 refuses its replay
; because no bootstrap precedes it.  The Store-node's checked prepare path
; cannot reach this state; that is precisely the invariant the theorem uses.
(defun bsk-e2-invalid-frame ()
  (fn-frame-seal *fn-frame-magic-store* *fn-frame-version*
                 *fn-frame-store-kind*
                 (fn-store-event-encode *csit-register-before-bootstrap*)))
(defun bsk-e2-invalid-record-pair ()
  (let ((pair (bsk-e2-frontier-pair)))
    (car (last
          (fn-bs-run (car pair)
                     (fn-sf-prepare-record
                      (cdr pair) *csit-register-before-bootstrap* '("g") 32)
                     (fn-bs-record-program ".stage-e2-invalid"
                                           (fn-bs-txn-name 0)
                                           (bsk-e2-invalid-frame))
                     nil '("g") 32)))))
(defun bsk-e2-invalid-finished-pair ()
  (let ((pair (bsk-e2-invalid-record-pair)))
    (car (last (fn-bs-run (car pair) (cdr pair)
                            (fn-bs-finish-program 0 0) nil '("g") 32)))))
(defun bsk-e2-invalid-image ()
  (fn-bs-crash (car (bsk-e2-invalid-finished-pair)) nil))
(defun bsk-e2-invalid-node ()
  (fn-sn-update *csnt-initial* (cdr (bsk-e2-invalid-finished-pair))
                (fn-sn-node *csnt-initial*)))
(assert-event
 (equal (cdr (bsk-e2-invalid-finished-pair))
        (fn-sn-files (bsk-e2-invalid-node))))
(assert-event
 (fn-bs-store-relation (car (bsk-e2-invalid-finished-pair))
                       (fn-sn-files (bsk-e2-invalid-node))))
(assert-event
 (fn-bs-crash-choicesp nil
                       (fn-bs-pending (car (bsk-e2-invalid-finished-pair)))
                       (fn-bs-unit (car (bsk-e2-invalid-finished-pair)))))
(assert-event (not (fn-csi-full-relationp (bsk-e2-invalid-node))))
(assert-event
 (equal (fn-bs-scan-records (fn-bs-scan-store (bsk-e2-invalid-image)))
        (list *csit-register-before-bootstrap*)))
(assert-event
 (not (fn-sn-observed-consumer-okp
       (fn-bs-scan-records (fn-bs-scan-store (bsk-e2-invalid-image))))))
(defthm bsk-e2-invalid-crash-admissible
  (fn-bs-crash-imagep (car (bsk-e2-invalid-finished-pair))
                      (bsk-e2-invalid-image))
  :hints (("Goal"
           :use ((:instance fn-bs-lose-everything-is-an-admissible-image
                            (s (car (bsk-e2-invalid-finished-pair))))))))

; Tooth for the maintained E2 relation.  The byte/kernel relation and
; modeled crash premise are both true at this actual physical program cut;
; only the node's checked consumer-prefix relation is absent.
(must-fail
 (assert-event
  (implies (and (fn-bs-store-relation
                 (car (bsk-e2-invalid-finished-pair))
                 (fn-sn-files (bsk-e2-invalid-node)))
                (fn-bs-crash-choicesp
                 nil (fn-bs-pending (car (bsk-e2-invalid-finished-pair)))
                 (fn-bs-unit (car (bsk-e2-invalid-finished-pair)))))
           (fn-sn-observed-consumer-okp
            (fn-bs-scan-records (fn-bs-scan-store
                                 (bsk-e2-invalid-image)))))))

; Tooth for the byte/kernel relation: a valid committed bootstrap node is
; paired with the invalid registration byte image.  The image is a legal
; crash of its own byte state but not related to that node's record history.
(assert-event
 (not (fn-bs-store-relation
       (car (bsk-e2-invalid-finished-pair))
       (fn-sn-files *csnt-after-boot*))))
(must-fail
 (assert-event
  (implies (and (fn-csi-full-relationp *csnt-after-boot*)
                (fn-bs-crash-choicesp
                 nil (fn-bs-pending (car (bsk-e2-invalid-finished-pair)))
                 (fn-bs-unit (car (bsk-e2-invalid-finished-pair)))))
           (fn-sn-observed-consumer-okp
            (fn-bs-scan-records (fn-bs-scan-store
                                 (bsk-e2-invalid-image)))))))

; Tooth for the modeled crash-image premise: the valid bootstrap byte state
; is related to its node, but the independently produced registration image
; has different framed content and fails consumer replay.
(must-fail
 (assert-event
  (implies (and (fn-csi-full-relationp *csnt-after-boot*)
                (fn-bs-store-relation
                 (car (bsk-e2-bootstrap-finished-pair))
                 (fn-sn-files *csnt-after-boot*)))
           (fn-sn-observed-consumer-okp
            (fn-bs-scan-records (fn-bs-scan-store
                                 (bsk-e2-invalid-image)))))))
(must-fail
 (assert-event
  (fn-sn-observed-consumer-okp
   (fn-bs-scan-records (fn-bs-scan-store (bsk-e2-invalid-image))))))

; K4 topic tooth: a syntactically valid topic anchor follows the completed
; consumer bootstrap.  Its authorization reference names no historical
; accepted article, so the independent topic projection faults at historical
; authorship.  The frame, filename, frontier and crash are produced by the
; actual byte programs; this is not a malformed scan or a sequence gap.  The
; node below is the exact generic Store/identity/consumer replay projection
; of those files.  It is a relation witness, not a served topic-prepare trace;
; proving the latter maintains the topic prefix is the open shared bridge.
(defconst *bsk-topic-source-id*
  (fn-id-subject (make-list 32 :initial-element 7)))
(defconst *bsk-topic-root-id* (make-list 32 :initial-element 8))
(defconst *bsk-topic-unbound-anchor*
  (list :topic-anchor 1 1 1 *bsk-topic-source-id*
        (list 0 0 *bsk-topic-source-id* 0 0 *fn-hsig-profile-tag*)
        1 *bsk-topic-root-id*))
(assert-event (fn-th-topic-eventp *bsk-topic-unbound-anchor*))
(assert-event (fn-store-event-p *bsk-topic-unbound-anchor*))
(defun bsk-topic-anchor-frame ()
  (fn-frame-seal *fn-frame-magic-store* *fn-frame-version*
                 *fn-frame-store-kind*
                 (fn-store-event-encode *bsk-topic-unbound-anchor*)))
(defun bsk-topic-frontier-pair ()
  (let ((pair (bsk-e2-bootstrap-finished-pair)))
    (car (last (fn-bs-run (car pair) (cdr pair)
                          (fn-bs-frontier-program ".allocation-topic-tooth"
                                                  (fn-bs-frontier-encode 2))
                          nil '("g") 32)))))
(defun bsk-topic-record-pair ()
  (let ((pair (bsk-topic-frontier-pair)))
    (car (last
          (fn-bs-run (car pair)
                     (fn-sf-prepare-record (cdr pair)
                                           *bsk-topic-unbound-anchor* '("g") 32)
                     (fn-bs-record-program ".stage-topic-tooth"
                                           (fn-bs-txn-name 1)
                                           (bsk-topic-anchor-frame))
                     nil '("g") 32)))))
(defun bsk-topic-finished-pair ()
  (let ((pair (bsk-topic-record-pair)))
    (car (last (fn-bs-run (car pair) (cdr pair)
                            (fn-bs-finish-program 1 1) nil '("g") 32)))))
(defun bsk-topic-image ()
  (fn-bs-crash (car (bsk-topic-finished-pair)) nil))
(defun bsk-topic-node ()
  (let* ((files (cdr (bsk-topic-finished-pair)))
         (records (fn-sf-records files))
         (node (fn-sf-replay-node '("g") 32 records
                                  (fn-sf-frontier files)))
         (consumer (cadr (fn-cpe-projection-replay nil records 0)))
         (s (fn-sn-update *csnt-after-boot* files node)))
    (update-nth 11 consumer (update-nth 9 2 s))))
(defthm bsk-topic-image-is-an-admissible-crash
  (fn-bs-crash-imagep (car (bsk-topic-finished-pair))
                      (bsk-topic-image))
  :hints (("Goal"
           :use ((:instance fn-bs-lose-everything-is-an-admissible-image
                            (s (car (bsk-topic-finished-pair))))))))
(assert-event
 (let* ((pair (bsk-topic-finished-pair))
        (s (bsk-topic-node))
        (scan (fn-bs-scan-store (bsk-topic-image)))
        (records (fn-bs-scan-records scan)))
   (and (fn-csi-full-relationp s)
        (fn-bs-store-relation (car pair) (fn-sn-files s))
        (fn-bs-crash-choicesp nil (fn-bs-pending (car pair))
                              (fn-bs-unit (car pair)))
        (equal records (list *csnt-boot* *bsk-topic-unbound-anchor*))
        (fn-sn-observed-consumer-okp records)
        (fn-sn-observed-identity-okp records)
        (not (fn-sn-observed-topic-okp records))
        (not (fn-sn-open-okp
              (fn-sn-open-observed (fn-sn-groups s) (fn-sn-capacity s)
                                   (fn-bs-scan-frontier scan) records))))))
(must-fail
 (assert-event
  (let* ((s (bsk-topic-node))
         (scan (fn-bs-scan-store (bsk-topic-image))))
    (fn-sn-open-okp
     (fn-sn-open-observed
      (fn-sn-groups s) (fn-sn-capacity s)
      (fn-bs-scan-frontier scan) (fn-bs-scan-records scan))))))

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
