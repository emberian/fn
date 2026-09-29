; fn: witnesses and teeth for books/store-reclaim-pack.lisp (STO-017,
; PRF-119): the per-article rewrite `store reclaim' checkpoints.
(in-package "ACL2")
(include-book "../../books/store-reclaim-pack")
(include-book "must-fail-checked")
(include-book "owner-served-invariants-tests")
(include-book "../../books/byte-store-frame")

; The owner fixture's store after its article completed (as in
; store-reclaim-holders-tests), its committed history as octets, and the
; one article.
(defconst *rpt-s* (fn-own-store (cdr (osi-finish *osi-completing* *osi-cfg* *osi-completing-prior*))))

; The arena of the fixture's history (audit-fixes, 2026-09-27): the payloads
; the host's entry interned from the owner's journal, in handle order, so
; that sealing them in order rebuilds the arena its articles' handles name.
(defun rcl-prior-payloads (prior i fuel)
  (declare (xargs :verify-guards nil :measure (nfix fuel)))
  (if (zp fuel)
      nil
    (let ((b (fn-hrt-bytes prior i)))
      (if (consp b)
          (cons b (rcl-prior-payloads prior (+ 1 i) (- fuel 1)))
        nil))))
(defconst *rpt-payloads* (rcl-prior-payloads *osi-completing-prior* 0 64))
(bpr-lift fn-rcl-store-counts 3)
(defun rpt-encode-all (rs)
  (declare (xargs :mode :program))
  (if (consp rs) (cons (fn-store-event-encode (car rs)) (rpt-encode-all (cdr rs))) nil))
; by specification: the flip: the history retains rows; the committed
; history's octets are the WIRE events they stand for (alpha through the
; arena that interned the journal), encoded.
(defconst *rpt-wire* (fn-hrt-wire-of *osi-completing-prior* (fn-sf-records (fn-sn-files *rpt-s*))))
(defmacro rpt-events () '(rpt-encode-all *rpt-wire*))
(defconst *rpt-art* (car (fn-state-articles (fn-node-acceptance (fn-sn-node *rpt-s*)))))
(defconst *rpt-msgid* (fn-article-msgid *rpt-art*))
(defconst *rpt-rule* '(:released-by-all-holders))
(defconst *rpt-ctx* (fn-rclp-ctx *rpt-rule* 0 *rpt-s*))
(defmacro rpt-new () '(fn-rclp-events (rpt-events) *rpt-ctx*))
; The index of the article's record in the history.
(defun rpt-index (events msgid i)
  (declare (xargs :mode :program))
  (if (consp events)
      (let ((d (fn-record-decode-exact (car events))))
        (if (and (fn-record-result-okp d)
                 (equal (fn-record-msgid (fn-record-result-record d)) msgid))
            i
          (rpt-index (cdr events) msgid (1+ i))))
    nil))
(defmacro rpt-i () '(rpt-index (rpt-events) *rpt-msgid* 0))

; The history is a nonempty summary event list, the article is reclaimable
; with no holder under the releasing rule, and its record is rewritten.
(assert-event (and (natp (rpt-i)) (< 1 (len (rpt-events)))
                   (fn-cc-octet-event-listp (rpt-events) 0 0 (len (rpt-events)))))
(assert-event (fn-rclp-rewrites-p (nth (rpt-i) (rpt-events)) *rpt-ctx*))
; The fixture's three articles carry no holder and an :absent verdict: all
; three are rewritten, in history order.
(defmacro rpt-msgids () '(fn-rclp-rewritten-msgids (rpt-events) *rpt-ctx*))
(assert-event (and (equal (len (rpt-msgids)) 3)
                   (member-equal *rpt-msgid* (rpt-msgids))))

; fn-rclp-event-decodes-to-the-tombstoned-record: witness.
(defmacro rpt-old () '(fn-record-result-record
                     (fn-record-decode-exact (nth (rpt-i) (rpt-events)))))
(defmacro rpt-dec () '(fn-record-decode-exact (nth (rpt-i) (rpt-new))))
(assert-event (and (fn-record-result-okp (rpt-dec))
                   (fn-rcl-tombstonep (fn-record-payload (fn-record-result-record (rpt-dec))))
                   (equal (fn-record-result-record (rpt-dec)) (fn-rclp-tombstoned (rpt-old)))
                   (not (equal (nth (rpt-i) (rpt-new)) (nth (rpt-i) (rpt-events))))))
; Tooth (rewrites-p): an event that is not rewritten decodes to itself,
; so the conclusion (a tombstone payload) fails for it.
(must-fail-checked (assert-event (fn-rcl-tombstonep
                          (fn-record-payload
                           (fn-record-result-record
                            (fn-record-decode-exact
                             (fn-rclp-event (nth (rpt-i) (rpt-events))
                                            (fn-rclp-ctx '(:keep-forever) 0 *rpt-s*))))))))

; fn-rclp-events-keep-the-summary-shape: witness; tooth (the hypothesis): a
; list that is not a summary list (a byte dropped) stays not one.
(assert-event (fn-cc-octet-event-listp (rpt-new) 0 0 (len (rpt-events))))
(must-fail-checked (assert-event (fn-cc-octet-event-listp
                          (fn-rclp-events (list (cdr (nth (rpt-i) (rpt-events)))) *rpt-ctx*)
                          0 0 (len (rpt-events)))))

; fn-rclp-events-idempotent: witness (a second pass under any context).
(assert-event (equal (fn-rclp-events (rpt-new) *rpt-ctx*) (rpt-new)))
(assert-event (equal (fn-rclp-rewritten-msgids (rpt-new) *rpt-ctx*) nil))

; fn-rclp-events-never-touch-a-held-article: witness per disjunct, and the
; conclusion fails with none of them (the releasing rule, no holder).
; (1) a BP obligation names the article.
(defconst *rpt-articles* (fn-state-articles (fn-node-acceptance (fn-sn-node *rpt-s*))))
(defconst *rpt-bp* (list *rpt-rule* 0 (list nil nil nil (list *rpt-msgid*))
                         nil *rpt-articles* nil (fn-rclp-article-index *rpt-articles*)))
(assert-event (fn-rcl-some-names-p (fn-rcl-obligations (nth 2 *rpt-bp*)) *rpt-msgid*
                                   (fn-article-memberships *rpt-art*)))
(assert-event (equal (nth (rpt-i) (fn-rclp-events (rpt-events) *rpt-bp*))
                     (nth (rpt-i) (rpt-events))))
; (2) the verdict list needs its payload.
(defconst *rpt-vd* (list *rpt-rule* 0 (list nil nil nil nil)
                         (list (cons *rpt-msgid* '(:unverified :signature 0)))
                         *rpt-articles* nil (fn-rclp-article-index *rpt-articles*)))
(assert-event (equal (nth (rpt-i) (fn-rclp-events (rpt-events) *rpt-vd*))
                     (nth (rpt-i) (rpt-events))))
; (3) keep-forever.
(assert-event (equal (fn-rclp-events (rpt-events) (fn-rclp-ctx '(:keep-forever) 0 *rpt-s*))
                     (rpt-events)))
; Tooth: with no holder, no needing verdict and a releasing rule, the
; conclusion fails.
(must-fail-checked (assert-event (equal (nth (rpt-i) (rpt-new)) (nth (rpt-i) (rpt-events)))))

; fn-rclp-article-index-finds-the-article (row A8): the index finds the
; fixture's article; over the articles twice (every Message-ID bound twice)
; the index agrees with the walk; an absent Message-ID finds nothing.
(assert-event (equal (cdr (hons-get *rpt-msgid* (fn-rcl-nth 6 *rpt-ctx*))) *rpt-art*))
(assert-event (equal (cdr (hons-assoc-equal *rpt-msgid*
                                            (fn-rclp-article-index
                                             (append *rpt-articles* *rpt-articles*))))
                     (fn-find-article *rpt-msgid* (append *rpt-articles* *rpt-articles*))))
(assert-event (equal (cdr (hons-get "<absent@rpt.invalid>" (fn-rcl-nth 6 *rpt-ctx*))) nil))

; fn-rclp-events-keep-every-other-kind: every event that is not a legacy
; record is unchanged; tooth: the article record (a legacy record) changes.
(defun rpt-others-same (old new)
  (declare (xargs :mode :program))
  (if (consp old)
      (and (or (fn-record-result-okp (fn-record-decode-exact (car old)))
               (equal (car old) (car new)))
           (rpt-others-same (cdr old) (cdr new)))
    t))
(assert-event (rpt-others-same (rpt-events) (rpt-new)))
(must-fail-checked (assert-event (fn-record-result-okp
                          (fn-record-decode-exact (list 0 1 2)))))

; fn-rclp-freed-is-the-admission-count: the committed record octets the
; admission gate sums fall by the freed amount.
(defmacro rpt-freed () '(fn-rclp-freed (rpt-events) *rpt-ctx*))
(assert-event (and (equal (- (len (fn-store-event-encode (rpt-old)))
                             (len (fn-store-event-encode (fn-record-result-record (rpt-dec)))))
                          (- (len (nth (rpt-i) (rpt-events))) (len (nth (rpt-i) (rpt-new)))))
                   (< 0 (- (len (nth (rpt-i) (rpt-events))) (len (nth (rpt-i) (rpt-new)))))))
(assert-event (equal (fn-rclp-octets (rpt-new)) (- (fn-rclp-octets (rpt-events)) (rpt-freed))))

; fn-rclp-rewritten-charge-is-the-history-unit (step 2): the rewritten
; article's pin keeps one unit of the charge it had, so the ledger's reserved
; charge falls by the rest once the rewrite is replayed; the witness charge is
; above the unit, so the release is non-degenerate.
(assert-event (and (< 1 (fn-record-charge (rpt-old)))
                   (equal (fn-rclp-charge-of (nth (rpt-i) (rpt-new))) 1)
                   (equal (fn-rclp-charge-of (nth (rpt-i) (rpt-events)))
                          (fn-record-charge (rpt-old)))))
(assert-event (and (< 0 (fn-rclp-freed-charge (rpt-events) *rpt-ctx*))
                   (equal (fn-rclp-charges (rpt-new))
                          (- (fn-rclp-charges (rpt-events))
                             (fn-rclp-freed-charge (rpt-events) *rpt-ctx*)))))
; Tooth (the rewrite test): under keep-forever nothing is rewritten and the
; article keeps its whole charge; it is not the unit.
(must-fail-checked (assert-event
            (equal (fn-rclp-charge-of
                    (nth (rpt-i) (fn-rclp-events (rpt-events)
                                                 (fn-rclp-ctx '(:keep-forever) 0 *rpt-s*))))
                   1)))

; The fixture's profile (the development preset) and a history past one
; unit of work, for store-log-reclaim-tests.
(defconst *rpt-profile* *fn-bs-profile-development*)
(assert-event (fn-bs-profile-admittedp *rpt-profile*))
(defmacro rpt-long () '(append (rpt-events) (make-list 4096 :initial-element '(1 2 3))))
