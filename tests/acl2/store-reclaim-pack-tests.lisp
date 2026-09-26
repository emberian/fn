; fn: witnesses and teeth for books/store-reclaim-pack.lisp (STO-017,
; PRF-119): the reclaiming pack `store reclaim' publishes.
(in-package "ACL2")
(include-book "../../books/store-reclaim-pack")
(include-book "std/testing/must-fail" :dir :system)
(include-book "owner-served-invariants-tests")

; The owner fixture's store after its article completed (as in
; store-reclaim-holders-tests), its committed history as octets, and the
; one article.
(defconst *rpt-s* (fn-own-store (cdr (fn-own-finish *osi-completing* *osi-cfg*))))
(defun rpt-encode-all (rs)
  (declare (xargs :mode :program))
  (if (consp rs) (cons (fn-store-event-encode (car rs)) (rpt-encode-all (cdr rs))) nil))
(defconst *rpt-events* (rpt-encode-all (fn-sf-records (fn-sn-files *rpt-s*))))
(defconst *rpt-art* (car (fn-state-articles (fn-node-acceptance (fn-sn-node *rpt-s*)))))
(defconst *rpt-msgid* (fn-article-msgid *rpt-art*))
(defconst *rpt-rule* '(:released-by-all-holders))
(defconst *rpt-ctx* (fn-rclp-ctx *rpt-rule* 0 *rpt-s*))
(defconst *rpt-new* (fn-rclp-events *rpt-events* *rpt-ctx*))
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
(defconst *rpt-i* (rpt-index *rpt-events* *rpt-msgid* 0))

; The history is a nonempty summary event list, the article is reclaimable
; with no holder under the releasing rule, and its record is rewritten.
(assert-event (and (natp *rpt-i*) (< 1 (len *rpt-events*))
                   (fn-cc-octet-event-listp *rpt-events* 0 0 (len *rpt-events*))))
(assert-event (fn-rclp-rewrites-p (nth *rpt-i* *rpt-events*) *rpt-ctx*))
(assert-event (equal (fn-rclp-rewritten-msgids *rpt-events* *rpt-ctx*)
                     (list *rpt-msgid*)))

; fn-rclp-event-decodes-to-the-tombstoned-record: witness.
(defconst *rpt-old* (fn-record-result-record
                     (fn-record-decode-exact (nth *rpt-i* *rpt-events*))))
(defconst *rpt-dec* (fn-record-decode-exact (nth *rpt-i* *rpt-new*)))
(assert-event (and (fn-record-result-okp *rpt-dec*)
                   (fn-rcl-tombstonep (fn-record-payload (fn-record-result-record *rpt-dec*)))
                   (equal (fn-record-result-record *rpt-dec*) (fn-rclp-tombstoned *rpt-old*))
                   (not (equal (nth *rpt-i* *rpt-new*) (nth *rpt-i* *rpt-events*)))))
; Tooth (rewrites-p): an event that is not rewritten decodes to itself,
; so the conclusion (a tombstone payload) fails for it.
(must-fail (assert-event (fn-rcl-tombstonep
                          (fn-record-payload
                           (fn-record-result-record
                            (fn-record-decode-exact
                             (fn-rclp-event (nth *rpt-i* *rpt-events*)
                                            (fn-rclp-ctx '(:keep-forever) 0 *rpt-s*))))))))

; fn-rclp-events-keep-the-summary-shape: witness; tooth (the hypothesis): a
; list that is not a summary list (a byte dropped) stays not one.
(assert-event (fn-cc-octet-event-listp *rpt-new* 0 0 (len *rpt-events*)))
(must-fail (assert-event (fn-cc-octet-event-listp
                          (fn-rclp-events (list (cdr (nth *rpt-i* *rpt-events*))) *rpt-ctx*)
                          0 0 (len *rpt-events*))))

; fn-rclp-events-idempotent: witness (a second pass under any context).
(assert-event (equal (fn-rclp-events *rpt-new* *rpt-ctx*) *rpt-new*))
(assert-event (equal (fn-rclp-rewritten-msgids *rpt-new* *rpt-ctx*) nil))

; fn-rclp-events-never-touch-a-held-article: witness per disjunct, and the
; conclusion fails with none of them (the releasing rule, no holder).
; (1) a BP obligation names the article.
(defconst *rpt-bp* (list *rpt-rule* 0 (list nil nil nil (list *rpt-msgid*))
                         nil (fn-state-articles (fn-node-acceptance (fn-sn-node *rpt-s*)))))
(assert-event (fn-rcl-some-names-p (fn-rcl-obligations (nth 2 *rpt-bp*)) *rpt-msgid*
                                   (fn-article-memberships *rpt-art*)))
(assert-event (equal (nth *rpt-i* (fn-rclp-events *rpt-events* *rpt-bp*))
                     (nth *rpt-i* *rpt-events*)))
; (2) the verdict list needs its payload.
(defconst *rpt-vd* (list *rpt-rule* 0 (list nil nil nil nil)
                         (list (cons *rpt-msgid* '(:unverified :signature 0)))
                         (fn-state-articles (fn-node-acceptance (fn-sn-node *rpt-s*)))))
(assert-event (equal (nth *rpt-i* (fn-rclp-events *rpt-events* *rpt-vd*))
                     (nth *rpt-i* *rpt-events*)))
; (3) keep-forever.
(assert-event (equal (fn-rclp-events *rpt-events* (fn-rclp-ctx '(:keep-forever) 0 *rpt-s*))
                     *rpt-events*))
; Tooth: with no holder, no needing verdict and a releasing rule, the
; conclusion fails.
(must-fail (assert-event (equal (nth *rpt-i* *rpt-new*) (nth *rpt-i* *rpt-events*))))

; fn-rclp-events-keep-every-other-kind: every event that is not a legacy
; record is unchanged; tooth: the article record (a legacy record) changes.
(defun rpt-others-same (old new)
  (declare (xargs :mode :program))
  (if (consp old)
      (and (or (fn-record-result-okp (fn-record-decode-exact (car old)))
               (equal (car old) (car new)))
           (rpt-others-same (cdr old) (cdr new)))
    t))
(assert-event (rpt-others-same *rpt-events* *rpt-new*))
(must-fail (assert-event (fn-record-result-okp
                          (fn-record-decode-exact (list 0 1 2)))))

; fn-rclp-freed-is-the-admission-count: the committed record octets the
; admission gate sums fall by the freed amount.
(defconst *rpt-freed* (fn-rclp-freed *rpt-events* *rpt-ctx*))
(assert-event (equal (- (len (fn-store-event-encode *rpt-old*))
                        (len (fn-store-event-encode (fn-record-result-record *rpt-dec*))))
                     *rpt-freed*))
(assert-event (equal (fn-rclp-octets *rpt-new*) (- (fn-rclp-octets *rpt-events*) *rpt-freed*)))

; The decision.  The fixture's profile: the development preset.
(defconst *rpt-profile* *fn-bs-profile-development*)
(assert-event (fn-bs-profile-admittedp *rpt-profile*))
(defconst *rpt-n* (len *rpt-events*))
; Fully packed (lower = n, no name, a selected generation): it reclaims.
(defconst *rpt-d* (fn-rclp-decide *rpt-profile* *rpt-rule* 0 *rpt-s* *rpt-events*
                                  *rpt-n* *rpt-n* nil 0 '(100) nil))
(assert-event (and (equal (car *rpt-d*) :reclaim)
                   (equal (nth 2 *rpt-d*) (list *rpt-msgid*))
                   (equal (nth 4 *rpt-d*)
                          (fn-cc-encode (cadr (fn-cc-capture *rpt-new* *rpt-n*))))))
; --dry-run writes nothing and names the same article.
(assert-event (equal (fn-rclp-decide *rpt-profile* *rpt-rule* 0 *rpt-s* *rpt-events*
                                     *rpt-n* *rpt-n* nil 0 '(100) t)
                     (list :dry-run (list *rpt-msgid*) *rpt-freed*
                           (fn-rcl-store-counts *rpt-rule* 0 *rpt-s*))))
; Not packed: compact first.
(assert-event (equal (fn-rclp-decide *rpt-profile* *rpt-rule* 0 *rpt-s* *rpt-events*
                                     *rpt-n* 0 nil nil nil nil)
                     '(:compact-first)))
; fn-rclp-keep-forever-writes-nothing: witness.
(assert-event (equal (car (fn-rclp-decide *rpt-profile* '(:keep-forever) 0 *rpt-s*
                                          *rpt-events* *rpt-n* *rpt-n* nil 0 '(100) nil))
                     :none))
