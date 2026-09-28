; fn: witnesses and teeth for the per-group expiry policy (Q14):
; books/expiry-policy.lisp, books/expiry-verdict.lisp, books/expiry.lisp,
; books/expiry-instant.lisp, and the reclaim context they feed
; (books/store-reclaim-pack.lisp).
(in-package "ACL2")
(include-book "../../books/expiry-instant")
(include-book "must-fail-checked")
(include-book "arena-lift")
; The owner fixture's three-article store and its committed history
; (*rpt-s*, *rpt-payloads*, rpt-events).
(include-book "store-reclaim-pack-tests")

; -----------------------------------------------------------------------------
; The operator's words (fn-xpy-words-policy-is-an-admitted-policy)

(defconst *xt-inn* (fn-xpy-policy 1 3 30 0))
(assert-event (equal (fn-xpy-words-policy '("keep" "1" "default" "3" "purge" "30")) *xt-inn*))
; any order
(assert-event (equal (fn-xpy-words-policy '("purge" "30" "keep" "1" "default" "3")) *xt-inn*))
(assert-event (equal (fn-xpy-words-policy '("clear")) *fn-xpy-keep-forever*))
; an octets window past 2^32 (two rows)
(assert-event (equal (fn-xpy-words-policy '("octets" "10000000000"))
                     (fn-xpy-policy 0 0 0 10000000000)))
; Teeth: out of INN's order (keep above purge), a repeated word, a leading
; zero, a missing number, no words.
(assert-event (null (fn-xpy-words-policy '("keep" "30" "purge" "7"))))
(assert-event (null (fn-xpy-words-policy '("keep" "1" "keep" "2"))))
(assert-event (null (fn-xpy-words-policy '("default" "07"))))
(assert-event (null (fn-xpy-words-policy '("default"))))
(assert-event (null (fn-xpy-words-policy nil)))
(must-fail-checked (assert-event (fn-xpy-words-policy '("keep" "30" "purge" "7"))))

; fn-xpy-rows-policy-after-expire-set: a target's policy reads back after
; the ordinary configuration fold; fn-xpy-group-policy falls back to "*".
(defconst *xt-v* (fn-cfg-apply (fn-cfg-initial) 1 0
                               (append (fn-xpy-deltas "fn.a" *xt-inn*)
                                       (fn-xpy-deltas "*" (fn-xpy-policy 0 0 0 0)))))
(assert-event (equal (fn-xpy-group-policy *xt-v* "fn.a") *xt-inn*))
(assert-event (equal (fn-xpy-group-policy *xt-v* "fn.b") *fn-xpy-keep-forever*))
(assert-event (and (fn-cfg-delta-listp (fn-xpy-deltas "fn.a" *xt-inn*))
                   (equal (len (fn-xpy-deltas "fn.a" *xt-inn*)) 5)))
; D03: no rows, keep forever.
(assert-event (equal (fn-xpy-group-policy (fn-cfg-initial) "fn.a") *fn-xpy-keep-forever*))

; -----------------------------------------------------------------------------
; Age (fn-xpy-age-instant keystones)

(defconst *xt-day* 86400)
; Instants on the stamp's clock: seconds since 2000-01-01T00:00:00Z.
(defconst *xt-e* 946684800)                   ; 2000-01-01 in Unix seconds
(defconst *xt-s* (- 1789862400 *xt-e*))       ; 2026-09-20T00:00:00Z
(defconst *xt-oct1* (- 1790812800 *xt-e*))    ; 2026-10-01T00:00:00Z
(defconst *xt-sep28* (- 1790553600 *xt-e*))   ; 2026-09-28T00:00:00Z
; Expires within [stamp + keep, stamp + purge]: honoured exactly.
(assert-event (equal (fn-xpy-age-instant *xt-inn* *xt-s* *xt-oct1*) *xt-oct1*))
; Below keep: raised to stamp + keep.  Above purge: lowered to stamp + purge.
(assert-event (equal (fn-xpy-age-instant *xt-inn* *xt-s* (+ *xt-s* 60))
                     (+ *xt-s* *xt-day*)))
(assert-event (equal (fn-xpy-age-instant *xt-inn* *xt-s* (+ *xt-s* (* 400 *xt-day*)))
                     (+ *xt-s* (* 30 *xt-day*))))
; Tooth (the bounds hypothesis of fn-xpy-age-instant-honours-expires-within-
; the-bounds): an Expires past purge is not honoured.
(must-fail-checked
 (assert-event (equal (fn-xpy-age-instant *xt-inn* *xt-s* (+ *xt-s* (* 400 *xt-day*)))
                      (+ *xt-s* (* 400 *xt-day*)))))
; No Expires: default days.
(assert-event (equal (fn-xpy-age-instant *xt-inn* *xt-s* nil) (+ *xt-s* (* 3 *xt-day*))))
; No age rule: never.  A :legacy stamp: never.
(assert-event (null (fn-xpy-age-instant (fn-xpy-policy 0 0 0 5) *xt-s* *xt-oct1*)))
(assert-event (null (fn-xpy-age-instant *xt-inn* :legacy *xt-oct1*)))

; The Expires: header of an article's octets (RFC 5536 section 3.2.5).
(defun xt-octets (s)
  (declare (xargs :mode :program))
  (fn-record-string-octets s))
(defun xt-article (msgid expires body)
  (declare (xargs :mode :program))
  (xt-octets (concatenate 'string
                          "From: x@example.invalid" (coerce '(#\Return #\Newline) 'string)
                          "Newsgroups: fn.a" (coerce '(#\Return #\Newline) 'string)
                          "Subject: expiry" (coerce '(#\Return #\Newline) 'string)
                          "Message-ID: " msgid (coerce '(#\Return #\Newline) 'string)
                          (if expires
                              (concatenate 'string "Expires: " expires
                                           (coerce '(#\Return #\Newline) 'string))
                            "")
                          (coerce '(#\Return #\Newline) 'string)
                          body (coerce '(#\Return #\Newline) 'string))))
(defconst *xt-p0* (xt-article "<a0@x>" "Thu, 01 Oct 2026 00:00:00 +0000" "zero"))
(defconst *xt-p1* (xt-article "<a1@x>" nil "one"))
(defconst *xt-p2* (xt-article "<a2@x>" nil "two two two two two two two two"))
(assert-event (equal (fn-xpy-expires-instant *xt-p0*) *xt-oct1*))
(assert-event (null (fn-xpy-expires-instant *xt-p1*)))
; The epoch is the stamp's (books/records-stamp.lisp: 2000-01-01), not Unix's.
(assert-event (equal (fn-xpy-expires-instant
                      (xt-article "<e@x>" "Sat, 01 Jan 2000 00:00:00 +0000" "e"))
                     0))
; Tooth: the header block stops at the empty line; an "Expires:" line in the
; body is not the header.
(assert-event (null (fn-xpy-expires-instant
                     (xt-article "<a3@x>" nil "Expires: Thu, 01 Oct 2026 00:00:00 +0000"))))

; -----------------------------------------------------------------------------
; The store's set (fn-xpy-expired-set-is-the-spec)

; Three articles, newest first; payload handles 0, 1, 2 name P0, P1, P2.  A2
; is cross-posted to fn.b, whose policy keeps forever.
(defconst *xt-a0* (fn-make-article "<a0@x>" 0 '("fn.a") '(("fn.a" . 1)) t *xt-s*))
(defconst *xt-a1* (fn-make-article "<a1@x>" 1 '("fn.a") '(("fn.a" . 2)) t *xt-s*))
(defconst *xt-a2* (fn-make-article "<a2@x>" 2 '("fn.a" "fn.b")
                                   '(("fn.a" . 3) ("fn.b" . 1)) t *xt-s*))
(defconst *xt-arts* (list *xt-a2* *xt-a1* *xt-a0*))
(defconst *xt-payloads* (list *xt-p0* *xt-p1* *xt-p2*))
(defconst *xt-q* (fn-cfg-quotas *xt-v*))
(bpr-lift fn-xpy-expired-set 3)
(bpr-lift fn-xpy-spec 4)
(defun xt-set (q now) (declare (xargs :mode :program))
  (in-arena-fn-xpy-expired-set *xt-payloads* q now *xt-arts*))
(defun xt-in (m q now) (declare (xargs :mode :program))
  (fn-xpy-expiredp m (xt-set q now)))
; At 2026-09-28: A1 (no Expires, default 3 days) is expired; A0 asks for
; 2026-10-01 and is honoured; A2 is kept by fn.b.
(assert-event (and (xt-in "<a1@x>" *xt-q* *xt-sep28*)
                   (not (xt-in "<a0@x>" *xt-q* *xt-sep28*))
                   (not (xt-in "<a2@x>" *xt-q* *xt-sep28*))))
; The walk is the specification.
(assert-event (equal (in-arena-fn-xpy-spec *xt-payloads* *xt-q* *xt-sep28* *xt-arts* nil)
                     '("<a1@x>")))
; After 2026-10-01 A0 goes too; A2 stays (fn-xpy-a-group-that-keeps-it-keeps-it).
(assert-event (and (xt-in "<a0@x>" *xt-q* (+ *xt-oct1* 1))
                   (not (xt-in "<a2@x>" *xt-q* (+ *xt-oct1* 1)))))
; Tooth (cross-posts): with fn.b under the same policy A2 goes.
(defconst *xt-q-both*
  (fn-cfg-quotas (fn-cfg-apply *xt-v* 2 0 (fn-xpy-deltas "fn.b" *xt-inn*))))
(assert-event (xt-in "<a2@x>" *xt-q-both* *xt-sep28*))
(must-fail-checked (assert-event (xt-in "<a2@x>" *xt-q* *xt-sep28*)))
; No policy: nothing expires (D03).
(assert-event (null (in-arena-fn-xpy-spec *xt-payloads* nil (+ *xt-oct1* 1) *xt-arts* nil)))

; Size: fn.a keeps the newest articles whose live octets fit; with the
; window exactly P2's length, A1 and A0 are outside it (no age rule), A2 is
; inside (and fn.b keeps it anyway).
(defconst *xt-q-size*
  (fn-cfg-quotas (fn-cfg-apply (fn-cfg-initial) 1 0
                               (fn-xpy-deltas "fn.a" (fn-xpy-policy 0 0 0 (len *xt-p2*))))))
(assert-event (equal (in-arena-fn-xpy-spec *xt-payloads* *xt-q-size* 0 *xt-arts* nil)
                     '("<a1@x>" "<a0@x>")))
; Tooth: one octet more and A1 fits.
(defconst *xt-q-size+*
  (fn-cfg-quotas (fn-cfg-apply (fn-cfg-initial) 1 0
                               (fn-xpy-deltas "fn.a" (fn-xpy-policy 0 0 0 (+ (len *xt-p2*)
                                                                            (len *xt-p1*)))))))
(assert-event (equal (in-arena-fn-xpy-spec *xt-payloads* *xt-q-size+* 0 *xt-arts* nil)
                     '("<a0@x>")))

; -----------------------------------------------------------------------------
; The verdict (fn-xpy-releasablep-is-rule-or-expired-and-unheld)

(defconst *xt-none* (list nil nil nil nil))
(defconst *xt-set-a1* (xt-set *xt-q* *xt-sep28*))
(assert-event (equal (fn-xpy-standing-verdict '(:keep-forever) *xt-sep28* *xt-none* nil
                                              *xt-set-a1* *xt-a1*)
                     :expired))
; Held: a BP obligation, an authorship verdict.
(assert-event (equal (fn-xpy-standing-verdict '(:keep-forever) *xt-sep28*
                                              (list nil nil nil (list "<a1@x>")) nil
                                              *xt-set-a1* *xt-a1*)
                     :held-bp-obligation))
(assert-event (equal (fn-xpy-standing-verdict '(:keep-forever) *xt-sep28* *xt-none*
                                              (list (cons "<a1@x>" '(:unverified :signature 0)))
                                              *xt-set-a1* *xt-a1*)
                     :verdict-needs-payload))
; Not expired: the rule's verdict (fn-xpy-standing-verdict-without-expiry).
(assert-event (equal (fn-xpy-standing-verdict '(:keep-forever) *xt-sep28* *xt-none* nil
                                              *xt-set-a1* *xt-a0*)
                     :rule-keeps))
; The rule releases first: :reclaimable, not :expired.
(assert-event (equal (fn-xpy-standing-verdict '(:released-by-all-holders) *xt-sep28*
                                              *xt-none* nil *xt-set-a1* *xt-a1*)
                     :reclaimable))
(must-fail-checked
 (assert-event (equal (fn-xpy-standing-verdict '(:keep-forever) *xt-sep28*
                                               (list nil nil nil (list "<a1@x>")) nil
                                               *xt-set-a1* *xt-a1*)
                      :expired)))

; -----------------------------------------------------------------------------
; Composed: the host's context (host/checkpoint-host.lisp
; fn-store-reclaim-context = fn-xpy-ctx) over the owner fixture's store, and
; the rewrite `store reclaim' checkpoints (fn-rclp-events).

(bpr-lift fn-xpy-ctx 4)
(bpr-lift fn-xpy-ctx-classes 1)
(defconst *xt-star* (fn-cfg-apply (fn-cfg-initial) 1 0
                                  (fn-xpy-deltas "*" (fn-xpy-policy 0 1 0 0))))
(defconst *xt-late* (expt 2 40))
(defconst *xt-ctx* (in-arena-fn-xpy-ctx *rpt-payloads* '(:keep-forever) *xt-late* *rpt-s* *xt-star*))
; Under keep-forever with every group's default of one day, long after,
; the three articles are expired and rewritten; the classes say so.
(assert-event (equal (len (fn-rclp-rewritten-msgids (rpt-events) *xt-ctx*)) 3))
(assert-event (equal (in-arena-fn-xpy-ctx-classes *rpt-payloads* *xt-ctx*) '(0 3 0 0 0 0)))
; Tooth (the policy is what releases): the same context with no policy
; rewrites nothing, and every article is :kept.
(defconst *xt-ctx0* (in-arena-fn-xpy-ctx *rpt-payloads* '(:keep-forever) *xt-late* *rpt-s*
                                         (fn-cfg-initial)))
(assert-event (equal (fn-rclp-rewritten-msgids (rpt-events) *xt-ctx0*) nil))
(assert-event (equal (in-arena-fn-xpy-ctx-classes *rpt-payloads* *xt-ctx0*) '(0 0 0 0 0 3)))
(must-fail-checked (assert-event (consp (fn-rclp-rewritten-msgids (rpt-events) *xt-ctx0*))))
; Too early (the stamp plus a day not reached at 0): nothing.
(defconst *xt-ctx-early* (in-arena-fn-xpy-ctx *rpt-payloads* '(:keep-forever) 0 *rpt-s* *xt-star*))
(assert-event (equal (fn-rclp-rewritten-msgids (rpt-events) *xt-ctx-early*) nil))
; A rerun of the rewritten history rewrites nothing (fn-rclp-events-idempotent
; under the expiring context).
(assert-event (equal (fn-rclp-rewritten-msgids (fn-rclp-events (rpt-events) *xt-ctx*) *xt-ctx*)
                     nil))

; fn-xpy-rci-recorded-context-is-the-decided-context: the recorded
; configuration (the instant's :set-limit row) keeps the quota rows.
(assert-event (equal (fn-cfg-quotas (fn-cfg-value (fn-rci-recorded-config
                                                   (fn-cfg-make 0 *xt-star*) 0 0 1 0 *xt-late*)))
                     (fn-cfg-quotas *xt-star*)))
