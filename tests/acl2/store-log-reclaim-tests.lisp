; fn: witnesses and teeth for books/store-log-reclaim.lisp (lane
; log-recovery): content reclamation over the record log, on the reclaiming
; pack's fixture (tests/acl2/store-reclaim-pack-tests: the owner fixture's
; store after its article completed, released by all holders).
(in-package "ACL2")
(include-book "../../books/store-log-reclaim")
(include-book "must-fail-checked")
(include-book "store-reclaim-pack-tests")
(bpr-lift fn-lgr-decide 6)
(bpr-lift fn-lgr-decide-stream 6)

(defmacro lgrt-d (dry) `(in-arena-fn-lgr-decide *rpt-payloads* *rpt-profile* *rpt-rule* 0 *rpt-s* (rpt-events) ,dry))

; fn-lgr-decide-checkpoints-the-rewrite, reachable: the store's history
; reclaims; the history the log's checkpoint takes is the rewrite, which
; differs from the history (the article became its tombstone), and the
; report names the article.  No observation or link limit applies.
(assert-event (equal (car (lgrt-d nil)) :reclaim))
(assert-event (and (fn-bs-profile-admittedp *rpt-profile*)
                   (consp (rpt-msgids))
                   (equal (nth 1 (lgrt-d nil)) (rpt-msgids))
                   (equal (nth 3 (lgrt-d nil)) (rpt-new))
                   (not (equal (rpt-new) (rpt-events)))
                   (equal (len (rpt-new)) (len (rpt-events)))))
(assert-event (equal (car (in-arena-fn-lgr-decide *rpt-payloads* *rpt-profile* *rpt-rule* 0 *rpt-s* (rpt-long) nil))
                     :reclaim))
; Without the :reclaim answer: the dry run names the same article and writes
; nothing (no rewritten history in its answer); keep-forever rewrites nothing.
(assert-event (equal (lgrt-d t)
                     (list :dry-run (rpt-msgids) (rpt-freed)
                           (in-arena-fn-rcl-store-counts *rpt-payloads* *rpt-rule* 0 *rpt-s*))))
(must-fail-checked (assert-event (equal (nth 3 (lgrt-d t)) (rpt-new))))
(assert-event (equal (car (in-arena-fn-lgr-decide *rpt-payloads* *rpt-profile* '(:keep-forever) 0 *rpt-s* (rpt-events) nil))
                     :none))
(must-fail-checked (assert-event
            (equal (nth 3 (in-arena-fn-lgr-decide *rpt-payloads* *rpt-profile* '(:keep-forever) 0 *rpt-s* (rpt-events) nil))
                   (rpt-new))))
; A rerun over the rewritten history rewrites nothing more.
(assert-event (equal (car (in-arena-fn-lgr-decide *rpt-payloads* *rpt-profile* *rpt-rule* 0 *rpt-s* (rpt-new) nil))
                     :none))
; A profile the store cannot run under is refused by name.
(assert-event (equal (in-arena-fn-lgr-decide *rpt-payloads* '(1 2 3) *rpt-rule* 0 *rpt-s* (rpt-events) nil)
                     '(:refused :profile)))

; fn-lgr-decide-stream-is-lgr-decide, reachable: over the fold of the fixture's
; history under its context, the streamed decision is the whole-history one
; without the records, and the per-record rewrites are the rewritten history.
(defmacro lgrt-acc (records) `(fn-rcls-fold ,records *rpt-ctx* (fn-rcls-init)))
(assert-event (true-listp (rpt-events)))
(assert-event (equal (in-arena-fn-lgr-decide-stream *rpt-payloads* *rpt-profile* *rpt-rule* 0 *rpt-s* (lgrt-acc (rpt-events)) nil)
                     (list :reclaim (rpt-msgids) (rpt-freed)
                           (in-arena-fn-rcl-store-counts *rpt-payloads* *rpt-rule* 0 *rpt-s*))))
(assert-event (equal (in-arena-fn-lgr-decide *rpt-payloads* *rpt-profile* *rpt-rule* 0 *rpt-s* (rpt-events) nil)
                     (list :reclaim (rpt-msgids) (rpt-freed) (rpt-new)
                           (in-arena-fn-rcl-store-counts *rpt-payloads* *rpt-rule* 0 *rpt-s*))))
(assert-event (equal (in-arena-fn-lgr-decide-stream *rpt-payloads* *rpt-profile* *rpt-rule* 0 *rpt-s* (lgrt-acc (rpt-events)) t)
                     (lgrt-d t)))
; Without the fold hypothesis: the fold of the rewritten history (not of the
; history) answers :none, not the history's :reclaim.
(assert-event (equal (car (in-arena-fn-lgr-decide-stream *rpt-payloads* *rpt-profile* *rpt-rule* 0 *rpt-s*
                                                (lgrt-acc (rpt-new)) nil))
                     :none))
(must-fail-checked (assert-event (equal (car (in-arena-fn-lgr-decide-stream *rpt-payloads* *rpt-profile* *rpt-rule* 0 *rpt-s*
                                                           (lgrt-acc (rpt-new)) nil))
                                (car (lgrt-d nil)))))
