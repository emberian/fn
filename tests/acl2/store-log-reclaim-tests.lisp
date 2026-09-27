; fn: witnesses and teeth for books/store-log-reclaim.lisp (lane
; log-recovery): content reclamation over the record log, on the reclaiming
; pack's fixture (tests/acl2/store-reclaim-pack-tests: the owner fixture's
; store after its article completed, released by all holders).
(in-package "ACL2")
(include-book "../../books/store-log-reclaim")
(include-book "std/testing/must-fail" :dir :system)
(include-book "store-reclaim-pack-tests")

(defmacro lgrt-d (dry) `(fn-lgr-decide *rpt-profile* *rpt-rule* 0 *rpt-s* (rpt-events) ,dry))

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
(assert-event (equal (car (fn-lgr-decide *rpt-profile* *rpt-rule* 0 *rpt-s* (rpt-long) nil))
                     :reclaim))
; Without the :reclaim answer: the dry run names the same article and writes
; nothing (no rewritten history in its answer); keep-forever rewrites nothing.
(assert-event (equal (lgrt-d t)
                     (list :dry-run (rpt-msgids) (rpt-freed)
                           (fn-rcl-store-counts *rpt-rule* 0 *rpt-s*))))
(must-fail (assert-event (equal (nth 3 (lgrt-d t)) (rpt-new))))
(assert-event (equal (car (fn-lgr-decide *rpt-profile* '(:keep-forever) 0 *rpt-s* (rpt-events) nil))
                     :none))
(must-fail (assert-event
            (equal (nth 3 (fn-lgr-decide *rpt-profile* '(:keep-forever) 0 *rpt-s* (rpt-events) nil))
                   (rpt-new))))
; A rerun over the rewritten history rewrites nothing more.
(assert-event (equal (car (fn-lgr-decide *rpt-profile* *rpt-rule* 0 *rpt-s* (rpt-new) nil))
                     :none))
; A profile the store cannot run under is refused by name.
(assert-event (equal (fn-lgr-decide '(1 2 3) *rpt-rule* 0 *rpt-s* (rpt-events) nil)
                     '(:refused :profile)))
