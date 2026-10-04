; fn: witnesses and teeth for books/reclaim-chunked-walk.lisp over the owner
; fixture's store (*rpt-s*, its arena *rpt-payloads*) and the expiring
; context over it (*xt-ctx*, books/expiry-instant: every article expired).
(in-package "ACL2")
(include-book "../../books/reclaim-chunked-walk")
(include-book "must-fail-checked")
(include-book "arena-lift")
(include-book "expiry-tests")
; Ground terms below reach the record codec seam: its attachment, and each
; constant through it as a make-event (books/codec-attach.lisp).
(include-book "../../books/codec-attach")

(defconst *rcw-rows* (fn-sf-records (fn-sn-files *rpt-s*)))
(defconst *rcw-configs* (list *xt-star*))
(assert-event (<= 3 (len *rcw-rows*)))

; The rewritten history the pass 2/3 walks produce (the offline rewrite of
; every captured row), whole and in two chunkings.
(bpr-lift fn-orc-rewrite-rows 2)
(make-event `(defconst *rcw-new* ',(in-arena-fn-orc-rewrite-rows *rpt-payloads* *rcw-rows* *xt-ctx*)))
(defconst *rcw-c1* (list (take 1 *rcw-new*) (nthcdr 1 *rcw-new*)))
(defconst *rcw-c2* (list (take 2 *rcw-new*) nil (nthcdr 2 *rcw-new*)))
(assert-event (equal (fn-rcw-concat *rcw-c1*) *rcw-new*))
(assert-event (equal (fn-rcw-concat *rcw-c2*) *rcw-new*))

; -----------------------------------------------------------------------------
; 1. KEYSTONE fn-rcw-acc-steps-is-capture, reached: both chunkings finish to
; the capture of the whole rewritten history, and the capture is not the
; capture of nothing (the premise is inhabited by a real history).
(defconst *rcw-whole* (fn-sco-capture *rcw-configs* *rcw-new*))
(defmacro rcw-acc (chunks)
  `(fn-rcw-acc-finish (fn-rcw-acc-steps (fn-rcw-acc-init *rcw-configs*) *rcw-configs* ,chunks)))
(assert-event (equal (rcw-acc *rcw-c1*) *rcw-whole*))
(assert-event (equal (rcw-acc *rcw-c2*) *rcw-whole*))
(assert-event (not (equal *rcw-whole* (fn-sco-capture *rcw-configs* nil))))
; Teeth (mutation): the chunks in another order are another history, and
; a dropped chunk is a shorter one.
(must-fail-checked
 (assert-event (equal (rcw-acc (list (nthcdr 1 *rcw-new*) (take 1 *rcw-new*))) *rcw-whole*)))
(must-fail-checked
 (assert-event (equal (rcw-acc (list (take 1 *rcw-new*))) *rcw-whole*)))
; The carried count is the record count, and the accumulator invariant holds.
(assert-event (fn-rcw-accp (fn-rcw-acc-steps (fn-rcw-acc-init *rcw-configs*) *rcw-configs* *rcw-c2*)))
(assert-event (equal (fn-rcw-acc-n (fn-rcw-acc-steps (fn-rcw-acc-init *rcw-configs*)
                                                     *rcw-configs* *rcw-c2*))
                     (len *rcw-new*)))

; -----------------------------------------------------------------------------
; 2. KEYSTONE fn-rcw-canon-acc-steps-is-the-checkpoint-capture, reached: the
; pass-2 steps over the chunks finish to the capture of the canonical rows
; of the whole history, handles from 0, and the final handle is the count of
; sealed payloads.
(bpr-lift fn-rcw-canon-acc-steps 4)
(defun rcw-canon-of (rows h fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (fn-scka-canon-rows rows fn-arena h))
(bpr-lift rcw-canon-of 2)
(bpr-lift fn-rcw-seal-count 1)
(make-event `(defconst *rcw-canon* ',(in-arena-rcw-canon-of *rpt-payloads* *rcw-new* 0)))
(assert-event (not (eq *rcw-canon* :bad)))
(make-event `(defconst *rcw-p2* ',(in-arena-fn-rcw-canon-acc-steps *rpt-payloads* (fn-rcw-acc-init *rcw-configs*)
                                                    *rcw-configs* *rcw-c2* 0)))
(assert-event (not (eq *rcw-p2* :bad)))
(assert-event (equal (fn-rcw-acc-finish (car *rcw-p2*))
                     (fn-sco-capture *rcw-configs* *rcw-canon*)))
(assert-event (equal (cadr *rcw-p2*)
                     (in-arena-fn-rcw-seal-count *rpt-payloads* *rcw-new*)))
(assert-event (< 0 (cadr *rcw-p2*)))
; Teeth: starting the second chunk's handles at 0 again (a host that did not
; carry H) is not the checkpoint's capture.
(make-event `(defconst *rcw-p2-reset* ',(let ((a (in-arena-fn-rcw-canon-acc-steps *rpt-payloads* (fn-rcw-acc-init *rcw-configs*)
                                            *rcw-configs* (list (take 2 *rcw-new*)) 0)))
    (in-arena-fn-rcw-canon-acc-steps *rpt-payloads* (car a) *rcw-configs*
                                     (list (nthcdr 2 *rcw-new*)) 0))))
(must-fail-checked
 (assert-event (equal (fn-rcw-acc-finish (car *rcw-p2-reset*))
                      (fn-sco-capture *rcw-configs* *rcw-canon*))))
