; fn: witnesses and teeth for books/reclaim-chunked-seal.lisp over the owner
; fixture rewritten under the expiring context
; (tests/acl2/reclaim-chunked-walk-tests.lisp: *rcw-new*, *rcw-c2*).
(in-package "ACL2")
(include-book "../../books/reclaim-chunked-seal")
(include-book "reclaim-chunked-walk-tests")

(defconst *rcs-keyring* (fn-sn-keyring *rpt-s*))
(defconst *rcs-gen* (fn-sn-keyring-generation *rpt-s*))
(defconst *rcs-h0* 40)

; -----------------------------------------------------------------------------
; 1. KEYSTONE fn-rcw-predict-acc-steps-is-predict, reached: pass 3 over two
; chunkings is fn-orcs-predict of the whole rewritten history; the rewrite
; made records (the expired articles' tombstones), so payloads are sealed.
(make-event `(defconst *rcs-whole* ',(fn-orcs-predict *rcw-new* *rcs-keyring* *rcs-gen* *rcs-h0*)))
(assert-event (not (eq (car *rcs-whole*) :bad)))
(assert-event (< 0 (len (cadr *rcs-whole*))))
(defmacro rcs-p3 (chunks)
  `(fn-rcw-predict-acc-steps (fn-rcw-acc-init *rcw-configs*) *rcw-configs* ,chunks
                             *rcs-keyring* *rcs-gen* *rcs-h0* nil))
(make-event `(defconst *rcs-p3* ',(rcs-p3 *rcw-c2*)))
(make-event `(defconst *rcs-p3b* ',(rcs-p3 *rcw-c1*)))
(make-event `(defconst *rcs-cap* ',(fn-sco-capture *rcw-configs* (car *rcs-whole*))))
(assert-event (equal (fn-rcw-acc-finish (car *rcs-p3*)) *rcs-cap*))
(assert-event (equal (fn-rcw-acc-finish (car *rcs-p3b*)) *rcs-cap*))
(assert-event (equal (caddr *rcs-p3*) (cadr *rcs-whole*)))
(assert-event (equal (cadr *rcs-p3*) (+ *rcs-h0* (len (cadr *rcs-whole*)))))
; Teeth: a host that restarts the handle at the base for every chunk (does
; not carry H) predicts other handles once an earlier chunk sealed one.
(make-event
 `(defconst *rcs-reset* ',(let ((a (fn-rcw-predict-acc-step (fn-rcw-acc-init *rcw-configs*)
                                                            *rcw-configs* (take 2 *rcw-new*)
                                                            *rcs-keyring* *rcs-gen* *rcs-h0*)))
                            (fn-rcw-predict-acc-step (car a) *rcw-configs* (nthcdr 2 *rcw-new*)
                                                     *rcs-keyring* *rcs-gen* *rcs-h0*))))
(assert-event (< 0 (len (fn-orcs-payloads (take 2 *rcw-new*)))))
(must-fail-checked
 (assert-event (equal (fn-rcw-acc-finish (car *rcs-reset*)) *rcs-cap*)))
; A chunk carrying the intern's refusal word is :bad, as the whole is.
(assert-event (equal (rcs-p3 (list (take 1 *rcw-new*) (list :bad))) :bad))
(assert-event (equal (car (fn-orcs-predict (append *rcw-new* (list :bad)) *rcs-keyring*
                                           *rcs-gen* *rcs-h0*))
                     :bad))

; -----------------------------------------------------------------------------
; 2. KEYSTONE fn-rcw-srcs-steps-is-the-walk, reached: the chunked writer walk
; is the one walk over the whole history, and it is not empty.
(bpr-lift fn-rcw-srcs-steps 3)
(bpr-lift fn-scka-srcs-n 4)
(make-event `(defconst *rcs-walk* ',(in-arena-fn-rcw-srcs-steps *rpt-payloads* *rcw-c2* nil nil)))
(assert-event (equal *rcs-walk*
                     (in-arena-fn-scka-srcs-n *rpt-payloads* *rcw-new* (len *rcw-new*) nil nil)))
(assert-event (consp (cadr *rcs-walk*)))
; Teeth: chunks out of order walk the payloads in another order.
(must-fail-checked
 (assert-event (equal (in-arena-fn-rcw-srcs-steps *rpt-payloads* (reverse *rcw-c2*) nil nil)
                      *rcs-walk*)))
