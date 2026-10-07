; fn: witnesses and teeth for books/reclaim-chunked-seal.lisp over the owner
; fixture rewritten under the expiring context
; (tests/acl2/reclaim-chunked-walk-tests.lisp: *rcw-new*, *rcw-c2*).
(in-package "ACL2")
(include-book "../../books/reclaim-chunked-seal")
(include-book "../../books/defkeystone")
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

; TEETH-62 BEGIN
; fn-rcw-predict-acc-steps-is-predict with its teeth (TEETH CONTRACT v1).  Not here: fn-rcw-rebuild-of-the-chunked-capture-is-the-full-open, whose two antecedents have no counterexample on a reached ledger (a negative h0 and a :bad chunk both leave the rebuild equal to the full open).
(defteeth fn-rcw-predict-acc-steps-is-predict
  :claim (((start-handle (natp h0)))
          (let ((r (fn-rcw-predict-acc-steps (fn-rcw-acc-init configs) configs chunks
                                              keyring generation h0 nil))
                 (all (fn-rcw-concat chunks)))
             (and (equal (equal r :bad) (if (fn-orcs-has-bad all) t nil))
                  (implies (not (equal r :bad))
                           (and (equal (fn-rcw-acc-finish (car r))
                                       (fn-sco-capture configs
                                                       (car (fn-orcs-predict all keyring
                                                                             generation h0))))
                                (equal (caddr r)
                                       (cadr (fn-orcs-predict all keyring generation h0)))
                                (equal (cadr r) (+ h0 (len (caddr r)))))))))
  :subject fn-rcw-predict-acc-steps
  :witness ((configs *rcw-configs*) (chunks *rcw-c2*) (keyring *rcs-keyring*) (generation *rcs-gen*) (h0 *rcs-h0*))
  :breaks ((start-handle ((configs *rcw-configs*) (chunks *rcw-c2*) (keyring *rcs-keyring*) (generation *rcs-gen*) (h0 -5)) :logical "a negative start handle is outside the guard (natp h0) of the walk"))
  :mutations ((handle-not-advanced
               (:conclusion (let ((r (fn-rcw-predict-acc-steps (fn-rcw-acc-init configs) configs chunks keyring generation h0 nil))) (equal (cadr r) h0)))
               ((configs *rcw-configs*) (chunks *rcw-c2*) (keyring *rcs-keyring*) (generation *rcs-gen*) (h0 *rcs-h0*))
               :fault "the final handle left at the start handle")))
