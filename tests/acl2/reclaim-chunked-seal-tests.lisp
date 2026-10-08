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
; fn-rcw-predict-acc-steps-is-predict with its teeth (TEETH CONTRACT v1).
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

; Host fnn-owner-reclaim-pass / fnn-checkpoint-walk, exercised by
; tests/test_native_reclaim_walk.py::test_a_pass_longer_than_two_chunks_installs_and_counts_the_available.
; true-list-listp was redundant: each chunk's residual tail is discarded.
(defteeth fn-rcw-srcs-steps-is-the-walk
  :claim (()
          (equal (fn-rcw-srcs-steps chunks lacc sacc fn-arena)
                 (fn-scka-srcs-n (fn-rcw-concat chunks) (len (fn-rcw-concat chunks))
                                 lacc sacc fn-arena)))
  :subject fn-scka-srcs-n
  :witness ((chunks *rcw-c2*) (lacc nil) (sacc nil))
  :stobjs ((fn-arena (fn-arn-seal-many *rpt-payloads* fn-arena)))
  :mutations ((skip-first-chunk
               (:conclusion
                (equal (fn-rcw-srcs-steps (cdr chunks) lacc sacc fn-arena)
                       (fn-scka-srcs-n (fn-rcw-concat chunks) (len (fn-rcw-concat chunks))
                                       lacc sacc fn-arena)))
               ((chunks *rcw-c2*) (lacc nil) (sacc nil))
               :fault "the writer advances its chunk cursor before consuming the first chunk")))
(assert-event
 (let ((chunks (list (append (take 2 *rcw-new*) 'tail) (nthcdr 2 *rcw-new*))))
   (and (not (true-list-listp chunks))
        (equal (in-arena-fn-rcw-srcs-steps *rpt-payloads* chunks nil nil) *rcs-walk*))))

; A full open that actually installs an owner (default config already creates fn.letters).
(assert-event
 (not (equal (fn-ock-recover-full (list *fn-cfg-default-record*) 8
              (car (fn-orcs-predict *rcw-new* *rcs-keyring* *rcs-gen* 0)) 4) :fault)))
(defteeth fn-rcw-rebuild-of-the-chunked-capture-is-the-full-open
 :claim (((handle (natp h0))) (equal (cadr (fn-owner-orcp-rebuild
                         (fn-rcw-acc-finish
                          (car (fn-rcw-predict-acc-steps (fn-rcw-acc-init configs) configs chunks
                                                         keyring generation h0 nil)))
                         configs frontier max-conns))
                  (fn-ock-recover-full configs frontier
                                       (car (fn-orcs-predict (fn-rcw-concat chunks) keyring
                                                             generation h0))
                                       max-conns)))
 :subject fn-owner-orcp-rebuild
 :witness ((configs (list *fn-cfg-default-record*)) (chunks *rcw-c2*)
           (keyring *rcs-keyring*) (generation *rcs-gen*) (h0 0) (frontier 8) (max-conns 4))
 :breaks ((handle ((h0 -1)) :logical "a negative predicted handle is outside the natural-handle guard"))
 :mutations ((skipped-chunk (:conclusion (equal (cadr (fn-owner-orcp-rebuild
                         (fn-rcw-acc-finish
                          (car (fn-rcw-predict-acc-steps (fn-rcw-acc-init configs) configs (cdr chunks)
                                                         keyring generation h0 nil)))
                         configs frontier max-conns))
                  (fn-ock-recover-full configs frontier
                                       (car (fn-orcs-predict (fn-rcw-concat chunks) keyring
                                                             generation h0))
                                       max-conns))) ()
              :fault "pass 3 advances past the first chunk before extending the capture")))
