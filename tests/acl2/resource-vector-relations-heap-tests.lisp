; Teeth for books/resource-vector-relations-heap: the run's capacity C' (PRF-223's statement since
; L-RUN-LAUNCH, books/admission-memory.lisp fn-adm-capacity) as a funded root of the resource vector.
; The witness is fn-core's fresh small store (tests/acl2/heap-command-tests.lisp's figures) with a
; configured capacity of 100 at the exact fifty-holder edge, where the gate holds fewer than 100 connections.
(in-package "ACL2")
(include-book "../../books/resource-vector-relations-heap")


(defconst *rvht-profile*
  '((102 110 45 115 116 111 114 101 45 49 48) 16384 8388608 196608 32768 16 256 128 1048576 1048576 1048576
    1048576 1048576 64 256 16384))
(defconst *rvht-img* '(81046496 30081024 1376256))
(defconst *rvht-cfg* '(100 nil 8388608 8388608 nil 0 0 0 nil 18 nil nil 119))
(defconst *rvht-tot* '(0 0 0 0 0 0 0 0 :resident))
(defconst *rvht-limit*
  (max (fn-mm-sum *rvht-profile* *rvht-img* (fn-adm-cfg-at *rvht-cfg* 50) *rvht-tot*)
       (fn-mm-reopen-need *rvht-profile* *rvht-img* (fn-adm-cfg-at *rvht-cfg* 50) *rvht-tot*)))
; C' is below the configured C there, and positive; under 150 MiB no connection fits.
(assert-event
 (let ((c (fn-adm-capacity *rvht-profile* *rvht-img* *rvht-cfg* *rvht-limit* *rvht-tot*)))
   (and (posp c) (< c (fn-mm-cfg-connections *rvht-cfg*)))))
(assert-event (null (fn-adm-capacity *rvht-profile* *rvht-img* *rvht-cfg* (* 150 1048576) *rvht-tot*)))

;; The relation at the witness (positive), and without its hypothesis (the 150 MiB limit no
;; connection fits).  fn-rv-connections-root is a relation, called by no host line, so its teeth are
;; these evaluations, not a host-bound keystone; the run's capacity itself is PRF-223's
;; (fn-adm-capacity-fits, fn-adm-capacity-is-the-most).
(assert-event
 (and (fn-rv-okp (fn-rv-connections-root *rvht-profile* *rvht-img* *rvht-cfg* *rvht-limit* *rvht-tot*))
      (fn-rv-fundedp (fn-rv-connections-root *rvht-profile* *rvht-img* *rvht-cfg* *rvht-limit* *rvht-tot*))))
;; The retired budget's claim, the root funded at the configured C, is false at the witness.
(assert-event
 (not (<= (fn-mm-sum *rvht-profile* *rvht-img* *rvht-cfg* *rvht-tot*) *rvht-limit*)))
