; Teeth for books/resource-vector-relations-heap: the run's capacity C' (PRF-223's statement since
; L-RUN-LAUNCH, books/admission-memory.lisp fn-adm-capacity) as a funded root of the resource vector.
; The witness is fn-core's fresh small store (tests/acl2/heap-command-tests.lisp's figures) with a
; configured capacity of 100 under a 240 MiB limit, where the gate holds fewer than 100 connections.
(in-package "ACL2")
(include-book "../../books/resource-vector-relations-heap")
(include-book "../../books/defkeystone")

(defconst *rvht-profile*
  '((102 110 45 115 116 111 114 101 45 49 48) 16384 8388608 196608 32768 16 256 128 1048576 1048576 1048576
    1048576 1048576 64 256 16384))
(defconst *rvht-img* '(81046496 30081024 1376256))
(defconst *rvht-cfg* '(100 nil 8388608 8388608 nil 0 0 0 256 18 nil nil 119))
(defconst *rvht-tot* '(0 0 0 0 0 0 0 0 :resident))
(defconst *rvht-limit* (* 240 1048576))
; C' is below the configured C there, and positive; under 150 MiB no connection fits.
(assert-event
 (let ((c (fn-adm-capacity *rvht-profile* *rvht-img* *rvht-cfg* *rvht-limit* *rvht-tot*)))
   (and (posp c) (< c (fn-mm-cfg-connections *rvht-cfg*)))))
(assert-event (null (fn-adm-capacity *rvht-profile* *rvht-img* *rvht-cfg* (* 150 1048576) *rvht-tot*)))

(defkeystone rvht-connection-capacity-funds-the-root
  (implies (posp (fn-adm-capacity profile img cfg limit tot))
           (and (fn-rv-okp (fn-rv-connections-root profile img cfg limit tot))
                (fn-rv-fundedp (fn-rv-connections-root profile img cfg limit tot))))
  :restates fn-rv-connection-capacity-funds-the-root
  :hyps (capacity)
  :subject fn-rv-connections-root
  :witness ((profile *rvht-profile*) (img *rvht-img*) (cfg *rvht-cfg*) (limit *rvht-limit*) (tot *rvht-tot*))
  :breaks ((capacity ((profile *rvht-profile*) (img *rvht-img*) (cfg *rvht-cfg*) (limit (* 150 1048576))
                      (tot *rvht-tot*))))
  :mutations ((funded-at-the-configured-capacity
               (:conclusion (<= (fn-mm-sum profile img cfg tot) (nfix limit)))
               ((profile *rvht-profile*) (img *rvht-img*) (cfg *rvht-cfg*) (limit *rvht-limit*) (tot *rvht-tot*))
               :fault "the root funded at the configured C instead of the gate's C' (the retired budget's claim)"))
  :hints (("Goal" :by fn-rv-connection-capacity-funds-the-root)))
