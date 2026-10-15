; Actual accepted cold-open path after a durable MOVE, with a reachable
; nonempty owner checkpoint. Original sequence differs from entry ordinal.
(in-package "ACL2")
(include-book "lc-cleaning-owner-fixtures")

(defun lcm-open-move-control (count i fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc) :verify-guards nil))
 (let* ((input (lcm-owner-input count)) (disk (fn-lc-at 0 input))
        (segs (fn-lc-at 1 input)) (header (fn-lc-at 2 input))
        (fn-lbc (ec-call (fn-lbc-open-rebuild (lcm-owner-rows count) segs fn-lbc)))
        (move (fn-lc-plan-move i header 1 :lc :eager segs fn-lbc)))
  (mv-let (cleaned fn-lbc afterdisk aftersegs cleantrace)
   (fn-lc-clean move disk segs '(:ok :ok) fn-lbc)
   (declare (ignore cleantrace))
   (let* ((positioned (fn-lc-positioned-tail aftersegs header))
          (tail (fn-lc-tail-history aftersegs header))
          (outcome (ec-call (fn-lc-proof-ok-outcomes
                              (len (fn-lc-open-program afterdisk :lc :eager aftersegs))))))
    (mv-let (opened fn-lbc finaldisk finalsegs trace owner)
     (fn-lc-open afterdisk :lc :eager (list *fn-cfg-default-record*) 8 4 aftersegs outcome fn-lbc)
     (declare (ignore finaldisk trace))
     (mv (list cleaned (fn-lc-head (fn-lc-head (fn-lc-head positioned)))
               (fn-lc-acceptance-tail tail) opened (fn-lbc-count fn-lbc)
               (fn-lbc-word :loc0 i fn-lbc) (fn-lbc-word :loc1 i fn-lbc)
               (ec-call (fn-lc-locators-resolve fn-lbc finalsegs))
               (equal owner (ec-call (fn-ock-recover-full (list *fn-cfg-default-record*) 8 (lcm-owner-rows count) 4)))) fn-lbc))))))
(verify-guards lcm-open-move-control)
(defun lcm-open-move-fixture (count i)
 (declare (xargs :guard t :verify-guards nil))
 (with-local-stobj fn-lbc
  (mv-let (out fn-lbc) (lcm-open-move-control count i fn-lbc) out)))
(verify-guards lcm-open-move-fixture)

(assert-event
 (equal (lcm-open-move-fixture 1 0)
        '(:ok :move nil :ok 1 2 231928234007 t t)))
(assert-event
 (equal (lcm-open-move-fixture 2 1)
        '(:ok :move nil :ok 2 2 231928234007 t t)))
