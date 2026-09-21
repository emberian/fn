; Teeth for the FNBS persistence-cut model.
(in-package "ACL2")
(include-book "../../books/bp-sequence-persistence")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bspt-root*
  (fn-bpn-sp-step (fn-bpn-sp-initial) :root-parent-barrier))
(defconst *bspt-namespace*
  (fn-bpn-sp-step *bspt-root* :sequence-parent-barrier))
(defconst *bspt-stage*
  (fn-bpn-sp-step *bspt-namespace* :stage-durable))
(defconst *bspt-name*
  (fn-bpn-sp-step *bspt-stage* :frontier-name-published))
(defconst *bspt-durable*
  (fn-bpn-sp-step *bspt-name* :sequence-directory-barrier))

; Each precursor cut is reachable, but authoring is impossible until both
; namespace barriers and the final sequence-directory barrier have occurred.
(assert-event (equal (fn-bpn-sp-effect *bspt-stage*) nil))
(assert-event (equal (fn-bpn-sp-effect *bspt-name*) nil))
(must-fail
 (assert-event (equal (fn-bpn-sp-effect *bspt-name*) '(:authored 0))))
(assert-event (equal (fn-bpn-sp-effect *bspt-durable*) '(:authored 0)))

; The root-parent fault is the native retry cut: no author before the retry's
; two barriers, and a successful retry may reserve zero because no stage was
; ever durable.
(defconst *bspt-root-failed*
  (fn-bpn-sp-step (fn-bpn-sp-initial) :root-parent-failed))
(assert-event (equal (fn-bpn-sp-effect *bspt-root-failed*) nil))
(must-fail
 (assert-event (equal (fn-bpn-sp-effect
                       (fn-bpn-sp-step *bspt-root-failed* :sequence-parent-barrier))
                      '(:authored 0))))

; A crash after the name but before its directory barrier fences.  Both a
; process restart and a power loss are pessimistically projected to this same
; result; the latter additionally relies on the documented fsync assumption.
(defconst *bspt-process-cut*
  (fn-bpn-sp-step *bspt-name* :process-restart))
(defconst *bspt-power-cut*
  (fn-bpn-sp-step *bspt-name* :power-loss))
(assert-event (fn-bpn-sp-fencedp *bspt-process-cut*))
(assert-event (fn-bpn-sp-fencedp *bspt-power-cut*))
(assert-event (equal (fn-bpn-sp-effect
                      (fn-bpn-sp-step *bspt-process-cut* :author)) nil))

; The directory-barriered successor survives a restart, but its pending
; sequence is intentionally abandoned.  A later completed reservation uses
; successor one, so the trace cannot author zero twice.
(defconst *bspt-after-restart*
  (fn-bpn-sp-step *bspt-durable* :process-restart))
(defconst *bspt-one*
  (fn-bpn-sp-trace *bspt-after-restart*
                    '(:root-parent-barrier :sequence-parent-barrier
                      :stage-durable :frontier-name-published
                      :sequence-directory-barrier)))
(assert-event (equal (fn-bpn-sp-effect *bspt-one*) '(:authored 1)))
(assert-event
 (no-duplicatesp-equal
  (fn-bpn-sp-authored
   (fn-bpn-sp-trace (fn-bpn-sp-initial)
                     '(:root-parent-barrier :sequence-parent-barrier
                       :stage-durable :frontier-name-published
                       :sequence-directory-barrier :author
                       :process-restart :root-parent-barrier
                       :sequence-parent-barrier :stage-durable
                       :frontier-name-published :sequence-directory-barrier
                       :author)))))
