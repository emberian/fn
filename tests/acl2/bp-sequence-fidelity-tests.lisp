; Reachable teeth for observed-file BP sequence recovery and returned values.
(in-package "ACL2")
(include-book "../../books/bp-sequence-fidelity")
(include-book "std/testing/must-fail" :dir :system)

; Ground correspondence witnesses for the exact recover subject.
(assert-event
 (equal (fn-bpn-sf-host-recover :absent t) '(:ready 0)))
(assert-event
 (equal (fn-bpn-sf-host-recover :absent nil)
        '(:fault :sequence-frontier-missing)))
(assert-event
 (equal (fn-bpn-sf-host-recover '(:valid 1) nil) '(:ready 1)))
(assert-event
 (equal (fn-bpn-sf-host-recover :malformed nil)
        '(:fault :sequence-frontier)))
(assert-event
 (equal (fn-bpn-sf-host-reserve 7) (fn-bpn-sequence-reserve 7)))

(defconst *bsft-first-events*
  '(:root-parent-barrier :sequence-parent-new
    (:recover :absent)
    :stage-durable :frontier-name-published
    :sequence-directory-barrier :return))

(defconst *bsft-first*
  (fn-bpn-sf-trace (fn-bpn-sf-initial) *bsft-first-events*))

; The value at native line 165 is the value tracked by the theorem.
(assert-event
 (fn-bpn-sf-trace-admissiblep (fn-bpn-sf-initial)
                                *bsft-first-events*))
(assert-event (equal (fn-bpn-sf-returned *bsft-first*) '(0)))
(assert-event (equal (fn-bpn-sf-confirmed *bsft-first*) 1))
(assert-event (fn-bpn-sf-safep *bsft-first*))

; A barriered successor can be lost before the accessor returns.  Recovery
; starts at one, so zero is burned rather than returned twice.
(defconst *bsft-lost-before-return-events*
  '(:root-parent-barrier :sequence-parent-new
    (:recover :absent)
    :stage-durable :frontier-name-published
    :sequence-directory-barrier :process-death
    :root-parent-barrier :sequence-parent-old
    (:recover (:valid 1))
    :stage-durable :frontier-name-published
    :sequence-directory-barrier :return))

(defmacro bsft-lost-before-return ()
  '(fn-bpn-sf-trace (fn-bpn-sf-initial)
                     *bsft-lost-before-return-events*))

(assert-event
 (fn-bpn-sf-trace-admissiblep (fn-bpn-sf-initial)
                                *bsft-lost-before-return-events*))
(assert-event
 (equal (fn-bpn-sf-returned (bsft-lost-before-return)) '(1)))
(assert-event
 (equal (fn-bpn-sf-confirmed (bsft-lost-before-return)) 2))

; A returned value may be lost with its caller before bundle authoring.  The
; next process still returns the successor, which is the stronger boundary
; needed by both native call sites.
(defconst *bsft-lost-return-events*
  (append *bsft-first-events*
          '(:process-death
            :root-parent-barrier :sequence-parent-old
            (:recover (:valid 1))
            :stage-durable :frontier-name-published
            :sequence-directory-barrier :return)))

(defmacro bsft-lost-return ()
  '(fn-bpn-sf-trace (fn-bpn-sf-initial) *bsft-lost-return-events*))

(assert-event
 (fn-bpn-sf-trace-admissiblep (fn-bpn-sf-initial)
                                *bsft-lost-return-events*))
(assert-event (equal (fn-bpn-sf-returned (bsft-lost-return)) '(1 0)))
(assert-event
 (no-duplicatesp-equal (fn-bpn-sf-returned (bsft-lost-return))))

; A staged residue is ignored after process death.  The still-visible old
; final is rebarriered and sequence one is then returned exactly once.
(defconst *bsft-staged-residue-events*
  (append *bsft-first-events*
          '(:root-parent-barrier :sequence-parent-old
            (:recover (:valid 1))
            :stage-durable :process-death
            :root-parent-barrier :sequence-parent-old
            (:recover (:valid 1))
            :stage-durable :frontier-name-published
            :sequence-directory-barrier :return)))

(defmacro bsft-staged-residue ()
  '(fn-bpn-sf-trace (fn-bpn-sf-initial) *bsft-staged-residue-events*))

(assert-event
 (fn-bpn-sf-trace-admissiblep (fn-bpn-sf-initial)
                                *bsft-staged-residue-events*))
(assert-event
 (equal (fn-bpn-sf-returned (bsft-staged-residue)) '(1 0)))

; After an unconfirmed rename, process death may expose the old final.  Retrying
; one is safe because that attempt never returned.
(defconst *bsft-old-final-events*
  (append *bsft-first-events*
          '(:root-parent-barrier :sequence-parent-old
            (:recover (:valid 1))
            :stage-durable :frontier-name-published :process-death
            :root-parent-barrier :sequence-parent-old
            (:recover (:valid 1))
            :stage-durable :frontier-name-published
            :sequence-directory-barrier :return)))

(defmacro bsft-old-final ()
  '(fn-bpn-sf-trace (fn-bpn-sf-initial) *bsft-old-final-events*))

(assert-event
 (fn-bpn-sf-trace-admissiblep (fn-bpn-sf-initial)
                                *bsft-old-final-events*))
(assert-event (equal (fn-bpn-sf-returned (bsft-old-final)) '(1 0)))

; The same cut may expose the renamed final.  Recovery then burns one and
; returns two; the model does not require blind fencing of a valid restart.
(defconst *bsft-new-final-events*
  (append *bsft-first-events*
          '(:root-parent-barrier :sequence-parent-old
            (:recover (:valid 1))
            :stage-durable :frontier-name-published :power-loss
            :root-parent-barrier :sequence-parent-old
            (:recover (:valid 2))
            :stage-durable :frontier-name-published
            :sequence-directory-barrier :return)))

(defmacro bsft-new-final ()
  '(fn-bpn-sf-trace (fn-bpn-sf-initial) *bsft-new-final-events*))

(assert-event
 (fn-bpn-sf-trace-admissiblep (fn-bpn-sf-initial)
                                *bsft-new-final-events*))
(assert-event (equal (fn-bpn-sf-returned (bsft-new-final)) '(2 0)))

; Existing namespaces do not reset on absence, and malformed bytes fence.
(defmacro bsft-old-absent ()
  '(fn-bpn-sf-trace
    *bsft-first*
    '(:process-death :root-parent-barrier :sequence-parent-old
      (:recover :absent))))
(defmacro bsft-malformed ()
  '(fn-bpn-sf-trace
    *bsft-first*
    '(:process-death :root-parent-barrier :sequence-parent-old
      (:recover :malformed))))
(assert-event (fn-bpn-sf-fencedp (bsft-old-absent)))
(assert-event (fn-bpn-sf-fencedp (bsft-malformed)))
(assert-event (equal (fn-bpn-sf-returned (bsft-old-absent)) '(0)))
(assert-event (equal (fn-bpn-sf-returned (bsft-malformed)) '(0)))

; Teeth for the keystone's sole hypothesis.  If physical storage exposes a
; valid frontier zero after zero was returned and frontier one was confirmed,
; the actual core happily recovers zero and the native sequence can be returned
; twice.  The concrete trace is reachable in the transition system, but the
; regressed observation is exactly where admissibility is false.
(defconst *bsft-regressed-events*
  (append *bsft-first-events*
          '(:process-death
            :root-parent-barrier :sequence-parent-old
            (:recover (:valid 0))
            :stage-durable :frontier-name-published
            :sequence-directory-barrier :return)))

(defmacro bsft-regressed ()
  '(fn-bpn-sf-trace (fn-bpn-sf-initial) *bsft-regressed-events*))

(assert-event
 (not (fn-bpn-sf-trace-admissiblep (fn-bpn-sf-initial)
                                     *bsft-regressed-events*)))
(assert-event (equal (fn-bpn-sf-returned (bsft-regressed)) '(0 0)))
(assert-event
 (not (no-duplicatesp-equal (fn-bpn-sf-returned (bsft-regressed)))))

(local
 (must-fail
  (defthm bsft-admissibility-hypothesis-has-teeth
    (no-duplicatesp-equal
     (fn-bpn-sf-returned
      (fn-bpn-sf-trace (fn-bpn-sf-initial) events))))))
