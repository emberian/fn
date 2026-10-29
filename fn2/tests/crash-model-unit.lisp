; Quest B1: concrete operation controls and evaluated keystone witnesses.
; Run from the worktree root: sh fn2/tools/certify.sh tests/crash-model-unit.lisp
(in-package "ACL2")
(include-book "../books/crash-model")

(defun fn2-cmu-fill (n byte)
  (declare (xargs :guard (and (natp n) (unsigned-byte-p 8 byte))))
  (if (zp n) nil (cons byte (fn2-cmu-fill (- n 1) byte))))

(defconst *fn2-cmu-honest* (fn2-cm-profile :crash-only t t nil 0 0))
(defconst *fn2-cmu-broad* (fn2-cm-profile :broad t t nil 0 0))
(defconst *fn2-cmu-lying* (fn2-cm-profile :lying nil t nil 0 0))
(defconst *fn2-cmu-radius* (fn2-cm-profile :broad t t nil 1 0))
(defconst *fn2-cmu-budget* (fn2-cm-profile :broad t t nil 0 1))
(defconst *fn2-cmu-zero* (fn2-cmu-fill 512 0))
(defconst *fn2-cmu-a* (fn2-cmu-fill 512 17))
(defconst *fn2-cmu-b* (fn2-cmu-fill 512 34))
; Nonconstant garbage: the tear relation must range over all octet strings.
(defconst *fn2-cmu-garbage* (append (fn2-cmu-fill 256 91) (fn2-cmu-fill 256 163)))
(defconst *fn2-cmu-s0* (fn2-cm-init 4096 512 4 0))
(defconst *fn2-cmu-empty* (fn2-cm-durable *fn2-cmu-s0*))
(defconst *fn2-cmu-image-a* (update-nth 0 *fn2-cmu-a* *fn2-cmu-empty*))
(defconst *fn2-cmu-image-ab* (update-nth 8 *fn2-cmu-b* *fn2-cmu-image-a*))
(defconst *fn2-cmu-submitted*
  (fn2-cm-submit-write *fn2-cmu-s0* 1 0 *fn2-cmu-a* nil))
(defconst *fn2-cmu-written*
  (fn2-cm-complete-write *fn2-cmu-submitted* 1 :ok *fn2-cmu-honest*))
(defconst *fn2-cmu-fencing* (fn2-cm-submit-fence *fn2-cmu-written* 10))
(defconst *fn2-cmu-fenced*
  (fn2-cm-complete-fence *fn2-cmu-fencing* 10 :ok *fn2-cmu-image-a* *fn2-cmu-honest*))

; Submitted writes may land before their completion is delivered. Completion
; changes visibility, but ordinary completion alone establishes no persistence.
(assert-event
 (and (equal (fn2-cm-durable *fn2-cmu-written*) *fn2-cmu-empty*)
      (equal (fn2-cm-visible *fn2-cmu-written*) *fn2-cmu-image-a*)
      (fn2-cm-crash-image-allowedp *fn2-cmu-submitted* *fn2-cmu-image-a* *fn2-cmu-honest*)
      (fn2-cm-crash-image-allowedp *fn2-cmu-written* *fn2-cmu-empty* *fn2-cmu-honest*)
      (fn2-cm-crash-image-allowedp *fn2-cmu-written*
        (update-nth 0 *fn2-cmu-garbage* *fn2-cmu-empty*) *fn2-cmu-honest*)
      (not (fn2-cm-crash-image-allowedp *fn2-cmu-written*
        (update-nth 24 *fn2-cmu-garbage* *fn2-cmu-empty*) *fn2-cmu-honest*))))

; Read outcomes distinguish IO, actual visible data, and another address's data.
(assert-event
 (and (fn2-cm-read-allowedp *fn2-cmu-written* 0 :ok *fn2-cmu-a* *fn2-cmu-honest*)
      (fn2-cm-read-allowedp *fn2-cmu-written* 0 :io nil *fn2-cmu-broad*)
      (fn2-cm-read-allowedp *fn2-cmu-written* 4096 '(:misdirect 0) *fn2-cmu-a* *fn2-cmu-broad*)
      (not (fn2-cm-read-allowedp *fn2-cmu-written* 4096 '(:misdirect 0) *fn2-cmu-a* *fn2-cmu-honest*))
      (not (fn2-cm-read-allowedp *fn2-cmu-written* 0 :ok *fn2-cmu-b* *fn2-cmu-broad*))))

; An honest barrier cannot omit covered data; lying acknowledgements can.
(assert-event
 (and (fn2-cm-fence-allowedp *fn2-cmu-fencing* 10 :ok *fn2-cmu-image-a* *fn2-cmu-honest*)
      (not (fn2-cm-fence-allowedp *fn2-cmu-fencing* 10 :ok *fn2-cmu-empty* *fn2-cmu-honest*))
      (fn2-cm-fence-allowedp *fn2-cmu-fencing* 10 :ok *fn2-cmu-empty* *fn2-cmu-lying*)
      (equal (fn2-cm-durable *fn2-cmu-fenced*) *fn2-cmu-image-a*)
      (fn2-cm-crash-image-allowedp *fn2-cmu-fenced* *fn2-cmu-image-a* *fn2-cmu-honest*)
      (not (fn2-cm-crash-image-allowedp *fn2-cmu-fenced* *fn2-cmu-empty* *fn2-cmu-honest*))))

; Row 8: a failed fence's two reopen views. Neither is a new successful fence.
(assert-event
 (let* ((failed (fn2-cm-complete-fence *fn2-cmu-fencing* 10 :io *fn2-cmu-empty* *fn2-cmu-broad*))
        (cached (fn2-cm-reopen failed nil))
        (reverted (fn2-cm-reopen failed t)))
   (and (fn2-cm-fence-allowedp *fn2-cmu-fencing* 10 :io *fn2-cmu-empty* *fn2-cmu-broad*)
        (equal (fn2-cm-durable failed) *fn2-cmu-empty*)
        (equal (fn2-cm-visible cached) *fn2-cmu-image-a*)
        (equal (fn2-cm-visible reverted) *fn2-cmu-empty*)
        (fn2-cm-crash-image-allowedp cached *fn2-cmu-empty* *fn2-cmu-broad*))))

; Fsyncgate also allows an arbitrary torn selection of the covered writes.
(assert-event
 (let* ((torn (update-nth 0 *fn2-cmu-garbage* *fn2-cmu-empty*))
        (failed (fn2-cm-complete-fence *fn2-cmu-fencing* 10 :io torn *fn2-cmu-broad*)))
   (and (fn2-cm-fence-allowedp *fn2-cmu-fencing* 10 :io torn *fn2-cmu-broad*)
        (equal (fn2-cm-durable failed) torn))))

; :io and :no-space do not undo an uncertain write. Short progress is known
; for the completed prefix; the remaining request is still crash-uncertain.
(assert-event
 (let* ((io (fn2-cm-complete-write *fn2-cmu-submitted* 1 :io *fn2-cmu-broad*))
        (space (fn2-cm-complete-write *fn2-cmu-submitted* 1 :no-space *fn2-cmu-broad*))
        (large (fn2-cm-submit-write *fn2-cmu-s0* 2 0 (append *fn2-cmu-a* *fn2-cmu-b*) nil))
        (short (fn2-cm-complete-write large 2 '(:short 512 0) *fn2-cmu-broad*)))
   (and (fn2-cm-crash-image-allowedp io *fn2-cmu-image-a* *fn2-cmu-broad*)
        (fn2-cm-crash-image-allowedp space *fn2-cmu-image-a* *fn2-cmu-broad*)
        (equal (car (fn2-cm-visible short)) *fn2-cmu-a*)
        (fn2-cm-crash-image-allowedp short
          (update-nth 1 *fn2-cmu-garbage* *fn2-cmu-image-a*) *fn2-cmu-broad*)) ))

; Misdirection changes the physical destination. Its own landing may tear.
(assert-event
 (let ((redirected (fn2-cm-complete-write *fn2-cmu-submitted* 1 '(:ok 4096) *fn2-cmu-broad*)))
   (and (equal (nth 8 (fn2-cm-visible redirected)) *fn2-cmu-a*)
        (equal (car (fn2-cm-visible redirected)) *fn2-cmu-zero*)
        (fn2-cm-crash-image-allowedp redirected
          (update-nth 8 *fn2-cmu-garbage* *fn2-cmu-empty*) *fn2-cmu-broad*))))

; Plain FUA persists only this request. Preflush+FUA covers completed writes
; at submission, plus its own request. Earlier submitted-but-incomplete data
; and writes completed after the preflush submission are outside that cover.
(assert-event
 (let* ((fua-submitted (fn2-cm-submit-write *fn2-cmu-written* 2 4096 *fn2-cmu-b* t))
        (fua (fn2-cm-complete-write fua-submitted 2 :ok *fn2-cmu-honest*))
        (pre-submitted (fn2-cm-submit-write *fn2-cmu-written* 2 4096 *fn2-cmu-b* :preflush-fua))
        (pre (fn2-cm-complete-write pre-submitted 2 :ok *fn2-cmu-honest*)))
   (and (equal (fn2-cm-durable fua) (update-nth 8 *fn2-cmu-b* *fn2-cmu-empty*))
        (not (equal (fn2-cm-durable fua) *fn2-cmu-image-ab*))
        (fn2-cm-crash-image-allowedp fua (fn2-cm-durable fua) *fn2-cmu-honest*)
        (equal (fn2-cm-durable pre) *fn2-cmu-image-ab*)
        (not (fn2-cm-crash-image-allowedp pre (fn2-cm-durable fua) *fn2-cmu-honest*)))))

(assert-event
 (let* ((s1 (fn2-cm-submit-write *fn2-cmu-submitted* 2 4096 *fn2-cmu-b* :preflush-fua))
        (s2 (fn2-cm-complete-write s1 1 :ok *fn2-cmu-honest*))
        (s3 (fn2-cm-complete-write s2 2 :ok *fn2-cmu-honest*)))
   (equal (fn2-cm-durable s3) (update-nth 8 *fn2-cmu-b* *fn2-cmu-empty*))))

; The fence's submission-time snapshot survives intervening overlapping writes.
; Completing an older fence after a newer one must not roll durable bytes back.
(assert-event
 (let* ((s1 (fn2-cm-submit-write *fn2-cmu-fencing* 2 0 *fn2-cmu-b* nil))
        (s2 (fn2-cm-complete-write s1 2 :ok *fn2-cmu-honest*))
        (s3 (fn2-cm-submit-fence s2 11))
        (image-b (update-nth 0 *fn2-cmu-b* *fn2-cmu-empty*))
        (old-first (fn2-cm-complete-fence s3 10 :ok *fn2-cmu-image-a* *fn2-cmu-honest*))
        (new-first (fn2-cm-complete-fence s3 11 :ok image-b *fn2-cmu-honest*))
        (old-last (fn2-cm-complete-fence new-first 10 :ok image-b *fn2-cmu-honest*)))
   (and (fn2-cm-fence-allowedp s3 10 :ok *fn2-cmu-image-a* *fn2-cmu-honest*)
        (equal (fn2-cm-durable old-first) *fn2-cmu-image-a*)
        (equal (fn2-cm-visible old-first) image-b)
        (fn2-cm-fence-allowedp new-first 10 :ok image-b *fn2-cmu-honest*)
        (equal (fn2-cm-durable old-last) image-b))))

; At-rest damage is explicit and spends the profile's per-run unit budget.
(assert-event
 (let* ((damaged (fn2-cm-corrupt *fn2-cmu-fenced* 0 *fn2-cmu-garbage* *fn2-cmu-budget*))
        (denied (fn2-cm-corrupt damaged 8 *fn2-cmu-garbage* *fn2-cmu-budget*)))
   (and (equal (car (fn2-cm-durable damaged)) *fn2-cmu-garbage*)
        (equal (fn2-cm-visible damaged) (fn2-cm-durable damaged))
        (equal denied damaged)
        (equal (fn2-cm-corrupt *fn2-cmu-fenced* 0 *fn2-cmu-garbage* *fn2-cmu-honest*)
               *fn2-cmu-fenced*))))

; Row 6 collateral damage has a declared radius. A clean remote sector is
; never licensed just because a different sector has an in-flight write.
(assert-event
 (let* ((s0 (fn2-cm-init 4096 512 4 1))
        (s1 (fn2-cm-submit-write s0 1 4096 *fn2-cmu-a* nil))
        (near (update-nth 0 *fn2-cmu-garbage* (fn2-cm-durable s0)))
        (far (update-nth 24 *fn2-cmu-garbage* (fn2-cm-durable s0))))
   (and (fn2-cm-crash-image-allowedp s1 near *fn2-cmu-radius*)
        (not (fn2-cm-crash-image-allowedp s1 far *fn2-cmu-radius*))
        (not (fn2-cm-crash-image-allowedp *fn2-cmu-submitted*
               (update-nth 8 *fn2-cmu-garbage* *fn2-cmu-empty*) *fn2-cmu-broad*)))))

; Device death is sticky across process death and reopening.
(assert-event
 (let* ((dead (fn2-cm-kill-device *fn2-cmu-fenced*))
        (crashed (fn2-cm-crash dead *fn2-cmu-image-a* *fn2-cmu-honest*))
        (reopened (fn2-cm-reopen crashed t)))
   (and (fn2-cm-read-allowedp reopened 0 :io nil *fn2-cmu-broad*)
        (not (fn2-cm-read-allowedp reopened 0 :ok *fn2-cmu-a* *fn2-cmu-broad*))
        (equal (fn2-cm-durable reopened) *fn2-cmu-image-a*))))

; The well-formedness tooth evaluates the antecedent and conclusion for every
; state-mutating dispatcher arm, plus reads (which leave state unchanged).
(defun fn2-cmu-preservedp (s event profile)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn2-cm-statep s)
       (fn2-cm-statep (fn2-cm-step s event profile))))

(defun fn2-cmu-wfp-positive ()
  (declare (xargs :verify-guards nil))
 (and (fn2-cm-statep *fn2-cmu-s0*)
      (fn2-cmu-preservedp *fn2-cmu-s0* (list :submit-write 1 0 *fn2-cmu-a* nil) *fn2-cmu-honest*)
      (fn2-cmu-preservedp *fn2-cmu-submitted* '(:complete-write 1 :ok) *fn2-cmu-honest*)
      (fn2-cmu-preservedp *fn2-cmu-submitted* '(:complete-write 1 :io) *fn2-cmu-broad*)
      (fn2-cmu-preservedp *fn2-cmu-submitted* '(:complete-write 1 :no-space) *fn2-cmu-broad*)
      (fn2-cmu-preservedp *fn2-cmu-submitted* '(:complete-write 1 (:short 256 0)) *fn2-cmu-broad*)
      (fn2-cmu-preservedp *fn2-cmu-written* '(:submit-fence 10) *fn2-cmu-honest*)
      (fn2-cmu-preservedp *fn2-cmu-fencing* (list :complete-fence 10 :ok *fn2-cmu-image-a*) *fn2-cmu-honest*)
      (fn2-cmu-preservedp *fn2-cmu-fencing* (list :complete-fence 10 :io *fn2-cmu-empty*) *fn2-cmu-broad*)
      (fn2-cmu-preservedp *fn2-cmu-written* (list :crash *fn2-cmu-image-a*) *fn2-cmu-honest*)
      (fn2-cmu-preservedp *fn2-cmu-written* (list :land-live *fn2-cmu-image-a*) *fn2-cmu-honest*)
      (fn2-cmu-preservedp *fn2-cmu-written* '(:reopen nil) *fn2-cmu-broad*)
      (fn2-cmu-preservedp *fn2-cmu-written* '(:reopen t) *fn2-cmu-broad*)
      (fn2-cmu-preservedp *fn2-cmu-written* '(:dead) *fn2-cmu-broad*)
      (fn2-cmu-preservedp *fn2-cmu-fenced* (list :corrupt 0 *fn2-cmu-garbage*) *fn2-cmu-budget*)
      (fn2-cmu-preservedp *fn2-cmu-fenced* '(:read 0) *fn2-cmu-honest*)))
(assert-event (equal (fn2-cmu-wfp-positive) t))

; Removing the initial state invariant makes the actual preservation
; conclusion false, not merely unprovable. A read cannot repair a bad image.
(defun fn2-cmu-wfp-negative ()
  (declare (xargs :verify-guards nil))
 (let* ((bad (fn2-cm-put 1 nil *fn2-cmu-s0*))
        (after (fn2-cm-step bad '(:read 0) *fn2-cmu-honest*)))
   (and (not (fn2-cm-statep bad)) (not (fn2-cm-statep after)))))
(assert-event (equal (fn2-cmu-wfp-negative) t))

; Completion identity remains unique while its completed-write record lives.
(assert-event
 (let* ((resubmitted (fn2-cm-submit-write *fn2-cmu-written* 1 4096 *fn2-cmu-b* nil))
        (completed (fn2-cm-complete-write resubmitted 1 :ok *fn2-cmu-honest*)))
   (and (fn2-cm-statep *fn2-cmu-written*)
        (fn2-cm-statep resubmitted) (fn2-cm-statep completed))))

; Honest-fence tooth: assert the whole named antecedent and conclusion,
; and assert an allowed post-crash image so the implication actually fires.
(assert-event
 (and (fn2-cm-fence-durability-hyps *fn2-cmu-fencing* 10 *fn2-cmu-image-a* *fn2-cmu-honest*)
      (fn2-cm-crash-image-allowedp *fn2-cmu-fenced* *fn2-cmu-image-a* *fn2-cmu-honest*)
      (fn2-cm-fence-durability-concl *fn2-cmu-fencing* 10 *fn2-cmu-image-a*
                                    *fn2-cmu-image-a* *fn2-cmu-honest*)))

; Removing A-PERSISTENCE-FENCE allows a successful lying fence followed by
; the old image. This is a concrete falsification of the same conclusion.
(defun fn2-cmu-fence-negative ()
  (declare (xargs :verify-guards nil))
 (let ((lied (fn2-cm-complete-fence *fn2-cmu-fencing* 10 :ok *fn2-cmu-empty* *fn2-cmu-lying*)))
   (and (not (fn2-cm-persistence-fence *fn2-cmu-lying*))
        (fn2-cm-fence-allowedp *fn2-cmu-fencing* 10 :ok *fn2-cmu-empty* *fn2-cmu-lying*)
        (fn2-cm-crash-image-allowedp lied *fn2-cmu-empty* *fn2-cmu-lying*)
        (not (fn2-cm-fence-durability-hyps *fn2-cmu-fencing* 10 *fn2-cmu-empty* *fn2-cmu-lying*))
        (not (fn2-cm-fence-durability-concl *fn2-cmu-fencing* 10 *fn2-cmu-empty*
                                           *fn2-cmu-empty* *fn2-cmu-lying*)))))
(assert-event (equal (fn2-cmu-fence-negative) t))

; FUA tooth over a dirty unrelated dependency, so "unchanged" is substantive.
; Replacing plain FUA by preflush+FUA removes precisely the own-only premise
; and makes the same conclusion false: the dependency becomes durable.
(defun fn2-cmu-fua-teeth ()
  (declare (xargs :verify-guards nil))
 (let* ((fua (fn2-cm-submit-write *fn2-cmu-written* 2 4096 *fn2-cmu-b* t))
        (pre (fn2-cm-submit-write *fn2-cmu-written* 2 4096 *fn2-cmu-b* :preflush-fua)))
   (and (fn2-cm-fua-only-hyps fua 2 '(:ok 4096) *fn2-cmu-honest* 0 512)
        (fn2-cm-fua-only-concl fua 2 '(:ok 4096) *fn2-cmu-honest* 0 512)
        (not (fn2-cm-fua-only-hyps pre 2 '(:ok 4096) *fn2-cmu-honest* 0 512))
        (not (fn2-cm-fua-only-concl pre 2 '(:ok 4096) *fn2-cmu-honest* 0 512)))))
(assert-event (equal (fn2-cmu-fua-teeth) t))

; Misdirection may occur while a request is still in flight: the crash cut
; must tear its physical destination even though no completion was delivered.
(assert-event
 (let* ((redirected (fn2-cm-redirect-write *fn2-cmu-submitted* 1 4096 *fn2-cmu-broad*))
        (physical (update-nth 8 *fn2-cmu-garbage* *fn2-cmu-empty*))
        (intended (update-nth 0 *fn2-cmu-garbage* *fn2-cmu-empty*))
        (completed (fn2-cm-complete-write redirected 1 :ok *fn2-cmu-broad*)))
   (and (fn2-cm-find 1 (fn2-cm-inflight redirected))
        (equal (fn2-cm-visible redirected) *fn2-cmu-empty*)
        (fn2-cm-crash-image-allowedp redirected physical *fn2-cmu-broad*)
        (not (fn2-cm-crash-image-allowedp redirected intended *fn2-cmu-broad*))
        (equal (fn2-cm-visible completed) (update-nth 8 *fn2-cmu-a* *fn2-cmu-empty*))
        (equal (fn2-cm-redirect-write *fn2-cmu-submitted* 1 4096 *fn2-cmu-honest*)
               *fn2-cmu-submitted*)
        (fn2-cmu-preservedp *fn2-cmu-submitted* '(:redirect-write 1 4096) *fn2-cmu-broad*))))

; The preflush has a process-death cut before its own FUA write begins.
; Before that phase finishes, only the earlier dependency can crash-land.
; Afterwards its dependency is durable even when the own write is short.
(assert-event
 (let* ((submitted (fn2-cm-submit-write *fn2-cmu-written* 2 4096
                                       (append *fn2-cmu-b* *fn2-cmu-b*) :preflush-fua))
        (own-torn (update-nth 8 *fn2-cmu-garbage* *fn2-cmu-image-a*))
        (preflushed (fn2-cm-complete-preflush submitted 2 :ok *fn2-cmu-image-a* *fn2-cmu-broad*))
        (short (fn2-cm-complete-write preflushed 2 '(:short 256 4096) *fn2-cmu-broad*))
        (prefix (append (fn2-cmu-fill 256 34) (fn2-cmu-fill 256 0))))
   (and (fn2-cm-crash-image-allowedp submitted *fn2-cmu-image-a* *fn2-cmu-broad*)
        (not (fn2-cm-crash-image-allowedp submitted own-torn *fn2-cmu-broad*))
        (equal (fn2-cm-at 3 (fn2-cm-find 2 (fn2-cm-inflight preflushed))) :fua-after-preflush)
        (equal (fn2-cm-durable preflushed) *fn2-cmu-image-a*)
        (fn2-cm-crash-image-allowedp preflushed *fn2-cmu-image-a* *fn2-cmu-broad*)
        (not (fn2-cm-crash-image-allowedp preflushed *fn2-cmu-empty* *fn2-cmu-broad*))
        (fn2-cm-crash-image-allowedp preflushed own-torn *fn2-cmu-broad*)
        (equal (fn2-cm-durable short) (update-nth 8 prefix *fn2-cmu-image-a*))
        (fn2-cmu-preservedp submitted
          (list :complete-preflush 2 :ok *fn2-cmu-image-a*) *fn2-cmu-broad*)
        (fn2-cmu-preservedp preflushed '(:complete-write 2 (:short 256 4096)) *fn2-cmu-broad*))))

; A failed preflush removes the own request before any of its bytes start.
; Its earlier dependency remains uncertain; neither cached visibility nor a
; late completion can revive the aborted request or authorize durability.
(assert-event
 (let* ((submitted (fn2-cm-submit-write *fn2-cmu-written* 2 4096 *fn2-cmu-b* :preflush-fua))
        (failed (fn2-cm-complete-preflush submitted 2 :io *fn2-cmu-empty* *fn2-cmu-broad*)))
   (and (not (fn2-cm-find 2 (fn2-cm-inflight failed)))
        (fn2-cm-failed failed)
        (equal (fn2-cm-durable failed) *fn2-cmu-empty*)
        (equal (fn2-cm-visible failed) *fn2-cmu-image-a*)
        (fn2-cm-crash-image-allowedp failed *fn2-cmu-image-a* *fn2-cmu-broad*)
        (fn2-cm-crash-image-allowedp failed *fn2-cmu-empty* *fn2-cmu-broad*)
        (not (fn2-cm-crash-image-allowedp failed
               (update-nth 8 *fn2-cmu-garbage* *fn2-cmu-empty*) *fn2-cmu-broad*))
        (equal (fn2-cm-complete-write failed 2 :ok *fn2-cmu-broad*) failed)
        (fn2-cmu-preservedp submitted
          (list :complete-preflush 2 :io *fn2-cmu-empty*) *fn2-cmu-broad*))))

; An assumption-disabled device may still actually persist a particular
; fence. Identical bytes do not erase the distinction between a persistence
; event and a lying completion whose cache can still be lost at a crash.
(assert-event
 (let* ((persisted (fn2-cm-complete-fence *fn2-cmu-fencing* 10 '(:ok :persist)
                                        *fn2-cmu-image-a* *fn2-cmu-lying*))
        (lied (fn2-cm-complete-fence *fn2-cmu-fencing* 10 '(:ok :lie)
                                   *fn2-cmu-image-a* *fn2-cmu-lying*)))
   (and (fn2-cm-fence-allowedp *fn2-cmu-fencing* 10 '(:ok :persist)
                              *fn2-cmu-image-a* *fn2-cmu-lying*)
        (fn2-cm-fence-allowedp *fn2-cmu-fencing* 10 '(:ok :lie)
                              *fn2-cmu-empty* *fn2-cmu-lying*)
        (not (fn2-cm-fence-allowedp *fn2-cmu-fencing* 10 '(:ok :lie)
                                   *fn2-cmu-image-a* *fn2-cmu-honest*))
        (equal (fn2-cm-durable persisted) *fn2-cmu-image-a*)
        (equal (fn2-cm-dstamps persisted) (fn2-cm-vstamps persisted))
        (equal (fn2-cm-durable lied) (fn2-cm-durable persisted))
        (not (fn2-cm-crash-image-allowedp persisted *fn2-cmu-empty* *fn2-cmu-lying*))
        (fn2-cm-crash-image-allowedp lied *fn2-cmu-empty* *fn2-cmu-lying*)
        (fn2-cmu-preservedp *fn2-cmu-fencing*
          (list :complete-fence 10 '(:ok :persist) *fn2-cmu-image-a*) *fn2-cmu-lying*)
        (fn2-cmu-preservedp *fn2-cmu-fencing*
          (list :complete-fence 10 '(:ok :lie) *fn2-cmu-empty*) *fn2-cmu-lying*))))

; FUA success persists by default even in a lying profile. Loss is an
; explicit environment choice permitted only without A-PERSISTENCE-FENCE.
(assert-event
 (let* ((submitted (fn2-cm-submit-write *fn2-cmu-s0* 1 0 *fn2-cmu-a* t))
        (row (fn2-cm-find 1 (fn2-cm-inflight submitted)))
        (persisted (fn2-cm-complete-write submitted 1 :ok *fn2-cmu-lying*))
        (lost (fn2-cm-complete-write submitted 1 '(:ok 0 :lose-fua) *fn2-cmu-lying*)))
   (and (fn2-cm-write-outcome-p submitted row '(:ok 0 :lose-fua) *fn2-cmu-lying*)
        (not (fn2-cm-write-outcome-p submitted row '(:ok 0 :lose-fua) *fn2-cmu-honest*))
        (equal (fn2-cm-complete-write submitted 1 '(:ok 0 :lose-fua) *fn2-cmu-honest*)
               submitted)
        (equal (fn2-cm-durable persisted) *fn2-cmu-image-a*)
        (equal (fn2-cm-durable lost) *fn2-cmu-empty*)
        (equal (fn2-cm-visible lost) *fn2-cmu-image-a*)
        (not (fn2-cm-crash-image-allowedp persisted *fn2-cmu-empty* *fn2-cmu-lying*))
        (fn2-cm-crash-image-allowedp lost *fn2-cmu-empty* *fn2-cmu-lying*)
        (fn2-cmu-preservedp submitted '(:complete-write 1 (:ok 0 :lose-fua)) *fn2-cmu-lying*)
        (fn2-cmu-preservedp submitted '(:complete-write 1 :ok) *fn2-cmu-lying*))))

; A larger profile allowance cannot widen the formatted device's declared
; damage radius. The earlier geometry1/profile1 test supplies the positive
; control; here only geometry changes to radius zero.
(assert-event
 (let* ((submitted (fn2-cm-submit-write *fn2-cmu-s0* 1 4096 *fn2-cmu-a* nil))
        (neighbor (update-nth 0 *fn2-cmu-garbage* *fn2-cmu-empty*)))
   (not (fn2-cm-crash-image-allowedp submitted neighbor *fn2-cmu-radius*))))

; Registration is not certification of the owed theorem itself.
(assert-event
 (and (member-eq 'fn2-cm-well-formedness (fn2-owed-names (w state)))
      (member-eq 'fn2-cm-honest-fence-durability (fn2-owed-names (w state)))
      (member-eq 'fn2-cm-fua-alone (fn2-owed-names (w state)))
      (not (getpropc 'fn2-cm-well-formedness 'theorem nil (w state)))
      (not (getpropc 'fn2-cm-honest-fence-durability 'theorem nil (w state)))
      (not (getpropc 'fn2-cm-fua-alone 'theorem nil (w state)))))

; Unit isolation, not global quiescence: a covered write survives even when
; another in-flight write tears in an unrelated unit. The whole crash image
; is deliberately different from the fence snapshot.
(defun fn2-cmu-fence-positive ()
  (declare (xargs :verify-guards nil))
 (let* ((s (fn2-cm-submit-write *fn2-cmu-fencing* 2 4096 *fn2-cmu-b* nil))
        (after (fn2-cm-complete-fence s 10 :ok *fn2-cmu-image-a* *fn2-cmu-honest*))
        (torn (update-nth 8 *fn2-cmu-garbage* *fn2-cmu-image-a*)))
   (and (fn2-cm-fence-durability-hyps s 10 *fn2-cmu-image-a* *fn2-cmu-honest*)
        (fn2-cm-crash-image-allowedp after torn *fn2-cmu-honest*)
        (not (equal torn (fn2-cm-visible s)))
        (fn2-cm-fence-durability-concl s 10 *fn2-cmu-image-a* torn *fn2-cmu-honest*))))
(assert-event (equal (fn2-cmu-fence-positive) t))

; Removing unit isolation admits a concrete destructive overlap. The fence
; itself still succeeds honestly; only its later overwrite defeats the claim.
(defun fn2-cmu-isolation-negative ()
  (declare (xargs :verify-guards nil))
 (let* ((s (fn2-cm-submit-write *fn2-cmu-fencing* 2 0 *fn2-cmu-b* nil))
        (after (fn2-cm-complete-fence s 10 :ok *fn2-cmu-image-a* *fn2-cmu-honest*))
        (torn (update-nth 0 *fn2-cmu-garbage* *fn2-cmu-image-a*)))
   (and (fn2-cm-statep s)
        (fn2-cm-fence-allowedp s 10 :ok *fn2-cmu-image-a* *fn2-cmu-honest*)
        (not (fn2-cm-fence-durability-hyps s 10 *fn2-cmu-image-a* *fn2-cmu-honest*))
        (fn2-cm-crash-image-allowedp after torn *fn2-cmu-honest*)
        (not (fn2-cm-fence-durability-concl s 10 *fn2-cmu-image-a* torn *fn2-cmu-honest*)))))
(assert-event (equal (fn2-cmu-isolation-negative) t))

; Shape-valid stamps alone do not establish snapshot freshness. A newer
; persisted version invalidates the snapshot premise, and an older visible
; stamp does not license corruption of the durable bytes.
(assert-event
 (let* ((stamps (update-nth 0 (fn2-cmu-fill 512 2) (fn2-cm-dstamps *fn2-cmu-fenced*)))
        (s0 (fn2-cm-put 3 stamps (fn2-cm-put 9 2 *fn2-cmu-fenced*)))
        (s (fn2-cm-submit-fence s0 11))
        (after (fn2-cm-complete-fence s 11 :ok *fn2-cmu-image-a* *fn2-cmu-honest*)))
   (and (fn2-cm-statep s)
        (fn2-cm-fence-allowedp s 11 :ok *fn2-cmu-image-a* *fn2-cmu-honest*)
        (not (fn2-cm-fence-durability-hyps s 11 *fn2-cmu-image-a* *fn2-cmu-honest*))
        (not (fn2-cm-crash-image-allowedp after *fn2-cmu-empty* *fn2-cmu-honest*))
        (fn2-cm-crash-image-allowedp after *fn2-cmu-image-a* *fn2-cmu-honest*))))

; Reachable stale-cache case: reopen reverts before an outstanding successful
; fence completes. The successful fence's durable bytes survive crash even
; though the reopened read view has an older stamp.
(assert-event
 (let* ((s (fn2-cm-reopen *fn2-cmu-fencing* t))
        (after (fn2-cm-complete-fence s 10 :ok *fn2-cmu-image-a* *fn2-cmu-honest*)))
   (and (fn2-cm-statep after)
        (equal (fn2-cm-visible after) *fn2-cmu-empty*)
        (equal (fn2-cm-durable after) *fn2-cmu-image-a*)
        (fn2-cm-crash-image-allowedp after *fn2-cmu-image-a* *fn2-cmu-honest*)
        (not (fn2-cm-crash-image-allowedp after *fn2-cmu-empty* *fn2-cmu-honest*)))))

; An old failing fence cannot tear a newer already persisted version merely
; because the older snapshot's completion stamp differs.
(assert-event
 (let* ((s (fn2-cm-submit-write *fn2-cmu-fencing* 2 0 *fn2-cmu-b* nil))
        (s (fn2-cm-complete-write s 2 :ok *fn2-cmu-broad*))
        (s (fn2-cm-submit-fence s 11))
        (new (fn2-cm-fence-image s 11))
        (s (fn2-cm-complete-fence s 11 :ok new *fn2-cmu-broad*)))
   (and (fn2-cm-fence-allowedp s 10 :io new *fn2-cmu-broad*)
        (not (fn2-cm-fence-allowedp s 10 :io *fn2-cmu-empty* *fn2-cmu-broad*)))))

; Fsyncgate loss and cache visibility are independent. Keeping cached bytes
; does not imply a later successful fence can write back forgotten dirty data.
(assert-event
 (let* ((s (fn2-cm-complete-fence *fn2-cmu-fencing* 10 :io
                                 *fn2-cmu-empty* *fn2-cmu-broad*))
        (s (fn2-cm-reopen s :cached-lost))
        (s (fn2-cm-submit-fence s 11))
        (s (fn2-cm-complete-fence s 11 :ok *fn2-cmu-empty* *fn2-cmu-broad*)))
   (and (fn2-cm-statep s)
        (fn2-cm-read-allowedp s 0 :ok *fn2-cmu-a* *fn2-cmu-broad*)
        (equal (fn2-cm-durable s) *fn2-cmu-empty*)
        (fn2-cm-crash-image-allowedp s *fn2-cmu-empty* *fn2-cmu-broad*)
        (not (fn2-cm-crash-image-allowedp s *fn2-cmu-image-a* *fn2-cmu-broad*)))))

; A failed preflush may land an earlier ambiguous completed write even when
; that write reported zero known progress and advanced no byte stamps. A
; later failed write is not part of the preflush submission snapshot.
(assert-event
 (let* ((s (fn2-cm-complete-write *fn2-cmu-submitted* 1 :io *fn2-cmu-broad*))
        (s (fn2-cm-submit-write s 2 4096 *fn2-cmu-b* :preflush-fua))
        (s (fn2-cm-submit-write s 3 8192 *fn2-cmu-b* nil))
        (s (fn2-cm-complete-write s 3 :io *fn2-cmu-broad*))
        (bad (update-nth 16 *fn2-cmu-b* *fn2-cmu-empty*))
        (after (fn2-cm-complete-preflush s 2 :io *fn2-cmu-image-a* *fn2-cmu-broad*)))
   (and (fn2-cm-statep s) (fn2-cm-statep after)
        (fn2-cm-failed after)
        (not (fn2-cm-find 2 (fn2-cm-inflight after)))
        (equal (fn2-cm-durable after) *fn2-cmu-image-a*)
        (equal (fn2-cm-complete-preflush s 2 :io bad *fn2-cmu-broad*) s))))

(fn2-assert-owed-teeth fn2-cm-well-formedness fn2-cm-honest-fence-durability fn2-cm-fua-alone)
