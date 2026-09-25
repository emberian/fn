; D31: the committed-history requirement, and the marker's catch-up.
;
; Review 2026-09-25 (planning/review-2026-09-25-gpt6-decisions.md §3): with A
; the committed prefix covered by success answers a client may rely on, M the
; durable marker's count and D the durable reconstructable length,
; A <= M <= D.  books/store-history-marker.lisp protects the finish path's
; acknowledgment.  Two cases were open, and this book closes both.
;
; (1) Absence must not mean legacy once the marker is in use.  The profile
;     (books/byte-store-frame.lisp, format 8) carries `history-marker':
;     `unmarked' (every format-7 store, and a format-8 store not migrated)
;     or `required'.  Under `required' an absent marker is damage
;     (`fn-hmr-open-verdict', :marker-missing); under `unmarked' the open is
;     today's `fn-hm-open-verdict'.  The requirement becomes durable only by
;     `store upgrade-profile', whose verdict (`fn-hmr-upgrade-verdict')
;     refuses `required' unless the marker is present and counts exactly the
;     reconstructed history; the command's open has written that marker
;     already (case 2), so the command is the two-step: the marker program,
;     then the profile program.  `init' never writes `required'
;     (`fn-bs-profile-init-verdict').
;
; (2) A success answered after recovery, with no later commit.  A record can
;     be durable while its marker is not (the process died between
;     fnn-publish's barrier and the marker's).  Recovery finds the record, and
;     the owner then answers a retry of that submission as already stored.
;     The catch-up point is RECOVERY: after the recovery barriers make the
;     reconstructed records durable and before the open returns (so before
;     any answer), a writable open replaces the marker by the reconstructed
;     count (`fn-hmr-catch-up').  Every answer a live process gives about a
;     held record is then below a durable marker, and so is every later
;     commit's.
;
; Host subjects (host/native/io.lisp): `fnn-check-history-marker' (every
; open, from the replay paths of `fnn-recover') calls `fn-hmr-open-verdict'
; and `fn-hmr-catch-up'; `fnn-recover' writes the catch-up frame through
; `fnn-mark-committed' (the marker program and its five cuts) after its fifth
; barrier and before the staging sweep; `fnn-command-upgrade-profile' calls
; `fn-hmr-upgrade-verdict'.
;
; The model.  A state is (COUNT MARKER ACKED PROFILE LIVE): D, the marker's
; observation, A as a count (every record below it has been answered as a
; success a client may rely on), the profile the open reads, and whether a
; process has completed an open and not since crashed or become uncertain.
; Crash images follow the byte model: the marker's is `fn-hm-crash-image'
; (books/byte-store-marker-program.lisp derives it,
; fn-bs-marker-crash-is-the-history-table), the profile's is old or new
; (books/byte-store-profile-program.lisp
; fn-bs-profile-program-crash-is-old-or-new), which the model takes at every
; profile cut.
(in-package "ACL2")
(include-book "store-history-marker")
(include-book "store-profile-upgrade")

; -----------------------------------------------------------------------------
; The decisions the host calls.

; The open's verdict under the store's profile.
(defun fn-hmr-open-verdict (profile observation record-count)
  (declare (xargs :guard t))
  (if (and (fn-bs-profile-marker-requiredp profile)
           (natp record-count)
           (equal observation '(:absent)))
      (list :refused :marker-missing)
    (fn-hm-open-verdict observation record-count)))

; The marker counts exactly RECORD-COUNT.
(defun fn-hmr-coveringp (observation record-count)
  (declare (xargs :guard t))
  (equal (fn-hm-open-verdict observation record-count)
         (list :admitted :marked record-count)))

; What a writable open writes before it returns: the frame of the
; reconstructed count when the open is admitted and the marker does not count
; exactly that history (absent, or behind it), else NIL.  NIL beyond the
; uint32 count domain as well; the open then stays short of live (below).
(defun fn-hmr-catch-up (profile observation record-count)
  (declare (xargs :guard t))
  (if (and (equal (car (fn-hmr-open-verdict profile observation record-count))
                  :admitted)
           (fn-hm-countp record-count)
           (not (fn-hmr-coveringp observation record-count)))
      (fn-hm-encode record-count)
    nil))

; `store upgrade-profile': the profile verdict, and `required' only over a
; marker that counts the reconstructed history.  A store already `required'
; needs no gate (its open refused an absent marker).
(defun fn-hmr-upgrade-verdict (current target observation record-count)
  (declare (xargs :guard t))
  (let ((verdict (fn-profile-upgrade-verdict current target)))
    (if (and (consp verdict) (equal (car verdict) :upgrade)
             (not (fn-bs-profile-marker-requiredp current))
             (fn-bs-profile-marker-requiredp
              (fn-profile-upgrade-target current target))
             (not (fn-hmr-coveringp observation record-count)))
        (list :refused :history-marker-not-covering)
      verdict)))

; -----------------------------------------------------------------------------
; The model.

(defun fn-hmr-state (count marker acked profile live)
  (declare (xargs :guard t))
  (list count marker acked profile live))

(defun fn-hmr-count (st)
  (declare (xargs :guard t :verify-guards nil))
  (nfix (nth 0 st)))

; The count a marker observation holds, 0 when absent or undecodable.
(defun fn-hmr-marker-count (obs)
  (declare (xargs :guard t))
  (if (and (consp obs) (eq (car obs) :present) (consp (cdr obs)))
      (nfix (fn-hm-decode (cadr obs)))
    0))

; One step of the history.
;   (:burn)               a reservation abandoned: nothing the open reads
;   (:uncertain B)        a publication cut before its directory barrier:
;                         the record survives iff B; the process is fenced
;   (:commit CUT C)       in a live process, the record of sequence COUNT is
;                         durable and the marker program runs to CUT;
;                         :marker-durable is the finish path: the process
;                         answers success and stays live.  With no frame
;                         (the uint32 end) the host faults before writing.
;   (:open CUT C)         a new process's writable open: refused, or admitted
;                         with the catch-up frame written to CUT (live when
;                         the frame is durable, or when no frame is needed
;                         because the marker already covers the history)
;   (:resolve K)          a live process answers that record K is stored
;                         (a retry resolved as already stored, a 240)
;   (:migrate TARGET C)   `store upgrade-profile TARGET' in a live process:
;                         on an :upgrade verdict the profile program runs,
;                         and its crash image is the old or the new profile
;                         (C); the offline command then exits
(defun fn-hmr-step (op st)
  (declare (xargs :guard t :verify-guards nil))
  (let ((count (fn-hmr-count st)) (marker (nth 1 st))
        (acked (nfix (nth 2 st))) (profile (nth 3 st)) (live (nth 4 st))
        (word (if (consp op) (car op) nil))
        (a1 (if (and (consp op) (consp (cdr op))) (cadr op) nil))
        (a2 (if (and (consp op) (consp (cdr op)) (consp (cddr op))) (caddr op) nil)))
    (cond
     ((equal word :uncertain)
      (fn-hmr-state (if a1 (1+ count) count) marker acked profile nil))
     ((equal word :commit)
      (if (not live)
          st
        (let ((frame (fn-hm-after-commit count)))
          (if (null frame)
              (fn-hmr-state (1+ count) marker acked profile nil)
            (fn-hmr-state (1+ count)
                          (fn-hm-crash-image a1 a2 marker (list :present frame))
                          (if (equal a1 :marker-durable) (max acked (1+ count)) acked)
                          profile
                          (equal a1 :marker-durable))))))
     ((equal word :open)
      (if (not (equal (car (fn-hmr-open-verdict profile marker count)) :admitted))
          (fn-hmr-state count marker acked profile nil)
        (let ((frame (fn-hmr-catch-up profile marker count)))
          (if frame
              (fn-hmr-state count
                            (fn-hm-crash-image a1 a2 marker (list :present frame))
                            acked profile (equal a1 :marker-durable))
            (fn-hmr-state count marker acked profile
                          (fn-hmr-coveringp marker count))))))
     ((equal word :resolve)
      (if (and live (natp a1) (< a1 count))
          (fn-hmr-state count marker (max acked (1+ a1)) profile live)
        st))
     ((equal word :migrate)
      (fn-hmr-state count marker acked
                    (if (and live a2
                             (equal (car (fn-hmr-upgrade-verdict profile a1 marker count))
                                    :upgrade))
                        (fn-profile-upgrade-target profile a1)
                      profile)
                    nil))
     (t st))))

(defun fn-hmr-run (ops st)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom ops) st (fn-hmr-run (cdr ops) (fn-hmr-step (car ops) st))))

; The invariant: the open admits; A <= M; a live process's marker counts
; exactly the history.  M <= D is the first clause (a marker above the
; history is refused).
(defun fn-hmr-invp (st)
  (declare (xargs :guard t :verify-guards nil))
  (and (equal (car (fn-hmr-open-verdict (nth 3 st) (nth 1 st) (fn-hmr-count st)))
              :admitted)
       (<= (nfix (nth 2 st)) (fn-hmr-marker-count (nth 1 st)))
       (implies (nth 4 st) (fn-hmr-coveringp (nth 1 st) (fn-hmr-count st)))))

; -----------------------------------------------------------------------------
; Shape facts the keystones spend.

(local
 (defthm fn-hmr-admitted-marker-bound
   (implies (equal (car (fn-hm-open-verdict obs k)) :admitted)
            (and (natp k) (<= (fn-hmr-marker-count obs) k)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (disable fn-hm-decode)))))

(local
 (defthm fn-hmr-hm-admitted-means
   (iff (equal (car (fn-hm-open-verdict obs k)) :admitted)
        (and (natp k)
             (or (equal obs '(:absent))
                 (and (consp obs) (equal (car obs) :present)
                      (consp (cdr obs)) (null (cddr obs))
                      (fn-hm-decode (cadr obs))
                      (<= (fn-hm-decode (cadr obs)) k)))))
   :hints (("Goal" :in-theory (enable fn-hm-open-verdict)))))

(local
 (defthm fn-hmr-open-verdict-admitted-means
   (iff (equal (car (fn-hmr-open-verdict p obs k)) :admitted)
        (and (equal (car (fn-hm-open-verdict obs k)) :admitted)
             (not (and (fn-bs-profile-marker-requiredp p)
                       (equal obs '(:absent))))))
   :hints (("Goal" :in-theory (disable fn-hm-decode fn-bs-profile-marker-requiredp)))))

(local
 (defthm fn-hmr-covering-means
   (equal (fn-hmr-coveringp obs k)
          (and (natp k) (consp obs) (equal (car obs) :present)
               (consp (cdr obs)) (null (cddr obs))
               (equal (fn-hm-decode (cadr obs)) k)))
   :hints (("Goal" :in-theory (disable fn-hm-decode)))))

(local
 (defthm fn-hmr-encode-decodes
   (implies (fn-hm-countp n)
            (equal (fn-hm-decode (fn-hm-encode n)) n))
   :hints (("Goal" :use fn-hm-decode-of-encode))))

(local
 (defthm fn-hmr-after-commit-frame
   (implies (fn-hm-after-commit count)
            (equal (fn-hm-decode (fn-hm-after-commit count)) (1+ (nfix count))))
   :hints (("Goal" :use ((:instance fn-hm-after-commit-decodes-to-the-next-count
                                    (sequence count)))
            :in-theory (disable fn-hm-encode fn-hm-decode)))))

(local
 (defthm fn-hmr-catch-up-shape
   (implies (fn-hmr-catch-up p obs k)
            (and (fn-hm-countp k)
                 (equal (fn-hmr-catch-up p obs k) (fn-hm-encode k))))
   :hints (("Goal" :in-theory '(fn-hmr-catch-up)))))

(local
 (defthm fn-hmr-catch-up-frame
   (implies (fn-hmr-catch-up p obs k)
            (and (equal (fn-hm-decode (fn-hmr-catch-up p obs k)) k)
                 (natp k)))
   :hints (("Goal" :use ((:instance fn-hmr-catch-up-shape)
                         (:instance fn-hmr-encode-decodes (n k)))
            :in-theory (disable fn-hm-encode fn-hm-decode fn-hmr-catch-up
                                fn-hmr-catch-up-shape fn-hmr-encode-decodes)))))

; A migrate step that writes `required' over an `unmarked' profile had a
; covering marker (the verdict's gate).
(local
 (defthm fn-hmr-upgrade-verdict-gate
   (implies (and (equal (car (fn-hmr-upgrade-verdict current target obs k)) :upgrade)
                 (not (fn-bs-profile-marker-requiredp current))
                 (fn-bs-profile-marker-requiredp
                  (fn-profile-upgrade-target current target)))
            (fn-hmr-coveringp obs k))
   :hints (("Goal" :in-theory (disable fn-profile-upgrade-verdict
                                       fn-profile-upgrade-target
                                       fn-hmr-coveringp
                                       fn-bs-profile-marker-requiredp)))))

; An upgrade keeps `required'.
(local
 (defthm fn-hmr-valid-profile-marker-word
   (implies (fn-bs-profile-validp values)
            (<= (fn-bs-pf 14 values) 1))
   :rule-classes :linear
   :hints (("Goal" :in-theory (e/d (fn-bs-profile-validp fn-bs-profile-invalid-reason)
                                   (fn-bs-pf fn-frame-values-okp
                                    fn-record-encoded-octets-ceiling))))))

(local
 (defthm fn-hmr-upgrade-verdict-is-the-profile-verdict
   (implies (equal (car (fn-hmr-upgrade-verdict current target obs k)) :upgrade)
            (equal (car (fn-profile-upgrade-verdict current target)) :upgrade))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (e/d (fn-hmr-upgrade-verdict)
                                   (fn-profile-upgrade-verdict fn-hmr-coveringp
                                    fn-profile-upgrade-target
                                    fn-bs-profile-marker-requiredp))))))

(local
 (defthm fn-hmr-upgrade-is-an-upgrade
   (implies (equal (car (fn-profile-upgrade-verdict current target)) :upgrade)
            (fn-profile-upgradep current (fn-profile-upgrade-target current target)))
   :hints (("Goal" :use ((:instance fn-profile-upgrade-verdict-writes-only-upgrades))
            :in-theory (disable fn-profile-upgrade-verdict fn-profile-upgrade-target
                                fn-profile-upgradep
                                fn-profile-upgrade-verdict-writes-only-upgrades
                                fn-bs-config-decode (:e fn-bs-config-decode))))))

(local
 (defthm fn-hmr-upgradep-marker-field
   (implies (fn-profile-upgradep old new)
            (and (fn-bs-profile-validp new)
                 (<= (fn-bs-profile-field 14 old) (fn-bs-profile-field 14 new))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-profile-upgradep fn-profile-bound)
                                   (fn-bs-profile-field fn-bs-profile-validp
                                    fn-bs-profile-admittedp))))))

(local
 (defthm fn-hmr-valid-marker-field
   (implies (fn-bs-profile-validp new)
            (<= (fn-bs-profile-field 14 new) 1))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-hmr-valid-profile-marker-word (values new)))
            :in-theory (e/d (fn-bs-profile-field)
                            (fn-bs-profile-validp fn-bs-pf
                             fn-hmr-valid-profile-marker-word))))))

(local
 (defthm fn-hmr-upgrade-keeps-the-requirement
   (implies (and (equal (car (fn-hmr-upgrade-verdict current target obs k)) :upgrade)
                 (fn-bs-profile-marker-requiredp current))
            (fn-bs-profile-marker-requiredp
             (fn-profile-upgrade-target current target)))
   :hints (("Goal"
            :use ((:instance fn-hmr-upgradep-marker-field
                             (old current)
                             (new (fn-profile-upgrade-target current target)))
                  (:instance fn-hmr-valid-marker-field
                             (new (fn-profile-upgrade-target current target))))
            :in-theory (e/d (fn-bs-profile-marker-requiredp)
                            (fn-profile-upgrade-verdict fn-hmr-upgrade-verdict
                             fn-profile-upgrade-target fn-profile-upgradep
                             fn-bs-profile-field fn-bs-profile-validp))))))

(local (in-theory (disable fn-hmr-upgrade-verdict fn-hmr-catch-up
                           fn-hmr-coveringp fn-hmr-open-verdict
                           fn-hm-open-verdict fn-hm-decode fn-hm-encode
                           fn-hm-after-commit fn-profile-upgrade-target
                           fn-bs-profile-marker-requiredp fn-hmr-catch-up-shape
                           (:e fn-hm-encode) (:e fn-hm-decode) (:e fn-hmr-catch-up)
                           (:e fn-hm-after-commit) (:e fn-hmr-coveringp)
                           (:e fn-hm-open-verdict) (:e fn-hmr-open-verdict))))

; -----------------------------------------------------------------------------
; Keystone 1: A <= M <= D and the live coverage are invariant.  Every step --
; a burn, an uncertain publication, a commit crashed at any marker cut or
; finished, an open crashed at any catch-up cut or completed, a resolution
; answered, a migration crashed on either side of the profile's rename --
; keeps the open admitted, every answered record below the marker, and a
; live process's marker equal to the history.
(defthm fn-hmr-step-preserves-the-invariant
  (implies (fn-hmr-invp st)
           (fn-hmr-invp (fn-hmr-step op st)))
  :hints (("Goal" :in-theory (enable fn-hm-crash-image))))

(defthm fn-hmr-run-preserves-the-invariant
  (implies (fn-hmr-invp st)
           (fn-hmr-invp (fn-hmr-run ops st)))
  :hints (("Goal" :in-theory (disable fn-hmr-invp fn-hmr-step))))

; -----------------------------------------------------------------------------
; Keystone 2 (A <= M, over the finish path and the resolution path): after any
; history from an invariant state, an open that finds fewer records than the
; newest record a process answered as stored -- by a 240 after its finish,
; or by resolving a retry as already stored after recovery, with or without
; a later commit -- is refused, naming the marker.
(local
 (defthm fn-hmr-invariant-below-an-answer-refuses
   (implies (and (fn-hmr-invp st) (natp k) (< k (nfix (nth 2 st))))
            (equal (fn-hmr-open-verdict (nth 3 st) (nth 1 st) k)
                   (list :refused :history-short-of-marker
                         (fn-hmr-marker-count (nth 1 st)))))
   :hints (("Goal" :in-theory (enable fn-hmr-open-verdict fn-hm-open-verdict)))))

(defthm fn-hmr-open-refuses-below-every-answered-record
  (let ((end (fn-hmr-run ops st)))
    (implies (and (fn-hmr-invp st) (natp k) (< k (nfix (nth 2 end))))
             (equal (fn-hmr-open-verdict (nth 3 end) (nth 1 end) k)
                    (list :refused :history-short-of-marker
                          (fn-hmr-marker-count (nth 1 end))))))
  :hints (("Goal" :use ((:instance fn-hmr-run-preserves-the-invariant)
                        (:instance fn-hmr-invariant-below-an-answer-refuses
                                   (st (fn-hmr-run ops st))))
           :in-theory (disable fn-hmr-run fn-hmr-invp
                               fn-hmr-run-preserves-the-invariant
                               fn-hmr-invariant-below-an-answer-refuses))))

; Keystone 3: a required store never admits an absent marker.  The
; requirement survives every step (an upgrade never lowers it), so whatever
; history follows, deleting the marker is refused as :marker-missing.
(local
 (defthm fn-hmr-step-keeps-the-requirement
   (implies (fn-bs-profile-marker-requiredp (nth 3 st))
            (fn-bs-profile-marker-requiredp (nth 3 (fn-hmr-step op st))))))

(local
 (defthm fn-hmr-run-keeps-the-requirement
   (implies (fn-bs-profile-marker-requiredp (nth 3 st))
            (fn-bs-profile-marker-requiredp (nth 3 (fn-hmr-run ops st))))
   :hints (("Goal" :in-theory (disable fn-hmr-step)))))

(defthm fn-hmr-required-store-never-admits-an-absent-marker
  (implies (and (fn-bs-profile-marker-requiredp (nth 3 st)) (natp k))
           (equal (fn-hmr-open-verdict (nth 3 (fn-hmr-run ops st)) '(:absent) k)
                  (list :refused :marker-missing)))
  :hints (("Goal" :use ((:instance fn-hmr-run-keeps-the-requirement))
           :in-theory (e/d (fn-hmr-open-verdict)
                           (fn-hmr-run fn-hmr-run-keeps-the-requirement)))))

; Keystone 4: the requirement becomes durable only after a covering marker.
; The one step that turns an `unmarked' profile `required' is a migration, in
; a live process (whose open wrote or found the marker), over a marker that
; counts exactly the history, and it leaves that marker as it was.
(defthm fn-hmr-requirement-follows-a-covering-marker
  (implies (and (not (fn-bs-profile-marker-requiredp (nth 3 st)))
                (fn-bs-profile-marker-requiredp (nth 3 (fn-hmr-step op st))))
           (and (equal (car op) :migrate)
                (nth 4 st)
                (fn-hmr-coveringp (nth 1 st) (fn-hmr-count st))
                (equal (nth 1 (fn-hmr-step op st)) (nth 1 st))))
  :hints (("Goal" :in-theory (disable fn-hmr-covering-means))))

; Keystone 5: migration of a store at rest is exactly the two-step.  From an
; `unmarked' store no process holds (every open is a new process), two steps
; reach `required' only as the open that makes the marker count the history
; (the catch-up program, run to its barrier) followed by the profile program
; of `store upgrade-profile'; the marker is then the covering one.
(local
 (defthm fn-hmr-catch-up-covers
   (implies (fn-hmr-catch-up p obs k)
            (fn-hmr-coveringp (list :present (fn-hmr-catch-up p obs k)) k))))

(local
 (defthm fn-hmr-live-only-after-an-open
   (implies (and (not (nth 4 st)) (nth 4 (fn-hmr-step op st)))
            (and (equal (car op) :open)
                 (fn-hmr-coveringp (nth 1 (fn-hmr-step op st))
                                   (fn-hmr-count (fn-hmr-step op st)))))
   :hints (("Goal" :in-theory (e/d (fn-hm-crash-image)
                                   (fn-hmr-covering-means))))))

(local
 (defthm fn-hmr-step-keeps-rest-without-requirement
   (implies (and (not (nth 4 st))
                 (not (fn-bs-profile-marker-requiredp (nth 3 st))))
            (not (fn-bs-profile-marker-requiredp (nth 3 (fn-hmr-step op st)))))
   :hints (("Goal" :use ((:instance fn-hmr-requirement-follows-a-covering-marker))
            :in-theory (disable fn-hmr-requirement-follows-a-covering-marker)))))

(defthm fn-hmr-legacy-store-migrates-by-the-two-step
  (let ((mid (fn-hmr-step op1 st)))
    (implies (and (not (nth 4 st))
                  (not (fn-bs-profile-marker-requiredp (nth 3 st)))
                  (fn-bs-profile-marker-requiredp (nth 3 (fn-hmr-step op2 mid))))
             (and (equal (car op1) :open)
                  (equal (car op2) :migrate)
                  (fn-hmr-coveringp (nth 1 mid) (fn-hmr-count mid))
                  (equal (nth 1 (fn-hmr-step op2 mid)) (nth 1 mid)))))
  :hints (("Goal" :use ((:instance fn-hmr-requirement-follows-a-covering-marker
                                   (op op2) (st (fn-hmr-step op1 st)))
                        (:instance fn-hmr-step-keeps-rest-without-requirement
                                   (op op1))
                        (:instance fn-hmr-live-only-after-an-open (op op1)))
           :in-theory (disable fn-hmr-step fn-hmr-coveringp fn-hmr-count
                               fn-hmr-requirement-follows-a-covering-marker
                               fn-hmr-step-keeps-rest-without-requirement
                               fn-hmr-live-only-after-an-open))))

; Export: the decisions stay executable; the model closes.
(in-theory (disable fn-hmr-step fn-hmr-run fn-hmr-invp fn-hmr-marker-count
                    fn-hmr-count fn-hmr-state))
