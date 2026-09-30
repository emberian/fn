; Private acknowledged image/spool byte trace, proof-only support for PRF-1144.
; Stable held FD/role identity and other-role frames are separate obligations.
; Visible read-after-write is not a durability or physical qualification claim.
(in-package "ACL2")
(include-book "history-image-effect-boundary")
(include-book "assumptions-hpi-positional")

(local (defthm fn-hpit-take-length
 (equal (len (fn-bs-take n xs)) (nfix n))
 :hints (("Goal" :in-theory (enable fn-bs-take)))))
(local (defthm fn-hpit-take-true-list
 (true-listp (fn-bs-take n xs))
 :hints (("Goal" :in-theory (enable fn-bs-take)))))
(local (defthm fn-hpit-nthcdr-through-prefix
 (implies (and (natp n) (true-listp x) (equal (len x) n))
  (equal (nthcdr n (append x y)) y))))
(local (defthm fn-hpit-take-appended-payload
 (implies (true-listp payload)
  (equal (take (len payload) (append payload suffix)) payload))))

(local (defthm fn-hpit-splice-readback
 (implies (and (natp offset) (true-listp payload))
  (equal (take (len payload) (nthcdr offset (fn-bs-splice old offset payload))) payload))
 :hints (("Goal" :in-theory (e/d (fn-bs-splice) (fn-bs-take take nthcdr))))))

; Full write followed by an exact read of the same held private file/range.
; This is conditional on the named physical observation assumptions. It
; does not infer them from native full counts or from an abstract digest.
(defthm fn-hpit-full-private-write-readback
 (implies (and (true-listp payload)
               (fn-assume-hpi-positional-write before after file offset payload write-got :ok)
               (fn-assume-hpi-positional-read after file offset (len payload) bytes read-got :ok))
  (equal bytes payload))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-assume-hpi-full-write-is-visible-byte-splice
                         (octets payload) (got write-got) (outcome :ok))
                       (:instance fn-assume-hpi-full-read-is-visible-byte-range
                         (bytes after) (count (len payload)) (octets bytes) (got read-got)
                         (outcome :ok)))
                  :in-theory (disable fn-bs-content fn-bs-splice take nthcdr))))

(local (defthm fn-hpit-read-plan-excludes-write-tags-unfolds
 (let ((plan (fn-hie-plan c effect stage ledger)))
  (implies (and (equal (fn-omk-at 0 plan) :io) (equal (fn-omk-at 1 plan) :read))
   (and (not (equal (fn-omk-at 0 effect) :write-page))
        (not (equal (fn-omk-at 0 effect) :write-spool)))))
 :hints (("Goal" :in-theory (e/d (fn-hie-plan fn-omk-at)
      (fn-hie-currentp fn-osj-native-slicep fn-hpi-octets-p))))))

(local (defthm fn-hpit-read-plan-is-issued-unfolds
 (implies (equal (fn-omk-at 1 (fn-hie-plan c effect stage ledger)) :read)
  (equal (fn-omk-at 0 (fn-hie-plan c effect stage ledger)) :io))
 :hints (("Goal" :in-theory (e/d (fn-hie-plan fn-omk-at)
      (fn-hie-currentp fn-osj-native-slicep fn-hpi-octets-p))))))

; Actual core observation contains precisely the named visible private range.
; FILE must be the actual retained holder for PLAN's selected FD role; the
; host/holder correspondence and frame relation are not replaced by this law.
(defthm fn-hpit-actual-read-observation-is-private-range
 (let* ((plan (fn-hie-plan c effect stage ledger))
        (offset (fn-omk-at 3 plan)) (count (fn-omk-at 4 plan)))
  (implies (and (equal (fn-omk-at 1 plan) :read)
                (fn-assume-hpi-positional-read visible file offset count bytes got :ok)
                (fn-hpi-octets-p count bytes))
   (equal (fn-hie-observation c effect stage ledger got :ok bytes)
    (list (if (equal (fn-omk-at 0 effect) :read-stage) :image-read :spool-read)
          (fn-omk-at 1 effect) stage (fn-omk-at 3 effect)
          (fn-omk-at 4 effect) (fn-omk-at 5 effect) (fn-omk-at 8 effect)
          :ok (take count (nthcdr offset (fn-bs-content visible file)))))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-assume-hpi-full-read-is-visible-byte-range
                         (bytes visible) (offset (fn-omk-at 3 (fn-hie-plan c effect stage ledger)))
                         (count (fn-omk-at 4 (fn-hie-plan c effect stage ledger)))
                         (octets bytes) (outcome :ok))
                       fn-hie-issued-plan-has-representable-interval
                       fn-hpit-read-plan-is-issued-unfolds
                       fn-hpit-read-plan-excludes-write-tags-unfolds)
                  :in-theory (e/d (fn-hie-observation fn-hie-outcome)
                                   (fn-hie-plan fn-hie-currentp fn-hpi-grant-matchesp fn-omk-at fn-bs-content
                                    fn-hpi-octets-p
                                    fn-osj-native-slicep take nthcdr)))))

; FILES is the stable, pairwise-distinct retained (stage data-spool table-spool)
; identity triple. The physical holder correspondence is an explicit caller
; obligation. STEP records (after role-index offset payload got), and carries
; the named observation and all untouched-role frames rather than assuming
; that a write to one role cannot mutate another role.
(defun fn-hpit-role-view (bytes files)
 (declare (xargs :guard t :verify-guards nil))
 (list (fn-bs-content bytes (nth 0 files))
       (fn-bs-content bytes (nth 1 files))
       (fn-bs-content bytes (nth 2 files))))

(defun fn-hpit-private-write-step-p (before step files)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((after (nth 0 step)) (role (nth 1 step)) (offset (nth 2 step))
        (payload (nth 3 step)) (got (nth 4 step)) (file (nth role files)))
  (and (true-listp files) (equal (len files) 3) (no-duplicatesp-equal files)
       (natp role) (< role 3)
       (fn-assume-hpi-positional-write before after file offset payload got :ok)
       (fn-assume-hpi-positional-other-role before after file (nth 0 files) :ok)
       (fn-assume-hpi-positional-other-role before after file (nth 1 files) :ok)
       (fn-assume-hpi-positional-other-role before after file (nth 2 files) :ok))))

(defun fn-hpit-model-role-write (view step)
 (declare (xargs :guard t :verify-guards nil))
 (let ((role (nth 1 step)))
  (update-nth role (fn-bs-splice (nth role view) (nth 2 step) (nth 3 step)) view)))

(defthm fn-hpit-private-write-updates-exactly-three-retained-roles
 (implies (fn-hpit-private-write-step-p before step files)
  (equal (fn-hpit-role-view (nth 0 step) files)
         (fn-hpit-model-role-write (fn-hpit-role-view before files) step)))
 :rule-classes nil
 :hints (("Goal" :cases ((equal (nth 1 step) 0) (equal (nth 1 step) 1))
  :use ((:instance fn-assume-hpi-full-write-is-visible-byte-splice
         (after (nth 0 step)) (file (nth (nth 1 step) files))
         (offset (nth 2 step)) (octets (nth 3 step)) (got (nth 4 step)) (outcome :ok))
        (:instance fn-assume-hpi-full-write-preserves-distinct-visible-role
         (after (nth 0 step)) (file (nth (nth 1 step) files)) (other (nth 0 files)) (outcome :ok))
        (:instance fn-assume-hpi-full-write-preserves-distinct-visible-role
         (after (nth 0 step)) (file (nth (nth 1 step) files)) (other (nth 1 files)) (outcome :ok))
        (:instance fn-assume-hpi-full-write-preserves-distinct-visible-role
         (after (nth 0 step)) (file (nth (nth 1 step) files)) (other (nth 2 files)) (outcome :ok)))
  :in-theory (e/d (fn-hpit-private-write-step-p fn-hpit-role-view fn-hpit-model-role-write)
                  (fn-bs-content fn-bs-splice)))))

(defun fn-hpit-private-write-trace-p (before steps files)
 (declare (xargs :guard t :verify-guards nil))
 (if (atom steps) (null steps)
  (and (fn-hpit-private-write-step-p before (car steps) files)
       (fn-hpit-private-write-trace-p (nth 0 (car steps)) (cdr steps) files))))

(defun fn-hpit-private-trace-after (before steps)
 (declare (xargs :guard t :verify-guards nil))
 (if (atom steps) before
  (fn-hpit-private-trace-after (nth 0 (car steps)) (cdr steps))))

(defun fn-hpit-model-role-trace (view steps)
 (declare (xargs :guard t :verify-guards nil))
 (if (atom steps) view
  (fn-hpit-model-role-trace (fn-hpit-model-role-write view (car steps)) (cdr steps))))

; Entire interleaved visible write trace, with the same retained identity
; triple throughout. Connecting these STEP records/payloads to actual HPI
; issued effects and joining canonical page bytes remains the producer proof.
(defthm fn-hpit-interleaved-private-trace-has-exact-visible-bytes
 (implies (fn-hpit-private-write-trace-p before steps files)
  (equal (fn-hpit-role-view (fn-hpit-private-trace-after before steps) files)
         (fn-hpit-model-role-trace (fn-hpit-role-view before files) steps)))
 :rule-classes nil
 :hints (("Goal" :induct (fn-hpit-private-write-trace-p before steps files)
  :in-theory (e/d (fn-hpit-private-write-trace-p fn-hpit-private-trace-after fn-hpit-model-role-trace)
                  (fn-hpit-role-view fn-hpit-model-role-write)))
         ("Subgoal *1/2" :use ((:instance fn-hpit-private-write-updates-exactly-three-retained-roles
                                              (step (car steps)))))))
