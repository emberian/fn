; S9 frozen final report. The cursor shares the installed graph after all
; producers join; it does not acquire a concurrent snapshot lease. Scratch
; for decimal digits/output staging and the stage's disk funding remain OPEN.
(in-package "ACL2")
(include-book "owner-retire-report-model")
(include-book "owner-report-feed-model")
(include-book "operator-report-descriptors")

; Cursor has eight frozen graph/scalar slots plus emitter and resume phase.
(defun fn-orr-start (step oc)
  (declare (xargs :guard t))
  (let* ((o (fn-ocfg-owner oc))
         (retention (fn-nls-retention (fn-own-store o)))
         (pins (fn-retain-pins retention)))
    (list :count-pins (fn-own-feeds o) pins pins 0 0
          (nfix (fn-retain-reserved retention)) step nil nil)))

(defun fn-orr-peer-line (entry)
  (declare (xargs :guard t))
  (let ((feed (fn-own-feed-entry-feed entry)))
    (append (fn-nls-text "retire peer=")
            (if (stringp (fn-own-feed-entry-name entry))
                (fn-nls-text (fn-own-feed-entry-name entry))
              (fn-nls-text "?"))
            (fn-nls-field "undelivered" (nfix (fn-feed-undelivered feed)))
            (fn-nls-field "dropped" (nfix (fn-feed-retry-dropped feed)))
            *fn-nls-lf*)))

(defun fn-orr-end-line (step undelivered held)
  (declare (xargs :guard (and (natp undelivered) (natp held))))
  (append (fn-nls-text "retired state=")
          (fn-nls-text (fn-oret-outcome-word step))
          (fn-nls-field "undelivered" (nfix undelivered))
          (fn-nls-field "obligations" (nfix held))
          *fn-nls-lf*
          (if (and (zp undelivered) (zp held)) nil
            (fn-nls-text
             "retire release: what stays is released only by `carry drop WORK --abandon REASON' on the stopped store
"))))

 ; Cursor adds emitter and continuation phase to the eight frozen graph slots.
; This composed source is unactivated until carried invariant/refinement and
; runtime/stage/lifetime funding are established. No whole line allocation.
(defun fn-orr-cursor (phase feeds pins root u held reserved outcome emitter resume)
  (declare (xargs :guard t))
  (list phase feeds pins root u held reserved outcome emitter resume))

(defun fn-orr-schedule (fields resume feeds pins root u held reserved outcome)
  (declare (xargs :guard (fn-orf-fieldsp fields)))
  (fn-orr-cursor :emit feeds pins root u held reserved outcome
                 (fn-orf-start fields) resume))

(defun fn-orr-peer-fields (entry)
  (declare (xargs :guard t))
  (let ((name (fn-own-feed-entry-name entry))
        (feed (fn-own-feed-entry-feed entry)))
    (fn-ord-peer (if (stringp name) name "?")
                 (nfix (fn-feed-undelivered feed))
                 (nfix (fn-feed-retry-dropped feed)))))

(defun fn-orr-obligation-fields (pin)
  (declare (xargs :guard t))
  (let ((id (fn-retain-obligation-id pin))
        (subject (fn-retain-obligation-subject pin)))
    (fn-ord-obligation (if (stringp id) id "")
                       (equal (fn-retain-obligation-kind pin) :forward)
                       (nfix (fn-retain-obligation-charge pin))
                       (if (stringp subject) subject ""))))

(defthm fn-orr-peer-fields-valid
  (fn-orf-fieldsp (fn-orr-peer-fields entry))
  :hints (("Goal" :in-theory (enable fn-orr-peer-fields))))
(defthm fn-orr-obligation-fields-valid
  (fn-orf-fieldsp (fn-orr-obligation-fields pin))
  :hints (("Goal" :in-theory (enable fn-orr-obligation-fields))))

(defun fn-orr-pin-domainp (pin)
  (declare (xargs :guard t))
  (and (stringp (fn-retain-obligation-id pin))
       (stringp (fn-retain-obligation-subject pin))
       (natp (fn-retain-obligation-charge pin))))

 ; Execution checks exactly the cursor prefix, never a remaining graph/list.
(defun fn-orr-fixed-spinep (x slots)
  (declare (xargs :guard (natp slots) :measure (nfix slots)))
  (if (zp slots) (equal x nil)
    (and (consp x) (fn-orr-fixed-spinep (cdr x) (+ -1 slots)))))

(defthm fn-orr-fixed-spine-is-shape
  (implies (natp slots)
           (equal (fn-orr-fixed-spinep x slots)
                  (and (true-listp x) (equal (len x) slots)))))

(defun fn-orr-ready-p (cursor)
  (declare (xargs :guard t))
  (and (mbe :logic (and (true-listp cursor) (equal (len cursor) 10))
            :exec (fn-orr-fixed-spinep cursor 10))
       (natp (nth 4 cursor)) (natp (nth 5 cursor)) (natp (nth 6 cursor))
       (if (equal (nth 0 cursor) :emit)
           (and (fn-orf-ready-p (nth 8 cursor))
                (member-eq (nth 9 cursor) '(:peers :obligations :release :done)))
         (and (member-eq (nth 0 cursor) '(:count-pins :peers :obligations :release :done))
              (equal (nth 8 cursor) nil) (equal (nth 9 cursor) nil)))))

(defun fn-orr-invariant (cursor)
  (declare (xargs :guard t))
  (and (true-listp cursor) (equal (len cursor) 10)
       (natp (nth 4 cursor)) (natp (nth 5 cursor)) (natp (nth 6 cursor))
       (if (equal (nth 0 cursor) :emit)
           (and (fn-orf-invariant (nth 8 cursor))
                (member-eq (nth 9 cursor) '(:peers :obligations :release :done)))
         (and (member-eq (nth 0 cursor) '(:count-pins :peers :obligations :release :done))
              (equal (nth 8 cursor) nil) (equal (nth 9 cursor) nil)))))

(defthm fn-orr-invariant-implies-ready
  (implies (fn-orr-invariant cursor) (fn-orr-ready-p cursor))
  :hints (("Goal" :in-theory
           (enable fn-orr-invariant fn-orr-ready-p fn-orf-invariant))))

; Actual output ABI matches fn-orf: (mv next-cursor octets done).
; One turn counts one pin, schedules one fixed descriptor spine, or performs
; one emitter quantum. A pending continuation emits no octet itself.
(defun fn-orr-step (cursor)
  (declare (xargs :guard (fn-orr-ready-p cursor) :verify-guards nil))
  (let ((phase (nth 0 cursor)) (feeds (nth 1 cursor))
        (pins (nth 2 cursor)) (root (nth 3 cursor))
        (u (nfix (nth 4 cursor))) (held (nfix (nth 5 cursor)))
        (reserved (nfix (nth 6 cursor))) (outcome (nth 7 cursor)))
    (case phase
      (:count-pins
       (mv (if (consp pins)
               (fn-orr-cursor :count-pins feeds (cdr pins) root u (+ 1 held)
                              reserved outcome nil nil)
             (fn-orr-cursor :peers feeds root root u held reserved outcome nil nil))
           nil nil))
      (:peers
       (if (consp feeds)
           (let* ((entry (car feeds)) (feed (fn-own-feed-entry-feed entry))
                  (undelivered (nfix (fn-feed-undelivered feed))))
             (mv (fn-orr-schedule
                  (fn-orr-peer-fields entry)
                  :peers (cdr feeds) pins root (+ u undelivered) held reserved outcome)
                 nil nil))
         (mv (fn-orr-schedule (fn-ord-header held reserved) :obligations
                              feeds pins root u held reserved outcome) nil nil)))
      (:obligations
       (if (consp pins)
           (let ((pin (car pins)))
             (mv (fn-orr-schedule
                  (fn-orr-obligation-fields pin)
                  :obligations feeds (cdr pins) root u held reserved outcome)
                 nil nil))
         (mv (fn-orr-schedule (fn-ord-end (equal outcome :drained) u held)
                              :release feeds pins root u held reserved outcome)
             nil nil)))
      (:release
       (if (and (zp u) (zp held))
           (mv (fn-orr-cursor :done feeds pins root u held reserved outcome nil nil) nil t)
         (mv (fn-orr-schedule (fn-ord-release) :done
                              feeds pins root u held reserved outcome) nil nil)))
      (:emit
       (mv-let (next output done) (fn-orf-step (nth 8 cursor))
         (mv (fn-orr-cursor (if done (nth 9 cursor) :emit)
                            feeds pins root u held reserved outcome
                            (if done nil next) (if done nil (nth 9 cursor)))
             output (and done (equal (nth 9 cursor) :done)))))
      (otherwise (mv cursor nil t)))))

(verify-guards fn-orr-step
  :hints (("Goal" :in-theory (enable fn-orr-ready-p))))

(defthm fn-orr-start-invariant
  (fn-orr-invariant (fn-orr-start step oc))
  :hints (("Goal" :in-theory (enable fn-orr-invariant fn-orr-start))))

(defthm fn-orr-step-preserves-invariant
  (implies (fn-orr-invariant cursor)
           (fn-orr-invariant (mv-nth 0 (fn-orr-step cursor))))
  :hints (("Goal"
           :use ((:instance fn-orf-step-preserves-invariant (c (nth 8 cursor))))
           :in-theory
           (e/d (fn-orr-step fn-orr-cursor fn-orr-schedule fn-orr-invariant)
                (fn-orf-step fn-orf-start fn-orf-invariant
                 fn-ord-peer fn-ord-header fn-ord-obligation fn-ord-end
                 fn-orf-step-preserves-invariant)))))

; The weaker guarded quantum statement had a redundant hypothesis. This
; unconditional logical theorem is proved; outside guards it permits no
; runtime use of an invalid cursor.
(defthm fn-orr-step-output-quantum-unconditional
  (and (true-listp (mv-nth 1 (fn-orr-step cursor)))
       (<= (len (mv-nth 1 (fn-orr-step cursor))) 1))
  :hints (("Goal" :in-theory (enable fn-orr-step fn-orf-step))))

(defthm fn-orr-step-output-octet
  (implies (and (fn-orr-invariant cursor)
                (consp (mv-nth 1 (fn-orr-step cursor))))
           (and (integerp (car (mv-nth 1 (fn-orr-step cursor))))
                (<= 0 (car (mv-nth 1 (fn-orr-step cursor))))
                (< (car (mv-nth 1 (fn-orr-step cursor))) 256)))
  :hints (("Goal"
           :use ((:instance fn-orf-step-output-octet (c (nth 8 cursor))))
           :in-theory (e/d (fn-orr-step fn-orr-invariant)
                           (fn-orf-step fn-orf-invariant fn-orf-step-output-octet)))))

(defthm fn-orr-step-done-is-final
  (implies (and (fn-orr-invariant cursor) (mv-nth 2 (fn-orr-step cursor)))
           (equal (nth 0 (mv-nth 0 (fn-orr-step cursor))) :done))
  :hints (("Goal" :in-theory
           (e/d (fn-orr-step fn-orr-cursor fn-orr-invariant)
                (fn-orf-step fn-orf-invariant)))))

; Proof-only rank. Its table/string/digit traversals are never host-called.
(defun fn-orr-phase-height (phase feeds pins root)
  (declare (xargs :guard t))
  (case phase
    (:count-pins (+ (len pins) (len feeds) (len root) 4))
    (:peers (+ (len feeds) (len pins) 3))
    (:obligations (+ (len pins) 2))
    (:release 1)
    (otherwise 0)))

(defun fn-orr-rank (cursor)
  (declare (xargs :guard (fn-orr-invariant cursor) :verify-guards nil))
  (let* ((phase (nth 0 cursor)) (feeds (nth 1 cursor)) (pins (nth 2 cursor))
         (root (nth 3 cursor)) (u (nfix (nth 4 cursor)))
         (held (nfix (nth 5 cursor))) (reserved (nfix (nth 6 cursor)))
         (outcome (nth 7 cursor))
         (major (if (equal phase :emit)
                    (+ 1 (fn-orr-phase-height (nth 9 cursor) feeds pins root))
                  (fn-orr-phase-height phase feeds pins root)))
         (minor
          (case phase
            (:emit (fn-orf-rank (nth 8 cursor)))
            (:peers (+ 1 (nfix (fn-orf-rank
                          (fn-orf-start (if (consp feeds)
                                            (fn-orr-peer-fields (car feeds))
                                          (fn-ord-header held reserved)))))))
            (:obligations (+ 1 (nfix (fn-orf-rank
                                (fn-orf-start (if (consp pins)
                                                  (fn-orr-obligation-fields (car pins))
                                                (fn-ord-end (equal outcome :drained) u held)))))))
            (:release (if (and (zp u) (zp held)) 0
                        (+ 1 (nfix (fn-orf-rank (fn-orf-start (fn-ord-release)))))))
            (otherwise 0))))
    (make-ord 1 (+ 1 (nfix major)) (nfix minor))))

(defthm fn-orr-ordinal-coefficients
  (implies (and (posp a) (posp b) (natp x) (natp y))
           (equal (o< (make-ord 1 a x) (make-ord 1 b y))
                  (or (< a b) (and (equal a b) (< x y)))))
  :hints (("Goal" :in-theory (enable o< make-ord o-finp o-first-expt o-first-coeff o-rst))))

(defthm fn-orr-rank-ordinal
  (o-p (fn-orr-rank cursor))
  :hints (("Goal" :in-theory (enable fn-orr-rank make-ord o-p o-finp o-first-expt o-first-coeff o-rst))))

(defthm fn-orr-step-decreases-rank
  (implies (and (fn-orr-invariant cursor) (not (equal (nth 0 cursor) :done)))
           (o< (fn-orr-rank (mv-nth 0 (fn-orr-step cursor))) (fn-orr-rank cursor)))
  :hints (("Goal"
           :use ((:instance fn-orf-step-decreases-rank (c (nth 8 cursor)))
                 (:instance fn-orf-terminal-stable (c (nth 8 cursor)))
                 (:instance fn-orf-step-preserves-invariant (c (nth 8 cursor)))
                 (:instance fn-orf-rank-natural (c (nth 8 cursor)))
                 (:instance fn-orf-rank-natural (c (mv-nth 0 (fn-orf-step (nth 8 cursor))))))
           :in-theory
           (e/d (fn-orr-step fn-orr-cursor fn-orr-schedule fn-orr-invariant fn-orr-rank fn-orr-phase-height)
                (fn-orf-step fn-orf-start fn-orf-invariant fn-orf-rank make-ord o<
                 (:executable-counterpart make-ord)
                 fn-orf-step-decreases-rank fn-orf-terminal-stable fn-orf-step-preserves-invariant)))))

(defthm fn-orr-invariant-true-listp
  (implies (fn-orr-invariant cursor) (true-listp cursor))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :in-theory (enable fn-orr-invariant))))

; Complete interpreter is proof-only: production calls STEP, never RUN/RANK.
(defun fn-orr-run (cursor)
  (declare (xargs :guard (fn-orr-invariant cursor) :verify-guards nil
                  :measure (if (fn-orr-invariant cursor) (fn-orr-rank cursor) 0)
                  :hints (("Goal" :use ((:instance fn-orr-step-decreases-rank))
                           :in-theory (disable fn-orr-step fn-orr-invariant fn-orr-rank mv-nth
                                               fn-orr-step-decreases-rank)))))
  (if (or (not (fn-orr-invariant cursor)) (equal (nth 0 cursor) :done))
      nil
    (mv-let (next output done) (fn-orr-step cursor)
      (append output (if done nil (fn-orr-run next))))))

(verify-guards fn-orr-run
  :hints (("Goal"
           :use ((:instance fn-orr-step-preserves-invariant)
                 (:instance fn-orr-step-output-quantum-unconditional))
           :in-theory (disable fn-orr-step fn-orr-invariant fn-orr-rank mv-nth))))

(local
 (defthm fn-orr-retry-count-is-health-count
   (equal (fn-fct-retry-drops-model queue) (fn-nh-dropped-count queue))
   :hints (("Goal" :induct (fn-fct-retry-drops-model queue)
            :in-theory (enable fn-fct-retry-drops-model fn-fct-retry-drop-bit
                               fn-nh-dropped-count)))))

(defthm fn-orr-peer-line-is-reference
  (implies (fn-feed-count-relationp (fn-own-feed-entry-feed entry))
           (equal (fn-orr-peer-line entry) (fn-oret-peer-line entry)))
  :hints (("Goal" :in-theory (enable fn-orr-peer-line fn-oret-peer-line
                                     fn-feed-count-relationp
                                     ))))

(defthm fn-orr-peer-fields-reference
  (equal (fn-orf-nls-reference (fn-orr-peer-fields entry)) (fn-orr-peer-line entry))
  :hints (("Goal" :in-theory (enable fn-orr-peer-fields fn-ord-peer fn-orf-nls-reference
                                     fn-orr-peer-line fn-nls-field fn-nls-value))))

(defthm fn-orr-obligation-fields-reference
  (implies (fn-orr-pin-domainp pin)
           (equal (fn-orf-nls-reference (fn-orr-obligation-fields pin))
                  (fn-nls-obligation-line pin)))
  :hints (("Goal" :in-theory (enable fn-orr-pin-domainp fn-orr-obligation-fields
                                     fn-ord-obligation fn-orf-nls-reference
                                     fn-nls-obligation-line fn-nls-field fn-nls-value
                                     fn-nls-kind-words))))

(in-theory (disable fn-orr-start fn-orr-step fn-orr-peer-line fn-orr-end-line))
