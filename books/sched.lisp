; A4 scheduler: one global machine index, intrusive principal FIFOs, fixed calendar.
(in-package "ACL2")
(include-book "columns")
(include-book "machines")
(include-book "profile")
(include-book "exec-state")
(include-book "owed")

(defconst *fn2-sched-anonymous* 0)
(defconst *fn2-timer-service-slot* 1)
(defconst *fn2-timer-service-step-max* 16)

(defcolumns fn2-sched
  ((principal :u16) (in-queue :bool) (prev :link) (next :link) (deadline :u60) (expired :bool))
  :init-name fn2-sched-columns-init
  :extra-fields
  ((fn2-sched-heads :type (array (unsigned-byte 32) (0)) :initially *fn2-none* :resizable t :why "Runnable FIFO heads are indexed by principal, not machine.")
   (fn2-sched-tails :type (array (unsigned-byte 32) (0)) :initially *fn2-none* :resizable t :why "Runnable FIFO tails are indexed by principal, not machine.")
   (fn2-sched-counts :type (array (unsigned-byte 32) (0)) :initially 0 :resizable t :why "Queue lengths are indexed by principal, not machine.")
   (fn2-sched-calendar :type (array (unsigned-byte 32) (0)) :initially 0 :resizable t :why "Visit positions follow calendar geometry, not row capacity.")
   (fn2-sched-services :type (array (unsigned-byte 1) (*fn2-calendar-services*)) :initially 0 :why "Four service postures are independent of machine population.")
   (fn2-sched-nprincipals :type (unsigned-byte 32) :initially 0 :why "Principal cardinality governs the principal-indexed arrays.")
   (fn2-sched-cursor :type (unsigned-byte 32) :initially 0 :why "One calendar position is shared by all visits.")
   (fn2-sched-queued :type (unsigned-byte 32) :initially 0 :why "Aggregate runnable population permits constant-time eligibility.")
   (fn2-sched-armed-timers :type (unsigned-byte 32) :initially 0 :why "Active machine deadlines permit constant-time timer readiness.")
   (fn2-sched-earliest-deadline :type (unsigned-byte 60) :initially *fn2-no-deadline* :why "Earliest unvisited machine deadline survives clock mailbox consumption.")
   (fn2-sched-scan-min :type (unsigned-byte 60) :initially *fn2-no-deadline* :why "Running minimum deadline across a bounded multi-turn timer sweep.")))

;; The weighted calendar (D7's S3).  A principal slot of weight w (1..255) appears w times per
;; round: pass k lists, in slot order, every slot whose weight exceeds k.  After every sixteen
;; principal entries, and after the last, the four services follow (commit, timer/grant, wake,
;; maintenance).  L = W + 4*ceiling(W/16) for W the sum of the weights
;; (`fn2-profile-calendar-length`); with every weight 1 it is the unweighted calendar, entry
;; for entry.  A calendar with any weight above 1 has at most 4,096 entries.
(defconst *fn2-sched-weighted-calendar-max* 4096)
(defun fn2-sched-weightsp (weights)
  (declare (xargs :guard t))
  (if (atom weights) (null weights)
    (and (integerp (car weights)) (<= 1 (car weights)) (<= (car weights) 255)
         (fn2-sched-weightsp (cdr weights)))))
(defun fn2-sched-weights-onesp (weights)
  (declare (xargs :guard t))
  (if (atom weights) t (and (equal (car weights) 1) (fn2-sched-weights-onesp (cdr weights)))))
(defun fn2-sched-weights-max (weights)
  (declare (xargs :guard t))
  (if (atom weights) 0 (max (nfix (car weights)) (fn2-sched-weights-max (cdr weights)))))
(defun fn2-sched-pass (weights k slot)
  (declare (xargs :guard (and (natp k) (natp slot))))
  (if (atom weights) nil
    (if (< k (nfix (car weights)))
        (cons slot (fn2-sched-pass (cdr weights) k (+ 1 slot)))
      (fn2-sched-pass (cdr weights) k (+ 1 slot)))))
(defun fn2-sched-principal-sequence (weights k top)
  (declare (xargs :guard (and (natp k) (natp top)) :measure (nfix (- (nfix top) (nfix k)))))
  (if (or (not (natp k)) (>= k (nfix top))) nil
    (append (fn2-sched-pass weights k 0)
            (fn2-sched-principal-sequence weights (+ 1 k) top))))
(defun fn2-sched-calendar-entries (sequence p in-block)
  (declare (xargs :guard (and (natp p) (natp in-block))))
  (if (atom sequence) nil
    (cons (car sequence)
          (if (or (atom (cdr sequence)) (>= in-block (1- *fn2-calendar-principals-per-group*)))
              (list* p (+ p 1) (+ p 2) (+ p 3)
                     (fn2-sched-calendar-entries (cdr sequence) p 0))
            (fn2-sched-calendar-entries (cdr sequence) p (+ 1 in-block))))))
(defun fn2-sched-calendar-list (weights)
  (declare (xargs :guard t))
  (fn2-sched-calendar-entries
   (fn2-sched-principal-sequence weights 0 (fn2-sched-weights-max weights)) (len weights) 0))

;; WEIGHTS is the calendar's weight list, one per principal slot (the core passes
;; `(fn2-profile-weights profile)`).
(defun fn2-sched-init-weightsp (profile weights)
  (declare (xargs :guard t))
  (and (fn2-sched-weightsp weights)
       (equal (len weights) (nfix (fn2-profile-p profile)))
       (unsigned-byte-p 32 (len (fn2-sched-calendar-list weights)))))

; Init accepts precisely the declared calendar geometry: the profile's weights (all 1 unless
; :accounts configures them), one per principal slot.
(defun fn2-sched-profilep (profile)
  (declare (xargs :guard t))
  (and (fn2-profilep profile)
       (posp (fn2-profile-p profile)) (<= (fn2-profile-p profile) 65536)
       (fn2-sched-init-weightsp profile (fn2-profile-weights profile))
       (or (fn2-sched-weights-onesp (fn2-profile-weights profile))
           (<= (len (fn2-sched-calendar-list (fn2-profile-weights profile)))
               *fn2-sched-weighted-calendar-max*))))
(defthm fn2-sched-profilep-weights
  (implies (fn2-sched-profilep profile)
           (fn2-sched-init-weightsp profile (fn2-profile-weights profile))))

(defun fn2-sched-principalp (principal fn2-sched)
  (declare (xargs :stobjs fn2-sched))
  (and (natp principal) (< principal (fn2-sched-nprincipals fn2-sched))
       (< principal 65536)
       (< principal (fn2-sched-heads-length fn2-sched))
       (< principal (fn2-sched-tails-length fn2-sched))
       (< principal (fn2-sched-counts-length fn2-sched))))

(defun fn2-sched-clear-machines (i fn2-sched)
  (declare (xargs :stobjs fn2-sched :guard (and (natp i) (fn2-sched-wfp fn2-sched))
                  :measure (nfix (- (nfix (fn2-sched-rows fn2-sched)) (nfix i)))))
  (if (or (not (natp i)) (>= i (nfix (fn2-sched-rows fn2-sched)))) fn2-sched
    (let* ((fn2-sched (fn2-sched-set-principal i 0 fn2-sched))
           (fn2-sched (fn2-sched-set-in-queue i 0 fn2-sched))
           (fn2-sched (fn2-sched-set-prev i *fn2-none* fn2-sched))
           (fn2-sched (fn2-sched-set-next i *fn2-none* fn2-sched))
           (fn2-sched (fn2-sched-set-deadline i *fn2-no-deadline* fn2-sched))
           (fn2-sched (fn2-sched-set-expired i 0 fn2-sched)))
      (fn2-sched-clear-machines (+ 1 i) fn2-sched))))
(defthm fn2-sched-clear-machines-wfp
  (implies (fn2-sched-wfp fn2-sched)
           (fn2-sched-wfp (fn2-sched-clear-machines i fn2-sched))))
(defthm fn2-sched-clear-machines-type
  (implies (and (fn2-schedp fn2-sched) (fn2-sched-wfp fn2-sched) (natp i))
           (fn2-schedp (fn2-sched-clear-machines i fn2-sched))))
(in-theory (disable fn2-sched-clear-machines))

(defun fn2-sched-clear-principals (i fn2-sched)
  (declare (xargs :stobjs fn2-sched :guard (natp i)
                  :measure (nfix (- (fn2-sched-heads-length fn2-sched) (nfix i)))))
  (if (not (fn2-sched-principalp i fn2-sched)) fn2-sched
    (let* ((fn2-sched (update-fn2-sched-headsi i *fn2-none* fn2-sched))
           (fn2-sched (update-fn2-sched-tailsi i *fn2-none* fn2-sched))
           (fn2-sched (update-fn2-sched-countsi i 0 fn2-sched)))
      (fn2-sched-clear-principals (+ 1 i) fn2-sched))))
(defthm fn2-sched-clear-principals-wfp
  (implies (fn2-sched-wfp fn2-sched)
           (fn2-sched-wfp (fn2-sched-clear-principals i fn2-sched))))
(defthm fn2-sched-clear-principals-type
  (implies (and (fn2-schedp fn2-sched) (fn2-sched-wfp fn2-sched) (natp i))
           (fn2-schedp (fn2-sched-clear-principals i fn2-sched))))
(in-theory (disable fn2-sched-clear-principals))

(defun fn2-sched-fill-calendar (i codes fn2-sched)
  (declare (xargs :stobjs fn2-sched :guard (natp i)
                  :measure (len codes)))
  (if (or (atom codes) (not (natp i)) (>= i (fn2-sched-calendar-length fn2-sched))) fn2-sched
    (let ((fn2-sched (update-fn2-sched-calendari
                      i (if (unsigned-byte-p 32 (car codes)) (car codes) 0) fn2-sched)))
      (fn2-sched-fill-calendar (+ 1 i) (cdr codes) fn2-sched))))
(defthm fn2-sched-fill-calendar-wfp
  (implies (fn2-sched-wfp fn2-sched)
           (fn2-sched-wfp (fn2-sched-fill-calendar i codes fn2-sched))))
(defthm fn2-sched-fill-calendar-type
  (implies (and (fn2-schedp fn2-sched) (fn2-sched-wfp fn2-sched) (natp i))
           (fn2-schedp (fn2-sched-fill-calendar i codes fn2-sched))))
(in-theory (disable fn2-sched-fill-calendar))

(defun fn2-sched-init (profile weights n fn2-sched)
  (declare (xargs :stobjs fn2-sched
                  :guard (and (fn2-sched-profilep profile) (fn2-sched-init-weightsp profile weights)
                              (unsigned-byte-p 32 n))))
  (let* ((p (fn2-profile-p profile))
         (codes (fn2-sched-calendar-list weights))
         (fn2-sched (fn2-sched-columns-init n fn2-sched))
         (fn2-sched (resize-fn2-sched-heads p fn2-sched))
         (fn2-sched (resize-fn2-sched-tails p fn2-sched))
         (fn2-sched (resize-fn2-sched-counts p fn2-sched))
         (fn2-sched (resize-fn2-sched-calendar (len codes) fn2-sched))
         (fn2-sched (update-fn2-sched-nprincipals p fn2-sched))
         (fn2-sched (update-fn2-sched-cursor 0 fn2-sched))
         (fn2-sched (update-fn2-sched-queued 0 fn2-sched))
         (fn2-sched (update-fn2-sched-armed-timers 0 fn2-sched))
         (fn2-sched (update-fn2-sched-earliest-deadline *fn2-no-deadline* fn2-sched))
         (fn2-sched (update-fn2-sched-scan-min *fn2-no-deadline* fn2-sched))
         (fn2-sched (update-fn2-sched-servicesi 0 0 fn2-sched))
         (fn2-sched (update-fn2-sched-servicesi 1 0 fn2-sched))
         (fn2-sched (update-fn2-sched-servicesi 2 0 fn2-sched))
         (fn2-sched (update-fn2-sched-servicesi 3 0 fn2-sched))
         (fn2-sched (fn2-sched-clear-machines 0 fn2-sched))
         (fn2-sched (fn2-sched-clear-principals 0 fn2-sched)))
    (fn2-sched-fill-calendar 0 codes fn2-sched)))
(defthm fn2-sched-init-wfp
  (implies (and (fn2-sched-profilep profile) (unsigned-byte-p 32 n))
           (fn2-sched-wfp (fn2-sched-init profile weights n fn2-sched))))
(defthm fn2-sched-init-type
  (implies (and (fn2-schedp fn2-sched) (fn2-sched-profilep profile) (unsigned-byte-p 32 n))
           (fn2-schedp (fn2-sched-init profile weights n fn2-sched))))
(in-theory (disable fn2-sched-init fn2-sched-profilep fn2-sched-init-weightsp))

(defun fn2-sched-make-runnable (machine principal fn2-sched)
  (declare (xargs :stobjs fn2-sched :guard (fn2-sched-wfp fn2-sched)))
  (cond
   ((not (and (natp machine) (< machine (fn2-sched-rows fn2-sched))
              (fn2-sched-principalp principal fn2-sched))) (mv :bounds fn2-sched))
   ((= (fn2-sched-in-queue machine fn2-sched) 1) (mv :already fn2-sched))
   (t
    (let ((tail (fn2-sched-tailsi principal fn2-sched))
          (count (fn2-sched-countsi principal fn2-sched)))
      (if (or (>= count *fn2-none*)
              (>= (fn2-sched-queued fn2-sched) *fn2-none*)
              (and (< 0 count) (>= tail (fn2-sched-rows fn2-sched))))
          (mv :state fn2-sched)
        (let* ((fn2-sched (fn2-sched-set-principal machine principal fn2-sched))
               (fn2-sched (fn2-sched-set-in-queue machine 1 fn2-sched))
               (fn2-sched (fn2-sched-set-prev machine
                           (if (= count 0) *fn2-none* tail) fn2-sched))
               (fn2-sched (fn2-sched-set-next machine *fn2-none* fn2-sched))
               (fn2-sched (if (= count 0)
                              (update-fn2-sched-headsi principal machine fn2-sched)
                            (fn2-sched-set-next tail machine fn2-sched)))
               (fn2-sched (update-fn2-sched-tailsi principal machine fn2-sched))
               (fn2-sched (update-fn2-sched-countsi principal (+ count 1) fn2-sched))
               (fn2-sched (update-fn2-sched-queued
                           (+ 1 (fn2-sched-queued fn2-sched)) fn2-sched)))
          (mv :ok fn2-sched)))))))

(defun fn2-sched-pop-head (principal fn2-sched)
  (declare (xargs :stobjs fn2-sched :guard (fn2-sched-wfp fn2-sched)))
  (cond ((not (fn2-sched-principalp principal fn2-sched))
         (mv :bounds *fn2-none* fn2-sched))
        ((= (fn2-sched-countsi principal fn2-sched) 0)
         (mv :empty *fn2-none* fn2-sched))
        (t
         (let ((head (fn2-sched-headsi principal fn2-sched))
               (count (fn2-sched-countsi principal fn2-sched)))
           (if (or (>= head (fn2-sched-rows fn2-sched))
                   (= (fn2-sched-queued fn2-sched) 0))
               (mv :state *fn2-none* fn2-sched)
             (let ((next (fn2-sched-next head fn2-sched)))
               (if (and (< 1 count) (>= next (fn2-sched-rows fn2-sched)))
                   (mv :state *fn2-none* fn2-sched)
                 (let* ((fn2-sched (fn2-sched-set-in-queue head 0 fn2-sched))
                        (fn2-sched (fn2-sched-set-prev head *fn2-none* fn2-sched))
                        (fn2-sched (fn2-sched-set-next head *fn2-none* fn2-sched))
                        (fn2-sched (update-fn2-sched-headsi principal
                                    (if (= count 1) *fn2-none* next) fn2-sched))
                        (fn2-sched (if (= count 1)
                                       (update-fn2-sched-tailsi principal *fn2-none* fn2-sched)
                                     (fn2-sched-set-prev next *fn2-none* fn2-sched)))
                        (fn2-sched (update-fn2-sched-countsi principal (- count 1) fn2-sched))
                        (fn2-sched (update-fn2-sched-queued (- (fn2-sched-queued fn2-sched) 1) fn2-sched)))
                   (mv :ok head fn2-sched)))))))))

;; Re-attribution (D7's S4): MACHINE's scheduler membership moves to principal TO.
;; Queued: unlinked from its FIFO (head, middle or tail) and appended to TO's tail,
;; one step; not queued: only its principal column is set.  Every link check precedes
;; the first write, so a refusal (:bounds, :state) leaves the scheduler unchanged.
(defun fn2-sched-reattribute (machine to fn2-sched)
  (declare (xargs :stobjs fn2-sched :guard (fn2-sched-wfp fn2-sched)))
  (cond
   ((not (and (natp machine) (< machine (fn2-sched-rows fn2-sched))
              (fn2-sched-principalp to fn2-sched))) (mv :bounds fn2-sched))
   ((not (= (fn2-sched-in-queue machine fn2-sched) 1))
    (let ((fn2-sched (fn2-sched-set-principal machine to fn2-sched))) (mv :ok fn2-sched)))
   (t
    (let* ((from (fn2-sched-principal machine fn2-sched))
           (rows (fn2-sched-rows fn2-sched)))
      (cond
       ((not (fn2-sched-principalp from fn2-sched)) (mv :state fn2-sched))
       ((equal from to) (mv :ok fn2-sched))
       (t
        (let ((prev (fn2-sched-prev machine fn2-sched))
              (next (fn2-sched-next machine fn2-sched))
              (fcount (fn2-sched-countsi from fn2-sched))
              (tcount (fn2-sched-countsi to fn2-sched))
              (ttail (fn2-sched-tailsi to fn2-sched)))
          (if (or (= fcount 0) (>= tcount *fn2-none*)
                  (and (< 0 tcount) (>= ttail rows))
                  (if (= prev *fn2-none*)
                      (not (= (fn2-sched-headsi from fn2-sched) machine))
                    (>= prev rows))
                  (if (= next *fn2-none*)
                      (not (= (fn2-sched-tailsi from fn2-sched) machine))
                    (>= next rows)))
              (mv :state fn2-sched)
            (let* ((fn2-sched (if (= prev *fn2-none*)
                                  (update-fn2-sched-headsi from next fn2-sched)
                                (fn2-sched-set-next prev next fn2-sched)))
                   (fn2-sched (if (= next *fn2-none*)
                                  (update-fn2-sched-tailsi from prev fn2-sched)
                                (fn2-sched-set-prev next prev fn2-sched)))
                   (fn2-sched (update-fn2-sched-countsi from (- fcount 1) fn2-sched))
                   (fn2-sched (fn2-sched-set-principal machine to fn2-sched))
                   (fn2-sched (fn2-sched-set-prev machine
                               (if (= tcount 0) *fn2-none* ttail) fn2-sched))
                   (fn2-sched (fn2-sched-set-next machine *fn2-none* fn2-sched))
                   (fn2-sched (if (= tcount 0)
                                  (update-fn2-sched-headsi to machine fn2-sched)
                                (fn2-sched-set-next ttail machine fn2-sched)))
                   (fn2-sched (update-fn2-sched-tailsi to machine fn2-sched))
                   (fn2-sched (update-fn2-sched-countsi to (+ tcount 1) fn2-sched)))
              (mv :ok fn2-sched))))))))))

; Return the entry's kind, principal slot (zero for services), and OLD cursor.
; An empty calendar is an uninitialized scheduler, represented by kind=255.
(defun fn2-sched-visit (fn2-sched)
  (declare (xargs :stobjs fn2-sched))
  (let ((position (fn2-sched-cursor fn2-sched))
        (length (fn2-sched-calendar-length fn2-sched))
        (p (fn2-sched-nprincipals fn2-sched)))
    (if (>= position length) (mv *fn2-visit-none* 0 position fn2-sched)
      (let* ((code (fn2-sched-calendari position fn2-sched))
             (next (if (< (+ position 1) length) (+ position 1) 0))
             (fn2-sched (update-fn2-sched-cursor
                         (if (unsigned-byte-p 32 next) next 0) fn2-sched)))
        (cond ((< code p) (mv *fn2-visit-principal* code position fn2-sched))
              ((< code (+ p *fn2-calendar-services*)) (mv (+ *fn2-visit-commit* (- code p)) 0 position fn2-sched))
              (t (mv *fn2-visit-none* 0 position fn2-sched)))))))

(defun fn2-sched-set-service (service ready fn2-sched)
  (declare (xargs :stobjs fn2-sched :guard (and (natp service) (< service *fn2-calendar-services*)
                                                              (unsigned-byte-p 1 ready))))
  (update-fn2-sched-servicesi service ready fn2-sched))
(defun fn2-sched-service-ready (service fn2-sched)
  (declare (xargs :stobjs fn2-sched :guard (and (natp service) (< service *fn2-calendar-services*))))
  (= (fn2-sched-servicesi service fn2-sched) 1))
(defun fn2-sched-eligiblep (fn2-sched)
  (declare (xargs :stobjs fn2-sched))
  (or (< 0 (fn2-sched-queued fn2-sched))
      (fn2-sched-service-ready 0 fn2-sched) (fn2-sched-service-ready 1 fn2-sched)
      (fn2-sched-service-ready 2 fn2-sched) (fn2-sched-service-ready 3 fn2-sched)))

(defthm fn2-sched-make-runnable-wfp
  (implies (and (fn2-schedp fn2-sched) (fn2-sched-wfp fn2-sched))
           (fn2-sched-wfp (mv-nth 1 (fn2-sched-make-runnable machine principal fn2-sched)))))
(defthm fn2-sched-pop-head-wfp
  (implies (and (fn2-schedp fn2-sched) (fn2-sched-wfp fn2-sched))
           (fn2-sched-wfp (mv-nth 2 (fn2-sched-pop-head principal fn2-sched)))))
(defthm fn2-sched-visit-wfp
  (implies (fn2-sched-wfp fn2-sched)
           (fn2-sched-wfp (mv-nth 3 (fn2-sched-visit fn2-sched)))))
(defthm fn2-sched-make-runnable-type
  (implies (and (fn2-schedp fn2-sched) (fn2-sched-wfp fn2-sched))
           (fn2-schedp (mv-nth 1 (fn2-sched-make-runnable machine principal fn2-sched)))))
(defthm fn2-sched-make-runnable-rows
  (equal (fn2-sched-rows (mv-nth 1 (fn2-sched-make-runnable machine principal fn2-sched))) (fn2-sched-rows fn2-sched)))
(defthm fn2-sched-make-runnable-raw-rows
  (equal (nth *fn2-sched-rows* (mv-nth 1 (fn2-sched-make-runnable machine principal fn2-sched)))
         (nth *fn2-sched-rows* fn2-sched)))
(defthm fn2-sched-pop-head-type
  (implies (and (fn2-schedp fn2-sched) (fn2-sched-wfp fn2-sched))
           (fn2-schedp (mv-nth 2 (fn2-sched-pop-head principal fn2-sched)))))
(defthm fn2-sched-pop-head-rows
  (equal (fn2-sched-rows (mv-nth 2 (fn2-sched-pop-head principal fn2-sched))) (fn2-sched-rows fn2-sched)))
(defthm fn2-sched-reattribute-wfp
  (implies (and (fn2-schedp fn2-sched) (fn2-sched-wfp fn2-sched))
           (fn2-sched-wfp (mv-nth 1 (fn2-sched-reattribute machine to fn2-sched)))))
(defthm fn2-sched-reattribute-type
  (implies (and (fn2-schedp fn2-sched) (fn2-sched-wfp fn2-sched))
           (fn2-schedp (mv-nth 1 (fn2-sched-reattribute machine to fn2-sched)))))
(defthm fn2-sched-reattribute-rows
  (equal (fn2-sched-rows (mv-nth 1 (fn2-sched-reattribute machine to fn2-sched))) (fn2-sched-rows fn2-sched)))
(defthm fn2-sched-visit-type
  (implies (and (fn2-schedp fn2-sched) (fn2-sched-wfp fn2-sched))
           (fn2-schedp (mv-nth 3 (fn2-sched-visit  fn2-sched)))))
(defthm fn2-sched-visit-rows
  (equal (fn2-sched-rows (mv-nth 3 (fn2-sched-visit  fn2-sched))) (fn2-sched-rows fn2-sched)))
(in-theory (disable fn2-sched-make-runnable fn2-sched-pop-head fn2-sched-reattribute fn2-sched-visit))

;; Calendar timer service (resources.lisp :timer): per-row monotonic deadlines
;; and bounded resumable expiration over fn2-control-now / fn2-control-timer-cursor.
(defun fn2-sched-arm-deadline (machine deadline fn2-sched fn2-control)
  (declare (xargs :stobjs (fn2-sched fn2-control)
                  :guard (and (fn2-sched-wfp fn2-sched) (fn2-control-wfp fn2-control))))
  (cond
   ((not (and (natp machine) (< machine (fn2-sched-rows fn2-sched))
              (unsigned-byte-p 60 deadline) (< deadline *fn2-no-deadline*)))
    (mv :bounds fn2-sched fn2-control))
   (t
    (let* ((was-unarmed (= (fn2-sched-deadline machine fn2-sched) *fn2-no-deadline*))
           (armed (fn2-sched-armed-timers fn2-sched)))
      (if (and was-unarmed (>= armed *fn2-none*))
          (mv :state fn2-sched fn2-control)
        (let* ((fn2-sched (fn2-sched-set-deadline machine deadline fn2-sched))
               (fn2-sched (fn2-sched-set-expired machine 0 fn2-sched))
               (fn2-sched (if was-unarmed
                              (update-fn2-sched-armed-timers (+ 1 armed) fn2-sched)
                            fn2-sched))
               (fn2-sched (if (< deadline (fn2-sched-earliest-deadline fn2-sched))
                              (update-fn2-sched-earliest-deadline deadline fn2-sched)
                            fn2-sched))
               (fn2-sched (if (< deadline (fn2-sched-scan-min fn2-sched))
                              (update-fn2-sched-scan-min deadline fn2-sched)
                            fn2-sched))
               (fn2-sched (if (<= deadline (fn2-control-now fn2-control))
                              (fn2-sched-set-service *fn2-timer-service-slot* 1 fn2-sched)
                            fn2-sched))
               (fn2-control (if (< deadline (fn2-control-idle-deadline fn2-control))
                                (update-fn2-control-idle-deadline deadline fn2-control)
                              fn2-control)))
          (mv :ok fn2-sched fn2-control)))))))

(defthm fn2-sched-arm-deadline-sched-wfp
  (implies (and (fn2-schedp fn2-sched) (fn2-sched-wfp fn2-sched))
           (fn2-sched-wfp (mv-nth 1 (fn2-sched-arm-deadline machine deadline fn2-sched fn2-control)))))
(defthm fn2-sched-arm-deadline-sched-type
  (implies (and (fn2-schedp fn2-sched) (fn2-sched-wfp fn2-sched))
           (fn2-schedp (mv-nth 1 (fn2-sched-arm-deadline machine deadline fn2-sched fn2-control)))))
(defthm fn2-sched-arm-deadline-sched-rows
  (equal (fn2-sched-rows (mv-nth 1 (fn2-sched-arm-deadline machine deadline fn2-sched fn2-control)))
         (fn2-sched-rows fn2-sched)))
(defthm fn2-sched-arm-deadline-control-wfp
  (implies (fn2-control-wfp fn2-control)
           (fn2-control-wfp (mv-nth 2 (fn2-sched-arm-deadline machine deadline fn2-sched fn2-control)))))
(defthm fn2-sched-arm-deadline-control-type
  (implies (fn2-controlp fn2-control)
           (fn2-controlp (mv-nth 2 (fn2-sched-arm-deadline machine deadline fn2-sched fn2-control)))))
(defthm fn2-sched-arm-deadline-refusal
  (implies (not (eq (mv-nth 0 (fn2-sched-arm-deadline machine deadline fn2-sched fn2-control)) :ok))
           (and (equal (mv-nth 1 (fn2-sched-arm-deadline machine deadline fn2-sched fn2-control)) fn2-sched)
                (equal (mv-nth 2 (fn2-sched-arm-deadline machine deadline fn2-sched fn2-control)) fn2-control))))
(in-theory (disable fn2-sched-arm-deadline))

(defun fn2-sched-clear-deadline (machine fn2-sched)
  (declare (xargs :stobjs fn2-sched :guard (fn2-sched-wfp fn2-sched)))
  (if (not (and (natp machine) (< machine (fn2-sched-rows fn2-sched))))
      (mv :bounds fn2-sched)
    (let* ((was-armed (< (fn2-sched-deadline machine fn2-sched) *fn2-no-deadline*))
           (armed (fn2-sched-armed-timers fn2-sched))
           (next-armed (if (and was-armed (< 0 armed)) (- armed 1) armed))
           (fn2-sched (fn2-sched-set-deadline machine *fn2-no-deadline* fn2-sched))
           (fn2-sched (fn2-sched-set-expired machine 0 fn2-sched))
           (fn2-sched (update-fn2-sched-armed-timers next-armed fn2-sched))
           (fn2-sched (if (= next-armed 0)
                          (update-fn2-sched-earliest-deadline *fn2-no-deadline* fn2-sched)
                        fn2-sched)))
      (mv :ok fn2-sched))))

(defthm fn2-sched-clear-deadline-wfp
  (implies (and (fn2-schedp fn2-sched) (fn2-sched-wfp fn2-sched))
           (fn2-sched-wfp (mv-nth 1 (fn2-sched-clear-deadline machine fn2-sched)))))
(defthm fn2-sched-clear-deadline-type
  (implies (and (fn2-schedp fn2-sched) (fn2-sched-wfp fn2-sched))
           (fn2-schedp (mv-nth 1 (fn2-sched-clear-deadline machine fn2-sched)))))
(defthm fn2-sched-clear-deadline-rows
  (equal (fn2-sched-rows (mv-nth 1 (fn2-sched-clear-deadline machine fn2-sched)))
         (fn2-sched-rows fn2-sched)))
(defthm fn2-sched-clear-deadline-refusal
  (implies (not (eq (mv-nth 0 (fn2-sched-clear-deadline machine fn2-sched)) :ok))
           (equal (mv-nth 1 (fn2-sched-clear-deadline machine fn2-sched)) fn2-sched)))
(in-theory (disable fn2-sched-clear-deadline))

(defun fn2-timer-service-ready-p (fn2-sched fn2-control)
  (declare (xargs :stobjs (fn2-sched fn2-control)
                  :guard (and (fn2-sched-wfp fn2-sched) (fn2-control-wfp fn2-control))))
  (or (fn2-sched-service-ready *fn2-timer-service-slot* fn2-sched)
      (and (< 0 (fn2-sched-armed-timers fn2-sched))
           (<= (fn2-sched-earliest-deadline fn2-sched)
               (fn2-control-now fn2-control)))
      (and (< (fn2-control-idle-deadline fn2-control) *fn2-no-deadline*)
           (<= (fn2-control-idle-deadline fn2-control)
               (fn2-control-now fn2-control)))))

(defun fn2-timer-expire-one (idx now min-dl woken fn2-sched)
  (declare (xargs :stobjs fn2-sched
                  :guard (and (fn2-sched-wfp fn2-sched) (natp idx)
                              (< idx (fn2-sched-rows fn2-sched))
                              (unsigned-byte-p 60 now) (unsigned-byte-p 60 min-dl)
                              (natp woken))))
  (let ((cur-min (if (unsigned-byte-p 60 min-dl) min-dl *fn2-no-deadline*)))
    (if (not (mbt (and (fn2-sched-wfp fn2-sched) (natp idx)
                       (< idx (fn2-sched-rows fn2-sched)))))
        (mv cur-min (nfix woken) fn2-sched)
      (let* ((dl (fn2-sched-deadline idx fn2-sched))
             (armed (fn2-sched-armed-timers fn2-sched)))
        (cond ((>= dl *fn2-no-deadline*) (mv cur-min (nfix woken) fn2-sched))
              ((<= dl (nfix now))
               (let* ((principal (fn2-sched-principal idx fn2-sched))
                      (fn2-sched (fn2-sched-set-deadline idx *fn2-no-deadline* fn2-sched))
                      (fn2-sched (fn2-sched-set-expired idx 1 fn2-sched))
                      (fn2-sched (if (< 0 armed)
                                     (update-fn2-sched-armed-timers (- armed 1) fn2-sched)
                                   fn2-sched)))
                 (mv-let (code fn2-sched) (fn2-sched-make-runnable idx principal fn2-sched)
                   (mv cur-min (if (eq code :ok) (+ 1 (nfix woken)) (nfix woken)) fn2-sched))))
              (t (mv (min cur-min dl) (nfix woken) fn2-sched)))))))

(defthm fn2-timer-expire-one-wfp
  (implies (and (fn2-schedp fn2-sched) (fn2-sched-wfp fn2-sched))
           (fn2-sched-wfp (mv-nth 2 (fn2-timer-expire-one idx now min-dl woken fn2-sched))))
  :hints (("Goal" :do-not '(eliminate-destructors))))
(defthm fn2-timer-expire-one-type
  (implies (and (fn2-schedp fn2-sched) (fn2-sched-wfp fn2-sched))
           (fn2-schedp (mv-nth 2 (fn2-timer-expire-one idx now min-dl woken fn2-sched))))
  :hints (("Goal" :do-not '(eliminate-destructors))))
(defthm fn2-timer-expire-one-rows
  (equal (fn2-sched-rows (mv-nth 2 (fn2-timer-expire-one idx now min-dl woken fn2-sched)))
         (fn2-sched-rows fn2-sched))
  :hints (("Goal" :do-not '(eliminate-destructors))))
(defthm fn2-timer-expire-one-raw-rows
  (equal (nth *fn2-sched-rows* (mv-nth 2 (fn2-timer-expire-one idx now min-dl woken fn2-sched)))
         (nth *fn2-sched-rows* fn2-sched))
  :hints (("Goal" :do-not '(eliminate-destructors))))
(defthm fn2-timer-expire-one-min-natp
  (implies (fn2-schedp fn2-sched)
           (natp (car (fn2-timer-expire-one idx now min-dl woken fn2-sched))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :do-not '(eliminate-destructors))))
(defthm fn2-timer-expire-one-min-bound
  (implies (fn2-schedp fn2-sched)
           (< (car (fn2-timer-expire-one idx now min-dl woken fn2-sched))
              (expt 2 60)))
  :rule-classes :linear
  :hints (("Goal" :do-not '(eliminate-destructors))))
(defthm fn2-timer-expire-one-woken-natp
  (natp (mv-nth 1 (fn2-timer-expire-one idx now min-dl woken fn2-sched)))
  :rule-classes :type-prescription)
(defthm fn2-timer-expire-one-woken-bound
  (<= (mv-nth 1 (fn2-timer-expire-one idx now min-dl woken fn2-sched))
      (+ 1 (nfix woken)))
  :rule-classes :linear)
(in-theory (disable fn2-timer-expire-one))

(defun fn2-timer-service-scan (left idx now min-dl woken fn2-sched)
  (declare (xargs :stobjs fn2-sched
                  :measure (nfix left)
                  :guard (and (fn2-sched-wfp fn2-sched) (natp left) (natp idx)
                              (< idx (fn2-sched-rows fn2-sched))
                              (unsigned-byte-p 60 now) (unsigned-byte-p 60 min-dl)
                              (natp woken))))
  (if (or (zp left)
          (not (mbt (and (fn2-schedp fn2-sched) (fn2-sched-wfp fn2-sched) (natp idx)
                         (< idx (fn2-sched-rows fn2-sched))
                         (unsigned-byte-p 60 now) (unsigned-byte-p 60 min-dl)
                         (natp woken)))))
      (mv (nfix idx) (if (unsigned-byte-p 60 min-dl) min-dl *fn2-no-deadline*) nil (nfix woken) fn2-sched)
    (mv-let (min-dl woken fn2-sched)
      (fn2-timer-expire-one idx now min-dl woken fn2-sched)
      (let ((next (+ 1 idx))
            (rows (fn2-sched-rows fn2-sched)))
        (if (>= next rows)
            (mv 0 min-dl t woken fn2-sched)
          (fn2-timer-service-scan (- left 1) next now min-dl woken fn2-sched))))))

(defthm fn2-timer-service-scan-wfp
  (implies (and (fn2-schedp fn2-sched) (fn2-sched-wfp fn2-sched))
           (fn2-sched-wfp (mv-nth 4 (fn2-timer-service-scan left idx now min-dl woken fn2-sched)))))
(defthm fn2-timer-service-scan-type
  (implies (and (fn2-schedp fn2-sched) (fn2-sched-wfp fn2-sched))
           (fn2-schedp (mv-nth 4 (fn2-timer-service-scan left idx now min-dl woken fn2-sched)))))
(defthm fn2-timer-service-scan-rows
  (equal (fn2-sched-rows (mv-nth 4 (fn2-timer-service-scan left idx now min-dl woken fn2-sched)))
         (fn2-sched-rows fn2-sched)))
(defthm fn2-timer-service-scan-raw-rows
  (equal (nth *fn2-sched-rows* (mv-nth 4 (fn2-timer-service-scan left idx now min-dl woken fn2-sched)))
         (nth *fn2-sched-rows* fn2-sched))
  :hints (("Goal" :use fn2-timer-service-scan-rows)))
(defthm fn2-timer-service-scan-next-natp
  (natp (car (fn2-timer-service-scan left idx now min-dl woken fn2-sched)))
  :rule-classes (:rewrite :type-prescription))
(defthm fn2-timer-service-scan-min-natp
  (implies (fn2-schedp fn2-sched)
           (natp (mv-nth 1 (fn2-timer-service-scan left idx now min-dl woken fn2-sched))))
  :rule-classes (:rewrite :type-prescription))
(defthm fn2-timer-service-scan-min-bound
  (implies (fn2-schedp fn2-sched)
           (< (mv-nth 1 (fn2-timer-service-scan left idx now min-dl woken fn2-sched))
              (expt 2 60)))
  :rule-classes :linear)
(defthm fn2-timer-service-scan-wrappedp-booleanp
  (booleanp (mv-nth 2 (fn2-timer-service-scan left idx now min-dl woken fn2-sched)))
  :rule-classes :type-prescription)
(defthm fn2-timer-service-scan-woken-natp
  (natp (mv-nth 3 (fn2-timer-service-scan left idx now min-dl woken fn2-sched)))
  :rule-classes :type-prescription)
(defthm fn2-timer-service-scan-woken-bound
  (<= (mv-nth 3 (fn2-timer-service-scan left idx now min-dl woken fn2-sched))
      (+ (nfix woken) (nfix left)))
  :rule-classes :linear)
(in-theory (disable fn2-timer-service-scan))

(defun fn2-timer-service-finish (wrappedp next-cur next-min now base-idle fn2-sched fn2-control)
  (declare (xargs :stobjs (fn2-sched fn2-control)
                  :guard (and (booleanp wrappedp) (natp next-cur)
                              (unsigned-byte-p 60 next-min) (unsigned-byte-p 60 now)
                              (unsigned-byte-p 60 base-idle)
                              (fn2-sched-wfp fn2-sched) (fn2-control-wfp fn2-control))))
  (let ((cur-min (if (unsigned-byte-p 60 next-min) next-min *fn2-no-deadline*))
        (cur-idle (if (unsigned-byte-p 60 base-idle) base-idle *fn2-no-deadline*)))
    (if wrappedp
        (let* ((eff-min (if (= (fn2-sched-armed-timers fn2-sched) 0)
                            *fn2-no-deadline* cur-min))
               (ready (if (and (< eff-min *fn2-no-deadline*) (<= eff-min (nfix now))) 1 0))
               (next-idle (min cur-idle eff-min))
               (fn2-sched (update-fn2-sched-earliest-deadline eff-min fn2-sched))
               (fn2-sched (update-fn2-sched-scan-min *fn2-no-deadline* fn2-sched))
               (fn2-sched (fn2-sched-set-service *fn2-timer-service-slot* ready fn2-sched))
               (fn2-control (update-fn2-control-timer-cursor 0 fn2-control))
               (fn2-control (update-fn2-control-idle-deadline next-idle fn2-control)))
          (mv fn2-sched fn2-control))
      (let* ((fn2-sched (update-fn2-sched-scan-min cur-min fn2-sched))
             (fn2-sched (fn2-sched-set-service *fn2-timer-service-slot* 1 fn2-sched))
             (fn2-control (update-fn2-control-timer-cursor
                           (if (unsigned-byte-p 32 next-cur) next-cur 0) fn2-control))
             (fn2-control (update-fn2-control-idle-deadline cur-idle fn2-control)))
        (mv fn2-sched fn2-control)))))

(defthm fn2-timer-service-finish-sched-wfp
  (implies (and (fn2-schedp fn2-sched) (fn2-sched-wfp fn2-sched))
           (fn2-sched-wfp (car (fn2-timer-service-finish wrappedp next-cur next-min now base-idle fn2-sched fn2-control)))))
(defthm fn2-timer-service-finish-sched-type
  (implies (and (fn2-schedp fn2-sched) (fn2-sched-wfp fn2-sched))
           (fn2-schedp (car (fn2-timer-service-finish wrappedp next-cur next-min now base-idle fn2-sched fn2-control)))))
(defthm fn2-timer-service-finish-sched-rows
  (equal (fn2-sched-rows (car (fn2-timer-service-finish wrappedp next-cur next-min now base-idle fn2-sched fn2-control)))
         (fn2-sched-rows fn2-sched)))
(defthm fn2-timer-service-finish-sched-raw-rows
  (equal (nth *fn2-sched-rows* (car (fn2-timer-service-finish wrappedp next-cur next-min now base-idle fn2-sched fn2-control)))
         (nth *fn2-sched-rows* fn2-sched))
  :hints (("Goal" :use fn2-timer-service-finish-sched-rows)))
(defthm fn2-timer-service-finish-control-wfp
  (implies (fn2-control-wfp fn2-control)
           (fn2-control-wfp (mv-nth 1 (fn2-timer-service-finish wrappedp next-cur next-min now base-idle fn2-sched fn2-control)))))
(defthm fn2-timer-service-finish-control-type
  (implies (fn2-controlp fn2-control)
           (fn2-controlp (mv-nth 1 (fn2-timer-service-finish wrappedp next-cur next-min now base-idle fn2-sched fn2-control)))))
(in-theory (disable fn2-timer-service-finish))

(defun fn2-timer-service-step (fn2-sched fn2-control)
  (declare (xargs :stobjs (fn2-sched fn2-control)
                  :guard (and (fn2-sched-wfp fn2-sched) (fn2-control-wfp fn2-control))))
  (let* ((rows (fn2-sched-rows fn2-sched))
         (now (fn2-control-now fn2-control))
         (idle (fn2-control-idle-deadline fn2-control))
         (base-idle (if (<= idle now) *fn2-no-deadline* idle)))
    (if (zp rows)
        (let* ((fn2-sched (fn2-sched-set-service *fn2-timer-service-slot* 0 fn2-sched))
               (fn2-sched (update-fn2-sched-armed-timers 0 fn2-sched))
               (fn2-sched (update-fn2-sched-earliest-deadline *fn2-no-deadline* fn2-sched))
               (fn2-sched (update-fn2-sched-scan-min *fn2-no-deadline* fn2-sched))
               (fn2-control (update-fn2-control-timer-cursor 0 fn2-control))
               (fn2-control (update-fn2-control-idle-deadline base-idle fn2-control)))
          (mv 0 fn2-sched fn2-control))
      (let* ((cur (fn2-control-timer-cursor fn2-control))
             (start (if (< cur rows) cur 0))
             (init-min (if (= start 0) *fn2-no-deadline* (fn2-sched-scan-min fn2-sched))))
        (mv-let (next-cur next-min wrappedp woken fn2-sched)
          (fn2-timer-service-scan *fn2-timer-service-step-max* start now init-min 0 fn2-sched)
          (mv-let (fn2-sched fn2-control)
            (fn2-timer-service-finish wrappedp next-cur next-min now base-idle fn2-sched fn2-control)
            (mv woken fn2-sched fn2-control)))))))

(defthm fn2-timer-service-step-sched-wfp
  (implies (and (fn2-schedp fn2-sched) (fn2-sched-wfp fn2-sched))
           (fn2-sched-wfp (mv-nth 1 (fn2-timer-service-step fn2-sched fn2-control)))))
(defthm fn2-timer-service-step-sched-type
  (implies (and (fn2-schedp fn2-sched) (fn2-sched-wfp fn2-sched))
           (fn2-schedp (mv-nth 1 (fn2-timer-service-step fn2-sched fn2-control)))))
(defthm fn2-timer-service-step-sched-rows
  (equal (fn2-sched-rows (mv-nth 1 (fn2-timer-service-step fn2-sched fn2-control)))
         (fn2-sched-rows fn2-sched)))
(defthm fn2-timer-service-step-control-wfp
  (implies (and (fn2-schedp fn2-sched) (fn2-sched-wfp fn2-sched)
                (fn2-controlp fn2-control) (fn2-control-wfp fn2-control))
           (fn2-control-wfp (mv-nth 2 (fn2-timer-service-step fn2-sched fn2-control)))))
(defthm fn2-timer-service-step-control-type
  (implies (and (fn2-schedp fn2-sched) (fn2-sched-wfp fn2-sched)
                (fn2-controlp fn2-control) (fn2-control-wfp fn2-control))
           (fn2-controlp (mv-nth 2 (fn2-timer-service-step fn2-sched fn2-control)))))
(defthm fn2-timer-service-step-woken-natp
  (natp (car (fn2-timer-service-step fn2-sched fn2-control)))
  :rule-classes (:rewrite :type-prescription))
(defthm fn2-timer-service-step-woken-bound
  (<= (car (fn2-timer-service-step fn2-sched fn2-control)) *fn2-timer-service-step-max*)
  :rule-classes :linear)
(in-theory (disable fn2-timer-service-step))

; Read-only evidence helpers, never called by the executor.
(defun fn2-sched-calendar-matchp (codes i fn2-sched)
  (declare (xargs :stobjs fn2-sched :verify-guards nil :measure (len codes)))
  (if (atom codes) t
    (and (natp i) (< i (fn2-sched-calendar-length fn2-sched))
         (equal (fn2-sched-calendari i fn2-sched) (car codes))
         (fn2-sched-calendar-matchp (cdr codes) (+ i 1) fn2-sched))))
;; The calendar is the weighted calendar of WEIGHTS, one weight in 1..255 per principal slot.
(defun fn2-sched-calendar-validp (weights fn2-sched)
  (declare (xargs :stobjs fn2-sched :verify-guards nil))
  (let ((codes (fn2-sched-calendar-list weights)))
    (and (fn2-sched-weightsp weights)
         (equal (len weights) (fn2-sched-nprincipals fn2-sched))
         (equal (fn2-sched-calendar-length fn2-sched) (len codes))
         (fn2-sched-calendar-matchp codes 0 fn2-sched))))
(defun fn2-sched-starvation-hyps (principal weights fn2-sched)
  (declare (xargs :stobjs fn2-sched :verify-guards nil))
  (and (fn2-schedp fn2-sched) (fn2-sched-wfp fn2-sched)
       (fn2-sched-principalp principal fn2-sched)
       (< 0 (fn2-sched-countsi principal fn2-sched))
       (< (fn2-sched-cursor fn2-sched) (fn2-sched-calendar-length fn2-sched))
       (fn2-sched-calendar-validp weights fn2-sched)))
(defun fn2-sched-visits-principal (left principal fn2-sched)
  (declare (xargs :stobjs fn2-sched :verify-guards nil :measure (nfix left)))
  (if (zp left) (mv nil fn2-sched)
    (mv-let (kind slot position fn2-sched) (fn2-sched-visit fn2-sched)
      (declare (ignore position))
      (if (and (= kind 0) (equal slot principal)) (mv t fn2-sched)
        (fn2-sched-visits-principal (- left 1) principal fn2-sched)))))
(defthm-owed fn2-sched-starvation (principal weights fn2-sched)
  (implies (fn2-sched-starvation-hyps principal weights fn2-sched)
           (mv-nth 0 (fn2-sched-visits-principal
                      (fn2-sched-calendar-length fn2-sched) principal fn2-sched)))
  :schema :bound :from (:operation fn2-sched)
  :teeth (fn2-sched-test-starvation fn2-sched-test-starvation-negative)
  :doc "Actual scheduler visit sequence over any weighted calendar (every principal weight 1..255) grants a continuously eligible principal an opportunity within calendar length L visits. This is an opportunity bound, not dependency progress or machine completion.")

(assert-event (fn2-assert-compliant-p
 '(fn2-sched-profilep fn2-sched-weightsp fn2-sched-weights-onesp fn2-sched-weights-max
   fn2-sched-pass fn2-sched-principal-sequence fn2-sched-calendar-entries fn2-sched-calendar-list
   fn2-sched-init-weightsp fn2-sched-principalp fn2-sched-init
   fn2-sched-make-runnable fn2-sched-pop-head fn2-sched-reattribute fn2-sched-visit
   fn2-sched-set-service fn2-sched-service-ready fn2-sched-eligiblep
   fn2-sched-arm-deadline fn2-sched-clear-deadline
   fn2-timer-service-ready-p fn2-timer-expire-one fn2-timer-service-scan
   fn2-timer-service-finish fn2-timer-service-step)
 (w state)))
