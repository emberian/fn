; A4 scheduler: one global machine index, intrusive principal FIFOs, fixed calendar.
(in-package "ACL2")
(include-book "columns")
(include-book "machines")
(include-book "profile")
(include-book "owed")

(defconst *fn2-sched-none* 4294967295)
(defconst *fn2-sched-anonymous* 0)

(defcolumns fn2-sched
  ((principal :u16) (in-queue :bool) (prev :u32) (next :u32))
  :init-name fn2-sched-columns-init
  :extra-fields
  ((fn2-sched-heads :type (array (unsigned-byte 32) (0)) :initially 4294967295 :resizable t)
   (fn2-sched-tails :type (array (unsigned-byte 32) (0)) :initially 4294967295 :resizable t)
   (fn2-sched-counts :type (array (unsigned-byte 32) (0)) :initially 0 :resizable t)
   (fn2-sched-calendar :type (array (unsigned-byte 32) (0)) :initially 0 :resizable t)
   (fn2-sched-services :type (array (unsigned-byte 1) (4)) :initially 0)
   (fn2-sched-nprincipals :type (unsigned-byte 32) :initially 0)
   (fn2-sched-cursor :type (unsigned-byte 32) :initially 0)
   (fn2-sched-queued :type (unsigned-byte 32) :initially 0)))

; Init accepts precisely the declared calendar geometry.  Each group has up
; to sixteen principal slots and all four protected services, in that order.
(defun fn2-sched-profilep (profile)
  (declare (xargs :guard t))
  (and (fn2-profilep profile)
       (posp (fn2-profile-p profile)) (<= (fn2-profile-p profile) 65536)
       (unsigned-byte-p 32 (fn2-profile-calendar-length profile))))

(defun fn2-sched-calendar-code (position principals)
  (declare (xargs :guard (and (natp position) (natp principals))))
  (let* ((full (floor principals 16)) (full-end (* full 20)))
    (if (< position full-end)
        (let ((group (floor position 20)) (within (mod position 20)))
          (if (< within 16) (+ (* group 16) within)
            (+ principals (- within 16))))
      (let ((within (- position full-end)) (remaining (mod principals 16)))
        (if (< within remaining) (+ (* full 16) within)
          (+ principals (- within remaining)))))))

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
           (fn2-sched (fn2-sched-set-prev i *fn2-sched-none* fn2-sched))
           (fn2-sched (fn2-sched-set-next i *fn2-sched-none* fn2-sched)))
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
    (let* ((fn2-sched (update-fn2-sched-headsi i *fn2-sched-none* fn2-sched))
           (fn2-sched (update-fn2-sched-tailsi i *fn2-sched-none* fn2-sched))
           (fn2-sched (update-fn2-sched-countsi i 0 fn2-sched)))
      (fn2-sched-clear-principals (+ 1 i) fn2-sched))))
(defthm fn2-sched-clear-principals-wfp
  (implies (fn2-sched-wfp fn2-sched)
           (fn2-sched-wfp (fn2-sched-clear-principals i fn2-sched))))
(defthm fn2-sched-clear-principals-type
  (implies (and (fn2-schedp fn2-sched) (fn2-sched-wfp fn2-sched) (natp i))
           (fn2-schedp (fn2-sched-clear-principals i fn2-sched))))
(in-theory (disable fn2-sched-clear-principals))

(defun fn2-sched-fill-calendar (i fn2-sched)
  (declare (xargs :stobjs fn2-sched :guard (natp i)
                  :measure (nfix (- (fn2-sched-calendar-length fn2-sched) (nfix i)))))
  (if (or (not (natp i)) (>= i (fn2-sched-calendar-length fn2-sched))) fn2-sched
    (let* ((code (fn2-sched-calendar-code i (fn2-sched-nprincipals fn2-sched)))
           (fn2-sched (update-fn2-sched-calendari
                       i (if (unsigned-byte-p 32 code) code 0) fn2-sched)))
      (fn2-sched-fill-calendar (+ 1 i) fn2-sched))))
(defthm fn2-sched-fill-calendar-wfp
  (implies (fn2-sched-wfp fn2-sched)
           (fn2-sched-wfp (fn2-sched-fill-calendar i fn2-sched))))
(defthm fn2-sched-fill-calendar-type
  (implies (and (fn2-schedp fn2-sched) (fn2-sched-wfp fn2-sched) (natp i))
           (fn2-schedp (fn2-sched-fill-calendar i fn2-sched))))
(in-theory (disable fn2-sched-fill-calendar))

(defun fn2-sched-init (profile n fn2-sched)
  (declare (xargs :stobjs fn2-sched :guard (and (fn2-sched-profilep profile) (unsigned-byte-p 32 n))))
  (let* ((p (fn2-profile-p profile))
         (l (fn2-profile-calendar-length profile))
         (fn2-sched (fn2-sched-columns-init n fn2-sched))
         (fn2-sched (resize-fn2-sched-heads p fn2-sched))
         (fn2-sched (resize-fn2-sched-tails p fn2-sched))
         (fn2-sched (resize-fn2-sched-counts p fn2-sched))
         (fn2-sched (resize-fn2-sched-calendar l fn2-sched))
         (fn2-sched (update-fn2-sched-nprincipals p fn2-sched))
         (fn2-sched (update-fn2-sched-cursor 0 fn2-sched))
         (fn2-sched (update-fn2-sched-queued 0 fn2-sched))
         (fn2-sched (update-fn2-sched-servicesi 0 0 fn2-sched))
         (fn2-sched (update-fn2-sched-servicesi 1 0 fn2-sched))
         (fn2-sched (update-fn2-sched-servicesi 2 0 fn2-sched))
         (fn2-sched (update-fn2-sched-servicesi 3 0 fn2-sched))
         (fn2-sched (fn2-sched-clear-machines 0 fn2-sched))
         (fn2-sched (fn2-sched-clear-principals 0 fn2-sched)))
    (fn2-sched-fill-calendar 0 fn2-sched)))
(defthm fn2-sched-init-wfp
  (implies (and (fn2-sched-profilep profile) (unsigned-byte-p 32 n))
           (fn2-sched-wfp (fn2-sched-init profile n fn2-sched))))
(defthm fn2-sched-init-type
  (implies (and (fn2-schedp fn2-sched) (fn2-sched-profilep profile) (unsigned-byte-p 32 n))
           (fn2-schedp (fn2-sched-init profile n fn2-sched))))
(in-theory (disable fn2-sched-init fn2-sched-profilep fn2-sched-calendar-code))

(defun fn2-sched-make-runnable (machine principal fn2-sched)
  (declare (xargs :stobjs fn2-sched :guard (fn2-sched-wfp fn2-sched)))
  (cond
   ((not (and (natp machine) (< machine (fn2-sched-rows fn2-sched))
              (fn2-sched-principalp principal fn2-sched))) (mv :bounds fn2-sched))
   ((= (fn2-sched-in-queue machine fn2-sched) 1) (mv :already fn2-sched))
   (t
    (let ((tail (fn2-sched-tailsi principal fn2-sched))
          (count (fn2-sched-countsi principal fn2-sched)))
      (if (or (>= count *fn2-sched-none*)
              (>= (fn2-sched-queued fn2-sched) *fn2-sched-none*)
              (and (< 0 count) (>= tail (fn2-sched-rows fn2-sched))))
          (mv :state fn2-sched)
        (let* ((fn2-sched (fn2-sched-set-principal machine principal fn2-sched))
               (fn2-sched (fn2-sched-set-in-queue machine 1 fn2-sched))
               (fn2-sched (fn2-sched-set-prev machine
                           (if (= count 0) *fn2-sched-none* tail) fn2-sched))
               (fn2-sched (fn2-sched-set-next machine *fn2-sched-none* fn2-sched))
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
         (mv :bounds *fn2-sched-none* fn2-sched))
        ((= (fn2-sched-countsi principal fn2-sched) 0)
         (mv :empty *fn2-sched-none* fn2-sched))
        (t
         (let ((head (fn2-sched-headsi principal fn2-sched))
               (count (fn2-sched-countsi principal fn2-sched)))
           (if (or (>= head (fn2-sched-rows fn2-sched))
                   (= (fn2-sched-queued fn2-sched) 0))
               (mv :state *fn2-sched-none* fn2-sched)
             (let ((next (fn2-sched-next head fn2-sched)))
               (if (and (< 1 count) (>= next (fn2-sched-rows fn2-sched)))
                   (mv :state *fn2-sched-none* fn2-sched)
                 (let* ((fn2-sched (fn2-sched-set-in-queue head 0 fn2-sched))
                        (fn2-sched (fn2-sched-set-prev head *fn2-sched-none* fn2-sched))
                        (fn2-sched (fn2-sched-set-next head *fn2-sched-none* fn2-sched))
                        (fn2-sched (update-fn2-sched-headsi principal
                                    (if (= count 1) *fn2-sched-none* next) fn2-sched))
                        (fn2-sched (if (= count 1)
                                       (update-fn2-sched-tailsi principal *fn2-sched-none* fn2-sched)
                                     (fn2-sched-set-prev next *fn2-sched-none* fn2-sched)))
                        (fn2-sched (update-fn2-sched-countsi principal (- count 1) fn2-sched))
                        (fn2-sched (update-fn2-sched-queued (- (fn2-sched-queued fn2-sched) 1) fn2-sched)))
                   (mv :ok head fn2-sched)))))))))

; Return the entry's kind, principal slot (zero for services), and OLD cursor.
; An empty calendar is an uninitialized scheduler, represented by kind=255.
(defun fn2-sched-visit (fn2-sched)
  (declare (xargs :stobjs fn2-sched))
  (let ((position (fn2-sched-cursor fn2-sched))
        (length (fn2-sched-calendar-length fn2-sched))
        (p (fn2-sched-nprincipals fn2-sched)))
    (if (>= position length) (mv 255 0 position fn2-sched)
      (let* ((code (fn2-sched-calendari position fn2-sched))
             (next (if (< (+ position 1) length) (+ position 1) 0))
             (fn2-sched (update-fn2-sched-cursor
                         (if (unsigned-byte-p 32 next) next 0) fn2-sched)))
        (cond ((< code p) (mv 0 code position fn2-sched))
              ((< code (+ p 4)) (mv (+ 1 (- code p)) 0 position fn2-sched))
              (t (mv 255 0 position fn2-sched)))))))

(defun fn2-sched-set-service (service ready fn2-sched)
  (declare (xargs :stobjs fn2-sched :guard (and (natp service) (< service 4)
                                                              (unsigned-byte-p 1 ready))))
  (update-fn2-sched-servicesi service ready fn2-sched))
(defun fn2-sched-service-ready (service fn2-sched)
  (declare (xargs :stobjs fn2-sched :guard (and (natp service) (< service 4))))
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
(defthm fn2-sched-pop-head-type
  (implies (and (fn2-schedp fn2-sched) (fn2-sched-wfp fn2-sched))
           (fn2-schedp (mv-nth 2 (fn2-sched-pop-head principal fn2-sched)))))
(defthm fn2-sched-pop-head-rows
  (equal (fn2-sched-rows (mv-nth 2 (fn2-sched-pop-head principal fn2-sched))) (fn2-sched-rows fn2-sched)))
(defthm fn2-sched-visit-type
  (implies (and (fn2-schedp fn2-sched) (fn2-sched-wfp fn2-sched))
           (fn2-schedp (mv-nth 3 (fn2-sched-visit  fn2-sched)))))
(defthm fn2-sched-visit-rows
  (equal (fn2-sched-rows (mv-nth 3 (fn2-sched-visit  fn2-sched))) (fn2-sched-rows fn2-sched)))
(in-theory (disable fn2-sched-make-runnable fn2-sched-pop-head fn2-sched-visit))

; Read-only evidence helpers, never called by the executor.
(defun fn2-sched-calendar-validp (i fn2-sched)
  (declare (xargs :stobjs fn2-sched :verify-guards nil
                  :measure (nfix (- (fn2-sched-calendar-length fn2-sched) (nfix i)))))
  (if (or (not (natp i)) (>= i (fn2-sched-calendar-length fn2-sched))) t
    (and (equal (fn2-sched-calendari i fn2-sched)
                (fn2-sched-calendar-code i (fn2-sched-nprincipals fn2-sched)))
         (fn2-sched-calendar-validp (+ i 1) fn2-sched))))
(defun fn2-sched-starvation-hyps (principal fn2-sched)
  (declare (xargs :stobjs fn2-sched :verify-guards nil))
  (and (fn2-schedp fn2-sched) (fn2-sched-wfp fn2-sched)
       (fn2-sched-principalp principal fn2-sched)
       (< 0 (fn2-sched-countsi principal fn2-sched))
       (< (fn2-sched-cursor fn2-sched) (fn2-sched-calendar-length fn2-sched))
       (equal (fn2-sched-calendar-length fn2-sched)
              (+ (fn2-sched-nprincipals fn2-sched)
                 (* 4 (ceiling (fn2-sched-nprincipals fn2-sched) 16))))
       (fn2-sched-calendar-validp 0 fn2-sched)))
(defun fn2-sched-visits-principal (left principal fn2-sched)
  (declare (xargs :stobjs fn2-sched :verify-guards nil :measure (nfix left)))
  (if (zp left) (mv nil fn2-sched)
    (mv-let (kind slot position fn2-sched) (fn2-sched-visit fn2-sched)
      (declare (ignore position))
      (if (and (= kind 0) (equal slot principal)) (mv t fn2-sched)
        (fn2-sched-visits-principal (- left 1) principal fn2-sched)))))
(defthm-owed fn2-sched-starvation (principal fn2-sched)
  (implies (fn2-sched-starvation-hyps principal fn2-sched)
           (mv-nth 0 (fn2-sched-visits-principal
                      (fn2-sched-calendar-length fn2-sched) principal fn2-sched)))
  :teeth "sched-unit visits every concrete principal from every cursor; removing principal 0's calendar entry falsifies the complete hypothesis and conclusion."
  :doc "Actual scheduler visit sequence grants a continuously eligible principal an opportunity within calendar length L visits. This is an opportunity bound, not dependency progress or machine completion.")

(assert-event (fn2-profile-exports-compliant-p
 '(fn2-sched-profilep fn2-sched-calendar-code fn2-sched-principalp fn2-sched-init
   fn2-sched-make-runnable fn2-sched-pop-head fn2-sched-visit
   fn2-sched-set-service fn2-sched-service-ready fn2-sched-eligiblep)
 (w state)))
