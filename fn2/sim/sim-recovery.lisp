; Recovery against the SAME durable byte image the simulated adapter mutates.
; Allocate fn2-recovery-image at run init. Each scan step copies one sector,
; and death discards only scan progress; the next attempt recopies from disk.
(in-package "ACL2")
(include-book "sim")
(include-book "recover-stub")

(defun fn2-sim-recovery-copy-bytes (address left fn2-sim-storage fn2-recovery-image)
  (declare (xargs :stobjs (fn2-sim-storage fn2-recovery-image)
                  :guard (and (fn2-sim-storage-wfp fn2-sim-storage) (natp address) (natp left))
                  :measure (nfix left)
                  :guard-hints (("Goal" :in-theory (enable fn2-sim-storage-rows)))))
  (cond ((equal (fn2-storage-dead fn2-sim-storage) 1) (mv :io fn2-recovery-image))
        ((zp left) (mv :ok fn2-recovery-image))
        ((or (not (natp address))
             (>= address (fn2-sim-storage-rows fn2-sim-storage))
             (>= address (fn2-recovery-bytes-length fn2-recovery-image)))
         (mv :bounds fn2-recovery-image))
        (t (let ((fn2-recovery-image
                  (fn2-recovery-put-byte address
                    (fn2-sim-storage-durable address fn2-sim-storage) fn2-recovery-image)))
             (fn2-sim-recovery-copy-bytes (+ 1 address) (- left 1) fn2-sim-storage fn2-recovery-image)))))
(defthm fn2-sim-recovery-copy-bytes-type
  (implies (and (fn2-sim-storagep fn2-sim-storage) (fn2-sim-storage-wfp fn2-sim-storage)
                (fn2-recovery-imagep fn2-recovery-image) (natp address) (natp left))
           (fn2-recovery-imagep
            (mv-nth 1 (fn2-sim-recovery-copy-bytes address left fn2-sim-storage fn2-recovery-image))))
  :hints (("Goal" :in-theory (enable fn2-sim-storage-rows))))
(defthm fn2-sim-recovery-copy-bytes-length
  (equal (fn2-recovery-bytes-length
          (mv-nth 1 (fn2-sim-recovery-copy-bytes address left fn2-sim-storage fn2-recovery-image)))
         (fn2-recovery-bytes-length fn2-recovery-image))
  :hints (("Goal" :in-theory (disable fn2-recovery-bytes-length))))
(in-theory (disable fn2-sim-recovery-copy-bytes fn2-recovery-bytes-length))

(defun fn2-sim-recovery-copy-sector (sector fn2-sim fn2-recovery-image)
  (declare (xargs :stobjs (fn2-sim fn2-recovery-image)
                  :guard (and (fn2-sim-ready fn2-sim) (unsigned-byte-p 32 sector))))
  (stobj-let ((fn2-sim-storage (fn2-sim-disk fn2-sim)))
    (code fn2-recovery-image)
    (fn2-sim-recovery-copy-bytes (* 4096 sector) 4096 fn2-sim-storage fn2-recovery-image)
    (mv code fn2-recovery-image)))
(defthm fn2-sim-recovery-copy-sector-type
  (implies (and (fn2-simp fn2-sim) (fn2-sim-ready fn2-sim)
                (fn2-recovery-imagep fn2-recovery-image) (unsigned-byte-p 32 sector))
           (fn2-recovery-imagep
            (mv-nth 1 (fn2-sim-recovery-copy-sector sector fn2-sim fn2-recovery-image))))
  :hints (("Goal" :use ((:instance fn2-sim-disk-type))
                  :in-theory (disable fn2-sim-disk-type))))
(defthm fn2-sim-recovery-copy-sector-length
  (equal (fn2-recovery-bytes-length
          (mv-nth 1 (fn2-sim-recovery-copy-sector sector fn2-sim fn2-recovery-image)))
         (fn2-recovery-bytes-length fn2-recovery-image)))
(in-theory (disable fn2-sim-recovery-copy-sector))

; Draw only the crash class during recovery; irrelevant network/adapter fault
; classes are neither consumed nor counted as injections. The actual selected
; crash goes through the common budget/hit/digest recorder.
(defun fn2-sim-recovery-choice (fn2-sim)
  (declare (xargs :stobjs fn2-sim :guard (fn2-sim-ready fn2-sim)))
  (mv-let (word fn2-sim) (fn2-sim-random fn2-sim)
    (if (and (< 0 (fn2-sim-fault-budget fn2-sim))
             (or (equal (fn2-sim-forced-fault fn2-sim) 15)
                 (and (equal (fn2-sim-forced-fault fn2-sim) 26)
                      (< (mod word 256) (fn2-sim-probabilitiesi 15 fn2-sim)))))
        (let ((fn2-sim (fn2-sim-force-fault 15 fn2-sim)))
          (fn2-sim-choose-fault fn2-sim))
      (mv 26 fn2-sim))))
(fn2-sim-shape fn2-sim-recovery-choice (fn2-sim) 1)

 ; Keep readiness opaque across composed and recursive transitions. Their
; exported preservation lemmas carry it; opening it loses the induction key.
(local (in-theory (disable fn2-sim-ready fn2-core-wfp)))

; code :dead means the attempt restarted; :ok scanned one sector; :bounds
; means the loader image was too short; :io is a sticky unreadable device. Never read stale pre-death scratch:
; the returned cursor starts at zero, and each sector is recopied before use.
; Reporting counts other than never-written do not affect classification.
(defun fn2-sim-recovery-step
  (i n ack-seq bad-tail damaged never profile
     fn2-core fn2-sim fn2-own fn2-recovery-image)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own fn2-recovery-image)
                  :guard (and (natp i) (unsigned-byte-p 32 n) (unsigned-byte-p 32 ack-seq)
                              (natp never) (fn2-core-wfp fn2-core)
                              (fn2-sim-ready fn2-sim) (fn2-own-wfp fn2-own))))
  (if (not (fn2-core-profilep profile))
      (mv :bounds i bad-tail damaged never fn2-core fn2-sim fn2-own fn2-recovery-image)
    (mv-let (fault fn2-sim) (fn2-sim-recovery-choice fn2-sim)
    (if (equal fault 15)
        (mv-let (fn2-core fn2-sim fn2-own) (fn2-sim-crash profile fn2-core fn2-sim fn2-own)
          (mv-let (start-code restart-n restart-tail restart-damage)
            (fn2-recover-start ack-seq fn2-recovery-image)
            (mv (if (and (eq start-code :ok) (equal restart-n n)) :dead :bounds)
                0 restart-tail restart-damage 0 fn2-core fn2-sim fn2-own fn2-recovery-image)))
      (if (>= i n)
          (mv :ok i bad-tail damaged never fn2-core fn2-sim fn2-own fn2-recovery-image)
        (mv-let (code fn2-recovery-image) (fn2-sim-recovery-copy-sector i fn2-sim fn2-recovery-image)
          (if (not (eq code :ok))
              (mv code i bad-tail damaged never fn2-core fn2-sim fn2-own fn2-recovery-image)
            (mv-let (done next bad-tail damaged valid never bad misplaced)
              (fn2-recover-step i n ack-seq bad-tail damaged 0 never 0 0 fn2-recovery-image)
              (declare (ignore done valid bad misplaced))
              (mv :ok next bad-tail damaged never fn2-core fn2-sim fn2-own fn2-recovery-image)))))))))

(defmacro fn2-sim-recovery-shape (name args corepos simpos ownpos imagepos extra)
  (let ((call `(,name ,@args fn2-core fn2-sim fn2-own fn2-recovery-image)))
    `(progn
       (defthm ,(fn2-columns-sym name "-SHAPE")
         (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                       (fn2-simp fn2-sim) (fn2-sim-ready fn2-sim)
                       (fn2-ownp fn2-own) (fn2-own-wfp fn2-own)
                       (fn2-recovery-imagep fn2-recovery-image) ,extra)
                  (and (fn2-corep (mv-nth ,corepos ,call))
                       (fn2-core-wfp (mv-nth ,corepos ,call))
                       (fn2-simp (mv-nth ,simpos ,call))
                       (fn2-sim-ready (mv-nth ,simpos ,call))
                       (fn2-ownp (mv-nth ,ownpos ,call))
                       (fn2-own-wfp (mv-nth ,ownpos ,call))
                       (fn2-recovery-imagep (mv-nth ,imagepos ,call)))))
       (defthm ,(fn2-columns-sym name "-LENGTH")
         (equal (fn2-recovery-bytes-length (mv-nth ,imagepos ,call))
                (fn2-recovery-bytes-length fn2-recovery-image))))))
(fn2-sim-recovery-shape fn2-sim-recovery-step (i n ack-seq bad-tail damaged never profile) 5 6 7 8
  (and (natp i) (unsigned-byte-p 32 n) (unsigned-byte-p 32 ack-seq) (natp never)))
(defthm fn2-sim-recovery-step-cursor-type
  (implies (natp i)
           (natp (mv-nth 1 (fn2-sim-recovery-step i n ack-seq bad-tail damaged never profile
                              fn2-core fn2-sim fn2-own fn2-recovery-image))))
  :rule-classes :type-prescription)
(defthm fn2-sim-recovery-step-never-type
  (implies (natp never)
           (natp (mv-nth 4 (fn2-sim-recovery-step i n ack-seq bad-tail damaged never profile
                              fn2-core fn2-sim fn2-own fn2-recovery-image))))
  :rule-classes :type-prescription)
(in-theory (disable fn2-sim-recovery-step))

(defun fn2-sim-recover-loop
  (fuel i n ack-seq crash-only bad-tail damaged never profile
        fn2-core fn2-sim fn2-own fn2-recovery-image)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own fn2-recovery-image)
                  :measure (nfix fuel)
                  :guard (and (natp fuel) (natp i) (unsigned-byte-p 32 n)
                              (unsigned-byte-p 32 ack-seq) (booleanp crash-only) (natp never)
                              (fn2-core-wfp fn2-core) (fn2-sim-ready fn2-sim) (fn2-own-wfp fn2-own))))
  (cond ((>= i n)
         (mv (fn2-recover-classification crash-only bad-tail damaged)
             fn2-core fn2-sim fn2-own fn2-recovery-image))
        ((zp fuel) (mv :unknown fn2-core fn2-sim fn2-own fn2-recovery-image))
        (t (mv-let (code next bad-tail damaged never fn2-core fn2-sim fn2-own fn2-recovery-image)
             (fn2-sim-recovery-step i n ack-seq bad-tail damaged never profile
                                    fn2-core fn2-sim fn2-own fn2-recovery-image)
             (if (not (or (eq code :ok) (eq code :dead)))
                 (mv :unknown fn2-core fn2-sim fn2-own fn2-recovery-image)
               (fn2-sim-recover-loop (- fuel 1) next n ack-seq crash-only bad-tail damaged never profile
                                      fn2-core fn2-sim fn2-own fn2-recovery-image))))))
(fn2-sim-recovery-shape fn2-sim-recover-loop
  (fuel i n ack-seq crash-only bad-tail damaged never profile) 1 2 3 4
  (and (natp fuel) (natp i) (unsigned-byte-p 32 n) (unsigned-byte-p 32 ack-seq)
       (booleanp crash-only) (natp never)))
(in-theory (disable fn2-sim-recover-loop))

(defun fn2-sim-recover-run
  (fuel ack-seq crash-only profile fn2-core fn2-sim fn2-own fn2-recovery-image)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own fn2-recovery-image)
                  :guard (and (natp fuel) (unsigned-byte-p 32 ack-seq) (booleanp crash-only)
                              (fn2-core-wfp fn2-core) (fn2-sim-ready fn2-sim) (fn2-own-wfp fn2-own))))
  (let ((bytes (stobj-let ((fn2-sim-storage (fn2-sim-disk fn2-sim)))
                 (bytes) (fn2-sim-storage-rows fn2-sim-storage) bytes)))
    (if (or (not (equal bytes (fn2-recovery-bytes-length fn2-recovery-image)))
            (not (fn2-core-profilep profile)))
        (mv :unknown fn2-core fn2-sim fn2-own fn2-recovery-image)
      (mv-let (code n bad-tail damaged) (fn2-recover-start ack-seq fn2-recovery-image)
        (if (not (eq code :ok)) (mv :unknown fn2-core fn2-sim fn2-own fn2-recovery-image)
          (fn2-sim-recover-loop fuel 0 n ack-seq crash-only bad-tail damaged 0 profile
                                 fn2-core fn2-sim fn2-own fn2-recovery-image))))))
(fn2-sim-recovery-shape fn2-sim-recover-run (fuel ack-seq crash-only profile) 1 2 3 4
  (and (natp fuel) (unsigned-byte-p 32 ack-seq) (booleanp crash-only)))
(in-theory (disable fn2-sim-recover-run))

(assert-event
 (fn2-profile-exports-compliant-p
  '(fn2-sim-recovery-copy-bytes fn2-sim-recovery-copy-sector fn2-sim-recovery-choice
    fn2-sim-recovery-step fn2-sim-recover-loop fn2-sim-recover-run) (w state)))
