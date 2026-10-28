; Simulated storage: byte images in 4 KiB sectors, 512-byte failure units.
; Every nondeterministic choice is a scalar supplied by the seeded simulator.
; A fence has its own image captured at SUBMISSION.  Its delayed completion
; cannot accidentally persist a later overlapping write.  Durable version
; stamps prevent an older concurrent fence from rolling back a newer one.
(in-package "ACL2")
(include-book "../books/columns")

; STAMP names the cached completed-write version (zero is the initial image).
; SNAPSHOT-STAMP freezes that version at fence submission. DURABLE-STAMP is
; the last version established by an honest fence or completed FUA, NOT the
; provenance of arbitrary bytes on media: live tears never advance it.
; Pending work means STAMP > DURABLE-STAMP; a reopened stale cache is not work.
; Fence arguments are operation tokens; OWNER stores token+1 (zero is free)
; in a separate profile-sized slot pool, independent of operation-row count.
(defcolumns fn2-sim-storage
  ((pending :u8) (durable :u8) (stamp :u60) (durable-stamp :u60))
  :rows-bound 4294967296
  :init-name fn2-storage-columns-init
  :extra-fields
  ((fn2-storage-fence-owner :type (array (unsigned-byte 60) (0)) :initially 0 :resizable t)
   (fn2-storage-snapshot :type (array (unsigned-byte 8) (0)) :initially 0 :resizable t)
   (fn2-storage-snapshot-stamp :type (array (unsigned-byte 60) (0)) :initially 0 :resizable t)
   (fn2-storage-fences :type (unsigned-byte 32) :initially 0)
   (fn2-storage-dead :type (unsigned-byte 1) :initially 0)))

(defun fn2-storage-clear (i fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage
                  :guard (and (fn2-sim-storage-wfp fn2-sim-storage) (natp i))
                  :measure (nfix (- (fn2-sim-storage-rows fn2-sim-storage) (nfix i)))))
  (if (or (not (natp (fn2-sim-storage-rows fn2-sim-storage))) (not (natp i)) (>= i (fn2-sim-storage-rows fn2-sim-storage))) fn2-sim-storage
    (let* ((fn2-sim-storage (fn2-sim-storage-set-pending i 0 fn2-sim-storage))
           (fn2-sim-storage (fn2-sim-storage-set-durable i 0 fn2-sim-storage))
           (fn2-sim-storage (fn2-sim-storage-set-stamp i 0 fn2-sim-storage))
           (fn2-sim-storage (fn2-sim-storage-set-durable-stamp i 0 fn2-sim-storage)))
      (fn2-storage-clear (+ 1 i) fn2-sim-storage))))

(defthm fn2-storage-clear-wfp
  (implies (fn2-sim-storage-wfp s)
           (fn2-sim-storage-wfp (fn2-storage-clear i s))))
(defthm fn2-storage-clear-type
  (implies (and (fn2-sim-storagep s) (fn2-sim-storage-wfp s) (natp i))
           (fn2-sim-storagep (fn2-storage-clear i s))))
(defthm fn2-storage-clear-rows
  (equal (fn2-sim-storage-rows (fn2-storage-clear i s))
         (fn2-sim-storage-rows s)))
(in-theory (disable fn2-storage-clear))

(defun fn2-storage-reset-fences (fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage :guard t))
  (let ((fn2-sim-storage (resize-fn2-storage-fence-owner 0 fn2-sim-storage)))
    (resize-fn2-storage-fence-owner (fn2-storage-fences fn2-sim-storage) fn2-sim-storage)))

(defthm fn2-storage-reset-fences-wfp
  (implies (fn2-sim-storage-wfp s)
           (fn2-sim-storage-wfp (fn2-storage-reset-fences s))))
(defthm fn2-storage-reset-fences-type
  (implies (fn2-sim-storagep s) (fn2-sim-storagep (fn2-storage-reset-fences s))))
(defthm fn2-storage-reset-fences-rows
  (equal (fn2-sim-storage-rows (fn2-storage-reset-fences s)) (fn2-sim-storage-rows s)))
(in-theory (disable fn2-storage-reset-fences))

(defun fn2-storage-init (nsectors nfences fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage
                  :guard (and (natp nsectors) (< nsectors 1048576)
                              (unsigned-byte-p 32 nfences)
                              (< (* 4096 nsectors nfences) 1152921504606846976))))
  (let* ((nbytes (* 4096 nsectors))
         (fn2-sim-storage (fn2-storage-columns-init nbytes fn2-sim-storage))
         (fn2-sim-storage (resize-fn2-storage-snapshot (* nbytes nfences) fn2-sim-storage))
         (fn2-sim-storage (resize-fn2-storage-snapshot-stamp (* nbytes nfences) fn2-sim-storage))
         (fn2-sim-storage (update-fn2-storage-fences nfences fn2-sim-storage))
         (fn2-sim-storage (fn2-storage-reset-fences fn2-sim-storage))
         (fn2-sim-storage (update-fn2-storage-dead 0 fn2-sim-storage)))
    (fn2-storage-clear 0 fn2-sim-storage)))

(defthm fn2-storage-init-wfp
  (implies (and (natp nsectors) (< nsectors 1048576))
           (fn2-sim-storage-wfp (fn2-storage-init nsectors nfences s))))
(in-theory (disable fn2-storage-init))

(defun fn2-storage-status (fault fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage :guard t))
  (cond ((equal (fn2-storage-dead fn2-sim-storage) 1) :io)
        ((eq fault :no-space) :no-space)
        ((eq fault :io) :io)
        (t :ok)))

; Redirected addresses are supplied explicitly: both intended and physical
; addresses remain visible in the simulator's fault record.
(defun fn2-storage-read-byte (address physical fault fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage :guard (fn2-sim-storage-wfp fn2-sim-storage)))
  (let ((code (fn2-storage-status fault fn2-sim-storage)))
    (cond ((not (eq code :ok)) (mv code 0))
          ((not (and (natp address) (< address (fn2-sim-storage-rows fn2-sim-storage))
                     (natp physical) (< physical (fn2-sim-storage-rows fn2-sim-storage))))
           (mv :bounds 0))
          (t (mv :ok (fn2-sim-storage-pending physical fn2-sim-storage))))))

; Stamp is the completion serial, shared by all bytes of one completed
; write.  The adapter increments serial once per completed write, never wraps.
; FUA persists this request only; it does not persist unrelated prior writes.
(defun fn2-storage-write-byte (address physical byte stamp fua fault fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage
                  :guard (and (fn2-sim-storage-wfp fn2-sim-storage)
                              (unsigned-byte-p 8 byte) (unsigned-byte-p 60 stamp))))
  (let ((code (fn2-storage-status fault fn2-sim-storage)))
    (cond ((not (eq code :ok)) (mv code fn2-sim-storage))
          ((not (and (natp address) (< address (fn2-sim-storage-rows fn2-sim-storage))
                     (natp physical) (< physical (fn2-sim-storage-rows fn2-sim-storage))))
           (mv :bounds fn2-sim-storage))
          (t (let* ((fn2-sim-storage (fn2-sim-storage-set-pending physical byte fn2-sim-storage))
                    (fn2-sim-storage (fn2-sim-storage-set-stamp physical stamp fn2-sim-storage))
                    (fn2-sim-storage (if fua (fn2-sim-storage-set-durable physical byte fn2-sim-storage)
                                       fn2-sim-storage))
                    (fn2-sim-storage (if fua (fn2-sim-storage-set-durable-stamp physical stamp fn2-sim-storage)
                                       fn2-sim-storage)))
               (mv :ok fn2-sim-storage))))))

(defthm fn2-storage-write-byte-wfp
  (implies (fn2-sim-storage-wfp s)
           (fn2-sim-storage-wfp (mv-nth 1 (fn2-storage-write-byte address physical byte stamp fua fault s)))))
(in-theory (disable fn2-storage-write-byte))

(defun fn2-storage-fence-slot-roomp (fence fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage :guard (fn2-sim-storage-wfp fn2-sim-storage)))
  (and (natp fence) (< fence (fn2-storage-fences fn2-sim-storage))
       (<= (* (+ 1 fence) (fn2-sim-storage-rows fn2-sim-storage))
           (fn2-storage-snapshot-length fn2-sim-storage))
       (<= (* (+ 1 fence) (fn2-sim-storage-rows fn2-sim-storage))
           (fn2-storage-snapshot-stamp-length fn2-sim-storage))))

; Search only the allocated fence slots, never the operation table.
(defun fn2-storage-find-fence (i owner fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage
                  :guard (and (natp i) (fn2-sim-storage-wfp fn2-sim-storage))
                  :measure (nfix (- (fn2-storage-fence-owner-length fn2-sim-storage) (nfix i)))))
  (if (or (not (natp i)) (>= i (fn2-storage-fence-owner-length fn2-sim-storage))) nil
    (if (and (equal (fn2-storage-fence-owneri i fn2-sim-storage) owner)
             (fn2-storage-fence-slot-roomp i fn2-sim-storage)) i
      (fn2-storage-find-fence (+ 1 i) owner fn2-sim-storage))))

(defthm fn2-storage-find-fence-bounds
  (implies (fn2-storage-find-fence i owner s)
           (and (natp (fn2-storage-find-fence i owner s))
                (< (fn2-storage-find-fence i owner s) (fn2-storage-fence-owner-length s))
                (fn2-storage-fence-slot-roomp (fn2-storage-find-fence i owner s) s)))
  :rule-classes (:rewrite :forward-chaining))
(defthm fn2-storage-find-fence-natural
  (or (null (fn2-storage-find-fence i owner s))
      (natp (fn2-storage-find-fence i owner s)))
  :rule-classes :type-prescription)
(defthm fn2-storage-find-fence-index
  (implies (fn2-storage-find-fence i owner s)
           (< (fn2-storage-find-fence i owner s)
              (len (nth *fn2-storage-fence-owneri* s))))
  :rule-classes (:rewrite :linear))
(in-theory (disable fn2-storage-find-fence))

(defun fn2-storage-fence-roomp (fence fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage :guard (fn2-sim-storage-wfp fn2-sim-storage)))
  (and (unsigned-byte-p 32 fence)
       (fn2-storage-find-fence 0 (+ 1 fence) fn2-sim-storage)))

(defun fn2-storage-fence-admission (fence fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage :guard (fn2-sim-storage-wfp fn2-sim-storage)))
  (cond ((not (unsigned-byte-p 32 fence)) :bounds)
        ((fn2-storage-fence-roomp fence fn2-sim-storage) :exhausted)
        ((fn2-storage-find-fence 0 0 fn2-sim-storage) :ok)
        (t :exhausted)))

; One traversal used for capture and commit; no transient byte lists.
(defun fn2-storage-fence-bytes (i base commit fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage
                  :guard (and (fn2-sim-storage-wfp fn2-sim-storage) (natp i) (natp base))
                  :measure (nfix (- (fn2-sim-storage-rows fn2-sim-storage) (nfix i)))))
  (if (or (not (natp (fn2-sim-storage-rows fn2-sim-storage))) (not (natp i)) (not (natp base))
          (>= i (fn2-sim-storage-rows fn2-sim-storage))
          (>= (+ base i) (fn2-storage-snapshot-length fn2-sim-storage))
          (>= (+ base i) (fn2-storage-snapshot-stamp-length fn2-sim-storage)))
      fn2-sim-storage
    (let* ((j (+ base i))
           (fn2-sim-storage
            (if commit
                (if (< (fn2-sim-storage-durable-stamp i fn2-sim-storage)
                       (fn2-storage-snapshot-stampi j fn2-sim-storage))
                    (let* ((fn2-sim-storage
                            (fn2-sim-storage-set-durable i (fn2-storage-snapshoti j fn2-sim-storage) fn2-sim-storage))
                           (fn2-sim-storage
                            (fn2-sim-storage-set-durable-stamp i (fn2-storage-snapshot-stampi j fn2-sim-storage) fn2-sim-storage)))
                      fn2-sim-storage)
                  fn2-sim-storage)
              (let* ((fn2-sim-storage
                      (update-fn2-storage-snapshoti j (fn2-sim-storage-pending i fn2-sim-storage) fn2-sim-storage))
                     (fn2-sim-storage
                      (update-fn2-storage-snapshot-stampi j (fn2-sim-storage-stamp i fn2-sim-storage) fn2-sim-storage)))
                fn2-sim-storage))))
      (fn2-storage-fence-bytes (+ 1 i) base commit fn2-sim-storage))))

(defthm fn2-storage-fence-bytes-wfp
  (implies (fn2-sim-storage-wfp s)
           (fn2-sim-storage-wfp (fn2-storage-fence-bytes i base commit s))))
(defthm fn2-storage-fence-bytes-owner-frame
  (equal (nth *fn2-storage-fence-owneri* (fn2-storage-fence-bytes i base commit s))
         (nth *fn2-storage-fence-owneri* s)))
(in-theory (disable fn2-storage-fence-bytes))

(defun fn2-storage-fence-capture (fence fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage :guard (fn2-sim-storage-wfp fn2-sim-storage)
                  :guard-hints (("Goal" :use ((:instance fn2-storage-find-fence-bounds
                                               (i 0) (owner 0) (s fn2-sim-storage)))))))
  (let ((code (fn2-storage-fence-admission fence fn2-sim-storage))
        (slot (fn2-storage-find-fence 0 0 fn2-sim-storage)))
    (if (not (and (eq code :ok) slot (unsigned-byte-p 32 fence)))
        (mv code fn2-sim-storage)
      (let* ((fn2-sim-storage (fn2-storage-fence-bytes 0 (* slot (fn2-sim-storage-rows fn2-sim-storage)) nil fn2-sim-storage))
             (fn2-sim-storage (update-fn2-storage-fence-owneri slot (+ 1 fence) fn2-sim-storage)))
        (mv :ok fn2-sim-storage)))))

(defun fn2-storage-fence-complete (fence fail lie fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage :guard (fn2-sim-storage-wfp fn2-sim-storage)
                  :guard-hints (("Goal" :use ((:instance fn2-storage-find-fence-bounds
                                               (i 0) (owner (+ 1 fence)) (s fn2-sim-storage)))))))
  (let ((slot (fn2-storage-fence-roomp fence fn2-sim-storage)))
    (if (not slot) (mv :bounds fn2-sim-storage)
      (let* ((failed (or fail (equal (fn2-storage-dead fn2-sim-storage) 1)))
             (fn2-sim-storage
              (if (or failed lie) fn2-sim-storage
                (fn2-storage-fence-bytes 0 (* slot (fn2-sim-storage-rows fn2-sim-storage)) t fn2-sim-storage)))
             (fn2-sim-storage (update-fn2-storage-fence-owneri slot 0 fn2-sim-storage)))
        (mv (if failed :io :ok) fn2-sim-storage)))))

; A failed barrier leaves pending visible.  Passing revert=t models the other
; allowed reopening view (old durable bytes).  The adapter still reports Io;
; neither view is evidence authorizing a durable acceptance.
(defun fn2-storage-reopen-bytes (i fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage
                  :guard (and (fn2-sim-storage-wfp fn2-sim-storage) (natp i))
                  :measure (nfix (- (fn2-sim-storage-rows fn2-sim-storage) (nfix i)))))
  (if (or (not (natp (fn2-sim-storage-rows fn2-sim-storage))) (not (natp i)) (>= i (fn2-sim-storage-rows fn2-sim-storage))) fn2-sim-storage
    (let* ((fn2-sim-storage (fn2-sim-storage-set-pending i (fn2-sim-storage-durable i fn2-sim-storage) fn2-sim-storage))
           (fn2-sim-storage (fn2-sim-storage-set-stamp i (fn2-sim-storage-durable-stamp i fn2-sim-storage) fn2-sim-storage)))
      (fn2-storage-reopen-bytes (+ 1 i) fn2-sim-storage))))

(defthm fn2-storage-reopen-bytes-wfp
  (implies (fn2-sim-storage-wfp s)
           (fn2-sim-storage-wfp (fn2-storage-reopen-bytes i s))))
(in-theory (disable fn2-storage-reopen-bytes))

(defun fn2-storage-reopen (revert fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage :guard (fn2-sim-storage-wfp fn2-sim-storage)))
  (if revert (fn2-storage-reopen-bytes 0 fn2-sim-storage) fn2-sim-storage))

; Crash chooser invokes this per 512-byte unit in ANY order.  Choices:
; 0 retains old durable; 1 lands written bytes; 2 lands zeroes; 3 garbage.
; Garbage is a supplied byte repeated through this unit; arbitrary per-byte
; garbage is expressible by fn2-storage-corrupt-byte.
(defun fn2-storage-land-bytes (i end choice garbage fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage
                  :guard (and (fn2-sim-storage-wfp fn2-sim-storage)
                              (natp i) (natp end) (unsigned-byte-p 8 garbage))
                  :measure (nfix (- (nfix end) (nfix i)))))
  (if (or (not (natp (fn2-sim-storage-rows fn2-sim-storage))) (not (natp i)) (not (natp end)) (>= i end)
          (>= i (fn2-sim-storage-rows fn2-sim-storage))) fn2-sim-storage
    (let* ((byte (cond ((equal choice 1) (fn2-sim-storage-pending i fn2-sim-storage))
                       ((equal choice 2) 0)
                       (t garbage)))
           ; Preserve a newer durable version even in a mixed dirty/stale
           ; unit. Other bytes of a dirty unit remain in its tear radius.
           (fn2-sim-storage
            (if (or (equal choice 0)
                    (< (fn2-sim-storage-stamp i fn2-sim-storage)
                       (fn2-sim-storage-durable-stamp i fn2-sim-storage)))
                fn2-sim-storage
              (fn2-sim-storage-set-durable i byte fn2-sim-storage))))
      (fn2-storage-land-bytes (+ 1 i) end choice garbage fn2-sim-storage))))

(defthm fn2-storage-land-bytes-wfp
  (implies (fn2-sim-storage-wfp s)
           (fn2-sim-storage-wfp (fn2-storage-land-bytes i end choice garbage s))))
(in-theory (disable fn2-storage-land-bytes))

(defun fn2-storage-pending-bytesp (i end fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage
                  :guard (and (fn2-sim-storage-wfp fn2-sim-storage) (natp i) (natp end))
                  :measure (nfix (- (nfix end) (nfix i)))))
  (if (or (not (natp i)) (not (natp end)) (>= i end)
          (>= i (fn2-sim-storage-rows fn2-sim-storage))) nil
    (or (> (fn2-sim-storage-stamp i fn2-sim-storage)
           (fn2-sim-storage-durable-stamp i fn2-sim-storage))
        (fn2-storage-pending-bytesp (+ 1 i) end fn2-sim-storage))))

(defun fn2-storage-unit-pendingp (unit fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage
                  :guard (and (fn2-sim-storage-wfp fn2-sim-storage) (unsigned-byte-p 32 unit))))
  (fn2-storage-pending-bytesp (* 512 unit) (+ 512 (* 512 unit)) fn2-sim-storage))

; A crash tears only units containing a pending write.  Its declared damage
; radius includes all bytes in that same 512-byte unit, including clean bytes.
; Clean units require a separate explicit collateral-corruption fault.
(defun fn2-storage-crash-unit (unit choice garbage fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage
                  :guard (and (fn2-sim-storage-wfp fn2-sim-storage)
                              (unsigned-byte-p 32 unit) (unsigned-byte-p 8 garbage))))
  (if (fn2-storage-unit-pendingp unit fn2-sim-storage)
      (fn2-storage-land-bytes (* 512 unit) (+ 512 (* 512 unit)) choice garbage fn2-sim-storage)
    fn2-sim-storage))

; Process death retains sticky physical device failure; only a new simulation
; initialization replaces the device. Release every fence slot; old snapshots
; cannot complete after death and are overwritten on the next capture.
(defun fn2-storage-crash-reset (fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage :guard (fn2-sim-storage-wfp fn2-sim-storage)))
  (let ((fn2-sim-storage (fn2-storage-reset-fences fn2-sim-storage)))
    (fn2-storage-reopen-bytes 0 fn2-sim-storage)))

(defun fn2-storage-kill-device (fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage :guard t))
  (update-fn2-storage-dead 1 fn2-sim-storage))

(defun fn2-storage-corrupt-byte (address byte fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage
                  :guard (and (fn2-sim-storage-wfp fn2-sim-storage) (unsigned-byte-p 8 byte))))
  (if (not (and (natp address) (< address (fn2-sim-storage-rows fn2-sim-storage))))
      fn2-sim-storage
    (let* ((fn2-sim-storage (fn2-sim-storage-set-durable address byte fn2-sim-storage))
           ; A clean cached byte sees bitrot too; dirty pending data is separate.
           (fn2-sim-storage
            (if (equal (fn2-sim-storage-stamp address fn2-sim-storage)
                       (fn2-sim-storage-durable-stamp address fn2-sim-storage))
                (fn2-sim-storage-set-pending address byte fn2-sim-storage)
              fn2-sim-storage)))
      fn2-sim-storage)))

(assert-event
 (and (eq (symbol-class 'fn2-storage-init (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn2-storage-read-byte (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn2-storage-write-byte (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn2-storage-fence-capture (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn2-storage-fence-complete (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn2-storage-crash-unit (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn2-storage-crash-reset (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn2-storage-corrupt-byte (w state)) :common-lisp-compliant)))

; Shape facts are deliberately about representations, not storage correctness.
; They keep composed adapter guard proofs from opening the storage recognizer.
(defmacro fn2-storage-shape-facts (name args extra mv-index)
  (let* ((result (if mv-index `(mv-nth ,mv-index (,name ,@args fn2-sim-storage))
                   `(,name ,@args fn2-sim-storage)))
         (ty (intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-PRESERVES-TYPE") name))
         (wf (intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-PRESERVES-WFP") name))
         (rows (intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-PRESERVES-ROWS") name)))
    `(progn
       (defthm ,ty
         (implies (and (fn2-sim-storagep fn2-sim-storage)
                       (fn2-sim-storage-wfp fn2-sim-storage) ,extra)
                  (fn2-sim-storagep ,result))
         :hints (("Goal" :in-theory (enable ,name))))
       (defthm ,wf
         (implies (fn2-sim-storage-wfp fn2-sim-storage)
                  (fn2-sim-storage-wfp ,result))
         :hints (("Goal" :in-theory (enable ,name))))
       (defthm ,rows
         (equal (fn2-sim-storage-rows ,result)
                (fn2-sim-storage-rows fn2-sim-storage))
         :hints (("Goal" :in-theory (e/d (,name) (fn2-sim-storage-rows)))))
       (in-theory (disable ,name)))))

(fn2-storage-shape-facts fn2-storage-fence-bytes (i base commit) (and (natp i) (natp base)) nil)
(fn2-storage-shape-facts fn2-storage-reopen-bytes (i) (natp i) nil)
(fn2-storage-shape-facts fn2-storage-land-bytes (i end choice garbage)
                         (and (natp i) (natp end) (unsigned-byte-p 8 garbage)) nil)
(fn2-storage-shape-facts fn2-storage-write-byte (address physical byte stamp fua fault)
                         (and (unsigned-byte-p 8 byte) (unsigned-byte-p 60 stamp)) 1)
(fn2-storage-shape-facts fn2-storage-fence-capture (fence) t 1)
(fn2-storage-shape-facts fn2-storage-fence-complete (fence fail lie) t 1)
(fn2-storage-shape-facts fn2-storage-reopen (revert) t nil)
(fn2-storage-shape-facts fn2-storage-crash-unit (unit choice garbage)
                         (and (unsigned-byte-p 32 unit) (unsigned-byte-p 8 garbage)) nil)
(fn2-storage-shape-facts fn2-storage-crash-reset () t nil)
(fn2-storage-shape-facts fn2-storage-kill-device () t nil)
(fn2-storage-shape-facts fn2-storage-corrupt-byte (address byte) (unsigned-byte-p 8 byte) nil)

(defthm fn2-storage-init-preserves-type
  (implies (and (fn2-sim-storagep s) (natp nsectors) (< nsectors 1048576)
                (unsigned-byte-p 32 nfences)
                (< (* 4096 nsectors nfences) 1152921504606846976))
           (fn2-sim-storagep (fn2-storage-init nsectors nfences s)))
  :hints (("Goal" :in-theory (enable fn2-storage-init))))

(defthm fn2-storage-read-byte-u8
  (implies (and (fn2-sim-storagep s) (fn2-sim-storage-wfp s))
           (unsigned-byte-p 8 (mv-nth 1 (fn2-storage-read-byte address physical fault s)))))

(defthm fn2-storage-snapshot-resize-rows
  (equal (fn2-sim-storage-rows (resize-fn2-storage-snapshot n s))
         (fn2-sim-storage-rows s)))
(defthm fn2-storage-snapshot-stamp-resize-rows
  (equal (fn2-sim-storage-rows (resize-fn2-storage-snapshot-stamp n s))
         (fn2-sim-storage-rows s)))
(in-theory (disable fn2-sim-storage-rows))
(defthm fn2-storage-init-rows
  (equal (fn2-sim-storage-rows (fn2-storage-init nsectors nfences s))
         (* 4096 nsectors))
  :hints (("Goal" :in-theory (enable fn2-storage-init))))

; Evaluated storage controls: overlapping writes straddling a fence, reversed
; fence completions, and FUA only affecting its own request.
(local
 (defun fn2-storage-overlap-control ()
   (declare (xargs :guard t))
   (with-local-stobj fn2-sim-storage
     (mv-let (answer fn2-sim-storage)
       (let ((fn2-sim-storage (fn2-storage-init 1 2 fn2-sim-storage)))
         (mv-let (c1 fn2-sim-storage) (fn2-storage-write-byte 17 17 11 1 nil nil fn2-sim-storage)
           (mv-let (c2 fn2-sim-storage) (fn2-storage-fence-capture 0 fn2-sim-storage)
             (mv-let (c3 fn2-sim-storage) (fn2-storage-write-byte 17 17 22 2 nil nil fn2-sim-storage)
               (mv-let (c4 fn2-sim-storage) (fn2-storage-fence-capture 1 fn2-sim-storage)
                 (mv-let (c5 fn2-sim-storage) (fn2-storage-fence-complete 0 nil nil fn2-sim-storage)
                   (let ((first (and (equal (fn2-sim-storage-durable 17 fn2-sim-storage) 11)
                                     (equal (fn2-sim-storage-pending 17 fn2-sim-storage) 22))))
                     (mv-let (c6 fn2-sim-storage) (fn2-storage-fence-complete 1 nil nil fn2-sim-storage)
                       (mv-let (c7 fn2-sim-storage) (fn2-storage-fence-complete 0 nil nil fn2-sim-storage)
                         (mv-let (c8 fn2-sim-storage) (fn2-storage-write-byte 18 18 33 3 nil nil fn2-sim-storage)
                           (mv-let (c9 fn2-sim-storage) (fn2-storage-write-byte 19 19 44 4 t nil fn2-sim-storage)
                             (mv (and first (eq c1 :ok) (eq c2 :ok) (eq c3 :ok) (eq c4 :ok)
                                      (eq c5 :ok) (eq c6 :ok) (eq c7 :bounds) (eq c8 :ok) (eq c9 :ok)
                                      (equal (fn2-sim-storage-durable 17 fn2-sim-storage) 22)
                                      (equal (fn2-sim-storage-durable 18 fn2-sim-storage) 0)
                                      (equal (fn2-sim-storage-durable 19 fn2-sim-storage) 44))
                                 fn2-sim-storage))))))))))))
       answer))))
(local (assert-event (fn2-storage-overlap-control)))

(local
 (defun fn2-storage-clean-crash-control ()
   (declare (xargs :guard t))
   (with-local-stobj fn2-sim-storage
     (mv-let (answer fn2-sim-storage)
       (let ((fn2-sim-storage (fn2-storage-init 2 1 fn2-sim-storage)))
         (mv-let (c1 fn2-sim-storage) (fn2-storage-write-byte 17 17 91 1 t nil fn2-sim-storage)
           (mv-let (c2 fn2-sim-storage) (fn2-storage-write-byte 4097 4097 92 2 nil nil fn2-sim-storage)
             (let* ((clean (not (fn2-storage-unit-pendingp 0 fn2-sim-storage)))
                    (dirty (fn2-storage-unit-pendingp 8 fn2-sim-storage))
                    (fn2-sim-storage (fn2-storage-crash-unit 0 2 0 fn2-sim-storage))
                    (fn2-sim-storage (fn2-storage-crash-unit 8 2 0 fn2-sim-storage))
                    (fn2-sim-storage (fn2-storage-crash-reset fn2-sim-storage))
                    (intact (and (equal (fn2-sim-storage-durable 17 fn2-sim-storage) 91)
                                 (equal (fn2-sim-storage-pending 17 fn2-sim-storage) 91)
                                 (equal (fn2-sim-storage-durable 4097 fn2-sim-storage) 0)))
                    (fn2-sim-storage (fn2-storage-kill-device fn2-sim-storage))
                    (fn2-sim-storage (fn2-storage-crash-reset fn2-sim-storage)))
               (mv (and (eq c1 :ok) (eq c2 :ok) clean dirty intact
                        (eq (fn2-storage-status nil fn2-sim-storage) :io))
                   fn2-sim-storage)))))
       answer))))
(local (assert-event (fn2-storage-clean-crash-control)))
