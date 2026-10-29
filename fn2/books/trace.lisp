; Bounded diagnostic transition ring. Runtime writes only fixed-width arrays.
; Decoding to lists belongs exclusively to independent simulator checkers.
(in-package "ACL2")
(include-book "columns")
(include-book "profile")
(defconst *fn2-trace-no-machine* 4294967295)
(defcolumns fn2-trace
  ((kind :u8) (machine :u32) (principal :u16) (position :u32) (bytes :u32) (steps :u32) (actions :u8) (runnable :bool) (wake-id :u32) (wake-principal :u16) (action-start :u32) (action-0-slot :u32) (action-0-gen :u60) (action-1-slot :u32) (action-1-gen :u60) (action-2-slot :u32) (action-2-gen :u60) (action-3-slot :u32) (action-3-gen :u60))
  :init-name fn2-trace-columns-init
  :extra-fields
  ((fn2-trace-enabled :type (unsigned-byte 1) :initially 0 :why "Ring-wide diagnostic control, independent of record rows.")
   (fn2-trace-head :type (unsigned-byte 32) :initially 0 :why "Ring-wide diagnostic control, independent of record rows.")
   (fn2-trace-count :type (unsigned-byte 32) :initially 0 :why "Ring-wide diagnostic control, independent of record rows.")
   (fn2-trace-lost :type (unsigned-byte 60) :initially 0 :why "Ring-wide diagnostic control, independent of record rows.")))

(defun fn2-trace-clear (fn2-trace)
  (declare (xargs :stobjs fn2-trace :guard (fn2-trace-wfp fn2-trace)))
  (let* ((fn2-trace (update-fn2-trace-head 0 fn2-trace))
         (fn2-trace (update-fn2-trace-count 0 fn2-trace))
         (fn2-trace (update-fn2-trace-lost 0 fn2-trace)))
    fn2-trace))
(fn2-trace-preserves fn2-trace-clear (fn2-trace) :rows nil :prefix "" :wfp-type nil)

(defun fn2-trace-init (capacity enabled fn2-trace)
  (declare (xargs :stobjs fn2-trace
                  :guard (and (unsigned-byte-p 32 capacity) (booleanp enabled))))
  (let* ((fn2-trace (fn2-trace-columns-init capacity fn2-trace))
         (fn2-trace (update-fn2-trace-enabled (if enabled 1 0) fn2-trace)))
    (fn2-trace-clear fn2-trace)))
(defthm fn2-trace-init-type
  (implies (and (fn2-tracep fn2-trace) (unsigned-byte-p 32 capacity))
           (fn2-tracep (fn2-trace-init capacity enabled fn2-trace))))
(defthm fn2-trace-init-wfp
  (implies (unsigned-byte-p 32 capacity)
           (fn2-trace-wfp (fn2-trace-init capacity enabled fn2-trace))))
(in-theory (disable fn2-trace-init))

; HEAD names the next write, COUNT the retained suffix. LOST saturates at the
; representation maximum rather than wrapping into a false no-loss report.
(defun fn2-trace-append (kind machine principal position bytes steps actions
                            runnable-after wake-id wake-principal action-start fn2-trace)
  (declare (xargs :stobjs fn2-trace :guard (fn2-trace-wfp fn2-trace)))
  (if (or (= (fn2-trace-enabled fn2-trace) 0)
          (not (natp (fn2-trace-head fn2-trace)))
          (>= (fn2-trace-head fn2-trace) (fn2-trace-rows fn2-trace))
          (not (and (unsigned-byte-p 8 kind) (unsigned-byte-p 32 machine)
                    (unsigned-byte-p 16 principal) (unsigned-byte-p 32 position)
                    (unsigned-byte-p 32 bytes) (unsigned-byte-p 32 steps)
                    (unsigned-byte-p 8 actions) (booleanp runnable-after)
                    (unsigned-byte-p 32 wake-id) (unsigned-byte-p 16 wake-principal)
                    (unsigned-byte-p 32 action-start))))
      fn2-trace
    (let* ((i (fn2-trace-head fn2-trace))
           (rows (fn2-trace-rows fn2-trace))
           (count (fn2-trace-count fn2-trace))
           (lost (fn2-trace-lost fn2-trace))
           (fn2-trace (fn2-trace-set-kind i kind fn2-trace))
           (fn2-trace (fn2-trace-set-machine i machine fn2-trace))
           (fn2-trace (fn2-trace-set-principal i principal fn2-trace))
           (fn2-trace (fn2-trace-set-position i position fn2-trace))
           (fn2-trace (fn2-trace-set-bytes i bytes fn2-trace))
           (fn2-trace (fn2-trace-set-steps i steps fn2-trace))
           (fn2-trace (fn2-trace-set-actions i actions fn2-trace))
           (fn2-trace (fn2-trace-set-runnable i (if runnable-after 1 0) fn2-trace))
           (fn2-trace (fn2-trace-set-wake-id i wake-id fn2-trace))
           (fn2-trace (fn2-trace-set-wake-principal i wake-principal fn2-trace))
           (fn2-trace (fn2-trace-set-action-start i action-start fn2-trace))
           (fn2-trace (fn2-trace-set-action-0-slot i 0 fn2-trace))
           (fn2-trace (fn2-trace-set-action-0-gen i 0 fn2-trace))
           (fn2-trace (fn2-trace-set-action-1-slot i 0 fn2-trace))
           (fn2-trace (fn2-trace-set-action-1-gen i 0 fn2-trace))
           (fn2-trace (fn2-trace-set-action-2-slot i 0 fn2-trace))
           (fn2-trace (fn2-trace-set-action-2-gen i 0 fn2-trace))
           (fn2-trace (fn2-trace-set-action-3-slot i 0 fn2-trace))
           (fn2-trace (fn2-trace-set-action-3-gen i 0 fn2-trace))
           (fn2-trace (update-fn2-trace-head
                       (if (< (+ 1 i) rows) (+ 1 i) 0) fn2-trace))
           (fn2-trace (update-fn2-trace-count
                       (if (< count rows) (+ 1 count) count) fn2-trace))
           (fn2-trace (update-fn2-trace-lost
                       (if (and (>= count rows) (< lost 1152921504606846975))
                           (+ 1 lost) lost) fn2-trace)))
      fn2-trace)))
(fn2-trace-preserves fn2-trace-append (kind machine principal position bytes steps actions runnable-after wake-id wake-principal action-start fn2-trace) :rows nil :prefix "" :wfp-type nil)

; Fill the most recently appended record from actual outbox OpRefs. Four is
; the declared descriptor quantum, never a traversal of an outstanding table.
(defun fn2-trace-action (ordinal opslot opgen fn2-trace)
  (declare (xargs :stobjs fn2-trace :guard (fn2-trace-wfp fn2-trace)))
  (let* ((head (fn2-trace-head fn2-trace))
         (rows (fn2-trace-rows fn2-trace))
         (i (if (zp head) (1- rows) (1- head))))
    (if (or (= (fn2-trace-enabled fn2-trace) 0)
            (zp (fn2-trace-count fn2-trace)) (not (natp i)) (>= i rows)
            (not (unsigned-byte-p 32 opslot)) (not (unsigned-byte-p 60 opgen)))
        fn2-trace
      (case ordinal
        (0 (let ((fn2-trace (fn2-trace-set-action-0-slot i opslot fn2-trace)))
             (fn2-trace-set-action-0-gen i opgen fn2-trace)))
        (1 (let ((fn2-trace (fn2-trace-set-action-1-slot i opslot fn2-trace)))
             (fn2-trace-set-action-1-gen i opgen fn2-trace)))
        (2 (let ((fn2-trace (fn2-trace-set-action-2-slot i opslot fn2-trace)))
             (fn2-trace-set-action-2-gen i opgen fn2-trace)))
        (3 (let ((fn2-trace (fn2-trace-set-action-3-slot i opslot fn2-trace)))
             (fn2-trace-set-action-3-gen i opgen fn2-trace)))
        (otherwise fn2-trace)))))
(fn2-trace-preserves fn2-trace-action (ordinal opslot opgen fn2-trace) :rows nil :prefix "" :wfp-type nil)

; Fixed record order shared with the test-only readers, not with the scheduler.
; 0 kind, 1 machine, 2 principal, 3 calendar position, 4 bytes, 5 steps,
; 6 actions, 7 runnable-after, 8 additional wake id, 9 wake principal,
; 10 initial outbox position, 11..18 four slot/generation pairs.
(defun fn2-trace-record (i fn2-trace)
  (declare (xargs :stobjs fn2-trace
                  :guard (and (fn2-trace-wfp fn2-trace) (natp i)
                              (< i (fn2-trace-rows fn2-trace)))))
  (list (fn2-trace-kind i fn2-trace)
        (fn2-trace-machine i fn2-trace)
        (fn2-trace-principal i fn2-trace)
        (fn2-trace-position i fn2-trace)
        (fn2-trace-bytes i fn2-trace)
        (fn2-trace-steps i fn2-trace)
        (fn2-trace-actions i fn2-trace)
        (fn2-trace-runnable i fn2-trace)
        (fn2-trace-wake-id i fn2-trace)
        (fn2-trace-wake-principal i fn2-trace)
        (fn2-trace-action-start i fn2-trace)
        (fn2-trace-action-0-slot i fn2-trace)
        (fn2-trace-action-0-gen i fn2-trace)
        (fn2-trace-action-1-slot i fn2-trace)
        (fn2-trace-action-1-gen i fn2-trace)
        (fn2-trace-action-2-slot i fn2-trace)
        (fn2-trace-action-2-gen i fn2-trace)
        (fn2-trace-action-3-slot i fn2-trace)
        (fn2-trace-action-3-gen i fn2-trace)))
(defun fn2-trace-records-aux (left i fn2-trace)
  (declare (xargs :stobjs fn2-trace :measure (nfix left)
                  :guard (and (fn2-trace-wfp fn2-trace) (natp left) (natp i))))
  (if (or (zp left) (>= i (fn2-trace-rows fn2-trace))) nil
    (cons (fn2-trace-record i fn2-trace)
          (fn2-trace-records-aux
           (1- left) (if (< (+ 1 i) (fn2-trace-rows fn2-trace)) (+ 1 i) 0)
           fn2-trace))))
(defun fn2-trace-records (fn2-trace)
  (declare (xargs :stobjs fn2-trace :guard (fn2-trace-wfp fn2-trace)))
  (let ((count (fn2-trace-count fn2-trace)) (rows (fn2-trace-rows fn2-trace)))
    (fn2-trace-records-aux (min count rows)
                           (if (< count rows) 0 (fn2-trace-head fn2-trace)) fn2-trace)))
(assert-event
 (fn2-profile-exports-compliant-p
  '(fn2-trace-init fn2-trace-clear fn2-trace-append fn2-trace-action
    fn2-trace-record fn2-trace-records) (w state)))
