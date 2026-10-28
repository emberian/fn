; Independent ownership monitor. All storage is reserved by fn2-own-init.
; The test-only semantic scans below never appear in a core runtime guard.
(in-package "ACL2")
(include-book "../books/pool")
(include-book "../books/vocab")
(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

(defcolumns fn2-own
  ((seen :bool) (gen :u60) (digest :u32))
  :init-name fn2-own-columns-init
  :extra-fields
  ((fn2-own-input-bytes :type (array (unsigned-byte 8) (0)) :initially 0 :resizable t)
   (fn2-own-input-state :type (array (unsigned-byte 8) (0)) :initially 0 :resizable t)
   (fn2-own-input-gen :type (array (unsigned-byte 60) (0)) :initially 0 :resizable t)
   (fn2-own-snapshot :type (array (unsigned-byte 60) (0)) :initially 0 :resizable t)
   (fn2-own-error :type (unsigned-byte 8) :initially 0)))

; Error numbers identify the first fault, so later fallout cannot hide it.
(defun fn2-own-fail (reason fn2-own)
  (declare (xargs :stobjs fn2-own :guard (unsigned-byte-p 8 reason)))
  (if (= (fn2-own-error fn2-own) 0)
      (update-fn2-own-error reason fn2-own)
    fn2-own))
(defthm fn2-own-fail-type
  (implies (and (fn2-ownp fn2-own) (unsigned-byte-p 8 reason))
           (fn2-ownp (fn2-own-fail reason fn2-own))))
(defthm fn2-own-fail-wfp
  (implies (fn2-own-wfp fn2-own)
           (fn2-own-wfp (fn2-own-fail reason fn2-own))))
(in-theory (disable fn2-own-fail))

(defun fn2-own-output-kindp (kind)
  (declare (xargs :guard t))
  (or (equal kind *fn2-action-send*) (equal kind *fn2-action-write*)))
(defun fn2-own-input-kindp (kind)
  (declare (xargs :guard t))
  (or (equal kind *fn2-action-receive*) (equal kind *fn2-action-read*)
      (equal kind *fn2-action-entropy*)))


; Shape support keeps composed monitoring guards independent of row semantics.
(defmacro fn2-own-preserves (name args hyps &optional position)
  (let* ((call `(,name ,@args fn2-own))
         (result (if position `(mv-nth ,position ,call) call)))
    `(progn
       (defthm ,(fn2-columns-sym name "-PRESERVES-TYPE")
         (implies (and (fn2-ownp fn2-own) (fn2-own-wfp fn2-own) ,@hyps)
                  (fn2-ownp ,result)))
       (defthm ,(fn2-columns-sym name "-PRESERVES-WFP")
         (implies (and (fn2-ownp fn2-own) (fn2-own-wfp fn2-own) ,@hyps)
                  (fn2-own-wfp ,result)))
       (in-theory (disable ,name)))))

; FNV-1a is evidence for accidental simulator bugs, not collision-free identity.
; The largest product is <2^57, within the supported 64-bit Lisp fixnum.
(defun fn2-own-hash-byte (hash byte)
  (declare (xargs :guard (and (unsigned-byte-p 32 hash) (unsigned-byte-p 8 byte))))
  (mod (ifix (* (logxor hash byte) 16777619)) 4294967296))
(defthm fn2-own-hash-byte-u32
  (unsigned-byte-p 32 (fn2-own-hash-byte hash byte))
  :hints (("Goal" :in-theory (disable logxor))))
(in-theory (disable fn2-own-hash-byte))

(defun fn2-own-pool-digest (base left hash fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix left)
                  :guard (and (natp base) (natp left) (unsigned-byte-p 32 hash))))
  (if (or (zp left) (>= base (fn2-pool-data-length fn2-pool))) hash
    (fn2-own-pool-digest (+ 1 base) (- left 1)
                         (fn2-own-hash-byte hash (fn2-pool-datai base fn2-pool)) fn2-pool)))
(defthm fn2-own-pool-digest-u32
  (implies (and (fn2-poolp fn2-pool) (natp base) (natp left) (unsigned-byte-p 32 hash))
           (unsigned-byte-p 32 (fn2-own-pool-digest base left hash fn2-pool)))
  :hints (("Goal" :in-theory (disable unsigned-byte-p))))
(in-theory (disable fn2-own-pool-digest))

; Generate a complete flat view from the outstanding-table declaration. This
; includes unused ring positions and every scalar except stray. New columns
; are automatically covered; the checker does not maintain a hand-written twin.
(defun fn2-own-word-cases (names i rowp)
  (if (endp names) nil
    (cons `(,i (,(car names) ,@(if rowp '(slot) nil) fn2-ops))
          (fn2-own-word-cases (cdr names) (+ 1 i) rowp))))
(defun fn2-own-column-readers (cols)
  (if (endp cols) nil
    (cons (fn2-columns-col-name 'fn2-ops (caar cols))
          (fn2-own-column-readers (cdr cols)))))
(defun fn2-own-scalar-readers (fields)
  (if (endp fields) nil
    (if (or (fn2-columns-arrayp (car fields)) (eq (caar fields) 'fn2-ops-stray))
        (fn2-own-scalar-readers (cdr fields))
      (cons (caar fields) (fn2-own-scalar-readers (cdr fields))))))
(make-event
 (let* ((schema (cdr (assoc-eq 'fn2-ops (table-alist 'fn2-columns (w state)))))
        (cols (fn2-own-column-readers (cadr (member-eq :columns schema))))
        (scalars (cons 'fn2-ops-rows
                       (fn2-own-scalar-readers (cadr (member-eq :extra-fields schema))))))
   `(progn
      (defconst *fn2-own-ncols* ,(len cols))
      (defconst *fn2-own-nscalars* ,(len scalars))
      (defun fn2-own-op-column-word (column slot fn2-ops)
        (declare (xargs :stobjs fn2-ops
                        :guard (and (fn2-ops-wfp fn2-ops) (natp slot)
                                    (< slot (fn2-ops-rows fn2-ops)))))
        (case column ,@(fn2-own-word-cases cols 0 t) (otherwise 0)))
      (defthm fn2-own-op-column-word-u60
        (implies (and (fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops) (natp slot)
                      (< slot (fn2-ops-rows fn2-ops)))
                 (unsigned-byte-p 60 (fn2-own-op-column-word column slot fn2-ops))))
      (defun fn2-own-op-scalar-word (i fn2-ops)
        (declare (xargs :stobjs fn2-ops))
        (case i ,@(fn2-own-word-cases scalars 0 nil) (otherwise 0)))
      (defthm fn2-own-op-scalar-word-u60
        (implies (fn2-opsp fn2-ops)
                 (unsigned-byte-p 60 (fn2-own-op-scalar-word i fn2-ops))))
      (in-theory (disable fn2-own-op-column-word fn2-own-op-scalar-word)))))

(defun fn2-own-ops-word-count (fn2-ops)
  (declare (xargs :stobjs fn2-ops :guard (fn2-ops-wfp fn2-ops)))
  (+ *fn2-own-nscalars* (* *fn2-own-ncols* (fn2-ops-rows fn2-ops))
     3 (fn2-ops-out-slot-length fn2-ops) (fn2-ops-out-gen-length fn2-ops)
     (fn2-ops-posted-fifo-length fn2-ops)))
(defun fn2-own-ops-word (i fn2-ops)
  (declare (xargs :stobjs fn2-ops :guard (and (fn2-ops-wfp fn2-ops) (natp i))))
  (let* ((rows (fn2-ops-rows fn2-ops))
         (nrows (* *fn2-own-ncols* rows))
         (qa (fn2-ops-out-slot-length fn2-ops))
         (qg (fn2-ops-out-gen-length fn2-ops))
         (qr (fn2-ops-posted-fifo-length fn2-ops)))
    (cond ((< i *fn2-own-nscalars*) (fn2-own-op-scalar-word i fn2-ops))
          ((< i (+ *fn2-own-nscalars* nrows))
           (let ((j (- i *fn2-own-nscalars*)))
             (fn2-own-op-column-word (mod j *fn2-own-ncols*)
                                     (floor j *fn2-own-ncols*) fn2-ops)))
          (t (let ((j (- i (+ *fn2-own-nscalars* nrows))))
               (cond ((= j 0) qa) ((= j 1) qg) ((= j 2) qr)
                     ((< j (+ 3 qa)) (fn2-ops-out-sloti (- j 3) fn2-ops))
                     ((< j (+ 3 qa qg)) (fn2-ops-out-geni (- j (+ 3 qa)) fn2-ops))
                     ((< j (+ 3 qa qg qr)) (fn2-ops-posted-fifoi (- j (+ 3 qa qg)) fn2-ops))
                     (t 0)))))))

(defthm fn2-own-ops-word-count-natp
  (implies (and (fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops))
           (natp (fn2-own-ops-word-count fn2-ops)))
  :rule-classes :type-prescription)
(in-theory (disable fn2-own-ops-word fn2-own-ops-word-count))

(defun fn2-own-copy-ops (n fn2-ops fn2-own)
  (declare (xargs :stobjs (fn2-ops fn2-own) :measure (nfix n)
                  :guard (and (fn2-ops-wfp fn2-ops) (natp n))))
  (if (zp n) fn2-own
    (let* ((i (- n 1)) (word (fn2-own-ops-word i fn2-ops))
           (fn2-own (if (and (< i (fn2-own-snapshot-length fn2-own))
                             (unsigned-byte-p 60 word))
                         (update-fn2-own-snapshoti i word fn2-own)
                       (fn2-own-fail 7 fn2-own))))
      (fn2-own-copy-ops i fn2-ops fn2-own))))
(fn2-own-preserves fn2-own-copy-ops (n fn2-ops)
  ((natp n) (fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops)))

(defun fn2-own-same-ops-p (n fn2-ops fn2-own)
  (declare (xargs :stobjs (fn2-ops fn2-own) :measure (nfix n)
                  :guard (and (fn2-ops-wfp fn2-ops) (natp n))))
  (if (zp n) t
    (let ((i (- n 1)))
      (and (< i (fn2-own-snapshot-length fn2-own))
           (equal (fn2-own-ops-word i fn2-ops) (fn2-own-snapshoti i fn2-own))
           (fn2-own-same-ops-p i fn2-ops fn2-own)))))

(defun fn2-own-clear-ops (n fn2-own)
  (declare (xargs :stobjs fn2-own :measure (nfix n)
                  :guard (and (fn2-own-wfp fn2-own) (natp n))))
  (if (zp n) fn2-own
    (let* ((i (- n 1))
           (fn2-own (if (< i (fn2-own-rows fn2-own))
                         (fn2-own-set-seen i 0 fn2-own) fn2-own)))
      (fn2-own-clear-ops i fn2-own))))
(defthm fn2-own-clear-ops-type
  (implies (and (fn2-ownp fn2-own) (fn2-own-wfp fn2-own) (natp n))
           (fn2-ownp (fn2-own-clear-ops n fn2-own))))
(defthm fn2-own-clear-ops-wfp
  (implies (and (fn2-own-wfp fn2-own) (natp n))
           (fn2-own-wfp (fn2-own-clear-ops n fn2-own))))
(in-theory (disable fn2-own-clear-ops))
(defun fn2-own-clear-input (n fn2-own)
  (declare (xargs :stobjs fn2-own :measure (nfix n) :guard (natp n)))
  (if (zp n) fn2-own
    (let* ((i (- n 1))
           (fn2-own (if (< i (fn2-own-input-state-length fn2-own))
                         (update-fn2-own-input-statei i 0 fn2-own) fn2-own)))
      (fn2-own-clear-input i fn2-own))))
(defthm fn2-own-clear-input-type
  (implies (and (fn2-ownp fn2-own) (natp n))
           (fn2-ownp (fn2-own-clear-input n fn2-own))))
(defthm fn2-own-clear-input-wfp
  (implies (and (fn2-own-wfp fn2-own) (natp n))
           (fn2-own-wfp (fn2-own-clear-input n fn2-own))))
(in-theory (disable fn2-own-clear-input))
(defun fn2-own-restart (fn2-own)
  (declare (xargs :stobjs fn2-own :guard (fn2-own-wfp fn2-own)))
  (let* ((fn2-own (fn2-own-clear-ops (fn2-own-rows fn2-own) fn2-own))
         (fn2-own (fn2-own-clear-input (fn2-own-input-state-length fn2-own) fn2-own)))
    fn2-own))
(fn2-own-preserves fn2-own-restart ()
  ())


(defun fn2-own-init (profile fn2-own)
  (declare (xargs :stobjs fn2-own :guard (fn2-profilep profile)
                  :guard-hints (("Goal" :in-theory (enable fn2-profilep fn2-profile-o fn2-profile-qa)))))
  (let* ((bytes (fn2-profile-pool-bytes (fn2-profile-pool-classes profile)))
         (ops (fn2-profile-o profile)) (qa (fn2-profile-qa profile))
         (fn2-own (fn2-own-columns-init ops fn2-own))
         (fn2-own (resize-fn2-own-input-bytes bytes fn2-own))
         (fn2-own (resize-fn2-own-input-state bytes fn2-own))
         (fn2-own (resize-fn2-own-input-gen bytes fn2-own))
         (fn2-own (resize-fn2-own-snapshot (+ *fn2-own-nscalars* 3
                                            (* (+ 2 *fn2-own-ncols*) ops) (* 2 qa)) fn2-own))
         (fn2-own (update-fn2-own-error 0 fn2-own)))
    (fn2-own-restart fn2-own)))

; This range marking invalidates old evidence even when reset kept the slot's
; generation. State 1 is lent/unwritten; state 2 is a witnessed physical byte.
(defun fn2-own-mark-input (base left gen fn2-own)
  (declare (xargs :stobjs fn2-own :measure (nfix left)
                  :guard (and (natp base) (natp left) (unsigned-byte-p 60 gen))))
  (if (zp left) fn2-own
    (if (not (and (< base (fn2-own-input-state-length fn2-own))
                   (< base (fn2-own-input-gen-length fn2-own))))
        (fn2-own-fail 7 fn2-own)
      (let* ((fn2-own (update-fn2-own-input-statei base 1 fn2-own))
             (fn2-own (update-fn2-own-input-geni base gen fn2-own)))
        (fn2-own-mark-input (+ 1 base) (- left 1) gen fn2-own)))))
(fn2-own-preserves fn2-own-mark-input (base left gen)
  ((natp base) (natp left) (unsigned-byte-p 60 gen)))


(defun fn2-own-observe-issue-parts (opslot fn2-pool fn2-ops fn2-own)
  (declare (xargs :stobjs (fn2-pool fn2-ops fn2-own)
                  :guard (and (fn2-pool-wfp fn2-pool) (fn2-ops-wfp fn2-ops)
                              (fn2-own-wfp fn2-own))))
  (if (not (and (natp opslot) (< opslot (fn2-ops-rows fn2-ops))
                 (< opslot (fn2-own-rows fn2-own))))
      (fn2-own-fail 7 fn2-own)
    (let* ((gen (fn2-ops-gen opslot fn2-ops))
           (kind (fn2-ops-kind opslot fn2-ops))
           (slot (fn2-ops-range-slot opslot fn2-ops))
           (off (fn2-ops-range-off opslot fn2-ops))
           (count (fn2-ops-range-len opslot fn2-ops)))
      (cond ((and (= (fn2-own-seen opslot fn2-own) 1)
                   (= (fn2-own-gen opslot fn2-own) gen)) fn2-own)
            ((not (or (fn2-own-output-kindp kind) (fn2-own-input-kindp kind))) fn2-own)
            ((>= slot (fn2-pool-rows fn2-pool)) (fn2-own-fail 1 fn2-own))
            (t
             (let* ((base (+ (fn2-pool-base slot fn2-pool) off))
                    (hash (fn2-own-pool-digest base count 2166136261 fn2-pool))
                    (fn2-own (fn2-own-set-seen opslot 1 fn2-own))
                    (fn2-own (fn2-own-set-gen opslot gen fn2-own))
                    (fn2-own (fn2-own-set-digest opslot hash fn2-own)))
               (if (fn2-own-input-kindp kind)
                   (fn2-own-mark-input base count (fn2-ops-range-gen opslot fn2-ops) fn2-own)
                 fn2-own)))))))
(fn2-own-preserves fn2-own-observe-issue-parts (opslot fn2-pool fn2-ops)
  ((fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool) (fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops)))


(defun fn2-own-observe-output-parts (opslot fn2-pool fn2-ops fn2-own)
  (declare (xargs :stobjs (fn2-pool fn2-ops fn2-own)
                  :guard (and (fn2-pool-wfp fn2-pool) (fn2-ops-wfp fn2-ops)
                              (fn2-own-wfp fn2-own))))
  (if (not (and (natp opslot) (< opslot (fn2-ops-rows fn2-ops))
                 (< opslot (fn2-own-rows fn2-own))))
      (fn2-own-fail 7 fn2-own)
    (let ((slot (fn2-ops-range-slot opslot fn2-ops)))
      (if (not (and (< slot (fn2-pool-rows fn2-pool))
                     (= (fn2-own-seen opslot fn2-own) 1)
                     (= (fn2-own-gen opslot fn2-own) (fn2-ops-gen opslot fn2-ops))
                     (= (fn2-ops-range-gen opslot fn2-ops) (fn2-pool-gen slot fn2-pool))
                     (= (fn2-pool-state slot fn2-pool) *fn2-pool-state-leased-out*)
                     (equal (fn2-own-digest opslot fn2-own)
                            (fn2-own-pool-digest
                             (+ (fn2-pool-base slot fn2-pool) (fn2-ops-range-off opslot fn2-ops))
                             (fn2-ops-range-len opslot fn2-ops) 2166136261 fn2-pool))))
          (fn2-own-fail 2 fn2-own)
        fn2-own))))
(fn2-own-preserves fn2-own-observe-output-parts (opslot fn2-pool fn2-ops)
  ((fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool) (fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops)))


; Observe the descriptor the adapter actually consumes, rather than assuming
; its saved copy still names the outstanding row's range. Checking identity
; separately also catches a wrong slot whose bytes happen to hash identically.
(defun fn2-own-observe-output-range-parts
    (opslot opgen rslot rgen off len fn2-pool fn2-ops fn2-own)
  (declare (xargs :stobjs (fn2-pool fn2-ops fn2-own)
                  :guard (and (fn2-pool-wfp fn2-pool) (fn2-ops-wfp fn2-ops)
                              (fn2-own-wfp fn2-own))))
  (if (not (and (natp opslot) (< opslot (fn2-ops-rows fn2-ops))
                 (equal opgen (fn2-ops-gen opslot fn2-ops))
                 (equal rslot (fn2-ops-range-slot opslot fn2-ops))
                 (equal rgen (fn2-ops-range-gen opslot fn2-ops))
                 (equal off (fn2-ops-range-off opslot fn2-ops))
                 (equal len (fn2-ops-range-len opslot fn2-ops))))
      (fn2-own-fail 1 fn2-own)
    (fn2-own-observe-output-parts opslot fn2-pool fn2-ops fn2-own)))
(fn2-own-preserves fn2-own-observe-output-range-parts
  (opslot opgen rslot rgen off len fn2-pool fn2-ops)
  ((fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
   (fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops)))


(defun fn2-own-record-input-byte-parts (slot gen index byte fn2-pool fn2-own)
  (declare (xargs :stobjs (fn2-pool fn2-own)
                  :guard (and (fn2-pool-wfp fn2-pool) (unsigned-byte-p 60 gen)
                              (natp index) (unsigned-byte-p 8 byte))))
  (if (not (and (natp slot) (< slot (fn2-pool-rows fn2-pool))))
      (fn2-own-fail 1 fn2-own)
    (let ((base (+ (fn2-pool-base slot fn2-pool) index)))
      (if (not (and (< base (fn2-own-input-bytes-length fn2-own))
                     (< base (fn2-own-input-state-length fn2-own))
                     (< base (fn2-own-input-gen-length fn2-own))
                     (= gen (fn2-pool-gen slot fn2-pool))
                     (= (fn2-pool-state slot fn2-pool) *fn2-pool-state-leased-in*)
                     (<= (fn2-pool-lease-off slot fn2-pool) index)
                     (< index (+ (fn2-pool-lease-off slot fn2-pool) (fn2-pool-lease-len slot fn2-pool)))))
          (fn2-own-fail 3 fn2-own)
        (let* ((fn2-own (update-fn2-own-input-bytesi base byte fn2-own))
               (fn2-own (update-fn2-own-input-statei base 2 fn2-own))
               (fn2-own (update-fn2-own-input-geni base gen fn2-own)))
          fn2-own)))))
(fn2-own-preserves fn2-own-record-input-byte-parts (slot gen index byte fn2-pool)
  ((fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool) (unsigned-byte-p 60 gen) (natp index) (unsigned-byte-p 8 byte)))


(defun fn2-own-observe-read-parts (slot gen index code byte fn2-pool fn2-own)
  (declare (xargs :stobjs (fn2-pool fn2-own) :guard (fn2-pool-wfp fn2-pool)))
  (if (not (eq code :ok)) fn2-own
    (if (not (and (natp slot) (< slot (fn2-pool-rows fn2-pool)) (natp index)
                   (equal (fn2-pool-gen slot fn2-pool) gen)
                   (or (= (fn2-pool-state slot fn2-pool) *fn2-pool-state-workspace*)
                       (= (fn2-pool-state slot fn2-pool) *fn2-pool-state-leased-out*))
                   (< index (fn2-pool-fill slot fn2-pool))))
        (fn2-own-fail 4 fn2-own)
      (let ((base (+ (fn2-pool-base slot fn2-pool) index)))
        (if (not (and (< base (fn2-own-input-bytes-length fn2-own))
                       (< base (fn2-own-input-state-length fn2-own))
                       (< base (fn2-own-input-gen-length fn2-own))))
            (fn2-own-fail 7 fn2-own)
          (if (and (equal (fn2-own-input-geni base fn2-own) gen)
                   (not (= (fn2-own-input-statei base fn2-own) 0))
                   (or (not (= (fn2-own-input-statei base fn2-own) 2))
                       (not (equal byte (fn2-own-input-bytesi base fn2-own)))))
              (fn2-own-fail 5 fn2-own)
            fn2-own))))))
(fn2-own-preserves fn2-own-observe-read-parts (slot gen index code byte fn2-pool)
  ((fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)))


; A successful machine write deliberately replaces received-byte provenance.
; It is legal only in workspace; the checker observes the completed core step.
(defun fn2-own-observe-core-write-parts (slot gen index code byte fn2-pool fn2-own)
  (declare (xargs :stobjs (fn2-pool fn2-own) :guard (fn2-pool-wfp fn2-pool)))
  (if (not (eq code :ok)) fn2-own
    (if (not (and (natp slot) (< slot (fn2-pool-rows fn2-pool)) (natp index)
                   (equal gen (fn2-pool-gen slot fn2-pool))
                   (= (fn2-pool-state slot fn2-pool) *fn2-pool-state-workspace*)
                   (< index (fn2-pool-fill slot fn2-pool))))
        (fn2-own-fail 4 fn2-own)
      (let ((base (+ (fn2-pool-base slot fn2-pool) index)))
        (if (not (and (< base (fn2-own-input-state-length fn2-own))
                       (< base (fn2-pool-data-length fn2-pool))
                       (equal byte (fn2-pool-datai base fn2-pool))))
            (fn2-own-fail 5 fn2-own)
          (update-fn2-own-input-statei base 0 fn2-own))))))
(fn2-own-preserves fn2-own-observe-core-write-parts
  (slot gen index code byte fn2-pool)
  ((fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)))

; EXPECTED-STRAY is a workload assertion, not the implementation's validator.
; The exact preallocated snapshot includes all nonstray state, not a hash.
(defun fn2-own-post-result
  (cell slot gen evkind outcome reason count aux0 aux1 expected-stray fn2-ops fn2-own)
  (declare (xargs :stobjs (fn2-ops fn2-own)
                  :guard (and (fn2-ops-wfp fn2-ops) (fn2-own-wfp fn2-own))))
  (let* ((words (fn2-own-ops-word-count fn2-ops))
         (stray (fn2-ops-stray fn2-ops))
         (fn2-own (if expected-stray (fn2-own-copy-ops words fn2-ops fn2-own) fn2-own))
         (fn2-ops (fn2-post-result cell slot gen evkind outcome reason count aux0 aux1 fn2-ops))
         (ok (if expected-stray
                 (and (equal (fn2-ops-stray fn2-ops) (fn2-saturating-inc60 stray))
                      (equal words (fn2-own-ops-word-count fn2-ops))
                      (fn2-own-same-ops-p words fn2-ops fn2-own))
               (equal stray (fn2-ops-stray fn2-ops))))
         (fn2-own (if ok fn2-own (fn2-own-fail 6 fn2-own))))
    (mv (if ok :ok :stray-contract) fn2-ops fn2-own)))
(fn2-own-preserves fn2-own-post-result (cell slot gen evkind outcome reason count aux0 aux1 expected-stray fn2-ops)
  ((fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops)) 2)


(defthm fn2-own-post-result-preserves-ops-type
  (implies (and (fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops))
           (fn2-opsp (mv-nth 1 (fn2-own-post-result
             cell slot gen evkind outcome reason count aux0 aux1 expected-stray fn2-ops fn2-own))))
  :hints (("Goal" :in-theory (enable fn2-own-post-result))))
(defthm fn2-own-post-result-preserves-ops-wfp
  (implies (and (fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops))
           (fn2-ops-wfp (mv-nth 1 (fn2-own-post-result
             cell slot gen evkind outcome reason count aux0 aux1 expected-stray fn2-ops fn2-own))))
  :hints (("Goal" :in-theory (enable fn2-own-post-result))))

; The following independent scans are test-only. A submitted send whose
; BorrowReleased was already harvested no longer names a borrowed range.
; Queued operations DO own their leases, before the adapter takes them.
(defun fn2-own-live-outputp (opslot fn2-ops)
  (declare (xargs :stobjs fn2-ops :verify-guards nil))
  (and (fn2-own-output-kindp (fn2-ops-kind opslot fn2-ops))
       (member-equal (fn2-ops-phase opslot fn2-ops)
                     (list *fn2-op-phase-queued* *fn2-op-phase-submitted* *fn2-op-phase-release-pending*))
       (= (fn2-ops-c1-harvested opslot fn2-ops) 0)))
(defun fn2-own-output-count (n slot fn2-ops)
  (declare (xargs :stobjs fn2-ops :verify-guards nil :measure (nfix n)))
  (if (zp n) 0
    (+ (if (and (fn2-own-live-outputp (- n 1) fn2-ops)
                (= slot (fn2-ops-range-slot (- n 1) fn2-ops))) 1 0)
       (fn2-own-output-count (- n 1) slot fn2-ops))))
(defun fn2-own-ranges-p (n fn2-pool fn2-ops)
  (declare (xargs :stobjs (fn2-pool fn2-ops) :verify-guards nil :measure (nfix n)))
  (if (zp n) t
    (let* ((i (- n 1)) (kind (fn2-ops-kind i fn2-ops))
           (phase (fn2-ops-phase i fn2-ops))
           (input (and (fn2-own-input-kindp kind)
                       (member-equal phase (list *fn2-op-phase-queued* *fn2-op-phase-submitted*))))
           (output (fn2-own-live-outputp i fn2-ops))
           (slot (fn2-ops-range-slot i fn2-ops)))
      (and
       (or (not (or input output))
           (and (natp slot) (< slot (fn2-pool-rows fn2-pool))
                (= (fn2-ops-range-gen i fn2-ops) (fn2-pool-gen slot fn2-pool))
                (= (fn2-ops-owner-kind i fn2-ops) (fn2-pool-owner-kind slot fn2-pool))
                (= (fn2-ops-owner-slot i fn2-ops) (fn2-pool-owner-slot slot fn2-pool))
                (= (fn2-ops-owner-gen i fn2-ops) (fn2-pool-owner-gen slot fn2-pool))
                (if input
                    (and (= (fn2-pool-state slot fn2-pool) *fn2-pool-state-leased-in*)
                         (= (fn2-pool-lease-op-slot slot fn2-pool) i)
                         (= (fn2-pool-lease-op-gen slot fn2-pool) (fn2-ops-gen i fn2-ops))
                         (= (fn2-pool-lease-off slot fn2-pool) (fn2-ops-range-off i fn2-ops))
                         (= (fn2-pool-lease-len slot fn2-pool) (fn2-ops-range-len i fn2-ops)))
                  (and (= (fn2-pool-state slot fn2-pool) *fn2-pool-state-leased-out*)
                       (<= (+ (fn2-ops-range-off i fn2-ops) (fn2-ops-range-len i fn2-ops))
                           (fn2-pool-fill slot fn2-pool))
                       (<= (fn2-own-output-count (fn2-ops-rows fn2-ops) slot fn2-ops)
                           (fn2-pool-out-count slot fn2-pool))))))
       (fn2-own-ranges-p i fn2-pool fn2-ops)))))

; Check immutable bytes at every observation boundary, including while the
; descriptor is still queued. The adapter completion hook checks again at the
; precise physical read, so a premature release cannot hide behind a turn.
(defun fn2-own-output-digests-p (n fn2-pool fn2-ops fn2-own)
  (declare (xargs :stobjs (fn2-pool fn2-ops fn2-own) :verify-guards nil
                  :measure (nfix n)))
  (if (zp n) t
    (let* ((i (- n 1)) (slot (fn2-ops-range-slot i fn2-ops)))
      (and (or (not (fn2-own-live-outputp i fn2-ops))
               (and (< i (fn2-own-rows fn2-own))
                    (< slot (fn2-pool-rows fn2-pool))
                    (= (fn2-own-seen i fn2-own) 1)
                    (= (fn2-own-gen i fn2-own) (fn2-ops-gen i fn2-ops))
                    (equal (fn2-own-digest i fn2-own)
                           (fn2-own-pool-digest
                            (+ (fn2-pool-base slot fn2-pool) (fn2-ops-range-off i fn2-ops))
                            (fn2-ops-range-len i fn2-ops) 2166136261 fn2-pool))))
           (fn2-own-output-digests-p i fn2-pool fn2-ops fn2-own)))))

(defun fn2-own-status (fn2-own)
  (declare (xargs :stobjs fn2-own))
  (case (fn2-own-error fn2-own)
    (0 :pass) (1 '(:fail :range-identity)) (2 '(:fail :output-mutated))
    (3 '(:fail :input-outside-loan)) (4 '(:fail :unreadable-input))
    (5 '(:fail :input-byte-mismatch)) (6 '(:fail :stray-mutated-state))
    (otherwise '(:fail :checker-capacity))))
(defun fn2-check-own-parts (fn2-pool fn2-ops fn2-own)
  (declare (xargs :stobjs (fn2-pool fn2-ops fn2-own) :verify-guards nil))
  (cond ((not (eq (fn2-own-status fn2-own) :pass)) (fn2-own-status fn2-own))
        ((not (fn2-pool-semanticp fn2-pool)) '(:fail :pool-semantic-invariant))
        ((not (fn2-own-ranges-p (fn2-ops-rows fn2-ops) fn2-pool fn2-ops))
         '(:fail :op-range-ownership))
        ((not (fn2-own-output-digests-p (fn2-ops-rows fn2-ops) fn2-pool fn2-ops fn2-own))
         '(:fail :output-mutated))
        (t :pass)))

(assert-event
 (fn2-profile-exports-compliant-p
  '(fn2-own-fail fn2-own-output-kindp fn2-own-input-kindp fn2-own-hash-byte
    fn2-own-pool-digest fn2-own-op-column-word fn2-own-op-scalar-word
    fn2-own-ops-word-count fn2-own-ops-word fn2-own-copy-ops fn2-own-same-ops-p
    fn2-own-init fn2-own-clear-ops fn2-own-clear-input fn2-own-restart
    fn2-own-mark-input fn2-own-observe-issue-parts fn2-own-observe-output-parts
    fn2-own-observe-output-range-parts fn2-own-record-input-byte-parts fn2-own-observe-read-parts
    fn2-own-observe-core-write-parts fn2-own-post-result fn2-own-status)
  (w state)))
