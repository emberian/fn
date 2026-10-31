; Layer C in the served core, seam C-S3 (fn2/docs/c-ordered-runs.md §8 item 8):
; every engine write of a transaction goes through its batch's private
; successor. A transaction's write slots are declared at :prepare (put, arg,
; arg-octets, resolve); in its :ready arm, in one transition, stage computes
; every slot's row against the tip and holds room, out reads an assigned
; value, B admits the member, and bind writes every row into the batch's
; private overlays; release frees the slots at the outcome. B's commit kind
; publishes a batch (its private overlays, of every schema, readable in one
; step) or drops it. The tables, the engine row, the defcosts and the core
; wrappers (fn2-successor-prepare-events and -commit-events, materialized in
; assembly-callbacks-c-prepare and -commit) are three books': this one holds the tables,
; the declaring calls (put, arg, arg-octets) and resolve; machines-c-stage
; stage and out; machines-c-bind bind, release, publication, the defcosts
; and the wrappers (C-SUCCESSOR-BOOK).
(in-package "ACL2")
(include-book "machines-c-sealer-kind")
(fn2-book-layer :c)
;; The assembly's dispatchers case-split over every schema id when open; the
;; successor treats them as opaque (their type facts are the assembly's).
(local (in-theory (disable fn2-run-layout-fields fn2-run-layout-keys fn2-run-layout-merge fn2-run-layout-size
                           fn2-fold-key-arg fn2-fold-arity fn2-fold-assigned-p fn2-run-layout-octets-max
                           fn2-run-layout-value-ok fn2-run-layout-fold-p fn2-run-version)))

; ---------------------------------------------------------------------------
; C-ENGINE-OWNER (as built, C1c): the engine's workspaces (overlay arenas,
; the bind scratch, the sealer's pages) are owned by the sealer machine's row:
; kind = fn2-sealer's position in the registry (the index's *FN2-SEALER-KIND*,
; asserted equal in machines-c-sealer.lisp), local slot 0, generation 1. The
; local slot, not the global id, because these constants are used before the
; index exists.
(make-event (value `(defconst *fn2-idc-owner-kind*
                     ,(let ((pos (position-eq 'fn2-sealer (fn2-machine-names (w state))))) (if (natp pos) pos 254)))))
(assert-event (not (equal *fn2-idc-owner-kind* 254)))
(defconst *fn2-idc-owner-slot* 0)
(defconst *fn2-idc-owner-gen* 1)
; The bind scratch takes one slot's octets at a time: an identity fact's
; content at 0 and its Message-ID at 32, or an entry's octet fields in field
; order from 0.
(defconst *fn2-idc-scratch-bytes* 4096)
(defconst *fn2-idc-scratch-mid* 32)
; An identity entry is at most the Message-ID, the 32-byte content and this
; much more (lengths, state, three identifiers).
(defconst *fn2-idc-entry-overhead* 48)

; A write slot's block of field rows (C-STRIPE): the staged row at +0 (key
; fields then value fields, at most 12), the args as given at +12 (a value,
; a packed handle for :out, an octet reference), the args evaluated at +24
; (a fold's event args, a record's article and principal), the key's row
; read from the installed runs at +36 (its value fields, at most 8).
(defconst *fn2-succ-entry* 0)
(defconst *fn2-succ-raw* 12)
(defconst *fn2-succ-eval* 24)
(defconst *fn2-succ-res* 36)
(defconst *fn2-succ-fields-max* 12)
(defconst *fn2-succ-values-max* 8)
(assert-event (<= (+ *fn2-succ-res* *fn2-succ-values-max*) *fn2-succ-block*))

;; Every assembled schema fits a slot: at most 12 entry fields and, for a
;; fold, 8 value fields and 12 args per event kind; its octet fields fit the
;; bind scratch together.
(defun fn2-succ-kinds-fit (sid kinds)
 (declare (xargs :verify-guards nil))
 (or (atom kinds) (and (<= (nfix (fn2-fold-arity sid (car kinds))) *fn2-succ-fields-max*) (fn2-succ-kinds-fit sid (cdr kinds)))))
(defun fn2-succ-octets-total (sid f n)
 (declare (xargs :verify-guards nil :measure (nfix (- (nfix n) (nfix f)))))
 (if (<= (nfix n) (nfix f)) 0 (+ (nfix (fn2-run-layout-octets-max sid f)) (fn2-succ-octets-total sid (+ 1 (nfix f)) n))))
(defun fn2-succ-schemas-fit (ids)
 (declare (xargs :verify-guards nil))
 (or (atom ids)
     (let* ((sid (car ids)) (nf (fn2-run-layout-fields sid 0)))
      (and (<= nf *fn2-succ-fields-max*)
           (or (not (fn2-run-layout-fold-p sid)) (<= (- nf (fn2-run-layout-keys sid)) *fn2-succ-values-max*))
           (fn2-succ-kinds-fit sid *fn2-run-fold-kinds*)
           (<= (fn2-succ-octets-total sid 0 nf) *fn2-idc-scratch-bytes*)
           (fn2-succ-schemas-fit (cdr ids))))))
(assert-event (fn2-succ-schemas-fit *fn2-run-assembled-ids*))

; ---------------------------------------------------------------------------
; Tables. The engine row: the bind scratch (held once taken), the arena
; size, the next overlay sequence number. A transaction row (one per
; transaction, as its decision row): its phase, the slot holding its
; identity fact (1 + index, or 0), its batch and commit position once bound,
; resolve's progress (slot RI, run bound RBOUND), and an exact lookup's
; (machines-c-groups.lisp: LPHASE, LBOUND, LROW, LVER). A slot row (row
; T * 16 + I): schema, kind (:insert, :record, or one of the folds' event
; kinds), the masks of args given (SET), given :event (EVENTS) and given
; :out (OUTS), what resolve found (FOUND, the schema's run version VRUN), the
; staged entry's SIZE, the owner its octet args are read under, the args
; declared late (LATE, C-S3a: octets given between stage and bind) and the
; late args filled since the last stage (FILLED).
(defcolumns fn2-id-engine ((scratch :bool) (slot :u32) (gen :u60) (arena :u32) (seq :u60)))
(defun fn2-id-engine-init-arena (bytes fn2-id-engine)
 (declare (xargs :stobjs fn2-id-engine :guard (unsigned-byte-p 32 bytes)))
 (let ((fn2-id-engine (fn2-id-engine-init 1 fn2-id-engine)))
  (fn2-id-engine-set-arena 0 bytes fn2-id-engine)))
(fn2-idc-child fn2-core-id-engine fn2-id-engine (fn2-id-engine-init-arena (fn2-b-capacity :identity-arena-bytes 65536 profile) fn2-id-engine)
 "The engine's bind scratch, arena size and overlay sequence (C-S3).")
(defcolumns fn2-succ-txns
 ((phase (:enum fn2-succ-phase (:idle :open :staged :bound :published)))
  (record :u8) (batch :u60) (event :u60)
  (ri :u32) (rstate (:enum fn2-succ-resolve (:fresh :next :look))) (rbound :u60)
  (lphase (:enum fn2-succ-lookup (:idle :overlays :runs :scan))) (lbound :u60) (lrow :u32) (lver :u60)))
(make-event
 `(defcolumns fn2-succ-slots
   ((phase (:enum fn2-succ-slot-phase (:empty :put :resolved)))
    (sid :u60) (kind (:enum fn2-succ-kind ,(append '(:insert :record) *fn2-run-fold-kinds*)))
    (set :u32) (events :u32) (outs :u32) (found :bool) (vrun :u60) (size :u32)
    (oset :bool) (sk :u8) (ss :u32) (sg :u60) (late :u32) (filled :u32))))
(fn2-idc-child fn2-core-succ-txns fn2-succ-txns
 (fn2-succ-txns-init (+ (nfix (fn2-profile-t profile)) (fn2-b-read-rows profile)) fn2-succ-txns)
 "A transaction's writes survive its yields between :prepare and its outcome (C-S3); then one row per read row, its exact lookup's continuation (C-S4).")
(fn2-idc-child fn2-core-succ-slots fn2-succ-slots (fn2-succ-slots-init (* *fn2-succ-slots* (nfix (fn2-profile-t profile))) fn2-succ-slots)
 "Each transaction's write slots (C-S3).")

; The first overlay row at or after O in phase PHASE (and, for a private
; one, of batch B); past the last, the row count.
(defun fn2-idc-find-overlay (k o phase b fn2-overlays)
 (declare (xargs :stobjs fn2-overlays :measure (nfix k) :guard (and (fn2-overlays-wfp fn2-overlays) (natp k))))
 (cond ((not (and (natp o) (< o (fn2-overlays-rows fn2-overlays)) (posp k))) (nfix (fn2-overlays-rows fn2-overlays)))
       ((and (equal (fn2-overlays-phase o fn2-overlays) phase)
             (or (not (equal phase *fn2-overlay-phase-private*)) (equal (fn2-overlays-batch o fn2-overlays) b)))
        o)
       (t (fn2-idc-find-overlay (- k 1) (+ 1 o) phase b fn2-overlays))))
(defthm fn2-idc-find-overlay-natp (natp (fn2-idc-find-overlay k o phase b fn2-overlays)) :rule-classes :type-prescription)
(defun fn2-idc-count-overlays (k o phase fn2-overlays)
 (declare (xargs :stobjs fn2-overlays :measure (nfix k) :guard (and (fn2-overlays-wfp fn2-overlays) (natp k))))
 (cond ((not (and (natp o) (< o (fn2-overlays-rows fn2-overlays)) (posp k))) 0)
       (t (+ (if (equal (fn2-overlays-phase o fn2-overlays) phase) 1 0)
             (fn2-idc-count-overlays (- k 1) (+ 1 o) phase fn2-overlays)))))
(defthm fn2-idc-count-overlays-natp (natp (fn2-idc-count-overlays k o phase fn2-overlays)) :rule-classes :type-prescription)

;; Shapes of the operations the successor uses (type, wfp, rows of every
;; stobj each returns), proved here once, each operation opened alone; READS
;; are folded (C-SHAPE-READS).
(defmacro fn2-idc-op-shape (fn args outs hyps &optional (plain 'nil) reads)
 `(defthm ,(fn2-columns-sym fn "-IDC-SHAPE")
   (implies (and ,@hyps) (and ,@(fn2-fc-shape-claims (if (consp (car outs)) outs (fn2-idc-shape-outs outs 1)) (cons fn args))))
   :hints (("Goal" :in-theory ,(cond ((eq plain :min) `(e/d (,fn) (fn2-overlays-rows fn2-overlay-index-rows fn2-fields-rows fn2-pool-rows ,@reads)))
                                     (plain `(e/d (,fn) (fn2-overlays-rows fn2-overlay-index-rows fn2-fields-rows fn2-pool-rows
                                                   fn2-id-engine-rows fn2-id-decides-rows fn2-id-stamps-rows
                                                   fn2-succ-txns-rows fn2-succ-slots-rows fn2-run-cursors-rows
                                                   fn2-run-paths-rows fn2-run-installed-rows
                                                   fn2-pool-reserve fn2-pool-release fn2-pool-reset fn2-pool-read
                                                   fn2-pool-write fn2-pool-class-for ,@reads)))
                                     (t
                                 `(e/d (,fn) (fn2-overlaysp fn2-overlays-wfp fn2-overlay-indexp fn2-overlay-index-wfp
                                          fn2-fieldsp fn2-fields-wfp fn2-poolp fn2-pool-wfp fn2-overlays-rows
                                          fn2-overlay-index-rows fn2-fields-rows fn2-pool-rows
                                          fn2-pool-reserve fn2-pool-release fn2-pool-reset fn2-pool-read fn2-pool-write
                                          fn2-pool-class-for fn2-id-enginep fn2-id-engine-wfp fn2-id-engine-rows
                                          fn2-id-decidesp fn2-id-decides-wfp fn2-id-decides-rows
                                          fn2-id-stampsp fn2-id-stamps-wfp fn2-id-stamps-rows ,@reads))))))))
(fn2-idc-op-shape fn2-ov-start (o schema slot gen ibase icap okind oslot ogen cov fn2-overlays fn2-overlay-index fn2-pool)
 (fn2-overlays fn2-pool) ((fn2-overlaysp fn2-overlays) (fn2-overlays-wfp fn2-overlays) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)))
(fn2-idc-op-shape fn2-ov-advance (o from to fn2-overlays) (fn2-overlays) ((fn2-overlaysp fn2-overlays) (fn2-overlays-wfp fn2-overlays)))
(fn2-idc-op-shape fn2-ov-write (o pos ebase repl fn2-overlays fn2-overlay-index fn2-fields fn2-pool) (fn2-overlays fn2-overlay-index fn2-pool)
 ((fn2-overlaysp fn2-overlays) (fn2-overlays-wfp fn2-overlays) (fn2-overlay-indexp fn2-overlay-index)
  (fn2-overlay-index-wfp fn2-overlay-index) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
 nil (fn2-ov-okp fn2-overlays-schema fn2-overlays-fill fn2-overlays-cap fn2-overlays-slot fn2-overlays-gen
      fn2-overlays-okind fn2-overlays-oslot fn2-overlays-ogen fn2-run-layout-size))
(fn2-idc-op-shape fn2-ov-insert (o ebase eb fn2-overlays fn2-overlay-index fn2-fields fn2-pool) (fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
 ((fn2-overlaysp fn2-overlays) (fn2-overlays-wfp fn2-overlays) (fn2-overlay-indexp fn2-overlay-index)
  (fn2-overlay-index-wfp fn2-overlay-index) (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
 nil (fn2-ov-okp fn2-overlays-phase fn2-overlays-okind fn2-overlays-oslot fn2-overlays-ogen fn2-overlays-count
      fn2-overlays-icap fn2-overlays-schema fn2-run-layout-merge))
(fn2-idc-op-shape fn2-id-record-insert (d o ebase sbase article binding principal fn2-id-decides fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
 (fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
 ((fn2-id-decidesp fn2-id-decides) (fn2-id-decides-wfp fn2-id-decides)
  (fn2-overlaysp fn2-overlays) (fn2-overlays-wfp fn2-overlays) (fn2-overlay-indexp fn2-overlay-index)
  (fn2-overlay-index-wfp fn2-overlay-index) (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
 :min (fn2-id-decides-others fn2-overlays-okind fn2-overlays-oslot fn2-overlays-ogen))
(in-theory (disable fn2-ov-start fn2-ov-advance))

;; Each function's output shapes (type, wfp, rows), proved right after it.
(defun fn2-idc-hyp-list (stobjs)
 (declare (xargs :verify-guards nil))
 (if (atom stobjs) nil
  (list* `(,(fn2-columns-sym (car stobjs) "P") ,(car stobjs)) `(,(fn2-columns-sym (car stobjs) "-WFP") ,(car stobjs))
         (fn2-idc-hyp-list (cdr stobjs)))))
(defmacro fn2-idc-fn-shape (fn args outs stobjs &optional (mode 't) reads)
 `(progn (fn2-idc-op-shape ,fn ,args ,outs ,(fn2-idc-hyp-list stobjs) ,mode ,reads)
         (in-theory (disable ,fn))))
; ---------------------------------------------------------------------------
; Field-row helpers.

; Copy row FROM to row TO (value and reference; the codec's resume columns
; are scratch); N rows FROM.. to TO...
(defun fn2-succ-copy-row (from to fn2-fields)
 (declare (xargs :stobjs fn2-fields :guard (and (fn2-fields-wfp fn2-fields) (natp from) (natp to))))
 (if (not (and (natp from) (natp to) (< from (fn2-fields-rows fn2-fields)) (< to (fn2-fields-rows fn2-fields)))) fn2-fields
  (fn2-fields-put to (value (fn2-fields-value from fn2-fields)) (ref-slot (fn2-fields-ref-slot from fn2-fields))
                  (ref-gen (fn2-fields-ref-gen from fn2-fields)) (ref-off (fn2-fields-ref-off from fn2-fields))
                  (ref-len (fn2-fields-ref-len from fn2-fields)) (status (fn2-fields-status from fn2-fields)))))
(fn2-fields-preserves fn2-succ-copy-row (from to fn2-fields) :position nil :raw-rows t)
(defun fn2-succ-copy-rows (n from to fn2-fields)
 (declare (xargs :stobjs fn2-fields :measure (nfix n) :guard (and (fn2-fields-wfp fn2-fields) (natp n) (natp from) (natp to))))
 (cond ((zp n) fn2-fields)
       ((not (and (natp from) (natp to) (< (+ from n -1) (fn2-fields-rows fn2-fields)) (< (+ to n -1) (fn2-fields-rows fn2-fields))))
        fn2-fields)
       (t (let ((fn2-fields (fn2-succ-copy-row from to fn2-fields)))
           (fn2-succ-copy-rows (- n 1) (+ 1 from) (+ 1 to) fn2-fields)))))
(fn2-fields-preserves fn2-succ-copy-rows (n from to fn2-fields) :position nil :raw-rows t)
; Set N rows from BASE to the value 0 (an absent fold row reads as zeros).
(defun fn2-succ-zero-rows (n base fn2-fields)
 (declare (xargs :stobjs fn2-fields :measure (nfix n) :guard (and (fn2-fields-wfp fn2-fields) (natp n) (natp base))))
 (cond ((zp n) fn2-fields)
       ((not (and (natp base) (< (+ base n -1) (fn2-fields-rows fn2-fields)))) fn2-fields)
       (t (let ((fn2-fields (fn2-fields-put (+ base n -1) (value 0) (ref-len 0))))
           (fn2-succ-zero-rows (- n 1) base fn2-fields)))))
(fn2-fields-preserves fn2-succ-zero-rows (n base fn2-fields) :position nil :raw-rows t)

; A slot's kind as the keyword its schema names it by.
(defun fn2-succ-kindkw (code)
 (declare (xargs :guard t))
 (if (unsigned-byte-p 8 code) (fn2-succ-kind-code->keyword code) nil))
; The number of args slot kind CODE of schema SID takes: an insert's entry
; fields, a record's article and principal, a fold event's args.
(defun fn2-succ-arity (sid code)
 (declare (xargs :guard t))
 (cond ((equal code *fn2-succ-kind-insert*) (nfix (fn2-run-layout-fields sid 0)))
       ((equal code *fn2-succ-kind-record*) 2)
       (t (nfix (fn2-fold-arity sid (fn2-succ-kindkw code))))))
(defthm fn2-succ-arity-natp (natp (fn2-succ-arity sid code)) :rule-classes :type-prescription)
(in-theory (disable fn2-succ-kindkw fn2-succ-arity))
; Whether arg J of event KW of fold SID is one of its key args.
(defun fn2-succ-key-arg-p (k kf sid kw j)
 (declare (xargs :guard (natp kf) :measure (nfix k)))
 (and (posp k) (or (equal (fn2-fold-key-arg sid kw kf) j) (fn2-succ-key-arg-p (- k 1) (+ 1 (nfix kf)) sid kw j))))
(defun fn2-succ-bit (j) (declare (xargs :guard (natp j))) (ash 1 (nfix j)))
(defun fn2-succ-has (mask j) (declare (xargs :guard (natp j))) (not (equal (logand (nfix mask) (fn2-succ-bit j)) 0)))
(defthm fn2-succ-bit-natp (natp (fn2-succ-bit j)) :rule-classes :type-prescription)
(local (in-theory (disable fn2-succ-bit fn2-succ-has)))

; ---------------------------------------------------------------------------
; Declaring writes (at :prepare).

; Slot I of transaction TX writes schema SID by KIND: a fold event kind of
; SID, :insert (a whole entry of a :unique or :latest schema that is not a
; fold), or :record (SID 1: the identity fact of decision TX, at most one per
; transaction). Any change to a transaction's slots leaves it :open (stage
; again) and restarts resolve.
(defun fn2-succ-put (tx i sid kind fn2-succ-txns fn2-succ-slots)
 (declare (xargs :stobjs (fn2-succ-txns fn2-succ-slots) :guard t))
 (b* (((unless (and (fn2-succ-txns-wfp fn2-succ-txns) (fn2-succ-slots-wfp fn2-succ-slots))) (mv :state fn2-succ-txns fn2-succ-slots))
      ((unless (and (natp tx) (< tx (fn2-succ-txns-rows fn2-succ-txns)) (natp i) (< i *fn2-succ-slots*)
                    (< (+ (* tx *fn2-succ-slots*) i) (fn2-succ-slots-rows fn2-succ-slots)) (unsigned-byte-p 60 sid)))
       (mv :bounds fn2-succ-txns fn2-succ-slots))
      ((unless (member (fn2-succ-txns-phase tx fn2-succ-txns)
                       (list *fn2-succ-phase-idle* *fn2-succ-phase-open* *fn2-succ-phase-staged*)))
       (mv :state fn2-succ-txns fn2-succ-slots))
      (code (fn2-succ-kind-keyword->code kind))
      ((unless (natp code)) (mv :kind fn2-succ-txns fn2-succ-slots))
      ((unless (< 0 (fn2-run-layout-fields sid 0))) (mv :schema fn2-succ-txns fn2-succ-slots))
      (rec (fn2-succ-txns-record tx fn2-succ-txns))
      ((unless (cond ((equal code *fn2-succ-kind-record*) (and (equal sid 1) (or (equal rec 0) (equal rec (+ 1 i)))))
                     ((equal code *fn2-succ-kind-insert*)
                      (and (not (fn2-run-layout-fold-p sid)) (member-eq (fn2-run-layout-merge sid) '(:unique :latest))))
                     (t (natp (fn2-fold-arity sid kind)))))
       (mv :kind fn2-succ-txns fn2-succ-slots))
      (s (+ (* tx *fn2-succ-slots*) i))
      (fn2-succ-slots (fn2-succ-slots-put s (phase *fn2-succ-slot-phase-put*) (sid sid) (kind code) (set 0) (events 0) (outs 0)
                                          (found 0) (vrun 0) (size 0) (oset 0) (sk 0) (ss 0) (sg 0) (late 0) (filled 0)))
      (rec (cond ((equal code *fn2-succ-kind-record*) (+ 1 i)) ((equal rec (+ 1 i)) 0) (t rec)))
      (fn2-succ-txns (fn2-succ-txns-put tx (phase *fn2-succ-phase-open*) (record rec) (ri 0)
                                        (rstate *fn2-succ-resolve-fresh*) (rbound 0))))
  (mv :ok fn2-succ-txns fn2-succ-slots)))
(fn2-idc-fn-shape fn2-succ-put (tx i sid kind fn2-succ-txns fn2-succ-slots) (fn2-succ-txns fn2-succ-slots) (fn2-succ-txns fn2-succ-slots) t
 (fn2-succ-txns-phase fn2-succ-txns-record))

;; An arg change: the slot is :put (resolve it again), the transaction :open.
(defun fn2-succ-touch (tx s set events outs late fn2-succ-txns fn2-succ-slots)
 (declare (xargs :stobjs (fn2-succ-txns fn2-succ-slots) :guard (and (fn2-succ-txns-wfp fn2-succ-txns) (fn2-succ-slots-wfp fn2-succ-slots))))
 (if (not (and (natp tx) (< tx (fn2-succ-txns-rows fn2-succ-txns)) (natp s) (< s (fn2-succ-slots-rows fn2-succ-slots))
               (unsigned-byte-p 32 set) (unsigned-byte-p 32 events) (unsigned-byte-p 32 outs) (unsigned-byte-p 32 late)))
     (mv :bounds fn2-succ-txns fn2-succ-slots)
  (let* ((fn2-succ-slots (fn2-succ-slots-put s (phase *fn2-succ-slot-phase-put*) (set set) (events events) (outs outs) (late late)))
         (fn2-succ-txns (fn2-succ-txns-put tx (phase *fn2-succ-phase-open*) (ri 0) (rstate *fn2-succ-resolve-fresh*) (rbound 0))))
   (mv :ok fn2-succ-txns fn2-succ-slots))))
(fn2-idc-fn-shape fn2-succ-touch (tx s set events outs late fn2-succ-txns fn2-succ-slots) (fn2-succ-txns fn2-succ-slots) (fn2-succ-txns fn2-succ-slots))

; The slot row of slot I of TX when it is declared and TX is :open or
; :staged: (mv code s sid code arity).
(defun fn2-succ-declared (tx i fn2-succ-txns fn2-succ-slots)
 (declare (xargs :stobjs (fn2-succ-txns fn2-succ-slots) :guard (and (fn2-succ-txns-wfp fn2-succ-txns) (fn2-succ-slots-wfp fn2-succ-slots))))
 (b* (((unless (and (natp tx) (< tx (fn2-succ-txns-rows fn2-succ-txns)) (natp i) (< i *fn2-succ-slots*)
                    (< (+ (* tx *fn2-succ-slots*) i) (fn2-succ-slots-rows fn2-succ-slots))))
       (mv :bounds 0 0 0 0))
      ((unless (member (fn2-succ-txns-phase tx fn2-succ-txns) (list *fn2-succ-phase-open* *fn2-succ-phase-staged*))) (mv :state 0 0 0 0))
      (s (+ (* tx *fn2-succ-slots*) i))
      ((when (equal (fn2-succ-slots-phase s fn2-succ-slots) *fn2-succ-slot-phase-empty*)) (mv :state 0 0 0 0))
      (sid (fn2-succ-slots-sid s fn2-succ-slots)) (code (fn2-succ-slots-kind s fn2-succ-slots)))
  (mv :ok s sid code (fn2-succ-arity sid code))))
(defthm fn2-succ-declared-types
 (and (natp (mv-nth 1 (fn2-succ-declared tx i fn2-succ-txns fn2-succ-slots)))
      (natp (mv-nth 4 (fn2-succ-declared tx i fn2-succ-txns fn2-succ-slots))))
 :rule-classes ((:type-prescription :corollary (natp (mv-nth 1 (fn2-succ-declared tx i fn2-succ-txns fn2-succ-slots))))
                (:type-prescription :corollary (natp (mv-nth 4 (fn2-succ-declared tx i fn2-succ-txns fn2-succ-slots))))))
(in-theory (disable fn2-succ-declared))

; Arg J of slot I of TX from SRC: :value (the integer VALUE), :event (the
; member's commit position, written at bind; an insert's integer field, or a
; record's article: the article identifier is the commit position), or :out (VALUE = K * 2^8 + F: integer field F of slot K < I's staged
; row, never a record's; never a fold's key arg, which resolve must read).
; An assigned arg takes no call. B0 is TX's stripe base. :ok, :bounds,
; :state, :kind.
(defun fn2-succ-arg (tx i j src value b0 fn2-succ-txns fn2-succ-slots fn2-fields)
 (declare (xargs :stobjs (fn2-succ-txns fn2-succ-slots fn2-fields) :guard t :guard-hints (("Goal" :in-theory (disable fn2-pool-reserve fn2-pool-release fn2-pool-reset fn2-pool-read fn2-pool-write
                                             fn2-pool-class-for fn2-ov-start fn2-ov-advance fn2-id-record-insert fn2-ov-insert
                                             fn2-ov-locate fn2-ov-entry fn2-run-copy-row fn2-fold-apply fn2-fold-assign
                                             fn2-run-layout-size fn2-run-lookup-step fn2-run-cursor-start
                                             fn2-fields-rows fn2-succ-slots-rows fn2-succ-txns-rows fn2-overlays-rows)))))
 (b* (((unless (and (fn2-succ-txns-wfp fn2-succ-txns) (fn2-succ-slots-wfp fn2-succ-slots) (fn2-fields-wfp fn2-fields)))
       (mv :state fn2-succ-txns fn2-succ-slots fn2-fields))
      ((mv code s sid kcode n) (fn2-succ-declared tx i fn2-succ-txns fn2-succ-slots))
      ((unless (eq code :ok)) (mv code fn2-succ-txns fn2-succ-slots fn2-fields))
      ((unless (and (natp tx) (natp i) (< i *fn2-succ-slots*) (natp s) (< s (fn2-succ-slots-rows fn2-succ-slots))
                    (natp j) (< j n) (< j *fn2-succ-fields-max*) (natp b0)
                    (<= (+ b0 *fn2-idc-stride*) (fn2-fields-rows fn2-fields)) (unsigned-byte-p 60 value)))
       (mv :bounds fn2-succ-txns fn2-succ-slots fn2-fields))
      (kw (fn2-succ-kindkw kcode))
      (insert (equal kcode *fn2-succ-kind-insert*)) (fold (not (or insert (equal kcode *fn2-succ-kind-record*))))
      ((when (or (and insert (fn2-run-layout-octets-max sid j)) (and fold (fn2-fold-assigned-p sid kw j))))
       (mv :kind fn2-succ-txns fn2-succ-slots fn2-fields))
      (k (floor value 256)) (f (mod value 256)) (ks (+ (* tx *fn2-succ-slots*) k))
      ((unless (case src
                (:value t)
                (:event (or insert (and (equal kcode *fn2-succ-kind-record*) (equal j 0))))
                (:out (and (< k i) (< ks (fn2-succ-slots-rows fn2-succ-slots))
                           (not (equal (fn2-succ-slots-phase ks fn2-succ-slots) *fn2-succ-slot-phase-empty*))
                           (not (equal (fn2-succ-slots-kind ks fn2-succ-slots) *fn2-succ-kind-record*))
                           (< f (fn2-run-layout-fields (fn2-succ-slots-sid ks fn2-succ-slots) 0))
                           (not (fn2-run-layout-octets-max (fn2-succ-slots-sid ks fn2-succ-slots) f))
                           (not (and fold (fn2-succ-key-arg-p (fn2-run-layout-keys sid) 0 sid kw j)))))
                (otherwise nil)))
       (mv :kind fn2-succ-txns fn2-succ-slots fn2-fields))
      (row (+ b0 (* *fn2-succ-block* i) *fn2-succ-raw* j))
      ((unless (< row (fn2-fields-rows fn2-fields))) (mv :bounds fn2-succ-txns fn2-succ-slots fn2-fields))
      (bit (fn2-succ-bit j))
      (set (logior (nfix (fn2-succ-slots-set s fn2-succ-slots)) bit))
      (events (logand (nfix (fn2-succ-slots-events s fn2-succ-slots)) (- #xffffffff bit)))
      (outs (logand (nfix (fn2-succ-slots-outs s fn2-succ-slots)) (- #xffffffff bit)))
      (late (logand (nfix (fn2-succ-slots-late s fn2-succ-slots)) (- #xffffffff bit)))
      (fn2-fields (fn2-fields-put row (value (if (eq src :event) 0 value)) (ref-len 0)))
      ((mv code fn2-succ-txns fn2-succ-slots)
       (fn2-succ-touch tx s set (if (eq src :event) (logior events bit) events) (if (eq src :out) (logior outs bit) outs) late
                       fn2-succ-txns fn2-succ-slots)))
  (mv code fn2-succ-txns fn2-succ-slots fn2-fields)))
(fn2-idc-fn-shape fn2-succ-arg (tx i j src value b0 fn2-succ-txns fn2-succ-slots fn2-fields) (fn2-succ-txns fn2-succ-slots fn2-fields)
 (fn2-succ-txns fn2-succ-slots fn2-fields) t
 (fn2-succ-slots-phase fn2-succ-slots-kind fn2-succ-slots-sid fn2-succ-slots-set fn2-succ-slots-events fn2-succ-slots-outs
  fn2-succ-slots-late fn2-run-layout-octets-max fn2-fold-assigned-p fn2-succ-key-arg-p fn2-run-layout-fields fn2-run-layout-keys))

; Octet arg J of insert slot I of TX: LEN octets at [OFF, OFF+LEN) of
; SLOT/GEN, readable under OKIND OSLOT OGEN until bind (which copies them
; into the arena); every octet arg of a slot under one owner (:owner).
(defun fn2-succ-arg-octets (tx i j slot gen off len okind oslot ogen b0 fn2-succ-txns fn2-succ-slots fn2-fields)
 (declare (xargs :stobjs (fn2-succ-txns fn2-succ-slots fn2-fields) :guard t :guard-hints (("Goal" :in-theory (disable fn2-pool-reserve fn2-pool-release fn2-pool-reset fn2-pool-read fn2-pool-write
                                             fn2-pool-class-for fn2-ov-start fn2-ov-advance fn2-id-record-insert fn2-ov-insert
                                             fn2-ov-locate fn2-ov-entry fn2-run-copy-row fn2-fold-apply fn2-fold-assign
                                             fn2-run-layout-size fn2-run-lookup-step fn2-run-cursor-start
                                             fn2-fields-rows fn2-succ-slots-rows fn2-succ-txns-rows fn2-overlays-rows)))))
 (b* (((unless (and (fn2-succ-txns-wfp fn2-succ-txns) (fn2-succ-slots-wfp fn2-succ-slots) (fn2-fields-wfp fn2-fields)))
       (mv :state fn2-succ-txns fn2-succ-slots fn2-fields))
      ((mv code s sid kcode n) (fn2-succ-declared tx i fn2-succ-txns fn2-succ-slots))
      ((unless (eq code :ok)) (mv code fn2-succ-txns fn2-succ-slots fn2-fields))
      ((unless (and (natp tx) (natp i) (< i *fn2-succ-slots*) (natp s) (< s (fn2-succ-slots-rows fn2-succ-slots))
                    (natp j) (< j n) (< j *fn2-succ-fields-max*) (natp b0)
                    (<= (+ b0 *fn2-idc-stride*) (fn2-fields-rows fn2-fields))
                    (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen) (unsigned-byte-p 32 off) (unsigned-byte-p 32 len)
                    (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen)))
       (mv :bounds fn2-succ-txns fn2-succ-slots fn2-fields))
      ((unless (and (equal kcode *fn2-succ-kind-insert*) (fn2-run-layout-octets-max sid j)))
       (mv :kind fn2-succ-txns fn2-succ-slots fn2-fields))
      ((unless (fn2-run-layout-value-ok sid j len)) (mv :bounds fn2-succ-txns fn2-succ-slots fn2-fields))
      ((when (and (equal (fn2-succ-slots-oset s fn2-succ-slots) 1)
                  (not (and (equal (fn2-succ-slots-sk s fn2-succ-slots) okind) (equal (fn2-succ-slots-ss s fn2-succ-slots) oslot)
                            (equal (fn2-succ-slots-sg s fn2-succ-slots) ogen)))))
       (mv :owner fn2-succ-txns fn2-succ-slots fn2-fields))
      (row (+ b0 (* *fn2-succ-block* i) *fn2-succ-raw* j))
      ((unless (< row (fn2-fields-rows fn2-fields))) (mv :bounds fn2-succ-txns fn2-succ-slots fn2-fields))
      (bit (fn2-succ-bit j))
      (set (logior (nfix (fn2-succ-slots-set s fn2-succ-slots)) bit))
      (events (logand (nfix (fn2-succ-slots-events s fn2-succ-slots)) (- #xffffffff bit)))
      (outs (logand (nfix (fn2-succ-slots-outs s fn2-succ-slots)) (- #xffffffff bit)))
      ; A digest field's row carries the codec's presence value 1 (an octet
      ; field's value is unused); a digest admits only length 32, so a length
      ; of 0 tells it apart from (:octets 32).
      (digest (not (fn2-run-layout-value-ok sid j 0)))
      (fn2-fields (fn2-fields-put row (value (if digest 1 0)) (ref-slot slot) (ref-gen gen) (ref-off off) (ref-len len)))
      (late (logand (nfix (fn2-succ-slots-late s fn2-succ-slots)) (- #xffffffff bit)))
      (fn2-succ-slots (fn2-succ-slots-put s (oset 1) (sk okind) (ss oslot) (sg ogen)))
      ((mv code fn2-succ-txns fn2-succ-slots) (fn2-succ-touch tx s set events outs late fn2-succ-txns fn2-succ-slots)))
  (mv code fn2-succ-txns fn2-succ-slots fn2-fields)))
(fn2-idc-fn-shape fn2-succ-arg-octets (tx i j slot gen off len okind oslot ogen b0 fn2-succ-txns fn2-succ-slots fn2-fields)
 (fn2-succ-txns fn2-succ-slots fn2-fields) (fn2-succ-txns fn2-succ-slots fn2-fields) t
 (fn2-succ-slots-oset fn2-succ-slots-sk fn2-succ-slots-ss fn2-succ-slots-sg fn2-succ-slots-set fn2-succ-slots-events
  fn2-succ-slots-outs fn2-succ-slots-late fn2-run-layout-octets-max fn2-run-layout-value-ok))

; Late octet arg J of insert slot I of TX (C-S3a): at most MAX octets,
; given by fn2-succ-fill-octets after stage and before bind. Stage sizes
; the entry by MAX (the raw row's length), so the room held covers any fill.
; A key field (the tip and resolve read keys at stage) and a digest field
; are :kind; MAX past the field's octet bound is :bounds.
(defun fn2-succ-arg-octets-late (tx i j max b0 fn2-succ-txns fn2-succ-slots fn2-fields)
 (declare (xargs :stobjs (fn2-succ-txns fn2-succ-slots fn2-fields) :guard t :guard-hints (("Goal" :in-theory (disable fn2-pool-reserve fn2-pool-release fn2-pool-reset fn2-pool-read fn2-pool-write
                                             fn2-pool-class-for fn2-ov-start fn2-ov-advance fn2-id-record-insert fn2-ov-insert
                                             fn2-ov-locate fn2-ov-entry fn2-run-copy-row fn2-fold-apply fn2-fold-assign
                                             fn2-run-layout-size fn2-run-lookup-step fn2-run-cursor-start
                                             fn2-fields-rows fn2-succ-slots-rows fn2-succ-txns-rows fn2-overlays-rows)))))
 (b* (((unless (and (fn2-succ-txns-wfp fn2-succ-txns) (fn2-succ-slots-wfp fn2-succ-slots) (fn2-fields-wfp fn2-fields)))
       (mv :state fn2-succ-txns fn2-succ-slots fn2-fields))
      ((mv code s sid kcode n) (fn2-succ-declared tx i fn2-succ-txns fn2-succ-slots))
      ((unless (eq code :ok)) (mv code fn2-succ-txns fn2-succ-slots fn2-fields))
      ((unless (and (natp tx) (natp i) (< i *fn2-succ-slots*) (natp s) (< s (fn2-succ-slots-rows fn2-succ-slots))
                    (natp j) (< j n) (< j *fn2-succ-fields-max*) (natp b0)
                    (<= (+ b0 *fn2-idc-stride*) (fn2-fields-rows fn2-fields)) (unsigned-byte-p 32 max)))
       (mv :bounds fn2-succ-txns fn2-succ-slots fn2-fields))
      ((unless (and (equal kcode *fn2-succ-kind-insert*) (fn2-run-layout-octets-max sid j)
                    (fn2-run-layout-value-ok sid j 0) (<= (nfix (fn2-run-layout-keys sid)) j)))
       (mv :kind fn2-succ-txns fn2-succ-slots fn2-fields))
      ((unless (fn2-run-layout-value-ok sid j max)) (mv :bounds fn2-succ-txns fn2-succ-slots fn2-fields))
      (row (+ b0 (* *fn2-succ-block* i) *fn2-succ-raw* j))
      ((unless (< row (fn2-fields-rows fn2-fields))) (mv :bounds fn2-succ-txns fn2-succ-slots fn2-fields))
      (bit (fn2-succ-bit j))
      (set (logior (nfix (fn2-succ-slots-set s fn2-succ-slots)) bit))
      (events (logand (nfix (fn2-succ-slots-events s fn2-succ-slots)) (- #xffffffff bit)))
      (outs (logand (nfix (fn2-succ-slots-outs s fn2-succ-slots)) (- #xffffffff bit)))
      (late (logior (nfix (fn2-succ-slots-late s fn2-succ-slots)) bit))
      (fn2-fields (fn2-fields-put row (value 0) (ref-slot 0) (ref-gen 0) (ref-off 0) (ref-len max)))
      ((mv code fn2-succ-txns fn2-succ-slots) (fn2-succ-touch tx s set events outs late fn2-succ-txns fn2-succ-slots)))
  (mv code fn2-succ-txns fn2-succ-slots fn2-fields)))
(fn2-idc-fn-shape fn2-succ-arg-octets-late (tx i j max b0 fn2-succ-txns fn2-succ-slots fn2-fields)
 (fn2-succ-txns fn2-succ-slots fn2-fields) (fn2-succ-txns fn2-succ-slots fn2-fields) t
 (fn2-succ-slots-set fn2-succ-slots-events fn2-succ-slots-outs fn2-succ-slots-late fn2-run-layout-octets-max
  fn2-run-layout-value-ok fn2-run-layout-keys))

; ---------------------------------------------------------------------------
; Resolve (at :prepare): for every slot that reads its key's row (a fold's,
; or a :unique insert whose key args are all :value), the key's newest row
; in the installed runs, newest run first, into the slot's +36 rows, and the
; schema's run version, which stage compares. Bounded: one run selection or
; one lookup step per call. TX's run cursor is its decision's (cursor row
; TX), so a decision in progress refuses :state.

; The key fields of slot S's row at ENTRY from its args at SRC: a fold's
; key arg for each key field, an insert's first NK args.
(defun fn2-succ-key-rows (k kf nk sid kw insert src entry fn2-fields)
 (declare (xargs :stobjs fn2-fields :measure (nfix k)
  :guard (and (fn2-fields-wfp fn2-fields) (natp k) (natp kf) (natp src) (natp entry))))
 (if (or (zp k) (not (and (natp kf) (natp nk) (< kf nk)))) fn2-fields
  (let ((a (if insert kf (fn2-fold-key-arg sid kw kf))))
   (if (not (and (natp a) (natp src) (natp entry) (< (+ src a) (fn2-fields-rows fn2-fields)) (< (+ entry kf) (fn2-fields-rows fn2-fields))))
       fn2-fields
    (let ((fn2-fields (fn2-fields-put (+ entry kf) (value (fn2-fields-value (+ src a) fn2-fields)) (ref-len 0))))
     (fn2-succ-key-rows (- k 1) (+ 1 kf) nk sid kw insert src entry fn2-fields))))))
(fn2-fields-preserves fn2-succ-key-rows (k kf nk sid kw insert src entry fn2-fields) :position nil :raw-rows t
 :hints (("Goal" :in-theory (disable fn2-fold-key-arg))))
; Whether slot S reads its key's row: a fold's (its key args are :value by
; arg's rule), or a :unique insert's whose key args are all given as values.
(defun fn2-succ-reads-key (s fn2-succ-slots)
 (declare (xargs :stobjs fn2-succ-slots :guard (and (fn2-succ-slots-wfp fn2-succ-slots) (natp s) (< s (fn2-succ-slots-rows fn2-succ-slots)))))
 (let* ((sid (fn2-succ-slots-sid s fn2-succ-slots)) (code (fn2-succ-slots-kind s fn2-succ-slots))
        (nk (nfix (fn2-run-layout-keys sid))) (mask (- (ash 1 nk) 1)))
  (cond ((equal code *fn2-succ-kind-record*) nil)
        ((equal code *fn2-succ-kind-insert*)
         (and (eq (fn2-run-layout-merge sid) :unique)
              (equal (logand (nfix (fn2-succ-slots-set s fn2-succ-slots)) mask) mask)
              (equal (logand (logior (nfix (fn2-succ-slots-events s fn2-succ-slots)) (nfix (fn2-succ-slots-outs s fn2-succ-slots))) mask) 0)))
        (t t))))
; The live run of SID with the greatest identifier below BOUND, among rows
; R.. (K of them); BEST the best so far (a row, or the row count).
(defun fn2-succ-newest-run (k r sid bound best fn2-run-installed)
 (declare (xargs :stobjs fn2-run-installed :measure (nfix k) :guard (and (fn2-run-installed-wfp fn2-run-installed) (natp k) (natp r))))
 (if (not (and (posp k) (natp r) (< r (fn2-run-installed-rows fn2-run-installed)))) best
  (let ((run (fn2-run-installed-run r fn2-run-installed)))
   (fn2-succ-newest-run (- k 1) (+ 1 r) sid bound
                        (if (and (equal (fn2-run-installed-state r fn2-run-installed) *fn2-run-installed-state-live*)
                                 (equal (fn2-run-installed-schema r fn2-run-installed) sid) (< (nfix run) (nfix bound))
                                 (or (not (and (natp best) (< best (fn2-run-installed-rows fn2-run-installed))))
                                     (< (nfix (fn2-run-installed-run best fn2-run-installed)) (nfix run))))
                            r best)
                        fn2-run-installed))))
; Slot S is resolved: FOUND, its schema's run version noted at its start.
; (An empty slot, MARK nil, is passed over unchanged.)
(defun fn2-succ-resolved (tx s found mark fn2-succ-txns fn2-succ-slots)
 (declare (xargs :stobjs (fn2-succ-txns fn2-succ-slots) :guard (and (fn2-succ-txns-wfp fn2-succ-txns) (fn2-succ-slots-wfp fn2-succ-slots))))
 (if (not (and (natp tx) (< tx (fn2-succ-txns-rows fn2-succ-txns)) (natp s) (< s (fn2-succ-slots-rows fn2-succ-slots))
               (unsigned-byte-p 32 (+ 1 (nfix (fn2-succ-txns-ri tx fn2-succ-txns))))))
     (mv :bounds fn2-succ-txns fn2-succ-slots)
  (let* ((fn2-succ-slots (if mark (fn2-succ-slots-put s (phase *fn2-succ-slot-phase-resolved*) (found (if found 1 0))) fn2-succ-slots))
         (fn2-succ-txns (fn2-succ-txns-put tx (ri (+ 1 (nfix (fn2-succ-txns-ri tx fn2-succ-txns)))) (rstate *fn2-succ-resolve-fresh*) (rbound 0))))
   (mv :more fn2-succ-txns fn2-succ-slots))))
(fn2-idc-fn-shape fn2-succ-resolved (tx s found mark fn2-succ-txns fn2-succ-slots) (fn2-succ-txns fn2-succ-slots) (fn2-succ-txns fn2-succ-slots) t
 (fn2-succ-txns-ri))

;; Slot S at RI, its run search in state :next: start the lookup in the
;; newest run below the bound, or resolve the slot absent.
(defun fn2-succ-resolve-next (tx s b0 fn2-succ-txns fn2-succ-slots fn2-run-installed fn2-run-cursors)
 (declare (xargs :stobjs (fn2-succ-txns fn2-succ-slots fn2-run-installed fn2-run-cursors)
  :guard (and (fn2-succ-txns-wfp fn2-succ-txns) (fn2-succ-slots-wfp fn2-succ-slots) (fn2-run-installed-wfp fn2-run-installed)
              (fn2-run-cursors-wfp fn2-run-cursors) (natp s) (< s (fn2-succ-slots-rows fn2-succ-slots)) (natp b0))
  :guard-hints (("Goal" :in-theory (disable fn2-run-cursor-start fn2-succ-resolved)))))
 (b* (((unless (and (natp tx) (< tx (fn2-succ-txns-rows fn2-succ-txns)) (natp s) (< s (fn2-succ-slots-rows fn2-succ-slots)) (natp b0)))
       (mv :bounds fn2-succ-txns fn2-succ-slots fn2-run-cursors))
      (sid (fn2-succ-slots-sid s fn2-succ-slots))
      (rows (fn2-run-installed-rows fn2-run-installed))
      (r (fn2-succ-newest-run rows 0 sid (fn2-succ-txns-rbound tx fn2-succ-txns) rows fn2-run-installed))
      ((unless (and (natp r) (< r rows)))
       (mv-let (code fn2-succ-txns fn2-succ-slots) (fn2-succ-resolved tx s nil t fn2-succ-txns fn2-succ-slots)
        (mv code fn2-succ-txns fn2-succ-slots fn2-run-cursors)))
      ((mv code fn2-run-cursors)
       (fn2-run-cursor-start tx sid (fn2-run-installed-top r fn2-run-installed) (fn2-run-installed-slot r fn2-run-installed)
                             (fn2-run-installed-gen r fn2-run-installed) (fn2-run-installed-unit r fn2-run-installed)
                             (fn2-run-installed-counter r fn2-run-installed) (+ b0 *fn2-idc-rb*)
                             (fn2-run-installed-okind r fn2-run-installed) (fn2-run-installed-oslot r fn2-run-installed)
                             (fn2-run-installed-ogen r fn2-run-installed) fn2-run-cursors))
      ((unless (eq code :ok)) (mv code fn2-succ-txns fn2-succ-slots fn2-run-cursors))
      (run (fn2-run-installed-run r fn2-run-installed))
      ((unless (unsigned-byte-p 60 run)) (mv :bounds fn2-succ-txns fn2-succ-slots fn2-run-cursors))
      (fn2-succ-txns (fn2-succ-txns-put tx (rstate *fn2-succ-resolve-look*) (rbound run))))
  (mv :more fn2-succ-txns fn2-succ-slots fn2-run-cursors)))
(fn2-idc-fn-shape fn2-succ-resolve-next (tx s b0 fn2-succ-txns fn2-succ-slots fn2-run-installed fn2-run-cursors)
 (fn2-succ-txns fn2-succ-slots fn2-run-cursors) (fn2-succ-txns fn2-succ-slots fn2-run-installed fn2-run-cursors) t
 (fn2-succ-newest-run fn2-run-cursor-start fn2-succ-resolved fn2-succ-slots-sid fn2-succ-txns-rbound fn2-run-installed-run
  fn2-run-installed-top fn2-run-installed-slot fn2-run-installed-gen fn2-run-installed-unit fn2-run-installed-counter
  fn2-run-installed-okind fn2-run-installed-oslot fn2-run-installed-ogen))

(defun fn2-succ-resolve-step (tx budget b0 fn2-succ-txns fn2-succ-slots fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-succ-txns fn2-succ-slots fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
  :guard (and (fn2-succ-txns-wfp fn2-succ-txns) (fn2-succ-slots-wfp fn2-succ-slots) (fn2-run-installed-wfp fn2-run-installed)
              (fn2-run-cursors-wfp fn2-run-cursors) (fn2-run-paths-wfp fn2-run-paths) (fn2-run-cache-wfp fn2-run-cache)
              (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (natp budget) (natp b0)
              (natp tx) (< tx (fn2-succ-txns-rows fn2-succ-txns)) (<= (+ b0 *fn2-idc-stride*) (fn2-fields-rows fn2-fields)))
  :guard-hints (("Goal" :in-theory (disable fn2-run-cursor-start fn2-succ-resolved fn2-succ-resolve-next fn2-run-lookup-step
                                            fn2-succ-key-rows fn2-succ-copy-rows fn2-fields-rows fn2-succ-slots-rows)))))
 (b* (((unless (and (natp tx) (< tx (fn2-succ-txns-rows fn2-succ-txns)) (natp b0)))
       (mv :bounds fn2-succ-txns fn2-succ-slots fn2-run-cursors fn2-run-paths fn2-fields))
      (ri (nfix (fn2-succ-txns-ri tx fn2-succ-txns)))
      ((unless (< ri *fn2-succ-slots*)) (mv :ok fn2-succ-txns fn2-succ-slots fn2-run-cursors fn2-run-paths fn2-fields))
      (s (+ (* tx *fn2-succ-slots*) ri))
      ((unless (< s (fn2-succ-slots-rows fn2-succ-slots))) (mv :bounds fn2-succ-txns fn2-succ-slots fn2-run-cursors fn2-run-paths fn2-fields))
      (sid (fn2-succ-slots-sid s fn2-succ-slots)) (code (fn2-succ-slots-kind s fn2-succ-slots))
      (entry (+ b0 (* *fn2-succ-block* ri)))
      ((when (equal (fn2-succ-slots-phase s fn2-succ-slots) *fn2-succ-slot-phase-empty*))
       (mv-let (c fn2-succ-txns fn2-succ-slots) (fn2-succ-resolved tx s nil nil fn2-succ-txns fn2-succ-slots)
        (mv c fn2-succ-txns fn2-succ-slots fn2-run-cursors fn2-run-paths fn2-fields)))
      (rstate (fn2-succ-txns-rstate tx fn2-succ-txns)))
  (cond
   ((equal rstate *fn2-succ-resolve-fresh*)
    (b* ((version (fn2-run-version sid (fn2-run-installed-rows fn2-run-installed) fn2-run-installed))
         ((unless (unsigned-byte-p 60 version)) (mv :bounds fn2-succ-txns fn2-succ-slots fn2-run-cursors fn2-run-paths fn2-fields))
         (fn2-succ-slots (fn2-succ-slots-set-vrun s version fn2-succ-slots))
         ((unless (fn2-succ-reads-key s fn2-succ-slots))
          (mv-let (c fn2-succ-txns fn2-succ-slots) (fn2-succ-resolved tx s nil t fn2-succ-txns fn2-succ-slots)
           (mv c fn2-succ-txns fn2-succ-slots fn2-run-cursors fn2-run-paths fn2-fields)))
         (nk (nfix (fn2-run-layout-keys sid)))
         (fn2-fields (fn2-succ-key-rows nk 0 nk sid (fn2-succ-kindkw code) (equal code *fn2-succ-kind-insert*)
                                        (+ entry *fn2-succ-raw*) entry fn2-fields))
         (fn2-succ-txns (fn2-succ-txns-put tx (rstate *fn2-succ-resolve-next*) (rbound *fn2-u60-max*))))
     (mv :more fn2-succ-txns fn2-succ-slots fn2-run-cursors fn2-run-paths fn2-fields)))
   ((equal rstate *fn2-succ-resolve-next*)
    (mv-let (c fn2-succ-txns fn2-succ-slots fn2-run-cursors)
      (fn2-succ-resolve-next tx s b0 fn2-succ-txns fn2-succ-slots fn2-run-installed fn2-run-cursors)
     (mv c fn2-succ-txns fn2-succ-slots fn2-run-cursors fn2-run-paths fn2-fields)))
   (t
    (b* (((mv c fn2-run-cursors fn2-run-paths fn2-fields)
          (fn2-run-lookup-step tx budget entry *fn2-idc-owner-kind* *fn2-idc-owner-slot* *fn2-idc-owner-gen*
                               fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool))
         ((when (eq c :absent))
          (let ((fn2-succ-txns (fn2-succ-txns-set-rstate tx *fn2-succ-resolve-next* fn2-succ-txns)))
           (mv :more fn2-succ-txns fn2-succ-slots fn2-run-cursors fn2-run-paths fn2-fields)))
         ((unless (eq c :found)) (mv c fn2-succ-txns fn2-succ-slots fn2-run-cursors fn2-run-paths fn2-fields))
         (nk (nfix (fn2-run-layout-keys sid)))
         (fn2-fields (fn2-succ-copy-rows (nfix (- (fn2-run-layout-fields sid 0) nk)) (+ b0 *fn2-idc-rb* *fn2-run-reader-entry* nk)
                                         (+ entry *fn2-succ-res*) fn2-fields))
         ((mv c fn2-succ-txns fn2-succ-slots) (fn2-succ-resolved tx s t t fn2-succ-txns fn2-succ-slots)))
     (mv c fn2-succ-txns fn2-succ-slots fn2-run-cursors fn2-run-paths fn2-fields))))))
(fn2-idc-fn-shape fn2-succ-resolve-step (tx budget b0 fn2-succ-txns fn2-succ-slots fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)
 (fn2-succ-txns fn2-succ-slots fn2-run-cursors fn2-run-paths fn2-fields)
 (fn2-succ-txns fn2-succ-slots fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool) t
 (fn2-succ-txns-ri fn2-succ-txns-rstate fn2-succ-slots-sid fn2-succ-slots-kind fn2-succ-slots-phase fn2-run-version
  fn2-succ-reads-key fn2-run-layout-keys fn2-run-layout-fields fn2-succ-kindkw fn2-succ-resolved fn2-succ-resolve-next
  fn2-run-lookup-step fn2-succ-key-rows fn2-succ-copy-rows fn2-run-cursors-rows fn2-run-paths-rows))

; One bounded step of resolve for TX (BUDGET at most 4,096): :more, :miss
; (a run page to load, as C-S1), or :ok when every slot is resolved. A
; transaction whose decision is in progress (it shares the run cursor) is
; refused :state.
(defun fn2-succ-resolve (tx budget b0 fn2-succ-txns fn2-succ-slots fn2-id-decides fn2-run-installed fn2-run-cursors fn2-run-paths
                         fn2-run-cache fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-succ-txns fn2-succ-slots fn2-id-decides fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache
                          fn2-fields fn2-pool) :guard t
  :guard-hints (("Goal" :in-theory (disable fn2-succ-resolve-step)))))
 (b* (((unless (and (fn2-succ-txns-wfp fn2-succ-txns) (fn2-succ-slots-wfp fn2-succ-slots) (fn2-id-decides-wfp fn2-id-decides)
                    (fn2-run-installed-wfp fn2-run-installed) (fn2-run-cursors-wfp fn2-run-cursors) (fn2-run-paths-wfp fn2-run-paths)
                    (fn2-run-cache-wfp fn2-run-cache) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool)))
       (mv :state fn2-succ-txns fn2-succ-slots fn2-run-cursors fn2-run-paths fn2-fields))
      ((unless (and (natp tx) (< tx (fn2-succ-txns-rows fn2-succ-txns)) (< tx (fn2-id-decides-rows fn2-id-decides))
                    (natp budget) (<= budget 4096) (natp b0) (<= (+ b0 *fn2-idc-stride*) (fn2-fields-rows fn2-fields))))
       (mv :bounds fn2-succ-txns fn2-succ-slots fn2-run-cursors fn2-run-paths fn2-fields))
      ((unless (and (member (fn2-succ-txns-phase tx fn2-succ-txns) (list *fn2-succ-phase-open* *fn2-succ-phase-staged*))
                    (member (fn2-id-decides-phase tx fn2-id-decides)
                            (list *fn2-id-decide-phase-idle* *fn2-id-decide-phase-done* *fn2-id-decide-phase-held*))))
       (mv :state fn2-succ-txns fn2-succ-slots fn2-run-cursors fn2-run-paths fn2-fields))
      (fn2-succ-txns (fn2-succ-txns-set-phase tx *fn2-succ-phase-open* fn2-succ-txns)))
  (fn2-succ-resolve-step tx budget b0 fn2-succ-txns fn2-succ-slots fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)))
(fn2-idc-fn-shape fn2-succ-resolve (tx budget b0 fn2-succ-txns fn2-succ-slots fn2-id-decides fn2-run-installed fn2-run-cursors fn2-run-paths
                                    fn2-run-cache fn2-fields fn2-pool)
 (fn2-succ-txns fn2-succ-slots fn2-run-cursors fn2-run-paths fn2-fields)
 (fn2-succ-txns fn2-succ-slots fn2-id-decides fn2-run-installed fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool) t
 (fn2-succ-txns-phase fn2-id-decides-phase))

