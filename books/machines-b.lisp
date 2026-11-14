; Layer B declarations; the assembly owns the single core instance.
(in-package "ACL2")
(include-book "machines")
(include-book "core-children")
(include-book "profile")
(include-book "sched")
(include-book "commit-alloc")
(include-book "read-pins")
(include-book "format-check")
(include-book "recovery")
(include-book "commit-members")
(fn2-book-layer :b)
(defun fn2-b-capacity (key default profile)
 (declare (xargs :guard t))
 (if (and (alistp profile) (assoc-equal key profile)) (fn2-profile-get key profile) default))
; Keep generated child/column guard proofs from expanding the full type database.
(in-theory (disable fn2-b-capacity))
(local (in-theory (disable tau-system)))
(defun fn2-b-barrier-mode (profile)
 (declare (xargs :guard t))
 (fn2-b-capacity :commit-barrier-mode 0 profile))
(defcorechild fn2-core-extents fn2-extents
 :init (fn2-alloc-init (fn2-b-capacity :extent-slots 16 profile) fn2-extents)
 :profilep (unsigned-byte-p 32 (fn2-b-capacity :extent-slots 16 profile))
 :why "Commit work survives scheduler yields.")
(defun fn2-b-checkpoint-capacity (profile)
 (declare (xargs :guard t))
 (nfix (fn2-b-capacity :checkpoint-candidates 4 profile)))
; Dedicated regions: six commit I/O edges, two roots per extent, one pin per
; operation, then six retained physical references per active checkpoint.
(defun fn2-b-alloc-edge-floor (profile)
 (declare (xargs :guard t))
 (+ 6 (* 2 (nfix (fn2-b-capacity :extent-slots 16 profile)))
    (nfix (fn2-profile-o profile)) (* 6 (fn2-b-checkpoint-capacity profile))))
(defcorechild fn2-core-alloc-edges fn2-alloc-edges
 :init (fn2-alloc-edges-init (fn2-b-capacity :alloc-edge-slots (fn2-b-alloc-edge-floor profile) profile) fn2-alloc-edges)
 :profilep (and
  (unsigned-byte-p 32 (fn2-b-capacity :alloc-edge-slots (fn2-b-alloc-edge-floor profile) profile))
  (<= (fn2-b-alloc-edge-floor profile)
      (fn2-b-capacity :alloc-edge-slots (fn2-b-alloc-edge-floor profile) profile)))
 :harvest (fn2-b-read-pin-harvest
           ((fn2-core-extents fn2-extents) (fn2-core-alloc-edges fn2-alloc-edges)))
 :why "Disjoint commit, root, operation-pin and checkpoint-reference edges survive yields.")
; Format checker rows (b-durability.md §11): 0-1 the commit kind's, 2
; recovery's, 3 .. 2+w D's large-upload windows, 3+w C's sealer, then
; 4+w .. 3+w+c E's control connections (fn2-ctl row S decodes FNCT into its
; slot's 128-row field stripe and hashes the BLAKE3 trailer in its b3 row,
; both at fn2-b-ctl-slot), then row 4+w+c for block reads and the
; final row 5+w+c for the checkpoint writer's private checker. The block read's check
; (fn2-block-read-done-children hashes a block read through a source
; manifest there, within one call, so one row serves every cursor row;
; b-durability.md S9a); the count is derived, so every profile has every
; row (main's ruling, 2026-10-30); w's default is resources.lisp's round-2
; bound (16), c's the tiny profile's 2; D's upload capacity, C's sealer row
; and E's control capacity read these functions.
(defun fn2-b-upload-windows (profile)
 (declare (xargs :guard t))
 (nfix (fn2-b-capacity :large-upload-windows 16 profile)))
(defun fn2-b-ctl-rows (profile)
 (declare (xargs :guard t))
 (nfix (fn2-b-capacity :control-connections 2 profile)))
(defun fn2-b-ctl-slot (s profile)
 (declare (xargs :guard t))
 (+ 4 (fn2-b-upload-windows profile) (nfix s)))
(defun fn2-b-format-floor (profile)
 (declare (xargs :guard t))
 (+ 6 (fn2-b-upload-windows profile) (fn2-b-ctl-rows profile)))
(defun fn2-b-format-slots (profile)
 (declare (xargs :guard t))
 (fn2-b-capacity :format-slots (fn2-b-format-floor profile) profile))
(defun fn2-b-block-read-row (rows)
 (declare (xargs :guard t))
 (nfix (- (nfix rows) 2)))
(defun fn2-b-checkpoint-row (rows)
 (declare (xargs :guard t))
 (nfix (- (nfix rows) 1)))
(defun fn2-b-checkpoint-slot (profile)
 (declare (xargs :guard t))
 (fn2-b-checkpoint-row (fn2-b-format-slots profile)))
(defthm fn2-b-ctl-slot-below-floor
 (implies (< (nfix s) (fn2-b-ctl-rows profile)) (< (fn2-b-ctl-slot s profile) (fn2-b-format-floor profile))))
(in-theory (disable fn2-b-upload-windows fn2-b-ctl-rows fn2-b-ctl-slot fn2-b-format-floor fn2-b-format-slots))
(defcorechild fn2-core-fc fn2-fc
 :init (fn2-fc-init (fn2-b-format-slots profile) fn2-fc)
 :profilep (and (unsigned-byte-p 32 (fn2-b-format-slots profile))
                (<= (fn2-b-format-floor profile) (fn2-b-format-slots profile)))
 :why "Commit work survives scheduler yields.")
(defcorechild fn2-core-fc-context fn2-fc-context
 :init (fn2-fc-context-init (fn2-b-format-slots profile) fn2-fc-context)
 :profilep (and (unsigned-byte-p 32 (fn2-b-format-slots profile))
                (<= (fn2-b-format-floor profile) (fn2-b-format-slots profile)))
 :why "Commit work survives scheduler yields.")
(defcorechild fn2-core-b3 fn2-b3
 :init (fn2-b3-table-init (fn2-b-format-slots profile) fn2-b3)
 :profilep (and (unsigned-byte-p 32 (fn2-b-format-slots profile))
                (<= (fn2-b-format-floor profile) (fn2-b-format-slots profile)))
 :why "Commit work survives scheduler yields.")
(defun fn2-b-digest-minimum (profile)
 (declare (xargs :guard t))
 (+ (* *fn2-digest-stride* (nfix (fn2-b-format-slots profile)))
    1 (nfix (fn2-b-capacity :extent-slots 16 profile))
    (fn2-rec-digest-rows (nfix (fn2-b-capacity :extent-slots 16 profile)))))
(defthm fn2-b-digest-minimum-natural
 (natp (fn2-b-digest-minimum profile)) :rule-classes :type-prescription)
(in-theory (disable fn2-b-digest-minimum))
(defcorechild fn2-core-digests fn2-digests
 :init (fn2-digests-init (fn2-b-capacity :digest-slots (fn2-b-digest-minimum profile) profile) fn2-digests)
 :profilep (and (unsigned-byte-p 32 (fn2-b-capacity :digest-slots (fn2-b-digest-minimum profile) profile))
  (<= (fn2-b-digest-minimum profile) (fn2-b-capacity :digest-slots (fn2-b-digest-minimum profile) profile)))
 :why "Hasher stripes and immutable predecessor seals survive commit yields and row reuse.")
; Field rows: a 128-row stripe per format slot from row 0 (commit.lisp; row 2
; is recovery's checker, so at least 384), then layer C's transaction stripe
; (the private successor's write slots and the exact lookup's area, C-S3,
; machines-c.lisp) per transaction at the table's end: a format constant (C
; asserts its slots fit).
(defconst *fn2-b-txn-field-rows* 2048)
(defconst *fn2-b-read-stride-rows* 1024)
;; Layer C's sealer stripe (C1c) below the transactions' stripes: a format
;; constant (C asserts its *fn2-seal-field-rows* fits): the build's 1,280
;; rows and its merge's read region (C5: the query key and eight sources'
;; reader rows, at most one read stride).
(defconst *fn2-b-seal-field-rows* (+ 1280 *fn2-b-read-stride-rows*))
;; Layer C's read rows (C-S4, machines-c-read.lisp), each with a stripe of
;; *fn2-b-read-stride* rows below the sealer's (C asserts its
;; *fn2-read-stride* fits). Rows [0, 2X) are layer D's query cursors', two a
;; cursor slot S of a profile that serves reading: 2S its read, 2S+1 the
;; lookups beside a scan (LIST's per-group counts). Rows [2X, 2X+N) are
;; layer E's consumer requests', request row S using read row 2X+S (N the
;; profile's :cns, 0 until fn2-cns serves). D's cursor kind and E's request
;; kind take their capacities from these functions.
(defconst *fn2-b-read-stride* *fn2-b-read-stride-rows*)
(defun fn2-b-cursor-rows (profile)
 (declare (xargs :guard t))
 (if (fn2-profile-get :reading profile) (nfix (fn2-profile-x profile)) 0))
(defun fn2-b-cns-rows (profile)
 (declare (xargs :guard t))
 (nfix (fn2-profile-get :cns profile)))
;; the authority rows' (fn2-auth, authority.lisp): the last :authority read
;; rows, one per row slot (its capacity is at most this)
(defun fn2-b-auth-rows (profile)
 (declare (xargs :guard t))
 (nfix (fn2-profile-get :authority profile)))
(defun fn2-b-read-rows (profile)
 (declare (xargs :guard t))
 (+ (* 2 (fn2-b-cursor-rows profile)) (fn2-b-cns-rows profile) (fn2-b-auth-rows profile)))
(defthm fn2-b-cursor-rows-natp (natp (fn2-b-cursor-rows profile)) :rule-classes :type-prescription)
(defthm fn2-b-cns-rows-natp (natp (fn2-b-cns-rows profile)) :rule-classes :type-prescription)
(defthm fn2-b-auth-rows-natp (natp (fn2-b-auth-rows profile)) :rule-classes :type-prescription)
(defthm fn2-b-read-rows-natp (natp (fn2-b-read-rows profile)) :rule-classes :type-prescription)
(defthm fn2-b-read-rows-parts
 (and (<= (* 2 (fn2-b-cursor-rows profile)) (fn2-b-read-rows profile))
      (<= (fn2-b-cns-rows profile) (fn2-b-read-rows profile)))
 :rule-classes :linear :hints (("Goal" :in-theory (enable fn2-b-read-rows))))
(in-theory (disable fn2-b-cursor-rows fn2-b-cns-rows fn2-b-auth-rows fn2-b-read-rows))
(defun fn2-b-field-rows (profile)
 (declare (xargs :guard t))
 (+ (* 128 (nfix (fn2-b-format-slots profile))) (* *fn2-b-txn-field-rows* (nfix (fn2-profile-t profile))) *fn2-b-seal-field-rows*
    (* *fn2-b-read-stride* (fn2-b-read-rows profile))))
(in-theory (disable fn2-b-field-rows))
(defcorechild fn2-core-fields fn2-fields
 :init (fn2-fields-init (fn2-b-capacity :format-field-slots (fn2-b-field-rows profile) profile) fn2-fields)
 :profilep (and (unsigned-byte-p 32 (fn2-b-capacity :format-field-slots (fn2-b-field-rows profile) profile))
                (<= 384 (fn2-b-capacity :format-field-slots (fn2-b-field-rows profile) profile)))
 :why "Commit work survives scheduler yields.")
(defcorechild fn2-core-rec-cand fn2-rec-cand
 :init (fn2-rec-cand-init (fn2-b-capacity :extent-slots 16 profile) fn2-rec-cand)
 :profilep (unsigned-byte-p 32 (fn2-b-capacity :extent-slots 16 profile))
 :why "Recovery's per-position discovery survives its yields; one row per arena extent.")
; B5-4 (b-durability.md §11 B5-4 M1): the member table and the settled outcomes.
(defcorechild fn2-core-commit-members fn2-commit-member
 :init (fn2-commit-member-init *fn2-commit-member-count* fn2-commit-member) :profilep t
 :why "A batch's members (kind, workspace, owner, event) survive its yields.")
(defcorechild fn2-core-commit-settled fn2-commit-settled
 :init (fn2-commit-settled-init *fn2-commit-settled-count* fn2-commit-settled) :profilep t
 :why "A settled outcome waits for its owner without pinning the batch row.")
; Each resource row retains its exact issuing op generation as edge holder.
(defcolumns fn2-commit-io
 ((extent :u32) (epoch :u60) (counter :u60) (pool-slot :u32) (pool-gen :u60)
  (op-slot :u32) (op-gen :u60) (ready :bool) (lent :bool)))
(defcorechild fn2-core-commit-io fn2-commit-io
 :init (fn2-commit-io-init 6 fn2-commit-io) :profilep t
 :why "Three reserved resources per batch, including operation-owned edges.")
(defcolumns fn2-commit-root
 ((installed :u60) (published :u60) (proposed :u60)
  (parent :u60) (extent :u32) (first-key :u60) (members :u32) (seal-ready :bool) (barrier-mode :bool)
  ; Row 0 only: the first refused batch of an abort in progress (0: none)
  ; and the event it began at (b54 M3).
  (aborting :u60) (abort-event :u60)
 ))
(local (in-theory (disable fn2-commit-rootp fn2-commit-root-wfp fn2-commit-root-rows)))
(defun fn2-commit-root-init-for (profile fn2-commit-root)
 (declare (xargs :stobjs fn2-commit-root
  :guard (and (unsigned-byte-p 32 (+ 1 (nfix (fn2-b-capacity :extent-slots 16 profile))))
              (unsigned-byte-p 1 (fn2-b-barrier-mode profile)))))
 ; Row 0's first-key is the next event; events start at 1, so 0 (every
 ; member and settled row's initial event) names no event (b54 M2).
 (let* ((fn2-commit-root (fn2-commit-root-init (+ 1 (nfix (fn2-b-capacity :extent-slots 16 profile))) fn2-commit-root))
        (fn2-commit-root (fn2-commit-root-set-first-key 0 1 fn2-commit-root)))
  (fn2-commit-root-set-barrier-mode 0 (fn2-b-barrier-mode profile) fn2-commit-root)))
(defthm fn2-commit-root-init-for-type
 (implies (and (fn2-commit-rootp root)
               (unsigned-byte-p 32 (+ 1 (nfix (fn2-b-capacity :extent-slots 16 profile))))
               (unsigned-byte-p 1 (fn2-b-barrier-mode profile)))
          (fn2-commit-rootp (fn2-commit-root-init-for profile root))))
(defthm fn2-commit-root-init-for-wfp
 (implies (and (unsigned-byte-p 32 (+ 1 (nfix (fn2-b-capacity :extent-slots 16 profile))))
               (unsigned-byte-p 1 (fn2-b-barrier-mode profile)))
          (fn2-commit-root-wfp (fn2-commit-root-init-for profile root))))
(in-theory (disable fn2-commit-root-init-for))
(defcorechild fn2-core-commit-root fn2-commit-root
 :init (fn2-commit-root-init-for profile fn2-commit-root)
 :profilep (and (unsigned-byte-p 32 (+ 1 (nfix (fn2-b-capacity :extent-slots 16 profile))))
                (unsigned-byte-p 1 (fn2-b-barrier-mode profile)))
 :why "Root handles are swapped only after durability; profile mode is authoritative.")
; Names come from one code list; diagnostic values stay fixed.
(defconst *fn2-commit-reasons* '((:none 0) (:timeout 1) (:seal 3) (:predecessor 4)
                               (:durable 5) (:issue 6) (:install 7) (:stray 255)))
(defun fn2-commit-reason-events (codes)
 (declare (xargs :verify-guards nil))
 (if (atom codes) nil
  (append (fn2-columns-enum-constants 'fn2-commit-reason (list (caar codes)) (cadar codes))
          (fn2-commit-reason-events (cdr codes)))))
(make-event (value (cons 'progn (fn2-commit-reason-events *fn2-commit-reasons*))))
(defconst *fn2-commit-seal-stages*
 '(:zero-dependency :zero-records :zero-seal :zero-scratch :page-header :manifest
   :hash-init :hash-page :save-page-hash :records-header :records :hash-records
   :save-records-hash :previous-seal :seal-header :seal-body :check-seal :save-seal :hash-seal-frame))
(make-event (value (cons 'progn (fn2-columns-enum-constants
 'fn2-commit-seal-stage *fn2-commit-seal-stages* 0))))
(defun fn2-commit-initial-generation (slot base n gen)
 (declare (xargs :guard t) (ignore slot base n)) gen)
; Phase-entry holdings. IO lifecycle, drain cursor and quarantine refine these
; potentials in commit-resources; installed ownership survives batch-row reuse.
(defconst *fn2-commit-holds*
 (let* ((base '((:batch . 1) (:pool . 4) (:extent . 1) (:root . 1)))
        (prepared (append base '((:prepared . 1))))
        (installed (append base '((:installed . 1)))))
  (list (cons :free nil) (cons :collect base) (cons :seal prepared)
   (cons :dependencies prepared) (cons :log-write prepared) (cons :fence prepared)
   (cons :durable prepared) (cons :install prepared) (cons :publish installed)
   (cons :notify installed) (cons :draining installed) (cons :uncertain :retained)
   (cons :dropping prepared))))
; Self transitions are implicit; recovery replaces the whole core, not a row.
; A dropping row's only way to :uncertain is the observer's stray result (a
; completion it never issued): retained, never dropped.
(defconst *fn2-commit-transitions*
 '((:free :collect) (:collect :seal :uncertain :dropping) (:seal :dependencies :uncertain :dropping)
   (:dependencies :log-write :fence :uncertain :dropping) (:log-write :fence :durable :uncertain)
   (:fence :log-write :durable :uncertain) (:durable :install :uncertain)
   (:install :publish :uncertain) (:publish :notify :uncertain)
   (:notify :draining :uncertain) (:draining :free :uncertain) (:uncertain) (:dropping :draining :uncertain)))
;; The :batch-membership wait kind is B's (B-S2, b-durability 11b): a
;; transaction parked for room in a commit batch; B attaches the pair in -b2.
(defwait :batch-membership :ready fn2-batchable-ready-p :grant fn2-batchable-grant-one :tables (fn2-core-machines)
  :doc "A transaction parked until a commit batch has room for it.")
(defmachine fn2-commit
 :states (:free :collect :seal :dependencies :log-write :fence :durable
          :install :publish :notify :draining :uncertain :dropping)
 :fields ((pending :u32) (stopped :bool) (pool-slot :u32) (pool-gen :u60)
          (batch-no :u60) (member-count :u32) (first-key :u60) (partner :u32)
          (cb-mode :bool) (cb-stage :u32) (cb-cursor :u32)
          (cb-issued :u32) (cb-done :u32) (cb-bytes :u60)
          (cb-failed :bool) (outcome :u8) (cb-reason :u8)
          (cb-fence-live :bool) (cb-fence-ok :bool) (cb-deps-ok :bool)
          (cb-log-ok :bool) (cb-published :bool) (cb-acks :u32)
          (cb-seal-len :u32) (cb-wrote :bool) (cb-open :bool) (dep-bytes :u32) (rec-bytes :u32))

 ;; b-durability 11: the journal IO is the row's own commit-io rows (no shared
 ;; :storage-job) and the fence slot is A's, taken at adapter take and released
 ;; by physical completion, so no commit phase holds either
 :holds ((:collect :batch-membership :storage-window) (:seal :batch-membership :storage-window)
         (:dependencies :batch-membership :storage-window)
         (:log-write :batch-membership :storage-window)
         (:fence :batch-membership :storage-window)
         (:durable :batch-membership :storage-window) (:install :batch-membership :storage-window)
         (:publish :batch-membership :storage-window) (:notify :storage-window) (:draining :storage-window)
         ;; S11: an uncertain batch keeps exactly what the failing path held
         ;; (its members, windows, jobs and fence) until recovery replaces the core
         (:uncertain :retained)
         (:dropping :batch-membership :storage-window))
 :budget (:bytes 4096 :steps 32 :descriptors 4)
 :capacity 2
 :initial ((generation fn2-commit-initial-generation) (ready-prev *fn2-none*) (ready-next *fn2-none*))
 ;; The arms are in the arm language (commit-arms.lisp), their contracts
 ;; derived in the commit's last callbacks section (assembly-callbacks-r2).
 :arms ((:free) (:collect) (:seal) (:dependencies) (:log-write) (:fence) (:durable)
        (:install) (:publish) (:notify) (:draining) (:uncertain) (:dropping))
 :observes ((:write-result) (:fence-result)))
(make-event (value `(assert-event
 (equal ',(strip-cars *fn2-commit-holds*)
        ',(fn2-machine-property 'fn2-commit :states (w state))))))
(include-book "commit")
;
; B5 recovery (STORAGE-DESIGN-ASTRA parts G and I over the genesis arena): one
; row, one 4 KiB unit read and verified at a time. Discovery reads every seal
; frame position; search finds the unique successor of the chain; verify
; checks seal, records frame and dependency page; install adopts allocator
; state and the commit frontier once, only for :intact or :torn-tail. The row
; takes its whole bundle at start (resources.lisp's (:recovery :start)) and
; holds it to :done.
(defconst *fn2-recovery-transitions*
 '((:free :read) (:read :read-result :search) (:read-result :verify :read :install)
   (:verify :read :search :install :done) (:search :read :install) (:install :read :done) (:done)))
(defmachine fn2-recovery-machine
 :states (:free :read :read-result :verify :search :install :done)
 :fields ((pending :u32) (stopped :bool) (pool-slot :u32) (pool-gen :u60)
          (rc-mode :u8) (rc-pos :u32) (rc-role :u8) (rc-stage :u32) (rc-filled :u32)
          (rc-ready :bool) (rc-outcome :u8) (rc-count :u32)
          (rc-chain :u60) (rc-arena :u32) (rc-high :u32) (rc-dirty :bool) (rc-ambiguous :bool)
          (rc-class :u8) (rc-witness :u60) (rc-witness-outcome :u8) (rc-assume :u8)
          (rc-epoch :u60) (rc-found :u32)
          ;; the payload pass: the chained commit whose records are read, the
          ;; record stream's cursor and end in its records unit, and the
          ;; source manifest being followed (its position, unit, units, stored
          ;; length and owner event)
          (rc-commit :u60) (rc-roff :u32) (rc-rend :u32)
          (rc-mpos :u32) (rc-munit :u8) (rc-munits :u8) (rc-mtotal :u60) (rc-mevent :u60)
          ;; M7's replay: the member workspace (held with the window), its
          ;; length and its member's event, the members replayed of the
          ;; current commit, and whether any was
          (rc-wslot :u32) (rc-wgen :u60) (rc-wlen :u32) (rc-wevent :u60) (rc-wmembers :u32) (rc-replayed :bool))
 :holds ((:read :storage-job :storage-window) (:read-result :storage-job :storage-window)
         (:verify :storage-job :storage-window) (:search :storage-job :storage-window)
         (:install :storage-job :storage-window))
 :budget (:bytes 4096 :steps 32 :descriptors 4)
 ;; a replay hook's refusal, after the replayed prefix (M7)
 :stops (:recovery-replay)
 :capacity 1
 :initial ((generation fn2-commit-initial-generation) (ready-prev *fn2-none*) (ready-next *fn2-none*))
 ;; The arms are in the arm language (recovery-machine.lisp), their
 ;; contracts derived in the callbacks section (assembly-callbacks.lisp).
 :arms ((:free) (:read) (:read-result) (:verify) (:search) (:install) (:done))
 :observes ((:read-result)))
(make-event (value `(assert-event
 (equal ',(strip-cars *fn2-recovery-transitions*)
        ',(fn2-machine-property 'fn2-recovery-machine :states (w state))))))

; B5-4 hooks (constrained in commit.lisp, attached by the upper layers): their
; tables are named by layer group, never by an upper layer's child names.
(defcost fn2-runs-install :bytes 4096 :tables (fn2-core-pool (:layers :c))
 :doc "C installs a durable batch's run-replacement member: decode its workspace, swap the schema's runs.")
(defcost fn2-member-replay :answers t :bytes 4096 :tables (fn2-core-pool fn2-core-fields (:layers :c :d))
 :doc "Rebuild a recovered transaction member's rows from its record stream.")
; Declared costs of recovery's outside calls. Each is a table-level operation
; of recovery-machine.lisp over the row's owner triple; none writes the row.
(defcost fn2-recovery-discover-unit :answers (:again :more :empty :invalid :candidate :bounds) :bytes 4096 :tables (fn2-core-pool fn2-core-fields fn2-core-fc
   fn2-core-fc-context fn2-core-b3 fn2-core-digests fn2-core-rec-cand)
 :doc "One discovery stage over the filled seal-frame unit (at most 4 KiB verified).")
(defcost fn2-recovery-chain-unit :answers (:again :more :next-role :chained :broken :bounds) :bytes 4096 :tables (fn2-core-pool fn2-core-fields fn2-core-fc
   fn2-core-fc-context fn2-core-b3 fn2-core-digests)
 :doc "One chain-verification stage over the filled unit of the found position.")
(defcost fn2-recovery-cand-epoch :doc "A candidate row's writer epoch.")
(defcost fn2-recovery-cand-mark :answers (:ok :bounds) :tables (fn2-core-rec-cand) :doc "Record a position's discovery status.")
(defcost fn2-recovery-link :answers t :tables (fn2-core-digests fn2-core-commit-root fn2-core-rec-cand)
 :doc "Link a verified position into the chain, the commit directory and the root recipe.")
(defcost fn2-recovery-scan :answers (:ok :bounds) :doc "Search 32 candidate rows for the chain's unique successor.")
(defcost fn2-recovery-dirty-scan :doc "Scan 32 candidate rows for anything beyond the chain.")
(defcost fn2-recovery-witness-match :answers (:ok :bounds) :doc "Compare the presented witness seal with the chain's.")
(defcost fn2-rec-witness-outcome :doc "The witness outcome (scholar ch. 4 item 10) from the assumption bits.")
(defcost fn2-rec-classify :doc "The recovery class from the assumption bits and the evidence words.")
(defcost fn2-recovery-commit-extent :answers (:ok :bounds) :doc "The arena position of a chained commit.")
(defcost fn2-recovery-records-open :answers (:ok :invalid) :tables (fn2-core-pool fn2-core-fields)
 :doc "Decode a chained commit's records frame header: the record stream's start and end in its unit.")
(defcost fn2-recovery-adopt :answers t :tables (fn2-core-extents fn2-core-alloc-edges)
 :doc "Adopt one arena position into the allocator with its recorded identity.")
(defcost fn2-commit-admit-txn :answers (:ok :exhausted :admission) :bytes 4096
 :tables (fn2-core-commit-members fn2-core-commit-settled fn2-core-commit-root fn2-core-fields fn2-core-pool)
 :doc "B-S2: admit a transaction member's workspace to a commit batch; (mv code batch event).")
(defcost fn2-commit-take :child fn2-cs-take :answers (:ok :pending :none) :tables (fn2-core-commit-settled)
 :doc "B-S2: the owner's settled outcome; (mv code batch event outcome).")
(defcost fn2-commit-txn-source :answers (:ok :none :bounds) :tables (fn2-core-fields fn2-core-pool)
 :doc "B-S2 S9: the article's source reference from an admitted workspace's acceptance record.")
; B-S2 S10: read [OFF, OFF+LEN) of a stored reference (physical unit PU,
; writer epoch, allocation) into the caller's lease LSLOT LGEN, in child
; form (D6 3/n: the cursor's arms call it). The allocation handle must still
; name the unit's extent (:stale otherwise); the read is one storage job, and
; its result arrives as the caller's :read-result. (mv code slot gen ...),
; as fn2-issue-read's.
(defun fn2-pinned-block-io-children (writep pu epoch alloc off len lslot lgen okind oslot ogen principal
                                   fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control)
 (declare (xargs :stobjs (fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control)
                 :guard (and (fn2-extents-wfp fn2-extents) (fn2-alloc-edges-wfp fn2-alloc-edges)
                             (fn2-pool-wfp fn2-pool) (fn2-ops-wfp fn2-ops)
                             (fn2-control-wfp fn2-control))))
 (b* (((unless (and (booleanp writep) (natp pu) (natp off) (posp len) (<= (+ off len) *fn2-commit-unit-bytes*)
                    (unsigned-byte-p 60 epoch) (unsigned-byte-p 60 alloc)))
       (mv :bounds 0 0 fn2-pool fn2-ops fn2-control fn2-extents fn2-alloc-edges))
      (extent (floor pu *fn2-commit-write-resources*))
      (code (fn2-alloc-handle-code extent epoch alloc fn2-extents))
      ((unless (eq code :ok))
       (mv (if (eq code :bounds) :bounds :stale) 0 0 fn2-pool fn2-ops fn2-control fn2-extents fn2-alloc-edges))
      ; Published allocations are immutable. This entry constructs one full
      ; physical unit in a reserved allocation; publication uses the journal.
      ((when (and writep
                  (not (and (= off 0) (= len *fn2-commit-unit-bytes*)
                            (= (fn2-extents-state extent fn2-extents) *fn2-extent-state-reserved*)))))
       (mv :bounds 0 0 fn2-pool fn2-ops fn2-control fn2-extents fn2-alloc-edges))
      ; OP-RESERVE takes this head without interleaving. Acquire its pin before
      ; ISSUE can publish a descriptor; a normal refused issue drops the pin.
      (candidate (fn2-ops-free-head fn2-ops))
      ((unless (fn2-op-slotp candidate fn2-ops))
       (mv :exhausted 0 0 fn2-pool fn2-ops fn2-control fn2-extents fn2-alloc-edges))
      (generation (fn2-ops-gen candidate fn2-ops))
      ((mv pin fn2-extents fn2-alloc-edges)
       (fn2-alloc-edge-add (fn2-b-read-pin-edge candidate fn2-extents) generation
         extent epoch alloc :outstanding-io fn2-extents fn2-alloc-edges))
      ((unless (eq pin :ok))
       (let ((fn2-control (fn2-control-record-stop *fn2-stop-reason-issue-storage* fn2-control)))
        (mv :bounds 0 0 fn2-pool fn2-ops fn2-control fn2-extents fn2-alloc-edges)))
      ((mv code slot gen fn2-pool fn2-ops fn2-control)
       (if writep
           (fn2-issue-write-children (* pu *fn2-commit-unit-bytes*) lslot lgen 0 len 0
                                    okind oslot ogen principal fn2-pool fn2-ops fn2-control)
         (fn2-issue-read-children (+ (* pu *fn2-commit-unit-bytes*) off) lslot lgen len okind oslot ogen principal
                                  fn2-pool fn2-ops fn2-control)))
      ((when (eq code :ok))
       (if (and (equal slot candidate) (equal gen generation))
           (mv :ok slot gen fn2-pool fn2-ops fn2-control fn2-extents fn2-alloc-edges)
         (let ((fn2-control (fn2-control-record-stop *fn2-stop-reason-issue-storage* fn2-control)))
          (mv :bounds slot gen fn2-pool fn2-ops fn2-control fn2-extents fn2-alloc-edges))))
      ; An uncertain/partially issued operation keeps its protection for
      ; recovery. Only an ordinary refusal before publication rolls it back.
      ((when (= (fn2-control-stop fn2-control) 1))
       (mv :bounds slot gen fn2-pool fn2-ops fn2-control fn2-extents fn2-alloc-edges))
      ((mv drop fn2-extents fn2-alloc-edges)
       (fn2-b-read-pin-drop candidate generation fn2-extents fn2-alloc-edges))
      (fn2-control (if (eq drop :ok) fn2-control
                     (fn2-control-record-stop *fn2-stop-reason-issue-storage* fn2-control))))
  (mv (if (eq code :exhausted) :exhausted :bounds) slot gen
      fn2-pool fn2-ops fn2-control fn2-extents fn2-alloc-edges)))
(fn2-pool-preserves fn2-pinned-block-io-children (writep pu epoch alloc off len lslot lgen okind oslot ogen principal
                                             fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control)
  :carriers ((fn2-pool 3 :prefix "-POOL") (fn2-ops 4 :prefix "-OPS") (fn2-control 5 :prefix "-CONTROL")
             (fn2-extents 6 :prefix "-EXTENTS") (fn2-alloc-edges 7 :prefix "-EDGES")))
(in-theory (disable fn2-pinned-block-io-children))

(defun fn2-block-read-children (pu epoch alloc off len lslot lgen okind oslot ogen principal
                                   fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control)
 (declare (xargs :stobjs (fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control)
                 :guard (and (fn2-extents-wfp fn2-extents) (fn2-alloc-edges-wfp fn2-alloc-edges)
                             (fn2-pool-wfp fn2-pool) (fn2-ops-wfp fn2-ops)
                             (fn2-control-wfp fn2-control))))
 (fn2-pinned-block-io-children nil pu epoch alloc off len lslot lgen okind oslot ogen principal
                              fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control))
(fn2-pool-preserves fn2-block-read-children (pu epoch alloc off len lslot lgen okind oslot ogen principal
                                             fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control)
  :carriers ((fn2-pool 3 :prefix "-POOL") (fn2-ops 4 :prefix "-OPS") (fn2-control 5 :prefix "-CONTROL")
             (fn2-extents 6 :prefix "-EXTENTS") (fn2-alloc-edges 7 :prefix "-EDGES")))

(defun fn2-block-write-children (pu epoch alloc off len lslot lgen okind oslot ogen principal
                                   fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control)
 (declare (xargs :stobjs (fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control)
                 :guard (and (fn2-extents-wfp fn2-extents) (fn2-alloc-edges-wfp fn2-alloc-edges)
                             (fn2-pool-wfp fn2-pool) (fn2-ops-wfp fn2-ops)
                             (fn2-control-wfp fn2-control))))
 (fn2-pinned-block-io-children t pu epoch alloc off len lslot lgen okind oslot ogen principal
                              fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control))
(fn2-pool-preserves fn2-block-write-children (pu epoch alloc off len lslot lgen okind oslot ogen principal
                                             fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control)
  :carriers ((fn2-pool 3 :prefix "-POOL") (fn2-ops 4 :prefix "-OPS") (fn2-control 5 :prefix "-CONTROL")
             (fn2-extents 6 :prefix "-EXTENTS") (fn2-alloc-edges 7 :prefix "-EDGES")))

(defcost fn2-block-read :child fn2-block-read-children :answers (:ok :exhausted :stale :bounds)
 :tables (fn2-core-extents fn2-core-alloc-edges fn2-core-pool fn2-core-ops fn2-core-control)
 :descriptors 1 :doc "Pin a stored reference through physical completion and read it into the caller's lease.")
(defcost fn2-block-write :child fn2-block-write-children :answers (:ok :exhausted :stale :bounds)
 :tables (fn2-core-extents fn2-core-alloc-edges fn2-core-pool fn2-core-ops fn2-core-control)
 :descriptors 1 :doc "Pin a reserved physical-unit construction through physical write completion; journal/fence publication remains separate.")

(defcost fn2-commit-posture :answers (:serving :draining) :tables (fn2-core-machines)
 :doc "B-S2 S11: :draining while a commit row is :uncertain (computed from the rows' phases), else :serving.")
;; LEFT octets from OFF of the lease SLOT GEN (owner OKIND OSLOT OGEN) into
;; hasher row ROW, one fn2-b3-update (at most 4,096 octets) a step, FUEL
;; steps at most: (mv code fn2-digests fn2-b3).
(defun fn2-block-hash-span (fuel row slot gen off left okind oslot ogen fn2-digests fn2-b3 fn2-pool)
 (declare (xargs :stobjs (fn2-digests fn2-b3 fn2-pool) :measure (nfix fuel)
                 :guard (and (fn2-pool-wfp fn2-pool) (natp off) (natp left))))
 (cond ((zp left) (mv :ok fn2-digests fn2-b3))
       ((not (and (posp fuel) (fn2-b3-ready row fn2-b3 fn2-digests)
                  (unsigned-byte-p 32 off) (unsigned-byte-p 32 left)))
        (mv :bounds fn2-digests fn2-b3))
       (t (mv-let (code used fn2-digests fn2-b3)
            (fn2-b3-update row slot gen off left okind oslot ogen fn2-digests fn2-b3 fn2-pool)
            (if (and (member-eq code '(:ok :more)) (posp used) (<= used left))
                (fn2-block-hash-span (- fuel 1) row slot gen (+ off (nfix used)) (nfix (- left (nfix used)))
                                     okind oslot ogen fn2-digests fn2-b3 fn2-pool)
              (mv :bounds fn2-digests fn2-b3))))))
(local
 (defthm fn2-block-hash-span-update-shape
  (implies (and (fn2-b3-ready row fn2-b3 fn2-digests) (fn2-pool-wfp fn2-pool)
                (integerp off) (<= 0 off) (< off 4294967296) (integerp left) (<= 0 left) (< left 4294967296)
                (fn2-digestsp fn2-digests) (fn2-b3p fn2-b3) (fn2-poolp fn2-pool))
   (b* (((mv & & d b) (fn2-b3-update row slot gen off left okind oslot ogen fn2-digests fn2-b3 fn2-pool)))
    (and (fn2-digestsp d) (fn2-digests-wfp d) (equal (fn2-digests-rows d) (fn2-digests-rows fn2-digests))
         (fn2-b3p b) (fn2-b3-wfp b) (equal (fn2-b3-rows b) (fn2-b3-rows fn2-b3))
         (equal (len (nth *fn2-b3-wordsi* b)) (len (nth *fn2-b3-wordsi* fn2-b3))))))
  :hints (("Goal" :use ((:instance fn2-b3-update-shape (len left)))
                  :in-theory (disable fn2-b3-update-shape fn2-b3-ready fn2-digestsp fn2-digests-wfp fn2-digests-rows
                                      fn2-b3p fn2-b3-wfp fn2-b3-rows)))))
(defthm fn2-block-hash-span-shape
 (implies (and (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests) (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3)
               (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
  (b* (((mv & d b) (fn2-block-hash-span fuel row slot gen off left okind oslot ogen fn2-digests fn2-b3 fn2-pool)))
   (and (fn2-digestsp d) (fn2-digests-wfp d) (equal (fn2-digests-rows d) (fn2-digests-rows fn2-digests))
        (fn2-b3p b) (fn2-b3-wfp b) (equal (fn2-b3-rows b) (fn2-b3-rows fn2-b3))
        (equal (len (nth *fn2-b3-wordsi* b)) (len (nth *fn2-b3-wordsi* fn2-b3))))))
 :hints (("Goal" :induct (fn2-block-hash-span fuel row slot gen off left okind oslot ogen fn2-digests fn2-b3 fn2-pool)
                 :in-theory (disable fn2-b3-ready fn2-digestsp fn2-digests-wfp fn2-digests-rows
                                     fn2-b3p fn2-b3-wfp fn2-b3-rows fn2-b3-update-shape))))
(in-theory (disable fn2-block-hash-span))
;; The LEN octets at BOFF of the lease LSLOT LGEN hashed in hasher row ROW
;; into its result slot: (mv code fn2-b3 fn2-digests).
(defun fn2-block-hash-into (row lslot lgen boff len okind oslot ogen fn2-b3 fn2-digests fn2-pool)
 (declare (xargs :stobjs (fn2-b3 fn2-digests fn2-pool) :guard (fn2-pool-wfp fn2-pool)
                 :guard-hints (("Goal" :in-theory (enable fn2-b3-ready)))))
 (b* ((key (fn2-digest-slot (nfix row) *fn2-b3-key*))
      (got (fn2-digest-slot (nfix row) *fn2-b3-result*))
      ((unless (and (natp row) (fn2-b3-ready row fn2-b3 fn2-digests) (fn2-digest-rowp key fn2-digests)
                    (natp boff) (natp len)))
       (mv :bounds fn2-b3 fn2-digests))
      ((mv fn2-digests fn2-b3) (fn2-b3-init row 0 key fn2-digests fn2-b3))
      ((mv code fn2-digests fn2-b3)
       (fn2-block-hash-span 8 row lslot lgen boff len okind oslot ogen fn2-digests fn2-b3 fn2-pool))
      ((unless (and (eq code :ok) (fn2-b3-ready row fn2-b3 fn2-digests) (fn2-digest-rowp got fn2-digests)))
       (mv :bounds fn2-b3 fn2-digests))
      (fn2-digests (fn2-b3-finalize got row fn2-digests fn2-b3)))
  (mv :ok fn2-b3 fn2-digests)))
(defthm fn2-block-hash-into-shape
 (implies (and (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests) (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3)
               (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
  (b* (((mv & b d) (fn2-block-hash-into row lslot lgen boff len okind oslot ogen fn2-b3 fn2-digests fn2-pool)))
   (and (fn2-digestsp d) (fn2-digests-wfp d) (equal (fn2-digests-rows d) (fn2-digests-rows fn2-digests))
        (fn2-b3p b) (fn2-b3-wfp b) (equal (fn2-b3-rows b) (fn2-b3-rows fn2-b3))
        (equal (len (nth *fn2-b3-wordsi* b)) (len (nth *fn2-b3-wordsi* fn2-b3))))))
 :hints (("Goal" :in-theory (e/d (fn2-b3-ready) (fn2-digestsp fn2-digests-wfp fn2-digests-rows
                                                   fn2-b3p fn2-b3-wfp fn2-b3-rows)))))
(in-theory (disable fn2-block-hash-into))
;; Whether digest row GOT equals the 32 octets at OFF of the lease (loaded
;; into digest row SCRATCH): (mv same fn2-digests).
(defun fn2-block-digest-at (got scratch lslot lgen off okind oslot ogen fn2-digests fn2-pool)
 (declare (xargs :stobjs (fn2-digests fn2-pool) :guard (fn2-pool-wfp fn2-pool)))
 (b* (((unless (and (natp off) (fn2-digest-rowp got fn2-digests) (fn2-digest-rowp scratch fn2-digests)))
       (mv nil fn2-digests))
      ((mv code fn2-digests) (fn2-rec-fetch 0 scratch lslot lgen off okind oslot ogen fn2-pool fn2-digests)))
  (mv (and (eq code :ok) (fn2-digest-rowp got fn2-digests) (fn2-digest-rowp scratch fn2-digests)
           (fn2-digest-equal got scratch fn2-digests))
      fn2-digests)))
(defthm fn2-block-digest-at-shape
 (implies (and (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests))
  (b* (((mv & d) (fn2-block-digest-at got scratch lslot lgen off okind oslot ogen fn2-digests fn2-pool)))
   (and (fn2-digestsp d) (fn2-digests-wfp d) (equal (fn2-digests-rows d) (fn2-digests-rows fn2-digests)))))
 :hints (("Goal" :in-theory (disable fn2-digestsp fn2-digests-wfp fn2-digests-rows))))
(in-theory (disable fn2-block-digest-at))
;; Digest row CV: the chaining value of the unit at absolute pool octet AT
;; (chunk counter COUNTER) when LEN is a whole unit, else row GOT again.
(defun fn2-block-cv-into (cv got at len counter fn2-digests fn2-pool)
 (declare (xargs :stobjs (fn2-digests fn2-pool) :guard (fn2-pool-wfp fn2-pool)))
 (cond ((not (and (fn2-digest-rowp cv fn2-digests) (fn2-digest-rowp got fn2-digests))) fn2-digests)
       ((not (equal len *fn2-commit-unit-bytes*)) (fn2-digest-copy cv got fn2-digests))
       ((and (natp at) (<= (+ at *fn2-commit-unit-bytes*) (fn2-pool-data-length fn2-pool))
             (unsigned-byte-p 48 counter))
        (fn2-b3-subtree-cv-into cv at *fn2-commit-unit-bytes* counter fn2-digests fn2-pool))
       (t fn2-digests)))
(defthm fn2-block-cv-into-shape
 (implies (and (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests))
  (let ((d (fn2-block-cv-into cv got at len counter fn2-digests fn2-pool)))
   (and (fn2-digestsp d) (fn2-digests-wfp d) (equal (fn2-digests-rows d) (fn2-digests-rows fn2-digests)))))
 :hints (("Goal" :in-theory (disable fn2-digestsp fn2-digests-wfp fn2-digests-rows))))
(in-theory (disable fn2-block-cv-into))
; B-S2 S10: the read's completion. Every requested octet arrived (BYTES =
; LEN; :io otherwise). A block named through a source manifest (VERIFY 1)
; is then checked against its entry, whose two digests the caller's lease
; LSLOT LGEN holds at HOFF (the block's own BLAKE3) and CVOFF (its chaining
; value at chunk counter 4 BLOCK; a block shorter than a unit carries its
; BLAKE3 there again, article-manifest.lisp): the LEN octets at BOFF of the
; lease are hashed in the format table's penultimate row (fn2-b-block-read-row), the
; read-side check's, initialized, fed and finalized within this one call,
; so one row serves every cursor row; either digest unequal answers :hash.
; :bounds: the row or the lease range is not there (the core contradicts
; its own layout). (mv code fn2-b3 fn2-digests).
(defun fn2-block-read-done-children (bytes len verify lslot lgen boff hoff cvoff block okind oslot ogen
                                           fn2-b3 fn2-digests fn2-pool)
 (declare (xargs :stobjs (fn2-b3 fn2-digests fn2-pool) :guard (fn2-pool-wfp fn2-pool)))
 (b* (((unless (and (natp bytes) (natp len) (equal bytes len))) (mv :io fn2-b3 fn2-digests))
      ((unless (equal verify 1)) (mv :ok fn2-b3 fn2-digests))
      (row (fn2-b-block-read-row (fn2-b3-rows fn2-b3)))
      (got (fn2-digest-slot row *fn2-b3-result*))
      (want (fn2-digest-slot row *fn2-fc-hash*))
      (cv (fn2-digest-slot row *fn2-fc-geometry*))
      ((unless (and (posp len) (<= len *fn2-commit-unit-bytes*) (natp boff) (natp hoff) (natp cvoff)
                    (natp lslot) (< lslot (fn2-pool-rows fn2-pool))))
       (mv :bounds fn2-b3 fn2-digests))
      ((mv code fn2-b3 fn2-digests)
       (fn2-block-hash-into row lslot lgen boff len okind oslot ogen fn2-b3 fn2-digests fn2-pool))
      ((unless (and (eq code :ok) (fn2-digest-rowp got fn2-digests) (fn2-digest-rowp want fn2-digests)
                    (fn2-digest-rowp cv fn2-digests)))
       (mv :bounds fn2-b3 fn2-digests))
      ((mv same fn2-digests) (fn2-block-digest-at got want lslot lgen hoff okind oslot ogen fn2-digests fn2-pool))
      ((unless same) (mv :hash fn2-b3 fn2-digests))
      (fn2-digests (fn2-block-cv-into cv got (+ (nfix (fn2-pool-slot-base lslot fn2-pool)) boff) len
                                      (* 4 (nfix block)) fn2-digests fn2-pool))
      ((mv same fn2-digests) (fn2-block-digest-at cv want lslot lgen cvoff okind oslot ogen fn2-digests fn2-pool)))
  (mv (if same :ok :hash) fn2-b3 fn2-digests)))
(defthm fn2-block-read-done-children-shape
 (implies (and (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests) (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3)
               (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
  (b* (((mv & b d) (fn2-block-read-done-children bytes len verify lslot lgen boff hoff cvoff block okind oslot ogen
                                                 fn2-b3 fn2-digests fn2-pool)))
   (and (fn2-digestsp d) (fn2-digests-wfp d) (equal (fn2-digests-rows d) (fn2-digests-rows fn2-digests))
        (fn2-b3p b) (fn2-b3-wfp b) (equal (fn2-b3-rows b) (fn2-b3-rows fn2-b3))
        (equal (len (nth *fn2-b3-wordsi* b)) (len (nth *fn2-b3-wordsi* fn2-b3))))))
 :hints (("Goal" :in-theory (disable fn2-digestsp fn2-digests-wfp fn2-digests-rows
                                    fn2-b3p fn2-b3-wfp fn2-b3-rows fn2-digest-rowp))))
(in-theory (disable fn2-block-read-done-children))
(defcost fn2-block-read-done :child fn2-block-read-done-children :answers (:ok :io :hash :bounds) :bytes 8192
 :tables (fn2-core-b3 fn2-core-digests fn2-core-pool)
 :doc "B-S2 S10: the read's completion; a block named through a source manifest checked against its entry's BLAKE3 and chaining value (S9a).")
(defcost fn2-recovery-release-workspace :answers t :tables (fn2-core-pool)
 :doc "Release M7's member workspace, the recovery bundle's range beside its window.")
(defcost fn2-recovery-finish :answers t :tables (fn2-core-commit-root fn2-core-extents)
 :doc "Install the commit frontier and begin the writer epoch above every adopted identity.")

; Keep child array bodies opaque only while admitting this declaration book.
(local (in-theory (disable fn2-extents-rows
 fn2-alloc-edges-rows
 fn2-fc-rows fn2-fc-context-rows
 fn2-b3-rows fn2-fields-rows
 fn2-commit-io-rows fn2-rec-cand-rows
 fn2-commit-io-extent fn2-commit-io-epoch fn2-commit-io-counter fn2-commit-io-pool-slot fn2-commit-io-pool-gen fn2-commit-io-op-slot fn2-commit-io-op-gen fn2-commit-io-ready fn2-commit-io-lent
 fn2-commit-root-rows
 fn2-commit-root-installed fn2-commit-root-published
 fn2-commit-root-proposed fn2-commit-root-parent fn2-commit-root-extent fn2-commit-root-first-key fn2-commit-root-members fn2-commit-root-seal-ready fn2-commit-root-barrier-mode fn2-commit-root-aborting fn2-commit-root-abort-event
 fn2-digests-rows
 fn2-fc-context-hash fn2-fc-context-geometry fn2-fc-context-previous-seal)))
