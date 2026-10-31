; Layer B declarations; the assembly owns the single core instance.
(in-package "ACL2")
(include-book "machines")
(include-book "core-children")
(include-book "profile")
(include-book "sched")
(include-book "commit-alloc")
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
(defcorechild fn2-core-alloc-edges fn2-alloc-edges
 :init (fn2-alloc-edges-init (fn2-b-capacity :alloc-edge-slots (+ 6 (* 2 (nfix (fn2-b-capacity :extent-slots 16 profile)))) profile) fn2-alloc-edges)
 :profilep (and
  (unsigned-byte-p 32 (fn2-b-capacity :alloc-edge-slots (+ 6 (* 2 (nfix (fn2-b-capacity :extent-slots 16 profile)))) profile))
  (<= (+ 6 (* 2 (nfix (fn2-b-capacity :extent-slots 16 profile))))
      (fn2-b-capacity :alloc-edge-slots (+ 6 (* 2 (nfix (fn2-b-capacity :extent-slots 16 profile)))) profile)))
 :why "Commit work survives scheduler yields.")
; Format checker rows (b-durability.md §11): 0-1 the commit kind's, 2
; recovery's, 3 .. 2+w D's large-upload windows, 3+w C's sealer, then
; 4+w .. 3+w+c E's control connections (fn2-ctl row S decodes FNCT into its
; slot's 128-row field stripe and hashes the BLAKE3 trailer in its b3 row,
; both at fn2-b-ctl-slot); the count is derived, so every profile has every
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
 (+ 4 (fn2-b-upload-windows profile) (fn2-b-ctl-rows profile)))
(defun fn2-b-format-slots (profile)
 (declare (xargs :guard t))
 (fn2-b-capacity :format-slots (fn2-b-format-floor profile) profile))
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
; is recovery's checker, so at least 384), then
; layer C's 1024-row transaction stripe (the private successor's write slots
; and the identity decision, C-S3, machines-c.lisp) per transaction at the
; table's end.
;; Layer C's sealer stripe (C1c) below the transactions' stripes: a format
;; constant (C asserts its *fn2-seal-field-rows* fits).
(defconst *fn2-b-seal-field-rows* 1280)
;; Layer C's read rows (C-S4, machines-c-read.lisp): one per query cursor
;; slot of a profile that serves reading, each with a stripe of
;; *fn2-b-read-stride* rows below the sealer's (layer D's cursor kind takes
;; its capacity from the same function; C asserts its *fn2-read-stride*
;; fits).
(defconst *fn2-b-read-stride* 1024)
(defun fn2-b-read-rows (profile)
 (declare (xargs :guard t))
 (if (fn2-profile-get :reading profile) (nfix (fn2-profile-x profile)) 0))
(defthm fn2-b-read-rows-natp (natp (fn2-b-read-rows profile)) :rule-classes :type-prescription)
(in-theory (disable fn2-b-read-rows))
(defun fn2-b-field-rows (profile)
 (declare (xargs :guard t))
 (+ (* 128 (nfix (fn2-b-format-slots profile))) (* 1024 (nfix (fn2-profile-t profile))) *fn2-b-seal-field-rows*
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
(defwait :batch-membership :ready fn2-batchable-ready-p :grant fn2-batchable-grant-one
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

 :holds ((:collect :batch-membership :storage-window) (:seal :batch-membership :storage-window)
         (:dependencies :batch-membership :storage-job :storage-window)
         (:log-write :batch-membership :storage-job :storage-window)
         (:fence :batch-membership :storage-job :storage-window :fence-slot)
         (:durable :batch-membership :storage-window) (:install :batch-membership :storage-window)
         (:publish :batch-membership :storage-window) (:notify :storage-window) (:draining :storage-window)
         (:uncertain :batch-membership :storage-job :storage-window :fence-slot)
         (:dropping :batch-membership :storage-window))
 :budget (:bytes 4096 :steps 32 :descriptors 4)
 :capacity 2
 :initial ((generation fn2-commit-initial-generation) (ready-prev *fn2-none*) (ready-next *fn2-none*))
 ; R7 port by the A/D DSL seat: every arm is declared :language :unchecked
 ; (the bodies were written before the restricted arm language), costs are
 ; the per-run caps, and each arm's successors are *fn2-commit-transitions*
 ; with its own phase; B states the real contracts.
 :observes ((:write-result fn2-commit-observe :cost (:bytes 4096 :steps 32 :descriptors 4) :writes () :next (:free :collect :seal :dependencies :log-write :fence :durable :install :publish :notify :draining :uncertain :dropping) :uses () :language :unchecked)
            (:fence-result fn2-commit-observe :cost (:bytes 4096 :steps 32 :descriptors 4) :writes () :next (:free :collect :seal :dependencies :log-write :fence :durable :install :publish :notify :draining :uncertain :dropping) :uses () :language :unchecked))
 :continuations
 ((:free fn2-commit-idle :cost (:bytes 4096 :steps 32 :descriptors 4) :writes () :next (:free :collect) :uses () :language :unchecked)
  (:collect fn2-commit-collect :cost (:bytes 4096 :steps 32 :descriptors 4) :writes () :next (:collect :seal :uncertain :dropping) :uses () :language :unchecked)
  (:seal fn2-commit-seal :cost (:bytes 4096 :steps 32 :descriptors 4) :writes () :next (:seal :dependencies :uncertain :dropping) :uses () :language :unchecked)
  (:dependencies fn2-commit-writes :cost (:bytes 4096 :steps 32 :descriptors 4) :writes () :next (:dependencies :log-write :fence :uncertain :dropping) :uses () :language :unchecked)
  (:log-write fn2-commit-writes :cost (:bytes 4096 :steps 32 :descriptors 4) :writes () :next (:log-write :fence :durable :uncertain) :uses () :language :unchecked)
  (:fence fn2-commit-fence :cost (:bytes 4096 :steps 32 :descriptors 4) :writes () :next (:fence :log-write :durable :uncertain) :uses () :language :unchecked)
  (:durable fn2-commit-durable :cost (:bytes 4096 :steps 32 :descriptors 4) :writes () :next (:durable :install :uncertain) :uses () :language :unchecked)
  (:install fn2-commit-install :cost (:bytes 4096 :steps 32 :descriptors 4) :writes () :next (:install :publish :uncertain) :uses () :language :unchecked)
  (:publish fn2-commit-publish :cost (:bytes 4096 :steps 32 :descriptors 4) :writes () :next (:publish :notify :uncertain) :uses () :language :unchecked)
  (:notify fn2-commit-notify :cost (:bytes 4096 :steps 32 :descriptors 4) :writes () :next (:notify :draining :uncertain) :uses () :language :unchecked)
  (:draining fn2-commit-drain :cost (:bytes 4096 :steps 32 :descriptors 4) :writes () :next (:draining :free :uncertain) :uses () :language :unchecked)
  (:uncertain fn2-commit-drain :cost (:bytes 4096 :steps 32 :descriptors 4) :writes () :next (:uncertain) :uses () :language :unchecked)
  (:dropping fn2-commit-drop :cost (:bytes 4096 :steps 32 :descriptors 4) :writes () :next (:dropping :draining) :uses () :language :unchecked)))
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
   (:verify :read :search :install) (:search :read :install) (:install :done) (:done)))
(defmachine fn2-recovery-machine
 :states (:free :read :read-result :verify :search :install :done)
 :fields ((pending :u32) (stopped :bool) (pool-slot :u32) (pool-gen :u60)
          (rc-mode :u8) (rc-pos :u32) (rc-role :u8) (rc-stage :u32) (rc-filled :u32)
          (rc-ready :bool) (rc-outcome :u8) (rc-count :u32)
          (rc-chain :u60) (rc-arena :u32) (rc-high :u32) (rc-dirty :bool) (rc-ambiguous :bool)
          (rc-class :u8) (rc-witness :u60) (rc-witness-outcome :u8) (rc-assume :u8)
          (rc-epoch :u60) (rc-found :u32))
 :holds ((:read :storage-job :storage-window) (:read-result :storage-job :storage-window)
         (:verify :storage-job :storage-window) (:search :storage-job :storage-window)
         (:install :storage-job :storage-window))
 :budget (:bytes 4096 :steps 32 :descriptors 4)
 :capacity 1
 :initial ((generation fn2-commit-initial-generation) (ready-prev *fn2-none*) (ready-next *fn2-none*))
 :observes ((:read-result fn2-recovery-observe :cost (:steps *fn2-work-empty*)
             :writes (rc-outcome rc-count rc-ready) :from (:read-result) :next (:read-result) :uses ()))
 :continuations
 ((:free fn2-recovery-idle :cost (:steps (:cost fn2-machine-idle :steps)) :writes () :next (:free)
   :uses (fn2-machine-idle))
  (:read fn2-recovery-read
   :cost (:bytes 4096 :steps *fn2-work-advance* :descriptors (:cost fn2-issue-read :descriptors))
   :writes (rc-chain rc-pos rc-found rc-filled rc-stage pending rc-ready)
   :tables (fn2-core-pool fn2-core-ops fn2-core-control)
   :next (:read :read-result :search)
   :uses (fn2-core-reset fn2-issue-read fn2-recovery-stop-bounds))
  (:read-result fn2-recovery-result :cost (:steps *fn2-work-mailbox*)
   :writes (rc-filled rc-stage rc-ready rc-pos rc-high rc-role rc-ambiguous rc-found)
   :tables (fn2-core-rec-cand fn2-core-control)
   :next (:read-result :verify :read :install)
   :uses (fn2-recovery-cand-mark fn2-recovery-stop-bounds))
  (:verify fn2-recovery-verify
   :cost (:bytes (:cost fn2-recovery-discover-unit :bytes) :steps *fn2-work-stage*)
   :writes (rc-stage rc-role rc-filled rc-pos rc-high rc-epoch rc-ready rc-chain rc-found rc-ambiguous)
   :tables (fn2-core-pool fn2-core-fields fn2-core-fc fn2-core-fc-context fn2-core-b3 fn2-core-digests
            fn2-core-rec-cand fn2-core-commit-root fn2-core-control)
   :next (:verify :read :search :install)
   :uses (fn2-recovery-discover-unit fn2-recovery-chain-unit fn2-recovery-cand-epoch fn2-recovery-cand-mark
          fn2-recovery-link fn2-recovery-stop-bounds))
  (:search fn2-recovery-search :cost (:steps *fn2-work-advance*)
   :writes (rc-ambiguous rc-stage rc-found rc-ready rc-pos rc-mode rc-role rc-filled)
   :tables (fn2-core-control)
   :next (:search :read :install)
   :uses (fn2-recovery-scan fn2-recovery-stop-bounds))
  (:install fn2-recovery-install :cost (:steps *fn2-work-transition*)
   :writes (rc-found rc-dirty rc-stage rc-class rc-witness-outcome stopped)
   :tables (fn2-core-pool fn2-core-extents fn2-core-alloc-edges fn2-core-commit-root fn2-core-control)
   :next (:install :done)
   :uses (fn2-recovery-install-scan fn2-recovery-install-classify fn2-recovery-install-adopt
          fn2-recovery-install-finish fn2-recovery-stop-bounds))
  (:done fn2-recovery-idle :cost (:steps (:cost fn2-machine-idle :steps)) :writes () :next (:done)
   :uses (fn2-machine-idle))))
(make-event (value `(assert-event
 (equal ',(strip-cars *fn2-recovery-transitions*)
        ',(fn2-machine-property 'fn2-recovery-machine :states (w state))))))

; B5-4 hooks (constrained in commit.lisp, attached by the upper layers): their
; tables are named by layer group, never by an upper layer's child names.
(defcost fn2-runs-install :bytes 4096 :tables (fn2-core-pool (:layers :c))
 :doc "C installs a durable batch's run-replacement member: decode its workspace, swap the schema's runs.")
(defcost fn2-member-replay :bytes 4096 :tables (fn2-core-pool (:layers :c :d))
 :doc "Rebuild a recovered transaction member's rows from its record stream.")
; Declared costs of recovery's outside calls. Each is a table-level operation
; of recovery-machine.lisp over the row's owner triple; none writes the row.
(defcost fn2-recovery-discover-unit :bytes 4096 :tables (fn2-core-pool fn2-core-fields fn2-core-fc
   fn2-core-fc-context fn2-core-b3 fn2-core-digests fn2-core-rec-cand)
 :doc "One discovery stage over the filled seal-frame unit (at most 4 KiB verified).")
(defcost fn2-recovery-chain-unit :bytes 4096 :tables (fn2-core-pool fn2-core-fields fn2-core-fc
   fn2-core-fc-context fn2-core-b3 fn2-core-digests)
 :doc "One chain-verification stage over the filled unit of the found position.")
(defcost fn2-recovery-cand-epoch :doc "A candidate row's writer epoch.")
(defcost fn2-recovery-cand-mark :tables (fn2-core-rec-cand) :doc "Record a position's discovery status.")
(defcost fn2-recovery-link :tables (fn2-core-digests fn2-core-commit-root fn2-core-rec-cand)
 :doc "Link a verified position into the chain, the commit directory and the root recipe.")
(defcost fn2-recovery-scan :doc "Search 32 candidate rows for the chain's unique successor.")
(defcost fn2-recovery-dirty-scan :doc "Scan 32 candidate rows for anything beyond the chain.")
(defcost fn2-recovery-witness-match :doc "Compare the presented witness seal with the chain's.")
(defcost fn2-rec-witness-outcome :doc "The witness outcome (scholar ch. 4 item 10) from the assumption bits.")
(defcost fn2-rec-classify :doc "The recovery class from the assumption bits and the evidence words.")
(defcost fn2-recovery-adopt :tables (fn2-core-extents fn2-core-alloc-edges)
 :doc "Adopt one arena position into the allocator with its recorded identity.")
(defcost fn2-commit-admit-txn :answers (:ok :exhausted :admission) :bytes 4096
 :tables (fn2-core-commit-members fn2-core-commit-settled fn2-core-commit-root fn2-core-fields fn2-core-pool)
 :doc "B-S2: admit a transaction member's workspace to a commit batch; (mv code batch event).")
(defcost fn2-commit-take :answers (:ok :pending :none) :tables (fn2-core-commit-settled)
 :doc "B-S2: the owner's settled outcome; (mv code batch event outcome).")
(defcost fn2-commit-txn-source :answers (:ok :none :bounds) :tables (fn2-core-fields fn2-core-pool)
 :doc "B-S2 S9: the article's source reference from an admitted workspace's acceptance record.")
(defcost fn2-block-read :answers (:ok :exhausted :stale :bounds) :tables (fn2-core-extents fn2-core-pool fn2-core-ops fn2-core-control)
 :descriptors 1 :doc "B-S2 S10: read a stored reference's range into the caller's lease (D6 3/n).")
(defcost fn2-block-read-done :answers (:ok :io) :doc "B-S2 S10: the read's completion.")
(defcost fn2-recovery-finish :tables (fn2-core-commit-root fn2-core-extents)
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
