; Layer B declarations; the assembly owns the single core instance.
(in-package "ACL2")
(include-book "machines")
(include-book "core-children")
(include-book "profile")
(include-book "sched")
(include-book "commit-alloc")
(include-book "format-check")
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
(defcorechild fn2-core-fc fn2-fc
 :init (fn2-fc-init (fn2-b-capacity :format-slots 2 profile) fn2-fc)
 :profilep (and (unsigned-byte-p 32 (fn2-b-capacity :format-slots 2 profile))
                (<= 2 (fn2-b-capacity :format-slots 2 profile)))
 :why "Commit work survives scheduler yields.")
(defcorechild fn2-core-fc-context fn2-fc-context
 :init (fn2-fc-context-init (fn2-b-capacity :format-slots 2 profile) fn2-fc-context)
 :profilep (and (unsigned-byte-p 32 (fn2-b-capacity :format-slots 2 profile))
                (<= 2 (fn2-b-capacity :format-slots 2 profile)))
 :why "Commit work survives scheduler yields.")
(defcorechild fn2-core-b3 fn2-b3
 :init (fn2-b3-table-init (fn2-b-capacity :format-slots 2 profile) fn2-b3)
 :profilep (and (unsigned-byte-p 32 (fn2-b-capacity :format-slots 2 profile))
                (<= 2 (fn2-b-capacity :format-slots 2 profile)))
 :why "Commit work survives scheduler yields.")
(defun fn2-b-digest-minimum (profile)
 (declare (xargs :guard t))
 (+ (* *fn2-digest-stride* (nfix (fn2-b-capacity :format-slots 2 profile)))
    1 (nfix (fn2-b-capacity :extent-slots 16 profile))))
(defthm fn2-b-digest-minimum-natural
 (natp (fn2-b-digest-minimum profile)) :rule-classes :type-prescription)
(in-theory (disable fn2-b-digest-minimum))
(defcorechild fn2-core-digests fn2-digests
 :init (fn2-digests-init (fn2-b-capacity :digest-slots (fn2-b-digest-minimum profile) profile) fn2-digests)
 :profilep (and (unsigned-byte-p 32 (fn2-b-capacity :digest-slots (fn2-b-digest-minimum profile) profile))
  (<= (fn2-b-digest-minimum profile) (fn2-b-capacity :digest-slots (fn2-b-digest-minimum profile) profile)))
 :why "Hasher stripes and immutable predecessor seals survive commit yields and row reuse.")
(defcorechild fn2-core-fields fn2-fields
 :init (fn2-fields-init (fn2-b-capacity :format-field-slots 256 profile) fn2-fields)
 :profilep (and (unsigned-byte-p 32 (fn2-b-capacity :format-field-slots 256 profile))
                (<= 256 (fn2-b-capacity :format-field-slots 256 profile)))
 :why "Commit work survives scheduler yields.")
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
 ))
(local (in-theory (disable fn2-commit-rootp fn2-commit-root-wfp fn2-commit-root-rows)))
(defun fn2-commit-root-init-for (profile fn2-commit-root)
 (declare (xargs :stobjs fn2-commit-root
  :guard (and (unsigned-byte-p 32 (+ 1 (nfix (fn2-b-capacity :extent-slots 16 profile))))
              (unsigned-byte-p 1 (fn2-b-barrier-mode profile)))))
 (let ((fn2-commit-root (fn2-commit-root-init (+ 1 (nfix (fn2-b-capacity :extent-slots 16 profile))) fn2-commit-root)))
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
                               (:durable 5) (:issue 6) (:stray 255)))
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
   (cons :notify installed) (cons :draining installed) (cons :uncertain :retained))))
; Self transitions are implicit; recovery replaces the whole core, not a row.
(defconst *fn2-commit-transitions*
 '((:free :collect) (:collect :seal :uncertain) (:seal :dependencies :uncertain)
   (:dependencies :log-write :fence :uncertain) (:log-write :fence :durable :uncertain)
   (:fence :log-write :durable :uncertain) (:durable :install :uncertain)
   (:install :publish :uncertain) (:publish :notify :uncertain)
   (:notify :draining :uncertain) (:draining :free :uncertain) (:uncertain)))
(defmachine fn2-commit
 :states (:free :collect :seal :dependencies :log-write :fence :durable
          :install :publish :notify :draining :uncertain)
 :fields ((pending :u32) (stopped :bool) (pool-slot :u32) (pool-gen :u60)
          (batch-no :u60) (member-count :u32) (first-key :u60) (partner :u32)
          (cb-mode :bool) (cb-stage :u32) (cb-cursor :u32)
          (cb-issued :u32) (cb-done :u32) (cb-bytes :u60)
          (cb-failed :bool) (outcome :u8) (cb-reason :u8)
          (cb-fence-live :bool) (cb-fence-ok :bool) (cb-deps-ok :bool)
          (cb-log-ok :bool) (cb-published :bool) (cb-acks :u32)
          (cb-seal-len :u32))

 :holds ((:collect :batch-membership :storage-window) (:seal :batch-membership :storage-window)
         (:dependencies :batch-membership :storage-job :storage-window)
         (:log-write :batch-membership :storage-job :storage-window)
         (:fence :batch-membership :storage-job :storage-window :fence-slot)
         (:durable :batch-membership :storage-window) (:install :batch-membership :storage-window)
         (:publish :batch-membership :storage-window) (:notify :storage-window) (:draining :storage-window)
         (:uncertain :batch-membership :storage-job :storage-window :fence-slot))
 :budget (:bytes 4096 :steps 32 :descriptors 4)
 :capacity 2
 :initial ((generation fn2-commit-initial-generation) (ready-prev *fn2-none*) (ready-next *fn2-none*))
 ; R7 port by the A/D DSL seat: every arm is declared :language :unchecked
 ; (the bodies were written before the restricted arm language), costs are
 ; the per-run caps, and each arm's successors are *fn2-commit-transitions*
 ; with its own phase; B states the real contracts.
 :observes ((:write-result fn2-commit-observe :cost (:bytes 4096 :steps 32 :descriptors 4) :writes () :next (:free :collect :seal :dependencies :log-write :fence :durable :install :publish :notify :draining :uncertain) :uses () :language :unchecked)
            (:fence-result fn2-commit-observe :cost (:bytes 4096 :steps 32 :descriptors 4) :writes () :next (:free :collect :seal :dependencies :log-write :fence :durable :install :publish :notify :draining :uncertain) :uses () :language :unchecked))
 :continuations
 ((:free fn2-commit-idle :cost (:bytes 4096 :steps 32 :descriptors 4) :writes () :next (:free :collect) :uses () :language :unchecked)
  (:collect fn2-commit-collect :cost (:bytes 4096 :steps 32 :descriptors 4) :writes () :next (:collect :seal :uncertain) :uses () :language :unchecked)
  (:seal fn2-commit-seal :cost (:bytes 4096 :steps 32 :descriptors 4) :writes () :next (:seal :dependencies :uncertain) :uses () :language :unchecked)
  (:dependencies fn2-commit-writes :cost (:bytes 4096 :steps 32 :descriptors 4) :writes () :next (:dependencies :log-write :fence :uncertain) :uses () :language :unchecked)
  (:log-write fn2-commit-writes :cost (:bytes 4096 :steps 32 :descriptors 4) :writes () :next (:log-write :fence :durable :uncertain) :uses () :language :unchecked)
  (:fence fn2-commit-fence :cost (:bytes 4096 :steps 32 :descriptors 4) :writes () :next (:fence :log-write :durable :uncertain) :uses () :language :unchecked)
  (:durable fn2-commit-durable :cost (:bytes 4096 :steps 32 :descriptors 4) :writes () :next (:durable :install :uncertain) :uses () :language :unchecked)
  (:install fn2-commit-install :cost (:bytes 4096 :steps 32 :descriptors 4) :writes () :next (:install :publish :uncertain) :uses () :language :unchecked)
  (:publish fn2-commit-publish :cost (:bytes 4096 :steps 32 :descriptors 4) :writes () :next (:publish :notify :uncertain) :uses () :language :unchecked)
  (:notify fn2-commit-notify :cost (:bytes 4096 :steps 32 :descriptors 4) :writes () :next (:notify :draining :uncertain) :uses () :language :unchecked)
  (:draining fn2-commit-drain :cost (:bytes 4096 :steps 32 :descriptors 4) :writes () :next (:draining :free :uncertain) :uses () :language :unchecked)
  (:uncertain fn2-commit-drain :cost (:bytes 4096 :steps 32 :descriptors 4) :writes () :next (:uncertain) :uses () :language :unchecked)))
(make-event (value `(assert-event
 (equal ',(strip-cars *fn2-commit-holds*)
        ',(fn2-machine-property 'fn2-commit :states (w state))))))
(include-book "commit")

; Keep child array bodies opaque only while admitting this declaration book.
(local (in-theory (disable fn2-extents-rows
 fn2-alloc-edges-rows
 fn2-fc-rows fn2-fc-context-rows
 fn2-b3-rows fn2-fields-rows
 fn2-commit-io-rows
 fn2-commit-io-extent fn2-commit-io-epoch fn2-commit-io-counter fn2-commit-io-pool-slot fn2-commit-io-pool-gen fn2-commit-io-op-slot fn2-commit-io-op-gen fn2-commit-io-ready fn2-commit-io-lent
 fn2-commit-root-rows
 fn2-commit-root-installed fn2-commit-root-published
 fn2-commit-root-proposed fn2-commit-root-parent fn2-commit-root-extent fn2-commit-root-first-key fn2-commit-root-members fn2-commit-root-seal-ready fn2-commit-root-barrier-mode
 fn2-digests-rows
 fn2-fc-context-hash fn2-fc-context-geometry fn2-fc-context-previous-seal)))
