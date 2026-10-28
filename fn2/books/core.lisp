; Layer-A core: bounded transitions over two children. A4 adds children here.
(in-package "ACL2")
(include-book "pool")
(include-book "vocab")
(include-book "std/util/bstar" :dir :system)

(defstobj fn2-core
  (fn2-core-pool :type fn2-pool)
  (fn2-core-ops :type fn2-ops))

(defthm fn2-core-pool-type
  (implies (fn2-corep fn2-core) (fn2-poolp (fn2-core-pool fn2-core))))
(defthm fn2-core-ops-type
  (implies (fn2-corep fn2-core) (fn2-opsp (fn2-core-ops fn2-core))))
(defthm fn2-core-update-pool-type
  (implies (and (fn2-corep fn2-core) (fn2-poolp p))
           (fn2-corep (update-fn2-core-pool p fn2-core))))
(defthm fn2-core-update-ops-type
  (implies (and (fn2-corep fn2-core) (fn2-opsp p))
           (fn2-corep (update-fn2-core-ops p fn2-core))))
(defthm fn2-core-pool-of-update-pool
  (equal (fn2-core-pool (update-fn2-core-pool p c)) p))
(defthm fn2-core-ops-of-update-pool
  (equal (fn2-core-ops (update-fn2-core-pool p c)) (fn2-core-ops c)))
(defthm fn2-core-pool-of-update-ops
  (equal (fn2-core-pool (update-fn2-core-ops p c)) (fn2-core-pool c)))
(defthm fn2-core-ops-of-update-ops
  (equal (fn2-core-ops (update-fn2-core-ops p c)) p))
(in-theory (disable fn2-corep fn2-core-pool fn2-core-ops
                    update-fn2-core-pool update-fn2-core-ops))


(defun fn2-core-wfp (fn2-core)
  (declare (xargs :stobjs fn2-core))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core))
              (fn2-ops (fn2-core-ops fn2-core)))
    (answer) (and (fn2-pool-wfp fn2-pool) (fn2-ops-wfp fn2-ops)) answer))

; The pool has at most sixteen size classes; general profile validity alone
; does not impose that representation constraint.
(defun fn2-core-profilep (profile)
  (declare (xargs :guard t))
  (and (fn2-profilep profile)
       (fn2-pool-profilep (fn2-profile-pool-classes profile))))

(in-theory (disable fn2-pool-init fn2-pool-reserve fn2-pool-release
                    fn2-pool-lease-in fn2-pool-lease-out fn2-pool-complete-in
                    fn2-pool-release-out fn2-pool-adapter-write
                    fn2-pool-write fn2-pool-reset fn2-pool-read fn2-pool-rows
                    fn2-op-cell fn2-op-range fn2-op-phase))

(defun fn2-core-init (profile fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-profilep profile)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core))
              (fn2-ops (fn2-core-ops fn2-core)))
    (fn2-pool fn2-ops)
    (let* ((fn2-pool (fn2-pool-init
                     (fn2-profile-pool-classes profile)
                     (fn2-profile-generation-start profile)
                     (fn2-profile-generation-limit profile) fn2-pool))
          (fn2-ops (fn2-ops-init profile fn2-ops)))
      (mv fn2-pool fn2-ops))
    fn2-core))
(defthm fn2-core-init-type
  (implies (and (fn2-corep fn2-core) (fn2-core-profilep profile))
           (fn2-corep (fn2-core-init profile fn2-core))))
(defthm fn2-core-init-wfp
  (implies (fn2-core-profilep profile)
           (fn2-core-wfp (fn2-core-init profile fn2-core))))
(in-theory (disable fn2-core-init fn2-core-profilep))

(defmacro fn2-core-shape-lemmas (name args position)
  (let ((call `(,name ,@args fn2-core)))
    `(progn
       (defthm ,(fn2-columns-sym name "-PRESERVES-TYPE")
         (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
                  (fn2-corep (mv-nth ,position ,call))))
       (defthm ,(fn2-columns-sym name "-PRESERVES-WFP")
         (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
                  (fn2-core-wfp (mv-nth ,position ,call))))
       (in-theory (disable ,name)))))

; DSL for bounded pool operations through the parent. Lists exist only at
; macro expansion, never in the emitted runtime paths.
(defmacro fn2-core-pool-wrapper (name target args results position)
  `(progn
     (defun ,name (,@args fn2-core)
       (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
       (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
         (,@results fn2-pool)
         (,target ,@args fn2-pool)
         (mv ,@results fn2-core)))
     (fn2-core-shape-lemmas ,name ,args ,position)))
(fn2-core-pool-wrapper fn2-core-reserve fn2-pool-reserve
  (class okind oslot ogen) (code slot gen) 3)
(fn2-core-pool-wrapper fn2-core-release fn2-pool-release
  (slot gen okind oslot ogen) (code) 1)
(fn2-core-pool-wrapper fn2-core-reset fn2-pool-reset
  (slot gen okind oslot ogen) (code) 1)
(fn2-core-pool-wrapper fn2-core-write fn2-pool-write
  (slot gen idx byte okind oslot ogen) (code) 1)
(defun fn2-core-read (slot gen idx okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (code byte) (fn2-pool-read slot gen idx okind oslot ogen fn2-pool)
    (mv code byte)))

; No row traversal: these are the scalar outbox preconditions needed by
; enqueue. A reservation takes the row and credit before a pool loan.
(defun fn2-core-outbox-ready (fn2-ops)
  (declare (xargs :stobjs fn2-ops :guard (fn2-ops-wfp fn2-ops)))
  (let ((capacity (fn2-ops-out-slot-length fn2-ops)))
    (and (< (fn2-ops-out-tail fn2-ops) capacity)
         (< (fn2-ops-out-tail fn2-ops) (fn2-ops-out-gen-length fn2-ops))
         (< capacity 4294967296))))

(defun fn2-core-lease (kind slot gen off len opslot opgen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (cond ((or (equal kind *fn2-action-receive*) (equal kind *fn2-action-read*)
             (equal kind *fn2-action-entropy*))
         (fn2-pool-lease-in slot gen len opslot opgen okind oslot ogen fn2-pool))
        ((or (equal kind *fn2-action-send*) (equal kind *fn2-action-write*))
         (mv-let (code fn2-pool)
           (fn2-pool-lease-out slot gen off len okind oslot ogen fn2-pool)
           (mv code off fn2-pool)))
        (t (mv :ok 0 fn2-pool))))
(fn2-pool-shape-lemmas fn2-core-lease
  (kind slot gen off len opslot opgen okind oslot ogen) 2)
(in-theory (disable fn2-core-lease))

; Shared issue implementation. The public wrappers supply only their own
; descriptor fields. Validate scalar widths before any mutation. The only
; post-reservation refusal is the pool lease; unreserve restores its row.
(defun fn2-core-issue (kind cap-index cap-nonce offset fua slot gen off len
                           may-release target-slot target-gen
                           okind oslot ogen principal fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core))
              (fn2-ops (fn2-core-ops fn2-core)))
    (code opslot opgen fn2-pool fn2-ops)
    (b* (((unless (and (unsigned-byte-p 32 cap-index) (unsigned-byte-p 32 cap-nonce)
                       (unsigned-byte-p 60 offset) (unsigned-byte-p 1 fua)
                       (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
                       (unsigned-byte-p 32 off) (unsigned-byte-p 32 len)
                       (unsigned-byte-p 32 target-slot) (unsigned-byte-p 60 target-gen)))
          (mv :bounds 0 0 fn2-pool fn2-ops))
         ((unless (fn2-core-outbox-ready fn2-ops))
          (mv :state 0 0 fn2-pool fn2-ops))
         ((mv code opslot opgen fn2-ops)
          (fn2-op-reserve kind okind oslot ogen principal may-release fn2-ops))
         ((unless (eq code :ok)) (mv code 0 0 fn2-pool fn2-ops))
         ((mv code actual-off fn2-pool)
          (fn2-core-lease kind slot gen off len opslot opgen okind oslot ogen fn2-pool))
         ((unless (eq code :ok))
          (mv-let (ignored fn2-ops) (fn2-op-unreserve opslot opgen fn2-ops)
            (declare (ignore ignored)) (mv code 0 0 fn2-pool fn2-ops)))
         ((mv ?ignored fn2-ops)
          (fn2-op-set-range opslot opgen slot gen actual-off len fn2-ops))
         ((mv ?ignored fn2-ops)
          (fn2-op-set-capability opslot opgen cap-index cap-nonce fn2-ops))
         ((mv ?ignored fn2-ops)
          (fn2-op-set-storage opslot opgen offset fua fn2-ops))
         ((mv ?ignored fn2-ops)
          (fn2-op-set-cancel-target opslot opgen target-slot target-gen fn2-ops))
         ((mv ?ignored fn2-ops) (fn2-op-enqueue opslot opgen fn2-ops)))
      (mv :ok opslot opgen fn2-pool fn2-ops))
    (mv code opslot opgen fn2-core)))
(fn2-core-shape-lemmas fn2-core-issue
  (kind cap-index cap-nonce offset fua slot gen off len may-release
        target-slot target-gen okind oslot ogen principal) 3)

(defmacro fn2-core-issue-wrapper (name args kind cap-index cap-nonce offset fua
                                      slot gen off len may-release target-slot target-gen)
  `(progn
     (defun ,name (,@args okind oslot ogen principal fn2-core)
       (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
       (fn2-core-issue ,kind ,cap-index ,cap-nonce ,offset ,fua ,slot ,gen ,off ,len
                       ,may-release ,target-slot ,target-gen
                       okind oslot ogen principal fn2-core))
     (fn2-core-shape-lemmas ,name (,@args okind oslot ogen principal) 3)))
(fn2-core-issue-wrapper fn2-issue-receive (cap-index cap-nonce slot gen len)
  *fn2-action-receive* cap-index cap-nonce 0 0 slot gen 0 len 0 0 0)
(fn2-core-issue-wrapper fn2-issue-send (cap-index cap-nonce slot gen off len may-release)
  *fn2-action-send* cap-index cap-nonce 0 0 slot gen off len may-release 0 0)
(fn2-core-issue-wrapper fn2-issue-read (offset slot gen len)
  *fn2-action-read* 0 0 offset 0 slot gen 0 len 0 0 0)
(fn2-core-issue-wrapper fn2-issue-write (offset slot gen off len fua)
  *fn2-action-write* 0 0 offset fua slot gen off len 0 0 0)
(fn2-core-issue-wrapper fn2-issue-fence ()
  *fn2-action-fence* 0 0 0 0 0 0 0 0 0 0 0)
(fn2-core-issue-wrapper fn2-issue-accept (cap-index cap-nonce)
  *fn2-action-accept* cap-index cap-nonce 0 0 0 0 0 0 0 0 0)
(fn2-core-issue-wrapper fn2-issue-close (cap-index cap-nonce)
  *fn2-action-close* cap-index cap-nonce 0 0 0 0 0 0 0 0 0)
(fn2-core-issue-wrapper fn2-issue-cancel (target-slot target-gen)
  *fn2-action-cancel* 0 0 0 0 0 0 0 0 0 target-slot target-gen)

(fn2-core-issue-wrapper fn2-issue-entropy (slot gen len)
  *fn2-action-entropy* 0 0 0 0 slot gen 0 len 0 0 0)

(defun fn2-harvest-one (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core))
              (fn2-ops (fn2-core-ops fn2-core)))
    (found opslot opgen cell evkind outcome reason count aux0 aux1 fn2-pool fn2-ops)
    (b* (((mv found opslot opgen cell fn2-ops) (fn2-harvest-next fn2-ops))
         ((unless found) (mv nil 0 0 0 0 0 0 0 0 0 fn2-pool fn2-ops))
         ((mv ?posted ?harvested evkind outcome reason count aux0 aux1)
          (fn2-op-cell cell opslot fn2-ops))
         ((mv slot gen ?off ?len) (fn2-op-range opslot fn2-ops))
         ((mv rp rh ?re ?ro ?rr ?rc ?ra ?rb) (fn2-op-cell 1 opslot fn2-ops))
         ((mv ?ignored fn2-pool)
          (cond ((or (equal evkind *fn2-event-receive-result*)
                     (equal evkind *fn2-event-read-result*)
                     (equal evkind *fn2-event-entropy-result*))
                 (fn2-pool-complete-in slot gen opslot opgen
                   (if (or (equal outcome *fn2-outcome-failed*)
                           (equal outcome *fn2-outcome-cancelled*)) 0 count) fn2-pool))
                ((or (equal evkind *fn2-event-borrow-released*)
                     (and (equal rh 0) (equal rp 0)
                          (or (equal evkind *fn2-event-write-result*)
                              (and (equal evkind *fn2-event-send-result*) (equal aux0 0)))))
                 (fn2-pool-release-out slot gen fn2-pool))
                (t (mv :ok fn2-pool))))
         ((mv ?ignored fn2-ops)
          (if (equal (fn2-op-phase opslot fn2-ops) *fn2-op-phase-done*)
              (fn2-op-finish opslot opgen fn2-ops) (mv :ok fn2-ops))))
      (mv found opslot opgen cell evkind outcome reason count aux0 aux1 fn2-pool fn2-ops))
    (mv found opslot opgen cell evkind outcome reason count aux0 aux1 fn2-core)))
(fn2-core-shape-lemmas fn2-harvest-one () 10)

(assert-event
 (fn2-profile-exports-compliant-p
  '(fn2-core-init fn2-core-wfp fn2-core-profilep fn2-core-reserve fn2-core-release
    fn2-core-reset fn2-core-write fn2-core-read fn2-core-issue fn2-core-lease
    fn2-issue-receive fn2-issue-send fn2-issue-read fn2-issue-write
    fn2-issue-fence fn2-issue-accept fn2-issue-close fn2-issue-cancel fn2-issue-entropy fn2-harvest-one)
  (w state)))

; Test-only evidence traversals. Free rows are canonical: their only nonzero
; fields may be generation and next-free. This is established by init/finish
; and is the exact premise required by constant-work reservation rollback.
(defun fn2-core-canonical-freep (n fn2-ops)
  (declare (xargs :stobjs fn2-ops :verify-guards nil :measure (nfix n)))
  (if (zp n) t
    (let ((slot (- n 1)))
      (and (or (not (equal (fn2-op-phase slot fn2-ops) *fn2-op-phase-free*))
               (equal (take 34 (cdr (fn2-ops-row-snapshot slot fn2-ops)))
                      '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)))
           (fn2-core-canonical-freep slot fn2-ops)))))
(defun fn2-core-refusal-hyps (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core))
              (fn2-ops (fn2-core-ops fn2-core)))
    (answer)
    (and (fn2-pool-semanticp fn2-pool) (fn2-ops-semanticp fn2-ops)
         (fn2-core-canonical-freep (fn2-ops-rows fn2-ops) fn2-ops))
    answer))
(defun fn2-core-refusal-resultp (code before after)
  (declare (ignore code))
  (equal before after))
(defmacro fn2-core-owe-refusal (name args)
  `(defthm-owed ,(fn2-columns-sym name "-REFUSAL") (,@args core)
     (mv-let (code slot gen after) (,name ,@args core)
       (declare (ignore slot gen))
       (implies (and (fn2-core-refusal-hyps core) (not (eq code :ok)))
                (fn2-core-refusal-resultp code core after)))
     :teeth "core-unit: every helper refuses malformed input unchanged; receive rollback after fresh/recycled reservation and generation-limit rollback; removed refusal premise succeeds and changes state."
     :doc "A refused issue preserves the entire logical core, including generations and free-row contents; free rows are canonical as produced by init and finish."))
(fn2-core-owe-refusal fn2-issue-receive (cap-index cap-nonce slot gen len okind oslot ogen principal))
(fn2-core-owe-refusal fn2-issue-send (cap-index cap-nonce slot gen off len may-release okind oslot ogen principal))
(fn2-core-owe-refusal fn2-issue-read (offset slot gen len okind oslot ogen principal))
(fn2-core-owe-refusal fn2-issue-write (offset slot gen off len fua okind oslot ogen principal))
(fn2-core-owe-refusal fn2-issue-fence (okind oslot ogen principal))
(fn2-core-owe-refusal fn2-issue-accept (cap-index cap-nonce okind oslot ogen principal))
(fn2-core-owe-refusal fn2-issue-close (cap-index cap-nonce okind oslot ogen principal))
(fn2-core-owe-refusal fn2-issue-cancel (target-slot target-gen okind oslot ogen principal))
(fn2-core-owe-refusal fn2-issue-entropy (slot gen len okind oslot ogen principal))

(defun fn2-core-fill-resultp (phase prefix-size off count old-prefix exposed-prefix written)
  (and (equal phase *fn2-pool-state-workspace*)
       (equal prefix-size (+ off count))
       (equal exposed-prefix (append old-prefix written))))
(defun fn2-core-fill-hyps (slot gen opslot opgen count written fn2-pool fn2-ops)
  (declare (xargs :stobjs (fn2-pool fn2-ops) :verify-guards nil))
  (and (fn2-pool-semanticp fn2-pool) (fn2-ops-semanticp fn2-ops)
       (fn2-pool-logical-slotp slot fn2-pool) (fn2-op-slotp opslot fn2-ops)
       (equal (fn2-pool-input-code slot gen opslot opgen fn2-pool) :ok)
       (< 0 (fn2-ops-post-count fn2-ops))
       (equal (fn2-ops-posted-fifoi (fn2-ops-post-head fn2-ops) fn2-ops) (* 2 opslot))
       (equal (fn2-op-gen opslot fn2-ops) opgen)
       (equal (fn2-ops-range-slot opslot fn2-ops) slot)
       (equal (fn2-ops-range-gen opslot fn2-ops) gen)
       (member-equal (fn2-ops-c0-event opslot fn2-ops)
         (list *fn2-event-receive-result* *fn2-event-read-result* *fn2-event-entropy-result*))
       (equal count (if (member-equal (fn2-ops-c0-outcome opslot fn2-ops)
                        (list *fn2-outcome-failed* *fn2-outcome-cancelled*)) 0
                      (fn2-ops-c0-count opslot fn2-ops)))
       (natp count) (<= count (fn2-pool-lease-len slot fn2-pool))
       (equal written (fn2-pool-logical-octets count
                         (+ (fn2-pool-base slot fn2-pool)
                            (fn2-pool-lease-off slot fn2-pool)) fn2-pool))
       (equal (fn2-pool-readable-code slot gen
                 (fn2-pool-owner-kind slot fn2-pool)
                 (fn2-pool-owner-slot slot fn2-pool)
                 (fn2-pool-owner-gen slot fn2-pool) fn2-pool) :state)))
 ; Evidence interpreter only: the written-byte witness is an actual sequence
; of calls to the adapter export, never a list inferred by reading memory.
; Runtime core helpers do not call this test/model traversal.
(defun fn2-core-evidence-initialize (slot gen opslot opgen idx written fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil
                  :measure (acl2-count written)))
  (if (atom written) (mv (null written) fn2-pool)
    (mv-let (code fn2-pool)
      (fn2-pool-adapter-write slot gen opslot opgen idx (car written) fn2-pool)
      (if (eq code :ok)
          (fn2-core-evidence-initialize slot gen opslot opgen (+ 1 (nfix idx))
                                        (cdr written) fn2-pool)
        (mv nil fn2-pool)))))

(defthm-owed fn2-core-harvest-byte-fill
  (slot gen opslot opgen count written loan-core ready-ops)
  (mv-let (initialized initialized-pool)
    (fn2-core-evidence-initialize slot gen opslot opgen
      (fn2-pool-lease-off slot (fn2-core-pool loan-core)) written
      (fn2-core-pool loan-core))
    (let* ((core (update-fn2-core-pool initialized-pool loan-core))
           (core (update-fn2-core-ops ready-ops core)))
      (implies
        (and initialized (equal count (len written))
             (fn2-core-fill-hyps slot gen opslot opgen count written
                                 (fn2-core-pool core) (fn2-core-ops core)))
        (let* ((before (fn2-core-pool core))
               (after (fn2-core-pool (mv-nth 10 (fn2-harvest-one core)))))
          (fn2-core-fill-resultp
            (fn2-pool-state slot after) (fn2-pool-fill slot after)
            (fn2-pool-lease-off slot before) count
            (fn2-pool-logical-octets (fn2-pool-fill slot before)
                                    (fn2-pool-base slot before) before)
            (fn2-pool-logical-octets (fn2-pool-fill slot after)
                                    (fn2-pool-base slot after) after)
            written)))))
  :teeth "core-unit: the evidence interpreter writes the two-byte loan using actual adapter-write calls; the full initialized/count/posted antecedent and exact exposed-prefix conclusion hold. Removing posted completion makes antecedent and conclusion false."
  :doc "At the composed harvest boundary, an input completion exposes exactly the initialized loan prefix. Initialization is an explicit successful trace of the real adapter-write export; ready-ops supplies the independently posted observation state. This trace premise is the environmental fidelity obligation, not an inference from bytes that happen to be in memory.")
