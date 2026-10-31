;; The transaction machine fn2-txn (layer D, quest D5; ROUND2 section B.2
;; row 4). The design is fn2/docs/d-machines-nntp.md section 14.4. An upload
;; whose header is complete takes a transaction row (A-S7's taken kind); the
;; transaction claims the exact octets of the Message-ID (claims.lisp, D0's
;; :identity-reservation) so same-Message-ID offers on one node serialize,
;; asks C's identity decision (C-S1) once the upload has its digest, writes
;; its records into its batch's private successor (C-S3: :prepare declares
;; the slots, :ready stages, admits and binds in one transition), and posts
;; the one outcome word to its connection, releasing the claim (handing it to
;; the FIFO's head), the successor, the upload and the row.
;; D5 1/n: the batch admission is B-S2's interim (fn2-commit-admit-txn
;; answers :not-served until B lands the transaction member), so every valid
;; article is refused :not-stored after :ready, and no fact is ever bound.
;; Registration book: assembly-index includes it after upload; its operations
;; and continuations are materialized by assembly-callbacks-d-txn.lisp.
(in-package "ACL2")
(include-book "upload")
(include-book "claims")
(include-book "machines-c-bind")
(include-book "machine-arms") ; defmachine-registry (MACHINE-FORM 6.5 P4)
(fn2-book-layer :d)

;; The claim walk's chain steps per run: each step compares at most one
;; Message-ID (250 octets) on an equal hash and length, so 16 steps stay
;; within the 4 KiB comparison bound of ROUND2 B.3.
(defconst *fn2-txn-claim-steps* 16)
;; Body lines counted per :prepare run (one pool read each).
(defconst *fn2-txn-count-bytes* 2048)
;; The schemas a POST writes (identity.lisp, ordered.lisp) and its write
;; slots (C-S3, W = 16): the identity fact, the article row, the operation
;; outcome, then one group-count accept per carried group. A cross-post to
;; more carried groups than *fn2-txn-groups-max* is refused :unaffordable
;; (the overview row and the addr entries of D5 2/n take the other slots).
(defconst *fn2-txn-identity-sid* 1)
(defconst *fn2-txn-article-sid* 2)
(defconst *fn2-txn-counts-sid* 5)
(defconst *fn2-txn-outcome-sid* 9)
(defconst *fn2-txn-slot-record* 0)
(defconst *fn2-txn-slot-article* 1)
(defconst *fn2-txn-slot-outcome* 2)
(defconst *fn2-txn-slot-accepts* 3)
(defconst *fn2-txn-groups-max* 6)
(assert-event (<= (+ *fn2-txn-slot-accepts* (* 2 *fn2-txn-groups-max*)) *fn2-succ-slots*))
;; The article row's values: a born article is live, version 1; the
;; operation outcome recorded with it is accepted (it is bound only into the
;; batch that accepts it).
(defconst *fn2-txn-article-live* 0)
(defconst *fn2-txn-article-version* 1)
(defconst *fn2-txn-outcome-accepted* 1)
;; Newsgroups is scanned at most this many octets per :prepare run.
(defconst *fn2-txn-scan-bytes* 1024)

;; The claim table (a D core child, one row per transaction slot).
(fn2-claims-preserves fn2-claims-init-buckets (left fn2-claims)
  :hyps ((fn2-claimsp fn2-claims) (fn2-claims-wfp fn2-claims) (<= (nfix left) (fn2-claims-rows fn2-claims))))
;; the core's init-wfp theorem has no recognizer hypothesis: wfp from wfp alone
(defthm fn2-claims-init-buckets-rows-equal
  (equal (fn2-claims-rows (fn2-claims-init-buckets left fn2-claims)) (fn2-claims-rows fn2-claims))
  :hints (("Goal" :in-theory (enable fn2-claims-init-buckets))))
(defthm fn2-claims-init-buckets-wfp-alone
  (implies (and (fn2-claims-wfp fn2-claims) (<= (nfix left) (fn2-claims-rows fn2-claims)))
           (fn2-claims-wfp (fn2-claims-init-buckets left fn2-claims)))
  :hints (("Goal" :in-theory (e/d (fn2-claims-init-buckets) (fn2-claimsp)))))
(defun fn2-txn-claims-profilep (profile)
  (declare (xargs :guard t))
  (unsigned-byte-p 32 (fn2-profile-t profile)))
(defun fn2-claims-init-for (profile fn2-claims)
  (declare (xargs :stobjs fn2-claims :guard (fn2-txn-claims-profilep profile)))
  (fn2-claims-table-init (fn2-profile-t profile) fn2-claims))
(defthm fn2-claims-init-for-type
  (implies (and (fn2-claimsp fn2-claims) (fn2-txn-claims-profilep profile))
           (fn2-claimsp (fn2-claims-init-for profile fn2-claims))))
(defthm fn2-claims-init-for-wfp
  (implies (fn2-txn-claims-profilep profile) (fn2-claims-wfp (fn2-claims-init-for profile fn2-claims)))
  :hints (("Goal" :in-theory (enable fn2-claims-init-for fn2-txn-claims-profilep))))
(in-theory (disable fn2-claims-init-for fn2-txn-claims-profilep))
(defcorechild fn2-core-claims fn2-claims
 :init (fn2-claims-init-for profile fn2-claims) :profilep (fn2-txn-claims-profilep profile)
 :why "The identity reservation: a transaction's claim on its Message-ID's exact octets and the FIFO of its waiters survive the transaction's yields (section 14.4.2).")

;; One row per transaction slot, and none unless the profile serves article
;; input (the upload's rule): a transaction exists only for an upload.
(defun fn2-txn-capacity (profile)
  (declare (xargs :guard t))
  (if (fn2-profile-get :posting-interim profile) (nfix (fn2-profile-t profile)) 0))
(defthm fn2-txn-capacity-natp (natp (fn2-txn-capacity profile)) :rule-classes :type-prescription)
(in-theory (disable fn2-txn-capacity))

;; The :ready transition's byte bound: C-S3's stage and bind and B's
;; admission happen in one run (nothing may stage or bind between a
;; transaction's stage and its bind), so the run's bound is their sum, above
;; ROUND2 B.3's 4 KiB (a departure recorded in the layer doc, 14.4).
(defconst *fn2-txn-admit-bytes* 4096)
(defconst *fn2-txn-ready-bytes* (+ 4096 8192 *fn2-txn-admit-bytes*))
(assert-event (equal *fn2-txn-ready-bytes* 16384))  ; the kind's :budget below

;; (The :prepare arm is fn2-txn-slots: the kind's table owns fn2-txn-prepare.)
(defmachine fn2-txn
 :states (:free :admit :reserve :lookup :prepare :ready :batched :accepted :refused :uncertain :releasing :draining :retired)
 :fields ((upload :link) (upload-gen :u60) (conn :link) (conn-gen :u60) (request :u32)
          (rule (:enum fn2-txn-rule (:post :ihave :takethis)))
          (word :u8) (offered :bool) (prepared :bool) (counted :u60) (lines :u32)
          (gcur :u32) (gskip :bool) (ngroups :u8)
          (stopped :bool) (next-free :link))
 :holds ((:admit :transaction-row) (:reserve :transaction-row)
         (:lookup :transaction-row :identity-reservation) (:prepare :transaction-row :identity-reservation)
         (:ready :transaction-row :identity-reservation)
         (:batched :transaction-row :identity-reservation :batch-membership)
         (:accepted :transaction-row :identity-reservation) (:refused :transaction-row :identity-reservation)
         (:uncertain :transaction-row :identity-reservation) (:releasing :transaction-row :identity-reservation)
         (:draining :transaction-row))
 :budget (:bytes 16384 :steps 32 :descriptors 4)
 :capacity (fn2-txn-capacity profile)
 ;; An upload takes the row at its :identity (section 14.3).
 :taken (:phase :admit :rows :transaction-row :ranges ()
         :copy (upload upload-gen conn conn-gen request rule principal-slot)
         :clear (word offered prepared counted lines gcur gskip ngroups stopped))
 :initial ((generation fn2-machine-initial-generation) (ready-prev *fn2-none*) (ready-next *fn2-none*)
           (upload *fn2-none*) (conn *fn2-none*) (account-ref *fn2-none*) (next-free fn2-machine-initial-next-free))
 :continuations
 ((:free fn2-txn-idle :cost (:steps (:cost fn2-machine-idle :steps)) :writes () :next (:free)
   :uses (fn2-machine-idle))
  (:admit fn2-txn-admit :cost (:bytes (:cost fn2-txn-begin :bytes) :steps *fn2-work-transition*)
   :writes (word upload) :tables (fn2-core-claims fn2-core-machines fn2-conn-table fn2-core-pool)
   :next (:admit :reserve :draining) :uses (fn2-txn-begin fn2-machine-refuse-phase))
  (:reserve fn2-txn-reserve :cost (:bytes (:cost fn2-txn-claim-walk :bytes) :steps *fn2-work-transition*)
   :writes () :tables (fn2-core-claims)
   :next (:reserve :lookup) :uses (fn2-txn-claim-walk fn2-machine-refuse-phase))
  (:lookup fn2-txn-lookup :cost (:bytes (:cost fn2-txn-decide :bytes) :steps *fn2-work-transition*)
   :writes (word offered)
   :tables (fn2-core-id-decides fn2-core-id-stamps fn2-core-overlays fn2-core-overlay-index fn2-core-run-installed
            fn2-core-run-cursors fn2-core-run-paths fn2-core-run-cache fn2-core-fields fn2-core-pool fn2-core-fc)
   :next (:lookup :prepare :refused) :uses (fn2-txn-decide fn2-machine-refuse-phase))
  (:prepare fn2-txn-slots :cost (:bytes (:cost fn2-txn-declare :bytes) :steps *fn2-work-transition*)
   :writes (word counted lines prepared gcur gskip ngroups)
   :tables (fn2-core-succ-txns fn2-core-succ-slots fn2-core-run-cursors fn2-core-run-paths fn2-core-fields fn2-core-pool)
   :next (:prepare :ready :refused) :uses (fn2-txn-declare fn2-machine-refuse-phase))
  (:ready fn2-txn-ready :cost (:bytes (:cost fn2-txn-commit :bytes) :steps *fn2-work-transition*)
   :writes (word offered)
   :tables (fn2-core-succ-txns fn2-core-succ-slots fn2-core-id-decides fn2-core-id-engine fn2-core-overlays
            fn2-core-overlay-index fn2-core-fields fn2-core-pool)
   :next (:ready :lookup :batched :refused) :uses (fn2-txn-commit fn2-machine-refuse-phase))
  (:batched fn2-txn-unreached :cost (:steps (:cost fn2-machine-refuse-phase :steps)) :writes ()
   :next (:batched) :uses (fn2-machine-refuse-phase))
  (:accepted fn2-txn-reply :cost (:steps (:cost fn2-txn-finish :steps)) :writes ()
   :tables (fn2-conn-table fn2-core-machines fn2-core-succ-txns fn2-core-succ-slots fn2-core-id-decides)
   :next (:releasing) :uses (fn2-txn-finish fn2-machine-refuse-phase))
  (:refused fn2-txn-reply :cost (:steps (:cost fn2-txn-finish :steps)) :writes ()
   :tables (fn2-conn-table fn2-core-machines fn2-core-succ-txns fn2-core-succ-slots fn2-core-id-decides)
   :next (:releasing) :uses (fn2-txn-finish fn2-machine-refuse-phase))
  (:uncertain fn2-txn-unreached :cost (:steps (:cost fn2-machine-refuse-phase :steps)) :writes ()
   :next (:uncertain) :uses (fn2-machine-refuse-phase))
  ;; one wake per run (the run's wake slot): the word woke the connection,
  ;; the claim's hand-over wakes its waiter here, the drain wakes the upload
  (:releasing fn2-txn-unclaim :cost (:steps (:cost fn2-txn-unclaim-run :steps)) :writes ()
   :tables (fn2-core-claims fn2-core-machines)
   :next (:draining) :uses (fn2-txn-unclaim-run fn2-machine-refuse-phase))
  (:draining fn2-txn-drain :cost (:steps (:cost fn2-txn-release :steps))
   :writes (generation upload upload-gen conn conn-gen next-free wait-reason)
   :tables (fn2-core-machines)
   :next (:free :retired) :uses (fn2-txn-release))
  (:retired fn2-txn-idle :cost (:steps (:cost fn2-machine-idle :steps)) :writes () :next (:retired)
   :uses (fn2-machine-idle))))

;; B-S2 is B's (commit.lisp, defcost in machines-b). Until P.4 writes the
;; member records into a workspace, :ready passes the upload's window, which
;; does not decode as member records: admission answers :admission and the
;; transaction is refused :not-stored (owed row fn2-txn-admission-interim).
;; The transaction's operations (each a wrapper or a staged helper below).
(defcost fn2-txn-hash :bytes 256 :doc "FNV-1a over the Message-ID's octets (at most 250), under the upload's owner.")
(defcost fn2-claim-begin-core :tables (fn2-core-claims) :doc "Start a claim on a Message-ID's exact octets.")
(defcost fn2-claim-walk-core :bytes 4096 :tables (fn2-core-claims)
  :effects ((:acquire (:identity-reservation)))
  :doc "Walk the claim's bucket at most 16 chain steps (one Message-ID compared per step on an equal hash): claimed, waiting in the holder's FIFO, or more.")
(defcost fn2-claim-release-core :tables (fn2-core-claims fn2-core-machines)
  :effects ((:release (:identity-reservation)))
  :doc "Release a held claim and hand it to its FIFO's head, waking that transaction.")
(defcost fn2-txn-begin :bytes 256 :tables (fn2-core-claims fn2-core-machines fn2-conn-table fn2-core-pool)
  :own-writes (word upload)
  :doc "Admit: wait for the upload's verdict when no Message-ID is supplied, else hash it and begin the claim.")
(defcost fn2-txn-claim-walk :bytes 4096 :tables (fn2-core-claims)
  :effects ((:acquire (:identity-reservation)))
  :doc "One run of the claim walk.")
(defcost fn2-txn-decide :bytes 4096
  :tables (fn2-core-id-decides fn2-core-id-stamps fn2-core-overlays fn2-core-overlay-index fn2-core-run-installed
           fn2-core-run-cursors fn2-core-run-paths fn2-core-run-cache fn2-core-fields fn2-core-pool fn2-core-fc)
  :own-writes (word offered)
  :doc "Lookup: the upload's verdict, then the identity offer (one run) or one decision step (another), then the injected-field refusal.")
(defcost fn2-txn-declare :bytes 8192
  :tables (fn2-core-succ-txns fn2-core-succ-slots fn2-core-run-cursors fn2-core-run-paths fn2-core-fields fn2-core-pool)
  :own-writes (word counted lines prepared gcur gskip ngroups)
  :doc "Prepare: count the body's lines (at most 2,048 octets per run); look each Newsgroups name up (at most 1,275 octets scanned and one lookup source per run); refuse :group or the injected fields; declare the write slots and resolve them (one step per run).")
(defcost fn2-txn-commit :bytes *fn2-txn-ready-bytes*
  :tables (fn2-core-succ-txns fn2-core-succ-slots fn2-core-id-decides fn2-core-id-engine fn2-core-overlays
           fn2-core-overlay-index fn2-core-fields fn2-core-pool)
  :own-writes (word offered)
  :effects ((:acquire (:batch-membership)))
  :doc "Ready, one transition: stage every slot against the tip, admit the member to the batch, bind on :ok; a stale identity fact decides again.")
(defcost fn2-txn-finish :steps *fn2-work-transition*
  :tables (fn2-conn-table fn2-core-machines fn2-core-succ-txns fn2-core-succ-slots fn2-core-id-decides)
  :doc "The outcome: post the word to the connection (waking it) and release the successor's slots and decision.")
(defcost fn2-txn-unclaim-run :steps *fn2-work-transition* :tables (fn2-core-claims fn2-core-machines)
  :effects ((:release (:identity-reservation)))
  :doc "Release the claim; its FIFO's head takes it and is woken.")
(defcost fn2-txn-wake-upload :tables (fn2-core-machines)
  :doc "Wake the upload this transaction held, if it still names it, so it drains.")

;; ------------------------------------------------------------------------
;; The operations, materialized after the core instance (assembly-callbacks-d-txn,
;; after the upload's continuations): wrappers over the claim table and C's seams, and the
;; staged helpers each arm calls (each with its own preservation facts).
(defmacro fn2-txn-op-events ()
 '(progn
(defun fn2-txn-hash (n slot gen off okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (natp n) (natp off))))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (code h1)
    (mv-let (code h1 h2) (fn2-ribbon-hash n slot gen off 0 okind oslot ogen fn2-pool)
      (declare (ignore h2)) (mv code h1))
    (mv code h1)))
(defthm fn2-txn-hash-type
  (unsigned-byte-p 32 (mv-nth 1 (fn2-txn-hash n slot gen off okind oslot ogen fn2-core))))
(defun fn2-claim-begin-core (c hash slot gen off len ok os og fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-claims (fn2-core-claims fn2-core)))
    (code fn2-claims) (fn2-claim-begin c hash slot gen off len ok os og fn2-claims) (mv code fn2-core)))
(fn2-core-preserves fn2-claim-begin-core (c hash slot gen off len ok os og fn2-core) :position 1 :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))
(defun fn2-claim-walk-core (c budget fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (natp budget))))
  (stobj-let ((fn2-claims (fn2-core-claims fn2-core)) (fn2-pool (fn2-core-pool fn2-core)))
    (code holder fn2-claims) (fn2-claim-walk c budget fn2-claims fn2-pool) (mv code holder fn2-core)))
(fn2-core-preserves fn2-claim-walk-core (c budget fn2-core) :position 2 :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))
(defun fn2-claim-state-core (c fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-claims (fn2-core-claims fn2-core)))
    (s) (if (fn2-claim-rowp c fn2-claims) (fn2-claims-state c fn2-claims) *fn2-claim-state-free*) s))
;; Release C's claim; the FIFO's head W (a claim row = a transaction slot)
;; takes it in the same step and is woken.
(defun fn2-claim-release-core (c fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* (((mv code w fn2-core)
        (stobj-let ((fn2-claims (fn2-core-claims fn2-core)))
          (code w fn2-claims) (fn2-claim-release c fn2-claims) (mv code w fn2-core)))
       ((unless (eq code :ok)) (mv code fn2-core))
       ((when (equal w *fn2-none*)) (mv :ok fn2-core))
       (waiter (+ (fn2-machine-kind-base *fn2-txn-kind* fn2-core) (nfix w)))
       ((unless (and (fn2-machine-idp waiter fn2-core) (eq (fn2-txn-snapshot-read-code waiter fn2-core) :ok)))
        (mv :bounds fn2-core)))
    (let ((fn2-core (fn2-machine-set-wake-id waiter fn2-core))) (mv :ok fn2-core))))
(fn2-core-preserves fn2-claim-release-core (c fn2-core) :position 1 :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))
(in-theory (disable fn2-commit-admit-txn fn2-txn-hash fn2-claim-begin-core fn2-claim-walk-core fn2-claim-state-core
                    fn2-claim-release-core))

;; The upload this transaction serves, read across rows (no cross-row
;; write): live while it keeps its generation and still names this
;; transaction; sealed once its verdict is written (the digest is stored in
;; window right after the source, fn2-upload-digest-at; the source is hashed
;; whole).
(defun fn2-txn-upload-live-p (u ugen id gen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (and (eq (fn2-upload-snapshot-read-code u fn2-core) :ok)
       (equal (fn2-machine-generation u fn2-core) ugen)
       (equal (fn2-upload-row-txn u fn2-core) id)
       (equal (fn2-upload-row-txn-gen u fn2-core) gen)))
(defun fn2-txn-upload-sealed-p (u fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (and (eq (fn2-upload-snapshot-read-code u fn2-core) :ok)
       (equal (fn2-upload-row-phase u fn2-core) *fn2-upload-state-sealed*)))
(defun fn2-txn-upload-aborting-p (u fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (and (eq (fn2-upload-snapshot-read-code u fn2-core) :ok)
       (equal (fn2-upload-row-phase u fn2-core) *fn2-upload-state-aborting*)))
;; The upload's verdict when it is sealed: its definite refusal word, else
;; its injected-field word (Xref/Injection, checked after identity and group
;; in the model's order), else 0.
(defun fn2-txn-upload-words (u fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (eq (fn2-upload-snapshot-read-code u fn2-core) :ok)
      (mv (fn2-upload-row-word u fn2-core) (fn2-upload-row-inj u fn2-core))
    (mv 0 0)))
;; At the drain: wake the upload U if it still names this row (ID of
;; generation GEN), so it sees the row gone and drains.
(defun fn2-txn-wake-upload (u id gen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (and (eq (fn2-upload-snapshot-read-code u fn2-core) :ok) (fn2-machine-idp u fn2-core)
           (equal (fn2-upload-row-txn u fn2-core) id) (equal (fn2-upload-row-txn-gen u fn2-core) gen))
      (fn2-machine-set-wake-id u fn2-core)
    fn2-core))
(fn2-core-preserves fn2-txn-wake-upload (u id gen fn2-core) :rows nil)
(in-theory (disable fn2-txn-upload-words fn2-txn-wake-upload))

;; :admit. Returns (mv next fn2-core): :reserve (claim begun), :idle (no
;; Message-ID was supplied and the verdict is not in yet), :draining (the
;; upload left, or the verdict without a Message-ID was posted), :stop.
;; D5 1/n: a POST without a Message-ID is answered with the upload's verdict
;; or the interim :not-stored; the generated Message-ID comes with injection
;; (D5 2/n, owed row fn2-txn-generated-message-id).
(defun fn2-txn-begin (id fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* (((unless (and (eq (fn2-txn-snapshot-read-code id fn2-core) :ok) (fn2-machine-idp id fn2-core)))
        (mv :stop fn2-core))
       (gen (fn2-machine-generation id fn2-core))
       (u (fn2-txn-row-upload id fn2-core)) (ugen (fn2-txn-row-upload-gen id fn2-core))
       ((unless (fn2-txn-upload-live-p u ugen id gen fn2-core)) (mv :draining fn2-core))
       (ml (fn2-upload-row-ml u fn2-core))
       ((when (equal ml 0))
        (if (not (fn2-txn-upload-sealed-p u fn2-core))
            (mv (if (fn2-txn-upload-aborting-p u fn2-core) :draining :idle) fn2-core)
          (b* (((mv w inj) (fn2-txn-upload-words u fn2-core))
               (word (cond ((not (equal w 0)) w) ((not (equal inj 0)) inj)
                           (t (fn2-upload-word-code :not-stored))))
               ((mv & fn2-core) (fn2-conn-post-word (fn2-txn-row-conn id fn2-core) (fn2-txn-row-conn-gen id fn2-core)
                                                   (fn2-txn-row-request id fn2-core) word fn2-core)))
            (mv :draining fn2-core))))
       (c0 (fn2-upload-row-c0-slot u fn2-core)) (g0 (fn2-upload-row-c0-gen u fn2-core))
       (mo (fn2-upload-row-mo u fn2-core))
       ((mv hcode hash) (fn2-txn-hash ml c0 g0 mo *fn2-upload-kind* u ugen fn2-core))
       ((unless (eq hcode :ok)) (mv :stop fn2-core))
       ((mv bcode fn2-core) (fn2-claim-begin-core (fn2-machine-slot id fn2-core) hash c0 g0 mo ml
                                                  *fn2-upload-kind* u ugen fn2-core)))
    (mv (if (eq bcode :ok) :reserve :stop) fn2-core)))
(fn2-core-preserves fn2-txn-begin (id fn2-core) :position 1 :rows nil)

;; :reserve, one run of the walk: (mv next fn2-core), :lookup (the claim is
;; held: taken now, or handed over by its holder's release), :run (more of
;; the chain), :idle (waiting in the holder's FIFO), :stop.
(defun fn2-txn-claim-walk (id fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* (((unless (fn2-machine-idp id fn2-core)) (mv :stop fn2-core))
       (c (fn2-machine-slot id fn2-core))
       (s (fn2-claim-state-core c fn2-core))
       ((when (equal s *fn2-claim-state-held*)) (mv :lookup fn2-core))
       ((when (equal s *fn2-claim-state-waiting*)) (mv :idle fn2-core))
       ((mv code & fn2-core) (fn2-claim-walk-core c *fn2-txn-claim-steps* fn2-core)))
    (mv (case code (:claimed :lookup) (:wait :idle) (:more :run) (otherwise :stop)) fn2-core)))
(fn2-core-preserves fn2-txn-claim-walk (id fn2-core) :position 1 :rows nil)

;; :lookup: (mv next fn2-core). The upload's verdict first (the model's
;; order: its definite refusals precede identity); then the identity offer
;; (one run) and the decision's steps (one per run); :stored goes on to
;; :prepare (the group check, then the injected fields: the model's order);
;; :duplicate, :conflict and :evidence are refused by word.
(defun fn2-txn-offer (id u ugen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* (((unless (and (eq (fn2-upload-snapshot-read-code u fn2-core) :ok) (fn2-machine-idp id fn2-core))) (mv :bounds fn2-core))
       (c0 (fn2-upload-row-c0-slot u fn2-core)) (g0 (fn2-upload-row-c0-gen u fn2-core))
       (c1 (fn2-upload-row-c1-slot u fn2-core)) (g1 (fn2-upload-row-c1-gen u fn2-core))
       ((mv in1 doff) (fn2-upload-digest-at (fn2-upload-row-hashed u fn2-core) (fn2-upload-chunk-cap c0 fn2-core))))
    (fn2-identity-offer (fn2-machine-slot id fn2-core) c0 g0 (fn2-upload-row-mo u fn2-core) (fn2-upload-row-ml u fn2-core)
                        (if in1 c1 c0) (if in1 g1 g0) doff *fn2-upload-kind* u ugen fn2-core)))
(fn2-core-preserves fn2-txn-offer (id u ugen fn2-core) :position 1 :rows nil)
(in-theory (disable fn2-txn-offer))
(defun fn2-txn-decide (id fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* (((unless (and (eq (fn2-txn-snapshot-read-code id fn2-core) :ok) (fn2-machine-idp id fn2-core)))
        (mv :stop fn2-core))
       (gen (fn2-machine-generation id fn2-core))
       (u (fn2-txn-row-upload id fn2-core)) (ugen (fn2-txn-row-upload-gen id fn2-core))
       ;; the upload left (its connection went): nothing to answer
       ((unless (and (fn2-txn-upload-live-p u ugen id gen fn2-core) (not (fn2-txn-upload-aborting-p u fn2-core))))
        (let ((fn2-core (fn2-machine-write-word id 0 fn2-core))) (mv :refused fn2-core)))
       ((unless (fn2-txn-upload-sealed-p u fn2-core)) (mv :idle fn2-core))
       ((mv w &) (fn2-txn-upload-words u fn2-core))
       ((unless (equal w 0)) (let ((fn2-core (fn2-machine-write-word id w fn2-core))) (mv :refused fn2-core)))
       ((unless (equal (fn2-txn-row-offered id fn2-core) 1))
        (b* (((mv code fn2-core) (fn2-txn-offer id u ugen fn2-core))
             ((unless (eq code :ok)) (mv :stop fn2-core)))
          (let ((fn2-core (fn2-machine-write-offered id 1 fn2-core))) (mv :run fn2-core))))
       ((mv answer fn2-core) (fn2-identity-step (fn2-machine-slot id fn2-core) 4096 fn2-core)))
    (case answer
      (:more (mv :run fn2-core))
      (:stored (mv :prepare fn2-core))
      (:duplicate (let ((fn2-core (fn2-machine-write-word id (fn2-upload-word-code :duplicate) fn2-core))) (mv :refused fn2-core)))
      ((:conflict :evidence) (let ((fn2-core (fn2-machine-write-word id (fn2-upload-word-code :conflict) fn2-core))) (mv :refused fn2-core)))
      (otherwise (mv :stop fn2-core)))))
(fn2-core-preserves fn2-txn-decide (id fn2-core) :position 1 :rows nil)

;; :prepare. The body's lines first (the article row's `lines`): LF octets of
;; [body, source) read under the upload's owner, at most
;; *fn2-txn-count-bytes* per run, COUNTED the continuation.
(defun fn2-txn-count-loop (n slot gen off lines okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix n)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp n) (natp off) (natp lines))))
  (if (zp n) (mv :ok lines)
    (mv-let (ok byte) (fn2-gram-read slot gen off okind oslot ogen fn2-pool)
      (if (not ok) (mv :bounds lines)
        (fn2-txn-count-loop (- n 1) slot gen (+ 1 off) (if (equal byte 10) (+ 1 (nfix lines)) (nfix lines))
                            okind oslot ogen fn2-pool)))))
(defthm fn2-txn-count-loop-natp
  (implies (natp lines) (natp (mv-nth 1 (fn2-txn-count-loop n slot gen off lines okind oslot ogen fn2-pool))))
  :rule-classes :type-prescription)
(defthm fn2-txn-count-loop-bound
  (implies (natp lines) (<= (mv-nth 1 (fn2-txn-count-loop n slot gen off lines okind oslot ogen fn2-pool))
                            (+ lines (nfix n))))
  :rule-classes :linear)
(in-theory (disable fn2-txn-count-loop))
(defun fn2-txn-count (slot gen off n lines okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (natp off) (natp n) (natp lines))))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (code lines2) (fn2-txn-count-loop n slot gen off lines okind oslot ogen fn2-pool) (mv code lines2)))
(defthm fn2-txn-count-natp
  (implies (natp lines) (natp (mv-nth 1 (fn2-txn-count slot gen off n lines okind oslot ogen fn2-core))))
  :rule-classes :type-prescription)
(in-theory (disable fn2-txn-count))
;; One counting run over [from, to) of the source (chunk 0 then chunk 1):
;; (mv code counted lines).
(defun fn2-txn-count-run (from to lines c0 g0 c1 g1 cap0 u ugen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (natp from) (natp to) (natp lines) (natp cap0))))
  (b* ((in0 (< from cap0))
       (n (min *fn2-txn-count-bytes* (min (nfix (- to from)) (if in0 (- cap0 from) (nfix (- to from))))))
       ((mv code lines2) (fn2-txn-count (if in0 c0 c1) (if in0 g0 g1) (if in0 from (- from cap0)) n lines
                                        *fn2-upload-kind* u ugen fn2-core)))
    (mv code (+ from n) lines2)))
(in-theory (disable fn2-txn-count-run))
;; The write slots of an accepted POST (C-S3): the identity fact (its
;; article and binding the member's commit position, :event; the offerer's
;; principal), the article row (key and birth the same event, live, version
;; 1, the source's content identity (appended after the source), the stored
;; length, the source until injection in D5 2/n, and the body's lines) and
;; the operation outcome ((principal, operation) with the operation the
;; member's commit position, fresh per NNTP attempt: NNT-005; the request
;; binding the source's identity; accepted; the event).
(defmacro fn2-txn-chain (&rest calls)
  (if (atom calls) '(mv :ok fn2-core)
    (if (atom (cdr calls)) (car calls)
      `(mv-let (c fn2-core) ,(car calls) (if (eq c :ok) (fn2-txn-chain ,@(cdr calls)) (mv c fn2-core))))))
(defun fn2-txn-put-article (tx dslot dgen doff bytes lines principal u ugen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (let ((i *fn2-txn-slot-article*))
    (fn2-txn-chain
     (fn2-successor-put tx i *fn2-txn-article-sid* :insert fn2-core)
     (fn2-successor-arg tx i *fn2-article-entry-field-article* :event 0 fn2-core)
     (fn2-successor-arg tx i *fn2-article-entry-field-birth* :event 0 fn2-core)
     (fn2-successor-arg tx i *fn2-article-entry-field-state* :value *fn2-txn-article-live* fn2-core)
     (fn2-successor-arg tx i *fn2-article-entry-field-version* :value *fn2-txn-article-version* fn2-core)
     (fn2-successor-arg-octets tx i *fn2-article-entry-field-source* dslot dgen doff *fn2-upload-digest-octets*
                               *fn2-upload-kind* u ugen fn2-core)
     (fn2-successor-arg tx i *fn2-article-entry-field-bytes* :value bytes fn2-core)
     (fn2-successor-arg tx i *fn2-article-entry-field-lines* :value lines fn2-core)
     (fn2-successor-put tx *fn2-txn-slot-record* *fn2-txn-identity-sid* :record fn2-core)
     (fn2-successor-arg tx *fn2-txn-slot-record* 0 :event 0 fn2-core)
     (fn2-successor-arg tx *fn2-txn-slot-record* 1 :value principal fn2-core)
     (fn2-successor-put tx *fn2-txn-slot-outcome* *fn2-txn-outcome-sid* :insert fn2-core)
     (fn2-successor-arg tx *fn2-txn-slot-outcome* *fn2-outcome-entry-field-principal* :value principal fn2-core)
     (fn2-successor-arg tx *fn2-txn-slot-outcome* *fn2-outcome-entry-field-operation* :event 0 fn2-core)
     (fn2-successor-arg-octets tx *fn2-txn-slot-outcome* *fn2-outcome-entry-field-request* dslot dgen doff
                               *fn2-upload-digest-octets* *fn2-upload-kind* u ugen fn2-core)
     (fn2-successor-arg tx *fn2-txn-slot-outcome* *fn2-outcome-entry-field-outcome* :value *fn2-txn-outcome-accepted* fn2-core)
     (fn2-successor-arg tx *fn2-txn-slot-outcome* *fn2-outcome-entry-field-event* :event 0 fn2-core))))
(fn2-core-preserves fn2-txn-put-article (tx dslot dgen doff bytes lines principal u ugen fn2-core) :position 1 :rows nil)
;; A group-count accept for GROUP in accept slot K (its number assigned high
;; + 1 at stage, C4a).
(defun fn2-txn-put-accept (tx k group fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (natp k))))
  (let ((i (+ *fn2-txn-slot-accepts* k)))
    (fn2-txn-chain
     (fn2-successor-put tx i *fn2-txn-counts-sid* :accept fn2-core)
     (fn2-successor-arg tx i 0 :value group fn2-core))))
(fn2-core-preserves fn2-txn-put-accept (tx k group fn2-core) :position 1 :rows nil)
(in-theory (disable fn2-txn-put-article fn2-txn-put-accept))

;; Newsgroups, a name at a time: the value's names are separated by commas
;; and white space (the model's split).
(defun fn2-txn-sep-p (b) (declare (xargs :guard t)) (member b '(44 32 9 13 10)))
;; Skip separators from OFF, at most N octets: (mv ok pos).
(defun fn2-txn-skip-loop (n slot gen off okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix n) :guard (and (fn2-pool-wfp fn2-pool) (natp n) (natp off))))
  (if (zp n) (mv t off)
    (mv-let (ok b) (fn2-gram-read slot gen off okind oslot ogen fn2-pool)
      (cond ((not ok) (mv nil off))
            ((fn2-txn-sep-p b) (fn2-txn-skip-loop (- n 1) slot gen (+ 1 off) okind oslot ogen fn2-pool))
            (t (mv t off))))))
;; Advance over a name from OFF, at most N octets: (mv ok pos).
(defun fn2-txn-name-loop (n slot gen off okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix n) :guard (and (fn2-pool-wfp fn2-pool) (natp n) (natp off))))
  (if (zp n) (mv t off)
    (mv-let (ok b) (fn2-gram-read slot gen off okind oslot ogen fn2-pool)
      (cond ((not ok) (mv nil off))
            ((fn2-txn-sep-p b) (mv t off))
            (t (fn2-txn-name-loop (- n 1) slot gen (+ 1 off) okind oslot ogen fn2-pool))))))
(defthm fn2-txn-skip-loop-natp
  (implies (natp off) (natp (mv-nth 1 (fn2-txn-skip-loop n slot gen off okind oslot ogen fn2-pool))))
  :rule-classes :type-prescription)
(defthm fn2-txn-skip-loop-pos
  (implies (natp off) (and (<= off (mv-nth 1 (fn2-txn-skip-loop n slot gen off okind oslot ogen fn2-pool))) (<= (mv-nth 1 (fn2-txn-skip-loop n slot gen off okind oslot ogen fn2-pool)) (+ off (nfix n)))))
  :rule-classes :linear)
(defthm fn2-txn-name-loop-natp
  (implies (natp off) (natp (mv-nth 1 (fn2-txn-name-loop n slot gen off okind oslot ogen fn2-pool))))
  :rule-classes :type-prescription)
(defthm fn2-txn-name-loop-pos
  (implies (natp off) (and (<= off (mv-nth 1 (fn2-txn-name-loop n slot gen off okind oslot ogen fn2-pool))) (<= (mv-nth 1 (fn2-txn-name-loop n slot gen off okind oslot ogen fn2-pool)) (+ off (nfix n)))))
  :rule-classes :linear)
(in-theory (disable fn2-txn-skip-loop fn2-txn-name-loop))
;; The next name of [CUR, END) of the Newsgroups value (offsets relative to
;; its BASE in chunk 0): (mv status start len next skip). STATUS :name
;; (START LEN, NEXT past it), :end, :run (more scanning; NEXT and SKIP the
;; continuation), :fault. A name longer than 250 octets is no group: it is
;; skipped (SKIP) to its end, never looked up in part.
(defun fn2-txn-next-name (base cur end skip slot gen okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (natp base) (natp cur) (natp end))))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (status start len next skip2)
    (b* ((lim (max cur (min end (+ cur *fn2-txn-scan-bytes*))))
         ((when skip)
          (mv-let (ok pos) (fn2-txn-name-loop (- lim cur) slot gen (+ base cur) okind oslot ogen fn2-pool)
            (let ((pos (- pos base)))
              (if (not ok) (mv :fault 0 0 cur skip) (mv :run 0 0 pos (and (= pos lim) (< pos end)))))))
         ((mv ok s) (fn2-txn-skip-loop (- lim cur) slot gen (+ base cur) okind oslot ogen fn2-pool))
         (s (- s base))
         ((unless ok) (mv :fault 0 0 cur nil))
         ((when (>= s end)) (mv :end 0 0 end nil))
         ((when (>= s lim)) (mv :run 0 0 s nil))
         (tlim (min end (+ s 251)))
         ((mv ok2 e) (fn2-txn-name-loop (- tlim s) slot gen (+ base s) okind oslot ogen fn2-pool))
         (e (- e base))
         ((unless ok2) (mv :fault 0 0 cur nil))
         ((when (and (= e tlim) (< e end) (= (- e s) 251))) (mv :run 0 0 e t)))
      (mv :name s (- e s) e nil))
    (mv status start len next skip2)))
(defthm fn2-txn-next-name-types
  (implies (and (natp base) (natp cur) (natp end))
           (and (natp (mv-nth 1 (fn2-txn-next-name base cur end skip slot gen okind oslot ogen fn2-core)))
                (natp (mv-nth 2 (fn2-txn-next-name base cur end skip slot gen okind oslot ogen fn2-core)))
                (natp (mv-nth 3 (fn2-txn-next-name base cur end skip slot gen okind oslot ogen fn2-core))))))
(in-theory (disable fn2-txn-next-name))

;; :prepare: (mv next fn2-core), :run, :ready, :refused, :stop. In order:
;; the body's lines (LF octets of [body, source) under the upload's owner,
;; at most *fn2-txn-count-bytes* per run); the Newsgroups names looked up
;; (S-GROUP; one lookup source per run, its arguments the same until it
;; answers), each carried one an accept slot; none carried: :group; then the
;; injected fields (the model's order); then the slots, and resolve (one step
;; per run).
(defun fn2-txn-count-step (id u ugen counted source lines fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (natp counted) (natp source) (natp lines))))
  (b* (((unless (eq (fn2-upload-snapshot-read-code u fn2-core) :ok)) (mv :stop fn2-core))
       (c0 (fn2-upload-row-c0-slot u fn2-core)) (g0 (fn2-upload-row-c0-gen u fn2-core))
       (c1 (fn2-upload-row-c1-slot u fn2-core)) (g1 (fn2-upload-row-c1-gen u fn2-core))
       (cap0 (fn2-upload-chunk-cap c0 fn2-core))
       ((mv code counted2 lines2) (fn2-txn-count-run counted source lines c0 g0 c1 g1 cap0 u ugen fn2-core))
       ((unless (and (eq code :ok) (unsigned-byte-p 60 counted2) (unsigned-byte-p 32 lines2))) (mv :stop fn2-core))
       (fn2-core (fn2-machine-write-counted id counted2 fn2-core)))
    (let ((fn2-core (fn2-machine-write-lines id lines2 fn2-core))) (mv :run fn2-core))))
(fn2-core-preserves fn2-txn-count-step (id u ugen counted source lines fn2-core) :position 1 :rows nil)
(defun fn2-txn-group-step (id tx u ugen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* (((unless (and (eq (fn2-upload-snapshot-read-code u fn2-core) :ok) (eq (fn2-txn-snapshot-read-code id fn2-core) :ok)))
        (mv :stop fn2-core))
       (c0 (fn2-upload-row-c0-slot u fn2-core)) (g0 (fn2-upload-row-c0-gen u fn2-core))
       (base (fn2-upload-row-no u fn2-core)) (end (fn2-upload-row-nl u fn2-core))
       (cur (fn2-txn-row-gcur id fn2-core)) (skip (equal (fn2-txn-row-gskip id fn2-core) 1))
       (ngroups (fn2-txn-row-ngroups id fn2-core))
       ((mv status start len next skip2) (fn2-txn-next-name base cur end skip c0 g0 *fn2-upload-kind* u ugen fn2-core))
       ((unless (unsigned-byte-p 32 next)) (mv :stop fn2-core)))
    (case status
      (:run (let ((fn2-core (fn2-machine-write-gcur id next fn2-core)))
              (let ((fn2-core (fn2-machine-write-gskip id (if skip2 1 0) fn2-core))) (mv :run fn2-core))))
      (:end (let ((fn2-core (fn2-machine-write-gcur id next fn2-core))) (mv :run fn2-core)))
      (:name
       (mv-let (code group fn2-core)
         (fn2-group-lookup tx c0 g0 (+ base start) len *fn2-upload-kind* u ugen 4096 fn2-core)
         (case code
           (:more (mv :run fn2-core))
           (:absent (let ((fn2-core (fn2-machine-write-gcur id next fn2-core))) (mv :run fn2-core)))
           (:ok (b* (((when (>= ngroups *fn2-txn-groups-max*))
                      (let ((fn2-core (fn2-machine-write-word id (fn2-upload-word-code :unaffordable) fn2-core))) (mv :refused fn2-core)))
                     ((mv pcode fn2-core) (fn2-txn-put-accept tx ngroups group fn2-core))
                     ((unless (eq pcode :ok)) (mv :stop fn2-core))
                     (fn2-core (fn2-machine-write-ngroups id (+ 1 ngroups) fn2-core)))
                  (let ((fn2-core (fn2-machine-write-gcur id next fn2-core))) (mv :run fn2-core))))
           (otherwise (mv :stop fn2-core)))))
      (otherwise (mv :stop fn2-core)))))
(fn2-core-preserves fn2-txn-group-step (id tx u ugen fn2-core) :position 1 :rows nil)
(in-theory (disable fn2-txn-count-step fn2-txn-group-step))
(defun fn2-txn-declare-1 (id fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* (((unless (and (eq (fn2-txn-snapshot-read-code id fn2-core) :ok) (fn2-machine-idp id fn2-core)))
        (mv :stop fn2-core))
       (tx (fn2-machine-slot id fn2-core))
       ;; declared already: resolve, one step per run
       ((when (equal (fn2-txn-row-prepared id fn2-core) 1))
        (mv-let (answer fn2-core) (fn2-successor-resolve tx 4096 fn2-core)
          (mv (case answer (:ok :ready) (:more :run) (otherwise :stop)) fn2-core)))
       (u (fn2-txn-row-upload id fn2-core)) (ugen (fn2-txn-row-upload-gen id fn2-core))
       ((unless (eq (fn2-upload-snapshot-read-code u fn2-core) :ok)) (mv :stop fn2-core))
       (source (fn2-upload-row-hashed u fn2-core))
       (counted (max (fn2-upload-row-scan-off u fn2-core) (fn2-txn-row-counted id fn2-core)))
       (lines (fn2-txn-row-lines id fn2-core))
       ((when (< counted source)) (fn2-txn-count-step id u ugen counted source lines fn2-core))
       ((when (< (fn2-txn-row-gcur id fn2-core) (fn2-upload-row-nl u fn2-core))) (fn2-txn-group-step id tx u ugen fn2-core))
       ((when (equal (fn2-txn-row-ngroups id fn2-core) 0))
        (let ((fn2-core (fn2-machine-write-word id (fn2-upload-word-code :group) fn2-core))) (mv :refused fn2-core)))
       ((mv & inj) (fn2-txn-upload-words u fn2-core))
       ((unless (equal inj 0)) (let ((fn2-core (fn2-machine-write-word id inj fn2-core))) (mv :refused fn2-core)))
       (c0 (fn2-upload-row-c0-slot u fn2-core)) (g0 (fn2-upload-row-c0-gen u fn2-core))
       (c1 (fn2-upload-row-c1-slot u fn2-core)) (g1 (fn2-upload-row-c1-gen u fn2-core))
       ((mv in1 doff) (fn2-upload-digest-at source (fn2-upload-chunk-cap c0 fn2-core)))
       ((mv code fn2-core) (fn2-txn-put-article tx (if in1 c1 c0) (if in1 g1 g0) doff source lines
                                                (fn2-txn-row-principal-slot id fn2-core) u ugen fn2-core))
       ((unless (eq code :ok)) (mv :stop fn2-core)))
    (let ((fn2-core (fn2-machine-write-prepared id 1 fn2-core))) (mv :run fn2-core))))
(fn2-core-preserves fn2-txn-declare-1 (id fn2-core) :position 1 :rows nil)

;; :ready, one transition (C-S3): stage every slot against the tip; on :ok
;; admit the member (B-S2, the interim answers :not-served: refused
;; :not-stored), and on the admission's :ok bind the slots into its batch
;; with the member's commit position, which cannot fail. :full and an
;; exhausted batch are backpressure (stay :ready, run again); :stale decides
;; again.
(defun fn2-txn-commit-1 (id fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* (((unless (and (eq (fn2-txn-snapshot-read-code id fn2-core) :ok) (fn2-machine-idp id fn2-core)))
        (mv :stop fn2-core))
       (tx (fn2-machine-slot id fn2-core))
       ((mv scode & fn2-core) (fn2-successor-stage tx fn2-core)))
    (case scode
      (:ok
       (b* (((unless (and (eq (fn2-txn-snapshot-read-code id fn2-core) :ok) (fn2-machine-idp id fn2-core)))
             (mv :stop fn2-core))
            (u (fn2-txn-row-upload id fn2-core)) (ugen (fn2-txn-row-upload-gen id fn2-core))
            ((unless (eq (fn2-upload-snapshot-read-code u fn2-core) :ok)) (mv :stop fn2-core))
            ((mv acode batch event fn2-core)
             (fn2-commit-admit-txn (fn2-upload-row-c0-slot u fn2-core) (fn2-upload-row-c0-gen u fn2-core)
                                   (fn2-upload-row-hashed u fn2-core) *fn2-upload-kind* u ugen fn2-core)))
         (case acode
           (:ok (mv-let (bcode fn2-core) (fn2-successor-bind tx batch event fn2-core)
                  (mv (if (eq bcode :ok) :batched :stop) fn2-core)))
           (:admission (let ((fn2-core (fn2-machine-write-word id (fn2-upload-word-code :not-stored) fn2-core))) (mv :refused fn2-core)))
           (:exhausted (mv :run fn2-core))
           (otherwise (mv :stop fn2-core)))))
      (:full (mv :run fn2-core))
      ;; a fact or a run moved under the identity fact: decide again (its
      ;; slots stay declared; :prepare resolves them again)
      (:stale (let ((fn2-core (fn2-machine-write-offered id 0 fn2-core))) (mv :lookup fn2-core)))
      (:duplicate (let ((fn2-core (fn2-machine-write-word id (fn2-upload-word-code :duplicate) fn2-core))) (mv :refused fn2-core)))
      (:evidence (let ((fn2-core (fn2-machine-write-word id (fn2-upload-word-code :conflict) fn2-core))) (mv :refused fn2-core)))
      (:identity-conflict-bound (let ((fn2-core (fn2-machine-write-word id (fn2-upload-word-code :identity-conflict-bound) fn2-core))) (mv :refused fn2-core)))
      (:capacity (let ((fn2-core (fn2-machine-write-word id (fn2-upload-word-code :unaffordable) fn2-core))) (mv :refused fn2-core)))
      (otherwise (mv :stop fn2-core)))))
(fn2-core-preserves fn2-txn-commit-1 (id fn2-core) :position 1 :rows nil)
;; The two runs that charge more than another kind's cap (:prepare 8 KiB,
;; :ready 16 KiB) end by asserting the row is still this kind's (the
;; charge's guard is over the row's kind after the run): anything else is
;; :stop, and the arm stops the core.
(defun fn2-txn-kind-ok (id fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (and (fn2-machine-idp id fn2-core) (equal (fn2-machine-kind id fn2-core) *fn2-txn-kind*)))
;; A phase write (the txn table) leaves the row's id and kind as they were.
(defthm fn2-txn-idp-of-table-update
  (equal (fn2-machine-idp id (update-fn2-txn-table x fn2-core)) (fn2-machine-idp id fn2-core))
  :hints (("Goal" :in-theory (enable fn2-machine-idp))))
(defthm fn2-txn-kind-of-table-update
  (equal (fn2-machine-kind id (update-fn2-txn-table x fn2-core)) (fn2-machine-kind id fn2-core))
  :hints (("Goal" :in-theory (enable fn2-machine-kind fn2-machine-idp))))
(defthm fn2-txn-idp-of-refuse-write
  (equal (fn2-machine-idp id (fn2-machine-refuse-write fn2-core)) (fn2-machine-idp id fn2-core))
  :hints (("Goal" :in-theory (enable fn2-machine-idp fn2-machine-refuse-write fn2-core-stop))))
(defthm fn2-txn-kind-of-refuse-write
  (equal (fn2-machine-kind id (fn2-machine-refuse-write fn2-core)) (fn2-machine-kind id fn2-core))
  :hints (("Goal" :in-theory (enable fn2-machine-kind fn2-machine-idp fn2-machine-refuse-write fn2-core-stop))))
(defmacro fn2-txn-checked (name inner)
  `(progn
     (defun ,name (id fn2-core)
       (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
       (mv-let (next fn2-core) (,inner id fn2-core)
         (if (fn2-txn-kind-ok id fn2-core) (mv next fn2-core) (mv :stop fn2-core))))
     (fn2-core-preserves ,name (id fn2-core) :position 1 :rows nil)
     (defthm ,(fn2-columns-sym name "-KIND")
       (implies (not (equal (mv-nth 0 (,name id fn2-core)) :stop))
                (and (fn2-machine-idp id (mv-nth 1 (,name id fn2-core)))
                     (equal (fn2-machine-kind id (mv-nth 1 (,name id fn2-core))) *fn2-txn-kind*)))
       :hints (("Goal" :in-theory (enable ,name fn2-txn-kind-ok))))))
(fn2-txn-checked fn2-txn-declare fn2-txn-declare-1)
(fn2-txn-checked fn2-txn-commit fn2-txn-commit-1)

;; :accepted / :refused: the word (0: the connection left, nothing to post)
;; to the connection, and the successor's slots and decision; :releasing
;; then releases the claim (its FIFO's head takes it), and the drain lets the
;; upload go: each run wakes one row. (mv next fn2-core).
(defun fn2-txn-finish (id fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* (((unless (and (eq (fn2-txn-snapshot-read-code id fn2-core) :ok) (fn2-machine-idp id fn2-core)))
        (mv :stop fn2-core))
       (word (fn2-txn-row-word id fn2-core))
       (tx (fn2-machine-slot id fn2-core))
       ((mv & fn2-core)
        (if (equal word 0) (mv :none fn2-core)
          (fn2-conn-post-word (fn2-txn-row-conn id fn2-core) (fn2-txn-row-conn-gen id fn2-core)
                              (fn2-txn-row-request id fn2-core) word fn2-core)))
       ((mv rcode fn2-core) (fn2-successor-release tx fn2-core)))
    (mv (if (eq rcode :ok) :releasing :stop) fn2-core)))
(fn2-core-preserves fn2-txn-finish (id fn2-core) :position 1 :rows nil)
(defun fn2-txn-unclaim-run (id fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (not (fn2-machine-idp id fn2-core)) (mv :stop fn2-core)
    (mv-let (code fn2-core) (fn2-claim-release-core (fn2-machine-slot id fn2-core) fn2-core)
      (mv (if (eq code :ok) :draining :stop) fn2-core))))
(fn2-core-preserves fn2-txn-unclaim-run (id fn2-core) :position 1 :rows nil)
(in-theory (disable fn2-txn-begin fn2-txn-claim-walk fn2-txn-decide fn2-txn-declare-1 fn2-txn-commit-1 fn2-txn-declare
                    fn2-txn-commit fn2-txn-finish fn2-txn-unclaim-run fn2-txn-kind-ok))
))

;; ------------------------------------------------------------------------
;; The transaction's continuations (materialized after the upload's).
(defmacro fn2-txn-events ()
 '(progn
(defmachine-callback fn2-txn-idle fn2-txn (id budget) 4
  (fn2-machine-idle id fn2-core))
(defmachine-callback fn2-txn-unreached fn2-txn (id budget) 4
  (fn2-machine-refuse-phase id fn2-core))

(defmachine-callback fn2-txn-admit fn2-txn (id budget) 4
  (fn2-machine-with-work 256 *fn2-work-transition* 0
    (mv-let (next fn2-core) (fn2-txn-begin id fn2-core)
      (case next
        (:reserve (let ((fn2-core (fn2-txn-put-core id (phase *fn2-txn-state-reserve*))))
                    (fn2-machine-result 256 *fn2-work-transition* 0 t fn2-core)))
        (:idle (fn2-machine-result 256 *fn2-work-transition* 0 nil fn2-core))
        (:draining (let ((fn2-core (fn2-txn-put-core id (phase *fn2-txn-state-draining*))))
                     (fn2-machine-result 256 *fn2-work-transition* 0 t fn2-core)))
        (otherwise (fn2-machine-refuse-phase id fn2-core))))))

(defmachine-callback fn2-txn-reserve fn2-txn (id budget) 4
  (fn2-machine-with-work 4096 *fn2-work-transition* 0
    (mv-let (next fn2-core) (fn2-txn-claim-walk id fn2-core)
      (case next
        (:lookup (let ((fn2-core (fn2-txn-put-core id (phase *fn2-txn-state-lookup*))))
                   (fn2-machine-result 4096 *fn2-work-transition* 0 t fn2-core)))
        (:run (fn2-machine-result 4096 *fn2-work-transition* 0 t fn2-core))
        (:idle (fn2-machine-result 4096 *fn2-work-transition* 0 nil fn2-core))
        (otherwise (fn2-machine-refuse-phase id fn2-core))))))

(defmachine-callback fn2-txn-lookup fn2-txn (id budget) 4
  (fn2-machine-with-work 4096 *fn2-work-transition* 0
    (mv-let (next fn2-core) (fn2-txn-decide id fn2-core)
      (case next
        (:run (fn2-machine-result 4096 *fn2-work-transition* 0 t fn2-core))
        (:idle (fn2-machine-result 4096 *fn2-work-transition* 0 nil fn2-core))
        (:prepare (let ((fn2-core (fn2-txn-put-core id (phase *fn2-txn-state-prepare*))))
                    (fn2-machine-result 4096 *fn2-work-transition* 0 t fn2-core)))
        (:refused (let ((fn2-core (fn2-txn-put-core id (phase *fn2-txn-state-refused*))))
                    (fn2-machine-result 4096 *fn2-work-transition* 0 t fn2-core)))
        (otherwise (fn2-machine-refuse-phase id fn2-core))))))

(defmachine-callback fn2-txn-slots fn2-txn (id budget) 4
  (fn2-machine-with-work 8192 *fn2-work-transition* 0
    (mv-let (next fn2-core) (fn2-txn-declare id fn2-core)
      (case next
        (:run (fn2-machine-result 8192 *fn2-work-transition* 0 t fn2-core))
        (:ready (let ((fn2-core (fn2-txn-put-core id (phase *fn2-txn-state-ready*))))
                  (fn2-machine-result 8192 *fn2-work-transition* 0 t fn2-core)))
        (:refused (let ((fn2-core (fn2-txn-put-core id (phase *fn2-txn-state-refused*))))
                    (fn2-machine-result 8192 *fn2-work-transition* 0 t fn2-core)))
        (otherwise (fn2-machine-refuse-phase id fn2-core))))))

(defmachine-callback fn2-txn-ready fn2-txn (id budget) 4
  (fn2-machine-with-work *fn2-txn-ready-bytes* *fn2-work-transition* 0
    (mv-let (next fn2-core) (fn2-txn-commit id fn2-core)
      (case next
        (:run (fn2-machine-result *fn2-txn-ready-bytes* *fn2-work-transition* 0 t fn2-core))
        (:lookup (let ((fn2-core (fn2-txn-put-core id (phase *fn2-txn-state-lookup*))))
                   (fn2-machine-result *fn2-txn-ready-bytes* *fn2-work-transition* 0 t fn2-core)))
        (:batched (let ((fn2-core (fn2-txn-put-core id (phase *fn2-txn-state-batched*))))
                    (fn2-machine-result *fn2-txn-ready-bytes* *fn2-work-transition* 0 nil fn2-core)))
        (:refused (let ((fn2-core (fn2-txn-put-core id (phase *fn2-txn-state-refused*))))
                    (fn2-machine-result *fn2-txn-ready-bytes* *fn2-work-transition* 0 t fn2-core)))
        (otherwise (fn2-machine-refuse-phase id fn2-core))))))

(defmachine-callback fn2-txn-reply fn2-txn (id budget) 4
  (fn2-machine-with-work 0 *fn2-work-transition* 0
    (mv-let (next fn2-core) (fn2-txn-finish id fn2-core)
      (if (eq next :releasing)
          (let ((fn2-core (fn2-txn-put-core id (phase *fn2-txn-state-releasing*))))
            (fn2-machine-result 0 *fn2-work-transition* 0 t fn2-core))
        (fn2-machine-refuse-phase id fn2-core)))))
(defmachine-callback fn2-txn-unclaim fn2-txn (id budget) 4
  (fn2-machine-with-work 0 *fn2-work-transition* 0
    (mv-let (next fn2-core) (fn2-txn-unclaim-run id fn2-core)
      (if (eq next :draining)
          (let ((fn2-core (fn2-txn-put-core id (phase *fn2-txn-state-draining*))))
            (fn2-machine-result 0 *fn2-work-transition* 0 t fn2-core))
        (fn2-machine-refuse-phase id fn2-core)))))

;; :draining returns the row to its partition.
(defmachine-callback fn2-txn-release fn2-txn (id budget) 4
  :contract (:cost (:steps *fn2-work-release*)
             :writes (generation upload upload-gen conn conn-gen next-free wait-reason)
             :tables (fn2-core-machines) :next (:free :retired)
             :uses (fn2-machine-gen-limit fn2-machine-free-head fn2-machine-reclaim-fn2-txn fn2-txn-wake-upload))
  (b* ((gen row-generation) (u row-upload)
       (retire (>= gen (fn2-machine-gen-limit fn2-core)))
       (next (fn2-machine-free-head *fn2-txn-admission-ordinal* fn2-core))
       (fn2-core (fn2-txn-put-core id
                   (phase (if retire *fn2-txn-state-retired* *fn2-txn-state-free*))
                   (generation (if retire gen (+ 1 gen)))
                   (upload *fn2-none*) (upload-gen 0) (conn *fn2-none*) (conn-gen 0)
                   (next-free next) (wait-reason *fn2-wait-none*)))
       (fn2-core (fn2-machine-reclaim-fn2-txn id retire fn2-core))
       (fn2-core (fn2-txn-wake-upload u id gen fn2-core)))
    (fn2-machine-result 0 *fn2-work-release* 0 nil fn2-core)))
(defmachine-callback fn2-txn-drain fn2-txn (id budget) 4
  (fn2-call fn2-txn-release id budget))

(defmachine-run fn2-txn)
))

; MACHINE-FORM 6.5 P4: the kind's take in child form, proved here;
; the admission section (assembly-callbacks-a) makes its core face.
(defmachine-registry fn2-txn)
