;; The upload machine fn2-upload (layer D, quest D4; ROUND2 section B.2
;; row 3). The design is fn2/docs/d-machines-nntp.md section 14.3. An upload
;; row is taken by a connection that opens an article block (POST after 340,
;; IHAVE after 335, TAKETHIS at once) with its window: two chunk slots of the
;; chunk class and the BLAKE3 hasher row 3 + its slot (B-S1). The
;; connection's feed writes the unstuffed source into the chunks
;; (upload-feed.lisp) and reports what it wrote (fn2-upload-input); the
;; upload's own runs hash it and scan its header (upload-scan.lisp), at most
;; 4 KiB per run, and once the terminator was framed and every octet is
;; hashed it gives its verdict and posts the word to its connection.
;; Registration book: assembly-index includes it after conn; its
;; continuations are materialized by assembly-callbacks-d.lisp.
(in-package "ACL2")
(include-book "machines-a")
(include-book "machines-b")
(include-book "conn")
(include-book "profile")
(include-book "upload-scan")
(include-book "upload-feed")
(include-book "blake3")
(fn2-book-layer :d)

;; The run quantum, split statically: at most *fn2-upload-hash-bytes* hashed
;; and *fn2-upload-scan-bytes* of header scanned per run.
(defconst *fn2-upload-hash-bytes* 2048)
(defconst *fn2-upload-scan-bytes* 2048)
(defconst *fn2-upload-run-bytes* (+ *fn2-upload-hash-bytes* *fn2-upload-scan-bytes*))
;; The pool class of a chunk (the profile's second class: 64 KiB in the
;; concrete profile) and the article bound when the profile names none
;; (fn1's source bound, specs/article-parser.md).
(defconst *fn2-upload-chunk-class* 1)
;; Large-upload windows (ROUND2 B.1): an upload holds one while it streams.
(defconst *fn2-upload-windows* 16)
(defconst *fn2-upload-article-max* 32768)
;; The source's content identity (BLAKE3, 32 octets) is appended to the
;; window right after the source at the verdict, for C's offer and the
;; article row (a pool workspace is written at its fill): in chunk 0 when it
;; fits there, else in chunk 1. The bound leaves its room in chunk 1.
(defconst *fn2-upload-digest-octets* 32)
;; Where it goes for a source of FILLED octets: (mv in1 off), IN1 true for
;; chunk 1.
(defun fn2-upload-digest-at (filled cap0)
  (declare (xargs :guard (and (natp filled) (natp cap0))))
  (cond ((<= (+ filled *fn2-upload-digest-octets*) cap0) (mv nil filled))
        ((<= filled cap0) (mv t 0))
        (t (mv t (- filled cap0)))))
(defthm fn2-upload-digest-at-natp
  (implies (and (natp filled) (natp cap0)) (natp (mv-nth 1 (fn2-upload-digest-at filled cap0))))
  :rule-classes :type-prescription)
;; Words an upload or a transaction posts to its connection (section 14.5),
;; by name; 0 is none.
(defconst *fn2-upload-words*
  '(:none :accepted :uncertain :duplicate :conflict :too-large :malformed :framing :line-length
    :header-fields :header-lines :header-octets :missing :duplicate-field :path :message-id :mismatch
    :injected :no-clock :group :identity-conflict-bound :unaffordable :control-malformed :refused :not-stored
    ;; the verdict's :missing, :duplicate-field and :injected by field (the catalogue's rows)
    :from-missing :subject-missing :newsgroups-missing :from-duplicate :subject-duplicate
    :newsgroups-duplicate :message-id-duplicate :date-duplicate :path-duplicate :xref :injection-info
    :injection-date))
;; The verdict's word refined by field, in the order the model checks them.
(defun fn2-upload-word-by-field (word seen)
  (declare (xargs :guard (natp seen)))
  (cond ((eq word :missing)
           (cond ((not (fn2-upload-bit seen *fn2-upload-field-from*)) :from-missing)
                 ((not (fn2-upload-bit seen *fn2-upload-field-subject*)) :subject-missing)
                 ((not (fn2-upload-bit seen *fn2-upload-field-ng*)) :newsgroups-missing)
                 (t :missing)))
          ((eq word :duplicate-field)
           (cond ((fn2-upload-bit seen (+ *fn2-upload-seen-dup* *fn2-upload-field-from*)) :from-duplicate)
                 ((fn2-upload-bit seen (+ *fn2-upload-seen-dup* *fn2-upload-field-subject*)) :subject-duplicate)
                 ((fn2-upload-bit seen (+ *fn2-upload-seen-dup* *fn2-upload-field-ng*)) :newsgroups-duplicate)
                 ((fn2-upload-bit seen (+ *fn2-upload-seen-dup* *fn2-upload-field-mid*)) :message-id-duplicate)
                 ((fn2-upload-bit seen (+ *fn2-upload-seen-dup* *fn2-upload-field-date*)) :date-duplicate)
                 (t :path-duplicate)))
          ((eq word :injected)
           (cond ((fn2-upload-bit seen *fn2-upload-field-xref*) :xref)
                 ((fn2-upload-bit seen *fn2-upload-field-injection-info*) :injection-info)
                 (t :injection-date)))
          (t word)))
(defun fn2-upload-word-code (word)
  (declare (xargs :guard t))
  (let ((tail (member-eq word *fn2-upload-words*)))
    (if tail (- (len *fn2-upload-words*) (len tail)) 0)))
(defun fn2-upload-word-of (code)
  (declare (xargs :guard (natp code)))
  (if (< code (len *fn2-upload-words*)) (nth code *fn2-upload-words*) :none))

;; The input configuration (a D core child, one row): whether posting is
;; served under the interim (section 14.5: the public capability stays off
;; until a POST can succeed; tests set :posting-interim) and the article
;; bound.
(defcolumns fn2-input-config ((posting :bool) (article-max :u32)))
(defun fn2-input-config-profilep (profile)
  (declare (xargs :guard t))
  (and (booleanp (fn2-profile-get :posting-interim profile))
       ;; article input needs the chunk class and a hasher row per window
       (or (not (fn2-profile-get :posting-interim profile))
           (and (true-listp (fn2-profile-get :pool-classes profile))
                (< *fn2-upload-chunk-class* (len (fn2-profile-get :pool-classes profile)))
                (< 0 (fn2-b-upload-windows profile))))
       (or (null (fn2-profile-get :article-max profile))
           (unsigned-byte-p 32 (fn2-profile-get :article-max profile)))))
(defun fn2-input-config-from (profile fn2-input-config)
  (declare (xargs :stobjs fn2-input-config :guard (fn2-input-config-profilep profile)))
  (let* ((fn2-input-config (fn2-input-config-init 1 fn2-input-config))
         (max (fn2-profile-get :article-max profile)))
    (fn2-input-config-put 0 (posting (if (fn2-profile-get :posting-interim profile) 1 0))
                          (article-max (if (unsigned-byte-p 32 max) max *fn2-upload-article-max*)))))
(defthm fn2-input-config-from-type
  (implies (fn2-input-configp fn2-input-config)
           (fn2-input-configp (fn2-input-config-from profile fn2-input-config))))
(defthm fn2-input-config-from-wfp
  (fn2-input-config-wfp (fn2-input-config-from profile fn2-input-config)))
(in-theory (disable fn2-input-config-from fn2-input-config-profilep))
(defcorechild fn2-core-input-config fn2-input-config
 :init (fn2-input-config-from profile fn2-input-config) :profilep (fn2-input-config-profilep profile)
 :why "The node's article-input settings: the posting switch and the article bound, read by the connection and the upload.")

;; One row per window, and none unless the profile serves article input
;; (B-S1: hasher rows 3 .. 2+w of fn2-b3 are the windows', B's row map). Opaque to the
;; directory's proofs (a capacity is a natural).
(defun fn2-upload-capacity (profile)
  (declare (xargs :guard t))
  (if (fn2-profile-get :posting-interim profile)
      (min (min (nfix (fn2-profile-u profile)) *fn2-upload-windows*)
           (fn2-b-upload-windows profile))
    0))
(defthm fn2-upload-capacity-natp (natp (fn2-upload-capacity profile)) :rule-classes :type-prescription)
(in-theory (disable fn2-upload-capacity))

(defmachine fn2-upload
 :states (:free :head :identity :receiving :validating :discard :sealed :aborting :draining :retired)
 :fields ((conn :link) (conn-gen :u60) (request :u32)
          (rule (:enum fn2-upload-rule (:post :ihave :takethis)))
          (c0-slot :link) (c0-gen :u60) (c1-slot :link) (c1-gen :u60)
          (filled :u60) (hashed :u60)
          (scan-off :u32) (ofield :u8) (visible :bool) (nfields :u16) (nlines :u16) (seen :u32)
          (mo :u32) (ml :u32) (no :u32) (nl :u32) (po :u32) (pl :u32)
          (head-status (:enum fn2-upload-head (:scanning :done :malformed :line-length :header-fields
                                                :header-lines :header-octets)))
          (word :u8) (inj :u8) (txn :link) (txn-gen :u60) (stopped :bool) (next-free :link))
 :holds ((:head :upload-row :chunk-window) (:identity :upload-row :chunk-window)
         (:receiving :upload-row :chunk-window) (:validating :upload-row :chunk-window)
         (:discard :upload-row :chunk-window) (:sealed :upload-row :chunk-window)
         (:aborting :upload-row :chunk-window) (:draining :upload-row :chunk-window))
 :budget (:bytes 4096 :steps 32 :descriptors 4)
 :capacity (fn2-upload-capacity profile)
 ;; A connection takes the row with its two chunks (A-S7).
 :taken (:phase :head :rows :upload-row
         :ranges ((:chunk-window :slot c0-slot :gen c0-gen :class 1)
                  (:chunk-window :slot c1-slot :gen c1-gen :class 1))
         :copy (conn conn-gen request rule principal-slot)
         :clear (filled hashed scan-off visible nfields nlines seen mo ml no nl po pl
                 head-status word inj txn-gen stopped))
 :initial ((generation fn2-machine-initial-generation) (ready-prev *fn2-none*) (ready-next *fn2-none*)
           (c0-slot *fn2-none*) (c1-slot *fn2-none*) (conn *fn2-none*) (txn *fn2-none*) (account-ref *fn2-none*)
           (ofield 12) (next-free fn2-machine-initial-next-free))
 :continuations
 ((:free fn2-upload-idle :cost (:steps (:cost fn2-machine-idle :steps)) :writes () :next (:free)
   :uses (fn2-machine-idle))
  (:head fn2-upload-work :cost (:bytes *fn2-upload-run-bytes* :steps *fn2-work-transition*)
   :writes (hashed scan-off ofield visible nfields nlines seen mo ml no nl po pl head-status word inj)
   :tables (fn2-core-b3 fn2-core-digests fn2-core-machines fn2-core-machine-tables fn2-core-pool)
   :next (:head :identity :receiving :validating :discard :sealed :aborting :draining)
   :uses (fn2-upload-advance fn2-machine-refuse-phase))
  ;; the header is complete: take the transaction (bundle :transaction :admit)
  (:identity fn2-upload-claim :cost (:steps *fn2-work-transition*)
   :writes (txn txn-gen wait-reason)
   :tables (fn2-core-machines fn2-core-pool fn2-txn-table fn2-core-machine-tables)
   :next (:identity :receiving :aborting) :uses (fn2-machine-take-fn2-txn fn2-upload-conn-live-p fn2-txn-gen-of))
  (:receiving fn2-upload-work :cost (:bytes *fn2-upload-run-bytes* :steps *fn2-work-transition*)
   :writes (hashed scan-off ofield visible nfields nlines seen mo ml no nl po pl head-status word inj)
   :tables (fn2-core-b3 fn2-core-digests fn2-core-machines fn2-core-machine-tables fn2-core-pool)
   :next (:receiving :validating :discard :sealed :aborting :draining) :uses (fn2-upload-advance fn2-machine-refuse-phase))
  (:validating fn2-upload-work :cost (:bytes *fn2-upload-run-bytes* :steps *fn2-work-transition*)
   :writes (hashed scan-off ofield visible nfields nlines seen mo ml no nl po pl head-status word inj)
   :tables (fn2-core-b3 fn2-core-digests fn2-core-machines fn2-core-machine-tables fn2-core-pool)
   :next (:validating :sealed :aborting :draining) :uses (fn2-upload-advance fn2-machine-refuse-phase))
  (:discard fn2-upload-work :cost (:bytes *fn2-upload-run-bytes* :steps *fn2-work-transition*)
   :writes (hashed scan-off ofield visible nfields nlines seen mo ml no nl po pl head-status word inj)
   :tables (fn2-core-b3 fn2-core-digests fn2-core-machines fn2-core-machine-tables fn2-core-pool)
   :next (:discard :sealed :aborting :draining) :uses (fn2-upload-advance fn2-machine-refuse-phase))
  ;; its transaction holds the octets (the Message-ID, the digest, the
  ;; source) until its outcome, then lets it drain
  (:sealed fn2-upload-hold :cost (:steps *fn2-work-transition*) :writes ()
   :next (:sealed :draining) :uses (fn2-upload-txn-live-p))
  (:aborting fn2-upload-abort :cost (:steps *fn2-work-transition*) :writes () :tables (fn2-core-machines)
   :next (:aborting :draining) :uses (fn2-upload-txn-live-p fn2-upload-wake))
  (:draining fn2-upload-drain :cost (:steps (:cost fn2-upload-release :steps))
   :writes (generation c0-slot c0-gen c1-slot c1-gen conn conn-gen filled hashed txn next-free wait-reason)
   :tables (fn2-core-pool fn2-core-machines)
   :next (:free :retired) :uses (fn2-upload-release))
  (:retired fn2-upload-idle :cost (:steps (:cost fn2-machine-idle :steps)) :writes () :next (:retired)
   :uses (fn2-machine-idle))))

(defcost fn2-conn-feed-run :bytes *fn2-conn-feed-cost* :tables (fn2-core-pool)
  :doc "Feed RX into the upload's chunk (upload-feed.lisp).")
(defcost fn2-conn-wake :tables (fn2-core-machines) :doc "Wake the upload this connection feeds.")
(defcost fn2-upload-gen-of :doc "An upload row's generation.")
;; Declared costs of the upload's outside calls (each a thin wrapper below).
(defcost fn2-upload-hash-step :bytes *fn2-upload-hash-bytes* :tables (fn2-core-b3 fn2-core-digests)
  :doc "BLAKE3 over one range of a chunk into the upload's hasher row (B's fn2-b3-update).")
(defcost fn2-upload-hash-begin :tables (fn2-core-b3 fn2-core-digests) :doc "Start the hasher row.")
(defcost fn2-upload-hash-end :tables (fn2-core-digests) :doc "Finalize the digest into the hasher row's result slot.")
(defcost fn2-upload-scan-step :bytes *fn2-upload-scan-bytes* :doc "Advance the header scan over chunk 0.")
(defcost fn2-upload-verdict-step :bytes 512 :doc "The definite verdict over the scanned header.")
(defcost fn2-upload-chunk-cap :doc "A chunk's capacity.")
(defcost fn2-upload-bound :doc "The article bound (the input configuration, at most two chunks).")
(defcost fn2-conn-post-word :tables (fn2-conn-table fn2-core-machines)
  :doc "Post an outcome word to the connection that awaits it (generation and request checked); wake it.")
(defcost fn2-upload-advance :bytes *fn2-upload-run-bytes* :steps *fn2-work-transition*
  :tables (fn2-core-b3 fn2-core-digests fn2-core-machines fn2-core-machine-tables fn2-core-pool)
  :own-writes (hashed scan-off ofield visible nfields nlines seen mo ml no nl po pl head-status word inj)
  :doc "One run of an upload's work: hash, scan, and at the end the verdict posted to its connection (or handed to its transaction); returns the phase to move to.")
(defcost fn2-txn-gen-of :doc "A transaction row's generation.")
(defcost fn2-upload-conn-live-p :doc "Whether the connection still feeds this upload.")
(defcost fn2-upload-txn-live-p :doc "Whether the upload's transaction still names it.")
(defcost fn2-upload-wake :tables (fn2-core-machines) :doc "Wake the upload's transaction.")

;; ------------------------------------------------------------------------
;; The operations both machines call, materialized after the core instance
;; and before the connection's continuations (assembly-callbacks-d.lisp).
(defmacro fn2-upload-op-events ()
 '(progn
(defun fn2-upload-hasher (id fn2-core)
  ;; the hasher row of the upload row ID: 3 + its slot (B-S1: rows 0-1 the
  ;; commit kind's, row 2 recovery's checker)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (eq (fn2-upload-snapshot-read-code id fn2-core) :ok) (+ 3 (nfix (fn2-machine-slot id fn2-core))) 0))
(defun fn2-upload-hash-begin (row fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-b3 (fn2-core-b3 fn2-core)) (fn2-digests (fn2-core-digests fn2-core)))
    (code fn2-digests fn2-b3)
    (if (and (natp row) (fn2-b3-ready row fn2-b3 fn2-digests) (fn2-digest-rowp (fn2-digest-slot row *fn2-b3-key*) fn2-digests))
        (mv-let (fn2-digests fn2-b3) (fn2-b3-init row 0 (fn2-digest-slot row *fn2-b3-key*) fn2-digests fn2-b3)
          (mv :ok fn2-digests fn2-b3))
      (mv :bounds fn2-digests fn2-b3))
    (mv code fn2-core)))
(fn2-core-preserves fn2-upload-hash-begin (row fn2-core) :position 1 :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))
(defun fn2-upload-hash-step (row slot gen off len id ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-b3 (fn2-core-b3 fn2-core)) (fn2-digests (fn2-core-digests fn2-core)) (fn2-pool (fn2-core-pool fn2-core)))
    (code consumed fn2-digests fn2-b3)
    (if (and (fn2-b3-ready row fn2-b3 fn2-digests) (fn2-pool-wfp fn2-pool)
             (unsigned-byte-p 32 off) (unsigned-byte-p 32 len))
        (fn2-b3-update row slot gen off len *fn2-upload-kind* id ogen fn2-digests fn2-b3 fn2-pool)
      (mv :bounds 0 fn2-digests fn2-b3))
    (mv code (nfix consumed) fn2-core)))
(fn2-core-preserves fn2-upload-hash-step (row slot gen off len id ogen fn2-core) :position 2 :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))
(defun fn2-upload-hash-end (row fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-b3 (fn2-core-b3 fn2-core)) (fn2-digests (fn2-core-digests fn2-core)))
    (code fn2-digests)
    (let ((dst (fn2-digest-slot (nfix row) *fn2-b3-result*)))
      (if (and (natp row) (fn2-b3-ready row fn2-b3 fn2-digests) (fn2-digest-rowp dst fn2-digests))
          (let ((fn2-digests (fn2-b3-finalize dst row fn2-digests fn2-b3))) (mv :ok fn2-digests))
        (mv :bounds fn2-digests)))
    (mv code fn2-core)))
(fn2-core-preserves fn2-upload-hash-end (row fn2-core) :position 1 :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))
(defun fn2-upload-chunk-cap (slot fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (n) (fn2-feed-cap slot fn2-pool) (nfix n)))
(defun fn2-upload-bound (cap0 cap1 fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-input-config (fn2-core-input-config fn2-core)))
    (max)
    (if (and (fn2-input-config-wfp fn2-input-config) (natp (fn2-input-config-rows fn2-input-config))
             (< 0 (fn2-input-config-rows fn2-input-config)))
        (fn2-input-config-article-max 0 fn2-input-config) 0)
    (min (nfix max) (nfix (- (+ (nfix cap0) (nfix cap1)) (+ 1 *fn2-upload-digest-octets*))))))
(defun fn2-upload-scan-step (slot gen off field visible fields lines seen mo ml no nl po pl id ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (status off field visible fields lines seen mo ml no nl po pl)
    (mv-let (status off field visible fields lines seen mo ml no nl po pl spent)
      (fn2-upload-scan *fn2-upload-scan-bytes* (nfix off) (nfix field) visible (nfix fields) (nfix lines) (nfix seen)
                       (nfix mo) (nfix ml) (nfix no) (nfix nl) (nfix po) (nfix pl) slot gen *fn2-upload-kind* id ogen fn2-pool)
      (declare (ignore spent))
      (mv status off field visible fields lines seen mo ml no nl po pl))
    (mv status off field visible fields lines seen mo ml no nl po pl)))
(defun fn2-upload-verdict-step (rule status seen mo ml po pl len bound slot gen id ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (word injected)
    (fn2-upload-verdict rule status (nfix seen) (nfix mo) (nfix ml) (nfix po) (nfix pl) (nfix len) (nfix bound)
                        *fn2-none* 0 0 0 0 0 0 slot gen *fn2-upload-kind* id ogen fn2-pool)
    (mv word injected)))
(in-theory (disable fn2-upload-hasher fn2-upload-hash-begin fn2-upload-hash-step fn2-upload-hash-end
                    fn2-upload-chunk-cap fn2-upload-bound fn2-upload-scan-step fn2-upload-verdict-step))


;; The head status as the scan's keyword.
(defun fn2-upload-head-keyword (hs)
  (declare (xargs :guard t))
  (cond ((equal hs *fn2-upload-head-done*) :header-done) ((equal hs *fn2-upload-head-malformed*) :malformed)
        ((equal hs *fn2-upload-head-line-length*) :line-length) ((equal hs *fn2-upload-head-header-fields*) :header-fields)
        ((equal hs *fn2-upload-head-header-lines*) :header-lines) ((equal hs *fn2-upload-head-header-octets*) :header-octets)
        (t :more)))
(defun fn2-upload-head-code (st)
  (declare (xargs :guard t))
  (case st (:header-done *fn2-upload-head-done*) (:malformed *fn2-upload-head-malformed*)
    (:line-length *fn2-upload-head-line-length*) (:header-fields *fn2-upload-head-header-fields*)
    (:header-lines *fn2-upload-head-header-lines*) (:header-octets *fn2-upload-head-header-octets*)
    (otherwise *fn2-upload-head-scanning*)))
;; Cross-row: an upload posts its word to its connection. The connection may
;; have moved on (closed, reused): the word is then dropped, the one place a
;; word is legitimately not delivered (section 14.4).
(defun fn2-conn-post-word (conn conn-gen request word fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (not (and (eq (fn2-conn-snapshot-read-code conn fn2-core) :ok) (unsigned-byte-p 8 word)
                (equal (fn2-machine-generation conn fn2-core) conn-gen)
                (equal (fn2-conn-row-request conn fn2-core) request)
                (equal (fn2-conn-row-phase conn fn2-core) *fn2-conn-state-article-input*)))
      (mv :dropped fn2-core)
    (let* ((fn2-core (fn2-machine-write-word conn word fn2-core))
           (fn2-core (fn2-machine-write-outcome-ready conn 1 fn2-core))
           (fn2-core (fn2-machine-set-wake-id conn fn2-core)))
      (mv :ok fn2-core))))
(fn2-core-preserves fn2-conn-post-word (conn conn-gen request word fn2-core) :position 1 :rows nil)

;; The upload's work, in stages each with its own preservation facts (a
;; single body with every stage inline costs minutes to prove).
;; Hash one step of [hashed, filled): (mv code hashed fn2-core).
(defun fn2-upload-hash-run (id gen row c0 g0 c1 g1 cap0 hashed filled fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (natp cap0) (natp hashed) (natp filled))))
  (b* (((unless (< hashed filled)) (mv :ok hashed fn2-core))
       ((mv hcode fn2-core) (if (equal hashed 0) (fn2-upload-hash-begin row fn2-core) (mv :ok fn2-core)))
       ((unless (eq hcode :ok)) (mv hcode hashed fn2-core))
       (in0 (< hashed cap0))
       (room (if in0 (- cap0 hashed) (- filled hashed)))
       (hlen (min *fn2-upload-hash-bytes* (min (- filled hashed) room)))
       ((mv scode consumed fn2-core)
        (fn2-upload-hash-step row (if in0 c0 c1) (if in0 g0 g1) (if in0 hashed (- hashed cap0)) hlen id gen fn2-core)))
    (if (or (eq scode :ok) (eq scode :more)) (mv :ok (+ hashed (nfix consumed)) fn2-core) (mv scode hashed fn2-core))))
(fn2-core-preserves fn2-upload-hash-run (id gen row c0 g0 c1 g1 cap0 hashed filled fn2-core) :position 2 :rows nil)
;; Advance the header scan over chunk 0 and store its state: (mv status hs fn2-core).
(defun fn2-upload-scan-run (id gen c0 g0 fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* (((unless (eq (fn2-upload-snapshot-read-code id fn2-core) :ok)) (mv :fault 0 fn2-core))
       (hs (fn2-upload-row-head-status id fn2-core))
       ((unless (equal hs *fn2-upload-head-scanning*)) (mv :skip hs fn2-core))
       ((mv st off field visible fields lines seen mo ml no nl po pl)
        (fn2-upload-scan-step c0 g0 (fn2-upload-row-scan-off id fn2-core) (fn2-upload-row-ofield id fn2-core)
                              (equal (fn2-upload-row-visible id fn2-core) 1)
                              (fn2-upload-row-nfields id fn2-core) (fn2-upload-row-nlines id fn2-core)
                              (fn2-upload-row-seen id fn2-core) (fn2-upload-row-mo id fn2-core) (fn2-upload-row-ml id fn2-core)
                              (fn2-upload-row-no id fn2-core) (fn2-upload-row-nl id fn2-core)
                              (fn2-upload-row-po id fn2-core) (fn2-upload-row-pl id fn2-core) id gen fn2-core))
       (hs (fn2-upload-head-code st))
       ((unless (and (not (eq st :fault)) (unsigned-byte-p 32 off) (unsigned-byte-p 8 field) (unsigned-byte-p 16 fields)
                     (unsigned-byte-p 16 lines) (unsigned-byte-p 32 seen) (unsigned-byte-p 32 mo) (unsigned-byte-p 32 ml)
                     (unsigned-byte-p 32 no) (unsigned-byte-p 32 nl) (unsigned-byte-p 32 po) (unsigned-byte-p 32 pl)))
        (mv :fault hs fn2-core))
       (fn2-core (fn2-machine-write-scan-off id off fn2-core))
       (fn2-core (fn2-machine-write-ofield id field fn2-core))
       (fn2-core (fn2-machine-write-visible id (if visible 1 0) fn2-core))
       (fn2-core (fn2-machine-write-nfields id fields fn2-core))
       (fn2-core (fn2-machine-write-nlines id lines fn2-core))
       (fn2-core (fn2-machine-write-seen id seen fn2-core))
       (fn2-core (fn2-machine-write-mo id mo fn2-core))
       (fn2-core (fn2-machine-write-ml id ml fn2-core))
       (fn2-core (fn2-machine-write-no id no fn2-core))
       (fn2-core (fn2-machine-write-nl id nl fn2-core))
       (fn2-core (fn2-machine-write-po id po fn2-core))
       (fn2-core (fn2-machine-write-pl id pl fn2-core))
       (fn2-core (fn2-machine-write-head-status id hs fn2-core)))
    (mv st hs fn2-core)))
(fn2-core-preserves fn2-upload-scan-run (id gen c0 g0 fn2-core) :position 2 :rows nil)
;; The block is complete and hashed: the digest, the verdict, the word
;; written to the row and posted to the connection, in three steps each with
;; its own preservation facts (inline they cost two minutes to prove).
;; The digest into the hasher row's result slot: (mv code fn2-core).
(defun fn2-upload-digest (row hashed fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* (((mv bcode fn2-core) (if (equal hashed 0) (fn2-upload-hash-begin row fn2-core) (mv :ok fn2-core))))
    (if (eq bcode :ok) (fn2-upload-hash-end row fn2-core) (mv bcode fn2-core))))
(fn2-core-preserves fn2-upload-digest (row hashed fn2-core) :position 1 :rows nil)
;; The verdict over the scanned header (reads only): (mv ok word inj), WORD
;; the definite refusal's code (0 none) and INJ the injected-field refusal's
;; (0 none), which the transaction applies after identity and group (the
;; model's order); OK nil when the row cannot be read.
(defun fn2-upload-word-now (id gen c0 g0 cap0 cap1 filled fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (natp filled))))
  (if (not (eq (fn2-upload-snapshot-read-code id fn2-core) :ok)) (mv nil 0 0)
    (b* ((seen (fn2-upload-row-seen id fn2-core))
         (rule (case (fn2-upload-row-rule id fn2-core) (0 :post) (1 :ihave) (otherwise :takethis)))
         ((mv word injected)
          (fn2-upload-verdict-step rule (fn2-upload-head-keyword (fn2-upload-row-head-status id fn2-core)) seen
                                   (fn2-upload-row-mo id fn2-core) (fn2-upload-row-ml id fn2-core)
                                   (fn2-upload-row-po id fn2-core) (fn2-upload-row-pl id fn2-core) filled
                                   (fn2-upload-bound cap0 cap1 fn2-core) c0 g0 id gen fn2-core))
         (w (if (eq word :ok) 0 (fn2-upload-word-code (fn2-upload-word-by-field word seen))))
         (inj (if (and (eq word :ok) injected) (fn2-upload-word-code (fn2-upload-word-by-field :injected seen)) 0)))
      (mv (and (unsigned-byte-p 8 w) (unsigned-byte-p 8 inj)) w inj))))
;; The source's content identity appended after the source at SLOT GEN OFF
;; (fn2-upload-digest-at), under this upload's owner.
(defun fn2-upload-digest-store (row slot gen off id ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (natp off))))
  (stobj-let ((fn2-digests (fn2-core-digests fn2-core)) (fn2-pool (fn2-core-pool fn2-core)))
    (code fn2-pool)
    (let ((src (fn2-digest-slot (nfix row) *fn2-b3-result*)))
      (if (and (natp row) (fn2-digest-rowp src fn2-digests) (fn2-pool-wfp fn2-pool))
          (fn2-digest-store *fn2-upload-digest-octets* src slot gen off *fn2-upload-kind* id ogen fn2-digests fn2-pool)
        (mv :bounds fn2-pool)))
    (mv code fn2-core)))
(fn2-core-preserves fn2-upload-digest-store (row slot gen off id ogen fn2-core) :position 1 :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))
;; Wake a row (the upload's transaction).
(defun fn2-upload-wake (x fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (and (unsigned-byte-p 32 x) (not (equal x *fn2-none*)) (fn2-machine-idp x fn2-core))
      (fn2-machine-set-wake-id x fn2-core)
    fn2-core))
(fn2-core-preserves fn2-upload-wake (x fn2-core) :rows nil)
;; The verdict handed to the transaction (it posts the one word): WORD and
;; INJ on this row, the digest stored, the transaction woken.
(defun fn2-upload-hand-over (id w inj txn fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (unsigned-byte-p 8 w) (unsigned-byte-p 8 inj))))
  (b* ((fn2-core (fn2-machine-write-word id w fn2-core))
       (fn2-core (fn2-machine-write-inj id inj fn2-core)))
    (fn2-upload-wake txn fn2-core)))
(fn2-core-preserves fn2-upload-hand-over (id w inj txn fn2-core) :rows nil)
;; The word recorded on the row and posted to the connection.
(defun fn2-upload-deliver-word (id code conn conn-gen request fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (unsigned-byte-p 8 code))))
  (b* ((fn2-core (fn2-machine-write-word id code fn2-core))
       ((mv & fn2-core) (fn2-conn-post-word conn conn-gen request code fn2-core)))
    fn2-core))
(fn2-core-preserves fn2-upload-deliver-word (id code conn conn-gen request fn2-core) :rows nil)
(in-theory (disable fn2-upload-digest fn2-upload-word-now fn2-upload-digest-store fn2-upload-wake fn2-upload-hand-over
                    fn2-upload-deliver-word))
;; The block is complete and hashed: (mv next fn2-core). With a transaction
;; (the header was complete): the digest stored, the verdict handed over,
;; :sealed. Without one (the header was refused): the refusal posted to the
;; connection, :draining; a clean verdict without a transaction is an
;; invariant failure.
(defun fn2-upload-finish (id gen row c0 g0 c1 g1 cap0 cap1 filled hashed conn conn-gen request txn fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (natp filled) (natp cap1))))
  (b* (((mv ecode fn2-core) (fn2-upload-digest row hashed fn2-core))
       ((unless (eq ecode :ok)) (mv :stop fn2-core))
       ((mv ok w inj) (fn2-upload-word-now id gen c0 g0 cap0 cap1 filled fn2-core))
       ((unless (and ok (unsigned-byte-p 8 w) (unsigned-byte-p 8 inj))) (mv :stop fn2-core))
       ((when (equal txn *fn2-none*))
        (if (equal w 0) (mv :stop fn2-core)
          (let ((fn2-core (fn2-upload-deliver-word id w conn conn-gen request fn2-core))) (mv :draining fn2-core))))
       ((mv in1 doff) (fn2-upload-digest-at filled (nfix cap0)))
       ((mv scode fn2-core) (fn2-upload-digest-store row (if in1 c1 c0) (if in1 g1 g0) doff id gen fn2-core))
       ((unless (eq scode :ok)) (mv :stop fn2-core)))
    (let ((fn2-core (fn2-upload-hand-over id w inj txn fn2-core))) (mv :sealed fn2-core))))
(fn2-core-preserves fn2-upload-finish (id gen row c0 g0 c1 g1 cap0 cap1 filled hashed conn conn-gen request txn fn2-core)
  :position 1 :rows nil)
(in-theory (disable fn2-upload-hash-run fn2-upload-scan-run fn2-upload-finish))

;; One run of the upload's work (section 14.3): hash at most
;; *fn2-upload-hash-bytes* of what the connection fed, advance the header
;; scan, and once the terminator was framed and everything is hashed, give
;; the verdict (to the transaction once the header is complete, else as the
;; refusal posted to the connection). Returns (mv next fn2-core), NEXT the
;; phase to move to (:identity :receiving :discard :sealed :aborting
;; :draining), or :run (more to do now), :idle (wait for input), :stop (an
;; invariant failed).
(defun fn2-upload-advance (id fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* (((unless (eq (fn2-upload-snapshot-read-code id fn2-core) :ok)) (mv :stop fn2-core))
       (gen (fn2-machine-generation id fn2-core)) (row (fn2-upload-hasher id fn2-core))
       (c0 (fn2-upload-row-c0-slot id fn2-core)) (g0 (fn2-upload-row-c0-gen id fn2-core))
       (c1 (fn2-upload-row-c1-slot id fn2-core)) (g1 (fn2-upload-row-c1-gen id fn2-core))
       (cap0 (fn2-upload-chunk-cap c0 fn2-core)) (cap1 (fn2-upload-chunk-cap c1 fn2-core))
       (conn (fn2-upload-row-conn id fn2-core)) (conn-gen (fn2-upload-row-conn-gen id fn2-core))
       (request (fn2-upload-row-request id fn2-core))
       (hashed (fn2-upload-row-hashed id fn2-core))
       (txn (fn2-upload-row-txn id fn2-core))
       (ph (fn2-upload-row-phase id fn2-core))
       ;; what the connection fed, read from its row: it has moved on when its
       ;; generation changed or it no longer feeds this row (this generation
       ;; of it). Its phase is not read: the take wakes this row while the
       ;; connection is still sending 340 (:reply), and a closing connection
       ;; keeps its generation until it drains, which wakes this row.
       ((unless (and (eq (fn2-conn-snapshot-read-code conn fn2-core) :ok)
                     (equal (fn2-machine-generation conn fn2-core) conn-gen)
                     (equal (fn2-conn-row-upload conn fn2-core) id)
                     (equal (fn2-conn-row-upload-gen conn fn2-core) gen)))
        (mv :aborting fn2-core))
       (filled (fn2-conn-row-fed conn fn2-core))
       (terminated (equal (fn2-conn-row-feed-mode conn fn2-core) *fn2-conn-feed-done*))
       (discard (fn2-conn-row-feed-discard conn fn2-core))
       ;; a discarded block: nothing to hash; at its terminator, the refusal
       ;; (handed to the transaction when there is one)
       ((unless (equal discard 0))
        (b* (((unless terminated)
              (mv (if (equal ph *fn2-upload-state-discard*) :idle :discard) fn2-core))
             (w (fn2-upload-word-code (if (equal discard 1) :framing :too-large)))
             ((unless (equal txn *fn2-none*)) (let ((fn2-core (fn2-upload-hand-over id w 0 txn fn2-core))) (mv :sealed fn2-core)))
             ((mv & fn2-core) (fn2-conn-post-word conn conn-gen request w fn2-core)))
          (mv :draining fn2-core)))
       ((mv hcode hashed fn2-core) (fn2-upload-hash-run id gen row c0 g0 c1 g1 cap0 hashed filled fn2-core))
       ((unless (and (eq hcode :ok) (unsigned-byte-p 60 hashed))) (mv :stop fn2-core))
       (fn2-core (fn2-machine-write-hashed id hashed fn2-core))
       ((mv st hs fn2-core) (fn2-upload-scan-run id gen c0 g0 fn2-core))
       ((when (eq st :fault)) (mv :stop fn2-core))
       ;; the header is complete: the transaction first (its claim serializes
       ;; same-Message-ID offers before the body is stored)
       ((when (and (equal hs *fn2-upload-head-done*) (equal txn *fn2-none*))) (mv :identity fn2-core))
       ((unless (and terminated (<= filled hashed)))
        (mv (cond ((or (< hashed filled) (eq st :budget)) :run)
                  ((and (not (equal hs *fn2-upload-head-scanning*)) (equal ph *fn2-upload-state-head*)) :receiving)
                  (t :idle))
            fn2-core)))
    (fn2-upload-finish id gen row c0 g0 c1 g1 cap0 cap1 filled hashed conn conn-gen request txn fn2-core)))
(fn2-core-preserves fn2-upload-advance (id fn2-core) :position 1 :rows nil)
;; Whether the connection still feeds this upload (its generation, and it
;; names this row and generation).
(defun fn2-upload-conn-live-p (conn conn-gen id gen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (and (eq (fn2-conn-snapshot-read-code conn fn2-core) :ok)
       (equal (fn2-machine-generation conn fn2-core) conn-gen)
       (equal (fn2-conn-row-upload conn fn2-core) id)
       (equal (fn2-conn-row-upload-gen conn fn2-core) gen)))
;; Whether the transaction TXN (of generation TGEN) still names this upload:
;; it lets go of it at its outcome.
(defun fn2-upload-txn-live-p (txn tgen id fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (and (eq (fn2-txn-snapshot-read-code txn fn2-core) :ok)
       (equal (fn2-machine-generation txn fn2-core) tgen)
       (equal (fn2-txn-row-upload txn fn2-core) id)))
(defun fn2-txn-gen-of (txn fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (eq (fn2-txn-snapshot-read-code txn fn2-core) :ok) (fn2-machine-generation txn fn2-core) 0))
(in-theory (disable fn2-upload-conn-live-p fn2-upload-txn-live-p fn2-txn-gen-of))
))

;; ------------------------------------------------------------------------
;; The upload's continuations (materialized after the connection's).
(defmacro fn2-upload-events ()
 '(progn
(defmachine-callback fn2-upload-idle fn2-upload (id budget) 4
  (fn2-machine-idle id fn2-core))
;; :aborting: the connection left. A transaction that still names this row
;; holds its octets: wake it (it finishes without a word) and wait for it to
;; let go; then drain.
(defmachine-callback fn2-upload-abort fn2-upload (id budget) 4
  (if (fn2-upload-txn-live-p row-txn row-txn-gen id fn2-core)
      (let ((fn2-core (fn2-upload-wake row-txn fn2-core)))
        (fn2-machine-result 0 *fn2-work-transition* 0 nil fn2-core))
    (let ((fn2-core (fn2-upload-put-core id (phase *fn2-upload-state-draining*))))
      (fn2-machine-result 0 *fn2-work-transition* 0 t fn2-core))))
;; :sealed: wait for the transaction's outcome, then drain.
(defmachine-callback fn2-upload-hold fn2-upload (id budget) 4
  (if (fn2-upload-txn-live-p row-txn row-txn-gen id fn2-core)
      (fn2-machine-result 0 *fn2-work-transition* 0 nil fn2-core)
    (let ((fn2-core (fn2-upload-put-core id (phase *fn2-upload-state-draining*))))
      (fn2-machine-result 0 *fn2-work-transition* 0 t fn2-core))))
;; :identity: take the transaction row (A-S7), the transaction's copies this
;; row's; refused, the take parked this row on the transaction kind's FIFO
;; and its grant runs this arm again. The connection gone: abort.
(defmachine-callback fn2-upload-claim fn2-upload (id budget) 4
  (if (not (fn2-upload-conn-live-p row-conn row-conn-gen id row-generation fn2-core))
      (let ((fn2-core (fn2-upload-put-core id (phase *fn2-upload-state-aborting*))))
        (fn2-machine-result 0 *fn2-work-transition* 0 t fn2-core))
    (mv-let (code tid tgen fn2-core)
      (fn2-machine-take-fn2-txn id id row-generation row-conn row-conn-gen row-request row-rule row-principal-slot fn2-core)
      (if (eq code :ok)
          (let ((fn2-core (fn2-upload-put-core id (phase *fn2-upload-state-receiving*) (txn tid)
                                               (txn-gen tgen))))
            (fn2-machine-result 0 *fn2-work-transition* 0 t fn2-core))
        (fn2-machine-result 0 *fn2-work-transition* 0 nil fn2-core)))))

;; :head, :receiving, :validating, :discard: one run of the work.
(defmachine-callback fn2-upload-work fn2-upload (id budget) 4
  (fn2-machine-with-work *fn2-upload-run-bytes* *fn2-work-transition* 0
    (mv-let (next fn2-core) (fn2-upload-advance id fn2-core)
      (case next
        (:run (fn2-machine-result *fn2-upload-run-bytes* *fn2-work-transition* 0 t fn2-core))
        (:idle (fn2-machine-result *fn2-upload-run-bytes* *fn2-work-transition* 0 nil fn2-core))
        (:identity (let ((fn2-core (fn2-upload-put-core id (phase *fn2-upload-state-identity*))))
                     (fn2-machine-result *fn2-upload-run-bytes* *fn2-work-transition* 0 t fn2-core)))
        (:receiving (let ((fn2-core (fn2-upload-put-core id (phase *fn2-upload-state-receiving*))))
                      (fn2-machine-result *fn2-upload-run-bytes* *fn2-work-transition* 0 t fn2-core)))
        (:sealed (let ((fn2-core (fn2-upload-put-core id (phase *fn2-upload-state-sealed*))))
                   (fn2-machine-result *fn2-upload-run-bytes* *fn2-work-transition* 0 nil fn2-core)))
        (:discard (let ((fn2-core (fn2-upload-put-core id (phase *fn2-upload-state-discard*))))
                    (fn2-machine-result *fn2-upload-run-bytes* *fn2-work-transition* 0 nil fn2-core)))
        (:aborting (let ((fn2-core (fn2-upload-put-core id (phase *fn2-upload-state-aborting*))))
                     (fn2-machine-result *fn2-upload-run-bytes* *fn2-work-transition* 0 t fn2-core)))
        (:draining (let ((fn2-core (fn2-upload-put-core id (phase *fn2-upload-state-draining*))))
                     (fn2-machine-result *fn2-upload-run-bytes* *fn2-work-transition* 0 t fn2-core)))
        (otherwise (fn2-machine-refuse-phase id fn2-core))))))

;; :draining releases the second chunk, then the first, then the row.
(defmachine-callback fn2-upload-release fn2-upload (id budget) 4
  :contract (:cost (:steps *fn2-work-release*)
             :writes (generation c0-slot c0-gen c1-slot c1-gen conn conn-gen filled hashed txn next-free wait-reason)
             :tables (fn2-core-pool fn2-core-machines) :next (:free :retired)
             :uses ((fn2-core-release :effects ((:release (:chunk-window))))
                    fn2-machine-gen-limit fn2-machine-free-head fn2-machine-reclaim-fn2-upload fn2-core-stop))
  (b* ((kind *fn2-upload-kind*) (gen row-generation)
       ((mv c1code fn2-core) (fn2-core-release row-c1-slot row-c1-gen kind id gen fn2-core))
       ((mv c0code fn2-core) (fn2-core-release row-c0-slot row-c0-gen kind id gen fn2-core)))
    (if (not (and (or (eq c1code :ok) (eq c1code :retired)) (or (eq c0code :ok) (eq c0code :retired))))
        (let ((fn2-core (fn2-core-stop *fn2-stop-reason-pool-release* fn2-core)))
          (fn2-machine-result 0 *fn2-work-state* 0 nil fn2-core))
      (b* ((retire (>= gen (fn2-machine-gen-limit fn2-core)))
           (next (fn2-machine-free-head *fn2-upload-admission-ordinal* fn2-core))
           (fn2-core (fn2-upload-put-core id
                       (phase (if retire *fn2-upload-state-retired* *fn2-upload-state-free*))
                       (generation (if retire gen (+ 1 gen)))
                       (c0-slot *fn2-none*) (c0-gen 0) (c1-slot *fn2-none*) (c1-gen 0)
                       (conn *fn2-none*) (conn-gen 0) (filled 0) (hashed 0) (txn *fn2-none*)
                       (next-free next) (wait-reason *fn2-wait-none*)))
           (fn2-core (fn2-machine-reclaim-fn2-upload id retire fn2-core)))
        (fn2-machine-result 0 *fn2-work-release* 0 nil fn2-core)))))
(defmachine-callback fn2-upload-drain fn2-upload (id budget) 4
  (fn2-call fn2-upload-release id budget))

(defmachine-run fn2-upload)
))
