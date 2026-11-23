;; The transaction machine fn2-txn (layer D, quest D5; ROUND2 section B.2
;; row 4). The design is docs/d-machines-nntp.md section 14.4. An upload
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
(include-book "txn-kind")
(include-book "upload")
(include-book "upload-stream")
(include-book "pool-copy")
(fn2-book-layer :d)

;; The claim walk's chain steps per run: each step compares at most one
;; Message-ID (250 octets) on an equal hash and length, so 16 steps stay
;; within the 4 KiB comparison bound of ROUND2 B.3.
(defconst *fn2-txn-claim-steps* 16)
;; Body lines counted per :prepare run (one pool read each).
(defconst *fn2-txn-count-bytes* 2048)
;; The schemas a POST writes (identity.lisp, ordered.lisp) and its write
;; slots (C-S3): the identity admission (C §4a: the evidence, the history
;; entry, the summary's and the candidate's :admit, the article index), the
;; article row, the operation outcome, then one group-count accept and
;; overview row per carried group up to the profile's :max-groups-per-article
;; (fn2-txn-groups-limit, bounded by *fn2-txn-groups-max* in txn-kind.lisp),
;; skipping *fn2-txn-slot-depend* (authority.lisp's read-dependency slot).
(defconst *fn2-txn-slot-evidence* 0)
(defconst *fn2-txn-slot-history* 1)
(defconst *fn2-txn-slot-summary* 2)
(defconst *fn2-txn-slot-candidate* 3)
(defconst *fn2-txn-slot-index* 4)
(defconst *fn2-txn-slot-article* 5)
(defconst *fn2-txn-slot-outcome* 6)
(defconst *fn2-txn-slot-addr* 7)

(defun fn2-txn-group-slot (k)
  (declare (xargs :guard (natp k)))
  (let ((s (+ *fn2-txn-slot-accepts* (* 2 (nfix k)))))
    (if (< s *fn2-txn-slot-depend*) s (+ 1 s))))
(defthm fn2-txn-group-slot-natp
  (natp (fn2-txn-group-slot k))
  :rule-classes :type-prescription)
;; The article row's values: a born article is live, version 1; the
;; operation outcome recorded with it is accepted (it is bound only into the
;; batch that accepts it).
(defconst *fn2-txn-article-live* 0)
(defconst *fn2-txn-article-version* 1)
;; Newsgroups is scanned at most this many octets per :prepare run.
(defconst *fn2-txn-scan-bytes* 1024)

;; The :ready transition's byte bound: C-S3's stage, the overview line's
;; Xref field (fn2-txn-xref, preflighted 2 KiB), emit and bind and B's admission happen
;; in one run (nothing may stage or bind between a transaction's stage and
;; its bind), so the run's bound is their sum, above ROUND2 B.3's 4 KiB (a
;; departure recorded in the layer doc, 14.4).
(defconst *fn2-txn-admit-bytes* 4096)
(defconst *fn2-txn-xref-bytes* 2048)
(defconst *fn2-txn-result-copy-bytes* (+ 512 (* 2 *fn2-overview-octets-max*)))
(defconst *fn2-txn-ready-bytes* (+ 4096 8192 8192 *fn2-txn-xref-bytes* *fn2-txn-admit-bytes*))
(assert-event (equal *fn2-txn-ready-bytes* 26624))  ; the kind's :budget (txn-kind.lisp)

(defconst *fn2-upload-word-duplicate* (fn2-upload-word-code :duplicate))
(defconst *fn2-upload-word-group* (fn2-upload-word-code :group))
(defconst *fn2-upload-word-refused* (fn2-upload-word-code :refused))

(defun fn2-txn-hash-pool (n slot gen off okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp n) (natp off))))
  (mv-let (code h1 h2) (fn2-ribbon-hash n slot gen off 0 okind oslot ogen fn2-pool)
    (declare (ignore h2)) (mv code h1)))
(defthm fn2-txn-hash-pool-type
  (unsigned-byte-p 32 (mv-nth 1 (fn2-txn-hash-pool n slot gen off okind oslot ogen fn2-pool))))
(in-theory (disable fn2-txn-hash-pool))

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
(defun fn2-txn-next-name-pool (base cur end skip slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp base) (natp cur) (natp end))))
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
    (mv :name s (- e s) e nil)))
(defthm fn2-txn-next-name-pool-types
  (implies (and (natp base) (natp cur) (natp end))
           (and (natp (mv-nth 1 (fn2-txn-next-name-pool base cur end skip slot gen okind oslot ogen fn2-pool)))
                (natp (mv-nth 2 (fn2-txn-next-name-pool base cur end skip slot gen okind oslot ogen fn2-pool)))
                (natp (mv-nth 3 (fn2-txn-next-name-pool base cur end skip slot gen okind oslot ogen fn2-pool))))))
(in-theory (disable fn2-txn-next-name-pool))

;; Find the value span (mv vstart vlen) of the first header field with code
;; TARGET in [off, end) of chunk 0.
(defun fn2-txn-find-header (left off end target slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix left)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp left) (natp off) (natp end) (natp target))))
  (if (or (zp left) (>= off end)) (mv 0 0)
    (b* ((n (min *fn2-upload-line-cost* (- end off)))
         ((mv code at) (fn2-pool-scan slot gen off n *fn2-pool-scan-crlf* okind oslot ogen fn2-pool))
         (at (nfix at))
         ((unless (and (eq code :ok) (< at n) (posp at))) (mv 0 0))
         (next (+ off at 2))
         ((mv ok colon) (fn2-upload-name at off off slot gen okind oslot ogen fn2-pool))
         (colon (nfix colon))
         ((unless ok) (fn2-txn-find-header (- left 1) next end target slot gen okind oslot ogen fn2-pool))
         (code2 (fn2-upload-field-code off (nfix (- colon off)) slot gen okind oslot ogen fn2-pool))
         ((unless (equal code2 target))
          (fn2-txn-find-header (- left 1) next end target slot gen okind oslot ogen fn2-pool))
         (lend (+ off at))
         ((mv ok2 b2) (if (< (+ 1 colon) lend) (fn2-gram-read slot gen (+ 1 colon) okind oslot ogen fn2-pool) (mv t 32)))
         (vstart (if (and ok2 (< (+ 1 colon) lend) (= b2 32)) (+ 2 colon) (+ 1 colon))))
      (mv (nfix vstart) (nfix (- lend vstart))))))
(defthm fn2-txn-find-header-types
  (and (natp (mv-nth 0 (fn2-txn-find-header left off end target slot gen okind oslot ogen fn2-pool)))
       (natp (mv-nth 1 (fn2-txn-find-header left off end target slot gen okind oslot ogen fn2-pool)))))
(in-theory (disable fn2-txn-find-header))


;; Reset the workspace's fill to OFF before synthesizing the overview slice.
(defun fn2-txn-truncate-to (off slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp off))))
  (let ((code (fn2-pool-workspace-code slot gen okind oslot ogen fn2-pool)))
    (if (not (and (eq code :ok) (unsigned-byte-p 32 off) (<= off (fn2-pool-cap slot fn2-pool))))
        (mv :bounds fn2-pool)
      (let ((fn2-pool (fn2-pool-set-fill slot off fn2-pool)))
        (mv :ok fn2-pool)))))
(fn2-pool-preserves fn2-txn-truncate-to (off slot gen okind oslot ogen fn2-pool) :position 1 :rows nil)
(in-theory (disable fn2-txn-truncate-to))

(defun fn2-txn-synth-ov-1 (so sl fo fl slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (fn2-gram-put-chain
   (fn2-gram-put-span (min 180 (nfix sl)) (nfix so) slot gen slot gen okind oslot ogen fn2-pool)
   (fn2-gram-put *fn2-gram-tab* slot gen okind oslot ogen fn2-pool)
   (fn2-gram-put-span (min 180 (nfix fl)) (nfix fo) slot gen slot gen okind oslot ogen fn2-pool)
   (fn2-gram-put *fn2-gram-tab* slot gen okind oslot ogen fn2-pool)))
(fn2-pool-preserves fn2-txn-synth-ov-1 (so sl fo fl slot gen okind oslot ogen fn2-pool) :position 1 :rows nil)
(in-theory (disable fn2-txn-synth-ov-1))

(defun fn2-txn-synth-ov-2 (dto dtl ms mg mo ml slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (fn2-gram-put-chain
   (fn2-gram-put-span (min 80 (nfix dtl)) (nfix dto) slot gen slot gen okind oslot ogen fn2-pool)
   (fn2-gram-put *fn2-gram-tab* slot gen okind oslot ogen fn2-pool)
   (fn2-gram-put-span (min 250 (nfix ml)) (nfix mo) ms mg slot gen okind oslot ogen fn2-pool)
   (fn2-gram-put *fn2-gram-tab* slot gen okind oslot ogen fn2-pool)
   (fn2-gram-put *fn2-gram-tab* slot gen okind oslot ogen fn2-pool)))
(fn2-pool-preserves fn2-txn-synth-ov-2 (dto dtl ms mg mo ml slot gen okind oslot ogen fn2-pool) :position 1 :rows nil)
(in-theory (disable fn2-txn-synth-ov-2))

(defun fn2-txn-synth-ov-3 (hashed lines slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (fn2-gram-put-chain
   (fn2-gram-put-number (nfix hashed) slot gen okind oslot ogen fn2-pool)
   (fn2-gram-put *fn2-gram-tab* slot gen okind oslot ogen fn2-pool)
   (fn2-gram-put-number (nfix lines) slot gen okind oslot ogen fn2-pool)))
(fn2-pool-preserves fn2-txn-synth-ov-3 (hashed lines slot gen okind oslot ogen fn2-pool) :position 1 :rows nil)
(in-theory (disable fn2-txn-synth-ov-3))

(defun fn2-txn-synth-ov-pool (ms mg mo ml scanned at hashed lines slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool
                  :guard (and (fn2-pool-wfp fn2-pool) (natp mo) (natp ml) (natp scanned) (natp at) (natp hashed) (natp lines))))
  (b* ((ov-off (+ at *fn2-upload-digest-octets*))
       ((mv so sl) (fn2-txn-find-header 64 0 scanned *fn2-upload-field-subject* slot gen okind oslot ogen fn2-pool))
       ((mv fo fl) (fn2-txn-find-header 64 0 scanned *fn2-upload-field-from* slot gen okind oslot ogen fn2-pool))
       ((mv dto dtl) (fn2-txn-find-header 64 0 scanned *fn2-upload-field-date* slot gen okind oslot ogen fn2-pool))
       ((mv code fn2-pool)
        (fn2-gram-put-chain
         (fn2-txn-truncate-to ov-off slot gen okind oslot ogen fn2-pool)
         (fn2-txn-synth-ov-1 so sl fo fl slot gen okind oslot ogen fn2-pool)
         (fn2-txn-synth-ov-2 dto dtl ms mg mo ml slot gen okind oslot ogen fn2-pool)
         (fn2-txn-synth-ov-3 hashed lines slot gen okind oslot ogen fn2-pool)))
       ((unless (eq code :ok)) (mv 0 0 fn2-pool))
       (ov-len (min *fn2-overview-octets-max* (nfix (- (fn2-gram-fill slot fn2-pool) ov-off)))))
    (mv ov-off ov-len fn2-pool)))
(fn2-pool-preserves fn2-txn-synth-ov-pool (ms mg mo ml scanned at hashed lines slot gen okind oslot ogen fn2-pool) :position 2 :rows nil)
(defthm fn2-txn-synth-ov-pool-types
  (implies (and (natp mo) (natp ml) (natp scanned) (natp at) (natp hashed) (natp lines))
           (and (natp (mv-nth 0 (fn2-txn-synth-ov-pool ms mg mo ml scanned at hashed lines slot gen okind oslot ogen fn2-pool)))
                (natp (mv-nth 1 (fn2-txn-synth-ov-pool ms mg mo ml scanned at hashed lines slot gen okind oslot ogen fn2-pool)))))
  :hints (("Goal" :in-theory (enable fn2-txn-synth-ov-pool))))
(in-theory (disable fn2-txn-synth-ov-pool))

(defcost fn2-txn-hash :child fn2-txn-hash-pool :answers t :bytes 256
  :doc "FNV-1a over the Message-ID's octets (at most 250), under the upload's owner.")
(defcost fn2-claim-begin-core :child fn2-claim-begin :answers (:ok :bounds :state) :tables (fn2-core-claims)
  :doc "Start a claim on a Message-ID's exact octets.")
(defcost fn2-claim-state-core :child fn2-claim-state :effects :per-use :doc "Read a transaction's claim state.")
(defcost fn2-txn-post-article-result :answers (:ok :dropped :fault) :faults (:fault) :bytes *fn2-txn-result-copy-bytes*
  :tables (fn2-core-claims fn2-core-pool fn2-core-machines fn2-conn-table fn2-cns-table)
  :doc "Post the held Message-ID and the article or evidence outcome before the claim can drain.")
(defcost fn2-claim-walk-core :child fn2-claim-walk :answers (:claimed :wait :more :bounds :state :fault) :faults (:bounds :state :fault) :bytes 4096
  :tables (fn2-core-claims)
  :effects ((:acquire (:identity-reservation)))
  :doc "Walk the claim's bucket at most 16 chain steps (one Message-ID compared per step on an equal hash): claimed, waiting in the holder's FIFO, or more.")
(defcost fn2-claim-release-core :answers (:ok :bounds :state) :tables (fn2-core-claims fn2-core-machines)
  :effects ((:release (:identity-reservation)))
  :doc "Release a held claim and hand it to its FIFO's head, waking that transaction.")
(defcost fn2-txn-offer :enqueues 1 :answers (:ok :bounds :state :exhausted :owner :stale)
  :tables (fn2-core-succ-txns fn2-core-id-decides fn2-core-fields fn2-core-pool fn2-core-machines fn2-core-control fn2-core-sched fn2-core-trace)
  :doc "Start the identity decision for the upload's Message-ID and content digest.")
(defcost fn2-txn-source-digest-ref :answers (:ok :bounds)
  :tables (fn2-core-machines fn2-core-machine-tables fn2-txn-table fn2-upload-table fn2-core-pool)
  :doc "Resolve the sealed upload's retained original SOURCE digest through the live transaction link.")
(defcost fn2-txn-retry-append :answers (:found :reused :absent :more :dropped :state) :faults (:state) :bytes 8192
  :tables (fn2-core-reads fn2-core-succ-txns fn2-core-run-cursors fn2-core-run-paths fn2-core-fields
           fn2-core-pool fn2-core-machines fn2-core-machine-tables fn2-txn-table fn2-cns-table fn2-upload-table)
  :doc "Look up the current APPEND's supplied key and post the stored outcome if its source digest agrees.")
(defcost fn2-txn-count :child fn2-txn-count-loop :answers (:ok :bounds) :bytes *fn2-txn-count-bytes*
  :doc "Count LF octets in up to 2,048 octets of a pool slot.")
(defcost fn2-txn-count-next :answers (:ok :bounds) :bytes *fn2-txn-count-bytes*
  :doc "Count LF octets in up to 2,048 octets of the upload's body.")
(defcost fn2-txn-next-name :child fn2-txn-next-name-pool :answers (:name :end :run :fault) :faults (:fault) :bytes *fn2-txn-scan-bytes*
  :doc "Scan chunk 0 for the next group name of Newsgroups.")
(defcost fn2-txn-add-group :answers t :tables (fn2-core-succ-txns fn2-core-succ-slots fn2-core-fields fn2-core-pool) :bytes 512
  :doc "Declare the group's count accept, overview row (its line late), and addressing entry; keep its name for the Xref field.")
(defcost fn2-txn-xref :answers t :tables (fn2-core-succ-txns fn2-core-succ-slots fn2-core-fields fn2-core-pool fn2-core-control)
  :bytes *fn2-txn-xref-bytes*
  :doc "Append the Xref field (the path identity, each group's name and staged number) to the overview line and give it to every overview slot.")
(defcost fn2-txn-put-post-for :answers t :tables (fn2-core-succ-txns fn2-core-succ-slots fn2-core-fields fn2-core-pool)
  :doc "Declare the article's identity, article and outcome slots and synthesize the overview line's first seven fields in chunk 0.")
(defcost fn2-txn-put-evidence-for :answers t :tables (fn2-core-succ-txns fn2-core-succ-slots fn2-core-fields)
  :doc "Declare the competing binding and its keyed APPEND outcome in the same private successor (ruling 6).")
(defcost fn2-txn-prebind :answers (:ok) :tables (fn2-core-fields)
  :doc "Pre-fill prospective event numbers into staged insert slots before emitting journal records.")
(defconst *fn2-authority-right-append* 2)
(defcost fn2-authority-allows :answers (:ok :access :more :state) :faults (:state) :bytes 4096
  :tables (fn2-core-succ-txns fn2-core-run-cursors fn2-core-run-paths fn2-core-fields)
  :doc "One bounded step of the append check (books/authority.lisp, AUTHORITY-20261105 section 4): (fn2-authority-allows tx durable-principal right target step head grant budget) -> (mv code step head grant), one exact lookup source per call (the head, the current grant, the grant row).")
(defcost fn2-authority-depend :answers (:ok :state) :faults (:state)
  :tables (fn2-core-succ-txns fn2-core-succ-slots fn2-core-fields)
  :doc "Declare the transaction's read dependency on the principal's authority head it decided under (once; nothing when no grant governed).")
(defcost fn2-txn-group-of :answers (:absent :bad-magic :bounds :done :end :entry :format :invariant :length :lost :miss :more
  :noncanonical :ok :owner :part :payload :schema :stale :state :truncated :unknown-tag :wide)
  :bytes 4096
  :tables (fn2-core-succ-txns fn2-core-run-cursors fn2-core-run-paths fn2-core-fields)
  :doc "The group at the scan's name: the one the append check in progress holds (XSTEP > 0), else one source of its name lookup.")
(defcost fn2-txn-wake-upload :tables (fn2-core-machines)
  :doc "Wake the upload this transaction held, if it still names it, so it drains.")
(defcost fn2-txn-groups-limit
  :doc "Profile-configured cross-post group limit (:max-groups-per-article, D27).")

(defmachine-arms fn2-txn :declare
 :subarms
 (;; one Newsgroups name: look it up, declare its group-count accept, overview and addr
  (group :on-refusal ((:stop :machine-phase))
   (:let gslot row-slot)
   (:let no (:read upload no)) (:let nl (:read upload nl))
   (:let c0 (:read upload c0-slot)) (:let g0 (:read upload c0-gen))
   (:let c1 (:read upload c1-slot)) (:let g1 (:read upload c1-gen))
   (:do (status start len next skip2)
        (fn2-txn-next-name no row-gcur nl (equal row-gskip 1) c0 g0 :owner upload)
    :accept (:run :end :name) :why "the name scan's three continuations; :fault goes to :on-refusal")
   (:cond ((not (unsigned-byte-p 32 next)) (:stop :machine-phase))
          ((eq status :run) (:set (gcur next) (gskip (if skip2 1 0)))
                            (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
          ((eq status :end) (:set (gcur next)) (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
          (t (:do (code group) (fn2-txn-group-of gslot row-xstep row-xgroup c0 g0 (+ no start) len :budget 4096 :owner upload)
              :accept ()
              :case (((:more) (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                     ((:absent) (:set (gcur next)) (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                     ((:ok)
                      (:cond ((>= row-ngroups (fn2-txn-groups-limit))
                              (:set (word *fn2-upload-word-unaffordable*)) (:next :refused)
                              (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                             ;; the authority seam (AUTHORITY-20261105 section
                             ;; 4): the principal's append grant for this
                             ;; destination, in bounded steps, then the read
                             ;; dependency on the head it was decided under
                             (t (:let pid (:read upload request-principal))
                                (:do (pc current) (fn2-upload-owner-principal row-conn row-conn-gen row-principal-slot)
                                 :accept (:ok :state) :why "recheck the live binding before a grant decision")
                                (:if (not (and (eq pc :ok) (equal current pid)))
                                     ((:set (word *fn2-upload-word-refused*)) (:next :refused)
                                      (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                                     ((:do (acode astep ahead agrant)
                                           (fn2-authority-allows gslot pid *fn2-authority-right-append* group
                                                                 (if (equal row-xstep 0) 0 (- row-xstep 1)) row-xhead row-xgrant 4096)
                                       :accept (:ok)
                                       :case (((:more)
                                               (:cond ((< astep 255)
                                                       (:set (xstep (+ 1 astep)) (xgroup group) (xhead ahead) (xgrant agrant))
                                                       (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                                                      (t (:stop :machine-phase))))
                                              ((:access) (:set (word *fn2-upload-word-refused*) (xstep 0)) (:next :refused)
                                               (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))))
                                      (:do (dcode) (fn2-authority-depend gslot pid agrant ahead) :accept (:ok))
                                      (:do (pcode) (fn2-txn-add-group gslot row-ngroups group pid c0 g0 c1 g1
                                                                       (+ no start) len :owner upload))
                                      (:if (eq pcode :ok)
                                           ((:set (ngroups (+ 1 row-ngroups)) (gcur next) (xstep 0))
                                            (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                                           ((:set (word *fn2-upload-word-unaffordable*)) (:next :refused)
                                            (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t)))))))))))))
  ;; :ready stages and admits in one scheduler turn. Only article
  ;; submissions need an overview or Xref. Evidence uses the same emit/bind.
  (ready-capacity :on-refusal ((:stop :machine-phase))
   (:if (equal row-tmode *fn2-txn-mode-evidence*)
        ((:set (word *fn2-upload-word-conflict*) (ecommit *fn2-txn-ecommit-refused*)))
        ((:set (word *fn2-upload-word-unaffordable*))))
   (:next :refused) (:charge :bytes *fn2-txn-ready-bytes* :steps *fn2-work-transition* :runnable t))
  (submit :on-refusal ((:stop :machine-phase))
   (:let sslot row-slot) (:let c1 (:read upload c1-slot)) (:let g1 (:read upload c1-gen))
   (:do (ecode elen)
        (fn2-successor-emit sslot c1 g1 0 (fn2-upload-chunk-cap c1) :owner upload)
    :accept ()
    :case (((:ok)
            (:do (acode b ev)
                 (fn2-commit-admit-txn c1 g1 elen :owner upload)
             :effects ((:acquire (:batch-membership)))
             :accept ()
             :case (((:ok)
                     (:if (and (unsigned-byte-p 60 b) (unsigned-byte-p 60 ev))
                          ((:do (bcode) (fn2-successor-bind sslot b ev))
                           (:set (batch b) (bevent ev))
                           (:next :batched) (:charge :bytes *fn2-txn-ready-bytes* :steps *fn2-work-transition* :runnable t))
                          ((:stop :machine-phase))))
                    ((:exhausted) (:park :batch-membership :steps *fn2-work-transition*))
                    ((:admission)
                     (:if (equal row-tmode *fn2-txn-mode-evidence*)
                          ((:set (ecommit *fn2-txn-ecommit-refused*) (word *fn2-upload-word-conflict*))
                           (:next :refused) (:charge :bytes *fn2-txn-ready-bytes* :steps *fn2-work-transition* :runnable t))
                          ((:set (word *fn2-upload-word-not-stored*))
                           (:next :refused) (:charge :bytes *fn2-txn-ready-bytes* :steps *fn2-work-transition* :runnable t)))))))
           ((:room) (:goto ready-capacity)))))
  ;; the outcome: the word to the owner (waking it; a consumer request also
  ;; gets an accepted article's commit position), the successor released
  (reply :on-refusal ((:stop :machine-phase))
   (:let rslot row-slot)
   (:if (not (equal row-word 0))
        ((:if (or (equal row-word *fn2-upload-word-accepted*)
                  (equal row-word *fn2-upload-word-conflict*))
          ((:do (pcode) (fn2-txn-post-article-result rslot row-upload row-upload-gen row-conn row-conn-gen row-request
                          row-word row-numbers-off row-numbers-len
                          (if (or (equal row-word *fn2-upload-word-accepted*)
                                  (equal row-ecommit *fn2-txn-ecommit-committed*)) row-bevent 0)
                          (if (or (equal row-word *fn2-upload-word-accepted*)
                                  (equal row-ecommit *fn2-txn-ecommit-committed*))
                              *fn2-cns-posted-accepted* *fn2-cns-posted-refused*))
            :accept (:ok :dropped) :why "a moved owner drops its completion"))
          ((:do (pcode) (fn2-upload-post-owner row-conn row-conn-gen row-request row-word 0)
            :accept (:ok :dropped) :why "a moved owner drops its completion")))
         (:do (rcode) (fn2-successor-release rslot)
          :accept (:ok :state) :why "a committed or bound transaction's successor is already closed")
         (:next :releasing) (:charge :bytes *fn2-txn-result-copy-bytes* :steps *fn2-work-transition* :runnable t))
        ((:do (rcode) (fn2-successor-release rslot)
          :accept (:ok :state) :why "a committed or bound transaction's successor is already closed")
         (:next :releasing) (:charge :steps *fn2-work-transition* :runnable t)))))
 :arms
 ((:free (:idle))
  ;; wait for the verdict when no Message-ID was scanned (posting the upload's
  ;; word, or :not-stored); else hash it and begin the claim
  (:admit :on-refusal ((:stop :machine-phase))
   (:cond ((not (:live upload))
           (:next :draining) (:charge :bytes 256 :steps *fn2-work-transition* :runnable t))
          (t (:let ml (:read upload ml)) (:let mo (:read upload mo))
             ;; the Message-ID's octets: in chunk 0, or a generated one in the store page
             (:let ms (if (equal (:read upload ilen) 0) (:read upload c0-slot) (:read upload lslot)))
             (:let mg (if (equal (:read upload ilen) 0) (:read upload c0-gen) (:read upload lgen)))
             (:let uphase (:read upload phase))
             (:cond ((and (equal ml 0) (equal uphase *fn2-upload-state-sealed*))
                     (:let w (:read upload word)) (:let inj (:read upload inj))
                     (:do (pcode) (fn2-upload-post-owner row-conn row-conn-gen row-request
                                                         (cond ((not (equal w 0)) w) ((not (equal inj 0)) inj)
                                                               (t *fn2-upload-word-not-stored*))
                                                         0)
                      :accept (:ok :dropped) :why "the owner may have moved on: the word is then dropped (section 14.4)")
                     (:next :draining) (:charge :bytes 256 :steps *fn2-work-transition* :runnable t))
                    ((and (equal ml 0) (equal uphase *fn2-upload-state-aborting*))
                     (:next :draining) (:charge :bytes 256 :steps *fn2-work-transition* :runnable t))
                    ((equal ml 0) (:charge :bytes 256 :steps *fn2-work-transition*))
                    (t (:do (hcode hash) (fn2-txn-hash ml ms mg mo :owner upload))
                       (:do (bcode) (fn2-claim-begin-core row-slot hash ms mg mo ml :owner upload))
                       (:next :reserve) (:charge :bytes 256 :steps *fn2-work-transition* :runnable t))))))
  ;; the claim walk: held, waiting in the holder's FIFO, or more
  (:reserve :on-refusal ((:stop :machine-phase))
   (:let s (fn2-claim-state-core row-slot))
   (:cond ((equal s *fn2-claim-state-held*)
           (:do (s2) (fn2-claim-state-core row-slot) :effects ((:acquire (:identity-reservation))))
           (:next :lookup) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
          ((equal s *fn2-claim-state-waiting*) (:charge :bytes 4096 :steps *fn2-work-transition*))
          (t (:do (code holder) (fn2-claim-walk-core row-slot *fn2-txn-claim-steps*)
              :accept ()
              :case (((:claimed) (:next :lookup) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
                     ((:wait) (:charge :bytes 4096 :steps *fn2-work-transition*))
                     ((:more) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t)))))))
  ;; the upload's verdict, then the identity offer (one run) or one decision step,
  ;; routed from C's separate facts (ruling 6, ruling 8)
  (:lookup :on-refusal ((:stop :machine-phase))
   (:let lslot row-slot)
   (:let uphase (:read upload phase))
   (:cond ((not (and (:live upload) (not (equal uphase *fn2-upload-state-aborting*))))
           (:set (word 0)) (:next :refused) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
          ((not (equal uphase *fn2-upload-state-sealed*)) (:charge :bytes 4096 :steps *fn2-work-transition*))
          (t (:let w (:read upload word))
             (:cond ((not (equal w 0)) (:set (word w)) (:next :refused)
                                       (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
                    ((and (not (equal (:read upload op) 0)) (equal row-outcome-checked 0))
                     (:do (rcode) (fn2-txn-retry-append lslot row-upload row-upload-gen
                                                      row-conn row-conn-gen row-request)
                      :accept ()
                      :case (((:more) (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                             ((:absent) (:set (outcome-checked 1))
                              (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                             ((:found :dropped)
                              (:do (rel) (fn2-successor-release lslot)
                               :accept (:ok :state) :why "the retry never binds a successor")
                              (:next :releasing)
                              (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                             ((:reused)
                              (:set (word *fn2-upload-word-operation-reused*)) (:next :refused)
                              (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t)))))
                    ((not (equal row-offered 1))
                     (:do (dcode ds dg doff) (fn2-txn-source-digest-ref lslot) :accept (:ok))
                     (:do (code) (fn2-txn-offer lslot (if (equal (:read upload ilen) 0) (:read upload c0-slot) (:read upload lslot))
                                                (if (equal (:read upload ilen) 0) (:read upload c0-gen) (:read upload lgen))
                                                (:read upload mo) (:read upload ml)
                                                ds dg doff :owner upload))
                     (:set (offered 1)) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
                    (t (:do (answer) (fn2-identity-decide lslot 4096)
                        :accept ()
                        :case (((:more) (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
                               ((:stored :duplicate :conflict :evidence)
                                (:do (fcode verdict selection h evidence coverage) (fn2-identity-facts lslot))
                                (:cond ((eq selection :same)
                                        (:set (word *fn2-upload-word-duplicate*)) (:next :refused)
                                        (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
                                       ((and (eq verdict :stored) (not (equal row-tmode *fn2-txn-mode-evidence*)))
                                        (:set (tmode *fn2-txn-mode-article*)) (:next :prepare)
                                        (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t))
                                       (t (:set (tmode *fn2-txn-mode-evidence*) (word *fn2-upload-word-conflict*))
                                          (:next :prepare)
                                          (:charge :bytes 4096 :steps *fn2-work-transition* :runnable t)))))))))))
  ;; count the body's lines, look each group up, refuse :group or the injected
  ;; fields, declare the slots (evidence or article); then resolve them
  (:prepare :on-refusal ((:stop :machine-phase))
   (:if (or (fn2-core-query-heldp (:read upload c0-slot) (:read upload c0-gen))
            (fn2-core-query-heldp (:read upload c1-slot) (:read upload c1-gen)))
        ((:charge :steps *fn2-work-state*))
        (
   (:if (equal row-prepared 1)
        ((:do (answer) (fn2-successor-resolve row-slot 4096)
          :accept ()
          :case (((:ok) (:next :ready) (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                 ((:more) (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t)))))
        ((:if (equal row-tmode *fn2-txn-mode-evidence*)
              ((:do (fcode verdict selection h evidence coverage) (fn2-identity-facts row-slot))
               (:do (dcode ds dg doff) (fn2-txn-source-digest-ref row-slot) :accept (:ok))
               (:do (pcode) (fn2-txn-put-evidence-for row-slot
                                                      (if (equal (:read upload ilen) 0) (:read upload c0-slot) (:read upload lslot))
                                                      (if (equal (:read upload ilen) 0) (:read upload c0-gen) (:read upload lgen))
                                                      (:read upload mo) (:read upload ml)
                                                      ds dg doff h (:read upload request-principal)
                                                      (:read upload op) :owner upload))
               (:if (eq pcode :ok)
                    ((:set (prepared 1)) (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                    ((:set (ecommit *fn2-txn-ecommit-refused*)) (:next :refused)
                     (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))))
              ((:let c0 (:read upload c0-slot)) (:let g0 (:read upload c0-gen))
               (:let c1 (:read upload c1-slot)) (:let g1 (:read upload c1-gen))
               (:let hashed (:read upload hashed)) (:let scanned (:read upload scan-off))
               (:let nl (:read upload nl))
               (:let counted (max scanned row-counted))
               (:cond ((< counted hashed)
                       ;; Nlines excludes the terminating blank header line.
                       ;; SOURCE-LINES counts the exact hashed source, including it.
                       (:let all-lines (:read upload source-lines))
                       (:let header-lines (+ 1 (:read upload nlines)))
                       (:if (and (unsigned-byte-p 32 all-lines) (<= header-lines all-lines))
                            ((:set (counted hashed) (lines (- all-lines header-lines)))
                             (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                            ((:stop :machine-phase))))
                      ;; the article's slots and its overview line's first
                      ;; seven fields, then its groups (chunk 1 keeps their names)
                      ((equal row-filed 0)
                       (:do (fcode verdict selection h evidence coverage) (fn2-identity-facts row-slot))
                       (:do (dcode ds dg doff) (fn2-txn-source-digest-ref row-slot) :accept (:ok))
                       (:do (lcode le lep lal) (fn2-upload-location-tuple row-upload row-upload-gen) :accept (:ok))
                       (:do (pcode) (fn2-txn-put-post-for row-slot
                                                          (if (equal (:read upload ilen) 0) (:read upload c0-slot) (:read upload lslot))
                                                          (if (equal (:read upload ilen) 0) (:read upload c0-gen) (:read upload lgen))
                                                          (:read upload mo) (:read upload ml)
                                                          c0 g0 scanned hashed (:read upload ilen)
                                                          ds dg doff
                                                          h (:read upload request-principal) row-lines
                                                          le lep lal
                                                          (:read upload lslot) (:read upload lgen) *fn2-upload-page-stored-source*
                                                          *fn2-upload-page-location-hashes* (* 32 (:read upload location-hashed))
                                                          (:read upload op)
                                                          :owner upload))
                       (:if (eq pcode :ok)
                            ((:set (filed 1)) (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                            ((:set (word *fn2-upload-word-unaffordable*)) (:next :refused)
                             (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))))
                      ((< row-gcur nl) (:goto group))
                      ((equal row-ngroups 0)
                       (:set (word *fn2-upload-word-group*)) (:next :refused)
                       (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                      (t (:let inj (:read upload inj))
                         (:if (not (equal inj 0))
                              ((:set (word inj)) (:next :refused)
                               (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))
                              ((:set (prepared 1))
                               (:charge :bytes 8192 :steps *fn2-work-transition* :runnable t))))))))))))
  ;; stage every slot against the tip, emit into chunk 1, admit the member, bind on :ok (one run)
  (:ready :on-refusal ((:stop :machine-phase))
   (:if (or (fn2-core-query-heldp (:read upload c0-slot) (:read upload c0-gen))
            (fn2-core-query-heldp (:read upload c1-slot) (:read upload c1-gen)))
        ((:charge :steps *fn2-work-state*))
        (
   (:let sslot row-slot)
   (:if (eq (fn2-commit-posture) :draining)
        ((:goto ready-capacity))
        ((:do (scode i) (fn2-successor-stage sslot)
          :accept ()
          :case (((:ok)
                  (:do (pcode) (fn2-txn-prebind sslot))
                  (:if (equal row-tmode *fn2-txn-mode-evidence*) ((:goto submit))
                    ((:let c0 (:read upload c0-slot)) (:let scanned (:read upload scan-off))
                     (:if (<= (+ scanned *fn2-upload-digest-octets*) (fn2-upload-chunk-cap c0)) ()
                          ((:goto ready-capacity)))
                     (:do (xcode noff nlen) (fn2-txn-xref sslot row-ngroups c0 (:read upload c0-gen)
                                               (:read upload c1-slot) (:read upload c1-gen)
                                               (+ scanned *fn2-upload-digest-octets*) :owner upload))
                     (:if (and (eq xcode :ok) (unsigned-byte-p 32 noff) (unsigned-byte-p 32 nlen))
                          ((:set (numbers-off noff) (numbers-len nlen)) (:goto submit))
                          ((:goto ready-capacity))))))
                 ((:full) (:charge :bytes *fn2-txn-ready-bytes* :steps *fn2-work-transition* :runnable t))
                 ;; A stale version or changed grant dependency requires a
                 ;; fresh outcome lookup and decision before anything is submitted.
                 ((:stale :changed)
                  (:do (rcode) (fn2-successor-release sslot))
                  (:set (outcome-checked 0) (offered 0) (prepared 0) (filed 0)
                        (gcur 0) (gskip 0) (ngroups 0) (xstep 0))
                  (:next :lookup) (:charge :bytes *fn2-txn-ready-bytes* :steps *fn2-work-transition* :runnable t))
                 ((:refused :evidence)
                  (:do (rcode) (fn2-successor-release sslot))
                  (:set (tmode *fn2-txn-mode-evidence*) (word *fn2-upload-word-conflict*)
                        (outcome-checked 0) (offered 0) (prepared 0) (filed 0)
                        (gcur 0) (gskip 0) (ngroups 0) (xstep 0))
                  (:next :lookup) (:charge :bytes *fn2-txn-ready-bytes* :steps *fn2-work-transition* :runnable t))
                 ((:duplicate)
                  (:if (and (equal i *fn2-txn-slot-outcome*) (not (equal (:read upload op) 0)))
                       ;; The tip includes unpublished members. Re-read the committed
                       ;; key and retry the decision if the competing batch drops it.
                       ((:do (rcode) (fn2-successor-release sslot))
                        (:set (tmode *fn2-txn-mode-article*) (word 0) (outcome-checked 0)
                              (offered 0) (prepared 0) (filed 0)
                              (gcur 0) (gskip 0) (ngroups 0) (xstep 0))
                        (:next :lookup)
                        (:charge :bytes *fn2-txn-ready-bytes* :steps *fn2-work-transition* :runnable t))
                       ((:if (equal row-tmode *fn2-txn-mode-evidence*)
                             ((:set (word *fn2-upload-word-conflict*) (ecommit *fn2-txn-ecommit-refused*)))
                             ((:set (word *fn2-upload-word-duplicate*))))
                        (:next :refused)
                        (:charge :bytes *fn2-txn-ready-bytes* :steps *fn2-work-transition* :runnable t))))
                 ((:capacity) (:goto ready-capacity)))))))))
  (:batched :on-refusal ((:stop :machine-phase))
   (:do (tcode tbatch tevent tout)
        (fn2-commit-take :owner upload)
    :effects ((:release (:batch-membership)))
    :accept ()
    :case (((:pending) (:charge :steps *fn2-work-empty* :runnable t))
           ((:ok)
            (:if (and (equal tbatch row-batch) (equal tevent row-bevent)) () ((:stop :machine-phase)))
            (:cond ((equal tout *fn2-commit-outcome-accepted*)
                    (:if (equal row-tmode *fn2-txn-mode-evidence*)
                         ((:set (ecommit *fn2-txn-ecommit-committed*) (word *fn2-upload-word-conflict*))
                          (:next :refused) (:charge :steps *fn2-work-transition* :runnable t))
                         ;; the article's payload extent is now the article's
                         ;; (every extent its stored octets occupy: the
                         ;; manifest's and each block's)
                         ((:let hrow (fn2-upload-hasher row-upload))
                          (:do (lcode le lep lal) (fn2-upload-location-tuple row-upload row-upload-gen) :accept (:ok))
                          (:do (acode) (fn2-upload-extents-of t tevent (* 128 hrow)
                                                              (+ (:read upload ilen) (:read upload hashed))
                                                              (:read upload lslot) (:read upload lgen) (:read upload mfill)
                                                              le lep lal *fn2-none* 0 0 0
                                                              :owner upload)
                           :accept (:ok))
                          (:set (word *fn2-upload-word-accepted*))
                          (:next :accepted) (:charge :steps *fn2-work-transition* :runnable t))))
                   ((equal tout *fn2-commit-outcome-uncertain*)
                    (:set (ecommit (if (equal row-tmode *fn2-txn-mode-evidence*) *fn2-txn-ecommit-uncertain* row-ecommit))
                          (word *fn2-upload-word-uncertain*))
                    (:next :uncertain) (:charge :steps *fn2-work-transition* :runnable t))
                   ((equal tout *fn2-commit-outcome-refused*)
                    (:if (equal row-tmode *fn2-txn-mode-evidence*)
                         ((:set (ecommit *fn2-txn-ecommit-refused*) (word *fn2-upload-word-conflict*))
                          (:next :refused) (:charge :steps *fn2-work-transition* :runnable t))
                         ((:set (word *fn2-upload-word-not-stored*))
                          (:next :refused) (:charge :steps *fn2-work-transition* :runnable t))))
                   (t (:stop :machine-phase)))))))
  (:accepted (:goto reply))
  (:refused (:goto reply))
  ;; A recoverable record may exist. Notify once and retain the claim,
  ;; successor and upload pending recovery. B fences further commit admission.
  (:uncertain :on-refusal ((:stop :txn-uncertain))
   (:if (equal row-stopped 0)
        ((:if (equal row-ecommit *fn2-txn-ecommit-uncertain*)
              ((:do (pcode) (fn2-txn-post-article-result row-slot row-upload row-upload-gen
                               row-conn row-conn-gen row-request *fn2-upload-word-conflict* 0 0 0 *fn2-cns-posted-uncertain*)
                :accept (:ok :dropped) :why "the ambiguous evidence remains pending even if the owner disconnected"))
              ((:do (pcode) (fn2-upload-post-owner row-conn row-conn-gen row-request *fn2-upload-word-uncertain* 0)
                :accept (:ok :dropped) :why "the ambiguous article remains pending even if the owner disconnected")))
         (:set (stopped 1)) (:charge :bytes *fn2-txn-result-copy-bytes* :steps *fn2-work-transition*))
        ((:charge :steps *fn2-work-empty*))))
  ;; release the claim; its FIFO's head takes it and is woken (the run's one wake)
  (:releasing :on-refusal ((:stop :machine-phase))
   (:do (code) (fn2-claim-release-core row-slot))
   (:next :draining) (:charge :steps *fn2-work-transition* :runnable t))
  (:draining
   (:let u row-upload) (:let gen row-generation)
   (:let next (fn2-machine-free-head *fn2-txn-admission-ordinal*))
   (:let retire (>= gen (fn2-machine-gen-limit)))
   (:set (generation (if retire gen (+ 1 gen))) (upload *fn2-none*) (upload-gen 0) (conn *fn2-none*) (conn-gen 0)
         (next-free next) (wait-reason *fn2-wait-none*))
   (:next (:if retire :retired :free))
   (:do () (fn2-machine-reclaim-fn2-txn id retire))
   (:do () (fn2-txn-wake-upload u id gen))
   (:charge :steps *fn2-work-release*))
  (:retired (:idle))))

;; ------------------------------------------------------------------------
;; The operations, materialized after the core instance (assembly-callbacks-d-txn,
;; after the upload's continuations): wrappers over the claim table and C's seams.
(defmacro fn2-txn-op-events ()
 '(progn
(defcost-faces fn2-txn)
(defun fn2-txn-groups-limit (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-txn-config (fn2-core-txn-config fn2-core)))
    (lim)
    (if (and (fn2-txn-config-wfp fn2-txn-config)
             (natp (fn2-txn-config-rows fn2-txn-config))
             (< 0 (fn2-txn-config-rows fn2-txn-config)))
        (fn2-txn-config-groups-max 0 fn2-txn-config)
      0)
    (min (nfix lim) *fn2-txn-groups-max*)))
(defthm fn2-txn-groups-limit-natp
  (natp (fn2-txn-groups-limit fn2-core))
  :rule-classes :type-prescription)
(defthm fn2-txn-groups-limit-bound
  (<= (fn2-txn-groups-limit fn2-core) *fn2-txn-groups-max*)
  :rule-classes :linear)
(in-theory (disable fn2-txn-groups-limit))
(defthm fn2-txn-hash-type
  (unsigned-byte-p 32 (mv-nth 1 (fn2-txn-hash n slot gen off okind oslot ogen fn2-core)))
  :hints (("Goal" :in-theory (e/d (fn2-txn-hash) (unsigned-byte-p)))))
(defthm fn2-txn-count-natp
  (implies (natp lines) (natp (mv-nth 1 (fn2-txn-count n slot gen off lines okind oslot ogen fn2-core))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn2-txn-count))))
(defthm fn2-txn-next-name-types
  (implies (and (natp base) (natp cur) (natp end))
           (and (natp (mv-nth 1 (fn2-txn-next-name base cur end skip slot gen okind oslot ogen fn2-core)))
                (natp (mv-nth 2 (fn2-txn-next-name base cur end skip slot gen okind oslot ogen fn2-core)))
                (natp (mv-nth 3 (fn2-txn-next-name base cur end skip slot gen okind oslot ogen fn2-core)))))
  :hints (("Goal" :in-theory (enable fn2-txn-next-name))))
;; The group at the Newsgroups scan's current name: while the append check
;; for it is in progress (XSTEP > 0) the group it holds, else one source of
;; the name's lookup (fn2-group-lookup).
(defun fn2-txn-group-of (tx xstep xgroup slot gen off len okind oslot ogen budget fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (and (posp xstep) (unsigned-byte-p 60 xgroup))
      (mv :ok xgroup fn2-core)
    (fn2-group-lookup tx slot gen off len okind oslot ogen budget fn2-core)))
(fn2-core-preserves fn2-txn-group-of (tx xstep xgroup slot gen off len okind oslot ogen budget fn2-core) :position 2 :rows nil
  :hints (("Goal" :in-theory (enable fn2-txn-group-of))))
(in-theory (disable fn2-txn-group-of))
;; Copy before either the claim or the upload can drain. The destination
;; belongs to the CNS request and remains reserved until its reply is posted.
;; A fault after commit stops serving without sending a refusal or retrying.
(defun fn2-txn-post-article-result (claim upload ugen owner ogen request word numbers-off numbers-len position posted fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)
                  :guard-hints (("Goal" :in-theory (enable fn2-core-wfp fn2-claim-rowp)))))
  (cond
   ((not (eq (fn2-cns-snapshot-read-code owner fn2-core) :ok))
    (fn2-conn-post-word owner ogen request
                       (if (equal posted *fn2-cns-posted-uncertain*) *fn2-upload-word-uncertain* word) fn2-core))
   ((not (and (equal (fn2-machine-generation owner fn2-core) ogen)
              (equal (fn2-cns-row-request owner fn2-core) request)
              (equal (fn2-cns-row-phase owner fn2-core) *fn2-cns-state-append*)
              (equal (fn2-cns-row-posted owner fn2-core) *fn2-cns-posted-none*)))
    (mv :dropped fn2-core))
   (t
    (b* (((mv valid slot gen off len)
          (stobj-let ((fn2-claims (fn2-core-claims fn2-core)))
           (valid slot gen off len)
           (if (and (fn2-claim-rowp claim fn2-claims)
                    (equal (fn2-claims-state claim fn2-claims) *fn2-claim-state-held*)
                    (equal (fn2-claims-ok claim fn2-claims) *fn2-upload-kind*)
                    (equal (fn2-claims-os claim fn2-claims) upload)
                    (equal (fn2-claims-og claim fn2-claims) ugen))
               (mv t (fn2-claims-slot claim fn2-claims) (fn2-claims-gen claim fn2-claims)
                   (nfix (fn2-claims-off claim fn2-claims)) (nfix (fn2-claims-len claim fn2-claims)))
             (mv nil 0 0 0 0))
           (mv valid slot gen off len)))
         ((unless (and valid (posp len) (<= len *fn2-format-message-id-max*))) (mv :fault fn2-core))
         (ns (fn2-cns-row-ns-slot owner fn2-core))
         (ng (fn2-cns-row-ns-gen owner fn2-core))
         ((mv code fn2-core)
          (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (code fn2-pool)
           (fn2-rd-copy len slot gen off *fn2-upload-kind* upload ugen
                        ns ng 0 *fn2-cns-kind* owner ogen fn2-pool)
           (mv code fn2-core)))
         ((unless (eq code :ok)) (mv :fault fn2-core))
         (accepted (equal word *fn2-upload-word-accepted*))
         ((when (and accepted
                     (not (and (eq (fn2-upload-snapshot-read-code upload fn2-core) :ok)
                               (equal (fn2-machine-generation upload fn2-core) ugen)
                               (natp numbers-off)
                               (posp numbers-len) (unsigned-byte-p 32 numbers-len)
                               (<= numbers-len *fn2-overview-octets-max*)))))
          (mv :fault fn2-core))
         ((mv copy fn2-core)
          (if accepted
              (let ((slot (fn2-upload-row-c0-slot upload fn2-core))
                    (gen (fn2-upload-row-c0-gen upload fn2-core)))
                (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (copy fn2-pool)
                  (fn2-rd-copy numbers-len slot gen numbers-off *fn2-upload-kind* upload ugen
                               ns ng len *fn2-cns-kind* owner ogen fn2-pool)
                  (mv copy fn2-core)))
            (mv :ok fn2-core)))
         ((unless (eq copy :ok)) (mv :fault fn2-core))
         (fn2-core (fn2-cns-put-core owner (append-numbers-len (if accepted numbers-len 0)) (name-len len))))
     (fn2-cns-post-outcome owner ogen request word position posted fn2-core)))))
(fn2-core-preserves fn2-txn-post-article-result (claim upload ugen owner ogen request word numbers-off numbers-len position posted fn2-core)
  :position 1 :rows nil :hints (("Goal" :in-theory (enable fn2-core-wfp fn2-claim-rowp))))
(in-theory (disable fn2-txn-post-article-result))

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
  :hints (("Goal" :in-theory (disable fn2-txn-snapshot-read-code nfix))))
(in-theory (disable fn2-commit-admit-txn fn2-claim-release-core))


;; At the drain: wake the upload U if it still names this row (ID of
;; generation GEN), so it sees the row gone and drains.
(defun fn2-txn-wake-upload (u id gen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (and (eq (fn2-upload-snapshot-read-code u fn2-core) :ok) (fn2-machine-idp u fn2-core)
           (equal (fn2-upload-row-txn u fn2-core) id) (equal (fn2-upload-row-txn-gen u fn2-core) gen))
      (fn2-machine-set-wake-id u fn2-core)
    fn2-core))
(fn2-core-preserves fn2-txn-wake-upload (u id gen fn2-core) :rows nil
  :hints (("Goal" :in-theory (disable fn2-upload-snapshot-read-code))))
(in-theory (disable fn2-txn-wake-upload))

;; TX is the transaction's local row slot; the machine link names a global
;; upload ID.  The page remains owned by that upload until the transaction
;; leaves :sealed, so all three consumers use this same retained SOURCE ref.
(defun fn2-txn-source-digest-ref (tx fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* (((unless (natp tx)) (mv :bounds 0 0 0))
       (id (+ (fn2-machine-kind-base *fn2-txn-kind* fn2-core) tx))
       ((unless (eq (fn2-txn-snapshot-read-code id fn2-core) :ok)) (mv :bounds 0 0 0))
       (gen (fn2-machine-generation id fn2-core))
       (u (fn2-txn-row-upload id fn2-core))
       (ug (fn2-txn-row-upload-gen id fn2-core))
       ((unless (and (eq (fn2-upload-snapshot-read-code u fn2-core) :ok)
                     (equal (fn2-machine-generation u fn2-core) ug)
                     (equal (fn2-upload-row-txn u fn2-core) id)
                     (equal (fn2-upload-row-txn-gen u fn2-core) gen)
                     (equal (fn2-upload-row-phase u fn2-core) *fn2-upload-state-sealed*)
                     (equal (fn2-upload-row-lease u fn2-core) *fn2-upload-lease-held*)
                     (equal (fn2-upload-row-word u fn2-core) 0)
                     (posp (fn2-upload-row-hashed u fn2-core))
                     (equal (fn2-upload-row-stored-hashed u fn2-core)
                            (+ (fn2-upload-row-ilen u fn2-core)
                               (fn2-upload-row-hashed u fn2-core)))))
        (mv :bounds 0 0 0))
       (slot (fn2-upload-row-lslot u fn2-core))
       (page-gen (fn2-upload-row-lgen u fn2-core))
       ((mv readable fill)
        (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (code n)
          (mv (fn2-pool-readable-code slot page-gen *fn2-upload-kind* u ug fn2-pool)
              (fn2-gram-fill slot fn2-pool))
          (mv code n)))
       ((unless (and (eq readable :ok)
                     (<= (+ *fn2-upload-page-source* *fn2-upload-digest-octets*) fill)))
        (mv :bounds 0 0 0)))
    (mv :ok slot page-gen *fn2-upload-page-source*)))
(in-theory (disable fn2-txn-source-digest-ref))

;; A replay uses the committed MID already copied into the owner's name
;; range. It does not publish the current upload's claim or payload.
(defun fn2-txn-retry-append (tx upload ugen owner ogen request fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)
                  :guard-hints (("Goal" :in-theory (enable fn2-core-wfp)))))
  (b* (((unless (and (eq (fn2-cns-snapshot-read-code owner fn2-core) :ok)
                     (equal (fn2-machine-generation owner fn2-core) ogen)
                     (equal (fn2-cns-row-phase owner fn2-core) *fn2-cns-state-append*)
                     (equal (fn2-cns-row-request owner fn2-core) request)
                     (equal (fn2-cns-row-posted owner fn2-core) *fn2-cns-posted-none*)
                     (equal (fn2-cns-row-upload owner fn2-core) upload)
                     (equal (fn2-cns-row-upload-gen owner fn2-core) ugen)))
        (mv :dropped fn2-core))
       ((unless (and (eq (fn2-upload-snapshot-read-code upload fn2-core) :ok)
                     (equal (fn2-machine-generation upload fn2-core) ugen)
                     (equal (fn2-upload-row-conn upload fn2-core) owner)
                     (equal (fn2-upload-row-conn-gen upload fn2-core) ogen)
                     (equal (fn2-upload-row-request upload fn2-core) request)))
        (mv :dropped fn2-core))
       ((mv dc ds dg doff) (fn2-txn-source-digest-ref tx fn2-core))
       ((unless (eq dc :ok)) (mv :state fn2-core))
       (op (fn2-upload-row-op upload fn2-core))
       (principal (fn2-upload-row-request-principal upload fn2-core))
       ((mv code event outcome midlen numbers-len fn2-core)
        (fn2-cns-read-append-outcome owner ogen request principal op 4096 fn2-core))
       ((unless (eq code :found)) (mv code fn2-core))
       ((unless (and (unsigned-byte-p 60 event) (posp event)
                     (posp midlen) (<= midlen *fn2-format-message-id-max*)
                     (unsigned-byte-p 32 numbers-len)
                     (or (equal outcome *fn2-txn-outcome-accepted*)
                         (equal outcome *fn2-txn-outcome-conflict*))))
        (mv :state fn2-core))
       (ws (fn2-cns-row-ws-slot owner fn2-core))
       (wg (fn2-cns-row-ws-gen owner fn2-core))
       ((mv cmp order)
        (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (cmp order)
          (mv-let (cmp order at)
            (fn2-pool-compare ds dg doff *fn2-upload-kind* upload ugen
                              ws wg 0 *fn2-cns-kind* owner ogen *fn2-upload-digest-octets* fn2-pool)
            (declare (ignore at))
            (mv cmp order))
          (mv cmp order)))
       ((unless (eq cmp :ok)) (mv :state fn2-core))
       ((unless (eq order :equal)) (mv :reused fn2-core))
       (word (if (equal outcome *fn2-txn-outcome-accepted*)
                 *fn2-upload-word-accepted*
               *fn2-upload-word-conflict*))
       (fn2-core (fn2-cns-put-core owner (name-len midlen) (append-numbers-len numbers-len)))
       ((mv posted fn2-core) (fn2-cns-post-outcome owner ogen request word event *fn2-cns-posted-accepted* fn2-core)))
    (mv (if (eq posted :ok) :found :dropped) fn2-core)))
(fn2-core-preserves fn2-txn-retry-append (tx upload ugen owner ogen request fn2-core)
  :position 1 :rows nil :hints (("Goal" :in-theory (disable fn2-cns-read-append-outcome))))
(in-theory (disable fn2-txn-retry-append))

(defun fn2-txn-offer (tx ms mg mo ml ds dg doff okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (fn2-identity-decide-start tx ms mg mo ml ds dg doff okind oslot ogen fn2-core))
(fn2-core-preserves fn2-txn-offer (tx ms mg mo ml ds dg doff okind oslot ogen fn2-core) :position 1 :rows nil)
(in-theory (disable fn2-txn-offer))

;; One counting run over [from, to) of the source (chunk 0 then chunk 1):
;; (mv code counted lines).
(defun fn2-txn-count-run (from to lines c0 g0 c1 g1 cap0 okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (natp from) (natp to) (natp lines) (natp cap0))))
  (b* ((in0 (< from cap0))
       (n (nfix (min *fn2-txn-count-bytes* (min (nfix (- to from)) (if in0 (- cap0 from) (nfix (- to from)))))))
       ((mv code lines2) (fn2-txn-count n (if in0 c0 c1) (if in0 g0 g1) (if in0 from (- from cap0)) lines
                                        okind oslot ogen fn2-core)))
    (mv code (+ from n) lines2)))
(defthm fn2-txn-count-run-natp-1
  (implies (natp from)
           (natp (mv-nth 1 (fn2-txn-count-run from to lines c0 g0 c1 g1 cap0 okind oslot ogen fn2-core))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (disable min nfix))))
(defthm fn2-txn-count-run-natp-2
  (implies (natp lines)
           (natp (mv-nth 2 (fn2-txn-count-run from to lines c0 g0 c1 g1 cap0 okind oslot ogen fn2-core))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (disable min nfix))))
(in-theory (disable fn2-txn-count-run))
(defun fn2-txn-count-next (c0 g0 c1 g1 counted to lines okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (natp counted) (natp to) (natp lines))))
  (fn2-txn-count-run counted to lines c0 g0 c1 g1 (fn2-upload-chunk-cap c0 fn2-core) okind oslot ogen fn2-core))
(in-theory (disable fn2-txn-count-next))

;; The write slots of an accepted POST (C-S3): the identity admission (C
;; §4a; fn2-txn-put-identity), the article row, and the operation outcome,
;; written via the generated per-schema put-row writers (<= 4 calls per fn).
(defun fn2-txn-put-identity-core (tx mslot mgen moff mlen dslot dgen doff okind oslot ogen h principal l fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* (((mv lineage domain incarnation) (fn2-core-origin-values fn2-core))
       ((unless (fn2-origin-tuplep lineage domain incarnation)) (mv :bounds fn2-core))
       ((mv c fn2-core)
        (if (equal l 1)
            (fn2-identity-history-put tx *fn2-txn-slot-history*
              (namespace *fn2-identity-namespace-netnews*) (name mslot mgen moff mlen)
              (profile *fn2-identity-profile-source*) (algorithm *fn2-identity-algorithm-blake3*)
              (digest dslot dgen doff) (lineage lineage) (domain domain)
              (incarnation incarnation) (position :event 0) (evidence :event 0) (article :event 0)
              :owner (okind oslot ogen) fn2-core)
          (mv :ok fn2-core)))
       ((unless (eq c :ok)) (mv c fn2-core))
       ((mv c fn2-core)
        (fn2-identity-evidence-put tx *fn2-txn-slot-evidence*
          (namespace *fn2-identity-namespace-netnews*) (name mslot mgen moff mlen)
          (profile *fn2-identity-profile-source*) (algorithm *fn2-identity-algorithm-blake3*)
          (digest dslot dgen doff) (lineage lineage) (domain domain)
          (incarnation incarnation) (occurrence :event 0)
          (kind *fn2-identity-evidence-kind-binding*) (issuer principal)
          :owner (okind oslot ogen) fn2-core))
       ((unless (eq c :ok)) (mv c fn2-core))
       ((mv c fn2-core)
        (fn2-identity-summary-admit tx *fn2-txn-slot-summary*
          (namespace *fn2-identity-namespace-netnews*) (name mslot mgen moff mlen)
          (ne :new *fn2-txn-slot-evidence*)
          (nr (if (equal l 1) :new :value) (if (equal l 1) *fn2-txn-slot-history* 0))
          (est l) (oldh h)
          :owner (okind oslot ogen) fn2-core))
       ((unless (eq c :ok)) (mv c fn2-core)))
    (fn2-identity-candidates-admit tx *fn2-txn-slot-candidate*
      (namespace *fn2-identity-namespace-netnews*) (name mslot mgen moff mlen)
      (profile *fn2-identity-profile-source*) (algorithm *fn2-identity-algorithm-blake3*)
      (digest dslot dgen doff)
      (ch (if (equal h 0) :out :value)
          (if (equal h 0) (+ (* *fn2-txn-slot-summary* 256) *fn2-identity-summary-entry-field-candidates*) h))
      (ne :new *fn2-txn-slot-evidence*) (q 1) (l l)
      :owner (okind oslot ogen) fn2-core)))
(fn2-core-preserves fn2-txn-put-identity-core
  (tx mslot mgen moff mlen dslot dgen doff okind oslot ogen h principal l fn2-core) :position 1 :rows nil)
(in-theory (disable fn2-txn-put-identity-core))

(defun fn2-txn-put-identity (tx mslot mgen moff mlen dslot dgen doff okind oslot ogen h principal local fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* ((l (if (equal local 1) 1 0))
       ((mv c fn2-core)
        (fn2-txn-put-identity-core tx mslot mgen moff mlen dslot dgen doff okind oslot ogen h principal l fn2-core))
       ((unless (and (eq c :ok) (equal l 1))) (mv c fn2-core)))
    (fn2-identity-article-put tx *fn2-txn-slot-index*
      (namespace *fn2-identity-namespace-netnews*) (name mslot mgen moff mlen)
      (h (if (equal h 0) :out :value)
         (if (equal h 0) (+ (* *fn2-txn-slot-summary* 256) *fn2-identity-summary-entry-field-candidates*) h))
      (article :event 0)
      :owner (okind oslot ogen) fn2-core)))
(fn2-core-preserves fn2-txn-put-identity
  (tx mslot mgen moff mlen dslot dgen doff okind oslot ogen h principal local fn2-core) :position 1 :rows nil)

(defun fn2-txn-put-article (tx mslot mgen moff mlen dslot dgen doff sslot sgen soff hoff hlen bytes lines lunit lepoch lalloc principal op okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* (((mv c fn2-core)
        (fn2-article-put tx *fn2-txn-slot-article*
          (article :event 0) (birth :event 0) (state *fn2-txn-article-live*)
          (version *fn2-txn-article-version*) (source dslot dgen doff)
          (stored-source sslot sgen soff)
          (location-hashes sslot sgen hoff hlen)
          (bytes bytes) (lines lines)
          (location-unit lunit) (location-epoch lepoch) (location-allocation lalloc)
          ;; Raw commitment span's octets are direct; longer sources use
          ;; their source manifest (article-manifest.lisp).
          (location-kind (if (fn2-am-manifestp bytes) *fn2-txn-location-source-manifest* *fn2-txn-location-raw-source*))
          :owner (okind oslot ogen) fn2-core))
       ((unless (eq c :ok)) (mv c fn2-core))
       ;; The operation is the supplied APPEND identity or the member's own
       ;; event. The group numbers are bound after Stage assigns them.
       ((mv c fn2-core)
        (fn2-outcome-put tx *fn2-txn-slot-outcome*
          (principal principal) (operation (if (equal op 0) :event :value) op)
          (id-source (if (equal op 0) *fn2-outcome-id-source-assigned* *fn2-outcome-id-source-supplied*))
          (request dslot dgen doff) (outcome *fn2-txn-outcome-accepted*) (event :event 0)
          (verb *fn2-outcome-verb-append*) (mid mslot mgen moff mlen) (numbers mslot mgen 0 0)
          :owner (okind oslot ogen) fn2-core))
       ((unless (eq c :ok)) (mv c fn2-core)))
    (fn2-successor-arg-octets-late tx *fn2-txn-slot-outcome* *fn2-outcome-entry-field-numbers*
                                  *fn2-overview-octets-max* fn2-core)))
(fn2-core-preserves fn2-txn-put-article (tx mslot mgen moff mlen dslot dgen doff sslot sgen soff hoff hlen bytes lines lunit lepoch lalloc principal op okind oslot ogen fn2-core)
  :position 1 :rows nil)
(in-theory (disable fn2-txn-put-identity fn2-txn-put-article))

;; A POST's slots: the identity admission (a local acceptance) and the
;; article row with its outcome, one call for the declaring run.
(defun fn2-txn-put-post (tx mslot mgen moff mlen dslot dgen doff sslot sgen soff hoff hlen bytes lines lunit lepoch lalloc okind oslot ogen h principal op fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* (((mv c fn2-core)
        (fn2-txn-put-identity tx mslot mgen moff mlen dslot dgen doff okind oslot ogen h principal 1 fn2-core))
       ((unless (eq c :ok)) (mv c fn2-core)))
    (fn2-txn-put-article tx mslot mgen moff mlen dslot dgen doff sslot sgen soff hoff hlen bytes lines lunit lepoch lalloc principal op okind oslot ogen fn2-core)))
(fn2-core-preserves fn2-txn-put-post (tx mslot mgen moff mlen dslot dgen doff sslot sgen soff hoff hlen bytes lines lunit lepoch lalloc okind oslot ogen h principal op fn2-core)
  :position 1 :rows nil)
(in-theory (disable fn2-txn-put-post))

(defun fn2-txn-add-group (tx k group principal c0 g0 c1 g1 noff nlen okind oslot ogen fn2-core)
  ;; Group K's count accept, overview row (its line given late, after stage,
  ;; when the Xref field's numbers exist) and, for the first, the addressing
  ;; entry; its name (NLEN octets at NOFF of chunk 0's Newsgroups field) is
  ;; appended to chunk 1 as one length octet and the name, for the Xref field.
  ;; Chunk 1 is scratch here: the source is durable and counted and its
  ;; retained SOURCE digest already copied into chunk 0 (fn2-txn-put-post-for).
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (natp k))))
  (b* ((ac (fn2-txn-group-slot k))
       (ov (+ 1 ac))
       ((unless (and (natp noff) (posp nlen) (unsigned-byte-p 8 nlen))) (mv :bounds fn2-core))
       ((mv c fn2-core)
        (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
          (c fn2-pool)
          (fn2-gram-put-chain
           (if (equal (nfix k) 0) (fn2-txn-truncate-to 0 c1 g1 okind oslot ogen fn2-pool) (mv :ok fn2-pool))
           (fn2-gram-put nlen c1 g1 okind oslot ogen fn2-pool)
           (fn2-gram-put-span nlen noff c0 g0 c1 g1 okind oslot ogen fn2-pool))
          (mv c fn2-core)))
       ((unless (eq c :ok)) (mv c fn2-core))
       ((mv c fn2-core) (fn2-group-counts-put-accept tx ac ':value group fn2-core))
       ((unless (eq c :ok)) (mv c fn2-core))
       ((mv c fn2-core)
        (fn2-overview-put tx ov (group group)
          (number :out (+ (* ac 256) *fn2-group-counts-entry-field-high*))
          (article :event 0) (position :event 0) (line c0 g0 0 0)
          :owner (okind oslot ogen) fn2-core))
       ((unless (eq c :ok)) (mv c fn2-core))
       ((mv c fn2-core)
        (fn2-successor-arg-octets-late tx ov *fn2-overview-entry-field-line* *fn2-overview-octets-max* fn2-core))
       ((unless (eq c :ok)) (mv c fn2-core)))
    (if (equal (nfix k) 0)
        (fn2-addr-put tx *fn2-txn-slot-addr*
          (principal principal) (position :event 0) (article :event 0)
          (stream group) (reasons 1) fn2-core)
      (mv :ok fn2-core))))
(fn2-core-preserves fn2-txn-add-group (tx k group principal c0 g0 c1 g1 noff nlen okind oslot ogen fn2-core) :position 1 :rows nil
  :hints (("Goal" :in-theory (disable nfix))))
(in-theory (disable fn2-txn-add-group))

(defun fn2-txn-synth-ov (ms mg mo ml scanned at hashed lines slot gen okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core
                  :guard (and (fn2-core-wfp fn2-core) (natp mo) (natp ml) (natp scanned) (natp at) (natp hashed) (natp lines))))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (ov-off ov-len fn2-pool)
    (fn2-txn-synth-ov-pool ms mg mo ml scanned at hashed lines slot gen okind oslot ogen fn2-pool)
    (mv ov-off ov-len fn2-core)))
(fn2-core-preserves fn2-txn-synth-ov (ms mg mo ml scanned at hashed lines slot gen okind oslot ogen fn2-core) :position 2 :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))
(in-theory (disable fn2-txn-synth-ov))

(defun fn2-txn-fill-ov-lines (k j tx c0 g0 ov-off ov-len okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :measure (nfix k)
                  :guard (and (fn2-core-wfp fn2-core) (natp k) (natp j))))
  (if (zp k) (mv :ok fn2-core)
    (mv-let (c fn2-core)
      (fn2-successor-fill-octets tx (+ 1 (fn2-txn-group-slot j))
                                 *fn2-overview-entry-field-line* c0 g0 ov-off ov-len okind oslot ogen fn2-core)
      (if (not (eq c :ok)) (mv c fn2-core)
        (fn2-txn-fill-ov-lines (- k 1) (+ 1 (nfix j)) tx c0 g0 ov-off ov-len okind oslot ogen fn2-core)))))
(fn2-core-preserves fn2-txn-fill-ov-lines (k j tx c0 g0 ov-off ov-len okind oslot ogen fn2-core) :position 1 :rows nil)
(in-theory (disable fn2-txn-fill-ov-lines))

;; One Xref pair of the overview line: " NAME:NUMBER", NAME the length-prefixed
;; name at OFF of chunk 1 (fn2-txn-add-group), appended to chunk 0:
;; (mv code next fn2-pool), NEXT the following name's offset.
(defun fn2-txn-xref-pair-pool (off number c0 g0 c1 g1 okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp off) (natp number))))
  (mv-let (ok len) (fn2-gram-read c1 g1 off okind oslot ogen fn2-pool)
    (if (not ok) (mv :bounds 0 fn2-pool)
      (mv-let (code fn2-pool)
        (fn2-gram-put-chain
         (fn2-gram-put 32 c0 g0 okind oslot ogen fn2-pool)
         (fn2-gram-put-span len (+ 1 off) c1 g1 c0 g0 okind oslot ogen fn2-pool)
         (fn2-gram-put 58 c0 g0 okind oslot ogen fn2-pool)
         (fn2-gram-put-number number c0 g0 okind oslot ogen fn2-pool))
        (mv code (+ 1 off len) fn2-pool)))))
(fn2-pool-preserves fn2-txn-xref-pair-pool (off number c0 g0 c1 g1 okind oslot ogen fn2-pool) :position 2 :rows nil)
(defthm fn2-txn-xref-pair-pool-natp
  (implies (natp off) (natp (mv-nth 1 (fn2-txn-xref-pair-pool off number c0 g0 c1 g1 okind oslot ogen fn2-pool))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn2-txn-xref-pair-pool))))
(in-theory (disable fn2-txn-xref-pair-pool))
;; The pairs of groups J.. (K of them): each group's staged number (the
;; overview slot's number, assigned at stage) after its name.
(defun fn2-txn-xref-pairs (k j tx off c0 g0 c1 g1 okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :measure (nfix k)
                  :guard (and (fn2-core-wfp fn2-core) (natp k) (natp j) (natp off))))
  (if (zp k) (mv :ok fn2-core)
    (b* (((mv vcode number)
          (fn2-successor-out tx (+ 1 (fn2-txn-group-slot j)) *fn2-overview-entry-field-number* fn2-core))
         ((unless (and (eq vcode :ok) (natp number))) (mv :bounds fn2-core))
         ((mv code next fn2-core)
          (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
            (code next fn2-pool)
            (fn2-txn-xref-pair-pool off number c0 g0 c1 g1 okind oslot ogen fn2-pool)
            (mv code next fn2-core)))
         ((unless (eq code :ok)) (mv code fn2-core)))
      (fn2-txn-xref-pairs (- k 1) (+ 1 (nfix j)) tx next c0 g0 c1 g1 okind oslot ogen fn2-core))))
(fn2-core-preserves fn2-txn-xref-pairs (k j tx off c0 g0 c1 g1 okind oslot ogen fn2-core) :position 1 :rows nil
  :hints (("Goal" :in-theory (disable nfix))))
(in-theory (disable fn2-txn-xref-pairs))
;; Count exactly the digits the existing bounded number renderer emits.
;; In particular this uses its power selection and its twenty-step fuel;
;; it does not introduce a separate decimal formatting policy.
(defun fn2-txn-xref-digits (left power)
  (declare (xargs :guard (and (natp left) (natp power)) :measure (nfix left)))
  (if (or (zp left) (zp power)) 0
    (+ 1 (fn2-txn-xref-digits (- left 1) (fn2-gram-next-power power)))))
(defthm fn2-txn-xref-digits-natp
  (natp (fn2-txn-xref-digits left power)) :rule-classes :type-prescription)

;; Before any output, inspect only each saved length octet and actual staged
;; number. Oversized/refused work never traverses the names. TOTAL includes
;; the existing overview, TAB/Xref prefix and actual path identity length.
(defun fn2-txn-xref-size (k j tx off total c1 g1 okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :measure (nfix k)
                  :guard (and (fn2-core-wfp fn2-core) (natp k) (natp j)
                              (natp off) (natp total))))
  (b* (((when (> total *fn2-overview-octets-max*)) (mv :bounds total))
       ((when (zp k)) (mv :ok total))
       ((mv vcode number)
        (fn2-successor-out tx (+ 1 (fn2-txn-group-slot j)) *fn2-overview-entry-field-number* fn2-core))
       ((unless (and (eq vcode :ok) (natp number))) (mv :bounds total))
       ((mv readable nlen)
        (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
          (readable nlen) (fn2-gram-read c1 g1 off okind oslot ogen fn2-pool)
          (mv readable nlen)))
       ((unless readable) (mv :bounds total))
       (digits (fn2-txn-xref-digits 20 (fn2-gram-pow10 20 number 1))))
    (fn2-txn-xref-size (- k 1) (+ 1 j) tx (+ off 1 nlen)
                       (+ total 2 nlen digits) c1 g1 okind oslot ogen fn2-core)))

(defthm fn2-txn-xref-size-natp
  (implies (natp total)
           (natp (mv-nth 1 (fn2-txn-xref-size k j tx off total c1 g1 okind oslot ogen fn2-core))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn2-txn-xref-size))))
(in-theory (disable fn2-txn-xref-digits fn2-txn-xref-size))

;; Cost after preflight: if W appended bytes comprise prefix 7, path P,
;; names N, pair punctuation 2K and digits D, W=7+P+N+2K+D.
;; Output W + names/path reads N+P + two length reads per group 2K
;; is 2W-7-D <= 2041. Refusal before output reads at most K length
;; octets. Filling the staged overview rows below binds references only.
;; The overview line's Xref field (PRF-206, RFC 5536 3.2.14), after stage:
;; TAB "Xref: " the node's path identity, then " NAME:NUMBER" for each of the
;; K groups, appended to the line synthesized at OV-OFF of chunk 0 (it ends
;; at chunk 0's fill); each group's overview slot is then given the whole
;; line. A line past the overview row's bound is :bounds (the transaction
;; refuses it as unaffordable).
(defun fn2-txn-xref (tx k c0 g0 c1 g1 ov-off okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (natp k) (natp ov-off))))
  (b* (((unless (<= k *fn2-txn-groups-max*)) (mv :bounds 0 0 fn2-core))
       ((mv before path-length)
        (stobj-let ((fn2-pool (fn2-core-pool fn2-core)) (fn2-control (fn2-core-control fn2-core)))
          (before path-length)
          (mv (fn2-gram-fill c0 fn2-pool) (fn2-control-path-identity-length fn2-control))
          (mv before path-length)))
       ((unless (<= ov-off before)) (mv :bounds 0 0 fn2-core))
       ((mv size-code expected)
        (fn2-txn-xref-size k 0 tx 0 (+ (- before ov-off) 1 (length "Xref: ") path-length)
                           c1 g1 okind oslot ogen fn2-core))
       ((unless (eq size-code :ok)) (mv :bounds 0 0 fn2-core))
       ((mv code fn2-core)
        (stobj-let ((fn2-pool (fn2-core-pool fn2-core)) (fn2-control (fn2-core-control fn2-core)))
          (code fn2-pool)
          (fn2-gram-put-chain
           (fn2-gram-put 9 c0 g0 okind oslot ogen fn2-pool)
           (fn2-gram-put-template 0 "Xref: " 0 0 0 0 c0 g0 0 0 c0 g0 okind oslot ogen fn2-pool)
           (fn2-upload-put-path 0 c0 g0 okind oslot ogen fn2-control fn2-pool))
          (mv code fn2-core)))
       ((unless (eq code :ok)) (mv code 0 0 fn2-core))
       (numbers-off (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (f) (fn2-gram-fill c0 fn2-pool) f))
       ((mv code fn2-core) (fn2-txn-xref-pairs k 0 tx 0 c0 g0 c1 g1 okind oslot ogen fn2-core))
       ((unless (eq code :ok)) (mv code 0 0 fn2-core))
       (ov-end (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (f) (fn2-gram-fill c0 fn2-pool) f))
       ((unless (and (<= ov-off ov-end) (equal (- ov-end ov-off) expected)
                     (<= expected *fn2-overview-octets-max*)
                     (<= ov-off numbers-off) (< numbers-off ov-end))) (mv :bounds 0 0 fn2-core))
       (numbers-len (- ov-end numbers-off))
       ((mv line-code fn2-core)
        (fn2-txn-fill-ov-lines k 0 tx c0 g0 ov-off (- ov-end ov-off) okind oslot ogen fn2-core))
       ((unless (eq line-code :ok)) (mv line-code 0 0 fn2-core))
       ((mv outcome-code fn2-core)
        (fn2-successor-fill-octets tx *fn2-txn-slot-outcome* *fn2-outcome-entry-field-numbers*
                                  c0 g0 numbers-off numbers-len okind oslot ogen fn2-core)))
    (mv outcome-code numbers-off numbers-len fn2-core)))
(fn2-core-preserves fn2-txn-xref (tx k c0 g0 c1 g1 ov-off okind oslot ogen fn2-core) :position 3 :rows nil
  :hints (("Goal" :in-theory (disable nfix))))
(in-theory (disable fn2-txn-xref))

;; The article's location is its upload's payload extent: the extent's first
;; physical unit (an extent is *fn2-storage-extent-units* units) and its handle; its
;; length the stored octets' (the injected field's ILEN and the source's HASHED).
(defun fn2-txn-put-post-for (tx ms mg mo ml c0 g0 scanned hashed ilen ds dg doff h principal lines pext pepoch palloc
                                sslot sgen soff hoff hlen op okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core
                  :guard (and (fn2-core-wfp fn2-core) (natp mo) (natp ml) (natp scanned) (natp hashed) (natp ilen)
                              (natp lines))))
  ;; The source is durable at the location (the upload stored and fenced it
  ;; before :sealed) and its lines are counted, so chunk 0 after the header is
  ;; scratch: the digest moves to SCANNED in chunk 0 (wherever the source's
  ;; length put it) and the overview line's first seven fields follow it
  ;; (the groups' Xref field is appended after stage, fn2-txn-xref), and
  ;; chunk 1 is free for the group names and then the emission (:ready)
  ;; however far the source runs into it.
  (b* ((cap0 (fn2-upload-chunk-cap c0 fn2-core))
       ((mv c fn2-core)
        (if (<= (+ scanned *fn2-upload-digest-octets*) cap0)
            (fn2-core-copy-range ds dg doff c0 g0 scanned *fn2-upload-digest-octets*
                                 okind oslot ogen fn2-core)
          (mv :bounds fn2-core)))
       ((unless (eq c :ok)) (mv c fn2-core))
       ((mv c fn2-core)
        (fn2-txn-put-post tx ms mg mo ml c0 g0 scanned sslot sgen soff hoff hlen (+ hashed ilen) lines
                          (* *fn2-storage-extent-units* (nfix pext)) pepoch palloc okind oslot ogen h principal op fn2-core))
       ((unless (eq c :ok)) (mv c fn2-core))
       ((mv ov-off ov-len fn2-core)
        (fn2-txn-synth-ov ms mg mo ml scanned scanned (+ hashed ilen) lines c0 g0 okind oslot ogen fn2-core)))
    (mv (if (and (equal ov-off (+ scanned *fn2-upload-digest-octets*)) (posp ov-len)) :ok :bounds) fn2-core)))
(fn2-core-preserves fn2-txn-put-post-for
  (tx ms mg mo ml c0 g0 scanned hashed ilen ds dg doff h principal lines pext pepoch palloc sslot sgen soff hoff hlen op okind oslot ogen fn2-core) :position 1 :rows nil)
(defun fn2-txn-put-evidence-for (tx ms mg mo ml ds dg doff h principal op okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* (((mv code fn2-core)
        (fn2-txn-put-identity tx ms mg mo ml ds dg doff okind oslot ogen h principal 0 fn2-core))
       ((unless (and (eq code :ok) (not (equal op 0)))) (mv code fn2-core)))
    (fn2-outcome-put tx *fn2-txn-slot-outcome*
      (principal principal) (operation op) (id-source *fn2-outcome-id-source-supplied*) (request ds dg doff)
      (outcome *fn2-txn-outcome-conflict*) (event :event 0)
      (verb *fn2-outcome-verb-append*) (mid ms mg mo ml) (numbers ms mg 0 0)
      :owner (okind oslot ogen) fn2-core)))
(fn2-core-preserves fn2-txn-put-evidence-for (tx ms mg mo ml ds dg doff h principal op okind oslot ogen fn2-core)
  :position 1 :rows nil)
(in-theory (disable fn2-txn-put-post-for fn2-txn-put-evidence-for))

(defun fn2-txn-prebind-slots (k i tx b0 event fn2-succ-slots fn2-fields)
  (declare (xargs :stobjs (fn2-succ-slots fn2-fields) :measure (nfix k)
                  :guard (and (fn2-succ-slots-wfp fn2-succ-slots) (fn2-fields-wfp fn2-fields)
                              (natp i) (natp tx) (natp b0))))
  (b* (((unless (and (posp k) (natp i) (< i *fn2-succ-slots*))) fn2-fields)
       (s (+ (* (nfix tx) *fn2-succ-slots*) i))
       ((unless (and (< s (fn2-succ-slots-rows fn2-succ-slots))
                     (not (equal (fn2-succ-slots-phase s fn2-succ-slots) *fn2-succ-slot-phase-empty*))
                     (equal (fn2-succ-slots-kind s fn2-succ-slots) *fn2-succ-kind-insert*)))
        (fn2-txn-prebind-slots (- k 1) (+ 1 i) tx b0 event fn2-succ-slots fn2-fields))
       (entry (+ (nfix b0) (* *fn2-succ-block* i)))
       (fn2-fields (fn2-succ-fill-events *fn2-succ-fields-max* 0 entry (fn2-succ-slots-events s fn2-succ-slots) event fn2-fields)))
    (fn2-txn-prebind-slots (- k 1) (+ 1 i) tx b0 event fn2-succ-slots fn2-fields)))
(fn2-fields-preserves fn2-txn-prebind-slots (k i tx b0 event fn2-succ-slots fn2-fields) :position nil :raw-rows t
  :hints (("Goal" :in-theory (disable fn2-succ-fill-events))))
(in-theory (disable fn2-txn-prebind-slots))

(defun fn2-txn-prospective-event (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* (((mv pick id &) (fn2-commit-pick fn2-core))
       ((when (and (eq pick :join) (fn2-commit-idp id fn2-core)))
        (+ (nfix (fn2-commit-row-first-key id fn2-core)) (nfix (fn2-commit-row-member-count id fn2-core))))
       ((mv & key & &) (fn2-commit-frontier fn2-core)))
    (nfix key)))
(defthm fn2-txn-prospective-event-natp
  (natp (fn2-txn-prospective-event fn2-core))
  :rule-classes :type-prescription)
(in-theory (disable fn2-txn-prospective-event))

(defun fn2-txn-prebind (tx fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (let ((event (fn2-txn-prospective-event fn2-core)))
    (stobj-let ((fn2-succ-slots (fn2-core-succ-slots fn2-core))
                (fn2-id-decides (fn2-core-id-decides fn2-core))
                (fn2-fields (fn2-core-fields fn2-core))
                (fn2-fc (fn2-core-fc fn2-core)))
      (fn2-fields)
      (mv-let (c b0) (fn2-idc-stripe tx (fn2-fc-rows fn2-fc) fn2-id-decides fn2-fields)
        (if (eq c :ok)
            (fn2-txn-prebind-slots *fn2-succ-slots* 0 tx b0 event fn2-succ-slots fn2-fields)
          fn2-fields))
      (mv :ok fn2-core))))
(fn2-core-preserves fn2-txn-prebind (tx fn2-core) :position 1 :rows nil
  :hints (("Goal" :in-theory (disable nfix))))
(in-theory (disable fn2-txn-prebind))
))

;; ------------------------------------------------------------------------
;; The transaction's continuations (materialized after the upload's).
(defmacro fn2-txn-events ()
 '(progn
(defmachine-arms fn2-txn)
(defmachine-run fn2-txn)
))
