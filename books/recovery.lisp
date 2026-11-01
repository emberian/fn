; B5 recovery, table level: the candidate directory, the named outcomes and
; the read-only byte helpers the recovery machine (machines-b) composes.
; The machine scans every frame position of the arena (STORAGE-DESIGN-ASTRA
; part G), never trusting a length or next pointer from an unchecked frame.
(in-package "ACL2")
(include-book "commit-format")
(include-book "alloc")
(fn2-book-layer :b)
(local (in-theory (disable fn2-digests-rows fn2-digestsp fn2-digests-wfp fn2-poolp fn2-pool-wfp
 fn2-fc-context-rows fn2-fc-contextp fn2-fc-context-wfp)))

; One row per arena position, written once by discovery before the chain
; pass reads it. Digest rows live in the recovery region of fn2-digests.
(defcolumns fn2-rec-cand
 ((status (:enum fn2-rec-status (:unread :empty :invalid :unreadable :candidate :chained)))
  (commit :u60) (epoch :u60) (allocation :u60) (first :u60) (last :u60)
  (seal-off :u32) (seal-len :u32)))

; Classification and witness outcome vocabularies (ROUND2 §E.4, scholar ch. 4).
(make-event (value (cons 'progn (fn2-columns-enum-constants
 'fn2-rec-class '(:none :intact :torn-tail :damaged :unknown) 0))))
(make-event (value (cons 'progn (fn2-columns-enum-constants
 'fn2-rec-witness '(:none :uncredited :consistent :rollback-detected :discontinuity) 0))))
(defconst *fn2-rec-classes* '(:none :intact :torn-tail :damaged :unknown))
(defconst *fn2-rec-witness-outcomes* '(:none :uncredited :consistent :rollback-detected :discontinuity))
; Discovery reads only seal frames; chain verification reads all three units.
(make-event (value (cons 'progn (fn2-columns-enum-constants
 'fn2-rec-mode '(:discover :chain) 0))))
; B-ASSUMPTIONS-AS-PARAMETERS: the profile's assumption bits are recovery
; inputs. :torn-tail needs crash-only AND A-PERSISTENCE-FENCE; a witness
; is credited only under A-INDEPENDENT-FRONTIER. A-INTEGRITY-EVIDENCE scopes
; the report: recovery checks every hash regardless, and never concludes
; :damaged from a checksum alone (a valid successor may follow a torn leader).
(defconst *fn2-rec-assume-crash-only* 1)
(defconst *fn2-rec-assume-fence* 2)
(defconst *fn2-rec-assume-integrity* 4)
(defconst *fn2-rec-assume-frontier* 8)
(defun fn2-rec-assumep (assume bit)
 (declare (xargs :guard (and (natp assume) (natp bit))))
 (not (equal (logand assume bit) 0)))

; Digest-row layout of the recovery region (base = first row past the commit
; directory): per position p, rows 4p..4p+3 hold final seal, previous seal,
; record-stream commitment and dependency hash; then the chain's previous
; seal, the presented witness seal and one scratch row.
(defconst *fn2-rec-final* 0)
(defconst *fn2-rec-previous* 1)
(defconst *fn2-rec-records* 2)
(defconst *fn2-rec-dependency* 3)
(defun fn2-rec-digest-rows (extents)
 (declare (xargs :guard (natp extents)))
 (+ 3 (* 4 extents)))
(defun fn2-rec-row (base p k)
 (declare (xargs :guard (and (natp base) (natp p) (natp k))))
 (+ base (* 4 p) k))
(defun fn2-rec-chain-row (base extents)
 (declare (xargs :guard (and (natp base) (natp extents))))
 (+ base (* 4 extents)))
(defun fn2-rec-witness-row (base extents)
 (declare (xargs :guard (and (natp base) (natp extents))))
 (+ base (* 4 extents) 1))
(defun fn2-rec-scratch-row (base extents)
 (declare (xargs :guard (and (natp base) (natp extents))))
 (+ base (* 4 extents) 2))

; Recovery owns the third checker continuation (format row 2) and its field
; range; commit rows 0 and 1 keep theirs. One 4 KiB unit is verified at a time.
(defconst *fn2-rec-checker-row* 2)
(defconst *fn2-rec-field-base* 256)

; Any nonzero byte in [off, off+left)? Pool refusal propagates unchanged.
(defun fn2-rec-nonzero (left slot gen off okind oslot ogen fn2-pool)
 (declare (xargs :stobjs fn2-pool :measure (nfix left)
  :guard (and (fn2-pool-wfp fn2-pool) (natp left) (natp off))))
 (if (zp left) (mv :ok nil)
  (mv-let (code byte) (fn2-pool-read slot gen off okind oslot ogen fn2-pool)
   (cond ((not (eq code :ok)) (mv code nil))
         ((not (equal byte 0)) (mv :ok t))
         (t (fn2-rec-nonzero (- left 1) slot gen (+ 1 off) okind oslot ogen fn2-pool))))))

(defun fn2-rec-byte-at (slot gen off okind oslot ogen fn2-pool)
 (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp off))))
 (mv-let (code byte) (fn2-pool-read slot gen off okind oslot ogen fn2-pool)
  (mv code (if (and (eq code :ok) (unsigned-byte-p 8 byte)) byte 0))))
(defthm fn2-rec-byte-at-natp
 (natp (mv-nth 1 (fn2-rec-byte-at slot gen off okind oslot ogen fn2-pool)))
 :rule-classes :type-prescription)
(defthm fn2-rec-byte-at-bound
 (< (mv-nth 1 (fn2-rec-byte-at slot gen off okind oslot ogen fn2-pool)) 256)
 :rule-classes :linear)
(in-theory (disable fn2-rec-byte-at))

; Load 32 little-endian bytes at off into digest row dst, word k first.
(defun fn2-rec-fetch (k dst slot gen off okind oslot ogen fn2-pool fn2-digests)
 (declare (xargs :stobjs (fn2-pool fn2-digests) :measure (nfix (- 8 (nfix k)))
  :guard (and (fn2-pool-wfp fn2-pool) (fn2-digest-rowp dst fn2-digests)
              (natp k) (<= k 8) (natp off))))
 (if (or (not (natp k)) (>= k 8)) (mv :ok fn2-digests)
  (b* ((at (+ off (* 4 k)))
       ((mv c0 b0) (fn2-rec-byte-at slot gen at okind oslot ogen fn2-pool))
       ((mv c1 b1) (fn2-rec-byte-at slot gen (+ 1 at) okind oslot ogen fn2-pool))
       ((mv c2 b2) (fn2-rec-byte-at slot gen (+ 2 at) okind oslot ogen fn2-pool))
       ((mv c3 b3) (fn2-rec-byte-at slot gen (+ 3 at) okind oslot ogen fn2-pool))
       ((unless (and (eq c0 :ok) (eq c1 :ok) (eq c2 :ok) (eq c3 :ok)))
        (mv (if (eq c0 :ok) (if (eq c1 :ok) (if (eq c2 :ok) c3 c2) c1) c0) fn2-digests))
       (word (+ b0 (* 256 b1) (* 65536 b2) (* 16777216 b3)))
       (fn2-digests (fn2-digest-set-word dst k word fn2-digests)))
   (fn2-rec-fetch (+ 1 k) dst slot gen off okind oslot ogen fn2-pool fn2-digests))))
(defthm fn2-rec-fetch-shape
 (implies (and (fn2-digestsp fn2-digests) (fn2-digest-rowp dst fn2-digests))
  (and (fn2-digestsp (mv-nth 1 (fn2-rec-fetch k dst slot gen off okind oslot ogen fn2-pool fn2-digests)))
       (fn2-digests-wfp (mv-nth 1 (fn2-rec-fetch k dst slot gen off okind oslot ogen fn2-pool fn2-digests)))
       (equal (fn2-digests-rows (mv-nth 1 (fn2-rec-fetch k dst slot gen off okind oslot ogen fn2-pool fn2-digests)))
              (fn2-digests-rows fn2-digests))))
 :hints (("Goal" :in-theory (disable fn2-digestsp fn2-digests-wfp fn2-digests-rows))))
(in-theory (disable fn2-rec-fetch))

(defun fn2-rec-zero-digest (dst fn2-digests)
 (declare (xargs :stobjs fn2-digests :guard (fn2-digest-rowp dst fn2-digests)))
 (let* ((fn2-digests (fn2-digest-set-word dst 0 0 fn2-digests))
        (fn2-digests (fn2-digest-set-word dst 1 0 fn2-digests))
        (fn2-digests (fn2-digest-set-word dst 2 0 fn2-digests))
        (fn2-digests (fn2-digest-set-word dst 3 0 fn2-digests))
        (fn2-digests (fn2-digest-set-word dst 4 0 fn2-digests))
        (fn2-digests (fn2-digest-set-word dst 5 0 fn2-digests))
        (fn2-digests (fn2-digest-set-word dst 6 0 fn2-digests)))
  (fn2-digest-set-word dst 7 0 fn2-digests)))
(defthm fn2-rec-zero-digest-shape
 (implies (and (fn2-digestsp fn2-digests) (fn2-digest-rowp dst fn2-digests))
  (and (fn2-digestsp (fn2-rec-zero-digest dst fn2-digests))
       (fn2-digests-wfp (fn2-rec-zero-digest dst fn2-digests))
       (equal (fn2-digests-rows (fn2-rec-zero-digest dst fn2-digests)) (fn2-digests-rows fn2-digests))))
 :hints (("Goal" :in-theory (disable fn2-digestsp fn2-digests-wfp fn2-digests-rows))))
(in-theory (disable fn2-rec-zero-digest))

; Expected context for one unit of position p, from the candidate's own
; identity. History and incarnation are the genesis base's (1, 1).
(defun fn2-rec-context (row p role epoch allocation commit page-hash previous geometry fn2-fc-context)
 (declare (xargs :stobjs fn2-fc-context
  :guard (and (fn2-fc-context-wfp fn2-fc-context) (natp row) (< row (fn2-fc-context-rows fn2-fc-context))
              (unsigned-byte-p 32 p) (natp role) (< role 3) (unsigned-byte-p 60 epoch)
              (unsigned-byte-p 60 allocation) (unsigned-byte-p 60 commit)
              (unsigned-byte-p 32 page-hash) (unsigned-byte-p 32 previous) (unsigned-byte-p 32 geometry))))
 (let* ((fn2-fc-context (fn2-fc-context-set-location row (+ (* 3 p) role) fn2-fc-context))
        (fn2-fc-context (fn2-fc-context-set-allocation row allocation fn2-fc-context))
        (fn2-fc-context (fn2-fc-context-set-history row 1 fn2-fc-context))
        (fn2-fc-context (fn2-fc-context-set-incarnation row 1 fn2-fc-context))
        (fn2-fc-context (fn2-fc-context-set-writer-epoch row epoch fn2-fc-context))
        (fn2-fc-context (fn2-fc-context-set-commit row commit fn2-fc-context))
        (fn2-fc-context (fn2-fc-context-set-page-kind row *page-kind-manifest* fn2-fc-context))
        (fn2-fc-context (fn2-fc-context-set-encoded-length row *fn2-commit-unit-bytes* fn2-fc-context))
        (fn2-fc-context (fn2-fc-context-set-hash row page-hash fn2-fc-context))
        (fn2-fc-context (fn2-fc-context-set-geometry row geometry fn2-fc-context))
        (fn2-fc-context (fn2-fc-context-set-extent-writer-epoch row epoch fn2-fc-context))
        (fn2-fc-context (fn2-fc-context-set-previous-commit row (if (zp commit) 0 (- commit 1)) fn2-fc-context))
        (fn2-fc-context (fn2-fc-context-set-previous-seal row previous fn2-fc-context)))
  (fn2-fc-context-set-extent row p fn2-fc-context)))
(defthm fn2-rec-context-shape
 (implies (and (fn2-fc-contextp fn2-fc-context) (fn2-fc-context-wfp fn2-fc-context)
               (natp row) (< row (fn2-fc-context-rows fn2-fc-context))
               (unsigned-byte-p 32 p) (natp role) (< role 3) (unsigned-byte-p 60 epoch)
               (unsigned-byte-p 60 allocation) (unsigned-byte-p 60 commit)
               (unsigned-byte-p 32 page-hash) (unsigned-byte-p 32 previous) (unsigned-byte-p 32 geometry))
  (and (fn2-fc-contextp (fn2-rec-context row p role epoch allocation commit page-hash previous geometry fn2-fc-context))
       (fn2-fc-context-wfp (fn2-rec-context row p role epoch allocation commit page-hash previous geometry fn2-fc-context))
       (equal (fn2-fc-context-rows (fn2-rec-context row p role epoch allocation commit page-hash previous geometry fn2-fc-context))
              (fn2-fc-context-rows fn2-fc-context))
       (equal (fn2-fc-context-hash row (fn2-rec-context row p role epoch allocation commit page-hash previous geometry fn2-fc-context)) page-hash)
       (equal (fn2-fc-context-geometry row (fn2-rec-context row p role epoch allocation commit page-hash previous geometry fn2-fc-context)) geometry)
       (equal (fn2-fc-context-previous-seal row (fn2-rec-context row p role epoch allocation commit page-hash previous geometry fn2-fc-context)) previous))))
(in-theory (disable fn2-rec-context))

; The classification rule, stated once over the machine's evidence words.
; damaged: a credited independent witness contradicts the chain. unknown:
; an unreadable or branching chain, or a dirty arena under a profile that
; cannot exclude lost acknowledged history. torn-tail: dirty arena under
; crash-only with honest fences. intact: nothing beyond the chain.
(defun fn2-rec-classify (assume dirty ambiguous witness-outcome)
 (declare (xargs :guard (natp assume)))
 (cond ((member-equal witness-outcome (list *fn2-rec-witness-rollback-detected* *fn2-rec-witness-discontinuity*))
        *fn2-rec-class-damaged*)
       (ambiguous *fn2-rec-class-unknown*)
       ((not dirty) *fn2-rec-class-intact*)
       ((and (fn2-rec-assumep assume *fn2-rec-assume-crash-only*)
             (fn2-rec-assumep assume *fn2-rec-assume-fence*)) *fn2-rec-class-torn-tail*)
       (t *fn2-rec-class-unknown*)))
(defthm fn2-rec-classify-type
 (and (natp (fn2-rec-classify assume dirty ambiguous witness-outcome))
      (< (fn2-rec-classify assume dirty ambiguous witness-outcome) 5))
 :rule-classes ((:type-prescription :typed-term (fn2-rec-classify assume dirty ambiguous witness-outcome))
                (:linear :corollary (< (fn2-rec-classify assume dirty ambiguous witness-outcome) 5))))

; Witness comparison (scholar ch. 4 §4.4 item 10): compared against the
; reconstructed chain; uncredited without A-INDEPENDENT-FRONTIER.
(defun fn2-rec-witness-outcome (assume witness chain matches)
 (declare (xargs :guard (and (natp assume) (natp witness) (natp chain))))
 (cond ((zp witness) *fn2-rec-witness-none*)
       ((not (fn2-rec-assumep assume *fn2-rec-assume-frontier*)) *fn2-rec-witness-uncredited*)
       ((< chain witness) *fn2-rec-witness-rollback-detected*)
       (matches *fn2-rec-witness-consistent*)
       (t *fn2-rec-witness-discontinuity*)))
(defthm fn2-rec-witness-outcome-type
 (and (natp (fn2-rec-witness-outcome assume witness chain matches))
      (< (fn2-rec-witness-outcome assume witness chain matches) 5))
 :rule-classes ((:type-prescription :typed-term (fn2-rec-witness-outcome assume witness chain matches))
                (:linear :corollary (< (fn2-rec-witness-outcome assume witness chain matches) 5))))

; Decoded seal-frame header at the recovery field base: is it a seal frame of
; position p in the genesis lineage? Returns the identity it claims.
(defun fn2-rec-field (k fn2-fields)
 (declare (xargs :stobjs fn2-fields
  :guard (and (fn2-fields-wfp fn2-fields) (natp k) (< k *fn2-format-sealed-batch-num-fields*)
              (<= (+ *fn2-rec-field-base* *fn2-format-sealed-batch-num-fields*) (fn2-fields-rows fn2-fields)))))
 (fn2-fields-value (+ *fn2-rec-field-base* k) fn2-fields))
(defun fn2-rec-field-off (k fn2-fields)
 (declare (xargs :stobjs fn2-fields
  :guard (and (fn2-fields-wfp fn2-fields) (natp k) (< k *fn2-format-sealed-batch-num-fields*)
              (<= (+ *fn2-rec-field-base* *fn2-format-sealed-batch-num-fields*) (fn2-fields-rows fn2-fields)))))
 (fn2-fields-ref-off (+ *fn2-rec-field-base* k) fn2-fields))
(defmacro fn2-rec-fieldsp ()
 '(and (fn2-fields-wfp fn2-fields)
       (<= (+ *fn2-rec-field-base* *fn2-format-sealed-batch-num-fields*) (fn2-fields-rows fn2-fields))))
(defun fn2-rec-header-check (p fn2-fields)
 (declare (xargs :stobjs fn2-fields :guard (and (fn2-rec-fieldsp) (natp p))))
 (let ((commit (fn2-rec-field *fn2-format-frame-header-field-commit* fn2-fields))
       (epoch (fn2-rec-field *fn2-format-frame-header-field-writer-epoch* fn2-fields))
       (allocation (fn2-rec-field *fn2-format-frame-header-field-extent-allocation* fn2-fields))
       (payload (fn2-rec-field *fn2-format-frame-header-field-payload-length* fn2-fields)))
  (mv (and (equal (fn2-rec-field *fn2-format-frame-header-field-magic* fn2-fields) *fn2-format-frame-magic*)
           (equal (fn2-rec-field *fn2-format-frame-header-field-frame-kind* fn2-fields) *frame-kind-seal*)
           (equal (fn2-rec-field *fn2-format-frame-header-field-ordinal* fn2-fields) 1)
           (equal (fn2-rec-field *fn2-format-frame-header-field-fragment-offset* fn2-fields) 0)
           (equal (fn2-rec-field *fn2-format-frame-header-field-history* fn2-fields) 1)
           (equal (fn2-rec-field *fn2-format-frame-header-field-incarnation* fn2-fields) 1)
           (equal (fn2-rec-field *fn2-format-frame-header-field-extent* fn2-fields) p)
           (equal (fn2-rec-field *fn2-format-frame-header-field-extent-writer-epoch* fn2-fields) epoch)
           (posp commit) (unsigned-byte-p 60 commit) (unsigned-byte-p 60 epoch)
           (unsigned-byte-p 60 allocation) (natp payload) (<= payload *fn2-commit-unit-bytes*))
      commit epoch allocation payload)))
(defun fn2-rec-digest-fieldp (k fn2-fields)
 (declare (xargs :stobjs fn2-fields
  :guard (and (fn2-rec-fieldsp) (natp k) (< k *fn2-format-sealed-batch-num-fields*))))
 (and (equal (fn2-rec-field k fn2-fields) 1)
      (<= (+ 32 (fn2-rec-field-off k fn2-fields)) *fn2-commit-unit-bytes*)))
; The decoded sealed batch must name the same identity as its frame.
(defun fn2-rec-seal-check (p commit epoch allocation fn2-fields)
 (declare (xargs :stobjs fn2-fields :guard (and (fn2-rec-fieldsp) (natp p))))
 (let ((first (fn2-rec-field *fn2-format-sealed-batch-field-event-first* fn2-fields))
       (last (fn2-rec-field *fn2-format-sealed-batch-field-event-last* fn2-fields)))
  (mv (and (equal (fn2-rec-field *fn2-format-sealed-batch-field-history* fn2-fields) 1)
           (equal (fn2-rec-field *fn2-format-sealed-batch-field-incarnation* fn2-fields) 1)
           (equal (fn2-rec-field *fn2-format-sealed-batch-field-extent* fn2-fields) p)
           (equal (fn2-rec-field *fn2-format-sealed-batch-field-extent-writer-epoch* fn2-fields) epoch)
           (equal (fn2-rec-field *fn2-format-sealed-batch-field-extent-allocation* fn2-fields) allocation)
           (equal (fn2-rec-field *fn2-format-sealed-batch-field-commit* fn2-fields) commit)
           (equal (fn2-rec-field *fn2-format-sealed-batch-field-previous-commit* fn2-fields) (- (nfix commit) 1))
           (<= first last)
           (fn2-rec-digest-fieldp *fn2-format-sealed-batch-field-previous-seal* fn2-fields)
           (fn2-rec-digest-fieldp *fn2-format-sealed-batch-field-final-seal* fn2-fields)
           (fn2-rec-digest-fieldp *fn2-format-sealed-batch-field-record-stream* fn2-fields)
           (fn2-rec-digest-fieldp *fn2-format-sealed-batch-field-dependencies-expected-hash* fn2-fields))
      first last)))

; Search for the unique successor of the chain: a candidate whose commit is
; TARGET and whose previous seal equals the chain row. A second match is a
; branch, which recovery never resolves by position.
(defun fn2-rec-search (left p arena target found twice base fn2-rec-cand fn2-digests)
 (declare (xargs :stobjs (fn2-rec-cand fn2-digests) :measure (nfix left)
  :guard (and (fn2-rec-cand-wfp fn2-rec-cand) (natp left) (natp p) (natp arena) (natp base))))
 (if (or (zp left) (not (natp p)) (>= p arena) (>= p (fn2-rec-cand-rows fn2-rec-cand))) (mv p found twice)
  (let* ((prev (fn2-rec-row base p *fn2-rec-previous*))
         (chain (fn2-rec-chain-row base arena))
         (match (and (equal (fn2-rec-cand-status p fn2-rec-cand) *fn2-rec-status-candidate*)
                     (equal (fn2-rec-cand-commit p fn2-rec-cand) target)
                     (fn2-digest-rowp prev fn2-digests) (fn2-digest-rowp chain fn2-digests)
                     (fn2-digest-equal prev chain fn2-digests))))
   (fn2-rec-search (- left 1) (+ 1 p) arena target
    (if (and match (equal found *fn2-alloc-none*)) p found)
    (or twice (and match (not (equal found *fn2-alloc-none*)))) base fn2-rec-cand fn2-digests))))

; Anything beyond the chain: a position that is neither empty nor chained.
(defun fn2-rec-dirty (left p high dirty fn2-rec-cand)
 (declare (xargs :stobjs fn2-rec-cand :measure (nfix left)
  :guard (and (fn2-rec-cand-wfp fn2-rec-cand) (natp left) (natp p) (natp high))))
 (if (or (zp left) (not (natp p)) (>= p high) (>= p (fn2-rec-cand-rows fn2-rec-cand))) (mv p dirty)
  (fn2-rec-dirty (- left 1) (+ 1 p) high
   (or dirty (not (member-equal (fn2-rec-cand-status p fn2-rec-cand)
                               (list *fn2-rec-status-empty* *fn2-rec-status-chained*)))) fn2-rec-cand)))
