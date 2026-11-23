; The upload kind's continuations (D4, books/upload.lisp), in their own leaf
; section book so arm-body edits do not invalidate assembly.cert or executor.cert.
(in-package "ACL2")
(include-book "assembly-callbacks-d")
(include-book "upload")
(include-book "upload-stream")
(include-book "upload-stream-reset")
(include-book "upload-stream-settle")
(include-book "upload-block-private")
(local (defun fn2-du-core-child-type-terms (children)
         (declare (xargs :verify-guards nil))
         (if (atom children) nil
           (cons `(,(fn2-columns-sym (cadar children) "P") (,(caar children) fn2-core))
                 (fn2-du-core-child-type-terms (cdr children))))))
(make-event
 (value `(local (defthm fn2-du-core-child-types-fc
                  (implies (fn2-corep fn2-core)
                           (and ,@(fn2-du-core-child-type-terms *fn2-core-children*)))
                  :rule-classes :forward-chaining))))
(make-event
 (value `(local (in-theory (enable ,@(fn2-core-child-wfp-forward-runes *fn2-core-children*))))))
(local
 (defthm fn2-du-dir-readers-over-other-child
   (implies (not (equal (nfix k) *fn2-core-machines*))
            (and (equal (fn2-machine-idp i (update-nth k v c)) (fn2-machine-idp i c))
                 (equal (fn2-machine-kind i (update-nth k v c)) (fn2-machine-kind i c))
                 (equal (fn2-machine-slot i (update-nth k v c)) (fn2-machine-slot i c))
                 (equal (fn2-core-machines (update-nth k v c)) (fn2-core-machines c))))
   :hints (("Goal" :in-theory (enable fn2-machine-idp fn2-machine-kind fn2-machine-kind-read-code
                                      fn2-machine-slot fn2-machine-slot-read-code fn2-core-machines)))))
(make-event
 (value `(local (in-theory (disable nth fn2-digests-rows fn2-b3-rows fn2-fields-rows
                                    fn2-pool-fill fn2-pool-base fn2-pool-data-length)))))
(local
 (defun fn2-du-wrap-preserves (x)
   (declare (xargs :mode :program))
   (cond ((atom x) x)
         ((eq (car x) 'fn2-core-preserves)
          `(encapsulate ()
             (local (in-theory (disable nfix min floor mod
                                        fn2-pool-range-in fn2-pool-workspace-code fn2-pool-readable-code
                                        fn2-layout-range-code fn2-feed-header-complete-p fn2-gram-fill
                                        fn2-upload-snapshot-read-code fn2-conn-snapshot-read-code
                                        fn2-cns-snapshot-read-code fn2-machine-generation
                                        fn2-upload-stored-hasher fn2-upload-hasher
                                        fn2-digest-rowp fn2-digest-slot fn2-b3-ready
                                        |(< x (if a b c))| |(< (if a b c) x)|)))
             ,x))
         (t (cons (fn2-du-wrap-preserves (car x))
                  (fn2-du-wrap-preserves (cdr x)))))))
(defmacro fn2-du-fast-events (form)
  `(make-event
    (mv-let (erp exp) (macroexpand1-cmp ',form 'assembly-callbacks-d-upload (w state) (default-state-vars nil))
      (if erp (er soft 'assembly-callbacks-d-upload "Expand failed: ~x0" ',form)
        (value (fn2-du-wrap-preserves exp))))))
(local
 (defthm fn2-du-workspace-code-implies-row-bounds
   (implies (equal (fn2-pool-workspace-code s g okind oid ogen p) :ok)
            (and (natp s) (integerp s) (<= 0 s) (< s (fn2-pool-rows p))))
   :rule-classes (:rewrite :forward-chaining)
   :hints (("Goal" :in-theory (enable fn2-pool-workspace-code fn2-pool-handle-code)))))
(local
 (defthm fn2-du-readable-code-implies-row-bounds
   (implies (equal (fn2-pool-readable-code s g okind oid ogen p) :ok)
            (and (natp s) (integerp s) (<= 0 s) (< s (fn2-pool-rows p))))
   :rule-classes (:rewrite :forward-chaining)
   :hints (("Goal" :in-theory (enable fn2-pool-readable-code fn2-pool-handle-code)))))
(local
 (defthm fn2-du-qref-array-nth-natp
   (implies (and (fn2-pool-query-ref-count$ap l) (natp s) (< s (len l)))
            (natp (nth s l)))
   :hints (("Goal" :in-theory (enable fn2-pool-query-ref-count$ap nth len unsigned-byte-p)))))
(local
 (defthm fn2-du-query-ref-count-nth-natp
   (implies (and (fn2-poolp p) (fn2-pool-wfp p) (natp s) (< s (fn2-pool-rows p)))
            (and (integerp (nth s (nth *fn2-pool-query-ref-count$ai* p)))
                 (<= 0 (nth s (nth *fn2-pool-query-ref-count$ai* p)))
                 (acl2-numberp (nth s (nth *fn2-pool-query-ref-count$ai* p)))))
   :hints (("Goal" :in-theory (union-theories '(natp fn2-poolp fn2-pool-query-ref-count$a-length)
                                              (theory 'minimal-theory))
                   :use ((:instance fn2-du-qref-array-nth-natp
                                    (l (nth *fn2-pool-query-ref-count$ai* p)))
                         (:instance fn2-pool-query-ref-count-length-when-wfp (fn2-pool p)))))))
(encapsulate ()
  (local (in-theory (disable fn2-pool-workspace-code fn2-pool-readable-code
                             fn2-pool-range-in fn2-feed-header-complete-p
                             fn2-gram-fill fn2-upload-stored-hasher)))
  (fn2-du-fast-events (fn2-upload-stream-stage-events)))
(fn2-du-fast-events (fn2-upload-stream-reset-op-events))
(fn2-du-fast-events (fn2-upload-stream-manifest-op-events))
(local
 (defthm fn2-du-upload-digest-preserves-tables
   (and (equal (fn2-core-machines (mv-nth 1 (fn2-upload-digest row hashed fn2-core)))
               (fn2-core-machines fn2-core))
        (equal (fn2-upload-table (mv-nth 1 (fn2-upload-digest row hashed fn2-core)))
               (fn2-upload-table fn2-core)))
   :hints (("Goal" :in-theory (e/d (fn2-upload-digest fn2-upload-hash-begin fn2-upload-hash-end)
                                   (fn2-b3-init fn2-b3-finalize fn2-b3-ready fn2-digest-rowp fn2-digest-slot))))))
(local
 (defthm fn2-du-upload-digest-preserves-machines-and-upload
   (and (equal (fn2-core-machines (mv-nth 1 (fn2-upload-digest row hashed fn2-core)))
               (fn2-core-machines fn2-core))
        (equal (fn2-upload-table (mv-nth 1 (fn2-upload-digest row hashed fn2-core)))
               (fn2-upload-table fn2-core))
        (equal (fn2-machine-idp id (mv-nth 1 (fn2-upload-digest row hashed fn2-core)))
               (fn2-machine-idp id fn2-core))
        (equal (fn2-machine-kind id (mv-nth 1 (fn2-upload-digest row hashed fn2-core)))
               (fn2-machine-kind id fn2-core))
        (equal (fn2-machine-slot id (mv-nth 1 (fn2-upload-digest row hashed fn2-core)))
               (fn2-machine-slot id fn2-core))
        (equal (fn2-upload-row-lslot id (mv-nth 1 (fn2-upload-digest row hashed fn2-core)))
               (fn2-upload-row-lslot id fn2-core))
        (equal (fn2-upload-row-lgen id (mv-nth 1 (fn2-upload-digest row hashed fn2-core)))
               (fn2-upload-row-lgen id fn2-core)))
   :hints (("Goal" :in-theory (e/d (fn2-machine-idp fn2-machine-kind fn2-machine-kind-read-code
                                    fn2-machine-slot fn2-machine-slot-read-code
                                    fn2-upload-row-lslot fn2-upload-row-lgen)
                                   (fn2-upload-digest))))))
(fn2-du-fast-events (fn2-upload-stream-op-events))
(local
 (defthm fn2-du-payload-settle-preserves-machines-and-upload
   (and (equal (fn2-core-machines (mv-nth 1 (fn2-upload-payload-settle e ep al fn2-core)))
               (fn2-core-machines fn2-core))
        (equal (fn2-machine-idp id (mv-nth 1 (fn2-upload-payload-settle e ep al fn2-core)))
               (fn2-machine-idp id fn2-core))
        (equal (fn2-machine-kind id (mv-nth 1 (fn2-upload-payload-settle e ep al fn2-core)))
               (fn2-machine-kind id fn2-core))
        (equal (fn2-machine-slot id (mv-nth 1 (fn2-upload-payload-settle e ep al fn2-core)))
               (fn2-machine-slot id fn2-core))
        (equal (fn2-upload-table (mv-nth 1 (fn2-upload-payload-settle e ep al fn2-core)))
               (fn2-upload-table fn2-core)))
   :hints (("Goal" :in-theory (enable fn2-upload-payload-settle fn2-core-stop
                                      fn2-machine-idp fn2-machine-kind fn2-machine-slot)))))
(encapsulate ()
  (local (in-theory (disable fn2-pool-workspace-code fn2-pool-readable-code
                             fn2-layout-range-code fn2-am-get-entry
                             fn2-upload-payload-settle fn2-am-entry-at min mod floor)))
  (fn2-du-fast-events (fn2-upload-stream-settle-op-events)))
(encapsulate ()
  (local (in-theory (disable fn2-upload-hash-private-children fn2-upload-cv-private-children)))
  (fn2-du-fast-events (fn2-upload-block-private-op-events)))

;; The source manifest's pure decisions the arms read (article-manifest.lisp).
(defcost fn2-am-fits :doc "Whether stored octets of a length are named by one source manifest.")
(defcost fn2-am-manifestp :doc "Whether stored octets exceed the raw commitment span (named through a manifest).")
(defcost fn2-upload-manifest-units :doc "The manifest units the drain settles, a unit of entries per step.")

(defun fn2-upload-release-c0 (slot gen okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (fn2-core-release slot gen okind oslot ogen fn2-core))
(fn2-core-preserves fn2-upload-release-c0 (slot gen okind oslot ogen fn2-core) :position 1 :rows nil)
(in-theory (disable fn2-upload-release-c0))
(defcost fn2-upload-release-c0 :answers t :tables (fn2-core-pool)
  :doc "Release the first chunk of a draining upload's chunk window.")

;; The store page's return, its own operation so D0's table keeps one row
;; per call site (the chunk window's release is fn2-core-release).
(defun fn2-upload-page-release (slot gen okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (fn2-core-release slot gen okind oslot ogen fn2-core))
(fn2-core-preserves fn2-upload-page-release (slot gen okind oslot ogen fn2-core) :position 1 :rows nil)
(in-theory (disable fn2-upload-page-release))
(defcost fn2-upload-page-release :answers t :tables (fn2-core-pool)
  :doc "Return a draining upload's store page (the generated Message-ID's lease).")

(defmachine-arms fn2-upload :declare
 :subarms
 ;; TAKE owns header, body and page together. The early-cancel drain
 ;; returns an uninitialized page without reading manifest or extent state.
 ((work
   (:cond ((not (equal row-lease *fn2-upload-lease-held*)) (:stop :machine-phase))
          (t
   ;; the owner feeding the source: a connection, or a consumer request
   ;; whose append frame is the article (e-surface.md 3.3)
   (:let lcns (:live cns))
   (:if (not (or lcns (:live conn)))
        ((:next :aborting) (:charge :bytes *fn2-upload-run-bytes* :steps *fn2-work-transition* :runnable t))
        ((:do (next)
              (fn2-upload-advance id (if lcns (:read cns fed) (:read conn fed))
                                  (equal (if lcns (:read cns feed-mode) (:read conn feed-mode)) *fn2-conn-feed-done*)
                                  (if lcns (:read cns feed-discard) (:read conn feed-discard)))
              :accept ()
              :case (((:run) (:charge :bytes *fn2-upload-run-bytes* :steps *fn2-work-transition* :runnable t))
                     ((:idle) (:charge :bytes *fn2-upload-run-bytes* :steps *fn2-work-transition*))
                     ((:identity) (:next :identity)
                      (:charge :bytes *fn2-upload-run-bytes* :steps *fn2-work-transition* :runnable t))
                     ((:receiving) (:next :receiving)
                      (:charge :bytes *fn2-upload-run-bytes* :steps *fn2-work-transition* :runnable t))
                     ;; the verdict is handed over: store the source before
                     ;; the transaction reads the sealed upload
                     ((:sealed) (:next :sealed)
                      (:charge :bytes *fn2-upload-run-bytes* :steps *fn2-work-transition* :runnable t))
                     ((:discard) (:next :discard)
                      (:charge :bytes *fn2-upload-run-bytes* :steps *fn2-work-transition*))
                     ((:draining) (:next :draining)
                      (:charge :bytes *fn2-upload-run-bytes* :steps *fn2-work-transition* :runnable t))
                     ((:stop) (:stop :machine-phase))))))))))
 :arms
 ((:free (:idle))
  (:head (:goto work))
  ;; :identity: take the transaction row (A-S7), the transaction's copies this
  ;; row's; refused, the take parked this row on the transaction kind's FIFO
  ;; and its grant runs this arm again. The owner gone: abort.
  (:identity
   (:if (not (or (:live conn) (:live cns)))
        ((:next :aborting) (:charge :steps *fn2-work-transition* :runnable t))
        ((:do (code tid tgen)
              (fn2-machine-take-fn2-txn *fn2-none* id row-generation row-conn row-conn-gen
                                        row-request row-rule row-principal-slot)
              :case (((:ok) (:set (txn tid) (txn-gen tgen)) (:next :stream-init)
                      (:charge :steps *fn2-work-transition* :runnable t))
                     ;; no fn2-txn row in the profile: unreachable in composition
                     ;; (posting, which every upload taker reads, is served only
                     ;; with one); a contract stop, never a park
                     ((:none) (:stop :machine-phase))
                     (:otherwise (:park :taken fn2-txn :steps *fn2-work-transition*)))))))
  (:receiving (:goto work))
  (:validating (:goto work))
  (:discard (:goto work))
;; Historical prebuffering states below are unreachable-in-composition:
  ;; valid headers enter STREAM-INIT; definite old-work verdicts go directly
  ;; to SEALED without storage. These states stop rather than execute a
  ;; second producer or exceed the unchanged 4096 run quota.
  ;; The former path stored octets as follows:
  ;; written to storage (B's allocator, the commit arena's units) and fenced
  ;; before the transaction may read the sealed upload, so the article row's
  ;; location names durable octets before the batch that accepts it writes
  ;; its journal. The stored octets are the source, after the injected
  ;; Message-ID field when the POST named none (its identifier from the
  ;; payload extent's handle, the field built in the store page). Octets that
  ;; fit one extent are stored there; longer ones block by block (one unit
  ;; each, three to an extent) through the store page's stage, each block's
  ;; entry built in the store page's source manifest, and the manifest last,
  ;; in an extent of its own, PEXT (article-manifest.lisp). A refused verdict
  ;; stores nothing; a full arena or a failed write refuses the article by
  ;; word.
  (:store (:stop :machine-phase))
  ;; The same bounded span selector drives this hash, raw writes, and
  ;; manifest staging. Hash prefix+source before block hashing reuses B3.
  (:stored-hash (:stop :machine-phase))
  (:location-hash (:stop :machine-phase))
  ;; :store-write: the next write (a piece of one extent's octets, a block,
  ;; or a manifest unit); a manifest's header goes into the store page first
  ;; (the page zeroed to it a unit per step, MSTEP 0, then the header), and a
  ;; block at unit 0 of an extent reserves that extent first
  (:store-write (:stop :machine-phase))
  (:store-wrote (:stop :machine-phase))
  (:store-fence (:stop :machine-phase))
  ;; fenced: a generated identifier stays in the store page (after the
  ;; field name), where the transaction reads the Message-ID (MO ML) for its
  ;; claim, identity and overview line; chunk 0 keeps the source until the
  ;; transaction has counted its lines
  (:store-fenced (:stop :machine-phase))
  ;; :sealed: wait for the transaction's outcome (relaying any settlement wake
  ;; to the transaction while it still names this upload), then drain.
  (:sealed
   (:if (:live child-txn)
        ((:do () (fn2-upload-wake row-txn)) (:charge :steps *fn2-work-transition*))
        ((:if (and (equal row-stream-active 1) (equal row-lease *fn2-upload-lease-held*))
          ((:set (stream-repack 0) (mstep 0)) (:next :stream-drain)
           (:charge :steps *fn2-work-transition* :runnable t))
          ((:next :draining) (:charge :steps *fn2-work-transition* :runnable t))))))
  ;; :aborting: the connection left. A transaction that still names this row
  ;; holds its octets: wake it (it finishes without a word) and wait for it to
  ;; let go; then drain.
  (:aborting
   (:cond ((not (equal row-pending 0)) (:charge :steps *fn2-work-poll*))
          ((:live child-txn) (:do () (fn2-upload-wake row-txn)) (:charge :steps *fn2-work-transition*))
          ((and (equal row-lease *fn2-upload-lease-held*) (equal row-stream-active 0))
           (:next :draining) (:charge :steps *fn2-work-transition* :runnable t))
          ((equal row-lease *fn2-upload-lease-held*)
           (:set (stream-repack 0) (mstep 0)) (:next :stream-drain)
           (:charge :steps *fn2-work-transition* :runnable t))
          (t (:next :draining) (:charge :steps *fn2-work-transition* :runnable t))))
  ;; :draining settles the extents the stored octets occupy (through the
  ;; manifest in the store page, a unit of its entries per step, MDRAIN),
  ;; returns the store page, then releases the second chunk, then the first,
  ;; then the row.
  (:draining :on-refusal ((:stop :pool-release :steps *fn2-work-state*))
   (:cond
          ;; Keep the page and extent state together until its last query
          ;; reference wakes this owner. No settlement precedes this check.
          ((and (equal row-lease *fn2-upload-lease-held*)
                (fn2-core-query-heldp row-lslot row-lgen))
           (:charge :steps *fn2-work-state*))
          ((and (equal row-lease *fn2-upload-lease-held*)
                (equal row-stream-active 0))
           (:do (lc) (fn2-upload-page-release row-lslot row-lgen)
            :effects ((:release (:storage-window))) :accept (:ok :retired)
            :why "a retired range is a completed release (the pool retires the slot)")
           (:set (lease *fn2-upload-lease-none*) (lslot *fn2-none*) (lgen 0))
           (:charge :steps *fn2-work-transition* :runnable t))
          ((and (equal row-lease *fn2-upload-lease-held*)
                (< row-mdrain (fn2-upload-manifest-units (+ row-ilen row-hashed) row-mfill)))
           (:let hrow (fn2-upload-hasher id))
           (:do (pcode) (fn2-upload-settle-unit (* 128 hrow) (+ row-ilen row-hashed) row-lslot row-lgen row-mfill
                                                row-mdrain)
            :accept (:ok))
           (:set (mdrain (+ 1 row-mdrain)))
           (:charge :bytes *fn2-commit-unit-bytes* :steps *fn2-work-transition* :runnable t))
          ((equal row-lease *fn2-upload-lease-held*)
           (:do (pcode) (fn2-upload-extents-close
             (if (equal row-rootext *fn2-none*) row-pext row-rootext)
             (if (equal row-rootext *fn2-none*) row-pepoch row-rootepoch)
             (if (equal row-rootext *fn2-none*) row-palloc row-rootalloc)
             row-cext row-cepoch row-calloc row-cfree)
            :accept (:ok))
           (:do (lc) (fn2-upload-page-release row-lslot row-lgen) :effects ((:release (:storage-window)))
                :accept (:ok :retired) :why "a retired range is a completed release (the pool retires the slot)")
           (:set (lease *fn2-upload-lease-none*) (lslot *fn2-none*) (lgen 0) (pext *fn2-none*) (cext *fn2-none*)
                 (cfree 0) (mfill 0) (mdrain 0) (rootext *fn2-none*) (rootepoch 0) (rootalloc 0))
           (:charge :steps *fn2-work-transition* :runnable t))
          ;; Test both chunks before settling or freeing either. A held C0
          ;; must not leave C1 freed while the row still carries its handle.
          ((or (fn2-core-query-heldp row-c0-slot row-c0-gen)
               (fn2-core-query-heldp row-c1-slot row-c1-gen))
           (:charge :steps *fn2-work-state*))
          (t
         (:do (pcode) (fn2-upload-payload-settle row-pext row-pepoch row-palloc) :accept (:ok))
         (:do (c1code) (fn2-core-release row-c1-slot row-c1-gen)
              :effects ((:release (:chunk-window)))
              :accept (:ok :retired) :why "a retired range is a completed release (the pool retires the slot)")
         (:do (c0code) (fn2-upload-release-c0 row-c0-slot row-c0-gen)
              :accept (:ok :retired) :why "a retired range is a completed release (the pool retires the slot)")
         (:let next (fn2-machine-free-head *fn2-upload-admission-ordinal*))
         (:let retire (>= row-generation (fn2-machine-gen-limit)))
         (:set (generation (if retire row-generation (+ 1 row-generation)))
               (c0-slot *fn2-none*) (c0-gen 0) (c1-slot *fn2-none*) (c1-gen 0) (pext *fn2-none*) (cext *fn2-none*)
               (conn *fn2-none*) (conn-gen 0) (filled 0) (hashed 0) (txn *fn2-none*)
               (next-free next) (wait-reason *fn2-wait-none*))
         (:next (:if retire :retired :free))
         (:do () (fn2-machine-reclaim-fn2-upload id retire))
         (:charge :steps *fn2-work-release*))))
    ;; The rolling path starts after the actual parsed header and transaction
  ;; claim row exist. C0 remains the header; the payload identity is stable.
  (:stream-init :on-refusal ((:stop :machine-phase))
   (:cond
    ((not (or (:live conn) (:live cns)))
     (:next :aborting) (:charge :steps *fn2-work-transition* :runnable t))
    ((equal row-mstep 0)
     (:do (ok word inj) (fn2-upload-word-now id row-generation row-c0-slot row-c0-gen 0 0 row-hashed))
     (:if (not ok) ((:stop :machine-phase))
       ((:if (not (equal word 0))
         ((:set (word word) (inj inj))
          (:do (code) (fn2-upload-start-discard id row-generation) :accept (:ok))
          (:next :discard) (:charge :bytes *fn2-upload-verdict-work-bytes* :steps *fn2-work-transition* :runnable t))
         ((:set (inj inj) (mstep 1) (rootext *fn2-none*) (rootepoch 0) (rootalloc 0) (stream-active 1)) (:charge :bytes *fn2-upload-verdict-work-bytes* :steps *fn2-work-transition* :runnable t))))))
    ((equal row-mstep 1)
     ; TAKE already owns all three ranges; never wait for a page while
     ; retaining only header/body windows.
     (:do (pc pid) (fn2-upload-owner-principal row-conn row-conn-gen row-principal-slot)
      :accept (:ok :state) :why "a missing principal refuses the upload before storage")
     (:cond ((not (and (eq pc :ok) (posp pid) (unsigned-byte-p 60 pid)))
             (:set (word *fn2-upload-word-refused*) (stream-active 0))
             (:do (dc) (fn2-upload-start-discard id row-generation) :accept (:ok))
             (:next :discard) (:charge :steps *fn2-work-transition* :runnable t))
            ((and (equal row-lease *fn2-upload-lease-held*)
                  (fn2-upload-stream-page-ready-p id row-generation))
             (:set (request-principal pid) (mstep 2))
             (:charge :steps *fn2-work-transition* :runnable t))
            (t (:stop :machine-phase))))
    ((equal row-mstep 2)
     (:do (code e ep al) (fn2-upload-payload-reserve) :accept ()
      :case (((:ok) (:set (pext e) (pepoch ep) (palloc al) (cext e) (cepoch ep) (calloc al) (cfree 1)
                         (pdone 0) (mfill 0) (stream-stage-used 0) (mstep 3))
                      (:charge :steps *fn2-work-transition* :runnable t))
             ((:no-space) (:set (word *fn2-upload-word-unaffordable*))
              (:do (dcode) (fn2-upload-start-discard id row-generation) :accept (:ok))
              (:next :stream-receiving) (:charge :steps *fn2-work-transition* :runnable t))
             (:otherwise (:stop :machine-phase)))))
    ((equal row-mstep 3)
     (:if (and (equal row-ml 0) (equal row-rule *fn2-upload-rule-post*))
      ((:do (code n) (fn2-upload-put-mid row-lslot row-lgen row-pepoch row-palloc row-op row-request-principal) :accept (:ok))
       (:set (ilen n) (mstep 4)) (:charge :bytes 264 :steps *fn2-work-transition* :runnable t))
      ((:set (ilen 0) (mstep 4)) (:charge :steps *fn2-work-transition* :runnable t))))
    (t
     (:let bound (fn2-upload-bound 0 0))
     (:do (code) (fn2-upload-page-zero-to (fn2-upload-stream-page-bytes (+ bound *fn2-upload-mid-line-max*)) row-lslot row-lgen)
      :accept () :case (((:ok) (:set (mstep 0)) (:next :stream-receiving)
                         (:charge :bytes *fn2-commit-unit-bytes* :steps *fn2-work-transition* :runnable t))
                       ((:more) (:charge :bytes *fn2-commit-unit-bytes* :steps *fn2-work-transition* :runnable t)))))))
  (:stream-receiving :on-refusal ((:stop :machine-phase))
   (:do (code) (fn2-upload-stream-progress id row-generation) :accept ()
    :case (((:run) (:charge :bytes *fn2-upload-run-bytes* :steps *fn2-work-transition* :runnable t))
           ((:idle) (:charge :bytes *fn2-upload-run-bytes* :steps *fn2-work-transition*))
           ((:window) (:next :stream-stage) (:charge :bytes *fn2-upload-run-bytes* :steps *fn2-work-transition* :runnable t))
           ((:gone) (:next :stream-refuse-fence) (:charge :steps *fn2-work-transition* :runnable t))
           ((:refused) (:next :stream-refuse-fence) (:charge :steps *fn2-work-transition* :runnable t))
           (:otherwise (:stop :machine-phase)))))
  (:stream-stage :on-refusal ((:stop :machine-phase))
   (:cond
    ((equal row-stream-stage-used *fn2-commit-unit-bytes*)
     (:next :stream-write) (:charge :steps *fn2-work-transition* :runnable t))
    ((and (equal row-stored-hashed (+ row-ilen row-stream-end))
          (or (equal row-stream-eof 0) (equal row-stream-stored-finalized 1)))
     (:next (:if (< 0 row-stream-stage-used) :stream-write :stream-fence))
     (:charge :steps *fn2-work-transition* :runnable t))
    (t (:do (code copied) (fn2-upload-stream-stage id row-generation) :accept ()
        :case (((:ok) (:charge :bytes *fn2-upload-stream-stage-work*
                               :steps *fn2-work-transition* :runnable t))
               ((:idle) (:charge :bytes *fn2-upload-stream-stage-work*
                                 :steps *fn2-work-transition*))
               (:otherwise (:stop :machine-phase)))))))
  (:stream-write :on-refusal ((:stop :machine-phase))
   (:let block (floor row-pdone *fn2-commit-unit-bytes*))
   (:cond
    ((and (equal (mod block *fn2-storage-extent-units*) 0) (equal row-cfree 0))
     (:do (code e ep al) (fn2-upload-payload-reserve) :accept ()
      :case (((:ok) (:set (cext e) (cepoch ep) (calloc al) (cfree 1))
                    (:charge :steps *fn2-work-transition* :runnable t))
             ((:no-space) (:set (word *fn2-upload-word-unaffordable*))
              (:do (dcode) (fn2-upload-start-discard id row-generation) :accept (:ok))
              (:next :stream-receiving) (:charge :steps *fn2-work-transition* :runnable t))
             (:otherwise (:stop :machine-phase)))))
    ((not (< 0 row-stream-stage-used)) (:stop :machine-phase))
    (t (:issue (fn2-issue-write (+ (* *fn2-commit-extent-bytes* row-cext)
                                  (* *fn2-commit-unit-bytes* (mod block *fn2-storage-extent-units*)))
                               row-lslot row-lgen *fn2-upload-page-stage* row-stream-stage-used 0
                               :principal row-principal-slot)
        :ok ((:set (sready 0)) (:next :stream-wrote)
             (:wait :completion :bytes *fn2-commit-unit-bytes* :steps *fn2-work-small*))))))
  (:stream-wrote :on-refusal ((:stop :machine-phase))
   (:cond
    ((equal row-sready 0) (:charge :steps *fn2-work-poll*))
    ((not (and (equal row-sevent *fn2-event-write-result*) (equal row-soutcome *fn2-outcome-done*)
               (equal row-scount row-stream-stage-used)))
     (:set (word *fn2-upload-word-uncertain*)) (:next :uncertain)
     (:charge :steps *fn2-work-transition* :runnable t))
    ((not (equal row-pending 0)) (:charge :steps *fn2-work-poll*))
    ;; A partial nonfinal block is durable but remains staged; its prefix is
    ;; overwritten only by the next append to this same logical block.
    ((and (< row-stream-stage-used *fn2-commit-unit-bytes*) (equal row-stream-eof 0))
     (:set (sready 0)) (:next :stream-fence) (:charge :steps *fn2-work-transition* :runnable t))
    (t (:set (mstep 0)) (:next :stream-block) (:charge :steps *fn2-work-transition* :runnable t))))
  (:stream-block :on-refusal ((:stop :machine-phase))
   (:let block (floor row-pdone *fn2-commit-unit-bytes*))
   (:cond
    ((not (fn2-upload-stream-page-ready-p id row-generation)) (:charge :steps *fn2-work-poll*))
    ((equal row-mstep 0)
     (:do (code) (fn2-upload-block-hash-keep id row-generation) :accept (:ok))
     (:set (mstep 1)) (:charge :bytes *fn2-commit-unit-bytes* :steps *fn2-work-transition* :runnable t))
    ((equal row-mstep 1)
     (:do (code) (fn2-upload-private-result-store id row-generation) :accept (:ok))
     (:set (mstep 2)) (:charge :bytes *fn2-upload-digest-octets* :steps *fn2-work-transition* :runnable t))
    ((equal row-mstep 2)
     (:if (< block *fn2-commit-write-resources*)
      ((:do (code) (fn2-core-copy-range row-lslot row-lgen *fn2-upload-page-hash*
                     row-lslot row-lgen (+ *fn2-upload-page-location-hashes* (* 32 block)) 32))
       (:if (not (eq code :ok))
            ((:stop :machine-phase))
            ((:set (location-hashed (+ block 1)) (mstep 3))
             (:charge :bytes *fn2-upload-digest-copy-bytes* :steps *fn2-work-transition* :runnable t))))
      ((:set (mstep 3)) (:charge :steps *fn2-work-transition* :runnable t))))
    ((equal row-mstep 3)
     (:if (equal row-stream-stage-used *fn2-commit-unit-bytes*)
      ((:do (code) (fn2-upload-block-cv-keep id row-generation) :accept (:ok))
       (:set (mstep 4)) (:charge :bytes *fn2-commit-unit-bytes* :steps *fn2-work-transition* :runnable t))
      ((:do (code) (fn2-core-copy-range row-lslot row-lgen *fn2-upload-page-hash*
                     row-lslot row-lgen (+ *fn2-upload-page-hash* 32) 32))
       (:if (not (eq code :ok))
            ((:stop :machine-phase))
            ((:set (mstep 5)) (:charge :bytes *fn2-upload-digest-copy-bytes* :steps *fn2-work-transition* :runnable t))))))
    ((equal row-mstep 4)
     (:do (code) (fn2-upload-private-result-store id row-generation) :accept (:ok))
     (:set (mstep 5)) (:charge :bytes *fn2-upload-digest-octets* :steps *fn2-work-transition* :runnable t))
    (t
     (:let hrow (fn2-upload-hasher id))
     (:do (code end) (fn2-upload-stream-entry hrow row-lslot row-lgen block row-stream-stage-used
          (+ (* *fn2-storage-extent-units* row-cext) (mod block *fn2-storage-extent-units*))
          row-cepoch row-calloc row-mfill *fn2-upload-kind* id row-generation) :accept (:ok))
     (:set (pdone (+ row-pdone row-stream-stage-used)) (stream-stage-used 0) (mfill end)
           (stream-provisional end) (cfree 0) (mstep 0) (sready 0))
     (:next :stream-stage) (:charge :bytes *fn2-upload-entry-bytes* :steps *fn2-work-transition* :runnable t))))
  (:stream-fence :on-refusal ((:stop :machine-phase))
   (:issue (fn2-issue-fence :principal row-principal-slot)
    :ok ((:set (sready 0)) (:next :stream-fenced) (:wait :completion :bytes 0 :steps *fn2-work-small*))))
  (:stream-fenced :on-refusal ((:stop :machine-phase))
   (:cond
    ((equal row-sready 0) (:charge :steps *fn2-work-poll*))
    ((not (and (equal row-sevent *fn2-event-fence-result*) (equal row-soutcome *fn2-outcome-done*)))
     (:set (word *fn2-upload-word-uncertain*)) (:next :uncertain)
     (:charge :steps *fn2-work-transition* :runnable t))
    ((not (equal row-pending 0)) (:charge :steps *fn2-work-poll*))
    ((not (fn2-upload-stream-page-ready-p id row-generation)) (:charge :steps *fn2-work-poll*))
    ((not (or (:live conn) (:live cns)))
     (:set (sready 0)) (:next :aborting) (:charge :steps *fn2-work-transition* :runnable t))
    ((equal row-stream-eof 1)
     (:set (sready 0) (mstep 0)) (:next :stream-final) (:charge :steps *fn2-work-transition* :runnable t))
    (t (:do (code) (fn2-upload-stream-reset id row-generation) :accept ()
        :case (((:ok) (:next :stream-receiving) (:charge :steps *fn2-work-transition* :runnable t))
               ((:workspace) (:charge :steps *fn2-work-poll*))
               (:otherwise (:stop :machine-phase)))))))
  (:stream-final :on-refusal ((:stop :machine-phase))
   (:let total (+ row-ilen row-hashed))
   (:cond
    ((equal row-mstep 0)
     (:do (code) (fn2-upload-stream-source-final id row-generation) :accept (:ok))
     (:set (mstep 1)) (:charge :bytes *fn2-upload-digest-octets* :steps *fn2-work-transition* :runnable t))
    ((not (fn2-am-manifestp total))
     (:if (equal row-ilen 0)
      ((:next :sealed) (:charge :steps *fn2-work-transition* :runnable t))
      ((:set (mo *fn2-upload-mid-field-octets*) (ml (nfix (- row-ilen (+ *fn2-upload-mid-field-octets* 2)))))
       (:next :sealed) (:charge :steps *fn2-work-transition* :runnable t))))
    ((equal row-rootext *fn2-none*)
     (:do (code e ep al) (fn2-upload-payload-reserve) :accept ()
      :case (((:ok) (:set (rootext e) (rootepoch ep) (rootalloc al))
                    (:charge :steps *fn2-work-transition* :runnable t))
             ((:no-space) (:set (word *fn2-upload-word-unaffordable*))
              (:next :stream-refuse-fence) (:charge :steps *fn2-work-transition* :runnable t))
             (:otherwise (:stop :machine-phase)))))
    (t (:let hrow (fn2-upload-hasher id))
       (:do (code end) (fn2-upload-stream-header hrow row-lslot row-lgen total *fn2-upload-kind* id row-generation) :accept (:ok))
       (:set (stream-provisional row-mfill) (stream-repack 0) (mfill end) (mstep 0))
       (:next :stream-repack) (:charge :bytes *fn2-upload-head-bytes* :steps *fn2-work-transition* :runnable t))))
  (:stream-repack :on-refusal ((:stop :machine-phase))
   (:cond
    ((<= row-stream-provisional (fn2-am-entry-at row-stream-repack))
     (:set (munit 0) (location-hashed 0) (mstep 0)) (:next :stream-root-write)
     (:charge :steps *fn2-work-transition* :runnable t))
    (t (:let hrow (fn2-upload-hasher id))
       (:do (code next end) (fn2-upload-repack-entry (* 128 hrow)
          row-lslot row-lgen (+ *fn2-upload-page-provisional* (fn2-am-entry-at row-stream-repack))
          (+ *fn2-upload-page-provisional* row-stream-provisional)
          row-lslot row-lgen (+ *fn2-upload-page-manifest* (fn2-am-entry-at row-mfill))
          *fn2-upload-kind* id row-generation) :accept (:ok))
       (:set (stream-repack (- next *fn2-upload-page-provisional*)) (mfill (- end *fn2-upload-page-manifest*)))
       (:charge :bytes *fn2-upload-entry-bytes* :steps *fn2-work-transition* :runnable t))))
  (:stream-root-write :on-refusal ((:stop :machine-phase))
   (:let at (+ *fn2-upload-page-manifest* (* row-munit *fn2-commit-unit-bytes*)))
   (:cond
    ((not (fn2-upload-stream-page-ready-p id row-generation)) (:charge :steps *fn2-work-poll*))
    ((equal row-mstep 0)
     (:do (code) (fn2-upload-root-hash-keep id row-generation) :accept (:ok))
     (:set (mstep 1)) (:charge :bytes *fn2-commit-unit-bytes* :steps *fn2-work-transition* :runnable t))
    ((equal row-mstep 1)
     (:do (code) (fn2-upload-private-result-store id row-generation) :accept (:ok))
     (:set (mstep 2) (location-hashed (+ row-munit 1)))
     (:charge :bytes *fn2-upload-digest-octets* :steps *fn2-work-transition* :runnable t))
    (t (:issue (fn2-issue-write (+ (* *fn2-commit-extent-bytes* row-rootext) (* row-munit *fn2-commit-unit-bytes*))
                   row-lslot row-lgen at *fn2-commit-unit-bytes* 0 :principal row-principal-slot)
        :ok ((:set (sready 0)) (:next :stream-root-wrote)
             (:wait :completion :bytes *fn2-commit-unit-bytes* :steps *fn2-work-small*))))))
  (:stream-root-wrote :on-refusal ((:stop :machine-phase))
   (:cond
    ((equal row-sready 0) (:charge :steps *fn2-work-poll*))
    ((not (and (equal row-sevent *fn2-event-write-result*) (equal row-soutcome *fn2-outcome-done*)
               (equal row-scount *fn2-commit-unit-bytes*)))
     (:set (word *fn2-upload-word-uncertain*)) (:next :uncertain)
     (:charge :steps *fn2-work-transition* :runnable t))
    ((not (equal row-pending 0)) (:charge :steps *fn2-work-poll*))
    (t (:let unit (+ row-munit 1)) (:set (munit unit) (mstep 0) (sready 0))
       (:next (:if (< (* unit *fn2-commit-unit-bytes*) row-mfill) :stream-root-write :stream-root-fence))
       (:charge :steps *fn2-work-transition* :runnable t))))
  (:stream-root-fence :on-refusal ((:stop :machine-phase))
   (:issue (fn2-issue-fence :principal row-principal-slot)
    :ok ((:set (sready 0)) (:next :stream-root-fenced) (:wait :completion :bytes 0 :steps *fn2-work-small*))))
  (:stream-root-fenced :on-refusal ((:stop :machine-phase))
   (:cond
    ((equal row-sready 0) (:charge :steps *fn2-work-poll*))
    ((not (and (equal row-sevent *fn2-event-fence-result*) (equal row-soutcome *fn2-outcome-done*)))
     (:set (word *fn2-upload-word-uncertain*)) (:next :uncertain)
     (:charge :steps *fn2-work-transition* :runnable t))
    ((not (equal row-pending 0)) (:charge :steps *fn2-work-poll*))
    ((not (fn2-upload-stream-page-ready-p id row-generation)) (:charge :steps *fn2-work-poll*))
    (t (:set (sready 0))
       (:if (equal row-ilen 0)
        ((:next :sealed) (:charge :steps *fn2-work-transition* :runnable t))
        ((:set (mo *fn2-upload-mid-field-octets*) (ml (nfix (- row-ilen (+ *fn2-upload-mid-field-octets* 2)))))
         (:next :sealed) (:charge :steps *fn2-work-transition* :runnable t))))))

  ;; Definitive refusal/owner departure reaches this only after all issued
  ;; writes have completed and their covering Fence succeeded. The retained
  ;; provisional stripe survives final canonical repacking unchanged.
  (:stream-refuse-fence :on-refusal ((:stop :machine-phase))
   (:issue (fn2-issue-fence :principal row-principal-slot)
    :ok ((:set (sready 0)) (:next :stream-refuse-fenced)
         (:wait :completion :bytes 0 :steps *fn2-work-small*))))
  (:stream-refuse-fenced :on-refusal ((:stop :machine-phase))
   (:cond
    ((equal row-sready 0) (:charge :steps *fn2-work-poll*))
    ((not (and (equal row-sevent *fn2-event-fence-result*) (equal row-soutcome *fn2-outcome-done*)))
     (:set (word *fn2-upload-word-uncertain*)) (:next :uncertain)
     (:charge :steps *fn2-work-transition* :runnable t))
    ((or (not (equal row-pending 0)) (not (fn2-upload-stream-page-ready-p id row-generation)))
     (:charge :steps *fn2-work-poll*))
    (t (:set (sready 0))
       (:next (:if (and (not (equal row-word 0)) (or (:live conn) (:live cns))) :sealed :aborting))
       (:charge :steps *fn2-work-transition* :runnable t))))
  (:stream-drain :on-refusal ((:stop :machine-phase))
   (:cond
    ((or (not (equal row-pending 0))
         (not (fn2-upload-stream-page-ready-p id row-generation))
         (fn2-core-query-heldp row-c0-slot row-c0-gen)
         (fn2-core-query-heldp row-c1-slot row-c1-gen))
     (:charge :steps *fn2-work-poll*))
    ((equal row-mstep 0)
     (:do (code) (fn2-upload-stream-settle-next id row-generation) :accept ()
      :case (((:ok) (:charge :bytes *fn2-upload-entry-bytes* :steps *fn2-work-transition* :runnable t))
             ((:end) (:set (mstep 1)) (:charge :steps *fn2-work-transition* :runnable t))
             (:otherwise (:stop :machine-phase)))))
    ((equal row-mstep 1)
     (:if (equal row-cfree 1)
      ((:do (code) (fn2-upload-payload-settle row-cext row-cepoch row-calloc) :accept (:ok))
       (:set (cfree 0) (mstep 2)) (:charge :steps *fn2-work-transition* :runnable t))
      ((:set (mstep 2)) (:charge :steps *fn2-work-transition* :runnable t))))
    ((equal row-mstep 2)
     (:if (equal row-rootext *fn2-none*)
      ((:set (mstep 3)) (:charge :steps *fn2-work-transition* :runnable t))
      ((:do (code) (fn2-upload-payload-settle row-rootext row-rootepoch row-rootalloc) :accept (:ok))
       (:set (rootext *fn2-none*) (rootepoch 0) (rootalloc 0) (mstep 3))
       (:charge :steps *fn2-work-transition* :runnable t))))
    (t (:do (code) (fn2-upload-page-release row-lslot row-lgen)
         :effects ((:release (:storage-window))) :accept (:ok :retired)
         :why "retired completes the exact workspace return")
       ;; First PEXT was either the first leader or the CFREE reservation;
       ;; clearing its carrier must not cancel that same handle twice.
       (:set (lslot *fn2-none*) (lgen 0) (lease *fn2-upload-lease-none*)
             (pext *fn2-none*) (cext *fn2-none*) (cfree 0) (mfill 0)
             (stream-active 0) (stream-provisional 0) (stream-repack 0) (mstep 0))
       (:next :draining) (:charge :steps *fn2-work-transition* :runnable t))))

  (:retired (:idle))
  ;; An issued storage operation was ambiguous or malformed. No settlement,
  ;; cancellation, workspace release or transaction hand-over can follow.
  (:uncertain (:stop :upload-uncertain)))
 :observes
 ((:write-result (:set (sevent event) (soutcome outcome) (scount count) (sready 1)) (:wake))
  (:fence-result (:set (sevent event) (soutcome outcome) (scount count) (sready 1)) (:wake))
  (:borrow-released (:wake))))

(local
 (defun fn2-du-arm-fns (arms)
   (declare (xargs :mode :program))
   (if (atom arms) nil (cons (cadar arms) (fn2-du-arm-fns (cdr arms))))))
(local
 (defun fn2-du-wrap-success-charge (x kind arm-fns)
   (declare (xargs :mode :program))
   (cond ((atom x) x)
         ((and (eq (car x) 'make-event) (consp (cdr x)) (consp (cadr x))
               (eq (caadr x) 'value) (consp (cdadr x)) (consp (cadadr x))
               (eq (car (cadadr x)) 'fn2-machine-success-charge-event))
          (let ((arm-ok (fn2-columns-sym kind "-ARM-OK-P"))
                (arm-charge (fn2-columns-sym kind "-ARM-CHARGE-OK-P"))
                (arm-next (fn2-columns-sym kind "-ARM-NEXT-OK-P"))
                (row-phase (fn2-columns-sym kind "-ROW-PHASE"))
                (snap-code (fn2-columns-sym kind "-SNAPSHOT-READ-CODE"))
                (run-fn (fn2-columns-sym kind "-RUN"))
                (thm-name (fn2-columns-sym (fn2-columns-sym kind "-RUN") "-SUCCESS-CHARGE"))
                (cc-thm (fn2-columns-sym kind "-FAST-CONTRACT-CHECK-CHARGE"))
                (rp-thm (fn2-columns-sym kind "-FAST-ROW-PHASE-IS-MACHINE-PHASE")))
            `(make-event
              (let ((guard (getpropc ',run-fn 'guard t (w state))))
                (value
                 `(encapsulate ()
                    (local
                     (defthm ,',cc-thm
                       (implies (fn2-core-success-p
                                 (mv-nth 4 (fn2-machine-contract-check
                                            (,',arm-ok id phase bytes steps descriptors c1)
                                            bytes steps descriptors runnable c1)))
                                (,',arm-charge
                                 phase
                                 (car (fn2-machine-contract-check
                                       (,',arm-ok id phase bytes steps descriptors c1)
                                       bytes steps descriptors runnable c1))
                                 (mv-nth 1 (fn2-machine-contract-check
                                            (,',arm-ok id phase bytes steps descriptors c1)
                                            bytes steps descriptors runnable c1))
                                 (mv-nth 2 (fn2-machine-contract-check
                                            (,',arm-ok id phase bytes steps descriptors c1)
                                            bytes steps descriptors runnable c1))))
                       :hints (("Goal" :in-theory
                                (remove-equal '(:rewrite fn2-core-stopped-p-is-exec-stop)
                                 (e/d (fn2-machine-contract-check ,',arm-ok
                                       fn2-core-success-p fn2-core-stopped-p fn2-core-stop-reason
                                       fn2-core-stop fn2-control-record-stop fn2-control-stop
                                       update-fn2-control-stop update-fn2-control-stop-reason)
                                      (,',arm-charge ,',arm-next
                                       fn2-machine-phase fn2-machine-phase-read-code)))))))
                    (local
                     (defthm ,',rp-thm
                       (implies (eq (,',snap-code id fn2-core) :ok)
                                (equal (,',row-phase id fn2-core)
                                       (fn2-machine-phase id fn2-core)))
                       :hints (("Goal" :in-theory
                                (enable ,',row-phase fn2-machine-phase
                                        ,',snap-code fn2-machine-phase-read-code)))))
                    (defthm ,',thm-name
                      (implies (and (fn2-corep fn2-core)
                                    ,guard
                                    (fn2-core-success-p (mv-nth 4 (,',run-fn id budget fn2-core))))
                               (,',arm-charge
                                (fn2-machine-phase id fn2-core)
                                (car (,',run-fn id budget fn2-core))
                                (mv-nth 1 (,',run-fn id budget fn2-core))
                                (mv-nth 2 (,',run-fn id budget fn2-core))))
                      :hints (("Goal" :in-theory
                               (e/d (,',run-fn ,',cc-thm ,',rp-thm fn2-core-stop-not-success)
                                    (fn2-machine-contract-check
                                     ,',arm-ok ,',arm-charge ,',arm-next ,',row-phase
                                     fn2-machine-phase ,',snap-code fn2-machine-phase-read-code
                                     fn2-core-success-p fn2-core-stop fn2-machine-refuse-phase
                                     ,@',arm-fns)))))))))))
         (t (cons (fn2-du-wrap-success-charge (car x) kind arm-fns)
                  (fn2-du-wrap-success-charge (cdr x) kind arm-fns))))))
(local
 (defun fn2-du-add-cor-hints (rules)
   (declare (xargs :mode :program))
   (if (atom rules) nil
     (cons (append (car rules)
                   '(:hints (("Goal" :in-theory
                              (union-theories '(fn2-run-quantitiesp natp)
                                (union-theories (executable-counterpart-theory :here)
                                                (theory 'minimal-theory)))))))
           (fn2-du-add-cor-hints (cdr rules))))))
(local
 (defun fn2-du-patch-result-tree (x extra-dis)
   (declare (xargs :mode :program))
   (cond ((atom x) x)
         ((and (eq (car x) ':rule-classes) (consp (cdr x)))
          (list* ':rule-classes (fn2-du-add-cor-hints (cadr x))
                 (fn2-du-patch-result-tree (cddr x) extra-dis)))
         ((and (eq (car x) 'e/d) (consp (cdr x)) (consp (cddr x)))
          (list 'e/d (cadr x) (append extra-dis (caddr x))))
         (t (cons (fn2-du-patch-result-tree (car x) extra-dis)
                  (fn2-du-patch-result-tree (cdr x) extra-dis))))))
(local
 (defun fn2-du-rewrite-core-ev (x kind runp arm-fns)
   (declare (xargs :mode :program))
   (cond ((atom x) x)
         ((eq (car x) 'fn2-machine-core-result-events)
          `(fn2-du-patch-result-tree
            ,x
            ',(append (and runp (cons (fn2-columns-sym kind "-ARM-OK-P") arm-fns))
                      (list (fn2-columns-sym kind "-SNAPSHOT-READ-CODE")
                            'fn2-machine-phase-read-code
                            '(:definition unsigned-byte-p)
                            '(:definition integer-range-p)
                            'ceiling 'floor 'mod))))
         ((eq (car x) 'fn2-core-preserves)
          `(encapsulate ()
             (local (in-theory (disable (:definition unsigned-byte-p) (:definition integer-range-p)
                                        nfix min floor mod ceiling fn2-machine-phase-read-code
                                        ,(fn2-columns-sym kind "-SNAPSHOT-READ-CODE")
                                        ,@(and runp (cons (fn2-columns-sym kind "-ARM-OK-P") arm-fns)))))
             ,x))
         (t (cons (fn2-du-rewrite-core-ev (car x) kind runp arm-fns)
                  (fn2-du-rewrite-core-ev (cdr x) kind runp arm-fns))))))
(local
 (defun fn2-du-find-result-fn (x)
   (declare (xargs :mode :program))
   (cond ((atom x) nil)
         ((and (eq (car x) 'fn2-machine-core-result-events)
               (consp (cdr x)) (consp (cadr x)) (eq (caadr x) 'quote))
          (cadadr x))
         (t (or (fn2-du-find-result-fn (car x))
                (fn2-du-find-result-fn (cdr x)))))))
(local
 (defun fn2-du-augment-arms-list (xs)
   (declare (xargs :mode :program))
   (if (atom xs) nil
     (let ((fn (fn2-du-find-result-fn (car xs))))
       (cond
        (fn
         (list* `(encapsulate ()
                   (local (in-theory (disable (:definition unsigned-byte-p) (:definition integer-range-p))))
                   ,(fn2-du-rewrite-core-ev (car xs) 'fn2-upload nil nil))
                `(local
                  (make-event
                   (let ((guard (getpropc ',fn 'guard t (w state)))
                         (iss (fn2-columns-sym ',fn "-ISSUED-EFFECT"))
                         (qnt (fn2-columns-sym ',fn "-QUANTITIES"))
                         (nums (fn2-columns-sym ',fn "-RESULT-NUMBERS"))
                         (gen (fn2-columns-sym ',fn "-ISSUED-EFFECT-GENERAL-N")))
                     (value
                      `(progn
                         (defthm ,nums
                           (implies (and (fn2-corep fn2-core) ,guard)
                                    (and (natp (car (,',fn id budget fn2-core)))
                                         (integerp (car (,',fn id budget fn2-core)))
                                         (<= 0 (car (,',fn id budget fn2-core)))
                                         (acl2-numberp (car (,',fn id budget fn2-core)))
                                         (natp (mv-nth 1 (,',fn id budget fn2-core)))
                                         (integerp (mv-nth 1 (,',fn id budget fn2-core)))
                                         (<= 0 (mv-nth 1 (,',fn id budget fn2-core)))
                                         (acl2-numberp (mv-nth 1 (,',fn id budget fn2-core)))
                                         (natp (mv-nth 2 (,',fn id budget fn2-core)))
                                         (integerp (mv-nth 2 (,',fn id budget fn2-core)))
                                         (<= 0 (mv-nth 2 (,',fn id budget fn2-core)))
                                         (acl2-numberp (mv-nth 2 (,',fn id budget fn2-core)))))
                           :rule-classes (:rewrite
                                          (:linear :corollary
                                           (implies (and (fn2-corep fn2-core) ,guard)
                                                    (and (<= 0 (car (,',fn id budget fn2-core)))
                                                         (<= 0 (mv-nth 1 (,',fn id budget fn2-core)))
                                                         (<= 0 (mv-nth 2 (,',fn id budget fn2-core)))))))
                           :hints (("Goal" :use ,qnt
                                           :in-theory (e/d (fn2-run-quantitiesp)
                                                           (,qnt ,',fn fn2-corep fn2-core-wfp)))))
                         (defthm ,gen
                           (implies (and (equal n (fn2-ops-rows (fn2-core-ops fn2-core)))
                                         (fn2-corep fn2-core)
                                         ,guard)
                                    (equal (fn2-ops-issued-count n (fn2-core-ops (mv-nth 4 (,',fn id budget fn2-core))))
                                           (+ (fn2-ops-issued-count n (fn2-core-ops fn2-core))
                                              (mv-nth 2 (,',fn id budget fn2-core)))))
                           :hints (("Goal" :use ,iss
                                           :in-theory (disable ,iss ,',fn fn2-core-ops fn2-corep fn2-core-wfp
                                                               fn2-ops-issued-count fn2-ops-rows)))))))))
                (fn2-du-augment-arms-list (cdr xs))))
        ((and (consp (car xs)) (eq (caar xs) 'progn)
              (consp (cdar xs)) (consp (cadar xs)) (eq (caadar xs) 'defun)
              (symbolp (cadr (cadar xs)))
              (search "-WRITE+" (symbol-name (cadr (cadar xs)))))
         (let ((w (cadr (cadar xs)))
               (fms (caddr (cadar xs))))
           (list* `(encapsulate ()
                     (local (in-theory (disable (:definition unsigned-byte-p) (:definition integer-range-p))))
                     ,(car xs))
                  `(local
                    (make-event
                     (value
                      `(defthm ,(fn2-columns-sym ',w "-PRESERVES-MACHINE-DIR")
                         (and (equal (fn2-machine-idp fn2-any-id (,',w ,@',fms)) (fn2-machine-idp fn2-any-id fn2-core))
                              (equal (fn2-machine-kind fn2-any-id (,',w ,@',fms)) (fn2-machine-kind fn2-any-id fn2-core))
                              (equal (fn2-machine-slot fn2-any-id (,',w ,@',fms)) (fn2-machine-slot fn2-any-id fn2-core)))
                         :hints (("Goal" :in-theory
                                  (union-theories
                                   '(,',w fn2-machine-refuse-write fn2-core-stop fn2-control-record-stop
                                     update-fn2-core-control update-fn2-upload-table
                                     fn2-machine-idp-bounds fn2-du-dir-readers-over-other-child
                                     ,(fn2-arm-frame-name ',w "-ARM-SLOT")
                                     ,@(fn2-arm-frame-directory-runes (strip-cars *fn2-machine-directory-fields*)))
                                   (theory 'fn2-arm-frame-base))))))))
                  `(local (in-theory (disable ,w)))
                  (fn2-du-augment-arms-list (cdr xs)))))
        ((and (consp (car xs)) (member-eq (caar xs) '(defun progn)))
         (cons `(encapsulate ()
                  (local (in-theory (disable (:definition unsigned-byte-p) (:definition integer-range-p))))
                  ,(fn2-du-rewrite-core-ev (car xs) 'fn2-upload nil nil))
               (fn2-du-augment-arms-list (cdr xs))))
        (t (cons (car xs) (fn2-du-augment-arms-list (cdr xs)))))))))
(make-event
 (mv-let (err events) (fn2-arms-link-core-events 'fn2-upload (fn2-arms-links 'fn2-upload (w state)) (w state))
   (if err (er soft 'assembly-callbacks-d-upload "~@0" err) (value (cons 'progn events)))))
(defcost-faces fn2-upload)
(make-event
 (mv-let (err form) (fn2-arms-events 'fn2-upload ':core (w state))
   (if err (er soft 'assembly-callbacks-d-upload "~@0" err)
     (value (cons 'progn (fn2-du-augment-arms-list (cdr form)))))))
(make-event
 (let* ((arm-fns (fn2-du-arm-fns (fn2-machine-property 'fn2-upload :continuations (w state))))
        (ev (fn2-du-rewrite-core-ev (fn2-machine-run-event 'fn2-upload (w state)) 'fn2-upload t arm-fns))
        (patched (fn2-du-wrap-success-charge ev 'fn2-upload arm-fns)))
   (if (equal patched ev)
       (er soft 'assembly-callbacks-d-upload "Could not patch fn2-upload-run-success-charge.")
     (value patched))))
