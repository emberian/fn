;; The upload machine fn2-upload (layer D, quest D4; ROUND2 section B.2
;; row 3). The design is docs/d-machines-nntp.md section 14.3. An upload
;; row is taken by a connection that opens an article block (POST after 340,
;; IHAVE after 335, TAKETHIS at once) with its window: two chunk slots of the
;; chunk class and the BLAKE3 hasher row 3 + its slot (B-S1). The
;; connection's feed writes the unstuffed source into the chunks
;; (upload-feed.lisp) and reports what it wrote (fn2-upload-input); the
;; upload's own runs hash it and scan its header (upload-scan.lisp), at most
;; 4 KiB per run, and once the terminator was framed and every octet is
;; hashed it gives its verdict and posts the word to its connection.
;; Schema and partition registration live in books/upload-kind.lisp;
;; its arms are declared and materialized by assembly-callbacks-d-upload.lisp.
(in-package "ACL2")
(include-book "assembly-index")
(include-book "article-manifest")
(fn2-book-layer :d)

;; The store page of stored octets longer than one extent (S-ARTICLE-LOCATION,
;; article-manifest.lisp): the generated Message-ID field from 0, the block
;; being stored from *fn2-upload-page-stage* (one unit), the block's BLAKE3 and
;; chaining value from *fn2-upload-page-hash*, and the source manifest from
;; *fn2-upload-page-manifest* (its units, written in order to the manifest's
;; extent). Its size is derived from the stored octets (fn2-upload-page-bytes).
(defconst *fn2-upload-page-stage* (* 64 (ceiling *fn2-upload-mid-line-max* 64)))
(defconst *fn2-upload-page-hash* (+ *fn2-upload-page-stage* *fn2-commit-unit-bytes*))
(defconst *fn2-upload-page-manifest* (+ *fn2-upload-page-hash* 64))
;; The octets the manifest's header and one entry touch (each encoded with
;; the 32-octet digests it names; an entry after the zeros that pad its unit).
(defconst *fn2-upload-head-bytes* (+ 32 *fn2-am-header-max*))
(defconst *fn2-upload-entry-bytes* (+ 64 (* 2 *fn2-am-entry-max*)))
(defun fn2-upload-page-bytes (total)
  (declare (xargs :guard t))
  (if (fn2-am-manifestp total)
      (+ *fn2-upload-page-manifest* (* *fn2-commit-unit-bytes* (fn2-am-units total)))
    *fn2-commit-unit-bytes*))

;; The words the store's refusals give (also the transaction's).
(defconst *fn2-upload-word-unaffordable* (fn2-upload-word-code :unaffordable))
(defconst *fn2-upload-word-not-stored* (fn2-upload-word-code :not-stored))

(defcost fn2-conn-feed-run :bytes *fn2-conn-feed-cost*
  :answers (:terminator :need-more :budget :bounds :fault)
  :faults (:bounds :fault)
  :tables (fn2-core-pool)
  :doc "Feed RX into the upload's chunk (upload-feed.lisp).")
(defcost fn2-upload-gen-of :doc "An upload row's generation.")
;; Declared costs of the upload's outside calls (each a thin wrapper below).
(defcost fn2-upload-hash-step :bytes *fn2-upload-hash-bytes* :tables (fn2-core-b3 fn2-core-digests)
  :doc "BLAKE3 over one range of a chunk into the upload's hasher row (B's fn2-b3-update).")
(defcost fn2-upload-hash-begin :tables (fn2-core-b3 fn2-core-digests) :doc "Start the hasher row.")
(defcost fn2-upload-hash-end :tables (fn2-core-digests) :doc "Finalize the digest into the hasher row's result slot.")
(defcost fn2-upload-scan-step :bytes *fn2-upload-scan-bytes* :doc "Advance the header scan over chunk 0.")
(defcost fn2-upload-verdict-step :bytes 512 :doc "The definite verdict over the scanned header.")
(defun fn2-upload-chunk-cap-pool (slot fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (nfix (fn2-feed-cap slot fn2-pool)))
(defthm fn2-upload-chunk-cap-pool-natp
  (natp (fn2-upload-chunk-cap-pool slot fn2-pool))
  :rule-classes :type-prescription)
(in-theory (disable fn2-upload-chunk-cap-pool))

(defun fn2-upload-hasher-children (id fn2-upload fn2-machines)
  (declare (xargs :stobjs (fn2-upload fn2-machines)
                  :guard (and (fn2-upload-wfp fn2-upload) (fn2-machines-wfp fn2-machines))))
  (if (and (fn2-machines-row-ok id)
           (equal (fn2-machines-kind id fn2-machines) *fn2-upload-kind*)
           (let ((slot (fn2-machines-slot id fn2-machines)))
             (and (natp slot) (< slot (fn2-upload-rows fn2-upload)))))
      (+ 3 (nfix (fn2-machines-slot id fn2-machines)))
    0))
(defthm fn2-upload-hasher-children-natp
  (natp (fn2-upload-hasher-children id fn2-upload fn2-machines))
  :rule-classes :type-prescription)
(in-theory (disable fn2-upload-hasher-children))

(defun fn2-conn-post-word-children (conn conn-gen request word fn2-conn fn2-machines fn2-control)
  (declare (xargs :stobjs (fn2-conn fn2-machines fn2-control)
                  :guard (and (fn2-conn-wfp fn2-conn) (fn2-machines-wfp fn2-machines) (fn2-control-wfp fn2-control))))
  (let ((slot (if (fn2-machines-row-ok conn) (fn2-machines-slot conn fn2-machines) 0)))
    (if (not (and (fn2-machines-row-ok conn)
                  (equal (fn2-machines-kind conn fn2-machines) *fn2-conn-kind*)
                  (natp slot) (< slot (fn2-conn-rows fn2-conn))
                  (unsigned-byte-p 8 word)
                  (equal (fn2-conn-generation slot fn2-conn) conn-gen)
                  (equal (fn2-conn-request slot fn2-conn) request)
                  (equal (fn2-conn-phase slot fn2-conn) *fn2-conn-state-article-input*)))
        (mv :dropped fn2-conn fn2-machines fn2-control)
      (mv-let (fn2-conn fn2-machines fn2-control)
        (fn2-conn-put-children conn slot (word word) (outcome-ready 1))
        (mv-let (fn2-machines fn2-control)
          (fn2-machines-wake-row conn fn2-machines fn2-control)
          (mv :ok fn2-conn fn2-machines fn2-control))))))
(fn2-conn-preserves fn2-conn-post-word-children (conn conn-gen request word fn2-conn fn2-machines fn2-control)
  :carriers ((fn2-conn 1 :prefix "-CONN") (fn2-machines 2 :prefix "-MACHINES") (fn2-control 3 :prefix "-CONTROL"))
  :rows nil)
(defthm fn2-conn-post-word-children-fn2-machines-rows
  (equal (fn2-machines-rows (mv-nth 2 (fn2-conn-post-word-children conn conn-gen request word fn2-conn fn2-machines fn2-control)))
         (fn2-machines-rows fn2-machines)))
(defthm fn2-conn-post-word-children-fn2-machines-raw-rows
  (equal (nth *fn2-machines-rows* (mv-nth 2 (fn2-conn-post-word-children conn conn-gen request word fn2-conn fn2-machines fn2-control)))
         (nth *fn2-machines-rows* fn2-machines)))
(in-theory (disable fn2-conn-post-word-children))
(make-event `(fn2-machines-keeps-directory fn2-conn-post-word-children
               (conn conn-gen request word fn2-conn fn2-machines fn2-control) 2 nil
               ,(fn2-machines-keeps-directory-hints 'fn2-conn-post-word-children (w state))))

(defun fn2-cns-post-outcome-children (cns cns-gen request word position fn2-cns fn2-machines fn2-control)
  (declare (xargs :stobjs (fn2-cns fn2-machines fn2-control)
                  :guard (and (fn2-cns-wfp fn2-cns) (fn2-machines-wfp fn2-machines) (fn2-control-wfp fn2-control))))
  (let ((slot (if (fn2-machines-row-ok cns) (fn2-machines-slot cns fn2-machines) 0)))
    (if (not (and (fn2-machines-row-ok cns)
                  (equal (fn2-machines-kind cns fn2-machines) *fn2-cns-kind*)
                  (natp slot) (< slot (fn2-cns-rows fn2-cns))
                  (unsigned-byte-p 8 word) (unsigned-byte-p 60 position)
                  (equal (fn2-cns-generation slot fn2-cns) cns-gen)
                  (equal (fn2-cns-request slot fn2-cns) request)
                  (equal (fn2-cns-phase slot fn2-cns) *fn2-cns-state-append*)
                  (equal (fn2-cns-posted slot fn2-cns) *fn2-cns-posted-none*)))
        (mv :dropped fn2-cns fn2-machines fn2-control)
      (mv-let (fn2-cns fn2-machines fn2-control)
        (fn2-cns-put-children cns slot
          (posted (cond ((equal word (fn2-upload-word-code :accepted)) *fn2-cns-posted-accepted*)
                        ((equal word (fn2-upload-word-code :uncertain)) *fn2-cns-posted-uncertain*)
                        (t *fn2-cns-posted-refused*)))
          (posted-word word)
          (cpos position))
        (mv-let (fn2-machines fn2-control)
          (fn2-machines-wake-row cns fn2-machines fn2-control)
          (mv :ok fn2-cns fn2-machines fn2-control))))))
(fn2-cns-preserves fn2-cns-post-outcome-children (cns cns-gen request word position fn2-cns fn2-machines fn2-control)
  :carriers ((fn2-cns 1 :prefix "-CNS") (fn2-machines 2 :prefix "-MACHINES") (fn2-control 3 :prefix "-CONTROL"))
  :rows nil)
(defthm fn2-cns-post-outcome-children-fn2-machines-rows
  (equal (fn2-machines-rows (mv-nth 2 (fn2-cns-post-outcome-children cns cns-gen request word position fn2-cns fn2-machines fn2-control)))
         (fn2-machines-rows fn2-machines)))
(defthm fn2-cns-post-outcome-children-fn2-machines-raw-rows
  (equal (nth *fn2-machines-rows* (mv-nth 2 (fn2-cns-post-outcome-children cns cns-gen request word position fn2-cns fn2-machines fn2-control)))
         (nth *fn2-machines-rows* fn2-machines)))
(in-theory (disable fn2-cns-post-outcome-children))
(make-event `(fn2-machines-keeps-directory fn2-cns-post-outcome-children
               (cns cns-gen request word position fn2-cns fn2-machines fn2-control) 2 nil
               ,(fn2-machines-keeps-directory-hints 'fn2-cns-post-outcome-children (w state))))

(defun fn2-upload-post-owner-children (conn conn-gen request word position fn2-conn fn2-cns fn2-machines fn2-control)
  (declare (xargs :stobjs (fn2-conn fn2-cns fn2-machines fn2-control)
                  :guard (and (fn2-conn-wfp fn2-conn) (fn2-cns-wfp fn2-cns)
                              (fn2-machines-wfp fn2-machines) (fn2-control-wfp fn2-control))))
  (if (and (fn2-machines-row-ok conn)
           (equal (fn2-machines-kind conn fn2-machines) *fn2-cns-kind*)
           (let ((slot (fn2-machines-slot conn fn2-machines)))
             (and (natp slot) (< slot (fn2-cns-rows fn2-cns)))))
      (mv-let (code fn2-cns fn2-machines fn2-control)
        (fn2-cns-post-outcome-children conn conn-gen request word position fn2-cns fn2-machines fn2-control)
        (mv code fn2-conn fn2-cns fn2-machines fn2-control))
    (mv-let (code fn2-conn fn2-machines fn2-control)
      (fn2-conn-post-word-children conn conn-gen request word fn2-conn fn2-machines fn2-control)
      (mv code fn2-conn fn2-cns fn2-machines fn2-control))))
(fn2-conn-preserves fn2-upload-post-owner-children (conn conn-gen request word position fn2-conn fn2-cns fn2-machines fn2-control)
  :carriers ((fn2-conn 1 :prefix "-CONN") (fn2-cns 2 :prefix "-CNS")
             (fn2-machines 3 :prefix "-MACHINES") (fn2-control 4 :prefix "-CONTROL"))
  :rows nil)
(defthm fn2-upload-post-owner-children-fn2-machines-rows
  (equal (fn2-machines-rows (mv-nth 3 (fn2-upload-post-owner-children conn conn-gen request word position fn2-conn fn2-cns fn2-machines fn2-control)))
         (fn2-machines-rows fn2-machines)))
(defthm fn2-upload-post-owner-children-fn2-machines-raw-rows
  (equal (nth *fn2-machines-rows* (mv-nth 3 (fn2-upload-post-owner-children conn conn-gen request word position fn2-conn fn2-cns fn2-machines fn2-control)))
         (nth *fn2-machines-rows* fn2-machines)))
(in-theory (disable fn2-upload-post-owner-children))
(make-event `(fn2-machines-keeps-directory fn2-upload-post-owner-children
               (conn conn-gen request word position fn2-conn fn2-cns fn2-machines fn2-control) 3 nil
               ,(fn2-machines-keeps-directory-hints 'fn2-upload-post-owner-children (w state))))

(defun fn2-upload-payload-settle-children (e epoch counter fn2-extents fn2-control)
  (declare (xargs :stobjs (fn2-extents fn2-control)
                  :guard (and (fn2-extents-wfp fn2-extents) (fn2-control-wfp fn2-control))))
  (if (equal e *fn2-none*) (mv :ok fn2-extents fn2-control)
    (b* (((mv code fn2-extents)
          (cond ((not (eq (fn2-alloc-handle-code e epoch counter fn2-extents) :ok)) (mv :fault fn2-extents))
                ((equal (fn2-extents-state e fn2-extents) *fn2-extent-state-allocated*) (mv :ok fn2-extents))
                (t (fn2-alloc-cancel-reservation e epoch counter fn2-extents))))
         (fn2-control (if (eq code :links) (fn2-control-record-stop *fn2-stop-reason-alloc-links* fn2-control) fn2-control)))
      (mv (if (eq code :ok) :ok :fault) fn2-extents fn2-control))))
(fn2-extents-preserves fn2-upload-payload-settle-children (e epoch counter fn2-extents fn2-control)
  :carriers ((fn2-extents 1 :prefix "-EXTENTS") (fn2-control 2 :prefix "-CONTROL"))
  :rows nil)
(in-theory (disable fn2-upload-payload-settle-children))

(defun fn2-upload-extent-commit-children (e epoch counter event fn2-extents)
  (declare (xargs :stobjs fn2-extents :guard (fn2-extents-wfp fn2-extents)))
  (if (not (unsigned-byte-p 60 event)) (mv :fault fn2-extents)
    (mv-let (code fn2-extents)
      (fn2-alloc-commit-allocation e epoch counter *fn2-txn-kind* event fn2-extents)
      (mv (if (eq code :ok) :ok :fault) fn2-extents))))
(fn2-extents-preserves fn2-upload-extent-commit-children (e epoch counter event fn2-extents)
  :position 1 :rows nil)
(in-theory (disable fn2-upload-extent-commit-children))

(defun fn2-upload-manifest-extents-children (fuel commit event base ls lg rel lim mfill okind oslot ogen
                                                  fn2-extents fn2-fields fn2-pool fn2-control)
  (declare (xargs :stobjs (fn2-extents fn2-fields fn2-pool fn2-control)
                  :measure (nfix fuel)
                  :guard (and (fn2-extents-wfp fn2-extents) (fn2-fields-wfp fn2-fields)
                              (fn2-pool-wfp fn2-pool) (fn2-control-wfp fn2-control) (natp fuel))))
  (let ((at (fn2-am-entry-at rel)))
    (if (or (>= at (nfix mfill)) (>= at (nfix lim))) (mv :ok fn2-extents fn2-fields fn2-control)
      (if (zp fuel) (mv :bounds fn2-extents fn2-fields fn2-control)
        (b* (((mv code next ?lo ?len unit epoch alloc fn2-fields)
              (fn2-am-get-entry base ls lg (+ *fn2-upload-page-manifest* at) (+ *fn2-upload-page-manifest* (nfix mfill))
                                okind oslot ogen fn2-fields fn2-pool))
             ((unless (and (eq code :ok) (natp next) (natp unit) (< *fn2-upload-page-manifest* next)))
              (mv :bounds fn2-extents fn2-fields fn2-control))
             ((mv code fn2-extents fn2-control)
              (cond ((not (equal (mod unit *fn2-commit-write-resources*) 0)) (mv :ok fn2-extents fn2-control))
                    (commit (mv-let (code fn2-extents)
                              (fn2-upload-extent-commit-children (floor unit *fn2-commit-write-resources*) epoch alloc event fn2-extents)
                              (mv code fn2-extents fn2-control)))
                    (t (fn2-upload-payload-settle-children (floor unit *fn2-commit-write-resources*) epoch alloc fn2-extents fn2-control))))
             ((unless (eq code :ok)) (mv code fn2-extents fn2-fields fn2-control)))
          (fn2-upload-manifest-extents-children (- fuel 1) commit event base ls lg (- next *fn2-upload-page-manifest*) lim mfill
                                                okind oslot ogen fn2-extents fn2-fields fn2-pool fn2-control))))))
(fn2-extents-preserves fn2-upload-manifest-extents-children
  (fuel commit event base ls lg rel lim mfill okind oslot ogen fn2-extents fn2-fields fn2-pool fn2-control)
  :carriers ((fn2-extents 1 :prefix "-EXTENTS") (fn2-fields 2 :prefix "-FIELDS") (fn2-control 3 :prefix "-CONTROL"))
  :rows nil)
(in-theory (disable fn2-upload-manifest-extents-children))

(defun fn2-upload-manifest-head-children (base total ls lg mfill okind oslot ogen fn2-fields fn2-pool)
  (declare (xargs :stobjs (fn2-fields fn2-pool)
                  :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
  (mv-let (code next fn2-fields)
    (fn2-am-get-header base total ls lg *fn2-upload-page-manifest* (+ *fn2-upload-page-manifest* (nfix mfill))
                       okind oslot ogen fn2-fields fn2-pool)
    (mv code (nfix (- next *fn2-upload-page-manifest*)) fn2-fields)))
(fn2-fields-preserves fn2-upload-manifest-head-children (base total ls lg mfill okind oslot ogen fn2-fields fn2-pool)
  :position 2 :rows nil)
(in-theory (disable fn2-upload-manifest-head-children))

(defun fn2-upload-manifest-walk-children (commit event base total ls lg mfill unit whole okind oslot ogen
                                                 fn2-extents fn2-fields fn2-pool fn2-control)
  (declare (xargs :stobjs (fn2-extents fn2-fields fn2-pool fn2-control)
                  :guard (and (fn2-extents-wfp fn2-extents) (fn2-fields-wfp fn2-fields)
                              (fn2-pool-wfp fn2-pool) (fn2-control-wfp fn2-control))))
  (if (not (and (fn2-am-manifestp total) (< 0 (nfix mfill)))) (mv :ok fn2-extents fn2-fields fn2-control)
    (b* ((lim (if whole (nfix mfill) (* *fn2-commit-unit-bytes* (+ 1 (nfix unit)))))
         ((mv code rel fn2-fields)
          (if (zp (nfix unit)) (fn2-upload-manifest-head-children base total ls lg mfill okind oslot ogen fn2-fields fn2-pool)
            (mv :ok (* *fn2-commit-unit-bytes* (nfix unit)) fn2-fields)))
         ((unless (eq code :ok)) (mv code fn2-extents fn2-fields fn2-control)))
      (fn2-upload-manifest-extents-children (+ 1 (nfix (fn2-am-blocks total))) commit event base ls lg rel lim mfill
                                            okind oslot ogen fn2-extents fn2-fields fn2-pool fn2-control))))
(fn2-extents-preserves fn2-upload-manifest-walk-children
  (commit event base total ls lg mfill unit whole okind oslot ogen fn2-extents fn2-fields fn2-pool fn2-control)
  :carriers ((fn2-extents 1 :prefix "-EXTENTS") (fn2-fields 2 :prefix "-FIELDS") (fn2-control 3 :prefix "-CONTROL"))
  :rows nil)
(in-theory (disable fn2-upload-manifest-walk-children))

(defun fn2-upload-extents-close-run-children (commit event pext pepoch palloc cext cepoch calloc cfree fn2-extents fn2-control)
  (declare (xargs :stobjs (fn2-extents fn2-control)
                  :guard (and (fn2-extents-wfp fn2-extents) (fn2-control-wfp fn2-control))))
  (b* (((mv code fn2-extents fn2-control)
        (if (and (equal cfree 1) (not commit))
            (fn2-upload-payload-settle-children cext cepoch calloc fn2-extents fn2-control)
          (mv :ok fn2-extents fn2-control)))
       ((unless (eq code :ok)) (mv code fn2-extents fn2-control)))
    (if commit
        (mv-let (code fn2-extents) (fn2-upload-extent-commit-children pext pepoch palloc event fn2-extents)
          (mv code fn2-extents fn2-control))
      (fn2-upload-payload-settle-children pext pepoch palloc fn2-extents fn2-control))))
(fn2-extents-preserves fn2-upload-extents-close-run-children
  (commit event pext pepoch palloc cext cepoch calloc cfree fn2-extents fn2-control)
  :carriers ((fn2-extents 1 :prefix "-EXTENTS") (fn2-control 2 :prefix "-CONTROL"))
  :rows nil)
(in-theory (disable fn2-upload-extents-close-run-children))

(defun fn2-upload-extents-of-children (commit event base total ls lg mfill pext pepoch palloc cext cepoch calloc cfree
                                              okind oslot ogen fn2-extents fn2-fields fn2-pool fn2-control)
  (declare (xargs :stobjs (fn2-extents fn2-fields fn2-pool fn2-control)
                  :guard (and (fn2-extents-wfp fn2-extents) (fn2-fields-wfp fn2-fields)
                              (fn2-pool-wfp fn2-pool) (fn2-control-wfp fn2-control))))
  (mv-let (code fn2-extents fn2-fields fn2-control)
    (fn2-upload-manifest-walk-children commit event base total ls lg mfill 0 t okind oslot ogen
                                       fn2-extents fn2-fields fn2-pool fn2-control)
    (if (not (eq code :ok)) (mv :fault fn2-extents fn2-fields fn2-control)
      (mv-let (code fn2-extents fn2-control)
        (fn2-upload-extents-close-run-children commit event pext pepoch palloc cext cepoch calloc cfree
                                               fn2-extents fn2-control)
        (mv (if (eq code :ok) :ok :fault) fn2-extents fn2-fields fn2-control)))))
(fn2-extents-preserves fn2-upload-extents-of-children
  (commit event base total ls lg mfill pext pepoch palloc cext cepoch calloc cfree
   okind oslot ogen fn2-extents fn2-fields fn2-pool fn2-control)
  :carriers ((fn2-extents 1 :prefix "-EXTENTS") (fn2-fields 2 :prefix "-FIELDS") (fn2-control 3 :prefix "-CONTROL"))
  :rows nil)
(in-theory (disable fn2-upload-extents-of-children))

(defcost fn2-upload-chunk-cap :child fn2-upload-chunk-cap-pool :doc "A chunk's capacity.")
(defcost fn2-upload-bound :doc "The article bound (the input configuration, at most two chunks).")
(defcost fn2-conn-post-word :child fn2-conn-post-word-children :tables (fn2-conn-table fn2-core-machines)
  :doc "Post an outcome word to the connection that awaits it (generation and request checked); wake it.")
(defcost fn2-cns-post-outcome :child fn2-cns-post-outcome-children :answers (:ok :dropped) :tables (fn2-cns-table fn2-core-machines)
  :doc "Post an append's outcome (its word and commit position) to the consumer request that awaits it (generation, request and phase checked); wake it.")
(defcost fn2-upload-post-owner :child fn2-upload-post-owner-children :answers (:ok :dropped) :tables (fn2-conn-table fn2-cns-table fn2-core-machines)
  :doc "Post an outcome to the upload's owner: a consumer request (fn2-cns-post-outcome) or a connection (fn2-conn-post-word).")
(defcost fn2-upload-advance :bytes *fn2-upload-run-bytes* :steps *fn2-work-transition*
  :answers (:run :idle :identity :receiving :sealed :discard :draining :stop)
  :faults (:stop)
  :tables (fn2-core-b3 fn2-core-digests fn2-core-machines fn2-core-machine-tables fn2-core-pool)
  :own-writes (hashed scan-off ofield visible nfields nlines seen mo ml no nl po pl head-status word inj)
  :doc "One run of an upload's work: hash, scan, and at the end the verdict posted to its connection (or handed to its transaction); returns the phase to move to.")
(defcost fn2-txn-gen-of :doc "A transaction row's generation.")
(defcost fn2-upload-conn-live-p :doc "Whether the connection still feeds this upload.")
(defcost fn2-upload-txn-live-p :doc "Whether the upload's transaction still names it.")
(defcost fn2-upload-wake :tables (fn2-core-machines) :doc "Wake the upload's transaction.")
(defcost fn2-upload-payload-reserve :answers (:ok :no-space :fault) :faults (:fault) :tables (fn2-core-extents)
  :doc "Reserve the extent the source is stored in (B's allocator): (mv code extent epoch counter).")
(defcost fn2-upload-payload-settle :child fn2-upload-payload-settle-children :answers (:ok :fault) :faults (:fault) :tables (fn2-core-extents)
  :doc "At the drain: a payload extent no transaction committed has its reservation cancelled.")
(defcost fn2-upload-store-span :doc "The next storage write's pool range, offset and length: (mv slot gen off len).")
(defcost fn2-upload-lease-class :doc "The pool class of the store page for stored octets of a length (nil: none).")
;; The source manifest's operations (stored octets longer than one extent).
(defcost fn2-upload-hasher :child fn2-upload-hasher-children :doc "The upload row's hasher row (3 + its slot), whose format stripe the manifest's fields use.")
(defcost fn2-upload-manifest-begin :answers (:ok :fault) :faults (:fault) :bytes *fn2-upload-head-bytes*
  :tables (fn2-core-pool fn2-core-fields)
  :doc "Encode the manifest's header at the (zeroed) store page's manifest: (mv code mfill).")
(defcost fn2-upload-stage :answers (:ok :fault) :faults (:fault) :bytes 4096 :tables (fn2-core-pool)
  :doc "Copy the next block of the stored octets into the store page's stage: (mv code len).")
(defcost fn2-upload-block-hash :answers (:ok :fault) :faults (:fault) :bytes *fn2-commit-unit-bytes*
  :tables (fn2-core-b3 fn2-core-digests fn2-core-pool)
  :doc "The staged block's BLAKE3 into the store page.")
(defcost fn2-upload-block-cv :answers (:ok :fault) :faults (:fault) :bytes *fn2-commit-unit-bytes*
  :tables (fn2-core-digests fn2-core-pool)
  :doc "The staged block's chaining value (its BLAKE3 for a short final block) into the store page.")
(defcost fn2-upload-block-entry :answers (:ok :fault) :faults (:fault) :bytes *fn2-upload-entry-bytes*
  :tables (fn2-core-pool fn2-core-fields)
  :doc "Encode the staged block's manifest entry after the manifest's octets: (mv code mfill).")
(defcost fn2-upload-page-zero-to :answers (:ok :more :fault) :faults (:fault) :bytes *fn2-commit-unit-bytes*
  :tables (fn2-core-pool)
  :doc "Zero the store page from its fill toward an offset, one unit at most (:more: not yet there).")
(defcost fn2-upload-extents-of :child fn2-upload-extents-of-children :answers (:ok :fault) :faults (:fault) :bytes *fn2-commit-extent-bytes*
  :tables (fn2-core-extents fn2-core-pool fn2-core-fields)
  :doc "Commit (to the article) or settle every extent stored octets occupy: the manifest's and each block's.")
(defcost fn2-upload-settle-unit :answers (:ok :fault) :faults (:fault) :bytes *fn2-commit-unit-bytes*
  :tables (fn2-core-extents fn2-core-pool fn2-core-fields)
  :doc "Settle the block extents the entries in one unit of the manifest name.")
(defcost fn2-upload-extents-close :answers (:ok :fault) :faults (:fault) :tables (fn2-core-extents)
  :doc "Settle the extent reserved for a block no entry names and the manifest's own (or the one payload extent).")
(defcost fn2-upload-put-mid :answers (:ok :fault) :faults (:fault) :bytes 264 :tables (fn2-core-pool fn2-core-control)
  :doc "Write the generated Message-ID field into the store page, <op-PRINCIPAL-OP@P> for an append's operation, else <fn2.E.A@P>: (mv code len).")

;; ------------------------------------------------------------------------
;; The operations both machines call, materialized after the core instance
;; and before the connection's continuations (assembly-callbacks-d.lisp).
(defmacro fn2-upload-op-events ()
 '(progn
(defun fn2-upload-hasher (id fn2-core)
  ;; the hasher row of the upload row ID: 3 + its slot (B-S1: rows 0-1 the
  ;; commit kind's, row 2 recovery's checker)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)
                  :guard-hints (("Goal" :in-theory (enable fn2-core-wfp)))))
  (stobj-let ((fn2-upload (fn2-upload-table fn2-core)) (fn2-machines (fn2-core-machines fn2-core)))
    (r) (fn2-upload-hasher-children id fn2-upload fn2-machines) r))
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
  :hints (("Goal" :in-theory (disable nfix))))
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
  :hints (("Goal" :in-theory (disable nfix))))
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
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)
                  :guard-hints (("Goal" :in-theory (enable fn2-core-wfp)))))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (n) (fn2-upload-chunk-cap-pool slot fn2-pool) n))
(defthm fn2-upload-chunk-cap-natp
  (natp (fn2-upload-chunk-cap slot fn2-core))
  :rule-classes :type-prescription)
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
(defun fn2-upload-verdict-step (rule status seen mo ml po pl len bound cslot cgen cs cl ck co cg slot gen id ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (word injected)
    (fn2-upload-verdict rule status (nfix seen) (nfix mo) (nfix ml) (nfix po) (nfix pl) (nfix len) (nfix bound)
                        (nfix cslot) (nfix cgen) (nfix cs) (nfix cl) (nfix ck) (nfix co) (nfix cg)
                        slot gen *fn2-upload-kind* id ogen fn2-pool)
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
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)
                  :guard-hints (("Goal" :in-theory (enable fn2-core-wfp)))))
  (stobj-let ((fn2-conn (fn2-conn-table fn2-core)) (fn2-machines (fn2-core-machines fn2-core))
              (fn2-control (fn2-core-control fn2-core)))
    (code fn2-conn fn2-machines fn2-control)
    (fn2-conn-post-word-children conn conn-gen request word fn2-conn fn2-machines fn2-control)
    (mv code fn2-core)))
(fn2-core-preserves fn2-conn-post-word (conn conn-gen request word fn2-core) :position 1 :rows nil)
(defun fn2-cns-post-outcome (cns cns-gen request word position fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)
                  :guard-hints (("Goal" :in-theory (enable fn2-core-wfp)))))
  (stobj-let ((fn2-cns (fn2-cns-table fn2-core)) (fn2-machines (fn2-core-machines fn2-core))
              (fn2-control (fn2-core-control fn2-core)))
    (code fn2-cns fn2-machines fn2-control)
    (fn2-cns-post-outcome-children cns cns-gen request word position fn2-cns fn2-machines fn2-control)
    (mv code fn2-core)))
(fn2-core-preserves fn2-cns-post-outcome (cns cns-gen request word position fn2-core) :position 1 :rows nil)
(defun fn2-upload-post-owner (conn conn-gen request word position fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)
                  :guard-hints (("Goal" :in-theory (enable fn2-core-wfp)))))
  (stobj-let ((fn2-conn (fn2-conn-table fn2-core)) (fn2-cns (fn2-cns-table fn2-core))
              (fn2-machines (fn2-core-machines fn2-core)) (fn2-control (fn2-core-control fn2-core)))
    (code fn2-conn fn2-cns fn2-machines fn2-control)
    (fn2-upload-post-owner-children conn conn-gen request word position fn2-conn fn2-cns fn2-machines fn2-control)
    (mv code fn2-core)))
(fn2-core-preserves fn2-upload-post-owner (conn conn-gen request word position fn2-core) :position 1 :rows nil)
(in-theory (disable fn2-conn-post-word fn2-cns-post-outcome))

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
(fn2-core-preserves fn2-upload-scan-run (id gen c0 g0 fn2-core) :position 2 :rows nil
  :hints (("Goal" :in-theory (disable fn2-upload-snapshot-read-code fn2-upload-head-code nfix unsigned-byte-p))))
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
         (conn (fn2-upload-row-conn id fn2-core))
         (conn-gen (fn2-upload-row-conn-gen id fn2-core))
         (conn-ok (and (eq (fn2-conn-snapshot-read-code conn fn2-core) :ok)
                       (equal (fn2-machine-generation conn fn2-core) conn-gen)))
         (cslot (if conn-ok (fn2-conn-row-tx-slot conn fn2-core) *fn2-none*))
         (cgen (if conn-ok (fn2-conn-row-tx-gen conn fn2-core) 0))
         (cl (if conn-ok (fn2-conn-row-line-e conn fn2-core) 0))
         ((mv word injected)
          (fn2-upload-verdict-step rule (fn2-upload-head-keyword (fn2-upload-row-head-status id fn2-core)) seen
                                   (fn2-upload-row-mo id fn2-core) (fn2-upload-row-ml id fn2-core)
                                   (fn2-upload-row-po id fn2-core) (fn2-upload-row-pl id fn2-core) filled
                                   (fn2-upload-bound cap0 cap1 fn2-core)
                                   cslot cgen 0 cl *fn2-conn-kind* conn conn-gen
                                   c0 g0 id gen fn2-core))
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
  :hints (("Goal" :in-theory (disable nfix))))
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
       ((mv & fn2-core) (fn2-upload-post-owner conn conn-gen request code 0 fn2-core)))
    fn2-core))
(fn2-core-preserves fn2-upload-deliver-word (id code conn conn-gen request fn2-core) :rows nil)
(in-theory (disable fn2-upload-post-owner fn2-upload-digest fn2-upload-word-now fn2-upload-digest-store fn2-upload-wake fn2-upload-hand-over
                    fn2-upload-deliver-word))
;; The payload extent (S-ARTICLE-LOCATION). Reserved from B's allocator
;; before the source is written: (mv code extent epoch counter fn2-core),
;; :no-space when no extent is free, :fault for a broken allocator (the
;; core stops :alloc-links on a broken free list, as the commit kind's
;; reservation does).
(defun fn2-upload-payload-reserve (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* (((mv code e epoch counter fn2-core)
        (stobj-let ((fn2-extents (fn2-core-extents fn2-core)))
          (code e epoch counter fn2-extents)
          (mv-let (code pressure e epoch counter fn2-extents) (fn2-alloc-reserve fn2-extents)
            (declare (ignore pressure))
            (mv code e epoch counter fn2-extents))
          (mv code e epoch counter fn2-core)))
       (fn2-core (if (eq code :links) (fn2-core-stop *fn2-stop-reason-alloc-links* fn2-core) fn2-core)))
    (cond ((and (eq code :ok) (unsigned-byte-p 32 e) (not (equal e *fn2-none*))
                (unsigned-byte-p 60 epoch) (unsigned-byte-p 60 counter))
           (mv :ok e epoch counter fn2-core))
          ((eq code :no-space) (mv :no-space 0 0 0 fn2-core))
          (t (mv :fault 0 0 0 fn2-core)))))
(fn2-core-preserves fn2-upload-payload-reserve (fn2-core) :position 4 :rows nil)
;; At the drain: an extent still reserved under this handle (no transaction
;; committed it) is returned; an allocated one is the article's. No extent
;; (*fn2-none*) is nothing to settle.
(defun fn2-upload-payload-settle (e epoch counter fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)
                  :guard-hints (("Goal" :in-theory (enable fn2-core-wfp)))))
  (stobj-let ((fn2-extents (fn2-core-extents fn2-core)) (fn2-control (fn2-core-control fn2-core)))
    (code fn2-extents fn2-control)
    (fn2-upload-payload-settle-children e epoch counter fn2-extents fn2-control)
    (mv code fn2-core)))
(fn2-core-preserves fn2-upload-payload-settle (e epoch counter fn2-core) :position 1 :rows nil)
;; The next storage write of the stored octets after DONE of them (the
;; injected field's ILEN octets from the store page LS LG, then the source
;; from the chunks): its pool range, the offset in it and the length (at most
;; one unit, never past the part or the chunk): (mv slot gen off len).
(defun fn2-upload-store-span (ls lg ilen c0 g0 c1 g1 done hashed fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (natp ilen) (natp done) (natp hashed))))
  (if (< done ilen) (mv ls lg done (min *fn2-commit-unit-bytes* (- ilen done)))
    (b* ((src (- done ilen))
         (cap0 (fn2-upload-chunk-cap c0 fn2-core))
         (in0 (< src cap0))
         (off (if in0 src (- src cap0)))
         (room (if in0 (- cap0 src) (nfix (- (fn2-upload-chunk-cap c1 fn2-core) off)))))
      (mv (if in0 c0 c1) (if in0 g0 g1) off
          (min *fn2-commit-unit-bytes* (min room (nfix (- hashed src))))))))
;; State preservation does not depend on the read-only span calculation.
;; Keep its branches out of the recursive stage-loop preservation induction.
(in-theory (disable fn2-upload-store-span))
(defun fn2-upload-lease-class (total fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (class) (fn2-pool-class-for (fn2-upload-page-bytes total) fn2-pool) class))
;; Zeros from the store page's fill to TO (the regions after the generated
;; field are written in place, and the manifest's last unit is whole on
;; storage): (mv code fn2-core).
(defun fn2-upload-page-zero (left at slot gen okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :measure (nfix left)
                  :guard (and (fn2-core-wfp fn2-core) (natp left) (natp at))))
  (if (zp left) (mv :ok fn2-core)
    (mv-let (code fn2-core) (fn2-core-write slot gen at 0 okind oslot ogen fn2-core)
      (if (eq code :ok) (fn2-upload-page-zero (- left 1) (+ at 1) slot gen okind oslot ogen fn2-core)
        (mv code fn2-core)))))
(fn2-core-preserves fn2-upload-page-zero (left at slot gen okind oslot ogen fn2-core) :position 1 :rows nil)
;; The page zeroed from its fill toward TO, one unit of zeros at most:
;; (mv code fn2-core), :more while TO is farther.
(defun fn2-upload-page-zero-to (to ls lg okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (let* ((pfill (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (n) (fn2-gram-fill ls fn2-pool) n))
         (left (nfix (- (nfix to) pfill))))
    (mv-let (code fn2-core)
      (fn2-upload-page-zero (min left *fn2-commit-unit-bytes*) pfill ls lg okind oslot ogen fn2-core)
      (mv (cond ((not (eq code :ok)) :fault) ((< *fn2-commit-unit-bytes* left) :more) (t :ok)) fn2-core))))
(fn2-core-preserves fn2-upload-page-zero-to (to ls lg okind oslot ogen fn2-core) :position 1 :rows nil)
;; The manifest begun (the page zeroed to its start first, by
;; fn2-upload-page-zero-to): the header (TOTAL stored octets, the source
;; identity where the verdict appended it) encoded at
;; *fn2-upload-page-manifest*: (mv code mfill fn2-core), MFILL the manifest's
;; octets. Fields at the window's format stripe (row ROW).
(defun fn2-upload-manifest-begin (row ls lg total c0 g0 c1 g1 hashed okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (natp hashed))))
  (b* ((pfill (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (n) (fn2-gram-fill ls fn2-pool) n))
       ((unless (equal pfill *fn2-upload-page-manifest*)) (mv :fault 0 fn2-core))
       ((mv in1 doff) (fn2-upload-digest-at hashed (fn2-upload-chunk-cap c0 fn2-core))))
    (stobj-let ((fn2-fields (fn2-core-fields fn2-core)) (fn2-pool (fn2-core-pool fn2-core)))
      (code end fn2-fields fn2-pool)
      (fn2-am-put-header (* 128 (nfix row)) total (if in1 c1 c0) (if in1 g1 g0) doff ls lg *fn2-upload-page-manifest*
                         okind oslot ogen fn2-fields fn2-pool)
      (mv (if (eq code :ok) :ok :fault) (nfix (- (nfix end) *fn2-upload-page-manifest*)) fn2-core))))
(fn2-core-preserves fn2-upload-manifest-begin (row ls lg total c0 g0 c1 g1 hashed okind oslot ogen fn2-core) :position 2 :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))
;; Block DONE / unit of the stored octets copied to the page's stage, piece
;; by piece (the generated field, chunk 0, chunk 1; FUEL pieces at most):
;; (mv code fn2-core).
(defun fn2-upload-stage-loop (fuel ls lg ilen c0 g0 c1 g1 d bstart bend hashed okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :measure (nfix fuel)
                  :guard (and (fn2-core-wfp fn2-core) (natp fuel) (natp ilen) (natp d) (natp bstart) (natp bend) (natp hashed))))
  (if (>= (nfix d) (nfix bend)) (mv :ok fn2-core)
    (if (zp fuel) (mv :bounds fn2-core)
      (b* (((mv s g o l) (fn2-upload-store-span ls lg ilen c0 g0 c1 g1 (nfix d) hashed fn2-core))
           (l (min (nfix l) (- (nfix bend) (nfix d))))
           ((unless (posp l)) (mv :bounds fn2-core))
           ((mv code fn2-core)
            (fn2-core-copy-range s g o ls lg (+ *fn2-upload-page-stage* (- (nfix d) (nfix bstart))) l
                                 okind oslot ogen fn2-core))
           ((unless (eq code :ok)) (mv code fn2-core)))
        (fn2-upload-stage-loop (- fuel 1) ls lg ilen c0 g0 c1 g1 (+ (nfix d) l) bstart bend hashed okind oslot ogen fn2-core)))))
(fn2-core-preserves fn2-upload-stage-loop (fuel ls lg ilen c0 g0 c1 g1 d bstart bend hashed okind oslot ogen fn2-core)
  :position 1 :rows nil)
(defun fn2-upload-stage (ls lg ilen c0 g0 c1 g1 done hashed okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (natp ilen) (natp done) (natp hashed))))
  (let ((bend (min (+ (nfix done) *fn2-commit-unit-bytes*) (+ (nfix ilen) (nfix hashed)))))
    (mv-let (code fn2-core) (fn2-upload-stage-loop 4 ls lg ilen c0 g0 c1 g1 done done bend hashed okind oslot ogen fn2-core)
      (mv (if (eq code :ok) :ok :fault) (nfix (- bend (nfix done))) fn2-core))))
(fn2-core-preserves fn2-upload-stage (ls lg ilen c0 g0 c1 g1 done hashed okind oslot ogen fn2-core) :position 2 :rows nil)
;; LEFT octets from OFF of SLOT GEN into the hasher row, a hasher step at a
;; time (FUEL steps at most): (mv code fn2-core).
(defun fn2-upload-hash-span (fuel row slot gen off left id ogen fn2-core)
  (declare (xargs :stobjs fn2-core :measure (nfix fuel) :guard (and (fn2-core-wfp fn2-core) (natp fuel) (natp left))))
  (if (zp left) (mv :ok fn2-core)
    (if (zp fuel) (mv :bounds fn2-core)
      (mv-let (code used fn2-core) (fn2-upload-hash-step row slot gen off left id ogen fn2-core)
        (if (and (member-eq code '(:ok :more)) (posp used) (<= used left))
            (fn2-upload-hash-span (- fuel 1) row slot gen (+ (nfix off) used) (- left used) id ogen fn2-core)
          (mv :bounds fn2-core))))))
(fn2-core-preserves fn2-upload-hash-span (fuel row slot gen off left id ogen fn2-core) :position 1 :rows nil)
;; The staged block's BLAKE3 into the page at *fn2-upload-page-hash* (the
;; window's hasher row ROW; after the verdict the source's digest is already
;; appended to it): (mv code fn2-core).
(defun fn2-upload-block-hash-run (row ls lg blen okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)) (ignorable okind))
  (b* (((mv code fn2-core) (fn2-upload-hash-begin row fn2-core))
       ((unless (eq code :ok)) (mv code fn2-core))
       ((mv code fn2-core)
        (if (and (natp blen) (<= blen *fn2-commit-unit-bytes*))
            (fn2-upload-hash-span 8 row ls lg *fn2-upload-page-stage* blen oslot ogen fn2-core)
          (mv :bounds fn2-core)))
       ((unless (eq code :ok)) (mv :bounds fn2-core))
       ((mv code fn2-core) (fn2-upload-hash-end row fn2-core))
       ((unless (eq code :ok)) (mv code fn2-core)))
    (fn2-upload-digest-store row ls lg *fn2-upload-page-hash* oslot ogen fn2-core)))
(fn2-core-preserves fn2-upload-block-hash-run (row ls lg blen okind oslot ogen fn2-core) :position 1 :rows nil)
(defun fn2-upload-block-hash (row ls lg blen okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (mv-let (code fn2-core) (fn2-upload-block-hash-run row ls lg blen okind oslot ogen fn2-core)
    (mv (if (eq code :ok) :ok :fault) fn2-core)))
(fn2-core-preserves fn2-upload-block-hash (row ls lg blen okind oslot ogen fn2-core) :position 1 :rows nil)
;; The staged block's chaining value at chunk counter 4 BLOCK (a whole unit)
;; into the page 32 octets after its BLAKE3; a short final block is no
;; complete subtree and its BLAKE3 (still the hasher row's result) goes there
;; again (article-manifest.lisp): (mv code fn2-core).
(defun fn2-upload-block-cv (row ls lg blen block okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)) (ignorable okind))
  (b* ((fn2-core
        (if (equal blen *fn2-commit-unit-bytes*)
            (stobj-let ((fn2-digests (fn2-core-digests fn2-core)) (fn2-pool (fn2-core-pool fn2-core)))
              (fn2-digests)
              (let ((dst (fn2-digest-slot (nfix row) *fn2-b3-result*))
                    (off (+ (if (and (natp ls) (< ls (fn2-pool-rows fn2-pool))) (nfix (fn2-pool-slot-base ls fn2-pool)) 0)
                            *fn2-upload-page-stage*))
                    (counter (* 4 (nfix block))))
                (if (and (natp row) (fn2-digest-rowp dst fn2-digests) (fn2-pool-wfp fn2-pool)
                         (<= (+ off *fn2-commit-unit-bytes*) (fn2-pool-data-length fn2-pool))
                         (unsigned-byte-p 48 counter))
                    (fn2-b3-subtree-cv-into dst off *fn2-commit-unit-bytes* counter fn2-digests fn2-pool)
                  fn2-digests))
              fn2-core)
          fn2-core))
       ((mv code fn2-core) (fn2-upload-digest-store row ls lg (+ 32 *fn2-upload-page-hash*) oslot ogen fn2-core)))
    (mv (if (eq code :ok) :ok :fault) fn2-core)))
(fn2-core-preserves fn2-upload-block-cv (row ls lg blen block okind oslot ogen fn2-core) :position 1 :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))
;; The block's entry after the manifest's MFILL octets (the packing rule):
;; (mv code mfill fn2-core).
(defun fn2-upload-block-entry (row ls lg block blen unit epoch alloc mfill okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* ((at (+ *fn2-upload-page-manifest* (fn2-am-entry-at mfill)))
       ((mv code fn2-core) (fn2-upload-page-zero-to at ls lg okind oslot ogen fn2-core))
       ((unless (eq code :ok)) (mv :fault 0 fn2-core)))
  (stobj-let ((fn2-fields (fn2-core-fields fn2-core)) (fn2-pool (fn2-core-pool fn2-core)))
    (code end fn2-fields fn2-pool)
    (fn2-am-put-entry (* 128 (nfix row)) block blen unit epoch alloc ls lg *fn2-upload-page-hash*
                      ls lg at okind oslot ogen fn2-fields fn2-pool)
    (mv (if (eq code :ok) :ok :fault) (nfix (- (nfix end) *fn2-upload-page-manifest*)) fn2-core))))
(fn2-core-preserves fn2-upload-block-entry (row ls lg block blen unit epoch alloc mfill okind oslot ogen fn2-core)
  :position 2 :rows nil :hints (("Goal" :in-theory (enable fn2-core-wfp))))
;; An accepted article's payload extent (its upload's reservation) becomes
;; allocated, owned by the article (the transaction kind, EVENT).
(defun fn2-upload-extent-commit (e epoch counter event fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (not (unsigned-byte-p 60 event)) (mv :fault fn2-core)
    (stobj-let ((fn2-extents (fn2-core-extents fn2-core)))
      (code fn2-extents)
      (fn2-alloc-commit-allocation e epoch counter *fn2-txn-kind* event fn2-extents)
      (mv (if (eq code :ok) :ok :fault) fn2-core))))
(fn2-core-preserves fn2-upload-extent-commit (e epoch counter event fn2-core) :position 1 :rows nil)
;; Every extent the entries of a manifest of MFILL octets starting before LIM
;; name (the extent of each entry at unit 0 of its extent), taken by COMMIT
;; (owned by the transaction kind's EVENT) or else settled (a reservation
;; nothing committed is cancelled), FUEL entries at most: (mv code fn2-core).
;; Fields at BASE; the page is owned by OKIND OSLOT OGEN.
(defun fn2-upload-manifest-extents (fuel commit event base ls lg rel lim mfill okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :measure (nfix fuel) :guard (and (fn2-core-wfp fn2-core) (natp fuel))))
  (let ((at (fn2-am-entry-at rel)))
    (if (or (>= at (nfix mfill)) (>= at (nfix lim))) (mv :ok fn2-core)
      (if (zp fuel) (mv :bounds fn2-core)
        (b* (((mv code next ?lo ?len unit epoch alloc fn2-core)
              (stobj-let ((fn2-fields (fn2-core-fields fn2-core)) (fn2-pool (fn2-core-pool fn2-core)))
                (code next lo len unit epoch alloc fn2-fields)
                (fn2-am-get-entry base ls lg (+ *fn2-upload-page-manifest* at) (+ *fn2-upload-page-manifest* (nfix mfill))
                                  okind oslot ogen fn2-fields fn2-pool)
                (mv code next lo len unit epoch alloc fn2-core)))
             ((unless (and (eq code :ok) (natp next) (natp unit) (< *fn2-upload-page-manifest* next))) (mv :bounds fn2-core))
             ((mv code fn2-core)
              (cond ((not (equal (mod unit *fn2-commit-write-resources*) 0)) (mv :ok fn2-core))
                    (commit (fn2-upload-extent-commit (floor unit *fn2-commit-write-resources*) epoch alloc event fn2-core))
                    (t (fn2-upload-payload-settle (floor unit *fn2-commit-write-resources*) epoch alloc fn2-core))))
             ((unless (eq code :ok)) (mv code fn2-core)))
          (fn2-upload-manifest-extents (- fuel 1) commit event base ls lg (- next *fn2-upload-page-manifest*) lim mfill
                                       okind oslot ogen fn2-core))))))
(fn2-core-preserves fn2-upload-manifest-extents (fuel commit event base ls lg rel lim mfill okind oslot ogen fn2-core)
  :position 1 :rows nil)
;; The manifest's header length (where its first entry follows): (mv code rel).
(defun fn2-upload-manifest-head (base total ls lg mfill okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-fields (fn2-core-fields fn2-core)) (fn2-pool (fn2-core-pool fn2-core)))
    (code next fn2-fields)
    (fn2-am-get-header base total ls lg *fn2-upload-page-manifest* (+ *fn2-upload-page-manifest* (nfix mfill))
                       okind oslot ogen fn2-fields fn2-pool)
    (mv code (nfix (- next *fn2-upload-page-manifest*)) fn2-core)))
(fn2-core-preserves fn2-upload-manifest-head (base total ls lg mfill okind oslot ogen fn2-core) :position 2 :rows nil)
;; The block extents a manifest of MFILL octets for TOTAL stored octets
;; names, by the entries in its unit UNIT (all of them, WHOLE; the header
;; is at the start of unit 0), committed (COMMIT, EVENT) or settled:
;; (mv code fn2-core).
(defun fn2-upload-manifest-walk (commit event base total ls lg mfill unit whole okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (not (and (fn2-am-manifestp total) (< 0 (nfix mfill)))) (mv :ok fn2-core)
    (b* ((lim (if whole (nfix mfill) (* *fn2-commit-unit-bytes* (+ 1 (nfix unit)))))
         ((mv code rel fn2-core)
          (if (zp (nfix unit)) (fn2-upload-manifest-head base total ls lg mfill okind oslot ogen fn2-core)
            (mv :ok (* *fn2-commit-unit-bytes* (nfix unit)) fn2-core)))
         ((unless (eq code :ok)) (mv code fn2-core)))
      (fn2-upload-manifest-extents (+ 1 (nfix (fn2-am-blocks total))) commit event base ls lg rel lim mfill
                                   okind oslot ogen fn2-core))))
(fn2-core-preserves fn2-upload-manifest-walk (commit event base total ls lg mfill unit whole okind oslot ogen fn2-core)
  :position 1 :rows nil)
;; The manifest's units the drain settles one per step (none without one).
(defun fn2-upload-manifest-units (total mfill)
  (declare (xargs :guard t))
  (if (fn2-am-manifestp total) (ceiling (nfix mfill) *fn2-commit-unit-bytes*) 0))
(defun fn2-upload-settle-unit (base total ls lg mfill unit okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (mv-let (code fn2-core) (fn2-upload-manifest-walk nil 0 base total ls lg mfill unit nil okind oslot ogen fn2-core)
    (mv (if (eq code :ok) :ok :fault) fn2-core)))
(fn2-core-preserves fn2-upload-settle-unit (base total ls lg mfill unit okind oslot ogen fn2-core) :position 1 :rows nil)
;; After the blocks' extents: a current extent reserved for a block whose
;; entry never came (CFREE) is settled, and the manifest's own extent (or the
;; one payload extent, PEXT) is committed (COMMIT, EVENT) or settled.
(defun fn2-upload-extents-close-run (commit event pext pepoch palloc cext cepoch calloc cfree fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* (((mv code fn2-core) (if (and (equal cfree 1) (not commit))
                               (fn2-upload-payload-settle cext cepoch calloc fn2-core) (mv :ok fn2-core)))
       ((unless (eq code :ok)) (mv code fn2-core)))
    (if commit (fn2-upload-extent-commit pext pepoch palloc event fn2-core)
      (fn2-upload-payload-settle pext pepoch palloc fn2-core))))
(fn2-core-preserves fn2-upload-extents-close-run (commit event pext pepoch palloc cext cepoch calloc cfree fn2-core)
  :position 1 :rows nil)
(defun fn2-upload-extents-close (pext pepoch palloc cext cepoch calloc cfree fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (mv-let (code fn2-core) (fn2-upload-extents-close-run nil 0 pext pepoch palloc cext cepoch calloc cfree fn2-core)
    (mv (if (eq code :ok) :ok :fault) fn2-core)))
(fn2-core-preserves fn2-upload-extents-close (pext pepoch palloc cext cepoch calloc cfree fn2-core) :position 1 :rows nil)
;; The extents of stored octets of TOTAL: every block's (the whole manifest
;; in one call, at most one extent of it decoded) and then the close.
(defun fn2-upload-extents-run (commit event base total ls lg mfill pext pepoch palloc cext cepoch calloc cfree
                                     okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* (((mv code fn2-core) (fn2-upload-manifest-walk commit event base total ls lg mfill 0 t okind oslot ogen fn2-core))
       ((unless (eq code :ok)) (mv code fn2-core)))
    (fn2-upload-extents-close-run commit event pext pepoch palloc cext cepoch calloc cfree fn2-core)))
(fn2-core-preserves fn2-upload-extents-run (commit event base total ls lg mfill pext pepoch palloc cext cepoch calloc cfree
                                                  okind oslot ogen fn2-core) :position 1 :rows nil)
(defun fn2-upload-extents-of (commit event base total ls lg mfill pext pepoch palloc cext cepoch calloc cfree
                                     okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)
                  :guard-hints (("Goal" :in-theory (enable fn2-core-wfp)))))
  (stobj-let ((fn2-extents (fn2-core-extents fn2-core)) (fn2-fields (fn2-core-fields fn2-core))
              (fn2-pool (fn2-core-pool fn2-core)) (fn2-control (fn2-core-control fn2-core)))
    (code fn2-extents fn2-fields fn2-control)
    (fn2-upload-extents-of-children commit event base total ls lg mfill pext pepoch palloc cext cepoch calloc cfree
                                    okind oslot ogen fn2-extents fn2-fields fn2-pool fn2-control)
    (mv code fn2-core)))
(fn2-core-preserves fn2-upload-extents-of (commit event base total ls lg mfill pext pepoch palloc cext cepoch calloc cfree
                                                  okind oslot ogen fn2-core) :position 1 :rows nil)
;; The path identity's octets [I, length) of fn2-control-path-identity,
;; appended to the page.
(defun fn2-upload-put-path (i slot gen okind oslot ogen fn2-control fn2-pool)
  (declare (xargs :stobjs (fn2-control fn2-pool)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp i))
                  :measure (nfix (- (fn2-control-path-identity-length fn2-control) (nfix i)))))
  (if (or (not (natp i)) (>= i (fn2-control-path-identity-length fn2-control))) (mv :ok fn2-pool)
    (mv-let (code fn2-pool)
      (fn2-gram-put (nfix (fn2-control-path-identityi i fn2-control)) slot gen okind oslot ogen fn2-pool)
      (if (not (eq code :ok)) (mv code fn2-pool)
        (fn2-upload-put-path (+ 1 i) slot gen okind oslot ogen fn2-control fn2-pool)))))
(fn2-pool-preserves fn2-upload-put-path (i slot gen okind oslot ogen fn2-control fn2-pool) :position 1 :rows nil)
;; The generated Message-ID field appended to the empty store page: the
;; template (*fn2-upload-mid-template*, to the "@"), the profile's path
;; identity, *fn2-upload-mid-close*: (mv code len fn2-core), LEN the field's
;; octets. An append with operation OP (not 0) gets *fn2-upload-op-mid-template*
;; over (PRINCIPAL, OP) instead.
(defun fn2-upload-put-mid (slot gen epoch alloc op principal okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)) (fn2-control (fn2-core-control fn2-core)))
    (code len fn2-pool)
    (if (and (natp epoch) (natp alloc) (natp op) (natp principal) (equal (fn2-gram-fill slot fn2-pool) 0))
        (mv-let (code fn2-pool)
          (fn2-gram-put-chain
           (if (equal op 0)
               (fn2-gram-put-template 0 *fn2-upload-mid-template* 0 epoch alloc 0 slot gen 0 0 slot gen okind oslot ogen fn2-pool)
             (fn2-gram-put-template 0 *fn2-upload-op-mid-template* 0 principal op 0 slot gen 0 0 slot gen okind oslot ogen fn2-pool))
           (fn2-upload-put-path 0 slot gen okind oslot ogen fn2-control fn2-pool)
           (fn2-gram-put-template 0 *fn2-upload-mid-close* 0 0 0 0 slot gen 0 0 slot gen okind oslot ogen fn2-pool))
          (mv (if (eq code :ok) :ok :fault) (nfix (fn2-gram-fill slot fn2-pool)) fn2-pool))
      (mv :fault 0 fn2-pool))
    (mv code len fn2-core)))
(fn2-core-preserves fn2-upload-put-mid (slot gen epoch alloc op principal okind oslot ogen fn2-core) :position 2 :rows nil
  :hints (("Goal" :in-theory (disable nfix))))
(in-theory (disable fn2-upload-payload-reserve fn2-upload-payload-settle fn2-upload-store-span
                    fn2-upload-lease-class fn2-upload-put-mid fn2-upload-page-zero fn2-upload-page-zero-to fn2-upload-manifest-begin
                    fn2-upload-stage-loop fn2-upload-stage fn2-upload-hash-span fn2-upload-block-hash-run fn2-upload-block-hash fn2-upload-block-entry
                    fn2-upload-extent-commit fn2-upload-manifest-extents fn2-upload-manifest-head fn2-upload-extents-run fn2-upload-extents-of
                    fn2-upload-block-cv fn2-upload-manifest-walk fn2-upload-manifest-units fn2-upload-settle-unit
                    fn2-upload-extents-close-run fn2-upload-extents-close))

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
;; phase to move to (:identity :receiving :discard :sealed :draining), or
;; :run (more to do now), :idle (wait for input), :stop (an invariant failed).
(defun fn2-upload-advance (id filled terminated discard fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (natp filled) (natp discard))))
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
       ;; a discarded block: nothing to hash; at its terminator, the refusal
       ;; (handed to the transaction when there is one)
       ((unless (equal discard 0))
        (b* (((unless terminated)
              (mv (if (equal ph *fn2-upload-state-discard*) :idle :discard) fn2-core))
             (w (fn2-upload-word-code (if (equal discard 1) :framing :too-large)))
             ((unless (equal txn *fn2-none*)) (let ((fn2-core (fn2-upload-hand-over id w 0 txn fn2-core))) (mv :sealed fn2-core)))
             ((mv & fn2-core) (fn2-upload-post-owner conn conn-gen request w 0 fn2-core)))
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
(fn2-core-preserves fn2-upload-advance (id filled terminated discard fn2-core) :position 1 :rows nil)
(in-theory (disable fn2-upload-advance))
))

;; ------------------------------------------------------------------------
;; The upload's continuations (materialized in assembly-callbacks-d-upload.lisp).
(defmacro fn2-upload-events ()
 '(progn
(defmachine-arms fn2-upload)
(defmachine-run fn2-upload)
))
