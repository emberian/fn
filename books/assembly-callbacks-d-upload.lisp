; The upload kind's continuations (D4, books/upload.lisp), in their own leaf
; section book so arm-body edits do not invalidate assembly.cert or executor.cert.
(in-package "ACL2")
(include-book "assembly-callbacks-d")
(include-book "upload")

(defun fn2-upload-release-c0 (slot gen okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (fn2-core-release slot gen okind oslot ogen fn2-core))
(fn2-core-preserves fn2-upload-release-c0 (slot gen okind oslot ogen fn2-core) :position 1 :rows nil)
(in-theory (disable fn2-upload-release-c0))
(defcost fn2-upload-release-c0 :answers t :tables (fn2-core-pool)
  :doc "Release the first chunk of a draining upload's chunk window.")

(defmachine-arms fn2-upload :declare
 :subarms
 ((work
   (:if (not (:live conn))
        ((:next :aborting) (:charge :bytes *fn2-upload-run-bytes* :steps *fn2-work-transition* :runnable t))
        ((:do (next)
              (fn2-upload-advance id (:read conn fed)
                                  (equal (:read conn feed-mode) *fn2-conn-feed-done*)
                                  (:read conn feed-discard))
              :accept ()
              :case (((:run) (:charge :bytes *fn2-upload-run-bytes* :steps *fn2-work-transition* :runnable t))
                     ((:idle) (:charge :bytes *fn2-upload-run-bytes* :steps *fn2-work-transition*))
                     ((:identity) (:next :identity)
                      (:charge :bytes *fn2-upload-run-bytes* :steps *fn2-work-transition* :runnable t))
                     ((:receiving) (:next :receiving)
                      (:charge :bytes *fn2-upload-run-bytes* :steps *fn2-work-transition* :runnable t))
                     ;; the verdict is handed over: store the source before
                     ;; the transaction reads the sealed upload
                     ((:sealed) (:next :store)
                      (:charge :bytes *fn2-upload-run-bytes* :steps *fn2-work-transition* :runnable t))
                     ((:discard) (:next :discard)
                      (:charge :bytes *fn2-upload-run-bytes* :steps *fn2-work-transition*))
                     ((:draining) (:next :draining)
                      (:charge :bytes *fn2-upload-run-bytes* :steps *fn2-work-transition* :runnable t))
                     ((:stop) (:stop :machine-phase))))))))
 :arms
 ((:free (:idle))
  (:head (:goto work))
  ;; :identity: take the transaction row (A-S7), the transaction's copies this
  ;; row's; refused, the take parked this row on the transaction kind's FIFO
  ;; and its grant runs this arm again. The connection gone: abort.
  (:identity
   (:if (not (:live conn))
        ((:next :aborting) (:charge :steps *fn2-work-transition* :runnable t))
        ((:do (code tid tgen)
              (fn2-machine-take-fn2-txn *fn2-none* id row-generation row-conn row-conn-gen
                                        row-request row-rule row-principal-slot)
              :case (((:ok) (:set (txn tid) (txn-gen tgen)) (:next :receiving)
                      (:charge :steps *fn2-work-transition* :runnable t))
                     (:otherwise (:park :taken fn2-txn :steps *fn2-work-transition*)))))))
  (:receiving (:goto work))
  (:validating (:goto work))
  (:discard (:goto work))
  ;; :store (S-ARTICLE-LOCATION): a clean verdict's source [0, HASHED) is
  ;; written to an extent of its own (B's allocator, the commit arena's
  ;; units) and fenced before the transaction may read the sealed upload,
  ;; so the article row's location names durable octets before the batch
  ;; that accepts it writes its journal. A refused verdict stores nothing;
  ;; a source longer than one extent waits for the source manifest (owed),
  ;; and a full arena or a failed write refuses the article by word.
  (:store :on-refusal ((:stop :machine-phase))
   (:cond ((not (equal row-word 0)) (:next :sealed) (:charge :steps *fn2-work-transition* :runnable t))
          ((or (equal row-hashed 0) (< *fn2-commit-extent-bytes* row-hashed))
           (:set (word *fn2-upload-word-unaffordable*)) (:next :sealed)
           (:charge :steps *fn2-work-transition* :runnable t))
          (t (:do (rcode e ep al) (fn2-upload-payload-reserve)
              :accept ()
              :case (((:ok) (:set (pext e) (pepoch ep) (palloc al) (pdone 0) (sready 0))
                      (:next :store-write) (:charge :steps *fn2-work-transition* :runnable t))
                     ((:no-space) (:set (word *fn2-upload-word-unaffordable*)) (:next :sealed)
                      (:charge :steps *fn2-work-transition* :runnable t)))))))
  (:store-write :on-refusal ((:stop :machine-phase))
   (:if (not (and (natp budget) (< 0 budget))) ((:yield))
        ((:do (wslot wgen woff wlen) (fn2-upload-store-span row-c0-slot row-c0-gen row-c1-slot row-c1-gen
                                                           row-pdone row-hashed))
         (:issue (fn2-issue-write (+ (* *fn2-commit-extent-bytes* row-pext) row-pdone) wslot wgen woff wlen 0
                                  :principal row-principal-slot)
          :ok ((:set (sready 0)) (:next :store-wrote)
               (:charge :bytes 4096 :steps *fn2-work-small* :descriptors 1))))))
  (:store-wrote :on-refusal ((:stop :machine-phase))
   (:cond ((equal row-sready 0) (:charge :steps *fn2-work-poll*))
          ((and (equal row-sevent *fn2-event-write-result*) (equal row-soutcome *fn2-outcome-done*)
                (< 0 row-scount) (<= (+ row-pdone row-scount) row-hashed))
           (:let done2 (+ row-pdone row-scount))
           (:set (pdone done2) (sready 0))
           (:next (:if (< done2 row-hashed) :store-write :store-fence))
           (:charge :steps *fn2-work-transition* :runnable t))
          ;; nothing durable is claimed for this source: the article is refused
          (t (:set (word *fn2-upload-word-not-stored*) (sready 0)) (:next :sealed)
             (:charge :steps *fn2-work-transition* :runnable t))))
  (:store-fence :on-refusal ((:stop :machine-phase))
   (:if (not (and (natp budget) (< 0 budget))) ((:yield))
        ((:issue (fn2-issue-fence :principal row-principal-slot)
          :ok ((:set (sready 0)) (:next :store-fenced)
               (:charge :steps *fn2-work-small* :descriptors 1))))))
  (:store-fenced :on-refusal ((:stop :machine-phase))
   (:cond ((equal row-sready 0) (:charge :steps *fn2-work-poll*))
          ((and (equal row-sevent *fn2-event-fence-result*) (equal row-soutcome *fn2-outcome-done*))
           (:set (sready 0)) (:next :sealed) (:charge :steps *fn2-work-transition* :runnable t))
          (t (:set (word *fn2-upload-word-not-stored*) (sready 0)) (:next :sealed)
             (:charge :steps *fn2-work-transition* :runnable t))))
  ;; :sealed: wait for the transaction's outcome (relaying any settlement wake
  ;; to the transaction while it still names this upload), then drain.
  (:sealed
   (:if (:live child-txn)
        ((:do () (fn2-upload-wake row-txn)) (:charge :steps *fn2-work-transition*))
        ((:next :draining) (:charge :steps *fn2-work-transition* :runnable t))))
  ;; :aborting: the connection left. A transaction that still names this row
  ;; holds its octets: wake it (it finishes without a word) and wait for it to
  ;; let go; then drain.
  (:aborting
   (:if (:live child-txn)
        ((:do () (fn2-upload-wake row-txn)) (:charge :steps *fn2-work-transition*))
        ((:next :draining) (:charge :steps *fn2-work-transition* :runnable t))))
  ;; :draining settles the payload extent, then releases the second chunk,
  ;; then the first, then the row.
  (:draining :on-refusal ((:stop :pool-release :steps *fn2-work-state*))
   (:do (pcode) (fn2-upload-payload-settle row-pext row-pepoch row-palloc) :accept (:ok))
   (:do (c1code) (fn2-core-release row-c1-slot row-c1-gen)
        :effects ((:release (:chunk-window)))
        :accept (:ok :retired) :why "a retired range is a completed release (the pool retires the slot)")
   (:do (c0code) (fn2-upload-release-c0 row-c0-slot row-c0-gen)
        :accept (:ok :retired) :why "a retired range is a completed release (the pool retires the slot)")
   (:let next (fn2-machine-free-head *fn2-upload-admission-ordinal*))
   (:let retire (>= row-generation (fn2-machine-gen-limit)))
   (:set (generation (if retire row-generation (+ 1 row-generation)))
         (c0-slot *fn2-none*) (c0-gen 0) (c1-slot *fn2-none*) (c1-gen 0) (pext *fn2-none*)
         (conn *fn2-none*) (conn-gen 0) (filled 0) (hashed 0) (txn *fn2-none*)
         (next-free next) (wait-reason *fn2-wait-none*))
   (:next (:if retire :retired :free))
   (:do () (fn2-machine-reclaim-fn2-upload id retire))
   (:charge :steps *fn2-work-release*))
  (:retired (:idle)))
 :observes
 ((:write-result (:set (sevent event) (soutcome outcome) (scount count) (sready 1)) (:wake))
  (:fence-result (:set (sevent event) (soutcome outcome) (scount count) (sready 1)) (:wake))
  (:borrow-released (:wake))))

(defmachine-arms fn2-upload)
(defmachine-run fn2-upload)
