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
                     ((:sealed) (:next :sealed)
                      (:charge :bytes *fn2-upload-run-bytes* :steps *fn2-work-transition*))
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
  ;; :draining releases the second chunk, then the first, then the row.
  (:draining :on-refusal ((:stop :pool-release :steps *fn2-work-state*))
   (:do (c1code) (fn2-core-release row-c1-slot row-c1-gen)
        :effects ((:release (:chunk-window)))
        :accept (:ok :retired) :why "a retired range is a completed release (the pool retires the slot)")
   (:do (c0code) (fn2-upload-release-c0 row-c0-slot row-c0-gen)
        :accept (:ok :retired) :why "a retired range is a completed release (the pool retires the slot)")
   (:let next (fn2-machine-free-head *fn2-upload-admission-ordinal*))
   (:let retire (>= row-generation (fn2-machine-gen-limit)))
   (:set (generation (if retire row-generation (+ 1 row-generation)))
         (c0-slot *fn2-none*) (c0-gen 0) (c1-slot *fn2-none*) (c1-gen 0)
         (conn *fn2-none*) (conn-gen 0) (filled 0) (hashed 0) (txn *fn2-none*)
         (next-free next) (wait-reason *fn2-wait-none*))
   (:next (:if retire :retired :free))
   (:do () (fn2-machine-reclaim-fn2-upload id retire))
   (:charge :steps *fn2-work-release*))
  (:retired (:idle)))
 :observes ())

(defmachine-arms fn2-upload)
(defmachine-run fn2-upload)
