;; The connection machine fn2-conn (layer D, quest D3; ROUND2 section B.2
;; row 1, its connection half: the listener is A's fn2-listener). The design,
;; with every arm's contract, is docs/d-machines-nntp.md section 4.2.
;; Declared through defmachine with every arm in the checked arm language
;; (none :unchecked); the decision table is conn-answer.lisp; the grammar is
;; nntp-grammar.lisp. Schema and partition registration live in
;; books/conn-kind.lisp; continuations are materialized by
;; assembly-callbacks-d-conn.lisp.
(in-package "ACL2")
(include-book "conn-kind")
(include-book "upload-kind")
(fn2-book-layer :d)

;; Declared costs of the connection's outside calls (section 4.2). Each is a
;; thin stobj-let wrapper over a pool-level function; none builds a list.
(defcost fn2-conn-frame :bytes *fn2-conn-frame-bytes* :tables (fn2-core-pool)
  :doc "Frame RX from the row's (start pos overflow): the grammar's framer under the frame quantum.")
(defcost fn2-conn-run-answer :bytes *fn2-conn-answer-bytes*
  :answers (:ok :bounds) :faults (:bounds) :tables (fn2-core-pool)
  :doc "Parse one framed line and answer it into TX (conn-answer.lisp); reads the clock mailbox.")
(defcost fn2-conn-run-overflow :bytes 512
  :answers (:ok :bounds) :faults (:bounds) :tables (fn2-core-pool)
  :doc "Render the overflow refusal into TX.")
(defcost fn2-conn-run-greeting :bytes 512
  :answers (:ok :bounds) :faults (:bounds) :tables (fn2-core-pool)
  :doc "Render the greeting, or the capacity 400, into TX.")
(defcost fn2-conn-fill :doc "A held pool slot's fill.")
(defcost fn2-conn-reading-p :doc "Whether the profile serves reading: the cursor partition has rows.")
(defcost fn2-conn-cursor-go :tables (fn2-cursor-table) :doc "Give the query cursor its move (TX is empty).")
(defcost fn2-conn-cursor-cancel :tables (fn2-cursor-table) :doc "Cancel a waiting query cursor: the connection drains.")
(defcost fn2-conn-posting-p :doc "Whether posting is served (the input configuration; section 14.5).")
(defcost fn2-conn-run-block-open :bytes 512
  :answers (:ok :bounds) :faults (:bounds) :tables (fn2-core-pool)
  :doc "Render a block's opening reply (340) into TX.")
(defcost fn2-conn-run-outcome :bytes 512
  :answers (:ok :bounds) :faults (:bounds) :tables (fn2-core-pool)
  :doc "Render a block's outcome reply into TX.")
(defcost fn2-conn-cap :doc "A held pool slot's capacity.")
(defcost fn2-conn-feed-run :bytes *fn2-conn-feed-cost*
  :answers (:terminator :need-more :budget :bounds :fault)
  :faults (:bounds :fault)
  :tables (fn2-core-pool)
  :doc "Feed RX into the upload's chunk (upload-feed.lisp).")
(defcost fn2-conn-wake :tables (fn2-core-machines) :doc "Wake the upload or cursor this connection serves.")

(defmachine-arms fn2-conn :declare
 :subarms
 ((input
   ;; Need-more: every filled octet is examined. All consumed: reset RX. Full
   ;; with a retained partial line: compact (next run). Else Receive at fill.
   (:let ((nfill (fn2-conn-fill row-rx-slot)) (cap (fn2-conn-cap row-rx-slot)))
     (:cond ((and (equal row-start nfill) (< 0 nfill))
             (:do (code) (fn2-core-reset row-rx-slot row-rx-gen)
                  :case (((:ok) (:set (start 0) (pos 0))
                          (:charge :bytes *fn2-conn-frame-bytes* :steps *fn2-work-mailbox* :runnable t)))))
            ((and (<= cap nfill) (< 0 row-start))
             (:set (compacting 1) (cursor 0))
             (:charge :bytes *fn2-conn-frame-bytes* :steps *fn2-work-mailbox* :runnable t))
            ((<= cap nfill)
             ;; A slot smaller than the line cap is full with one unfinished line:
             ;; refuse it as overlong and close (a profile check keeps served
             ;; slots at least *fn2-conn-range-min*, so this is a small-profile edge).
             (:do (code) (fn2-conn-run-overflow row-mask row-tx-slot row-tx-gen)
                  :case (((:ok) (:set (tx-off 0) (after :closing)) (:next :reply)
                          (:charge :bytes *fn2-conn-frame-bytes* :steps *fn2-work-mailbox* :runnable t)))))
            (t (:let ((len (min *fn2-conn-receive-bytes* (- cap nfill))))
                 (:issue (fn2-issue-receive row-cap-index row-cap-nonce row-rx-slot row-rx-gen len
                                            :principal row-principal-slot)
                         :ok ((:wait :completion :bytes (+ *fn2-conn-frame-bytes* len)))))))))
  (block-input
   ;; RX exhausted during a block: reset it when every octet was fed, else
   ;; Receive (the feed consumes every octet it frames, so nothing is retained).
   (:let ((nfill (fn2-conn-fill row-rx-slot)) (cap (fn2-conn-cap row-rx-slot)))
     (:cond ((and (equal row-start nfill) (< 0 nfill))
             (:do (code) (fn2-core-reset row-rx-slot row-rx-gen)
                  :case (((:ok) (:set (start 0) (pos 0)) (:charge :steps *fn2-work-mailbox* :runnable t)))))
            ((<= cap nfill) (:stop :machine-phase))
            (t (:let ((len (min *fn2-conn-receive-bytes* (- cap nfill))))
                 (:issue (fn2-issue-receive row-cap-index row-cap-nonce row-rx-slot row-rx-gen len
                                            :principal row-principal-slot)
                         :ok ((:wait :completion :bytes len))))))))
  (frame
   ;; Frame from the row's continuation; at a line, answer it and move to :reply.
   (:do (status s p o) (fn2-conn-frame row-rx-slot row-rx-gen row-start row-pos row-overflow)
        :case (((:line)
                (:do (ccode) (fn2-account-charge-core row-principal-slot *fn2-account-charge-requests* 1))
                (:do (code after next rule)
                     (fn2-conn-run-answer s p row-mask row-auth-pending row-posting (fn2-conn-reading-p)
                                          row-rx-slot row-rx-gen row-tx-slot row-tx-gen)
                     :accept ())
                (:cond ((not (and (eq code :ok) (eq ccode :ok))) (:stop :machine-phase))
                       ;; TAKETHIS refused before an upload exists (:discard, or posting off):
                       ;; TX[0, fill) holds the token; drain the immediate block and answer 439.
                       ((and (equal after *fn2-conn-after-article-input*) (equal rule *fn2-conn-rule-none*))
                        (:set (start p) (pos p) (overflow 0) (auth-pending next) (rule :takethis)
                              (line-e (fn2-conn-fill row-tx-slot)) (upload *fn2-none*) (upload-gen 0)
                              (feed-mode 0) (feed-discard 0) (fed 0) (word *fn2-upload-word-refused*)
                              (outcome-ready 0) (request row-ordinal) (ordinal (+ 1 row-ordinal)))
                        (:next :article-input)
                        (:charge :bytes *fn2-conn-run-bytes* :steps *fn2-work-transition* :runnable t))
                       ;; POST/IHAVE/TAKETHIS where posting is served: TX[0, fill) holds any
                       ;; transit Message-ID; the next run takes an upload (section 14.2)
                       ((equal after *fn2-conn-after-article-input*)
                        (:set (start p) (pos p) (overflow 0) (auth-pending next) (rule rule)
                              (line-e (fn2-conn-fill row-tx-slot))
                              (request row-ordinal) (ordinal (+ 1 row-ordinal)))
                        (:charge :bytes *fn2-conn-run-bytes* :steps *fn2-work-transition* :runnable t))
                       ;; a reader command: nothing rendered; the next run takes a
                       ;; query cursor for the line [s, p) (section 15.3)
                       ((equal after *fn2-conn-after-query*)
                        (:set (start p) (pos p) (overflow 0) (auth-pending next) (line-s s) (line-e p)
                              (request row-ordinal) (ordinal (+ 1 row-ordinal)))
                        (:next :query)
                        (:charge :bytes *fn2-conn-run-bytes* :steps *fn2-work-transition* :runnable t))
                       (t (:set (start p) (pos p) (overflow 0) (tx-off 0) (after after)
                                (auth-pending next) (ordinal (+ 1 row-ordinal)))
                          (:next :reply)
                          (:charge :bytes *fn2-conn-run-bytes* :steps *fn2-work-transition* :runnable t))))
               ((:overflow :long-line)
                (:do (ccode) (fn2-account-charge-core row-principal-slot *fn2-account-charge-requests* 1))
                (:do (code) (fn2-conn-run-overflow row-mask row-tx-slot row-tx-gen) :accept ())
                (:if (not (and (eq code :ok) (eq ccode :ok)))
                     ((:stop :machine-phase))
                     ((:set (start s) (pos p) (overflow o) (tx-off 0) (after :closing))
                      (:next :reply)
                      (:charge :bytes *fn2-conn-run-bytes* :steps *fn2-work-transition* :runnable t))))
               ((:budget)
                (:set (start s) (pos p) (overflow o))
                (:charge :bytes *fn2-conn-frame-bytes* :steps *fn2-work-transition* :runnable t))
               ((:need-more)
                (:set (start s) (pos p) (overflow o))
                (:goto input))
               (:otherwise (:stop :machine-phase))))))
 :arms
 ((:free (:idle))
  ;; :greeting renders the greeting (or the capacity 400) and moves to :reply.
  (:greeting
   (:let ((ref row-account-ref)
          (refused (if (and (not (equal row-account-ref *fn2-none*)) (equal row-refused 0)) 0 1)))
     (:do (ucode) (fn2-account-unbook-ref (if (equal refused 1) ref *fn2-none*))
          :case (((:ok)
                  (:let ((posting (fn2-conn-posting-p)))
                    (:do (code after) (fn2-conn-run-greeting refused posting row-mask row-tx-slot row-tx-gen)
                         :case (((:ok)
                                 (:set (tx-off 0) (after after) (refused refused) (posting posting)
                                       (account-ref (if (equal refused 1) *fn2-none* ref))
                                       (mask (logior (if (equal row-peer-family 0) 0 *fn2-nntp-state-peer*)
                                                     (logior *fn2-nntp-state-reader* *fn2-nntp-state-anonymous*))))
                                 (:next :reply)
                                 (:charge :bytes 512 :steps *fn2-work-transition* :runnable t))))))))))
  (:command
   (:cond ((not (equal row-pending 0)) (:charge :steps *fn2-work-empty*))
          ;; A POST, IHAVE, or TAKETHIS line awaits an upload row and its
          ;; window (A-S7). POST/IHAVE render 340/335 or park on the upload
          ;; FIFO; TAKETHIS has an immediate block and drains without a row
          ;; when none is free (section 14.2).
          ((not (equal row-rule *fn2-conn-rule-none*))
           (:do (tcode u ugen)
                (fn2-machine-take-fn2-upload *fn2-none* id row-generation row-request
                                             (if (equal row-rule *fn2-conn-rule-ihave*)
                                                 *fn2-upload-rule-ihave*
                                               (if (equal row-rule *fn2-conn-rule-takethis*)
                                                   *fn2-upload-rule-takethis*
                                                 *fn2-upload-rule-post*))
                                             row-principal-slot)
                :case (((:ok)
                        (:if (equal row-rule *fn2-conn-rule-takethis*)
                             ((:set (upload u) (upload-gen ugen) (feed-mode 0) (feed-discard 0)
                                    (fed 0) (word 0) (outcome-ready 0))
                              (:next :article-input)
                              (:charge :steps *fn2-work-transition* :runnable t))
                             ((:do (code) (fn2-conn-run-block-open row-rule row-mask row-tx-slot row-tx-gen)
                                   :case (((:ok)
                                           (:set (tx-off row-line-e) (after :article-input) (upload u) (upload-gen ugen)
                                                 (feed-mode 0) (feed-discard 0) (fed 0) (word 0) (outcome-ready 0))
                                           (:next :reply)
                                           (:charge :bytes 512 :steps *fn2-work-transition* :runnable t)))))))
                       (:otherwise
                        (:if (equal row-rule *fn2-conn-rule-takethis*)
                             ((:set (upload *fn2-none*) (upload-gen 0) (feed-mode 0) (feed-discard 0)
                                    (fed 0) (word *fn2-upload-word-unaffordable*) (outcome-ready 0))
                              (:next :article-input)
                              (:charge :steps *fn2-work-transition* :runnable t))
                             ((:park :taken fn2-upload :steps *fn2-work-transition*)))))))
          ;; Move a retained partial line to the front of RX.
          ((equal row-compacting 1)
           (:do (code cursor)
                (fn2-core-drop-prefix row-rx-slot row-rx-gen row-start row-cursor *fn2-conn-compact-bytes*)
                :case (((:more) (:set (cursor cursor))
                        (:charge :bytes *fn2-conn-compact-bytes* :steps *fn2-work-transition* :runnable t))
                       ((:ok) (:set (compacting 0) (cursor 0) (start 0) (pos cursor))
                        (:charge :bytes *fn2-conn-compact-bytes* :steps *fn2-work-transition* :runnable t)))))
          (t (:goto frame))))
  ;; :article-input: feed the block; once its outcome is posted, render it.
  (:article-input
   (:cond ((not (equal row-pending 0)) (:charge :steps *fn2-work-empty*))
          ((equal row-outcome-ready 1)
           (:do (code after) (fn2-conn-run-outcome row-rule row-word row-line-e row-mask row-tx-slot row-tx-gen)
                :case (((:ok)
                        (:set (tx-off row-line-e) (line-e 0) (after after) (upload *fn2-none*) (upload-gen 0)
                              (rule :none) (word 0) (outcome-ready 0) (feed-mode 0) (feed-discard 0) (fed 0))
                        (:next :reply)
                        (:charge :bytes 512 :steps *fn2-work-transition* :runnable t)))))
          ((equal row-feed-mode *fn2-conn-feed-done*) (:charge :steps *fn2-work-empty*))
          (t (:let ((u row-upload) (rfed row-fed))
               (:do (status start mode why copied)
                    (fn2-conn-feed-run row-start row-feed-mode row-feed-discard rfed row-rx-slot row-rx-gen
                                       u row-upload-gen)
                    :accept ())
               (:let ((fed (+ rfed (nfix copied))))
                 (:do () (fn2-conn-wake u))
                 (:if (not (and (unsigned-byte-p 32 start) (unsigned-byte-p 8 mode) (unsigned-byte-p 8 why)
                                (unsigned-byte-p 60 fed)))
                      ((:stop :machine-phase))
                      ((:case status
                         ((:terminator)
                          (:set (start start) (pos start) (feed-mode *fn2-conn-feed-done*)
                                (feed-discard why) (fed fed)
                                (word (if (and (equal u *fn2-none*) (equal why 1)) *fn2-upload-word-framing* row-word))
                                (outcome-ready (if (equal u *fn2-none*) 1 row-outcome-ready)))
                          (:charge :bytes *fn2-conn-feed-cost* :steps *fn2-work-transition*
                                   :runnable (equal u *fn2-none*)))
                         ((:need-more)
                          (:set (start start) (pos start) (feed-mode mode) (feed-discard why) (fed fed))
                          (:goto block-input))
                         ((:budget)
                          (:set (start start) (pos start) (feed-mode mode) (feed-discard why) (fed fed))
                          (:charge :bytes *fn2-conn-feed-cost* :steps *fn2-work-transition* :runnable t))
                         (:otherwise (:stop :machine-phase))))))))))
  ;; :reply sends [tx-off, fill) of TX by loan; once sent and released, TX is
  ;; reset and the row moves to its AFTER phase.
  (:reply
   (:cond ((not (equal row-pending 0)) (:charge :steps *fn2-work-empty*))
          ((not (equal row-borrows 0)) (:charge :steps *fn2-work-poll*))
          (t (:let ((off row-tx-off) (after row-after) (nfill (fn2-conn-fill row-tx-slot)))
               (:if (< off nfill)
                    ((:let ((len (min *fn2-conn-send-bytes* (- nfill off))))
                       (:issue (fn2-issue-send row-cap-index row-cap-nonce row-tx-slot row-tx-gen off len 1
                                               :principal row-principal-slot)
                               :ok ((:set (borrows 1)) (:wait :completion :bytes len)))))
                    ((:if (equal after *fn2-conn-after-query*)
                          ((:do (code)
                                (fn2-core-truncate row-tx-slot row-tx-gen
                                                   (if (:live child-cursor) (:read child-cursor roff) 0))
                                :case (((:ok) (:set (tx-off 0)) (:next :query)
                                        (:charge :steps *fn2-work-mailbox* :runnable t)))))
                          ((:do (code)
                                (fn2-core-truncate row-tx-slot row-tx-gen
                                                   (if (equal after *fn2-conn-after-article-input*) row-line-e 0))
                                :case (((:ok) (:set (tx-off 0))
                                        (:cond ((equal after *fn2-conn-after-closing*) (:next :closing))
                                               ((equal after *fn2-conn-after-article-input*) (:next :article-input))
                                               (t (:next :command)))
                                        (:charge :steps *fn2-work-mailbox* :runnable t))))))))))))
  (:upgrading (:stop :machine-phase))
  (:closing
   (:if (not (equal row-pending 0))
        ((:charge :steps *fn2-work-empty*))
        ((:issue (fn2-issue-close row-cap-index row-cap-nonce :principal row-principal-slot)
                 :ok ((:wait :completion :bytes 0))))))
  ;; :draining releases TX, then RX, then the row (the connection partition's
  ;; reclaim), once nothing is pending or lent.
  (:draining
   (:cond ((not (equal row-pending 0)) (:charge :steps *fn2-work-empty*))
          ((not (equal row-borrows 0)) (:charge :steps *fn2-work-poll*))
          (t (:let ((qry row-query) (qgen row-query-gen) (upl row-upload))
               (:do (tcode) (fn2-core-release row-tx-slot row-tx-gen)
                    :effects ((:release (:tx-range))) :accept ())
               (:do (rcode) (fn2-core-release row-rx-slot row-rx-gen)
                    :effects ((:release (:rx-range))) :accept ())
               (:do (acode) (fn2-account-unbook-ref row-account-ref) :accept ())
               (:do () (fn2-conn-cursor-cancel qry qgen))
               (:do () (fn2-conn-wake (if (equal upl *fn2-none*) qry upl)))
               (:cond ((not (and (or (eq tcode :ok) (eq tcode :retired))
                                 (or (eq rcode :ok) (eq rcode :retired))))
                       (:stop :pool-release :steps *fn2-work-state*))
                      ((not (eq acode :ok)) (:stop :account :steps *fn2-work-state*))
                      (t (:let ((retire (>= row-generation (fn2-machine-gen-limit)))
                                (next (fn2-machine-free-head *fn2-conn-admission-ordinal*)))
                           (:set (generation (if retire row-generation (+ 1 row-generation)))
                                 (rx-slot *fn2-none*) (rx-gen 0) (tx-slot *fn2-none*) (tx-gen 0)
                                 (cap-index 0) (cap-nonce 0) (start 0) (pos 0) (overflow 0) (compacting 0)
                                 (cursor 0) (tx-off 0) (ordinal 0) (auth-pending :none) (refused 0)
                                 (next-free next) (wait-reason *fn2-wait-none*) (account-ref *fn2-none*)
                                 (upload *fn2-none*) (query *fn2-none*) (query-gen 0))
                           (:do () (fn2-machine-reclaim-fn2-conn id retire))
                           (:if retire ((:next :retired)) ((:next :free)))
                           (:charge :steps *fn2-work-release*))))))))
  (:retired (:idle))
  ;; :query (section 15.3).
  (:query
   (:if (equal row-query *fn2-none*)
        ((:do (tcode x xgen)
              (fn2-machine-take-fn2-cursor *fn2-none* id row-generation *fn2-conn-kind* row-mask
                                           row-rx-slot row-rx-gen row-line-s row-line-e
                                           row-tx-slot row-tx-gen row-group row-current row-pin row-posting)
              :case (((:ok) (:set (query x) (query-gen xgen)) (:charge :steps *fn2-work-transition*))
                     (:otherwise (:park :taken fn2-cursor :steps *fn2-work-transition*)))))
        ((:cond ((not (:live child-cursor)) (:stop :machine-phase))
                ((equal (:read child-cursor turn) 1) (:charge :steps *fn2-work-transition*))
                ((< (:read child-cursor roff) (fn2-conn-fill row-tx-slot))
                 (:set (tx-off (:read child-cursor roff)) (after :query)) (:next :reply)
                 (:charge :steps *fn2-work-transition* :runnable t))
                ((equal (:read child-cursor done) 1)
                 (:do (rcode)
                      (fn2-core-truncate row-tx-slot row-tx-gen
                                         (if (equal (:read child-cursor update) 3) (:read child-cursor roff) 0))
                      :case (((:ok)
                              (:let ((upd (:read child-cursor update)) (g (:read child-cursor sel))
                                     (c (:read child-cursor ncurrent)) (v (:read child-cursor spin))
                                     (x row-query) (xgen row-query-gen))
                                (:do () (fn2-conn-cursor-go x xgen))
                                (:do () (fn2-conn-wake x))
                                (:let ((sel (equal upd 2)) (ihv (equal upd 3)))
                                  (:set (query *fn2-none*) (query-gen 0)
                                        (group (if sel g row-group))
                                        (current (if (or sel (equal upd 1)) c row-current))
                                        (pin (if sel v row-pin))
                                        (rule (if ihv :ihave row-rule))
                                        (line-e (if ihv c row-line-e)))
                                  (:next :command)
                                  (:charge :steps *fn2-work-transition* :runnable t)))))))
                (t (:do () (fn2-conn-cursor-go row-query row-query-gen))
                   (:do () (fn2-conn-wake row-query))
                   (:charge :steps *fn2-work-transition*)))))))
 :observes
 ((:receive-result :from (:command :article-input)
   (:if (and (or (equal outcome *fn2-outcome-done*) (equal outcome *fn2-outcome-short*))
             (natp count) (< 0 count))
        ((:do (code) (fn2-account-charge-core row-principal-slot *fn2-account-charge-rx* count)
              :case (((:ok) (:wake)))))
        ((:next :closing) (:wake))))
  (:send-result :from (:reply)
   (:if (not (eq (fn2-machine-pool-borrows-read-code row-tx-slot) :ok))
        ((:stop :machine-observation))
        ((:let ((borrows (fn2-machine-pool-borrows row-tx-slot)))
           (:if (and (or (equal outcome *fn2-outcome-done*) (equal outcome *fn2-outcome-short*))
                     (natp count))
                ((:do (code) (fn2-account-charge-core row-principal-slot *fn2-account-charge-tx* count)
                      :case (((:ok) (:set (borrows borrows) (tx-off (+ row-tx-off count))) (:wake)))))
                ((:set (borrows borrows)) (:next :closing) (:wake)))))))
  (:borrow-released
   (:if (not (eq (fn2-machine-pool-borrows-read-code row-tx-slot) :ok))
        ((:stop :machine-observation))
        ((:set (borrows (fn2-machine-pool-borrows row-tx-slot))) (:wake))))
  (:close-result :from (:closing)
   (:next :draining) (:wake))))

;; ------------------------------------------------------------------------
;; The operations, materialized after the core instance
;; (assembly-callbacks-d.lisp). The row's owner triple for every pool access
;; is (*fn2-conn-kind* oslot ogen).
(defmacro fn2-conn-op-events ()
 '(progn
(defun fn2-conn-frame (slot gen start pos overflow oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (status s p o)
    (fn2-gram-frame *fn2-conn-frame-bytes* (nfix start) (max (nfix start) (nfix pos)) (if (equal overflow 1) 1 0)
                    *fn2-nntp-line-cap* slot gen *fn2-conn-kind* oslot ogen fn2-pool)
    (mv status s p o)))

;; A held slot's fill, and its capacity (0 for a slot outside the pool).
(defun fn2-conn-fill (slot fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (n) (if (and (natp slot) (< slot (fn2-pool-rows fn2-pool))) (nfix (fn2-pool-fill slot fn2-pool)) 0)
    (nfix n)))
(defun fn2-conn-cap (slot fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (n) (if (and (natp slot) (< slot (fn2-pool-rows fn2-pool))) (nfix (fn2-pool-cap slot fn2-pool)) 0)
    (nfix n)))

(defun fn2-conn-clock (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (seen flags real)
    (mv (equal (fn2-ops-clock-seen fn2-ops) 1) (fn2-ops-clock-flags fn2-ops) (fn2-ops-clock-real fn2-ops))
    (mv seen flags real)))

(defun fn2-conn-auth-keyword (code)
  (declare (xargs :guard t))
  (cond ((equal code *fn2-conn-auth-user*) :user) ((equal code *fn2-conn-auth-sasl*) :sasl)
        ((equal code *fn2-conn-auth-redeem*) :redeem) (t :none)))
(defun fn2-conn-auth-code (pending)
  (declare (xargs :guard t))
  (case pending (:user *fn2-conn-auth-user*) (:sasl *fn2-conn-auth-sasl*)
    (:redeem *fn2-conn-auth-redeem*) (otherwise *fn2-conn-auth-none*)))
(defun fn2-conn-after-code (after)
  (declare (xargs :guard t))
  (case after (:closing *fn2-conn-after-closing*)
    ((:article-input :ihave :takethis :discard) *fn2-conn-after-article-input*)
    (:query *fn2-conn-after-query*)
    (otherwise *fn2-conn-after-command*)))
(defun fn2-conn-rule-code (after)
  (declare (xargs :guard t))
  (case after (:article-input *fn2-conn-rule-post*)
    (:ihave *fn2-conn-rule-ihave*)
    (:takethis *fn2-conn-rule-takethis*)
    (otherwise *fn2-conn-rule-none*)))
(defun fn2-conn-upload-rule (rule)
  (declare (xargs :guard t))
  (cond ((equal rule *fn2-conn-rule-ihave*) *fn2-upload-rule-ihave*)
        ((equal rule *fn2-conn-rule-takethis*) *fn2-upload-rule-takethis*)
        (t *fn2-upload-rule-post*)))
(defun fn2-conn-rule-keyword (rule)
  (declare (xargs :guard t))
  (cond ((equal rule *fn2-conn-rule-ihave*) :ihave)
        ((equal rule *fn2-conn-rule-takethis*) :takethis)
        (t :post)))

;; One framed line [s, e) answered into TX: (mv code after pending rule fn2-core),
;; AFTER, PENDING and RULE as the row's enum codes.
(defun fn2-conn-run-answer (s e mask pending posting reading rslot rgen tslot tgen oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (mv-let (seen flags real) (fn2-conn-clock fn2-core)
    (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
      (code after next fn2-pool)
      (fn2-answer (nfix s) (nfix e) mask (fn2-conn-auth-keyword pending) (equal posting 1) reading seen flags real
                       rslot rgen tslot tgen *fn2-conn-kind* oslot ogen fn2-pool)
      (mv code (fn2-conn-after-code after) (fn2-conn-auth-code next) (fn2-conn-rule-code after) fn2-core))))
(fn2-core-preserves fn2-conn-run-answer (s e mask pending posting reading rslot rgen tslot tgen oslot ogen fn2-core) :position 4 :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))

(defun fn2-conn-run-greeting (refused posting mask tslot tgen oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (code after fn2-pool)
    (fn2-answer-greeting (equal refused 1) (equal posting 1) mask tslot tgen *fn2-conn-kind* oslot ogen fn2-pool)
    (mv code (fn2-conn-after-code after) fn2-core)))
(fn2-core-preserves fn2-conn-run-greeting (refused posting mask tslot tgen oslot ogen fn2-core) :position 2 :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))

(defun fn2-conn-run-overflow (mask tslot tgen oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (code fn2-pool)
    (fn2-answer-overflow mask tslot tgen *fn2-conn-kind* oslot ogen fn2-pool)
    (mv code fn2-core)))
(fn2-core-preserves fn2-conn-run-overflow (mask tslot tgen oslot ogen fn2-core) :position 1 :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))
(defun fn2-conn-posting-p (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-input-config (fn2-core-input-config fn2-core)))
    (p) (and (fn2-input-config-wfp fn2-input-config) (natp (fn2-input-config-rows fn2-input-config))
             (< 0 (fn2-input-config-rows fn2-input-config)) (equal (fn2-input-config-posting 0 fn2-input-config) 1))
    (if p 1 0)))
(defun fn2-upload-gen-of (u fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (eq (fn2-upload-snapshot-read-code u fn2-core) :ok) (fn2-machine-generation u fn2-core) 0))
(defthm fn2-conn-posting-p-bit
  (bitp (fn2-conn-posting-p fn2-core))
  :rule-classes ((:type-prescription :typed-term (fn2-conn-posting-p fn2-core))
                 (:rewrite :corollary (unsigned-byte-p 1 (fn2-conn-posting-p fn2-core)))))
(defthm fn2-upload-gen-of-u60
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
           (unsigned-byte-p 60 (fn2-upload-gen-of u fn2-core))))
(defun fn2-conn-run-block-open (rule mask tslot tgen oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (code fn2-pool)
    (fn2-answer-block-open (equal rule *fn2-conn-rule-ihave*) mask tslot tgen *fn2-conn-kind* oslot ogen fn2-pool)
    (mv code fn2-core)))
(fn2-core-preserves fn2-conn-run-block-open (rule mask tslot tgen oslot ogen fn2-core) :position 1 :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))
(defun fn2-conn-run-outcome (rule word mlen mask tslot tgen oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (code after fn2-pool)
    (fn2-answer-outcome (fn2-conn-rule-keyword rule) (fn2-upload-word-of (nfix word)) (nfix mlen)
                        mask tslot tgen *fn2-conn-kind* oslot ogen fn2-pool)
    (mv code (fn2-conn-after-code after) fn2-core)))
(fn2-core-preserves fn2-conn-run-outcome (rule word mlen mask tslot tgen oslot ogen fn2-core) :position 2 :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))
;; Feed [start, fill) of RX into the upload's current chunk (the first while
;; it has room), at most *fn2-conn-feed-bytes* octets and no further than one
;; octet past the article bound (so a too-large block is refused, never
;; buffered).
(defun fn2-conn-feed-pool (left start mode discard rslot rgen oslot ogen slot sgen u ugen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (status start2 mode2 discard2 copied fn2-pool)
    (fn2-upload-feed (max 1 (nfix left)) (nfix start) (nfix mode) discard rslot rgen *fn2-conn-kind* oslot ogen
                     slot sgen *fn2-upload-kind* u ugen fn2-pool)
    (mv status start2 mode2 discard2 copied fn2-core)))
(fn2-core-preserves fn2-conn-feed-pool (left start mode discard rslot rgen oslot ogen slot sgen u ugen fn2-core)
  :position 5 :rows nil :hints (("Goal" :in-theory (enable fn2-core-wfp))))
(in-theory (disable fn2-conn-feed-pool))
(defun fn2-conn-feed-run (start mode why fed rslot rgen u ugen oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (equal u *fn2-none*)
      (if (not (and (natp start) (natp mode) (natp fed) (natp why)))
          (mv :bounds 0 0 0 0 fn2-core)
        (b* ((discard (not (equal why 0)))
             ((mv status start2 mode2 discard2 copied fn2-core)
              (fn2-conn-feed-pool *fn2-conn-feed-bytes* start mode discard rslot rgen oslot ogen *fn2-none* 0 0 0 fn2-core))
             (why2 (cond (discard why) (discard2 1) (t 0))))
          (mv (if (eq status :full) :budget status) start2 mode2 why2 (nfix copied) fn2-core)))
    (b* (((unless (and (eq (fn2-upload-snapshot-read-code u fn2-core) :ok)
                       (equal (fn2-machine-generation u fn2-core) ugen)
                       (natp start) (natp mode) (natp fed) (natp why)))
          (mv :bounds 0 0 0 0 fn2-core))
         (c0 (fn2-upload-row-c0-slot u fn2-core)) (g0 (fn2-upload-row-c0-gen u fn2-core))
         (c1 (fn2-upload-row-c1-slot u fn2-core)) (g1 (fn2-upload-row-c1-gen u fn2-core))
         (cap0 (fn2-upload-chunk-cap c0 fn2-core)) (cap1 (fn2-upload-chunk-cap c1 fn2-core))
         (bound (fn2-upload-bound cap0 cap1 fn2-core))
         (in0 (< fed cap0))
         (discard (not (equal why 0)))
         (left (if discard *fn2-conn-feed-bytes* (min *fn2-conn-feed-bytes* (nfix (- (+ 1 bound) fed)))))
         ((mv status start2 mode2 discard2 copied fn2-core)
          (fn2-conn-feed-pool left start mode discard rslot rgen oslot ogen (if in0 c0 c1) (if in0 g0 g1) u ugen fn2-core))
         (fed2 (+ fed (nfix copied)))
         (too-large (and (not discard2) (or (< bound fed2) (and (eq status :full) (not in0)))))
         (why2 (cond (discard why) (too-large 2) (discard2 1) (t 0))))
      (mv (if (eq status :full) :budget status) start2 mode2 why2 (nfix copied) fn2-core))))
(fn2-core-preserves fn2-conn-feed-run (start mode why fed rslot rgen u ugen oslot ogen fn2-core) :position 5 :rows nil)
(defun fn2-conn-wake (u fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (and (unsigned-byte-p 32 u) (not (equal u *fn2-none*))) (fn2-machine-set-wake-id u fn2-core) fn2-core))
(fn2-core-preserves fn2-conn-wake (u fn2-core) :rows nil)

;; Reading is served when the cursor partition has rows (read rows, :reading).
(defun fn2-conn-reading-p (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (< 0 (nfix (fn2-machine-connection-count *fn2-cursor-admission-ordinal* fn2-core))))
;; The query cursor seen from its connection (section 15.3): X is live while
;; its generation is the one the take returned.
(defun fn2-conn-cursor-live-p (x xgen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (and (unsigned-byte-p 32 x) (not (equal x *fn2-none*))
       (eq (fn2-cursor-snapshot-read-code x fn2-core) :ok)
       (equal (fn2-machine-generation x fn2-core) xgen)))
(defun fn2-conn-cursor-go (x xgen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (fn2-conn-cursor-live-p x xgen fn2-core) (fn2-cursor-put-core x (turn 1)) fn2-core))
(fn2-core-preserves fn2-conn-cursor-go (x xgen fn2-core) :rows nil)
(defun fn2-conn-cursor-cancel (x xgen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (fn2-conn-cursor-live-p x xgen fn2-core) (fn2-cursor-put-core x (cancel 1) (turn 1)) fn2-core))
(fn2-core-preserves fn2-conn-cursor-cancel (x xgen fn2-core) :rows nil)

(in-theory (disable fn2-conn-posting-p fn2-upload-gen-of fn2-conn-run-block-open fn2-conn-run-outcome fn2-conn-feed-run
                    fn2-conn-wake fn2-conn-reading-p fn2-conn-cursor-live-p fn2-conn-cursor-go fn2-conn-cursor-cancel))
(in-theory (disable fn2-conn-frame fn2-conn-fill fn2-conn-cap fn2-conn-clock fn2-conn-run-answer
                    fn2-conn-run-greeting fn2-conn-run-overflow))
))

;; The connection's continuations (materialized in assembly-callbacks-d-conn.lisp).
(defmacro fn2-conn-events ()
 '(progn
(defmachine-arms fn2-conn)
(defmachine-run fn2-conn)
))
