; The connection kind's continuations (D3, books/conn.lisp), in their own leaf
; section book so arm-body edits do not invalidate assembly.cert or executor.cert.
(in-package "ACL2")
(include-book "assembly-callbacks-d")
(include-book "conn")
(local (defun fn2-dc-core-child-type-terms (children)
         (declare (xargs :verify-guards nil))
         (if (atom children) nil
           (cons `(,(fn2-columns-sym (cadar children) "P") (,(caar children) fn2-core))
                 (fn2-dc-core-child-type-terms (cdr children))))))
(make-event
 (value `(local (defthm fn2-dc-core-child-types-fc
                  (implies (fn2-corep fn2-core)
                           (and ,@(fn2-dc-core-child-type-terms *fn2-core-children*)))
                  :rule-classes :forward-chaining))))
(make-event
 (value `(local (in-theory (enable ,@(fn2-core-child-wfp-forward-runes *fn2-core-children*))))))
(local
 (make-event
  (let* ((old (cdr (assoc-eq 'fn2-tls-admit (table-alist 'fn2-machine-arm-bodies (w state)))))
         (arms
          '((:free (:idle)) (:held (:idle))
            (:draining
             (:if (equal 0 1)
                  ((:next :draining) (:charge :steps *fn2-work-empty*))
                  ((:let next (fn2-machine-free-head *fn2-tls-admit-admission-ordinal*))
                   (:let retire (>= row-generation (fn2-machine-gen-limit)))
                   (:set (generation (if retire row-generation (+ 1 row-generation)))
                         (conn *fn2-none*) (conn-gen 0) (next-free next) (wait-reason *fn2-wait-none*))
                   (:next (:if retire :retired :free))
                   (:do () (fn2-machine-reclaim-fn2-tls-admit id retire))
                   (:charge :steps *fn2-work-release*))))
            (:retired (:idle)))))
    (value `(table fn2-machine-arm-bodies 'fn2-tls-admit
                   ',(fn2-decl-set :arms arms old))))))
(fn2-tls-events)

(defconst *fn2-upload-word-framing* (fn2-upload-word-code :framing))
(defconst *fn2-upload-word-unaffordable* (fn2-upload-word-code :unaffordable))
(defconst *fn2-upload-word-refused* (fn2-upload-word-code :refused))

(defun fn2-conn-release-rx (slot gen okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (fn2-core-release slot gen okind oslot ogen fn2-core))
(fn2-core-preserves fn2-conn-release-rx (slot gen okind oslot ogen fn2-core) :position 1 :rows nil)
(in-theory (disable fn2-conn-release-rx))
(defcost fn2-conn-release-rx :answers t :tables (fn2-core-pool) :effects ((:release (:rx-range)))
  :doc "Release a draining connection's RX pool range.")

(defmachine-arms fn2-conn :declare
 :subarms
 ((tls-timeout
   ;; Cancel the saved descriptor, then let Close/drain wait for both real
   ;; terminal observations. A deadline alone never releases a live loan.
   (:if (equal row-pending 0)
        ((:next :closing) (:charge :steps *fn2-work-transition* :runnable t))
        ((:issue (fn2-issue-cancel row-tls-op row-tls-op-gen :principal row-principal-slot)
          :ok ((:next :closing) (:wait :completion :bytes 0))))))
  (upgrade-issue
   (:let nfill (fn2-conn-fill row-rx-slot))
   (:let retained (nfix (- nfill row-start)))
   (:cond ((equal row-upgrade-target *fn2-conn-upgrade-target-tls*)
           (:issue (fn2-issue-tls-start row-cap-index row-cap-nonce row-rx-slot row-rx-gen row-start retained
                                       :principal row-principal-slot)
            :bind (issued-slot issued-gen)
            :ok ((:set (tls-op issued-slot) (tls-op-gen issued-gen) (upgrade-stage *fn2-conn-upgrade-stage-running*) (borrows 1))
                 (:wait :completion :bytes 0))))
          ((equal row-upgrade-target *fn2-conn-upgrade-target-compress*)
           (:issue (fn2-issue-compress-start row-cap-index row-cap-nonce row-rx-slot row-rx-gen row-start retained
                                            :principal row-principal-slot)
            :bind (issued-slot issued-gen)
            :ok ((:set (tls-op issued-slot) (tls-op-gen issued-gen) (upgrade-stage *fn2-conn-upgrade-stage-running*) (borrows 1))
                 (:wait :completion :bytes 0))))
          (t (:stop :machine-phase))))
  (compress-upgrade
   (:cond ((equal row-upgrade-stage *fn2-conn-upgrade-stage-none*)
           (:do (code) (fn2-compress-render-handoff row-mask row-tx-slot row-tx-gen)
            :case ((:otherwise (:stop :machine-phase))))
           (:set (upgrade-stage *fn2-conn-upgrade-stage-admitted*) (tls-ok 0)
                 (tx-off 0) (after *fn2-conn-after-upgrading*))
           (:next :reply) (:charge :bytes 512 :steps *fn2-work-transition* :runnable t))
          ((equal row-upgrade-stage *fn2-conn-upgrade-stage-finished*)
           (:if (equal row-tls-ok 1)
                ((:do (code) (fn2-core-reset row-rx-slot row-rx-gen)
                  :case ((:otherwise (:stop :machine-phase))))
                 ; Authentication, principal, group, current and pin survive.
                 (:set (start 0) (pos 0) (overflow 0)
                       (mask (logior row-mask *fn2-nntp-state-compressed*))
                       (tls-op *fn2-none*) (tls-op-gen 0)
                       (upgrade-target *fn2-conn-upgrade-target-none*)
                       (upgrade-stage *fn2-conn-upgrade-stage-none*) (tls-ok 0))
                 (:next :command) (:charge :steps *fn2-work-transition* :runnable t))
                ((:next :closing) (:charge :steps *fn2-work-transition* :runnable t))))
          (t (:stop :machine-phase))))
  (input
   ;; Need-more: every filled octet is examined. All consumed: reset RX. Full
   ;; with a retained partial line: compact (next run). Else Receive at fill.
   (:let nfill (fn2-conn-fill row-rx-slot))
   (:let cap (fn2-conn-cap row-rx-slot))
   (:cond ((and (equal row-start nfill) (< 0 nfill))
           (:do (code) (fn2-core-reset row-rx-slot row-rx-gen)
                :case ((:otherwise (:stop :machine-phase))))
           (:set (start 0) (pos 0))
           (:charge :bytes *fn2-conn-frame-bytes* :steps *fn2-work-mailbox* :runnable t))
          ((and (<= cap nfill) (< 0 row-start))
           (:set (compacting 1) (cursor 0))
           (:charge :bytes *fn2-conn-frame-bytes* :steps *fn2-work-mailbox* :runnable t))
          ((<= cap nfill)
           ;; A slot smaller than the line cap is full with one unfinished line:
           ;; refuse it as overlong and close (a profile check keeps served
           ;; slots at least *fn2-conn-range-min*, so this is a small-profile edge).
           (:do (code) (fn2-conn-run-overflow row-mask row-tx-slot row-tx-gen)
                :case ((:otherwise (:stop :machine-phase))))
           (:set (tx-off 0) (after *fn2-conn-after-closing*))
           (:next :reply)
           (:charge :bytes *fn2-conn-frame-bytes* :steps *fn2-work-mailbox* :runnable t))
          (t (:let len (min *fn2-conn-receive-bytes* (nfix (- cap nfill))))
             (:issue (fn2-issue-receive row-cap-index row-cap-nonce row-rx-slot row-rx-gen len
                                        :principal row-principal-slot)
                     :ok ((:wait :completion :bytes (+ *fn2-conn-frame-bytes* len)))))))
  (block-input
   ;; RX exhausted during a block: reset it when every octet was fed, else
   ;; Receive (the feed consumes every octet it frames, so nothing is retained).
   (:let nfill (fn2-conn-fill row-rx-slot))
   (:let cap (fn2-conn-cap row-rx-slot))
   (:cond ((and (equal row-start nfill) (< 0 nfill))
           (:do (code) (fn2-core-reset row-rx-slot row-rx-gen)
                :case ((:otherwise (:stop :machine-phase))))
           (:set (start 0) (pos 0))
           (:charge :bytes *fn2-conn-feed-cost* :steps *fn2-work-mailbox* :runnable t))
          ((<= cap nfill) (:stop :machine-phase))
          (t (:let len (min *fn2-conn-receive-bytes* (nfix (- cap nfill))))
             (:issue (fn2-issue-receive row-cap-index row-cap-nonce row-rx-slot row-rx-gen len
                                        :principal row-principal-slot)
                     :ok ((:wait :completion :bytes (+ *fn2-conn-feed-cost* len)))))))
  (frame
   ;; Frame from the row's continuation; at a line, answer it and move to :reply.
   (:do (status s p o) (fn2-conn-frame row-rx-slot row-rx-gen row-start row-pos row-overflow))
   (:case status
     ((:line)
      (:do (ccode) (fn2-account-charge-core row-principal-slot *fn2-account-charge-requests* 1))
      (:do (code after next rule)
           (fn2-conn-run-answer s p row-mask row-auth-pending row-posting (fn2-conn-reading-p)
                                row-rx-slot row-rx-gen row-tx-slot row-tx-gen)
           :case ((:otherwise (:stop :machine-phase))))
      (:cond ((not (eq ccode :ok)) (:stop :machine-phase))
             ;; TAKETHIS refused before an upload exists (:discard, or posting off):
             ;; TX[0, fill) holds the token; drain the immediate block and answer 439.
             ((and (equal after *fn2-conn-after-article-input*) (equal rule *fn2-conn-rule-none*))
              (:set (start p) (pos p) (overflow 0) (auth-pending next) (rule *fn2-conn-rule-takethis*)
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
             ((or (equal after *fn2-conn-after-upgrading*)
                  (equal after *fn2-conn-after-compress-upgrading*))
              (:set (start p) (pos p) (overflow 0) (auth-pending next)
                    (upgrade-target (if (equal after *fn2-conn-after-compress-upgrading*)
                                        *fn2-conn-upgrade-target-compress* *fn2-conn-upgrade-target-tls*))
                    (upgrade-stage *fn2-conn-upgrade-stage-none*) (tls-ok 0))
              (:next :upgrading)
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
      (:do (code) (fn2-conn-run-overflow row-mask row-tx-slot row-tx-gen)
           :case ((:otherwise (:stop :machine-phase))))
      (:if (not (eq ccode :ok))
           ((:stop :machine-phase))
           ((:set (start s) (pos p) (overflow o) (tx-off 0) (after *fn2-conn-after-closing*))
            (:next :reply)
            (:charge :bytes *fn2-conn-run-bytes* :steps *fn2-work-transition* :runnable t))))
     ((:budget)
      (:set (start s) (pos p) (overflow o))
      (:charge :bytes *fn2-conn-frame-bytes* :steps *fn2-work-transition* :runnable t))
     ((:need-more)
      (:set (start s) (pos p) (overflow o))
      (:goto input))
     (:otherwise (:stop :machine-phase)))))
 :arms
 ((:free (:idle))
  ;; :greeting renders the greeting (or the capacity 400) and moves to :reply.
  (:greeting :on-refusal ((:stop :machine-phase))
   (:let ref row-account-ref)
   (:let refused (if (and (not (equal row-account-ref *fn2-none*)) (equal row-refused 0)) 0 1))
   (:do (ucode) (fn2-account-unbook-ref (if (equal refused 1) ref *fn2-none*)))
   (:let posting (fn2-conn-posting-p))
   (:let peering (fn2-conn-peering-p))
   (:do (code after) (fn2-conn-greet-op refused posting row-mask row-tx-slot row-tx-gen))
   (:set (tx-off 0) (after after) (refused refused) (posting posting)
         (account-ref (if (equal refused 1) *fn2-none* ref))
         (mask (logior (if (and (equal peering 1) (not (equal row-peer-family 0))) *fn2-nntp-state-peer* 0)
                       (logior *fn2-nntp-state-reader* *fn2-nntp-state-anonymous*
                               (logior (if (fn2-tls-enabled-p) *fn2-nntp-state-tls-available* 0)
                                       (if (fn2-compress-enabled-p) *fn2-nntp-state-compress-available* 0))))))
   (:next :reply)
   (:charge :bytes 512 :steps *fn2-work-transition* :runnable t))
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
                                             row-principal-slot 0)
                :case (((:ok)
                        (:if (equal row-rule *fn2-conn-rule-takethis*)
                             ((:set (upload u) (upload-gen ugen) (feed-mode 0) (feed-discard 0)
                                    (fed 0) (word 0) (outcome-ready 0))
                              (:next :article-input)
                              (:charge :steps *fn2-work-transition* :runnable t))
                             ((:do (code) (fn2-conn-run-block-open row-rule row-mask row-tx-slot row-tx-gen)
                                   :case ((:otherwise (:stop :machine-phase))))
                              (:set (tx-off row-line-e) (after *fn2-conn-after-article-input*) (upload u) (upload-gen ugen)
                                    (feed-mode 0) (feed-discard 0) (fed 0) (word 0) (outcome-ready 0))
                              (:next :reply)
                              (:charge :bytes 512 :steps *fn2-work-transition* :runnable t))))
                       ;; no fn2-upload row: unreachable in composition (posting,
                       ;; read before an article line gets here, needs upload windows)
                       ((:none) (:stop :machine-phase))
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
                        (:charge :bytes *fn2-conn-compact-bytes* :steps *fn2-work-transition* :runnable t))
                       (:otherwise (:stop :machine-phase)))))
          (t (:goto frame))))
  ;; :article-input: feed the block; once its outcome is posted, render it.
  (:article-input
   (:cond ((not (equal row-pending 0)) (:charge :steps *fn2-work-empty*))
          ((equal row-outcome-ready 1)
           (:do (code after) (fn2-conn-run-outcome row-rule row-word row-line-e row-mask row-tx-slot row-tx-gen)
                :case ((:otherwise (:stop :machine-phase))))
           (:set (tx-off row-line-e) (line-e 0) (after after) (upload *fn2-none*) (upload-gen 0)
                 (rule *fn2-conn-rule-none*) (word 0) (outcome-ready 0) (feed-mode 0) (feed-discard 0) (fed 0))
           (:next :reply)
           (:charge :bytes 512 :steps *fn2-work-transition* :runnable t))
          ((equal row-feed-mode *fn2-conn-feed-done*) (:charge :steps *fn2-work-empty*))
          (t (:let u row-upload)
             (:let rfed row-fed)
             (:do (status start mode why copied)
                  (fn2-conn-feed-run row-start row-feed-mode row-feed-discard rfed row-rx-slot row-rx-gen
                                     u row-upload-gen)
                  :accept (:terminator :need-more :budget)
                  :why "a feed step ends at the terminator, short of input, or at its quantum; :full is folded into :budget"
                  :case ((:otherwise (:stop :machine-phase))))
             (:let fed (+ rfed (nfix copied)))
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
                     (:otherwise (:stop :machine-phase))))))))
  ;; :reply sends [tx-off, fill) of TX by loan; once sent and released, TX is
  ;; reset and the row moves to its AFTER phase.
  (:reply
   (:cond ((and (equal row-after *fn2-conn-after-upgrading*)
                (equal row-upgrade-target *fn2-conn-upgrade-target-tls*) (fn2-tls-expired-p id)) (:goto tls-timeout))
          ((not (equal row-pending 0)) (:charge :steps *fn2-work-empty*))
          ((not (equal row-borrows 0)) (:charge :steps *fn2-work-poll*))
          (t (:let off row-tx-off)
             (:let after row-after)
             (:let nfill (fn2-conn-fill row-tx-slot))
             (:if (< off nfill)
                  ((:let len (min *fn2-conn-send-bytes* (nfix (- nfill off))))
                   (:issue (fn2-issue-send row-cap-index row-cap-nonce row-tx-slot row-tx-gen off len 1
                                           :principal row-principal-slot)
                           :bind (issued-slot issued-gen)
                           :ok ((:set (borrows 1) (tls-op issued-slot) (tls-op-gen issued-gen))
                                (:wait :completion :bytes len))))
                  ((:if (equal after *fn2-conn-after-query*)
                        ((:do (code)
                              (fn2-core-truncate row-tx-slot row-tx-gen
                                                 (if (:live child-cursor) (:read child-cursor roff) 0))
                              :case ((:otherwise (:stop :machine-phase))))
                         (:set (tx-off 0))
                         (:next :query)
                         (:charge :steps *fn2-work-mailbox* :runnable t))
                        ((:do (code)
                              (fn2-core-truncate row-tx-slot row-tx-gen
                                                 (if (equal after *fn2-conn-after-article-input*) row-line-e 0))
                              :case ((:otherwise (:stop :machine-phase))))
                         (:set (tx-off 0))
                         (:next (:if (equal after *fn2-conn-after-closing*) :closing
                                  (:if (equal after *fn2-conn-after-article-input*) :article-input
                                   (:if (or (equal after *fn2-conn-after-upgrading*)
                                            (equal after *fn2-conn-after-compress-upgrading*)) :upgrading :command))))
                         (:charge :steps *fn2-work-mailbox* :runnable t))))))))
  (:upgrading
   (:cond ((and (equal row-upgrade-target *fn2-conn-upgrade-target-tls*) (fn2-tls-expired-p id)) (:goto tls-timeout))
          ((or (not (equal row-pending 0)) (not (equal row-borrows 0))) (:charge :steps *fn2-work-empty*))
          ((equal row-upgrade-stage *fn2-conn-upgrade-stage-admitted*) (:goto upgrade-issue))
          ((equal row-upgrade-target *fn2-conn-upgrade-target-compress*) (:goto compress-upgrade))
          ((not (equal row-upgrade-target *fn2-conn-upgrade-target-tls*)) (:stop :machine-phase))
          ((equal row-upgrade-stage *fn2-conn-upgrade-stage-none*)
           (:do (tcode token token-gen) (fn2-machine-take-fn2-tls-admit *fn2-none* id row-generation)
            :accept ()
            :case (((:ok)
                    (:do (dcode deadline) (fn2-tls-arm-timer id (fn2-tls-timeout-ms))
                     :case ((:otherwise (:stop :machine-phase))))
                    (:do (rcode) (fn2-tls-render-handoff t row-mask row-tx-slot row-tx-gen)
                     :case ((:otherwise (:stop :machine-phase))))
                    (:set (tls-token token) (tls-token-gen token-gen) (upgrade-stage *fn2-conn-upgrade-stage-admitted*)
                          (tls-ok 0) (tx-off 0) (after *fn2-conn-after-upgrading*))
                    (:next :reply) (:charge :bytes 512 :steps *fn2-work-transition* :runnable t))
                   (:otherwise
                    (:do (rcode) (fn2-tls-render-handoff nil row-mask row-tx-slot row-tx-gen)
                     :case ((:otherwise (:stop :machine-phase))))
                    (:set (upgrade-target *fn2-conn-upgrade-target-none*)
                          (tx-off 0) (after *fn2-conn-after-command*))
                    (:next :reply) (:charge :bytes 512 :steps *fn2-work-transition* :runnable t)))))
          ((equal row-upgrade-stage *fn2-conn-upgrade-stage-finished*)
           (:if (equal row-tls-ok 1)
                ((:do (dcode) (fn2-tls-clear-timer id) :case ((:otherwise (:stop :machine-phase))))
                 (:do (rcode) (fn2-core-reset row-rx-slot row-rx-gen) :case ((:otherwise (:stop :machine-phase))))
                 (:do (tcode) (fn2-tls-release-token row-tls-token row-tls-token-gen id row-generation)
                  :case ((:otherwise (:stop :machine-phase))))
                 (:set (start 0) (pos 0) (overflow 0) (group 0) (current 0) (pin 0)
                       (auth-pending *fn2-conn-auth-none*)
                       (mask (logior *fn2-nntp-state-reader* *fn2-nntp-state-anonymous* *fn2-nntp-state-tls*
                                     (logand row-mask *fn2-nntp-state-compress-available*)))
                       (tls-token *fn2-none*) (tls-token-gen 0) (tls-op *fn2-none*) (tls-op-gen 0)
                       (upgrade-target *fn2-conn-upgrade-target-none*)
                       (upgrade-stage *fn2-conn-upgrade-stage-none*) (tls-ok 0))
                 (:next :command) (:charge :steps *fn2-work-transition* :runnable t))
                ((:next :closing) (:charge :steps *fn2-work-transition* :runnable t))))
          (t (:stop :machine-phase))))
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
          ;; Preserve both ranges and all cleanup state while a query holds
          ;; either one. Last-reference release wakes this exact live owner.
          ((or (fn2-core-query-heldp row-tx-slot row-tx-gen)
               (fn2-core-query-heldp row-rx-slot row-rx-gen))
           (:charge :steps *fn2-work-state*))
          (t (:if (equal row-upgrade-target *fn2-conn-upgrade-target-tls*)
                  ((:do (dcode) (fn2-tls-clear-timer id) :case ((:otherwise (:stop :machine-phase))))
                   (:do (tcode) (fn2-tls-release-token row-tls-token row-tls-token-gen id row-generation)
                    :case ((:otherwise (:stop :machine-phase)))))
                  ())
             (:let qry row-query)
             (:let qgen row-query-gen)
             (:let upl row-upload)
             (:do (tcode) (fn2-core-release row-tx-slot row-tx-gen)
                  :effects ((:release (:tx-range)))
                  :accept (:ok :retired) :why "a retired range is a completed release (the pool retires the slot)"
                  :case ((:otherwise (:stop :pool-release :steps *fn2-work-state*))))
             (:do (rcode) (fn2-conn-release-rx row-rx-slot row-rx-gen)
                  :accept (:ok :retired) :why "a retired range is a completed release (the pool retires the slot)"
                  :case ((:otherwise (:stop :pool-release :steps *fn2-work-state*))))
             (:do (acode) (fn2-account-unbook-ref row-account-ref)
                  :case ((:otherwise (:stop :account :steps *fn2-work-state*))))
             (:do () (fn2-conn-cursor-cancel qry qgen))
             (:do () (fn2-conn-wake (if (equal upl *fn2-none*) qry upl)))
             (:let next (fn2-machine-free-head *fn2-conn-admission-ordinal*))
             (:let retire (>= row-generation (fn2-machine-gen-limit)))
             (:set (generation (if retire row-generation (+ 1 row-generation)))
                   (rx-slot *fn2-none*) (rx-gen 0) (tx-slot *fn2-none*) (tx-gen 0)
                   (cap-index 0) (cap-nonce 0) (start 0) (pos 0) (overflow 0) (compacting 0)
                   (cursor 0) (tx-off 0) (ordinal 0) (auth-pending *fn2-conn-auth-none*) (refused 0)
                   (next-free next) (wait-reason *fn2-wait-none*) (account-ref *fn2-none*)
                   (upload *fn2-none*) (query *fn2-none*) (query-gen 0)
                   (tls-token *fn2-none*) (tls-token-gen 0) (tls-op *fn2-none*) (tls-op-gen 0)
                   (upgrade-target *fn2-conn-upgrade-target-none*)
                   (upgrade-stage *fn2-conn-upgrade-stage-none*) (tls-ok 0))
             (:next (:if retire :retired :free))
             (:do () (fn2-machine-reclaim-fn2-conn id retire))
             (:charge :steps *fn2-work-release*))))
  (:retired (:idle))
  ;; :query (section 15.3).
  (:query
   (:if (equal row-query *fn2-none*)
        ((:do (tcode x xgen)
              (fn2-machine-take-fn2-cursor *fn2-none* id row-generation *fn2-conn-kind* row-mask
                                           row-rx-slot row-rx-gen row-line-s row-line-e
                                           row-tx-slot row-tx-gen row-group row-current row-pin row-posting)
              :case (((:ok) (:set (query x) (query-gen xgen)) (:charge :steps *fn2-work-transition*))
                     ;; no fn2-cursor row: unreachable in composition (a query is
                     ;; answered only where reading is served, fn2-conn-reading-p)
                     ((:none) (:stop :machine-phase))
                     (:otherwise (:park :taken fn2-cursor :steps *fn2-work-transition*)))))
        ((:cond ((not (:live child-cursor)) (:stop :machine-phase))
                ((equal (:read child-cursor turn) 1) (:charge :steps *fn2-work-transition*))
                ((< (:read child-cursor roff) (fn2-conn-fill row-tx-slot))
                 (:set (tx-off (:read child-cursor roff)) (after *fn2-conn-after-query*)) (:next :reply)
                 (:charge :steps *fn2-work-transition* :runnable t))
                ;; the cursor could not complete a reply whose status line went
                ;; (a storage read failed mid-article): the connection closes
                ((and (equal (:read child-cursor done) 1)
                      (equal (:read child-cursor update) *fn2-cursor-update-close*))
                 (:let x row-query)
                 (:let xgen row-query-gen)
                 (:do () (fn2-conn-cursor-go x xgen))
                 (:do () (fn2-conn-wake x))
                 (:set (query *fn2-none*) (query-gen 0))
                 (:next :closing)
                 (:charge :steps *fn2-work-transition* :runnable t))
                ((equal (:read child-cursor done) 1)
                 (:do (rcode)
                      (fn2-core-truncate row-tx-slot row-tx-gen
                                         (if (equal (:read child-cursor update) *fn2-cursor-update-ihave*)
                                             (:read child-cursor roff) 0))
                      :case ((:otherwise (:stop :machine-phase))))
                 (:let upd (:read child-cursor update))
                 (:let g (:read child-cursor sel))
                 (:let c (:read child-cursor ncurrent))
                 (:let v (:read child-cursor spin))
                 (:let x row-query)
                 (:let xgen row-query-gen)
                 (:do () (fn2-conn-cursor-go x xgen))
                 (:do () (fn2-conn-wake x))
                 (:let sel (equal upd *fn2-cursor-update-selection*))
                 (:let ihv (equal upd *fn2-cursor-update-ihave*))
                 (:set (query *fn2-none*) (query-gen 0)
                       (group (if sel g row-group))
                       (current (if (or sel (equal upd *fn2-cursor-update-current*)) c row-current))
                       (pin (if sel v row-pin))
                       (rule (if ihv *fn2-conn-rule-ihave* row-rule))
                       (line-e (if ihv c row-line-e)))
                 (:next :command)
                 (:charge :steps *fn2-work-transition* :runnable t))
                (t (:do () (fn2-conn-cursor-go row-query row-query-gen))
                   (:do () (fn2-conn-wake row-query))
                   (:charge :steps *fn2-work-transition*)))))))
 :observes
 ((:receive-result :from (:command :article-input)
   (:if (and (or (equal outcome *fn2-outcome-done*) (equal outcome *fn2-outcome-short*))
             (natp count) (< 0 count))
        ((:do (code) (fn2-account-charge-core row-principal-slot *fn2-account-charge-rx* count))
         (:if (eq code :ok) ((:wake)) ((:stop :machine-observation))))
        ((:next :closing) (:wake))))
  (:send-result :from (:reply :closing)
   (:if (not (eq (fn2-machine-pool-borrows-read-code row-tx-slot) :ok))
        ((:stop :machine-observation))
        ((:let borrows (fn2-machine-pool-borrows row-tx-slot))
         ;; Every Send terminal reports consumed application input, including
         ;; failure/cancellation. Only success permits advancing the reply.
         (:do (code) (fn2-account-charge-core row-principal-slot *fn2-account-charge-tx* count))
         (:if (eq code :ok)
              ((:if (and (or (equal outcome *fn2-outcome-done*) (equal outcome *fn2-outcome-short*))
                         (natp count))
                    ((:set (borrows borrows) (tx-off (+ row-tx-off count))) (:wake))
                    ((:set (borrows borrows)) (:next :closing) (:wake))))
              ((:stop :machine-observation))))))
  (:borrow-released
   (:let loan-slot (if (or (equal row-upgrade-stage *fn2-conn-upgrade-stage-running*)
                          (equal row-upgrade-stage *fn2-conn-upgrade-stage-finished*)) row-rx-slot row-tx-slot))
   (:if (not (eq (fn2-machine-pool-borrows-read-code loan-slot) :ok))
        ((:stop :machine-observation))
        ((:set (borrows (fn2-machine-pool-borrows loan-slot))) (:wake))))
  (:tls-result :from (:upgrading :closing)
   (:if (or (not (equal row-upgrade-target *fn2-conn-upgrade-target-tls*))
            (not (eq (fn2-machine-pool-borrows-read-code row-rx-slot) :ok)))
        ((:stop :machine-observation))
        ((:set (borrows (fn2-machine-pool-borrows row-rx-slot))
               (upgrade-stage *fn2-conn-upgrade-stage-finished*) (tls-ok (if (equal outcome *fn2-outcome-done*) 1 0)))
         (:wake))))
  (:compress-result :from (:upgrading :closing)
   (:if (or (not (equal row-upgrade-target *fn2-conn-upgrade-target-compress*))
            (not (eq (fn2-machine-pool-borrows-read-code row-rx-slot) :ok)))
        ((:stop :machine-observation))
        ((:set (borrows (fn2-machine-pool-borrows row-rx-slot))
               (upgrade-stage *fn2-conn-upgrade-stage-finished*) (tls-ok (if (equal outcome *fn2-outcome-done*) 1 0)))
         (:wake))))
  (:cancel-result :from (:closing) (:wake))
  (:close-result :from (:closing)
   (:next :draining) (:wake))))

(local
 (defun fn2-dc-arm-fns (arms)
   (declare (xargs :mode :program))
   (if (atom arms) nil (cons (cadar arms) (fn2-dc-arm-fns (cdr arms))))))
(local
 (defun fn2-dc-wrap-success-charge (x kind arm-fns)
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
         (t (cons (fn2-dc-wrap-success-charge (car x) kind arm-fns)
                  (fn2-dc-wrap-success-charge (cdr x) kind arm-fns))))))
(defmachine-arms fn2-conn)
(make-event
 (let* ((ev (fn2-machine-run-event 'fn2-conn (w state)))
        (arm-fns (fn2-dc-arm-fns (fn2-machine-property 'fn2-conn :continuations (w state))))
        (patched (fn2-dc-wrap-success-charge ev 'fn2-conn arm-fns)))
   (if (equal patched ev)
       (er soft 'assembly-callbacks-d-conn "Could not patch fn2-conn-run-success-charge.")
     (value patched))))

