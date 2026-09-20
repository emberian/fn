; fn: teeth for books/config-stream.lisp -- the two durable kinds as one
; sequence-ordered stream (packet R5/R6 of specs/reconfiguration.md).
;
; The separating witness this book exists for is the last section: one
; capacity decrease that the configuration-only replay the host performs
; today ACCEPTS and the merged replay REFUSES, with the article records that
; make the difference spelled out.  That separation is the whole argument for
; offering `set-capacity' only under the merged stream.

(in-package "ACL2")
(include-book "../../books/config-stream")
(include-book "../../books/store-config")

(local (in-theory (enable fn-cfg-vocabulary fn-cfg-invariants-vocabulary
                          fn-cnode-vocabulary fn-cstr-vocabulary)))

(defconst *cstr-t-stamp* (fn-clock-observation 7 1000 5 t))
(defconst *cstr-t-payload* '(72 105))

; -----------------------------------------------------------------------------
; Ground records of both kinds.
;
; The default record is generation 1 of every fn store (tools/run_store.py
; init).  Under THE DECISION of books/config-stream.lisp the sequence field
; of every record, of either kind, is its position in the unified stream: the
; default record is at 0, the two articles at 1 and 2, the capacity change
; at 3.

(defun cstr-t-article (seq txid msgid)
  (declare (xargs :mode :program))
  (fn-record-make seq txid 1 msgid *cstr-t-payload* '("fn.test")
                  (concatenate 'string "ob-" msgid) "subject" "ev" 1))

(defconst *cstr-t-a1* (cstr-t-article 1 0 "<a@t>"))
(defconst *cstr-t-a2* (cstr-t-article 2 1 "<b@t>"))
(defconst *cstr-t-articles* (list *cstr-t-a1* *cstr-t-a2*))

; The capacity decrease, written twice: once as the host numbers it TODAY
; (sequence = the previous generation, 1, because the configuration file is
; its own sequence space) and once as the unified stream numbers it (3).
(defconst *cstr-t-cap-today*
  (fn-cfg-record-make 1 2 2 (list (fn-cfg-set-capacity 1)) *cstr-t-stamp*))
(defconst *cstr-t-cap-unified*
  (fn-cfg-record-make 3 2 2 (list (fn-cfg-set-capacity 1)) *cstr-t-stamp*))

; A group creation, at the unified position 3, for the merge witnesses.
(defconst *cstr-t-create-unified*
  (fn-cfg-record-make 3 2 2 (list (fn-cfg-create-group "fn.dtn" "policy-a"))
                      *cstr-t-stamp*))

(defconst *cstr-t-configs* (list *fn-cfg-default-record* *cstr-t-create-unified*))

; -----------------------------------------------------------------------------
; fn-cstr-merge: losslessness, length and order

(defconst *cstr-t-merged* (fn-cstr-merge *cstr-t-configs* *cstr-t-articles*))

; A NON-DEGENERATE witness: both kinds present, and the merge interleaves
; them -- config, article, article, config -- rather than concatenating.
(assert-event (equal (len *cstr-t-merged*) 4))
(assert-event (equal (fn-cstr-jrec-seqs *cstr-t-merged*) '(0 1 2 3)))
(assert-event (equal (fn-jrec-kind (nth 0 *cstr-t-merged*)) :config))
(assert-event (equal (fn-jrec-kind (nth 1 *cstr-t-merged*)) :article))
(assert-event (equal (fn-jrec-kind (nth 2 *cstr-t-merged*)) :article))
(assert-event (equal (fn-jrec-kind (nth 3 *cstr-t-merged*)) :config))
; and it is NOT either concatenation, so the ordering is doing work
(assert-event (not (equal *cstr-t-merged*
                          (append (fn-cstr-config-jrecs *cstr-t-configs*)
                                  (fn-cstr-article-jrecs *cstr-t-articles*)))))
(assert-event (not (equal *cstr-t-merged*
                          (append (fn-cstr-article-jrecs *cstr-t-articles*)
                                  (fn-cstr-config-jrecs *cstr-t-configs*)))))

; fn-cstr-merge-keeps-every-config-record / -article-record, instantiated
(assert-event (equal (fn-cstr-kind-bodies :config *cstr-t-merged*) *cstr-t-configs*))
(assert-event (equal (fn-cstr-kind-bodies :article *cstr-t-merged*) *cstr-t-articles*))

; fn-cstr-merge-is-sequence-ordered, instantiated, and its hypotheses given
; teeth: an out-of-order configuration file merges to an out-of-order stream.
(assert-event (fn-cstr-nondecreasingp (fn-cstr-jrec-seqs *cstr-t-merged*)))
(defconst *cstr-t-unsorted-configs* (list *cstr-t-create-unified* *fn-cfg-default-record*))
(assert-event (not (fn-cstr-nondecreasingp (fn-cstr-config-seqs *cstr-t-unsorted-configs*))))
(assert-event (not (fn-cstr-nondecreasingp
                    (fn-cstr-jrec-seqs (fn-cstr-merge *cstr-t-unsorted-configs*
                                                      *cstr-t-articles*)))))

; The merged stream is what the replay loop wants: sequences 0,1,2,... from 0.
(assert-event (fn-jrec-sequences-from *cstr-t-merged* 0))
(assert-event (fn-jrec-listp *cstr-t-merged*))

; -----------------------------------------------------------------------------
; The merged replay runs, and it is the one the keystone is about

(defconst *cstr-t-replayed* (fn-cstr-replay *cstr-t-configs* *cstr-t-articles*))
(assert-event (equal (fn-replay-result-kind *cstr-t-replayed*) :ok))
(assert-event (equal (fn-cfg-generation
                      (fn-cnode-config (fn-replay-result-node *cstr-t-replayed*)))
                     2))
; fn-cstr-ok-merged-replay-ends-in-a-configured-node, instantiated
(assert-event (fn-cnode-statep (fn-replay-result-node *cstr-t-replayed*)))
; and the accounting conjunct that keystone carries is not vacuous here: the
; two articles really did reserve.
(assert-event (equal (fn-retain-reserved
                      (fn-node-retention
                       (fn-cnode-node (fn-replay-result-node *cstr-t-replayed*))))
                     2))

; -----------------------------------------------------------------------------
; THE SEPARATING WITNESS (R6).
;
; One capacity decrease to 1, over a history whose two articles hold a
; reservation total of 2.
;
;   * the configuration-only replay -- `fn-cnode-config-replay', exactly what
;     host/store-node-host.lisp runs at open today -- ACCEPTS it, because its
;     node has replayed no articles and therefore has a reservation total of
;     zero.  The store it hands back has capacity 1 and is about to replay two
;     articles that need 2;
;   * the merged replay REFUSES it, at the record, with `:config-refusal',
;     because `fn-cnode-record-acceptablep' sees the reservation total the
;     earlier article records produced;
;   * the LIVE admission the operator's request goes through
;     (`fn-cnode-record-acceptablep' on the live node) also refuses it.  The
;     merged replay agrees with live admission; the configuration-only replay
;     does not, and that disagreement is the reason `set-capacity' is not
;     offered until the interleaving lands.

(defconst *cstr-t-config-first*
  (fn-cnode-config-replay (list *fn-cfg-default-record* *cstr-t-cap-today*)))
(assert-event (equal (fn-replay-result-kind *cstr-t-config-first*) :ok))
(assert-event (equal (fn-cfg-capacity
                      (fn-cfg-value
                       (fn-cnode-config (fn-replay-result-node *cstr-t-config-first*))))
                     1))

(defconst *cstr-t-merged-cap*
  (fn-cstr-replay (list *fn-cfg-default-record* *cstr-t-cap-unified*)
                  *cstr-t-articles*))
(assert-event (equal (fn-replay-result-kind *cstr-t-merged-cap*) :fault))
(assert-event (equal (fn-replay-result-reason *cstr-t-merged-cap*) :config-refusal))
(assert-event (equal (fn-replay-result-sequence *cstr-t-merged-cap*) 3))

; The two replays disagree on the same operator intent.  That is the
; separation, and it is by more than a weakest clause: one reports :ok with a
; capacity below the reservation the very next records establish, the other
; reports a named refusal at the offending record.
(assert-event (not (equal (fn-replay-result-kind *cstr-t-config-first*)
                          (fn-replay-result-kind *cstr-t-merged-cap*))))

; Control: raise the capacity instead of lowering it and both agree.  Without
; this the witness above could be read as "the merged replay refuses
; everything".
(defconst *cstr-t-raise-unified*
  (fn-cfg-record-make 3 2 2 (list (fn-cfg-set-capacity 4194304)) *cstr-t-stamp*))
(defconst *cstr-t-merged-raise*
  (fn-cstr-replay (list *fn-cfg-default-record* *cstr-t-raise-unified*)
                  *cstr-t-articles*))
(assert-event (equal (fn-replay-result-kind *cstr-t-merged-raise*) :ok))
(assert-event (equal (fn-cfg-capacity
                      (fn-cfg-value
                       (fn-cnode-config (fn-replay-result-node *cstr-t-merged-raise*))))
                     4194304))
; A decrease to exactly the reservation total is the boundary case and is
; admitted: the merged replay is not simply refusing every decrease.
(defconst *cstr-t-merged-boundary*
  (fn-cstr-replay (list *fn-cfg-default-record*
                        (fn-cfg-record-make 3 2 2 (list (fn-cfg-set-capacity 2))
                                            *cstr-t-stamp*))
                  *cstr-t-articles*))
(assert-event (equal (fn-replay-result-kind *cstr-t-merged-boundary*) :ok))

; -----------------------------------------------------------------------------
; What a generation serves: teeth for the two keystones
;
; fn-cstr-created-group-is-served-exactly-from-its-generation and
; fn-cstr-retired-group-is-served-exactly-below-its-generation.  The witness
; is a value with two groups already in it, so neither theorem is exercised
; on a one-group table.

(defconst *cstr-t-v1*
  (fn-cfg-value (fn-cnode-config (fn-replay-result-node
                                  (fn-cnode-config-replay (list *fn-cfg-default-record*))))))
(assert-event (equal (fn-cfg-group-names *cstr-t-v1* 1) '("fn.letters" "fn.test")))

; Creation at generation 2: served at 2 and above, NOT served at 1 or 0.
(defconst *cstr-t-v2*
  (fn-cfg-apply-delta *cstr-t-v1* 2 *cstr-t-stamp*
                      (fn-cfg-create-group "fn.dtn" "policy-a")))
(assert-event (fn-cfg-group-livep *cstr-t-v2* 2 "fn.dtn"))
(assert-event (fn-cfg-group-livep *cstr-t-v2* 7 "fn.dtn"))
(assert-event (not (fn-cfg-group-livep *cstr-t-v2* 1 "fn.dtn")))
(assert-event (not (fn-cfg-group-livep *cstr-t-v2* 0 "fn.dtn")))
; The served TABLE differs at the two generations, which is what a
; per-connection pin observes.
(assert-event (equal (fn-cfg-group-names *cstr-t-v2* 1) '("fn.letters" "fn.test")))
(assert-event (equal (fn-cfg-group-names *cstr-t-v2* 2)
                     '("fn.letters" "fn.test" "fn.dtn")))

; Retirement at generation 3: served below 3, not served at 3 and above, and
; the entry is still there with its watermark slot (NNT-006).
(defconst *cstr-t-v3*
  (fn-cfg-apply-delta *cstr-t-v2* 3 *cstr-t-stamp* (fn-cfg-remove-group "fn.test")))
(assert-event (fn-cfg-group-livep *cstr-t-v3* 2 "fn.test"))
(assert-event (not (fn-cfg-group-livep *cstr-t-v3* 3 "fn.test")))
(assert-event (not (fn-cfg-group-livep *cstr-t-v3* 9 "fn.test")))
(assert-event (equal (fn-cfg-group-all-names (fn-cfg-groups *cstr-t-v3*))
                     '("fn.letters" "fn.test" "fn.dtn")))
(assert-event (equal (fn-cfg-group-names *cstr-t-v3* 3) '("fn.letters" "fn.dtn")))

; -----------------------------------------------------------------------------
; fn-cstr-replay-of-a-config-only-history-is-fn-cnode-config-replay: the
; definitional agreement, instantiated, so that adopting the merge is visibly
; a no-op on a store with no articles.
(assert-event (equal (fn-cstr-replay (list *fn-cfg-default-record*) nil)
                     (fn-cnode-config-replay (list *fn-cfg-default-record*))))
