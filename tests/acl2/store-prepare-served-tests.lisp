; Witnesses for books/store-prepare-served.lisp (PRF-290; audit packet G2-P3,
; lane audit-fixes): the standalone Store's served decision, the prepare
; host/store-node-host.lisp fn-store-sn-prepare calls
; (fn-psrv-store-prepare-next, over the Store's live configuration, the
; state's second reservation and the interned count the arena holds).
(in-package "ACL2")
(include-book "../../books/store-prepare-served")
(include-book "store-prepare-correspondence-tests")

; The Store's live configuration: the replay of its configuration history.
; *spt-serving* is the default (fn.letters and fn.test served);
; *spt-retired* follows it with a removal of fn.test (generation 2).
(defconst *spt-serving*
  (fn-config-replay 0 (fn-cnode-line-ceiling) (list *fn-cfg-default-record*)))
(defconst *spt-retired*
  (fn-config-replay 0 (fn-cnode-line-ceiling)
                    (list *fn-cfg-default-record*
                          (fn-cfg-record-make 1 7 2 (list (fn-cfg-remove-group "fn.test"))
                                              *fn-cfg-default-stamp*))))
(defconst *spt-w* *spc-second-wire*)   ; fn.test only
(defconst *spt-s* *spc-second-reserved*)
(defconst *spt-count* 1)               ; the arena holds the first article

; fn-psrv-store-prepare-next-cases, the served arm: the configuration serves
; fn.test, the prepare stages the record exactly as the carried prepare does,
; and the Store moves to :record-staged.
(assert-event
 (and (fn-cnode-selection-servedp *spt-serving* (fn-record-groups *spt-w*))
      (equal (fn-psrv-store-prepare-next *spt-serving* *spt-s* *spt-w* *spt-count*)
             (fn-store-prepare-carried-next *spt-s* *spt-w* *spt-count*))
      (equal (fn-sf-phase (fn-sn-files (fn-psrv-store-prepare-next *spt-serving* *spt-s* *spt-w*
                                                                    *spt-count*)))
             :record-staged)))
; The refusal arm: fn.test retired, the Store is unchanged (the host answers
; :refused), while the carried prepare alone would have staged it.
(assert-event
 (and (not (fn-cnode-selection-servedp *spt-retired* (fn-record-groups *spt-w*)))
      (equal (fn-psrv-store-prepare-next *spt-retired* *spt-s* *spt-w* *spt-count*) *spt-s*)
      (not (equal (fn-store-prepare-carried-next *spt-s* *spt-w* *spt-count*) *spt-s*))))
; The conjunct the lemma drops, (fn-record-p w): a non-record is refused on
; both sides of the equality even where its (absent) groups would be served.
(assert-event
 (and (not (fn-record-p 'not-a-record))
      (equal (fn-psrv-store-prepare-next *spt-serving* *spt-s* 'not-a-record *spt-count*) *spt-s*)
      (equal (if (fn-cnode-selection-servedp *spt-serving* (fn-record-groups 'not-a-record))
                 (fn-store-prepare-carried-next *spt-s* 'not-a-record *spt-count*)
               *spt-s*)
             *spt-s*)))

; RFC 3977 section 6 (PKT-615; books/store-prepare-served.lisp
; fn-psrv-store-prepare-refuses-exhausted-by-definition).  A CONSTRUCTED boundary state:
; the Store's node with fn.test's watermark at 2,147,483,647 (reaching it
; takes that many articles).  Every hypothesis holds (a record, served, its
; numbers past the bound) and so does the conclusion: the Store unchanged,
; the word :article-numbers-exhausted.
(defun spt-with-next (s group n)
  (let* ((node (fn-sn-node s))
         (a (fn-node-acceptance node)))
    (fn-sn-update s (fn-sn-files s)
                  (fn-node-make-state
                   (fn-make-state (fn-state-groups a)
                                  (put-assoc-equal group n (fn-state-nexts a))
                                  (fn-state-articles a) (fn-state-next-txid a)
                                  (fn-state-pending a) (fn-state-fenced a))
                   (fn-node-retention node) (fn-node-stage node) (fn-node-bindings node)))))
(defconst *spt-s-at* (spt-with-next *spt-s* "fn.test" *fn-nntp-max-article-number*))
(assert-event
 (and (fn-record-p *spt-w*)
      (fn-cnode-selection-servedp *spt-serving* (fn-record-groups *spt-w*))
      (not (fn-psrv-store-numberedp *spt-s-at* *spt-w*))
      (equal (fn-psrv-store-prepare-next *spt-serving* *spt-s-at* *spt-w* *spt-count*) *spt-s-at*)
      (equal (fn-psrv-store-refusal-kind *spt-serving* *spt-s-at* *spt-w*)
             :article-numbers-exhausted)))
; Hypothesis removal, (not numberedp): the reachable Store fits, the record
; is staged and the word is not asked; removal of the served hypothesis: the
; retired configuration at the bound answers :refused (no number named).
(assert-event
 (and (fn-psrv-store-numberedp *spt-s* *spt-w*)
      (not (equal (fn-psrv-store-prepare-next *spt-serving* *spt-s* *spt-w* *spt-count*) *spt-s*))
      (not (fn-cnode-selection-servedp *spt-retired* (fn-record-groups *spt-w*)))
      (equal (fn-psrv-store-refusal-kind *spt-retired* *spt-s-at* *spt-w*) :refused)))
