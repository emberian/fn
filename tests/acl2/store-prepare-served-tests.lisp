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
