; Teeth for books/reader-open-carried.lisp (the reader's connection open with
; the selection's invariant carried) and for the retention commit's carried
; node invariant (books/replay.lisp fn-replay-apply-retention-event's mbt).
(in-package "ACL2")
(include-book "../../books/reader-open-carried")
(include-book "owner-advance-carried-tests")

; -----------------------------------------------------------------------------
; Reachable witness: the archive the reader host's seed selection uses
; (host/reader-host.lisp *fn-reader-archive*): one committed article in one
; group, as fn-accept-prepare and fn-accept-complete leave it.
(defconst *rdc-t-groups* '("fn.letters"))
; by specification: the flip -- the acceptance machine carries the payload as
; an arena handle (natp), never octets; the host seeds the arena with the
; article's octets (*fn-reader-payload*, "Message-ID: <reader@example.invalid>
; CRLF CRLF Hello CRLF") and the archive holds handle 0.
(defconst *rdc-t-archive*
  (fn-accept-complete
   (fn-accept-prepare (fn-initial-state *rdc-t-groups*) 1
                      "<reader@example.invalid>"
                      0
                      *rdc-t-groups* 0)
   0 1 :durable))
(defconst *rdc-t-verdicts* '(("<reader@example.invalid>" . :pinned-for-the-test)))
(defconst *rdc-t-config* (fn-inj-make-config nil '(102 110) '((102 110 46 108 101 116 116 101 114 115)) 1000))
(defconst *rdc-t-sel* (fn-rdc-selection *rdc-t-archive* *rdc-t-verdicts*))

; fn-rdc-selection-establishes and fn-rdc-reset-is-served-open, antecedent and
; conclusion, on the witness.
(assert-event (consp (fn-state-articles *rdc-t-archive*)))
(assert-event (fn-nntp-projectionp *rdc-t-archive*))
(assert-event (fn-rdc-readyp *rdc-t-sel*))
(assert-event (fn-statep (fn-rdc-archive *rdc-t-sel*)))
(assert-event (equal (fn-rdc-verdicts *rdc-t-sel*) *rdc-t-verdicts*))
(assert-event (equal (fn-rdc-index *rdc-t-sel*)
                     (fn-midx-build (fn-state-articles *rdc-t-archive*))))
(assert-event (consp (fn-rdc-index *rdc-t-sel*)))
(defconst *rdc-t-opened*
  (fn-rdc-reset *rdc-t-sel* 510 8192 *rdc-t-config* nil nil (fn-auth-open-config)))
(assert-event
 (equal *rdc-t-opened*
        (fn-served-pin-verdicts
         (fn-served-open *rdc-t-archive* 510 8192 *rdc-t-config* nil nil
                         (fn-auth-open-config))
         *rdc-t-verdicts*)))
; Non-degenerate: a greeting is written, the connection carries the selected
; archive, its trie and its verdicts, and its reader session is projected.
(defconst *rdc-t-conn* (fn-served-result-conn *rdc-t-opened*))
(assert-event (consp (fn-served-reply-octets (fn-served-result-effects *rdc-t-opened*))))
(assert-event (equal (fn-served-conn-archive *rdc-t-conn*) *rdc-t-archive*))
(assert-event (equal (fn-served-conn-index *rdc-t-conn*) (fn-rdc-index *rdc-t-sel*)))
(assert-event (equal (fn-served-conn-verdicts *rdc-t-conn*) *rdc-t-verdicts*))
(assert-event (equal (fn-nntp-session-projected
                      (fn-auth-reader-session (fn-served-conn-session *rdc-t-conn*)))
                     t))

; The Store selection over owner-advance-carried-tests' committed owner store.
(defconst *rdc-t-store* (fn-own-store (fn-ocfg-owner *acar-t-committed*)))
(assert-event (fn-sn-statep *rdc-t-store*))
(assert-event (fn-rdc-readyp (fn-rdc-store-selection *rdc-t-store*)))
(assert-event (equal (fn-rdc-archive (fn-rdc-store-selection *rdc-t-store*))
                     (fn-node-acceptance (fn-sn-node *rdc-t-store*))))
(assert-event (not (fn-rdc-readyp (fn-rdc-store-selection '(not a store)))))

; The host's per-connection call runs compiled code.
(assert-event
 (and (eq (symbol-class 'fn-rdc-reset (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rdc-served-open (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rdc-selection (w state)) :common-lisp-compliant)))

; -----------------------------------------------------------------------------
; Hypothesis removal, fn-rdc-served-open-is-served-open.
; (1) Without the index hypothesis (fn-statep holds; the index is not the
; archive's trie): the connection pins a different index.
(assert-event (fn-statep *rdc-t-archive*))
(assert-event (not (equal nil (fn-midx-build (fn-state-articles *rdc-t-archive*)))))
(assert-event
 (not (equal (fn-rdc-served-open *rdc-t-archive* nil 510 8192 *rdc-t-config* nil nil
                                 (fn-auth-open-config))
             (fn-served-open *rdc-t-archive* 510 8192 *rdc-t-config* nil nil
                             (fn-auth-open-config)))))
; (2) Without fn-statep (corrupted-state witness: an article list the
; acceptance recogniser refuses; the index hypothesis holds): the reference
; records the projection as failed, the carried open, which took it from a
; selection, does not.
(defconst *rdc-t-bad*
  (fn-make-state (fn-state-groups *rdc-t-archive*)
                 (fn-state-nexts *rdc-t-archive*)
                 (cons '(not an article) (fn-state-articles *rdc-t-archive*))
                 (fn-state-next-txid *rdc-t-archive*) nil nil))
(assert-event (not (fn-statep *rdc-t-bad*)))
(assert-event
 (not (equal (fn-rdc-served-open *rdc-t-bad* (fn-midx-build (fn-state-articles *rdc-t-bad*))
                                 510 8192 *rdc-t-config* nil nil (fn-auth-open-config))
             (fn-served-open *rdc-t-bad* 510 8192 *rdc-t-config* nil nil
                             (fn-auth-open-config)))))

; Hypothesis removal, fn-rdc-reset-is-served-open: a selection that did not
; answer :ready (the corrupted archive is refused) opens over no archive.
(assert-event (not (fn-rdc-readyp (fn-rdc-selection *rdc-t-bad* *rdc-t-verdicts*))))
(assert-event
 (not (equal (fn-rdc-reset (fn-rdc-selection *rdc-t-bad* *rdc-t-verdicts*)
                           510 8192 *rdc-t-config* nil nil (fn-auth-open-config))
             (fn-served-pin-verdicts
              (fn-served-open *rdc-t-bad* 510 8192 *rdc-t-config* nil nil
                              (fn-auth-open-config))
              *rdc-t-verdicts*))))

; -----------------------------------------------------------------------------
; The retention commit (books/replay.lisp fn-replay-apply-retention-event):
; its body's (mbt (fn-node-statep advanced)) rests on
; fn-replay-advance-preserves-node-statep.  Witness: the committed owner
; store's node, advanced to its next transaction id.
(defconst *rdc-t-node* (fn-sn-node *rdc-t-store*))
(defconst *rdc-t-k* (fn-state-next-txid (fn-node-acceptance *rdc-t-node*)))
(assert-event (fn-node-statep *rdc-t-node*))
(assert-event (fn-node-statep (fn-replay-advance-txid *rdc-t-node* *rdc-t-k*)))
(assert-event (equal (fn-state-next-txid
                      (fn-node-acceptance (fn-replay-advance-txid *rdc-t-node* *rdc-t-k*)))
                     *rdc-t-k*))
; Without its hypothesis (corrupted-state witness: not a node), the advance
; returns its argument and the conclusion fails.
(assert-event (not (fn-node-statep '(not a node))))
(thm (not (fn-node-statep (fn-replay-advance-txid '(not a node) k)))
     :hints (("Goal" :in-theory (enable fn-replay-advance-txid))))
