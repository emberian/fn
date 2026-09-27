; Teeth for books/replay-identity-index.lisp (PRF-242).
;
; The witness history is config-physical-replay-tests' mixed history,
; extended: an undertaking and its release (the ledger's id moves from the
; pins to the releases), two configuration records at txid 7, then two
; articles.  The host's two opens are exercised as the host calls them: the
; full replay (the capture of the empty prefix, extended over the whole
; history) and the checkpoint resume (the capture after the first article,
; extended over the rest), so the tries are both built step by step from
; empty and built once from a node that already knows an article, a pin and
; a release.
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)
(include-book "../../books/replay-identity-index")

(defconst *rii-t-stamp* *fn-cfg-default-stamp*)
(defconst *rii-t-undertake*
  (fn-store-retention-event-make :undertake 0 0 0
                                 "forward-rii" "subject" "evidence" 10))
(defconst *rii-t-release*
  (fn-store-retention-event-make :release 1 1 1
                                 "forward-rii" "subject" "evidence" 0))
(defconst *rii-t-decrease*
  (fn-cfg-record-make 1 7 2 (list (fn-cfg-set-capacity 1)) *rii-t-stamp*))
(defconst *rii-t-increase*
  (fn-cfg-record-make 2 7 3 (list (fn-cfg-set-capacity 20)) *rii-t-stamp*))
; The history holds RETAINED rows (records flip): each article is the held
; row of its wire record, at a handle of its own (the fold reads no bytes).
(defun rii-t-article (sequence txid msgid obligation)
  (fn-held-plain (fn-record-make sequence txid txid msgid '(65) '("fn.test")
                                 obligation "subject" "evidence" 2 841000000)
                 sequence))
(defconst *rii-t-article* (rii-t-article 2 7 "<rii@example.invalid>" "archive-rii"))
(defconst *rii-t-article-2* (rii-t-article 3 8 "<rii-2@example.invalid>" "archive-rii-2"))
; The same Message-ID again, under a fresh obligation id: acceptance refuses.
(defconst *rii-t-dup-msgid* (rii-t-article 3 8 "<rii@example.invalid>" "archive-rii-3"))
; A fresh Message-ID under the held obligation id: retention refuses.
(defconst *rii-t-dup-id* (rii-t-article 3 8 "<rii-4@example.invalid>" "archive-rii"))
; A fresh Message-ID under the released undertaking's id: still known.
(defconst *rii-t-released-id* (rii-t-article 3 8 "<rii-5@example.invalid>" "forward-rii"))

(defconst *rii-t-configs*
  (list *fn-cfg-default-record* *rii-t-decrease* *rii-t-increase*))
(defconst *rii-t-prefix* (list *rii-t-undertake* *rii-t-release* *rii-t-article*))
(defconst *rii-t-events* (append *rii-t-prefix* (list *rii-t-article-2*)))
(defconst *rii-t-empty* (fn-sco-capture *rii-t-configs* nil))
(defconst *rii-t-capture* (fn-sco-capture *rii-t-configs* *rii-t-prefix*))
(defconst *rii-t-frontier* 9)

; -----------------------------------------------------------------------------
; fn-rii-sco-extend-is-sco-extend (no hypothesis), reachable on both host
; paths; the fold finishes :ok and opens.

(defconst *rii-t-full-e*
  (fn-sco-extend *rii-t-empty* *rii-t-configs* *rii-t-events*))
(defconst *rii-t-resumed-e*
  (fn-sco-extend *rii-t-capture* *rii-t-configs* (list *rii-t-article-2*)))
(assert-event
 (and (equal (fn-rii-sco-extend *rii-t-empty* *rii-t-configs* *rii-t-events*)
             *rii-t-full-e*)
      (equal (fn-rii-sco-extend *rii-t-capture* *rii-t-configs*
                                (list *rii-t-article-2*))
             *rii-t-resumed-e*)
      (equal *rii-t-resumed-e* *rii-t-full-e*)
      (equal (fn-replay-result-kind
              (fn-sco-cpr-finish (fn-sco-cpr *rii-t-full-e*) *rii-t-configs*))
             :ok)))

; The node the replay built knows both articles, one pin per article and the
; released undertaking: every identity question had a nonempty answer set.
(defconst *rii-t-node*
  (fn-cnode-node (fn-replay-result-node
                  (fn-sco-cpr-finish (fn-sco-cpr *rii-t-full-e*) *rii-t-configs*))))
(assert-event
 (and (equal (len (fn-state-articles (fn-node-acceptance *rii-t-node*))) 2)
      (fn-rii-knownp "forward-rii" (fn-node-retention *rii-t-node*))
      (fn-rii-knownp "archive-rii" (fn-node-retention *rii-t-node*))
      (fn-rii-knownp "archive-rii-2" (fn-node-retention *rii-t-node*))
      (not (fn-rii-knownp "archive-rii-3" (fn-node-retention *rii-t-node*)))
      (consp (fn-retain-releases (fn-node-retention *rii-t-node*)))))

; Each identity refusal is decided by the tries as the scans decide it: the
; fold stops at the refused article, both ways.
(defun rii-t-fold (history)
  (fn-sco-cpr-finish
   (fn-sco-cpr (fn-sco-extend *rii-t-empty* *rii-t-configs* history))
   *rii-t-configs*))
(defun rii-t-twin-fold (history)
  (fn-sco-cpr-finish
   (fn-sco-cpr (fn-rii-sco-extend *rii-t-empty* *rii-t-configs* history))
   *rii-t-configs*))
(assert-event
 (let ((dup-msgid (append *rii-t-prefix* (list *rii-t-dup-msgid*)))
       (dup-id (append *rii-t-prefix* (list *rii-t-dup-id*)))
       (released-id (append *rii-t-prefix* (list *rii-t-released-id*))))
   (and (equal (rii-t-twin-fold dup-msgid) (rii-t-fold dup-msgid))
        (equal (fn-replay-result-kind (rii-t-fold dup-msgid)) :fault)
        (equal (fn-replay-result-reason (rii-t-fold dup-msgid)) :event-refusal)
        (equal (rii-t-twin-fold dup-id) (rii-t-fold dup-id))
        (equal (fn-replay-result-reason (rii-t-fold dup-id)) :event-refusal)
        (equal (rii-t-twin-fold released-id) (rii-t-fold released-id))
        (equal (fn-replay-result-reason (rii-t-fold released-id)) :event-refusal))))

; -----------------------------------------------------------------------------
; fn-rii-classified-open-is-classified-open (no hypothesis), and the
; recognizer twins, reachable: the open of the extended capture is :ok.

(assert-event
 (let ((opened (fn-rii-classified-open *rii-t-full-e* *rii-t-configs*
                                       *rii-t-frontier*)))
   (and (equal opened (fn-sopc-classified-open *rii-t-full-e* *rii-t-configs*
                                               *rii-t-frontier*))
        (equal (fn-sn-open-kind (cadr opened)) :ok)
        (fn-rii-sf-record-listp *rii-t-events* 0 0 *rii-t-frontier*)
        (fn-sf-record-listp *rii-t-events* 0 0 *rii-t-frontier*)
        (fn-rii-sn-statep (fn-sn-open-state (cadr opened)))
        (fn-sn-statep (fn-sn-open-state (cadr opened))))))

; A history out of sequence (the two articles swapped) and one past the
; frontier: refused alike.
(assert-event
 (let ((swapped (append (list *rii-t-undertake* *rii-t-release*)
                        (list *rii-t-article-2* *rii-t-article*))))
   (and (not (fn-rii-sf-record-listp swapped 0 0 *rii-t-frontier*))
        (not (fn-sf-record-listp swapped 0 0 *rii-t-frontier*))
        (not (fn-rii-sf-record-listp *rii-t-events* 0 0 8))
        (not (fn-sf-record-listp *rii-t-events* 0 0 8))
        (equal (fn-rii-classified-open *rii-t-full-e* *rii-t-configs* 8)
               (fn-sopc-classified-open *rii-t-full-e* *rii-t-configs* 8))
        (equal (fn-sn-open-kind
                (cadr (fn-rii-classified-open *rii-t-full-e* *rii-t-configs* 8)))
               :error))))

(assert-event
 (equal (fn-event-fields *rii-t-article* nil) (list t 2 7 7)))

; -----------------------------------------------------------------------------
; The fold's keystone and the step's under their hypothesis, reachable: the
; paused node of the capture and the tries built from it (the resume's).
;
; fn-rii-okp contains a defun-sk (fn-rii-known-okp): it is a theorem's
; hypothesis and the carried functions' guard, never evaluated.  So each
; relation fact below is a theorem, and the twins whose guard carries it are
; evaluated without guard checking (make-event), as the host's raw call
; runs them.

(defconst *rii-t-paused-cn* (fn-sco-at 1 (fn-sco-cpr *rii-t-capture*)))
(defconst *rii-t-paused-node* (fn-cnode-node *rii-t-paused-cn*))
(defconst *rii-t-ix* (fn-rii-ix-of *rii-t-paused-node*))

(defthm rii-t-ix-is-related
  (fn-rii-okp *rii-t-ix* *rii-t-paused-node*)
  :hints (("Goal" :use ((:instance fn-rii-okp-of-ix-of
                                   (node *rii-t-paused-node*))))))

(defmacro rii-t-raw (name form)
  `(make-event
    (list 'defconst ',name (list 'quote (with-guard-checking :none ,form)))))

(rii-t-raw *rii-t-step* (fn-rii-apply-record *rii-t-paused-node* *rii-t-article-2*
                                             *rii-t-ix*))
(rii-t-raw *rii-t-step-dup* (fn-rii-apply-record *rii-t-paused-node*
                                                 *rii-t-dup-msgid* *rii-t-ix*))
(rii-t-raw *rii-t-prefix-run* (fn-rii-sco-cpr-prefix *rii-t-paused-cn* nil
                                                     (list *rii-t-article-2*)
                                                     3 3 *rii-t-ix*))
(assert-event
 (and (fn-cnode-statep *rii-t-paused-cn*)
      (fn-mxc-lookup "<rii@example.invalid>" (car *rii-t-ix*))
      (fn-rii-id-hasp "archive-rii" (cdr *rii-t-ix*))
      (fn-rii-id-hasp "forward-rii" (cdr *rii-t-ix*))
      (not (fn-rii-id-hasp "archive-rii-2" (cdr *rii-t-ix*)))
      (equal *rii-t-step*
             (fn-replay-apply-record *rii-t-paused-node* *rii-t-article-2*))
      (consp *rii-t-step*)
      (equal *rii-t-step-dup*
             (fn-replay-apply-record *rii-t-paused-node* *rii-t-dup-msgid*))
      (null *rii-t-step-dup*)
      (equal *rii-t-prefix-run*
             (fn-sco-cpr-prefix *rii-t-paused-cn* nil (list *rii-t-article-2*) 3 3))
      (fn-sco-pausedp *rii-t-prefix-run*)))

; Hypothesis removal, CORRUPTED tries (no fold builds these: the tries are
; built from the node or advanced by fn-rii-ix-next).  Each holds one entry
; the node does not: the second article's Message-ID, or its obligation id.
; The twin then refuses the second article, which the scan admits.  (A trie
; that MISSES an entry is not a counterexample to the step: the staged node's
; own recognizer, in fn-node-pending-matchesp's logical body, refuses the
; duplicate the trie let through.)
(defconst *rii-t-fake-msgid*
  (cons (fn-rii-id-put "<rii-2@example.invalid>" (car *rii-t-ix*)) (cdr *rii-t-ix*)))
(defconst *rii-t-fake-id*
  (cons (car *rii-t-ix*) (fn-rii-id-put "archive-rii-2" (cdr *rii-t-ix*))))

(defthm rii-t-fake-msgid-keeps-the-id-trie
  (fn-rii-known-okp (cdr *rii-t-fake-msgid*) (fn-node-retention *rii-t-paused-node*))
  :hints (("Goal" :use ((:instance fn-rii-kbuild-is-known-okp
                                   (retention (fn-node-retention
                                               *rii-t-paused-node*))))
           :in-theory (disable fn-rii-known-okp fn-rii-kbuild-is-known-okp))))
(defthm rii-t-fake-msgid-is-not-related
  (not (fn-rii-okp *rii-t-fake-msgid* *rii-t-paused-node*))
  :hints (("Goal" :in-theory (enable fn-rii-okp))))
(defthm rii-t-fake-id-is-not-related
  (not (fn-rii-okp *rii-t-fake-id* *rii-t-paused-node*))
  :hints (("Goal" :in-theory (enable fn-rii-okp)
           :use ((:instance fn-rii-known-okp-necc
                            (ktrie (cdr *rii-t-fake-id*))
                            (retention (fn-node-retention *rii-t-paused-node*))
                            (id "archive-rii-2"))))))

(rii-t-raw *rii-t-bad-msgid-step* (fn-rii-apply-record *rii-t-paused-node*
                                                       *rii-t-article-2*
                                                       *rii-t-fake-msgid*))
(rii-t-raw *rii-t-bad-id-step* (fn-rii-apply-record *rii-t-paused-node*
                                                    *rii-t-article-2* *rii-t-fake-id*))
(rii-t-raw *rii-t-bad-id-event* (fn-rii-cpr-apply-event *rii-t-paused-cn*
                                                        *rii-t-article-2* *rii-t-fake-id*))
(rii-t-raw *rii-t-bad-prefix* (fn-rii-sco-cpr-prefix *rii-t-paused-cn* nil
                                                     (list *rii-t-article-2*) 3 3
                                                     *rii-t-fake-msgid*))
(assert-event
 (and (equal (car *rii-t-fake-id*)
             (fn-midx-build (fn-state-articles
                             (fn-node-acceptance *rii-t-paused-node*))))
      (fn-mxc-lookup "<rii-2@example.invalid>" (car *rii-t-fake-msgid*))
      (fn-rii-id-hasp "archive-rii-2" (cdr *rii-t-fake-id*))
      (not (fn-rii-knownp "archive-rii-2" (fn-node-retention *rii-t-paused-node*)))
      (null *rii-t-bad-msgid-step*)
      (null *rii-t-bad-id-step*)
      (consp (fn-replay-apply-record *rii-t-paused-node* *rii-t-article-2*))
      (null *rii-t-bad-id-event*)
      (consp (fn-cpr-apply-event *rii-t-paused-cn* *rii-t-article-2*))
      (equal (fn-replay-result-reason *rii-t-bad-prefix*) :event-refusal)
      (fn-sco-pausedp
       (fn-sco-cpr-prefix *rii-t-paused-cn* nil (list *rii-t-article-2*) 3 3))))
(must-fail
 (defthm rii-t-apply-record-without-msgid-trie
   (equal *rii-t-bad-msgid-step*
          (fn-replay-apply-record *rii-t-paused-node* *rii-t-article-2*))))
(must-fail
 (defthm rii-t-apply-record-without-id-trie
   (equal *rii-t-bad-id-step*
          (fn-replay-apply-record *rii-t-paused-node* *rii-t-article-2*))))
(must-fail
 (defthm rii-t-cpr-apply-event-without-okp
   (equal *rii-t-bad-id-event*
          (fn-cpr-apply-event *rii-t-paused-cn* *rii-t-article-2*))))
(must-fail
 (defthm rii-t-prefix-without-okp
   (equal *rii-t-bad-prefix*
          (fn-sco-cpr-prefix *rii-t-paused-cn* nil (list *rii-t-article-2*) 3 3))))

; -----------------------------------------------------------------------------
; fn-rii-ix-next-keeps-okp.  Reachable: the release step from the node that
; holds the undertaking; the release arm keeps the id trie itself.

(defconst *rii-t-pinned*
  (fn-cnode-node (fn-sco-at 1 (fn-sco-cpr (fn-sco-capture *rii-t-configs*
                                                          (list *rii-t-undertake*))))))
(defconst *rii-t-pinned-ix* (fn-rii-ix-of *rii-t-pinned*))
(defconst *rii-t-released* (fn-replay-apply-record *rii-t-pinned* *rii-t-release*))
(assert-event
 (and (fn-rii-release-event-p *rii-t-release*)
      (consp *rii-t-released*)
      (fn-rii-knownp "forward-rii" (fn-node-retention *rii-t-pinned*))
      (equal (cdr (fn-rii-ix-next *rii-t-pinned-ix* *rii-t-pinned* *rii-t-released*
                                  *rii-t-release*))
             (cdr *rii-t-pinned-ix*))))
(defthm rii-t-release-step-is-related
  (fn-rii-okp (fn-rii-ix-next *rii-t-pinned-ix* *rii-t-pinned* *rii-t-released*
                              *rii-t-release*)
              *rii-t-released*)
  :hints (("Goal" :use ((:instance fn-rii-ix-next-keeps-okp
                                   (ix *rii-t-pinned-ix*) (old *rii-t-pinned*)
                                   (new *rii-t-released*)
                                   (release *rii-t-release*))
                        (:instance fn-rii-okp-of-ix-of (node *rii-t-pinned*)))
           :in-theory (disable fn-rii-ix-next-keeps-okp fn-rii-okp-of-ix-of))))

; Removal of the release condition: the same release event, but NEW is not
; the replay's step from OLD (it is the node after the first article, whose
; ledger knows "archive-rii" as well).  OLD's relation holds (above, by
; fn-rii-okp-of-ix-of), the event is a release, NEW is not its step, and the
; kept id trie misses "archive-rii".
(defconst *rii-t-wrong-next*
  (fn-rii-ix-next *rii-t-pinned-ix* *rii-t-pinned* *rii-t-paused-node*
                  *rii-t-release*))
(assert-event
 (and (fn-rii-release-event-p *rii-t-release*)
      (not (equal *rii-t-paused-node*
                  (fn-replay-apply-record *rii-t-pinned* *rii-t-release*)))
      (not (fn-rii-id-hasp "archive-rii" (cdr *rii-t-wrong-next*)))
      (fn-rii-knownp "archive-rii" (fn-node-retention *rii-t-paused-node*))))
(defthm rii-t-wrong-next-is-not-related
  (not (fn-rii-okp *rii-t-wrong-next* *rii-t-paused-node*))
  :hints (("Goal" :in-theory (enable fn-rii-okp)
           :use ((:instance fn-rii-known-okp-necc
                            (ktrie (cdr *rii-t-wrong-next*))
                            (retention (fn-node-retention *rii-t-paused-node*))
                            (id "archive-rii"))))))
(must-fail
 (defthm rii-t-ix-next-without-release-step
   (fn-rii-okp *rii-t-wrong-next* *rii-t-paused-node*)))

; Removal of the relation: tries that do not describe OLD stay wrong after a
; step that changes nothing they would repair (no release: the arm that
; keeps the id trie is the unchanged-ledger arm).
(defconst *rii-t-still-wrong*
  (fn-rii-ix-next *rii-t-fake-id* *rii-t-paused-node* *rii-t-paused-node* nil))
(assert-event
 (and (not (fn-rii-release-event-p nil))
      (equal (cdr *rii-t-still-wrong*) (cdr *rii-t-fake-id*))))
(defthm rii-t-still-wrong-is-not-related
  (not (fn-rii-okp *rii-t-still-wrong* *rii-t-paused-node*))
  :hints (("Goal" :in-theory (enable fn-rii-okp)
           :use ((:instance fn-rii-known-okp-necc
                            (ktrie (cdr *rii-t-fake-id*))
                            (retention (fn-node-retention *rii-t-paused-node*))
                            (id "archive-rii-2"))))))
(must-fail
 (defthm rii-t-ix-next-without-okp
   (fn-rii-okp *rii-t-still-wrong* *rii-t-paused-node*)))

; -----------------------------------------------------------------------------
; The host's calls run compiled code: every function it reaches is
; guard-verified.

(assert-event
 (and (eq (symbol-class 'fn-rii-sco-extend (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rii-sco-cpr-resume (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rii-sco-cpr-prefix (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rii-cpr-apply-event (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rii-apply-record (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rii-apply-retention-event (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rii-node-prepare (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rii-ix-next (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rii-classified-open (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rii-sco-store-open (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rii-sco-finalize-from (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rii-sn-statep (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rii-sf-statep (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rii-sf-record-listp (w state)) :common-lisp-compliant)))
