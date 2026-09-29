; store-finalize-carried-check.lisp -- the carried pair's invariant made
; decidable (row A9, item (2) of lane incremental-finalize-3; PRF-1005).
;
; The carried entries of books/store-finalize-incremental.lisp (PRF-968)
; take the pair (R . IX) under fn-sfi-cpr-carriedp: R paused, its node
; configured, IX under fn-rii-okp with it.  fn-rii-okp's second conjunct is
; a defun-sk (fn-rii-known-okp: for every string, the id trie answers what
; the retention ledger answers), so the invariant is a verified guard the
; evaluator cannot run: under guard checking a call errors ("cannot ev
; FN-RII-KNOWN-OKP"), and with guard checking :none the mbe :logic sides run
; and the tries are not consulted, so a wrong trie is invisible there.  ACL2
; also refuses an abstract stobj holding the pair (fn-cnode-statep reaches
; the attached fn-digest).  So the :program host keeps the obligation.
;
; This book gives the boundary a DECIDABLE check with three answers kept
; distinct (AGENTS: uncertain, refused and accepted):
;   :ok                  IX is exactly the rebuilt pair fn-rii-ix-of of the
;                        paused node -- fn-sfk-check-ok-is-carried: the
;                        invariant HOLDS (fn-rii-okp-of-ix-of);
;   :wrong-msgid-trie    IX's Message-ID trie is not the rebuilt one --
;                        fn-sfk-check-wrong-msgid-trie-is-not-carried: the
;                        invariant FAILS (fn-sfi-carried-msgid-trie-is-the-
;                        rebuilt-trie: under fn-rii-okp the Message-ID trie
;                        is canonical);
;   :not-paused, :node-not-configured, :not-a-pair -- the invariant FAILS by
;                        its own first conjuncts;
;   :uncertain-id-trie   the Message-ID trie is the rebuilt one and the id
;                        trie is not structurally the rebuilt one: fn-rii-okp
;                        is extensional there (fn-rii-known-okp), so this
;                        book decides NOTHING -- the check says so instead of
;                        guessing.
; The check is one node pass (fn-rii-ix-of) and is never on a served path:
; it is what a test, a tooth or an operator verb runs at the *1* boundary.
; The served path's reliance is the trust row A-CARRIED-PAIR
; (books/assumptions-publication.lisp): the pair a host carries across
; extensions is the one fn-sfi-carry / fn-sfi-extend-open-carried produced,
; which the preservation theorems keep carried.

(in-package "ACL2")

(include-book "store-finalize-incremental")

(defun fn-sfk-carried-check (r ix)
  (declare (xargs :guard t))
  (cond ((not (fn-sco-pausedp r)) :not-paused)
        ((not (fn-cnode-statep (fn-sco-at 1 r))) :node-not-configured)
        ((not (consp ix)) :not-a-pair)
        (t (let ((built (fn-rii-ix-of (fn-cnode-node (fn-sco-at 1 r)))))
             (cond ((not (equal (car ix) (car built))) :wrong-msgid-trie)
                   ((equal (cdr ix) (cdr built)) :ok)
                   (t :uncertain-id-trie))))))

(local
 (defthm fn-sfk-ix-of-is-a-cons
   (consp (fn-rii-ix-of node))
   :hints (("Goal" :in-theory (e/d (fn-rii-ix-of) (fn-mxc-build fn-rii-kbuild))))))

(local
 (defthm fn-sfk-pair-of-car-and-cdr
   (implies (and (consp ix) (consp built)
                 (equal (car ix) (car built))
                 (equal (cdr ix) (cdr built)))
            (equal ix built))
   :rule-classes nil))

; :ok establishes the invariant: the check's :ok is the three conjuncts with
; IX the rebuilt pair, and the rebuilt pair is under fn-rii-okp.
(defthm fn-sfk-check-ok-facts
  (implies (equal (fn-sfk-carried-check r ix) :ok)
           (and (fn-sco-pausedp r)
                (fn-cnode-statep (fn-sco-at 1 r))
                (equal ix (fn-rii-ix-of (fn-cnode-node (fn-sco-at 1 r))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-sfk-pair-of-car-and-cdr
                            (built (fn-rii-ix-of (fn-cnode-node (fn-sco-at 1 r))))))
           :in-theory (e/d (fn-sfk-carried-check)
                           (fn-rii-ix-of fn-cnode-statep fn-sco-pausedp fn-sco-at
                            fn-cnode-node)))))

(defthm fn-sfk-check-ok-is-carried
  (implies (equal (fn-sfk-carried-check r ix) :ok)
           (fn-sfi-cpr-carriedp r ix))
  :hints (("Goal" :do-not-induct t
           :use (fn-sfk-check-ok-facts
                 (:instance fn-rii-okp-of-ix-of
                            (node (fn-cnode-node (fn-sco-at 1 r)))))
           :in-theory (e/d (fn-sfi-cpr-carriedp)
                           (fn-sfk-carried-check fn-rii-okp fn-rii-ix-of fn-cnode-statep
                            fn-sco-pausedp fn-sco-at fn-cnode-node fn-rii-okp-of-ix-of)))))

; :wrong-msgid-trie refutes it.
(defthm fn-sfk-check-wrong-msgid-trie-is-not-carried
  (implies (equal (fn-sfk-carried-check r ix) :wrong-msgid-trie)
           (not (fn-sfi-cpr-carriedp r ix)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-sfi-carried-msgid-trie-is-the-rebuilt-trie
                            (node (fn-cnode-node (fn-sco-at 1 r)))))
           :in-theory (e/d (fn-sfk-carried-check fn-sfi-cpr-carriedp)
                           (fn-rii-okp fn-rii-ix-of fn-cnode-statep fn-sco-pausedp
                            fn-sco-at fn-cnode-node
                            fn-sfi-carried-msgid-trie-is-the-rebuilt-trie)))))

; The three shape answers refute it by the invariant's own conjuncts.
(defthm fn-sfk-check-shape-answers-are-not-carried
  (implies (member-equal (fn-sfk-carried-check r ix)
                         '(:not-paused :node-not-configured :not-a-pair))
           (not (fn-sfi-cpr-carriedp r ix)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-sfk-carried-check fn-sfi-cpr-carriedp fn-rii-okp)
                                  (fn-rii-ix-of fn-cnode-statep fn-sco-pausedp
                                   fn-sco-at fn-cnode-node fn-rii-known-okp
                                   fn-midx-build)))))

; The open's own pair checks :ok: what fn-sfi-carry builds is the rebuilt pair.
(defthm fn-sfk-carry-checks-ok
  (implies (fn-sfi-carry c)
           (equal (fn-sfk-carried-check (fn-sco-cpr c) (fn-sfi-carry c)) :ok))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-sfk-carried-check fn-sfi-carry)
                                  (fn-rii-ix-of fn-cnode-statep fn-sco-pausedp
                                   fn-sco-at fn-cnode-node fn-sco-cpr)))))

(in-theory (disable fn-sfk-carried-check))
