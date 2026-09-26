; Teeth for PRF-173 (served-path-scale).  Part 1: the one-pass :exec paths the
; whole-node recognizer runs at every Store open, `fn-articles-freshp'
; (books/acceptance.lisp, exec `fn-fr-freshp') and
; `fn-node-articles-have-archive-bindingsp' (books/node.lisp, exec
; `fn-nab-articles-boundp').
;
; The refinements `fn-articles-freshp-is-one-pass' and
; `fn-node-articles-have-archive-bindingsp-is-indexed' have no hypothesis, so
; the teeth are witnesses: the recognizer, evaluated (its guard-verified
; :exec path), agrees with a reference that is the quadratic :logic body
; copied with guards unverified, on a node the transitions reach (twelve
; committed articles) and on corrupted states built from it (labelled
; CORRUPTED: no transition produces them; the open meets them only in bytes
; it did not write).  Last, the executed functions are shown not to reach the
; quadratic walks: the statement about the executed function.
(in-package "ACL2")
(include-book "../../books/owner")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; References: the :logic bodies, copied.

(defun opt-all-memberships (articles)
  (declare (xargs :verify-guards nil))
  (if (consp articles)
      (append (fn-article-memberships (car articles))
              (opt-all-memberships (cdr articles)))
    nil))

(defun opt-conflictsp (ms articles)
  (declare (xargs :verify-guards nil))
  (if (consp ms)
      (or (fn-pair-memberp (car ms) (opt-all-memberships articles))
          (opt-conflictsp (cdr ms) articles))
    nil))

(defun opt-freshp (articles)
  (declare (xargs :verify-guards nil))
  (if (consp articles)
      (and (not (opt-conflictsp (fn-article-memberships (car articles))
                                (cdr articles)))
           (opt-freshp (cdr articles)))
    t))

(defun opt-bindingsp (articles bindings pins)
  (declare (xargs :verify-guards nil))
  (if (consp articles)
      (let ((binding (fn-node-find-binding (fn-article-msgid (car articles))
                                           bindings)))
        (and (consp binding)
             (fn-retain-matching-releasep
              (fn-retain-find-id (fn-node-binding-id binding) pins)
              (fn-node-binding-id binding)
              (fn-node-binding-subject binding)
              :archive
              (fn-retain-obligation-evidence
               (fn-retain-find-id (fn-node-binding-id binding) pins)))
             (opt-bindingsp (cdr articles) bindings pins)))
    t))

; -----------------------------------------------------------------------------
; A reachable node: twelve articles committed through fn-node-prepare and
; fn-node-complete, each in both groups.

(defconst *opt-groups* '("fn.letters" "fn.test"))
(defconst *opt-keys* '("a" "b" "c" "d" "e" "f" "g" "h" "i" "j" "k" "l"))

(defun opt-commit-all (s keys txid)
  (declare (xargs :verify-guards nil))
  (if (consp keys)
      (opt-commit-all
       (fn-node-complete
        (fn-node-prepare s 9 (concatenate 'string "<" (car keys) "@example.invalid>")
                         '(72 105 13 10) *opt-groups*
                         (concatenate 'string "archive-" (car keys))
                         (concatenate 'string "content-" (car keys))
                         (concatenate 'string "release-" (car keys))
                         1 841000000)
        txid 9 :durable)
       (cdr keys) (+ 1 txid))
    s))

(defconst *opt-node*
  (opt-commit-all (fn-node-initial-state *opt-groups* 1000) *opt-keys* 0))
(defconst *opt-articles* (fn-state-articles (fn-node-acceptance *opt-node*)))
(defconst *opt-bindings* (fn-node-bindings *opt-node*))
(defconst *opt-pins* (fn-retain-pins (fn-node-retention *opt-node*)))

; Reachable positive witness: all twelve committed, the node a node, both
; relations hold on the executed path and on the references.
(assert-event (equal (len *opt-articles*) 12))
(assert-event (equal (len *opt-bindings*) 12))
(assert-event (equal (len *opt-pins*) 12))
(assert-event (equal (len (opt-all-memberships *opt-articles*)) 24))
(assert-event (fn-node-statep *opt-node*))
(assert-event (equal (fn-articles-freshp *opt-articles*) t))
(assert-event (equal (fn-fr-freshp *opt-articles*) t))
(assert-event (equal (opt-freshp *opt-articles*) t))
(assert-event (equal (fn-node-articles-have-archive-bindingsp
                      *opt-articles* *opt-bindings* *opt-pins*) t))
(assert-event (equal (fn-nab-articles-boundp
                      *opt-articles* *opt-bindings* *opt-pins*) t))
(assert-event (equal (opt-bindingsp *opt-articles* *opt-bindings* *opt-pins*) t))

; -----------------------------------------------------------------------------
; CORRUPTED states: each fails on both paths, and the node recognizer refuses.

; The first article again at the end: its memberships meet their twin eleven
; articles later.
(defconst *opt-articles-dup* (append *opt-articles* (list (car *opt-articles*))))
(assert-event (equal (fn-articles-freshp *opt-articles-dup*) nil))
(assert-event (equal (fn-fr-freshp *opt-articles-dup*) nil))
(assert-event (equal (opt-freshp *opt-articles-dup*) nil))

; One membership shared by two articles six apart, the other memberships
; distinct: fails on one pair only.
(defun opt-with-memberships (article ms)
  (declare (xargs :verify-guards nil))
  (fn-make-article (fn-article-msgid article) (fn-article-payload article)
                   (fn-article-groups article) ms
                   (fn-article-pin article) (fn-article-stamp article)))
(defconst *opt-one-shared*
  (list (opt-with-memberships (nth 0 *opt-articles*) '(("fn.test" . 1)))
        (opt-with-memberships (nth 1 *opt-articles*) '(("fn.test" . 2)))
        (opt-with-memberships (nth 2 *opt-articles*) '(("fn.test" . 3)))
        (opt-with-memberships (nth 3 *opt-articles*) '(("fn.test" . 4)))
        (opt-with-memberships (nth 4 *opt-articles*) '(("fn.test" . 5)))
        (opt-with-memberships (nth 5 *opt-articles*) '(("fn.test" . 6)))
        (opt-with-memberships (nth 6 *opt-articles*) '(("fn.letters" . 9) ("fn.test" . 1)))))
(assert-event (equal (fn-articles-freshp *opt-one-shared*) nil))
(assert-event (equal (opt-freshp *opt-one-shared*) nil))
(assert-event (equal (fn-articles-freshp (butlast *opt-one-shared* 1)) t))
(assert-event (equal (opt-freshp (butlast *opt-one-shared* 1)) t))

; The relation's own edges, kept by the one pass: a membership repeated inside
; ONE article is not a conflict (an article is checked against the others,
; never itself), and equal non-cons elements are not memberships.
(defconst *opt-self-twice*
  (list (opt-with-memberships (nth 0 *opt-articles*) '(("fn.test" . 1) ("fn.test" . 1)))))
(assert-event (equal (fn-articles-freshp *opt-self-twice*) t))
(assert-event (equal (opt-freshp *opt-self-twice*) t))
(defconst *opt-atoms*
  (list (opt-with-memberships (nth 0 *opt-articles*) '(7 "x"))
        (opt-with-memberships (nth 1 *opt-articles*) '(7 "x"))))
(assert-event (equal (fn-articles-freshp *opt-atoms*) t))
(assert-event (equal (opt-freshp *opt-atoms*) t))

; A pin released from the ledger (the sixth): its article has no archive pin.
(defconst *opt-pins-less* (append (take 5 *opt-pins*) (nthcdr 6 *opt-pins*)))
(assert-event (equal (fn-node-articles-have-archive-bindingsp
                      *opt-articles* *opt-bindings* *opt-pins-less*) nil))
(assert-event (equal (opt-bindingsp *opt-articles* *opt-bindings* *opt-pins-less*) nil))

; A binding dropped: its article is unbound.
(defconst *opt-bindings-less* (cdr *opt-bindings*))
(assert-event (equal (fn-node-articles-have-archive-bindingsp
                      *opt-articles* *opt-bindings-less* *opt-pins*) nil))
(assert-event (equal (opt-bindingsp *opt-articles* *opt-bindings-less* *opt-pins*) nil))

; The FIRST binding of a Message-ID decides (the linear search's answer): a
; wrong-subject binding for an article's Message-ID placed before its good
; binding fails; placed after it, it is never consulted.
(defconst *opt-bad-binding*
  (fn-node-make-binding (fn-node-binding-msgid (nth 3 *opt-bindings*))
                        "another-subject"
                        (fn-node-binding-id (nth 3 *opt-bindings*))))
(assert-event (equal (fn-node-articles-have-archive-bindingsp
                      *opt-articles* (cons *opt-bad-binding* *opt-bindings*) *opt-pins*)
                     nil))
(assert-event (equal (opt-bindingsp *opt-articles* (cons *opt-bad-binding* *opt-bindings*)
                                    *opt-pins*)
                     nil))
(assert-event (equal (fn-node-articles-have-archive-bindingsp
                      *opt-articles* (append *opt-bindings* (list *opt-bad-binding*))
                      *opt-pins*)
                     t))
(assert-event (equal (opt-bindingsp *opt-articles*
                                    (append *opt-bindings* (list *opt-bad-binding*))
                                    *opt-pins*)
                     t))
; The same for pins: a pin with the binding's identity but another subject
; placed first fails; placed last, it is never consulted.
(defconst *opt-bad-pin*
  (fn-retain-make-obligation (fn-retain-obligation-id (nth 4 *opt-pins*))
                             "another-subject" :archive
                             (fn-retain-obligation-evidence (nth 4 *opt-pins*))
                             1))
(assert-event (equal (fn-node-articles-have-archive-bindingsp
                      *opt-articles* *opt-bindings* (cons *opt-bad-pin* *opt-pins*))
                     nil))
(assert-event (equal (opt-bindingsp *opt-articles* *opt-bindings*
                                    (cons *opt-bad-pin* *opt-pins*))
                     nil))
(assert-event (equal (fn-node-articles-have-archive-bindingsp
                      *opt-articles* *opt-bindings* (append *opt-pins* (list *opt-bad-pin*)))
                     t))

; The corrupted node: the node recognizer refuses the duplicated articles.
(assert-event
 (not (fn-node-statep
       (fn-node-make-state
        (fn-make-state *opt-groups* (fn-state-nexts (fn-node-acceptance *opt-node*))
                       *opt-one-shared* (fn-state-next-txid (fn-node-acceptance *opt-node*))
                       nil nil)
        (fn-node-retention *opt-node*) nil *opt-bindings*))))

; -----------------------------------------------------------------------------
; The executed functions: the :exec branch of each recognizer is the one-pass
; function, and no function the one pass calls reaches the quadratic walks.

(defun opt-exec-branch (fn wrld)
  (declare (xargs :mode :program))
  (let ((body (getpropc fn 'unnormalized-body nil wrld)))
    (and (consp body) (eq (car body) 'return-last)
         (equal (cadr body) ''mbe1-raw)
         (caddr body))))

(assert-event (equal (opt-exec-branch 'fn-articles-freshp (w state))
                     '(fn-fr-freshp articles)))
(assert-event (equal (opt-exec-branch 'fn-node-articles-have-archive-bindingsp (w state))
                     '(fn-nab-articles-boundp articles bindings pins)))

(defun opt-callees (fns wrld seen)
  (declare (xargs :mode :program))
  (if (endp fns)
      seen
    (if (member-eq (car fns) seen)
        (opt-callees (cdr fns) wrld seen)
      (let ((body (getpropc (car fns) 'unnormalized-body nil wrld)))
        (opt-callees (append (all-fnnames body) (cdr fns)) wrld
                     (cons (car fns) seen))))))

(defconst *opt-quadratic*
  '(fn-all-article-memberships fn-memberships-conflictsp fn-pair-memberp
    fn-node-find-binding fn-retain-find-id member-equal))

(assert-event (not (intersectp-eq (opt-callees '(fn-fr-freshp) (w state) nil)
                                  *opt-quadratic*)))
(assert-event (not (intersectp-eq (opt-callees '(fn-nab-articles-boundp) (w state) nil)
                                  *opt-quadratic*)))

; -----------------------------------------------------------------------------
; Part 2: the group index extended at refresh, fn-gidx-refresh-is-build
; (books/owner.lisp; fn-own-refresh passes the old view's group index, the old
; visible articles and the new ones).  One hypothesis: the old index is the
; build of the old articles, or there is none.

(defconst *opt-old* (cdr *opt-articles*))
(defconst *opt-old-index* (fn-gidx-build *opt-old*))

; Reachable witness: one acceptance grew the visible list by one article at
; its head; the hypothesis holds; the extension branch runs (the put of the
; new article's two entries onto the old index) and equals the rebuild.
(assert-event (equal (cdr *opt-articles*) *opt-old*))
(assert-event (consp *opt-old-index*))
(assert-event (equal *opt-old-index* (fn-gidx-build *opt-old*)))
(assert-event (equal (fn-gidx-refresh *opt-old-index* *opt-old* *opt-articles*)
                     (fn-gidx-put-all (fn-index-article-entries (car *opt-articles*))
                                      *opt-old-index*)))
(assert-event (equal (len (fn-index-article-entries (car *opt-articles*))) 2))
(assert-event (equal (fn-gidx-refresh *opt-old-index* *opt-old* *opt-articles*)
                     (fn-gidx-build *opt-articles*)))
; No change, and no index: the other two branches keep the conclusion.
(assert-event (equal (fn-gidx-refresh *opt-old-index* *opt-old* *opt-old*)
                     (fn-gidx-build *opt-old*)))
(assert-event (equal (fn-gidx-refresh nil *opt-old* *opt-articles*)
                     (fn-gidx-build *opt-articles*)))

; Hypothesis removed: a stale index (the build of a shorter prefix, not of the
; old articles) extended by one article is not the build of the new list.
(defconst *opt-stale-index* (fn-gidx-build (cddr *opt-articles*)))
(assert-event (not (equal *opt-stale-index* (fn-gidx-build *opt-old*))))
(assert-event (not (equal (fn-gidx-refresh *opt-stale-index* *opt-old* *opt-articles*)
                          (fn-gidx-build *opt-articles*))))
(must-fail
 (thm (equal (fn-gidx-refresh buckets old-articles new-articles)
             (fn-gidx-build new-articles))))

; -----------------------------------------------------------------------------
; Part 3: the admission's identity test, fn-retain-known-id-scanp-is-known-idp
; (books/retention.lisp; fn-retain-admissiblep's :exec runs the scan).  No
; hypothesis: witnesses on the reachable ledger of the twelve-article node.

(defconst *opt-ledger* (fn-node-retention *opt-node*))
(assert-event (equal (len (fn-retain-pins *opt-ledger*)) 12))
; Known: an archive identity the node committed; unknown: a fresh one.
(assert-event (fn-retain-known-id-scanp "archive-f" (fn-retain-pins *opt-ledger*)
                                        (fn-retain-releases *opt-ledger*)))
(assert-event (fn-retain-known-idp "archive-f" (fn-retain-pins *opt-ledger*)
                                   (fn-retain-releases *opt-ledger*)))
(assert-event (not (fn-retain-known-id-scanp "archive-z" (fn-retain-pins *opt-ledger*)
                                             (fn-retain-releases *opt-ledger*))))
(assert-event (not (fn-retain-known-idp "archive-z" (fn-retain-pins *opt-ledger*)
                                        (fn-retain-releases *opt-ledger*))))
; The admission the host runs refuses the known identity and admits the fresh
; one, through the scan.
(assert-event (not (fn-retain-admissiblep *opt-ledger* "archive-f" "content-z" :archive
                                          "release-z" 1)))
(assert-event (fn-retain-admissiblep *opt-ledger* "archive-z" "content-z" :archive
                                     "release-z" 1))
(assert-event (not (intersectp-eq (opt-callees '(fn-retain-known-id-scanp) (w state) nil)
                                  '(fn-retain-obligation-ids fn-retain-release-ids
                                    member-equal))))
