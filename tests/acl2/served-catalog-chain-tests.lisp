; served-catalog-chain-tests.lisp -- teeth for books/served-catalog-chain.lisp
; (step 8 of the catalog slice).
;
; What is asserted: (1) the view a pinned version names, with and without
; non-article records between the rows (fn-scr-view-of); (2) the lifted
; dispatcher agrees with the pinned one on a reachable command over a
; catalog whose view IS the pinned archive, and disagrees when it is not
; (the view hypothesis of fn-scr-catalogp is not idle); (3) every layer is
; guard-verified; (4) the keystone needs each of its hypotheses.
;
; The fixture is the served-catalog tests' (tests/acl2/served-catalog-tests.
; lisp): three wire records in fn.test / fn.other, their payloads as the
; arena's logical value, the rows as fn-cat-load assigns them.

(in-package "ACL2")

(include-book "../../books/served-catalog-chain")
(include-book "must-fail-checked")

(defconst *scct-p0* (append (fn-record-string-octets "Subject: a") '(13 10 13 10 65 13 10)))
(defconst *scct-p1* (append (fn-record-string-octets "Subject: b") '(13 10 13 10 66 13 10)))
(defconst *scct-p2* (append (fn-record-string-octets "Subject: c") '(13 10 13 10 67 13 10)))

;; A held row from a wire record and its arena handle (numbers by
;; fn-cat-assign, as fn-cat-load assigns them).
(defun scct-held (w handle numbers)
  (fn-held-make (fn-record-sequence w) (fn-record-txid w) (fn-record-generation w)
                (fn-record-msgid w) handle (fn-record-groups w) (fn-record-obligation-id w)
                (fn-record-content-subject w) (fn-record-release-evidence w)
                (fn-record-charge w) (fn-record-stamp w)
                (fn-held-facts-of (fn-record-payload w))
                (fn-held-context-of (fn-record-payload w) nil 0) numbers nil))

(defun scct-catalog (ws handle c)
  (if (consp ws)
      (scct-catalog (cdr ws) (+ 1 handle)
                    (append c (list (fn-cat-assign (scct-held (car ws) handle nil) c))))
    c))

;; Consecutive record sequences 0, 1, 2: the history holds articles only.
(defconst *scct-w0* (fn-record-make 0 1 1 "<a@x>" *scct-p0* '("fn.test") "o" "s" "e" 1 5))
(defconst *scct-w1* (fn-record-make 1 2 2 "<b@x>" *scct-p1* '("fn.test" "fn.other") "o" "s" "e" 1 5))
(defconst *scct-w2* (fn-record-make 2 3 3 "<c@x>" *scct-p2* '("fn.test") "o" "s" "e" 1 5))
(defconst *scct-a* (list *scct-p0* *scct-p1* *scct-p2*))
(defconst *scct-c* (scct-catalog (list *scct-w0* *scct-w1* *scct-w2*) 0 nil))

;; Sequences 0, 2, 5: non-article records at 1, 3 and 4 (a group
;; declaration, a configuration record, a verdict) stand between the rows.
(defconst *scct-g0* (fn-record-make 0 1 1 "<a@x>" *scct-p0* '("fn.test") "o" "s" "e" 1 5))
(defconst *scct-g1* (fn-record-make 2 3 2 "<b@x>" *scct-p1* '("fn.test" "fn.other") "o" "s" "e" 1 5))
(defconst *scct-g2* (fn-record-make 5 6 3 "<c@x>" *scct-p2* '("fn.test") "o" "s" "e" 1 5))
(defconst *scct-cg* (scct-catalog (list *scct-g0* *scct-g1* *scct-g2*) 0 nil))

;; (1) The view of a pinned version: the rows whose sequence is below it.
(defthm scct-view-of-consecutive
  (and (equal (fn-scr-view-of 0 *scct-c*) 0)
       (equal (fn-scr-view-of 1 *scct-c*) 1)
       (equal (fn-scr-view-of 2 *scct-c*) 2)
       (equal (fn-scr-view-of 3 *scct-c*) 3)
       (equal (fn-scr-view-of 7 *scct-c*) 3)
       (equal (fn-scr-view-of 0 nil) 0)
       (equal (fn-scr-view-of 5 nil) 0))
  :rule-classes nil)

(defthm scct-view-of-with-gaps
  (and (equal (fn-scr-view-of 0 *scct-cg*) 0)
       (equal (fn-scr-view-of 1 *scct-cg*) 1)   ; the record at 1 is not a row
       (equal (fn-scr-view-of 2 *scct-cg*) 1)
       (equal (fn-scr-view-of 3 *scct-cg*) 2)
       (equal (fn-scr-view-of 5 *scct-cg*) 2)
       (equal (fn-scr-view-of 6 *scct-cg*) 3)
       (equal (fn-scr-view-of 100 *scct-cg*) 3))
  :rule-classes nil)

;; (2) The lifted dispatcher on a reachable command.  The pinned archive is
;; the view at 3 (every row), its index the pin built from those articles.
;; Macros: a theorem may name the arena's and the catalog's logical values
;; where the stobjs are required; a function may not.
(defmacro scct-arch (v)
  `(fn-make-state '("fn.test" "fn.other") '(("fn.test" . 4) ("fn.other" . 2))
                  (fn-cat-view-articles ,v *scct-a* *scct-c*) 0 nil nil))

(defmacro scct-index (v)
  `(fn-gidx-pin (fn-midx-build (fn-cat-view-articles ,v *scct-a* *scct-c*))
                (fn-gidx-build (fn-cat-view-articles ,v *scct-a* *scct-c*))))

;; An open, projected session in fn.test; command lines are octets, tokens
;; the tokenizer's (books/nntp-session.lisp).
(defconst *scct-session* (fn-nntp-make-session t "fn.test" nil t))
(defmacro scct-tokens (line) `(fn-nntp-tokenize (fn-nntp-string-octets ,line)))

(defthm scct-command-agrees-at-the-pinned-view
  (let ((arch (scct-arch 3)) (index (scct-index 3)))
    (and ;; the hypothesis, conjunct by conjunct
         (equal (fn-state-articles arch) (fn-cat-view-articles 3 *scct-a* *scct-c*))
         (fn-statep arch)
         (fn-gidx-pin-correspondencep index arch)
         (fn-midx-correspondencep (fn-gidx-pin-trie index) (fn-state-articles arch))
         (fn-cnx-freshp *scct-c*)
         ;; the article at number 3 by the catalog is the pinned reply, a 220
         (equal (fn-scr-command *scct-session* arch index nil nil (scct-tokens "ARTICLE 3") 3 *scct-a* *scct-c*)
                (fn-nntp-command-pinned *scct-session* arch index nil nil (scct-tokens "ARTICLE 3") *scct-a*))
         ;; the effect is (:reply octets); the reply's first octets are "220"
         (equal (take 3 (cadr (car (fn-nntp-result-effects
                                    (fn-scr-command *scct-session* arch index nil nil (scct-tokens "ARTICLE 3")
                                                    3 *scct-a* *scct-c*)))))
                (list 50 50 48))
         ;; STAT by Message-ID
         (equal (fn-scr-command *scct-session* arch index nil nil (scct-tokens "STAT <b@x>") 3 *scct-a* *scct-c*)
                (fn-nntp-command-pinned *scct-session* arch index nil nil (scct-tokens "STAT <b@x>") *scct-a*))))
  :rule-classes nil)

;; OVER over a range (lane join-f2-12): the catalog's step answers a CURSOR
;; (the range's lines are built one window at a time by the host,
;; books/over-window.lisp), so fn-scr-command-is-command-pinned equates the
;; results' sessions and their EXPANDED effects (fn-ovw-expand).  The
;; witness asserts that complete conclusion, and its teeth: the step's one
;; effect is the cursor, the two results differ literally, the expansion is
;; the pinned side's reply itself (which carries no cursor), and that reply
;; is the 224 block.
(defthm scct-over-range-answers-a-cursor
  (let* ((arch (scct-arch 3)) (index (scct-index 3))
         (cat (fn-scr-command *scct-session* arch index nil nil (scct-tokens "OVER 1-3") 3 *scct-a* *scct-c*))
         (pinned (fn-nntp-command-pinned *scct-session* arch index nil nil (scct-tokens "OVER 1-3") *scct-a*)))
    (and ;; the hypothesis, conjunct by conjunct (fn-scr-catalogp is a
         ;; defun-nx: its conjuncts, as scct-command-agrees-at-the-pinned-view
         ;; states them)
         (equal (fn-state-articles arch) (fn-cat-view-articles 3 *scct-a* *scct-c*))
         (fn-statep arch)
         (fn-gidx-pin-correspondencep index arch)
         (fn-midx-correspondencep (fn-gidx-pin-trie index) (fn-state-articles arch))
         (fn-cnx-freshp *scct-c*)
         ;; the conclusion
         (equal (fn-nntp-result-session cat) (fn-nntp-result-session pinned))
         (equal (fn-ovw-expand (fn-nntp-result-effects cat) *scct-a* *scct-c*)
                (fn-ovw-expand (fn-nntp-result-effects pinned) *scct-a* *scct-c*))
         ;; teeth
         (fn-ovw-cursor-effectp (car (fn-nntp-result-effects cat)))
         (null (cdr (fn-nntp-result-effects cat)))
         (not (equal cat pinned))
         (equal (fn-ovw-expand (fn-nntp-result-effects cat) *scct-a* *scct-c*)
                (fn-nntp-result-effects pinned))
         (equal (take 3 (cadr (car (fn-nntp-result-effects pinned)))) (list 50 50 52))
         (< 3 (len (fn-nntp-result-effects (fn-ovw-expand-result cat *scct-a* *scct-c*))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ovw-expand fn-ovw-expand-result fn-ovw-cursor-effectp
                                     fn-ovw-cursor-octets fn-ovw-lines fn-ovw-reply fn-ovw-status
                                     fn-ovw-empty-text fn-ovw-cursor))))

;; The view hypothesis has teeth: the same archive served at the view the
;; pin does NOT name (view 2 lacks the third row) answers ARTICLE 3
;; differently.
(defthm scct-command-differs-off-the-view
  (let ((arch (scct-arch 3)) (index (scct-index 3)))
    (and (not (equal (fn-state-articles arch) (fn-cat-view-articles 2 *scct-a* *scct-c*)))
         (not (equal (fn-scr-command *scct-session* arch index nil nil (scct-tokens "ARTICLE 3")
                                     2 *scct-a* *scct-c*)
                     (fn-nntp-command-pinned *scct-session* arch index nil nil (scct-tokens "ARTICLE 3") *scct-a*)))))
  :rule-classes nil)

;; (3) Every layer the host reaches is guard-verified.
(assert-event
 (equal (list (symbol-class 'fn-scr-view-of (w state))
              (symbol-class 'fn-scr-command (w state))
              (symbol-class 'fn-scr-step (w state))
              (symbol-class 'fn-scr-post-step (w state))
              (symbol-class 'fn-scr-peer-delegate (w state))
              (symbol-class 'fn-scr-peer-step (w state))
              (symbol-class 'fn-scr-auth-delegate (w state))
              (symbol-class 'fn-scr-auth-step (w state))
              (symbol-class 'fn-scr-dispatch-core (w state))
              (symbol-class 'fn-scr-dispatch (w state))
              (symbol-class 'fn-scr-dispatch-events (w state))
              (symbol-class 'fn-scr-feed-byte (w state))
              (symbol-class 'fn-scr-feed-span (w state))
              (symbol-class 'fn-scr-step-span-fast (w state))
              (symbol-class 'fn-scr-own-read-span (w state))
              (symbol-class 'fn-scr-ocfg-read-span (w state)))
        (make-list 16 :initial-element :common-lisp-compliant)))

;; (4) The keystone needs each hypothesis (as tests/acl2/served-span-tests.lisp
;; states them for the carried read).  Each attempt runs in the keystone and
;; the minimal theory, where the complete statement proves (the control
;; below): what fails is the keystone's use without the hypothesis.
(defthm scct-read-span-control
  (implies (and (fn-ocl-relation oc)
                (fn-scar-view-indexedp (fn-ocfg-owner oc))
                (fn-scr-owner-catalogp (fn-ocfg-owner oc) id fn-arena fn-cat)
                (fn-scol-okp fn-arena fn-cat) (fn-gacc-okp cache)
                (natp i) (natp end))
           (equal (fn-scr-ocfg-read-span oc id i end cache fn-octets fn-arena fn-cat)
                  (fn-ocfg-read-tls-prefix oc id (fn-oct-slice-list i end fn-octets) fn-arena)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-scr-ocfg-read-span-is-reference-under-ocl-relation)
                                      (theory 'minimal-theory)))))

(must-fail-checked
 (defthm scct-read-span-needs-ocl-relation
   (implies (and (fn-scar-view-indexedp (fn-ocfg-owner oc))
                 (fn-scr-owner-catalogp (fn-ocfg-owner oc) id fn-arena fn-cat)
                 (fn-scol-okp fn-arena fn-cat) (fn-gacc-okp cache)
                 (natp i) (natp end))
            (equal (fn-scr-ocfg-read-span oc id i end cache fn-octets fn-arena fn-cat)
                   (fn-ocfg-read-tls-prefix oc id (fn-oct-slice-list i end fn-octets) fn-arena)))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories '(fn-scr-ocfg-read-span-is-reference-under-ocl-relation)
                                       (theory 'minimal-theory))))))

(must-fail-checked
 (defthm scct-read-span-needs-view-indexedp
   (implies (and (fn-ocl-relation oc)
                 (fn-scr-owner-catalogp (fn-ocfg-owner oc) id fn-arena fn-cat)
                 (fn-scol-okp fn-arena fn-cat) (fn-gacc-okp cache)
                 (natp i) (natp end))
            (equal (fn-scr-ocfg-read-span oc id i end cache fn-octets fn-arena fn-cat)
                   (fn-ocfg-read-tls-prefix oc id (fn-oct-slice-list i end fn-octets) fn-arena)))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories '(fn-scr-ocfg-read-span-is-reference-under-ocl-relation)
                                       (theory 'minimal-theory))))))

;; Without the overview column's premise F (lane served-columns): the
;; dispatcher's OVER/HDR arms read the rows' columns, so the keystone is not
;; usable without it.
(must-fail-checked
 (defthm scct-read-span-needs-the-overview-column
   (implies (and (fn-ocl-relation oc)
                 (fn-scar-view-indexedp (fn-ocfg-owner oc))
                 (fn-scr-owner-catalogp (fn-ocfg-owner oc) id fn-arena fn-cat)
                 (fn-gacc-okp cache)
                 (natp i) (natp end))
            (equal (fn-scr-ocfg-read-span oc id i end cache fn-octets fn-arena fn-cat)
                   (fn-ocfg-read-tls-prefix oc id (fn-oct-slice-list i end fn-octets) fn-arena)))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories '(fn-scr-ocfg-read-span-is-reference-under-ocl-relation)
                                       (theory 'minimal-theory))))))

;; PKT-643: without the access cache's invariant (books/group-access-cache.lisp
;; fn-gacc-okp, which the host keeps: fn-gacc-okp-of-nil and
;; fn-gacc-prepare-keeps-okp), a restricted session's commands would read a
;; view the cache merely claims.
(must-fail-checked
 (defthm scct-read-span-needs-the-access-cache
   (implies (and (fn-ocl-relation oc)
                 (fn-scar-view-indexedp (fn-ocfg-owner oc))
                 (fn-scr-owner-catalogp (fn-ocfg-owner oc) id fn-arena fn-cat)
                 (fn-scol-okp fn-arena fn-cat)
                 (natp i) (natp end))
            (equal (fn-scr-ocfg-read-span oc id i end cache fn-octets fn-arena fn-cat)
                   (fn-ocfg-read-tls-prefix oc id (fn-oct-slice-list i end fn-octets) fn-arena)))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories '(fn-scr-ocfg-read-span-is-reference-under-ocl-relation)
                                       (theory 'minimal-theory))))))

(must-fail-checked
 (defthm scct-read-span-needs-the-catalog-relation
   (implies (and (fn-ocl-relation oc)
                 (fn-scar-view-indexedp (fn-ocfg-owner oc))
                 (fn-scol-okp fn-arena fn-cat) (fn-gacc-okp cache)
                 (natp i) (natp end))
            (equal (fn-scr-ocfg-read-span oc id i end cache fn-octets fn-arena fn-cat)
                   (fn-ocfg-read-tls-prefix oc id (fn-oct-slice-list i end fn-octets) fn-arena)))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories '(fn-scr-ocfg-read-span-is-reference-under-ocl-relation)
                                       (theory 'minimal-theory))))))

(must-fail-checked
 (defthm scct-read-span-needs-natp-start
   (implies (and (fn-ocl-relation oc)
                 (fn-scar-view-indexedp (fn-ocfg-owner oc))
                 (fn-scr-owner-catalogp (fn-ocfg-owner oc) id fn-arena fn-cat)
                 (fn-scol-okp fn-arena fn-cat) (fn-gacc-okp cache)
                 (natp end))
            (equal (fn-scr-ocfg-read-span oc id i end cache fn-octets fn-arena fn-cat)
                   (fn-ocfg-read-tls-prefix oc id (fn-oct-slice-list i end fn-octets) fn-arena)))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories '(fn-scr-ocfg-read-span-is-reference-under-ocl-relation)
                                       (theory 'minimal-theory))))))

(must-fail-checked
 (defthm scct-read-span-needs-natp-end
   (implies (and (fn-ocl-relation oc)
                 (fn-scar-view-indexedp (fn-ocfg-owner oc))
                 (fn-scr-owner-catalogp (fn-ocfg-owner oc) id fn-arena fn-cat)
                 (fn-scol-okp fn-arena fn-cat) (fn-gacc-okp cache)
                 (natp i))
            (equal (fn-scr-ocfg-read-span oc id i end cache fn-octets fn-arena fn-cat)
                   (fn-ocfg-read-tls-prefix oc id (fn-oct-slice-list i end fn-octets) fn-arena)))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories '(fn-scr-ocfg-read-span-is-reference-under-ocl-relation)
                                       (theory 'minimal-theory))))))

; -----------------------------------------------------------------------------
; PKT-479 on the catalog path (catalog-columns, 2026-09-27):
; fn-scr-scan-span-is-feed-span, the scan fn-scr-step-span-core runs as the
; executable of the byte fold.  No hypothesis, so no must-fail: the witness
; runs the executable scan on a live buffer and catalog, as the host runs it,
; against the byte fold, over every sub-range a socket read can cut (every
; start with the read running to the end, every end with the read starting
; at 0), on served-scan-tests' reader connection and its DATE and two
; pipelined POSTs; and the host's step, which yields after the first article
; (PKT-600).

(include-book "served-scan-tests")

(assert-event
 (equal (list (symbol-class 'fn-scr-scan-span (w state))
              (symbol-class 'fn-scr-step-span-core (w state)))
        '(:common-lisp-compliant :common-lisp-compliant)))

(defun scct-scan-agree (conn i end fn-octets fn-arena fn-cat)
  (declare (xargs :stobjs (fn-octets fn-arena fn-cat) :verify-guards nil))
  (equal (fn-scr-scan-span conn i end nil nil nil nil nil fn-octets fn-arena fn-cat)
         (fn-scr-feed-span conn i end nil nil nil nil nil fn-octets fn-arena fn-cat)))

(defun scct-scan-cuts (conn cut n fn-octets fn-arena fn-cat)
  (declare (xargs :stobjs (fn-octets fn-arena fn-cat) :verify-guards nil
                  :measure (nfix (- (1+ n) cut))))
  (if (or (not (natp cut)) (not (natp n)) (> cut n))
      t
    (and (scct-scan-agree conn 0 cut fn-octets fn-arena fn-cat)
         (scct-scan-agree conn cut n fn-octets fn-arena fn-cat)
         (scct-scan-cuts conn (1+ cut) n fn-octets fn-arena fn-cat))))

(defun scct-scan-all (conn octets)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (v fn-arena)
      (with-local-stobj fn-cat
        (mv-let (v fn-arena fn-cat)
          (with-local-stobj fn-octets
            (mv-let (v fn-octets fn-arena fn-cat)
              (let ((fn-octets (fn-octets-from-list octets fn-octets)))
                (mv (list (scct-scan-cuts conn 0 (fn-octets-len fn-octets) fn-octets fn-arena fn-cat)
                          (fn-served-counted-consumed
                           (fn-scr-step-span-core conn 0 (fn-octets-len fn-octets) nil nil nil nil nil
                                                  fn-octets fn-arena fn-cat))
                          (fn-served-counted-consumed
                           (fn-scr-feed-span conn 0 (fn-octets-len fn-octets) nil nil nil nil nil
                                             fn-octets fn-arena fn-cat)))
                    fn-octets fn-arena fn-cat))
              (mv v fn-arena fn-cat)))
          (mv v fn-arena)))
      v)))

(defconst *scct-scan* (scct-scan-all *sct-reader* *sct-two-posts*))
(assert-event (equal (first *scct-scan*) t))
; the host's step consumed DATE, POST and the first article, and yielded:
; the same count as the byte fold, short of the whole input.
(assert-event (and (equal (second *scct-scan*) (third *scct-scan*))
                   (< (second *scct-scan*) (len *sct-two-posts*))
                   (< (+ (len (sct-line "DATE")) (len *sct-post-a*) -1) (second *scct-scan*))))
