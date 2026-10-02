; over-window-tests.lisp -- teeth for books/over-window.lisp (lane join-f2-10).
;
; The fixture is served-catalog-tests' three-article catalog (fn.test 1, 2, 3;
; fn.other 1).  Positive witnesses evaluate BOTH sides of the keystone
; fn-ovw-run-is-over-range-cat on it at W = 1, 2 and 7 (the reply is really
; split: the first quantum at W = 1 leaves a live cursor); the empty range
; (423, and 420 for XOVER) and no group (412).  Hypothesis removal for
; fn-ovw-run-is-reply: a non-natural K, the retained hypothesis holding and
; the conclusion failing.  Mutation: the first quantum alone is not the reply
; (the windowed reply is never truncated by stopping early).

(in-package "ACL2")
(include-book "../../books/over-window")

(defconst *ovwt-p0* (append (fn-record-string-octets "Subject: a") '(13 10 13 10 65 13 10)))
(defconst *ovwt-p1* (append (fn-record-string-octets "Subject: b") '(13 10 13 10 66 13 10)))
(defconst *ovwt-p2* (append (fn-record-string-octets "Subject: c") '(13 10 13 10 67 13 10)))
(defconst *ovwt-w0* (fn-record-make 0 1 1 "<a@x>" *ovwt-p0* '("fn.test") "o" "s" "e" 1 5))
(defconst *ovwt-w1* (fn-record-make 1 2 2 "<b@x>" *ovwt-p1* '("fn.test" "fn.other") "o" "s" "e" 1 5))
(defconst *ovwt-w2* (fn-record-make 2 3 3 "<c@x>" *ovwt-p2* '("fn.test") "o" "s" "e" 1 5))

(defun ovwt-held (w handle numbers)
  (fn-held-make (fn-record-sequence w) (fn-record-txid w) (fn-record-generation w)
                (fn-record-msgid w) handle (fn-record-groups w) (fn-record-obligation-id w)
                (fn-record-content-subject w) (fn-record-release-evidence w)
                (fn-record-charge w) (fn-record-stamp w)
                (fn-held-facts-of (fn-record-payload w))
                (fn-held-context-of (fn-record-payload w) nil 0) numbers nil))

(defconst *ovwt-a* (list *ovwt-p0* *ovwt-p1* *ovwt-p2*))
(defconst *ovwt-r0* (fn-cat-assign (ovwt-held *ovwt-w0* 0 nil) nil))
(defconst *ovwt-r1* (fn-cat-assign (ovwt-held *ovwt-w1* 1 nil) (list *ovwt-r0*)))
(defconst *ovwt-r2* (fn-cat-assign (ovwt-held *ovwt-w2* 2 nil) (list *ovwt-r0* *ovwt-r1*)))
(defconst *ovwt-c* (list *ovwt-r0* *ovwt-r1* *ovwt-r2*))

(defun ovwt-session (group)
  (fn-nntp-make-session t group nil t))

(defconst *ovwt-range* (fn-record-string-octets "1-10"))
(defconst *ovwt-past* (fn-record-string-octets "7-9"))

; The old reader's reply octets.
(defmacro ovwt-old (session token legacyp)
  `(fn-served-reply-octets
    (cdr (fn-nntp-over-range-cat ,session 3 ,token ,legacyp *ovwt-a* *ovwt-c*))))

;; POSITIVE: the keystone's conclusion, both conjuncts, at three widths; the
;; reply is a 224 with three lines ending in the dot.
(defthm ovwt-keystone-witness
  (let ((s (ovwt-session "fn.test")))
    (and (equal (car (fn-nntp-over-range-cat s 3 *ovwt-range* nil *ovwt-a* *ovwt-c*)) s)
         (equal (fn-ovw-octets s 3 *ovwt-range* nil nil 1 *ovwt-a* *ovwt-c*) (ovwt-old s *ovwt-range* nil))
         (equal (fn-ovw-octets s 3 *ovwt-range* nil nil 2 *ovwt-a* *ovwt-c*) (ovwt-old s *ovwt-range* nil))
         (equal (fn-ovw-octets s 3 *ovwt-range* nil nil 7 *ovwt-a* *ovwt-c*) (ovwt-old s *ovwt-range* nil))
         (equal (take 3 (ovwt-old s *ovwt-range* nil)) '(50 50 52))
         (equal (last (ovwt-old s *ovwt-range* nil) ) '(10))
         (equal (len (fn-ovw-lines "fn.test" 1 3 nil 3 *ovwt-a* *ovwt-c*)) 3)))
  :rule-classes nil)

;; The reply is really windowed: at W = 1 the start probes nothing, the first
;; quantum sends the status line and ONE line and leaves a live cursor at 2.
(defthm ovwt-first-quantum
  (let* ((s (ovwt-session "fn.test"))
         (cur (mv-nth 1 (fn-ovw-start s 3 *ovwt-range* nil nil *ovwt-c*))))
    (and (equal (mv-nth 0 (fn-ovw-start s 3 *ovwt-range* nil nil *ovwt-c*)) nil)
         (equal cur (fn-ovw-cursor "fn.test" 1 3 3 nil t nil))
         (equal (mv-nth 1 (fn-ovw-step cur 1 *ovwt-a* *ovwt-c*))
                (fn-ovw-cursor "fn.test" 2 3 3 nil nil nil))
         (equal (len (fn-ovw-lines "fn.test" 1 (fn-ovw-hi 1 3 1) nil 3 *ovwt-a* *ovwt-c*)) 1)
         ;; MUTATION: the first quantum alone is a strict prefix, not the reply
         (not (equal (mv-nth 0 (fn-ovw-step cur 1 *ovwt-a* *ovwt-c*))
                     (ovwt-old s *ovwt-range* nil)))))
  :rule-classes nil)

;; POSITIVE, the refusals: a range past the group's high (423; XOVER 420) and
;; no group selected (412), all equal to the old reader.
(defthm ovwt-refusals-witness
  (let ((s (ovwt-session "fn.test")) (n (ovwt-session nil)))
    (and (equal (fn-ovw-octets s 3 *ovwt-past* nil nil 2 *ovwt-a* *ovwt-c*) (ovwt-old s *ovwt-past* nil))
         (equal (take 3 (ovwt-old s *ovwt-past* nil)) '(52 50 51))
         (equal (fn-ovw-octets s 3 *ovwt-past* t nil 2 *ovwt-a* *ovwt-c*) (ovwt-old s *ovwt-past* t))
         (equal (take 3 (ovwt-old s *ovwt-past* t)) '(52 50 48))
         (equal (fn-ovw-octets n 3 *ovwt-range* nil nil 2 *ovwt-a* *ovwt-c*) (ovwt-old n *ovwt-range* nil))
         (equal (take 3 (ovwt-old n *ovwt-range* nil)) '(52 49 50))))
  :rule-classes nil)

;; HYPOTHESIS REMOVAL (fn-ovw-run-is-reply without (natp k)): K = :x, the
;; retained (natp top) holds, the conclusion fails (the step reads K as 0 and
;; sends the lines; the specification's range from :x is empty).
(defthm ovwt-run-is-reply-needs-natp-k
  (and (not (natp :x))
       (natp 3)
       (not (equal (fn-ovw-run (fn-ovw-cursor "fn.test" :x 3 3 nil t nil) 2 *ovwt-a* *ovwt-c*)
                   (fn-ovw-reply (fn-ovw-lines "fn.test" :x 3 nil 3 *ovwt-a* *ovwt-c*) nil t))))
  :rule-classes nil)

;; FRAME (fn-ovw-step-of-commit-pinned): a fourth fn.test article commits
;; after the pin.  POSITIVE: every hypothesis holds for the cursor pinned at
;; 3 and its quantum is unchanged (and sends all three lines).  HYPOTHESIS
;; REMOVAL (v <= count): the same cursor pinned at 4 over the old catalog --
;; the retained hypotheses hold, the omitted one fails, and the quantum sees
;; the new article, so the conclusion fails.
(defconst *ovwt-p3* (append (fn-record-string-octets "Subject: d") '(13 10 13 10 68 13 10)))
(defconst *ovwt-w3* (fn-record-make 3 4 4 "<d@x>" *ovwt-p3* '("fn.test") "o" "s" "e" 1 5))
(defconst *ovwt-a4* (list *ovwt-p0* *ovwt-p1* *ovwt-p2* *ovwt-p3*))
(defconst *ovwt-h3* (ovwt-held *ovwt-w3* 3 nil))

(defthm ovwt-step-of-commit-pinned-witness
  (let ((cur (fn-ovw-cursor "fn.test" 1 4 3 nil t nil)))
    (and (fn-cnx-freshp *ovwt-c*) (nth 0 cur) (natp (nth 3 cur))
         (<= (nth 3 cur) (fn-cat-count *ovwt-c*))
         (equal (fn-ovw-step cur 7 *ovwt-a4* (fn-cat-commit *ovwt-h3* *ovwt-c*))
                (fn-ovw-step cur 7 *ovwt-a4* *ovwt-c*))
         (equal (len (fn-ovw-lines "fn.test" 1 4 nil 3 *ovwt-a4* *ovwt-c*)) 3)))
  :rule-classes nil)

(defthm ovwt-step-of-commit-needs-pinned-view
  (let ((cur (fn-ovw-cursor "fn.test" 1 4 4 nil t nil)))
    (and (fn-cnx-freshp *ovwt-c*) (nth 0 cur) (natp (nth 3 cur))
         (not (<= (nth 3 cur) (fn-cat-count *ovwt-c*)))
         (equal (len (fn-ovw-lines "fn.test" 1 4 nil 4 *ovwt-a4* (fn-cat-commit *ovwt-h3* *ovwt-c*))) 4)
         (not (equal (fn-ovw-step cur 7 *ovwt-a4* (fn-cat-commit *ovwt-h3* *ovwt-c*))
                     (fn-ovw-step cur 7 *ovwt-a4* *ovwt-c*)))))
  :rule-classes nil)

;; ---------------------------------------------------------------------------
;; THE SERVED CURSOR (lane served-catalog-live, 2026-10-02): a node with an
;; Xref server name -- every configured node -- answers the range through
;; fn-nntp-xref-reply-cat, and that arm's cursor carries the name.  Before
;; this lane the arm answered the whole range in one step and the cursor
;; above was reached only by a node with no name (tests/test_native_over_pins
;; had never seen a quantum).

(defconst *ovwt-server* (fn-record-string-octets "news.example"))

(defmacro ovwt-old-served (session token legacyp)
  `(fn-served-reply-octets
    (cdr (fn-nntp-over-range-served-cat ,session 3 ,token ,legacyp *ovwt-server*
                                        *ovwt-a* *ovwt-c*))))

;; POSITIVE (fn-ovw-run-is-over-range-served-cat): the antecedent and both
;; conjuncts at three widths.  The served reply is not the plain one (its
;; lines carry the Xref field), so the cursor's server field is read.
;; MUTATION (labelled): a cursor that dropped its server name runs to the
;; plain reply, not the served one.
(defthm ovwt-served-keystone-witness
  (let ((s (ovwt-session "fn.test")))
    (and (fn-xref-serverp *ovwt-server*)
         (equal (car (fn-nntp-over-range-served-cat s 3 *ovwt-range* nil *ovwt-server*
                                                    *ovwt-a* *ovwt-c*))
                s)
         (equal (fn-ovw-octets s 3 *ovwt-range* nil *ovwt-server* 1 *ovwt-a* *ovwt-c*)
                (ovwt-old-served s *ovwt-range* nil))
         (equal (fn-ovw-octets s 3 *ovwt-range* nil *ovwt-server* 2 *ovwt-a* *ovwt-c*)
                (ovwt-old-served s *ovwt-range* nil))
         (equal (fn-ovw-octets s 3 *ovwt-range* nil *ovwt-server* 7 *ovwt-a* *ovwt-c*)
                (ovwt-old-served s *ovwt-range* nil))
         (equal (take 3 (ovwt-old-served s *ovwt-range* nil)) '(50 50 52))
         (equal (len (fn-ovw-lines "fn.test" 1 3 *ovwt-server* 3 *ovwt-a* *ovwt-c*)) 3)
         (not (equal (ovwt-old-served s *ovwt-range* nil) (ovwt-old s *ovwt-range* nil)))
         (< (len (ovwt-old s *ovwt-range* nil)) (len (ovwt-old-served s *ovwt-range* nil)))
         ;; mutation: the server dropped from the cursor
         (not (equal (fn-ovw-octets s 3 *ovwt-range* nil nil 2 *ovwt-a* *ovwt-c*)
                     (ovwt-old-served s *ovwt-range* nil)))))
  :rule-classes nil)

;; The served reply is really windowed, and the cursor keeps its server name
;; across a quantum.
(defthm ovwt-served-first-quantum
  (let* ((s (ovwt-session "fn.test"))
         (cur (mv-nth 1 (fn-ovw-start s 3 *ovwt-range* nil *ovwt-server* *ovwt-c*))))
    (and (equal cur (fn-ovw-cursor "fn.test" 1 3 3 nil t *ovwt-server*))
         (equal (mv-nth 1 (fn-ovw-step cur 1 *ovwt-a* *ovwt-c*))
                (fn-ovw-cursor "fn.test" 2 3 3 nil nil *ovwt-server*))
         (not (equal (mv-nth 0 (fn-ovw-step cur 1 *ovwt-a* *ovwt-c*))
                     (ovwt-old-served s *ovwt-range* nil)))))
  :rule-classes nil)

;; POSITIVE, the served refusals (423; XOVER 420; no group 412).
(defthm ovwt-served-refusals-witness
  (let ((s (ovwt-session "fn.test")) (n (ovwt-session nil)))
    (and (equal (fn-ovw-octets s 3 *ovwt-past* nil *ovwt-server* 2 *ovwt-a* *ovwt-c*)
                (ovwt-old-served s *ovwt-past* nil))
         (equal (take 3 (ovwt-old-served s *ovwt-past* nil)) '(52 50 51))
         (equal (fn-ovw-octets s 3 *ovwt-past* t *ovwt-server* 2 *ovwt-a* *ovwt-c*)
                (ovwt-old-served s *ovwt-past* t))
         (equal (take 3 (ovwt-old-served s *ovwt-past* t)) '(52 50 48))
         (equal (fn-ovw-octets n 3 *ovwt-range* nil *ovwt-server* 2 *ovwt-a* *ovwt-c*)
                (ovwt-old-served n *ovwt-range* nil))
         (equal (take 3 (ovwt-old-served n *ovwt-range* nil)) '(52 49 50))))
  :rule-classes nil)

;; HYPOTHESIS REMOVAL (fn-ovw-run-is-over-range-served-cat without SERVER),
;; on a CORRUPTED catalog (labelled: no commit builds it): the first row's
;; overview column is the second payload's.  With no server name the cursor
;; reads the bytes (the plain reader) and the served reader reads the column,
;; so the conclusion fails; the first conjunct (the session) still holds.
(defconst *ovwt-bad-h0*
  (fn-held-make (fn-record-sequence *ovwt-w0*) (fn-record-txid *ovwt-w0*)
                (fn-record-generation *ovwt-w0*) (fn-record-msgid *ovwt-w0*) 0
                (fn-record-groups *ovwt-w0*) (fn-record-obligation-id *ovwt-w0*)
                (fn-record-content-subject *ovwt-w0*) (fn-record-release-evidence *ovwt-w0*)
                (fn-record-charge *ovwt-w0*) (fn-record-stamp *ovwt-w0*)
                (fn-held-facts-of *ovwt-p1*)
                (fn-held-context-of *ovwt-p0* nil 0) nil nil))
(defconst *ovwt-bad-r0* (fn-cat-assign *ovwt-bad-h0* nil))
(defconst *ovwt-bad-c* (list *ovwt-bad-r0* *ovwt-r1* *ovwt-r2*))

(defthm ovwt-served-keystone-needs-a-server
  (let ((s (ovwt-session "fn.test")))
    (and ;; fn-scol-okp is a defun-nx: its row conjunct fails
         (fn-arena-p *ovwt-a*)
         (not (fn-scol-rows-okp *ovwt-bad-c* *ovwt-a*))
         (equal (car (fn-nntp-over-range-served-cat s 3 *ovwt-range* nil nil *ovwt-a* *ovwt-bad-c*))
                s)
         (not (equal (fn-ovw-octets s 3 *ovwt-range* nil nil 2 *ovwt-a* *ovwt-bad-c*)
                     (fn-served-reply-octets
                      (cdr (fn-nntp-over-range-served-cat s 3 *ovwt-range* nil nil
                                                          *ovwt-a* *ovwt-bad-c*)))))))
  :rule-classes nil)

;; FRAME with a server name (fn-ovw-step-of-commit-pinned): every hypothesis
;; holds for the cursor pinned at 3 and its quantum is unchanged by the
;; fourth article's commit.  REMOVAL (v <= count): pinned at 4 the quantum
;; sees the new article.  The two column hypotheses (fn-scol-okp,
;; fn-article-listp) and fn-scol-row-okp are the proof's route through the
;; reference fold; no witness here shows them necessary (a pinned window
;; reads no row at or past its view), and they are not claimed to be.
(defthm ovwt-served-step-of-commit-pinned-witness
  (let ((cur (fn-ovw-cursor "fn.test" 1 4 3 nil t *ovwt-server*)))
    (and (fn-cnx-freshp *ovwt-c*) (nth 0 cur) (natp (nth 3 cur))
         (<= (nth 3 cur) (fn-cat-count *ovwt-c*))
         (nth 6 cur)
         ;; fn-scol-okp (a defun-nx), conjunct by conjunct
         (fn-arena-p *ovwt-a4*)
         (fn-scol-rows-okp *ovwt-c* *ovwt-a4*)
         (fn-article-listp '("fn.test" "fn.other") (fn-cat-view-articles 3 *ovwt-a4* *ovwt-c*))
         (fn-scol-row-okp *ovwt-h3* *ovwt-a4*)
         (equal (fn-ovw-step cur 7 *ovwt-a4* (fn-cat-commit *ovwt-h3* *ovwt-c*))
                (fn-ovw-step cur 7 *ovwt-a4* *ovwt-c*))
         (equal (len (fn-ovw-lines "fn.test" 1 4 *ovwt-server* 3 *ovwt-a4* *ovwt-c*)) 3)))
  :rule-classes nil)

(defthm ovwt-served-step-of-commit-needs-pinned-view
  (let ((cur (fn-ovw-cursor "fn.test" 1 4 4 nil t *ovwt-server*)))
    (and (fn-cnx-freshp *ovwt-c*) (nth 0 cur) (natp (nth 3 cur))
         (not (<= (nth 3 cur) (fn-cat-count *ovwt-c*)))
         (not (equal (fn-ovw-step cur 7 *ovwt-a4* (fn-cat-commit *ovwt-h3* *ovwt-c*))
                     (fn-ovw-step cur 7 *ovwt-a4* *ovwt-c*)))))
  :rule-classes nil)
