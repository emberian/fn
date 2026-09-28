; served-catalog-tests.lisp -- witnesses and teeth for books/served-catalog.lisp
; (catalog slice, step 7b: the Message-ID, article-number and range arms
; read the catalog at the connection's pinned view).
;
; The fixture is three committed articles in commit order; the views are
; counts.  Every witness below is ground and is proved by evaluation; a
; must-fail form is a hypothesis-removal witness and is preceded by the
; affirmative check of every retained hypothesis, the failure of the omitted
; one and the failure of the conclusion.
(in-package "ACL2")
(include-book "../../books/served-catalog")
(include-book "must-fail-checked")

(defconst *sct-p0* (append (fn-record-string-octets "Subject: a") '(13 10 13 10 65 13 10)))
(defconst *sct-p1* (append (fn-record-string-octets "Subject: b") '(13 10 13 10 66 13 10)))
(defconst *sct-p2* (append (fn-record-string-octets "Subject: c") '(13 10 13 10 67 13 10)))
(defconst *sct-w0* (fn-record-make 0 1 1 "<a@x>" *sct-p0* '("fn.test") "o" "s" "e" 1 5))
(defconst *sct-w1* (fn-record-make 1 2 2 "<b@x>" *sct-p1* '("fn.test" "fn.other") "o" "s" "e" 1 5))
(defconst *sct-w2* (fn-record-make 2 3 3 "<c@x>" *sct-p2* '("fn.test") "o" "s" "e" 1 5))

;; A held row from a wire record and its arena handle (numbers assigned by
;; fn-cat-assign below, as fn-cat-load assigns them).
(defun sct-held (w handle numbers)
  (fn-held-make (fn-record-sequence w) (fn-record-txid w) (fn-record-generation w)
                (fn-record-msgid w) handle (fn-record-groups w) (fn-record-obligation-id w)
                (fn-record-content-subject w) (fn-record-release-evidence w)
                (fn-record-charge w) (fn-record-stamp w)
                (fn-held-facts-of (fn-record-payload w))
                (fn-held-context-of (fn-record-payload w) nil 0) numbers nil))

(defconst *sct-a* (list *sct-p0* *sct-p1* *sct-p2*))
(defconst *sct-r0* (fn-cat-assign (sct-held *sct-w0* 0 nil) nil))
(defconst *sct-r1* (fn-cat-assign (sct-held *sct-w1* 1 nil) (list *sct-r0*)))
(defconst *sct-r2* (fn-cat-assign (sct-held *sct-w2* 2 nil) (list *sct-r0* *sct-r1*)))
(defconst *sct-c* (list *sct-r0* *sct-r1* *sct-r2*))

;; The fixture's number column: fn.test 1, 2, 3 and fn.other 1; fresh.
(defthm sct-fixture
  (and (fn-cnx-freshp *sct-c*)
       (equal (fn-held-number-in "fn.test" *sct-r0*) 1)
       (equal (fn-held-number-in "fn.test" *sct-r1*) 2)
       (equal (fn-held-number-in "fn.other" *sct-r1*) 1)
       (equal (fn-held-number-in "fn.test" *sct-r2*) 3)
       (equal (fn-held-number-in "fn.other" *sct-r2*) nil))
  :rule-classes nil)

;; KEYSTONE A witnessed across views: the row committed after the pin is
;; invisible at the pinned view (count 2) and found at the next (count 3);
;; the finder is the archive scan over the view's articles at both.
(defthm sct-msgid-across-views
  (and (equal (fn-scat-msgid-article "<c@x>" 3 *sct-a* *sct-c*)
              (fn-cat-row-article 2 *sct-a* *sct-c*))
       (consp (fn-scat-msgid-article "<c@x>" 3 *sct-a* *sct-c*))
       ;; the article carries row 2's handle; a reader serves its bytes by the arena
       (equal (fn-article-payload (fn-scat-msgid-article "<c@x>" 3 *sct-a* *sct-c*)) 2)
       (equal (fn-nntp-article-bytes (fn-scat-msgid-article "<c@x>" 3 *sct-a* *sct-c*) *sct-a*)
              *sct-p2*)
       (equal (fn-scat-msgid-article "<c@x>" 2 *sct-a* *sct-c*) nil)
       (equal (fn-scat-msgid-article "<a@x>" 2 *sct-a* *sct-c*)
              (fn-cat-row-article 0 *sct-a* *sct-c*))
       (equal (fn-scat-msgid-article "<c@x>" 2 *sct-a* *sct-c*)
              (fn-find-article "<c@x>" (fn-cat-view-articles 2 *sct-a* *sct-c*)))
       (equal (fn-scat-msgid-article "<c@x>" 3 *sct-a* *sct-c*)
              (fn-find-article "<c@x>" (fn-cat-view-articles 3 *sct-a* *sct-c*)))
       (equal (fn-scat-msgid-article "<z@x>" 3 *sct-a* *sct-c*) nil))
  :rule-classes nil)

;; KEYSTONE B witnessed across views and groups: fn.test 3 is the row
;; committed after the pin; fn.other 1 is the second row's number in its
;; other group; a number above the group's high mark finds nothing.
(defthm sct-number-across-views
  (and (equal (fn-scat-number-article "fn.test" 3 3 *sct-a* *sct-c*)
              (fn-cat-row-article 2 *sct-a* *sct-c*))
       (equal (fn-scat-number-article "fn.test" 3 2 *sct-a* *sct-c*) nil)
       (equal (fn-scat-number-article "fn.test" 1 2 *sct-a* *sct-c*)
              (fn-cat-row-article 0 *sct-a* *sct-c*))
       (equal (fn-scat-number-article "fn.other" 1 2 *sct-a* *sct-c*)
              (fn-cat-row-article 1 *sct-a* *sct-c*))
       (equal (fn-scat-number-article "fn.test" 4 3 *sct-a* *sct-c*) nil)
       (equal (fn-scat-number-article "fn.test" 3 3 *sct-a* *sct-c*)
              (fn-nntp-find-group-number
               "fn.test" 3 (fn-cat-view-articles 3 *sct-a* *sct-c*)))
       (equal (fn-scat-number-article "fn.test" 3 2 *sct-a* *sct-c*)
              (fn-nntp-find-group-number
               "fn.test" 3 (fn-cat-view-articles 2 *sct-a* *sct-c*)))
       (equal (fn-scat-number-article "fn.other" 1 3 *sct-a* *sct-c*)
              (fn-nntp-find-group-number
               "fn.other" 1 (fn-cat-view-articles 3 *sct-a* *sct-c*))))
  :rule-classes nil)

;;; Teeth.

;; KEYSTONE B without fn-cnx-freshp (a corrupted-state witness): a catalog
;; whose third row was bound to fn.test 1 again.  The number column answers
;; the oldest binding (seq 0), the served walk over the view answers the
;; newest (seq 2): the equation fails.
(defconst *sct-c-dup*
  (list *sct-r0* *sct-r1* (sct-held *sct-w2* 2 '(("fn.test" . 1)))))

(defthm sct-teeth-freshness-hypotheses
  (and (not (fn-cnx-freshp *sct-c-dup*))              ; the omitted hypothesis fails
       (stringp "fn.test") (posp 1)                   ; the retained ones hold
       (not (equal (fn-scat-number-article "fn.test" 1 3 *sct-a* *sct-c-dup*)
                   (fn-nntp-find-group-number
                    "fn.test" 1 (fn-cat-view-articles 3 *sct-a* *sct-c-dup*)))))
  :rule-classes nil)

(must-fail-checked
 (defthm sct-teeth-number-article-without-freshness
   (equal (fn-scat-number-article "fn.test" 1 3 *sct-a* *sct-c-dup*)
          (fn-nntp-find-group-number
           "fn.test" 1 (fn-cat-view-articles 3 *sct-a* *sct-c-dup*)))
   :rule-classes nil))

;; The per-row lemma without GROUP (a corrupted-state witness: an atom in a
;; numbers alist, which fn-held-numbersp forbids): the served walk stops at
;; the atom (its car is nil, the group), the catalog's alist walk skips it.
(defthm sct-teeth-row-group-hypotheses
  (and (equal nil nil) (posp 5)
       (not (iff (equal (fn-nntp-membership-number nil '(7 (nil . 5))) 5)
                 (equal 5 (let ((pair (fn-cat-assoc nil '(7 (nil . 5)))))
                            (if (consp pair) (cdr pair) nil))))))
  :rule-classes nil)

(must-fail-checked
 (defthm sct-teeth-row-without-group
   (iff (equal (fn-nntp-membership-number nil '(7 (nil . 5))) 5)
        (equal 5 (let ((pair (fn-cat-assoc nil '(7 (nil . 5)))))
                   (if (consp pair) (cdr pair) nil))))
   :rule-classes nil))

;; The per-row lemma without (posp N): at N = 0 the served walk reads 0 for
;; an absent group and the catalog nil.
(defthm sct-teeth-row-posp-hypotheses
  (and (stringp "fn.test") (not (posp 0))
       (not (iff (equal (fn-nntp-membership-number "fn.test" nil) 0)
                 (equal 0 (let ((pair (fn-cat-assoc "fn.test" nil)))
                            (if (consp pair) (cdr pair) nil))))))
  :rule-classes nil)

(must-fail-checked
 (defthm sct-teeth-row-without-posp
   (iff (equal (fn-nntp-membership-number "fn.test" nil) 0)
        (equal 0 (let ((pair (fn-cat-assoc "fn.test" nil)))
                   (if (consp pair) (cdr pair) nil))))
   :rule-classes nil))

;;; ----------------------------------------------------------------------------
;;; 7b rest: the range arms across views.  Each witness evaluates the arm the
;;; -cat dispatcher calls AND the served fold over the view's articles, and
;;; asserts they agree and what they answer.  The crossings: an old and a
;;; refreshed view over an append; a cancel whose target is committed before
;;; the reader's view and one committed after it; a redecision; a
;;; reclamation.

(defun sct-session (group)
  (fn-nntp-make-session t group nil t))

;; The shown numbers and the OVER lines at a view, catalog and fold.
(defmacro sct-agree (group v a c)
  `(and (equal (fn-scat-range-numbers ,group 1 10 ,v ,c)
               (fn-nntp-group-range-numbers ,group 1 10 (fn-cat-view-articles ,v ,a ,c)))
        (equal (fn-nov-lines-for-numbers-cat
                ,group (fn-scat-range-numbers ,group 1 10 ,v ,c) ,v ,a ,c)
               (fn-nov-lines-for-numbers
                ,group (fn-nntp-group-range-numbers ,group 1 10 (fn-cat-view-articles ,v ,a ,c))
                (fn-cat-view-articles ,v ,a ,c) ,a))
        (equal (fn-scat-group-low ,group ,v ,c)
               (fn-nntp-group-low ,group (fn-cat-view-articles ,v ,a ,c)))))

;; APPEND: the view pinned before the third commit and the refreshed one.
(defthm sct-range-append
  (and (sct-agree "fn.test" 2 *sct-a* *sct-c*)
       (sct-agree "fn.test" 3 *sct-a* *sct-c*)
       (sct-agree "fn.other" 3 *sct-a* *sct-c*)
       (equal (fn-scat-range-numbers "fn.test" 1 10 2 *sct-c*) '(1 2))
       (equal (fn-scat-range-numbers "fn.test" 1 10 3 *sct-c*) '(1 2 3))
       (equal (fn-scat-range-numbers "fn.other" 1 10 3 *sct-c*) '(1))
       (equal (len (fn-nov-lines-for-numbers-cat
                    "fn.test" (fn-scat-range-numbers "fn.test" 1 10 3 *sct-c*) 3 *sct-a* *sct-c*))
              3)
       ;; the clamp: a range past the group's high names nothing more
       (equal (fn-scat-range-numbers "fn.test" 1 4294967295 3 *sct-c*) '(1 2 3)))
  :rule-classes nil)

;; CANCEL AFTER TARGET: row 1 (fn.test 2) is withdrawn at count 3, then the
;; cancel's own row commits (fn.test 4).  The view pinned at 3 still shows
;; the target; the refreshed view at 4 does not, and shows the cancel's row.
(defconst *sct-p3* (append (fn-record-string-octets "Subject: cancel") '(13 10 13 10 88 13 10)))
(defconst *sct-w3* (fn-record-make 3 4 4 "<d@x>" *sct-p3* '("fn.test") "o" "s" "e" 1 5))
(defconst *sct-a4* (list *sct-p0* *sct-p1* *sct-p2* *sct-p3*))
(defconst *sct-cw* (fn-cat$a-withdraw 1 3 *sct-c*))
(defconst *sct-c4* (fn-cat$a-commit (sct-held *sct-w3* 3 nil) *sct-cw*))

(defthm sct-range-cancel-after-target
  (and (fn-cnx-freshp *sct-c4*)
       (sct-agree "fn.test" 3 *sct-a4* *sct-c4*)
       (sct-agree "fn.test" 4 *sct-a4* *sct-c4*)
       (sct-agree "fn.other" 4 *sct-a4* *sct-c4*)
       (equal (fn-scat-range-numbers "fn.test" 1 10 3 *sct-c4*) '(1 2 3))
       (equal (fn-scat-range-numbers "fn.test" 1 10 4 *sct-c4*) '(1 3 4))
       (equal (fn-scat-range-numbers "fn.other" 1 10 3 *sct-c4*) '(1))
       (equal (fn-scat-range-numbers "fn.other" 1 10 4 *sct-c4*) nil))
  :rule-classes nil)

;; CANCEL BEFORE TARGET: the cancel's row commits first (seq 3), then the
;; target (seq 4, fn.test 5) and its withdrawal at count 5.  The view before
;; the target never shows it; the view at 5 is the catalog's single window in
;; which the target is visible (the owner's publication order R1 decides
;; whether a reader can acquire it: the record's finding); every later view
;; hides it.  At every view the catalog answers what the fold answers.
(defconst *sct-p4* (append (fn-record-string-octets "Subject: late") '(13 10 13 10 89 13 10)))
(defconst *sct-w4* (fn-record-make 4 5 5 "<e@x>" *sct-p4* '("fn.test") "o" "s" "e" 1 5))
(defconst *sct-a5* (list *sct-p0* *sct-p1* *sct-p2* *sct-p3* *sct-p4*))
(defconst *sct-c5*
  (fn-cat$a-withdraw 4 3 (fn-cat$a-commit (sct-held *sct-w4* 4 nil)
                                          (fn-cat$a-commit (sct-held *sct-w3* 3 nil) *sct-c*))))
(defconst *sct-c6*
  (fn-cat$a-commit (sct-held *sct-w0* 0 '(("fn.other" . 2))) *sct-c5*))

(defthm sct-range-cancel-before-target
  (and (fn-cnx-freshp *sct-c6*)
       (sct-agree "fn.test" 4 *sct-a5* *sct-c6*)
       (sct-agree "fn.test" 5 *sct-a5* *sct-c6*)
       (sct-agree "fn.test" 6 *sct-a5* *sct-c6*)
       (equal (fn-scat-range-numbers "fn.test" 1 10 4 *sct-c6*) '(1 2 3 4))
       (equal (fn-scat-range-numbers "fn.test" 1 10 5 *sct-c6*) '(1 2 3 4 5))
       (equal (fn-scat-range-numbers "fn.test" 1 10 6 *sct-c6*) '(1 2 3 4 6)))
  :rule-classes nil)

;; REDECISION: a row's verdict context replaced; the shown numbers and the
;; overview lines do not read it, at the old view or the new.
(defconst *sct-cr* (fn-cat$a-redecide 0 (fn-held-context *sct-r1*) *sct-c*))

(defthm sct-range-redecision
  (and (sct-agree "fn.test" 3 *sct-a* *sct-cr*)
       (equal (fn-scat-range-numbers "fn.test" 1 10 3 *sct-cr*)
              (fn-scat-range-numbers "fn.test" 1 10 3 *sct-c*))
       (equal (fn-nov-lines-for-numbers-cat "fn.test" '(1 2 3) 3 *sct-a* *sct-cr*)
              (fn-nov-lines-for-numbers-cat "fn.test" '(1 2 3) 3 *sct-a* *sct-c*)))
  :rule-classes nil)

;; RECLAMATION: the payload behind handle 1 becomes a tombstone.  The number
;; stays shown (LISTGROUP keeps it: RFC 3977 numbers are not reused) and OVER
;; skips the row, at the old view and the new, as the fold does.
(defconst *sct-tomb* (append *fn-rcl-magic* (make-list 81 :initial-element 0)))
(defconst *sct-ar* (list *sct-p0* *sct-tomb* *sct-p2*))

(defthm sct-range-reclamation
  (and (fn-rcl-tombstonep *sct-tomb*)
       (sct-agree "fn.test" 2 *sct-ar* *sct-c*)
       (sct-agree "fn.test" 3 *sct-ar* *sct-c*)
       (equal (fn-scat-range-numbers "fn.test" 1 10 3 *sct-c*) '(1 2 3))
       (equal (len (fn-nov-lines-for-numbers-cat "fn.test" '(1 2 3) 3 *sct-ar* *sct-c*)) 2)
       (equal (len (fn-nov-lines-for-numbers-cat "fn.test" '(1 2 3) 3 *sct-a* *sct-c*)) 3))
  :rule-classes nil)

;; The arms themselves, one per command family, at the refreshed view.
(defthm sct-arms-agree
  (let* ((arch (fn-make-state '("fn.test" "fn.other") '(("fn.test" . 4) ("fn.other" . 2))
                              (fn-cat-view-articles 3 *sct-a* *sct-c*) 0 nil nil))
         (s (sct-session "fn.test")))
    (and (equal (fn-nntp-over-range-cat s 3 "1-10" nil *sct-a* *sct-c*)
                (fn-nntp-over-range s arch "1-10" *sct-a*))
         (equal (fn-nntp-listgroup-command-cat s arch nil 3 *sct-c*)
                (fn-nntp-listgroup-command s arch nil))
         (equal (fn-nntp-group-result-cat s arch "fn.test" 3 *sct-c*)
                (fn-nntp-group-result s arch "fn.test"))
         (equal (fn-nntp-list-counts-command-cat s arch nil 3 *sct-c*)
                (fn-nntp-list-counts-command s arch nil))
         (equal (fn-nntp-hdr-command-cat s '("Subject" "1-10") 3 nil *sct-a* *sct-c*)
                (fn-nntp-hdr-command s arch '("Subject" "1-10") nil *sct-a*))
         (equal (fn-nntp-xpat-response-cat s '("Subject" "1-10" "*b*") 3 *sct-a* *sct-c*)
                (fn-nntp-xpat-response s arch '("Subject" "1-10" "*b*") *sct-a*))))
  :rule-classes nil)

;;; Teeth for KEYSTONE N (fn-scat-range-numbers-is-group-range-numbers).

(defthm sct-teeth-n-freshness-hypotheses
  (and (not (fn-cnx-freshp *sct-c-dup*))
       (stringp "fn.test") (natp 1) (natp 10)
       (not (equal (fn-scat-range-numbers "fn.test" 1 10 3 *sct-c-dup*)
                   (fn-nntp-group-range-numbers "fn.test" 1 10
                                                (fn-cat-view-articles 3 *sct-a* *sct-c-dup*)))))
  :rule-classes nil)

(must-fail-checked
 (defthm sct-teeth-n-without-freshness
   (equal (fn-scat-range-numbers "fn.test" 1 10 3 *sct-c-dup*)
          (fn-nntp-group-range-numbers "fn.test" 1 10
                                       (fn-cat-view-articles 3 *sct-a* *sct-c-dup*)))
   :rule-classes nil))

(defthm sct-teeth-n-low-hypotheses
  (and (fn-cnx-freshp *sct-c*) (stringp "fn.test") (not (natp -5)) (natp 10)
       (not (equal (fn-scat-range-numbers "fn.test" -5 10 3 *sct-c*)
                   (fn-nntp-group-range-numbers "fn.test" -5 10
                                                (fn-cat-view-articles 3 *sct-a* *sct-c*)))))
  :rule-classes nil)

(must-fail-checked
 (defthm sct-teeth-n-without-natp-low
   (equal (fn-scat-range-numbers "fn.test" -5 10 3 *sct-c*)
          (fn-nntp-group-range-numbers "fn.test" -5 10 (fn-cat-view-articles 3 *sct-a* *sct-c*)))
   :rule-classes nil))

(defthm sct-teeth-n-high-hypotheses
  (and (fn-cnx-freshp *sct-c*) (stringp "fn.test") (natp 1) (not (natp 5/2))
       (not (equal (fn-scat-range-numbers "fn.test" 1 5/2 3 *sct-c*)
                   (fn-nntp-group-range-numbers "fn.test" 1 5/2
                                                (fn-cat-view-articles 3 *sct-a* *sct-c*)))))
  :rule-classes nil)

(must-fail-checked
 (defthm sct-teeth-n-without-natp-high
   (equal (fn-scat-range-numbers "fn.test" 1 5/2 3 *sct-c*)
          (fn-nntp-group-range-numbers "fn.test" 1 5/2 (fn-cat-view-articles 3 *sct-a* *sct-c*)))
   :rule-classes nil))

;;; Teeth for KEYSTONE P (fn-scat-available-article-is-available).  Without
;;; GROUP (a corrupted-state witness: an atom in a row's numbers alist, which
;;; fn-held-numbersp forbids): the catalog binds the nil group past the atom,
;;; the served membership walk stops at it.  (For KEYSTONE N this witness
;;; does not separate the sides: the clamp at the group's next number hides
;;; the row; N carries GROUP from P and its weakening is not attempted.)
(defconst *sct-c-atom* (list (sct-held *sct-w0* 0 '(7 (nil . 1)))))

(defthm sct-teeth-p-group-hypotheses
  (and (fn-cnx-freshp *sct-c-atom*) (not nil)
       (not (equal (fn-scat-available-article nil 1 1 *sct-a* *sct-c-atom*)
                   (fn-nntp-available-article nil 1 (fn-cat-view-articles 1 *sct-a* *sct-c-atom*)))))
  :rule-classes nil)

(must-fail-checked
 (defthm sct-teeth-p-without-group
   (equal (fn-scat-available-article nil 1 1 *sct-a* *sct-c-atom*)
          (fn-nntp-available-article nil 1 (fn-cat-view-articles 1 *sct-a* *sct-c-atom*)))
   :rule-classes nil))

(defthm sct-teeth-p-freshness-hypotheses
  (and (not (fn-cnx-freshp *sct-c-dup*)) (stringp "fn.test")
       (not (equal (fn-scat-available-article "fn.test" 1 3 *sct-a* *sct-c-dup*)
                   (fn-nntp-available-article "fn.test" 1
                                              (fn-cat-view-articles 3 *sct-a* *sct-c-dup*)))))
  :rule-classes nil)

(must-fail-checked
 (defthm sct-teeth-p-without-freshness
   (equal (fn-scat-available-article "fn.test" 1 3 *sct-a* *sct-c-dup*)
          (fn-nntp-available-article "fn.test" 1 (fn-cat-view-articles 3 *sct-a* *sct-c-dup*)))
   :rule-classes nil))

;;; ----------------------------------------------------------------------------
;;; F2 (lane sca-join-5): GROUP's summary and low from the catalog's live table
;;; (KEYSTONES fn-scat-group-summary-is-pass, fn-scat-group-low-is-pass: no
;;; hypotheses, so the teeth are the reachable witnesses that the TABLE
;;; branch is the one taken, and the two witnesses of why the branch is
;;; guarded by the top view and the horizon).
;;;
;;; The fixture is *sct-c4* above: row 1 (fn.test 2, fn.other 1) withdrawn at
;;; version 3 by fn-cat$a-withdraw (*sct-cw*), then the fourth article
;;; (fn.test 4) committed.

;; REACHABLE WITNESS (table branch): at the count 4, past the withdrawal's
;; horizon 4, the summary is read from the table -- fn.test 1, 3, 4 live,
;; count 3 -- and equals the pass and the served fold over the view.
(defthm sct-f2-summary-from-table
  (and (fn-scat-top-viewp 4 *sct-c4*)
       (equal (fn-cat-horizon *sct-c4*) 4)
       (equal (fn-cat-group-live-count "fn.test" *sct-c4*) 3)
       (equal (fn-cat-group-live-low "fn.test" *sct-c4*) 1)
       (equal (fn-cat-group-live-high "fn.test" *sct-c4*) 4)
       (equal (fn-scat-group-summary nil "fn.test" 4 *sct-c4*) '(3 1 4))
       (equal (fn-scat-group-summary nil "fn.test" 4 *sct-c4*)
              (fn-scat-group-summary-pass nil "fn.test" 4 *sct-c4*))
       (equal (fn-scat-group-low "fn.test" 4 *sct-c4*) 1)
       (equal (fn-scat-group-low "fn.test" 4 *sct-c4*)
              (fn-scat-group-low-pass "fn.test" 4 *sct-c4*))
       (equal (fn-scat-group-low "fn.test" 4 *sct-c4*)
              (fn-nntp-group-low "fn.test" (fn-cat-view-articles 4 *sct-a4* *sct-c4*)))
       ;; fn.other: its only row is withdrawn; the table says empty, as the pass
       (equal (fn-cat-group-live-count "fn.other" *sct-c4*) 0)
       (equal (fn-scat-group-summary nil "fn.other" 4 *sct-c4*)
              (fn-scat-group-summary-pass nil "fn.other" 4 *sct-c4*)))
  :rule-classes nil)

;; WHY THE HORIZON: right after the withdrawal (count 3, horizon 4) the
;; withdrawn row is still visible to a reader at version 3 (RFC 3977 lets a
;; removed article stay until the reader's view moves): the pass counts
;; fn.test 1..3, the table 1 and 3.  The top view holds (v = count), the
;; horizon test fails, the table disagrees -- so the branch takes the pass.
(defthm sct-f2-below-horizon
  (and (equal (fn-cat-count *sct-cw*) 3)
       (equal (fn-cat-horizon *sct-cw*) 4)
       (not (fn-scat-top-viewp 3 *sct-cw*))
       (equal (fn-scat-group-summary-pass nil "fn.test" 3 *sct-cw*) '(3 1 3))
       (equal (fn-cat-group-live-count "fn.test" *sct-cw*) 2)
       (equal (fn-scat-group-summary nil "fn.test" 3 *sct-cw*) '(3 1 3)))
  :rule-classes nil)

;; WHY THE TOP VIEW: a reader pinned at version 2 of the four-row catalog
;; sees fn.test 1, 2 (row 1's withdrawal is at 3); the table, at the top,
;; says 1, 3, 4.
(defthm sct-f2-older-view
  (and (not (fn-scat-top-viewp 2 *sct-c4*))
       (equal (fn-scat-group-summary-pass nil "fn.test" 2 *sct-c4*) '(2 1 2))
       (equal (fn-scat-group-summary nil "fn.test" 2 *sct-c4*) '(2 1 2))
       (not (equal (fn-cat-group-live-count "fn.test" *sct-c4*) 2)))
  :rule-classes nil)

;;; F2 item 1: the Xref ARTICLE/HEAD arm by number and of the current article
;;; reads the catalog (fn-rcompat-retrieval-cat, KEYSTONE
;;; fn-rcompat-retrieval-cat-is-retrieval).  The archive is the view's
;;; articles at count 3; the session is in fn.test at number 1.
(defmacro sct-f2-state3 ()
  '(fn-make-state '("fn.test" "fn.other") (list (cons "fn.test" 4) (cons "fn.other" 2))
                  (fn-cat-view-articles 3 *sct-a* *sct-c*) 1 nil nil))
(defmacro sct-f2-session ()
  '(fn-nntp-set-cursor (fn-nntp-open-session (sct-f2-state3)) "fn.test" 1))
(defconst *sct-f2-server* (fn-nntp-string-octets "news.example.org"))
(defconst *sct-f2-args-2* (list (fn-nntp-string-octets "2")))
(defconst *sct-f2-args-9* (list (fn-nntp-string-octets "9")))

;; REACHABLE WITNESS: every antecedent; number 2 is found (220, the cursor
;; moves to 2), number 9 is not (423), the current article (1) is found; the
;; catalog arm and the archive arm answer the same octets and session.
(defthm sct-f2-xref-retrieval
  (and (equal (fn-state-articles (sct-f2-state3)) (fn-cat-view-articles 3 *sct-a* *sct-c*))
       (fn-cnx-freshp *sct-c*)
       (consp (fn-scat-number-article "fn.test" 2 3 *sct-a* *sct-c*))
       (equal (fn-nntp-session-current
               (fn-nntp-result-session
                (fn-rcompat-retrieval-cat (sct-f2-session) (sct-f2-state3) nil :article *sct-f2-args-2*
                                          *sct-f2-server* 3 *sct-a* *sct-c*)))
              2)
       (equal (fn-rcompat-retrieval-cat (sct-f2-session) (sct-f2-state3) nil :article *sct-f2-args-2*
                                        *sct-f2-server* 3 *sct-a* *sct-c*)
              (fn-rcompat-retrieval (sct-f2-session) (sct-f2-state3) nil :article *sct-f2-args-2*
                                    *sct-f2-server* *sct-a*))
       (equal (fn-rcompat-retrieval-cat (sct-f2-session) (sct-f2-state3) nil :head *sct-f2-args-9*
                                        *sct-f2-server* 3 *sct-a* *sct-c*)
              (fn-nntp-single (sct-f2-session) "423 no article with that number"))
       (equal (fn-rcompat-retrieval-cat (sct-f2-session) (sct-f2-state3) nil :head *sct-f2-args-9*
                                        *sct-f2-server* 3 *sct-a* *sct-c*)
              (fn-rcompat-retrieval (sct-f2-session) (sct-f2-state3) nil :head *sct-f2-args-9*
                                    *sct-f2-server* *sct-a*))
       (equal (fn-rcompat-retrieval-cat (sct-f2-session) (sct-f2-state3) nil :head nil
                                        *sct-f2-server* 3 *sct-a* *sct-c*)
              (fn-rcompat-retrieval (sct-f2-session) (sct-f2-state3) nil :head nil
                                    *sct-f2-server* *sct-a*))
       (not (equal (fn-rcompat-retrieval-cat (sct-f2-session) (sct-f2-state3) nil :head nil
                                             *sct-f2-server* 3 *sct-a* *sct-c*)
                   (fn-nntp-single (sct-f2-session) "420 no current article"))))
  :rule-classes nil)

;; HYPOTHESIS REMOVAL (the archive is the view's articles): an archive with
;; no articles, freshness kept; the catalog arm finds number 2, the archive
;; arm does not.
(defconst *sct-f2-state0*
  (fn-make-state '("fn.test" "fn.other") (list (cons "fn.test" 4) (cons "fn.other" 2))
                 nil 1 nil nil))

(defthm sct-f2-xref-retrieval-view-hypotheses
  (and (fn-cnx-freshp *sct-c*)
       (not (equal (fn-state-articles *sct-f2-state0*) (fn-cat-view-articles 3 *sct-a* *sct-c*)))
       (not (equal (fn-rcompat-retrieval-cat (sct-f2-session) *sct-f2-state0* nil :article *sct-f2-args-2*
                                             *sct-f2-server* 3 *sct-a* *sct-c*)
                   (fn-rcompat-retrieval (sct-f2-session) *sct-f2-state0* nil :article *sct-f2-args-2*
                                         *sct-f2-server* *sct-a*))))
  :rule-classes nil)

(must-fail-checked
 (defthm sct-f2-xref-retrieval-without-view
   (equal (fn-rcompat-retrieval-cat (sct-f2-session) *sct-f2-state0* nil :article *sct-f2-args-2*
                                    *sct-f2-server* 3 *sct-a* *sct-c*)
          (fn-rcompat-retrieval (sct-f2-session) *sct-f2-state0* nil :article *sct-f2-args-2*
                                *sct-f2-server* *sct-a*))
   :rule-classes nil))

;;; Teeth for KEYSTONE fn-nntp-verdict-hdr-response-cat-is-archive (lane
;;; scale-reads): HDR :fn-verified reads the catalog and ONE pass over the
;;; verdict list.  The list holds a non-pair, a newer and an older verdict for
;;; <b@x> (the newer is the recorded one) and none for <c@x> (no record).
(defconst *sct-vh-verdicts*
  (list (cons "<b@x>" (fn-stx-make-verdict :absent nil 2))
        7
        (cons "<a@x>" (fn-stx-make-verdict :absent nil 1))
        (cons "<b@x>" (fn-stx-make-verdict :absent nil 0))))

(defmacro sct-vh-arch ()
  `  (fn-make-state '("fn.test" "fn.other") '(("fn.test" . 4) ("fn.other" . 2))
                 (fn-cat-view-articles 3 *sct-a* *sct-c*) 0 nil nil))

(defun sct-vh-args-fn (xs)
  (declare (xargs :mode :program))
  (if (consp xs)
      (cons (list 'fn-nntp-string-octets (car xs)) (sct-vh-args-fn (cdr xs)))
    nil))

(defmacro sct-vh-args (&rest xs)
  (cons 'list (sct-vh-args-fn xs)))

(defmacro sct-vh-agree (session args arch c)
  `(equal (fn-nntp-verdict-hdr-response-cat ,session *sct-vh-verdicts* ,args 3 *sct-a* ,c)
          (fn-nntp-verdict-hdr-response ,session ,arch *sct-vh-verdicts* ,args)))

;; Positive: both hypotheses hold and every arm agrees; the range reply has
;; three lines, <b@x>'s the newer verdict (generation 2), <c@x>'s no-record.
(defthm sct-teeth-vh-positive
  (and (fn-cnx-freshp *sct-c*)
       (equal (fn-state-articles (sct-vh-arch)) (fn-cat-view-articles 3 *sct-a* *sct-c*))
       (sct-vh-agree (sct-session "fn.test") (sct-vh-args ":fn-verified" "1-10") (sct-vh-arch) *sct-c*)
       (sct-vh-agree (sct-session "fn.test") (sct-vh-args ":fn-verified" "2") (sct-vh-arch) *sct-c*)
       (sct-vh-agree (fn-nntp-make-session t "fn.test" 3 t) (sct-vh-args ":fn-verified") (sct-vh-arch) *sct-c*)
       (sct-vh-agree (sct-session "fn.test") (sct-vh-args ":fn-verified" "<b@x>") (sct-vh-arch) *sct-c*)
       (sct-vh-agree (sct-session "fn.test") (sct-vh-args ":fn-verified" "<z@x>") (sct-vh-arch) *sct-c*)
       (equal (fn-nntp-verdict-hdr-response-cat (sct-session "fn.test") *sct-vh-verdicts*
                                                (sct-vh-args ":fn-verified" "1-10") 3 *sct-a* *sct-c*)
              (fn-nntp-multi
               (sct-session "fn.test") (fn-nntp-hdr-initial nil)
               (list (fn-nntp-hdr-line (fn-nntp-decimal-field 1)
                                       (fn-stx-reader-item (fn-stx-make-verdict :absent nil 1)))
                     (fn-nntp-hdr-line (fn-nntp-decimal-field 2)
                                       (fn-stx-reader-item (fn-stx-make-verdict :absent nil 2)))
                     (fn-nntp-hdr-line (fn-nntp-decimal-field 3) (fn-stx-reader-item nil)))))
       (equal (fn-stx-reader-lookup "<b@x>" *sct-vh-verdicts*) (fn-stx-make-verdict :absent nil 2)))
  :rule-classes nil)

;; Without freshness (a duplicated number): the retained hypothesis holds,
;; the omitted one fails, and the conclusion fails.
(defmacro sct-vh-arch-dup ()
  `  (fn-make-state '("fn.test" "fn.other") '(("fn.test" . 4) ("fn.other" . 2))
                 (fn-cat-view-articles 3 *sct-a* *sct-c-dup*) 0 nil nil))

(defthm sct-teeth-vh-freshness-hypotheses
  (and (not (fn-cnx-freshp *sct-c-dup*))
       (equal (fn-state-articles (sct-vh-arch-dup)) (fn-cat-view-articles 3 *sct-a* *sct-c-dup*))
       (not (sct-vh-agree (sct-session "fn.test") (sct-vh-args ":fn-verified" "1-10") (sct-vh-arch-dup) *sct-c-dup*)))
  :rule-classes nil)

(must-fail-checked
 (defthm sct-teeth-vh-without-freshness
   (sct-vh-agree (sct-session "fn.test") (sct-vh-args ":fn-verified" "1-10") (sct-vh-arch-dup) *sct-c-dup*)
   :rule-classes nil))

;; Without the view equation (an archive of other articles): freshness holds,
;; the omitted hypothesis fails, and the conclusion fails.
(defmacro sct-vh-arch-other ()
  `  (fn-make-state '("fn.test" "fn.other") '(("fn.test" . 4) ("fn.other" . 2))
                 (cdr (fn-cat-view-articles 3 *sct-a* *sct-c*)) 0 nil nil))

(defthm sct-teeth-vh-view-hypotheses
  (and (fn-cnx-freshp *sct-c*)
       (not (equal (fn-state-articles (sct-vh-arch-other)) (fn-cat-view-articles 3 *sct-a* *sct-c*)))
       (not (sct-vh-agree (sct-session "fn.test") (sct-vh-args ":fn-verified" "1-10") (sct-vh-arch-other) *sct-c*)))
  :rule-classes nil)

(must-fail-checked
 (defthm sct-teeth-vh-without-view
   (sct-vh-agree (sct-session "fn.test") (sct-vh-args ":fn-verified" "1-10") (sct-vh-arch-other) *sct-c*)
   :rule-classes nil))
