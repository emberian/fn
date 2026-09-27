; served-catalog-tests.lisp -- witnesses and teeth for books/served-catalog.lisp
; (catalog slice, step 7b: the Message-ID and article-number arms read the
; catalog at the connection's pinned view).
;
; The fixture is three committed articles in commit order; the views are
; counts.  Every witness below is ground and is proved by evaluation; a
; must-fail form is a hypothesis-removal witness and is preceded by the
; affirmative check of every retained hypothesis, the failure of the omitted
; one and the failure of the conclusion.
(in-package "ACL2")
(include-book "../../books/served-catalog")
(include-book "std/testing/must-fail" :dir :system)

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
       (equal (fn-article-payload (fn-scat-msgid-article "<c@x>" 3 *sct-a* *sct-c*))
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

(must-fail
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

(must-fail
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

(must-fail
 (defthm sct-teeth-row-without-posp
   (iff (equal (fn-nntp-membership-number "fn.test" nil) 0)
        (equal 0 (let ((pair (fn-cat-assoc "fn.test" nil)))
                   (if (consp pair) (cdr pair) nil))))
   :rule-classes nil))
