; fn: teeth for books/catalog-relation.lisp (wave 5, lane catalog-slice step 6).
;
; What this book is evidence FOR.  `fn-cat-load-establishes-relation' and
; `fn-cat-load-from-empty': the load fold over a MIXED history (an article,
; a retention event, an article) from the creators yields a catalog whose
; rows, materialized by handle, are exactly the history's article records
; in order -- the entries 2 to 4 of design 1.5 in one shape, with the
; retention event skipped and the store sequence a column of the row.
; `fn-cat-relation-of-withdraw', `-of-redecide', `-of-complete': the row
; updates and the completion keep the relation.  The exec path runs the
; fold on live stobjs; the keystones get ground witnesses with their
; complete antecedent and a must-fail per falsifiable hypothesis.

(in-package "ACL2")
(include-book "../../books/catalog-relation")
(include-book "std/testing/must-fail" :dir :system)

(assert-event
 (and (eq (symbol-class 'fn-cat-load (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-cat-load-row (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-cat-wire-list (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-cat-history-relation (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sf-article-records (w state)) :common-lisp-compliant)))

; -----------------------------------------------------------------------------
; A mixed history: article at sequence 0, a retention event at 1, an
; article at 2.

(defconst *crl-p0* (append (fn-record-string-octets "Subject: a") '(13 10 13 10 65 13 10)))
(defconst *crl-p2* (append (fn-record-string-octets "Subject: c") '(13 10 13 10 67 13 10)))
(defconst *crl-w0* (fn-record-make 0 1 1 "<a@x>" *crl-p0* '("fn.test") "o" "s" "e" 1 5))
(defconst *crl-r1* (fn-store-retention-event-make :undertake 1 2 2 "id" "subject" "evidence" 3))
(defconst *crl-w2* (fn-record-make 2 3 3 "<c@x>" *crl-p2* '("fn.test") "o" "s" "e" 1 5))
(defconst *crl-h* (list *crl-w0* *crl-r1* *crl-w2*))

(assert-event (and (fn-record-p *crl-w0*) (fn-store-retention-event-p *crl-r1*)
                   (not (fn-record-p *crl-r1*)) (fn-record-p *crl-w2*)
                   (equal (fn-sf-article-records *crl-h*) (list *crl-w0* *crl-w2*))))

; -----------------------------------------------------------------------------
; The exec path: the fold on live stobjs, then the materialized rows, the
; article index against the store sequence, and the updates.

(defun crl-run (fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((fn-arena (fn-arena-clear fn-arena))
         (fn-cat (fn-cat-clear fn-cat)))
    (mv-let (fn-arena fn-cat)
      (fn-cat-load *crl-h* nil 0 fn-arena fn-cat)
      (let* ((loaded (list (fn-cat-count fn-cat) (fn-arena-count fn-arena)
                           (fn-cat-wire-list 0 fn-arena fn-cat)
                           (fn-cat-history-relation *crl-h* fn-arena fn-cat)
                           (fn-record-sequence (fn-cat-at 1 fn-cat))   ; store sequence 2 at index 1
                           (fn-cat-group-number "fn.test" 2 fn-cat)     ; number 2 is index 1
                           (fn-cat-msgid-seqs "<c@x>" fn-cat)))
             (fn-cat (fn-cat-withdraw 0 5 fn-cat))
             (fn-cat (fn-cat-redecide 1 (fn-hc-make (fn-stx-make-verdict :verified nil 4) nil 4) fn-cat))
             (kept (fn-cat-history-relation *crl-h* fn-arena fn-cat)))
        (mv (list loaded kept) fn-arena fn-cat)))))

(defun crl-exec ()
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (with-local-stobj fn-cat
        (mv-let (result fn-arena fn-cat)
          (crl-run fn-arena fn-cat)
          (mv result fn-arena)))
      result)))

(assert-event
 (equal (crl-exec)
        (list (list 2 2 (list *crl-w0* *crl-w2*) t 2 1 '(1))
              t)))

; -----------------------------------------------------------------------------
; The keystones on ground values (the logical side).

; The creators' logical values are nil (a stobj creator is not evaluated;
; the theorem opens the fold on the list model).
(defthm crl-w-load-from-empty
  (and (natp 0)
       (equal (create-fn-arena) nil) (equal (create-fn-cat) nil)
       (mv-let (a c)
         (fn-cat-load *crl-h* nil 0 nil nil)
         (and (fn-cat-history-relation *crl-h* a c)
              (equal (fn-cat-wire-list 0 a c) (list *crl-w0* *crl-w2*))
              (equal (fn-cat-count c) 2)
              (equal (fn-arena-count a) 2))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable create-fn-arena create-fn-cat))))

; The loaded state, on the logical side: the arena is the two payloads, the
; catalog the two rows over handles 0 and 1 with their numbers assigned.
(defconst *crl-a* (list *crl-p0* *crl-p2*))
(defun crl-held (w handle)
  (fn-held-make (fn-record-sequence w) (fn-record-txid w) (fn-record-generation w)
                (fn-record-msgid w) handle (fn-record-groups w) (fn-record-obligation-id w)
                (fn-record-content-subject w) (fn-record-release-evidence w)
                (fn-record-charge w) (fn-record-stamp w)
                (fn-held-facts-of (fn-record-payload w))
                (fn-held-context-of (fn-record-payload w) nil 0) nil nil))
(defconst *crl-c*
  (list (fn-cat-assign (crl-held *crl-w0* 0) nil)
        (fn-cat-assign (crl-held *crl-w2* 1) (list (fn-cat-assign (crl-held *crl-w0* 0) nil)))))
(defthm crl-w-loaded-is-the-fold
  (mv-let (a c)
    (fn-cat-load *crl-h* nil 0 nil nil)
    (and (equal a *crl-a*) (equal c *crl-c*)))
  :rule-classes nil)

; The entry is not vacuous, and extends: loading one more article onto the
; loaded state is the relation with the history extended.
(defconst *crl-w3* (fn-record-make 3 4 4 "<d@x>" *crl-p0* '("fn.test") "o" "s" "e" 1 5))
(defthm crl-w-load-establishes
  (and (fn-cat-history-relation *crl-h* *crl-a* *crl-c*)
       (natp 0)
       (mv-let (a c)
         (fn-cat-load (list *crl-w3*) nil 0 *crl-a* *crl-c*)
         (and (fn-cat-history-relation (append *crl-h* (list *crl-w3*)) a c)
              (equal (fn-cat-count c) 3))))
  :rule-classes nil)

; Without the relation at the start (a catalog whose row 0 does not
; materialize to the history's article): loading keeps it out.
(defconst *crl-c-bad*
  (list (fn-cat-assign (fn-held-make 0 1 1 "<z@x>" 0 '("fn.test") "o" "s" "e" 1 5
                                     (fn-hf-make 1 nil 0 nil) (fn-hc-make (fn-stx-make-verdict :absent nil 0) nil 0) nil nil)
                       nil)
        (nth 1 *crl-c*)))
(defthm crl-w-load-without-relation
  (and (not (fn-cat-history-relation *crl-h* *crl-a* *crl-c-bad*))
       (mv-let (a c)
         (fn-cat-load (list *crl-w3*) nil 0 *crl-a* *crl-c-bad*)
         (not (fn-cat-history-relation (append *crl-h* (list *crl-w3*)) a c))))
  :rule-classes nil)
(must-fail
 (defthm crl-r-load-without-relation
   (mv-let (a c)
     (fn-cat-load (list *crl-w3*) nil 0 *crl-a* *crl-c-bad*)
     (fn-cat-history-relation (append *crl-h* (list *crl-w3*)) a c))
   :rule-classes nil))

; Preserved by a withdrawal and a redecision.
(defthm crl-w-preserved
  (and (fn-cat-history-relation *crl-h* *crl-a* *crl-c*)
       (natp 0) (< 0 (fn-cat-count *crl-c*)) (natp 5)
       (fn-cat-history-relation *crl-h* *crl-a* (fn-cat-withdraw 0 5 *crl-c*))
       (natp 1) (< 1 (fn-cat-count *crl-c*)) (fn-hc-p (fn-hc-make (fn-stx-make-verdict :verified nil 4) nil 4))
       (fn-cat-history-relation *crl-h* *crl-a* (fn-cat-redecide 1 (fn-hc-make (fn-stx-make-verdict :verified nil 4) nil 4) *crl-c*))
       ; not vacuous: the updates change the rows
       (not (equal (fn-cat-withdraw 0 5 *crl-c*) *crl-c*))
       (not (equal (fn-cat-redecide 1 (fn-hc-make (fn-stx-make-verdict :verified nil 4) nil 4) *crl-c*) *crl-c*)))
  :rule-classes nil)

; Preserved by the completion: a prepared row over a handle the arena
; holds, whose wire is the record the history appends.
(defconst *crl-a3* (append *crl-a* (list *crl-p0*)))   ; = (fn-arena-seal-list *crl-p0* *crl-a*) by fn-arena-seal-list-is-append
(defconst *crl-held3*
  (fn-held-make 3 4 4 "<d@x>" 2 '("fn.test") "o" "s" "e" 1 5
                (fn-held-facts-of *crl-p0*) (fn-held-context-of *crl-p0* nil 0) nil nil))
(defconst *crl-pc* (fn-pc-make (cons 4 2) 2 *crl-held3* :plan :res))

(defthm crl-w-complete-preserves
  (and (fn-cat-history-relation *crl-h* *crl-a3* *crl-c*)
       (fn-pc-p *crl-pc*)
       (equal (cons 4 2) (fn-pc-token *crl-pc*))
       (equal (fn-pc-expected *crl-pc*) (fn-cat-count *crl-c*))
       (< (fn-record-payload (fn-pc-held *crl-pc*)) (fn-arena-count *crl-a3*))
       (equal (fn-held-wire-of (fn-pc-held *crl-pc*) *crl-a3*) *crl-w3*)
       (fn-record-p *crl-w3*)
       (fn-cat-history-relation (append *crl-h* (list *crl-w3*)) *crl-a3*
                                (mv-nth 2 (fn-cat-complete (cons 4 2) *crl-pc* *crl-c*)))
       (equal (fn-cat-count (mv-nth 2 (fn-cat-complete (cons 4 2) *crl-pc* *crl-c*))) 3))
  :rule-classes nil)

; Without the token: nothing commits, and the extended history is not
; related.
(defthm crl-w-complete-without-token
  (and (not (equal (cons 5 2) (fn-pc-token *crl-pc*)))
       (not (fn-cat-history-relation (append *crl-h* (list *crl-w3*)) *crl-a3*
                                     (mv-nth 2 (fn-cat-complete (cons 5 2) *crl-pc* *crl-c*)))))
  :rule-classes nil)
(must-fail
 (defthm crl-r-complete-without-token
   (fn-cat-history-relation (append *crl-h* (list *crl-w3*)) *crl-a3*
                            (mv-nth 2 (fn-cat-complete (cons 5 2) *crl-pc* *crl-c*)))
   :rule-classes nil))
