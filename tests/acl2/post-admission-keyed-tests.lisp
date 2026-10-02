; Teeth for books/post-admission-keyed.lisp (lane paged-history-6, PRF-1044):
; the served POST's admission with the keyed Message-ID index.
;
; Positive witnesses assert the complete antecedent and conclusion of each
; theorem on ground values: a :scale profile under the nil carry
; (fn-pvc-carryp nil, as tests/acl2/store-profile-carried-tests.lisp), a key
; derived from a node-secret entry (fn-mpxt-key-of-entry), three held rows
; and a fourth carrying the POST's Message-ID.  The exec path runs on a live
; local catalog.  The `:mpx-saturated' branch has NO ground witness here: a
; home page saturates only past its slots (books/msgid-pages-exec
; *fn-mpxt-page-slots*, 1,024, and its overflow), which no ground fixture
; reaches; the natives' 10,000-row family (tests/test_native_reader_index.py)
; shows the index placing every row (unplaced 0, stuck 0).

(in-package "ACL2")
(include-book "../../books/post-admission-keyed")
(include-book "must-fail-checked")

; -----------------------------------------------------------------------------
; The host runs compiled code: the subject is guard-verified.

(assert-event
 (and (eq (symbol-class 'fn-pak-post-admission (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pak-index-health-line (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-cat$c-msgid-saturatedp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-cat$c-clear-keyed (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-cat$c-index-health (w state)) :common-lisp-compliant)))

; -----------------------------------------------------------------------------
; Ground values.

(defconst *pak-profile* (fn-bs-config-for-profile :scale))
(defconst *pak-key*
  (fn-mpxt-key-of-entry (fn-ns-create-entry '(112 97 107) (make-list 32 :initial-element 9))))
(defconst *pak-other-key*
  (fn-mpxt-key-of-entry (fn-ns-create-entry '(112 97 107) (make-list 32 :initial-element 10))))

(assert-event (and (fn-pvc-carryp nil)
                   (fn-mpxt-keyp *pak-key*) (equal (len *pak-key*) *fn-mpxt-key-octets*)
                   (not (equal *pak-key* *pak-other-key*))))

(defun pak-held (seq msgid groups octets)
  (fn-held-make seq (+ 1 seq) 0 msgid seq groups "o" "s" "e" 1 5
                (fn-hf-make octets 14 2 nil)
                (fn-hc-make (fn-stx-make-verdict :unverified nil 0) nil 0) nil nil))

(defconst *pak-h0* (pak-held 0 "<pak-zero@example.invalid>" '("fn.test") 100))
(defconst *pak-h1* (pak-held 1 "<pak-one@example.invalid>" '("fn.test") 200))
(defconst *pak-h2* (pak-held 2 "<pak-two@example.invalid>" '("fn.test") 300))
(defconst *pak-rows* (list *pak-h0* *pak-h1* *pak-h2*))
(defconst *pak-msgid* "<pak-three@example.invalid>")
(defconst *pak-msgid-octets* (fn-record-string-octets *pak-msgid*))
(defconst *pak-h3* (pak-held 3 *pak-msgid* '("fn.test") 400))

;; fn-pak-post-admission reads the live catalog (an abstract stobj takes no
;; ground constant): a local fn-cat keyed with KEY and holding ROWS, then the
;; host's admission call itself.
(defun pak-commit-rows (rows fn-cat)
  (declare (xargs :stobjs fn-cat :mode :program))
  (if (endp rows) fn-cat
    (let ((fn-cat (fn-cat-commit (car rows) fn-cat)))
      (pak-commit-rows (cdr rows) fn-cat))))

(defun pak-admit-run (carry profile msgid-octets payload-length group-count charge key rows fn-cat)
  (declare (xargs :stobjs fn-cat :mode :program))
  (let* ((fn-cat (fn-cat-clear-keyed key fn-cat))
         (fn-cat (pak-commit-rows rows fn-cat)))
    (mv (fn-pak-post-admission carry profile msgid-octets payload-length group-count charge
                               key fn-cat)
        fn-cat)))

(defun pak-admit (carry profile msgid-octets payload-length group-count charge key rows)
  (declare (xargs :mode :program))
  (with-local-stobj fn-cat
    (mv-let (verdict fn-cat)
      (pak-admit-run carry profile msgid-octets payload-length group-count charge key rows fn-cat)
      verdict)))

(assert-event (and (fn-held-p *pak-h0*) (fn-held-p *pak-h1*) (fn-held-p *pak-h2*)
                   (fn-held-p *pak-h3*)
                   (equal (fn-record-msgid *pak-h3*) (fn-record-octets-string *pak-msgid-octets*))))

; -----------------------------------------------------------------------------
; The boundary admits this POST (the antecedent of the keystone is not
; vacuous): payload 2,048 octets, one group, charge 3.

(assert-event
 (equal (fn-pvc-post-boundary-carried nil *pak-profile* *pak-msgid-octets* 2048 1 3) :ok))

; fn-pak-post-admission over the opened view (a live catalog holding the
; rows, pak-admit): :ok, and the keystone's conclusion -- the fold over the rows and the
; fourth row places it (no unplaced row is added).
(assert-event
 (and (equal (pak-admit nil *pak-profile* *pak-msgid-octets* 2048 1 3
                                    *pak-key* *pak-rows*)
             :ok)
      (equal (fn-mlh-build-unplaced *pak-key* (append *pak-rows* (list *pak-h3*)))
             (fn-mlh-build-unplaced *pak-key* *pak-rows*))
      (equal (fn-mlh-build-unplaced *pak-key* (append *pak-rows* (list *pak-h3*))) 0)))

; fn-pak-post-admission-refused-is-the-boundary-by-definition: every bound's
; refusal passes through, whatever the key and the catalog; and the sixth
; word is never the boundary's (fn-pak-boundary-never-says-mpx-saturated).
(assert-event
 (let ((bad-msgid (fn-record-string-octets "not a message id")))
   (and (equal (fn-pvc-post-boundary-carried nil *pak-profile* bad-msgid 2048 1 3)
               :bad-message-id)
        (equal (pak-admit nil *pak-profile* bad-msgid 2048 1 3 *pak-key* *pak-rows*)
               :bad-message-id)
        (equal (pak-admit nil *pak-profile* *pak-msgid-octets* 2048 0 3
                                      *pak-key* *pak-rows*)
               (fn-pvc-post-boundary-carried nil *pak-profile* *pak-msgid-octets* 2048 0 3))
        (not (equal (fn-pvc-post-boundary-carried nil *pak-profile* *pak-msgid-octets* 2048 0 3)
                    :ok))
        (not (equal (fn-pvc-post-boundary-carried nil *pak-profile* *pak-msgid-octets* 2048 0 3)
                    :mpx-saturated)))))

; fn-pak-post-admission-is-a-named-verdict: each answer above is one of the
; six words, and the six texts are distinct printable lines
; (books/store-budget-naming.lisp).
(assert-event
 (and (fn-sbud-post-boundary-verdictp
       (pak-admit nil *pak-profile* *pak-msgid-octets* 2048 1 3 *pak-key* *pak-rows*))
      (fn-sbud-post-boundary-verdictp
       (pak-admit nil *pak-profile* *pak-msgid-octets* 2048 0 3 *pak-key* *pak-rows*))
      (fn-sbud-post-boundary-verdictp :mpx-saturated)
      (not (fn-sbud-post-boundary-verdictp :unnamed))
      (equal (fn-sbud-post-boundary-refusal :mpx-saturated) *fn-sbud-refusal-mpx-saturated*)
      (fn-sbud-printable-ascii-p *fn-sbud-refusal-mpx-saturated*)
      (no-duplicatesp-equal
       (list (fn-sbud-post-boundary-refusal :bad-message-id)
             (fn-sbud-post-boundary-refusal :payload-bound)
             (fn-sbud-post-boundary-refusal :group-bound)
             (fn-sbud-post-boundary-refusal :charge-bound)
             (fn-sbud-post-boundary-refusal :mpx-saturated)
             (fn-sbud-post-boundary-refusal :unnamed)))
      (null (fn-sbud-post-boundary-refusal :ok))))

; Hypothesis-removal witness for the keystone's Message-ID hypothesis: a
; fourth row carrying ANOTHER Message-ID is placed too here, but the theorem
; says nothing about it -- the conclusion is checked, the omitted hypothesis
; fails, and the retained one (the verdict :ok) holds.
(assert-event
 (let ((other (pak-held 3 "<pak-other@example.invalid>" '("fn.test") 400)))
   (and (equal (pak-admit nil *pak-profile* *pak-msgid-octets* 2048 1 3
                                      *pak-key* *pak-rows*)
               :ok)
        (not (equal (fn-record-msgid other) (fn-record-octets-string *pak-msgid-octets*))))))

; -----------------------------------------------------------------------------
; The executable path on a live local catalog: the keyed clear, three
; commits, the served refusal under the table's own key (two page reads)
; and under another key (the fold over the rows, unreachable in
; composition, the same answer), the health line.

(defun pak-exec-run (fn-cat)
  (declare (xargs :stobjs fn-cat))
  (let* ((fn-cat (fn-cat-clear-keyed *pak-key* fn-cat))
         (fn-cat (fn-cat-commit *pak-h0* fn-cat))
         (fn-cat (fn-cat-commit *pak-h1* fn-cat))
         (fn-cat (fn-cat-commit *pak-h2* fn-cat))
         (own (fn-pak-post-admission nil *pak-profile* *pak-msgid-octets* 2048 1 3
                                     *pak-key* fn-cat))
         (other (fn-pak-post-admission nil *pak-profile* *pak-msgid-octets* 2048 1 3
                                       *pak-other-key* fn-cat))
         (health (fn-cat-index-health *pak-key* fn-cat))
         (line (fn-pak-index-health-line health))
         (fn-cat (fn-cat-clear fn-cat)))
    (mv (list own other health line (fn-cat-count fn-cat)) fn-cat)))

(defun pak-exec ()
  (with-local-stobj fn-cat
    (mv-let (result fn-cat) (pak-exec-run fn-cat) result)))

(assert-event
 (let* ((result (pak-exec))
        (health (third result)))
   (and (equal (first result) :ok)
        (equal (second result) :ok)
        ; fn-cat-index-health-is-the-build: (pages entries unplaced stuck)
        (equal health (list (fn-mlh-pages (fn-mlh-build *pak-key* *pak-rows*))
                            (fn-mlh-count (fn-mlh-build *pak-key* *pak-rows*))
                            (fn-mlh-build-unplaced *pak-key* *pak-rows*)
                            (fn-mlh-stuck (fn-mlh-build *pak-key* *pak-rows*))))
        (equal (second health) 3) (equal (third health) 0) (equal (fourth health) 0)
        (fn-sbud-printable-ascii-p (butlast (fourth result) 1))
        (equal (car (last (fourth result))) 10)
        (equal (fifth result) 0))))

; The health line of a malformed answer names it unavailable, still one line.
(assert-event
 (and (equal (car (last (fn-pak-index-health-line nil))) 10)
      (not (equal (fn-pak-index-health-line nil) (fn-pak-index-health-line '(1 2 3 4))))))

; -----------------------------------------------------------------------------
; The keystone is not a restatement: without the verdict hypothesis the
; conclusion is not provable (a saturated table refuses exactly the rows it
; cannot place: fn-pak-post-admission-saturated-is-not-indexed).

(must-fail-checked
 (defthm pak-r-indexed-without-the-verdict
   (implies (equal (fn-record-msgid h) (fn-record-octets-string msgid-octets))
            (equal (fn-mlh-build-unplaced key (append fn-cat (list h)))
                   (fn-mlh-build-unplaced key fn-cat)))
   :rule-classes nil))
