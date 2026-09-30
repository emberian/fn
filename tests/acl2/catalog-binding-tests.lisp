(in-package "ACL2")
(include-book "../../books/catalog")
(include-book "../../books/acceptance-binding-held")
(include-book "../../books/crypto-attach")

(defun fn-cbt-row (binding)
  (declare (xargs :guard t))
  (fn-held-plain
   (fn-record-make 1 2 3 "<a>" '(66 13 10) '("g") "o" "s" "e" 4 5 binding)
   0))

; Actual catalog commit/withdraw/redecide preserve the received binding.
(defun fn-cbt-preservation-check ()
  (declare (xargs :guard t :verify-guards nil))
  (let* ((b (fn-ab-for-received :relay-v1 '(65 13 10)))
        (h (fn-cbt-row b)))
   (and (fn-ab-p b) (fn-held-p h) (fn-cat-rowp h)
        (with-local-stobj fn-cat
          (mv-let (ok fn-cat)
            (let* ((fn-cat (fn-cat-commit h fn-cat))
                   (committed (fn-cat-at 0 fn-cat))
                   (commit-ok
                    (and (equal (fn-cat-count fn-cat) 1)
                         (equal (fn-cat-msgid-seqs "<a>" fn-cat) '(0))
                         (fn-cat-rowp committed)
                         (fn-held-p committed)
                         (equal (fn-held-binding committed) b)
                         (equal (fn-ab-held-binding-action "<a>" b committed)
                                :same-binding)))
                   (fn-cat (fn-cat-withdraw 0 0 fn-cat))
                   (withdrawn (fn-cat-at 0 fn-cat))
                   (withdraw-ok
                    (and (fn-cat-rowp withdrawn)
                         (consp (fn-held-withdrawn withdrawn))
                         (equal (fn-held-binding withdrawn) b)
                         (equal (fn-cat-msgid-seqs "<a>" fn-cat) '(0))
                         (equal (fn-ab-held-binding-action "<a>" b withdrawn)
                                :same-binding)))
                   (fn-cat (fn-cat-redecide 0
                             (fn-hc-make (fn-stx-make-verdict :absent nil 1) nil 1)
                             fn-cat))
                   (redecided (fn-cat-at 0 fn-cat)))
              (mv (and commit-ok withdraw-ok (fn-cat-rowp redecided)
                       (equal (fn-held-binding redecided) b)
                       (equal (fn-cat-msgid-seqs "<a>" fn-cat) '(0))
                       (equal (fn-ab-held-binding-action "<a>" b redecided)
                              :same-binding))
                  fn-cat))
            ok)))))

(assert-event (fn-cbt-preservation-check))

; A missing mandatory descriptor violates the maintained catalog row shape;
; every other field comes from the same valid row (corrupted-state mutation).
(assert-event
 (let* ((b (fn-ab-for-received :relay-v1 '(65 13 10)))
        (h (fn-cbt-row b))
        (corrupt (update-nth 15 nil h)))
   (and (fn-held-p h) (fn-cat-rowp h)
        (fn-held-shapep corrupt)
        (equal (take 15 corrupt) (take 15 h))
        (not (fn-ab-p (fn-held-binding corrupt)))
        (not (fn-cat-rowp corrupt))
        (equal (fn-ab-held-binding-action "<a>" b corrupt) :recovery-required))))

; Deliberately bypassing the composed acceptance writer can commit two rows
; under one Message-ID.  rowp alone therefore cannot be the accepted-row
; association/uniqueness invariant.  This is a corrupted-state witness,
; not a production acceptance path.  The first historical descriptor remains.
(defun fn-cbt-corrupt-duplicate-check ()
  (declare (xargs :guard t :verify-guards nil))
  (let* ((first (fn-ab-for-received :relay-v1 '(65 13 10)))
        (second (fn-ab-for-received :native-source '(65 13 10)))
        (h1 (fn-cbt-row first))
        (h2 (fn-cbt-row second)))
   (and (fn-held-p h1) (fn-held-p h2)
        (not (equal first second))
        (with-local-stobj fn-cat
          (mv-let (ok fn-cat)
            (let* ((fn-cat (fn-cat-commit h1 fn-cat))
                   (fn-cat (fn-cat-commit h2 fn-cat)))
              (mv (and (equal (fn-cat-count fn-cat) 2)
                       (equal (fn-cat-msgid-seqs "<a>" fn-cat) '(0 1))
                       (equal (fn-held-binding (fn-cat-at 0 fn-cat)) first)
                       (equal (fn-held-binding (fn-cat-at 1 fn-cat)) second)
                       (equal (fn-ab-held-binding-action "<a>" second
                                                         (fn-cat-at 0 fn-cat))
                              :conflict))
                  fn-cat))
            ok)))))

(assert-event (fn-cbt-corrupt-duplicate-check))
