;; fn: the catalog, the generic (lane paged-catalog-2, 2026-10-01: split from
;; books/catalog-logic.lisp, which keeps the logical side, the old
;; foundation fn-cat$c, the correspondence and every obligation).  The split
;; is the arena's (books/payload-arena.lisp over payload-arena-extent-logic):
;; `attach-stobj' must precede the generic's `defabsstobj', so an
;; implementation book (books/catalog-paged.lisp) includes the logical side
;; without the generic, and books/catalog-paged-attach.lisp attaches it
;; before this book.  Every book above includes this one unchanged.

(in-package "ACL2")
(include-book "catalog-logic")

; -----------------------------------------------------------------------------
; The catalog.  The exports are stated over the list; `:attachable t' lets
; an image attach another implementation of the same logical side.

(defabsstobj fn-cat
  :foundation fn-cat$c
  :recognizer (fn-cat-p :logic fn-cat$ap :exec fn-cat$cp)
  :creator (create-fn-cat :logic create-fn-cat$a :exec create-fn-cat$c)
  :corr-fn fn-cat$corr-w
  :exports ((fn-cat-count :logic fn-cat$a-count :exec fn-cat$c-count)
            (fn-cat-at :logic fn-cat$a-at :exec fn-cat$c-at)
            (fn-cat-msgid-seqs :logic fn-cat$a-msgid-seqs :exec fn-cat$c-msgid-seqs)
            (fn-cat-group-number :logic fn-cat$a-group-number :exec fn-cat$c-group-number)
            (fn-cat-group-next :logic fn-cat$a-group-next :exec fn-cat$c-group-next)
            (fn-cat-group-count :logic fn-cat$a-group-count :exec fn-cat$c-group-count)
            (fn-cat-total-octets :logic fn-cat$a-total-octets :exec fn-cat$c-total-octets)
            (fn-cat-visible-at :logic fn-cat$a-visible-at :exec fn-cat$c-visible-at)
            (fn-cat-group-live-count :logic fn-cat$a-group-live-count
                                     :exec fn-cat$c-group-live-count)
            (fn-cat-group-live-low :logic fn-cat$a-group-live-low :exec fn-cat$c-group-live-low)
            (fn-cat-group-live-high :logic fn-cat$a-group-live-high
                                    :exec fn-cat$c-group-live-high)
            (fn-cat-horizon :logic fn-cat$a-horizon :exec fn-cat$c-horizon)
            (fn-cat-commit :logic fn-cat$a-commit :exec fn-cat$c-commit-w :protect t)
            (fn-cat-withdraw :logic fn-cat$a-withdraw :exec fn-cat$c-withdraw-w :protect t)
            (fn-cat-redecide :logic fn-cat$a-redecide :exec fn-cat$c-redecide :protect t)
            (fn-cat-clear :logic fn-cat$a-clear :exec fn-cat$c-clear-w :protect t)
            (fn-cat-withdrawn-at :logic fn-cat$a-withdrawn-at :exec fn-cat$c-withdrawn-at)
            (fn-cat-clear-keyed :logic fn-cat$a-clear-keyed :exec fn-cat$c-clear-keyed :protect t)
            (fn-cat-msgid-saturatedp :logic fn-cat$a-msgid-saturatedp :exec fn-cat$c-msgid-saturatedp)
            (fn-cat-index-health :logic fn-cat$a-index-health :exec fn-cat$c-index-health))
  :corr-fn-exists t
  :attachable t)

; -----------------------------------------------------------------------------
; The logical view, opened: a theorem over `fn-cat' is a theorem over the
; list of held records.

(defthm fn-cat-p-is-rowsp
  (equal (fn-cat-p x) (fn-cat-rowsp x)))

(defthm fn-cat-p-when-held-listp
  (implies (fn-held-listp x) (fn-cat-p x)))

(defthm fn-cat-count-is-len
  (equal (fn-cat-count fn-cat) (len fn-cat)))

(defthm fn-cat-at-is-nth
  (equal (fn-cat-at seq fn-cat) (nth seq fn-cat)))

(defthm fn-cat-msgid-seqs-is-seqs-for
  (equal (fn-cat-msgid-seqs msgid fn-cat) (fn-cat-seqs-for msgid fn-cat 0)))

(defthm fn-cat-group-number-is-number-seq
  (equal (fn-cat-group-number group n fn-cat) (fn-cat-number-seq group n fn-cat 0)))

(defthm fn-cat-group-next-is-high
  (equal (fn-cat-group-next group fn-cat) (+ 1 (fn-cat-group-high group fn-cat))))

(defthm fn-cat-group-count-is-rows
  (equal (fn-cat-group-count group fn-cat) (fn-cat-group-rows group fn-cat)))

(defthm fn-cat-total-octets-is-octets-of
  (equal (fn-cat-total-octets fn-cat) (fn-cat-octets-of fn-cat)))

(defthm fn-cat-visible-at-is-visiblep
  (equal (fn-cat-visible-at seq v fn-cat) (fn-cat-visiblep seq v fn-cat)))

(defthm fn-cat-commit-is-append
  (equal (fn-cat-commit h fn-cat) (append fn-cat (list (fn-cat-assign h fn-cat)))))

(defthm fn-cat-withdraw-is-mark
  (equal (fn-cat-withdraw target by fn-cat)
         (fn-cat-mark-withdrawn target (len fn-cat) by fn-cat)))

(defthm fn-cat-redecide-is-update-nth
  (equal (fn-cat-redecide seq context fn-cat)
         (update-nth seq (fn-held-with-context (nth seq fn-cat) context) fn-cat)))

(defthm fn-cat-clear-is-nil
  (equal (fn-cat-clear fn-cat) nil))

(defthm fn-cat-clear-keyed-is-nil
  (equal (fn-cat-clear-keyed key fn-cat) nil))

; THE SERVED REFUSAL over the opened view (books/msgid-pages-exec 7j): the
; fold over the rows and one more row carrying MSGID places it exactly when
; the refusal does not fire -- the POST that is accepted is indexed.
(defthm fn-cat-msgid-saturatedp-is-the-outcome
  (implies (equal msgid (fn-record-msgid h))
           (iff (equal (fn-mpxt-build-unplaced key (append fn-cat (list h)))
                       (fn-mpxt-build-unplaced key fn-cat))
                (not (fn-cat-msgid-saturatedp key msgid fn-cat))))
  :hints (("Goal" :in-theory (e/d (fn-cat-msgid-saturatedp fn-cat$a-msgid-saturatedp)
                                  (fn-mpxt-build-append fn-mpxt-build-saturatedp-is-the-build
                                   fn-mpxt-build-nil fn-mpxt-set-key-is-a-list mv-nth
                                   fn-mpxt-build-saturatedp-is-the-outcome))
           :use ((:instance fn-mpxt-build-saturatedp-is-the-outcome (rows fn-cat))))))

(defthm fn-cat-index-health-is-the-build
  (equal (fn-cat-index-health key fn-cat)
         (list (fn-mpxt-pages (fn-mpxt-build key fn-cat)) (fn-mpxt-count (fn-mpxt-build key fn-cat))
               (fn-mpxt-build-unplaced key fn-cat) (fn-mpxt-stuck (fn-mpxt-build key fn-cat)))))

(defthm fn-cat-group-live-count-is-count-from
  (equal (fn-cat-group-live-count g fn-cat)
         (fn-cat-live-count-from g 1 (fn-cat-group-high g fn-cat) fn-cat)))

(defthm fn-cat-group-live-low-is-first
  (equal (fn-cat-group-live-low g fn-cat)
         (fn-cat-live-first g 1 (fn-cat-group-high g fn-cat) fn-cat)))

(defthm fn-cat-group-live-high-is-last
  (equal (fn-cat-group-live-high g fn-cat)
         (fn-cat-live-last g (fn-cat-group-high g fn-cat) fn-cat)))

(defthm fn-cat-horizon-is-horizon-of
  (equal (fn-cat-horizon fn-cat)
         (if (fn-cat-rowsp fn-cat) (fn-cat-horizon-of fn-cat) (+ 1 (len fn-cat)))))

(defthm fn-cat-withdrawn-at-is-from
  (equal (fn-cat-withdrawn-at w fn-cat) (fn-cat-withdrawn-at-from w fn-cat 0)))

(in-theory (disable fn-cat-p fn-cat-count fn-cat-at fn-cat-msgid-seqs
                    fn-cat-group-number fn-cat-group-next fn-cat-group-count
                    fn-cat-total-octets fn-cat-visible-at fn-cat-commit
                    fn-cat-withdraw fn-cat-redecide fn-cat-clear
                    fn-cat-clear-keyed fn-cat-msgid-saturatedp fn-cat-index-health
                    fn-cat-group-live-count fn-cat-group-live-low fn-cat-group-live-high
                    fn-cat-horizon fn-cat-withdrawn-at
                    fn-cat-p-is-rowsp fn-cat-assign fn-cat-visiblep
                    fn-cat-mark-withdrawn fn-held-with-numbers
                    fn-held-with-withdrawn fn-held-with-context))

; KEYSTONES over the opened view: a commit appends one row whose numbers
; are one past each of its groups' highs, and leaves every row below the
; old count as it was; a number is bound to at most one row (the first
; found is the only one); a row withdrawn at version W is visible to a
; version V exactly when V <= W.

(defthm fn-cat-commit-keeps-rows
  (implies (and (natp seq) (< seq (fn-cat-count fn-cat)))
           (equal (fn-cat-at seq (fn-cat-commit h fn-cat))
                  (fn-cat-at seq fn-cat)))
  :hints (("Goal" :in-theory (enable fn-ctg-nth-of-append-below))))

(defthm fn-cat-commit-new-row
  (equal (fn-cat-at (fn-cat-count fn-cat) (fn-cat-commit h fn-cat))
         (fn-cat-assign h fn-cat))
  :hints (("Goal" :in-theory (enable fn-ctg-nth-of-append-at))))

(defthm fn-cat-commit-count
  (equal (fn-cat-count (fn-cat-commit h fn-cat)) (+ 1 (fn-cat-count fn-cat)))
  :hints (("Goal" :in-theory (enable fn-ctg-len-of-append))))

(defthm fn-cat-commit-binds-fresh-numbers
  (implies (and (fn-cat-p fn-cat) (member-equal g (fn-record-groups h)))
           (equal (fn-cat-group-number g (fn-cat-group-next g fn-cat) (fn-cat-commit h fn-cat))
                  (fn-cat-count fn-cat)))
  :hints (("Goal" :in-theory (enable fn-cat-p-is-rowsp fn-ctg-number-seq-of-fresh))))

(defthm fn-cat-visible-at-withdrawn
  (implies (and (natp seq) (natp v) (< seq (fn-cat-count fn-cat))
                (fn-held-withdrawn (fn-cat-at seq fn-cat)))
           (equal (fn-cat-visible-at seq v fn-cat)
                  (and (< seq v) (<= v (car (fn-held-withdrawn (fn-cat-at seq fn-cat)))))))
  :hints (("Goal" :in-theory (enable fn-cat-visiblep))))

; The full held recognizer of the rows, for a book that needs it beside
; fn-cat-p (the recognizer is the digest-free shape, fn-cat-rowsp): every
; export that changes the rows preserves it.
(defthm fn-cat-commit-keeps-held-listp
  (implies (and (fn-held-listp fn-cat) (fn-held-p h))
           (fn-held-listp (fn-cat-commit h fn-cat)))
  :hints (("Goal" :in-theory (enable fn-cat-commit-is-append))))

(defthm fn-cat-withdraw-keeps-held-listp
  (implies (and (fn-held-listp fn-cat) (natp target) (natp by))
           (fn-held-listp (fn-cat-withdraw target by fn-cat)))
  :hints (("Goal" :in-theory (enable fn-cat-withdraw-is-mark fn-cat-mark-withdrawn)
           :use ((:instance fn-cat-held-p-of-with-withdrawn
                            (h (nth target fn-cat)) (w (cons (len fn-cat) by)))
                 (:instance fn-held-withdrawnp (x (cons (len fn-cat) by)))))))

(defthm fn-cat-redecide-keeps-held-listp
  (implies (and (fn-held-listp fn-cat) (fn-hc-p context) (natp seq)
                (< seq (len fn-cat)))
           (fn-held-listp (fn-cat-redecide seq context fn-cat)))
  :hints (("Goal" :in-theory (enable fn-cat-redecide-is-update-nth))))

;; Withdrawn from includers (lane rule-hygiene, tools/rule_cost.py).
;; Each is tried in includers' proofs and pays for its frames in
;; almost none (planning/evidence/rule-cost-*.json has the counts;
;; docs/proof-style.md section 8).  An includer that needs one
;; enables it where it is used.
(in-theory (disable (:definition fn-scat-msgid-idp)))
