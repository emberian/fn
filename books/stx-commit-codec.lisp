; fn: membership commit payload codec, shared by transport and committed evidence.
(in-package "ACL2")
(include-book "statement-invariants")
(include-book "membership-epochs-invariants")
(defconst *fn-stx-max-commit-octets* 512)

(defun fn-stx-op-of-code (n)
  (declare (xargs :guard t))
  (cond ((equal n 0) :add)
        ((equal n 1) :remove)
        ((equal n 2) :rotate)
        (t nil)))

(defun fn-stx-op-code (op)
  (declare (xargs :guard t))
  (cond ((equal op :add) 0)
        ((equal op :remove) 1)
        ((equal op :rotate) 2)
        (t 3)))

(defthm fn-stx-op-of-code-is-an-op
  (implies (fn-stx-op-of-code n)
           (fn-me-opp (fn-stx-op-of-code n))))

(defun fn-stx-commit-items (c)
  (declare (xargs :guard (fn-me-commitp c)))
  (list (cons :bytes (fn-me-commit-id c))
        (cons :uint (fn-me-commit-base c))
        (cons :bytes (fn-me-commit-actor c))
        (cons :uint (fn-stx-op-code (fn-me-commit-op c)))
        (cons :bytes (fn-me-commit-subject c))))

(defun fn-stx-commit-encodablep (c)
  (declare (xargs :guard t))
  (and (fn-me-commitp c)
       (fn-cbor-octet-listp (fn-me-commit-id c))
       (fn-record-uint32p (fn-me-commit-base c))
       (fn-cbor-octet-listp (fn-me-commit-actor c))
       (fn-cbor-octet-listp (fn-me-commit-subject c))))

(defun fn-stx-commit-encode (c)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-stx-commit-encodablep c)
      (fn-stmt-encode-items (fn-stx-commit-items c))
    nil))

(defun fn-stx-commit-of-items (items)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory
                                 (enable fn-stmt-uint-item-p
                                         fn-stmt-bytes-item-p)))))
  (if (not (and (consp items) (fn-stmt-bytes-item-p (car items))))
      (fn-stmt-error :id)
    (let ((i1 (cdr items)))
      (if (not (and (consp i1) (fn-stmt-uint-item-p (car i1))))
          (fn-stmt-error :base)
        (let ((i2 (cdr i1)))
          (if (not (and (consp i2) (fn-stmt-bytes-item-p (car i2))))
              (fn-stmt-error :actor)
            (let ((i3 (cdr i2)))
              (if (not (and (consp i3) (fn-stmt-uint-item-p (car i3))
                            (fn-stx-op-of-code (cdr (car i3)))))
                  (fn-stmt-error :op)
                (let ((i4 (cdr i3)))
                  (if (not (and (consp i4) (fn-stmt-bytes-item-p (car i4))))
                      (fn-stmt-error :subject)
                    (if (not (null (cdr i4)))
                        (fn-stmt-error :trailing)
                      (fn-stmt-ok
                       (fn-me-commit (cdr (car items)) (cdr (car i1))
                                     (cdr (car i2))
                                     (fn-stx-op-of-code (cdr (car i3)))
                                     (cdr (car i4)))))))))))))))

(defun fn-stx-commit-decode-exact (octets)
  (declare (xargs :guard t))
  (if (not (fn-cbor-at-mostp octets *fn-stx-max-commit-octets*))
      (fn-stmt-error :limit)
    (let ((items (fn-stmt-decode-items 5 octets)))
      (if (not (fn-stmt-okp items))
          items
        (fn-stx-commit-of-items (fn-stmt-value items))))))

; fn-stmt-okp, fn-stmt-value and fn-stmt-ok are opaque here: books/statement
; withdraws their definitions and books/statement-invariants withdraws the
; result algebra that relates them (fn-stmt-invariants-vocabulary).  Nothing
; in this book's include chain re-opens either, so without the two rewrites
; named below the accepting branch of fn-stx-commit-of-items stops at
; (fn-me-commitp (fn-stmt-value (fn-stmt-ok (fn-me-commit ...)))) -- the
; commit is built and the conclusion cannot see it.  The two rewrites are
; enabled AT THIS FORM (docs/proof-style.md, "never enable a vocabulary
; book-wide"): each is about fn-stmt-ok alone, so neither fans.
;
; No shape fact about fn-stmt-decode-items is needed.  Every field the
; conclusion constrains is constrained by fn-stx-commit-of-items' own branch
; tests: the base by fn-stmt-uint-item-p (hence fn-record-uint32p, hence
; natp) and the op by fn-stx-op-of-code-is-an-op.  The decoder stays disabled.
(defthm fn-stx-commit-decode-is-a-commit
  (implies (fn-stmt-okp (fn-stx-commit-decode-exact octets))
           (fn-me-commitp (fn-stmt-value (fn-stx-commit-decode-exact octets))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-me-commitp fn-me-commit fn-stmt-uint-item-p
                            fn-record-uint32p fn-me-opp
                            fn-stmt-okp-of-ok fn-stmt-value-of-ok
                            (:d fn-stx-commit-of-items)
                            (:d fn-stx-commit-decode-exact))
                           (fn-stmt-decode-items fn-cbor-at-mostp)))))

(in-theory (disable (:d fn-stx-commit-of-items)
                    (:d fn-stx-commit-decode-exact)
                    (:d fn-stx-commit-encode)))

; -----------------------------------------------------------------------------
; The commits a contact batch carries
;
; A commit enters only from a VERIFIED statement: fn-stx-batch-delta is
; already the verified projection, so the scan below never sees an
; unverified article's payload.

(defun fn-stx-commit-of-statement (s)
  (declare (xargs :guard (fn-stmt-p s) :guard-hints (("Goal" :in-theory (enable fn-stmt-p)))))
  (if (not (equal (fn-stmt-kind s) :policy))
      nil
    (let ((r (fn-stx-commit-decode-exact (fn-stmt-payload s))))
      (if (fn-stmt-okp r)
          (fn-stmt-value r)
        nil))))

(defthm fn-stx-commit-of-statement-is-a-commit
  (implies (fn-stx-commit-of-statement s)
           (fn-me-commitp (fn-stx-commit-of-statement s)))
  :hints (("Goal" :in-theory (disable fn-stx-commit-decode-exact))))

