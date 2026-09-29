;; The transaction file name, the scan's naming seam, as a leaf book.
;;
;; books/byte-store-scan.lisp's second constrained function (its header: "Two
;; seams are constrained functions"), and the observation pairing over it,
;; lived in the scan; books/byte-store-txn-name.lisp, which realizes the seam
;; with the decimal renderer and attaches it, needed nothing else of the scan
;; but included the whole byte store tower above it (byte-store-frame, 641
;; dependents, of which 389 reached it only through the renderer).  The seam
;; needs only fn-bs-namep (books/byte-store.lisp).  Every form is moved
;; verbatim from the scan, which includes this book.
(in-package "ACL2")
(include-book "byte-store")

; The transaction file name.  The decimal format "{:020d}.txn" is the host's
; (tools/run_store.py); what the scan needs of it is that it is a name and
; that distinct sequence numbers get distinct names.
(encapsulate
  (((fn-bs-txn-name *) => *))
  (local
   (defun fn-bs-txn-chars (n)
     (declare (xargs :guard t :verify-guards nil :measure (nfix n)))
     (if (zp n) nil (cons #\a (fn-bs-txn-chars (1- n))))))
  (local
   (defthm fn-bs-txn-chars-are-characters
     (character-listp (fn-bs-txn-chars n))))
  (local
   (defthm fn-bs-txn-chars-length
     (equal (len (fn-bs-txn-chars n)) (nfix n))))
  (local
   (defthm fn-bs-txn-chars-injective
     (implies (and (natp i) (natp j)
                   (equal (fn-bs-txn-chars i) (fn-bs-txn-chars j)))
              (equal i j))
     :rule-classes nil
     :hints (("Goal" :use ((:instance fn-bs-txn-chars-length (n i))
                           (:instance fn-bs-txn-chars-length (n j)))
              :in-theory (disable fn-bs-txn-chars-length)))))
  (local
   (defthm fn-bs-coerce-list-of-string
     (implies (character-listp x)
              (equal (coerce (coerce x 'string) 'list) x))
     :rule-classes nil
     :hints (("Goal" :use coerce-inverse-2))))
  ; Under the minimal theory nothing rewrites the two coerce terms away, so
  ; the string equality carries to the character lists by congruence.
  (local
   (defthm fn-bs-txn-chars-injective-through-coerce
     (implies (and (natp i) (natp j)
                   (equal (coerce (fn-bs-txn-chars i) 'string)
                          (coerce (fn-bs-txn-chars j) 'string)))
              (equal i j))
     :rule-classes nil
     :hints (("Goal"
              :use ((:instance fn-bs-coerce-list-of-string (x (fn-bs-txn-chars i)))
                    (:instance fn-bs-coerce-list-of-string (x (fn-bs-txn-chars j)))
                    fn-bs-txn-chars-injective
                    (:instance fn-bs-txn-chars-are-characters (n i))
                    (:instance fn-bs-txn-chars-are-characters (n j)))
              :in-theory (theory 'minimal-theory)))))
  (local (defun fn-bs-txn-name (n) (coerce (fn-bs-txn-chars n) 'string)))
  (defthm fn-bs-txn-name-is-a-name
    (fn-bs-namep (fn-bs-txn-name n)))
  (defthm fn-bs-txn-name-is-injective
    (implies (and (natp i) (natp j) (not (equal i j)))
             (not (equal (fn-bs-txn-name i) (fn-bs-txn-name j))))
    :hints (("Goal" :use fn-bs-txn-chars-injective-through-coerce))))

; The pairing the host's observer calls (host/native store observer): each
; sorted observed transaction name bound to the scan codec's sequence.
(defun fn-bs-txn-observation-pairs (names sequence)
  "Bind each sorted observed transaction name to the scan codec's sequence."
  (declare (xargs :guard t :verify-guards nil))
  (if (consp names)
      (if (equal (car names) (fn-bs-txn-name sequence))
          ; `nfix': `fn-bs-txn-observation-covered' (books/byte-store-txn-name)
          ; reaches this function in the branch where its own `natp' checks
          ; failed, so `:guard t' here leaves (acl2-numberp sequence) with
          ; nothing to prove it and the guard conjecture suggests no induction.
          ; The two callers start at 0 or at a checked lower bound, so `nfix'
          ; is the identity on the composed machine.
          (let ((rest (fn-bs-txn-observation-pairs (cdr names)
                                                   (1+ (nfix sequence)))))
            (if (equal rest :invalid)
                :invalid
              (cons (list sequence (car names)) rest)))
        :invalid)
    (if (null names) nil :invalid)))

(verify-guards fn-bs-txn-observation-pairs)
