; fn prototype (lane proto-adt-2, 2026-09-27): the snapshot BYTES of an ADT
; value.  NOT on a served path; no host calls it.
;
; FNADTSN2 (lane arena-store-3, 2026-09-28; coordinator decision 4 of
; 2026-09-28: free region placement).  The canonical image of a value
; (books/proto/adt-lib.lisp `adt-canon') has one byte form, a function of the
; value alone:
;
;   page 0, the header (little-endian u64 words unless noted):
;     octets 0-7    magic "FNADTSN2"
;     octets 8-15   format version 2
;     octets 16-47  the schema digest: SHA-256 of `adt-schema-octets'
;     octets 48-55  N, the record count
;     octets 56-63  R, the region count: one per column, then the pool
;     octets 64+16r region r's first page;  72+16r  its length in octets
;     octets 64+16R NPAGES, the image's page count
;     zeros to the end of the page
;   then region r at its first page, zero-padded to (adt-cap used) pages:
;     a column: N cells, (adt-bwidth kind) octets each, little-endian --
;       a scalar field's encoded value (adt-enc), or for an :octets field
;       two columns, the offset and the length in the pool (8 octets each);
;     the pool: every :octets value, in record order, fields in schema
;       order (the canonical image's pool: adt-canon appends in that order,
;       so the offset column is the running sum of the lengths before it).
;
; The canonical image places the regions in order after the header
; (`adt-starts-l').  The decoder accepts ANY placement the header states
; (`adt-placement-ok': every region after page 0, inside NPAGES, apart from
; every other), so a region that outgrows its pages moves to new pages at
; the image's end and nothing else moves (books/history-pages-grow.lisp);
; pages no region holds are not read.  FNADTSN1 (contiguous placement, no
; NPAGES word) is refused :magic.
;
; Pages are 16384 octets (2048 little-endian u64 words): the page store's
; page (lane proto-pagestore, books/proto/pagestore.lisp *pgs-page-words*),
; and `adt-page-digests' is the SHA-256 of each page's octets in order, the
; page store's per-page digest (its `pgs-digest' over a page's content) and
; the Merkle tree's leaf level.  A region takes a power-of-two number of
; pages, so its pages move only when it doubles.
;
; Theorems:
;   adt-decode-ser       the decoder inverts the serializer on every value
;                        whose image is addressable by u64 offsets
;   adt-ser-image-of-corr   the bytes of ANY image corresponding to A are
;                        (adt-ser s a): two histories that reach the same
;                        value reach the same bytes (path independence)
;   adt-kser-image-of-kcorr the same for a keyed set, over its live view
;   adt-page-digest-nth  leaf K is the digest of page K

(in-package "ACL2")
(include-book "adt-bytes-lib")
(include-book "adt-key-lib")
(include-book "../sha256")
(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (disable nth update-nth nthcdr take)))

; -----------------------------------------------------------------------------
; A. Widths, and which schemas have a byte form.

(defun adt-width-for (b)
  ; octets for a natural at most B
  (declare (xargs :guard (natp b)))
  (cond ((< (nfix b) 256) 1)
        ((< (nfix b) 65536) 2)
        ((< (nfix b) 4294967296) 4)
        (t 8)))

(defun adt-bwidth (k)
  (declare (xargs :guard (adt-kindp k)))
  (case (car k)
    ((:u8 :bool) 1)
    (:u32 4)
    (:u64 8)
    (:nat (adt-width-for (cadr k)))
    (:enum (adt-width-for (len (cdr k))))
    (otherwise 8)))

(defun adt-bkindp (k)
  (declare (xargs :guard t))
  (and (adt-kindp k)
       (case (car k)
         (:nat (< (cadr k) *adt-u64-limit*))
         (:enum (and (symbol-listp (cdr k)) (< (len (cdr k)) *adt-u64-limit*)))
         (otherwise t))))

(defun adt-bschemap1 (s)
  (declare (xargs :guard t))
  (if (atom s) (null s) (and (adt-bkindp (car s)) (adt-bschemap1 (cdr s)))))

(defun adt-bschemap (s)
  ; a schema with a byte form: every kind representable, the header in a page
  (declare (xargs :guard t))
  (and (adt-schemap s) (adt-bschemap1 s)
       (<= (+ 72 (* 16 (+ 1 (adt-ncols s)))) *adt-page*)))

(defun adt-col-widths (s)
  (declare (xargs :guard (adt-schemap s)))
  (if (atom s) nil
    (if (adt-octets-kind-p (car s))
        (list* 8 8 (adt-col-widths (cdr s)))
      (cons (adt-bwidth (car s)) (adt-col-widths (cdr s))))))

(defthm adt-len-col-widths
  (equal (len (adt-col-widths s)) (adt-ncols s)))

(local
 (defthm adt-index-below-len-b
   (implies (member-equal v l) (< (adt-index v l) (len l)))
   :rule-classes :linear))

(defthm adt-enc-below-width
  (implies (and (adt-bkindp k) (not (adt-octets-kind-p k)) (adt-val-okp k v))
           (and (natp (adt-enc k v))
                (< (adt-enc k v) (expt 2 (* 8 (adt-bwidth k))))))
  :hints (("Goal" :in-theory (enable adt-enc adt-val-okp))))

; -----------------------------------------------------------------------------
; B. The schema digest.


(defun adt-char-codes (cs)
  (declare (xargs :guard (character-listp cs)))
  (if (atom cs) nil (cons (char-code (car cs)) (adt-char-codes (cdr cs)))))

(defun adt-sym-octets (x)
  (declare (xargs :guard (symbolp x)))
  (let ((p (coerce (symbol-package-name x) 'list))
        (n (coerce (symbol-name x) 'list)))
    (append (adt-le 2 (len p)) (adt-char-codes p)
            (adt-le 2 (len n)) (adt-char-codes n))))

(defun adt-syms-octets (xs)
  (declare (xargs :guard (symbol-listp xs)))
  (if (atom xs) nil (append (adt-sym-octets (car xs)) (adt-syms-octets (cdr xs)))))

(defun adt-kind-octets (k)
  (declare (xargs :guard (adt-bkindp k)))
  (case (car k)
    (:u8 '(1)) (:u32 '(2)) (:u64 '(3)) (:bool '(4))
    (:nat (cons 5 (adt-le 8 (cadr k))))
    (:enum (append (cons 6 (adt-le 8 (len (cdr k)))) (adt-syms-octets (cdr k))))
    (otherwise '(7))))

(defun adt-schema-octets (s)
  ; the schema, as octets: each kind in order
  (declare (xargs :guard (adt-bschemap1 s)))
  (if (atom s) nil (append (adt-kind-octets (car s)) (adt-schema-octets (cdr s)))))

(defun adt-schema-digest (s)
  (declare (xargs :guard (adt-bschemap1 s)))
  (fn-sha256 (append (adt-le 8 (len s)) (adt-schema-octets s))))

(defthm adt-schema-digest-shape
  (and (true-listp (adt-schema-digest s)) (equal (len (adt-schema-digest s)) 32))
  :hints (("Goal" :use ((:instance fn-sha256-shape (m (append (adt-le 8 (len s)) (adt-schema-octets s)))))
           :in-theory (disable fn-sha256-shape fn-sha256))))

(defthm adt-take-32-schema-digest
  (equal (take 32 (adt-schema-digest s)) (adt-schema-digest s))
  :hints (("Goal" :use ((:instance adt-take-len-self (x (adt-schema-digest s))))
           :in-theory (disable adt-take-len-self adt-schema-digest))))

(defthm adt-nthcdr-32-schema-digest
  (equal (nthcdr 32 (adt-schema-digest s)) nil)
  :hints (("Goal" :use ((:instance adt-nthcdr-len-self (x (adt-schema-digest s))))
           :in-theory (disable adt-nthcdr-len-self adt-schema-digest))))

(in-theory (disable adt-schema-digest))

; -----------------------------------------------------------------------------
; C. Cells: each record as its flat columns' cells, the pool position
; threaded through; and the pool.

(defun adt-row-cells (s r pos)
  ; (cells . next-pos)
  (declare (xargs :verify-guards nil))
  (if (atom s)
      (cons nil (nfix pos))
    (if (adt-octets-kind-p (car s))
        (let ((rest (adt-row-cells (cdr s) (cdr r) (+ (nfix pos) (len (car r))))))
          (cons (list* (nfix pos) (len (car r)) (car rest)) (cdr rest)))
      (let ((rest (adt-row-cells (cdr s) (cdr r) pos)))
        (cons (cons (adt-enc (car s) (car r)) (car rest)) (cdr rest))))))

(defun adt-row-pool (s r)
  (declare (xargs :verify-guards nil))
  (if (atom s) nil
    (if (adt-octets-kind-p (car s))
        (append (car r) (adt-row-pool (cdr s) (cdr r)))
      (adt-row-pool (cdr s) (cdr r)))))

(defun adt-rows-cells (s a pos)
  (declare (xargs :verify-guards nil))
  (if (atom a) nil
    (cons (car (adt-row-cells s (car a) pos))
          (adt-rows-cells s (cdr a) (cdr (adt-row-cells s (car a) pos))))))

(defun adt-rows-pool (s a)
  (declare (xargs :verify-guards nil))
  (if (atom a) nil (append (adt-row-pool s (car a)) (adt-rows-pool s (cdr a)))))

(defthm adt-row-cells-next
  (equal (cdr (adt-row-cells s r pos)) (+ (nfix pos) (len (adt-row-pool s r)))))

(defthm adt-true-listp-row-pool
  (true-listp (adt-row-pool s r))
  :rule-classes :type-prescription)

(defthm adt-true-listp-rows-pool
  (true-listp (adt-rows-pool s a))
  :rule-classes :type-prescription)

(defthm adt-len-row-cells
  (and (true-listp (car (adt-row-cells s r pos)))
       (equal (len (car (adt-row-cells s r pos))) (adt-ncols s))))

(defthm adt-rows-of-len-rows-cells
  (adt-rows-of-len (adt-ncols s) (adt-rows-cells s a pos)))

(defthm adt-len-rows-cells
  (equal (len (adt-rows-cells s a pos)) (len a)))

(defthm adt-octetsp-row-pool
  (implies (adt-rec-p s r) (adt-octetsp (adt-row-pool s r)))
  :hints (("Goal" :in-theory (enable adt-rec-p adt-val-okp))))

(defthm adt-octetsp-rows-pool
  (implies (adt-seq-p s a) (adt-octetsp (adt-rows-pool s a))))

; Every cell of a row fits its column's width, given room in the pool.
(defun adt-cells-fit (ws cells)
  (declare (xargs :guard t))
  (if (atom ws) t
    (and (consp cells) (natp (car cells)) (< (car cells) (expt 2 (* 8 (nfix (car ws)))))
         (adt-cells-fit (cdr ws) (cdr cells)))))

(defthm adt-row-cells-fit
  (implies (and (adt-bschemap1 s) (adt-rec-p s r) (natp pos)
                (< (+ pos (len (adt-row-pool s r))) *adt-u64-limit*))
           (adt-cells-fit (adt-col-widths s) (car (adt-row-cells s r pos))))
  :hints (("Goal" :induct (adt-row-cells s r pos)
           :in-theory (e/d (adt-rec-p) (adt-val-okp adt-bwidth adt-bkindp adt-kindp)))))

(defun adt-rows-fit (ws rows)
  (declare (xargs :guard t))
  (if (atom rows) t (and (adt-cells-fit ws (car rows)) (adt-rows-fit ws (cdr rows)))))

(defthm adt-rows-cells-fit
  (implies (and (adt-bschemap1 s) (adt-seq-p s a) (natp pos)
                (< (+ pos (len (adt-rows-pool s a))) *adt-u64-limit*))
           (adt-rows-fit (adt-col-widths s) (adt-rows-cells s a pos))))

(defthm adt-rows-fit-column
  (implies (and (adt-rows-fit ws rows) (consp ws))
           (and (adt-all-below (adt-cars rows) (expt 2 (* 8 (nfix (car ws)))))
                (adt-rows-fit (cdr ws) (adt-cdrs rows)))))

; -----------------------------------------------------------------------------
; D. The image.

(defconst *adt-magic* '(70 78 65 68 84 83 78 50))   ; "FNADTSN2"
(defconst *adt-version* 2)

(defun adt-col-regs (ws cols)
  (declare (xargs :verify-guards nil))
  (if (atom ws) nil
    (cons (adt-le-list (nfix (car ws)) (car cols)) (adt-col-regs (cdr ws) (cdr cols)))))

(defun adt-regs (s a)
  (declare (xargs :verify-guards nil))
  (append (adt-col-regs (adt-col-widths s) (adt-transpose (adt-ncols s) (adt-rows-cells s a 0)))
          (list (adt-rows-pool s a))))

(defun adt-meta (starts lens)
  (declare (xargs :verify-guards nil))
  (if (atom starts) nil
    (append (adt-le 8 (car starts)) (adt-le 8 (car lens)) (adt-meta (cdr starts) (cdr lens)))))

(defthm adt-unle-append
  (implies (<= (nfix w) (len x))
           (equal (adt-unle w (append x rest)) (adt-unle w x))))

(defun adt-hdr-const ()
  ; the magic and the version: the first 16 octets
  (declare (xargs :guard t))
  (append *adt-magic* (adt-le 8 *adt-version*)))

(defthm adt-hdr-const-facts
  (and (true-listp (adt-hdr-const))
       (equal (len (adt-hdr-const)) 16)
       (equal (take 8 (adt-hdr-const)) *adt-magic*)
       (equal (len (nthcdr 8 (adt-hdr-const))) 8)
       (equal (nthcdr 16 (adt-hdr-const)) nil)
       (equal (adt-unle 8 (nthcdr 8 (adt-hdr-const))) *adt-version*))
  :hints (("Goal" :in-theory (enable take nthcdr))))

(in-theory (disable adt-hdr-const (:executable-counterpart adt-hdr-const)))

(defun adt-header-content (s n regs)
  ; FNADTSN2: after the region table, the image's page count
  (declare (xargs :verify-guards nil))
  (append (adt-hdr-const) (adt-schema-digest s)
          (adt-le 8 n) (adt-le 8 (len regs))
          (adt-meta (adt-starts regs 1) (adt-lens regs))
          (adt-le 8 (adt-end regs 1))))

(defun adt-header (s n regs)
  (declare (xargs :verify-guards nil))
  (let ((h (adt-header-content s n regs)))
    (append h (adt-zeros (- *adt-page* (len h))))))

(defun adt-ser (s a)
  ; THE snapshot bytes of the value A
  (declare (xargs :verify-guards nil))
  (let ((regs (adt-regs s a)))
    (append (adt-header s (len a) regs) (adt-body regs))))

; -----------------------------------------------------------------------------
; E. The decoder.  Every check refuses by name; none repairs.

(defun adt-read-meta (r b)
  ; R (first-page, length) pairs: (starts . lengths)
  (declare (xargs :guard (and (natp r) (true-listp b))))
  (if (zp r)
      (cons nil nil)
    (let ((rest (adt-read-meta (1- r) (nthcdr 16 b))))
      (cons (cons (adt-unle 8 b) (car rest))
            (cons (adt-unle 8 (nthcdr 8 b)) (cdr rest))))))

(defun adt-starts-l (lens start)
  (declare (xargs :guard (and (nat-listp lens) (natp start))))
  (if (atom lens) nil
    (cons (nfix start) (adt-starts-l (cdr lens) (+ (nfix start) (adt-cap (nfix (car lens))))))))

(defun adt-end-l (lens start)
  (declare (xargs :guard (and (nat-listp lens) (natp start))))
  (if (atom lens) (nfix start)
    (adt-end-l (cdr lens) (+ (nfix start) (adt-cap (nfix (car lens)))))))

; FNADTSN2: a region may lie anywhere after the header, inside the image
; and apart from every other region.  The canonical image (`adt-ser') places
; them in order (`adt-starts-l'); an image whose region grew by moving it to
; new pages places it elsewhere, and the decoder reads it where the header
; says.
(defun adt-apart (s c starts lens)
  ; the region [S, S+C) and every region of STARTS/LENS share no page
  (declare (xargs :guard (and (natp s) (natp c) (true-listp starts) (nat-listp lens))))
  (if (or (atom starts) (atom lens)) t
    (let ((s2 (nfix (car starts))) (c2 (adt-cap (nfix (car lens)))))
      (and (or (zp c) (zp c2) (<= (+ s c) s2) (<= (+ s2 c2) s))
           (adt-apart s c (cdr starts) (cdr lens))))))

(defun adt-placement-ok (starts lens np)
  ; every region after the header page, inside NP pages, apart from the rest
  (declare (xargs :guard (and (true-listp starts) (nat-listp lens) (natp np))))
  (if (or (atom starts) (atom lens)) t
    (let ((s (car starts)) (c (adt-cap (nfix (car lens)))))
      (and (natp s) (<= 1 s) (<= (+ s c) (nfix np))
           (adt-apart s c (cdr starts) (cdr lens))
           (adt-placement-ok (cdr starts) (cdr lens) np)))))

(defun adt-col-sizes-ok (ws n useds)
  (declare (xargs :guard t))
  (if (atom ws) t
    (and (consp useds) (equal (car useds) (* (nfix (car ws)) (nfix n)))
         (adt-col-sizes-ok (cdr ws) n (cdr useds)))))

(defun adt-dec-cols (ws n starts useds b)
  (declare (xargs :verify-guards nil))
  (if (atom ws) nil
    (cons (adt-unle-list (nfix (car ws)) n
                         (take (nfix (car useds)) (nthcdr (* *adt-page* (nfix (car starts))) b)))
          (adt-dec-cols (cdr ws) n (cdr starts) (cdr useds) b))))

(defun adt-dec-row (s cells pool pos)
  ; (ok values next-pos): scalar cells must lie in their column type,
  ; octets cells must be the running offset and lie in the pool
  (declare (xargs :verify-guards nil))
  (if (atom s)
      (list t nil (nfix pos))
    (if (adt-octets-kind-p (car s))
        (let ((off (car cells)) (ln (cadr cells)))
          (if (and (equal off (nfix pos)) (natp ln) (<= (+ (nfix pos) ln) (len pool)))
              (let ((rest (adt-dec-row (cdr s) (cddr cells) pool (+ (nfix pos) ln))))
                (list (car rest) (cons (take ln (nthcdr (nfix pos) pool)) (cadr rest)) (caddr rest)))
            (list nil nil (nfix pos))))
      (if (adt-elt-p (adt-ctype (car s)) (car cells))
          (let ((rest (adt-dec-row (cdr s) (cdr cells) pool pos)))
            (list (car rest) (cons (adt-dec (car s) (car cells)) (cadr rest)) (caddr rest)))
        (list nil nil (nfix pos))))))

(defun adt-dec-rows (s rows pool pos)
  ; (ok records end-pos)
  (declare (xargs :verify-guards nil))
  (if (atom rows)
      (list t nil (nfix pos))
    (let ((r (adt-dec-row s (car rows) pool pos)))
      (if (car r)
          (let ((rest (adt-dec-rows s (cdr rows) pool (caddr r))))
            (list (car rest) (cons (cadr r) (cadr rest)) (caddr rest)))
        (list nil nil (nfix pos))))))

(defun adt-decode (s b)
  ; (:ok records) or (:refused reason)
  (declare (xargs :verify-guards nil))
  (let* ((m (adt-ncols s)) (nreg (+ 1 m)))
    (cond ((not (true-listp b)) (list :refused :not-a-list))
          ((< (len b) *adt-page*) (list :refused :short))
          ((not (equal (take 8 b) *adt-magic*)) (list :refused :magic))
          ((not (equal (adt-unle 8 (nthcdr 8 b)) *adt-version*)) (list :refused :version))
          ((not (equal (take 32 (nthcdr 16 b)) (adt-schema-digest s))) (list :refused :schema))
          ((not (equal (adt-unle 8 (nthcdr 56 b)) nreg)) (list :refused :regions))
          (t
           (let* ((n (adt-unle 8 (nthcdr 48 b)))
                  (meta (adt-read-meta nreg (nthcdr 64 b)))
                  (starts (car meta))
                  (useds (cdr meta))
                  (np (adt-unle 8 (nthcdr (+ 64 (* 16 nreg)) b)))
                  (ws (adt-col-widths s)))
             (cond ((not (adt-placement-ok starts useds np)) (list :refused :placement))
                   ((not (adt-col-sizes-ok ws n useds)) (list :refused :column-size))
                   ((not (equal (len b) (* *adt-page* np))) (list :refused :length))
                   (t
                    (let* ((cols (adt-dec-cols ws n starts useds b))
                           (pool (take (nfix (nth m useds)) (nthcdr (* *adt-page* (nfix (nth m starts))) b)))
                           (rows (adt-dec-rows s (adt-untranspose n cols) pool 0)))
                      (if (and (car rows) (equal (caddr rows) (len pool)))
                          (list :ok (cadr rows))
                        (list :refused :cells))))))))))

; -----------------------------------------------------------------------------
; F. Each part's inverse.

(local
 (defthm adt-append-assoc-b
   (equal (append (append a b) c) (append a (append b c)))))

(local
 (defthm adt-append-nil-b
   (implies (true-listp x) (equal (append x nil) x))))

(defthm adt-unle-le-alone
  (implies (and (natp x) (natp w) (< x (expt 2 (* 8 w))))
           (equal (adt-unle w (adt-le w x)) x))
  :hints (("Goal" :use ((:instance adt-unle-le (rest nil))) :in-theory (disable adt-unle-le))))

(defthm adt-unle-list-le-list-alone
  (implies (and (natp w) (adt-all-below xs (expt 2 (* 8 w))) (true-listp xs))
           (equal (adt-unle-list w (len xs) (adt-le-list w xs)) xs))
  :hints (("Goal" :use ((:instance adt-unle-list-le-list (rest nil)))
           :in-theory (disable adt-unle-list-le-list))))

(defthm adt-len-meta
  (equal (len (adt-meta starts lens)) (* 16 (len starts))))

(defthm adt-read-meta-meta
  (implies (and (adt-all-below starts *adt-u64-limit*) (adt-all-below lens *adt-u64-limit*)
                (true-listp starts) (true-listp lens) (equal (len lens) (len starts)))
           (equal (adt-read-meta (len starts) (append (adt-meta starts lens) rest))
                  (cons starts lens)))
  :hints (("Goal" :induct (adt-meta starts lens))))

(defthm adt-starts-is-starts-l
  (equal (adt-starts regs start) (adt-starts-l (adt-lens regs) start)))

(defthm adt-end-is-end-l
  (equal (adt-end regs start) (adt-end-l (adt-lens regs) start)))

(local
 (defun adt-dec-cols-induct (ws cols regs start prefix)
   (declare (xargs :verify-guards nil))
   (if (atom ws)
       (list cols regs start prefix)
     (adt-dec-cols-induct (cdr ws) (cdr cols) (cdr regs)
                          (+ (nfix start) (adt-cap (len (car regs))))
                          (append prefix (adt-pad (car regs)))))))

(defun adt-cols-fit (ws cols)
  (declare (xargs :guard t))
  (if (atom ws) t
    (and (consp cols) (adt-all-below (car cols) (expt 2 (* 8 (nfix (car ws)))))
         (true-listp (car cols))
         (adt-cols-fit (cdr ws) (cdr cols)))))

(defun adt-cols-len (cols n)
  (declare (xargs :guard t))
  (if (atom cols) t (and (equal (len (car cols)) (nfix n)) (adt-cols-len (cdr cols) n))))

(defthm adt-true-list-listp-col-regs
  (true-list-listp (adt-col-regs ws cols)))

(defthm adt-true-list-listp-append
  (implies (and (true-list-listp x) (true-list-listp y)) (true-list-listp (append x y))))

(defthm adt-dec-cols-of-image
  (implies (and (adt-cols-fit ws cols) (adt-cols-len cols n) (true-listp cols) (natp n)
                (equal (len cols) (len ws)) (nat-listp ws)
                (equal regs (append (adt-col-regs ws cols) more))
                (true-list-listp more)
                (natp start) (true-listp prefix) (equal (len prefix) (* *adt-page* start)))
           (equal (adt-dec-cols ws n (adt-starts regs start) (adt-lens regs)
                                (append prefix (adt-body regs)))
                  cols))
  :hints (("Goal" :induct (adt-dec-cols-induct ws cols regs start prefix)
           :in-theory (disable adt-starts-is-starts-l adt-pad)
           :expand ((adt-body regs)))
          ("Subgoal *1/2" :use ((:instance adt-region-of-image (r 0))))))

(local
 (defun adt-dec-row-induct (s r pos pre)
   (declare (xargs :verify-guards nil))
   (if (atom s)
       (list r pos pre)
     (if (adt-octets-kind-p (car s))
         (adt-dec-row-induct (cdr s) (cdr r) (+ (nfix pos) (len (car r))) (append pre (car r)))
       (adt-dec-row-induct (cdr s) (cdr r) pos pre)))))

(defthm adt-dec-row-of-cells
  (implies (and (adt-schemap s) (adt-rec-p s r) (natp pos) (true-listp pre) (equal (len pre) pos))
           (equal (adt-dec-row s (car (adt-row-cells s r pos)) (append pre (adt-row-pool s r) post) pos)
                  (list t r (+ pos (len (adt-row-pool s r))))))
  :hints (("Goal" :induct (adt-dec-row-induct s r pos pre)
           :in-theory (enable adt-rec-p adt-val-okp))))

(local
 (defun adt-dec-rows-induct (s a pos pre)
   (declare (xargs :verify-guards nil))
   (if (atom a)
       (list pos pre)
     (adt-dec-rows-induct s (cdr a) (+ (nfix pos) (len (adt-row-pool s (car a))))
                          (append pre (adt-row-pool s (car a)))))))

(defthm adt-dec-rows-of-cells
  (implies (and (adt-schemap s) (adt-seq-p s a) (natp pos) (true-listp pre) (equal (len pre) pos))
           (equal (adt-dec-rows s (adt-rows-cells s a pos) (append pre (adt-rows-pool s a) post) pos)
                  (list t a (+ pos (len (adt-rows-pool s a))))))
  :hints (("Goal" :induct (adt-dec-rows-induct s a pos pre)
           :in-theory (disable adt-dec-row adt-row-cells))
          ("Subgoal *1/2" :use ((:instance adt-dec-row-of-cells (r (car a))
                                           (post (append (adt-rows-pool s (cdr a)) post)))))))

; The header's fields read back.
(defthm adt-lens-starts-shape
  (and (true-listp (adt-lens regs)) (equal (len (adt-lens regs)) (len regs))
       (true-listp (adt-starts-l lens start)) (equal (len (adt-starts-l lens start)) (len lens))))

(defthm adt-len-starts
  (equal (len (adt-starts regs start)) (len regs)))

(defthm adt-len-header-content
  (equal (len (adt-header-content s n regs)) (+ 72 (* 16 (len regs))))
  :hints (("Goal" :in-theory (enable adt-header-content))))

(local
 (defthm adt-unle-past-meta
   (implies (and (true-listp starts) (equal (len lens) (len starts)))
            (equal (nthcdr (* 16 (len starts)) (append (adt-meta starts lens) rest)) rest))
   :hints (("Goal" :induct (adt-meta starts lens) :in-theory (enable nthcdr)))))

(defthm adt-header-reads
  (implies (and (<= (+ 72 (* 16 (len regs))) *adt-page*)
                (natp n) (< n *adt-u64-limit*) (< (len regs) *adt-u64-limit*)
                (adt-all-below (adt-starts regs 1) *adt-u64-limit*)
                (adt-all-below (adt-lens regs) *adt-u64-limit*)
                (< (adt-end regs 1) *adt-u64-limit*))
           (let ((b (append (adt-header s n regs) body)))
             (and (equal (take 8 b) *adt-magic*)
                  (equal (adt-unle 8 (nthcdr 8 b)) *adt-version*)
                  (equal (take 32 (nthcdr 16 b)) (adt-schema-digest s))
                  (equal (adt-unle 8 (nthcdr 48 b)) n)
                  (equal (adt-unle 8 (nthcdr 56 b)) (len regs))
                  (equal (adt-read-meta (len regs) (nthcdr 64 b))
                         (cons (adt-starts regs 1) (adt-lens regs)))
                  (equal (adt-unle 8 (nthcdr (+ 64 (* 16 (len regs))) b)) (adt-end regs 1))
                  (equal (len (adt-header s n regs)) *adt-page*))))
  :hints (("Goal" :in-theory (e/d (adt-header adt-header-content) (adt-starts-is-starts-l adt-end-is-end-l))
           :use ((:instance adt-read-meta-meta (starts (adt-starts regs 1)) (lens (adt-lens regs))
                            (rest (append (adt-le 8 (adt-end regs 1))
                                          (adt-zeros (- *adt-page* (+ 72 (* 16 (len regs))))) body)))
                 (:instance adt-unle-past-meta (starts (adt-starts regs 1)) (lens (adt-lens regs))
                            (rest (append (adt-le 8 (adt-end regs 1))
                                          (adt-zeros (- *adt-page* (+ 72 (* 16 (len regs))))) body)))))))

; Every first page and every length is below the image's end.
(defthm adt-end-l-lower
  (implies (natp start) (<= start (adt-end-l lens start)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable adt-cap))))

(defthm adt-starts-l-below-end
  (implies (and (natp start) (natp lim) (< (adt-end-l lens start) lim))
           (adt-all-below (adt-starts-l lens start) lim)))

(defthm adt-lens-below-image
  (implies (and (nat-listp lens) (natp start) (natp lim)
                (< (* *adt-page* (adt-end-l lens start)) lim))
           (adt-all-below lens lim))
  :hints (("Goal" :induct (adt-end-l lens start) :in-theory (disable adt-cap))
          ("Subgoal *1/2" :use ((:instance adt-cap-covers (u (car lens)))
                                (:instance adt-end-l-lower (lens (cdr lens))
                                           (start (+ start (adt-cap (car lens)))))))))

(defthm adt-nat-listp-lens
  (nat-listp (adt-lens regs)))

(local
 (defun adt-wsrows-induct (ws rows)
   (declare (xargs :verify-guards nil))
   (if (atom ws) (list ws rows) (adt-wsrows-induct (cdr ws) (adt-cdrs rows)))))

(defthm adt-true-listp-cars
  (true-listp (adt-cars rows)))

(defthm adt-cols-fit-of-transpose
  (implies (adt-rows-fit ws rows)
           (adt-cols-fit ws (adt-transpose (len ws) rows)))
  :hints (("Goal" :induct (adt-wsrows-induct ws rows))
          ("Subgoal *1/2" :expand ((adt-transpose (len ws) rows))
           :use ((:instance adt-rows-fit-column)))))

(defthm adt-cols-len-of-transpose
  (implies (equal n (len rows))
           (adt-cols-len (adt-transpose m rows) n)))

(defthm adt-col-sizes-of-regs
  (implies (and (adt-cols-len cols n) (equal (len cols) (len ws)) (nat-listp ws) (natp n)
                (equal regs (append (adt-col-regs ws cols) more)))
           (adt-col-sizes-ok ws n (adt-lens regs))))

(defthm adt-len-col-regs
  (equal (len (adt-col-regs ws cols)) (len ws)))

(defthm adt-nat-listp-col-widths
  (nat-listp (adt-col-widths s)))

(defthm adt-len-regs
  (equal (len (adt-regs s a)) (+ 1 (adt-ncols s))))

(defthm adt-len-ser
  (implies (adt-bschemap s)
           (equal (len (adt-ser s a)) (* *adt-page* (adt-end (adt-regs s a) 1))))
  :hints (("Goal" :in-theory (e/d (adt-header) (adt-end-is-end-l adt-regs))
           :use ((:instance adt-len-body (regs (adt-regs s a)) (start 1))))))

(defthm adt-nth-lens
  (implies (and (natp r) (< r (len regs)))
           (equal (nth r (adt-lens regs)) (len (nth r regs))))
  :hints (("Goal" :in-theory (enable nth))))

(local
 (defthm adt-nth-len-append
   (equal (nth (len x) (append x (list p))) p)
   :hints (("Goal" :in-theory (enable nth) :induct (len x)))))

(defthm adt-nth-append-at-len
  (implies (equal m (len x))
           (equal (nth m (append x (list p))) p)))

(defthm adt-len-region-below-body
  (implies (and (natp r) (< r (len regs)))
           (<= (len (nth r regs)) (len (adt-body regs))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable nth) :induct (nth r regs))))

(defthm adt-ser-is-header-body
  (equal (append (adt-header s (len a) (adt-regs s a)) (adt-body (adt-regs s a)))
         (adt-ser s a)))

(defthm adt-header-true-listp
  (true-listp (adt-header s n regs))
  :hints (("Goal" :in-theory (enable adt-header))))

(in-theory (disable adt-ser adt-header))

(defthm adt-rows-pool-is-last-region
  (equal (nth (adt-ncols s) (adt-regs s a)) (adt-rows-pool s a))
  :hints (("Goal" :in-theory (enable adt-regs)
           :use ((:instance adt-nth-append-at-len (m (adt-ncols s))
                            (x (adt-col-regs (adt-col-widths s)
                                             (adt-transpose (adt-ncols s) (adt-rows-cells s a 0))))
                            (p (adt-rows-pool s a)))))))

(defthm adt-regs-is
  (equal (adt-regs s a)
         (append (adt-col-regs (adt-col-widths s) (adt-transpose (adt-ncols s) (adt-rows-cells s a 0)))
                 (list (adt-rows-pool s a))))
  :rule-classes nil)

(defthm adt-true-list-listp-regs
  (true-list-listp (adt-regs s a)))

(in-theory (disable adt-regs))

; The decoder's reads of a serialized image, one step at a time.
(defun adt-ser-okp (s a)
  ; the image is addressable: a byte schema, a value, u64 counts and offsets
  (declare (xargs :verify-guards nil))
  (and (adt-bschemap s) (adt-seq-p s a)
       (< (len a) *adt-u64-limit*)
       (< (len (adt-ser s a)) *adt-u64-limit*)))

(defthm adt-len-header
  (implies (<= (+ 72 (* 16 (len regs))) *adt-page*)
           (equal (len (adt-header s n regs)) *adt-page*))
  :hints (("Goal" :in-theory (enable adt-header))))

(defthm adt-len-ser-body
  (implies (adt-bschemap s)
           (equal (len (adt-ser s a)) (+ *adt-page* (len (adt-body (adt-regs s a))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (adt-bschemap) (adt-ser-is-header-body adt-len-ser))
           :use ((:instance adt-ser-is-header-body)))))

(local
 (defun adt-rl-induct (r lens start)
   (if (or (zp r) (atom lens)) (list r lens start)
     (adt-rl-induct (1- r) (cdr lens) (+ (nfix start) (adt-cap (nfix (car lens))))))))

(defthm adt-natp-nth-starts-l
  (implies (and (natp r) (< r (len lens)))
           (natp (nth r (adt-starts-l lens start))))
  :rule-classes (:rewrite
                 (:rewrite :corollary
                           (implies (and (natp r) (< r (len lens)))
                                    (and (integerp (nth r (adt-starts-l lens start)))
                                         (<= 0 (nth r (adt-starts-l lens start)))))))
  :hints (("Goal" :in-theory (e/d (nth) (adt-cap)) :induct (adt-rl-induct r lens start))))

(defthm adt-len-pool-below-ser
  (implies (adt-bschemap s)
           (<= (len (adt-rows-pool s a)) (len (adt-ser s a))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable adt-len-region-below-body adt-len-ser adt-len-body)
           :use ((:instance adt-len-ser-body)
                 (:instance adt-len-region-below-body (regs (adt-regs s a)) (r (adt-ncols s)))))))

(defthm adt-ser-okp-bounds
  (implies (adt-ser-okp s a)
           (and (adt-all-below (adt-starts-l (adt-lens (adt-regs s a)) 1) *adt-u64-limit*)
                (adt-all-below (adt-lens (adt-regs s a)) *adt-u64-limit*)
                (< (len (adt-rows-pool s a)) *adt-u64-limit*)
                (equal (len (adt-ser s a)) (* *adt-page* (adt-end-l (adt-lens (adt-regs s a)) 1)))))
  :hints (("Goal" :in-theory (e/d (adt-bschemap adt-ser-okp) (adt-len-ser adt-starts-l-below-end adt-lens-below-image
                                                               adt-len-region-below-body))
           :use ((:instance adt-len-ser)
                 (:instance adt-len-ser-body)
                 (:instance adt-starts-l-below-end (lens (adt-lens (adt-regs s a))) (start 1)
                            (lim *adt-u64-limit*))
                 (:instance adt-lens-below-image (lens (adt-lens (adt-regs s a))) (start 1)
                            (lim *adt-u64-limit*))
                 (:instance adt-len-region-below-body (regs (adt-regs s a)) (r (adt-ncols s)))
                 (:instance adt-len-header-content (n (len a)) (regs (adt-regs s a)))))))

(defthm adt-ser-header-reads
  (implies (adt-ser-okp s a)
           (let ((b (adt-ser s a)))
             (and (true-listp b)
                  (<= *adt-page* (len b))
                  (equal (take 8 b) *adt-magic*)
                  (equal (adt-unle 8 (nthcdr 8 b)) *adt-version*)
                  (equal (take 32 (nthcdr 16 b)) (adt-schema-digest s))
                  (equal (adt-unle 8 (nthcdr 48 b)) (len a))
                  (equal (adt-unle 8 (nthcdr 56 b)) (+ 1 (adt-ncols s)))
                  (equal (adt-read-meta (+ 1 (adt-ncols s)) (nthcdr 64 b))
                         (cons (adt-starts-l (adt-lens (adt-regs s a)) 1) (adt-lens (adt-regs s a))))
                  (equal (adt-unle 8 (nthcdr (+ 80 (* 16 (adt-ncols s))) b))
                         (adt-end-l (adt-lens (adt-regs s a)) 1)))))
  :hints (("Goal" :in-theory (e/d (adt-bschemap adt-ser-okp) (adt-header-reads adt-ser-okp-bounds adt-ser-is-header-body))
           :use ((:instance adt-ser-okp-bounds)
                 (:instance adt-ser-is-header-body)
                 (:instance adt-header-reads (n (len a)) (regs (adt-regs s a))
                            (body (adt-body (adt-regs s a))))))))

(defthm adt-ser-columns
  (implies (adt-ser-okp s a)
           (and (adt-col-sizes-ok (adt-col-widths s) (len a) (adt-lens (adt-regs s a)))
                (equal (adt-dec-cols (adt-col-widths s) (len a)
                                     (adt-starts-l (adt-lens (adt-regs s a)) 1)
                                     (adt-lens (adt-regs s a))
                                     (adt-ser s a))
                       (adt-transpose (adt-ncols s) (adt-rows-cells s a 0)))))
  :hints (("Goal" :in-theory (e/d (adt-bschemap adt-ser-okp) (adt-dec-cols-of-image adt-ser-okp-bounds adt-cols-fit-of-transpose
                                                                         adt-ser-is-header-body adt-col-sizes-of-regs))
           :use ((:instance adt-ser-okp-bounds)
                 (:instance adt-regs-is)
                 (:instance adt-ser-is-header-body)
                 (:instance adt-rows-cells-fit (pos 0))
                 (:instance adt-cols-fit-of-transpose (ws (adt-col-widths s)) (rows (adt-rows-cells s a 0)))
                 (:instance adt-col-sizes-of-regs (ws (adt-col-widths s)) (n (len a))
                            (cols (adt-transpose (adt-ncols s) (adt-rows-cells s a 0)))
                            (regs (adt-regs s a))
                            (more (list (adt-rows-pool s a))))
                 (:instance adt-dec-cols-of-image
                            (ws (adt-col-widths s)) (n (len a))
                            (cols (adt-transpose (adt-ncols s) (adt-rows-cells s a 0)))
                            (regs (adt-regs s a)) (more (list (adt-rows-pool s a)))
                            (start 1) (prefix (adt-header s (len a) (adt-regs s a))))))))

(defthm adt-ser-pool
  (implies (adt-ser-okp s a)
           (equal (take (len (adt-rows-pool s a))
                        (nthcdr (* *adt-page* (nth (adt-ncols s) (adt-starts-l (adt-lens (adt-regs s a)) 1)))
                                (adt-ser s a)))
                  (adt-rows-pool s a)))
  :hints (("Goal" :in-theory (e/d (adt-bschemap adt-ser-okp) (adt-region-of-image adt-ser-okp-bounds adt-ser-is-header-body))
           :use ((:instance adt-ser-okp-bounds)
                 (:instance adt-ser-is-header-body)
                 (:instance adt-region-of-image (regs (adt-regs s a)) (r (adt-ncols s)) (start 1)
                            (prefix (adt-header s (len a) (adt-regs s a))))))))

(in-theory (disable adt-ser-okp))

; The canonical placement is a placement.
(local
 (defun adt-all-at-least (xs b)
   (if (atom xs) t (and (<= b (nfix (car xs))) (adt-all-at-least (cdr xs) b)))))

(local
 (defthm adt-starts-l-at-least
   (implies (and (natp s) (natp b) (<= b s)) (adt-all-at-least (adt-starts-l lens s) b))
   :hints (("Goal" :in-theory (disable adt-cap)))))

(local
 (defthm adt-apart-when-after
   (implies (and (natp s) (natp c) (adt-all-at-least starts (+ s c)))
            (adt-apart s c starts lens))
   :hints (("Goal" :in-theory (disable adt-cap)))))

(defthm adt-placement-ok-of-starts-l
  (implies (and (natp s) (<= 1 s))
           (adt-placement-ok (adt-starts-l lens s) lens (adt-end-l lens s)))
  :hints (("Goal" :induct (adt-end-l lens s) :in-theory (disable adt-cap))
          ("Subgoal *1/2" :use ((:instance adt-end-l-lower (lens (cdr lens)) (start (+ s (adt-cap (nfix (car lens))))))
                                (:instance adt-starts-l-at-least (lens (cdr lens)) (s (+ s (adt-cap (nfix (car lens)))))
                                           (b (+ s (adt-cap (nfix (car lens))))))
                                (:instance adt-apart-when-after (c (adt-cap (nfix (car lens))))
                                           (starts (adt-starts-l (cdr lens) (+ s (adt-cap (nfix (car lens))))))
                                           (lens (cdr lens)))))))

(defthm adt-decode-ser-when-okp
  (implies (adt-ser-okp s a)
           (equal (adt-decode s (adt-ser s a)) (list :ok a)))
  :hints (("Goal"
           :in-theory (e/d (adt-bschemap)
                           (adt-starts-is-starts-l adt-dec-rows-of-cells adt-ser adt-regs adt-rows-cells
                            adt-rows-pool adt-transpose adt-dec-rows adt-dec-cols adt-read-meta
                            adt-starts-l adt-lens adt-col-widths adt-end-l adt-col-sizes-ok
                            adt-untranspose adt-unle adt-schemap adt-bschemap1))
           :use ((:instance adt-ser-okp-bounds)
                 (:instance adt-placement-ok-of-starts-l (lens (adt-lens (adt-regs s a))) (s 1))
                 (:instance adt-dec-rows-of-cells (pos 0) (pre nil) (post nil))))
          ("Goal'" :in-theory (e/d (adt-bschemap adt-ser-okp)
                                   (adt-starts-is-starts-l adt-dec-rows-of-cells adt-ser adt-regs adt-rows-cells
                                    adt-rows-pool adt-transpose adt-dec-rows adt-dec-cols adt-read-meta
                                    adt-starts-l adt-lens adt-col-widths adt-end-l adt-col-sizes-ok
                                    adt-untranspose adt-unle adt-schemap adt-bschemap1)))))

; THE round trip: the decoder inverts the serializer on every value of a
; byte-representable schema whose image is addressable by u64 offsets.
(defthm adt-decode-ser
  (implies (and (adt-bschemap s) (adt-seq-p s a)
                (< (len a) *adt-u64-limit*)
                (< (len (adt-ser s a)) *adt-u64-limit*))
           (equal (adt-decode s (adt-ser s a)) (list :ok a)))
  :hints (("Goal" :use ((:instance adt-decode-ser-when-okp))
           :in-theory (e/d (adt-ser-okp) (adt-decode-ser-when-okp adt-decode adt-ser)))))

; -----------------------------------------------------------------------------
; G. Pages and the per-page digest table: the Merkle leaf level.

(local
 (defthm adt-len-nthcdr-local
   (implies (and (natp n) (<= n (len b))) (equal (len (nthcdr n b)) (- (len b) n)))
   :hints (("Goal" :in-theory (enable nthcdr) :induct (nthcdr n b)))))

(defun adt-pages (b)
  ; the image as whole pages, in order
  (declare (xargs :guard (true-listp b) :measure (len b)))
  (if (or (atom b) (< (len b) *adt-page*))
      nil
    (cons (take *adt-page* b) (adt-pages (nthcdr *adt-page* b)))))

(defun adt-digests (pages)
  (declare (xargs :guard t))
  (if (atom pages) nil (cons (fn-sha256 (car pages)) (adt-digests (cdr pages)))))

(defun adt-page-digests (s a)
  ; leaf K is the SHA-256 of page K of the value's snapshot bytes
  (declare (xargs :verify-guards nil))
  (adt-digests (adt-pages (adt-ser s a))))

(local
 (defun adt-pk-induct (k b)
   (declare (xargs :measure (len b)))
   (if (or (zp k) (atom b) (< (len b) *adt-page*))
       (list k b)
     (adt-pk-induct (1- k) (nthcdr *adt-page* b)))))

(local
 (defthm adt-nthcdr-nthcdr-local
   (implies (and (natp m) (natp n))
            (equal (nthcdr m (nthcdr n b)) (nthcdr (+ m n) b)))
   :hints (("Goal" :in-theory (enable nthcdr)))))

(defthm adt-len-digests
  (equal (len (adt-digests pages)) (len pages)))

(defthm adt-len-pages-exact
  (implies (and (natp e) (equal (len b) (* *adt-page* e)))
           (equal (len (adt-pages b)) e))
  :hints (("Goal" :induct (adt-pk-induct e b))))

(defthm adt-nth-pages
  (implies (and (natp k) (< k (len (adt-pages b))))
           (equal (nth k (adt-pages b)) (take *adt-page* (nthcdr (* *adt-page* k) b))))
  :hints (("Goal" :induct (adt-pk-induct k b) :in-theory (enable nth nthcdr)
           :expand ((adt-pages b)))))

(defthm adt-nth-digests
  (implies (and (natp k) (< k (len pages)))
           (equal (nth k (adt-digests pages)) (fn-sha256 (nth k pages))))
  :hints (("Goal" :in-theory (enable nth))))

; Leaf K of the table is the digest of page K of the snapshot bytes; the
; table has one leaf per page; and it is a function of the value alone.
(defthm adt-page-digest-nth
  (implies (and (natp k) (< k (len (adt-page-digests s a))))
           (equal (nth k (adt-page-digests s a))
                  (fn-sha256 (take *adt-page* (nthcdr (* *adt-page* k) (adt-ser s a))))))
  :hints (("Goal" :in-theory (e/d (adt-page-digests) (adt-ser)))))

(defthm adt-len-page-digests
  (implies (adt-bschemap s)
           (equal (len (adt-page-digests s a)) (adt-end (adt-regs s a) 1)))
  :hints (("Goal" :in-theory (e/d (adt-page-digests) (adt-ser adt-end-is-end-l adt-len-pages-exact))
           :use ((:instance adt-len-ser)
                 (:instance adt-len-pages-exact (b (adt-ser s a)) (e (adt-end (adt-regs s a) 1)))))))

; -----------------------------------------------------------------------------
; H. The bytes of an IMAGE: every image that corresponds to the value has
; the value's bytes, so two histories reaching one value reach one image of
; bytes (the determinism the coordinator asked of a snapshot digest).

(defun adt-ser-image (s c)
  ; a sequence image's snapshot bytes, read through its columns
  (declare (xargs :verify-guards nil))
  (adt-ser s (adt-abs s c)))

(defthm adt-ser-image-of-corr
  (implies (adt-corr s c a)
           (equal (adt-ser-image s c) (adt-ser s a))))

(defthm adt-ser-image-path-independent
  (implies (and (adt-corr s c1 a) (adt-corr s c2 a))
           (equal (adt-ser-image s c1) (adt-ser-image s c2)))
  :rule-classes nil)

(defun adt-kser-image (s dir c)
  ; a keyed set's snapshot bytes: its live records, in logical order
  (declare (xargs :verify-guards nil))
  (adt-ser s (adt-kview dir (adt-abs (adt-pschema s) c))))

(defthm adt-kser-image-of-kcorr
  (implies (adt-kcorr s dir j c a)
           (equal (adt-kser-image s dir c) (adt-ser s a)))
  :hints (("Goal" :in-theory (enable adt-kcorr))))

(defthm adt-kser-image-path-independent
  (implies (and (adt-kcorr s dir j c1 a) (adt-kcorr s dir j c2 a))
           (equal (adt-kser-image s dir c1) (adt-kser-image s dir c2)))
  :rule-classes nil)

(in-theory (disable adt-ser-image adt-kser-image adt-page-digests))
