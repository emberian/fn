; SCN-1009: literal actual arena-tick/catalog antecedents and conclusions.
(in-package "ACL2")
(include-book "../../books/legacy-parser-catalog")

(defconst *lpvcat-full* '(83 117 98 106 101 99 116 58 13 10 32 102 105 114 115 116 13 10 9 115 101 99 111 110 100 13 10 83 117 98 106 101 99 116 58 32 108 97 116 101 114 13 10 70 114 111 109 58 32 119 114 105 116 101 114 13 10 68 97 116 101 58 32 84 117 101 13 10 77 101 115 115 97 103 101 45 73 68 58 32 60 109 64 110 62 13 10 82 101 102 101 114 101 110 99 101 115 58 32 60 97 64 110 62 13 10 13 10 98 111 100 121 13 10))
(defthm lpvcat-full-actual-tick-positive
  (let* ((arena (list nil *lpvcat-full*))
         (h 1) (pin '(:origin 17))
         (n (fn-arena-payload-len h arena))
         (out (mv-nth 0 (fn-lpc-tick (fn-lpc-begin h n pin) n arena))))
    (and (fn-cbor-octet-listp (nth h arena))
         (equal (fn-lpc-nov-value out arena) (fn-hnov-of (nth h arena)))
         (equal (fn-lpc-body-lines out) (fn-hf-body-lines-of (nth h arena)))
         (fn-lpc-cursor-bounds-p out)
         (equal (fn-lpc-at 2 out) pin)))
  :rule-classes nil)

(defconst *lpvcat-invalid* '(83 117 98 106 101 99 116 58 32 120 13 10 32 9 13 10 13 10 98 111 100 121 13 10))
(defthm lpvcat-invalid-actual-tick-positive
  (let* ((arena (list nil *lpvcat-invalid*))
         (h 1) (pin '(:origin 17))
         (n (fn-arena-payload-len h arena))
         (out (mv-nth 0 (fn-lpc-tick (fn-lpc-begin h n pin) n arena))))
    (and (fn-cbor-octet-listp (nth h arena))
         (equal (fn-lpc-nov-value out arena) (fn-hnov-of (nth h arena)))
         (equal (fn-lpc-body-lines out) (fn-hf-body-lines-of (nth h arena)))
         (fn-lpc-cursor-bounds-p out)
         (equal (fn-lpc-at 2 out) pin)))
  :rule-classes nil)

(defconst *lpvcat-body-nul* '(83 117 98 106 101 99 116 58 32 120 13 10 13 10 0 13 10))
(defthm lpvcat-body-nul-actual-tick-positive
  (let* ((arena (list nil *lpvcat-body-nul*))
         (h 1) (pin '(:origin 17))
         (n (fn-arena-payload-len h arena))
         (out (mv-nth 0 (fn-lpc-tick (fn-lpc-begin h n pin) n arena))))
    (and (fn-cbor-octet-listp (nth h arena))
         (equal (fn-lpc-nov-value out arena) (fn-hnov-of (nth h arena)))
         (equal (fn-lpc-body-lines out) (fn-hf-body-lines-of (nth h arena)))
         (fn-lpc-cursor-bounds-p out)
         (equal (fn-lpc-at 2 out) pin)))
  :rule-classes nil)

(defconst *lpvcat-tomb* '(0 70 78 45 82 67 76 49 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120 120))
(defthm lpvcat-tomb-actual-tick-positive
  (let* ((arena (list nil *lpvcat-tomb*))
         (h 1) (pin '(:origin 17))
         (n (fn-arena-payload-len h arena))
         (out (mv-nth 0 (fn-lpc-tick (fn-lpc-begin h n pin) n arena))))
    (and (fn-cbor-octet-listp (nth h arena))
         (equal (fn-lpc-nov-value out arena) (fn-hnov-of (nth h arena)))
         (equal (fn-lpc-body-lines out) (fn-hf-body-lines-of (nth h arena)))
         (fn-lpc-cursor-bounds-p out)
         (equal (fn-lpc-at 2 out) pin)))
  :rule-classes nil)

(defconst *lpvcat-short-magic* '(0 70 78 45 82 67 76 49))
(defthm lpvcat-short-magic-actual-tick-positive
  (let* ((arena (list nil *lpvcat-short-magic*))
         (h 1) (pin '(:origin 17))
         (n (fn-arena-payload-len h arena))
         (out (mv-nth 0 (fn-lpc-tick (fn-lpc-begin h n pin) n arena))))
    (and (fn-cbor-octet-listp (nth h arena))
         (equal (fn-lpc-nov-value out arena) (fn-hnov-of (nth h arena)))
         (equal (fn-lpc-body-lines out) (fn-hf-body-lines-of (nth h arena)))
         (fn-lpc-cursor-bounds-p out)
         (equal (fn-lpc-at 2 out) pin)))
  :rule-classes nil)

; Exact expected projection: first repeated Subject wins, a first-line empty
; value uses the folded first SP exactly once, and TAB scrubs to SP.
(defthm lpvcat-exact-projection-positive
 (let* ((arena (list *lpvcat-full*)) (n (fn-arena-payload-len 0 arena))
        (out (mv-nth 0 (fn-lpc-tick (fn-lpc-begin 0 n :pin) n arena))))
   (and (equal (fn-lpc-nov-value out arena)
               (fn-hnov-make nil t "first second" "writer" "Tue" "<m@n>" "<a@n>"))
        (equal (fn-lpc-body-lines out) 1)))
 :rule-classes nil)

; Tombstones reject header syntax while preserving the catalog tombstone bit.
(assert-event
 (and (equal (fn-hnov-of *lpvcat-tomb*) (fn-hnov-make t nil "" "" "" "" ""))
      (equal (fn-hnov-of *lpvcat-short-magic*) (fn-hnov-make nil nil "" "" "" "" ""))))

; Literal verdict theorem positive includes its sole octet antecedent.
(defthm lpvcat-verdict-positive
  (let ((bytes *lpvcat-full*))
    (and (fn-cbor-octet-listp bytes)
         (equal (eq (fn-lpc-verdict (fn-lpc-feed bytes (fn-lpc-begin 1 (len bytes) :pin))) :valid)
                (fn-article-result-okp (fn-article-parse bytes)))))
  :rule-classes nil)

; HYPOTHESIS REMOVAL: arbitrary non-octet opaque body input is accepted by
; the byte grammar; the actual reference parser's octet preflight rejects it.
(defthm lpvcat-without-octets
  (let* ((arena '((13 10 256))) (h 0) (pin :pin)
         (n (fn-arena-payload-len h arena))
         (out (mv-nth 0 (fn-lpc-tick (fn-lpc-begin h n pin) n arena))))
    (and (not (fn-cbor-octet-listp (nth h arena)))
         (not (equal (fn-lpc-nov-value out arena) (fn-hnov-of (nth h arena))))
         (not (equal (eq (fn-lpc-verdict out) :valid)
                     (fn-article-result-okp (fn-article-parse (nth h arena)))))))
  :rule-classes nil)

; The natural-handle premise was removed after proving the stronger result.
; A logical negative handle still projects the same exact first source.
(defthm lpvcat-negative-handle-stronger-positive
  (let* ((arena (list *lpvcat-full*)) (h -1) (pin :pin)
         (n (fn-arena-payload-len h arena))
         (out (mv-nth 0 (fn-lpc-tick (fn-lpc-begin h n pin) n arena))))
    (and (not (natp h)) (fn-cbor-octet-listp (nth h arena))
         (equal (fn-lpc-nov-value out arena) (fn-hnov-of (nth h arena)))))
  :hints (("Goal"
           :use ((:instance fn-lpc-tick-full-nov-is-actual-catalog
                           (h -1) (fn-arena (list *lpvcat-full*)) (pin :pin)))
           :in-theory (union-theories (theory 'minimal-theory)
                                      (executable-counterpart-theory :here))))
  :rule-classes nil)

(defthm lpvcat-feed-prefix-positive
  (let ((s (fn-lpc-begin 0 89 :pin)) (bytes *lpvcat-tomb*))
    (and (natp (fn-lpc-at 3 s))
         (<= 8 (+ (fn-lpc-at 3 s) (len bytes)))
         (iff (fn-lpc-at 7 (fn-lpc-feed bytes s))
              (and (fn-lpc-at 7 s)
                   (fn-rcl-prefixp (nthcdr (fn-lpc-at 3 s) *fn-rcl-magic*) bytes)))))
  :rule-classes nil)

; HYPOTHESIS REMOVAL: all other prefix antecedents hold. Nfix restarts a
; fractional position at zero, retaining a partial prefix without eight bytes.
(defthm lpvcat-prefix-without-natural-position
  (let ((s (fn-lpc-put 3 15/2 (fn-lpc-begin 0 89 :pin))) (bytes '(0)))
    (and (not (natp (fn-lpc-at 3 s)))
         (<= 8 (+ (fn-lpc-at 3 s) (len bytes)))
         (not (iff (fn-lpc-at 7 (fn-lpc-feed bytes s))
                    (and (fn-lpc-at 7 s)
                         (fn-rcl-prefixp (nthcdr (fn-lpc-at 3 s) *fn-rcl-magic*) bytes))))))
  :rule-classes nil)

; HYPOTHESIS REMOVAL: natural position holds, but an unconsumed prefix is
; not evidence that the complete eight-byte magic exists in a short source.
(defthm lpvcat-prefix-without-enough-bytes
  (let ((s (fn-lpc-begin 0 89 :pin)) (bytes nil))
    (and (natp (fn-lpc-at 3 s))
         (not (<= 8 (+ (fn-lpc-at 3 s) (len bytes))))
         (not (iff (fn-lpc-at 7 (fn-lpc-feed bytes s))
                    (and (fn-lpc-at 7 s)
                         (fn-rcl-prefixp (nthcdr (fn-lpc-at 3 s) *fn-rcl-magic*) bytes))))))
  :rule-classes nil)

(defthm lpvcat-feed-tombstone-positive
  (equal (fn-lpc-tombstonep (fn-lpc-feed *lpvcat-tomb* (fn-lpc-begin 1 (len *lpvcat-tomb*) :pin)))
         (fn-rcl-tombstonep *lpvcat-tomb*))
  :rule-classes nil)

(defthm lpvcat-feed-catalog-positive
  (let ((arena (list *lpvcat-full*)) (h 0) (pin :pin))
    (and (fn-cbor-octet-listp (nth h arena))
         (equal (fn-lpc-nov-value (fn-lpc-feed (nth h arena) (fn-lpc-begin h (len (nth h arena)) pin)) arena)
                (fn-hnov-of (nth h arena)))))
  :rule-classes nil)

(defthm lpvcat-agreement-positive
  (and (fn-cbor-octet-listp *lpvcat-full*) (fn-lpc-agreesp *lpvcat-full* :pin))
  :rule-classes nil)
(defthm lpvcat-agreement-without-octets
  (and (not (fn-cbor-octet-listp '(13 10 256)))
       (not (fn-lpc-agreesp '(13 10 256) :pin)))
  :rule-classes nil)

; MUTATION: replacing the carried magic match would clear the tombstone.
(assert-event
 (let* ((s (fn-lpc-feed *lpvcat-tomb* (fn-lpc-begin 0 89 :pin)))
        (mutated (fn-lpc-put 7 nil s)))
   (and (equal (fn-lpc-nov-value s (list *lpvcat-tomb*)) (fn-hnov-of *lpvcat-tomb*))
        (not (equal (fn-lpc-nov-value mutated (list *lpvcat-tomb*)) (fn-hnov-of *lpvcat-tomb*))))))

; Executable stobj witnesses resume at every byte and across distinct cuts.
(defun lpvcat-chunked (s fuel steps fn-arena)
  (declare (xargs :stobjs fn-arena :measure (nfix steps) :verify-guards nil))
  (if (or (zp steps) (not (eq (fn-lpc-verdict s) :yield))) s
    (mv-let (next consumed work verdict) (fn-lpc-tick s fuel fn-arena)
      (declare (ignore consumed work verdict))
      (lpvcat-chunked next fuel (1- steps) fn-arena))))

(defun lpvcat-chunked-case (bytes fuel fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let* ((fn-arena (fn-arena-clear fn-arena))
         (fn-arena (fn-arena-seal-list bytes fn-arena))
         (s (lpvcat-chunked (fn-lpc-begin 0 (len bytes) '(:origin 17))
                           fuel (+ 1 (len bytes)) fn-arena)))
    (mv (and (equal (fn-lpc-nov-value s (list bytes)) (fn-hnov-of bytes))
             (equal (fn-lpc-body-lines s) (fn-hf-body-lines-of bytes))
             (fn-lpc-cursor-bounds-p s)
             (not (eq (fn-lpc-verdict s) :yield))
             (equal (fn-lpc-at 2 s) '(:origin 17))) fn-arena)))

(defun lpvcat-chunked-exec (bytes fuel)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena) (lpvcat-chunked-case bytes fuel fn-arena) result)))

(assert-event
 (and (lpvcat-chunked-exec *lpvcat-full* 1)
      (lpvcat-chunked-exec *lpvcat-invalid* 1)
      (lpvcat-chunked-exec *lpvcat-body-nul* 1)
      (lpvcat-chunked-exec *lpvcat-tomb* 1)
      (lpvcat-chunked-exec *lpvcat-short-magic* 1)
      (lpvcat-chunked-exec *lpvcat-full* 3)
      (lpvcat-chunked-exec *lpvcat-full* 7)
      (lpvcat-chunked-exec *lpvcat-tomb* 8)))
