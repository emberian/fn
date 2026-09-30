; Source constructor inventory of the exact legacy byte cursor.
; This models fresh CONS sites, never output tree size. Integer buffers,
; compiler helpers, native call lists and runtime refinement remain outside
; this structural model; no served activation follows from its bound.
(in-package "ACL2")
(include-book "legacy-parser-cursor")

; A PUT copies i+1 cells even when the input tail is malformed. The only
; data-dependent PUT index is the close-fields key, proved less than five
; by the actual branch condition. Span allocates four cells.
(defun fn-lpa-close-conses (s)
  (declare (xargs :guard t))
  (let ((key (fn-lpc-at 6 s)) (fields (fn-lpc-at 8 s)))
    (if (and (natp key) (< key 5) (not (fn-lpc-at key fields)))
        (+ 4 1 key) 0)))

(defun fn-lpa-value-conses (s byte)
  (declare (xargs :guard t))
  (declare (ignore s))
  (if (fn-article-header-bytep byte) 11 1))

; Every arm mirrors FN-LPC-HEADER-BYTE. Counts include transient PUT copies,
; the five-cell name candidate list and newly closed spans/path copies.
(defun fn-lpa-header-conses (s byte)
  (declare (xargs :guard t))
  (let ((phase (fn-lpc-at 0 s)))
    (cond
     ((eq phase :bad) 0)
     ((eq phase :body) (if (or (equal byte 13) (equal byte 10)) 1 0))
     ((eq phase :body-cr) 1)
     ((eq phase :cr-start)
      (if (and (equal byte 10) (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s)))
          (+ 9 1 (fn-lpa-close-conses s)) 1))
     ((eq phase :cr-line) (if (equal byte 10) 3 1))
     ((equal byte 13)
      (cond ((eq phase :start) 1)
            ((or (eq phase :first) (eq phase :value))
             (if (eq (fn-lpc-at 10 s) :fold-empty) 1 7))
            (t 1)))
     ((or (equal byte 10) (<= *fn-article-max-line-octets* (nfix (fn-lpc-at 1 s)))) 1)
     ((eq phase :start)
      (if (fn-article-wspp byte)
          (if (fn-lpc-at 2 s) (+ 11 (fn-lpa-value-conses s byte)) 1)
        (if (and (fn-article-ftextp byte) (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s)))
            (+ 11 5 (fn-lpa-close-conses s)) 1)))
     ((eq phase :name)
      (cond ((equal byte 58) 10)
            ((fn-article-ftextp byte) 15)
            (t 1)))
     ((eq phase :first)
      (if (fn-article-wspp byte) (fn-lpa-value-conses s byte) 1))
     ((eq phase :value) (fn-lpa-value-conses s byte))
     (t 1))))

(defun fn-lpa-body-conses (s)
  (declare (xargs :guard t))
  (if (eq (fn-lpc-at 0 s) :bad) 0 2))

(defun fn-lpa-byte-conses (s byte)
  (declare (xargs :guard t))
  (+ 8 (fn-lpa-header-conses (fn-lpc-at 4 s) byte)
     (if (equal (fn-lpc-at 5 s) 4) (fn-lpa-body-conses (fn-lpc-at 6 s)) 0)))

(defthm fn-lpa-close-conses-bound
  (and (natp (fn-lpa-close-conses s)) (<= (fn-lpa-close-conses s) 9))
  :hints (("Goal" :in-theory (enable fn-lpa-close-conses))))
(defthm fn-lpa-value-conses-bound
  (and (natp (fn-lpa-value-conses s byte)) (<= (fn-lpa-value-conses s byte) 11))
  :hints (("Goal" :in-theory (enable fn-lpa-value-conses))))
(defthm fn-lpa-header-conses-bound
  (and (natp (fn-lpa-header-conses s byte)) (<= (fn-lpa-header-conses s byte) 25))
  :hints (("Goal" :use (fn-lpa-close-conses-bound fn-lpa-value-conses-bound)
           :in-theory (e/d (fn-lpa-header-conses)
                          (fn-lpa-close-conses fn-lpa-value-conses fn-lpc-at
                           fn-article-ftextp fn-article-wspp
                           fn-lpa-close-conses-bound fn-lpa-value-conses-bound)))))
(defthm fn-lpa-byte-conses-bound
  (and (natp (fn-lpa-byte-conses s byte)) (<= (fn-lpa-byte-conses s byte) 35))
  :hints (("Goal" :use ((:instance fn-lpa-header-conses-bound (s (fn-lpc-at 4 s))))
           :in-theory (e/d (fn-lpa-byte-conses fn-lpa-body-conses)
                          (fn-lpa-header-conses fn-lpc-at fn-lpa-header-conses-bound)))))

(defthm fn-lpa-byte-conses-ceiling
  (<= (fn-lpa-byte-conses s byte) 35)
  :rule-classes :linear
  :hints (("Goal" :use fn-lpa-byte-conses-bound
           :in-theory (disable fn-lpa-byte-conses fn-lpa-byte-conses-bound))))

; Cost-only observer follows exactly the actual tick's stop condition,
; arena read and byte transition. It overcharges each logical MV tuple at
; four fresh cells including the final return. A compiled multiple-value
; optimization may allocate less; this does not presume it allocates zero.
(defun fn-lpa-tick-conses (s fuel fn-arena)
  (declare (xargs :stobjs fn-arena :measure (nfix fuel) :verify-guards nil
                  :guard (and (natp fuel) (fn-lpc-ready-p s fn-arena))))
  (if (or (zp fuel) (<= (fn-lpc-at 1 s) (fn-lpc-at 3 s))) 4
    (let ((byte (fn-arena-get (fn-lpc-at 0 s) (fn-lpc-at 3 s) fn-arena)))
      (+ 4 (fn-lpa-byte-conses s byte)
         (fn-lpa-tick-conses (fn-lpc-byte s byte) (1- fuel) fn-arena)))))

(defthm fn-lpa-tick-conses-are-bounded-by-actual-work
  (let ((work (mv-nth 2 (fn-lpc-tick s fuel fn-arena))))
    (and (natp (fn-lpa-tick-conses s fuel fn-arena))
         (<= (fn-lpa-tick-conses s fuel fn-arena) (+ 4 (* 39 work)))))
  :hints (("Goal" :induct (fn-lpc-tick s fuel fn-arena)
           :in-theory (e/d (fn-lpa-tick-conses fn-lpc-tick)
                           (fn-lpc-byte fn-lpa-byte-conses fn-lpc-verdict)))))

(defthm fn-lpa-tick-conses-are-bounded-by-fuel
  (implies (natp fuel)
           (<= (fn-lpa-tick-conses s fuel fn-arena) (+ 4 (* 39 fuel))))
  :hints (("Goal" :use (fn-lpa-tick-conses-are-bounded-by-actual-work fn-lpc-tick-bounded)
           :in-theory (disable fn-lpa-tick-conses fn-lpc-tick fn-lpa-tick-conses-are-bounded-by-actual-work
                               fn-lpc-tick-bounded))))

(verify-guards fn-lpa-tick-conses
 :hints (("Goal" :in-theory (e/d (fn-lpc-ready-p)
                       (fn-lpc-byte fn-lpc-at fn-lpa-byte-conses fn-lpa-tick-conses)))))
