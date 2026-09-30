; Source-dominated scalar widths of the actual legacy cursor.
; These invariants are carried, never whole-state checked on a served tick.
(in-package "ACL2")
(include-book "legacy-parser-header")

(defun fn-lps-header-count-p (s pos)
  (declare (xargs :guard t))
  (and (natp pos) (natp (fn-lpc-at 1 s))
       (<= (fn-lpc-at 1 s) pos)))

(defthm fn-lps-header-byte-count-preserved
  (implies (fn-lps-header-count-p s pos)
           (fn-lps-header-count-p (fn-lpc-header-byte s byte pos h pin)
                                  (+ 1 pos)))
  :hints (("Goal" :in-theory
           (e/d (fn-lps-header-count-p fn-lpc-header-byte fn-lpc-value-byte
                 fn-lpc-header-bad fn-lpc-at)
                (fn-lpc-put fn-lpc-close-fields fn-lpc-name-step fn-lpc-name-key)))))

(defun fn-lps-body-count-p (s pos)
  (declare (xargs :guard t))
  (and (natp pos) (natp (fn-lpc-at 1 s))
       (<= (fn-lpc-at 1 s) pos)))

(defthm fn-lps-body-byte-count-preserved
  (implies (fn-lps-body-count-p s pos)
           (fn-lps-body-count-p (fn-lpc-body-byte s byte) (+ 1 pos)))
  :hints (("Goal" :in-theory (enable fn-lps-body-count-p fn-lpc-body-byte fn-lpc-at))))

(defun fn-lps-scalars-p (s)
  (declare (xargs :guard t))
  (and (fn-lpc-cursor-bounds-p s)
       (fn-lps-header-count-p (fn-lpc-at 4 s) (fn-lpc-at 3 s))
       (fn-lps-body-count-p (fn-lpc-at 6 s) (fn-lpc-at 3 s))))

(defthm fn-lps-begin-establishes-scalars
  (fn-lps-scalars-p (fn-lpc-begin h n pin))
  :hints (("Goal" :in-theory
           (enable fn-lps-scalars-p fn-lps-header-count-p fn-lps-body-count-p
                   fn-lpc-begin fn-lpc-header-begin fn-lpc-header-bad fn-lpc-at))))

(defthm fn-lps-byte-preserves-scalars
  (implies (fn-lps-scalars-p s)
           (fn-lps-scalars-p (fn-lpc-byte s byte)))
  :hints (("Goal" :use (fn-lpc-byte-preserves-bounds
                 (:instance fn-lps-body-byte-count-preserved
                            (s (fn-lpc-at 6 s)) (pos (fn-lpc-at 3 s))))
           :in-theory
           (e/d (fn-lps-scalars-p fn-lpc-byte fn-lpc-at fn-lps-body-count-p)
                (fn-lpc-header-byte fn-lpc-header-bounds-p fn-lpc-cursor-bounds-p
                 fn-lpc-body-byte fn-lpc-split-byte fn-lps-header-count-p
                 fn-lps-body-byte-count-preserved fn-lpc-byte-preserves-bounds)))))

(defthm fn-lps-tick-preserves-scalars
  (implies (fn-lps-scalars-p s)
           (fn-lps-scalars-p (mv-nth 0 (fn-lpc-tick s fuel fn-arena))))
  :hints (("Goal" :induct (fn-lpc-tick s fuel fn-arena)
           :in-theory (e/d (fn-lpc-tick)
                          (fn-lpc-byte fn-lps-scalars-p fn-lpc-at fn-lpc-verdict)))))

; LIMIT is a representation/profile coordinate, not a parser ceiling.
(defthm fn-lps-tick-scalars-fit-source-width
  (implies (and (fn-lps-scalars-p s) (fn-lpc-ready-p s fn-arena)
                (<= (fn-lpc-at 1 s) limit))
           (let* ((out (mv-nth 0 (fn-lpc-tick s fuel fn-arena)))
                  (header (fn-lpc-at 4 out)) (body (fn-lpc-at 6 out)))
             (and (natp (fn-lpc-at 3 out)) (<= (fn-lpc-at 3 out) limit)
                  (natp (fn-lpc-at 1 header)) (<= (fn-lpc-at 1 header) limit)
                  (natp (fn-lpc-at 4 header)) (<= (fn-lpc-at 4 header) limit)
                  (natp (fn-lpc-at 5 header)) (<= (fn-lpc-at 5 header) limit)
                  (natp (fn-lpc-at 1 body)) (<= (fn-lpc-at 1 body) limit))))
  :hints (("Goal"
           :use (fn-lps-tick-preserves-scalars fn-lpc-tick-preserves-ready
                 fn-lpc-tick-preserves-source)
           :in-theory
           (e/d (fn-lps-scalars-p fn-lps-header-count-p fn-lps-body-count-p
                 fn-lpc-cursor-bounds-p fn-lpc-header-bounds-p fn-lpc-ready-p)
                (fn-lpc-tick fn-lpc-at fn-lps-tick-preserves-scalars
                 fn-lpc-tick-preserves-ready fn-lpc-tick-preserves-source)))))

(defthm fn-lps-tick-results-fit-quantum-width
  (implies (and (natp fuel) (<= fuel quantum-limit))
           (and (natp (mv-nth 1 (fn-lpc-tick s fuel fn-arena)))
                (natp (mv-nth 2 (fn-lpc-tick s fuel fn-arena)))
                (<= (mv-nth 1 (fn-lpc-tick s fuel fn-arena)) quantum-limit)
                (<= (mv-nth 2 (fn-lpc-tick s fuel fn-arena)) quantum-limit)))
  :hints (("Goal" :use fn-lpc-tick-bounded
           :in-theory (disable fn-lpc-tick fn-lpc-tick-bounded))))
