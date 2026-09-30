; Internal selected-row entry. The registered provider supplies the SAME
; immutable held row; this entry does not select or authorize a row.
(in-package "ACL2")
(include-book "over-row-state")
(include-book "nov-held-row-pieces")
(include-book "legacy-parser-cursor")
(include-book "nov-piece-window")
(include-book "over-row-pieces")

(defun fn-ohr-selected-row-begin (range pin row fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (true-listp range)
                              (natp (fn-record-payload row))
                              (< (fn-record-payload row)
                                 (fn-arena-count fn-arena)))))
  (let* ((handle (fn-record-payload row))
         (length (fn-arena-payload-len handle fn-arena))
         (facts (fn-held-facts row)))
    (if (fn-hf-nov facts)
        (if (and (fn-hnov-ok (fn-hf-nov facts))
                 (not (fn-hnov-tomb (fn-hf-nov facts))))
            (fn-obc-row-ready range pin
              (fn-npw-column-pieces (nth 1 range) facts length))
          (fn-obc-begin (fn-obc-next-range range (nth 5 range)) pin))
      (fn-obc-make range pin :parse
                   (fn-lpc-begin handle length pin) nil 0))))

; Guard vocabulary is established by the registered producer and carried by
; the response holder. A served quantum must not evaluate this validator.
(defun fn-ohr-active-p (s fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (and (true-listp s) (true-listp (nth 0 s)) (natp (nth 5 s))
       (case (nth 2 s)
         (:parse (fn-lpc-ready-p (nth 3 s) fn-arena))
         (:emit (fn-npw-piecesp (nth 4 s) fn-arena))
         (otherwise nil))))

(defun fn-ohr-active-one (s fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (fn-ohr-active-p s fn-arena)
                  :verify-guards nil))
  (let ((range (nth 0 s)) (pin (nth 1 s)))
    (case (nth 2 s)
      (:parse
       (mv-let (parser consumed work verdict)
         (fn-lpc-tick (nth 3 s) 1 fn-arena)
         (declare (ignore consumed work))
         (cond
          ((eq verdict :yield)
           (mv nil (fn-obc-make range pin :parse parser nil 0)))
          ((and (eq verdict :valid) (not (fn-lpc-tombstonep parser)))
           (mv nil (fn-obc-row-ready range pin
                     (fn-obc-parser-pieces (nth 1 range) parser))))
          (t (mv nil (fn-obc-begin
                       (fn-obc-next-range range (nth 5 range)) pin))))))
      (:emit
       (if (consp (nth 4 s))
           (mv-let (out pieces pos)
             (fn-npw-one (nth 4 s) (nth 5 s) fn-arena)
             (mv out (fn-obc-make range pin :emit nil pieces pos)))
         (mv nil (and range (fn-obc-begin range pin)))))
      (otherwise (mv nil nil)))))

(verify-guards fn-ohr-active-one
  :hints (("Goal" :in-theory
           (e/d (fn-ohr-active-p)
                (fn-lpc-tick fn-lpc-ready-p fn-npw-one fn-npw-piecesp
                 fn-obc-row-ready fn-obc-next-range fn-obc-parser-pieces
                 fn-lpc-tombstonep nth)))))
