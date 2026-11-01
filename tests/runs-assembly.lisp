; Layer C's units stand on the served assembly (C-ONE-ASSEMBLY): the
; production schemas (identity, article metadata, overview, addressing)
; assembled once in books/runs-served.lisp, the range reads in
; books/range-served.lisp. Every C unit includes this book, which holds the
; teeth makers for the per-schema keystones the assembly generates.
(in-package "ACL2")
(include-book "../books/range-served")
(include-book "std/util/bstar" :dir :system)

;; Teeth makers for the per-schema keystones the assembly generates; each
;; unit instantiates them for its schemas.
;; Keystone teeth, one set per schema. Positive: the statement holds at an
;; inhabited premise (checked). Negative: without the premise (unsorted
;; entries, refused :order part way) the conclusion fails.
(defmacro fn2-rt-teeth (name id key meta good bad queries badq)
 (let ((entry (fn2-columns-sym name "-ENTRY")))
  `(progn
    (defun ,(fn2-columns-sym name "-PAGE-ROUNDTRIP-POSITIVE") ()
     (declare (xargs :verify-guards nil))
     (and (fn2-run-page-inputp ,(fn2-codec-constant entry "") ',key ,meta ,good)
          (equal (fn2-run-page-image ,id ,(fn2-codec-constant entry "") ,meta ,good)
                 (list :ok :ok :ok (fn2-run-page-spec ,(fn2-codec-constant entry "") ,meta ,good)))))
    (defun ,(fn2-columns-sym name "-PAGE-ROUNDTRIP-NEGATIVE") ()
     (declare (xargs :verify-guards nil))
     (and (not (fn2-run-page-inputp ,(fn2-codec-constant entry "") ',key ,meta ,bad))
          (not (equal (fn2-run-page-image ,id ,(fn2-codec-constant entry "") ,meta ,bad)
                      (list :ok :ok :ok (fn2-run-page-spec ,(fn2-codec-constant entry "") ,meta ,bad))))))
    (defun ,(fn2-columns-sym name "-SEEKS-HOLD") (qs)
     (declare (xargs :verify-guards nil))
     (or (atom qs)
         (and (fn2-run-values-layoutp ,(fn2-codec-constant entry "") (car qs))
              (equal (fn2-run-seek-image ,id ,(fn2-codec-constant entry "") ,meta ,good (car qs))
                     (fn2-run-lower-bound-spec ',key ,good (car qs) 0))
              (,(fn2-columns-sym name "-SEEKS-HOLD") (cdr qs)))))
    (defun ,(fn2-columns-sym name "-SEEK-LOWER-BOUND-POSITIVE") ()
     (declare (xargs :verify-guards nil))
     (,(fn2-columns-sym name "-SEEKS-HOLD") ,queries))
    (defun ,(fn2-columns-sym name "-SEEK-LOWER-BOUND-NEGATIVE") ()
     (declare (xargs :verify-guards nil))
     (not (equal (fn2-run-seek-image ,id ,(fn2-codec-constant entry "") ,meta ,bad ,badq)
                 (fn2-run-lower-bound-spec ',key ,bad ,badq 0))))
    (fn2-assert-owed-teeth ,(fn2-columns-sym name "-PAGE-ROUNDTRIP") ,(fn2-columns-sym name "-SEEK-LOWER-BOUND")))))

; Run-lookup teeth. Positive: inhabited premise (checked), every query in a
; list agrees with the spec. Negative: without sortedness the conclusion fails.
(defmacro fn2-rt-run-teeth (name id key good bad limit queries badq)
 (let ((entry (fn2-columns-sym name "-ENTRY")))
  `(progn
    (defun ,(fn2-columns-sym name "-RUN-LOOKUPS-HOLD") (qs)
     (declare (xargs :verify-guards nil))
     (or (atom qs)
         (and (fn2-run-values-layoutp ,(fn2-codec-constant entry "") (car qs))
              (equal (fn2-run-lookup-image ,id ,(fn2-codec-constant entry "") ,good ,limit (car qs)) (fn2-run-key-lookup-spec ',key ,good (car qs)))
              (,(fn2-columns-sym name "-RUN-LOOKUPS-HOLD") (cdr qs)))))
    (defun ,(fn2-columns-sym name "-RUN-LOOKUP-EXACT-POSITIVE") ()
     (declare (xargs :verify-guards nil))
     (and (fn2-run-run-inputp ,(fn2-codec-constant entry "") ',key ,good ,limit)
          (,(fn2-columns-sym name "-RUN-LOOKUPS-HOLD") ,queries)))
    (defun ,(fn2-columns-sym name "-RUN-LOOKUP-EXACT-NEGATIVE") ()
     (declare (xargs :verify-guards nil))
     (and (not (fn2-run-run-inputp ,(fn2-codec-constant entry "") ',key ,bad ,limit))
          (not (equal (fn2-run-lookup-image ,id ,(fn2-codec-constant entry "") ,bad ,limit ,badq) (fn2-run-key-lookup-spec ',key ,bad ,badq)))))
    (fn2-assert-owed-teeth ,(fn2-columns-sym name "-RUN-LOOKUP-EXACT")))))
(defmacro fn2-rt-scan-teeth (name id key good bad limit queries badq)
 (let ((entry (fn2-columns-sym name "-ENTRY")))
  `(progn
    (defun ,(fn2-columns-sym name "-RUN-SCANS-HOLD") (qs)
     (declare (xargs :verify-guards nil))
     (or (atom qs)
         (and (fn2-run-values-layoutp ,(fn2-codec-constant entry "") (caar qs))
              (equal (fn2-run-scan-image ,id ,(fn2-codec-constant entry "") ,good ,limit (caar qs) (cadar qs))
                     (fn2-run-scan-spec ',key ,good (caar qs) (cadar qs)))
              (,(fn2-columns-sym name "-RUN-SCANS-HOLD") (cdr qs)))))
    (defun ,(fn2-columns-sym name "-RUN-SCAN-POSITIVE") ()
     (declare (xargs :verify-guards nil))
     (and (fn2-run-run-inputp ,(fn2-codec-constant entry "") ',key ,good ,limit)
          (,(fn2-columns-sym name "-RUN-SCANS-HOLD") ,queries)))
    (defun ,(fn2-columns-sym name "-RUN-SCAN-NEGATIVE") ()
     (declare (xargs :verify-guards nil))
     (and (not (fn2-run-run-inputp ,(fn2-codec-constant entry "") ',key ,bad ,limit))
          (not (equal (fn2-run-scan-image ,id ,(fn2-codec-constant entry "") ,bad ,limit ,badq 64)
                      (fn2-run-scan-spec ',key ,bad ,badq 64)))))
    (fn2-assert-owed-teeth ,(fn2-columns-sym name "-RUN-SCAN")))))
;; Overlay teeth. Positive: entries inserted out of order (every seventh,
;; wrapping) read back sorted, every insert :ok. Negative: a repeated key
;; (premise false) is refused :duplicate, so the image differs from the spec.
(defun fn2-rt-shuffle-loop (k i n entries)
 (declare (xargs :verify-guards nil :measure (nfix k)))
 (if (zp k) nil
  (cons (nth (mod (* 7 (nfix i)) (nfix n)) entries) (fn2-rt-shuffle-loop (- k 1) (+ 1 (nfix i)) n entries))))
(defun fn2-rt-shuffle (entries i n)
 (declare (xargs :verify-guards nil))
 (fn2-rt-shuffle-loop (nfix (- (nfix n) (nfix i))) i n entries))
(defmacro fn2-rt-overlay-teeth (name id key good bad)
 (let ((entry (fn2-columns-sym name "-ENTRY")))
  `(progn
    (defun ,(fn2-columns-sym name "-OVERLAY-SORTED-POSITIVE") ()
     (declare (xargs :verify-guards nil))
     (and (fn2-ov-inputp ,(fn2-codec-constant entry "") ',key ,good)
          (equal (fn2-ov-image ,id ,(fn2-codec-constant entry "") ,good) (fn2-ov-image-spec ',key ,good))))
    (defun ,(fn2-columns-sym name "-OVERLAY-SORTED-NEGATIVE") ()
     (declare (xargs :verify-guards nil))
     (and (not (fn2-ov-inputp ,(fn2-codec-constant entry "") ',key ,bad))
          (not (equal (fn2-ov-image ,id ,(fn2-codec-constant entry "") ,bad) (fn2-ov-image-spec ',key ,bad)))))
    (fn2-assert-owed-teeth ,(fn2-columns-sym name "-OVERLAY-SORTED")))))
