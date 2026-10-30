; Layer C's test assembly: the identity schema (fn2/books/identity.lisp), the
; ordered schemas (fn2/books/ordered.lisp) and the run units' two fixture
; schemas, assembled once, with the identity decision. Every C unit includes
; this book (range-assembly.lisp adds the range reads on top), so a world
; holds one assembly (the dispatcher's functions are defined once per world).
(in-package "ACL2")
(include-book "../books/identity")
(include-book "../books/ordered")
(include-book "std/util/bstar" :dir :system)

(defrunschema fn2-rt-num :id 900
 :key ((group (:id group)) (number (:id group-number)))
 :value ((article (:id article)))
 :merge :unique)
; The octet-keyed fixture: a Binding-shaped key (Message-ID octets, content
; digest), so one Message-ID with two contents is two adjacent entries.
(defrunschema fn2-rt-mid :id 901
 :key ((message-id (:octets 250)) (content :digest))
 :value ((article (:id article)))
 :merge :union)

(fn2-run-assemble)
(fn2-identity-assemble)

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
