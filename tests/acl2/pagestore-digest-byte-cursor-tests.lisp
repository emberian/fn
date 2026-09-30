(in-package "ACL2")
(include-book "../../books/pagestore-digest-byte-refinement")

;; Test-only fuel driver, not a served stream function.
(defun pgs-dcbt-run (fuel byte-total msg pgs-digest)
  (declare (xargs :stobjs pgs-digest :measure (nfix fuel) :verify-guards nil))
  (if (or (zp fuel) (eq (pgs-dc-mode pgs-digest) :done)) pgs-digest
    (mv-let (status pgs-digest)
      (pgs-dcb-step byte-total
        (fn-b3-words 16 (fn-b3-nthcdrx (pgs-dcb-next-byte-offset pgs-digest) msg))
        pgs-digest)
      (declare (ignore status))
      (pgs-dcbt-run (1- fuel) byte-total msg pgs-digest))))

(defun-nx pgs-dcbt-example (msg)
  (let* ((byte-total (len msg))
         (cursor (pgs-dcb-begin 0 0 byte-total :capture-17 :lease-23 (create-pgs-digest)))
         (next (pgs-dcbt-run 128 byte-total msg cursor)))
    (list (pgs-dc-mode next) (pgs-dcb-result-octets next)
          (pgs-dc-capture next) (pgs-dc-lease next))))

(defthm pgs-dcbt-empty-positive
  (equal (pgs-dcbt-example nil)
         (list :done (fn-blake3 nil) :capture-17 :lease-23))
  :rule-classes nil)

(defthm pgs-dcbt-partial-blocks-positive
  (and (equal (pgs-dcbt-example '(1)) (list :done (fn-blake3 '(1)) :capture-17 :lease-23))
       (equal (pgs-dcbt-example '(1 2 3)) (list :done (fn-blake3 '(1 2 3)) :capture-17 :lease-23))
       (equal (pgs-dcbt-example '(1 2 3 4 5 6 7))
              (list :done (fn-blake3 '(1 2 3 4 5 6 7)) :capture-17 :lease-23))
       (equal (pgs-dcbt-example (make-list 63 :initial-element 9))
              (list :done (fn-blake3 (make-list 63 :initial-element 9)) :capture-17 :lease-23))
       (equal (pgs-dcbt-example (make-list 65 :initial-element 9))
              (list :done (fn-blake3 (make-list 65 :initial-element 9)) :capture-17 :lease-23)))
  :rule-classes nil)

(defthm pgs-dcbt-chunk-boundaries-positive
  (and (equal (pgs-dcbt-example (make-list 1023 :initial-element 9))
              (list :done (fn-blake3 (make-list 1023 :initial-element 9)) :capture-17 :lease-23))
       (equal (pgs-dcbt-example (make-list 1024 :initial-element 9))
              (list :done (fn-blake3 (make-list 1024 :initial-element 9)) :capture-17 :lease-23))
       (equal (pgs-dcbt-example (make-list 1025 :initial-element 9))
              (list :done (fn-blake3 (make-list 1025 :initial-element 9)) :capture-17 :lease-23))
       (equal (pgs-dcbt-example (make-list 2049 :initial-element 9))
              (list :done (fn-blake3 (make-list 2049 :initial-element 9)) :capture-17 :lease-23)))
  :rule-classes nil)

;; Full literal byte-tail theorem antecedent and conclusion.
(defthm pgs-dcbt-tail-positive
  (let* ((byte-total 3) (msg '(1 2 3))
         (cursor (mv-nth 1 (pgs-dcb-step byte-total nil
                   (pgs-dcb-begin 0 0 byte-total :capture-17 :lease-23 (create-pgs-digest)))))
         (block (fn-b3-words 16 msg)))
    (and (equal (pgs-dc-mode cursor) :chunk)
         (natp byte-total) (equal (len msg) byte-total)
         (natp (pgs-dc-start cursor)) (natp (pgs-dc-pos cursor)) (natp (pgs-dc-end cursor))
         (<= (pgs-dc-start cursor) (pgs-dc-pos cursor))
         (<= (pgs-dc-pos cursor) (pgs-dc-end cursor))
         (<= (* 8 (pgs-dc-pos cursor)) byte-total)
         (<= byte-total (* 8 (pgs-dc-end cursor)))
         (equal (pgs-dc-end cursor) (pgs-dc-total cursor))
         (<= (- (pgs-dc-end cursor) (pgs-dc-pos cursor)) 8)
         (true-listp (pgs-dc-cv cursor)) (equal (len (pgs-dc-cv cursor)) 8)
         (equal block (fn-b3-words 16 (pgs-dcr-span (pgs-dc-pos cursor) (pgs-dc-end cursor) msg)))
         (equal (pgs-dcr-denote msg (mv-nth 1 (pgs-dcb-step byte-total block cursor)))
                (pgs-dcr-denote msg cursor))))
  :hints (("Goal" :in-theory (enable pgs-dcr-denote pgs-dcr-current pgs-dcr-span)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
  :rule-classes nil)

;; Canonical fixed block hypothesis removed; every other antecedent holds.
(defthm pgs-dcbt-tail-block-removal
  (let* ((byte-total 3) (msg '(1 2 3))
         (cursor (mv-nth 1 (pgs-dcb-step byte-total nil
                   (pgs-dcb-begin 0 0 byte-total :capture-17 :lease-23 (create-pgs-digest)))))
         (block nil))
    (and (equal (pgs-dc-mode cursor) :chunk)
         (natp byte-total) (equal (len msg) byte-total)
         (natp (pgs-dc-start cursor)) (natp (pgs-dc-pos cursor)) (natp (pgs-dc-end cursor))
         (<= (pgs-dc-start cursor) (pgs-dc-pos cursor))
         (<= (pgs-dc-pos cursor) (pgs-dc-end cursor))
         (<= (* 8 (pgs-dc-pos cursor)) byte-total)
         (<= byte-total (* 8 (pgs-dc-end cursor)))
         (equal (pgs-dc-end cursor) (pgs-dc-total cursor))
         (<= (- (pgs-dc-end cursor) (pgs-dc-pos cursor)) 8)
         (true-listp (pgs-dc-cv cursor)) (equal (len (pgs-dc-cv cursor)) 8)
         (not (equal block (fn-b3-words 16 (pgs-dcr-span (pgs-dc-pos cursor) (pgs-dc-end cursor) msg))))
         (not (equal (pgs-dcr-denote msg (mv-nth 1 (pgs-dcb-step byte-total block cursor)))
                     (pgs-dcr-denote msg cursor)))))
  :hints (("Goal" :in-theory (enable pgs-dcr-denote pgs-dcr-current pgs-dcr-span)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
  :rule-classes nil)

;; Separately labelled stale fixed scratch: nonzero padding beyond ELEN.
(defthm pgs-dcbt-tail-padding-mutation
  (let* ((msg '(1 2 3)) (byte-total 3)
         (cursor (mv-nth 1 (pgs-dcb-step byte-total nil
                   (pgs-dcb-begin 0 0 byte-total :capture-17 :lease-23 (create-pgs-digest)))))
         (good (mv-nth 1 (pgs-dcb-step byte-total (fn-b3-words 16 msg) cursor)))
         (bad (mv-nth 1 (pgs-dcb-step byte-total (fn-b3-words 16 '(1 2 3 9)) cursor))))
    (and (equal (pgs-dc-mode good) :return) (equal (pgs-dc-mode bad) :return)
         (not (equal (pgs-dc-output good) (pgs-dc-output bad)))))
  :rule-classes nil)

(defun-nx pgs-dcbt-small-root ()
  (let* ((cursor (pgs-dcb-begin 0 0 3 :capture-17 :lease-23 (create-pgs-digest)))
         (cursor (mv-nth 1 (pgs-dcb-step 3 nil cursor)))
         (cursor (mv-nth 1 (pgs-dcb-step 3 (fn-b3-words 16 '(1 2 3)) cursor))))
    (mv-nth 1 (pgs-dcb-step 3 nil cursor))))

(defthm pgs-dcbt-terminal-positive
  (let ((byte-total 3) (msg '(1 2 3)) (cursor (pgs-dcbt-small-root)))
    (and (natp byte-total) (fn-b3-octet-listp msg) (equal (len msg) byte-total)
         (equal (pgs-dc-mode cursor) :root) (equal (pgs-dc-depth cursor) 0)
         (equal (pgs-dcr-denote msg cursor)
                (pgs-dcr-denote msg (pgs-dcb-begin 0 0 byte-total :capture-17 :lease-23 cursor)))
         (equal (pgs-dcb-result-octets (mv-nth 1 (pgs-dcb-step byte-total nil cursor)))
                (fn-blake3 msg))))
  :hints (("Goal" :in-theory (enable pgs-dcr-denote pgs-dcr-current pgs-dcr-span pgs-dcbt-small-root)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
  :rule-classes nil)

;; Literal captured-source semantic equality removed from terminal theorem;
;; all retained hypotheses affirmed, omitted hypothesis and conclusion fail.
(defthm pgs-dcbt-terminal-carry-removal
  (let ((byte-total 3) (msg '(1 2 4)) (cursor (pgs-dcbt-small-root)))
    (and (natp byte-total) (fn-b3-octet-listp msg) (equal (len msg) byte-total)
         (equal (pgs-dc-mode cursor) :root) (equal (pgs-dc-depth cursor) 0)
         (not (equal (pgs-dcr-denote msg cursor)
                     (pgs-dcr-denote msg (pgs-dcb-begin 0 0 byte-total :capture-17 :lease-23 cursor))))
         (not (equal (pgs-dcb-result-octets (mv-nth 1 (pgs-dcb-step byte-total nil cursor)))
                     (fn-blake3 msg)))))
  :hints (("Goal" :in-theory (enable pgs-dcr-denote pgs-dcr-current pgs-dcr-span pgs-dcbt-small-root)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
  :rule-classes nil)

(defthm pgs-dcbt-demand-positive
  (let ((cursor (mv-nth 1 (pgs-dcb-step 65 nil
                  (pgs-dcb-begin 0 0 65 :capture-17 :lease-23 (create-pgs-digest))))))
    (and (equal (pgs-dc-mode cursor) :chunk)
         (natp (pgs-dcb-read-demand 65 cursor))
         (<= (pgs-dcb-read-demand 65 cursor) 64)
         (equal (pgs-dcb-read-demand 65 cursor) 64)
         (equal (pgs-dcb-next-byte-offset cursor) 0)))
  :rule-classes nil)
