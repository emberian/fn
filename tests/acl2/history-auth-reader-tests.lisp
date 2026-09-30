(in-package "ACL2")
(include-book "../../books/history-auth-reader")

; Logical test I/O only. Runtime clients perform one requested byte or tick;
; they do not materialize PAGE alists or call this fuel-driven test traversal.
(defun fn-hsr-auth-test-run (fuel c buffer pages trace pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :measure (nfix fuel)
                  :guard (natp fuel) :verify-guards nil))
  (if (zp fuel) (mv :fuel c (reverse trace) pgs-digest-state)
    (case (fn-hsr-field 0 c)
      (:need-read
       (mv-let (v request next) (fn-hsr-auth-request c)
         (if (not (equal v :need-read)) (mv v next (reverse trace) pgs-digest-state)
           (let ((bytes (cdr (assoc-equal (fn-hsr-field 5 request) pages))))
             (mv-let (v next)
               (fn-hsr-auth-complete request (fn-hsr-field 3 request) (len bytes) :read-ok next)
               (declare (ignore v))
               (fn-hsr-auth-test-run (1- fuel) next bytes pages
                                     (cons (fn-hsr-field 5 request) trace) pgs-digest-state))))))
      (:digest
       (mv-let (v next pgs-digest-state) (fn-hsr-auth-digest-tick c pgs-digest-state)
         (declare (ignore v))
         (fn-hsr-auth-test-run (1- fuel) next buffer pages trace pgs-digest-state)))
      (:byte
       (let ((demand (fn-hsr-auth-byte-demand c)))
         (if (not (consp buffer)) (mv :missing-byte c (reverse trace) pgs-digest-state)
           (mv-let (v next)
             (fn-hsr-auth-feed-byte (fn-hsr-field 1 demand) (fn-hsr-field 2 demand) (car buffer) c)
             (if (not (equal v :yield)) (mv v next (reverse trace) pgs-digest-state)
               (fn-hsr-auth-test-run (1- fuel) next (cdr buffer) pages trace pgs-digest-state))))))
      (:release
       (mv-let (v next) (fn-hsr-auth-release (fn-hsr-field 5 (fn-hsr-field 1 c)) c)
         (if (not (equal v :released)) (mv v next (reverse trace) pgs-digest-state)
           (fn-hsr-auth-test-run (1- fuel) next nil pages trace pgs-digest-state))))
      (otherwise (mv (fn-hsr-field 17 c) c (reverse trace) pgs-digest-state)))))

(defun-nx fn-hsr-auth-test-example (np logical ddig pages fuel)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((mem (update-nth *pgs-mi* (pgs-zeros 20) (create-pgs-mem)))
         (root (mv-nth 0 (pgs-x-write-rec 0 9 17 np ddig mem (create-fn-octets-pg))))
         (c (mv-nth 1 (fn-hsr-auth-begin root 0 41 '(:captured 7) '(:lease 8 2))))
         (selected (fn-hsr-auth-select-page logical c (create-pgs-digest-state)))
         (result (fn-hsr-auth-test-run fuel (mv-nth 1 selected) nil pages nil (mv-nth 2 selected))))
    (list (mv-nth 0 result) (mv-nth 1 result) (mv-nth 2 result))))

(defconst *fn-hsr-auth-data-words* (make-list 2048 :initial-element 42))
(defconst *fn-hsr-auth-data* (pgs-words-le-octets *fn-hsr-auth-data-words*))
(defconst *fn-hsr-auth-data-digest* (pgs-octets-be-nat (fn-blake3 *fn-hsr-auth-data*)))
(defconst *fn-hsr-auth-table-words* (pgs-encode-table (list (list 304 7 *fn-hsr-auth-data-digest*))))
(defconst *fn-hsr-auth-table* (pgs-words-le-octets *fn-hsr-auth-table-words*))
(defconst *fn-hsr-auth-table-digest* (pgs-octets-be-nat (fn-blake3 *fn-hsr-auth-table*)))
(defconst *fn-hsr-auth-directory-words* (pgs-encode-run (list (list 91 8 *fn-hsr-auth-table-digest*)) 1))
(defconst *fn-hsr-auth-directory* (pgs-words-le-octets *fn-hsr-auth-directory-words*))
(defconst *fn-hsr-auth-directory-digest* (pgs-octets-be-nat (fn-blake3 *fn-hsr-auth-directory*)))
(defconst *fn-hsr-auth-pages*
  (list (cons 17 *fn-hsr-auth-directory*) (cons 91 *fn-hsr-auth-table*) (cons 304 *fn-hsr-auth-data*)))

; Actual root record comes from existing pgs-x-write-rec. Physical page numbers
; are deliberately unrelated to logical page0; all three real digests execute.
(defthm fn-hsr-auth-three-page-positive
   (let ((result (fn-hsr-auth-test-example 1 0 *fn-hsr-auth-directory-digest* *fn-hsr-auth-pages* 60000)))
     (and (equal (first result) '(:verified-page 0 41 0 304 2))
          (equal (third result) '(17 91 304))
          (equal (fn-hsr-field 0 (second result)) :verified)
          (equal (fn-hsr-auth-verified-byte-demand 123 (second result)) '(:buffer-byte 2 123 1))))
 :rule-classes nil)

; The selected six-word directory entry begins at word2046 and crosses the
; physical17/18 boundary. Hash and shape checks cover both pages together.
(defconst *fn-hsr-auth-wide-directory-words*
  (pgs-encode-run (append (make-list 341 :initial-element '(70 8 0))
                         (list (list 91 8 *fn-hsr-auth-table-digest*))) 2))
(defconst *fn-hsr-auth-wide-directory* (pgs-words-le-octets *fn-hsr-auth-wide-directory-words*))
(defconst *fn-hsr-auth-wide-digest* (pgs-octets-be-nat (fn-blake3 *fn-hsr-auth-wide-directory*)))
(defconst *fn-hsr-auth-wide-pages*
  (list (cons 17 (take 16384 *fn-hsr-auth-wide-directory*))
        (cons 18 (nthcdr 16384 *fn-hsr-auth-wide-directory*))
        (cons 91 *fn-hsr-auth-table*) (cons 304 *fn-hsr-auth-data*)))
(defthm fn-hsr-auth-straddling-directory-positive
  (let ((r (fn-hsr-auth-test-example 116282 116281 *fn-hsr-auth-wide-digest* *fn-hsr-auth-wide-pages* 90000)))
    (and (equal (first r) '(:verified-page 0 41 116281 304 3))
         (equal (third r) '(17 18 91 304))))
  :rule-classes nil)

(defthm fn-hsr-auth-directory-damage-stops-mapping
  (let ((r (fn-hsr-auth-test-example 1 0 *fn-hsr-auth-directory-digest*
             (acons 17 (update-nth 0 92 *fn-hsr-auth-directory*) *fn-hsr-auth-pages*) 60000)))
    (and (equal (first r) '(:refused (:dir-damaged 17)))
         (equal (third r) '(17))
         (equal (fn-hsr-field 5 (fn-hsr-field 1 (second r))) 0)
         (not (fn-hsr-auth-verified-byte-demand 0 (second r)))))
  :rule-classes nil)
(defconst *fn-hsr-auth-newer-directory*
  (pgs-words-le-octets (pgs-encode-run (list (list 91 10 *fn-hsr-auth-table-digest*)) 1)))
(defthm fn-hsr-auth-directory-malformed-stops-mapping
  (let ((r (fn-hsr-auth-test-example 1 0 (pgs-octets-be-nat (fn-blake3 *fn-hsr-auth-newer-directory*))
             (acons 17 *fn-hsr-auth-newer-directory* *fn-hsr-auth-pages*) 60000)))
    (and (equal (first r) '(:refused (:dir-malformed 17))) (equal (third r) '(17))))
  :rule-classes nil)
(defthm fn-hsr-auth-table-damage-stops-data-read
  (let ((r (fn-hsr-auth-test-example 1 0 *fn-hsr-auth-directory-digest*
             (acons 91 (update-nth 0 49 *fn-hsr-auth-table*) *fn-hsr-auth-pages*) 60000)))
    (and (equal (first r) '(:refused (:table-damaged 0 91))) (equal (third r) '(17 91))))
  :rule-classes nil)
(defthm fn-hsr-auth-data-damage-never-borrows
  (let ((r (fn-hsr-auth-test-example 1 0 *fn-hsr-auth-directory-digest*
             (acons 304 (update-nth 0 43 *fn-hsr-auth-data*) *fn-hsr-auth-pages*) 60000)))
    (and (equal (first r) '(:refused (:page-damaged 0 304)))
         (equal (third r) '(17 91 304))
         (not (fn-hsr-auth-verified-byte-demand 0 (second r)))))
  :rule-classes nil)
