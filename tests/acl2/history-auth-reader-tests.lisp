(in-package "ACL2")
(include-book "../../books/history-auth-reader")
(include-book "../../books/pagestore-digest-cursor-domain")

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

; The first physical borrow may have ID0. A short completion retains it until
; settlement and cannot expose even one byte to the decoder.
(defun-nx fn-hsr-auth-test-waiting ()
  (declare (xargs :guard t :verify-guards nil))
  (let* ((mem (update-nth *pgs-mi* (pgs-zeros 20) (create-pgs-mem)))
         (root (mv-nth 0 (pgs-x-write-rec 0 9 17 1 *fn-hsr-auth-directory-digest*
                                         mem (create-fn-octets-pg))))
         (c (mv-nth 1 (fn-hsr-auth-begin root 0 41 '(:captured 7) '(:lease 8 2))))
         (selected (fn-hsr-auth-select-page 0 c (create-pgs-digest-state)))
         (issued (fn-hsr-auth-request (mv-nth 1 selected))))
    (list (mv-nth 1 issued) (mv-nth 2 issued))))

(defthm fn-hsr-auth-short-completion-positive
  (let* ((issued (fn-hsr-auth-test-waiting)) (request (first issued)) (c (second issued))
         (count 16383) (discovery-id 0)
         (completed (fn-hsr-auth-complete request discovery-id count :read-ok c))
         (next (mv-nth 1 completed)))
    (and (fn-hsr-auth-shapep c)
         (equal (fn-hsr-field 0 c) :waiting)
         (equal (fn-hsr-field 0 (fn-hsr-field 1 c)) :waiting)
         (equal request (fn-hsr-field 4 (fn-hsr-field 1 c)))
         (natp discovery-id) (not (equal count 16384))
         (equal (mv-nth 0 completed) '(:uncertain :read-completion))
         (equal (fn-hsr-field 0 next) :uncertain)
         (equal (fn-hsr-field 5 (fn-hsr-field 1 next)) discovery-id)
         (equal (fn-hsr-field 2 next) (fn-hsr-field 2 c))
         (not (fn-hsr-auth-byte-demand next))
         (not (fn-hsr-auth-verified-byte-demand 0 next))
         (equal (mv-nth 0 (fn-hsr-auth-release discovery-id next)) :released)
         (equal (fn-hsr-field 0 (mv-nth 1 (fn-hsr-auth-release discovery-id next))) :uncertain)))
  :rule-classes nil)

(defthm fn-hsr-auth-begin-shape-positive
  (let* ((root '(:pgs-commit 9 17 1 0 0))
         (begun (fn-hsr-auth-begin root 0 41 '(:captured 7) '(:lease 8 2))))
    (and (equal (mv-nth 0 begun) :idle)
         (fn-hsr-auth-shapep (mv-nth 1 begun))
         (fn-hsr-io-invariantp (fn-hsr-field 1 (mv-nth 1 begun)))
         (fn-hsr-auth-lifetimep (mv-nth 1 begun))))
  :rule-classes nil)

(defthm fn-hsr-auth-begin-shape-hypothesis-removal
  (let ((begun (fn-hsr-auth-begin nil 0 41 '(:captured 7) '(:lease 8 2))))
    (and (not (equal (mv-nth 0 begun) :idle))
         (not (fn-hsr-auth-lifetimep (mv-nth 1 begun)))
         (not (and (fn-hsr-auth-shapep (mv-nth 1 begun))
                   (fn-hsr-io-invariantp (fn-hsr-field 1 (mv-nth 1 begun)))))))
  :rule-classes nil)

; Hypothesis-removal witness over deliberately corrupted state.
(defthm fn-hsr-auth-short-shape-removal
  (let* ((issued (fn-hsr-auth-test-waiting)) (original (second issued))
         (c (fn-hsr-put 2 nil original)) (request (first issued)) (discovery-id 0) (count 16383)
         (completed (fn-hsr-auth-complete request discovery-id count :read-ok c))
         (next (mv-nth 1 completed)))
    (and (equal (fn-hsr-field 0 c) :waiting) (equal (fn-hsr-field 0 (fn-hsr-field 1 c)) :waiting) (equal request (fn-hsr-field 4 (fn-hsr-field 1 c))) (natp discovery-id) (not (equal count 16384))
         (not (fn-hsr-auth-shapep c))
         (not (and (equal (mv-nth 0 completed) '(:uncertain :read-completion))
                   (equal (fn-hsr-field 0 next) :uncertain)
                   (equal (fn-hsr-field 5 (fn-hsr-field 1 next)) discovery-id)
                   (equal (fn-hsr-field 2 next) (fn-hsr-field 2 c))
                   (not (fn-hsr-auth-byte-demand next))
                   (not (fn-hsr-auth-verified-byte-demand 0 next))))))
  :rule-classes nil)

; Hypothesis-removal witness over deliberately corrupted state.
(defthm fn-hsr-auth-short-auth-mode-removal
  (let* ((issued (fn-hsr-auth-test-waiting)) (original (second issued))
         (c (fn-hsr-put 0 :idle original)) (request (first issued)) (discovery-id 0) (count 16383)
         (completed (fn-hsr-auth-complete request discovery-id count :read-ok c))
         (next (mv-nth 1 completed)))
    (and (fn-hsr-auth-shapep c) (equal (fn-hsr-field 0 (fn-hsr-field 1 c)) :waiting) (equal request (fn-hsr-field 4 (fn-hsr-field 1 c))) (natp discovery-id) (not (equal count 16384))
         (not (equal (fn-hsr-field 0 c) :waiting))
         (not (and (equal (mv-nth 0 completed) '(:uncertain :read-completion))
                   (equal (fn-hsr-field 0 next) :uncertain)
                   (equal (fn-hsr-field 5 (fn-hsr-field 1 next)) discovery-id)
                   (equal (fn-hsr-field 2 next) (fn-hsr-field 2 c))
                   (not (fn-hsr-auth-byte-demand next))
                   (not (fn-hsr-auth-verified-byte-demand 0 next))))))
  :rule-classes nil)

; Hypothesis-removal witness over deliberately corrupted state.
(defthm fn-hsr-auth-short-io-mode-removal
  (let* ((issued (fn-hsr-auth-test-waiting)) (original (second issued))
         (c (fn-hsr-put 1 (fn-hsr-put 0 :idle (fn-hsr-field 1 original)) original)) (request (first issued)) (discovery-id 0) (count 16383)
         (completed (fn-hsr-auth-complete request discovery-id count :read-ok c))
         (next (mv-nth 1 completed)))
    (and (fn-hsr-auth-shapep c) (equal (fn-hsr-field 0 c) :waiting) (equal request (fn-hsr-field 4 (fn-hsr-field 1 c))) (natp discovery-id) (not (equal count 16384))
         (not (equal (fn-hsr-field 0 (fn-hsr-field 1 c)) :waiting))
         (not (and (equal (mv-nth 0 completed) '(:uncertain :read-completion))
                   (equal (fn-hsr-field 0 next) :uncertain)
                   (equal (fn-hsr-field 5 (fn-hsr-field 1 next)) discovery-id)
                   (equal (fn-hsr-field 2 next) (fn-hsr-field 2 c))
                   (not (fn-hsr-auth-byte-demand next))
                   (not (fn-hsr-auth-verified-byte-demand 0 next))))))
  :rule-classes nil)

; Hypothesis-removal witness.
(defthm fn-hsr-auth-short-request-removal
  (let* ((issued (fn-hsr-auth-test-waiting)) (original (second issued))
         (c original) (request nil) (discovery-id 0) (count 16383)
         (completed (fn-hsr-auth-complete request discovery-id count :read-ok c))
         (next (mv-nth 1 completed)))
    (and (fn-hsr-auth-shapep c) (equal (fn-hsr-field 0 c) :waiting) (equal (fn-hsr-field 0 (fn-hsr-field 1 c)) :waiting) (natp discovery-id) (not (equal count 16384))
         (not (equal request (fn-hsr-field 4 (fn-hsr-field 1 c))))
         (not (and (equal (mv-nth 0 completed) '(:uncertain :read-completion))
                   (equal (fn-hsr-field 0 next) :uncertain)
                   (equal (fn-hsr-field 5 (fn-hsr-field 1 next)) discovery-id)
                   (equal (fn-hsr-field 2 next) (fn-hsr-field 2 c))
                   (not (fn-hsr-auth-byte-demand next))
                   (not (fn-hsr-auth-verified-byte-demand 0 next))))))
  :rule-classes nil)

; Hypothesis-removal witness.
(defthm fn-hsr-auth-short-discovery-removal
  (let* ((issued (fn-hsr-auth-test-waiting)) (original (second issued))
         (c original) (request (first issued)) (discovery-id nil) (count 16383)
         (completed (fn-hsr-auth-complete request discovery-id count :read-ok c))
         (next (mv-nth 1 completed)))
    (and (fn-hsr-auth-shapep c) (equal (fn-hsr-field 0 c) :waiting) (equal (fn-hsr-field 0 (fn-hsr-field 1 c)) :waiting) (equal request (fn-hsr-field 4 (fn-hsr-field 1 c))) (not (equal count 16384))
         (not (natp discovery-id))
         (not (and (equal (mv-nth 0 completed) '(:uncertain :read-completion))
                   (equal (fn-hsr-field 0 next) :uncertain)
                   (equal (fn-hsr-field 5 (fn-hsr-field 1 next)) discovery-id)
                   (equal (fn-hsr-field 2 next) (fn-hsr-field 2 c))
                   (not (fn-hsr-auth-byte-demand next))
                   (not (fn-hsr-auth-verified-byte-demand 0 next))))))
  :rule-classes nil)

; Hypothesis-removal witness.
(defthm fn-hsr-auth-short-count-removal
  (let* ((issued (fn-hsr-auth-test-waiting)) (original (second issued))
         (c original) (request (first issued)) (discovery-id 0) (count 16384)
         (completed (fn-hsr-auth-complete request discovery-id count :read-ok c))
         (next (mv-nth 1 completed)))
    (and (fn-hsr-auth-shapep c) (equal (fn-hsr-field 0 c) :waiting) (equal (fn-hsr-field 0 (fn-hsr-field 1 c)) :waiting) (equal request (fn-hsr-field 4 (fn-hsr-field 1 c))) (natp discovery-id)
         (not (not (equal count 16384)))
         (not (and (equal (mv-nth 0 completed) '(:uncertain :read-completion))
                   (equal (fn-hsr-field 0 next) :uncertain)
                   (equal (fn-hsr-field 5 (fn-hsr-field 1 next)) discovery-id)
                   (equal (fn-hsr-field 2 next) (fn-hsr-field 2 c))
                   (not (fn-hsr-auth-byte-demand next))
                   (not (fn-hsr-auth-verified-byte-demand 0 next))))))
  :rule-classes nil)

; A second logical read uses the same root pin and the next request serial.
; An old completion cannot acquire ownership in the new pass.
(defun-nx fn-hsr-auth-test-repeat-select ()
  (declare (xargs :guard t :verify-guards nil))
  (let* ((first-read (fn-hsr-auth-test-example 1 0 *fn-hsr-auth-directory-digest*
                                           *fn-hsr-auth-pages* 60000))
         (verified (second first-read))
         (released (fn-hsr-auth-release 2 verified))
         (selected (fn-hsr-auth-select-page 0 (mv-nth 1 released) (create-pgs-digest-state)))
         (issued (fn-hsr-auth-request (mv-nth 1 selected))))
    (list verified (mv-nth 0 released) (mv-nth 1 issued) (mv-nth 2 issued)
          (mv-nth 1 selected))))

(defthm fn-hsr-auth-repeat-select-serial-positive
  (let* ((repeated (fn-hsr-auth-test-repeat-select))
         (verified (first repeated)) (request (third repeated)) (waiting (fourth repeated))
         (old (first (fn-hsr-auth-test-waiting)))
         (stale (fn-hsr-auth-complete old 88 16384 :read-ok waiting)))
    (and (equal (fn-hsr-field 0 verified) :verified)
         (equal (second repeated) :released)
         (equal request '(:read-page 0 41 3 :directory 17 278528 16384 0))
         (equal (fn-hsr-field 2 waiting) (fn-hsr-field 2 verified))
         (equal (fn-hsr-field 6 (fn-hsr-field 1 waiting)) '(:captured 7))
         (equal (fn-hsr-field 7 (fn-hsr-field 1 waiting)) '(:lease 8 2))
         (equal (fn-hsr-field 3 (fn-hsr-field 1 waiting)) 4)
         (equal (mv-nth 0 stale) '(:refused :stale-completion))
         (equal (mv-nth 1 stale) waiting)
         (equal (fn-hsr-field 5 (fn-hsr-field 1 waiting)) nil)))
  :rule-classes nil)

(defthm fn-hsr-auth-lifetime-io-positive
  (let* ((issued (fn-hsr-auth-test-waiting)) (request (first issued)) (waiting (second issued))
         (observed (mv-nth 1 (fn-hsr-auth-complete request 0 16384 :read-ok waiting)))
         (short (mv-nth 1 (fn-hsr-auth-complete request 0 16383 :read-ok waiting)))
         (cancelled (mv-nth 1 (fn-hsr-auth-cancel waiting)))
         (joined (mv-nth 1 (fn-hsr-auth-joined-failure request :uncertain cancelled)))
         (released (mv-nth 1 (fn-hsr-auth-release 0 short)))
         (need-read (fifth (fn-hsr-auth-test-repeat-select)))
         (reissued (fn-hsr-auth-request need-read)))
    (and (fn-hsr-auth-lifetimep waiting)
         (fn-hsr-auth-lifetimep need-read)
         (equal (fn-hsr-field 0 need-read) :need-read)
         (equal (mv-nth 0 reissued) :need-read)
         (fn-hsr-auth-lifetimep (mv-nth 2 reissued))
         (fn-hsr-auth-lifetimep observed)
         (fn-hsr-auth-lifetimep short)
         (fn-hsr-auth-lifetimep cancelled)
         (fn-hsr-auth-lifetimep joined)
         (fn-hsr-auth-lifetimep released)
         (equal (fn-hsr-field 0 observed) :digest)
         (equal (fn-hsr-field 0 short) :uncertain)
         (equal (fn-hsr-field 0 cancelled) :waiting)
         (equal (fn-hsr-field 0 joined) :uncertain)
         (equal (fn-hsr-field 0 released) :uncertain)))
  :rule-classes nil)

; One literal antecedent-removal counterexample for each I/O lifetime theorem.
(defthm fn-hsr-auth-lifetime-io-hypothesis-removals
  (and (not (fn-hsr-auth-lifetimep nil))
       (not (fn-hsr-auth-lifetimep (mv-nth 2 (fn-hsr-auth-request nil))))
       (not (fn-hsr-auth-lifetimep (mv-nth 1 (fn-hsr-auth-complete nil 0 16384 :read-ok nil))))
       (not (fn-hsr-auth-lifetimep (mv-nth 1 (fn-hsr-auth-cancel nil))))
       (not (fn-hsr-auth-lifetimep (mv-nth 1 (fn-hsr-auth-joined-failure nil :uncertain nil))))
       (not (fn-hsr-auth-lifetimep (mv-nth 1 (fn-hsr-auth-release 0 nil)))))
  :rule-classes nil)

; Deliberately corrupted outer/nested mode disagreement is refused unchanged.
(defthm fn-hsr-auth-corrupted-waiting-mode-refused
  (let* ((issued (fn-hsr-auth-test-waiting))
         (c (fn-hsr-put 1 (fn-hsr-put 0 :observed (fn-hsr-field 1 (second issued)))
                        (second issued)))
         (completion (fn-hsr-auth-complete (first issued) 0 16384 :read-ok c))
         (join (fn-hsr-auth-joined-failure (first issued) :uncertain c)))
    (and (fn-hsr-auth-shapep c) (not (fn-hsr-auth-lifetimep c))
         (equal (fn-hsr-field 0 c) :waiting)
         (equal (fn-hsr-field 0 (fn-hsr-field 1 c)) :observed)
         (equal (mv-nth 0 completion) '(:refused :completion-state))
         (equal (mv-nth 1 completion) c)
         (equal (mv-nth 0 join) '(:refused :join-state))
         (equal (mv-nth 1 join) c)))
  :rule-classes nil)
