(in-package "ACL2")
(include-book "../../books/pagestore-digest-cursor-domain")
(include-book "../../books/history-auth-reader-source")
(defun fn-hsr-source-test-run (fuel c buffer pages trace pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :measure (nfix fuel)
                  :guard (natp fuel) :verify-guards nil
                  :hints (("Goal" :in-theory (disable fn-hsr-auth-request fn-hsr-auth-complete
                    fn-hsr-auth-digest-tick fn-hsr-auth-byte-demand fn-hsr-auth-feed-byte
                    fn-hsr-auth-release fn-hsr-field)))))
  (if (zp fuel) (mv :fuel c (reverse trace) pgs-digest-state)
    (case (fn-hsr-field 0 c)
      (:need-read
       (mv-let (v request next) (fn-hsr-auth-request c)
         (if (not (equal v :need-read)) (mv v next (reverse trace) pgs-digest-state)
           (let ((bytes (cdr (assoc-equal (fn-hsr-field 5 request) pages))))
             (mv-let (v next)
               (fn-hsr-auth-complete request (fn-hsr-field 3 request) (len bytes) :read-ok next)
               (declare (ignore v))
               (fn-hsr-source-test-run (1- fuel) next bytes pages
                                     (cons (fn-hsr-field 5 request) trace) pgs-digest-state))))))
      (:digest
       (mv-let (v next pgs-digest-state) (fn-hsr-auth-digest-tick c pgs-digest-state)
         (declare (ignore v))
         (fn-hsr-source-test-run (1- fuel) next buffer pages trace pgs-digest-state)))
      (:byte
       (let ((demand (fn-hsr-auth-byte-demand c)))
         (if (not (consp buffer)) (mv :missing-byte c (reverse trace) pgs-digest-state)
           (mv-let (v next)
             (fn-hsr-auth-feed-byte (fn-hsr-field 1 demand) (fn-hsr-field 2 demand) (car buffer) c)
             (if (not (equal v :yield)) (mv v next (reverse trace) pgs-digest-state)
               (fn-hsr-source-test-run (1- fuel) next (cdr buffer) pages trace pgs-digest-state))))))
      (:release
       (mv-let (v next) (fn-hsr-auth-release (fn-hsr-field 5 (fn-hsr-field 1 c)) c)
         (if (not (equal v :released)) (mv v next (reverse trace) pgs-digest-state)
           (fn-hsr-source-test-run (1- fuel) next nil pages trace pgs-digest-state))))
      (otherwise (mv (fn-hsr-field 17 c) c (reverse trace) pgs-digest-state)))))


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



(defun-nx fn-hsr-source-test-verified ()
  (declare (xargs :guard t :verify-guards nil))
  (let* ((mem (update-nth *pgs-mi* (pgs-zeros 20) (create-pgs-mem)))
         (root (mv-nth 0 (pgs-x-write-rec 0 9 17 1 *fn-hsr-auth-directory-digest*
                                         mem (create-fn-octets-pg))))
         (begun (fn-hsr-source-begin root '(41 (7 3) 0 0) 0 '(:lease 8 2)))
         (selected (fn-hsr-auth-select-page 0 (mv-nth 1 begun) (create-pgs-digest-state)))
         (run (fn-hsr-source-test-run 60000 (mv-nth 1 selected) nil *fn-hsr-auth-pages* nil
                                  (mv-nth 2 selected))))
    (list (mv-nth 1 run) (mv-nth 2 begun))))

(defthm fn-hsr-source-verified-byte-positive
  (let* ((fixture (fn-hsr-source-test-verified)) (c (car fixture)) (b (cadr fixture))
         (d '(:need-byte (41 (7 3) 0 0) :cells 9 0 0))
         (answer (fn-hsr-source-verified-byte d b 0 c)))
    (and (fn-hsr-source-boundp b c)
         (equal (fn-hsr-field 17 c) '(:verified-page 0 41 0 304 2))
         (equal answer '(:ready (:buffer-byte 2 0 1) (:byte (41 (7 3) 0 0) :cells 9 0 0)))))
  :rule-classes nil)

(defthm fn-hsr-source-stale-demands-negative
  (let* ((fixture (fn-hsr-source-test-verified)) (c (car fixture)) (b (cadr fixture))
         (d '(:need-byte (41 (7 3) 0 0) :cells 9 0 0)))
    (and (fn-hsr-source-boundp b c)
         (equal (car (fn-hsr-source-verified-byte d b 0 c)) :ready)
         (equal (fn-hsr-source-verified-byte d b 1 c) '(:refused :source-byte))
         (equal (fn-hsr-source-verified-byte '(:need-byte (41 (7 3) 1 0) :cells 9 0 0) b 0 c)
                '(:refused :source-byte))
         (equal (fn-hsr-source-verified-byte '(:need-byte (41 (7 3) 0 1) :cells 9 0 0) b 0 c)
                '(:refused :source-byte))
         (equal (fn-hsr-source-verified-byte '(:need-byte (41 (7 4) 0 0) :cells 9 0 0) b 0 c)
                '(:refused :source-byte))
         (equal (fn-hsr-source-verified-byte '(:need-byte (41 (7 3) 0 0) :cells 9 1 0) b 0 c)
                '(:refused :source-byte))
         (equal (fn-hsr-source-verified-byte '(:need-byte (41 (7 3) 0 0) :cells 9 0 16384) b 0 c)
                '(:refused :source-byte))))
  :rule-classes nil)

(defthm fn-hsr-source-action-positive
  (let* ((fixture (fn-hsr-source-test-verified)) (c (car fixture)) (b (cadr fixture))
         (d '(:need-byte (41 (7 3) 0 0) :cells 9 0 0))
         (answer (fn-hsr-source-action d b 0 c)))
    (and (fn-hsr-source-boundp b c)
         (equal answer (fn-hsr-source-verified-byte d b 0 c))
         (equal (car answer) :ready)
         (equal (fn-hsr-source-byte-complete (caddr answer) 42)
                '(:byte (41 (7 3) 0 0) :cells 9 0 0 42))))
  :rule-classes nil)

(defun-nx fn-hsr-source-test-issued ()
  (declare (xargs :guard t :verify-guards nil))
  (let* ((mem (update-nth *pgs-mi* (pgs-zeros 20) (create-pgs-mem)))
         (root (mv-nth 0 (pgs-x-write-rec 0 9 17 1 *fn-hsr-auth-directory-digest*
                                         mem (create-fn-octets-pg))))
         (begin (fn-hsr-source-begin root '(41 (7 3) 0 0) 0 '(:lease 8 2)))
         (select (fn-hsr-auth-select-page 0 (mv-nth 1 begin) (create-pgs-digest-state)))
         (issued (fn-hsr-auth-request (mv-nth 1 select))))
    (list (mv-nth 1 issued) (mv-nth 2 issued))))

(defthm fn-hsr-source-cancel-digest-before-settle-positive
  (let* ((issued (fn-hsr-source-test-issued)) (request (car issued))
         (observed (fn-hsr-auth-complete request 0 (len *fn-hsr-auth-directory*) :read-ok (cadr issued)))
         (c (mv-nth 1 observed)) (cancel (fn-hsr-source-cancel-returned :uncertain c))
         (next (mv-nth 1 cancel)) (release (fn-hsr-auth-release 0 next)))
    (and (equal (mv-nth 0 observed) :yield)
         (equal (fn-hsr-field 0 c) :digest)
         (equal (fn-hsr-source-settle-demand 0 c) '(:retained :buffer-binding))
         (equal (mv-nth 0 (fn-hsr-auth-release 0 c)) '(:refused :release-state))
         (equal (fn-hsr-field 0 next) :refused)
         (equal (fn-hsr-field 5 (fn-hsr-field 1 next)) 0)
         (equal (fn-hsr-auth-identities next) (fn-hsr-auth-identities c))
         (equal (fn-hsr-source-settle-demand 0 next) '(:settle 0))
         (equal (mv-nth 0 release) :released)
         (equal (fn-hsr-source-settle-demand nil (mv-nth 1 release)) '(:closed))))
  :rule-classes nil)

(defthm fn-hsr-source-cancel-returned-exact-pending-positive
  (let* ((issued (fn-hsr-source-test-issued)) (c (cadr issued))
         (joined (fn-hsr-source-cancel-returned :uncertain c)) (next (mv-nth 1 joined))
         (invalid (fn-hsr-source-cancel-returned :ok c)))
    (and (equal (fn-hsr-field 0 c) :waiting)
         (equal (fn-hsr-field 4 (fn-hsr-field 1 c)) (car issued))
         (equal (fn-hsr-source-settle-demand nil c) '(:retained :pending-source))
         (equal (fn-hsr-field 0 next) :uncertain)
         (equal (fn-hsr-source-settle-demand nil next) '(:closed))
         (equal (fn-hsr-field 0 (mv-nth 1 invalid)) :waiting)
         (equal (fn-hsr-source-settle-demand nil (mv-nth 1 invalid)) '(:retained :pending-source))))
  :rule-classes nil)
