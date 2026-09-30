(in-package "ACL2")
(include-book "../../books/history-page-reader-io")

(defun fn-hsr-test-io-request (phase physical logical c)
  (declare (xargs :guard t))
  (mv-let (a b next) (fn-hsr-io-request phase physical logical c) (list a b next)))
(defun fn-hsr-test-io-complete (request discovery-id count status c)
  (declare (xargs :guard t))
  (mv-let (a next) (fn-hsr-io-complete request discovery-id count status c) (list a next)))
(defun fn-hsr-test-io-cancel (c)
  (declare (xargs :guard t))
  (mv-let (a next) (fn-hsr-io-cancel c) (list a next)))
(defun fn-hsr-test-io-release (discovery-id c)
  (declare (xargs :guard t))
  (mv-let (a next) (fn-hsr-io-release discovery-id c) (list a next)))
(defun fn-hsr-test-io-joined-failure (request outcome c)
  (declare (xargs :guard t))
  (mv-let (a next) (fn-hsr-io-joined-failure request outcome c) (list a next)))

(defconst *fn-hsr-io-start* (fn-hsr-io-begin 0 9 '(:source 17) '(:lease 8 2)))
(defconst *fn-hsr-io-issued* (fn-hsr-test-io-request :directory 100 341 *fn-hsr-io-start*))
(defconst *fn-hsr-io-request* (mv-nth 1 *fn-hsr-io-issued*))
(defconst *fn-hsr-io-wait* (mv-nth 2 *fn-hsr-io-issued*))
(defconst *fn-hsr-io-observed*
  (mv-nth 1 (fn-hsr-test-io-complete *fn-hsr-io-request* 0 16384 :read-ok *fn-hsr-io-wait*)))

(defun fn-hsr-test-cycle-conclusion (phase physical logical discovery-id c)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((issued (fn-hsr-test-io-request phase physical logical c))
         (old-request (mv-nth 1 issued))
         (observed (mv-nth 1 (fn-hsr-test-io-complete old-request discovery-id 16384 :read-ok
                                                (mv-nth 2 issued))))
         (released (mv-nth 1 (fn-hsr-test-io-release discovery-id observed)))
         (again (fn-hsr-test-io-request phase physical logical released)))
    (and (equal (mv-nth 0 issued) :need-read)
         (equal (fn-hsr-field 0 observed) :observed)
         (equal (fn-hsr-field 5 observed) discovery-id)
         (equal (mv-nth 0 again) :need-read)
         (equal (fn-hsr-field 3 (mv-nth 1 again)) (+ 1 (fn-hsr-field 3 old-request)))
         (not (equal (mv-nth 1 again) old-request))
         (equal (mv-nth 1 (fn-hsr-test-io-complete old-request discovery-id 16384 :read-ok
                                             (mv-nth 2 again)))
                (mv-nth 2 again)))))
(defun fn-hsr-test-short-conclusion (c discovery-id count status)
  (declare (xargs :guard t))
  (let* ((next (mv-nth 1 (fn-hsr-test-io-complete (fn-hsr-field 4 c) discovery-id count status c)))
         (released (mv-nth 1 (fn-hsr-test-io-release discovery-id next)))
         (cancelled (mv-nth 1 (fn-hsr-test-io-cancel released))))
    (and (equal (fn-hsr-field 0 next) :uncertain)
         (equal (fn-hsr-field 5 next) discovery-id)
         (equal (fn-hsr-field 0 released) :uncertain)
         (equal (fn-hsr-field 5 released) nil)
         (equal (fn-hsr-field 0 cancelled) :uncertain)
         (equal (mv-nth 0 (fn-hsr-test-io-request :data 100 341 cancelled))
                '(:refused :request-state)))))

; Root/resource tickets begin at zero. NIL alone denotes no held discovery.
(assert-event
 (and (natp 0) (natp 9) (fn-hsr-io-invariantp *fn-hsr-io-start*)
      (fn-hsr-io-invariantp *fn-hsr-io-wait*)
      (fn-hsr-io-invariantp *fn-hsr-io-observed*)
      (equal *fn-hsr-io-request* '(:read-page 0 9 0 :directory 100 1638400 16384 341))
      (equal (fn-hsr-field 5 *fn-hsr-io-observed*) 0)))
(assert-event
 (and (fn-hsr-io-invariantp *fn-hsr-io-start*)
      (equal (fn-hsr-field 0 *fn-hsr-io-start*) :idle)
      (member-eq :directory '(:directory :table :data)) (natp 100) (natp 341) (natp 0)
      (fn-hsr-test-cycle-conclusion :directory 100 341 0 *fn-hsr-io-start*)))
(assert-event
 (let* ((cancelled (mv-nth 1 (fn-hsr-test-io-cancel *fn-hsr-io-wait*)))
        (joined (mv-nth 1 (fn-hsr-test-io-complete *fn-hsr-io-request* 0 16384 :read-ok cancelled))))
   (and (fn-hsr-io-invariantp *fn-hsr-io-wait*)
        (fn-hsr-io-invariantp cancelled) (fn-hsr-io-invariantp joined)
        (equal (fn-hsr-field 4 cancelled) (fn-hsr-field 4 *fn-hsr-io-wait*))
        (equal (fn-hsr-field 5 cancelled) (fn-hsr-field 5 *fn-hsr-io-wait*))
        (equal (mv-nth 1 (fn-hsr-test-io-release 0 cancelled)) cancelled)
        (equal (fn-hsr-field 0 joined) :refused) (equal (fn-hsr-field 5 joined) 0)
        (fn-hsr-io-invariantp (mv-nth 1 (fn-hsr-test-io-release 0 joined))))))
(assert-event
 (and (fn-hsr-io-shapep *fn-hsr-io-wait*) (equal (fn-hsr-field 0 *fn-hsr-io-wait*) :waiting)
      (natp 0) (or (not (equal :read-ok :read-ok)) (not (equal 17 16384)))
      (fn-hsr-test-short-conclusion *fn-hsr-io-wait* 0 17 :read-ok)))
(assert-event
 (let* ((joined (mv-nth 1 (fn-hsr-test-io-joined-failure *fn-hsr-io-request* :uncertain *fn-hsr-io-wait*)))
        (cancelled (mv-nth 1 (fn-hsr-test-io-cancel joined))))
   (and (fn-hsr-io-invariantp *fn-hsr-io-wait*) (fn-hsr-io-invariantp joined)
        (fn-hsr-io-invariantp cancelled) (equal (fn-hsr-field 0 joined) :uncertain)
        (equal (fn-hsr-field 0 cancelled) :uncertain) (not (fn-hsr-field 4 joined))
        (not (fn-hsr-field 5 joined)))))
; All literal identity conclusions on an actual nonempty pending request.
(assert-event
 (let* ((c *fn-hsr-io-wait*) (request *fn-hsr-io-request*) (ids (fn-hsr-io-identities c)))
   (and (equal (fn-hsr-io-identities (mv-nth 2 (fn-hsr-test-io-request :data 120 341 c))) ids)
        (equal (fn-hsr-io-identities (mv-nth 1 (fn-hsr-test-io-complete request 0 16384 :read-ok c))) ids)
        (equal (fn-hsr-io-identities (mv-nth 1 (fn-hsr-test-io-cancel c))) ids)
        (equal (fn-hsr-io-identities (mv-nth 1 (fn-hsr-test-io-release 0 c))) ids)
        (equal (fn-hsr-io-identities (mv-nth 1 (fn-hsr-test-io-joined-failure request :refused c))) ids))))
; Corrupted-state removals for each invariant-preservation hypothesis.
(assert-event
 (let ((c nil))
   (and (not (fn-hsr-io-invariantp c))
        (not (fn-hsr-io-invariantp (mv-nth 2 (fn-hsr-test-io-request :data 1 1 c))))
        (not (fn-hsr-io-invariantp (mv-nth 1 (fn-hsr-test-io-complete nil 0 16384 :read-ok c))))
        (not (fn-hsr-io-invariantp (mv-nth 1 (fn-hsr-test-io-cancel c))))
        (not (fn-hsr-io-invariantp (mv-nth 1 (fn-hsr-test-io-release 0 c))))
        (not (fn-hsr-io-invariantp (mv-nth 1 (fn-hsr-test-io-joined-failure nil :refused c)))))))
(assert-event
 (with-guard-checking :none
   (and (not (natp -1)) (natp 9)
        (not (fn-hsr-io-invariantp (fn-hsr-io-begin -1 9 :c :l))))))
(assert-event
 (with-guard-checking :none
   (and (natp 0) (not (natp -1))
        (not (fn-hsr-io-invariantp (fn-hsr-io-begin 0 -1 :c :l))))))
; Mismatch premise removed: matching completion really advances the cursor.
(assert-event
 (and (equal *fn-hsr-io-request* (fn-hsr-field 4 *fn-hsr-io-wait*))
      (not (equal *fn-hsr-io-observed* *fn-hsr-io-wait*))))

(assert-event
 (let ((c '(:idle -1 9 0 nil nil :c :l nil)) (phase :directory) (physical 100) (logical 341) (discovery-id 0))
   (and (not (fn-hsr-io-invariantp c))
        (equal (fn-hsr-field 0 c) :idle)
        (member-eq phase '(:directory :table :data))
        (natp physical)
        (natp logical)
        (natp discovery-id)
        (not (fn-hsr-test-cycle-conclusion phase physical logical discovery-id c)))))

(assert-event
 (let ((c *fn-hsr-io-wait*) (phase :directory) (physical 100) (logical 341) (discovery-id 0))
   (and (fn-hsr-io-invariantp c)
        (not (equal (fn-hsr-field 0 c) :idle))
        (member-eq phase '(:directory :table :data))
        (natp physical)
        (natp logical)
        (natp discovery-id)
        (not (fn-hsr-test-cycle-conclusion phase physical logical discovery-id c)))))

(assert-event
 (let ((c *fn-hsr-io-start*) (phase :bogus) (physical 100) (logical 341) (discovery-id 0))
   (and (fn-hsr-io-invariantp c)
        (equal (fn-hsr-field 0 c) :idle)
        (not (member-eq phase '(:directory :table :data)))
        (natp physical)
        (natp logical)
        (natp discovery-id)
        (not (fn-hsr-test-cycle-conclusion phase physical logical discovery-id c)))))

(assert-event
 (let ((c *fn-hsr-io-start*) (phase :directory) (physical -1) (logical 341) (discovery-id 0))
   (and (fn-hsr-io-invariantp c)
        (equal (fn-hsr-field 0 c) :idle)
        (member-eq phase '(:directory :table :data))
        (not (natp physical))
        (natp logical)
        (natp discovery-id)
        (not (fn-hsr-test-cycle-conclusion phase physical logical discovery-id c)))))

(assert-event
 (let ((c *fn-hsr-io-start*) (phase :directory) (physical 100) (logical -1) (discovery-id 0))
   (and (fn-hsr-io-invariantp c)
        (equal (fn-hsr-field 0 c) :idle)
        (member-eq phase '(:directory :table :data))
        (natp physical)
        (not (natp logical))
        (natp discovery-id)
        (not (fn-hsr-test-cycle-conclusion phase physical logical discovery-id c)))))

(assert-event
 (let ((c *fn-hsr-io-start*) (phase :directory) (physical 100) (logical 341) (discovery-id nil))
   (and (fn-hsr-io-invariantp c)
        (equal (fn-hsr-field 0 c) :idle)
        (member-eq phase '(:directory :table :data))
        (natp physical)
        (natp logical)
        (not (natp discovery-id))
        (not (fn-hsr-test-cycle-conclusion phase physical logical discovery-id c)))))

(assert-event
 (let ((c '(:waiting -1 9 1 (:read-page 0 9 0 :directory 100 1638400 16384 341) nil :c :l nil)) (discovery-id 0) (count 17) (status :read-ok))
   (and (not (fn-hsr-io-shapep c))
        (equal (fn-hsr-field 0 c) :waiting)
        (natp discovery-id)
        (or (not (equal status :read-ok)) (not (equal count 16384)))
        (not (fn-hsr-test-short-conclusion c discovery-id count status)))))

(assert-event
 (let ((c *fn-hsr-io-start*) (discovery-id 0) (count 17) (status :read-ok))
   (and (fn-hsr-io-shapep c)
        (not (equal (fn-hsr-field 0 c) :waiting))
        (natp discovery-id)
        (or (not (equal status :read-ok)) (not (equal count 16384)))
        (not (fn-hsr-test-short-conclusion c discovery-id count status)))))

(assert-event
 (let ((c *fn-hsr-io-wait*) (discovery-id nil) (count 17) (status :read-ok))
   (and (fn-hsr-io-shapep c)
        (equal (fn-hsr-field 0 c) :waiting)
        (not (natp discovery-id))
        (or (not (equal status :read-ok)) (not (equal count 16384)))
        (not (fn-hsr-test-short-conclusion c discovery-id count status)))))

(assert-event
 (let ((c *fn-hsr-io-wait*) (discovery-id 0) (count 16384) (status :read-ok))
   (and (fn-hsr-io-shapep c)
        (equal (fn-hsr-field 0 c) :waiting)
        (natp discovery-id)
        (not (or (not (equal status :read-ok)) (not (equal count 16384))))
        (not (fn-hsr-test-short-conclusion c discovery-id count status)))))
