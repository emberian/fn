; PRF-1107: fixed-state request/completion and page-borrow continuation.
; Mapping authority is supplied by the authenticated caller, not this I/O seam.
(in-package "ACL2")
(include-book "history-page-reader")
(local (include-book "arithmetic/top" :dir :system))

; mode,ticket,epoch,next serial,pending request,borrow ID,capture,lease,cancel.
; The exact registered incarnation and physical buffer remain in the caller's
; ledger. Scalar IDs distinguish them without retaining/traversing file paths.
(defun fn-hsr-io-shapep (c)
  (declare (xargs :guard t))
  (and (fn-hsr-widthp c 9)
       (member-eq (fn-hsr-field 0 c) '(:idle :waiting :observed :refused :uncertain))
       (natp (fn-hsr-field 1 c)) (natp (fn-hsr-field 2 c))
       (natp (fn-hsr-field 3 c))
       (or (null (fn-hsr-field 5 c)) (natp (fn-hsr-field 5 c)))
       (or (not (fn-hsr-field 4 c)) (fn-hsr-widthp (fn-hsr-field 4 c) 9))
       (booleanp (fn-hsr-field 8 c))))

(defun fn-hsr-io-begin (ticket epoch capture lease)
  (declare (xargs :guard (and (natp ticket) (natp epoch))))
  (list :idle ticket epoch 0 nil nil capture lease nil))

(defun fn-hsr-io-request (phase physical logical c)
  (declare (xargs :guard t))
  (if (not (and (fn-hsr-io-shapep c) (equal (fn-hsr-field 0 c) :idle)
                (not (fn-hsr-field 4 c)) (equal (fn-hsr-field 5 c) nil)
                (not (fn-hsr-field 8 c))
                (member-eq phase '(:directory :table :data))
                (natp physical) (natp logical)))
      (mv '(:refused :request-state) nil c)
    (let* ((ticket (fn-hsr-field 1 c)) (epoch (fn-hsr-field 2 c))
           (serial (fn-hsr-field 3 c))
           (request (list :read-page ticket epoch serial phase physical
                          (* 16384 physical) 16384 logical)))
      (mv :need-read request
          (list :waiting ticket epoch (+ 1 serial) request nil
                (fn-hsr-field 6 c) (fn-hsr-field 7 c) nil)))))

(defun fn-hsr-io-complete (request discovery-id count status c)
  (declare (xargs :guard t))
  (cond ((not (and (fn-hsr-io-shapep c)
                    (equal (fn-hsr-field 0 c) :waiting)
                    (equal request (fn-hsr-field 4 c))
                    (natp discovery-id)))
         (mv '(:refused :stale-completion) c))
        (t
         (let* ((verdict (cond ((not (and (equal status :read-ok) (equal count 16384)))
                               '(:uncertain :read-completion))
                              ((fn-hsr-field 8 c) '(:refused :cancelled))
                              (t :observed)))
                (mode (cond ((equal verdict :observed) :observed)
                            ((equal (car verdict) :uncertain) :uncertain)
                            (t :refused))))
           (mv verdict
               (list mode (fn-hsr-field 1 c) (fn-hsr-field 2 c) (fn-hsr-field 3 c)
                     nil discovery-id (fn-hsr-field 6 c) (fn-hsr-field 7 c)
                     (fn-hsr-field 8 c)))))))

(defun fn-hsr-io-cancel (c)
  (declare (xargs :guard t))
  (if (not (fn-hsr-io-shapep c)) (mv '(:refused :cancel-state) c)
    (let ((waiting (equal (fn-hsr-field 0 c) :waiting)))
      (mv (cond (waiting :waiting-for-join)
                ((equal (fn-hsr-field 0 c) :uncertain) '(:uncertain :cancelled-after-io))
                (t '(:refused :cancelled)))
          (list (cond (waiting :waiting)
                      ((equal (fn-hsr-field 0 c) :uncertain) :uncertain)
                      (t :refused))
                (fn-hsr-field 1 c) (fn-hsr-field 2 c) (fn-hsr-field 3 c)
                (fn-hsr-field 4 c) (fn-hsr-field 5 c)
                (fn-hsr-field 6 c) (fn-hsr-field 7 c) t)))))

(defun fn-hsr-io-release (discovery-id c)
  ; Called only after the host has settled the exact buffer and removed all
  ; consumer aliases. Does not release any physical resource by itself.
  (declare (xargs :guard t))
  (if (not (and (fn-hsr-io-shapep c) (natp discovery-id)
                (equal discovery-id (fn-hsr-field 5 c))
                (not (equal (fn-hsr-field 0 c) :waiting))
                (not (fn-hsr-field 4 c))))
      (mv '(:refused :release-state) c)
    (let ((mode (fn-hsr-field 0 c)))
      (mv :released
          (list (if (member-eq mode '(:refused :uncertain)) mode :idle)
                (fn-hsr-field 1 c) (fn-hsr-field 2 c) (fn-hsr-field 3 c)
                nil nil (fn-hsr-field 6 c) (fn-hsr-field 7 c) (fn-hsr-field 8 c))))))

; Logical carried invariant; never evaluated by an I/O guard.
(defun fn-hsr-io-invariantp (c)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-hsr-io-shapep c)
       (implies (equal (fn-hsr-field 0 c) :idle)
                (and (equal (fn-hsr-field 5 c) nil) (not (fn-hsr-field 8 c))))
       (implies (equal (fn-hsr-field 0 c) :observed)
                (and (natp (fn-hsr-field 5 c)) (not (fn-hsr-field 8 c))))
       (if (equal (fn-hsr-field 0 c) :waiting)
           (let ((r (fn-hsr-field 4 c)))
             (and (equal (fn-hsr-field 0 r) :read-page)
                  (equal (fn-hsr-field 1 r) (fn-hsr-field 1 c))
                  (equal (fn-hsr-field 2 r) (fn-hsr-field 2 c))
                  (natp (fn-hsr-field 3 r))
                  (equal (+ 1 (fn-hsr-field 3 r)) (fn-hsr-field 3 c))
                  (member-eq (fn-hsr-field 4 r) '(:directory :table :data))
                  (natp (fn-hsr-field 5 r))
                  (equal (fn-hsr-field 6 r) (* 16384 (fn-hsr-field 5 r)))
                  (equal (fn-hsr-field 7 r) 16384)
                  (natp (fn-hsr-field 8 r))
                  (equal (fn-hsr-field 5 c) nil)))
         (not (fn-hsr-field 4 c)))))

(defthm fn-hsr-io-begin-establishes-invariant
  (implies (and (natp ticket) (natp epoch))
           (fn-hsr-io-invariantp (fn-hsr-io-begin ticket epoch capture lease))))

(defthm fn-hsr-io-request-preserves-invariant
  (implies (fn-hsr-io-invariantp c)
           (fn-hsr-io-invariantp (mv-nth 2 (fn-hsr-io-request phase physical logical c))))
  :hints (("Goal" :in-theory (enable fn-hsr-io-request fn-hsr-io-invariantp fn-hsr-io-shapep fn-hsr-widthp))))

(defthm fn-hsr-io-complete-preserves-invariant
  (implies (fn-hsr-io-invariantp c)
           (fn-hsr-io-invariantp
            (mv-nth 1 (fn-hsr-io-complete request discovery-id count status c))))
  :hints (("Goal" :in-theory (enable fn-hsr-io-complete fn-hsr-io-invariantp fn-hsr-io-shapep))))

(defthm fn-hsr-io-cancel-preserves-invariant
  (implies (fn-hsr-io-invariantp c)
           (fn-hsr-io-invariantp (mv-nth 1 (fn-hsr-io-cancel c))))
  :hints (("Goal" :in-theory (enable fn-hsr-io-cancel fn-hsr-io-invariantp fn-hsr-io-shapep))))

(defthm fn-hsr-io-release-preserves-invariant
  (implies (fn-hsr-io-invariantp c)
           (fn-hsr-io-invariantp (mv-nth 1 (fn-hsr-io-release discovery-id c))))
  :hints (("Goal" :in-theory (enable fn-hsr-io-release fn-hsr-io-invariantp fn-hsr-io-shapep))))

(defun fn-hsr-io-joined-failure (request outcome c)
  ; The native exception path has completed/unwound and settled its own token;
  ; no vector was handed off. A refusal before issue differs from uncertain I/O.
  (declare (xargs :guard t))
  (if (not (and (fn-hsr-io-shapep c) (equal (fn-hsr-field 0 c) :waiting)
                (equal request (fn-hsr-field 4 c))
                (member-eq outcome '(:refused :uncertain))))
      (mv '(:refused :stale-join) c)
    (mv (list outcome :read-joined)
        (list outcome (fn-hsr-field 1 c) (fn-hsr-field 2 c) (fn-hsr-field 3 c)
              nil nil (fn-hsr-field 6 c) (fn-hsr-field 7 c) (fn-hsr-field 8 c)))))

(defthm fn-hsr-io-joined-failure-preserves-invariant
  (implies (fn-hsr-io-invariantp c)
           (fn-hsr-io-invariantp (mv-nth 1 (fn-hsr-io-joined-failure request outcome c))))
  :hints (("Goal" :in-theory (enable fn-hsr-io-joined-failure fn-hsr-io-invariantp fn-hsr-io-shapep))))

(defthm fn-hsr-io-cancel-preserves-outstanding-ownership
  (let ((next (mv-nth 1 (fn-hsr-io-cancel c))))
    (and (equal (fn-hsr-field 4 next) (fn-hsr-field 4 c))
         (equal (fn-hsr-field 5 next) (fn-hsr-field 5 c))
         (implies (equal (fn-hsr-field 0 c) :uncertain)
                  (equal (fn-hsr-field 0 next) :uncertain))))
  :hints (("Goal" :in-theory (e/d (fn-hsr-io-cancel) (fn-hsr-io-shapep)))))

(defthm fn-hsr-io-stale-completion-cannot-advance
  (implies (not (equal request (fn-hsr-field 4 c)))
           (equal (mv-nth 1 (fn-hsr-io-complete request discovery-id count status c)) c))
  :hints (("Goal" :in-theory (e/d (fn-hsr-io-complete) (fn-hsr-io-shapep)))))

(defthm fn-hsr-io-release-cannot-reuse-pending-or-faulted-state
  (let ((next (mv-nth 1 (fn-hsr-io-release discovery-id c))))
    (and (implies (equal (fn-hsr-field 0 c) :waiting) (equal next c))
         (implies (member-eq (fn-hsr-field 0 c) '(:refused :uncertain))
                  (equal (fn-hsr-field 0 next) (fn-hsr-field 0 c)))))
  :hints (("Goal" :in-theory (e/d (fn-hsr-io-release) (fn-hsr-io-shapep)))))

; One actual read/consume/release cycle fences an otherwise identical next read.
; The physical owner supplies a fresh natural DISCOVERY-ID per successful read.
(defthm fn-hsr-io-cycle-fences-old-completion
  (implies (and (fn-hsr-io-invariantp c) (equal (fn-hsr-field 0 c) :idle)
                (member-eq phase '(:directory :table :data))
                (natp physical) (natp logical) (natp discovery-id))
           (let* ((issued (fn-hsr-io-request phase physical logical c))
                  (old-request (mv-nth 1 issued))
                  (observed (mv-nth 1 (fn-hsr-io-complete old-request discovery-id 16384 :read-ok
                                                         (mv-nth 2 issued))))
                  (released (mv-nth 1 (fn-hsr-io-release discovery-id observed)))
                  (again (fn-hsr-io-request phase physical logical released)))
             (and (equal (mv-nth 0 issued) :need-read)
                  (equal (fn-hsr-field 0 observed) :observed)
                  (equal (fn-hsr-field 5 observed) discovery-id)
                  (equal (mv-nth 0 again) :need-read)
                  (equal (fn-hsr-field 3 (mv-nth 1 again)) (+ 1 (fn-hsr-field 3 old-request)))
                  (not (equal (mv-nth 1 again) old-request))
                  (equal (mv-nth 1 (fn-hsr-io-complete old-request discovery-id 16384 :read-ok
                                                      (mv-nth 2 again)))
                         (mv-nth 2 again)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-hsr-io-invariantp fn-hsr-io-shapep fn-hsr-io-request
                              fn-hsr-io-complete fn-hsr-io-release))))

(defun fn-hsr-io-identities (c)
  (declare (xargs :guard t))
  (list (fn-hsr-field 1 c) (fn-hsr-field 2 c)
        (fn-hsr-field 6 c) (fn-hsr-field 7 c)))

(defthm fn-hsr-io-transitions-preserve-identities
  (and (equal (fn-hsr-io-identities (mv-nth 2 (fn-hsr-io-request phase physical logical c)))
              (fn-hsr-io-identities c))
       (equal (fn-hsr-io-identities
               (mv-nth 1 (fn-hsr-io-complete request discovery-id count status c)))
              (fn-hsr-io-identities c))
       (equal (fn-hsr-io-identities (mv-nth 1 (fn-hsr-io-cancel c)))
              (fn-hsr-io-identities c))
       (equal (fn-hsr-io-identities (mv-nth 1 (fn-hsr-io-release discovery-id c)))
              (fn-hsr-io-identities c))
       (equal (fn-hsr-io-identities (mv-nth 1 (fn-hsr-io-joined-failure request outcome c)))
              (fn-hsr-io-identities c)))
  :hints (("Goal" :in-theory (e/d (fn-hsr-io-identities fn-hsr-io-request fn-hsr-io-complete
                                  fn-hsr-io-cancel fn-hsr-io-release fn-hsr-io-joined-failure)
                                 (fn-hsr-io-shapep)))))

(defthm fn-hsr-io-short-read-stays-uncertain-through-cleanup
  (implies (and (fn-hsr-io-shapep c) (equal (fn-hsr-field 0 c) :waiting)
                (natp discovery-id)
                (or (not (equal status :read-ok)) (not (equal count 16384))))
           (let* ((next (mv-nth 1 (fn-hsr-io-complete (fn-hsr-field 4 c)
                                                      discovery-id count status c)))
                  (released (mv-nth 1 (fn-hsr-io-release discovery-id next)))
                  (cancelled (mv-nth 1 (fn-hsr-io-cancel released))))
             (and (equal (fn-hsr-field 0 next) :uncertain)
                  (equal (fn-hsr-field 5 next) discovery-id)
                  (equal (fn-hsr-field 0 released) :uncertain)
                  (equal (fn-hsr-field 5 released) nil)
                  (equal (fn-hsr-field 0 cancelled) :uncertain)
                  (equal (mv-nth 0 (fn-hsr-io-request phase physical logical cancelled))
                         '(:refused :request-state)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-hsr-io-shapep fn-hsr-io-complete
                              fn-hsr-io-release fn-hsr-io-cancel fn-hsr-io-request))))

(in-theory (disable fn-hsr-io-shapep fn-hsr-io-begin fn-hsr-io-request fn-hsr-io-complete
                    fn-hsr-io-cancel fn-hsr-io-release fn-hsr-io-invariantp
                    fn-hsr-io-joined-failure fn-hsr-io-identities))
