; Internal CURRENT outgoing job over the SAME physical pool. The registered
; parent derives episode/storage/demand; no host job/claim setter is exported.
; Installed outgoing family and genuine storage factory are absent today.
(in-package "ACL2")
(include-book "page-read-ledger")
(defun fn-rog-widthp (x n)
 (declare (xargs :guard (natp n)))
 (if (zp n) (null x)
  (and (consp x) (fn-rog-widthp (cdr x) (1- n)))))
(defun fn-rog-episodep (x)
 (declare (xargs :guard t))
 (and (fn-rog-widthp x 3) (eq (fn-prl-nth 0 x) :receiver-response)
      (fn-prl-nth 1 x) (natp (fn-prl-nth 2 x))))
(defun fn-rog-window-tokenp (x)
 (declare (xargs :guard t))
 (and (fn-rog-widthp x 5) (eq (fn-prl-nth 0 x) :reader-output-window)
      (fn-rog-episodep (fn-prl-nth 1 x))
      (natp (fn-prl-nth 2 x)) (natp (fn-prl-nth 3 x)) (fn-prl-nth 4 x)))
(defun fn-rog-jobp (x)
 (declare (xargs :guard t))
 (and (fn-rog-widthp x 12) (eq (fn-prl-nth 0 x) :reader-output-job)
      (fn-rog-window-tokenp (fn-prl-nth 4 x))
      (equal (fn-prl-nth 1 x) (fn-prl-nth 1 (fn-prl-nth 4 x)))
      (equal (fn-prl-nth 2 x) (fn-prl-nth 2 (fn-prl-nth 4 x)))
      (equal (fn-prl-nth 6 x) (fn-prl-nth 4 (fn-prl-nth 4 x)))
      (fn-rog-widthp (fn-prl-nth 5 x) 4)
      (equal (fn-prl-nth 0 (fn-prl-nth 5 x)) (fn-prl-nth 4 x))
      (fn-prs-vectorp (fn-prl-nth 1 (fn-prl-nth 5 x)))
      (member-eq (fn-prl-nth 2 (fn-prl-nth 5 x)) '(:active :cancelled :released))
      (equal (fn-prl-nth 3 (fn-prl-nth 5 x)) (fn-prl-nth 3 (fn-prl-nth 4 x)))
      (natp (fn-prl-nth 7 x)) (natp (fn-prl-nth 8 x))
      (<= (fn-prl-nth 8 x) (fn-prl-nth 7 x))))
; Demand is projected by the actual registered family, not passed by native.
; PRS spends its actual OLD NEXT once. The row resides in the query context;
; the legacy ledger binding list is neither scanned nor copied here.
(defun fn-rog-reserve-current (episode serial storage demand job ledger)
 (declare (xargs :guard t))
 (cond
  ((and (fn-rog-jobp job) (not (eq (fn-prl-nth 3 job) :returned)))
   (mv :busy job ledger))
  ((not (and (fn-rog-episodep episode) (natp serial) storage
             (or (and (null job) (equal serial 0))
                 (and (fn-rog-jobp job) (eq (fn-prl-nth 3 job) :returned)
                      (equal episode (fn-prl-nth 1 job))
                      (equal serial (+ 1 (fn-prl-nth 2 job)))))
             (fn-prs-vectorp demand) (equal (fn-prl-nth 4 demand) 1)))
   (mv :unavailable job ledger))
  (t
   (mv-let (word next charged)
    (fn-prs-issue (fn-prl-nth 0 ledger) (fn-prl-baseline ledger)
                 '(0 0 0 0 0) (fn-prl-nth 1 ledger) (fn-prl-nth 2 ledger)
                 (fn-prl-nth 4 (fn-prl-nth 0 ledger)) demand)
    (if (not (eq word :admitted)) (mv word job ledger)
     (let ((token (list :reader-output-window episode serial (fn-prl-nth 2 ledger) storage)))
      (mv :reserved
       (list :reader-output-job episode serial :reserved token
             (list token demand :active (fn-prl-nth 2 ledger))
             storage 0 0 nil nil nil)
       (fn-prl-build (fn-prl-nth 0 ledger) charged next
                     (fn-prl-nth 3 ledger) (fn-prl-baseline ledger)))))))))
(defun fn-rog-prepare-current (token job)
 (declare (xargs :guard t))
 (cond
  ((not (and (fn-rog-jobp job) (equal token (fn-prl-nth 4 job)))) (mv :stale job))
  ((eq (fn-prl-nth 3 job) :constructing) (mv :already-prepared job))
  ((not (eq (fn-prl-nth 3 job) :reserved)) (mv :retained job))
  (t (mv :constructing
      (list (fn-prl-nth 0 job) (fn-prl-nth 1 job) (fn-prl-nth 2 job) :constructing
            token (fn-prl-nth 5 job) (fn-prl-nth 6 job)
            (fn-prl-nth 7 job) (fn-prl-nth 8 job) (fn-prl-nth 9 job)
            (fn-prl-nth 10 job) (fn-prl-nth 11 job))))))
; INTERNAL source factory completion. WINDOW/TOTAL denote this exact bounded
; window, never LEN of the whole response. CURRENT parent persists intent
; before actual storage installation; escape retains the claim.
(defun fn-rog-install-current (token total window-plan job)
 (declare (xargs :guard t))
 (if (not (and (fn-rog-jobp job) (equal token (fn-prl-nth 4 job))
               (eq (fn-prl-nth 3 job) :constructing) (natp total)))
  (mv :unavailable job)
  (mv :installed
   (list (fn-prl-nth 0 job) (fn-prl-nth 1 job) (fn-prl-nth 2 job) :installed
         token (fn-prl-nth 5 job) (fn-prl-nth 6 job) total 0 window-plan nil nil))))
; Actual transport reports count/outcome only. Core owns partial-write offset.
; :drained is output progress, never alias settlement or a refund.
(defun fn-rog-observe-current (token word count job)
 (declare (xargs :guard t))
 (cond
  ((not (and (fn-rog-jobp job) (equal token (fn-prl-nth 4 job))))
   (mv :stale nil job))
  ((not (member-eq (fn-prl-nth 3 job) '(:installed :writing :wait)))
   (mv :retained (fn-prl-nth 8 job) job))
  ((not (and (natp count) (<= count (- (fn-prl-nth 7 job) (fn-prl-nth 8 job)))
             (or (eq word :written)
                 (and (member-eq word '(:input :output :cancelled :failed)) (equal count 0)))))
   (mv :invalid-io-observation (fn-prl-nth 8 job) job))
  (t
   (let* ((offset (+ (fn-prl-nth 8 job) count))
          (phase (cond ((member-eq word '(:cancelled :failed)) :cancelled)
                       ((and (eq word :written) (equal offset (fn-prl-nth 7 job))) :drained)
                       ((or (member-eq word '(:input :output)) (equal count 0)) :wait)
                       (t :writing)))
          (next (list (fn-prl-nth 0 job) (fn-prl-nth 1 job) (fn-prl-nth 2 job) phase
                      (fn-prl-nth 4 job) (fn-prl-nth 5 job) (fn-prl-nth 6 job)
                      (fn-prl-nth 7 job) offset (fn-prl-nth 9 job) word nil)))
    (mv phase offset next)))))
; The real selected-family publication/storage and registered alias epilogue
; do not exist yet. Public source gates must refuse before constructors.
(defun fn-rog-outgoing-source-status ()
 (declare (xargs :guard t)) :outgoing-source-unavailable)

(defthm fn-rog-observe-retains-source-storage-and-charge
 (let ((next (mv-nth 2 (fn-rog-observe-current token word count job))))
  (and (equal (fn-prl-nth 1 next) (fn-prl-nth 1 job))
       (equal (fn-prl-nth 2 next) (fn-prl-nth 2 job))
       (equal (fn-prl-nth 4 next) (fn-prl-nth 4 job))
       (equal (fn-prl-nth 5 next) (fn-prl-nth 5 job))
       (equal (fn-prl-nth 6 next) (fn-prl-nth 6 job))
       (equal (fn-prl-nth 9 next) (fn-prl-nth 9 job))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
   :in-theory (e/d (fn-rog-observe-current fn-prl-nth)
                    (fn-rog-jobp fn-rog-window-tokenp)))))
(defthm fn-rog-observe-preserves-bounded-window-cursor
 (implies (fn-rog-jobp job)
   (fn-rog-jobp (mv-nth 2 (fn-rog-observe-current token word count job))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
   :in-theory (e/d (fn-rog-observe-current fn-rog-jobp fn-rog-widthp fn-prl-nth)
                    (fn-rog-window-tokenp fn-prs-vectorp)))))

; Actual operation issuer uses this gate, not the algebra-only reserve kernel.
; A real epilogue must establish the released claim/receipt relation. Mere
; :returned, :drained, or a host cancellation report never authorizes reuse.
(defun fn-rog-successor-ready-p (job)
 (declare (xargs :guard t))
 (and (fn-rog-jobp job)
      (eq (fn-prl-nth 3 job) :returned)
      (eq (fn-prl-nth 2 (fn-prl-nth 5 job)) :released)
      (equal (fn-prl-nth 1 (fn-prl-nth 5 job)) '(0 0 0 0 0))
      (consp (fn-prl-nth 11 job))))
(defun fn-rog-reserve-issued-current (episode serial storage demand job ledger)
 (declare (xargs :guard t))
 (if (and job (not (fn-rog-successor-ready-p job)))
     (mv :busy job ledger)
  (fn-rog-reserve-current episode serial storage demand job ledger)))
