; Bounded namespace and accounting for native FNWF/FNRJ journals.
;
; Recovery feeds each observed record to this machine once.  Thereafter the
; carried frontier owns the next name, count, aggregate size, initialization
; state, and resolution headroom.  The host only observes names and byte
; lengths and executes an authorized immutable publication operation.
(in-package "ACL2")
(include-book "journal-publish")
(include-book "byte-store-txn-name")
(include-book "frame")

(defconst *fn-aj-max-records* 4096)
(defconst *fn-aj-workflow-max-aggregate* 16777216)
(defconst *fn-aj-receipt-max-aggregate* 67108864)

(defun fn-aj-domainp (domain)
  (member-equal domain '(:workflow :receipt)))

(defun fn-aj-max-record-length (domain)
  (+ *fn-frame-overhead-octets*
     (if (equal domain :workflow)
         *fn-frame-max-workflow-payload*
       *fn-frame-max-receipt-payload*)))

(defun fn-aj-max-aggregate (domain)
  (if (equal domain :workflow)
      *fn-aj-workflow-max-aggregate*
    *fn-aj-receipt-max-aggregate*))

(defun fn-aj-suffix (domain)
  (if (equal domain :workflow) '(#\. #\w #\f) '(#\. #\r #\j)))

(defun fn-aj-record-name-chars (domain sequence)
  (append (fn-bs-txn-digits sequence) (fn-aj-suffix domain)))

(defun fn-aj-record-name (domain sequence)
  (declare (xargs :guard t :verify-guards nil))
  (coerce (fn-aj-record-name-chars domain sequence) 'string))

(defun fn-aj-state (domain next aggregate initializedp)
  (list domain (nfix next) (nfix aggregate) (if initializedp t nil)))

(defun fn-aj-domain (s) (if (consp s) (car s) nil))
(defun fn-aj-next (s) (if (consp (cdr s)) (car (cdr s)) 0))
(defun fn-aj-aggregate (s)
  (if (consp (cdr (cdr s))) (car (cdr (cdr s))) 0))
(defun fn-aj-initializedp (s)
  (if (consp (cdr (cdr (cdr s))))
      (car (cdr (cdr (cdr s)))) nil))

(defun fn-aj-statep (s)
  (and (true-listp s)
       (equal (len s) 4)
       (fn-aj-domainp (fn-aj-domain s))
       (natp (fn-aj-next s))
       (<= (fn-aj-next s) *fn-aj-max-records*)
       (natp (fn-aj-aggregate s))
       (<= (fn-aj-aggregate s)
           (fn-aj-max-aggregate (fn-aj-domain s)))
       (booleanp (fn-aj-initializedp s))
       (equal (fn-aj-initializedp s)
              (if (zp (fn-aj-next s)) nil t))))

(defun fn-aj-initial (domain)
  (if (fn-aj-domainp domain)
      (fn-aj-state domain 0 0 nil)
    :fault))

(defun fn-aj-kind-allowedp (s kind)
  (if (fn-aj-initializedp s)
      (not (equal kind :config))
    (equal kind :config)))

(defun fn-aj-advance (s frame-length)
  (fn-aj-state (fn-aj-domain s)
               (+ 1 (fn-aj-next s))
               (+ (fn-aj-aggregate s) (nfix frame-length))
               t))

(defun fn-aj-fits-p (s frame-length reserve-resolutionp)
  (let* ((domain (fn-aj-domain s))
         (reserve-slots (if reserve-resolutionp 2 1))
         (reserve-bytes (if reserve-resolutionp
                            (fn-aj-max-record-length domain) 0)))
    (and (natp frame-length)
         (<= frame-length (fn-aj-max-record-length domain))
         (<= (+ (fn-aj-next s) reserve-slots) *fn-aj-max-records*)
         (<= (+ (fn-aj-aggregate s) frame-length reserve-bytes)
             (fn-aj-max-aggregate domain)))))

(defun fn-aj-recover-record (s observed-name frame-length kind)
  ; OBSERVED-NAME and FRAME-LENGTH are filesystem observations.  ACL2 owns
  ; their interpretation and advances the bounded frontier only on an exact
  ; next-name/configuration match.
  (if (and (fn-aj-statep s)
           (stringp observed-name)
           (equal observed-name
                  (fn-aj-record-name (fn-aj-domain s)
                                     (fn-aj-next s)))
           (fn-aj-kind-allowedp s kind)
           (fn-aj-fits-p s frame-length nil))
      (fn-aj-advance s frame-length)
    :fault))

; (:ok final-name publication successor) is a capability issued only after
; the caller reports ownership of the journal lock and absence of ACL2's exact
; next name.  The raw executor receives the embedded publication state and
; cannot create authority on its own.
(defun fn-aj-authorize (s kind frame-length reserve-resolutionp
                              lock-ownedp next-absentp)
  (if (and (fn-aj-statep s)
           (fn-aj-kind-allowedp s kind)
           (fn-aj-fits-p s frame-length reserve-resolutionp)
           (equal lock-ownedp t)
           (equal next-absentp t))
      (list :ok
            (fn-aj-record-name (fn-aj-domain s) (fn-aj-next s))
            (fn-jpub-initial t)
            (fn-aj-advance s frame-length))
    (list :refused :journal-admission)))

(defun fn-aj-operationp (operation)
  (and (true-listp operation)
       (equal (len operation) 4)
       (equal (car operation) :ok)
       (stringp (car (cdr operation)))
       (fn-jpub-statep (car (cdr (cdr operation))))
       (equal (fn-jpub-next-action (car (cdr (cdr operation)))) :stage)
       (fn-aj-statep (car (cdr (cdr (cdr operation)))))))

(defun fn-aj-operation-name (operation) (car (cdr operation)))
(defun fn-aj-operation-publication (operation) (car (cdr (cdr operation))))
(defun fn-aj-operation-successor (operation)
  (car (cdr (cdr (cdr operation)))))

(defthm fn-aj-statep-of-initial
  (implies (fn-aj-domainp domain)
           (fn-aj-statep (fn-aj-initial domain))))

(defthm fn-aj-authorize-produces-operation
  (implies (equal (car (fn-aj-authorize s kind frame-length reserve
                                        lock-ownedp next-absentp))
                  :ok)
           (fn-aj-operationp
            (fn-aj-authorize s kind frame-length reserve
                             lock-ownedp next-absentp))))

(defthm fn-aj-authorized-successor-advances-once
  (implies (equal (car (fn-aj-authorize s kind frame-length reserve
                                        lock-ownedp next-absentp))
                  :ok)
           (equal (fn-aj-next
                   (fn-aj-operation-successor
                    (fn-aj-authorize s kind frame-length reserve
                                     lock-ownedp next-absentp)))
                  (+ 1 (fn-aj-next s)))))

(deftheory fn-app-journal-vocabulary
  '(fn-aj-domainp fn-aj-max-record-length fn-aj-max-aggregate fn-aj-suffix
    fn-aj-record-name-chars fn-aj-record-name fn-aj-state fn-aj-domain
    fn-aj-next fn-aj-aggregate fn-aj-initializedp fn-aj-statep fn-aj-initial
    fn-aj-kind-allowedp fn-aj-advance fn-aj-fits-p fn-aj-recover-record
    fn-aj-authorize fn-aj-operationp fn-aj-operation-name
    fn-aj-operation-publication fn-aj-operation-successor))

