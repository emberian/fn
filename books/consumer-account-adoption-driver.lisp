; The operator's static/redeemed input continuation for account adoption.
; This state is never authentication authority. Only the actual typed durable
; C completion may publish its prepared account/config roots. Per-step CURRENT
; operation admission precedes these allocating constructors in the owner.
(in-package "ACL2")
(include-book "consumer-account-input")

; Fixed12, with borrowed immutable inputs and carried candidate annotations.
(defun fn-cadd-job (phase source candidate bindings static redeemed cursor
                         ordered orderedmeta selection begin-count)
 (declare (xargs :guard t))
 (list :account-adoption-job phase source candidate bindings static redeemed
       cursor ordered orderedmeta selection begin-count))

(defun fn-cadd-policy (config)
 (declare (xargs :guard t))
 (+ (if (fn-auth-config-requiredp config) 1 0)
    (if (fn-auth-config-protected-onlyp config) 2 0)
    (if (fn-auth-config-tls-availablep config) 4 0)))

(defun fn-cadd-begin (config bindings candidate redeemed source begin-count)
 (declare (xargs :guard t))
 (if (not (fn-cp-idp candidate)) '(:refused :candidate-identity)
  (list :yield
   (fn-cadd-job :static source candidate bindings (fn-auth-config-creds config)
                redeemed (fn-aic-initial (fn-cadd-policy config) bindings)
                nil nil nil begin-count))))

; Exact input-only work descriptor. The issuer reads the registered job and
; current owner source itself; an arbitrary caller-supplied descriptor is not
; a grant. Redeemed conversion is the existing ACL2 fn-auth-account-cred of
; this selected row, once, under its existing bounded row grammar.
(defun fn-cadd-work (job)
 (declare (xargs :guard t))
 (let ((phase (fn-cp-nth 1 job)) (source (fn-cp-nth 2 job)))
  (case phase
   (:static (if (consp (fn-cp-nth 5 job))
                (list :account-candidate-feed source :static (car (fn-cp-nth 5 job)))
              (list :account-candidate-transition source phase)))
   (:redeemed (if (consp (fn-cp-nth 6 job))
                  (list :account-candidate-feed source :redeemed (car (fn-cp-nth 6 job)))
                (list :account-candidate-transition source phase)))
   ((:insert-static :insert-redeemed)
    (list :account-candidate-tick source (fn-cp-nth 7 job)))
   (otherwise (list :account-candidate-transition source phase)))))

(defun fn-cadd-with (job phase static redeemed cursor ordered orderedmeta selection)
 (declare (xargs :guard t))
 (fn-cadd-job phase (fn-cp-nth 2 job) (fn-cp-nth 3 job) (fn-cp-nth 4 job)
              static redeemed cursor ordered orderedmeta selection (fn-cp-nth 11 job)))

; Eligibility and credential come from ONE actual selected redeemed-row
; producer in the ACL2 owner, never from native policy or a whole-table merge.
; The installed source relation must connect them to (car REDEEMED).
(defun fn-cadd-tick (job redeemed-credential eligiblep)
 (declare (xargs :guard t))
 (let ((phase (fn-cp-nth 1 job))
       (static (fn-cp-nth 5 job)) (redeemed (fn-cp-nth 6 job))
       (cursor (fn-cp-nth 7 job)))
  (case phase
   (:static
    (if (consp static)
        (let ((one (fn-aic-feed cursor (car static) 0)))
         (if (eq (fn-cp-nth 0 one) :yield)
             (list :yield (fn-cadd-with job :insert-static (cdr static) redeemed
                                       (fn-cp-nth 1 one) nil nil nil)) one))
      (list :yield (fn-cadd-with job :redeemed nil redeemed cursor nil nil nil))))
   (:redeemed
    (if (consp redeemed)
        (if eligiblep
            (let ((one (fn-aic-feed cursor redeemed-credential 1)))
             (if (eq (fn-cp-nth 0 one) :yield)
                 (list :yield (fn-cadd-with job :insert-redeemed nil (cdr redeemed)
                                           (fn-cp-nth 1 one) nil nil nil)) one))
          (list :yield (fn-cadd-with job :redeemed nil (cdr redeemed) cursor nil nil nil)))
      (list :prepared
       (fn-cadd-with job :ready nil nil cursor (fn-cp-nth 2 (fn-cp-nth 1 cursor))
                     (fn-cp-nth 3 (fn-cp-nth 1 cursor)) nil))))
   ((:insert-static :insert-redeemed)
    (let* ((one (fn-aic-tick cursor)) (word (fn-cp-nth 0 one)))
     (if (member-eq word '(:ready :yield))
         (list :yield
          (fn-cadd-with job
                       (if (eq word :ready)
                           (if (eq phase :insert-static) :static :redeemed) phase)
                       static redeemed (fn-cp-nth 1 one) nil nil nil)) one)))
   (:ready (list :prepared job))
   (:await-durable '(:refused :account-publication-pending))
   (:done (list :accepted job))
   (otherwise '(:refused :account-adoption-phase)))))

; Marker is interpreted by the typed CONFIGURATION producer. The old E
; fence recipe is never emitted to actual publication. C carries its own
; sequence/generation and does not manufacture an extra E row/count/frontier.
(defun fn-cadd-next (job cp identity-next next-txid keyring-generation
                        config-generation event-count)
 (declare (xargs :guard t))
 (if (not (eq (fn-cp-nth 1 job) :ready))
     '(:refused :candidate-not-prepared)
  (let* ((a (fn-cp-nth 6 cp)) (p (fn-cp-nth 5 a))
         (candidate (fn-cp-nth 3 job))
         (selection
          (if (and p (not (equal candidate (fn-cp-nth 1 p))))
              ; A lost operator continuation is explicitly discarded as a
              ; funded durable transition; old admitted authority stays.
              (list :operation
               (list :authority-discard (fn-cp-nth 1 p) (fn-cp-nth 1 a)) nil)
            (fn-cad-authority-operation cp candidate (fn-cp-nth 8 job)
                                       (fn-cp-nth 10 (fn-cp-nth 1 (fn-cp-nth 7 job))) next-txid)))
         (op (fn-cp-nth 1 selection)))
   (if (and (eq (fn-cp-nth 0 selection) :operation)
            (eq (fn-cp-nth 0 op) :authority-fence))
       (list :configure
        (list :account-authority-adopt candidate config-generation (fn-cp-nth 1 a)
              (fn-cp-nth 11 job) event-count (fn-cp-nth 3 p) (fn-cp-nth 7 p)))
     (let ((one (fn-cad-authority-event identity-next next-txid keyring-generation selection)))
      (if (eq (fn-cp-nth 0 one) :ok)
          (list :publish (fn-cp-nth 1 one) (fn-cp-nth 2 one)) one))))))

; Called inside the SAME once-called durable owner collector, not after a
; transport answer. Installation of the saved decision and advancement of its
; candidate cursor are one atomic owner publication. This pure helper itself
; cannot establish the DURABLE observation/selected-operation correspondence.
(defun fn-cadd-published (job selection root predecessor-count)
 (declare (xargs :guard t))
 (if (not (fn-cp-uintp predecessor-count))
     '(:recovery-required :account-event-count)
  (if (eq (fn-cp-nth 0 selection) :configure)
     (if root
         (list :accepted
          (fn-cadd-with job :done nil nil (fn-cp-nth 7 job)
                        (fn-cp-nth 8 job) (fn-cp-nth 9 job) nil))
       '(:recovery-required :account-publication-root))
  (if (eq (fn-cp-nth 0 selection) :publish)
      (let* ((consume (fn-cp-nth 2 selection)) (ordered (fn-cp-nth 8 job))
             (event (fn-cp-nth 1 selection))
             (begin-count
              (if (eq (fn-cp-nth 0 (fn-cp-nth 4 event)) :authority-begin)
                  predecessor-count (fn-cp-nth 11 job))))
       (list :yield
        (fn-cadd-job :ready (fn-cp-nth 2 job) (fn-cp-nth 3 job) (fn-cp-nth 4 job)
                     nil nil (fn-cp-nth 7 job)
                     (if consume (if (consp ordered) (cdr ordered) nil) ordered)
                     (if consume (fn-cp-nth 2 (fn-cp-nth 9 job)) (fn-cp-nth 9 job))
                     nil begin-count)))
    '(:recovery-required :account-publication-selection)))))

(in-theory (disable fn-cadd-job fn-cadd-policy fn-cadd-begin fn-cadd-work
                    fn-cadd-with fn-cadd-tick fn-cadd-next fn-cadd-published))
