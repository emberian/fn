; Actual operation selector for the paired E preparation / sole typed C commit.
; The registered fixed12 job remains nonauthorizing. Its slot10 retains the
; SAME configuration preparation from the saved full7/full8 durable decision.
(in-package "ACL2")
(include-book "consumer-account-adoption-driver")
(include-book "consumer-account-config-commit")

(defun fn-catd-preparation (job)
 (declare (xargs :guard t))
 (let ((saved (fn-cp-nth 10 job)))
  (and (eq (fn-cp-nth 0 saved) :account-preparation) (fn-cp-nth 1 saved))))

; No scanned account/table merge here: one selected credential is already
; at the candidate cursor, and its exact intent comes from the paired trie.
; The maintained input/source relation and operation admission are owed by
; the actual caller; a supplied job is not an allocation/source grant.
(defun fn-catd-next (job cp identity-next next-txid keyring-generation
                         config-generation event-count)
 (declare (xargs :guard t))
 (if (not (eq (fn-cp-nth 1 job) :ready)) '(:refused :candidate-not-prepared)
  (let* ((a (fn-cp-nth 6 cp)) (p (fn-cp-nth 5 a))
         (ap (fn-cp-nth 5 p)) (b (fn-catd-preparation job))
         (candidate (fn-cp-nth 3 job)) (base (fn-cp-nth 1 a))
         (bindingp (and p (equal candidate (fn-cp-nth 1 p))
                        (eq (fn-cp-nth 4 b) :binding)))
         (tombstonep (eq (fn-cp-nth 6 b) :tombstone))
         (intent (and bindingp (not tombstonep)
                      (fn-cai-get-octets (fn-cp-nth 5 b)
                        (fn-cp-nth 2 (fn-cp-nth 7 job))))))
   (cond
    (bindingp
     (let* ((op (fn-cab-operation candidate base (fn-cp-nth 5 b)
                                  (if tombstonep 2 (fn-cp-nth 1 intent))
                                  (if tombstonep 1 (fn-cp-nth 2 intent))
                                  (if tombstonep (make-list 32 :initial-element 0)
                                    (fn-cp-nth 3 intent))))
            (event (list :consumer-authority identity-next next-txid keyring-generation op)))
      (if (fn-cab-eventp event)
          (list :publish event (not tombstonep))
        '(:refused :candidate-binding-intent))))
    ((and p (equal candidate (fn-cp-nth 1 p))
          (eq (fn-cp-nth 1 ap) :ready) (eq (fn-cp-nth 4 b) :ready))
     (list :configure
      (fn-cacm-marker candidate config-generation base (fn-cp-nth 11 job)
                      event-count (fn-cp-nth 3 p) (fn-cp-nth 7 p))))
    (t
     (let* ((selection
             (cond
              ((and p (not (equal candidate (fn-cp-nth 1 p))))
               (list :operation (list :authority-discard (fn-cp-nth 1 p) base) nil))
              ((and p (eq (fn-cp-nth 1 ap) :ready))
               (if (member-eq (fn-cp-nth 4 b) '(:bindings-reverse :scan :restore))
                   (list :operation (list :authority-prepare candidate base) nil)
                 '(:refused :configuration-preparation-unavailable)))
              (t (fn-cad-authority-operation cp candidate (fn-cp-nth 8 job)
                   (fn-cp-nth 10 (fn-cp-nth 1 (fn-cp-nth 7 job))) next-txid))))
            (one (fn-cad-authority-event identity-next next-txid keyring-generation selection)))
      (if (eq (fn-cp-nth 0 one) :ok)
          ; A row is consumed only after its corresponding binding is durable.
          (list :publish (fn-cp-nth 1 one) nil) one)))))))

; This is called exactly once inside the owner durable collector with the
; saved decision. E complete is full7, typed C complete is full8. No caller
; can turn a reply/socket acknowledgement into a persisted stage here.
(defun fn-catd-published (job selection full)
 (declare (xargs :guard t))
 (if (not (eq (fn-cp-nth 0 full) :ok)) '(:recovery-required :account-decision)
  (case (fn-cp-nth 0 selection)
   (:configure
    (if (fn-cp-nth 2 full)
        (list :accepted
         (fn-cadd-with job :done nil nil (fn-cp-nth 7 job)
                       (fn-cp-nth 8 job) (fn-cp-nth 9 job) nil))
      '(:recovery-required :account-publication-root)))
   (:publish
    (let* ((event (fn-cp-nth 1 selection)) (op (fn-cp-nth 4 event))
           (consume (and (eq (fn-cp-nth 0 op) :authority-binding)
                         (fn-cp-nth 2 selection)))
           (ordered (fn-cp-nth 8 job)))
     (list :yield
      (fn-cadd-job :ready (fn-cp-nth 2 job) (fn-cp-nth 3 job) (fn-cp-nth 4 job)
                   nil nil (fn-cp-nth 7 job)
                   (if consume (if (consp ordered) (cdr ordered) nil) ordered)
                   (if consume (fn-cp-nth 2 (fn-cp-nth 9 job)) (fn-cp-nth 9 job))
                   (list :account-preparation (fn-cp-nth 6 full))
                   (if (eq (fn-cp-nth 0 op) :authority-begin)
                       (fn-cp-nth 1 event) (fn-cp-nth 11 job))))))
   (otherwise '(:recovery-required :account-publication-selection)))))

(in-theory (disable fn-catd-preparation fn-catd-next fn-catd-published))
