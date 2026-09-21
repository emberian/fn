; Durable identity and immutable publication authority for native BP receive
; evidence.
;
; The native host owns one spool lock for the whole journal.  At startup it
; barriers the dedicated evidence directory, sorts every observed entry name,
; and hands the complete bounded observation to fn-bpn-evidence-recover.  This
; machine accepts only the exact ACL2-rendered contiguous namespace.  Legacy
; root-level passive-<transfer>.{wire,adu,refused,uncertain} files are retained
; but are not members of this namespace and never allocate a new identity.
;
; Each identity's .wire file is the allocation record: it contains the exact
; transfer octets and is published without replacement.  A durable wire
; consumes the identity even if its verdict sidecar is absent.  Consequently a
; crash or a refused sidecar publication cannot make a later session overwrite
; retained transfer evidence whose TCPCL transfer ID happened to be the same.
(in-package "ACL2")
(include-book "journal-publish")
(include-book "byte-store-txn-name")

(defconst *fn-bpn-evidence-max-records* 4096)

(defconst *fn-bpn-evidence-directory-name* "receive-evidence")

(defun fn-bpn-evidence-max-entries ()
  (* 2 *fn-bpn-evidence-max-records*))

(defun fn-bpn-evidence-kindp (kind)
  (member-equal kind '(:wire :adu :refused :uncertain)))

(defun fn-bpn-evidence-outcomep (outcome)
  (member-equal outcome '(:accepted :refused :uncertain)))

(defun fn-bpn-evidence-suffix (kind)
  (case kind
    (:wire '(#\. #\w #\i #\r #\e))
    (:adu '(#\. #\a #\d #\u))
    (:refused '(#\. #\r #\e #\f #\u #\s #\e #\d))
    (:uncertain '(#\. #\u #\n #\c #\e #\r #\t #\a #\i #\n))
    (otherwise nil)))

(defun fn-bpn-evidence-name-chars (sequence kind)
  (append (fn-bs-txn-digits sequence)
          (fn-bpn-evidence-suffix kind)))

(defun fn-bpn-evidence-name (sequence kind)
  (declare (xargs :guard t :verify-guards nil))
  (coerce (fn-bpn-evidence-name-chars sequence kind) 'string))

(defun fn-bpn-evidence-result-kind (outcome)
  (case outcome
    (:accepted :adu)
    (:refused :refused)
    (otherwise :uncertain)))

(defun fn-bpn-evidence-state (next)
  (list :ready (nfix next)))

(defun fn-bpn-evidence-next (st)
  (if (and (consp st) (consp (cdr st)))
      (car (cdr st))
    0))

(defun fn-bpn-evidence-next-wire-name (st)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpn-evidence-name (fn-bpn-evidence-next st) :wire))

(defun fn-bpn-evidence-next-result-name (st outcome)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpn-evidence-name (fn-bpn-evidence-next st)
                        (fn-bpn-evidence-result-kind outcome)))

(defun fn-bpn-evidence-statep (st)
  (and (true-listp st)
       (equal (len st) 2)
       (equal (car st) :ready)
       (natp (fn-bpn-evidence-next st))
       (<= (fn-bpn-evidence-next st) *fn-bpn-evidence-max-records*)))

(defun fn-bpn-evidence-entry-name (entry)
  (if (consp entry) (car entry) nil))

(defun fn-bpn-evidence-entry-kind (entry)
  (if (consp entry) (cdr entry) nil))

(defun fn-bpn-evidence-regular-namep (entry name)
  (and (stringp (fn-bpn-evidence-entry-name entry))
       (equal (fn-bpn-evidence-entry-name entry) name)
       (equal (fn-bpn-evidence-entry-kind entry) :regular)))

; Names are sorted by the host only to bound this fold's work.  The fold still
; checks every exact name and ordering relation, so sorting grants no authority.
; For one identity the lexical order is optional verdict sidecar, then .wire.
(defun fn-bpn-evidence-recover-sorted (entries sequence)
  (declare (xargs :guard t
                  :verify-guards nil
                  :measure (len entries)))
  (if (atom entries)
      (fn-bpn-evidence-state sequence)
    (if (not (< sequence *fn-bpn-evidence-max-records*))
        (list :fault :capacity)
      (let* ((entry (car entries))
             (wire (fn-bpn-evidence-name sequence :wire))
             (adu (fn-bpn-evidence-name sequence :adu))
             (refused (fn-bpn-evidence-name sequence :refused))
             (uncertain (fn-bpn-evidence-name sequence :uncertain)))
        (cond
         ((fn-bpn-evidence-regular-namep entry wire)
          (fn-bpn-evidence-recover-sorted (cdr entries) (+ 1 sequence)))
         ((or (fn-bpn-evidence-regular-namep entry adu)
              (fn-bpn-evidence-regular-namep entry refused)
              (fn-bpn-evidence-regular-namep entry uncertain))
          (if (and (consp (cdr entries))
                   (fn-bpn-evidence-regular-namep (car (cdr entries)) wire))
              (fn-bpn-evidence-recover-sorted (cdr (cdr entries))
                                               (+ 1 sequence))
            (list :fault :sidecar-without-wire)))
         (t (list :fault :namespace)))))))

(defun fn-bpn-evidence-recover (entries)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (true-listp entries)
           (<= (len entries) (* 2 *fn-bpn-evidence-max-records*)))
      (fn-bpn-evidence-recover-sorted entries 0)
    (list :fault :bound)))

; (:ok identity wire-name result-name wire-publication result-publication
;      successor)
; is issued only for the exact next names, while the caller reports exclusive
; lock ownership and absence of both names.  The host installs SUCCESSOR only
; after WIRE-PUBLICATION is durable.  A result-side refusal therefore cannot
; reuse a durable wire identity, while either uncertain publication fences the
; whole process.
(defun fn-bpn-evidence-authorize (st outcome lock-ownedp
                                        wire-absentp result-absentp)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((sequence (fn-bpn-evidence-next st))
         (result-kind (fn-bpn-evidence-result-kind outcome)))
    (if (and (fn-bpn-evidence-statep st)
             (< sequence *fn-bpn-evidence-max-records*)
             (fn-bpn-evidence-outcomep outcome)
             (equal lock-ownedp t)
             (equal wire-absentp t)
             (equal result-absentp t))
        (list :ok sequence
              (fn-bpn-evidence-name sequence :wire)
              (fn-bpn-evidence-name sequence result-kind)
              (fn-jpub-initial t)
              (fn-jpub-initial t)
              (fn-bpn-evidence-state (+ 1 sequence)))
      (list :refused :evidence-admission))))

(defun fn-bpn-evidence-operationp (operation)
  (and (true-listp operation)
       (equal (len operation) 7)
       (equal (car operation) :ok)
       (natp (nth 1 operation))
       (stringp (nth 2 operation))
       (stringp (nth 3 operation))
       (fn-jpub-statep (nth 4 operation))
       (fn-jpub-statep (nth 5 operation))
       (fn-bpn-evidence-statep (nth 6 operation))))

(defun fn-bpn-evidence-operation-identity (operation) (nth 1 operation))
(defun fn-bpn-evidence-operation-wire-name (operation) (nth 2 operation))
(defun fn-bpn-evidence-operation-result-name (operation) (nth 3 operation))
(defun fn-bpn-evidence-operation-wire-publication (operation) (nth 4 operation))
(defun fn-bpn-evidence-operation-result-publication (operation) (nth 5 operation))
(defun fn-bpn-evidence-operation-successor (operation) (nth 6 operation))

(defthm fn-bpn-evidence-recovery-produces-state-or-fault
  (implies
   (and (natp sequence)
        (<= sequence *fn-bpn-evidence-max-records*))
   (or (fn-bpn-evidence-statep
        (fn-bpn-evidence-recover-sorted entries sequence))
       (equal (car (fn-bpn-evidence-recover-sorted entries sequence)) :fault))))

(defthm fn-bpn-evidence-authorize-produces-operation
  (implies (equal (car (fn-bpn-evidence-authorize
                        state outcome lock-ownedp wire-absentp result-absentp))
                  :ok)
           (fn-bpn-evidence-operationp
            (fn-bpn-evidence-authorize
             state outcome lock-ownedp wire-absentp result-absentp))))

(defthm fn-bpn-evidence-successor-does-not-reuse-identity
  (implies (equal (car (fn-bpn-evidence-authorize
                        state outcome lock-ownedp wire-absentp result-absentp))
                  :ok)
           (equal
            (fn-bpn-evidence-next
             (fn-bpn-evidence-operation-successor
              (fn-bpn-evidence-authorize
               state outcome lock-ownedp wire-absentp result-absentp)))
            (+ 1 (fn-bpn-evidence-operation-identity
                  (fn-bpn-evidence-authorize
                   state outcome lock-ownedp wire-absentp result-absentp))))))

(defthm fn-bpn-evidence-recovery-counts-wire-only-identity
  (implies (and (fn-bpn-evidence-statep state)
                (< (fn-bpn-evidence-next state)
                   *fn-bpn-evidence-max-records*))
           (equal
            (fn-bpn-evidence-recover-sorted
             (list (cons (fn-bpn-evidence-name
                          (fn-bpn-evidence-next state) :wire)
                         :regular))
             (fn-bpn-evidence-next state))
            (fn-bpn-evidence-state
             (+ 1 (fn-bpn-evidence-next state))))))

(deftheory fn-bp-receive-evidence-vocabulary
  '(fn-bpn-evidence-kindp fn-bpn-evidence-outcomep
    fn-bpn-evidence-name fn-bpn-evidence-state fn-bpn-evidence-next
    fn-bpn-evidence-next-wire-name fn-bpn-evidence-next-result-name
    fn-bpn-evidence-statep fn-bpn-evidence-recover
    fn-bpn-evidence-authorize fn-bpn-evidence-operationp
    fn-bpn-evidence-operation-identity fn-bpn-evidence-operation-wire-name
    fn-bpn-evidence-operation-result-name
    fn-bpn-evidence-operation-wire-publication
    fn-bpn-evidence-operation-result-publication
    fn-bpn-evidence-operation-successor))
