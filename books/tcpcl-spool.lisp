; TCPCL spool recovery decisions and the process-death cut around publication.
;
; The native host owns descriptors and directory barriers.  This book owns
; which names are recoverable staging names, which entries recovery removes,
; and the abstract cut that leaves such a name behind before the final
; acknowledgement is released.

(in-package "ACL2")

(defconst *fn-tcl-spool-stage-prefix*
  '(46 105 110 99 111 109 105 110 103 45)) ; .incoming-

(defun fn-tcl-spool-prefixp (prefix octets)
  (declare (xargs :guard t))
  (if (atom prefix)
      t
    (and (consp octets)
         (equal (car prefix) (car octets))
         (fn-tcl-spool-prefixp (cdr prefix) (cdr octets)))))

(defun fn-tcl-spool-drop-prefix (prefix octets)
  (declare (xargs :guard t))
  (if (atom prefix)
      octets
    (fn-tcl-spool-drop-prefix (cdr prefix)
                              (if (consp octets) (cdr octets) nil))))

(defun fn-tcl-spool-decimal-to-hyphenp (octets)
  (declare (xargs :guard t))
  (and (consp octets)
       (if (equal (car octets) 45)
           t
         (and (natp (car octets))
              (<= 48 (car octets))
              (<= (car octets) 57)
              (fn-tcl-spool-decimal-to-hyphenp (cdr octets))))))

(defun fn-tcl-spool-after-hyphen (octets)
  (declare (xargs :guard t))
  (if (atom octets)
      nil
    (if (equal (car octets) 45)
        (cdr octets)
      (fn-tcl-spool-after-hyphen (cdr octets)))))

(defun fn-tcl-spool-hexp (octets)
  (declare (xargs :guard t))
  (if (atom octets)
      t
    (and (natp (car octets))
         (or (and (<= 48 (car octets)) (<= (car octets) 57))
             (and (<= 97 (car octets)) (<= (car octets) 102)))
         (fn-tcl-spool-hexp (cdr octets)))))

(defun fn-tcl-spool-stage-namep (name)
  (declare (xargs :guard t))
  (and (true-listp name)
       (fn-tcl-spool-prefixp *fn-tcl-spool-stage-prefix* name)
       (let* ((suffix (fn-tcl-spool-drop-prefix
                       *fn-tcl-spool-stage-prefix* name))
              (random (fn-tcl-spool-after-hyphen suffix)))
         (and (consp suffix)
              ; At least one decimal PID octet precedes the separator.
              (not (equal (car suffix) 45))
              (fn-tcl-spool-decimal-to-hyphenp suffix)
              (equal (len random) 24)
              (fn-tcl-spool-hexp random)))))

; :REMOVE is restricted to a regular file in the exact private grammar.
; Anything else in the reserved prefix is evidence recovery cannot explain.
(defun fn-tcl-spool-entry-action (name kind)
  (declare (xargs :guard t))
  (cond ((fn-tcl-spool-stage-namep name)
         (if (equal kind :regular) :remove :fault))
        ((fn-tcl-spool-prefixp *fn-tcl-spool-stage-prefix* name) :fault)
        (t :keep)))

(defun fn-tcl-spool-recovery-actions (entries)
  (declare (xargs :guard t))
  (if (atom entries)
      nil
    (let ((entry (if (consp (car entries)) (car entries) nil)))
      (cons (fn-tcl-spool-entry-action (car entry) (cdr entry))
            (fn-tcl-spool-recovery-actions (cdr entries))))))

(defun fn-tcl-spool-member-eq (x xs)
  (declare (xargs :guard t))
  (if (atom xs)
      nil
    (or (equal x (car xs))
        (fn-tcl-spool-member-eq x (cdr xs)))))

(defun fn-tcl-spool-recovery-plan (entries)
  (declare (xargs :guard t))
  (let ((actions (fn-tcl-spool-recovery-actions entries)))
    (if (fn-tcl-spool-member-eq :fault actions)
        (list :fault nil)
      (list :ok actions))))

; A small physical-state model for the host cut.  ENTRIES are directory
; entries, ACKP says whether the final XFER_ACK escaped the held queue, and
; STATUS is :ready, :staging, :published, or :recovery.
(defun fn-tcl-spool-state (entries ackp status)
  (declare (xargs :guard t))
  (list entries (if ackp t nil) status))

(defun fn-tcl-spool-entries (st)
  (declare (xargs :guard t))
  (if (consp st) (car st) nil))
(defun fn-tcl-spool-ackp (st)
  (declare (xargs :guard t))
  (if (and (consp st) (consp (cdr st))) (car (cdr st)) nil))
(defun fn-tcl-spool-status (st)
  (declare (xargs :guard t))
  (if (and (consp st) (consp (cdr st))
           (consp (cdr (cdr st))))
      (car (cdr (cdr st)))
    nil))

(defun fn-tcl-spool-remove-actions (entries actions)
  (declare (xargs :guard t))
  (if (or (atom entries) (atom actions))
      nil
    (if (equal (car actions) :remove)
        (fn-tcl-spool-remove-actions (cdr entries) (cdr actions))
      (cons (car entries)
            (fn-tcl-spool-remove-actions (cdr entries) (cdr actions))))))

(defun fn-tcl-spool-stage-data (entry st)
  (declare (xargs :guard t))
  (fn-tcl-spool-state (cons entry (fn-tcl-spool-entries st))
                      nil :staging))

(defun fn-tcl-spool-crash-before-publish (st)
  (declare (xargs :guard t))
  (fn-tcl-spool-state (fn-tcl-spool-entries st) nil :recovery))

(defun fn-tcl-spool-recover (st)
  (declare (xargs :guard t))
  (let* ((plan (fn-tcl-spool-recovery-plan (fn-tcl-spool-entries st)))
         (status (car plan))
         (actions (car (cdr plan))))
    (if (equal status :ok)
        (fn-tcl-spool-state
         (fn-tcl-spool-remove-actions (fn-tcl-spool-entries st) actions)
         nil :ready)
      (fn-tcl-spool-state (fn-tcl-spool-entries st) nil :fault))))

(defthm fn-tcl-spool-recovery-keeps-final-and-removes-regular-stage
  (implies (and (fn-tcl-spool-stage-namep stage)
                (not (fn-tcl-spool-prefixp *fn-tcl-spool-stage-prefix* final)))
           (equal
            (fn-tcl-spool-recover
             (fn-tcl-spool-crash-before-publish
              (fn-tcl-spool-stage-data
               (cons stage :regular)
               (fn-tcl-spool-state (list (cons final :regular)) nil :ready))))
            (fn-tcl-spool-state (list (cons final :regular)) nil :ready))))

(defthm fn-tcl-spool-nonregular-stage-fails-closed
  (implies (fn-tcl-spool-stage-namep stage)
           (equal (fn-tcl-spool-status
                   (fn-tcl-spool-recover
                    (fn-tcl-spool-state
                     (list (cons stage :other)) nil :recovery)))
                  :fault)))

(deftheory fn-tcl-spool-vocabulary
  '(fn-tcl-spool-stage-namep
    fn-tcl-spool-entry-action
    fn-tcl-spool-recovery-plan
    fn-tcl-spool-stage-data
    fn-tcl-spool-crash-before-publish
    fn-tcl-spool-recover
    fn-tcl-spool-entries
    fn-tcl-spool-ackp
    fn-tcl-spool-status))
