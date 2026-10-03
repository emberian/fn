; Logical operation boundary, HST-046 / PRF-1252.  This is executable
; reference behavior, not a served-path representation or physical-I/O
; theorem.  Physical termination is an explicit environmental receipt;
; timeout, connection close and an application result cannot supply it.
(in-package "ACL2")
(include-book "resource-vector-tree")

; Reserve owner baseline and rescue before a user's bank can be opened.
(defun fn-rop-install (budget baseline reserve slots reserve-slots)
  (declare (xargs :guard t :verify-guards nil))
  (fn-rt-install budget baseline reserve slots reserve-slots))

; The principal is the root slot AND its generation.  Slots 0 and 1 belong
; to baseline/rescue; a user cannot address either as its funding producer.
(defun fn-rop-open (tree owner-slot budget slots)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (and (natp owner-slot) (<= 2 owner-slot)))
      (list :reserved-owner-slot tree)
    (let ((r (fn-rt-step tree (list :root :open owner-slot budget slots))))
      (if (eq (car r) :opened)
          (list :opened (cadr r) (cons owner-slot (caddr r)))
        r))))

(defun fn-rop-token (owner slot gen)
  (declare (xargs :guard t))
  (list :resource owner slot gen))

(defun fn-rop-tokenp (token)
  (declare (xargs :guard t))
  (and (true-listp token) (equal (len token) 4)
       (eq (car token) :resource)
       (consp (nth 1 token)) (natp (car (nth 1 token)))
       (<= 2 (car (nth 1 token))) (natp (cdr (nth 1 token)))
       (natp (nth 2 token)) (natp (nth 3 token))))

(defun fn-rop-token-livep (tree token)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-rop-tokenp token)
       (fn-rv-sub-bankp (car (nth 1 token)) (cdr (nth 1 token)) (fn-rt-root tree))
       (fn-rv-drawnp (nth 2 token) (nth 3 token)
                    (fn-rt-sub (car (nth 1 token)) tree))))

(defun fn-rop-draw (tree owner slot demand)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (and (consp owner) (natp (car owner)) (<= 2 (car owner))
                (natp (cdr owner)) (natp slot)))
      (list :invalid-principal tree)
    (let ((r (fn-rt-step tree (cons owner (list :draw slot demand)))))
      (if (eq (car r) :drawn)
          (list :drawn (cadr r) (fn-rop-token owner slot (caddr r)))
        r))))

; The gate itself is drawn FIRST.  Its demand prepays the admission and
; refusal path, including transient reusable allocation and spent work.
; Only then is the operation drawn.  A denied operation therefore still
; spends the gate's work.  The gate token must be released after the gate
; physically finishes; refusal is not a refund of spent coordinates.
; Tariff construction must occur inside a caller's already funded quantum;
; passing DEMAND here does not account for computing it outside this call.
(defun fn-rop-admit (tree owner gate-slot gate-demand slot demand)
  (declare (xargs :guard t :verify-guards nil))
  (let ((gate (fn-rop-draw tree owner gate-slot gate-demand)))
    (if (not (eq (car gate) :drawn))
        (list (car gate) tree nil nil)
      (let ((operation (fn-rop-draw (cadr gate) owner slot demand)))
        (list (car operation) (cadr operation)
              (caddr gate)
              (and (eq (car operation) :drawn) (caddr operation)))))))

; A timeout is observational only: preserve the physical and output holds.
(defun fn-rop-timeout (tree token)
  (declare (xargs :guard t :verify-guards nil))
  (list (if (fn-rop-token-livep tree token) :pending :stale) tree))

; Refund transient reusable excess only AFTER physical termination.  The
; caller's retained output remains on the SAME draw (no uncharged transfer).
; An empty retained output settles now; otherwise the token stays live.
(defun fn-rop-complete (tree token physical-terminalp retained)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((not (fn-rop-token-livep tree token)) (list :stale tree))
        ((not physical-terminalp) (list :pending tree))
        (t
         (let* ((owner (nth 1 token)) (slot (nth 2 token)) (gen (nth 3 token))
                (held (fn-rv-reusable
                       (fn-rv-demand slot (fn-rt-sub (car owner) tree)))))
           (if (not (and (fn-rv-vectorp retained)
                         (equal (fn-rv-spent retained) *fn-rv-zero*)
                         (fn-rv-below retained held)))
               (list :invalid-retention tree)
             (let ((r (fn-rt-step tree
                                  (cons owner (list :refund slot gen
                                                    (fn-rv-monus held retained))))))
               (if (not (eq (car r) :refunded)) r
                 (if (equal retained *fn-rv-zero*)
                     (fn-rt-step (cadr r) (cons owner (list :settle slot gen)))
                   (list :retained (cadr r) token)))))))))

; Output release is itself a physical receipt; an application ACK alone
; does not make either condition true.
(defun fn-rop-release (tree token physical-terminalp output-releasedp)
  (declare (xargs :guard t :verify-guards nil))
  (if (and physical-terminalp output-releasedp)
      (fn-rop-complete tree token t *fn-rv-zero*)
    (fn-rop-timeout tree token)))

(defun fn-rop-idle-rowsp (rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (and (consp (car rows)) (equal (caar rows) 0)
           (fn-rop-idle-rowsp (cdr rows)))
    (null rows)))

; Drain before destroy.  No caller boolean overrides outstanding draws;
; a live gate, worker, I/O or retained output draw blocks bank destruction.
; This whole-bank walk is a teardown reference, not a scheduling quantum.
(defun fn-rop-close (tree owner)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((not (and (consp owner) (natp (car owner)) (<= 2 (car owner))
                   (natp (cdr owner))
                   (fn-rv-sub-bankp (car owner) (cdr owner) (fn-rt-root tree))))
         (list :stale tree))
        ((not (fn-rop-idle-rowsp (fn-rv-slots (fn-rt-sub (car owner) tree))))
         (list :pending tree))
        (t (fn-rt-step tree (list :root :destroy (car owner) (cdr owner))))))

(defthm fn-rop-timeout-keeps-tree-by-definition
  (equal (cadr (fn-rop-timeout tree token)) tree))

(defthm fn-rop-complete-without-terminal-keeps-tree-by-definition
  (implies (not terminalp)
           (equal (cadr (fn-rop-complete tree token terminalp retained)) tree)))

(defthm fn-rop-close-with-outstanding-draw-keeps-tree-by-definition
  (implies (not (fn-rop-idle-rowsp
                 (fn-rv-slots (fn-rt-sub (car owner) tree))))
           (equal (cadr (fn-rop-close tree owner)) tree)))

(in-theory (disable fn-rop-install fn-rop-open fn-rop-token fn-rop-tokenp
                    fn-rop-token-livep fn-rop-draw fn-rop-admit fn-rop-timeout
                    fn-rop-complete fn-rop-release fn-rop-idle-rowsp fn-rop-close))
