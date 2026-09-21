; fn: bounded, incremental input framing for outbound NNTP feed replies.
;
; The outbound feed port decides what a complete response line means in
; books/owner-feed.lisp.  This book owns only the preceding CRLF framing.  It
; uses fn-wire-next's proved command-mode machine, returns at most one line on
; each call, and retains its bounded unconsumed suffix for the next call.
;
; Pulling one event matters: a completed reply can authorize an FNFD record
; and a following command.  The host must persist that record before it asks
; for the next event; it may not fold an arbitrary reply batch in :program.
(in-package "ACL2")
(include-book "wire")
(include-book "nntp-syntax")

; host/native/io.lisp's FNN-RECV uses this many octets per nonblocking read.
; The native feed service obtains this limit through its host wrapper; it does
; not choose a larger buffer.  A retained suffix is therefore bounded by this
; constant even when one socket read contains several response lines.
(defconst *fn-feed-wire-input-max-chunk-octets* 512)

(defun fn-fwi-make-state (wire pending)
  (list wire pending))

(defun fn-fwi-wire (x)
  (if (consp x) (car x) nil))

(defun fn-fwi-pending (x)
  (if (and (consp x) (consp (cdr x))) (cadr x) nil))

(defun fn-fwi-statep (x)
  (and (true-listp x) (equal (len x) 2)
       (fn-wire-statep (fn-fwi-wire x))
       (fn-wire-octet-listp (fn-fwi-pending x))
       (<= (len (fn-fwi-pending x)) *fn-feed-wire-input-max-chunk-octets*)))

(defun fn-fwi-initial-state ()
  ; Responses are NNTP command lines.  Article mode is never entered here.
  (fn-fwi-make-state
   (fn-wire-initial-state *fn-nntp-max-initial-line-octets* 1) nil))

(defun fn-fwi-chunkp (octets)
  (and (fn-wire-octet-listp octets)
       (<= (len octets) *fn-feed-wire-input-max-chunk-octets*)))

; A caller must drain retained input before offering another socket read.  This
; prevents concatenating arbitrary chunks in the adapter and establishes the
; bound of the retained suffix directly from one host read.
(defun fn-fwi-callp (st octets)
  (and (fn-fwi-statep st) (fn-fwi-chunkp octets)
       (or (null (fn-fwi-pending st)) (null octets))))

(defun fn-fwi-input (st octets)
  (if (consp (fn-fwi-pending st)) (fn-fwi-pending st) octets))

(defun fn-fwi-kind (x)
  (if (consp x) (car x) nil))

(defun fn-fwi-next-state (x)
  (if (and (consp x) (consp (cdr x))) (cadr x) nil))

(defun fn-fwi-line (x)
  (if (and (consp x) (consp (cdr x)) (consp (cddr x))) (caddr x) nil))

(defun fn-fwi-result (kind st line)
  (list kind st line))

(defun fn-fwi-command-eventp (event)
  (and (consp event) (consp (cdr event))
       (equal (car event) :command)
       (fn-wire-octet-listp (cadr event))))

(defun fn-fwi-from-wire-next (next)
  (let ((st (fn-fwi-make-state (fn-wire-next-state next)
                                (fn-wire-next-unconsumed next)))
        (event (fn-wire-next-event next)))
    (if (fn-fwi-command-eventp event)
        (fn-fwi-result :line st (cadr event))
      (if (equal (fn-wire-state-mode (fn-wire-next-state next)) :closed)
          (fn-fwi-result :closed st nil)
        (fn-fwi-result :need-input st nil)))))

(defun fn-fwi-step (st octets)
  (if (not (fn-fwi-callp st octets))
      (fn-fwi-result :invalid st nil)
    (fn-fwi-from-wire-next
     (fn-wire-next (fn-fwi-wire st) (fn-fwi-input st octets)))))

; The host table has one parser state for each connected feed.  Peer identity
; and connection validity remain the owner-feed port's responsibility; this
; recognizer makes only the retained-input bound and uniqueness explicit.
(defun fn-fwi-table-entryp (entry)
  (and (consp entry) (stringp (car entry)) (fn-fwi-statep (cdr entry))))

(defun fn-fwi-table-names (table)
  (if (consp table)
      (cons (if (consp (car table)) (car (car table)) nil)
            (fn-fwi-table-names (cdr table)))
    nil))

(defun fn-fwi-memberp (x xs)
  (if (consp xs)
      (or (equal x (car xs)) (fn-fwi-memberp x (cdr xs)))
    nil))

(defun fn-fwi-no-duplicatesp (xs)
  (if (consp xs)
      (and (not (fn-fwi-memberp (car xs) (cdr xs)))
           (fn-fwi-no-duplicatesp (cdr xs)))
    t))

(defun fn-fwi-tablep (table)
  (if (consp table)
      (and (fn-fwi-table-entryp (car table))
           (fn-fwi-tablep (cdr table))
           (fn-fwi-no-duplicatesp (fn-fwi-table-names table)))
    (null table)))

(defun fn-fwi-table-lookup (peer table)
  (if (consp table)
      (if (consp (car table))
          (if (equal peer (car (car table)))
              (cdr (car table))
            (fn-fwi-table-lookup peer (cdr table)))
        (fn-fwi-table-lookup peer (cdr table)))
    nil))

(defun fn-fwi-table-remove (peer table)
  (if (consp table)
      (if (and (consp (car table)) (equal peer (car (car table))))
          (fn-fwi-table-remove peer (cdr table))
        (cons (car table) (fn-fwi-table-remove peer (cdr table))))
    nil))

(defun fn-fwi-table-put (peer st table)
  (cons (cons peer st) (fn-fwi-table-remove peer table)))

(defthm fn-fwi-initial-state-is-state
  (fn-fwi-statep (fn-fwi-initial-state))
  :hints (("Goal" :in-theory (enable fn-fwi-initial-state fn-fwi-statep
                                      fn-fwi-make-state))))

; The named equation links this adapter API to the existing proved incremental
; wire machine.  It is the correspondence subject for the host wrapper.
(defthm fn-fwi-step-is-wire-next
  (implies (fn-fwi-callp st octets)
           (equal (fn-fwi-step st octets)
                  (fn-fwi-from-wire-next
                   (fn-wire-next (fn-fwi-wire st) (fn-fwi-input st octets)))))
  :hints (("Goal" :in-theory (enable fn-fwi-step))))

(defthm fn-fwi-step-invalid-is-explicit
  (implies (not (fn-fwi-callp st octets))
           (equal (fn-fwi-kind (fn-fwi-step st octets)) :invalid))
  :hints (("Goal" :in-theory (enable fn-fwi-step fn-fwi-kind))))

(verify-guards fn-fwi-make-state)
(verify-guards fn-fwi-wire)
(verify-guards fn-fwi-pending)
(verify-guards fn-fwi-statep)
(verify-guards fn-fwi-initial-state)
(verify-guards fn-fwi-chunkp)
(verify-guards fn-fwi-callp)
(verify-guards fn-fwi-input)
(verify-guards fn-fwi-kind)
(verify-guards fn-fwi-next-state)
(verify-guards fn-fwi-line)
(verify-guards fn-fwi-result)
(verify-guards fn-fwi-command-eventp)
(verify-guards fn-fwi-from-wire-next)
(verify-guards fn-fwi-step)
(verify-guards fn-fwi-table-entryp)
(verify-guards fn-fwi-table-names)
(verify-guards fn-fwi-memberp)
(verify-guards fn-fwi-no-duplicatesp)
(verify-guards fn-fwi-tablep)
(verify-guards fn-fwi-table-lookup)
(verify-guards fn-fwi-table-remove)
(verify-guards fn-fwi-table-put)
