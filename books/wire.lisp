; fn NNTP wire framing: an executable, bounded, per-connection byte machine.
;
; This book deliberately stops before NNTP command interpretation.  It turns
; socket octets into complete CRLF lines, and (when explicitly placed in article
; mode) turns dot-stuffed lines into an article event.  A malformed delimiter or
; resource violation closes this model connection.  Closing is the selected safe
; boundary: no rejected article suffix can be reinterpreted as a command.

(in-package "ACL2")

; -----------------------------------------------------------------------------
; Primitive domains and dot transformation

(defun fn-wire-octetp (x)
  (and (integerp x) (<= 0 x) (<= x 255)))

(defun fn-wire-octet-listp (xs)
  (if (consp xs)
      (and (fn-wire-octetp (car xs))
           (fn-wire-octet-listp (cdr xs)))
    (null xs)))

(defun fn-wire-octet-linesp (lines)
  (if (consp lines)
      (and (fn-wire-octet-listp (car lines))
           (fn-wire-octet-linesp (cdr lines)))
    (null lines)))

(defun fn-wire-stuff-line (line)
  (if (and (consp line) (equal (car line) 46))
      (cons 46 line)
    line))

(defun fn-wire-unstuff-line (line)
  (if (and (consp line) (equal (car line) 46))
      (cdr line)
    line))

(defun fn-wire-reverse-octets-aux (octets accumulator)
  (if (consp octets)
      (fn-wire-reverse-octets-aux (cdr octets) (cons (car octets) accumulator))
    accumulator))

(defun fn-wire-reverse-octets (octets)
  (fn-wire-reverse-octets-aux octets nil))

(defthm fn-wire-reverse-octets-preserves-octet-listp
  (implies (and (fn-wire-octet-listp octets)
                (fn-wire-octet-listp accumulator))
           (fn-wire-octet-listp
            (fn-wire-reverse-octets-aux octets accumulator))))

(defthm fn-wire-reverse-octets-octet-listp
  (implies (fn-wire-octet-listp octets)
           (fn-wire-octet-listp (fn-wire-reverse-octets octets)))
  :hints (("Goal" :in-theory (enable fn-wire-reverse-octets))))

(defthm fn-wire-octet-listp-cdr
  (implies (fn-wire-octet-listp octets)
           (fn-wire-octet-listp (cdr octets))))

(defthm fn-wire-reverse-octets-aux-cdr-octet-listp
  (implies (fn-wire-octet-listp octets)
           (fn-wire-octet-listp
            (cdr (fn-wire-reverse-octets-aux octets nil))))
  :hints (("Goal" :use ((:instance fn-wire-reverse-octets-preserves-octet-listp
                                    (accumulator nil))))))

(defthm fn-wire-octet-listp-unstuff-line
  (implies (fn-wire-octet-listp line)
           (fn-wire-octet-listp (fn-wire-unstuff-line line))))

(defthm fn-wire-unstuff-reversed-octet-listp
  (implies (fn-wire-octet-listp octets)
           (fn-wire-octet-listp
            (fn-wire-unstuff-line (fn-wire-reverse-octets octets)))))

(defthm fn-wire-unstuff-stuff-line
  (equal (fn-wire-unstuff-line (fn-wire-stuff-line line)) line))

; -----------------------------------------------------------------------------
; State and results
;
; State fields are (mode reversed-current-line reversed-body pending-crp
;                  body-octet-count line-limit body-limit).
; body-octet-count charges each accepted decoded line plus its CRLF, making the
; body limit a bound on retained payload, rather than merely the number of
; source lines.  `pending-crp` means the parser has seen CR and will accept only
; LF next.

(defun fn-wire-modep (x)
  (or (equal x :command)
      (equal x :article)
      (equal x :closed)))

(defun fn-wire-state-mode (x)
  (declare (xargs :guard (true-listp x) :verify-guards nil))
  (car x))

(defun fn-wire-state-line-rev (x)
  (declare (xargs :guard (true-listp x) :verify-guards nil))
  (car (cdr x)))

(defun fn-wire-state-body-rev (x)
  (declare (xargs :guard (true-listp x) :verify-guards nil))
  (car (cdr (cdr x))))

(defun fn-wire-state-pending-crp (x)
  (declare (xargs :guard (true-listp x) :verify-guards nil))
  (car (cdr (cdr (cdr x)))))

(defun fn-wire-state-body-size (x)
  (declare (xargs :guard (true-listp x) :verify-guards nil))
  (car (cdr (cdr (cdr (cdr x))))))

(defun fn-wire-state-line-limit (x)
  (declare (xargs :guard (true-listp x) :verify-guards nil))
  (car (cdr (cdr (cdr (cdr (cdr x)))))))

(defun fn-wire-state-body-limit (x)
  (declare (xargs :guard (true-listp x) :verify-guards nil))
  (car (cdr (cdr (cdr (cdr (cdr (cdr x))))))))

(defun fn-wire-make-state (mode line-rev body-rev pending-crp body-size
                                 line-limit body-limit)
  (list mode line-rev body-rev pending-crp body-size line-limit body-limit))

(defun fn-wire-line-cost (line)
  (declare (xargs :guard (fn-wire-octet-listp line)
                  :verify-guards nil))
  (+ 2 (len line)))

(defun fn-wire-lines-size (lines)
  (declare (xargs :guard (fn-wire-octet-linesp lines)
                  :verify-guards nil))
  (if (consp lines)
      (+ (fn-wire-line-cost (car lines))
         (fn-wire-lines-size (cdr lines)))
    0))

(defthm fn-wire-lines-size-cons
  (equal (fn-wire-lines-size (cons line lines))
         (+ (fn-wire-line-cost line) (fn-wire-lines-size lines))))

(defun fn-wire-statep (x)
  (and (true-listp x)
       (equal (len x) 7)
       (fn-wire-modep (fn-wire-state-mode x))
       (fn-wire-octet-listp (fn-wire-state-line-rev x))
       (fn-wire-octet-linesp (fn-wire-state-body-rev x))
       (or (equal (fn-wire-state-pending-crp x) t)
           (null (fn-wire-state-pending-crp x)))
       (natp (fn-wire-state-body-size x))
       (posp (fn-wire-state-line-limit x))
       (posp (fn-wire-state-body-limit x))
       (<= (len (fn-wire-state-line-rev x))
           (fn-wire-state-line-limit x))
       (equal (fn-wire-state-body-size x)
              (fn-wire-lines-size (fn-wire-state-body-rev x)))
       (<= (fn-wire-state-body-size x)
           (fn-wire-state-body-limit x))
       (or (equal (fn-wire-state-mode x) :article)
           (and (null (fn-wire-state-body-rev x))
                (equal (fn-wire-state-body-size x) 0)))
       (or (not (equal (fn-wire-state-mode x) :closed))
           (and (null (fn-wire-state-line-rev x))
                (null (fn-wire-state-pending-crp x))))))

(defun fn-wire-initial-state (line-limit body-limit)
  (if (and (posp line-limit) (posp body-limit))
      (fn-wire-make-state :command nil nil nil 0 line-limit body-limit)
    nil))

(defthm fn-wire-initial-state-is-state
  (implies (and (posp line-limit) (posp body-limit))
           (fn-wire-statep (fn-wire-initial-state line-limit body-limit)))
  :hints (("Goal" :in-theory (enable fn-wire-initial-state fn-wire-statep))))

(defun fn-wire-result-state (x)
  (declare (xargs :guard (or (consp x) (null x))
                  :verify-guards nil))
  (car x))

(defun fn-wire-result-events (x)
  (declare (xargs :guard (or (consp x) (null x))
                  :verify-guards nil))
  (cdr x))

(defun fn-wire-make-result (wire-state events)
  (cons wire-state events))

(defun fn-wire-command-event (line)
  (list :command line))

(defun fn-wire-article-event (body)
  (list :article body))

(defun fn-wire-reject-event (reason)
  (list :reject reason))

(defun fn-wire-close (wire-state reason)
  (declare (xargs :guard (fn-wire-statep wire-state)
                  :verify-guards nil))
  (fn-wire-make-result
   (fn-wire-make-state :closed nil nil nil 0
                       (fn-wire-state-line-limit wire-state)
                       (fn-wire-state-body-limit wire-state))
   (list (fn-wire-reject-event reason))))

; A session machine calls this only after it has accepted a POST-like command.
; It deliberately requires no partially parsed command line.
(defun fn-wire-begin-article (wire-state)
  (if (and (fn-wire-statep wire-state)
           (equal (fn-wire-state-mode wire-state) :command)
           (null (fn-wire-state-line-rev wire-state))
           (null (fn-wire-state-pending-crp wire-state)))
      (fn-wire-make-state :article nil nil nil 0
                          (fn-wire-state-line-limit wire-state)
                          (fn-wire-state-body-limit wire-state))
    wire-state))

; -----------------------------------------------------------------------------
; One-byte input and incremental feeding

(defun fn-wire-after-line (wire-state line)
  (declare (xargs :guard (and (fn-wire-statep wire-state)
                              (fn-wire-octet-listp line))
                  :verify-guards nil))
  (if (equal (fn-wire-state-mode wire-state) :command)
      (fn-wire-make-result
       (fn-wire-make-state :command nil nil nil 0
                           (fn-wire-state-line-limit wire-state)
                           (fn-wire-state-body-limit wire-state))
       (list (fn-wire-command-event line)))
    (if (equal line '(46))
        (fn-wire-make-result
         (fn-wire-make-state :command nil nil nil 0
                             (fn-wire-state-line-limit wire-state)
                             (fn-wire-state-body-limit wire-state))
         (list (fn-wire-article-event
                (reverse (fn-wire-state-body-rev wire-state)))))
      (let ((decoded (fn-wire-unstuff-line line)))
        (if (<= (+ (fn-wire-state-body-size wire-state)
                   (fn-wire-line-cost decoded))
                (fn-wire-state-body-limit wire-state))
            (fn-wire-make-result
             (fn-wire-make-state :article nil
                                 (cons decoded (fn-wire-state-body-rev wire-state))
                                 nil
                                 (+ (fn-wire-state-body-size wire-state)
                                    (fn-wire-line-cost decoded))
                                 (fn-wire-state-line-limit wire-state)
                                 (fn-wire-state-body-limit wire-state))
             nil)
          (fn-wire-close wire-state :body-overlimit))))))

(defun fn-wire-feed-byte (wire-state byte)
  (if (not (fn-wire-statep wire-state))
      (fn-wire-make-result wire-state nil)
    (if (equal (fn-wire-state-mode wire-state) :closed)
        (fn-wire-make-result wire-state nil)
      (if (not (fn-wire-octetp byte))
          (fn-wire-close wire-state :malformed)
        (if (equal (fn-wire-state-pending-crp wire-state) t)
            (if (equal byte 10)
                (fn-wire-after-line
                 (fn-wire-make-state (fn-wire-state-mode wire-state)
                                     (fn-wire-state-line-rev wire-state)
                                     (fn-wire-state-body-rev wire-state)
                                     nil
                                     (fn-wire-state-body-size wire-state)
                                     (fn-wire-state-line-limit wire-state)
                                     (fn-wire-state-body-limit wire-state))
                 (fn-wire-reverse-octets (fn-wire-state-line-rev wire-state)))
              (fn-wire-close wire-state :malformed))
          (if (equal byte 13)
              (fn-wire-make-result
               (fn-wire-make-state (fn-wire-state-mode wire-state)
                                   (fn-wire-state-line-rev wire-state)
                                   (fn-wire-state-body-rev wire-state)
                                   t
                                   (fn-wire-state-body-size wire-state)
                                   (fn-wire-state-line-limit wire-state)
                                   (fn-wire-state-body-limit wire-state))
               nil)
            (if (equal byte 10)
                (fn-wire-close wire-state :malformed)
              (if (< (len (fn-wire-state-line-rev wire-state))
                     (fn-wire-state-line-limit wire-state))
                  (fn-wire-make-result
                   (fn-wire-make-state (fn-wire-state-mode wire-state)
                                       (cons byte (fn-wire-state-line-rev wire-state))
                                       (fn-wire-state-body-rev wire-state)
                                       nil
                                       (fn-wire-state-body-size wire-state)
                                       (fn-wire-state-line-limit wire-state)
                                       (fn-wire-state-body-limit wire-state))
                   nil)
                (fn-wire-close wire-state :line-overlimit)))))))))

(defthm fn-wire-feed-byte-preserves-statep
  (implies (fn-wire-statep wire-state)
           (fn-wire-statep
            (fn-wire-result-state (fn-wire-feed-byte wire-state byte))))
  :hints (("Goal" :in-theory (enable fn-wire-feed-byte
                                      fn-wire-after-line
                                      fn-wire-close
                                      fn-wire-statep))))

(defun fn-wire-feed-proper (wire-state octets)
  (declare (xargs :guard (and (fn-wire-statep wire-state)
                              (fn-wire-octet-listp octets))
                  :verify-guards nil
                  :measure (acl2-count octets)))
  ; The public wrapper establishes fn-wire-octet-listp before calling this
  ; worker.  Once a boundary failure closes the connection, do not walk any
  ; arbitrary suffix that followed it.
  (if (or (not (consp octets))
          (and (fn-wire-statep wire-state)
               (equal (fn-wire-state-mode wire-state) :closed)))
      (fn-wire-make-result wire-state nil)
    (let* ((first (fn-wire-feed-byte wire-state (car octets)))
           (rest (fn-wire-feed-proper (fn-wire-result-state first) (cdr octets))))
      (fn-wire-make-result (fn-wire-result-state rest)
                           (append (fn-wire-result-events first)
                                   (fn-wire-result-events rest))))))

; The host boundary supplies proper octet lists.  A malformed/improper ACL2
; list is rejected before it is treated as a completed socket chunk.  The
; closed-state branch comes first, so rejected data is never scanned again.
(defun fn-wire-feed (wire-state octets)
  (if (not (fn-wire-statep wire-state))
      (fn-wire-make-result wire-state nil)
    (if (equal (fn-wire-state-mode wire-state) :closed)
        (fn-wire-make-result wire-state nil)
      (if (fn-wire-octet-listp octets)
          (fn-wire-feed-proper wire-state octets)
        (fn-wire-close wire-state :malformed)))))

(defun fn-wire-continue (result octets)
  (declare (xargs :guard (true-listp result)
                  :verify-guards nil))
  (let ((next (fn-wire-feed (fn-wire-result-state result) octets)))
    (fn-wire-make-result (fn-wire-result-state next)
                         (append (fn-wire-result-events result)
                                 (fn-wire-result-events next)))))

; Pull exactly one framing event.  Unlike fn-wire-feed, this leaves every
; octet after that event unconsumed, so a host can process a POST-like command,
; switch to article mode, and then resume on the same socket chunk.  This is
; the host-dispatch API; fn-wire-feed remains a fixed-mode composition helper.
; Result fields are (state event unconsumed-octets), where event is NIL when
; the supplied octets contain no complete event.
(defun fn-wire-next-state (x)
  (declare (xargs :guard (true-listp x) :verify-guards nil))
  (car x))

(defun fn-wire-next-event (x)
  (declare (xargs :guard (true-listp x) :verify-guards nil))
  (car (cdr x)))

(defun fn-wire-next-unconsumed (x)
  (declare (xargs :guard (true-listp x) :verify-guards nil))
  (car (cdr (cdr x))))

(defun fn-wire-make-next (wire-state event unconsumed)
  (list wire-state event unconsumed))

(defun fn-wire-next (wire-state octets)
  (declare (xargs :measure (acl2-count octets)))
  (if (or (not (fn-wire-statep wire-state))
          (and (fn-wire-statep wire-state)
               (equal (fn-wire-state-mode wire-state) :closed)))
      (fn-wire-make-next wire-state nil octets)
    (if (null octets)
        (fn-wire-make-next wire-state nil nil)
      (if (not (consp octets))
          (let ((rejected (fn-wire-close wire-state :malformed)))
            (fn-wire-make-next (fn-wire-result-state rejected)
                               (car (fn-wire-result-events rejected)) nil))
        (let ((one (fn-wire-feed-byte wire-state (car octets))))
          (if (consp (fn-wire-result-events one))
              (fn-wire-make-next (fn-wire-result-state one)
                                 (car (fn-wire-result-events one))
                                 (cdr octets))
            (fn-wire-next (fn-wire-result-state one) (cdr octets)))))))
)

(defthm fn-wire-feed-empty
  (equal (fn-wire-feed wire-state nil)
         (fn-wire-make-result wire-state nil)))

(defthm fn-wire-feed-closed-noop
  (implies (and (fn-wire-statep wire-state)
                (equal (fn-wire-state-mode wire-state) :closed))
           (equal (fn-wire-feed wire-state octets)
                  (fn-wire-make-result wire-state nil))))

(defthm fn-wire-next-closed-noop
  (implies (and (fn-wire-statep wire-state)
                (equal (fn-wire-state-mode wire-state) :closed))
           (equal (fn-wire-next wire-state octets)
                  (fn-wire-make-next wire-state nil octets))))

(defthm fn-wire-feed-proper-append
  (equal (fn-wire-feed-proper wire-state (append left right))
         (fn-wire-make-result
          (fn-wire-result-state
           (fn-wire-feed-proper
            (fn-wire-result-state (fn-wire-feed-proper wire-state left)) right))
          (append (fn-wire-result-events (fn-wire-feed-proper wire-state left))
                  (fn-wire-result-events
                   (fn-wire-feed-proper
                    (fn-wire-result-state (fn-wire-feed-proper wire-state left))
                    right))))))

; -----------------------------------------------------------------------------
; Executable guard closure

(verify-guards fn-wire-octetp)
(verify-guards fn-wire-octet-listp)
(verify-guards fn-wire-octet-linesp)
(verify-guards fn-wire-stuff-line)
(verify-guards fn-wire-unstuff-line)
(verify-guards fn-wire-reverse-octets-aux)
(verify-guards fn-wire-reverse-octets)
(verify-guards fn-wire-modep)
(verify-guards fn-wire-state-mode)
(verify-guards fn-wire-state-line-rev)
(verify-guards fn-wire-state-body-rev)
(verify-guards fn-wire-state-pending-crp)
(verify-guards fn-wire-state-body-size)
(verify-guards fn-wire-state-line-limit)
(verify-guards fn-wire-state-body-limit)
(verify-guards fn-wire-make-state)
(verify-guards fn-wire-line-cost)
(verify-guards fn-wire-lines-size)
(verify-guards fn-wire-statep)
(verify-guards fn-wire-initial-state)
(verify-guards fn-wire-result-state)
(verify-guards fn-wire-result-events)
(verify-guards fn-wire-make-result)
(verify-guards fn-wire-command-event)
(verify-guards fn-wire-article-event)
(verify-guards fn-wire-reject-event)
(verify-guards fn-wire-close)
(verify-guards fn-wire-begin-article)
(verify-guards fn-wire-after-line)
(verify-guards fn-wire-feed-byte)
(verify-guards fn-wire-feed-proper)
(verify-guards fn-wire-feed)
(verify-guards fn-wire-continue)
(verify-guards fn-wire-next-state)
(verify-guards fn-wire-next-event)
(verify-guards fn-wire-next-unconsumed)
(verify-guards fn-wire-make-next)
(verify-guards fn-wire-next)
