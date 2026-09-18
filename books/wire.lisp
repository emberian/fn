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

(defun fn-wire-state-mode (x) (car x))
(defun fn-wire-state-line-rev (x) (car (cdr x)))
(defun fn-wire-state-body-rev (x) (car (cdr (cdr x))))
(defun fn-wire-state-pending-crp (x) (car (cdr (cdr (cdr x)))))
(defun fn-wire-state-body-size (x) (car (cdr (cdr (cdr (cdr x))))))
(defun fn-wire-state-line-limit (x) (car (cdr (cdr (cdr (cdr (cdr x)))))))
(defun fn-wire-state-body-limit (x) (car (cdr (cdr (cdr (cdr (cdr (cdr x))))))))

(defun fn-wire-make-state (mode line-rev body-rev pending-crp body-size
                                 line-limit body-limit)
  (list mode line-rev body-rev pending-crp body-size line-limit body-limit))

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
       (posp (fn-wire-state-body-limit x))))

(defun fn-wire-initial-state (line-limit body-limit)
  (if (and (posp line-limit) (posp body-limit))
      (fn-wire-make-state :command nil nil nil 0 line-limit body-limit)
    nil))

(defun fn-wire-result-state (x) (car x))
(defun fn-wire-result-events (x) (cdr x))

(defun fn-wire-make-result (wire-state events)
  (cons wire-state events))

(defun fn-wire-command-event (line)
  (list :command line))

(defun fn-wire-article-event (body)
  (list :article body))

(defun fn-wire-reject-event (reason)
  (list :reject reason))

(defun fn-wire-close (wire-state reason)
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

(defun fn-wire-line-cost (line)
  (+ 2 (len line)))

(defun fn-wire-after-line (wire-state line)
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
                 (reverse (fn-wire-state-line-rev wire-state)))
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

(defun fn-wire-feed (wire-state octets)
  (if (consp octets)
      (let* ((first (fn-wire-feed-byte wire-state (car octets)))
             (rest (fn-wire-feed (fn-wire-result-state first) (cdr octets))))
        (fn-wire-make-result (fn-wire-result-state rest)
                             (append (fn-wire-result-events first)
                                     (fn-wire-result-events rest))))
    (fn-wire-make-result wire-state nil)))

(defun fn-wire-continue (result octets)
  (let ((next (fn-wire-feed (fn-wire-result-state result) octets)))
    (fn-wire-make-result (fn-wire-result-state next)
                         (append (fn-wire-result-events result)
                                 (fn-wire-result-events next)))))

(defthm fn-wire-feed-empty
  (equal (fn-wire-feed wire-state nil)
         (fn-wire-make-result wire-state nil)))

(defthm fn-wire-feed-append
  (equal (fn-wire-feed wire-state (append left right))
         (fn-wire-continue (fn-wire-feed wire-state left) right)))
