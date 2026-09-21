; fn NNTP wire framing: an executable, bounded, per-connection byte machine.
;
; This book deliberately stops before NNTP command interpretation.  It turns
; socket octets into complete CRLF lines, and (when explicitly placed in article
; mode) turns dot-stuffed lines into an article event.  A malformed delimiter or
; resource violation closes this model connection.  Closing is the selected safe
; boundary: no rejected article suffix can be reinterpreted as a command.
;
; The served path is fn-wire-next, called from host/reader-host.lisp:91.  Each
; byte of a chunk must therefore cost a fixed amount of work: the state carries
; the current reversed line's length and the retained body's octet size, and
; the per-byte step reads those carried fields instead of re-running the state
; recognizer over the retained input.  fn-wire-feed-byte-reference and
; fn-wire-next-reference retain the earlier recomputing definitions, and
; fn-wire-next-matches-reference proves the served path returns exactly what
; they return on every fn-wire-statep input.

(in-package "ACL2")

; ---------------------------------------------------------------------------
; Total selectors.  The records below are positional lists; these two helpers
; are their logical primitives by mbe, so an accessor is guard-total (:guard t)
; and no caller ever incurs a true-listp obligation to read a field.

(defun fn-wire-ag-car (x)
  (declare (xargs :guard t))
  (mbe :logic (car x) :exec (if (consp x) (car x) nil)))

(defun fn-wire-ag-cdr (x)
  (declare (xargs :guard t))
  (mbe :logic (cdr x) :exec (if (consp x) (cdr x) nil)))

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

; ---------------------------------------------------------------------------
; Outbound article blocks
;
; A retained article is exact source octets.  The outbound direction is not
; permitted to repair bare LF, discard a final blank line, or otherwise choose
; a different source spelling.  It first accepts only a bounded sequence of
; CRLF-terminated octet lines, then applies RFC 3977 section 3.1.1's one wire
; transformation (a leading dot becomes two) and appends the block terminator.
; The result record is (:ok octets) or (:refused reason).  In particular NIL
; is a valid empty article and is not used as the refusal signal.

(defun fn-wire-reverse-lines-aux (lines accumulator)
  (declare (xargs :guard t))
  (if (consp lines)
      (fn-wire-reverse-lines-aux (cdr lines) (cons (car lines) accumulator))
    accumulator))

(defun fn-wire-reverse-lines (lines)
  (declare (xargs :guard t))
  (fn-wire-reverse-lines-aux lines nil))

; `append' requires a true list in executable ACL2.  This total counterpart
; keeps the public renderer guard-t on malformed host values; on proper lists
; (the successful parser result) it is ordinary append.
(defun fn-wire-append (left right)
  (declare (xargs :guard t :measure (acl2-count left)))
  (if (consp left)
      (cons (car left) (fn-wire-append (cdr left) right))
    right))

(defun fn-wire-outbound-ok (octets)
  (declare (xargs :guard t))
  (list :ok octets))

(defun fn-wire-outbound-refused (reason)
  (declare (xargs :guard t))
  (list :refused reason))

(defun fn-wire-outbound-okp (result)
  (declare (xargs :guard t))
  (and (consp result) (equal (car result) :ok)))

(defun fn-wire-outbound-octets (result)
  (declare (xargs :guard t))
  (if (fn-wire-outbound-okp result)
      (fn-wire-ag-car (fn-wire-ag-cdr result))
    nil))

(defun fn-wire-outbound-reason (result)
  (declare (xargs :guard t))
  (if (and (consp result) (equal (car result) :refused))
      (fn-wire-ag-car (fn-wire-ag-cdr result))
    nil))

; `fuel' is an explicit source-octet bound.  A CRLF consumes two units at
; once, so an input whose final CRLF crosses the bound is refused too.  This
; scanner has no newline normalization branch: CR not followed by LF, bare LF,
; a non-octet and an unterminated final line are all distinct refusal reasons.
(defun fn-wire-outbound-lines-aux (octets fuel line-rev lines-rev)
  (declare (xargs :guard t :verify-guards nil :measure (acl2-count octets)))
  (cond
   ((null octets)
    (if (null line-rev)
        (fn-wire-outbound-ok (fn-wire-reverse-lines lines-rev))
      (fn-wire-outbound-refused :unterminated)))
   ((not (consp octets)) (fn-wire-outbound-refused :malformed-list))
   ((not (fn-wire-octetp (car octets)))
    (fn-wire-outbound-refused :non-octet))
   ((equal (car octets) 13)
    (if (and (consp (cdr octets))
             (equal (car (cdr octets)) 10)
             (<= 2 (nfix fuel)))
        (fn-wire-outbound-lines-aux
         (cdr (cdr octets)) (- (nfix fuel) 2) nil
         (cons (fn-wire-reverse-octets line-rev) lines-rev))
      (if (and (consp (cdr octets))
               (equal (car (cdr octets)) 10))
          (fn-wire-outbound-refused :overlimit)
        (fn-wire-outbound-refused :malformed-cr))))
   ((equal (car octets) 10) (fn-wire-outbound-refused :bare-lf))
   ((zp (nfix fuel)) (fn-wire-outbound-refused :overlimit))
   (t (fn-wire-outbound-lines-aux (cdr octets) (1- (nfix fuel))
                                  (cons (car octets) line-rev) lines-rev))))

(defun fn-wire-outbound-lines (octets limit)
  (declare (xargs :guard t :verify-guards nil))
  (fn-wire-outbound-lines-aux octets (nfix limit) nil nil))

(defun fn-wire-render-lines (lines)
  (declare (xargs :guard t :verify-guards nil :measure (acl2-count lines)))
  (if (consp lines)
      (fn-wire-append (fn-wire-stuff-line (car lines))
                      (fn-wire-append '(13 10)
                                      (fn-wire-render-lines (cdr lines))))
    nil))

(defun fn-wire-render-block (article limit)
  (declare (xargs :guard t :verify-guards nil))
  (let ((parsed (fn-wire-outbound-lines article limit)))
    (if (fn-wire-outbound-okp parsed)
        (fn-wire-outbound-ok
         (fn-wire-append (fn-wire-render-lines (fn-wire-outbound-octets parsed))
                         '(46 13 10)))
      parsed)))

(defun fn-wire-prefixp (prefix octets)
  (declare (xargs :guard t :verify-guards nil :measure (acl2-count prefix)))
  (if (consp prefix)
      (and (consp octets)
           (equal (car prefix) (car octets))
           (fn-wire-prefixp (cdr prefix) (cdr octets)))
    t))

(defconst *fn-wire-check-prefix* '(67 72 69 67 75 32))       ; "CHECK "
(defconst *fn-wire-ihave-prefix* '(73 72 65 86 69 32))       ; "IHAVE "
(defconst *fn-wire-takethis-prefix* '(84 65 75 69 84 72 73 83 32)) ; "TAKETHIS "

; Split one command line without accepting a different delimiter.  The line
; is returned WITH its CRLF because it is already ACL2's command effect and
; must cross the socket verbatim.  This is bounded independently from the
; following article source.
(defun fn-wire-outbound-command-line-aux (octets fuel reversed)
  (declare (xargs :guard t :verify-guards nil :measure (acl2-count octets)))
  (cond
   ((null octets) (fn-wire-outbound-refused :unterminated-command))
   ((not (consp octets)) (fn-wire-outbound-refused :malformed-list))
   ((not (fn-wire-octetp (car octets)))
    (fn-wire-outbound-refused :non-octet))
   ((equal (car octets) 13)
    (if (and (consp (cdr octets))
             (equal (car (cdr octets)) 10)
             (<= 2 (nfix fuel)))
         (fn-wire-outbound-ok
         (list (fn-wire-append (fn-wire-reverse-octets reversed) '(13 10))
               (cdr (cdr octets))))
      (if (and (consp (cdr octets))
               (equal (car (cdr octets)) 10))
          (fn-wire-outbound-refused :command-overlimit)
        (fn-wire-outbound-refused :malformed-command-cr))))
   ((equal (car octets) 10) (fn-wire-outbound-refused :bare-command-lf))
   ((zp (nfix fuel)) (fn-wire-outbound-refused :command-overlimit))
   (t (fn-wire-outbound-command-line-aux (cdr octets) (1- (nfix fuel))
                                          (cons (car octets) reversed)))))

(defun fn-wire-outbound-command-line (octets limit)
  (declare (xargs :guard t :verify-guards nil))
  (fn-wire-outbound-command-line-aux octets (nfix limit) nil))

(defun fn-wire-render-feed-command (command command-limit article-limit)
  (declare (xargs :guard t :verify-guards nil))
  (cond
   ((null command) (fn-wire-outbound-ok nil))
   ((or (fn-wire-prefixp *fn-wire-check-prefix* command)
        (fn-wire-prefixp *fn-wire-ihave-prefix* command))
    (let ((line (fn-wire-outbound-command-line command command-limit)))
      (if (and (fn-wire-outbound-okp line)
               (null (fn-wire-ag-car
                      (fn-wire-ag-cdr (fn-wire-outbound-octets line)))))
          (fn-wire-outbound-ok (fn-wire-ag-car
                                (fn-wire-outbound-octets line)))
        (if (fn-wire-outbound-okp line)
            (fn-wire-outbound-refused :offer-has-body)
          line))))
   ((fn-wire-prefixp *fn-wire-takethis-prefix* command)
    (let ((line (fn-wire-outbound-command-line command command-limit)))
      (if (not (fn-wire-outbound-okp line))
          line
        (let ((block (fn-wire-render-block
                      (fn-wire-ag-car
                       (fn-wire-ag-cdr (fn-wire-outbound-octets line)))
                      article-limit)))
          (if (fn-wire-outbound-okp block)
              (fn-wire-outbound-ok
               (fn-wire-append (fn-wire-ag-car (fn-wire-outbound-octets line))
                               (fn-wire-outbound-octets block)))
            block)))))
   (t (fn-wire-render-block command article-limit))))

; -----------------------------------------------------------------------------
; State and results
;
; State fields are (mode reversed-current-line line-octet-count reversed-body
;                  pending-crp body-octet-count line-limit body-limit).
; line-octet-count is the length of the reversed current line and
; body-octet-count charges each accepted decoded line plus its CRLF, making the
; body limit a bound on retained payload, rather than merely the number of
; source lines.  Both counters are maintained incrementally by the per-byte
; step, and fn-wire-statep requires each to equal the measurement of the
; retained list it summarizes, so a carried counter cannot drift from the
; retained input it bounds.  `pending-crp` means the parser has seen CR and
; will accept only LF next.

(defun fn-wire-modep (x)
  (or (equal x :command)
      (equal x :article)
      (equal x :closed)))

(defun fn-wire-state-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 8)))

(defun fn-wire-state-mode (x)
  (declare (xargs :guard t))
  (fn-wire-ag-car x))

(defun fn-wire-state-line-rev (x)
  (declare (xargs :guard t))
  (fn-wire-ag-car (fn-wire-ag-cdr x)))

(defun fn-wire-state-line-len (x)
  (declare (xargs :guard t))
  (fn-wire-ag-car (fn-wire-ag-cdr (fn-wire-ag-cdr x))))

(defun fn-wire-state-body-rev (x)
  (declare (xargs :guard t))
  (fn-wire-ag-car (fn-wire-ag-cdr (fn-wire-ag-cdr (fn-wire-ag-cdr x)))))

(defun fn-wire-state-pending-crp (x)
  (declare (xargs :guard t))
  (fn-wire-ag-car (fn-wire-ag-cdr (fn-wire-ag-cdr (fn-wire-ag-cdr (fn-wire-ag-cdr x))))))

(defun fn-wire-state-body-size (x)
  (declare (xargs :guard t))
  (fn-wire-ag-car (fn-wire-ag-cdr (fn-wire-ag-cdr (fn-wire-ag-cdr (fn-wire-ag-cdr (fn-wire-ag-cdr x)))))))

(defun fn-wire-state-line-limit (x)
  (declare (xargs :guard t))
  (fn-wire-ag-car (fn-wire-ag-cdr (fn-wire-ag-cdr (fn-wire-ag-cdr (fn-wire-ag-cdr (fn-wire-ag-cdr (fn-wire-ag-cdr x))))))))

(defun fn-wire-state-body-limit (x)
  (declare (xargs :guard t))
  (fn-wire-ag-car (fn-wire-ag-cdr (fn-wire-ag-cdr (fn-wire-ag-cdr (fn-wire-ag-cdr (fn-wire-ag-cdr (fn-wire-ag-cdr (fn-wire-ag-cdr x)))))))))

(defun fn-wire-make-state (mode line-rev line-len body-rev pending-crp
                                body-size line-limit body-limit)
  (list mode line-rev line-len body-rev pending-crp body-size
        line-limit body-limit))


; Record lemmas for the wire state record: its shape and one accessor-of-constructor
; equality per field.  Below this point nothing opens the record.

(defthm fn-wire-state-shapep-of-fn-wire-make-state
  (fn-wire-state-shapep (fn-wire-make-state mode line-rev line-len body-rev pending-crp body-size line-limit body-limit)))

(defthm fn-wire-state-mode-of-fn-wire-make-state
  (equal (fn-wire-state-mode (fn-wire-make-state mode line-rev line-len body-rev pending-crp body-size line-limit body-limit))
         mode))

(defthm fn-wire-state-line-rev-of-fn-wire-make-state
  (equal (fn-wire-state-line-rev (fn-wire-make-state mode line-rev line-len body-rev pending-crp body-size line-limit body-limit))
         line-rev))

(defthm fn-wire-state-line-len-of-fn-wire-make-state
  (equal (fn-wire-state-line-len (fn-wire-make-state mode line-rev line-len body-rev pending-crp body-size line-limit body-limit))
         line-len))

(defthm fn-wire-state-body-rev-of-fn-wire-make-state
  (equal (fn-wire-state-body-rev (fn-wire-make-state mode line-rev line-len body-rev pending-crp body-size line-limit body-limit))
         body-rev))

(defthm fn-wire-state-pending-crp-of-fn-wire-make-state
  (equal (fn-wire-state-pending-crp (fn-wire-make-state mode line-rev line-len body-rev pending-crp body-size line-limit body-limit))
         pending-crp))

(defthm fn-wire-state-body-size-of-fn-wire-make-state
  (equal (fn-wire-state-body-size (fn-wire-make-state mode line-rev line-len body-rev pending-crp body-size line-limit body-limit))
         body-size))

(defthm fn-wire-state-line-limit-of-fn-wire-make-state
  (equal (fn-wire-state-line-limit (fn-wire-make-state mode line-rev line-len body-rev pending-crp body-size line-limit body-limit))
         line-limit))

(defthm fn-wire-state-body-limit-of-fn-wire-make-state
  (equal (fn-wire-state-body-limit (fn-wire-make-state mode line-rev line-len body-rev pending-crp body-size line-limit body-limit))
         body-limit))

(in-theory (disable (:d fn-wire-state-shapep) (:d fn-wire-make-state) (:d fn-wire-state-mode) (:d fn-wire-state-line-rev) (:d fn-wire-state-line-len) (:d fn-wire-state-body-rev) (:d fn-wire-state-pending-crp) (:d fn-wire-state-body-size) (:d fn-wire-state-line-limit) (:d fn-wire-state-body-limit)))

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
  (and (fn-wire-state-shapep x)
       (fn-wire-modep (fn-wire-state-mode x))
       (fn-wire-octet-listp (fn-wire-state-line-rev x))
       (fn-wire-octet-linesp (fn-wire-state-body-rev x))
       (or (equal (fn-wire-state-pending-crp x) t)
           (null (fn-wire-state-pending-crp x)))
       (natp (fn-wire-state-line-len x))
       (natp (fn-wire-state-body-size x))
       (posp (fn-wire-state-line-limit x))
       (posp (fn-wire-state-body-limit x))
       (equal (fn-wire-state-line-len x)
              (len (fn-wire-state-line-rev x)))
       (<= (fn-wire-state-line-len x)
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
      (fn-wire-make-state :command nil 0 nil nil 0 line-limit body-limit)
    nil))

(defthm fn-wire-initial-state-is-state
  (implies (and (posp line-limit) (posp body-limit))
           (fn-wire-statep (fn-wire-initial-state line-limit body-limit)))
  :hints (("Goal" :in-theory (enable fn-wire-initial-state fn-wire-statep fn-wire-state-shapep))))

(defun fn-wire-result-shapep (x)
  (declare (xargs :guard t))
  (consp x))

(defun fn-wire-result-state (x)
  (declare (xargs :guard t))
  (fn-wire-ag-car x))

(defun fn-wire-result-events (x)
  (declare (xargs :guard t))
  (fn-wire-ag-cdr x))

(defun fn-wire-make-result (wire-state events)
  (cons wire-state events))


; Record lemmas for the result record (a state consed onto an event list).

(defthm fn-wire-result-shapep-of-fn-wire-make-result
  (fn-wire-result-shapep (fn-wire-make-result wire-state events)))

(defthm fn-wire-result-state-of-fn-wire-make-result
  (equal (fn-wire-result-state (fn-wire-make-result wire-state events))
         wire-state))

(defthm fn-wire-result-events-of-fn-wire-make-result
  (equal (fn-wire-result-events (fn-wire-make-result wire-state events))
         events))

(in-theory (disable (:d fn-wire-result-shapep) (:d fn-wire-make-result)
                    (:d fn-wire-result-state) (:d fn-wire-result-events)))

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
   (fn-wire-make-state :closed nil 0 nil nil 0
                       (fn-wire-state-line-limit wire-state)
                       (fn-wire-state-body-limit wire-state))
   (list (fn-wire-reject-event reason))))

(defthm fn-wire-close-is-statep
  (implies (fn-wire-statep wire-state)
           (fn-wire-statep
            (fn-wire-result-state (fn-wire-close wire-state reason))))
  :hints (("Goal" :in-theory (enable fn-wire-close fn-wire-statep
                                      ))))

; A car-form restatement of the accessor-form fact above, kept because the
; framing loops in books/wire-invariants.lisp reason about the result
; record's pairing and leave goals in car form.  It is a `-by-definition`
; twin, not a registry event.
(defthm fn-wire-close-is-statep-car-form
  (implies (fn-wire-statep wire-state)
           (fn-wire-statep (car (fn-wire-close wire-state reason))))
  :hints (("Goal"
           :use ((:instance fn-wire-close-is-statep))
           :in-theory (e/d (fn-wire-result-state)
                           (fn-wire-close fn-wire-statep)))))

; -----------------------------------------------------------------------------
; Entering article mode
;
; A session machine calls this only after it has accepted a POST-like command.
; It requires a valid, quiesced command-mode connection: no partially parsed
; command line and no pending CR.  A request that does not meet that condition
; is refused explicitly, with the input state returned unchanged and one
; :begin-article-unquiesced reject event, rather than silently returning the
; unchanged state as if article mode had been entered.  Refusal does not close
; the connection; the caller decides what to do with the reject event.

(defun fn-wire-begin-article-admissiblep (wire-state)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-wire-statep wire-state)
       (equal (fn-wire-state-mode wire-state) :command)
       (null (fn-wire-state-line-rev wire-state))
       (null (fn-wire-state-pending-crp wire-state))))

; RFC 3977's multiline data grammar has no command-line-sized article-line
; ceiling.  The chosen profile admits every source line within the retained
; article bound plus one physical octet for the only outbound expansion, a
; line-leading dot.  Keeping this calculation in ACL2 makes the served mode
; switch and the outbound renderer share one capacity contract.
(defun fn-wire-article-line-limit (wire-state)
  (declare (xargs :guard t))
  (+ 1 (nfix (fn-wire-state-body-limit wire-state))))

; RFC 3977's 510-octet command-content ceiling does not constrain article
; data.  A caller switches to its selected physical article-line profile only
; after a complete, quiescent command has requested article mode.  The byte
; machine continues to carry one active ceiling, so its per-byte work stays
; constant; this transition is the explicit mode/profile seam rather than an
; accidental reuse of the command ceiling for article bytes.
(defun fn-wire-begin-article-with-line-limit (wire-state article-line-limit)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-wire-begin-article-admissiblep wire-state)
      (if (posp article-line-limit)
          (fn-wire-make-result
           (fn-wire-make-state :article nil 0 nil nil 0
                               article-line-limit
                               (fn-wire-state-body-limit wire-state))
           nil)
        (fn-wire-make-result
         wire-state
         (list (fn-wire-reject-event :begin-article-bad-line-limit))))
    (fn-wire-make-result
     wire-state
     (list (fn-wire-reject-event :begin-article-unquiesced)))))

(defun fn-wire-begin-article (wire-state)
  (declare (xargs :guard t :verify-guards nil))
  (fn-wire-begin-article-with-line-limit
   wire-state (fn-wire-state-line-limit wire-state)))

(defun fn-wire-begin-article-refusedp (result)
  (declare (xargs :guard (or (consp result) (null result))
                  :verify-guards nil))
  (consp (fn-wire-result-events result)))

; The refusal case is exactly the inadmissible case: this is an equality, so no
; other input is refused and no inadmissible input is silently accepted.
(defthm fn-wire-begin-article-refuses-exactly-the-inadmissible
  (equal (fn-wire-begin-article-refusedp (fn-wire-begin-article wire-state))
         (not (fn-wire-begin-article-admissiblep wire-state)))
  :hints (("Goal" :in-theory (enable fn-wire-begin-article
                                      fn-wire-begin-article-with-line-limit
                                      fn-wire-begin-article-refusedp
                                      ))))

(defthm fn-wire-begin-article-refusal-keeps-state
  (implies (not (fn-wire-begin-article-admissiblep wire-state))
           (and (equal (fn-wire-result-state (fn-wire-begin-article wire-state))
                       wire-state)
                (equal (fn-wire-result-events (fn-wire-begin-article wire-state))
                       (list (fn-wire-reject-event :begin-article-unquiesced)))))
  :hints (("Goal" :in-theory (enable fn-wire-begin-article
                                      fn-wire-begin-article-with-line-limit
                                      ))))

(defthm fn-wire-begin-article-acceptance-enters-empty-article-mode
  (implies (fn-wire-begin-article-admissiblep wire-state)
           (let ((next (fn-wire-result-state
                        (fn-wire-begin-article wire-state))))
             (and (fn-wire-statep next)
                  (equal (fn-wire-state-mode next) :article)
                  (null (fn-wire-state-line-rev next))
                  (equal (fn-wire-state-line-len next) 0)
                  (null (fn-wire-state-body-rev next))
                  (equal (fn-wire-state-body-size next) 0)
                  (equal (fn-wire-state-line-limit next)
                         (fn-wire-state-line-limit wire-state))
                  (equal (fn-wire-state-body-limit next)
                         (fn-wire-state-body-limit wire-state)))))
  :hints (("Goal" :in-theory (enable fn-wire-begin-article
                                      fn-wire-begin-article-with-line-limit
                                      fn-wire-begin-article-admissiblep
                                      fn-wire-statep))))

(defthm fn-wire-begin-article-preserves-statep
  (implies (fn-wire-statep wire-state)
           (fn-wire-statep
            (fn-wire-result-state (fn-wire-begin-article wire-state))))
  :hints (("Goal" :in-theory (enable fn-wire-begin-article
                                      fn-wire-begin-article-with-line-limit
                                      fn-wire-begin-article-admissiblep
                                      fn-wire-statep))))

(defthm fn-wire-begin-article-with-line-limit-acceptance
  (implies (and (fn-wire-begin-article-admissiblep wire-state)
                (posp article-line-limit))
           (let ((next (fn-wire-result-state
                        (fn-wire-begin-article-with-line-limit
                         wire-state article-line-limit))))
             (and (fn-wire-statep next)
                  (equal (fn-wire-state-mode next) :article)
                  (equal (fn-wire-state-line-limit next) article-line-limit)
                  (equal (fn-wire-state-body-limit next)
                         (fn-wire-state-body-limit wire-state))
                  (null (fn-wire-state-line-rev next))
                  (null (fn-wire-state-body-rev next)))))
  :hints (("Goal"
           :in-theory (enable fn-wire-begin-article-with-line-limit
                              fn-wire-begin-article-admissiblep
                              fn-wire-statep))))

(defthm fn-wire-begin-article-with-line-limit-preserves-statep
  (implies (fn-wire-statep wire-state)
           (fn-wire-statep
            (fn-wire-result-state
             (fn-wire-begin-article-with-line-limit
              wire-state article-line-limit))))
  :hints (("Goal"
           :in-theory (enable fn-wire-begin-article-with-line-limit
                              fn-wire-begin-article-admissiblep
                              fn-wire-statep))))

(defthm fn-wire-article-line-limit-is-positive
  (implies (fn-wire-statep wire-state)
           (posp (fn-wire-article-line-limit wire-state)))
  :hints (("Goal" :in-theory (enable fn-wire-article-line-limit
                                      fn-wire-statep))))

; -----------------------------------------------------------------------------
; One-byte input and incremental feeding

(defun fn-wire-after-line (wire-state line)
  (declare (xargs :guard (and (fn-wire-statep wire-state)
                              (fn-wire-octet-listp line))
                  :verify-guards nil))
  (if (equal (fn-wire-state-mode wire-state) :command)
      (fn-wire-make-result
       (fn-wire-make-state :command nil 0 nil nil 0
                           (fn-wire-state-line-limit wire-state)
                           (fn-wire-state-body-limit wire-state))
       (list (fn-wire-command-event line)))
    (if (equal line '(46))
        (fn-wire-make-result
         (fn-wire-make-state :command nil 0 nil nil 0
                             (fn-wire-state-line-limit wire-state)
                             (fn-wire-state-body-limit wire-state))
         (list (fn-wire-article-event
                (reverse (fn-wire-state-body-rev wire-state)))))
      (let ((decoded (fn-wire-unstuff-line line)))
        (if (<= (+ (fn-wire-state-body-size wire-state)
                   (fn-wire-line-cost decoded))
                (fn-wire-state-body-limit wire-state))
            (fn-wire-make-result
             (fn-wire-make-state :article nil 0
                                 (cons decoded (fn-wire-state-body-rev wire-state))
                                 nil
                                 (+ (fn-wire-state-body-size wire-state)
                                    (fn-wire-line-cost decoded))
                                 (fn-wire-state-line-limit wire-state)
                                 (fn-wire-state-body-limit wire-state))
             nil)
          (fn-wire-close wire-state :body-overlimit))))))

; The per-byte step of the served path.  Every branch reads carried scalars and
; conses at most one octet: it runs no recognizer over the retained line, the
; retained body, or the body size.  Its guard is fn-wire-statep, established
; once per chunk by fn-wire-next.
(defun fn-wire-feed-byte (wire-state byte)
  (declare (xargs :guard (fn-wire-statep wire-state)
                  :verify-guards nil))
  (if (equal (fn-wire-state-mode wire-state) :closed)
      (fn-wire-make-result wire-state nil)
    (if (not (fn-wire-octetp byte))
        (fn-wire-close wire-state :malformed)
      (if (equal (fn-wire-state-pending-crp wire-state) t)
          (if (equal byte 10)
              (fn-wire-after-line
               (fn-wire-make-state (fn-wire-state-mode wire-state)
                                   (fn-wire-state-line-rev wire-state)
                                   (fn-wire-state-line-len wire-state)
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
                                 (fn-wire-state-line-len wire-state)
                                 (fn-wire-state-body-rev wire-state)
                                 t
                                 (fn-wire-state-body-size wire-state)
                                 (fn-wire-state-line-limit wire-state)
                                 (fn-wire-state-body-limit wire-state))
             nil)
          (if (equal byte 10)
              (fn-wire-close wire-state :malformed)
            (if (< (fn-wire-state-line-len wire-state)
                   (fn-wire-state-line-limit wire-state))
                (fn-wire-make-result
                 (fn-wire-make-state (fn-wire-state-mode wire-state)
                                     (cons byte (fn-wire-state-line-rev wire-state))
                                     (+ 1 (fn-wire-state-line-len wire-state))
                                     (fn-wire-state-body-rev wire-state)
                                     nil
                                     (fn-wire-state-body-size wire-state)
                                     (fn-wire-state-line-limit wire-state)
                                     (fn-wire-state-body-limit wire-state))
                 nil)
              (fn-wire-close wire-state :line-overlimit))))))))

(defthm fn-wire-feed-byte-preserves-statep
  (implies (fn-wire-statep wire-state)
           (fn-wire-statep
            (fn-wire-result-state (fn-wire-feed-byte wire-state byte))))
  :hints (("Goal" :in-theory (enable fn-wire-feed-byte
                                      fn-wire-after-line
                                      fn-wire-close
                                      fn-wire-statep))))

; The retained-input bound is carried, not recomputed: the two counters the
; step maintains are exactly the measurements of the lists they bound, so the
; bound on retained octets survives every step.
; A car-form restatement of the accessor-form fact above, kept because the
; framing loops in books/wire-invariants.lisp reason about the result
; record's pairing and leave goals in car form.  It is a `-by-definition`
; twin, not a registry event.
(defthm fn-wire-feed-byte-preserves-statep-car-form
  (implies (fn-wire-statep wire-state)
           (fn-wire-statep (car (fn-wire-feed-byte wire-state byte))))
  :hints (("Goal"
           :use ((:instance fn-wire-feed-byte-preserves-statep))
           :in-theory (e/d (fn-wire-result-state)
                           (fn-wire-feed-byte fn-wire-statep)))))

(defthm fn-wire-feed-byte-retained-input-is-bounded
  (implies (fn-wire-statep wire-state)
           (let ((next (fn-wire-result-state
                        (fn-wire-feed-byte wire-state byte))))
             (and (<= (len (fn-wire-state-line-rev next))
                      (fn-wire-state-line-limit next))
                  (<= (fn-wire-lines-size (fn-wire-state-body-rev next))
                      (fn-wire-state-body-limit next)))))
  :hints (("Goal"
           :use ((:instance fn-wire-feed-byte-preserves-statep))
           :in-theory (e/d (fn-wire-statep)
                           (fn-wire-feed-byte
                            fn-wire-feed-byte-preserves-statep)))))

; The earlier per-byte step, retained as the reference for the equality
; theorem below.  It re-runs fn-wire-statep on every byte and measures the
; retained line with `len`; on an article that makes a chunk of B octets cost
; work quadratic in B.
(defun fn-wire-feed-byte-reference (wire-state byte)
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
                                     (len (fn-wire-state-line-rev wire-state))
                                     (fn-wire-state-body-rev wire-state)
                                     nil
                                     (fn-wire-lines-size
                                      (fn-wire-state-body-rev wire-state))
                                     (fn-wire-state-line-limit wire-state)
                                     (fn-wire-state-body-limit wire-state))
                 (fn-wire-reverse-octets (fn-wire-state-line-rev wire-state)))
              (fn-wire-close wire-state :malformed))
          (if (equal byte 13)
              (fn-wire-make-result
               (fn-wire-make-state (fn-wire-state-mode wire-state)
                                   (fn-wire-state-line-rev wire-state)
                                   (len (fn-wire-state-line-rev wire-state))
                                   (fn-wire-state-body-rev wire-state)
                                   t
                                   (fn-wire-lines-size
                                    (fn-wire-state-body-rev wire-state))
                                   (fn-wire-state-line-limit wire-state)
                                   (fn-wire-state-body-limit wire-state))
               nil)
            (if (equal byte 10)
                (fn-wire-close wire-state :malformed)
              (if (< (len (fn-wire-state-line-rev wire-state))
                     (fn-wire-state-line-limit wire-state))
                  (fn-wire-make-result
                   (fn-wire-make-state
                    (fn-wire-state-mode wire-state)
                    (cons byte (fn-wire-state-line-rev wire-state))
                    (len (cons byte (fn-wire-state-line-rev wire-state)))
                    (fn-wire-state-body-rev wire-state)
                    nil
                    (fn-wire-lines-size (fn-wire-state-body-rev wire-state))
                    (fn-wire-state-line-limit wire-state)
                    (fn-wire-state-body-limit wire-state))
                   nil)
                (fn-wire-close wire-state :line-overlimit)))))))))

(defthm fn-wire-feed-byte-reference-is-feed-byte
  (implies (fn-wire-statep wire-state)
           (equal (fn-wire-feed-byte-reference wire-state byte)
                  (fn-wire-feed-byte wire-state byte)))
  :hints (("Goal" :in-theory (enable fn-wire-feed-byte
                                      fn-wire-feed-byte-reference
                                      fn-wire-statep))))

(defthm fn-wire-feed-byte-matches-reference
  (implies (fn-wire-statep wire-state)
           (equal (fn-wire-feed-byte wire-state byte)
                  (fn-wire-feed-byte-reference wire-state byte)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-wire-feed-byte-reference-is-feed-byte)))))

(defun fn-wire-feed-proper (wire-state octets)
  (declare (xargs :guard (and (fn-wire-statep wire-state)
                              (fn-wire-octet-listp octets))
                  :verify-guards nil
                  :measure (acl2-count octets)))
  ; The public wrapper establishes fn-wire-octet-listp before calling this
  ; worker.  Once a boundary failure closes the connection, do not walk any
  ; arbitrary suffix that followed it.
  (if (or (not (consp octets))
          (equal (fn-wire-state-mode wire-state) :closed))
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

; A guard fact, not a rule: with the result record opaque the events field is
; still a true list whenever the record is.  Stated once, :rule-classes nil,
; and cited by the verify-guards of fn-wire-continue below.
(defthm fn-wire-result-events-of-a-true-list-is-a-true-list
  (implies (true-listp result)
           (true-listp (fn-wire-result-events result)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-wire-result-events))))

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
; the host-dispatch API (host/reader-host.lisp:91); fn-wire-feed remains a
; fixed-mode composition helper.
; Result fields are (state event unconsumed-octets), where event is NIL when
; the supplied octets contain no complete event.
(defun fn-wire-next-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 3)))

(defun fn-wire-next-state (x)
  (declare (xargs :guard t))
  (fn-wire-ag-car x))

(defun fn-wire-next-event (x)
  (declare (xargs :guard t))
  (fn-wire-ag-car (fn-wire-ag-cdr x)))

(defun fn-wire-next-unconsumed (x)
  (declare (xargs :guard t))
  (fn-wire-ag-car (fn-wire-ag-cdr (fn-wire-ag-cdr x))))

(defun fn-wire-make-next (wire-state event unconsumed)
  (list wire-state event unconsumed))


; Record lemmas for the next record: its shape and one accessor-of-constructor
; equality per field.  Below this point nothing opens the record.

(defthm fn-wire-next-shapep-of-fn-wire-make-next
  (fn-wire-next-shapep (fn-wire-make-next wire-state event unconsumed)))

(defthm fn-wire-next-state-of-fn-wire-make-next
  (equal (fn-wire-next-state (fn-wire-make-next wire-state event unconsumed))
         wire-state))

(defthm fn-wire-next-event-of-fn-wire-make-next
  (equal (fn-wire-next-event (fn-wire-make-next wire-state event unconsumed))
         event))

(defthm fn-wire-next-unconsumed-of-fn-wire-make-next
  (equal (fn-wire-next-unconsumed (fn-wire-make-next wire-state event unconsumed))
         unconsumed))

(in-theory (disable (:d fn-wire-next-shapep) (:d fn-wire-make-next) (:d fn-wire-next-state) (:d fn-wire-next-event) (:d fn-wire-next-unconsumed)))

; The chunk loop.  fn-wire-statep is established once, by fn-wire-next, before
; this loop starts; each iteration performs the constant-work per-byte step and
; an O(1) mode test.
(defun fn-wire-next-loop (wire-state octets)
  (declare (xargs :guard (fn-wire-statep wire-state)
                  :verify-guards nil
                  :measure (acl2-count octets)))
  (if (equal (fn-wire-state-mode wire-state) :closed)
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
            (fn-wire-next-loop (fn-wire-result-state one) (cdr octets))))))))

(defun fn-wire-next (wire-state octets)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-wire-statep wire-state))
      (fn-wire-make-next wire-state nil octets)
    (fn-wire-next-loop wire-state octets)))

; The earlier chunk loop, retained as the reference for the equality theorem
; below: it re-established fn-wire-statep on every byte.
(defun fn-wire-next-reference (wire-state octets)
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
        (let ((one (fn-wire-feed-byte-reference wire-state (car octets))))
          (if (consp (fn-wire-result-events one))
              (fn-wire-make-next (fn-wire-result-state one)
                                 (car (fn-wire-result-events one))
                                 (cdr octets))
            (fn-wire-next-reference (fn-wire-result-state one)
                                    (cdr octets))))))))

(defthm fn-wire-next-reference-is-next-loop
  (implies (fn-wire-statep wire-state)
           (equal (fn-wire-next-reference wire-state octets)
                  (fn-wire-next-loop wire-state octets)))
  :hints (("Goal"
           :induct (fn-wire-next-loop wire-state octets)
           :in-theory (e/d (fn-wire-next-loop fn-wire-next-reference)
                           (fn-wire-feed-byte
                            fn-wire-feed-byte-reference
                            fn-wire-statep)))))

(defthm fn-wire-next-loop-matches-reference
  (implies (fn-wire-statep wire-state)
           (equal (fn-wire-next-loop wire-state octets)
                  (fn-wire-next-reference wire-state octets)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-wire-next-reference-is-next-loop)))))

; The served path returns exactly what the recomputing reference returns, for
; every valid state and every chunk.  This is the theorem that lets the carried
; counters replace the per-byte state recognizer.
(defthm fn-wire-next-matches-reference
  (implies (fn-wire-statep wire-state)
           (equal (fn-wire-next wire-state octets)
                  (fn-wire-next-reference wire-state octets)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-wire-next-reference-is-next-loop))
           :in-theory (e/d (fn-wire-next)
                           (fn-wire-next-loop
                            fn-wire-next-reference
                            fn-wire-statep)))))

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

; The fixed-mode composition helper's partition law.  It is the induction that
; the served-path partition theorem in wire-invariants.lisp uses, through
; fn-wire-drive-is-feed-proper.
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
                    right)))))
  ; This is the one theorem in the book that is *about* the pairing inside the
  ; result record rather than about a field of it, so it opens that record
  ; locally.  Nothing is exported open: the export event below withdraws the
  ; record again for every includer.
  :hints (("Goal" :in-theory (enable fn-wire-make-result
                                     fn-wire-result-state
                                     fn-wire-result-events))))

; -----------------------------------------------------------------------------
; Executable guard closure

(verify-guards fn-wire-octetp)
(verify-guards fn-wire-octet-listp)
(verify-guards fn-wire-octet-linesp)
(verify-guards fn-wire-stuff-line)
(verify-guards fn-wire-unstuff-line)
(verify-guards fn-wire-reverse-octets-aux)
(verify-guards fn-wire-reverse-octets)
(verify-guards fn-wire-reverse-lines-aux)
(verify-guards fn-wire-reverse-lines)
(verify-guards fn-wire-append)
(verify-guards fn-wire-outbound-ok)
(verify-guards fn-wire-outbound-refused)
(verify-guards fn-wire-outbound-okp)
(verify-guards fn-wire-outbound-octets)
(verify-guards fn-wire-outbound-reason)
(verify-guards fn-wire-outbound-lines-aux)
(verify-guards fn-wire-outbound-lines)
(verify-guards fn-wire-render-lines)
(verify-guards fn-wire-render-block)
(verify-guards fn-wire-prefixp)
(verify-guards fn-wire-outbound-command-line-aux)
(verify-guards fn-wire-outbound-command-line)
(verify-guards fn-wire-render-feed-command)
(verify-guards fn-wire-modep)
(verify-guards fn-wire-make-state)
(verify-guards fn-wire-line-cost)
(verify-guards fn-wire-lines-size)
(verify-guards fn-wire-statep)
(verify-guards fn-wire-initial-state)
(verify-guards fn-wire-make-result)
(verify-guards fn-wire-command-event)
(verify-guards fn-wire-article-event)
(verify-guards fn-wire-reject-event)
(verify-guards fn-wire-close)
(verify-guards fn-wire-begin-article-admissiblep)
(verify-guards fn-wire-article-line-limit)
(verify-guards fn-wire-begin-article-with-line-limit)
(verify-guards fn-wire-begin-article)
(verify-guards fn-wire-begin-article-refusedp)
(verify-guards fn-wire-after-line)
(verify-guards fn-wire-feed-byte)
(verify-guards fn-wire-feed-byte-reference)
(verify-guards fn-wire-feed-proper)
(verify-guards fn-wire-feed)
(verify-guards fn-wire-continue
  :hints (("Goal" :use ((:instance fn-wire-result-events-of-a-true-list-is-a-true-list)))))
(verify-guards fn-wire-make-next)
(verify-guards fn-wire-next-loop)
(verify-guards fn-wire-next)
(verify-guards fn-wire-next-reference)

; ---------------------------------------------------------------------------
; Export theory
;
; What leaves this book enabled: the keystones, the record lemmas, the
; list-recursive vocabulary proofs induct on (fn-wire-octet-listp,
; fn-wire-octet-linesp, fn-wire-lines-size, fn-wire-reverse-octets) and the
; total fn-wire-ag- selectors.  Every record accessor, constructor and shape
; was withdrawn at its record above.  Withdrawn here: the state recognizer,
; the initial state and every transition, so an includer computes with them
; but never inherits their unfolding.

(deftheory fn-wire-step-vocabulary
  '(fn-wire-statep fn-wire-modep fn-wire-initial-state
    fn-wire-line-cost fn-wire-close
    fn-wire-begin-article-admissiblep fn-wire-article-line-limit
    fn-wire-begin-article-with-line-limit
    fn-wire-begin-article
    fn-wire-begin-article-refusedp
    fn-wire-after-line fn-wire-feed-byte fn-wire-feed-byte-reference
    fn-wire-feed-proper fn-wire-feed fn-wire-continue
    fn-wire-next-loop fn-wire-next fn-wire-next-reference
    fn-wire-command-event fn-wire-article-event fn-wire-reject-event
    fn-wire-stuff-line fn-wire-unstuff-line
    fn-wire-outbound-okp fn-wire-outbound-octets fn-wire-outbound-reason
    fn-wire-outbound-lines fn-wire-render-block fn-wire-render-feed-command))

(in-theory (disable fn-wire-step-vocabulary))
