(in-package "ACL2")
(include-book "../books/columns-call-guards")

(defcolumns fn2-guard-output ((value :u60)))
(defcolumns fn2-guard-input ((word :u8))
 :extra-fields
 ((fn2-guard-limit :type (unsigned-byte 8) :initially 0
   :why "Fixture scalar observation from a read-only input.")
  (fn2-guard-fixed :type (array (unsigned-byte 8) (2)) :initially 0
   :why "Fixture fixed-array observation with its public length bridge.")))
(make-event
 (let ((world (w state)))
  (value `(defconst *fn2-guard-incoming-theory* ',(current-theory :here)))))

; The input is read-only. All three numeric observations must use their
; public type/bound contracts while the actual setter guard is verified.
(defun fn2-guard-copy (i fn2-guard-output fn2-guard-input)
 (declare (xargs :stobjs (fn2-guard-output fn2-guard-input)
  :guard (and (fn2-guard-output-wfp fn2-guard-output)
              (fn2-guard-input-wfp fn2-guard-input) (natp i)
              (< i (fn2-guard-output-rows fn2-guard-output))
              (< i (fn2-guard-input-rows fn2-guard-input)))
  :guard-hints ((fn2-columns-guard-hint '(fn2-guard-output fn2-guard-input)
                                       nil nil world))))
 (fn2-guard-output-set-value i
  (+ (fn2-guard-input-word i fn2-guard-input)
     (fn2-guard-limit fn2-guard-input) (fn2-guard-fixedi 0 fn2-guard-input))
  fn2-guard-output))
(assert-event (eq (symbol-class 'fn2-guard-copy (w state)) :common-lisp-compliant))
(assert-event
 (let* ((world (w state))
        (tables '(fn2-guard-output fn2-guard-input))
        (readers (fn2-columns-getter-runes tables world))
        (hint (fn2-columns-guard-hint tables nil nil world))
        (closed (caddr (cadr hint)))
        (opened (fn2-columns-guard-hint tables nil '(fn2-guard-input-word) world)))
  (and (subsetp-eq '(fn2-guard-output-value fn2-guard-output-rows
                    fn2-guard-input-word fn2-guard-input-rows
                    fn2-guard-limit fn2-guard-fixedi fn2-guard-fixed-length) readers)
       (not (member-eq 'fn2-guard-output-set-value readers))
       (not (member-eq 'fn2-guard-input-word-bound closed))
       (not (member-eq 'fn2-guard-fixedi-fixed-natp closed))
       (member-eq 'nth closed)
       (not (member-eq 'fn2-guard-input-word (caddr (cadr opened))))
       ; Hints change proof theory only; they supply no guard or proof bypass.
       (equal (len hint) 2) (eq (car hint) :in-theory)
       (subsetp-equal *fn2-guard-incoming-theory* (current-theory :here)))))

; A missing input index bound has an actual counterexample. The hint does
; not make an out-of-range input read safe, even when the output row exists.
(defun fn2-guard-index-control (fn2-guard-output fn2-guard-input)
 (declare (xargs :stobjs (fn2-guard-output fn2-guard-input)))
 (let* ((fn2-guard-output (fn2-guard-output-init 1 fn2-guard-output))
        (fn2-guard-input (fn2-guard-input-init 0 fn2-guard-input)))
  (mv (and (fn2-guard-outputp fn2-guard-output) (fn2-guard-output-wfp fn2-guard-output)
           (fn2-guard-inputp fn2-guard-input) (fn2-guard-input-wfp fn2-guard-input)
           (< 0 (fn2-guard-output-rows fn2-guard-output))
           (not (< 0 (fn2-guard-input-rows fn2-guard-input))))
      fn2-guard-output fn2-guard-input)))
(defun fn2-guard-hints-unit ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-guard-output
  (mv-let (ok fn2-guard-output)
   (with-local-stobj fn2-guard-input
    (mv-let (ok fn2-guard-output fn2-guard-input)
     (fn2-guard-index-control fn2-guard-output fn2-guard-input)
     (mv ok fn2-guard-output)))
   ok)))
(assert-event (fn2-guard-hints-unit))

; The default discovers both read-only observations and a stateful producer's
; proved public boundary. The producer is deliberately left enabled here.
(defun fn2-guard-increment (i fn2-guard-output)
 (declare (xargs :stobjs fn2-guard-output
  :guard (and (fn2-guard-output-wfp fn2-guard-output) (natp i)
              (< i (fn2-guard-output-rows fn2-guard-output)))))
 (fn2-guard-output-set-value i 1 fn2-guard-output))
(fn2-guard-output-preserves fn2-guard-increment (i fn2-guard-output) :disable nil)
(defun fn2-guard-auto-copy (i fn2-guard-output fn2-guard-input)
 (declare (xargs :stobjs (fn2-guard-output fn2-guard-input)
  :guard (and (fn2-guard-output-wfp fn2-guard-output)
              (fn2-guard-input-wfp fn2-guard-input) (natp i)
              (< i (fn2-guard-output-rows fn2-guard-output))
              (< i (fn2-guard-input-rows fn2-guard-input)))
  :guard-hints ((fn2-columns-call-guard-hint 'fn2-guard-auto-copy nil nil world))))
 (let ((fn2-guard-output (fn2-guard-increment i fn2-guard-output)))
  (fn2-guard-output-set-value i (fn2-guard-input-word i fn2-guard-input) fn2-guard-output)))
(assert-event (eq (symbol-class 'fn2-guard-auto-copy (w state)) :common-lisp-compliant))
(assert-event
 (let* ((world (w state))
        (hint (fn2-columns-call-guard-hint 'fn2-guard-auto-copy nil nil world))
        (closed (caddr (cadr hint)))
        (opened (fn2-columns-call-guard-hint 'fn2-guard-auto-copy nil
                    '(fn2-guard-input-word fn2-guard-increment) world)))
  (and (subsetp-eq '(fn2-guard-input-word fn2-guard-input-rows fn2-guard-increment) closed)
       (not (member-eq 'fn2-guard-auto-copy closed))
       (not (member-eq 'fn2-guard-input-word-bound closed))
       (not (member-eq 'fn2-guard-increment-preserves-wfp closed))
       (not (intersectp-eq '(fn2-guard-input-word fn2-guard-increment) (caddr (cadr opened)))))))
