; fn: host wrappers over books/config for the Python bridge (packet R1).
;
; `run_store.py initialize' writes one default configuration record through
; these entry points and `recover' replays it through them.  No value here is
; computed by Python: the record octets, the generation and the served group
; table all come out of `books/config'.  A host wrapper never decides anything
; a book does not already decide.

(in-package "ACL2")
(include-book "../books/config-invariants")

(defun fn-cfg-host-line-ceiling ()
  ; RFC 3977 section 3.1's initial line, as the admissibility argument.
  ; OPEN (packet R5): `books/nntp-syntax' owns
  ; `*fn-nntp-max-initial-line-octets*'; this wrapper repeats the number until
  ; the per-generation projection verdict lands and the node supplies it.
  ; Recorded in planning/lanes/HANDOFF-w4-config-records.md.
  (declare (xargs :guard t))
  510)

(defun fn-cfg-host-default-octets ()
  (declare (xargs :guard t))
  (fn-cfg-encode *fn-cfg-default-record*))

(defun fn-cfg-host-group-name-octets (names)
  (declare (xargs :guard t))
  (if (consp names)
      (cons (fn-record-string-octets (car names))
            (fn-cfg-host-group-name-octets (cdr names)))
    nil))

(defun fn-cfg-host-replay-octets (octets)
  ; Decode one durable configuration record, replay it, and return
  ; (generation group-name-octets capacity), or :bad.  Fail closed: an
  ; undecodable record, an unknown record kind and an inadmissible change are
  ; all :bad here and a refusal at the boundary, never a silent default.
  (declare (xargs :guard t))
  (let ((parsed (fn-cfg-decode-exact octets)))
    (if (not (fn-record-parse-okp parsed))
        :bad
      (let ((cfg (fn-config-replay 0 (fn-cfg-host-line-ceiling)
                                   (list (fn-record-parse-value parsed)))))
        (if (equal cfg :fault)
            :bad
          (list (fn-cfg-generation cfg)
                (fn-cfg-host-group-name-octets
                 (fn-cfg-group-names (fn-cfg-value cfg)
                                     (fn-cfg-generation cfg)))
                (fn-cfg-capacity (fn-cfg-value cfg))))))))
