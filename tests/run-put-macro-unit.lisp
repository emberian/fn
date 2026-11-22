; Check the macros generated from the real run schemas at expansion time.
(in-package "ACL2")
(include-book "../books/machines-c-bind")
(include-book "std/testing/must-fail" :dir :system)

; Named inputs may arrive out of order. The digest shorthand expands to
; 32 bytes. A grant-set has explicit empty MID and group-number spans.
(make-event
 (er-let* ((form
            (macroexpand1
             '(fn2-outcome-put tx slot (request ds dg off)
                (principal pid) (operation op) (id-source source)
                (event :event 0) (outcome code) (verb verb) (mid ds dg 0 0) (numbers ns ng 0 0)
                :owner (kind owner gen) fn2-core)
             'fn2-run-put-macro-test state)))
   (value `(assert-event
             (equal ',form '(fn2-outcome-put-row tx slot
                            ':value pid ':value op ':value source
                            ds dg off 32 ':value code ':event 0 ':value verb
                            ds dg 0 0 ns ng 0 0 kind owner gen fn2-core))))))

; The accept fold computes NUMBER, so GROUP is its only caller-owned input.
(make-event
 (er-let* ((form (macroexpand1 '(fn2-group-counts-accept tx slot (group gid) fn2-core)
                               'fn2-run-put-macro-test state)))
   (value `(assert-event (equal ',form '(fn2-group-counts-put-accept tx slot ':value gid fn2-core))))))

(defmacro fn2-run-put-must-refuse (call)
  `(must-fail
    (make-event
     (er-let* ((form (macroexpand1 ',call 'fn2-run-put-macro-test state)))
       (value (list 'value-triple (list 'quote form)))))
    :expected :any))

(fn2-run-put-must-refuse
 (fn2-outcome-put tx slot (principal pid) (operation op)
  (request ds dg off) (outcome code) (event :event 0) (verb verb)
  (mid ds dg 0 0) (numbers ns ng 0 0) :owner (kind owner gen) fn2-core))

(fn2-run-put-must-refuse
 (fn2-outcome-put tx slot (principal pid) (operation op) (id-source source)
  (request ds dg off) (outcome code) (event :event 0) (verb verb)
  (mid ds dg 0 0) (numbers ns ng 0 0) (id-source other) :owner (kind owner gen) fn2-core))

(fn2-run-put-must-refuse
 (fn2-outcome-put tx slot (principal pid) (operation op) (id-source)
  (request ds dg off) (outcome code) (event :event 0) (verb verb)
  (mid ds dg 0 0) (numbers ns ng 0 0) :owner (kind owner gen) fn2-core))
