; Coordinate/parser controls, not an initialized native campaign witness.
(in-package "ACL2")
(include-book "../sim/native-device-cut")
(include-book "native-device-bindings-unit")

(defconst *fn2-cut-control* (list *fn2-nde-write-take* '(:ack 1)))
(assert-event
 (and
  (eq (fn2-nde-cut-position '(:boundary 1 "device-submit" 4 7 t)
        *fn2-cut-control* nil :fdatasync) :before-submit)
  (eq (fn2-nde-cut-position '(:boundary 1 "device-syscall" 4 7 t)
        *fn2-cut-control* (take 1 *fn2-nde-write-physical*) :fdatasync) :before-physical)
  (eq (fn2-nde-cut-position '(:boundary 1 "device-syscall-return" 4 7 t)
        *fn2-cut-control* *fn2-nde-write-physical* :fdatasync) :after-physical)
  (eq (fn2-nde-cut-position '(:boundary 1 "device-return" 4 7 t)
        *fn2-cut-control* *fn2-nde-write-physical* :fdatasync) :before-terminal-post)))
(assert-event
 (and
  (eq (fn2-nde-cut-position '(:boundary 1 "device-return" 4 8 t)
       *fn2-cut-control* *fn2-nde-write-physical* :fdatasync) :cut-identity)
  (eq (fn2-nde-cut-position '(:boundary 1 "device-syscall-return" 4 7 t)
       *fn2-cut-control* (take 2 *fn2-nde-write-physical*) :fdatasync) :cut-return-position)
  (eq (fn2-nde-cut-position '(:boundary 1 "device-syscall" 4 7 t)
       *fn2-cut-control* *fn2-nde-write-physical* :fdatasync) :cut-begin-position)
  (eq (fn2-nde-cut-position '(:boundary 1 "device-return" 4 7 t)
       (append *fn2-cut-control* (list *fn2-nde-write-post*))
       *fn2-nde-write-physical* :fdatasync) :cut-identity)
  (eq (fn2-nde-cut-position '(:boundary 1 "tls-send" 4 7 t)
       *fn2-cut-control* *fn2-nde-write-physical* :fdatasync) :unmapped-cut)))
(assert-event
 (and
  (equal (fn2-nde-cut-prefix '((:boundary 1 "take" nil nil nil)
                             (:boundary 2 "device-submit" 4 7 t)) 0 nil nil)
         '( :ok nil nil (:boundary 2 "device-submit" 4 7 t)))
  (eq (mv-nth 0 (fn2-nde-cut-prefix '((:boundary 2 "device-submit" 4 7 t)) 0 nil nil)) :malformed-cut-capture)
  (eq (mv-nth 0 (fn2-nde-cut-prefix '((:boundary 1 "device-submit" 4 7 t) (:begin 1)) 0 nil nil)) :after-cut)
  (eq (mv-nth 0 (fn2-nde-cut-prefix '((:boundary 1 "device-submit" 4 7 nil)) 0 nil nil)) :missing-cut)))
; Shape/coordinate controls alone cannot produce a successful replay: this
; forged empty control prefix fails before any core transition is attempted.
(assert-event
 (not (eq (car (fn2-native-device-cut-replay
                '((:profile nil) (:boot-start nil 1 :ok)
                  (:boundary 1 "device-return" 4 7 t)) 17 :fdatasync)) :pass)))
