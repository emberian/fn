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
  (equal (mv-list 4 (fn2-nde-cut-prefix '((:boundary 1 "take" nil nil nil)
                                         (:boundary 2 "device-submit" 4 7 t)) 0 nil nil))
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

; A concurrent enqueue after the selected physical return is not a second
; physical operation. A later begin would contradict this worker coordinate.
(assert-event
 (let ((queued (append *fn2-nde-write-physical*
                '((:submit 2 (17 5 8 :write 200 1 (9) 0 1 1))))))
  (and (eq (fn2-nde-cut-position '(:boundary 4 "device-syscall-return" 4 7 t)
             *fn2-cut-control* queued :fdatasync) :after-physical)
       (eq (fn2-nde-cut-position '(:boundary 4 "device-syscall-return" 4 7 t)
             *fn2-cut-control* (append queued '((:begin 2))) :fdatasync) :cut-return-position))))

; The selected post follows the matching terminal in the control stream.
; An earlier post, a recycled slot, or a different read payload cannot witness it.
(assert-event
 (let* ((cut '(:boundary 8 "post" 5 7 t))
        (records '((:submit 2 (17 5 7 :read 100 3 nil 0 1 1))
                   (:begin 2) (:return 2 2 0 (8 9))))
        (prefix (list *fn2-nde-read-take* '(:ack 1)))
        (trace (append prefix (list *fn2-nde-read-post*))))
  (and (eq (fn2-nde-cut-position cut trace records :fdatasync) :after-terminal-post)
       (eq (fn2-nde-cut-position cut prefix records :fdatasync) :cut-post-position)
       (eq (fn2-nde-cut-position (update-nth 4 8 cut) trace records :fdatasync) :cut-identity)
       (eq (fn2-nde-cut-position cut (append trace (list *fn2-nde-write-post*)) records :fdatasync)
           :cut-post-position)
       (eq (fn2-nde-cut-position cut (append trace (list *fn2-nde-read-post*)) records :fdatasync)
           :cut-post-position)
       (eq (fn2-nde-cut-position cut trace (butlast records 1) :fdatasync) :cut-post-position)
       (eq (fn2-nde-cut-position cut (append prefix (list (update-nth 12 '(8 10) *fn2-nde-read-post*)))
                                 records :fdatasync) :cut-post-position))))
