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
  (eq (car (mv-list 4 (fn2-nde-cut-prefix '((:boundary 2 "device-submit" 4 7 t)) 0 nil nil))) :malformed-cut-capture)
  (eq (car (mv-list 4 (fn2-nde-cut-prefix '((:boundary 1 "device-submit" 4 7 t) (:begin 1)) 0 nil nil))) :after-cut)
  (eq (car (mv-list 4 (fn2-nde-cut-prefix '((:boundary 1 "device-submit" 4 7 nil)) 0 nil nil))) :missing-cut)))
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

; Concurrent device coordinates. Jobs: a Write (slot 4), Reads (slots 5, 6)
; and a Fence (slot 8), each with its own take in the control prefix.
(defconst *fn2-cut-w4* '(17 4 7 :write 100 3 (8 9 10) 0 1 1))
(defconst *fn2-cut-r5* '(17 5 7 :read 100 3 nil 0 1 1))
(defconst *fn2-cut-r6* '(17 6 7 :read 100 3 nil 0 1 1))
(defconst *fn2-cut-f8* '(17 8 7 :fence 0 0 nil 0 1 1))
(defconst *fn2-cut-takes*
 (list *fn2-nde-write-take* '(:ack 1) *fn2-nde-read-take* '(:ack 1)
       (update-nth 1 6 *fn2-nde-read-take*) '(:ack 1)
       (update-nth 3 *fn2-action-fence* (update-nth 1 8 *fn2-nde-write-take*)) '(:ack 1)))
(defun fn2-cut-at (label slot records)
 (declare (xargs :verify-guards nil))
 (fn2-nde-cut-position (list :boundary 9 label slot 7 t) *fn2-cut-takes* records :fdatasync))

; Before syscall: any job ready under the hazards, not only the oldest. A
; Read may begin beside a Read, ahead of an earlier queued Read, and beside a
; Fence once the Writes before it have returned.
(assert-event
 (and (eq (fn2-cut-at "device-syscall" 6
           (list (list :submit 1 *fn2-cut-r5*) (list :submit 2 *fn2-cut-r6*) '(:begin 1)))
          :before-physical)
      (eq (fn2-cut-at "device-syscall" 6
           (list (list :submit 1 *fn2-cut-r5*) (list :submit 2 *fn2-cut-r6*)))
          :before-physical)
      (eq (fn2-cut-at "device-syscall" 6
           (list (list :submit 1 *fn2-cut-w4*) '(:begin 1) '(:return 1 3 0 nil)
                 (list :submit 2 *fn2-cut-f8*) '(:begin 2) (list :submit 3 *fn2-cut-r6*)))
          :before-physical)
      (eq (fn2-cut-at "device-syscall" 8
           (list (list :submit 1 *fn2-cut-r5*) (list :submit 2 *fn2-cut-f8*) '(:begin 1)))
          :before-physical)))
; Teeth: the same coordinate is refused once one ordered job is unreturned.
(assert-event
 (let ((w4-r6 (list (list :submit 1 *fn2-cut-w4*) (list :submit 2 *fn2-cut-r6*) '(:begin 1)))
       (r5-w4 (list (list :submit 1 *fn2-cut-r5*) (list :submit 2 *fn2-cut-w4*)))
       (f8-w4 (list (list :submit 1 *fn2-cut-f8*) (list :submit 2 *fn2-cut-w4*) '(:begin 1)))
       (f8-w4-r6 (list (list :submit 1 *fn2-cut-f8*) (list :submit 2 *fn2-cut-w4*)
                       (list :submit 3 *fn2-cut-r6*) '(:begin 1))))
  (and (eq (fn2-cut-at "device-syscall" 6 w4-r6) :cut-begin-position)
       (eq (fn2-cut-at "device-syscall" 6 (append w4-r6 '((:return 1 3 0 nil)))) :before-physical)
       (eq (fn2-cut-at "device-syscall" 4 r5-w4) :cut-begin-position)
       (eq (fn2-cut-at "device-syscall" 4 (append r5-w4 '((:begin 1)))) :cut-begin-position)
       (eq (fn2-cut-at "device-syscall" 4 (append r5-w4 '((:begin 1) (:return 1 2 0 (8 9)))))
           :before-physical)
       (eq (fn2-cut-at "device-syscall" 4 f8-w4) :cut-begin-position)
       (eq (fn2-cut-at "device-syscall" 4 (append f8-w4 '((:return 1 0 0 nil)))) :before-physical)
       (eq (fn2-cut-at "device-syscall" 6 f8-w4-r6) :cut-begin-position)
       (eq (fn2-cut-at "device-syscall" 6 (append f8-w4-r6 '((:return 1 0 0 nil) (:begin 2) (:return 2 3 0 nil))))
           :before-physical))))

; After syscall: until this boundary the worker still holds its job, so only
; unordered jobs may begin after its return; any job may return.
(assert-event
 (let ((r5-r6 (list (list :submit 1 *fn2-cut-r5*) (list :submit 2 *fn2-cut-r6*)
                    '(:begin 1) '(:begin 2) '(:return 1 2 0 (8 9))))
       (r5-f8 (list (list :submit 1 *fn2-cut-r5*) (list :submit 2 *fn2-cut-f8*)
                    '(:begin 1) '(:return 1 2 0 (8 9)) '(:begin 2) '(:return 2 0 0 nil)))
       (f8-r6 (list (list :submit 1 *fn2-cut-f8*) (list :submit 2 *fn2-cut-r6*)
                    '(:begin 1) '(:return 1 0 0 nil) '(:begin 2))))
  (and (eq (fn2-cut-at "device-syscall-return" 5 r5-r6) :after-physical)
       (eq (fn2-cut-at "device-syscall-return" 5 (append r5-r6 '((:return 2 2 0 (8 9))))) :after-physical)
       (eq (fn2-cut-at "device-syscall-return" 5 r5-f8) :after-physical)
       (eq (fn2-cut-at "device-syscall-return" 8 f8-r6) :after-physical))))
; Teeth: a job ordered with the returned one, or an unsubmitted id, begins.
(assert-event
 (let ((r5-w4 (list (list :submit 1 *fn2-cut-r5*) (list :submit 2 *fn2-cut-w4*)
                    '(:begin 1) '(:return 1 2 0 (8 9))))
       (w4-r6 (list (list :submit 1 *fn2-cut-w4*) (list :submit 2 *fn2-cut-r6*)
                    '(:begin 1) '(:return 1 3 0 nil)))
       (f8-w4 (list (list :submit 1 *fn2-cut-f8*) (list :submit 2 *fn2-cut-w4*)
                    '(:begin 1) '(:return 1 0 0 nil))))
  (and (eq (fn2-cut-at "device-syscall-return" 5 r5-w4) :after-physical)
       (eq (fn2-cut-at "device-syscall-return" 5 (append r5-w4 '((:begin 2)))) :cut-return-position)
       (eq (fn2-cut-at "device-syscall-return" 4 w4-r6) :after-physical)
       (eq (fn2-cut-at "device-syscall-return" 4 (append w4-r6 '((:begin 2)))) :cut-return-position)
       (eq (fn2-cut-at "device-syscall-return" 8 f8-w4) :after-physical)
       (eq (fn2-cut-at "device-syscall-return" 8 (append f8-w4 '((:begin 2)))) :cut-return-position)
       (eq (fn2-cut-at "device-syscall-return" 5 (append r5-w4 '((:begin 9)))) :cut-return-position))))
