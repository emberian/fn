(in-package "ACL2")
(include-book "../sim/native-device-bindings")
(defconst *fn2-nde-write-take*
 (list :take 4 7 *fn2-action-write* 0 0 2 3 0 3 100 0 0 0 0 0 0))
(defconst *fn2-nde-write-post*
 (list :post 0 4 7 *fn2-event-write-result* *fn2-outcome-failed* *fn2-reason-uncertain*
       2 0 0 0 '(0 0 0 0 0) nil))
(defconst *fn2-nde-write-physical*
 '((:submit 1 (17 4 7 :write 100 3 (8 9 10) 0 1 1)) (:begin 1) (:return 1 2 0 nil)))
(assert-event
 (and (fn2-nde-take-descriptor-p *fn2-nde-write-take* '(17 4 7 :write 100 3 (8 9 10) 0 1 1) :fdatasync)
      (not (fn2-nde-take-descriptor-p *fn2-nde-write-take* '(17 4 8 :write 100 3 (8 9 10) 0 1 1) :fdatasync))
      (not (fn2-nde-take-descriptor-p *fn2-nde-write-take* '(17 4 7 :write 101 3 (8 9 10) 0 1 1) :fdatasync))
      (not (fn2-nde-take-descriptor-p *fn2-nde-write-take* '(17 4 7 :write 100 2 (8 9) 0 1 1) :fdatasync))))
(assert-event
 (and (fn2-nde-post-p *fn2-nde-write-post* (list *fn2-nde-write-take*) *fn2-nde-write-physical* :fdatasync)
      (not (fn2-nde-post-p (update-nth 7 3 *fn2-nde-write-post*) (list *fn2-nde-write-take*) *fn2-nde-write-physical* :fdatasync))
      (not (fn2-nde-post-p *fn2-nde-write-post* (list *fn2-nde-write-take*) nil :fdatasync))
      (not (fn2-nde-post-p *fn2-nde-write-post* (list *fn2-nde-write-take*) (take 2 *fn2-nde-write-physical*) :fdatasync))))
(defconst *fn2-nde-read-take*
 (list :take 5 7 *fn2-action-read* 0 0 2 3 0 3 100 0 0 0 0 0 0))
(defconst *fn2-nde-read-post*
 (list :post 0 5 7 *fn2-event-read-result* *fn2-outcome-short* *fn2-reason-none*
       2 0 0 0 '(0 0 0 0 0) '(8 9)))
(assert-event
 (let ((records '((:submit 2 (17 5 7 :read 100 3 nil 0 1 1)) (:begin 2) (:return 2 2 0 (8 9)))))
  (and (fn2-nde-post-p *fn2-nde-read-post* (list *fn2-nde-read-take*) records :fdatasync)
       (not (fn2-nde-post-p (update-nth 12 '(8 10) *fn2-nde-read-post*) (list *fn2-nde-read-take*) records :fdatasync)))))
; Only an explicit unsupported FUA request explains a device Post without a
; physical job. An ordinary failed Write still requires its physical evidence.
(assert-event
 (let* ((fua (update-nth 11 1 *fn2-nde-write-take*))
        (failed (update-nth 7 0 (update-nth 6 *fn2-reason-io* *fn2-nde-write-post*))))
  (and (fn2-nde-post-p failed (list fua) nil :fdatasync)
       (not (fn2-nde-post-p failed (list *fn2-nde-write-take*) nil :fdatasync)))))

; Removed descriptor fields cannot be accepted as an apparently matching job.
(defun fn2-nde-removed-fields-rejected (fields d take)
 (declare (xargs :verify-guards nil))
 (if (atom fields) t
  (and (not (fn2-nde-take-descriptor-p take (update-nth (car fields) nil d) :fdatasync))
       (fn2-nde-removed-fields-rejected (cdr fields) d take))))
(assert-event
 (fn2-nde-removed-fields-rejected '(0 1 2 3 4 5 6 7 8 9)
    '(17 4 7 :write 100 3 (8 9 10) 0 1 1) *fn2-nde-write-take*))
; Failed raw Writes retain the shared IO reason; they are not short-success.
(assert-event
 (let ((post (update-nth 7 0 (update-nth 6 *fn2-reason-io* *fn2-nde-write-post*)))
       (physical '((:submit 1 (17 4 7 :write 100 3 (8 9 10) 0 1 1)) (:begin 1) (:return 1 -1 5 nil))))
  (and (fn2-nde-post-p post (list *fn2-nde-write-take*) physical :fdatasync)
       (not (fn2-nde-post-p *fn2-nde-write-post* (list *fn2-nde-write-take*) physical :fdatasync)))))

; Equal Write contents cannot excuse a wrong physical address or backing slab.
; These are scalar controls; actual replay obtains address/length from the
; actual host-op-span authorization, not from these literal fixture values.
(assert-event
 (let ((d '(17 4 7 :write 100 3 (8 9 10) 20 1 1)))
  (and (fn2-nde-loan-span-p d :ok 20 3)
       (not (fn2-nde-loan-span-p (update-nth 7 21 d) :ok 20 3))
       (not (fn2-nde-loan-span-p (update-nth 8 2 d) :ok 20 3))
       (not (fn2-nde-loan-span-p d :owner 20 3))
       (not (fn2-nde-loan-span-p d :ok 20 2))
       (not (fn2-nde-take-descriptor-p *fn2-nde-write-take* (update-nth 8 2 d) :fdatasync)))))
(assert-event
 (let ((d '(17 5 7 :read 100 3 nil 20 1 1)))
  (and (fn2-nde-loan-span-p d :ok 20 3)
       (not (fn2-nde-loan-span-p (update-nth 7 21 d) :ok 20 3))
       (not (fn2-nde-loan-span-p (update-nth 8 2 d) :ok 20 3)))))

; The selected adapter emits a proper 13-field device Post with no peer.
; Fail closed on malformed captures rather than defaulting missing NIL fields.
(assert-event
 (and (not (fn2-nde-post-p (take 10 *fn2-nde-write-post*)
              (list *fn2-nde-write-take*) *fn2-nde-write-physical* :fdatasync))
      (not (fn2-nde-post-p (append *fn2-nde-write-post* '(extra))
              (list *fn2-nde-write-take*) *fn2-nde-write-physical* :fdatasync))
      (not (fn2-nde-post-p (append *fn2-nde-write-post* 'dotted)
              (list *fn2-nde-write-take*) *fn2-nde-write-physical* :fdatasync))
      (not (fn2-nde-post-p (update-nth 10 1 *fn2-nde-write-post*)
              (list *fn2-nde-write-take*) *fn2-nde-write-physical* :fdatasync))
      (not (fn2-nde-post-p (update-nth 11 '(1 0 0 0 0) *fn2-nde-write-post*)
              (list *fn2-nde-write-take*) *fn2-nde-write-physical* :fdatasync))))
