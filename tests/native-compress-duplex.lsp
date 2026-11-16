;;; Backend duplex gate, loaded after native-compress-input-prefix.lsp in the
;;; SAME qualified served image. No listener, login, or public admission claim.
;;; The input fixture uses actual Receive/EAGAIN/core-post. Its callback issues
;;; three actual Send loans over the SAME C stream and private socket pair.
(in-package "ACL2")

(defun fn2-native-compress-fixture-hex (octets)
 (format nil "~(~{~2,'0x~}~)" (coerce octets 'list)))

(defun fn2-native-compress-duplex-replies (host cap peer)
 (let ((rows nil) (expected-tx 0)
       (transport (fn2-native-compress-transport (fn2-ncap-compress cap))))
  ;; No codec reopen/rebind between replies. A repeated reply exercises the
  ;; encoder dictionary retained by the peer's one persistent inflater.
  (dolist (text '("201 backend ready" "201 backend ready" "205 closing"))
   (let* ((plain (concatenate '(simple-array (unsigned-byte 8) (*))
                   (map '(vector (unsigned-byte 8)) #'char-code text) #(13 10)))
          (core (fn2-nhost-core host)) (wire nil))
    (multiple-value-bind (reserved range range-gen updated) (fn2-core-reserve 0 1 0 1 core)
     (assert (eq reserved :ok)) (setf core updated)
     (loop for byte across plain for offset from 0
      do (multiple-value-bind (written updated)
             (fn2-core-write range range-gen offset byte 1 0 1 core)
           (assert (eq written :ok)) (setf core updated)))
     (multiple-value-bind (issued slot generation updated)
         (fn2-issue-send 1 (fn2-ncap-nonce cap) range range-gen 0 (length plain) 1 1 0 1 0 core)
      (assert (eq issued :ok)) (setf (fn2-nhost-core host) updated)
      (fn2-n-take host)
      (let ((op (aref (fn2-nhost-ops host) slot)))
       (assert (and (= (fn2-nop-kind op) *fn2-action-send*)
                    (= (fn2-nop-gen op) generation)
                    (eq transport (fn2-native-compress-transport (fn2-ncap-compress cap)))))
       ;; Seven-byte private encoder output requires repeated real codec/drain
       ;; turns; each turn is selected and observed by the actual ACL2 caller.
       (dotimes (turn 256)
        (declare (ignore turn))
        (when (= (fn2-nop-state op) +fn2-n-completed+) (return))
        (fn2-n-start-ready host slot cap))
       (incf expected-tx (length plain))
       (assert (and (= (fn2-nop-state op) +fn2-n-completed+)
                    (= (fn2-nop-outcome op) *fn2-outcome-done*)
                    (= (fn2-nop-reason op) *fn2-reason-none*)
                    (= (fn2-nop-count op) (length plain))
                    (= (fn2-ncap-tx cap) expected-tx)))
       (fn2-n-post-completions host)
       (let ((post (car (last (fn2-n-trace-list host)))))
        (assert (equal post
                 (list :post 0 slot generation *fn2-event-send-result*
                   *fn2-outcome-done* *fn2-reason-none* (length plain) 0 0
                   *fn2-peer-family-none* '(0 0 0 0 0) (coerce plain 'list))))))))
    ;; The peer independently receives wire bytes, rather than inspecting the
    ;; codec's private output window or equating app count with wire count.
    (let ((buffer (make-array 256 :element-type '(unsigned-byte 8))))
     (sb-sys:with-pinned-objects (buffer)
      (loop repeat 64
       do (multiple-value-bind (count errno)
              (fn2-native-recv peer (sb-sys:vector-sap buffer) (length buffer))
            (cond ((plusp count)
                   (setf wire (nconc wire (coerce (subseq buffer 0 count) 'list))))
                  ((and (= count -1) (member errno '(11 35))) (return))
                  (t (error "Backend peer receive failed ~S/~S" count errno)))))))
    (assert wire)
    (push (list (fn2-native-compress-fixture-hex plain)
                (fn2-native-compress-fixture-hex wire)) rows)))
  (let* ((json (format nil "[~{[~s,~s]~^,~}]" (apply #'append (nreverse rows))))
         (process (sb-ext:run-program "python3" '("tests/compress_peer_oracle.py")
                    :search t :wait t :input (make-string-input-stream json)
                    :output *standard-output* :error *error-output*)))
   (assert (eql (sb-ext:process-exit-code process) 0)))
  t))

(defun fn2-native-compress-duplex-control (library)
 (fn2-native-compress-input-prefix-control library t #'fn2-native-compress-duplex-replies))
