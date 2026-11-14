; Compression supplies policy; capability/loan/allocation ownership is generated.
(in-package "ACL2")
(include-book "compress-transport-state")
(include-book "codec-profile")
(include-book "compress-policy")
(fn2-book-layer :d)
(defcodec-transport-lifecycle fn2-compress-transport
 :input-quantum-field input-quantum :output-quantum-field output-quantum)
(defcodec-transport-upgrade fn2-compress-transport fn2-codec-copy-plan
 :input-quantum-field input-quantum :status-field nil)

(defun fn2-compress-transport-start
 (cap nonce slot generation total capacity iq oq ratio burst fn2-compress-transport)
 (declare (xargs :stobjs fn2-compress-transport :verify-guards nil
                 :guard (fn2-compress-transport-wfp fn2-compress-transport)))
 (if (not (and (posp iq) (unsigned-byte-p 32 iq) (unsigned-byte-p 32 oq) (<= *fn2-compress-min-output-window* oq)
               (posp ratio) (unsigned-byte-p 32 ratio) (posp burst) (unsigned-byte-p 32 burst)
               (<= oq burst)))
     (mv :bounds fn2-compress-transport)
  (mv-let (code turns) (fn2-codec-upgrade-turns capacity iq)
   (if (not (eq code :ok)) (mv :bounds fn2-compress-transport)
    (mv-let (code fn2-compress-transport)
     (fn2-compress-transport-begin cap nonce slot generation total capacity iq oq
                                  (max iq oq) turns fn2-compress-transport)
     (if (not (eq code :ok)) (mv code fn2-compress-transport)
      (let ((fn2-compress-transport
             (fn2-compress-transport-put 0 (credit burst) (ratio ratio) (burst burst))))
       (mv :ok fn2-compress-transport))))))))
(verify-guards fn2-compress-transport-start)
(defthm fn2-compress-transport-start-wfp
 (implies (and (fn2-compress-transportp s) (fn2-compress-transport-wfp s))
  (fn2-compress-transport-wfp
   (mv-nth 1 (fn2-compress-transport-start cap nonce slot generation total capacity iq oq ratio burst s)))))
