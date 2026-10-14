; LC model journal record: one chained frame, one served range and suffix.
; The metadata is in the log, never in a checkpoint article/history tape.
; The frame grammar, value codec and log-home codec are existing exports.
(in-package "ACL2")
(include-book "log-checkpoint-values")
(include-book "log-locator-resolves")
(include-book "store-tree-codec")
(include-book "store-log")

(defconst *fn-lc-record-kind* 5)
(defun fn-lc-record-frame (prev h payload)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((metadata (ec-call (fn-scc-encode h)))
        (wire (ec-call (fn-lc-expected-range payload)))
        (home (ec-call (fn-lc-expected-home-frame h)))
        (body (fn-lc-join prev
                (fn-lc-join (ec-call (fn-cbor-u32-bytes (len metadata)))
                 (fn-lc-join (ec-call (fn-cbor-u32-bytes (len wire)))
                  (fn-lc-join metadata (fn-lc-join wire home)))))))
   (ec-call (fn-frame-seal *fn-lg-magic* *fn-lg-version*
                         *fn-lc-record-kind* body))))
(defun fn-lc-record-frame-row (frame max)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((opened (ec-call (fn-frame-open frame max)))
        (body (fn-lc-drop 32 (fn-frame-result-payload opened)))
        (n (nfix (ec-call (fn-cbor-u32-from (fn-lc-take 4 body)))))
        (decoded (ec-call (fn-scc-decode-tree (fn-lc-take n (fn-lc-drop 8 body))))))
   (if (and (fn-frame-result-okp opened)
            (equal (fn-frame-result-kind opened) *fn-lc-record-kind*)
            (equal (fn-lc-head decoded) :ok)
            (fn-held-p (fn-lc-at 1 decoded)))
       (fn-lc-at 1 decoded) :bad)))
(defun fn-lc-record-framep (frame prev max)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((opened (ec-call (fn-frame-open frame max)))
        (payload (fn-frame-result-payload opened))
        (body (fn-lc-drop 32 payload))
        (m (nfix (ec-call (fn-cbor-u32-from (fn-lc-take 4 body)))))
        (n (nfix (ec-call (fn-cbor-u32-from (fn-lc-take 4 (fn-lc-drop 4 body)))))))
   (and (fn-frame-result-okp opened)
        (equal (fn-frame-result-magic opened) *fn-lg-magic*)
        (equal (fn-frame-result-version opened) *fn-lg-version*)
        (equal (fn-frame-result-kind opened) *fn-lc-record-kind*)
        (equal (fn-lc-take 32 payload) prev)
        (<= (+ 8 m n) (len body))
        (fn-held-p (fn-lc-record-frame-row frame max))
        (equal (fn-lc-drop (+ 8 m n) body)
               (ec-call (fn-lc-expected-home-frame
                         (fn-lc-record-frame-row frame max)))))))
(defun fn-lc-record-frame-served-offset (frame)
 (declare (xargs :guard t :verify-guards nil))
 (+ *fn-frame-header-octets* 32 8
    (nfix (ec-call (fn-cbor-u32-from
                    (fn-lc-take 4 (fn-lc-drop (+ *fn-frame-header-octets* 32) frame)))))))
(defun fn-lc-record-frame-served-length (frame)
 (declare (xargs :guard t :verify-guards nil))
 (nfix (ec-call (fn-cbor-u32-from
          (fn-lc-take 4 (fn-lc-drop (+ *fn-frame-header-octets* 36) frame))))))

(verify-guards fn-lc-record-frame)
(verify-guards fn-lc-record-frame-row)
(verify-guards fn-lc-record-framep)
(verify-guards fn-lc-record-frame-served-offset)
(verify-guards fn-lc-record-frame-served-length)

; Keep codecs opaque to consumers; ground executable controls still run.
(in-theory (disable fn-lc-record-frame fn-lc-record-frame-row fn-lc-record-framep))
