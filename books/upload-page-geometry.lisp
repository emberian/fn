; Shared actual ROOT upload sizing; no cold payload-policy change.
(in-package "ACL2")
(include-book "profile")
(include-book "upload-window-geometry")
(include-book "source-manifest-codec")
(fn2-book-layer :b)

(defconst *fn2-article-location-hashes-max* (* 32 *fn2-commit-write-resources*))

(defconst *fn2-upload-chunk-class* 1)

(defconst *fn2-upload-article-max* 32768)


(defconst *fn2-upload-mid-field-octets* 12)

(defconst *fn2-upload-mid-template*
  (concatenate 'string "Message-ID: <fn2." (string (code-char 1)) "." (string (code-char 1)) "@"))

(defconst *fn2-upload-mid-close* (coerce (list #\> (code-char 13) (code-char 10)) 'string))

(defconst *fn2-upload-op-mid-template*
  (concatenate 'string "Message-ID: <op-" (string (code-char 1)) "-" (string (code-char 1)) "@"))

(assert-event (<= (length *fn2-upload-op-mid-template*) (length *fn2-upload-mid-template*)))

(defconst *fn2-upload-mid-line-max*
  (+ (- (length *fn2-upload-mid-template*) 2) 40 *fn2-profile-path-identity-max* (length *fn2-upload-mid-close*)))

(assert-event (equal (- *fn2-upload-mid-line-max* (+ *fn2-upload-mid-field-octets* 2)) 250))

(assert-event (<= (+ *fn2-upload-article-max* *fn2-upload-mid-line-max*) *fn2-am-stored-max*))

(defconst *fn2-upload-page-stored-source* (* 64 (ceiling *fn2-upload-mid-line-max* 64)))

(defconst *fn2-upload-page-source* (+ *fn2-upload-page-stored-source* *fn2-upload-digest-octets*))

(defconst *fn2-upload-page-location-hashes* (+ *fn2-upload-page-stored-source* 64))

(assert-event (equal (+ *fn2-upload-page-source* *fn2-upload-digest-octets*)
                     *fn2-upload-page-location-hashes*))

(defconst *fn2-upload-page-stage*
  (+ *fn2-upload-page-location-hashes* (* 64 (ceiling *fn2-article-location-hashes-max* 64))))

(defconst *fn2-upload-page-hash* (+ *fn2-upload-page-stage* *fn2-commit-unit-bytes*))

(defconst *fn2-upload-page-manifest* (+ *fn2-upload-page-hash* 64))

(defconst *fn2-upload-head-bytes* (+ 32 *fn2-am-header-max*))

(defconst *fn2-upload-entry-bytes* (+ 64 (* 2 *fn2-am-entry-max*)))

(defun fn2-upload-page-bytes (total)
  (declare (xargs :guard t))
  (if (fn2-am-manifestp total)
      (+ *fn2-upload-page-manifest* (* *fn2-commit-unit-bytes* (fn2-am-units total)))
    *fn2-upload-page-manifest*))

; These scalar decisions are consumed by the actual input configuration
; and upload producer as well as resource admission.
(defun fn2-upload-profile-article-max (profile)
 (declare (xargs :guard t))
 (let ((max (fn2-profile-get :article-max profile)))
  (if (unsigned-byte-p 32 max) max *fn2-upload-article-max*)))
(defun fn2-upload-input-bound (article-max cap0 cap1)
 (declare (xargs :guard t) (ignorable cap0 cap1))
 (nfix article-max))
(defun fn2-upload-article-profilep (profile)
 (declare (xargs :guard t))
 (or (null (fn2-profile-get :article-max profile))
     (and (natp (fn2-profile-get :article-max profile))
          (<= (+ (fn2-profile-get :article-max profile) *fn2-upload-mid-line-max*) *fn2-am-stored-max*))))

(defconst *fn2-upload-page-provisional*
  (+ *fn2-upload-page-manifest* *fn2-upload-raw-bytes*))
(defun fn2-upload-stream-page-bytes (total)
  (declare (xargs :guard t))
  (+ *fn2-upload-page-provisional*
     (* *fn2-commit-unit-bytes* (fn2-am-units total))))
