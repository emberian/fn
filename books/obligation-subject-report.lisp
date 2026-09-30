; A read-only answer about independent active obligations. Aggregation here
; authorizes no release/reclaim. The logical oracle is never served.
(in-package "ACL2")
(include-book "obligation-subject-grammar")
(include-book "retention-obligation-view")
(include-book "native-live-status")
(include-book "identity")

(defun fn-oqr-line (subject pair)
  (declare (xargs :guard (and (fn-record-octet-stringp subject) (fn-vd-pairp pair))
                  :verify-guards nil))
  (append (fn-nls-text "subject-hex=")
          (fn-id-hex-octets (fn-record-string-octets subject))
          (fn-nls-field "obligations" (car pair))
          (fn-nls-field "charge" (cdr pair)) *fn-nls-lf*))

(defun fn-oqr-live-report (subject view)
  (declare (xargs :guard (fn-record-octet-stringp subject) :verify-guards nil))
  (fn-oqr-line subject (fn-rov-subject subject view)))

(defun fn-oqr-oracle-report (subject pins)
  (declare (xargs :guard (and (fn-record-octet-stringp subject)
                            (fn-retain-obligation-listp pins)) :verify-guards nil))
  (fn-oqr-line subject (fn-vd-oracle-at subject (fn-rov-contribs pins))))

(verify-guards fn-oqr-line
  :hints (("Goal" :in-theory (enable fn-record-octet-stringp
                                    fn-record-string-octets fn-vd-pairp))))
(verify-guards fn-oqr-live-report
  :hints (("Goal" :in-theory (enable fn-rov-subject))))
(verify-guards fn-oqr-oracle-report)

(defthm fn-oqr-live-is-reconstruction
  (implies (and (stringp subject) (fn-rov-correspondp view pins))
           (equal (fn-oqr-live-report subject view)
                  (fn-oqr-oracle-report subject pins)))
  :hints (("Goal" :in-theory (enable fn-oqr-live-report fn-oqr-oracle-report))))

 ; One-page query: no per-subject report cache is created. An unsupported
; continuation or oversize reply is named-refused by ACL2; normal reports
; fit the existing FNLS chunk under the admitted profile.
(defun fn-oqr-live-answer (subject view offset cached)
  (declare (xargs :guard (fn-record-octet-stringp subject) :verify-guards nil))
  (let ((report (fn-oqr-live-report subject view)))
    (list (if (and (equal offset 0) (<= (len report) *fn-nls-chunk-octets*))
              (fn-nls-page (fn-nls-buffer report) 0)
            (fn-nls-reply-encode :refused 0 nil
              (append (fn-nls-text "obligation-subject-one-page") *fn-nls-lf*)))
          cached)))
; FNLS concrete buffer/page entries remain :ideal in their existing book.
; This composed framing helper is not advertised as guard-verified.
(defthm fn-oqr-live-answer-is-reconstruction
  (implies (and (stringp subject) (fn-rov-correspondp view pins)
                (<= (len (fn-oqr-oracle-report subject pins)) *fn-nls-chunk-octets*))
           (equal (fn-oqr-live-answer subject view 0 cached)
                  (list (fn-nls-page (fn-nls-buffer
                           (fn-oqr-oracle-report subject pins)) 0) cached)))
  :hints (("Goal" :in-theory (enable fn-oqr-live-answer))))
(in-theory (disable fn-oqr-line fn-oqr-live-report fn-oqr-oracle-report
                    fn-oqr-live-answer))
