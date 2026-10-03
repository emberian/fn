; STO-10005: resumable developer init compares the immutable initial intent.
; Sealed profile and generation-one record are observed under the writer lock.
; The later configuration history/limit overlay is not the initial intent.
(in-package "ACL2")
(include-book "config")

(defun fn-nir-initial-recordp (record)
  (declare (xargs :guard t))
  (and (fn-cfg-record-shapep record)
       (equal (fn-cfg-record-sequence record) 0)
       (equal (fn-cfg-record-txid record) 0)
       (equal (fn-cfg-record-generation record) 1)))

; Requested/recorded are decoded profile values. Record inputs are exact
; frame octets. NIL recorded record means an interrupted init has not yet
; published generation one; it may install the requested groups. A present
; corrupt record is a fault, never absence or a policy refusal.
(defun fn-nir-resume-decision (requested-profile recorded-profile
                                               requested-octets recorded-octets history)
  (declare (xargs :guard t))
  (let* ((requested (fn-cfg-decode-exact requested-octets))
         (recorded (fn-cfg-decode-exact recorded-octets)))
    (cond ((not (and (fn-record-parse-okp requested)
                    (fn-nir-initial-recordp (fn-record-parse-value requested))))
           '(:fault :requested-initial-record-invalid))
          ((and (null recorded-octets) (consp history))
           '(:fault :missing-initial-record))
          ((and recorded-octets
                (not (and (fn-record-parse-okp recorded)
                          (fn-nir-initial-recordp (fn-record-parse-value recorded)))))
           '(:fault :recorded-initial-record-invalid))
          ((not (equal requested-profile recorded-profile))
           '(:refused :profile-mismatch))
          ((null recorded-octets) '(:accepted :resume))
          ((not (equal (fn-cfg-record-change (fn-record-parse-value requested))
                       (fn-cfg-record-change (fn-record-parse-value recorded))))
           '(:refused :initial-groups-mismatch))
          (t '(:accepted :resume)))))

; PRF-1270: clock stamps are intentionally not compared. The decode premises
; state the actual bytes' contract; this is not a universal codec roundtrip.
(defthm fn-nir-resume-admits-identical-initial-contract-across-stamps
  (implies
   (and (equal (fn-cfg-decode-exact requested-octets)
               (fn-record-parse-ok (fn-cfg-record-make 0 0 1 change requested-stamp) nil))
        (equal (fn-cfg-decode-exact recorded-octets)
               (fn-record-parse-ok (fn-cfg-record-make 0 0 1 change recorded-stamp) nil)))
   (equal (fn-nir-resume-decision profile profile requested-octets recorded-octets history)
          '(:accepted :resume)))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (fn-record-parse-ok fn-record-parse-okp fn-record-parse-value fn-cfg-record-shapep fn-cfg-record-make
                                    fn-cfg-record-sequence fn-cfg-record-txid
                                    fn-cfg-record-generation fn-cfg-record-change
                                    fn-cfg-ag-car fn-cfg-ag-cdr)
                                   (fn-cfg-decode-exact)))))

; The requested and recorded initial change lists are distinct: a resume
; cannot report acceptance merely because the sealed profile matches.
(defthm fn-nir-resume-refuses-distinct-initial-changes
  (implies
   (and (equal (fn-cfg-decode-exact requested-octets)
               (fn-record-parse-ok (fn-cfg-record-make 0 0 1 requested-change requested-stamp) nil))
        (equal (fn-cfg-decode-exact recorded-octets)
               (fn-record-parse-ok (fn-cfg-record-make 0 0 1 recorded-change recorded-stamp) nil))
        (not (equal requested-change recorded-change)))
   (equal (fn-nir-resume-decision profile profile requested-octets recorded-octets history)
          '(:refused :initial-groups-mismatch)))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (fn-record-parse-ok fn-record-parse-okp fn-record-parse-value fn-cfg-record-shapep fn-cfg-record-make
                                    fn-cfg-record-sequence fn-cfg-record-txid
                                    fn-cfg-record-generation fn-cfg-record-change
                                    fn-cfg-ag-car fn-cfg-ag-cdr)
                                   (fn-cfg-decode-exact)))))

(defun fn-nir-resume-line (decision)
  (declare (xargs :guard t))
  (case (and (consp decision) (consp (cdr decision)) (cadr decision))
    (:missing-initial-record "init fault reason=missing-initial-record")
    (:profile-mismatch "init refused reason=profile-mismatch: existing store keeps its sealed profile")
    (:initial-groups-mismatch "init refused reason=initial-groups-mismatch: existing store keeps its initial groups")
    (:requested-initial-record-invalid "init fault reason=requested-initial-record-invalid")
    (:recorded-initial-record-invalid "init fault reason=recorded-initial-record-invalid")
    (otherwise "init fault reason=invalid-resume-decision")))
