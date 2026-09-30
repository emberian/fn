; Actual committed row/configuration boundary for SUB-008.
(in-package "ACL2")
(include-book "substrate-committed-transcript")
(include-book "peer-transit-authority")
(defun fn-stce-row-start (row)
  (declare (xargs :guard t))
  (let* ((held (cond ((fn-held-p row) row)
                     ((fn-hstxa-p row) (fn-hstxa-held row)) (t nil)))
         (groups (if held (fn-record-groups held) nil)))
    (fn-stce-start (fn-sn-row-delta row) groups)))

(local (defthm fn-stce-config-hex-is-id-hex
  (implies (fn-cfg-hex-digit-octetsp xs) (fn-id-hex-listp xs))
  :hints (("Goal" :induct (fn-cfg-hex-digit-octetsp xs)
                  :in-theory (enable fn-cfg-hex-digit-octetsp fn-cfg-hex-digit-octetp
                                     fn-id-hex-listp fn-id-hex-digitp)))))
(defun fn-stce-entry-authority (entry generation)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable fn-cfg-principal-hexp)))))
  (let ((authority (fn-cfg-group-authority entry)))
    (if (and entry (fn-cfg-entry-livep entry generation)
             (fn-cfg-principal-hexp authority))
        (fn-id-unhex (fn-record-string-octets authority)) nil)))
; (:resolve-authority tail name generation core-cursor pinned-configuration)
(defun fn-stce-authority-tagp (cursor)
  (declare (xargs :guard t))
  (and (true-listp cursor) (equal (len cursor) 6)
       (equal (car cursor) :resolve-authority)))
(defun fn-stce-authority-answer (cursor)
  (declare (xargs :guard (true-listp cursor)))
  (fn-stce-entry-authority
   (fn-cfg-group-find (nth 1 cursor) (nth 2 cursor)) (nth 3 cursor)))
(defun fn-stce-authority-sourcep (cursor)
  (declare (xargs :guard (true-listp cursor)))
  (equal (fn-stce-authority-answer cursor)
         (fn-pta-group-authority (nth 5 cursor) (nth 3 cursor) (nth 2 cursor))))
(defun fn-stce-authority-start (cursor cfg generation)
  (declare (xargs :guard (and (true-listp cursor) (consp (nth 2 cursor)))))
  (list :resolve-authority (fn-cfg-groups cfg) (car (nth 2 cursor))
        generation cursor cfg))
(defun fn-stce-row-resume (evidence cursor cfg generation keyring)
  (declare (xargs :guard (fn-prin-keyringp keyring)))
  (cond
   ((fn-stce-authority-tagp cursor)
    (let ((tail (nth 1 cursor)) (name (nth 2 cursor)))
      (cond
       ((atom tail) (fn-stce-resume evidence (nth 4 cursor) nil keyring))
       ((equal (fn-cfg-group-name (car tail)) name)
        (fn-stce-resume evidence (nth 4 cursor)
                        (fn-stce-entry-authority (car tail) (nth 3 cursor)) keyring))
       (t (mv evidence
              (list :resolve-authority (cdr tail) name (nth 3 cursor)
                    (nth 4 cursor) (nth 5 cursor)) :resolving-authority)))))
   ((and (fn-stce-select-tagp cursor) (consp (nth 1 cursor)) (consp (nth 2 cursor)))
    (mv evidence (fn-stce-authority-start cursor cfg generation) :resolving-authority))
   (t (fn-stce-resume evidence cursor nil keyring))))

(defthm fn-stce-authority-start-pins-the-policy-source
  (fn-stce-authority-sourcep (fn-stce-authority-start cursor cfg generation))
  :hints (("Goal" :in-theory (e/d (fn-stce-authority-sourcep fn-stce-authority-answer
                                    fn-stce-authority-start fn-stce-entry-authority
                                    fn-pta-group-authority)
                                   (fn-cfg-group-find fn-cfg-groups fn-cfg-group-authority
                                    fn-cfg-entry-livep fn-cfg-principal-hexp fn-id-unhex
                                    fn-record-string-octets)))))
(defthm fn-stce-authority-scan-keeps-the-pinned-source
  (implies (and (fn-stce-authority-tagp cursor)
                (consp (nth 1 cursor))
                (not (equal (fn-cfg-group-name (car (nth 1 cursor))) (nth 2 cursor))))
           (equal (fn-stce-authority-sourcep
                   (mv-nth 1 (fn-stce-row-resume evidence cursor cfg generation keyring)))
                  (fn-stce-authority-sourcep cursor)))
  :hints (("Goal" :in-theory (e/d (fn-stce-row-resume fn-stce-authority-sourcep
                                    fn-stce-authority-answer fn-cfg-group-find)
                                   (fn-stce-authority-tagp fn-stce-entry-authority
                                    fn-stce-resume fn-stce-authority-start
                                    fn-pta-group-authority fn-cfg-group-name)))))
(defthm fn-stce-authority-resolution-is-the-pinned-policy-source
  (implies (and (fn-stce-authority-tagp cursor) (fn-stce-authority-sourcep cursor)
                (or (atom (nth 1 cursor))
                    (equal (fn-cfg-group-name (car (nth 1 cursor))) (nth 2 cursor))))
           (equal (fn-stce-row-resume evidence cursor cfg generation keyring)
                  (fn-stce-resume evidence (nth 4 cursor)
                   (fn-pta-group-authority (nth 5 cursor) (nth 3 cursor) (nth 2 cursor))
                   keyring)))
  :hints (("Goal" :in-theory (e/d (fn-stce-row-resume fn-stce-authority-sourcep
                                    fn-stce-authority-answer fn-cfg-group-find
                                    fn-stce-entry-authority)
                                   (fn-stce-authority-tagp fn-stce-resume
                                    fn-stce-authority-start fn-pta-group-authority
                                    fn-cfg-group-name fn-cfg-entry-livep
                                    fn-cfg-group-authority fn-cfg-principal-hexp
                                    fn-id-unhex fn-record-string-octets)))))

(local (defthm fn-stce-lace-is-statements
  (implies (fn-lace-p lace) (fn-stce-statementsp lace))
  :hints (("Goal" :in-theory (enable fn-lace-p fn-stce-statementsp)))))
(defthm fn-stce-committed-row-start-has-cursor-shape
  (fn-stce-cursor-shapep (fn-stce-row-start row))
  :hints (("Goal" :in-theory (e/d (fn-stce-row-start)
                                   (fn-sn-row-delta fn-stce-start
                                    fn-stce-cursor-shapep fn-record-groups)))))

; The collector already carries the actual accepted row type. Dispatch on its
; fixed head rather than revalidating every group/number/context in that row.
(defun fn-stce-row-start-carried (row)
  (declare (xargs :guard (or (fn-held-p row) (fn-hstxa-p row))))
  (let ((held (if (natp (fn-cbor-ag-car row)) row (fn-hstxa-held row))))
    (fn-stce-start (fn-hc-delta (fn-held-context held)) (fn-record-groups held))))
(defthm fn-stce-row-start-carried-is-row-start
  (implies (or (fn-held-p row) (fn-hstxa-p row))
           (equal (fn-stce-row-start-carried row) (fn-stce-row-start row)))
  :hints (("Goal" :in-theory (e/d (fn-stce-row-start-carried fn-stce-row-start
                                    fn-sn-row-delta fn-hstxa-p)
                                   (fn-held-p fn-stce-start fn-hc-delta
                                    fn-held-context fn-record-groups)))))
