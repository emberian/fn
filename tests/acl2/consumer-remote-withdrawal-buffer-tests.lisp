(in-package "ACL2")
(include-book "../../books/consumer-remote-withdrawal-buffer")

; Concrete local stobj fixtures do not supply production allocation authority.
(defun fn-crwdt-step (s key extent prefix)
 (declare (xargs :guard (fn-cbor-octet-listp prefix)))
 (with-local-stobj fn-octets
  (mv-let (answer bytes fn-octets)
   (let ((fn-octets (fn-octets-from-list prefix fn-octets)))
    (mv-let (answer fn-octets) (fn-crwd-step s key extent fn-octets)
     (mv answer (fn-octets-list fn-octets) fn-octets)))
   (list answer bytes))))
(defun fn-crwdt-run (fuel answer key extent fn-octets)
 (declare (xargs :stobjs fn-octets :guard (natp fuel) :measure (nfix fuel)))
 (if (or (zp fuel) (not (eq (fn-cp-nth 0 answer) :yield))) (mv answer fn-octets)
  (mv-let (next fn-octets) (fn-crwd-step (fn-cp-nth 1 answer) key extent fn-octets)
   (fn-crwdt-run (- fuel 1) next key extent fn-octets))))
(defun fn-crwdt-encode (start key extent)
 (declare (xargs :guard t))
 (with-local-stobj fn-octets
  (mv-let (answer bytes fn-octets)
   (let ((fn-octets (fn-octets-reserve (nfix extent) fn-octets)))
    (mv-let (answer fn-octets) (fn-crwdt-run 600 start key extent fn-octets)
     (mv answer (fn-octets-list fn-octets) fn-octets)))
   (list answer bytes))))
(defun fn-crwdt-projection (msgid)
 (declare (xargs :guard t))
 (list :report-input (list :current-article
                       (fn-make-article msgid 99 '("a") '(("a" . 7)) t nil))
       '("a") '(("a" . 7))))

; Unconditional concrete boundary: complete result AND complete buffer effect.
(assert-event
 (let* ((start (fn-crwd-begin '(key) :withdrawal-target (fn-crwdt-projection "<target>") 40 2))
        (s (cadr start)) (prefix '(9 8))
        (actual (fn-crwdt-step s '(key) 40 prefix)))
  (and (eq (car start) :yield)
       (equal (cadr actual) '(9 8 70))
       (mv-let (answer bytes) (fn-crwd-reference s '(key) 40 prefix)
        (equal actual (list answer bytes))))))

; Complete existing FNWD1 report/decoder, containing ONLY the target Message-ID.
(assert-event
 (let* ((msgid "<target>")
        (start (fn-crwd-begin '(key) :withdrawal-target (fn-crwdt-projection msgid) 40 0))
        (actual (fn-crwdt-encode start '(key) 40)))
  (and (equal (car actual) '(:encoded))
       (equal (cadr actual) (fn-ncr-withdrawal-report (fn-record-string-octets msgid)))
       (equal (fn-ncr-withdrawal-decode (cadr actual))
              (list :withdrawn (fn-record-string-octets msgid))))))

; Existing codec maximum is representable; it is not an invented query bound.
(assert-event
 (let* ((msgid (coerce (make-list *fn-cp-max-token* :initial-element #\a) 'string))
        (start (fn-crwd-begin '(key) :withdrawn (fn-crwdt-projection msgid) (+ 5 *fn-cp-max-token*) 0))
        (actual (fn-crwdt-encode start '(key) (+ 5 *fn-cp-max-token*))))
  (and (eq (car start) :yield) (equal (car actual) '(:encoded))
       (equal (len (cadr actual)) (+ 5 *fn-cp-max-token*))
       (equal (cadr actual) (fn-ncr-withdrawal-report (fn-record-string-octets msgid))))))

; Current-source/extent refusals assert exact unchanged concrete effects.
(assert-event
 (let* ((start (fn-crwd-begin '(key) :withdrawn (fn-crwdt-projection "<target>") 40 2))
        (s (cadr start)) (prefix '(9 8)))
  (and (equal (fn-crwdt-step s '(changed) 40 prefix)
              (list '(:refused :consumer-source-changed) prefix))
       (equal (fn-crwdt-step s '(key) 1 prefix)
              (list '(:refused :remote-report-extent) prefix))
       (equal (fn-crwdt-step s '(key) 40 '(9))
              (list '(:refused :remote-report-extent) '(9))))))

; Corrupted cursor bytes refuse before write. A visible article cannot enter
; this target-only format; the missing visible-report producer is unavailable.
(assert-event
 (and (equal (fn-crwdt-step (fn-crwd-state '(key) '(999) 1 2) '(key) 2 '(7))
             (list '(:refused :remote-withdrawal-octet) '(7)))
      (equal (fn-crwd-begin '(key) :visible (fn-crwdt-projection "<a>") 40 0)
             '(:unavailable :remote-visible-report-producer))
      (equal (fn-crwd-begin '(key) :withdrawn (fn-crwdt-projection "<a>") 1 0)
             '(:refused :oversize))
      (equal (fn-crwd-begin '(key) :withdrawn (fn-crwdt-projection "") 40 0)
             '(:refused :remote-withdrawal-message-id))))
