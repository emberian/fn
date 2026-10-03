; Redeem client input admission. Host reads one character or socket window;
; ACL2 decides whether it can be retained and whether a line is complete.
(in-package "ACL2")
(include-book "nntp-syntax")

(defun fn-rip-password-limit ()
  (declare (xargs :guard t))
  (min (- *fn-nntp-max-command-octets* 13)
       (- *fn-nntp-max-command-octets* 14))) ; XREDEEM PASS / AUTHINFO PASS

(defun fn-rip-password-step (used returnp octet)
  (declare (xargs :guard t))
  (cond ((not (and (natp used) (<= used (fn-rip-password-limit))
                   (booleanp returnp))) :refused)
        ((or (equal octet :eof) (equal octet 10))
         (if (posp used) :end :refused))
        (returnp :refused)
        ((equal octet 13) :return)
        ((and (integerp octet) (<= 33 octet) (<= octet 126)
              (< used (fn-rip-password-limit))) :octet)
        (t :refused)))

(defun fn-rip-reply-status (used lf)
  (declare (xargs :guard t))
  (cond ((not (natp used)) :refused)
        ((natp lf)
         (if (and (< lf used) (<= (+ 1 lf) *fn-nntp-max-response-octets*))
             :line :refused))
        ((< used *fn-nntp-max-response-octets*) :need)
        (t :refused)))

(defun fn-rip-token-octets (x)
  (declare (xargs :guard t))
  (cond ((stringp x)
         (if (<= (length x) *fn-nntp-max-command-octets*)
             (fn-record-string-octets x) nil))
        ((fn-cbor-at-mostp x *fn-nntp-max-command-octets*) x)
        (t nil)))

(defun fn-rip-command (kind first second)
  (declare (xargs :guard t))
  (let* ((a (fn-rip-token-octets first))
         (b (fn-rip-token-octets second))
         (line (cond ((equal kind :starttls) (fn-record-string-octets "STARTTLS"))
                     ((equal kind :quit) (fn-record-string-octets "QUIT"))
                     ((and (equal kind :password) (consp a) (true-listp a)
                           (fn-nntp-printable-tokenp a)
                           (fn-cbor-at-mostp a (fn-rip-password-limit)))
                      (append (fn-record-string-octets "XREDEEM PASS ") a))
                     ((and (equal kind :code) (consp a) (true-listp a)
                           (fn-nntp-printable-tokenp a)
                           (not (fn-nntp-keywordp a "PASS"))
                           (consp b) (true-listp b) (fn-nntp-printable-tokenp b))
                      (append (fn-record-string-octets "XREDEEM ") a '(32) b))
                     (t nil))))
    (if (and (consp line) (fn-nntp-command-inputp line))
        (append line '(13 10)) nil)))

; PRF-1302: the subjects called before retaining the next password octet
; or interpreting a complete reply. No environment hypotheses.
(defthm fn-rip-password-admission-stays-within-wire-capacity
  (implies (equal (fn-rip-password-step used returnp octet) :octet)
           (and (natp used) (booleanp returnp) (not returnp)
                (integerp octet) (<= 33 octet) (<= octet 126)
                (<= (+ used 1 13) *fn-nntp-max-command-octets*)))
  :rule-classes nil)

(defthm fn-rip-reply-admission-stays-within-wire-capacity
  (implies (equal (fn-rip-reply-status used lf) :line)
           (and (natp used) (natp lf) (< lf used)
                (<= (+ lf 1) *fn-nntp-max-response-octets*)))
  :rule-classes nil)

(in-theory (disable fn-rip-password-limit fn-rip-password-step fn-rip-reply-status
                    fn-rip-command))
