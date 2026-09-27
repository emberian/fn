; fn: the wire and command-line forms of a consumer WAIT (PRF-252, CNS-007).
;
; Two more local-control consumer requests on the FNCL request kind 4
; (books/consumer-local-control.lisp), whose codec is unchanged: this book
; wraps it.
;
;   code 9   wait        consumer id, timeout (uint32 seconds)
;   code 10  bound-wait  consumer id, timeout, the account's password
;
; The timeout is 0 to *fn-cwait-max-seconds*.  Both are answered on the poll
; reply kind 6 (`fn-ncl-poll-reply-encode'), exactly as a poll is: the
; answer IS a poll's (books/consumer-wait.lisp).
;
;   fn consumer wait CONTROL NAME CURSOR REPORT --timeout S
;   fn consumer bound-wait CONTROL NAME SECRET-FILE CURSOR REPORT --timeout S
;
; Every other request, reply and command is `fn-ncl-request-encode' /
; `-decode' / `fn-ncl-cli-plan''s, unchanged
; (`fn-cwait-request-decode-of-another-code-is-the-consumer-decode',
; `fn-cwait-cli-plan-of-another-command-is-the-consumer-plan').
;
; Host callers: host/native-control-host.lisp
; `fn-native-control-host-consumer-request-encode', `-request-decode' and
; `-cli-plan', which host/native/control.lisp and
; host/native/consumer-local.lisp call.
(in-package "ACL2")
(include-book "consumer-local-control")

(defconst *fn-cwait-max-seconds* 3600)
(defconst *fn-cwait-wait-code* 9)
(defconst *fn-cwait-bound-wait-code* 10)
(defconst *fn-cwait-timeout-flag*
  '(45 45 116 105 109 101 111 117 116)) ; --timeout

(defun fn-cwait-secondsp (x)
  (declare (xargs :guard t))
  (and (natp x) (<= x *fn-cwait-max-seconds*)))

; FIRST the consumer id; SECOND the timeout in seconds (wait) or the list
; (SECONDS PASSWORD) (bound-wait).
(defun fn-cwait-request-encode (kind first second)
  (declare (xargs :guard t))
  (case kind
    (:wait
     (if (and (fn-cp-idp first) (fn-cwait-secondsp second))
         (let ((payload (append (list *fn-cwait-wait-code*)
                                (fn-cp-id-bytes first)
                                (fn-cbor-u32-bytes second))))
           (if (<= (len payload) *fn-ncl-max-payload*)
               (fn-nctrl-seal *fn-ncl-request-kind* payload)
             :bad))
       :bad))
    (:bound-wait
     (if (and (fn-cp-idp first) (true-listp second) (equal (len second) 2)
              (fn-cwait-secondsp (car second))
              (fn-ncl-secretp (cadr second)))
         (let ((payload (append (list *fn-cwait-bound-wait-code*)
                                (fn-cp-id-bytes first)
                                (fn-cbor-u32-bytes (car second))
                                (fn-ncl-secret-bytes (cadr second)))))
           (if (<= (len payload) *fn-ncl-bound-max-payload*)
               (fn-nctrl-seal *fn-ncl-request-kind* payload)
             :bad))
       :bad))
    (otherwise (fn-ncl-request-encode kind first second))))

; The wait payload's body after its code: the id, the timeout and, for a
; bound wait, the password.
(defun fn-cwait-read-body (bound body)
  (declare (xargs :guard (fn-cbor-octet-listp body)
                  :verify-guards nil))
  (let ((one (fn-cp-read-id body)))
    (if (not (eq (fn-cp-nth 0 one) :ok))
        (list :refused :consumer)
      (let ((two (fn-cp-read-u32 (fn-cp-nth 2 one))))
        (cond
         ((not (and (eq (fn-cp-nth 0 two) :ok)
                    (fn-cwait-secondsp (fn-cp-nth 1 two))))
          (list :refused :timeout))
         ((not bound)
          (if (null (fn-cp-nth 2 two))
              (list :consumer :wait (fn-cp-nth 1 one) (fn-cp-nth 1 two))
            (list :refused :timeout)))
         (t
          (let ((three (fn-ncl-read-secret (fn-cp-nth 2 two))))
            (if (and (eq (fn-cp-nth 0 three) :ok)
                     (null (fn-cp-nth 2 three)))
                (list :consumer :bound-wait (fn-cp-nth 1 one)
                      (list (fn-cp-nth 1 two) (fn-cp-nth 1 three)))
              (list :refused :secret)))))))))

(defun fn-cwait-request-decode (octets)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((opened (fn-nctrl-open octets *fn-ncl-request-kind*))
         (payload (and (fn-frame-result-okp opened)
                       (fn-frame-result-payload opened))))
    (if (and (consp payload)
             (member (car payload)
                     (list *fn-cwait-wait-code* *fn-cwait-bound-wait-code*)))
        (if (and (fn-cbor-octet-listp payload)
                 (<= (len payload)
                     (if (equal (car payload) *fn-cwait-bound-wait-code*)
                         *fn-ncl-bound-max-payload*
                       *fn-ncl-max-payload*)))
            (fn-cwait-read-body
             (equal (car payload) *fn-cwait-bound-wait-code*) (cdr payload))
          (list :refused :size))
      (fn-ncl-request-decode octets))))

(defun fn-cwait-cli-plan (command argv)
  (declare (xargs :guard t :verify-guards nil))
  (let ((control (fn-cp-nth 0 argv))
        (id (fn-cp-nth 1 argv))
        (third (fn-cp-nth 2 argv))
        (fourth (fn-cp-nth 3 argv))
        (fifth (fn-cp-nth 4 argv))
        (sixth (fn-cp-nth 5 argv)))
    (cond
     ((equal command '(119 97 105 116)) ; wait
      (let ((seconds (fn-ncfg-decimal sixth)))
        (if (and (equal (len argv) 6)
                 (fn-ncl-absolute-pathp control)
                 (fn-cp-idp id) (fn-ncfg-printablep id)
                 (fn-ncl-absolute-pathp third)
                 (fn-ncl-absolute-pathp fourth)
                 (not (equal third fourth))
                 (equal fifth *fn-cwait-timeout-flag*)
                 (fn-cwait-secondsp seconds))
            (list :run :wait control id third fourth nil seconds)
          (list :usage :wait))))
     ((equal command '(98 111 117 110 100 45 119 97 105 116)) ; bound-wait
      (let ((seconds (fn-ncfg-decimal (fn-cp-nth 6 argv))))
        (if (and (equal (len argv) 7)
                 (fn-ncl-absolute-pathp control)
                 (fn-cp-idp id) (fn-ncfg-printablep id)
                 (fn-ncl-absolute-pathp third)
                 (fn-ncl-absolute-pathp fourth)
                 (fn-ncl-absolute-pathp fifth)
                 (not (equal fourth fifth))
                 (not (equal third fourth))
                 (not (equal third fifth))
                 (equal sixth *fn-cwait-timeout-flag*)
                 (fn-cwait-secondsp seconds))
            (list :run :bound-wait control id fourth fifth third seconds)
          (list :usage :bound-wait))))
     (t (fn-ncl-cli-plan command argv)))))

;; The article a poll report carries, for an agent's reader
;; (tools/fn_agent.py, through `fn consumer-article REPORT'): a carried
;; event's record (the signed form, books/stx-accept-records.lisp) or the
;; plain record an unsigned article's report is (fn-col-poll-report-octets).
;; (:ok MSGID RECEIVED) with the Message-ID text and the article octets as
;; stored, or (:refused :codec).  `consumer-project' remains the projection
;; of a signed report with its authorship; this one decides nothing about
;; authorship.
(defun fn-cwait-record-article (record-result)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-record-result-okp record-result)
      (let ((record (fn-record-result-record record-result)))
        (list :ok (fn-record-msgid record) (fn-record-payload record)))
    (list :refused :codec)))

(defun fn-cwait-report-article (octets)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (true-listp octets))
      (list :refused :codec)
    (let ((carried (fn-stxa-decode-exact octets)))
      (if (fn-stmt-okp carried)
          (fn-cwait-record-article
           (fn-record-decode-exact
            (fn-stxa-article-record (fn-stmt-value carried))))
        (fn-cwait-record-article (fn-record-decode-exact octets))))))

; The old kinds are the consumer codec's, unchanged.
(defthm fn-cwait-request-encode-of-another-kind-is-the-consumer-encode
  (implies (not (member kind '(:wait :bound-wait)))
           (equal (fn-cwait-request-encode kind first second)
                  (fn-ncl-request-encode kind first second)))
  :rule-classes nil)

(defthm fn-cwait-request-decode-of-another-code-is-the-consumer-decode
  (implies (not (member (car (fn-frame-result-payload
                              (fn-nctrl-open octets *fn-ncl-request-kind*)))
                        '(9 10)))
           (equal (fn-cwait-request-decode octets)
                  (fn-ncl-request-decode octets)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cwait-request-decode)
                                  (fn-nctrl-open fn-ncl-request-decode
                                   fn-cwait-read-body)))))

(defthm fn-cwait-cli-plan-of-another-command-is-the-consumer-plan
  (implies (not (member-equal command '((119 97 105 116)
                                        (98 111 117 110 100 45 119 97 105 116))))
           (equal (fn-cwait-cli-plan command argv)
                  (fn-ncl-cli-plan command argv)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cwait-cli-plan) (fn-ncl-cli-plan)))))


; --- The request round trip (the frame and field lemmas are local) ---

(local
 (defthm fn-cwait-nctrl-open-of-seal
   (implies (and (fn-cbor-octet-listp payload)
                 (<= (len payload) *fn-nctrl-max-payload*))
            (equal (fn-nctrl-open (fn-nctrl-seal *fn-ncl-request-kind* payload)
                                  *fn-ncl-request-kind*)
                   (fn-frame-ok *fn-nctrl-magic* *fn-nctrl-version*
                                *fn-ncl-request-kind* payload)))
   :hints (("Goal"
            :use ((:instance fn-frame-decode-of-host-framing
                             (magic *fn-nctrl-magic*)
                             (version *fn-nctrl-version*)
                             (kind *fn-ncl-request-kind*)
                             (max-payload *fn-nctrl-max-payload*)))
            :in-theory (e/d (fn-nctrl-open fn-nctrl-seal
                             fn-frame-inputp fn-frame-magicp
                             fn-frame-protected fn-frame-header
                             fn-cbor-u32-bytes-are-octets
                             fn-frame-octet-listp-of-append)
                            (fn-frame-decode fn-frame-trailer
                             fn-frame-protected-prefix
                             fn-frame-decode-of-host-framing))))))

(local
 (defthm fn-cwait-read-u32-of-u32-bytes
   (implies (fn-cp-uintp n)
            (equal (fn-cp-read-u32 (fn-cbor-u32-bytes n)) (list :ok n nil)))
   :hints (("Goal" :use ((:instance fn-cp-read-u32-roundtrip (rest nil)))
            :in-theory (disable fn-cp-read-u32-roundtrip fn-cp-read-u32 fn-cbor-u32-bytes)))))

(local
 (defthm fn-cwait-len-of-consp
   (implies (consp x) (< 0 (len x)))
   :rule-classes :linear))

(local
 (defthm fn-cwait-take-len
   (implies (true-listp s) (equal (take (len s) s) s))))

(local
 (defthm fn-cwait-secret-bytes-facts
   (implies (fn-ncl-secretp s)
            (and (fn-cbor-octet-listp (fn-ncl-secret-bytes s))
                 (equal (fn-ncl-read-secret (fn-ncl-secret-bytes s)) (list :ok s nil))
                 (equal (len (fn-ncl-secret-bytes s)) (+ 2 (len s)))))
   :hints (("Goal" :cases ((< (len s) 256))
            :in-theory (e/d (fn-ncl-secret-bytes fn-ncl-secretp fn-ncl-read-secret
                             fn-cbor-octetp fn-cbor-octet-listp-implies-true-listp)
                            (floor mod))))))

; KEYSTONE (the wire).  Every wait request the encoder writes (it refuses
; :bad an id, timeout or password outside its field) decodes to its own id
; and timeout (and password), so the owner waits for exactly the consumer
; and the time the command line named.
(defthm fn-cwait-wait-request-roundtrip
  (implies (not (equal (fn-cwait-request-encode :wait id seconds) :bad))
           (equal (fn-cwait-request-decode
                   (fn-cwait-request-encode :wait id seconds))
                  (list :consumer :wait id seconds)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cwait-request-encode fn-cwait-request-decode
                            fn-cwait-read-body fn-cwait-nctrl-open-of-seal
                            fn-cp-id-bytes fn-cp-read-id fn-cp-uintp
                            fn-cbor-octet-listp-append fn-cbor-u32-bytes-are-octets
                            fn-cp-id-bytes-octets fn-cwait-read-u32-of-u32-bytes)
                           (fn-nctrl-open fn-nctrl-seal fn-cbor-u32-bytes
                            fn-cp-read-u32)))))

(defthm fn-cwait-bound-wait-request-roundtrip
  (implies (not (equal (fn-cwait-request-encode :bound-wait id
                                                (list seconds secret))
                       :bad))
           (equal (fn-cwait-request-decode
                   (fn-cwait-request-encode :bound-wait id (list seconds secret)))
                  (list :consumer :bound-wait id (list seconds secret))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cwait-request-encode fn-cwait-request-decode
                            fn-cwait-read-body fn-cwait-nctrl-open-of-seal
                            fn-cp-id-bytes fn-cp-read-id fn-cp-uintp
                            fn-cwait-secret-bytes-facts
                            fn-cbor-octet-listp-append fn-cbor-u32-bytes-are-octets
                            fn-cp-id-bytes-octets fn-cp-read-u32-roundtrip)
                           (fn-nctrl-open fn-nctrl-seal fn-cbor-u32-bytes
                            fn-ncl-secret-bytes fn-ncl-read-secret fn-ncl-secretp
                            fn-cp-read-u32)))))

(verify-guards fn-cwait-read-body)
(verify-guards fn-cwait-request-decode)
(verify-guards fn-cwait-cli-plan)
;; PKT-709 (friend-blockers-2): the report reader is guard-verified, so the
;; report summary a consumer command prints (books/consumer-reason.lisp) is.
(verify-guards fn-cwait-record-article)
(verify-guards fn-cwait-report-article)
