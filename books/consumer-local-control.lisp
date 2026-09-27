; Bounded local-owner consumer command frame.  The Unix socket's 0600 path
; binds one local owner principal; no principal, query/view version or Store
; coordinates arrive in these bytes.
;
; PRF-234 (CNS-006): a consumer the configuration binds to an account
; (books/consumer-bound.lisp) is driven by two more commands, `bound-poll'
; (code 7: the consumer id and the account's password) and `bound-ack'
; (code 8: the password, then the cursor).  The password is the account's
; own credential, checked by ACL2 against the verifier AUTHINFO checks; it
; is carried only in the request and never in a reply.  Its field is a
; two-octet length and 1 to *fn-ncl-max-secret* octets: the longest
; AUTHINFO PASS argument a 512-octet NNTP command line carries.
(in-package "ACL2")
(include-book "native-control")
(include-book "consumer-position")
(include-book "store-events")

(defconst *fn-ncl-request-kind* 4)
(defconst *fn-ncl-reply-kind* 5)
(defconst *fn-ncl-poll-reply-kind* 6)
(defconst *fn-ncl-status-reply-kind* 9)
(defconst *fn-ncl-max-payload* 513)
(defconst *fn-ncl-poll-max-payload* (+ 9 346 *fn-stxa-max-octets*))
(defconst *fn-ncl-status-max-payload* 13)
(defconst *fn-ncl-max-secret* 496)
(defconst *fn-ncl-bound-max-payload* 1024)

(defun fn-ncl-secretp (x)
  (and (consp x) (fn-cbor-octet-listp x) (<= (len x) *fn-ncl-max-secret*)))

(defun fn-ncl-secret-bytes (x)
  (list* (floor (len x) 256) (mod (len x) 256) x))

(defun fn-ncl-read-secret (xs)
  "Read one secret field: (:ok SECRET REST) or (:bad)."
  (if (and (consp xs) (consp (cdr xs))
           (fn-cbor-octetp (car xs)) (fn-cbor-octetp (cadr xs)))
      (let ((n (+ (* 256 (car xs)) (cadr xs)))
            (body (cddr xs)))
        (if (and (posp n) (<= n *fn-ncl-max-secret*) (true-listp body)
                 (<= n (len body)))
            (list :ok (take n body) (nthcdr n body))
          (list :bad)))
    (list :bad)))

(defun fn-ncl-command-code (kind)
  (case kind (:register 0) (:ack 1) (:position 2)
        (:unregister 3) (:bootstrap 4) (:poll 5) (:status 6)
        (:bound-poll 7) (:bound-ack 8)
        (otherwise nil)))
(defun fn-ncl-code-command (code)
  (case code (0 :register) (1 :ack) (2 :position)
        (3 :unregister) (4 :bootstrap) (5 :poll) (6 :status)
        (7 :bound-poll) (8 :bound-ack)
        (otherwise nil)))
(verify-guards fn-ncl-command-code)
(verify-guards fn-ncl-code-command)

(defun fn-ncl-request-encode (kind first second)
  (let* ((code (fn-ncl-command-code kind))
         (payload
          (case kind
            (:bootstrap (and (null first) (null second) (list code)))
            (:register (and (fn-cp-idp first) (fn-cp-idp second)
                            (append (list code) (fn-cp-id-bytes first)
                                    (fn-cp-id-bytes second))))
            (:ack (and (null second)
                       (eq (fn-cp-nth 0 (fn-cp-cursor-decode first)) :ok)
                       (cons code first)))
            ((:position :unregister :poll :status)
             (and (fn-cp-idp first) (null second)
                  (cons code (fn-cp-id-bytes first))))
            ; PRF-234: FIRST the consumer id (bound-poll) or the cursor
            ; (bound-ack), SECOND the account's password.
            (:bound-poll
             (and (fn-cp-idp first) (fn-ncl-secretp second)
                  (append (list code) (fn-cp-id-bytes first)
                          (fn-ncl-secret-bytes second))))
            (:bound-ack
             (and (fn-ncl-secretp second)
                  (eq (fn-cp-nth 0 (fn-cp-cursor-decode first)) :ok)
                  (append (list code) (fn-ncl-secret-bytes second) first)))
            (otherwise nil))))
    (if (and payload (fn-cbor-octet-listp payload)
             (<= (len payload)
                 (if (member kind '(:bound-poll :bound-ack))
                     *fn-ncl-bound-max-payload*
                   *fn-ncl-max-payload*)))
        (fn-nctrl-seal *fn-ncl-request-kind* payload)
      :bad)))

(defun fn-ncl-request-decode (octets)
  (let ((opened (fn-nctrl-open octets *fn-ncl-request-kind*)))
    (if (not (fn-frame-result-okp opened)) (list :refused :frame)
      (let ((payload (fn-frame-result-payload opened)))
        (if (or (not (consp payload))
                (not (fn-cbor-octet-listp payload))
                (not (<= (len payload)
                         (if (member (car payload) '(7 8))
                             *fn-ncl-bound-max-payload*
                           *fn-ncl-max-payload*))))
            (list :refused :size)
          (let ((kind (fn-ncl-code-command (car payload)))
                (body (cdr payload)))
           (case kind
            (:bootstrap
             (if (null body) (list :consumer :bootstrap nil nil)
               (list :refused :bootstrap)))
            (:register
             (let ((one (fn-cp-read-id body)))
               (if (not (eq (fn-cp-nth 0 one) :ok))
                   (list :refused :consumer)
                 (let ((two (fn-cp-read-id (fn-cp-nth 2 one))))
                   (if (and (eq (fn-cp-nth 0 two) :ok)
                            (null (fn-cp-nth 2 two)))
                       (list :consumer :register (fn-cp-nth 1 one)
                             (fn-cp-nth 1 two))
                     (list :refused :group))))))
            (:ack
             (if (eq (fn-cp-nth 0 (fn-cp-cursor-decode body)) :ok)
                 (list :consumer :ack body nil)
               (list :refused :cursor)))
            ((:position :unregister :poll :status)
             (let ((one (fn-cp-read-id body)))
               (if (and (eq (fn-cp-nth 0 one) :ok)
                        (null (fn-cp-nth 2 one)))
                   (list :consumer kind (fn-cp-nth 1 one) nil)
                 (list :refused :consumer))))
            (:bound-poll
             (let ((one (fn-cp-read-id body)))
               (if (not (eq (fn-cp-nth 0 one) :ok))
                   (list :refused :consumer)
                 (let ((two (fn-ncl-read-secret (fn-cp-nth 2 one))))
                   (if (and (eq (fn-cp-nth 0 two) :ok)
                            (null (fn-cp-nth 2 two)))
                       (list :consumer :bound-poll (fn-cp-nth 1 one)
                             (fn-cp-nth 1 two))
                     (list :refused :secret))))))
            (:bound-ack
             (let ((one (fn-ncl-read-secret body)))
               (if (not (eq (fn-cp-nth 0 one) :ok))
                   (list :refused :secret)
                 (if (eq (fn-cp-nth 0 (fn-cp-cursor-decode (fn-cp-nth 2 one)))
                         :ok)
                     (list :consumer :bound-ack (fn-cp-nth 2 one)
                           (fn-cp-nth 1 one))
                   (list :refused :cursor)))))
            (otherwise (list :refused :kind)))))))))

(defun fn-ncl-status-code (status)
  (case status (:accepted 0) (:refused 1) (:uncertain 2)
        (:fault 3) (otherwise nil)))
(defun fn-ncl-code-status (code)
  (case code (0 :accepted) (1 :refused) (2 :uncertain)
        (3 :fault) (otherwise nil)))
(verify-guards fn-ncl-status-code)
(verify-guards fn-ncl-code-status)

(defun fn-ncl-reply-encode (status cursor)
  (let ((code (fn-ncl-status-code status)))
    (if (and code
             (or (null cursor)
                 (and (eq status :accepted)
                      (eq (fn-cp-nth 0 (fn-cp-cursor-decode cursor)) :ok))))
        (fn-nctrl-seal *fn-ncl-reply-kind* (cons code cursor))
      :bad)))

(defun fn-ncl-reply-decode (octets)
  (let ((opened (fn-nctrl-open octets *fn-ncl-reply-kind*)))
    (if (not (fn-frame-result-okp opened)) (list :refused :frame)
      (let ((payload (fn-frame-result-payload opened)))
        (if (and (consp payload)
                 (fn-cbor-octet-listp payload)
                 (<= (len payload) *fn-ncl-max-payload*)
                 (fn-ncl-code-status (car payload))
                 (or (null (cdr payload))
                     (and (eq (fn-ncl-code-status (car payload)) :accepted)
                          (eq (fn-cp-nth 0 (fn-cp-cursor-decode (cdr payload))) :ok))))
            (list :consumer-reply (fn-ncl-code-status (car payload))
                  (cdr payload))
          (list :refused :reply))))))

; Status has its own FNCT kind and fixed scalar grammar.  It cannot be
; mistaken for a cursor reply: accepted carries exactly three uint32 fields
; (committed ACK, journal frontier, event-distance), refusal carries none.
(defun fn-ncl-status-reply-encode (status ack frontier gap)
  (let ((code (fn-ncl-status-code status)))
    (if (if (eq status :accepted)
            (and (fn-cp-uintp ack) (fn-cp-uintp frontier)
                 (fn-cp-uintp gap) (<= ack frontier)
                 (equal gap (- frontier ack)))
          (and code (null ack) (null frontier) (null gap)))
        (let ((payload
               (if (eq status :accepted)
                   (append (list code) (fn-cbor-u32-bytes ack)
                           (fn-cbor-u32-bytes frontier)
                           (fn-cbor-u32-bytes gap))
                 (list code))))
          (fn-nctrl-seal *fn-ncl-status-reply-kind* payload))
      :bad)))

(defun fn-ncl-status-open (octets)
  (declare (xargs :guard t))
  (if (not (fn-cbor-octet-listp octets)) (fn-frame-error :malformed)
    (let ((opened
           (fn-frame-decode
            octets (fn-frame-trailer (fn-frame-protected-prefix octets))
            *fn-ncl-status-max-payload*)))
      (if (and (fn-frame-result-okp opened)
               (equal (fn-frame-result-magic opened) *fn-nctrl-magic*)
               (equal (fn-frame-result-version opened) *fn-nctrl-version*)
               (equal (fn-frame-result-kind opened)
                      *fn-ncl-status-reply-kind*))
          opened
        (fn-frame-error :kind)))))

(defun fn-ncl-status-reply-decode (octets)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (disable fn-cp-nth
                                                            fn-cp-read-fields
                                                            fn-ncl-status-open)))))
  (let ((opened (fn-ncl-status-open octets)))
    (if (not (fn-frame-result-okp opened)) (list :refused :frame)
      (let* ((payload (fn-frame-result-payload opened))
             (status (and (consp payload)
                          (fn-ncl-code-status (car payload)))))
        (cond
         ((or (not status) (not (fn-cbor-octet-listp payload)))
          (list :refused :reply))
         ((eq status :accepted)
          (let ((fields (fn-cp-read-fields (cdr payload)
                                           '(:uint :uint :uint))))
            (if (and (eq (car fields) :ok) (null (fn-cp-nth 2 fields)))
                (let ((vals (fn-cp-nth 1 fields)))
                  (if (and (fn-cp-uintp (fn-cp-nth 0 vals))
                           (fn-cp-uintp (fn-cp-nth 1 vals))
                           (fn-cp-uintp (fn-cp-nth 2 vals))
                           (<= (fn-cp-nth 0 vals) (fn-cp-nth 1 vals))
                           (equal (fn-cp-nth 2 vals)
                                  (- (fn-cp-nth 1 vals)
                                     (fn-cp-nth 0 vals))))
                      (list :consumer-status-reply :accepted
                            (fn-cp-nth 0 vals) (fn-cp-nth 1 vals)
                            (fn-cp-nth 2 vals))
                    (list :refused :reply)))
              (list :refused :reply))))
         ((null (cdr payload))
          (list :consumer-status-reply status nil nil nil))
         (t (list :refused :reply)))))))

; The status encoder uses the same host framing composition as the native
; control encoder.  Keep the frame codec closed except in this decoding proof.
(defthm fn-ncl-status-open-of-sealed-payload
  (implies (and (fn-cbor-octet-listp payload)
                (<= (len payload) *fn-ncl-status-max-payload*))
           (equal (fn-ncl-status-open
                   (fn-nctrl-seal *fn-ncl-status-reply-kind* payload))
                  (fn-frame-ok *fn-nctrl-magic* *fn-nctrl-version*
                               *fn-ncl-status-reply-kind* payload)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-frame-decode-of-host-framing
                            (magic *fn-nctrl-magic*)
                            (version *fn-nctrl-version*)
                            (kind *fn-ncl-status-reply-kind*)
                            (max-payload *fn-ncl-status-max-payload*)))
           :in-theory (e/d (fn-ncl-status-open fn-nctrl-seal
                            fn-frame-inputp fn-frame-magicp
                            fn-frame-protected fn-frame-header
                            fn-cbor-u32-bytes-are-octets
                            fn-frame-octet-listp-of-append)
                           (fn-frame-decode fn-frame-trailer
                            fn-frame-protected-prefix
                            fn-frame-decode-of-host-framing)))))

(defthm fn-ncl-status-accepted-payload-inputp
  (implies (and (fn-cp-uintp ack) (fn-cp-uintp frontier)
                (fn-cp-uintp gap))
           (and (fn-cbor-octet-listp
                 (append '(0) (fn-cbor-u32-bytes ack)
                         (fn-cbor-u32-bytes frontier)
                         (fn-cbor-u32-bytes gap)))
                (equal (len (append '(0) (fn-cbor-u32-bytes ack)
                                    (fn-cbor-u32-bytes frontier)
                                    (fn-cbor-u32-bytes gap)))
                       *fn-ncl-status-max-payload*)))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-cp-uintp fn-cbor-u32-bytes-are-octets
                 fn-frame-octet-listp-of-append fn-cp-u32-bytes-four
                 fn-frame-len-of-append)
                (fn-cbor-u32-bytes binary-append)))))

(defthm fn-ncl-status-fields-roundtrip
  (implies (and (fn-cp-uintp ack) (fn-cp-uintp frontier)
                (fn-cp-uintp gap))
           (equal (fn-cp-read-fields
                   (append (fn-cbor-u32-bytes ack)
                           (fn-cbor-u32-bytes frontier)
                           (fn-cbor-u32-bytes gap))
                   '(:uint :uint :uint))
                  (list :ok (list ack frontier gap) nil)))
  :hints (("Goal"
           :use ((:instance fn-cp-fields-roundtrip
                            (vals (list ack frontier gap))
                            (kinds '(:uint :uint :uint)) (rest nil)))
           :in-theory (e/d (fn-cp-fields-encode fn-cp-fields-validp)
                           (fn-cp-read-fields fn-cp-fields-roundtrip)))))

; KEYSTONE PRF-068: the native host calls the status encoder and decoder in
; host/native-control-host.lisp.  The four premises are precisely the scalar
; and distance constraints accepted by the encoder; none names a decoder arm.
(defthm fn-ncl-status-accepted-reply-roundtrip
  (implies (and (fn-cp-uintp ack)
                (fn-cp-uintp frontier)
                (<= ack frontier)
                (equal gap (- frontier ack)))
           (equal (fn-ncl-status-reply-decode
                   (fn-ncl-status-reply-encode :accepted ack frontier gap))
                  (list :consumer-status-reply :accepted
                        ack frontier gap)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-ncl-status-open-of-sealed-payload
                            (payload
                             (append '(0) (fn-cbor-u32-bytes ack)
                                     (fn-cbor-u32-bytes frontier)
                                     (fn-cbor-u32-bytes gap))))
                 (:instance fn-ncl-status-accepted-payload-inputp))
           :in-theory (e/d (fn-ncl-status-reply-encode
                            fn-ncl-status-reply-decode
                            fn-ncl-status-code fn-ncl-code-status
                            fn-cp-uintp)
                           (fn-ncl-status-open fn-nctrl-seal
                            fn-cp-read-fields fn-frame-decode)))))

(defthm fn-ncl-status-nonaccepted-reply-roundtrip
  (implies (member-eq status '(:refused :uncertain :fault))
           (equal (fn-ncl-status-reply-decode
                   (fn-ncl-status-reply-encode status nil nil nil))
                  (list :consumer-status-reply status nil nil nil)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-ncl-status-open-of-sealed-payload
                            (payload (list (fn-ncl-status-code status)))))
           :in-theory (e/d (fn-ncl-status-reply-encode
                            fn-ncl-status-reply-decode
                            fn-ncl-status-code fn-ncl-code-status)
                           (fn-ncl-status-open fn-nctrl-seal
                            fn-cp-read-fields fn-frame-decode
                            (:executable-counterpart
                             fn-ncl-status-reply-encode))))))

; Poll carries one exact accepted Store event at most.  The two lengths make
; the cursor and report unambiguous without asking raw Lisp to parse either.
(defun fn-ncl-poll-event-bytesp (bytes)
  (and (consp bytes) (fn-cbor-octet-listp bytes)
       (<= (len bytes) *fn-stxa-max-octets*)))

(defun fn-ncl-poll-seal (payload)
  (if (or (not (fn-cbor-octet-listp payload))
          (> (len payload) *fn-ncl-poll-max-payload*))
      :bad
    (let ((protected (fn-frame-protected
                      *fn-nctrl-magic* *fn-nctrl-version*
                      *fn-ncl-poll-reply-kind* payload)))
      (append protected (fn-frame-trailer protected)))))

(defun fn-ncl-poll-open (octets)
  (if (not (fn-cbor-octet-listp octets)) (fn-frame-error :malformed)
    (let ((opened
           (fn-frame-decode
            octets (fn-frame-trailer (fn-frame-protected-prefix octets))
            *fn-ncl-poll-max-payload*)))
      (if (and (fn-frame-result-okp opened)
               (equal (fn-frame-result-magic opened) *fn-nctrl-magic*)
               (equal (fn-frame-result-version opened) *fn-nctrl-version*)
               (equal (fn-frame-result-kind opened)
                      *fn-ncl-poll-reply-kind*))
          opened
        (fn-frame-error :kind)))))

(defun fn-ncl-poll-reply-encode (status cursor report)
  (let ((code (fn-ncl-status-code status)))
    (if (and code
             (if (eq status :accepted)
                 (and (true-listp cursor)
                      (<= (len cursor) 346)
                      (eq (fn-cp-nth 0 (fn-cp-cursor-decode cursor)) :ok)
                      (or (null report) (fn-ncl-poll-event-bytesp report)))
               (and (null cursor) (null report))))
        (let ((payload
               (append (list code) (fn-cbor-u32-bytes (len cursor)) cursor
                       (fn-cbor-u32-bytes (len report)) report)))
          (if (<= (len payload) *fn-ncl-poll-max-payload*)
              (fn-ncl-poll-seal payload)
            :bad))
      :bad)))

(defun fn-ncl-poll-reply-decode (octets)
  (let ((opened (fn-ncl-poll-open octets)))
    (if (not (fn-frame-result-okp opened)) (list :refused :frame)
      (let ((payload (fn-frame-result-payload opened)))
        (if (or (not (consp payload))
                (not (fn-cbor-octet-listp payload))
                (not (<= (len payload) *fn-ncl-poll-max-payload*)))
            (list :refused :size)
          (let* ((status (fn-ncl-code-status (car payload)))
                 (one (fn-cp-read-u32 (cdr payload)))
                 (n (fn-cp-nth 1 one))
                 (rest (fn-cp-nth 2 one)))
            (if (or (not status) (not (eq (car one) :ok))
                    (not (natp n))
                    (> n 346) (< (len rest) n))
                (list :refused :cursor)
              (let* ((cursor (take n rest))
                     (two (fn-cp-read-u32 (nthcdr n rest)))
                     (m (fn-cp-nth 1 two))
                     (body (fn-cp-nth 2 two)))
                (if (or (not (eq (car two) :ok))
                        (not (natp m))
                        (> m *fn-stxa-max-octets*)
                        (not (equal (len body) m)))
                    (list :refused :report)
                  (if (if (eq status :accepted)
                          (and (eq (fn-cp-nth 0
                                    (fn-cp-cursor-decode cursor)) :ok)
                               (or (null body) (fn-ncl-poll-event-bytesp body)))
                        (and (null cursor) (null body)))
                      (list :consumer-poll-reply status cursor body)
                    (list :refused :reply)))))))))))

; CLI grammar is ACL2-owned too.  The raw executable only converts bounded
; argv text to octets, reads the named ack-token file, and transports bytes.
(defun fn-ncl-absolute-pathp (path)
  (and (consp path) (equal (car path) 47)
       (fn-cbor-at-mostp path *fn-ncfg-max-path*)
       (fn-cbor-octet-listp path)
       (not (member-equal 0 path))))

(defun fn-ncl-cli-plan (command argv)
  (let ((control (fn-cp-nth 0 argv))
        (id (fn-cp-nth 1 argv))
        (third (fn-cp-nth 2 argv))
        (fourth (fn-cp-nth 3 argv)))
    (cond
     ; PKT-709: `fn consumer' and `fn consumer help' print the grammar
     ; (fn-ncl-usage-text), not `missing arguments'.
     ((equal command '(104 101 108 112)) (list :help)) ; help
     ((not (fn-ncl-absolute-pathp control)) (list :usage :control-path))
     ((equal command '(98 111 111 116 115 116 114 97 112)) ; bootstrap
      (if (equal (len argv) 1)
          (list :run :bootstrap control nil nil nil)
        (list :usage :bootstrap)))
     ((equal command '(114 101 103 105 115 116 101 114)) ; register
      (if (and (equal (len argv) 4)
               (fn-cp-idp id) (fn-ncfg-printablep id)
               (fn-cp-idp third) (fn-af-newsgroup-namep third)
               (fn-ncl-absolute-pathp fourth))
          (list :run :register control id third fourth)
        (list :usage :register)))
     ((equal command '(112 111 115 105 116 105 111 110)) ; position
      (if (and (equal (len argv) 3)
               (fn-cp-idp id) (fn-ncfg-printablep id)
               (fn-ncl-absolute-pathp third))
          (list :run :position control id nil third)
        (list :usage :position)))
     ((equal command '(112 111 108 108)) ; poll
      (if (and (equal (len argv) 4)
               (fn-cp-idp id) (fn-ncfg-printablep id)
               (fn-ncl-absolute-pathp third)
               (fn-ncl-absolute-pathp fourth)
               (not (equal third fourth)))
          (list :run :poll control id third fourth)
        (list :usage :poll)))
     ((equal command '(115 116 97 116 117 115)) ; status
      (if (and (equal (len argv) 2)
               (fn-cp-idp id) (fn-ncfg-printablep id))
          (list :run :status control id nil nil)
        (list :usage :status)))
     ((equal command '(97 99 107)) ; ack
      (if (and (equal (len argv) 2) (fn-ncl-absolute-pathp id))
          (list :run :ack control id nil nil)
        (list :usage :ack)))
     ; PRF-234: `bound-poll CONTROL NAME SECRET-FILE CURSOR REPORT' and
     ; `bound-ack CONTROL CURSOR-FILE SECRET-FILE'.  The password is read
     ; from a file (never argv, which other local users can list); the
     ; plan's seventh element names it.
     ((equal command '(98 111 117 110 100 45 112 111 108 108)) ; bound-poll
      (let ((fifth (fn-cp-nth 4 argv)))
        (if (and (equal (len argv) 5)
                 (fn-cp-idp id) (fn-ncfg-printablep id)
                 (fn-ncl-absolute-pathp third)
                 (fn-ncl-absolute-pathp fourth)
                 (fn-ncl-absolute-pathp fifth)
                 (not (equal fourth fifth))
                 (not (equal third fourth))
                 (not (equal third fifth)))
            (list :run :bound-poll control id fourth fifth third)
          (list :usage :bound-poll))))
     ((equal command '(98 111 117 110 100 45 97 99 107)) ; bound-ack
      (if (and (equal (len argv) 3) (fn-ncl-absolute-pathp id)
               (fn-ncl-absolute-pathp third))
          (list :run :bound-ack control id nil nil third)
        (list :usage :bound-ack)))
     ((equal command '(117 110 114 101 103 105 115 116 101 114)) ; unregister
      (if (and (equal (len argv) 2)
               (fn-cp-idp id) (fn-ncfg-printablep id))
          (list :run :unregister control id nil nil)
        (list :usage :unregister)))
     (t (list :usage :command)))))

;; PKT-709 (the stranger rehearsal, 2026-09-27): the grammar this plan
;; accepts, as the one usage text the host prints for `help', for no words
;; and after every usage refusal.  CONTROL is the node's control socket
;; ([control] path in fn.toml).
(defun fn-ncl-usage-text ()
  (declare (xargs :guard t))
  "usage: fn consumer [--json] COMMAND CONTROL ...  (CONTROL is the node's control socket, [control] path in fn.toml; every path is absolute)
  register CONTROL NAME GROUP CURSOR-OUT   declare consumer NAME for GROUP (bootstraps the node's consumer history first when needed) and write its first cursor
  position CONTROL NAME CURSOR-OUT         write NAME's committed cursor again
  poll CONTROL NAME CURSOR-OUT REPORT-OUT  write the next event's report and its cursor (read-only; nothing is acknowledged)
  wait CONTROL NAME CURSOR-OUT REPORT-OUT --timeout S   poll, sleeping up to S seconds (at most 3600) for an event
  ack CONTROL CURSOR-FILE                  acknowledge up to the cursor a poll wrote
  bound-poll CONTROL NAME SECRET-FILE CURSOR-OUT REPORT-OUT   poll as a consumer bound to an account (operator: consumer bind NAME --account LOGIN)
  bound-wait CONTROL NAME SECRET-FILE CURSOR-OUT REPORT-OUT --timeout S
  bound-ack CONTROL CURSOR-FILE SECRET-FILE
  status CONTROL NAME                      committed ack, journal frontier and the distance between them
  unregister CONTROL NAME
  bootstrap CONTROL                        make the node's consumer history (register does this itself)
--json prints one JSON line: command, outcome, reason and, for a poll or wait, the report (article, withdrawn or empty) and its Message-ID.
A refusal names its reason (consumer refused unknown-consumer).  fn consumer-article [--json] REPORT prints what a report holds.
docs/agents.md, Local consumers")

; PRF-234: the password a secret file holds: its octets less one final
; line end (LF or CRLF), so `echo PASSWORD > FILE' holds PASSWORD.
(defun fn-ncl-secret-of-file (octets)
  (declare (xargs :guard (true-listp octets)))
  (let ((xs (if (and (consp octets) (equal (car (last octets)) 10))
                (butlast octets 1)
              octets)))
    (if (and (consp xs) (equal (car (last xs)) 13))
        (butlast xs 1)
      xs)))

(verify-guards fn-ncl-secretp)
(verify-guards fn-ncl-secret-bytes)
(verify-guards fn-ncl-read-secret)
(verify-guards fn-ncl-secret-of-file)
(verify-guards fn-ncl-request-encode)
(verify-guards fn-ncl-request-decode)
(verify-guards fn-ncl-reply-encode)
(verify-guards fn-ncl-reply-decode)
(verify-guards fn-ncl-status-reply-encode)
(verify-guards fn-ncl-status-open)
(verify-guards fn-ncl-status-reply-decode)
(verify-guards fn-ncl-poll-event-bytesp)
(verify-guards fn-ncl-poll-seal)
(verify-guards fn-ncl-poll-open)
(verify-guards fn-ncl-poll-reply-encode)
(verify-guards fn-ncl-poll-reply-decode)
(verify-guards fn-ncl-absolute-pathp)
(verify-guards fn-ncl-cli-plan)
