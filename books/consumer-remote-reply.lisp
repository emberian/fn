; Logical FNCR reply grammar. Framing/status decisions belong to ACL2.
; The native writer still owes bounded concrete encoding, installed BODY and
; retained source recheck. This reference codec is not a TLS/durability proof.
(in-package "ACL2")
(include-book "consumer-remote-fields")
(include-book "frame-fields")
(include-book "frame-trailer")

(defconst *fn-crr-magic* '(70 78 67 82))
(defconst *fn-crr-statuses* '(:accepted :refused :uncertain :unavailable))
(defconst *fn-crr-kinds* '(:progress :position :status :poll))

(defun fn-crr-spec (record-ceiling)
 (declare (xargs :guard t))
 (list (cons :enum *fn-crr-statuses*) (cons :enum *fn-crr-kinds*)
       (cons :blob (1+ *fn-cp-max-token*)) :nat :nat :nat (cons :blob (1+ (nfix record-ceiling)))))

(defun fn-crr-profilep (record-ceiling)
 (declare (xargs :guard t))
 (and (posp record-ceiling) (fn-frame-spec-listp (fn-crr-spec record-ceiling))
      (<= (fn-frame-specs-width (fn-crr-spec record-ceiling)) *fn-frame-max-payload*)))

; Fixed8, with exact zero/empty unused fields. No login/credential/principal
; is disclosed. :uncertain and :unavailable are distinct wire statuses.
(defun fn-crr-replyp (reply record-ceiling)
 (declare (xargs :guard t))
 (let ((status (fn-cp-nth 1 reply)) (kind (fn-cp-nth 2 reply))
       (cursor (fn-cp-nth 3 reply)) (ack (fn-cp-nth 4 reply))
       (frontier (fn-cp-nth 5 reply)) (gap (fn-cp-nth 6 reply))
       (report (fn-cp-nth 7 reply)))
  (and (fn-cbor-at-mostp reply 8) (true-listp reply) (equal (len reply) 8)
       (eq (car reply) :remote-reply) (member-eq status *fn-crr-statuses*)
       (member-eq kind *fn-crr-kinds*)
       (fn-cbor-at-mostp cursor *fn-cp-max-token*) (fn-cbor-octet-listp cursor)
       (fn-cp-uintp ack) (fn-cp-uintp frontier) (fn-cp-uintp gap)
       (fn-cbor-at-mostp report (nfix record-ceiling)) (fn-cbor-octet-listp report)
       (if (not (eq status :accepted))
           (and (if (and (eq status :unavailable) (eq kind :poll))
                        (eq (fn-cp-nth 0 (fn-cp-cursor-decode cursor)) :ok)
                      (null cursor))
                (equal ack 0) (equal frontier 0) (equal gap 0) (null report))
         (case kind
          (:status (and (null cursor) (<= ack frontier) (equal gap (- frontier ack)) (null report)))
          (:poll (and (eq (fn-cp-nth 0 (fn-cp-cursor-decode cursor)) :ok)
                      (equal ack 0) (equal frontier 0) (equal gap 0)))
          (:progress
           (and (or (null cursor) (eq (fn-cp-nth 0 (fn-cp-cursor-decode cursor)) :ok))
                (equal ack 0) (equal frontier 0) (equal gap 0) (null report)))
          (:position
           (and (eq (fn-cp-nth 0 (fn-cp-cursor-decode cursor)) :ok)
                (equal ack 0) (equal frontier 0) (equal gap 0) (null report)))
          (otherwise nil))))))

 ; Nullable blob has an explicit tag. Empty is (0); nonempty is (1 . bytes),
; so a real one-octet zero report is never confused with absence.
(defun fn-crr-wire-values (reply)
 (declare (xargs :guard t))
 (let ((cursor (fn-cp-nth 3 reply)) (report (fn-cp-nth 7 reply)))
  (list (fn-cp-nth 1 reply) (fn-cp-nth 2 reply)
        (if cursor (cons 1 cursor) '(0))
        (fn-cp-nth 4 reply) (fn-cp-nth 5 reply) (fn-cp-nth 6 reply)
        (if report (cons 1 report) '(0)))))

(defun fn-crr-optional-blob (blob)
 (declare (xargs :guard t))
 (cond ((equal blob '(0)) '(:blob nil))
       ((and (consp blob) (equal (car blob) 1) (consp (cdr blob))) (list :blob (cdr blob)))
       (t '(:refused :reply-blob))))

(defun fn-crr-encode-reference (reply record-ceiling)
 (declare (xargs :guard t
   :guard-hints (("Goal" :in-theory (e/d (fn-crr-profilep)
                              (fn-crr-spec fn-crr-replyp fn-frame-values-okp))))))
 (if (not (and (consp reply) (fn-crr-profilep record-ceiling) (fn-crr-replyp reply record-ceiling)
                (fn-frame-values-okp (fn-crr-spec record-ceiling) (fn-crr-wire-values reply)))) :bad
  (let ((payload (fn-frame-fields-octets (fn-crr-spec record-ceiling) (fn-crr-wire-values reply))))
   (if (not (and (fn-cbor-octet-listp payload) (<= (len payload) *fn-frame-max-payload*))) :bad
    (let ((protected (fn-frame-protected *fn-crr-magic* 1 2 payload)))
     (append protected (fn-frame-trailer protected)))))))

(defun fn-crr-decode-reference (octets record-ceiling)
 (declare (xargs :guard t
   :guard-hints (("Goal" :in-theory (e/d (fn-crr-profilep)
                              (fn-crr-spec fn-crr-replyp fn-frame-specs-width))))))
 (if (not (and (fn-crr-profilep record-ceiling)
               (fn-cbor-at-mostp octets (+ *fn-frame-overhead-octets* (fn-frame-specs-width (fn-crr-spec record-ceiling))))
               (fn-cbor-octet-listp octets))) '(:refused :reply-size)
  (let ((opened (fn-frame-decode octets (fn-frame-trailer (fn-frame-protected-prefix octets))
                                 (fn-frame-specs-width (fn-crr-spec record-ceiling)))))
   (if (not (and (fn-frame-result-okp opened) (equal (fn-frame-result-magic opened) *fn-crr-magic*)
                  (equal (fn-frame-result-version opened) 1) (equal (fn-frame-result-kind opened) 2)
                  (fn-cbor-octet-listp (fn-frame-result-payload opened))))
       '(:refused :reply-frame)
    (let* ((parsed (fn-frame-fields-parse (fn-crr-spec record-ceiling) (fn-frame-result-payload opened)))
           (values (fn-frame-parse-value parsed))
           (cursor (fn-crr-optional-blob (fn-cp-nth 2 values)))
           (report (fn-crr-optional-blob (fn-cp-nth 6 values)))
           (reply (list :remote-reply (fn-cp-nth 0 values) (fn-cp-nth 1 values)
                        (fn-cp-nth 1 cursor) (fn-cp-nth 3 values) (fn-cp-nth 4 values)
                        (fn-cp-nth 5 values) (fn-cp-nth 1 report))))
     (if (and (fn-frame-parse-okp parsed) (eq (fn-cp-nth 0 cursor) :blob)
              (eq (fn-cp-nth 0 report) :blob) (fn-crr-replyp reply record-ceiling))
         reply '(:refused :reply-fields)))))))

(in-theory (disable fn-crr-wire-values fn-crr-optional-blob fn-crr-spec fn-crr-profilep fn-crr-replyp fn-crr-encode-reference fn-crr-decode-reference))
