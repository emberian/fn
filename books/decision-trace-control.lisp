; fn: `fn operator CONFIG trace on|off|drain', the control frames (lane
; obs-decision-trace; observability program section 2a).
;
; FNCT kind 26 is the request (the verb, and for `drain' the sequence number
; the client has seen: rows at most that are freed), kind 27 the reply (the
; status, a reason word, and the lines: `FN_TRACE {...}' JSON rows the host
; rendered from ACL2's records after the ring's lock was released).  Kinds 1
; to 25 are books/native-control*.lisp, tls-reload.lisp, wire-family-identity's.
;
; The kind is classified :read (books/native-control-kinds.lisp): it writes no
; store, so a disk-stall shed (PRF-311) never refuses it.  `fn-dtrace-verb'
; (books/decision-trace.lisp) decides what a verb does; the host applies it.
; An owner that predates kind 26 answers the plain refusal (kind 2) to a frame
; it cannot decode, read by the client as :owner-lacks-trace.

(in-package "ACL2")
(include-book "native-control")
(include-book "native-control-reason")
(include-book "decision-trace")

(defconst *fn-dtrace-request-kind* 26)
(defconst *fn-dtrace-reply-kind* 27)
(defconst *fn-dtrace-drain-rows* 64)       ; rows per drain, at most
(defconst *fn-dtrace-max-lines* *fn-record-max-payload*)
(defconst *fn-dtrace-request-spec* (list (cons :enum '(:on :off :drain)) :nat))
(defconst *fn-dtrace-reply-spec*
  (list (cons :enum *fn-nctrl-statuses*)
        (cons :blob *fn-nctrl-max-reason-octets*)
        (cons :blob *fn-dtrace-max-lines*)))

; Rows per drain, at most; the host asks (an operator action, not the served
; path: the rows pass through one octet list of at most this many).
(defun fn-dtrace-drain-limit ()
  (declare (xargs :guard t))
  *fn-dtrace-drain-rows*)

(defun fn-dtrace-request-encode (verb since)
  (declare (xargs :guard t))
  (let ((values (list verb since)))
    (if (not (and (member-eq verb '(:on :off :drain))
                  (natp since) (< since 18446744073709551616)
                  (fn-frame-values-okp *fn-dtrace-request-spec* values)))
        :bad
      (fn-nctrl-seal *fn-dtrace-request-kind*
                     (fn-frame-fields-octets *fn-dtrace-request-spec* values)))))

; (VERB SINCE), or nil for any other frame.
(defun fn-dtrace-request-decode (octets)
  (declare (xargs :guard (fn-cbor-octet-listp octets)))
  (let ((opened (fn-nctrl-open octets *fn-dtrace-request-kind*)))
    (if (not (fn-frame-result-okp opened))
        nil
      (let ((payload (fn-frame-result-payload opened)))
        (if (not (fn-cbor-octet-listp payload))
            nil
          (let ((fields (fn-frame-fields-parse *fn-dtrace-request-spec* payload)))
            (if (not (fn-frame-parse-okp fields))
                nil
              (let ((values (fn-frame-parse-value fields)))
                (if (and (true-listp values) (equal (len values) 2)
                         (member-eq (car values) '(:on :off :drain)))
                    values
                  nil)))))))))

(defun fn-dtrace-reply-encode (status reason lines)
  (declare (xargs :guard t))
  (let ((values (list status (fn-nctrl-reason-word reason) lines)))
    (if (not (and (member-equal status *fn-nctrl-statuses*)
                  (fn-frame-values-okp *fn-dtrace-reply-spec* values)))
        :bad
      (fn-nctrl-seal *fn-dtrace-reply-kind*
                     (fn-frame-fields-octets *fn-dtrace-reply-spec* values)))))

; What the client reads: (STATUS WORD LINES) from a kind-27 reply; an owner
; that predates kind 26 answers the plain kind 2 status, read as that status
; with the word owner-lacks-trace and no lines; else :bad.
(defun fn-dtrace-reply-read (octets)
  (declare (xargs :guard (fn-cbor-octet-listp octets)))
  (let ((opened (fn-nctrl-open octets *fn-dtrace-reply-kind*)))
    (if (fn-frame-result-okp opened)
        (let ((payload (fn-frame-result-payload opened)))
          (if (not (fn-cbor-octet-listp payload))
              :bad
            (let ((fields (fn-frame-fields-parse *fn-dtrace-reply-spec* payload)))
              (if (not (fn-frame-parse-okp fields))
                  :bad
                (let ((values (fn-frame-parse-value fields)))
                  (if (and (true-listp values) (equal (len values) 3))
                      values
                    :bad))))))
      (let ((plain (fn-native-control-reply-decode octets)))
        (if (member-equal plain *fn-nctrl-statuses*)
            (list plain (fn-record-string-octets "owner-lacks-trace") nil)
          :bad)))))

; The answer of a verb the plan refused or an action it took, as the reply's
; (STATUS REASON): :accepted with no reason, or :refused with the name.
(defun fn-dtrace-verb-status (decision)
  (declare (xargs :guard t))
  (if (and (true-listp decision) (equal (car decision) :refused) (consp (cdr decision)))
      (list :refused (cadr decision))
    (list :accepted nil)))

; The line ACL2 renders for a verb that returns no rows (a frame's blob is not
; empty): the tracing state after it, or the refusal.
(defun fn-dtrace-status-line (word)
  (declare (xargs :guard t))
  (fn-record-string-octets
   (cond ((equal word :on) "FN_TRACE {\"v\":2,\"type\":\"trace\",\"state\":\"on\"}")
         ((equal word :off) "FN_TRACE {\"v\":2,\"type\":\"trace\",\"state\":\"off\"}")
         (t "FN_TRACE {\"v\":2,\"type\":\"trace\",\"state\":\"refused\"}"))))

; Witnesses (the teeth).  A request round-trips; another kind's frame is no
; request; a reply round-trips with its lines; an old owner's plain status is
; read as a refusal by name.
(defthm fn-dtrace-request-round-trips
  (and (equal (fn-dtrace-request-decode (fn-dtrace-request-encode :drain 41)) '(:drain 41))
       (equal (fn-dtrace-request-decode (fn-dtrace-request-encode :on 0)) '(:on 0))
       (equal (fn-dtrace-request-decode (fn-dtrace-request-encode :off 0)) '(:off 0))
       (equal (fn-dtrace-request-encode :flush 0) :bad)
       (equal (fn-dtrace-request-encode :drain 18446744073709551616) :bad)
       (null (fn-dtrace-request-decode nil))
       (null (fn-dtrace-request-decode (fn-dtrace-reply-encode :accepted nil (fn-dtrace-status-line :on)))))
  :rule-classes nil)

(defthm fn-dtrace-reply-round-trips
  (let ((lines (fn-record-string-octets "FN_TRACE {}")))
    (and (equal (fn-dtrace-reply-read (fn-dtrace-reply-encode :accepted nil lines))
                (list :accepted (fn-nctrl-reason-word nil) lines))
         (equal (car (fn-dtrace-reply-read
                      (fn-dtrace-reply-encode :refused :not-configured
                                              (fn-dtrace-status-line :refused))))
                :refused)
         ;; an empty blob is no frame: a reply always carries a line
         (equal (fn-dtrace-reply-encode :accepted nil nil) :bad)))
  :rule-classes nil)
