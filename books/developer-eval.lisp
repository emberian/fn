; fn: the developer image's `eval' request (lane obs-dev-eval, program
; build/coordinator/OBSERVABILITY-PROGRAM-20261007.md section 2c; RP-1 to RP-3).
;
; A developer image evaluates one Lisp form inside a running node's owner
; quantum (host/native/developer-eval.lisp), asked over the node's existing
; control socket by `fn operator CONFIG eval'.  This book is the part of that
; request ACL2 decides:
;
;   * the two frames, FNCT kind 40 (the request: the form's octets) and kind
;     41 (the reply: the status word and the evaluation's output);
;   * `fn-deval-admit', whether a request is evaluated at all, from the
;     observations the host makes (the profile the image was saved with, the
;     peer's UID, the owner's UID, the frame's length, whether the node is
;     stopping).  KEYSTONE fn-deval-admits-only-the-developer-operator;
;   * the one kind the control classifier adds for this image
;     (fn-deval-extra-kinds, attached to books/native-control-kinds.lisp's
;     fn-ctlk-extra-kinds), so the host asks its handler chain about the
;     frame and about no other frame it did not already ask about.
;
; ABSENT FROM PRODUCTION BY CONSTRUCTION.  Nothing in a production image's
; world includes this book: host/native/build.lisp includes it only when
; FN_NATIVE_PROFILE is `developer', so a production world has no `fn-deval-'
; symbol, its classifier answers nil for kind 40 (the default attachment), and
; the frame is refused as the unknown kind it is.  tools/extract/closure_why.py
; bans the prefix from the extracted core, and
; tests/test_developer_surface_absent.py checks the saved images and the core.
;
; The lines the owner logs around an evaluation are rendered by
; books/owner-log.lisp (fn-olog-developer-eval-*) and the journal entry by
; books/owner-time-journal.lisp (fn-otm-eval-step): a production book may
; render a line about an event only a developer node has, as replay of a
; developer node's journal must read it.
;
; This book owns the prefix `fn-deval-' (docs/prefixes.md).

(in-package "ACL2")
(include-book "native-control")
(include-book "native-control-kinds")
(include-book "owner-log")
(include-book "owner-time-journal")
(include-book "definterface")

;; The tau system is off in this book (lane tau-pass, tools/tau_cost.py).
(local (in-theory (disable (tau-system))))

; -----------------------------------------------------------------------------
; The frames

(defconst *fn-deval-request-kind* 40)
(defconst *fn-deval-reply-kind* 41)

; The form's bound, in octets (the evaluator's input bound before this book).
(defconst *fn-deval-max-form-octets* 65536)

;
; The evaluator keeps at most this many characters of what a form prints
; (host/native/developer-eval.lisp reads it from here), then appends a note of
; at most *fn-deval-truncation-note-octets* octets.  A character is at most
; four octets of UTF-8, so the reply's output field is bounded by
; *fn-deval-max-output-octets*, and the whole reply frame by what a client
; reads of a control reply (fn-deval-reply-fits-the-clients-read-bound).
(defconst *fn-deval-max-output-characters* 65536)
(defconst *fn-deval-truncation-note-octets* 64)
(defconst *fn-deval-max-output-octets*
  (+ (* 4 *fn-deval-max-output-characters*) *fn-deval-truncation-note-octets*))
(defun fn-deval-max-output-characters ()
  (declare (xargs :guard t))
  *fn-deval-max-output-characters*)

(defconst *fn-deval-statuses*
  '(:ok :error :not-developer :not-the-operator :too-large :stopping))

(defconst *fn-deval-request-spec* (list (cons :blob *fn-deval-max-form-octets*)))
(defconst *fn-deval-reply-spec*
  (list (cons :enum *fn-deval-statuses*) (cons :blob *fn-deval-max-output-octets*)))

; The longest request frame this image admits (header, the form at its bound,
; trailer): the host passes it as `fn-deval-admit's MAX-OCTETS.
(defun fn-deval-max-frame-octets ()
  (declare (xargs :guard t))
  (+ *fn-frame-overhead-octets* (fn-frame-specs-width *fn-deval-request-spec*)))

;; A reply with the longest output the evaluator can keep is a frame a client
;; reads: it is within the bound a control reply is read under
;; (books/native-control.lisp *fn-nctrl-max-command-frame*), and within the
;; payload every FNCT frame carries.
(defthm fn-deval-reply-fits-the-clients-read-bound
  (and (<= (+ *fn-frame-overhead-octets* (fn-frame-specs-width *fn-deval-reply-spec*))
           *fn-nctrl-max-command-frame*)
       (<= (fn-frame-specs-width *fn-deval-reply-spec*) *fn-nctrl-max-payload*))
  :rule-classes nil)

(defun fn-deval-request-encode (form)
  ; A non-empty form of at most *fn-deval-max-form-octets* octets; else :bad.
  (declare (xargs :guard (fn-cbor-octet-listp form)))
  (if (and (fn-cbor-octet-listp form) (consp form)
           (fn-frame-values-okp *fn-deval-request-spec* (list form)))
      (fn-nctrl-seal *fn-deval-request-kind*
                     (fn-frame-fields-octets *fn-deval-request-spec* (list form)))
    :bad))

(defun fn-deval-request-decode (octets)
  ; The form's octets, or nil for any other frame.
  (declare (xargs :guard (fn-cbor-octet-listp octets)))
  (let ((opened (fn-nctrl-open octets *fn-deval-request-kind*)))
    (if (not (fn-frame-result-okp opened))
        nil
      (let ((payload (fn-frame-result-payload opened)))
        (if (not (fn-cbor-octet-listp payload))
            nil
          (let ((fields (fn-frame-fields-parse *fn-deval-request-spec* payload)))
            (if (not (fn-frame-parse-okp fields))
                nil
              (let ((values (fn-frame-parse-value fields)))
                (if (and (true-listp values) (consp values) (consp (car values)))
                    (car values)
                  nil)))))))))

; A frame blob is never empty: an evaluation that printed nothing is answered
; with one LF.
(defun fn-deval-reply-output (output)
  (declare (xargs :guard (fn-cbor-octet-listp output)))
  (if (consp output) output (list 10)))

(defun fn-deval-reply-encode (status output)
  ; The sealed reply, or :bad when STATUS is not one of the statuses or
  ; OUTPUT is not octets within the output bound.
  (declare (xargs :guard (fn-cbor-octet-listp output)))
  (let ((values (list status (fn-deval-reply-output output))))
    (if (and (member-eq status *fn-deval-statuses*)
             (fn-frame-values-okp *fn-deval-reply-spec* values))
        (fn-nctrl-seal *fn-deval-reply-kind*
                       (fn-frame-fields-octets *fn-deval-reply-spec* values))
      :bad)))

(defun fn-deval-reply-read (octets)
  ; (STATUS OUTPUT) from a kind-41 reply, or :bad.
  (declare (xargs :guard (fn-cbor-octet-listp octets)))
  (let ((opened (fn-nctrl-open octets *fn-deval-reply-kind*)))
    (if (not (fn-frame-result-okp opened))
        :bad
      (let ((payload (fn-frame-result-payload opened)))
        (if (not (fn-cbor-octet-listp payload))
            :bad
          (let ((fields (fn-frame-fields-parse *fn-deval-reply-spec* payload)))
            (if (not (fn-frame-parse-okp fields))
                :bad
              (let ((values (fn-frame-parse-value fields)))
                (if (and (true-listp values) (equal (len values) 2))
                    values
                  :bad)))))))))

; -----------------------------------------------------------------------------
; Admission

; THE FUNCTION THE HOST CALLS (host/native/developer-eval.lisp
; fnn-deval-control-handle).  PROFILE is the image profile the host saved the
; image with; PEER-UID the UID of the process on the other end of the control
; socket (nil when the host could not observe it); OWNER-UID the node
; process's own; OCTETS the request frame's length; MAX-OCTETS
; `fn-deval-max-frame-octets'; STOPPING whether the node is shutting down.
; The first condition that fails names the refusal, in this order.
(defun fn-deval-admit (profile peer-uid owner-uid octets max-octets stopping)
  (declare (xargs :guard t))
  (cond ((not (equal profile :developer)) '(:refused :not-developer))
        ((not (and (natp peer-uid) (equal peer-uid owner-uid)))
         '(:refused :not-the-operator))
        ((not (and (natp octets) (natp max-octets) (<= octets max-octets)))
         '(:refused :too-large))
        (stopping '(:refused :stopping))
        (t :admit)))

; The reply status a refusal is answered with: the reason, which is also a
; reply status.
(defun fn-deval-refusal-status (verdict)
  (declare (xargs :guard t))
  (if (and (consp verdict) (equal (car verdict) :refused) (consp (cdr verdict))
           (member-eq (cadr verdict) *fn-deval-statuses*))
      (cadr verdict)
    :error))

; KEYSTONE (RP-2).  A request is admitted exactly when the image is a
; developer image, the peer is the node's own operator (the same UID, and a
; UID observed at all), the frame is within its bound, and the node is not
; stopping.  No hypothesis.
(defthm fn-deval-admits-only-the-developer-operator
  (equal (equal (fn-deval-admit profile peer-uid owner-uid octets max-octets stopping)
                :admit)
         (and (equal profile :developer)
              (natp peer-uid)
              (equal peer-uid owner-uid)
              (natp octets)
              (natp max-octets)
              (<= octets max-octets)
              (not stopping))))

; Each condition alone, with the earlier ones holding, is refused by its name.
(defthm fn-deval-refuses-a-production-image
  (implies (not (equal profile :developer))
           (equal (fn-deval-admit profile peer-uid owner-uid octets max-octets stopping)
                  '(:refused :not-developer))))

(defthm fn-deval-refuses-another-user
  (implies (and (equal profile :developer)
                (not (and (natp peer-uid) (equal peer-uid owner-uid))))
           (equal (fn-deval-admit profile peer-uid owner-uid octets max-octets stopping)
                  '(:refused :not-the-operator))))

(defthm fn-deval-refuses-an-oversize-frame
  (implies (and (equal profile :developer)
                (natp peer-uid) (equal peer-uid owner-uid)
                (not (and (natp octets) (natp max-octets) (<= octets max-octets))))
           (equal (fn-deval-admit profile peer-uid owner-uid octets max-octets stopping)
                  '(:refused :too-large))))

(defthm fn-deval-refuses-a-stopping-node
  (implies (and (equal profile :developer)
                (natp peer-uid) (equal peer-uid owner-uid)
                (natp octets) (natp max-octets) (<= octets max-octets)
                stopping)
           (equal (fn-deval-admit profile peer-uid owner-uid octets max-octets stopping)
                  '(:refused :stopping))))

; A refusal is answered with a status of the reply's own table.
(defthm fn-deval-refusal-status-is-a-reply-status
  (member-eq (fn-deval-refusal-status
              (fn-deval-admit profile peer-uid owner-uid octets max-octets stopping))
             *fn-deval-statuses*)
  :hints (("Goal" :in-theory (enable fn-deval-refusal-status fn-deval-admit))))

; -----------------------------------------------------------------------------
; The classifier's addition

(defconst *fn-deval-extra-kinds*
  (list (cons *fn-deval-request-kind* :read)))

(defun fn-deval-extra-kinds ()
  (declare (xargs :guard t))
  *fn-deval-extra-kinds*)

; The request is a read: it writes no Store, so a stalled disk's shed does
; not answer it BUSY (the evaluator is how a developer looks at that disk).
; Logically the classifier still reads the constrained table; the attachment
; is what executes (tests/acl2/developer-eval-tests.lisp evaluates the
; classifier on a real request frame, and tests/acl2/native-control-kinds-tests
; on the same frame in a world without this book).
(defattach fn-ctlk-extra-kinds fn-deval-extra-kinds)

; -----------------------------------------------------------------------------
; The host entries (host/native/developer-eval.lisp), declared here and not in
; host/interfaces.lisp: a production world does not include this book, so it
; carries no declaration of an entry it does not define
; (tools/interface_emit.py reads this file as one of its SOURCES).

(definterface fn-deval-admit
  :class :common-lisp-compliant
  :keystones (fn-deval-admits-only-the-developer-operator))
(definterface fn-deval-max-frame-octets
  :class :common-lisp-compliant)
(definterface fn-deval-max-output-characters
  :class :common-lisp-compliant)
(definterface fn-deval-request-encode
  :class :common-lisp-compliant
  :kinds ((form fn-cbor-octet-listp)))
(definterface fn-deval-request-decode
  :class :common-lisp-compliant
  :kinds ((octets fn-cbor-octet-listp)))
(definterface fn-deval-reply-encode
  :class :common-lisp-compliant
  :kinds ((output fn-cbor-octet-listp)))
(definterface fn-deval-reply-read
  :class :common-lisp-compliant
  :kinds ((octets fn-cbor-octet-listp)))
(definterface fn-deval-refusal-status
  :class :common-lisp-compliant)

; The production books' functions this host file calls for its three lines
; and its journal entry.
(definterface fn-olog-developer-eval-begin-line
  :class :common-lisp-compliant
  :kinds ((digest fn-cbor-octet-listp)))
(definterface fn-olog-developer-eval-end-line
  :class :common-lisp-compliant)
(definterface fn-olog-developer-eval-refused-line
  :class :common-lisp-compliant)
(definterface fn-otm-eval-step
  :class :common-lisp-compliant
  :keystones ((fn-otm-replay-stops-at-the-developer-eval-entry :via fn-otm-eval-mark)))
