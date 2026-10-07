; Teeth for books/developer-eval.lisp and its two production-book companions
; (lane obs-dev-eval; build/coordinator/OBSERVABILITY-PROGRAM-20261007.md
; section 3, RP-2 and the book half of RP-3).
;
; 1. KEYSTONE fn-deval-admits-only-the-developer-operator (RP-2), per literal
;    theorem: a reachable positive witness asserting the complete antecedent
;    and the admission; per hypothesis, a hypothesis-removal witness that
;    affirms every retained hypothesis, the failure of the omitted one and the
;    failure of the conclusion, with the refusal named, and a `must-fail' of
;    the admission with that hypothesis omitted.  Mutation witnesses
;    (labelled) are separate: four mutants of fn-deval-admit, each admitting a
;    request the keystone refuses.
; 2. The frames: round trips, and a frame of another kind decodes to nothing.
; 3. The classifier: the request frame is classified :read in this world (the
;    attachment), and kind 40 is among the admitted kinds; the same frame in a
;    world without this book is tests/acl2/native-control-kinds-tests.lisp.
; 4. The three service-log lines of RP-3, exactly, and one line each.
; 5. The journal's developer-eval entry: replay stops at it with
;    (:hand-touched SEQ), after the entries before it agreed.

(in-package "ACL2")
(include-book "../../books/developer-eval")
(include-book "../../books/owner-time-journal-stream")
(include-book "must-fail-checked")

(defconst *det-max* (fn-deval-max-frame-octets))
(defconst *det-frame* 65582)
(assert-event (equal *det-max* *det-frame*))

; ---------------------------------------------------------------------------
; 1. Admission

; Positive witness: the complete antecedent of the keystone's right side, and
; the admission it concludes.
(assert-event
 (let ((profile :developer) (peer-uid 501) (owner-uid 501)
       (octets 100) (max-octets *det-max*) (stopping nil))
   (and (equal profile :developer)
        (natp peer-uid) (equal peer-uid owner-uid)
        (natp octets) (natp max-octets) (<= octets max-octets)
        (not stopping)
        (equal (fn-deval-admit profile peer-uid owner-uid octets max-octets stopping)
               :admit))))

; The bound is inclusive: a frame at the bound is admitted, one past it is not.
(assert-event (equal (fn-deval-admit :developer 0 0 *det-max* *det-max* nil) :admit))
(assert-event (equal (fn-deval-admit :developer 0 0 (+ 1 *det-max*) *det-max* nil)
                     '(:refused :too-large)))

; Hypothesis removal, each with the other six retained: the named refusal.
; (1) profile
(assert-event
 (let ((profile :production) (peer-uid 501) (owner-uid 501)
       (octets 100) (max-octets *det-max*) (stopping nil))
   (and (not (equal profile :developer))
        (natp peer-uid) (equal peer-uid owner-uid)
        (natp octets) (natp max-octets) (<= octets max-octets) (not stopping)
        (not (equal (fn-deval-admit profile peer-uid owner-uid octets max-octets stopping)
                    :admit))
        (equal (fn-deval-admit profile peer-uid owner-uid octets max-octets stopping)
               '(:refused :not-developer)))))
; (2) the peer's UID is observed
(assert-event
 (let ((profile :developer) (peer-uid nil) (owner-uid nil)
       (octets 100) (max-octets *det-max*) (stopping nil))
   (and (equal profile :developer)
        (not (natp peer-uid)) (equal peer-uid owner-uid)
        (natp octets) (natp max-octets) (<= octets max-octets) (not stopping)
        (equal (fn-deval-admit profile peer-uid owner-uid octets max-octets stopping)
               '(:refused :not-the-operator)))))
; (3) the peer is the operator
(assert-event
 (let ((profile :developer) (peer-uid 502) (owner-uid 501)
       (octets 100) (max-octets *det-max*) (stopping nil))
   (and (equal profile :developer)
        (natp peer-uid) (not (equal peer-uid owner-uid))
        (natp octets) (natp max-octets) (<= octets max-octets) (not stopping)
        (equal (fn-deval-admit profile peer-uid owner-uid octets max-octets stopping)
               '(:refused :not-the-operator)))))
; (4) the frame length is observed
(assert-event
 (let ((profile :developer) (peer-uid 501) (owner-uid 501)
       (octets nil) (max-octets *det-max*) (stopping nil))
   (and (equal profile :developer)
        (natp peer-uid) (equal peer-uid owner-uid)
        (not (natp octets)) (natp max-octets) (not stopping)
        (equal (fn-deval-admit profile peer-uid owner-uid octets max-octets stopping)
               '(:refused :too-large)))))
; (5) the bound is a natural
(assert-event
 (let ((profile :developer) (peer-uid 501) (owner-uid 501)
       (octets 100) (max-octets nil) (stopping nil))
   (and (equal profile :developer)
        (natp peer-uid) (equal peer-uid owner-uid)
        (natp octets) (not (natp max-octets)) (not stopping)
        (equal (fn-deval-admit profile peer-uid owner-uid octets max-octets stopping)
               '(:refused :too-large)))))
; (6) the frame is within the bound
(assert-event
 (let ((profile :developer) (peer-uid 501) (owner-uid 501)
       (octets 70000) (max-octets *det-max*) (stopping nil))
   (and (equal profile :developer)
        (natp peer-uid) (equal peer-uid owner-uid)
        (natp octets) (natp max-octets) (not (<= octets max-octets)) (not stopping)
        (equal (fn-deval-admit profile peer-uid owner-uid octets max-octets stopping)
               '(:refused :too-large)))))
; (7) the node is not stopping
(assert-event
 (let ((profile :developer) (peer-uid 501) (owner-uid 501)
       (octets 100) (max-octets *det-max*) (stopping t))
   (and (equal profile :developer)
        (natp peer-uid) (equal peer-uid owner-uid)
        (natp octets) (natp max-octets) (<= octets max-octets) stopping
        (equal (fn-deval-admit profile peer-uid owner-uid octets max-octets stopping)
               '(:refused :stopping)))))

; The refusal's answer is a reply status of the frame table, one per reason.
(assert-event
 (and (equal (fn-deval-refusal-status '(:refused :not-developer)) :not-developer)
      (equal (fn-deval-refusal-status '(:refused :not-the-operator)) :not-the-operator)
      (equal (fn-deval-refusal-status '(:refused :too-large)) :too-large)
      (equal (fn-deval-refusal-status '(:refused :stopping)) :stopping)))

; Each hypothesis omitted, the admission is not a theorem.
(must-fail-checked
 (defthm det-admission-without-the-profile
   (implies (and (natp peer-uid) (equal peer-uid owner-uid)
                 (natp octets) (natp max-octets) (<= octets max-octets) (not stopping))
            (equal (fn-deval-admit profile peer-uid owner-uid octets max-octets stopping)
                   :admit))))
(must-fail-checked
 (defthm det-admission-without-an-observed-uid
   (implies (and (equal profile :developer) (equal peer-uid owner-uid)
                 (natp octets) (natp max-octets) (<= octets max-octets) (not stopping))
            (equal (fn-deval-admit profile peer-uid owner-uid octets max-octets stopping)
                   :admit))))
(must-fail-checked
 (defthm det-admission-without-the-same-uid
   (implies (and (equal profile :developer) (natp peer-uid)
                 (natp octets) (natp max-octets) (<= octets max-octets) (not stopping))
            (equal (fn-deval-admit profile peer-uid owner-uid octets max-octets stopping)
                   :admit))))
(must-fail-checked
 (defthm det-admission-without-an-observed-length
   (implies (and (equal profile :developer) (natp peer-uid) (equal peer-uid owner-uid)
                 (natp max-octets) (<= octets max-octets) (not stopping))
            (equal (fn-deval-admit profile peer-uid owner-uid octets max-octets stopping)
                   :admit))))
(must-fail-checked
 (defthm det-admission-without-the-bound
   (implies (and (equal profile :developer) (natp peer-uid) (equal peer-uid owner-uid)
                 (natp octets) (natp max-octets) (not stopping))
            (equal (fn-deval-admit profile peer-uid owner-uid octets max-octets stopping)
                   :admit))))
(must-fail-checked
 (defthm det-admission-while-stopping
   (implies (and (equal profile :developer) (natp peer-uid) (equal peer-uid owner-uid)
                 (natp octets) (natp max-octets) (<= octets max-octets))
            (equal (fn-deval-admit profile peer-uid owner-uid octets max-octets stopping)
                   :admit))))

; MUTATION witnesses (labelled): four mutants of fn-deval-admit, each admitting
; a request the keystone refuses.  A mutant is a function the host does not
; call; the witness is the request it admits and the keystone's right side
; failing on it.
(defun det-mutant-ignores-the-uid (profile peer-uid owner-uid octets max-octets stopping)
  (declare (xargs :guard t) (ignore peer-uid owner-uid))
  (cond ((not (equal profile :developer)) '(:refused :not-developer))
        ((not (and (natp octets) (natp max-octets) (<= octets max-octets)))
         '(:refused :too-large))
        (stopping '(:refused :stopping))
        (t :admit)))
(defun det-mutant-admits-a-production-image (profile peer-uid owner-uid octets max-octets stopping)
  (declare (xargs :guard t) (ignore profile))
  (cond ((not (and (natp peer-uid) (equal peer-uid owner-uid))) '(:refused :not-the-operator))
        ((not (and (natp octets) (natp max-octets) (<= octets max-octets)))
         '(:refused :too-large))
        (stopping '(:refused :stopping))
        (t :admit)))
(defun det-mutant-ignores-the-bound (profile peer-uid owner-uid octets max-octets stopping)
  (declare (xargs :guard t) (ignore octets max-octets))
  (cond ((not (equal profile :developer)) '(:refused :not-developer))
        ((not (and (natp peer-uid) (equal peer-uid owner-uid))) '(:refused :not-the-operator))
        (stopping '(:refused :stopping))
        (t :admit)))
(defun det-mutant-ignores-stopping (profile peer-uid owner-uid octets max-octets stopping)
  (declare (xargs :guard t) (ignore stopping))
  (cond ((not (equal profile :developer)) '(:refused :not-developer))
        ((not (and (natp peer-uid) (equal peer-uid owner-uid))) '(:refused :not-the-operator))
        ((not (and (natp octets) (natp max-octets) (<= octets max-octets)))
         '(:refused :too-large))
        (t :admit)))
(assert-event
 (and (equal (det-mutant-ignores-the-uid :developer 502 501 100 *det-max* nil) :admit)
      (not (equal (fn-deval-admit :developer 502 501 100 *det-max* nil) :admit))
      (equal (det-mutant-admits-a-production-image :production 501 501 100 *det-max* nil) :admit)
      (not (equal (fn-deval-admit :production 501 501 100 *det-max* nil) :admit))
      (equal (det-mutant-ignores-the-bound :developer 501 501 70000 *det-max* nil) :admit)
      (not (equal (fn-deval-admit :developer 501 501 70000 *det-max* nil) :admit))
      (equal (det-mutant-ignores-stopping :developer 501 501 100 *det-max* t) :admit)
      (not (equal (fn-deval-admit :developer 501 501 100 *det-max* t) :admit))))
(must-fail-checked
 (defthm det-mutant-admits-only-the-developer-operator
   (equal (equal (det-mutant-ignores-the-uid profile peer-uid owner-uid octets max-octets stopping)
                 :admit)
          (and (equal profile :developer) (natp peer-uid) (equal peer-uid owner-uid)
               (natp octets) (natp max-octets) (<= octets max-octets) (not stopping)))))

; ---------------------------------------------------------------------------
; 2. The frames

(defconst *det-form* (fn-record-string-octets "(+ 1 2)"))
(defconst *det-request* (fn-deval-request-encode *det-form*))
(assert-event
 (and (fn-cbor-octet-listp *det-request*)
      (equal (fn-deval-request-decode *det-request*) *det-form*)
      (<= (len *det-request*) *det-max*)))
; A form at the bound is encodable, one octet past it and the empty form are not.
(assert-event
 (and (fn-cbor-octet-listp (fn-deval-request-encode (make-list *fn-deval-max-form-octets*
                                                              :initial-element 97)))
      (<= (len (fn-deval-request-encode (make-list *fn-deval-max-form-octets*
                                                  :initial-element 97)))
          *det-max*)
      (equal (fn-deval-request-encode (make-list (+ 1 *fn-deval-max-form-octets*)
                                                :initial-element 97))
             :bad)
      (equal (fn-deval-request-encode nil) :bad)))
; Another FNCT kind is not an eval request; neither is a flipped octet.
(assert-event
 (and (null (fn-deval-request-decode (fn-tlsr-request-encode :reload)))
      (null (fn-deval-request-decode
             (update-nth 12 (+ 1 (nth 12 *det-request*)) *det-request*)))
      (null (fn-deval-request-decode nil))))

(defconst *det-reply* (fn-deval-reply-encode :ok (fn-record-string-octets "3")))
(assert-event
 (and (fn-cbor-octet-listp *det-reply*)
      (equal (fn-deval-reply-read *det-reply*) (list :ok (fn-record-string-octets "3")))
      (equal (fn-deval-reply-read (fn-deval-reply-encode :stopping nil))
             '(:stopping (10)))
      (equal (fn-deval-reply-encode :accepted nil) :bad)
      (equal (fn-deval-reply-read *det-request*) :bad)
      (equal (fn-deval-reply-read nil) :bad)))

;; The longest output the evaluator keeps (65,536 characters of up to four octets
;; each, and the note after a truncation) is a reply a client reads; one octet
;; more is refused, not cut.
(assert-event
 (let ((longest (fn-deval-reply-encode
                 :ok (make-list (+ (* 4 (fn-deval-max-output-characters)) 64)
                                :initial-element 97))))
   (and (equal (fn-deval-max-output-characters) 65536)
        (fn-cbor-octet-listp longest)
        (<= (len longest) *fn-nctrl-max-command-frame*)
        (equal (fn-deval-reply-encode
                :ok (make-list (+ (* 4 (fn-deval-max-output-characters)) 65)
                               :initial-element 97))
               :bad))))

; ---------------------------------------------------------------------------
; 3. The classifier

(defun det-word (xs fn-octets)
  (declare (xargs :stobjs fn-octets :verify-guards nil))
  (let* ((fn-octets (fn-octets-clear fn-octets))
         (fn-octets (fn-octets-append-list xs fn-octets)))
    (mv (fn-ctlk-frame-handler fn-octets) fn-octets)))

(assert-event (mv-let (w fn-octets) (det-word *det-request* fn-octets)
                (mv (equal w :read) fn-octets))
              :stobjs-out '(nil fn-octets))
; The built-in kinds keep their words (the attachment adds, never reclassifies).
(assert-event (mv-let (w fn-octets) (det-word (fn-tlsr-request-encode :reload) fn-octets)
                (mv (equal w :read) fn-octets))
              :stobjs-out '(nil fn-octets))
(assert-event (mv-let (w fn-octets) (det-word (fn-pinv-bindings-request-encode) fn-octets)
                (mv (equal w :store) fn-octets))
              :stobjs-out '(nil fn-octets))
(assert-event
 (and (member-equal *fn-deval-request-kind* (fn-ctlk-admitted-kinds))
      (equal (fn-ctlk-word *fn-deval-request-kind*) :read)
      (equal (fn-ctlk-extra-kinds) *fn-deval-extra-kinds*)))

; ---------------------------------------------------------------------------
; 4. The service-log lines (RP-3)

(defun det-text (s) (declare (xargs :mode :program)) (fn-record-string-octets s))
(defconst *det-digest* (make-list 32 :initial-element 171))
(defconst *det-obs* (fn-clock-observation 0 812345678901 0 t))

(assert-event
 (equal (fn-olog-developer-eval-begin-line 501 7 *det-digest* *det-obs*)
        (det-text "developer-eval begin uid=501 form-octets=7 form-digest=abababababababababababababababababababababababababababababababab time=2025-09-28T03:34:38Z")))
(assert-event
 (and (equal (fn-olog-developer-eval-end-line :ok 12 1000 1003)
             (det-text "developer-eval end status=ok output-octets=12 duration-ms=3"))
      (equal (fn-olog-developer-eval-end-line :error 0 5 5)
             (det-text "developer-eval end status=error output-octets=0 duration-ms=0"))
      ; a reading that went back is a zero duration, not a negative one
      (equal (fn-olog-developer-eval-end-line :ok 1 9 4)
             (det-text "developer-eval end status=ok output-octets=1 duration-ms=0"))))
(assert-event
 (and (equal (fn-olog-developer-eval-refused-line :not-developer)
             (det-text "developer-eval refused reason=not-developer"))
      (equal (fn-olog-developer-eval-refused-line :not-the-operator)
             (det-text "developer-eval refused reason=not-the-operator"))
      (equal (fn-olog-developer-eval-refused-line :too-large)
             (det-text "developer-eval refused reason=too-large"))
      (equal (fn-olog-developer-eval-refused-line :stopping)
             (det-text "developer-eval refused reason=stopping"))))
; Whatever the observations held, one line (the keystones are the theorems);
; the unobserved digest and clock are named, not invented.
(assert-event
 (and (equal (fn-olog-developer-eval-begin-line 501 7 nil (fn-clock-observation 0 0 0 nil))
             (det-text "developer-eval begin uid=501 form-octets=7 form-digest=none time=none"))
      (fn-olog-no-breakp (fn-olog-developer-eval-begin-line 13 10 '(13 10) *det-obs*))))
; MUTATION witness: a second line is not one line.
(assert-event
 (not (fn-olog-no-breakp (append (fn-olog-developer-eval-end-line :ok 1 1 2) '(10 10)))))

; ---------------------------------------------------------------------------
; 5. The journal entry

(defun det-replay-verdict (s es)
  (mv-let (v s2) (fn-otm-replay s es) (declare (ignore s2)) v))

(defun det-run (s steps)
  (mv-let (es s2) (fn-otm-run s steps) (list es s2)))
(defun det-mark (s uid n)
  (mv-let (s2 e) (fn-otm-eval-mark s uid n) (list s2 e)))

; A run: one clock event, the developer-eval entry, one more clock event.
(defconst *det-run1* (det-run (fn-otm-init) '((:event :clock 12000 nil))))
(defconst *det-es1* (car *det-run1*))
(defconst *det-s1* (cadr *det-run1*))
(defconst *det-mark* (det-mark *det-s1* 501 7))
(defconst *det-eval* (cadr *det-mark*))
(defconst *det-s2* (car *det-mark*))
(defconst *det-es3* (car (det-run *det-s2* '((:event :clock 13000 nil)))))
(assert-event
 (and (equal *det-es1* '((1 1 12000 0 0 0 7)))
      (equal *det-eval* '(2 8 12000 501 7 0 0))
      (equal *det-es3* '((3 1 13000 0 0 0 7)))))
; The entry's line and its read-back.
(assert-event
 (and (equal (fn-otm-jline *det-eval*) (det-text "2 8 12000 501 7 0 0
"))
      (equal (fn-otm-journal-read (fn-otm-jlines (list *det-eval*))) (list *det-eval*))
      (equal (fn-otm-eval-step *det-s1* 501 7)
             (list *det-s2* (fn-otm-jline *det-eval*)))))
; Before the entry, replay agrees; at it, replay stops with its sequence number,
; whatever follows.
(assert-event
 (and (equal (det-replay-verdict (fn-otm-init) *det-es1*) :agrees)
      (equal (det-replay-verdict (fn-otm-init) (append *det-es1* (list *det-eval*)))
             '(:hand-touched 2))
      (equal (det-replay-verdict (fn-otm-init)
                                 (append *det-es1* (list *det-eval*) *det-es3*))
             '(:hand-touched 2))
      (not (equal (det-replay-verdict (fn-otm-init)
                                      (append *det-es1* (list *det-eval*) *det-es3*))
                  :agrees))))
; The entry advances the sequence like a note: the entry after it is numbered
; past it, and without it the same entry is a gap (the sink dropped it).
(assert-event
 (equal (det-replay-verdict (fn-otm-init) (append *det-es1* *det-es3*)) '(:gap 2)))
; A developer-eval entry out of sequence is a gap before it is a hand-touch.
(assert-event
 (equal (det-replay-verdict (fn-otm-init) (list '(5 8 12000 501 7 0 0))) '(:gap 1)))
; The report names it, and the exit is not the agreeing one.
(defconst *det-journal*
  (fn-otm-jlines (append (list (fn-otm-start-entry 0 t)) *det-es1* (list *det-eval*) *det-es3*)))
(assert-event
 (equal (fn-otm-journal-report *det-journal*)
        (det-text "journal: entries=4 segments=1 status=whole replay=hand-touched-at-2
")))
(assert-event
 (let ((st (fn-otjs-consume *det-journal* (fn-otjs-init))))
   (and (equal (fn-otjs-field 5 st) '(:hand-touched 2))
        (equal (fn-otjs-exit st) 1))))
