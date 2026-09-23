; Teeth for the operator's submission (books/owner.lisp fn-own-operator-submit,
; the keystones in books/owner-invariants.lisp):
;
;   fn-own-operator-decision-is-an-injection-of-the-payload
;   fn-own-operator-submission-is-an-injection-of-the-payload
;   fn-own-operator-submit-without-a-clock-refuses-and-changes-nothing
;   fn-own-operator-retry-resubmits-the-stored-injection
;
; The subject is fn-own-operator-submit, which host/owner-host.lisp
; `fn-owner-operator-submit' steps as the (:operator-submit ...) event and
; which host/native/owner.lisp `fnn-owner-control-submit-serialized' calls for
; `fn operator CONFIG post'.
;
; THE WITNESS IS THE INN LAB'S OWN ARTICLE.  planning/evidence/inn-lab-dabebb84-
; 2026-09-22.md, "fn's feed -> innd", carries the octets `operator post`
; submitted and innd refused `437 Missing "Path" header field'; the node's
; path identity was fnA.hbox.test.  Below, the same octets through the owner
; now come out injected: the Path, Injection-Date and Injection-Info lines
; the served POST of the same run carried, then the submitted octets
; unchanged.  Every expected octet string is written out here from the RFC
; 5536 field syntax, never computed by the function under test.
;
; For each keystone: the reachable witness, and one `must-fail' per
; hypothesis with the keystone's own hints, beside the concrete value that
; refutes the weakened statement.

(in-package "ACL2")
(include-book "../../books/owner-invariants")
(include-book "../../books/injection-invariants")
(include-book "std/testing/must-fail" :dir :system)

(defun opt-codes (cs)
  (declare (xargs :mode :program))
  (if (consp cs) (cons (char-code (car cs)) (opt-codes (cdr cs))) nil))
(defun opt-octets (s)
  (declare (xargs :mode :program))
  (opt-codes (coerce s 'list)))
(defun opt-lines (lines)
  ; each line and its CRLF
  (declare (xargs :mode :program))
  (if (consp lines)
      (append (opt-octets (car lines)) '(13 10) (opt-lines (cdr lines)))
    nil))

; -----------------------------------------------------------------------------
; The lab's node and the lab's article

(defconst *opt-agent* (opt-octets "fnA.hbox.test"))
(defconst *opt-groups* (list (opt-octets "fn.letters")))
(defconst *opt-config* (fn-inj-make-config t *opt-agent* *opt-groups* 32768))
(assert-event (fn-inj-configp *opt-config*))
(defconst *opt-msgid*
  (opt-octets "<inn-lab-fn-operator-8a5f502-20260922T212621Z@example.invalid>"))
(defconst *opt-payload*
  (opt-lines (list "From: lab@example.invalid"
                   "Newsgroups: fn.letters"
                   "Subject: submitted through operator post"
                   "Date: Tue, 22 Sep 2026 21:26:21 -0000"
                   "Message-ID: <inn-lab-fn-operator-8a5f502-20260922T212621Z@example.invalid>"
                   ""
                   "From the fn INN interop lab.")))
; 2026-09-22T21:26:47Z, the Injection-Date the lab's run carried, in
; milliseconds since 2000-01-01T00:00:00Z; and a reading a minute later.
(defconst *opt-obs* (fn-clock-observation 1000000 843427607000 500 t))
(defconst *opt-later* (fn-clock-observation 1060000 843427667000 500 t))
(defconst *opt-injected*
  (append (opt-lines (list "Path: fnA.hbox.test!not-for-mail"
                           "Injection-Date: Tue, 22 Sep 2026 21:26:47 +0000"
                           "Injection-Info: fnA.hbox.test"))
          *opt-payload*))

; The owner over a fresh store serving fn.letters, configured and clocked.
(defconst *opt-bare* (fn-own-start (fn-sn-initial '("fn.letters") 10) 4))
(defconst *opt-0*
  (fn-own-run *opt-bare* (list (list :configure *opt-config*)
                               (list :observe *opt-obs*))))
(assert-event (fn-own-relation *opt-0*))
(assert-event (equal (fn-own-clock *opt-0*) *opt-obs*))

; -----------------------------------------------------------------------------
; Keystones 1 and 2: what is queued is an injection of the payload

(defconst *opt-decision* (fn-own-operator-decision-of *opt-0* *opt-msgid*
                                                      *opt-groups* *opt-payload*))
(assert-event (fn-inj-injectedp *opt-decision*))
; The exact octets: the Path innd asked for is there.
(assert-event (equal (fn-inj-decision-octets *opt-decision*) *opt-injected*))
(assert-event (fn-inj-reinjectionp (fn-inj-decision-octets *opt-decision*)
                                   *opt-payload* *opt-agent* *opt-msgid*))
(assert-event (equal (fn-own-operator-submit-result *opt-0* *opt-msgid*
                                                    *opt-groups* *opt-payload*)
                     :submitted))
(defconst *opt-queued* (fn-own-operator-submit *opt-0* *opt-msgid* *opt-groups*
                                               *opt-payload*))
(assert-event (equal (len (fn-own-queue *opt-queued*)) 1))
(assert-event (fn-own-control-submissionp (car (fn-own-queue *opt-queued*))))
(assert-event (equal (fn-inj-decision-octets
                      (fn-own-sub-decision (car (fn-own-queue *opt-queued*))))
                     *opt-injected*))
; Separating: the verb's former decision stored the payload as read, which is
; not a re-injection of anything (no Path line), and is what innd refused.
(assert-event (equal (fn-inj-decision-octets
                      (fn-own-control-decision *opt-config* *opt-msgid*
                                               *opt-groups* *opt-payload*))
                     *opt-payload*))
(assert-event (not (fn-inj-reinjectionp *opt-payload* *opt-payload*
                                        *opt-agent* *opt-msgid*)))

; A decision that is not an injection: `From: yue' (the agents run of
; 2026-09-22 posted with --from yue; the article here is that run's shape --
; the evidence records the header, not the octets).
(defconst *opt-yue-msgid* (opt-octets "<yue-03@example.invalid>"))
(defconst *opt-yue*
  (opt-lines (list "From: yue"
                   "Newsgroups: fn.letters"
                   "Subject: run 03"
                   "Message-ID: <yue-03@example.invalid>"
                   ""
                   "hello from yue")))
(defconst *opt-yue-decision*
  (fn-own-operator-decision-of *opt-0* *opt-yue-msgid* *opt-groups* *opt-yue*))
(assert-event (not (fn-inj-injectedp *opt-yue-decision*)))
(assert-event (equal (fn-inj-decision-reason *opt-yue-decision*) :from-invalid))

; Tooth for keystone 1: without `injectedp' the octets of a refusal (none)
; are no re-injection of the payload.
(must-fail
 (defthm opt-decision-without-injection
   (let ((d (fn-own-operator-decision cfg clock node msgid groups octets)))
     (fn-inj-reinjectionp (fn-inj-decision-octets d) octets
                          (fn-inj-config-agent cfg) msgid))
   :hints (("Goal" :in-theory (e/d (fn-own-operator-decision)
                                   (fn-inj-decide fn-inj-reinjectionp
                                    fn-own-stored-octets fn-own-clock-usablep))
            :use ((:instance fn-inj-injected-article-is-a-reinjection-of-its-source
                             (source octets) (config cfg) (observation clock)))))))
(assert-event (not (fn-inj-reinjectionp (fn-inj-decision-octets *opt-yue-decision*)
                                        *opt-yue* *opt-agent* *opt-yue-msgid*)))

; A Message-ID on the command line that the article does not carry is
; refused, not reconciled.
(assert-event
 (equal (fn-inj-decision-reason
         (fn-own-operator-decision-of *opt-0* (opt-octets "<other@example.invalid>")
                                      *opt-groups* *opt-payload*))
        :control-mismatch))

; Tooth for keystone 2: without `:submitted' the queue holds nothing.
(must-fail
 (defthm opt-submission-without-submitted
   (let* ((q (fn-own-queue (fn-own-operator-submit o msgid groups octets)))
          (d (fn-own-sub-decision (car q))))
     (and (equal (len q) 1)
          (fn-own-control-submissionp (car q))
          (fn-inj-injectedp d)))
   :hints (("Goal" :in-theory (e/d (fn-own-operator-submit-result
                                    fn-own-operator-submit fn-own-enqueue
                                    fn-own-operator-decision-of)
                                   (fn-own-operator-decision fn-inj-reinjectionp))))))
(assert-event (equal (fn-own-operator-submit-result *opt-0* *opt-yue-msgid*
                                                    *opt-groups* *opt-yue*)
                     :refused))
(assert-event (equal (len (fn-own-queue (fn-own-operator-submit
                                         *opt-0* *opt-yue-msgid* *opt-groups*
                                         *opt-yue*)))
                     0))

; -----------------------------------------------------------------------------
; Keystone 3 (D10-a): no clock, nothing injected, nothing queued

(defconst *opt-no-clock* (fn-own-configure *opt-bare* *opt-config*))
(assert-event (null (fn-own-clock *opt-no-clock*)))
(assert-event (equal (fn-own-operator-submit-result *opt-no-clock* *opt-msgid*
                                                    *opt-groups* *opt-payload*)
                     :refused))
(assert-event (equal (fn-own-operator-submit *opt-no-clock* *opt-msgid*
                                             *opt-groups* *opt-payload*)
                     *opt-no-clock*))
(assert-event (equal (fn-inj-decision-reason
                      (fn-own-operator-decision-of *opt-no-clock* *opt-msgid*
                                                   *opt-groups* *opt-payload*))
                     :clock-unusable))
; A reading without a wall time is no clock either.
(defconst *opt-blind* (fn-clock-observation 1000000 843427607000 500 nil))
(assert-event (equal (fn-inj-decision-reason
                      (fn-own-operator-decision *opt-config* *opt-blind*
                                                (fn-sn-node (fn-own-store *opt-0*))
                                                *opt-msgid* *opt-groups*
                                                *opt-payload*))
                     :clock-unusable))

; Tooth: without the hypothesis, the clocked owner submits.
(must-fail
 (defthm opt-refusal-without-no-clock
   (and (equal (fn-own-operator-submit-result o msgid groups octets) :refused)
        (equal (fn-own-operator-submit o msgid groups octets) o))
   :hints (("Goal" :in-theory (e/d (fn-own-operator-submit-result
                                    fn-own-operator-submit
                                    fn-own-operator-decision-of
                                    fn-own-operator-decision
                                    fn-own-clock-usablep)
                                   (fn-inj-decide))))))
(assert-event (not (equal (fn-own-operator-submit *opt-0* *opt-msgid*
                                                  *opt-groups* *opt-payload*)
                          *opt-0*)))

; -----------------------------------------------------------------------------
; Keystone 4: a retry after the first became durable is the stored article

; The submission through the writer: take, the store events of the durable
; path over a record carrying exactly the queued octets, the completion.
(defconst *opt-record*
  (fn-record-make 0 0 0
                  "<inn-lab-fn-operator-8a5f502-20260922T212621Z@example.invalid>"
                  *opt-injected* '("fn.letters")
                  "opt-pin" "opt-content" "opt-release" 2 841000000))
(defconst *opt-taken* (fn-own-take-submission *opt-queued*))
(assert-event (fn-own-control-submissionp (fn-own-inflight *opt-taken*)))
(defconst *opt-done*
  (fn-own-run *opt-taken*
              (list '(:store (:io :start-frontier nil))
                    '(:store (:io :frontier-file :ok))
                    '(:store (:io :frontier-replace :ok))
                    '(:store (:io :frontier-directory :ok))
                    (list :store (list :prepare *opt-record*))
                    '(:store (:io :record-file :ok))
                    '(:store (:io :record-link :ok))
                    '(:store (:io :record-directory :ok))
                    '(:complete))))
(assert-event (equal (fn-own-control-outcome-result *opt-done* :durable) :accepted))
(defconst *opt-stored*
  (fn-own-observe (fn-own-control-outcome *opt-done* :durable) *opt-later*))
(assert-event (equal (fn-own-clock *opt-stored*) *opt-later*))
(assert-event (equal (fn-own-stored-octets (fn-sn-node (fn-own-store *opt-stored*))
                                           *opt-msgid*)
                     *opt-injected*))

; The retry, a minute later: the decision is the stored article, so the store
; answers its duplicate.  A fresh injection would differ in Injection-Date.
(assert-event
 (equal (fn-own-operator-decision-of *opt-stored* *opt-msgid* *opt-groups*
                                     *opt-payload*)
        (fn-inj-make-decision :injected nil *opt-msgid* *opt-groups* *opt-injected*)))
(assert-event
 (not (equal (fn-inj-decision-octets
              (fn-inj-decide *opt-payload* *opt-config* *opt-later*))
             *opt-injected*)))

; One tooth per hypothesis, the keystone's hints kept.
(defmacro opt-retry (name &rest hyps)
  `(defthm ,name
     (implies (and ,@hyps)
              (equal (fn-own-operator-decision cfg later node msgid groups octets)
                     (fn-inj-make-decision
                      :injected nil msgid groups
                      (fn-inj-decision-octets (fn-inj-decide octets cfg first)))))
     :hints (("Goal" :in-theory (e/d (fn-own-operator-decision fn-own-clock-usablep)
                                     (fn-inj-decide fn-inj-reinjectionp
                                      fn-own-stored-octets
                                      fn-inj-injected-article-is-a-reinjection-of-its-source
                                      fn-inj-injection-requires-posting-allowed))
              :use ((:instance fn-inj-injected-article-is-a-reinjection-of-its-source
                               (source octets) (config cfg) (observation first))
                    (:instance fn-inj-injection-requires-posting-allowed
                               (source octets) (config cfg) (observation first))
                    (:instance fn-own-a-reinjection-is-not-absent
                               (stored (fn-inj-decision-octets
                                        (fn-inj-decide octets cfg first)))
                               (source octets) (agent (fn-inj-config-agent cfg))
                               (msgid msgid)))))
     :rule-classes nil))

; The keystone itself, admitted again through the macro so the must-fails
; below fail on their statements and not on their hints.
(opt-retry opt-retry-full
           (fn-inj-injectedp (fn-inj-decide octets cfg first))
           (equal (fn-inj-decision-msgid (fn-inj-decide octets cfg first)) msgid)
           (equal (fn-own-stored-octets node msgid)
                  (fn-inj-decision-octets (fn-inj-decide octets cfg first)))
           (fn-clock-observationp later)
           (fn-clock-has-wall later))

; Without the first injection: nothing stored is its octets.
(must-fail
 (opt-retry opt-retry-without-injected
            (equal (fn-inj-decision-msgid (fn-inj-decide octets cfg first)) msgid)
            (equal (fn-own-stored-octets node msgid)
                   (fn-inj-decision-octets (fn-inj-decide octets cfg first)))
            (fn-clock-observationp later)
            (fn-clock-has-wall later)))
; Without the Message-ID agreeing: an article submitted with no Message-ID
; was injected under a generated one, and its stored octets carry that line,
; which is no re-injection under another identifier.
(must-fail
 (opt-retry opt-retry-without-msgid
            (fn-inj-injectedp (fn-inj-decide octets cfg first))
            (equal (fn-own-stored-octets node msgid)
                   (fn-inj-decision-octets (fn-inj-decide octets cfg first)))
            (fn-clock-observationp later)
            (fn-clock-has-wall later)))
(defconst *opt-no-id*
  (opt-lines (list "From: lab@example.invalid" "Newsgroups: fn.letters"
                   "Subject: no identifier" "" "body")))
(assert-event (fn-inj-injectedp (fn-inj-decide *opt-no-id* *opt-config* *opt-obs*)))
(assert-event (not (fn-inj-reinjectionp
                    (fn-inj-decision-octets
                     (fn-inj-decide *opt-no-id* *opt-config* *opt-obs*))
                    *opt-no-id* *opt-agent* *opt-msgid*)))

; Without the stored article: the node holds nothing, and a fresh injection
; under the later clock carries another Injection-Date.
(must-fail
 (opt-retry opt-retry-without-stored
            (fn-inj-injectedp (fn-inj-decide octets cfg first))
            (equal (fn-inj-decision-msgid (fn-inj-decide octets cfg first)) msgid)
            (fn-clock-observationp later)
            (fn-clock-has-wall later)))
(assert-event
 (not (equal (fn-own-operator-decision-of *opt-0* *opt-msgid* *opt-groups* *opt-payload*)
             (fn-own-operator-decision *opt-config* *opt-later*
                                       (fn-sn-node (fn-own-store *opt-0*))
                                       *opt-msgid* *opt-groups* *opt-payload*))))
; Without a later reading at all, and without its wall time: refused.
(must-fail
 (opt-retry opt-retry-without-observation
            (fn-inj-injectedp (fn-inj-decide octets cfg first))
            (equal (fn-inj-decision-msgid (fn-inj-decide octets cfg first)) msgid)
            (equal (fn-own-stored-octets node msgid)
                   (fn-inj-decision-octets (fn-inj-decide octets cfg first)))
            (fn-clock-has-wall later)))
(must-fail
 (opt-retry opt-retry-without-wall
            (fn-inj-injectedp (fn-inj-decide octets cfg first))
            (equal (fn-inj-decision-msgid (fn-inj-decide octets cfg first)) msgid)
            (equal (fn-own-stored-octets node msgid)
                   (fn-inj-decision-octets (fn-inj-decide octets cfg first)))
            (fn-clock-observationp later)))
(assert-event
 (equal (fn-inj-decision-reason
         (fn-own-operator-decision *opt-config* *opt-blind*
                                   (fn-sn-node (fn-own-store *opt-stored*))
                                   *opt-msgid* *opt-groups* *opt-payload*))
        :clock-unusable))
