; fn: teeth for books/app-pattern-delivery.lisp.
;
; fn-pat-reader-delivers-what-the-writer-encoded: inhabited by a real Store
; event (the hybrid-store fixture's constructor, books/hybrid-store) around
; the source the pubsub posting role encodes; the reader delivers exactly
; the payload.  Each hypothesis is needed: the fixture's own event (a source
; that is not the writer's encoding, outside the kind) is delivered as
; :foreign, not as a payload; a cursor of another position fails the
; projection (:binding); a source of the grammar outside the kind (a From
; that is no mailbox-list) is refused :from.  The report kinds that are not
; articles (empty, withdrawn) pass through.  The spool check accepts the
; request it wrote and refuses another payload, another generation, and a
; non-request.

(in-package "ACL2")
(include-book "../../books/app-pattern-delivery")
(include-book "hybrid-store-tests")
(include-book "../../books/defkeystone")

(defconst *apd-name* (fn-ak-text "pubsub"))
(defconst *apd-from* (fn-ak-text "author@example.invalid"))
(defconst *apd-group* (fn-ak-text "example"))
(defconst *apd-msgid-text* "<pattern1@example.invalid>")
(defconst *apd-msgid* (fn-ak-text *apd-msgid-text*))
(defconst *apd-payload* (fn-ak-iota 115))
(defconst *apd-seconds* 1791115200)

(make-event
 `(defconst *apd-source*
    ',(fn-pat-encode *apd-name* *apd-from* *apd-seconds* *apd-group* *apd-msgid* *apd-payload*)))
(assert-event (consp *apd-source*))
(assert-event (null (fn-pat-values-check *apd-name* *apd-from* *apd-seconds* *apd-group* *apd-msgid*)))

(make-event `(defconst *apd-received*
               ',(fn-hsig-injected-carrier-octets
                  *apd-source* *hst-principal* *hst-keys*
                  *hst-signatures* *hst-injection-config*
                  *hst-injection-observation*)))
(assert-event (consp *apd-received*))
(make-event `(defconst *apd-subject-id*
               ',(fn-id-subject-of-payload *apd-received*)))
(defconst *apd-subject* (fn-record-octets-string (fn-id-text *apd-subject-id*)))
(make-event `(defconst *apd-obligation*
               ',(fn-record-octets-string
                  (fn-id-text
                   (fn-id-obligation-of (fn-record-string-octets *apd-msgid-text*)
                                        *apd-subject-id*)))))
(make-event `(defconst *apd-event*
               ',(fn-hsig-authorized-injected-carried-submission-event
                  2 3 4 4 *hst-snapshot* *apd-msgid-text*
                  *apd-source* *apd-received* '("example")
                  *apd-obligation* *apd-subject* "release"
                  (fn-charge-for-payload (len *apd-received*))
                  *hst-principal* *hst-keys* *hst-signatures* *hst-ml-key*
                  :verified :verified *hst-injection-config*
                  *hst-injection-observation*)))
(assert-event (fn-stxa-p *apd-event*))

(defconst *apd-cursor* (fn-cp-cursor-encode (fn-cp-cursor '(1) '(2) '(3) '(4) '(5) 1 1 1 3)))
(defconst *apd-event-bytes* (fn-stxa-encode *apd-event*))

; Inhabited: every hypothesis holds and the reader delivers the payload.
(make-event `(defconst *apd-projection* ',(fn-cpj-project *apd-cursor* *apd-event-bytes*)))
(assert-event (equal (car *apd-projection*) :ok))
(assert-event (equal (nth 6 *apd-projection*) *apd-source*))
(assert-event
 (equal (fn-pat-decode :opaque-1 (fn-pat-project *apd-cursor* *apd-event-bytes*))
        (list :deliver 2 *apd-msgid* *apd-payload*)))
(assert-event (equal (fn-pat-delivery-name 2) (fn-ak-text "00000000000000000002.payload")))

; The source hypothesis is needed: the fixture's event projects, but its
; source is not the writer's encoding (and not of the kind).
(defconst *apd-other-bytes* (fn-stxa-encode *hst-injected-event*))
(assert-event (equal (car (fn-cpj-project *apd-cursor* *apd-other-bytes*)) :ok))
(assert-event
 (equal (fn-pat-decode :opaque-1 (fn-pat-project *apd-cursor* *apd-other-bytes*))
        (list :foreign :malformed (fn-ak-text "<hybrid@example.invalid>"))))

; The projection hypothesis is needed: a cursor of another position.
(defconst *apd-cursor-2* (fn-cp-cursor-encode (fn-cp-cursor '(1) '(2) '(3) '(4) '(5) 1 1 1 2)))
(assert-event (equal (car (fn-pat-decode :opaque-1 (fn-pat-project *apd-cursor-2* *apd-event-bytes*)))
                     :foreign))
(assert-event (equal (cadr (fn-pat-decode :opaque-1 (fn-pat-project *apd-cursor-2* *apd-event-bytes*)))
                     :binding))

; The values hypothesis is needed: a grammar source outside the kind.
(defconst *apd-bad-values*
  (fn-ak-values (fn-ak-text "nomailbox") (fn-ak-text "x") *apd-group*
                (fn-ak-text "s") *apd-msgid* (fn-ak-text "t")))
(assert-event (fn-pat-values-check *apd-name* (fn-ak-text "nomailbox") 0 *apd-group* *apd-msgid*))
(assert-event
 (equal (fn-pat-decode :opaque-1
                       (list :article 7 *apd-msgid*
                             (fn-wg-encode *fn-ak-grammar*
                                           (fn-ak-grammar-value *apd-bad-values* *apd-payload*))))
        (list :foreign :from *apd-msgid*)))

; Reports that are not articles.
(assert-event (equal (fn-pat-decode :opaque-1 (fn-pat-project *apd-cursor* nil)) '(:empty)))
(assert-event
 (equal (fn-pat-decode :opaque-1 (fn-pat-project *apd-cursor*
                                                 (append *fn-ncr-withdrawal-magic* *apd-msgid*)))
        (list :withdrawn *apd-msgid*)))

; The spool.
(defconst *apd-request*
  (fn-native-hybrid-control-author-encode
   1 *apd-source* (make-list 64 :initial-element 17) (make-list 3309 :initial-element 19)
   (fn-ak-text "/k/ml-public.pem")))
(assert-event (null (fn-pat-spool-check *apd-request* 1 *apd-name* *apd-from* *apd-group*
                                        *apd-msgid* *apd-payload*)))
(assert-event (equal (fn-pat-spool-check *apd-request* 1 *apd-name* *apd-from* *apd-group*
                                         *apd-msgid* (fn-ak-text "other"))
                     :spool-conflict))
(assert-event (equal (fn-pat-spool-check *apd-request* 2 *apd-name* *apd-from* *apd-group*
                                         *apd-msgid* *apd-payload*)
                     :spool-request))
(assert-event (equal (fn-pat-spool-check '(1 2 3) 1 *apd-name* *apd-from* *apd-group*
                                         *apd-msgid* *apd-payload*)
                     :spool-request))

; push/pull (pipeline): each delivery goes to exactly one worker of N.
(defun apd-delivering-workers (decision i n)
  (declare (xargs :measure (nfix (- n i)) :verify-guards nil))
  (if (and (natp i) (natp n) (< i n))
      (if (equal (car (fn-pat-select decision (fn-pat-decimal i) (fn-pat-decimal n))) :deliver)
          (cons i (apd-delivering-workers decision (1+ i) n))
        (apd-delivering-workers decision (1+ i) n))
    nil))
(defconst *apd-delivery* (list :deliver 2 *apd-msgid* *apd-payload*))
(assert-event (equal (len (apd-delivering-workers *apd-delivery* 0 3)) 1))
(assert-event (equal (apd-delivering-workers *apd-delivery* 0 3)
                     (list (fn-pat-partition *apd-msgid* 3))))
(assert-event (equal (len (apd-delivering-workers *apd-delivery* 0 7)) 1))
; The others skip it by its Message-ID; a withdrawal is partitioned the same
; way; empty reports and foreign articles pass to every worker.
(assert-event
 (let ((other (mod (1+ (fn-pat-partition *apd-msgid* 3)) 3)))
   (equal (fn-pat-select *apd-delivery* (fn-pat-decimal other) (fn-pat-decimal 3))
          (list :skip *apd-msgid*))))
(assert-event
 (equal (len (remove-equal nil
                           (list (equal (car (fn-pat-select (list :withdrawn *apd-msgid*) (fn-pat-decimal 0) (fn-pat-decimal 3))) :withdrawn)
                                 (equal (car (fn-pat-select (list :withdrawn *apd-msgid*) (fn-pat-decimal 1) (fn-pat-decimal 3))) :withdrawn)
                                 (equal (car (fn-pat-select (list :withdrawn *apd-msgid*) (fn-pat-decimal 2) (fn-pat-decimal 3))) :withdrawn))))
        1))
(assert-event (equal (fn-pat-select '(:empty) (fn-pat-decimal 1) (fn-pat-decimal 3)) '(:empty)))
; One worker delivers everything.
(assert-event (equal (fn-pat-select *apd-delivery* (fn-pat-decimal 0) (fn-pat-decimal 1)) *apd-delivery*))
; Messages spread: three Message-IDs do not all land in one partition of 4.
(assert-event
 (not (equal (list (fn-pat-partition (fn-ak-text "<a@x>") 4) (fn-pat-partition (fn-ak-text "<b@x>") 4)
                   (fn-pat-partition (fn-ak-text "<c@x>") 4) (fn-pat-partition (fn-ak-text "<d@x>") 4))
             (make-list 4 :initial-element (fn-pat-partition (fn-ak-text "<a@x>") 4)))))

; ---------------------------------------------------------------------------
; PRF-1325/1329 keystones with their teeth (TEETH CONTRACT v1).  Not here:
; fn-pat-select-is-one-worker, whose (posp workers) hypothesis has no
; counterexample (fn-pat-select skips exactly when the index is not the
; partition, and fn-pat-partition is total in N), so its removal waits on a
; proof of the weakened theorem; fn-pat-reader-delivers-what-the-writer-encoded
; (four hypotheses over a projected cursor event, owed).
(defteeth fn-pat-partition-is-a-worker
  :claim (((workers (posp n)))
          (and (natp (fn-pat-partition msgid n)) (< (fn-pat-partition msgid n) n)))
  :subject fn-pat-select
  :witness ((msgid *apd-msgid*) (n 3))
  :breaks ((workers ((msgid *apd-msgid*) (n 0))))
  :mutations ((worker-zero-unused
               (:conclusion (and (natp (fn-pat-partition msgid n))
                                 (< 0 (fn-pat-partition msgid n))
                                 (< (fn-pat-partition msgid n) n)))
               ((msgid *apd-msgid*) (n 3))
               :fault "a partition that never chooses worker 0")))

(defteeth fn-pat-values-check-is-the-kind
  :claim (() (iff (fn-pat-values-check name-word from seconds group msgid)
                  (not (fn-ak-rows-valuesp *fn-ak-v1-rows*
                                           (fn-pat-values name-word from seconds group msgid)))))
  :subject fn-pat-values-check
  :witness ((name-word *apd-name*) (from (fn-ak-text "nomailbox")) (seconds 0)
            (group *apd-group*) (msgid *apd-msgid*))
  :mutations ((check-inverted
               (:conclusion (iff (fn-pat-values-check name-word from seconds group msgid)
                                 (fn-ak-rows-valuesp *fn-ak-v1-rows*
                                                     (fn-pat-values name-word from seconds group msgid))))
               ((name-word *apd-name*) (from *apd-from*) (seconds *apd-seconds*)
                (group *apd-group*) (msgid *apd-msgid*))
               :fault "a values check that refuses exactly the article-kind rows it should pass")))

; ---------------------------------------------------------------------------
; fn-pat-reader-delivers-what-the-writer-encoded (TEETH CONTRACT v1).  The
; keystone's four antecedents sit inside its `let', so the claim has no
; labelled hypothesis and the removal witness is a mutation: the source
; antecedent dropped, at the fixture's own event (a source that is not the
; writer's encoding, delivered as :foreign).  The other three have no
; counterexample here: fn-pat-encode answers nil exactly for values or a
; payload outside the kind, and an :ok projection carries a nonempty source,
; so (nth 6 p) = the encoding forces :ok, a passing check and a payload of the
; kind together; their removal waits on a proof of the weakened theorem.
(defteeth fn-pat-reader-delivers-what-the-writer-encoded
  :claim (() (let ((p (fn-cpj-project cursor event)))
               (implies (and (equal (car p) :ok)
                             (not (fn-pat-values-check name-word from seconds group msgid))
                             (fn-ak-payloadp payload)
                             (equal (nth 6 p)
                                    (fn-pat-encode name-word from seconds group msgid payload)))
                        (equal (fn-pat-decode :opaque-1 (fn-pat-project cursor event))
                               (list :deliver (nth 2 p) (nth 5 p) payload)))))
  :subject fn-pat-decode
  :witness ((cursor *apd-cursor*) (event *apd-event-bytes*) (name-word *apd-name*)
            (from *apd-from*) (seconds *apd-seconds*) (group *apd-group*)
            (msgid *apd-msgid*) (payload *apd-payload*))
  :mutations ((without-the-source-antecedent
               (:conclusion (let ((p (fn-cpj-project cursor event)))
                              (implies (and (equal (car p) :ok)
                                            (not (fn-pat-values-check name-word from seconds group msgid))
                                            (fn-ak-payloadp payload))
                                       (equal (fn-pat-decode :opaque-1 (fn-pat-project cursor event))
                                              (list :deliver (nth 2 p) (nth 5 p) payload)))))
               ((cursor *apd-cursor*) (event *apd-other-bytes*) (name-word *apd-name*)
                (from *apd-from*) (seconds *apd-seconds*) (group *apd-group*)
                (msgid *apd-msgid*) (payload *apd-payload*))
               :fault "a reader that owes the payload for any projected event, whatever source it binds")
              (delivered-after-its-sequence
               (:conclusion (let ((p (fn-cpj-project cursor event)))
                              (implies (and (equal (car p) :ok)
                                            (not (fn-pat-values-check name-word from seconds group msgid))
                                            (fn-ak-payloadp payload)
                                            (equal (nth 6 p)
                                                   (fn-pat-encode name-word from seconds group msgid payload)))
                                       (equal (fn-pat-decode :opaque-1 (fn-pat-project cursor event))
                                              (list :deliver (1+ (nth 2 p)) (nth 5 p) payload)))))
               ((cursor *apd-cursor*) (event *apd-event-bytes*) (name-word *apd-name*)
                (from *apd-from*) (seconds *apd-seconds*) (group *apd-group*)
                (msgid *apd-msgid*) (payload *apd-payload*))
               :fault "a payload file numbered one past the event's sequence")))
