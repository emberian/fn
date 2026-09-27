; Witnesses for books/owner-results.lisp: per typed result a ground value the
; recognizer the native host checks (host/native/owner.lisp fnn-owner-result)
; accepts and a malformed one it refuses (the host then faults, exit 4); the
; keystone fn-ores-sealed-plan-is-indexed-fetch on a two-peer plan; the
; by-definition equations on ground values.

(in-package "ACL2")
(include-book "../../books/owner-results")
(include-book "std/testing/must-fail" :dir :system)

; Two FNFD enqueue records for two peers, in journal order.
(defconst *ort-inn* '(105 110 110))                   ; "inn"
(defconst *ort-fnb* '(102 110 98))                    ; "fnb"
(defconst *ort-msgid* '(60 97 64 102 110 62))         ; "<a@fn>"
(defconst *ort-records*
  (list (list :feed-enqueue (list *ort-inn* *ort-msgid* 7))
        (list :feed-enqueue (list *ort-fnb* *ort-msgid* 7))))
; A record the codec refuses (no such kind): its frame is :bad.
(defconst *ort-bad-records*
  (list (list :feed-nonsense (list *ort-inn* *ort-msgid* 7))))

; A macro, not a constant: the seal calls the attached trailer, which a
; defconst may not evaluate.
(defmacro ort-publication ()
  '(fn-ores-feed-publication :ready nil *ort-records* 7 nil :ok nil))

; FeedPublication, positive: the recognizer holds, the plan has one pair per
; record, the pairs are in the records' order and name each record's peer,
; and each frame is non-empty sealed octets.
(assert-event (fn-ores-feed-publication-p (ort-publication)))
(assert-event (equal (strip-cars (fn-ores-feedpub-plan (ort-publication)))
                     '("inn" "fnb")))
(assert-event (equal (len (fn-ores-feedpub-plan (ort-publication))) 2))
(assert-event (equal (fn-ores-feedpub-word (ort-publication)) :ready))
(assert-event (equal (fn-ores-feedpub-token (ort-publication)) 7))
; The keystone on the ground plan, at both indices and past the end: the
; I-th pair is the I-th peer of the old peer list and the seal of the I-th
; encoded frame (the two answers the host used to join by index).
(assert-event
 (let ((plan (fn-ores-sealed-plan *ort-records*)))
   (and (equal (nth 0 plan)
               (cons (nth 0 (fn-ores-record-peers *ort-records*))
                     (fn-ores-seal (fn-frame-item 0 (fn-ores-encode-records *ort-records*)))))
        (equal (nth 1 plan)
               (cons (nth 1 (fn-ores-record-peers *ort-records*))
                     (fn-ores-seal (fn-frame-item 1 (fn-ores-encode-records *ort-records*)))))
        (equal (nth 2 plan) nil)
        (not (equal (cdr (nth 0 plan)) (cdr (nth 1 plan)))))))
; The seal verifies: the trailer over the protected prefix is the frame's.
(assert-event
 (let ((frame (cdr (nth 0 (fn-ores-sealed-plan *ort-records*)))))
   (equal (fn-frame-trailer (fn-frame-protected-prefix frame))
          (nthcdr (- (len frame) 32) frame))))

; FeedPublication, malformed: a refused record seals to :bad and the host
; refuses the value; so does a non-symbol word and a non-octet command.
(assert-event (equal (cdr (car (fn-ores-sealed-plan *ort-bad-records*))) :bad))
(assert-event (not (fn-ores-feed-publication-p
                    (fn-ores-feed-publication :ready nil *ort-bad-records* nil nil :ok nil))))
(assert-event (not (fn-ores-feed-publication-p
                    (fn-ores-feed-publication "ready" nil nil nil nil :ok nil))))
(assert-event (not (fn-ores-feed-publication-p
                    (fn-ores-feed-publication :offer nil nil nil '(300) :ok nil))))
(assert-event (not (fn-ores-feed-publication-p (cdr (ort-publication)))))

; The feed port's publication: the command rendered by ACL2 and its status.
(assert-event
 (let ((p (fn-ores-feed-port-publication :idle nil nil nil nil)))
   (and (fn-ores-feed-publication-p p)
        (equal (fn-ores-feedpub-plan p) nil)
        (equal (fn-ores-feedpub-peer p) nil))))

; SubmissionTaken.
(defconst *ort-taken*
  (fn-ores-submission-taken :taken 3 *ort-msgid* '(65 66) (list '(102 110))
                            '(:carry) nil nil))
(assert-event (fn-ores-submission-taken-p *ort-taken*))
(assert-event (equal (fn-ores-taken-octets *ort-taken*) '(65 66)))
(assert-event (not (fn-ores-submission-taken-p
                    (fn-ores-submission-taken :taken 3 "<a@fn>" '(65 66) nil nil nil nil))))
(assert-event (not (fn-ores-submission-taken-p
                    (fn-ores-submission-taken :took 3 *ort-msgid* '(65 66) nil nil nil nil))))

; ServedStep.
(defconst *ort-served*
  (fn-ores-served-step :ok '(50 48 48 13 10) nil t nil 5 '(97)))
(assert-event (fn-ores-served-step-p *ort-served*))
(assert-event (equal (fn-ores-served-starttlsp *ort-served*) t))
(assert-event (not (fn-ores-served-step-p
                    (fn-ores-served-step :ok '(50 48 48 13 10) 7 t nil 5 '(97)))))
(assert-event (not (fn-ores-served-step-p
                    (fn-ores-served-step :ok '(256) nil t nil 5 '(97)))))

; Capture.
(assert-event (fn-ores-capture-p (fn-ores-capture 10 4096 '(1 2) 9 65536)))
(assert-event (not (fn-ores-capture-p (fn-ores-capture 10 -1 '(1 2) 9 65536))))

; ConfigResult: a refusal names ACL2's reason; a staged result carries a
; non-empty record; each other combination is refused by the host.
(assert-event (equal (fn-ores-config-refused :no-delta)
                     '(:config-result :refused nil :no-delta)))
(assert-event (fn-ores-config-result-p (fn-ores-config-refused :no-delta)))
(assert-event (fn-ores-config-result-p '(:config-result :staged (1 2) nil)))
(assert-event (equal (fn-ores-config-staged-result nil :delta-kind)
                     '(:config-result :refused nil :delta-kind)))
(assert-event (not (fn-ores-config-result-p '(:config-result :staged nil nil))))
(assert-event (not (fn-ores-config-result-p '(:config-result :refused (1) :x))))
(assert-event (not (fn-ores-config-result-p '(:config-result :durable nil nil))))

; The recognizers are not vacuous: none holds of nil or of another shape.
(assert-event (not (or (fn-ores-feed-publication-p nil)
                       (fn-ores-submission-taken-p nil)
                       (fn-ores-served-step-p nil)
                       (fn-ores-capture-p nil)
                       (fn-ores-config-result-p nil)
                       (fn-ores-served-step-p *ort-taken*)
                       (fn-ores-config-result-p (ort-publication)))))
