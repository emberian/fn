; fn: witnesses and teeth for books/owner-reclaim.lisp (Q16, lane
; online-reclaim): the online reclaim pass over the owner's rows.
(in-package "ACL2")
(include-book "../../books/owner-reclaim")
(include-book "must-fail-checked")
(include-book "arena-lift")
; The owner fixture's store (*rpt-s*, its arena *rpt-payloads*, its history's
; octets rpt-events) and the expiring context over it (*xt-ctx*: every
; article expired; *xt-ctx0*: no policy, nothing released).
(include-book "expiry-tests")

(bpr-lift fn-orc-rows-octets 1)
(bpr-lift fn-orc-rewrite-rows 2)
(bpr-lift fn-orc-fold 3)

(defconst *ort-rows* (fn-sf-records (fn-sn-files *rpt-s*)))
; (macros, not constants: the codec's attachment is not callable in a defconst)
(defmacro ort-new () '(in-arena-fn-orc-rewrite-rows *rpt-payloads* *ort-rows* *xt-ctx*))

; The rows' octets are the committed history the offline verb streams.
(assert-event (equal (in-arena-fn-orc-rows-octets *rpt-payloads* *ort-rows*) (rpt-events)))

; KEYSTONE fn-orc-rewrite-rows-is-the-offline-rewrite, positive witness: the
; rewrite changes rows (three articles expire), and the octets of the
; rewritten rows are the offline rewrite of the history.
(assert-event (not (equal (ort-new) *ort-rows*)))
(assert-event (equal (len (fn-rclp-rewritten-msgids (rpt-events) *xt-ctx*)) 3))
(assert-event (equal (in-arena-fn-orc-rows-octets *rpt-payloads* (ort-new))
                     (fn-rclp-events (rpt-events) *xt-ctx*)))
; Mutation: the rows kept as they were are not the offline rewrite.
(must-fail-checked
 (assert-event (equal (in-arena-fn-orc-rows-octets *rpt-payloads* *ort-rows*)
                      (fn-rclp-events (rpt-events) *xt-ctx*))))
; Under no policy the rewrite is the identity, and so is the offline one.
(assert-event (equal (in-arena-fn-orc-rewrite-rows *rpt-payloads* *ort-rows* *xt-ctx0*)
                     *ort-rows*))
; A rerun over the rewritten rows rewrites nothing
; (fn-rclp-events-idempotent, through the keystone).
(assert-event (equal (in-arena-fn-orc-rewrite-rows *rpt-payloads* (ort-new) *xt-ctx*)
                     (ort-new)))

; fn-orc-fold-is-the-offline-fold: the fold over the rows is the offline
; fold over the history (count, Message-IDs, freed octets).
(assert-event (equal (in-arena-fn-orc-fold *rpt-payloads* *ort-rows* *xt-ctx* (fn-rcls-init))
                     (fn-rcls-fold (rpt-events) *xt-ctx* (fn-rcls-init))))
(assert-event (equal (len (nth 1 (in-arena-fn-orc-fold *rpt-payloads* *ort-rows* *xt-ctx*
                                                       (fn-rcls-init))))
                     3))

; KEYSTONE fn-orc-decision-names-the-rewritten-articles, positive witness:
; recorded, admitted, not a dry run, the decision reclaims and names the
; three rewritten articles and the freed octets.
(defconst *ort-profile*
  (fn-bs-profile-set-fields *fn-bs-profile-defaults*
                            '((1 . 1000) (4 . 20000) (7 . 1000) (3 . 1090139))))
(assert-event (fn-bs-profile-admittedp *ort-profile*))
(defconst *ort-v* (fn-cfg-value (fn-rci-recorded-config (fn-cfg-make 0 *xt-star*)
                                                        0 0 1 0 *xt-late*)))
(assert-event (fn-rci-recordedp *ort-v*))
(bpr-lift fn-rci-decide-stream 5)
(defmacro ort-acc () '(in-arena-fn-orc-fold *rpt-payloads* *ort-rows* *xt-ctx* (fn-rcls-init)))
(defmacro ort-d () '(in-arena-fn-rci-decide-stream *rpt-payloads* *ort-profile* *ort-v* *rpt-s*
                                                     (ort-acc) nil))
(assert-event (equal (car (ort-d)) :reclaim))
(assert-event (equal (nth 1 (ort-d)) (fn-rclp-rewritten-msgids (rpt-events) *xt-ctx*)))
(assert-event (equal (nth 2 (ort-d)) (fn-rclp-freed (rpt-events) *xt-ctx*)))
(assert-event (consp (fn-rclp-rewritten-msgids (rpt-events) *xt-ctx*)))
; Each concluded condition fails alone: a dry run, an unrecorded
; configuration, a profile not admitted, a context releasing nothing.
(assert-event (equal (car (in-arena-fn-rci-decide-stream *rpt-payloads* *ort-profile* *ort-v*
                                                         *rpt-s* (ort-acc) t))
                     :dry-run))
(assert-event (equal (in-arena-fn-rci-decide-stream *rpt-payloads* *ort-profile*
                                                    (fn-cfg-value (fn-cfg-make 0 *xt-star*))
                                                    *rpt-s* (ort-acc) nil)
                     '(:refused :no-recorded-instant)))
(assert-event (equal (in-arena-fn-rci-decide-stream *rpt-payloads* '(1 2 3) *ort-v*
                                                    *rpt-s* (ort-acc) nil)
                     '(:refused :profile)))
(assert-event (equal (car (in-arena-fn-rci-decide-stream
                           *rpt-payloads* *ort-profile* *ort-v* *rpt-s*
                           (in-arena-fn-orc-fold *rpt-payloads* *ort-rows* *xt-ctx0*
                                                 (fn-rcls-init))
                           nil))
                     :none))
; The request.
(assert-event (equal (fn-orc-request-word nil nil nil t) :requested))
(assert-event (equal (fn-orc-request-status :requested) :accepted))
(assert-event (equal (fn-orc-request-word :captured nil nil t) :in-flight))
(assert-event (equal (fn-orc-request-word nil 12 nil t) :queued))
(assert-event (equal (fn-orc-request-word nil nil t t) :blocked))
(assert-event (equal (fn-orc-request-status :blocked) :refused))
(assert-event (equal (fn-orc-request-word nil nil nil nil) :no-recorded-instant))
(assert-event (equal (fn-orc-request-status :no-recorded-instant) :refused))
(must-fail-checked
 (defthm ort-never-past-a-deferral-without-idle
   (implies blockedp
            (equal (fn-orc-request-status (fn-orc-request-word pass inflight blockedp recordedp))
                   :refused))
   :rule-classes nil))

; Sweep S038: the capture's own admission (fn-orc-capture-slot, KEYSTONE
; fn-orc-capture-takes-only-a-free-slot).
; Positive witnesses, every arm: a free slot is taken (a writing pass holds
; INFLIGHT at its count, a dry run leaves it); a held pass refuses
; :in-flight and a publication in flight refuses a writing pass :queued,
; each leaving the slot as it was; a dry run beside a publication is taken.
(assert-event
 (and (equal (fn-orc-capture-slot :recorded 7 nil nil) '(:capture :recorded 7))
      (equal (fn-orc-capture-slot :dry-run 7 nil nil) '(:capture :dry-run nil))
      (equal (fn-orc-capture-slot :recorded 9 :dry-run nil) '(:in-flight :dry-run nil))
      (equal (fn-orc-capture-slot :dry-run 9 :recorded 7) '(:in-flight :recorded 7))
      (equal (fn-orc-capture-slot :recorded 9 nil 5) '(:queued nil 5))
      (equal (fn-orc-capture-slot :dry-run 9 nil 5) '(:capture :dry-run 5))))
; The third conjunct, positive: after a taken capture every second capture,
; of either mode, is refused.
(assert-event
 (let ((r (fn-orc-capture-slot :recorded 7 nil nil)))
   (and (keywordp :recorded) (equal (car r) :capture)
        (equal (car (fn-orc-capture-slot :recorded 8 (cadr r) (caddr r))) :in-flight)
        (equal (car (fn-orc-capture-slot :dry-run 8 (cadr r) (caddr r))) :in-flight))))
; Hypothesis removal for (keywordp mode): a MODE of nil is taken (the
; antecedent's other half holds), is not a keyword, and leaves the slot
; free of a pass, so a second capture (a dry run, which no publication
; count stops) is taken too: the conclusion fails.
(assert-event
 (let ((r (fn-orc-capture-slot nil 7 nil nil)))
   (and (equal (car r) :capture)
        (not (keywordp nil))
        (equal (car (fn-orc-capture-slot :dry-run 8 (cadr r) (caddr r))) :capture))))
; Mutation (labelled): the pre-S038 capture, which wrote the slot without
; deciding, over a slot a publication holds (case (b) of the finding): it
; overwrites the publication's count, which the decision above never does.
(defun ost-pre-s038-capture (mode count pass inflight)
  (declare (ignore pass))
  (list :capture mode (if (eq mode :dry-run) inflight count)))
(assert-event
 (and (not (equal (cdr (ost-pre-s038-capture :recorded 9 nil 5)) (list nil 5)))
      (equal (cdr (fn-orc-capture-slot :recorded 9 nil 5)) (list nil 5))))
