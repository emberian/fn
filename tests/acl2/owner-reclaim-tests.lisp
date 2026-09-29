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
