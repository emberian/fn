; Teeth for books/native-control-line (row S1, PRF-975): the reasoned reply
; with a line, FNCT kind 23.  KEYSTONE fn-native-control-printed-line-is-the-
; decisions: a reachable witness asserting its whole antecedent and
; conclusion over the sentence a live limit decision renders
; (books/limits-live.lisp fn-lim-decision-line, the line
; host/native/admin.lisp fnn-owner-limit-serialized answers); per hypothesis
; a witness that keeps the other, fails the omitted one and fails the
; conclusion, then a must-fail of the weakened theorem.
(in-package "ACL2")
(include-book "../../books/native-control-line")
(include-book "../../books/limits-live")
(include-book "../../books/codec-attach")
(include-book "must-fail-checked")

(defconst *nclt-applied*
  (fn-lim-decision-line "max-transactions" 14 '(:applied 2342) 900))
(defconst *nclt-recorded*
  (fn-lim-decision-line "max-history-octets" 805306368 '(:at-restart 13398) 900))
(defconst *nclt-below*
  (fn-lim-decision-line "max-transactions" 3
                        '(:refused :below-current-use "max-transactions" 6) 900))

(defmacro nclt-printed (status reason line)
  `(let ((step (fn-native-control-lined-client-step
                (fn-native-control-lined-reply-read
                 (fn-native-control-lined-reply-encode ,status ,reason ,line)))))
     (and (equal step (list :status ,status (fn-nctrl-reason-word ,reason)
                            (fn-ncline-line ,line)))
          (equal (fn-native-control-lined-detail step)
                 (fn-ncline-line ,line)))))

; Reachable witnesses: the three sentences the live verb answers, each the
; whole antecedent (a status in the enumeration, a line ACL2 accepts) and the
; conclusion (the step carries the line, the printed detail is its octets).
(assert-event (equal *nclt-applied*
                     "applied limit max-transactions=14 heap=2342 MB: served now, no data moved"))
(assert-event (and (member-equal :accepted *fn-nctrl-statuses*)
                   (fn-ncline-line *nclt-applied*)
                   (nclt-printed :accepted (fn-lim-decision-reason '(:applied 2342))
                                 *nclt-applied*)))
(assert-event (equal (fn-ncline-line *nclt-applied*)
                     (fn-record-string-octets *nclt-applied*)))
(assert-event (and (member-equal :accepted *fn-nctrl-statuses*)
                   (fn-ncline-line *nclt-recorded*)
                   (nclt-printed :accepted (fn-lim-decision-reason '(:at-restart 13398))
                                 *nclt-recorded*)))
(assert-event (and (member-equal :refused *fn-nctrl-statuses*)
                   (fn-ncline-line *nclt-below*)
                   (nclt-printed :refused
                                 (fn-lim-decision-reason
                                  '(:refused :below-current-use "max-transactions" 6))
                                 *nclt-below*)))
; The sentence is one line, not one word: it has spaces, and the reason
; field still names the decision's class.
(assert-event (member-equal 32 (fn-ncline-line *nclt-applied*)))
(assert-event (equal (fn-nctrl-reason-word (fn-lim-decision-reason '(:applied 2342)))
                     (fn-record-string-octets "applied")))

; Hypothesis (member status): the line is accepted, the status is not in the
; enumeration; nothing is sealed and the client steps to the transport.
(assert-event (fn-ncline-line *nclt-applied*))
(assert-event (not (member-equal :no-such-status *fn-nctrl-statuses*)))
(assert-event (equal (fn-native-control-lined-reply-encode :no-such-status :applied
                                                           *nclt-applied*)
                     :bad))
(assert-event (not (nclt-printed :no-such-status :applied *nclt-applied*)))
(must-fail-checked
 (defthm nclt-without-membership
   (implies (fn-ncline-line line)
            (equal (fn-native-control-lined-client-step
                    (fn-native-control-lined-reply-read
                     (fn-native-control-lined-reply-encode status reason line)))
                   (list :status status (fn-nctrl-reason-word reason)
                         (fn-ncline-line line))))
   :hints (("Goal" :in-theory (disable member-equal)))
   :rule-classes nil))

; Hypothesis (a line ACL2 accepts): the status is in the enumeration; a line
; with a newline, an empty line, a non-string and a line of 1,025 octets are
; not lines, and the reply is kind 18 unchanged: the step has no line.
(defconst *nclt-long* (coerce (make-list 1025 :initial-element #\a) 'string))
(assert-event (member-equal :accepted *fn-nctrl-statuses*))
(assert-event (not (fn-ncline-line (concatenate 'string "applied" (string #\Newline)))))
(assert-event (not (fn-ncline-line "")))
(assert-event (not (fn-ncline-line 'applied)))
(assert-event (not (fn-ncline-line *nclt-long*)))
(assert-event (fn-ncline-line (subseq *nclt-long* 0 1024)))
(assert-event (equal (fn-native-control-lined-client-step
                      (fn-native-control-lined-reply-read
                       (fn-native-control-lined-reply-encode :accepted :applied *nclt-long*)))
                     (list :status :accepted (fn-record-string-octets "applied"))))
(assert-event (not (nclt-printed :accepted :applied *nclt-long*)))
(must-fail-checked
 (defthm nclt-without-a-line
   (implies (member-equal status *fn-nctrl-statuses*)
            (equal (fn-native-control-lined-client-step
                    (fn-native-control-lined-reply-read
                     (fn-native-control-lined-reply-encode status reason line)))
                   (list :status status (fn-nctrl-reason-word reason)
                         (fn-ncline-line line))))
   :rule-classes nil))

; The lineless reply is the reasoned reply's octets, kind 18 (an old client
; reads it): fn-ncline-read-of-a-lineless-encode's witness.
(assert-event (equal (fn-native-control-lined-reply-encode :refused :below-current-use nil)
                     (fn-native-control-reasoned-reply-encode :refused :below-current-use)))
