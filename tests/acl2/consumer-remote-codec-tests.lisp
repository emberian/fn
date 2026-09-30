; Protocol component witnesses. These are not endpoint/credential proofs.
(in-package "ACL2")
(include-book "../../books/consumer-remote-codec")

(defconst *cr-login* '(97 108 105 99 101))
(defconst *cr-secret* '(112 97 115 115))
(defconst *cr-consumer* '(97 103 101 110 116))
(defconst *cr-groups* '((102 110 46 97) (102 110 46 98)))
(defconst *cr-cursor*
  (fn-cp-cursor-encode
   (fn-cp-cursor '(104) '(105) *cr-consumer* '(112) '(113) 1 2 3 4)))

(defun cr-request (op groups cursor seconds)
  (list :remote-consumer op *cr-login* *cr-secret* *cr-consumer*
        groups cursor seconds))

; Each operation is a nonempty reachable antecedent and complete conclusion
; of fn-cr-decoded-request-is-protected-and-consumer-only, plus exact fields.
(defun cr-positivep (request)
  (let* ((bytes (fn-cr-request-encode request 8))
         (answer (fn-cr-request-decode bytes t 8)))
    (and (not (equal bytes :bad))
         (eq (car answer) :remote-consumer)
         (fn-cr-requestp answer 8)
         (member-eq (fn-cp-nth 1 answer) *fn-cr-operations*)
         (equal answer request))))

(assert-event (cr-positivep (cr-request :register *cr-groups* nil 0)))
(assert-event (cr-positivep (cr-request :rebase *cr-groups* nil 0)))
(assert-event (cr-positivep (cr-request :poll nil nil 0)))
(assert-event (cr-positivep (cr-request :wait nil nil 30)))
(assert-event (cr-positivep (cr-request :position nil nil 0)))
(assert-event (cr-positivep (cr-request :status nil nil 0)))
(assert-event (cr-positivep (cr-request :ack nil *cr-cursor* 0)))
(assert-event (cr-positivep (cr-request :unregister nil nil 0)))

; Hypothesis-removal witness: without a remote-consumer answer none of the
; admission conclusion follows (false protected channel, refusal not valid).
(assert-event
 (let ((answer (fn-cr-request-decode
                (fn-cr-request-encode (cr-request :poll nil nil 0) 8) nil 8)))
   (and (not (eq (car answer) :remote-consumer))
        (not (fn-cr-requestp answer 8))
        (not (member-eq (fn-cp-nth 1 answer) *fn-cr-operations*))
        (equal answer '(:refused :protected-channel)))))

; Private owner/admin/bootstrap commands have no remote enumeration value.
(assert-event (equal (fn-cr-request-encode (cr-request :bootstrap nil nil 0) 8) :bad))
(assert-event (equal (fn-cr-request-encode (cr-request :admin nil nil 0) 8) :bad))
(assert-event
 (equal (fn-cr-request-decode (fn-ncl-request-encode :poll *cr-consumer* nil) t 8)
        '(:refused :frame)))
(assert-event
 (equal (fn-cr-request-encode (cr-request :register *cr-groups* nil 0) 1) :bad))
(assert-event
 (equal (fn-cr-request-encode (cr-request :poll *cr-groups* nil 0) 8) :bad))
(assert-event
 (equal (fn-cr-request-encode (cr-request :wait nil nil 3601) 8) :bad))
(assert-event
 (equal (fn-cr-request-encode
         (update-nth 4 '(111 116 104 101 114) (cr-request :ack nil *cr-cursor* 0)) 8)
        :bad))
(assert-event
 (equal (fn-cr-request-encode
         (update-nth 3 nil (cr-request :poll nil nil 0)) 8) :bad))
; A group name greater than a cursor ID is represented in its group blob.
(assert-event
 (cr-positivep
  (cr-request :register (list (append '(102 110 46) (make-list 70 :initial-element 97)))
              nil 0)))

; Corruption/mutation witnesses: trailing bytes, changed version, damaged
; integrity trailer, and a remote frame beyond the preflight budget refuse.
(assert-event
 (equal (car (fn-cr-request-decode
              (append (fn-cr-request-encode (cr-request :poll nil nil 0) 8) '(0)) t 8))
        :refused))
(assert-event
 (equal (car (fn-cr-request-decode
              (update-nth 4 2 (fn-cr-request-encode (cr-request :poll nil nil 0) 8)) t 8))
        :refused))
(assert-event
 (let* ((frame (fn-cr-request-encode (cr-request :poll nil nil 0) 8))
        (n (1- (len frame))))
   (equal (car (fn-cr-request-decode
                (update-nth n (mod (1+ (nth n frame)) 256) frame) t 8))
          :refused)))
(assert-event
 (equal (fn-cr-request-decode (make-list (1+ (fn-cr-read-bound 1)) :initial-element 0) t 1)
        '(:refused :size)))
