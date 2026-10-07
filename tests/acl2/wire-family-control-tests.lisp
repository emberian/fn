; Teeth for books/wire-family-control (fnct.reasoned-reply, kind 18, and
; fnct.line-reply, kind 23).
;
; Positive: refused, uncertain and accepted replies with a named reason and
; with NONE: the host's encoding is the grammar's and both decoders accept it
; with the same value.  Agreement on refusals: an empty reason, a reason past
; 512 octets, an unknown status code, a trailing octet and the wrong kind are
; refused by both.  A lined reply without a line is sent as kind 18, which
; the kind-23 grammar refuses.
(in-package "ACL2")
(include-book "../../books/wire-family-control")
(include-book "../../books/defkeystone")

(defun wfctl-reasoned-agrees (status reason)
  (let* ((x (fn-native-control-reasoned-reply-encode status reason))
         (v (list status (fn-nctrl-reason-word reason))))
    (and (not (equal x :bad))
         (equal x (fn-wg-encode *fn-wf-ctl-reasoned-reply-grammar* v))
         (equal (fn-nctrl-reasoned-reply-payload-decode (fn-nctrl-open x 18)) v)
         (equal (fn-wg-decode *fn-wf-ctl-reasoned-reply-grammar* x) (fn-wg-ok v nil)))))

(defun wfctl-lined-agrees (status reason line)
  (let* ((x (fn-native-control-lined-reply-encode status reason line))
         (v (list status (fn-nctrl-reason-word reason) (fn-ncline-line line))))
    (and (not (equal x :bad))
         (equal x (fn-wg-encode *fn-wf-ctl-lined-reply-grammar* v))
         (equal (fn-ncline-reply-payload-decode (fn-nctrl-open x 23)) v)
         (equal (fn-wg-decode *fn-wf-ctl-lined-reply-grammar* x) (fn-wg-ok v nil)))))

(assert-event
 (and (wfctl-reasoned-agrees :refused :no-owner)
      (wfctl-reasoned-agrees :uncertain nil)
      (wfctl-reasoned-agrees :accepted nil)
      (wfctl-lined-agrees :accepted nil "applied: max-connections 64")
      (wfctl-lined-agrees :refused :limit-exceeds-profile "x")))

(defun wfctl-both-refuse-18 (x)
  (and (equal (fn-nctrl-reasoned-reply-payload-decode (fn-nctrl-open x 18)) :bad)
       (not (and (fn-wg-okp (fn-wg-decode *fn-wf-ctl-reasoned-reply-grammar* x))
                 (null (fn-wg-rest (fn-wg-decode *fn-wf-ctl-reasoned-reply-grammar* x)))))))

(assert-event
 (let ((good (fn-native-control-reasoned-reply-encode :refused :no-owner)))
   (and (wfctl-both-refuse-18 (fn-wg-encode *fn-wf-ctl-reasoned-reply-grammar* '(:refused nil)))
        (wfctl-both-refuse-18 (fn-wg-encode *fn-wf-ctl-reasoned-reply-grammar*
                                            (list :refused (make-list 513 :initial-element 97))))
        (wfctl-both-refuse-18 (fn-nctrl-seal 18 (list 99 0 0 0 1 97)))
        (wfctl-both-refuse-18 (append good '(0)))
        (wfctl-both-refuse-18 (fn-nctrl-seal 23 (list 3 0 0 0 1 97)))
        ; no line: kind 18, refused by the kind-23 grammar
        (not (fn-wg-okp (fn-wg-decode *fn-wf-ctl-lined-reply-grammar*
                                      (fn-native-control-lined-reply-encode :refused :no-owner nil)))))))

; ---------------------------------------------------------------------------
; The kind-18 and kind-23 agreement keystones with their teeth (TEETH
; CONTRACT v1).  A decoder keystone's octet-list hypothesis has no
; counterexample (a non-octet list is refused by both sides), so it stays
; inside the claim and the teeth are two conclusion mutations.  An encoder
; keystone's hypotheses are removed at an unknown status (the encoder refuses,
; the status has no grammar value) and, for the lined reply, at a missing
; line (sent as kind 18, which the kind-23 grammar does not accept).
(defconst *wfctl-reasoned-good* (fn-native-control-reasoned-reply-encode :refused :no-owner))
(defconst *wfctl-lined-good*
  (fn-native-control-lined-reply-encode :accepted nil "applied: max-connections 64"))

(defteeth fn-wf-ctl-reasoned-decode-agrees
  :claim (() (implies (fn-cbor-octet-listp x)
                      (let ((r (fn-nctrl-reasoned-reply-payload-decode (fn-nctrl-open x 18)))
                            (w (fn-wg-decode *fn-wf-ctl-reasoned-reply-grammar* x)))
                        (and (iff (not (equal r :bad))
                                  (and (fn-wg-okp w) (null (fn-wg-rest w))))
                             (implies (not (equal r :bad))
                                      (equal (fn-wg-value w) r))))))
  :subject fn-nctrl-reasoned-reply-payload-decode
  :witness ((x *wfctl-reasoned-good*))
  :mutations ((reason-dropped
               (:conclusion (implies (fn-cbor-octet-listp x)
                             (let ((r (fn-nctrl-reasoned-reply-payload-decode (fn-nctrl-open x 18)))
                                   (w (fn-wg-decode *fn-wf-ctl-reasoned-reply-grammar* x)))
                               (and (iff (not (equal r :bad))
                                         (and (fn-wg-okp w) (null (fn-wg-rest w))))
                                    (implies (not (equal r :bad))
                                             (equal (fn-wg-value w) (list (car r) nil)))))))
               ((x *wfctl-reasoned-good*))
               :fault "a decoder that drops the reason word")
              (trailing-octets-accepted
               (:conclusion (implies (fn-cbor-octet-listp x)
                             (let ((r (fn-nctrl-reasoned-reply-payload-decode (fn-nctrl-open x 18)))
                                   (w (fn-wg-decode *fn-wf-ctl-reasoned-reply-grammar* x)))
                               (and (iff (not (equal r :bad)) (fn-wg-okp w))
                                    (implies (not (equal r :bad))
                                             (equal (fn-wg-value w) r))))))
               ((x (append *wfctl-reasoned-good* '(0))))
               :fault "a decoder that accepts a frame followed by a trailing octet")))

(defteeth fn-wf-ctl-reasoned-encode-agrees
  :claim (((encodes (not (equal (fn-native-control-reasoned-reply-encode status reason) :bad))))
          (let ((v (list status (fn-nctrl-reason-word reason))))
            (and (fn-wg-valuep *fn-wf-ctl-reasoned-reply-grammar* v)
                 (equal (fn-native-control-reasoned-reply-encode status reason)
                        (fn-wg-encode *fn-wf-ctl-reasoned-reply-grammar* v)))))
  :subject fn-native-control-reasoned-reply-encode
  :witness ((status :refused) (reason :no-owner))
  :breaks ((encodes ((status :bogus) (reason nil))))
  :mutations ((reason-dropped
               (:conclusion (let ((v (list status (fn-nctrl-reason-word nil))))
                              (and (fn-wg-valuep *fn-wf-ctl-reasoned-reply-grammar* v)
                                   (equal (fn-native-control-reasoned-reply-encode status reason)
                                          (fn-wg-encode *fn-wf-ctl-reasoned-reply-grammar* v)))))
               ((status :refused) (reason :no-owner))
               :fault "an encoder that never writes the reason it was given")))

(defteeth fn-wf-ctl-lined-decode-agrees
  :claim (() (implies (fn-cbor-octet-listp x)
                      (let ((r (fn-ncline-reply-payload-decode (fn-nctrl-open x 23)))
                            (w (fn-wg-decode *fn-wf-ctl-lined-reply-grammar* x)))
                        (and (iff (not (equal r :bad))
                                  (and (fn-wg-okp w) (null (fn-wg-rest w))))
                             (implies (not (equal r :bad))
                                      (equal (fn-wg-value w) r))))))
  :subject fn-ncline-reply-payload-decode
  :witness ((x *wfctl-lined-good*))
  :mutations ((line-dropped
               (:conclusion (implies (fn-cbor-octet-listp x)
                             (let ((r (fn-ncline-reply-payload-decode (fn-nctrl-open x 23)))
                                   (w (fn-wg-decode *fn-wf-ctl-lined-reply-grammar* x)))
                               (and (iff (not (equal r :bad))
                                         (and (fn-wg-okp w) (null (fn-wg-rest w))))
                                    (implies (not (equal r :bad))
                                             (equal (fn-wg-value w) (list (car r) (cadr r) nil)))))))
               ((x *wfctl-lined-good*))
               :fault "a decoder that drops the line")
              (trailing-octets-accepted
               (:conclusion (implies (fn-cbor-octet-listp x)
                             (let ((r (fn-ncline-reply-payload-decode (fn-nctrl-open x 23)))
                                   (w (fn-wg-decode *fn-wf-ctl-lined-reply-grammar* x)))
                               (and (iff (not (equal r :bad)) (fn-wg-okp w))
                                    (implies (not (equal r :bad))
                                             (equal (fn-wg-value w) r))))))
               ((x (append *wfctl-lined-good* '(0))))
               :fault "a decoder that accepts a frame followed by a trailing octet")))

(defteeth fn-wf-ctl-lined-encode-agrees
  :claim (((line (fn-ncline-line line))
           (encodes (not (equal (fn-native-control-lined-reply-encode status reason line) :bad))))
          (let ((v (list status (fn-nctrl-reason-word reason) (fn-ncline-line line))))
            (and (fn-wg-valuep *fn-wf-ctl-lined-reply-grammar* v)
                 (equal (fn-native-control-lined-reply-encode status reason line)
                        (fn-wg-encode *fn-wf-ctl-lined-reply-grammar* v)))))
  :subject fn-native-control-lined-reply-encode
  :witness ((status :accepted) (reason nil) (line "applied: max-connections 64"))
  :breaks ((line ((status :accepted) (reason nil) (line nil)))
           (encodes ((status :bogus) (reason nil) (line "x"))))
  :mutations ((line-dropped
               (:conclusion (let ((v (list status (fn-nctrl-reason-word reason) nil)))
                              (and (fn-wg-valuep *fn-wf-ctl-lined-reply-grammar* v)
                                   (equal (fn-native-control-lined-reply-encode status reason line)
                                          (fn-wg-encode *fn-wf-ctl-lined-reply-grammar* v)))))
               ((status :accepted) (reason nil) (line "applied: max-connections 64"))
               :fault "an encoder that never writes the line it was given")))
