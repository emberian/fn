; Concrete FNCE4 chunk writer. The installed operation must reserve the exact
; record extent before calling this entry; this codec does not issue funds.
(in-package "ACL2")
(include-book "consumer-remote-event-codec")
(include-book "octets-stobj")

; Largest fixed header =38+4*64=294, larger than uint16+256 name.
(defconst *fn-crevb-max-chunk* (+ 38 (* 4 *fn-cp-max-id*)))

(defun fn-crevb-plan (answer used extent)
 (declare (xargs :guard t))
 (if (not (eq (fn-cp-nth 0 answer) :chunk)) (list :unchanged answer)
  (let ((chunk (fn-cp-nth 1 answer)))
   (cond ((not (and (fn-cbor-at-mostp chunk *fn-crevb-max-chunk*)
                    (fn-cbor-octet-listp chunk))) '(:refused :remote-event-chunk))
         ((not (and (natp used) (natp extent) (<= (+ used (len chunk)) extent)))
          '(:refused :remote-event-extent))
         (t (list :append chunk (fn-cp-nth 2 answer)))))))

(defun fn-crevb-step (s key extent fn-octets)
 (declare (xargs :stobjs fn-octets :guard t
                  :guard-hints (("Goal" :in-theory (enable fn-crevb-plan fn-cp-nth)))))
 (let ((plan (fn-crevb-plan (fn-crev-tick s key) (fn-octets-len fn-octets) extent)))
  (if (eq (fn-cp-nth 0 plan) :append)
      (let ((fn-octets (fn-octets-append-list (fn-cp-nth 1 plan) fn-octets)))
       (mv (list :yield (fn-cp-nth 2 plan)) fn-octets))
    (mv (if (eq (fn-cp-nth 0 plan) :unchanged) (fn-cp-nth 1 plan) plan) fn-octets))))

; Proof-only list observation of both the result and the complete effect.
(defun fn-crevb-reference (s key extent bytes)
 (declare (xargs :guard t))
 (let ((plan (fn-crevb-plan (fn-crev-tick s key) (len bytes) extent)))
  (if (eq (fn-cp-nth 0 plan) :append)
      (mv (list :yield (fn-cp-nth 2 plan)) (ec-call (binary-append bytes (fn-cp-nth 1 plan))))
    (mv (if (eq (fn-cp-nth 0 plan) :unchanged) (fn-cp-nth 1 plan) plan) bytes))))

(defthm fn-crevb-step-is-reference-result-and-buffer-effect
 (equal (fn-crevb-step s key extent fn-octets)
        (fn-crevb-reference s key extent fn-octets))
 :rule-classes nil
 :hints (("Goal" :in-theory
          (e/d (fn-crevb-step fn-crevb-reference fn-oct-len-is-len fn-oct-append-list-is-append)
               (fn-crevb-plan fn-crev-tick fn-cp-nth len)))))

(in-theory (disable fn-crevb-plan fn-crevb-step fn-crevb-reference))
