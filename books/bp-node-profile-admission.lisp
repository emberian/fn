; The BP node profile at the receive boundary (PRF-134; D27, the codec half
; of P5; planning/design-2026-09-25-bounds.md section 5, P5 for BP).
;
; A received transfer reaches the FNBS machine only through
; `fn-bpnpf-admitted-receive-event', the function the host calls
; (host/native/bp-service.lisp fnn-bps-receive).  It applies the node's
; profile (books/bp-node-profile, fn-bpnpf-profile-read) before and after
; PRF-128's channel admission (fn-bpaj-admitted-receive-event):
;
;   - a wire longer than the profile's bundle octets is refused by name,
;     :bundle-beyond-profile, before the decoder reads it: the profile's
;     bundle octets are the decoder's input bound (the walk that checks it
;     visits at most that many conses plus one);
;   - a bundle whose ADU is longer than the profile's ADU octets (for a
;     fragment, the total ADU length its primary block names) is refused by
;     name, :adu-beyond-profile, before custody: a family can never grow an
;     ADU the profile does not admit;
;   - anything else is exactly the channel admission's answer
;     (fn-bpnpf-admission-within-profile-is-the-channel-answer), so every
;     PRF-128 theorem about that answer holds of this one.
;
; The held image's bound is the profile's held octets, which the machine
; state carries (fn-bpnpf-valid-profile-opens) and the step and the family
; plan check.  The codec widths are the profile's ceiling
; (fn-bpnpf-profile-within-codec-widths): no profile names a value a codec
; refuses.
(in-package "ACL2")
(include-book "bp-channel-ingress")
(include-book "bp-node-profile")

; The ADU a bundle carries: a fragment's total ADU length, else its payload's
; length.  0 for anything that is not a bundle.
(defun fn-bpnpf-bundle-adu-length (bundle)
  (declare (xargs :guard t))
  (if (not (fn-bpb-bundlep bundle))
      0
    (let* ((primary (fn-bpb-bundle-primary bundle))
           (flags (fn-bpn-nth 1 primary)))
      (if (and (natp flags) (fn-bpp-fragmentp flags))
          (nfix (fn-bpn-nth 10 primary))
        (len (fn-bpb-payload bundle))))))

(defun fn-bpnpf-ready-bundle (answer)
  (declare (xargs :guard t))
  (fn-bpn-nth 1 (fn-bpnf-receive-wire-event-value answer)))

(defun fn-bpnpf-admitted-receive-event (profile admission config wire observation)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((not (fn-bpnpf-profilep profile))
         (list :refused :profile))
        ((equal (fn-cbor-ag-car admission) :refused)
         (fn-bpaj-admitted-receive-event admission config wire observation))
        ((not (fn-cbor-at-mostp wire (fn-bpnpf-bundle-octets profile)))
         (list :refused :bundle-beyond-profile))
        (t
         (let ((answer (fn-bpaj-admitted-receive-event
                        admission config wire observation)))
           (if (and (fn-bpnf-receive-wire-readyp answer)
                    (< (fn-bpnpf-adu-octets profile)
                       (fn-bpnpf-bundle-adu-length
                        (fn-bpnpf-ready-bundle answer))))
               (list :refused :adu-beyond-profile)
             answer)))))

(defthm fn-bpnpf-profile-fields-are-naturals
  (implies (fn-bpnpf-profilep p)
           (and (natp (caddr p)) (natp (cadddr p))
                (natp (fn-bpn-nth 2 p)) (natp (fn-bpn-nth 3 p))
                (natp (fn-bpnpf-adu-octets p))
                (natp (fn-bpnpf-bundle-octets p))))
  :rule-classes :forward-chaining)

(defthm fn-bpnpf-bundle-adu-length-is-natural
  (natp (fn-bpnpf-bundle-adu-length bundle))
  :rule-classes :type-prescription)

(verify-guards fn-bpnpf-admitted-receive-event
  :hints (("Goal" :in-theory (disable fn-bpnpf-profilep
                                      fn-bpnpf-bundle-adu-length
                                      fn-bpnpf-adu-octets
                                      fn-bpnpf-bundle-octets
                                      fn-bpaj-admitted-receive-event))))

; -----------------------------------------------------------------------------
; Theorems.

(local
 (defthm fn-bpnpf-at-mostp-is-length
   (implies (and (natp bound) (fn-cbor-at-mostp xs bound))
            (<= (len xs) bound))
   :hints (("Goal" :induct (fn-cbor-at-mostp xs bound)
            :in-theory (enable fn-cbor-at-mostp)))))

; The codec widths are the profile's ceiling: every field a profile names is
; within the width of the codec that carries it.
(defthm fn-bpnpf-profile-within-codec-widths
  (implies (fn-bpnpf-profilep p)
           (and (<= (fn-bpnpf-adu-octets p) *fn-bpa-max-octets*)
                (<= (fn-bpnpf-adu-octets p) *fn-bpb-max-data*)
                (<= (fn-bpnpf-bundle-octets p) *fn-bpb-max-input*)
                (<= (cadr p) *fn-bpnf-max-held-image*)
                (<= (+ (cadr p) 3072) *fn-bpn-lifecycle-max-payload*)))
  :rule-classes nil)

; Refinement to PRF-128's subject: within the profile, the answer is the
; channel admission's answer.
(defthm fn-bpnpf-admission-within-profile-is-the-channel-answer
  (let ((answer (fn-bpaj-admitted-receive-event
                 admission config wire observation)))
    (implies (and (fn-bpnpf-profilep profile)
                  (fn-cbor-at-mostp wire (fn-bpnpf-bundle-octets profile))
                  (implies (fn-bpnf-receive-wire-readyp answer)
                           (<= (fn-bpnpf-bundle-adu-length
                                (fn-bpnpf-ready-bundle answer))
                               (fn-bpnpf-adu-octets profile))))
             (equal (fn-bpnpf-admitted-receive-event
                     profile admission config wire observation)
                    answer)))
  :hints (("Goal" :in-theory (disable fn-bpaj-admitted-receive-event
                                      fn-bpnpf-profilep fn-cbor-at-mostp
                                      fn-bpnpf-bundle-adu-length
                                      fn-bpnpf-ready-bundle
                                      fn-bpnf-receive-wire-readyp))))

(local
 (defthm fn-bpnpf-refused-channel-is-not-ready
   (implies (equal (fn-cbor-ag-car admission) :refused)
            (not (fn-bpnf-receive-wire-readyp
                  (fn-bpaj-admitted-receive-event
                   admission config wire observation))))))

; Keystone: a received bundle the machine takes custody of is within the
; profile -- its wire within the bundle octets and its ADU within the ADU
; octets -- and is the channel admission's :ready event.
(defthm fn-bpnpf-admission-ready-is-within-profile
  (let ((r (fn-bpnpf-admitted-receive-event
            profile admission config wire observation)))
    (implies (fn-bpnf-receive-wire-readyp r)
             (and (fn-bpnpf-profilep profile)
                  (<= (len wire) (fn-bpnpf-bundle-octets profile))
                  (<= (fn-bpnpf-bundle-adu-length (fn-bpnpf-ready-bundle r))
                      (fn-bpnpf-adu-octets profile))
                  (equal r (fn-bpaj-admitted-receive-event
                            admission config wire observation)))))
  :hints (("Goal" :in-theory (disable fn-bpaj-admitted-receive-event
                                      fn-bpnpf-bundle-adu-length
                                      fn-bpnpf-ready-bundle fn-cbor-at-mostp
                                      fn-bpnf-receive-wire-readyp
                                      fn-bpnpf-profilep)
           :use ((:instance fn-bpnpf-at-mostp-is-length
                  (xs wire) (bound (fn-bpnpf-bundle-octets profile)))))))

; Keystone: beyond the profile, refused by name and never custody.
(defthm fn-bpnpf-admission-refuses-beyond-the-profile
  (let ((answer (fn-bpaj-admitted-receive-event
                 admission config wire observation)))
    (implies (and (fn-bpnpf-profilep profile)
                  (not (equal (fn-cbor-ag-car admission) :refused)))
             (and (implies (not (fn-cbor-at-mostp
                                 wire (fn-bpnpf-bundle-octets profile)))
                           (equal (fn-bpnpf-admitted-receive-event
                                   profile admission config wire observation)
                                  (list :refused :bundle-beyond-profile)))
                  (implies (and (fn-cbor-at-mostp
                                 wire (fn-bpnpf-bundle-octets profile))
                                (fn-bpnf-receive-wire-readyp answer)
                                (< (fn-bpnpf-adu-octets profile)
                                   (fn-bpnpf-bundle-adu-length
                                    (fn-bpnpf-ready-bundle answer))))
                           (equal (fn-bpnpf-admitted-receive-event
                                   profile admission config wire observation)
                                  (list :refused :adu-beyond-profile))))))
  :hints (("Goal" :in-theory (disable fn-bpaj-admitted-receive-event
                                      fn-bpnpf-profilep fn-cbor-at-mostp
                                      fn-bpnpf-bundle-adu-length
                                      fn-bpnpf-ready-bundle
                                      fn-bpnf-receive-wire-readyp))))
