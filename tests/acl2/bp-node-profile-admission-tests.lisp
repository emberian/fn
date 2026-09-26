; Teeth of books/bp-node-profile-admission.lisp (PRF-134): the node's profile
; at the receive boundary.  Over PRF-128's reachable admitted answer (the
; foundation bundle on an admitted channel, bp-channel-ingress-tests): a
; witness per keystone that asserts every hypothesis and the conclusion; per
; hypothesis a witness that checks the retained hypotheses, the failure of
; the omitted one and of the conclusion, then a must-fail of the weakened
; theorem (its search cut short on purpose: the counterexample is the
; assert-event before it).
(in-package "ACL2")
(include-book "../../books/bp-node-profile-admission")
(include-book "../../books/bp-fragment")
(include-book "bp-channel-ingress-tests")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bpnpat-adu* (fn-bpnpf-bundle-adu-length *bpnf-bundle*))
(defconst *bpnpat-wire-octets* (len *bpnf-wire*))
(defun bpnpat-profile (adu bundle) (list 64 16777216 adu bundle))
(defun bpnpat-answer (profile admission wire)
  (fn-bpnpf-admitted-receive-event profile admission *bpnf-config* wire
                                   *bpnf-obs*))

;; The bundle's ADU is its four payload octets (not a fragment).
(assert-event (equal *bpnpat-adu* 4))
(assert-event (< 60 *bpnpat-wire-octets*))

;; ---------------------------------------------------------------------------
;; fn-bpnpf-admission-within-profile-is-the-channel-answer.  Witness: the
;; profile at exactly the bundle's wire and ADU.
(defconst *bpnpat-exact* (bpnpat-profile *bpnpat-adu* *bpnpat-wire-octets*))
(assert-event
 (and (fn-bpnpf-profilep *bpnpat-exact*)
      (fn-cbor-at-mostp *bpnf-wire* (fn-bpnpf-bundle-octets *bpnpat-exact*))
      (fn-bpnf-receive-wire-readyp *bpcin-admitted-answer*)
      (<= (fn-bpnpf-bundle-adu-length (fn-bpnpf-ready-bundle *bpcin-admitted-answer*))
          (fn-bpnpf-adu-octets *bpnpat-exact*))
      (equal (bpnpat-answer *bpnpat-exact* *bpcin-result* *bpnf-wire*)
             *bpcin-admitted-answer*)))
;; Without a profile (no bundle field): not the channel answer.
(assert-event
 (let ((p '(64 16777216 4)))
   (and (not (fn-bpnpf-profilep p))
        (not (equal (bpnpat-answer p *bpcin-result* *bpnf-wire*)
                    *bpcin-admitted-answer*)))))
(must-fail
 (defthm bpnpat-within-without-profile
   (implies (and (fn-cbor-at-mostp wire (fn-bpnpf-bundle-octets profile))
                 (implies (fn-bpnf-receive-wire-readyp
                           (fn-bpaj-admitted-receive-event admission config wire observation))
                          (<= (fn-bpnpf-bundle-adu-length
                               (fn-bpnpf-ready-bundle
                                (fn-bpaj-admitted-receive-event admission config wire observation)))
                              (fn-bpnpf-adu-octets profile))))
            (equal (fn-bpnpf-admitted-receive-event profile admission config wire observation)
                   (fn-bpaj-admitted-receive-event admission config wire observation)))
   :hints (("Goal" :do-not-induct t :in-theory (theory 'minimal-theory)))))
;; Without the wire within the bundle octets (one octet short).
(defconst *bpnpat-short-bundle*
  (bpnpat-profile *bpnpat-adu* (1- *bpnpat-wire-octets*)))
(assert-event
 (and (fn-bpnpf-profilep *bpnpat-short-bundle*)
      (not (fn-cbor-at-mostp *bpnf-wire* (fn-bpnpf-bundle-octets *bpnpat-short-bundle*)))
      (equal (bpnpat-answer *bpnpat-short-bundle* *bpcin-result* *bpnf-wire*)
             '(:refused :bundle-beyond-profile))
      (not (equal (bpnpat-answer *bpnpat-short-bundle* *bpcin-result* *bpnf-wire*)
                  *bpcin-admitted-answer*))))
(must-fail
 (defthm bpnpat-within-without-bundle-bound
   (implies (and (fn-bpnpf-profilep profile)
                 (implies (fn-bpnf-receive-wire-readyp
                           (fn-bpaj-admitted-receive-event admission config wire observation))
                          (<= (fn-bpnpf-bundle-adu-length
                               (fn-bpnpf-ready-bundle
                                (fn-bpaj-admitted-receive-event admission config wire observation)))
                              (fn-bpnpf-adu-octets profile))))
            (equal (fn-bpnpf-admitted-receive-event profile admission config wire observation)
                   (fn-bpaj-admitted-receive-event admission config wire observation)))
   :hints (("Goal" :do-not-induct t :in-theory (theory 'minimal-theory)))))
;; Without the ADU within the ADU octets (one octet short).
(defconst *bpnpat-short-adu*
  (bpnpat-profile (1- *bpnpat-adu*) *bpnpat-wire-octets*))
(assert-event
 (and (fn-bpnpf-profilep *bpnpat-short-adu*)
      (fn-cbor-at-mostp *bpnf-wire* (fn-bpnpf-bundle-octets *bpnpat-short-adu*))
      (fn-bpnf-receive-wire-readyp *bpcin-admitted-answer*)
      (not (<= (fn-bpnpf-bundle-adu-length (fn-bpnpf-ready-bundle *bpcin-admitted-answer*))
               (fn-bpnpf-adu-octets *bpnpat-short-adu*)))
      (equal (bpnpat-answer *bpnpat-short-adu* *bpcin-result* *bpnf-wire*)
             '(:refused :adu-beyond-profile))))
(must-fail
 (defthm bpnpat-within-without-adu-bound
   (implies (and (fn-bpnpf-profilep profile)
                 (fn-cbor-at-mostp wire (fn-bpnpf-bundle-octets profile)))
            (equal (fn-bpnpf-admitted-receive-event profile admission config wire observation)
                   (fn-bpaj-admitted-receive-event admission config wire observation)))
   :hints (("Goal" :do-not-induct t :in-theory (theory 'minimal-theory)))))

;; ---------------------------------------------------------------------------
;; fn-bpnpf-admission-ready-is-within-profile.  Witness: the exact profile's
;; :ready answer is within it.
(assert-event
 (let ((r (bpnpat-answer *bpnpat-exact* *bpcin-result* *bpnf-wire*)))
   (and (fn-bpnf-receive-wire-readyp r)
        (fn-bpnpf-profilep *bpnpat-exact*)
        (<= (len *bpnf-wire*) (fn-bpnpf-bundle-octets *bpnpat-exact*))
        (<= (fn-bpnpf-bundle-adu-length (fn-bpnpf-ready-bundle r))
            (fn-bpnpf-adu-octets *bpnpat-exact*))
        (equal r *bpcin-admitted-answer*))))
;; Without :ready (an invalid profile's refusal): the conclusion fails.
(assert-event
 (let ((r (bpnpat-answer '(0 0 0 0) *bpcin-result* *bpnf-wire*)))
   (and (equal r '(:refused :profile))
        (not (fn-bpnf-receive-wire-readyp r))
        (not (fn-bpnpf-profilep '(0 0 0 0))))))
(must-fail
 (defthm bpnpat-ready-without-ready
   (fn-bpnpf-profilep profile)
   :hints (("Goal" :do-not-induct t :in-theory (theory 'minimal-theory)))))

;; ---------------------------------------------------------------------------
;; fn-bpnpf-admission-refuses-beyond-the-profile.  Witnesses: the two short
;; profiles above, on an admitted channel.
(assert-event (not (equal (fn-cbor-ag-car *bpcin-result*) :refused)))
;; Without an admitted channel: a refused channel keeps its own reason, not
;; the profile's, even past both bounds.
(assert-event
 (let ((short (bpnpat-profile 1 1)))
   (and (fn-bpnpf-profilep short)
        (equal (fn-cbor-ag-car *bpcin-ambiguous*) :refused)
        (not (fn-cbor-at-mostp *bpnf-wire* (fn-bpnpf-bundle-octets short)))
        (equal (bpnpat-answer short *bpcin-ambiguous* *bpnf-wire*)
               '(:refused :ambiguous-peer)))))
(must-fail
 (defthm bpnpat-refuses-without-admitted-channel
   (implies (and (fn-bpnpf-profilep profile)
                 (not (fn-cbor-at-mostp wire (fn-bpnpf-bundle-octets profile))))
            (equal (fn-bpnpf-admitted-receive-event profile admission config wire observation)
                   (list :refused :bundle-beyond-profile)))
   :hints (("Goal" :do-not-induct t :in-theory (theory 'minimal-theory)))))
;; Without a profile: the verdict is :profile, not the bound's.
(assert-event
 (equal (bpnpat-answer '(64 16777216 1 1) *bpcin-result* *bpnf-wire*)
        '(:refused :bundle-beyond-profile)))
(assert-event
 (equal (bpnpat-answer '(64 16777216 1) *bpcin-result* *bpnf-wire*)
        '(:refused :profile)))
(must-fail
 (defthm bpnpat-refuses-without-profile
   (implies (and (not (equal (fn-cbor-ag-car admission) :refused))
                 (not (fn-cbor-at-mostp wire (fn-bpnpf-bundle-octets profile))))
            (equal (fn-bpnpf-admitted-receive-event profile admission config wire observation)
                   (list :refused :bundle-beyond-profile)))
   :hints (("Goal" :do-not-induct t :in-theory (theory 'minimal-theory)))))

;; ---------------------------------------------------------------------------
;; A fragment's ADU is its total ADU length, not its payload: a fragment of a
;; 70,000-octet ADU carrying four octets is refused under the default ADU.
(defconst *bpnpat-fragment*
  (fn-bpb-make-bundle
   (fn-bpf-fragment-block (fn-bpb-bundle-primary *bpnf-bundle*) 0 70000)
   (fn-bpb-bundle-blocks *bpnf-bundle*)
   (fn-bpb-bundle-payload *bpnf-bundle*)))
(assert-event (fn-bpb-bundlep *bpnpat-fragment*))
(assert-event (equal (fn-bpnpf-bundle-adu-length *bpnpat-fragment*) 70000))
(assert-event (< *fn-bpnpf-default-adu* 70000))

;; ---------------------------------------------------------------------------
;; fn-bpnpf-profile-within-codec-widths.  Witness: the largest profile.
(assert-event
 (let ((p '(16777216 16777216 16777216 16777216)))
   (and (fn-bpnpf-profilep p)
        (<= (fn-bpnpf-adu-octets p) *fn-bpa-max-octets*)
        (<= (fn-bpnpf-bundle-octets p) *fn-bpb-max-input*)
        (<= (cadr p) *fn-bpnf-max-held-image*))))
;; Without a profile: a field past 2^24 is past a width.
(assert-event
 (let ((p '(64 16777216 16777217 1048576)))
   (and (not (fn-bpnpf-profilep p))
        (not (<= (fn-bpnpf-adu-octets p) *fn-bpa-max-octets*)))))
