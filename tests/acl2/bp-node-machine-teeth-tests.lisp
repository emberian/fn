; A1 progress teeth start from the event admitted by the native BP boundary.
; These are reachable kind-5 receive/publication traces, not hand-built held
; rows.  Pending checks below become executable when the progress event lands.
(in-package "ACL2")
(include-book "../../books/bp-report-author")
(include-book "../../books/bp-node-receive-boundary")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bpnmt-local* (cons :dtn '(47 47 98 112 45 108 111 99 97 108 47)))
(defconst *bpnmt-sender* (cons :dtn '(47 47 98 112 45 115 101 110 100 101 114 47)))
(defconst *bpnmt-unrouted* (cons :dtn '(47 47 98 112 45 111 116 104 101 114 47)))
(defconst *bpnmt-local-config*
  (fn-bpn-config *bpnmt-local* 3600000 2 32 1048576))
(defconst *bpnmt-sender-config*
  (fn-bpn-config *bpnmt-sender* 3600000 2 32 1048576))
(defconst *bpnmt-observation* (fn-clock-observation 1000 0 0 nil))
(defconst *bpnmt-ingress*
  (list :cl (cons 0 1) 1 *bpnmt-sender* '(115 101 110 100 101 114) 0))
(defconst *bpnmt-request*
  (fn-bpa-encode
   (fn-bpa-make-request "w" "s" "dtn://bp-sender/" "dtn://bp-local/"
                        "p" "i" "c" "t" '(88 13 10))))
(defconst *bpnmt-n03-old*
  (fn-bpn-send-bundle *bpnmt-sender-config* *bpnmt-unrouted*
                      '(1 2 3 4) 7 *bpnmt-observation*))
(defconst *bpnmt-n03-new*
  (fn-bpn-send-bundle *bpnmt-sender-config* *bpnmt-local*
                      *bpnmt-request* 8 *bpnmt-observation*))

(defun bpnmt-durable-receive (st bundle ingress observation)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((prepared (fn-bpnf-receive-wire-event
                    *bpnmt-local-config* (fn-bpb-encode bundle)
                    observation ingress))
         (proposal (fn-bpn-report-author-step
                    st (fn-bpnf-receive-wire-event-value prepared)))
         (effect (car (fn-bpnf-answer-effects proposal)))
         (issued (fn-bpnf-answer-state proposal)))
    (if (and (fn-bpnf-receive-wire-readyp prepared)
             (equal (car effect) :persist)
             (equal (fn-bpn-nth 3 (fn-bpnf-issued issued)) :store))
        (fn-bpnf-answer-state
         (fn-bpn-report-author-step
          issued (list :persist-result (fn-bpn-nth 1 effect)
                       (fn-bpn-nth 2 effect) :durable)))
      st)))

(defconst *bpnmt-n03-s0*
  (fn-bpnf-initial-state *bpnmt-local-config* 8 1048576))
(defconst *bpnmt-n03-s1*
  (bpnmt-durable-receive *bpnmt-n03-s0* *bpnmt-n03-old*
                         *bpnmt-ingress* *bpnmt-observation*))
(defconst *bpnmt-n03-s2*
  (bpnmt-durable-receive *bpnmt-n03-s1* *bpnmt-n03-new*
                         *bpnmt-ingress* *bpnmt-observation*))

; N03's entire receive antecedent is asserted before any progress claim:
; the older transit bundle and newer local request are both admitted by the
; production receive boundary and durably held, with no issued operation.
(assert-event
 (and (fn-bpb-bundlep *bpnmt-n03-old*)
      (fn-bpb-bundlep *bpnmt-n03-new*)
      (fn-bpnf-receive-wire-readyp
       (fn-bpnf-receive-wire-event
        *bpnmt-local-config* (fn-bpb-encode *bpnmt-n03-old*)
        *bpnmt-observation* *bpnmt-ingress*))
      (fn-bpnf-receive-wire-readyp
       (fn-bpnf-receive-wire-event
        *bpnmt-local-config* (fn-bpb-encode *bpnmt-n03-new*)
        *bpnmt-observation* *bpnmt-ingress*))
      (fn-bpnf-host-eventp
       (fn-bpnf-receive-wire-event-value
        (fn-bpnf-receive-wire-event
         *bpnmt-local-config* (fn-bpb-encode *bpnmt-n03-old*)
         *bpnmt-observation* *bpnmt-ingress*)))
      (fn-bpnf-host-eventp
       (fn-bpnf-receive-wire-event-value
        (fn-bpnf-receive-wire-event
         *bpnmt-local-config* (fn-bpb-encode *bpnmt-n03-new*)
         *bpnmt-observation* *bpnmt-ingress*)))
      (equal (len (fn-bpnf-held-list *bpnmt-n03-s2*)) 2)
      (equal (fn-bpn-nth 3 (second (fn-bpnf-held-list *bpnmt-n03-s2*))) 0)
      (equal (fn-bpn-nth 3 (first (fn-bpnf-held-list *bpnmt-n03-s2*))) 1)
      (fn-bpnf-heldp (second (fn-bpnf-held-list *bpnmt-n03-s2*)))
      (fn-bpnf-heldp (first (fn-bpnf-held-list *bpnmt-n03-s2*)))
      (equal (fn-bpp-destination
              (fn-bpb-bundle-primary
               (fn-bpnf-held-bundle
                (second (fn-bpnf-held-list *bpnmt-n03-s2*)))))
             *bpnmt-unrouted*)
      (equal (fn-bpp-destination
              (fn-bpb-bundle-primary
               (fn-bpnf-held-bundle
                (first (fn-bpnf-held-list *bpnmt-n03-s2*)))))
             *bpnmt-local*)
      (equal (fn-bpah-held-class
              (first (fn-bpnf-held-list *bpnmt-n03-s2*))) :request)
      (equal (fn-bpah-held-expiry
              (first (fn-bpnf-held-list *bpnmt-n03-s2*))
              *bpnmt-observation*) :live)
      (equal (fn-bpah-held-expiry
              (second (fn-bpnf-held-list *bpnmt-n03-s2*))
              *bpnmt-observation*) :live)
      (not (fn-bpn-machine-state-fenced (fn-bpnf-base *bpnmt-n03-s2*)))
      (not (fn-bpnf-issued *bpnmt-n03-s2*))))

; PENDING N03 positive: under an empty routing observation, a progress event
; first gives the old key a (:route rg) wait; at unchanged generation the
; newer request emits the existing :deliver effect and later settles kind 7.
; PENDING N03 negative: the least-arrival-regardless mutation repeatedly
; selects the unrouted old entry; preserve all other eligibility premises.
; PENDING N04: two *received* valid no-fragment bundles with 48 KiB and 8 KiB
; payloads, both encoded below 131072, are checked against a 32768-byte MRU;
; only the older exceeds it and only the younger is attempted.
; PENDING N05: with F=1, kind 8 refuses without mutation; with F=2, kind 8
; and a failed kind 9 settle; at remaining=D+R+margin, kind 11 still pays debt.
; The N04/N05 pending forms are not counted as tests or theorem teeth.
