; The received dispatch frame and the clock-domain marker both use FNBS kind
; 6, but their version and canonical names distinguish their authority.
(in-package "ACL2")
(include-book "../../books/bp-fnbs-dispatch-codec")
(include-book "../../books/bp-fnbs-dispatch-invariants")
(include-book "../../books/bp-clock-domain")
(include-book "std/testing/must-fail" :dir :system)

(defconst *fn-test-bpnp-dispatch*
  (fn-bpnp-dispatch-record
   1 2 3 '(1 2 3)
   (cons :dtn '(47 47 114 101 108 97 121 47))))
(defconst *fn-test-bpnp-boot-id*
  (fn-record-string-octets "01234567-89ab-cdef-0123-456789abcdef"))

(assert-event (fn-bpnp-dispatch-recordp *fn-test-bpnp-dispatch*))
(assert-event
 (equal (fn-bpnp-dispatch-unframe
         (fn-bpnp-dispatch-frame *fn-test-bpnp-dispatch*))
        *fn-test-bpnp-dispatch*))
(assert-event
 (equal (fn-bpcd-unframe
         (fn-bpnp-dispatch-frame *fn-test-bpnp-dispatch*))
        nil))
(assert-event
 (equal (fn-bpnp-dispatch-unframe
         (fn-bpcd-frame *fn-test-bpnp-boot-id*))
        nil))

(defconst *fn-test-bpnp-max-identity*
  (fn-bpnp-dispatch-record 1 3 4
    (make-list 1024 :initial-element 7) (list :ipn 9 10)))
(assert-event (fn-bpnp-dispatch-recordp *fn-test-bpnp-max-identity*))
(assert-event
 (equal (fn-bpnp-dispatch-unframe
         (fn-bpnp-dispatch-frame *fn-test-bpnp-max-identity*))
        *fn-test-bpnp-max-identity*))
(assert-event
 (equal (fn-bpnp-dispatch-unframe
         (fn-bpnp-dispatch-frame
          (fn-bpnp-dispatch-record 1 4 5 '(9) (list :dtn-none))))
        (fn-bpnp-dispatch-record 1 4 5 '(9) (list :dtn-none))))

(defconst *fn-test-bpnp-overlong-identity*
  (fn-bpnp-dispatch-record 1 3 4
    (make-list 1025 :initial-element 7) (list :ipn 9 10)))
(assert-event (not (fn-bpnp-dispatch-recordp *fn-test-bpnp-overlong-identity*)))
(assert-event
 (equal (fn-bpnp-dispatch-frame *fn-test-bpnp-overlong-identity*) :bad))
(must-fail
 (defthm fn-test-bpnp-round-trip-needs-record
   (equal (fn-bpnp-dispatch-unframe
           (fn-bpnp-dispatch-frame *fn-test-bpnp-overlong-identity*))
          *fn-test-bpnp-overlong-identity*)))
