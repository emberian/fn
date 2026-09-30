(in-package "ACL2")
(include-book "../../books/assumptions-selected-runtime-native-constructors")
(assert-event
 (and (equal (fn-srnc-connection-owned-census 1 1 0 1) 1280)
      (equal (fn-srnc-connection-owned-census 1 0 1 1) 1280)
      (equal (fn-srnc-connection-owned-census 1 0 0 1) 1232)
      (equal (fn-srnc-unit-status :node (car (fn-srnc-unit-row :node))
                                 *fn-srnc-runtime*) :native-owned-row)
      (equal (fn-srnc-unit-status :node "foreign-source" *fn-srnc-runtime*) :unavailable)
      (equal (fn-srnc-unit-status :node (car (fn-srnc-unit-row :node))
                                 '("SBCL" "2.6.8" "ARM64" "Darwin")) :unavailable)
      (equal (fn-srnc-unit-status :unknown "" *fn-srnc-runtime*) :unavailable)))
; Physical assumption calls are deliberately non-executable. The matching
; positive physical antecedent/request and ARM64 hypothesis removal are in
; the exact fresh SBCL constructor fixture, not a local zero witness.
(assert-event
 (let ((s (car (fn-srnc-unit-row :service-owned)))
       (n (car (fn-srnc-unit-row :node)))
       (m (car (fn-srnc-unit-row :mux)))
       (f (car (fn-srnc-unit-row :fixed-fault))))
  (and (equal (mv-list 2 (fn-srnc-connection-owned-request
                          1 1 0 1 s n m f *fn-srnc-runtime*)) '(:native-owned-row 1280))
       (equal (mv-list 2 (fn-srnc-connection-owned-request
                          1 1 0 1 "foreign-service" n m f *fn-srnc-runtime*)) '(:unavailable nil))
       (equal (mv-list 2 (fn-srnc-connection-owned-request
                          1 -1 0 1 s n m f *fn-srnc-runtime*)) '(:unavailable nil)))))

(assert-event
 (and (equal (fn-srnc-installation-owned-census 1 1) 912)
      (equal (fn-srnc-installation-owned-census 1 0) 848)
      (equal (fn-srnc-unit-status :collector-installation
               (car (fn-srnc-unit-row :collector-installation)) *fn-srnc-runtime*)
             :native-owned-row)))
