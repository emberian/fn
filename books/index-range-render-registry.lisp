(in-package "ACL2")
(include-book "index-range-render-trajectory")
(include-book "index-backing-provider")
; Ghost/caller domain only. Actual body performs a single registry descent.
(defun fn-ibr-control-render-domain-p (control fn-render-holder fn-arena)
 (declare (xargs :stobjs (fn-render-holder fn-arena) :guard t))
 (and (equal (fn-rh-plan fn-render-holder) (fn-spp-at 4 control))
  (case (fn-spp-at 3 control)
   (:group (fn-gns-group-cursorp (fn-spp-at 6 control)))
   (:number (and (fn-gns-number-cursorp (fn-spp-at 7 control))
                  (true-listp (fn-spp-at 1 (fn-spp-at 8 control)))))
   (:held (fn-ibr-held-current-ready-p control fn-arena))
   (otherwise t))))
(defun fn-ibr-node-render-ready-p (token address depth fn-render-holder fn-ibp-node fn-arena)
 (declare (xargs :stobjs (fn-render-holder fn-ibp-node fn-arena)
  :guard (and (fn-ibp-query-tokenp token) (natp address) (natp depth))))
 (mv-let (status control capture borrow left)
  (fn-ibp-node-query-read token (+ 1 depth) address depth fn-ibp-node)
  (declare (ignore capture borrow left))
  (implies (eq status :live)
           (fn-ibr-control-render-domain-p control fn-render-holder fn-arena))))
(defun fn-ibr-node-render-one
 (token fuel capacity address depth fn-render-holder fn-ibp-node fn-arena fn-octets)
 (declare (xargs :stobjs (fn-render-holder fn-ibp-node fn-arena fn-octets)
  :measure (nfix depth) :verify-guards nil
  :guard (and (fn-ibp-query-tokenp token) (natp fuel) (natp capacity)
               (natp address) (natp depth) (equal token (fn-rh-query fn-render-holder))
               (fn-ibr-node-render-ready-p token address depth fn-render-holder fn-ibp-node fn-arena))))
 (cond
  ((<= fuel depth) (mv :yield fuel fn-render-holder fn-ibp-node fn-octets))
  ((zp depth)
   (if (not (and (zp address)
     (fn-ibp-node-children-boundp 'fn-ibp-query-segment fn-ibp-node)
     (fn-ibp-node-children-boundp 'fn-query-payload-grants fn-ibp-node)))
    (mv :unavailable fuel fn-render-holder fn-ibp-node fn-octets)
    (stobj-let ((fn-ibp-query-segment
                 (fn-ibp-node-children-get 'fn-ibp-query-segment fn-ibp-node
                                           (create-fn-ibp-query-segment)))
                (fn-query-payload-grants
                 (fn-ibp-node-children-get 'fn-query-payload-grants fn-ibp-node
                                           (create-fn-query-payload-grants))))
     (word fn-render-holder fn-ibp-query-segment fn-octets)
     (fn-ibr-joint-segment-render-one capacity fn-render-holder fn-ibp-query-segment
                                     fn-query-payload-grants fn-arena fn-octets)
     (mv word (- fuel 1) fn-render-holder fn-ibp-node fn-octets))))
  ((equal (mod address 2) 0)
   (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-left fn-ibp-node))
    (mv :unavailable fuel fn-render-holder fn-ibp-node fn-octets)
    (stobj-let ((fn-ibp-node-left
                 (fn-ibp-node-children-get 'fn-ibp-node-left fn-ibp-node
                                           (create-fn-ibp-node-left))))
     (word left fn-render-holder fn-ibp-node-left fn-octets)
     (fn-ibr-node-render-one token (- fuel 1) capacity (floor address 2) (- depth 1)
                            fn-render-holder fn-ibp-node-left fn-arena fn-octets)
     (mv word left fn-render-holder fn-ibp-node fn-octets))))
  (t
   (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-right fn-ibp-node))
    (mv :unavailable fuel fn-render-holder fn-ibp-node fn-octets)
    (stobj-let ((fn-ibp-node-right
                 (fn-ibp-node-children-get 'fn-ibp-node-right fn-ibp-node
                                           (create-fn-ibp-node-right))))
     (word left fn-render-holder fn-ibp-node-right fn-octets)
     (fn-ibr-node-render-one token (- fuel 1) capacity (floor address 2) (- depth 1)
                            fn-render-holder fn-ibp-node-right fn-arena fn-octets)
     (mv word left fn-render-holder fn-ibp-node fn-octets))))))
(verify-guards fn-ibr-node-render-one
 :hints (("Goal"
  :expand ((:free (token fuel address depth)
             (fn-ibp-node-query-read token fuel address depth fn-ibp-node)))
  :in-theory
  (e/d (fn-ibr-node-render-ready-p fn-ibr-control-render-domain-p
         fn-ibr-dispatch-domain-p)
       (fn-ibp-node-query-read fn-ibr-joint-segment-render-one
        fn-ibr-held-current-ready-p fn-gns-group-cursorp fn-gns-number-cursorp)))))
; This INTERNAL entry accepts capacity only from a future genuine output
; factory receipt. It is not a native supplied allowance or installed callback.
(defun fn-ibr-render-registry-ready-p (fn-render-holder fn-mio$c fn-arena)
 (declare (xargs :stobjs (fn-render-holder fn-mio$c fn-arena) :guard t))
 (if (not (fn-rh-live fn-render-holder)) t
  (let ((token (fn-rh-query fn-render-holder)))
   (and (fn-ibp-query-tokenp token)
    (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
     (ready)
     (stobj-let ((fn-ibp-node (fn-ibp-registry fn-index-backing)))
      (ready)
      (fn-ibr-node-render-ready-p token (- (nth 2 token) 1)
        (fn-ibp-slot-depth fn-index-backing) fn-render-holder fn-ibp-node fn-arena)
      ready)
     ready)))))
(defun fn-ibr-render-registry-one
 (fuel capacity fn-render-holder fn-mio$c fn-arena fn-octets)
 (declare (xargs :stobjs (fn-render-holder fn-mio$c fn-arena fn-octets)
  :guard (and (natp fuel) (natp capacity)
              (fn-ibr-render-registry-ready-p fn-render-holder fn-mio$c fn-arena))
  :verify-guards nil))
 (let ((token (fn-rh-query fn-render-holder)))
  (if (not (and (fn-rh-live fn-render-holder) (fn-ibp-query-tokenp token)))
   (mv :unavailable fuel fn-render-holder fn-mio$c fn-octets)
   (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
    (word left fn-render-holder fn-index-backing fn-octets)
    (let ((depth (fn-ibp-slot-depth fn-index-backing)))
     (stobj-let ((fn-ibp-node (fn-ibp-registry fn-index-backing)))
      (word left fn-render-holder fn-ibp-node fn-octets)
      (fn-ibr-node-render-one token fuel capacity (- (nth 2 token) 1)
        depth fn-render-holder fn-ibp-node fn-arena fn-octets)
      (mv word left fn-render-holder fn-index-backing fn-octets)))
    (mv word left fn-render-holder fn-mio$c fn-octets)))))
(verify-guards fn-ibr-render-registry-one
 :hints (("Goal" :in-theory
  (e/d (fn-ibr-render-registry-ready-p fn-ibp-query-tokenp)
       (fn-ibr-node-render-ready-p fn-ibr-node-render-one)))))

(local
 (defthm fn-ibr-child-owner-frame-by-definition
  (let ((rh (mv-nth 1 (fn-ibr-joint-segment-render-one capacity fn-render-holder
           fn-ibp-query-segment fn-query-payload-grants fn-arena fn-octets))))
   (and (equal (fn-rh-live rh) (fn-rh-live fn-render-holder))
        (equal (fn-rh-pin rh) (fn-rh-pin fn-render-holder))
        (equal (fn-rh-query rh) (fn-rh-query fn-render-holder))
        (equal (fn-rh-resource rh) (fn-rh-resource fn-render-holder))
        (equal (fn-rh-origin rh) (fn-rh-origin fn-render-holder))))
  :hints (("Goal" :use fn-ibr-render-one-retains-custody-and-owner-identities
                   :in-theory nil))))
(defthm fn-ibr-node-render-one-retains-owner-identities
 (let ((rh (mv-nth 2 (fn-ibr-node-render-one token fuel capacity address depth
                      fn-render-holder fn-ibp-node fn-arena fn-octets))))
  (and (equal (fn-rh-live rh) (fn-rh-live fn-render-holder))
       (equal (fn-rh-pin rh) (fn-rh-pin fn-render-holder))
       (equal (fn-rh-query rh) (fn-rh-query fn-render-holder))
       (equal (fn-rh-resource rh) (fn-rh-resource fn-render-holder))
       (equal (fn-rh-origin rh) (fn-rh-origin fn-render-holder))))
 :rule-classes nil
 :hints (("Goal"
  :induct (fn-ibr-node-render-one token fuel capacity address depth
             fn-render-holder fn-ibp-node fn-arena fn-octets)
  :in-theory (e/d (fn-ibr-node-render-one)
                  (fn-ibr-joint-segment-render-one fn-rh-live fn-rh-pin
                   fn-rh-query fn-rh-resource fn-rh-origin)))))
