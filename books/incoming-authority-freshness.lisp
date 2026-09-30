; PRF-1167. Bounded authority half of retained incoming freshness.
; The owner collector supplies actual projections; no host authority tuple.
(in-package "ACL2")
(include-book "consumer-account-availability")

; Exact fixed width comparison, including octet validity. Even malformed tails
; are inspected at most N cells; no whole namespace/digest equality is used.
(defun fn-iaf-octets= (n x y)
 (declare (xargs :guard (natp n) :measure (nfix n)))
 (if (zp n) (and (null x) (null y))
  (and (consp x) (consp y)
       (natp (car x)) (< (car x) 256)
       (natp (car y)) (< (car y) 256)
       (equal (car x) (car y))
       (fn-iaf-octets= (1- n) (cdr x) (cdr y)))))

(defthm fn-iaf-fixed-octets-match-is-exact
 (implies (fn-iaf-octets= n x y) (equal x y))
 :rule-classes nil)

(defun fn-iaf-holder= (x y)
 (declare (xargs :guard t))
 (and (consp x) (consp (cdr x)) (null (cddr x))
      (consp y) (consp (cdr y)) (null (cddr y))
      (eq (car x) :incoming) (eq (car y) :incoming)
      (natp (cadr x)) (natp (cadr y)) (equal (cadr x) (cadr y))))

; Refers to the actual canonical CP7 and the sole available root publication.
; The full canonical/publication source correspondence is carried by the owner
; producer, never tested by traversing the Store, config or account graph.
(defun fn-iaf-authority-status (epoch generation count canonical publication)
 (declare (xargs :guard t))
 (let* ((cp (fn-cp-nth 5 canonical)) (authority (fn-cp-nth 6 cp))
        (namespace (fn-cp-nth 3 authority)))
  (if (and (natp epoch) (natp generation) (natp count)
           (eq (fn-cp-nth 0 canonical) :ready)
           (equal epoch (fn-cp-nth 1 canonical))
           (equal count (fn-cp-nth 2 canonical))
           (natp (fn-cp-nth 1 authority))
           (fn-iaf-octets= 40 namespace (fn-cp-nth 2 publication))
           (fn-cra-availablep cp epoch count publication))
      :authority-available :authority-unavailable)))

; Freshness12 = tag phase holderToken epoch intentDigest32 configGeneration
; namespace40 authorityRevision fenceEventCount root4 originalContext queryToken.
; Root and originalContext are borrowed immutable aliases, never compared.
(defun fn-iaf-compare-current (saved holder epoch intent generation canonical publication)
 (declare (xargs :guard t))
 (if (and (eq (fn-cp-nth 0 saved) :incoming-freshness)
          (member-eq (fn-cp-nth 1 saved) '(:awaiting-query :query-attached))
          (fn-iaf-holder= holder (fn-cp-nth 2 saved))
          (equal epoch (fn-cp-nth 3 saved))
          (fn-iaf-octets= 32 intent (fn-cp-nth 4 saved))
          (equal generation (fn-cp-nth 5 saved))
          (fn-iaf-octets= 40 (fn-cp-nth 3 (fn-cp-nth 6 (fn-cp-nth 5 canonical)))
                            (fn-cp-nth 6 saved))
          (equal (fn-cp-nth 1 (fn-cp-nth 6 (fn-cp-nth 5 canonical)))
                 (fn-cp-nth 7 saved))
          (equal (fn-cp-nth 4 publication) (fn-cp-nth 8 saved)))
     :authority-current :recapture-required))

(defthm fn-iaf-current-refuses-changed-configuration
 (implies (not (equal generation (fn-cp-nth 5 saved)))
  (equal (fn-iaf-compare-current saved holder epoch intent generation canonical publication)
         :recapture-required))
 :hints (("Goal" :in-theory (disable fn-iaf-octets= fn-cp-nth))))

(defthm fn-iaf-current-refuses-changed-authority
 (implies (not (equal (fn-cp-nth 1 (fn-cp-nth 6 (fn-cp-nth 5 canonical)))
                       (fn-cp-nth 7 saved)))
  (equal (fn-iaf-compare-current saved holder epoch intent generation canonical publication)
         :recapture-required))
 :hints (("Goal" :in-theory (disable fn-iaf-octets= fn-cp-nth))))

; The literal availability gate is the already guarded account consumer, not
; a second interpretation of the sidecar's revision/root slots.
(defthm fn-iaf-available-uses-canonical-current-publication
 (implies (equal (fn-iaf-authority-status epoch generation count canonical publication)
                 :authority-available)
  (and (equal epoch (fn-cp-nth 1 canonical))
       (equal count (fn-cp-nth 2 canonical))
       (fn-cra-availablep (fn-cp-nth 5 canonical) epoch count publication)))
 :rule-classes nil
 :hints (("Goal" :in-theory (disable fn-cra-availablep fn-iaf-octets= fn-cp-nth))))

(in-theory (disable fn-iaf-authority-status fn-iaf-compare-current fn-iaf-octets=))
