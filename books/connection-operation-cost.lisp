; Source-shaped INTERNAL evaluator. The immutable descriptor's producer must
; establish the complete selected-runtime envelope; its shape is not authority.
; Native code supplies neither these coefficients nor a demand vector.
(in-package "ACL2")
(include-book "allocation-epoch-domain")
(include-book "snapshot-source-token")
(include-book "page-read-ledger")

; Installation10: tag, shared-PRS serial, SAMEpool association6, complete
; source-coordinate roster, immediate domain, logical holder grant5,
; allocation-account base, per input octet, per registry level, input quantum.
; Coefficients already include qualified request-count/byte geometry lowering,
; frames, first use and the entire native/callback return/cleanup closure.
; This book has no constructor or setter for an authoritative installation.

(defun fn-cop-octets-match (x y fuel)
 (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
 (if (or (atom x) (atom y)) (and (null x) (null y))
  (and (not (zp fuel))
       (integerp (car x)) (<= 0 (car x)) (< (car x) 256)
       (integerp (car y)) (<= 0 (car y)) (< (car y) 256)
       (eql (car x) (car y))
       (fn-cop-octets-match (cdr x) (cdr y) (1- fuel)))))

(defun fn-cop-octets-left (x fuel)
 (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
 (cond ((null x) (mv :counted fuel))
       ((or (atom x) (zp fuel) (not (integerp (car x)))
            (< (car x) 0) (<= 256 (car x))) (mv :refused fuel))
       (t (fn-cop-octets-left (cdr x) (1- fuel)))))

(defun fn-cop-input-left (kind family address peer fuel)
 (declare (xargs :guard (natp fuel)))
 (if (not (case kind
            (:reader (and (null family) (null address) (null peer)))
            (:peer (and (null family) (null address)))
            (:exposure (or (and (eq family :inet) (fn-omk-widthp address 4))
                           (and (eq family :inet6) (fn-omk-widthp address 16))))
            (otherwise nil)))
     (mv :refused fuel)
   (mv-let (word left) (fn-cop-octets-left address fuel)
    (if (eq word :counted) (fn-cop-octets-left peer (nfix left))
      (mv word left)))))

(defun fn-cop-times-roomp (a b domain)
 (declare (xargs :guard t))
 (and (natp a) (natp b) (natp domain) (<= a domain) (<= b domain)
      (or (zp b) (<= a (floor domain b)))))

(defun fn-cop-vector-room (used charged demand domain fuel)
 (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
 (if (zp fuel) (and (null used) (null charged) (null demand))
  (and (consp used) (consp charged) (consp demand)
       (fn-aed-add-roomp (car used) (car charged) domain)
       (fn-aed-add-roomp (+ (car used) (car charged)) (car demand) domain)
       (fn-cop-vector-room (cdr used) (cdr charged) (cdr demand) domain (1- fuel)))))

(defun fn-cop-issuer-domainp (ledger demand domain)
 (declare (xargs :guard t))
 (let ((budget (fn-prl-nth 0 ledger)) (next (fn-prl-nth 2 ledger)))
  (and (natp domain) (natp next) (< next domain)
       (fn-omk-widthp budget 5) (fn-omk-widthp demand 5)
       (fn-cop-vector-room '(0 0 0 0 0) budget '(0 0 0 0 0) domain 5)
       (equal (fn-prl-nth 4 demand) 1)
       (fn-cop-vector-room (fn-prl-baseline ledger) (fn-prl-nth 1 ledger) demand domain 5))))

; All multiplication is preceded by a divide-domain check; all addition by a
; subtract-domain check. The rejected case does not construct an oversized sum.
(defun fn-cop-body-demand (base per-input input per-level levels domain)
 (declare (xargs :guard t))
 (if (not (and (fn-cop-times-roomp per-input input domain)
               (fn-cop-times-roomp per-level levels domain)))
     (mv :unavailable nil)
   (let ((input-cost (* per-input input)) (level-cost (* per-level levels)))
    (if (not (fn-aed-add-roomp base input-cost domain)) (mv :unavailable nil)
     (let ((prefix (+ base input-cost)))
      (if (fn-aed-add-roomp prefix level-cost domain)
          (mv :derived (+ prefix level-cost))
        (mv :unavailable nil)))))))

(defthm fn-cop-octets-match-is-exact
 (implies (fn-cop-octets-match x y fuel) (equal x y))
 :rule-classes nil)

(defthm fn-cop-octets-left-bounded
 (implies (natp fuel)
  (and (natp (mv-nth 1 (fn-cop-octets-left x fuel)))
       (<= (mv-nth 1 (fn-cop-octets-left x fuel)) fuel))))

(defthm fn-cop-derived-body-fits
 (implies (eq (mv-nth 0 (fn-cop-body-demand base per-input input per-level levels domain)) :derived)
  (let ((body (mv-nth 1 (fn-cop-body-demand base per-input input per-level levels domain))))
   (and (natp body) (<= body domain)
        (equal body (+ base (* per-input input) (* per-level levels))))))
 :hints (("Goal" :in-theory (disable fn-cop-times-roomp)))
 :rule-classes nil)

(defun fn-cop-evaluate (installation kind family address peer depth)
 (declare (xargs :guard t))
 (let ((domain (fn-omk-at 4 installation))
       (quantum (fn-omk-at 9 installation)))
  (if (not (and (fn-omk-widthp installation 10)
                (eq (fn-omk-at 0 installation) :connection-operation-installation)
                (natp (fn-omk-at 1 installation))
                (natp domain) (natp quantum) (<= quantum domain)
                (natp depth) (< depth domain)))
      (mv :unsupported-runtime nil 0 0 0)
    (mv-let (word left) (fn-cop-input-left kind family address peer quantum)
     (if (not (eq word :counted)) (mv :refused nil 0 0 quantum)
      (let ((levels (+ 1 depth)))
       (if (not (fn-cop-times-roomp 8 levels domain))
           (mv :unsupported-runtime nil 0 0 quantum)
        (mv-let (derived body)
         (fn-cop-body-demand (fn-omk-at 6 installation)
                            (fn-omk-at 7 installation) (- quantum (nfix left))
                            (fn-omk-at 8 installation) levels domain)
         (if (eq derived :derived)
             (mv :derived (fn-omk-at 5 installation) (* 8 levels) body quantum)
           (mv :unsupported-runtime nil 0 0 quantum))))))))))
