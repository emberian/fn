; Fixture instrumentation only: seven generated getters, no layout twin.
; The seed has empty number maps/summary groups and no escaped slot owner.
; This is NOT a general native column snapshot/extraction implementation.
(in-package "ACL2")
(include-book "lc-bounded-check-tests")
(include-book "../../books/catalog-columns-guards")

(defun lcm-fixture-read-rowwords (i fuel fn-lbc-rowwords)
 (declare (xargs :stobjs fn-lbc-rowwords :guard t :verify-guards nil :measure (nfix fuel)))
 (if (or (zp (nfix fuel)) (<= (fn-lbc-rowwords-count fn-lbc-rowwords) (nfix i))) nil
  (cons (list (ec-call (fn-lbc-rowwords-get-handle (nfix i) fn-lbc-rowwords)) (ec-call (fn-lbc-rowwords-get-loc0 (nfix i) fn-lbc-rowwords)) (ec-call (fn-lbc-rowwords-get-loc1 (nfix i) fn-lbc-rowwords)) (ec-call (fn-lbc-rowwords-get-head-length (nfix i) fn-lbc-rowwords)) (ec-call (fn-lbc-rowwords-get-stamp (nfix i) fn-lbc-rowwords)) (ec-call (fn-lbc-rowwords-get-prefix-max (nfix i) fn-lbc-rowwords)) (ec-call (fn-lbc-rowwords-get-txid (nfix i) fn-lbc-rowwords)) (ec-call (fn-lbc-rowwords-get-generation (nfix i) fn-lbc-rowwords)) (ec-call (fn-lbc-rowwords-get-charge (nfix i) fn-lbc-rowwords)) (ec-call (fn-lbc-rowwords-get-msgid-hash (nfix i) fn-lbc-rowwords)) (ec-call (fn-lbc-rowwords-get-msgid-offset (nfix i) fn-lbc-rowwords)) (ec-call (fn-lbc-rowwords-get-msgid-length (nfix i) fn-lbc-rowwords)) (ec-call (fn-lbc-rowwords-get-withdrawal-at (nfix i) fn-lbc-rowwords)) (ec-call (fn-lbc-rowwords-get-withdrawal-by (nfix i) fn-lbc-rowwords)) (ec-call (fn-lbc-rowwords-get-overview-offset (nfix i) fn-lbc-rowwords)) (ec-call (fn-lbc-rowwords-get-flags (nfix i) fn-lbc-rowwords)))
        (lcm-fixture-read-rowwords (+ 1 (nfix i)) (1- (nfix fuel)) fn-lbc-rowwords))))
(verify-guards lcm-fixture-read-rowwords)

(defun lcm-fixture-read-msgid-octets (i fuel fn-lbc-msgid-octets)
 (declare (xargs :stobjs fn-lbc-msgid-octets :guard t :verify-guards nil :measure (nfix fuel)))
 (if (or (zp (nfix fuel)) (<= (fn-lbc-msgid-octets-count fn-lbc-msgid-octets) (nfix i))) nil
  (cons (list (ec-call (fn-lbc-msgid-octets-get-octet (nfix i) fn-lbc-msgid-octets)))
        (lcm-fixture-read-msgid-octets (+ 1 (nfix i)) (1- (nfix fuel)) fn-lbc-msgid-octets))))
(verify-guards lcm-fixture-read-msgid-octets)

(defun lcm-fixture-read-overview-octets (i fuel fn-lbc-overview-octets)
 (declare (xargs :stobjs fn-lbc-overview-octets :guard t :verify-guards nil :measure (nfix fuel)))
 (if (or (zp (nfix fuel)) (<= (fn-lbc-overview-octets-count fn-lbc-overview-octets) (nfix i))) nil
  (cons (list (ec-call (fn-lbc-overview-octets-get-octet (nfix i) fn-lbc-overview-octets)))
        (lcm-fixture-read-overview-octets (+ 1 (nfix i)) (1- (nfix fuel)) fn-lbc-overview-octets))))
(verify-guards lcm-fixture-read-overview-octets)

(defun lcm-fixture-read-msgid-slots (i fuel fn-lbc-msgid-slots)
 (declare (xargs :stobjs fn-lbc-msgid-slots :guard t :verify-guards nil :measure (nfix fuel)))
 (if (or (zp (nfix fuel)) (<= (fn-lbc-msgid-slots-count fn-lbc-msgid-slots) (nfix i))) nil
  (cons (list (ec-call (fn-lbc-msgid-slots-get-word (nfix i) fn-lbc-msgid-slots)))
        (lcm-fixture-read-msgid-slots (+ 1 (nfix i)) (1- (nfix fuel)) fn-lbc-msgid-slots))))
(verify-guards lcm-fixture-read-msgid-slots)

(defun lcm-fixture-read-directory (i fuel fn-lbc-directory)
 (declare (xargs :stobjs fn-lbc-directory :guard t :verify-guards nil :measure (nfix fuel)))
 (if (or (zp (nfix fuel)) (<= (fn-lbc-directory-count fn-lbc-directory) (nfix i))) nil
  (cons (list (ec-call (fn-lbc-directory-get-sequence (nfix i) fn-lbc-directory)) (ec-call (fn-lbc-directory-get-facts-octets (nfix i) fn-lbc-directory)) (ec-call (fn-lbc-directory-get-body-start (nfix i) fn-lbc-directory)) (ec-call (fn-lbc-directory-get-body-start-present (nfix i) fn-lbc-directory)) (ec-call (fn-lbc-directory-get-body-lines (nfix i) fn-lbc-directory)) (ec-call (fn-lbc-directory-get-nov-start (nfix i) fn-lbc-directory)) (ec-call (fn-lbc-directory-get-nov-length (nfix i) fn-lbc-directory)) (ec-call (fn-lbc-directory-get-render-nov-start (nfix i) fn-lbc-directory)) (ec-call (fn-lbc-directory-get-render-nov-length (nfix i) fn-lbc-directory)) (ec-call (fn-lbc-directory-get-groups-start (nfix i) fn-lbc-directory)) (ec-call (fn-lbc-directory-get-groups-count (nfix i) fn-lbc-directory)) (ec-call (fn-lbc-directory-get-numbers-start (nfix i) fn-lbc-directory)) (ec-call (fn-lbc-directory-get-numbers-count (nfix i) fn-lbc-directory)) (ec-call (fn-lbc-directory-get-article-ok (nfix i) fn-lbc-directory)) (ec-call (fn-lbc-directory-get-head-ok (nfix i) fn-lbc-directory)) (ec-call (fn-lbc-directory-get-body-ok (nfix i) fn-lbc-directory)) (ec-call (fn-lbc-directory-get-raw-head-length (nfix i) fn-lbc-directory)) (ec-call (fn-lbc-directory-get-framed (nfix i) fn-lbc-directory)))
        (lcm-fixture-read-directory (+ 1 (nfix i)) (1- (nfix fuel)) fn-lbc-directory))))
(verify-guards lcm-fixture-read-directory)

(defun lcm-fixture-read-memberships (i fuel fn-lbc-memberships)
 (declare (xargs :stobjs fn-lbc-memberships :guard t :verify-guards nil :measure (nfix fuel)))
 (if (or (zp (nfix fuel)) (<= (fn-lbc-memberships-count fn-lbc-memberships) (nfix i))) nil
  (cons (list (ec-call (fn-lbc-memberships-get-group-start (nfix i) fn-lbc-memberships)) (ec-call (fn-lbc-memberships-get-group-length (nfix i) fn-lbc-memberships)) (ec-call (fn-lbc-memberships-get-number (nfix i) fn-lbc-memberships)))
        (lcm-fixture-read-memberships (+ 1 (nfix i)) (1- (nfix fuel)) fn-lbc-memberships))))
(verify-guards lcm-fixture-read-memberships)

(defun lcm-fixture-read-nov (i fuel fn-lbc-nov)
 (declare (xargs :stobjs fn-lbc-nov :guard t :verify-guards nil :measure (nfix fuel)))
 (if (or (zp (nfix fuel)) (<= (fn-lbc-nov-count fn-lbc-nov) (nfix i))) nil
  (cons (list (ec-call (fn-lbc-nov-get-tomb (nfix i) fn-lbc-nov)) (ec-call (fn-lbc-nov-get-ok (nfix i) fn-lbc-nov)) (ec-call (fn-lbc-nov-get-subject-start (nfix i) fn-lbc-nov)) (ec-call (fn-lbc-nov-get-subject-length (nfix i) fn-lbc-nov)) (ec-call (fn-lbc-nov-get-from-start (nfix i) fn-lbc-nov)) (ec-call (fn-lbc-nov-get-from-length (nfix i) fn-lbc-nov)) (ec-call (fn-lbc-nov-get-date-start (nfix i) fn-lbc-nov)) (ec-call (fn-lbc-nov-get-date-length (nfix i) fn-lbc-nov)) (ec-call (fn-lbc-nov-get-msgid-start (nfix i) fn-lbc-nov)) (ec-call (fn-lbc-nov-get-msgid-length (nfix i) fn-lbc-nov)) (ec-call (fn-lbc-nov-get-references-start (nfix i) fn-lbc-nov)) (ec-call (fn-lbc-nov-get-references-length (nfix i) fn-lbc-nov)))
        (lcm-fixture-read-nov (+ 1 (nfix i)) (1- (nfix fuel)) fn-lbc-nov))))
(verify-guards lcm-fixture-read-nov)

(defun lcm-fixture-escape-cells (i fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc) :verify-guards nil :measure (nfix i)))
 (if (zp (nfix i)) nil
  (cons (cons (1- (nfix i)) (ec-call (fn-lbc-escape-store-get (1- (nfix i)) fn-lbc)))
        (lcm-fixture-escape-cells (1- (nfix i)) fn-lbc))))
(verify-guards lcm-fixture-escape-cells)

(defun lcm-fixture-value (fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc) :verify-guards nil))
 (let* ((row (stobj-let ((fn-lbc-rowwords (fn-lbc-row-store fn-lbc)))
                (value) (lcm-fixture-read-rowwords 0 (fn-lbc-rowwords-count fn-lbc-rowwords) fn-lbc-rowwords) value))
(msgid (stobj-let ((fn-lbc-msgid-octets (fn-lbc-msgid-store fn-lbc)))
                (value) (lcm-fixture-read-msgid-octets 0 (fn-lbc-msgid-octets-count fn-lbc-msgid-octets) fn-lbc-msgid-octets) value))
(overview (stobj-let ((fn-lbc-overview-octets (fn-lbc-overview-store fn-lbc)))
                (value) (lcm-fixture-read-overview-octets 0 (fn-lbc-overview-octets-count fn-lbc-overview-octets) fn-lbc-overview-octets) value))
(slot (stobj-let ((fn-lbc-msgid-slots (fn-lbc-slot-store fn-lbc)))
                (value) (lcm-fixture-read-msgid-slots 0 (fn-lbc-msgid-slots-count fn-lbc-msgid-slots) fn-lbc-msgid-slots) value))
(directory (stobj-let ((fn-lbc-directory (fn-lbc-directory-store fn-lbc)))
                (value) (lcm-fixture-read-directory 0 (fn-lbc-directory-count fn-lbc-directory) fn-lbc-directory) value))
(membership (stobj-let ((fn-lbc-memberships (fn-lbc-membership-store fn-lbc)))
                (value) (lcm-fixture-read-memberships 0 (fn-lbc-memberships-count fn-lbc-memberships) fn-lbc-memberships) value))
(nov (stobj-let ((fn-lbc-nov (fn-lbc-nov-store fn-lbc)))
                (value) (lcm-fixture-read-nov 0 (fn-lbc-nov-count fn-lbc-nov) fn-lbc-nov) value)))
  (list row msgid overview '(nil nil nil) slot directory membership nov
        nil (lcm-fixture-escape-cells (fn-lbc-count fn-lbc) fn-lbc) nil)))
(verify-guards lcm-fixture-value)

(defun lcm-fixture-build-snapshot (rows segs fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc)))
 (let ((fn-lbc (ec-call (fn-lbc-open-rebuild rows segs fn-lbc))))
  (mv (lcm-fixture-value fn-lbc) fn-lbc)))
(defun lcm-fixture-snapshot (rows segs)
 (declare (xargs :guard t :verify-guards nil))
 (with-local-stobj fn-lbc
  (mv-let (value fn-lbc) (lcm-fixture-build-snapshot rows segs fn-lbc) value)))
(verify-guards lcm-fixture-snapshot)
