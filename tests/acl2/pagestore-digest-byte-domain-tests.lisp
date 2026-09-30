(in-package "ACL2")
(include-book "../../books/pagestore-digest-byte-domain")

(defthm pgs-dbdt-begin-positive
  (let ((limit 0) (byte-total 3))
    (and (natp limit) (<= limit 63) (natp byte-total)
         (<= (pgs-dcb-word-count byte-total) (* 128 (expt 2 limit)))
         (pgs-dbd-domainp limit byte-total
           (pgs-dcb-begin 0 0 byte-total :capture :lease (create-pgs-digest-state)))))
  :hints (("Goal" :in-theory (enable pgs-dbd-domainp pgs-dcd-domainp pgs-dbd-framesp
                                   pgs-dcd-framesp pgs-dcb-begin pgs-dc-begin pgs-dcb-word-count)))
  :rule-classes nil)

(defthm pgs-dbdt-begin-limit-natural-removal
  (let ((limit -1) (byte-total 0))
    (and (not (natp limit)) (<= limit 63) (natp byte-total)
         (<= (pgs-dcb-word-count byte-total) (* 128 (expt 2 limit)))
         (not (pgs-dbd-domainp limit byte-total
           (pgs-dcb-begin 0 0 byte-total :capture :lease (create-pgs-digest-state))))))
  :hints (("Goal" :in-theory (enable pgs-dbd-domainp pgs-dcd-domainp pgs-dcb-word-count)))
  :rule-classes nil)

(defthm pgs-dbdt-begin-limit-capacity-removal
  (let ((limit 64) (byte-total 0))
    (and (natp limit) (not (<= limit 63)) (natp byte-total)
         (<= (pgs-dcb-word-count byte-total) (* 128 (expt 2 limit)))
         (not (pgs-dbd-domainp limit byte-total
           (pgs-dcb-begin 0 0 byte-total :capture :lease (create-pgs-digest-state))))))
  :hints (("Goal" :in-theory (enable pgs-dbd-domainp pgs-dcd-domainp pgs-dcb-word-count)))
  :rule-classes nil)

(defthm pgs-dbdt-begin-byte-natural-removal
  (let ((limit 0) (byte-total -1))
    (and (natp limit) (<= limit 63) (not (natp byte-total))
         (<= (pgs-dcb-word-count byte-total) (* 128 (expt 2 limit)))
         (not (pgs-dbd-domainp limit byte-total
           (pgs-dcb-begin 0 0 byte-total :capture :lease (create-pgs-digest-state))))))
  :hints (("Goal" :in-theory (enable pgs-dbd-domainp pgs-dcb-word-count)))
  :rule-classes nil)

(defthm pgs-dbdt-begin-span-bound-removal
  (let ((limit 0) (byte-total 1025))
    (and (natp limit) (<= limit 63) (natp byte-total)
         (not (<= (pgs-dcb-word-count byte-total) (* 128 (expt 2 limit))))
         (not (pgs-dbd-domainp limit byte-total
           (pgs-dcb-begin 0 0 byte-total :capture :lease (create-pgs-digest-state))))))
  :hints (("Goal" :in-theory (enable pgs-dbd-domainp pgs-dcd-domainp pgs-dcb-begin
                                   pgs-dc-begin pgs-dcb-word-count)))
  :rule-classes nil)

(defthm pgs-dbdt-partial-step-positive
  (let* ((byte-total 3)
         (cursor (mv-nth 1 (pgs-dcb-step byte-total nil
                   (pgs-dcb-begin 0 0 byte-total :capture :lease (create-pgs-digest-state)))))
         (next (mv-nth 1 (pgs-dcb-step byte-total nil cursor))))
    (and (pgs-dbd-domainp 0 byte-total cursor)
         (pgs-dbd-domainp 0 byte-total next)
         (equal (pgs-dc-mode cursor) :chunk)
         (equal (pgs-dc-mode next) :return)
         (member-eq (mv-nth 0 (pgs-dcb-step byte-total nil cursor)) '(:continue :done))
         (natp byte-total)
         (equal (pgs-dc-total cursor) (pgs-dcb-word-count byte-total))
         (<= (pgs-dc-start cursor) (pgs-dc-pos cursor))
         (<= (pgs-dc-pos cursor) (pgs-dc-end cursor))
         (<= (pgs-dc-end cursor) (pgs-dc-total cursor))
         (<= (* 8 (pgs-dc-pos cursor)) byte-total)))
  :hints (("Goal" :in-theory (enable pgs-dbd-domainp pgs-dcd-domainp pgs-dbd-framesp
                                   pgs-dcd-framesp pgs-dcb-begin pgs-dc-begin
                                   pgs-dcb-word-count pgs-dcb-step pgs-dc-step)))
  :rule-classes nil)

;; Literal sole-hypothesis removal plus independently identified corrupted mode.
(defthm pgs-dbdt-domain-removal-corrupted-mode
  (let* ((byte-total 3)
         (cursor (update-pgs-dc-mode :broken
                   (pgs-dcb-begin 0 0 byte-total :capture :lease (create-pgs-digest-state))))
         (next (mv-nth 1 (pgs-dcb-step byte-total nil cursor))))
    (and (not (pgs-dbd-domainp 0 byte-total cursor))
         (not (pgs-dbd-domainp 0 byte-total next))
         (not (member-eq (mv-nth 0 (pgs-dcb-step byte-total nil cursor)) '(:continue :done)))))
  :hints (("Goal" :in-theory (enable pgs-dbd-domainp pgs-dcd-domainp pgs-dcb-begin
                                   pgs-dc-begin pgs-dcb-word-count pgs-dcb-step pgs-dc-step)))
  :rule-classes nil)

(defthm pgs-dbdt-guard-domain-removal-corrupted-position
  (let* ((byte-total 3)
         (cursor (update-pgs-dc-pos 1
                   (pgs-dcb-begin 0 0 byte-total :capture :lease (create-pgs-digest-state)))))
    (and (not (pgs-dbd-domainp 0 byte-total cursor))
         (not (and (natp byte-total)
                   (equal (pgs-dc-total cursor) (pgs-dcb-word-count byte-total))
                   (<= (pgs-dc-start cursor) (pgs-dc-pos cursor))
                   (<= (pgs-dc-pos cursor) (pgs-dc-end cursor))
                   (<= (pgs-dc-end cursor) (pgs-dc-total cursor))
                   (<= (* 8 (pgs-dc-pos cursor)) byte-total)))))
  :hints (("Goal" :in-theory (enable pgs-dbd-domainp pgs-dcd-domainp pgs-dcb-begin
                                   pgs-dc-begin pgs-dcb-word-count)))
  :rule-classes nil)

;; Ground driver only, never served; stop on the actual restored right-child start.
(defun-nx pgs-dbdt-right-child (fuel byte-total pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :measure (nfix fuel) :verify-guards nil))
  (if (or (zp fuel) (equal (pgs-dc-start pgs-digest-state) 128)) pgs-digest-state
    (pgs-dbdt-right-child (1- fuel) byte-total
      (mv-nth 1 (pgs-dcb-step byte-total nil pgs-digest-state)))))

(defthm pgs-dbdt-return-left-positive
  (let* ((byte-total 1025)
         (cursor (pgs-dbdt-right-child 24 byte-total
                   (pgs-dcb-begin 0 0 byte-total :capture :lease (create-pgs-digest-state)))))
    (and (equal (pgs-dc-mode cursor) :node) (equal (pgs-dc-depth cursor) 1)
         (equal (pgs-dc-start cursor) 128) (equal (pgs-dc-pos cursor) 128)
         (pgs-dbd-domainp 1 byte-total cursor)
         (pgs-dbd-domainp 1 byte-total (mv-nth 1 (pgs-dcb-step byte-total nil cursor)))
         (<= (* 8 (pgs-dc-pos cursor)) byte-total)))
  :hints (("Goal" :in-theory (enable pgs-dbd-domainp pgs-dcd-domainp pgs-dbd-framesp
                                   pgs-dcd-framesp pgs-dcb-begin pgs-dc-begin pgs-dcb-word-count
                                   pgs-dcb-step pgs-dc-step)
                  :expand ((:free (fuel byte-total cursor) (pgs-dbdt-right-child fuel byte-total cursor))
                           (:free (limit total cursor) (pgs-dcd-framesp 1 limit total cursor))
                           (:free (limit total cursor) (pgs-dcd-framesp 0 limit total cursor))
                           (:free (total cursor) (pgs-dbd-framesp 1 total cursor)))))
  :rule-classes nil)
