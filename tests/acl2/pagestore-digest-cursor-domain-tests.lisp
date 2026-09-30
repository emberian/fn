(in-package "ACL2")
(include-book "../../books/pagestore-digest-cursor-domain")

(defthm pgs-dcdt-begin-positive
  (let ((limit 1) (nb 17))
    (and (natp limit) (<= limit 63) (natp nb)
         (<= (* 8 nb) (* 128 (expt 2 limit)))
         (pgs-dcd-domainp limit
           (pgs-dc-begin 0 0 nb :capture :lease (create-pgs-digest-state)))))
  :hints (("Goal" :in-theory (enable pgs-dcd-domainp pgs-dcd-framesp pgs-dc-begin)))
  :rule-classes nil)

(defthm pgs-dcdt-begin-limit-natural-removal
  (let ((limit -1) (nb 0))
    (and (not (natp limit)) (<= limit 63) (natp nb)
         (<= (* 8 nb) (* 128 (expt 2 limit)))
         (not (pgs-dcd-domainp limit
           (pgs-dc-begin 0 0 nb :capture :lease (create-pgs-digest-state))))))
  :hints (("Goal" :in-theory (enable pgs-dcd-domainp)))
  :rule-classes nil)

(defthm pgs-dcdt-begin-limit-capacity-removal
  (let ((limit 64) (nb 0))
    (and (natp limit) (not (<= limit 63)) (natp nb)
         (<= (* 8 nb) (* 128 (expt 2 limit)))
         (not (pgs-dcd-domainp limit
           (pgs-dc-begin 0 0 nb :capture :lease (create-pgs-digest-state))))))
  :hints (("Goal" :in-theory (enable pgs-dcd-domainp)))
  :rule-classes nil)

(defthm pgs-dcdt-begin-block-natural-removal
  (let ((limit 0) (nb -1))
    (and (natp limit) (<= limit 63) (not (natp nb))
         (<= (* 8 nb) (* 128 (expt 2 limit)))
         (not (pgs-dcd-domainp limit
           (pgs-dc-begin 0 0 nb :capture :lease (create-pgs-digest-state))))))
  :hints (("Goal" :in-theory (enable pgs-dcd-domainp pgs-dc-begin)))
  :rule-classes nil)

(defthm pgs-dcdt-begin-span-bound-removal
  (let ((limit 0) (nb 17))
    (and (natp limit) (<= limit 63) (natp nb)
         (not (<= (* 8 nb) (* 128 (expt 2 limit))))
         (not (pgs-dcd-domainp limit
           (pgs-dc-begin 0 0 nb :capture :lease (create-pgs-digest-state))))))
  :hints (("Goal" :in-theory (enable pgs-dcd-domainp pgs-dc-begin)))
  :rule-classes nil)

(defthm pgs-dcdt-step-positive
  (let* ((cursor (pgs-dc-begin 0 0 17 :capture :lease (create-pgs-digest-state)))
         (next (mv-nth 1 (pgs-dc-step nil cursor))))
    (and (pgs-dcd-domainp 1 cursor)
         (pgs-dcd-domainp 1 next)
         (member-eq (mv-nth 0 (pgs-dc-step nil cursor)) '(:continue :done))
         (<= (pgs-dc-start cursor) (pgs-dc-pos cursor))
         (<= (pgs-dc-pos cursor) (pgs-dc-end cursor))
         (<= (pgs-dc-end cursor) (pgs-dc-total cursor))))
  :hints (("Goal" :in-theory (enable pgs-dc-begin pgs-dc-step pgs-dcd-domainp pgs-dcd-framesp)))
  :rule-classes nil)

;; Literal domain removal for step preservation and never-invalid. No retained
;; hypothesis exists. Corrupted mode is separately identified as mutation.
(defthm pgs-dcdt-domain-removal-corrupted-mode
  (let* ((cursor (update-pgs-dc-mode :broken
                   (pgs-dc-begin 0 0 1 :capture :lease (create-pgs-digest-state))))
         (next (mv-nth 1 (pgs-dc-step nil cursor))))
    (and (not (pgs-dcd-domainp 0 cursor))
         (not (pgs-dcd-domainp 0 next))
         (not (member-eq (mv-nth 0 (pgs-dc-step nil cursor)) '(:continue :done)))))
  :hints (("Goal" :in-theory (enable pgs-dc-begin pgs-dc-step pgs-dcd-domainp pgs-dcd-framesp)))
  :rule-classes nil)

(defthm pgs-dcdt-guard-domain-removal-corrupted-position
  (let ((cursor (update-pgs-dc-pos 9
                  (pgs-dc-begin 0 0 1 :capture :lease (create-pgs-digest-state)))))
    (and (not (pgs-dcd-domainp 0 cursor))
         (not (and (<= (pgs-dc-start cursor) (pgs-dc-pos cursor))
                   (<= (pgs-dc-pos cursor) (pgs-dc-end cursor))
                   (<= (pgs-dc-end cursor) (pgs-dc-total cursor))))))
  :hints (("Goal" :in-theory (enable pgs-dc-begin pgs-dcd-domainp)))
  :rule-classes nil)

(defthm pgs-dcdt-profile-positive
  (and (natp 1) (<= (* 8 1) (expt 2 64))
       (pgs-dcd-domainp 57 (pgs-dc-begin 0 0 1 :capture :lease (create-pgs-digest-state)))
       (natp 1) (<= 1 (expt 2 32))
       (pgs-dcd-domainp 36 (pgs-dc-begin 0 0 256 :capture :lease (create-pgs-digest-state))))
  :hints (("Goal" :in-theory (enable pgs-dc-begin pgs-dcd-domainp pgs-dcd-framesp)))
  :rule-classes nil)

(defthm pgs-dcdt-u64-natural-removal
  (let ((nb -1))
    (and (not (natp nb)) (<= (* 8 nb) (expt 2 64))
         (not (pgs-dcd-domainp 57 (pgs-dc-begin 0 0 nb :capture :lease (create-pgs-digest-state))))))
  :hints (("Goal" :in-theory (enable pgs-dc-begin pgs-dcd-domainp)))
  :rule-classes nil)

(defthm pgs-dcdt-u64-bound-removal
  (let ((nb (+ 1 (expt 2 61))))
    (and (natp nb) (not (<= (* 8 nb) (expt 2 64)))
         (not (pgs-dcd-domainp 57 (pgs-dc-begin 0 0 nb :capture :lease (create-pgs-digest-state))))))
  :hints (("Goal" :in-theory (enable pgs-dc-begin pgs-dcd-domainp)))
  :rule-classes nil)

(defthm pgs-dcdt-directory-natural-removal
  (let ((page-count -1))
    (and (not (natp page-count)) (<= page-count (expt 2 32))
         (not (pgs-dcd-domainp 36
                (pgs-dc-begin 0 0 (* 256 page-count) :capture :lease (create-pgs-digest-state))))))
  :hints (("Goal" :in-theory (enable pgs-dc-begin pgs-dcd-domainp)))
  :rule-classes nil)

(defthm pgs-dcdt-directory-bound-removal
  (let ((page-count (+ 1 (expt 2 32))))
    (and (natp page-count) (not (<= page-count (expt 2 32)))
         (not (pgs-dcd-domainp 36
                (pgs-dc-begin 0 0 (* 256 page-count) :capture :lease (create-pgs-digest-state))))))
  :hints (("Goal" :in-theory (enable pgs-dc-begin pgs-dcd-domainp)))
  :rule-classes nil)
