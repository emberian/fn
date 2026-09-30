(in-package "ACL2")
(include-book "../../books/pagestore-digest-cursor-progress")

;; Literal test driver only. The general finish theorem uses no fuel ceiling.
(defun pgs-dcst-run (fuel byte-total msg pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :measure (nfix fuel) :verify-guards nil))
  (if (or (zp fuel) (equal (pgs-dc-mode pgs-digest-state) :done)) pgs-digest-state
    (mv-let (status pgs-digest-state)
      (pgs-dcb-step byte-total
        (fn-b3-words 16 (fn-b3-nthcdrx (pgs-dcb-next-byte-offset pgs-digest-state) msg))
        pgs-digest-state)
      (declare (ignore status))
      (pgs-dcst-run (1- fuel) byte-total msg pgs-digest-state))))

(defun-nx pgs-dcst-small-chunk ()
  (mv-nth 1 (pgs-dcb-step 3 nil
    (pgs-dcb-begin 0 0 3 :capture :lease (create-pgs-digest-state)))))

(defun-nx pgs-dcst-done (msg)
  (pgs-dcst-run 128 (len msg) msg
    (pgs-dcb-begin 0 0 (len msg) :capture :lease (create-pgs-digest-state))))

(defthm pgs-dcst-begin-positive
  (let ((limit 1) (byte-total 1025) (msg (make-list 1025 :initial-element 9)))
    (and (natp limit) (<= limit 63) (fn-b3-octet-listp msg) (equal (len msg) byte-total)
         (<= (pgs-dcb-word-count byte-total) (* 128 (expt 2 limit)))
         (pgs-dcs-invariantp limit byte-total msg
           (pgs-dcb-begin 0 0 byte-total :capture :lease (create-pgs-digest-state)))))
  :hints (("Goal" :use ((:instance pgs-dcs-begin-establishes-invariant
                          (limit 1) (byte-total 1025) (msg (make-list 1025 :initial-element 9))
                          (sel 0) (base 0) (capture :capture) (lease :lease)
                          (pgs-digest-state (create-pgs-digest-state))))
                  :in-theory (disable pgs-dcs-invariantp pgs-dcb-begin
                                      pgs-dcs-begin-establishes-invariant)))
  :rule-classes nil)

(defthm pgs-dcst-step-and-progress-positive
  (let* ((limit 0) (byte-total 3) (msg '(1 2 3)) (cursor (pgs-dcst-small-chunk))
         (block (fn-b3-words 16 msg)) (next (mv-nth 1 (pgs-dcb-step byte-total block cursor))))
    (and (equal (pgs-dc-mode cursor) :chunk)
         (pgs-dcs-invariantp limit byte-total msg cursor)
         (pgs-dcs-blockp block msg cursor)
         (pgs-dcs-invariantp limit byte-total msg next)
         (not (equal (pgs-dc-mode cursor) :done))
         (member-eq (mv-nth 0 (pgs-dcb-step byte-total block cursor)) '(:continue :done))
         (equal (equal (mv-nth 0 (pgs-dcb-step byte-total block cursor)) :done)
                (equal (pgs-dc-mode next) :done))
         (equal (pgs-dcr-denote msg next) (pgs-dcr-denote msg cursor))
         (equal (pgs-dc-capture next) (pgs-dc-capture cursor))
         (equal (pgs-dc-lease next) (pgs-dc-lease cursor))
         (natp (pgs-dcs-potential cursor))
         (< (pgs-dcs-potential next) (pgs-dcs-potential cursor))
         (equal (pgs-dcs-potential next) (- (pgs-dcs-potential cursor) 1))))
  :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                                   pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
                                   pgs-dcs-phasep pgs-dcs-blockp pgs-dcr-denote pgs-dcr-current pgs-dcr-span
                                   pgs-dcs-potential pgs-dcs-frame-work pgs-dcs-chunk-work)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
  :rule-classes nil)

;; Hypothesis removal: correct input state, wrong consuming block.
(defthm pgs-dcst-step-block-removal
  (let* ((limit 0) (byte-total 3) (msg '(1 2 3)) (cursor (pgs-dcst-small-chunk)) (block nil)
         (next (mv-nth 1 (pgs-dcb-step byte-total block cursor))))
    (and (pgs-dcs-invariantp limit byte-total msg cursor)
         (not (pgs-dcs-blockp block msg cursor))
         (not (equal (pgs-dc-mode cursor) :done))
         (not (pgs-dcs-invariantp limit byte-total msg next))))
  :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                                   pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
                                   pgs-dcs-phasep pgs-dcs-blockp pgs-dcr-denote pgs-dcr-current pgs-dcr-span)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
  :rule-classes nil)

;; Source mutation after consumption, separately labelled. Both source lists
;; have the same length; the retained no-demand block contract still holds.
(defthm pgs-dcst-step-invariant-removal-source-mutation
  (let* ((limit 0) (byte-total 3) (msg '(1 2 4))
         (cursor (mv-nth 1 (pgs-dcb-step byte-total (fn-b3-words 16 '(1 2 3)) (pgs-dcst-small-chunk))))
         (block nil) (next (mv-nth 1 (pgs-dcb-step byte-total block cursor))))
    (and (equal (pgs-dc-mode cursor) :return)
         (not (equal (pgs-dc-mode cursor) :done))
         (not (pgs-dcs-invariantp limit byte-total msg cursor))
         (pgs-dcs-blockp block msg cursor)
         (not (pgs-dcs-invariantp limit byte-total msg next))))
  :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dcs-blockp pgs-dcr-denote
                                   pgs-dcr-current pgs-dcr-span)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
  :rule-classes nil)

(defthm pgs-dcst-progress-invariant-removal-corrupted-mode
  (let* ((limit 0) (byte-total 3) (msg '(1 2 3))
         (cursor (update-pgs-dc-mode :broken (pgs-dcst-small-chunk)))
         (next (mv-nth 1 (pgs-dcb-step byte-total nil cursor))))
    (and (not (pgs-dcs-invariantp limit byte-total msg cursor))
         (not (equal (pgs-dc-mode cursor) :done))
         (natp (pgs-dcs-potential cursor))
         (not (< (pgs-dcs-potential next) (pgs-dcs-potential cursor)))))
  :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                                   pgs-dcs-potential pgs-dcs-frame-work pgs-dcb-step pgs-dc-step)))
  :rule-classes nil)

(defthm pgs-dcst-terminal-and-progress-done-positive
  (let* ((limit 0) (byte-total 3) (msg '(1 2 3)) (cursor (pgs-dcst-done msg))
         (next (mv-nth 1 (pgs-dcb-step byte-total nil cursor))))
    (and (pgs-dcs-invariantp limit byte-total msg cursor)
         (equal (pgs-dc-mode cursor) :done)
         (pgs-dcs-blockp nil msg cursor)
         (equal (pgs-dcb-result-octets cursor) (fn-blake3 msg))
         (equal (pgs-dc-result cursor) (pgs-octets-be-nat (fn-blake3 msg)))
         (not (< (pgs-dcs-potential next) (pgs-dcs-potential cursor)))))
  :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                                   pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
                                   pgs-dcs-phasep pgs-dcs-blockp pgs-dcr-denote pgs-dcr-current pgs-dcs-potential)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
  :rule-classes nil)

(defthm pgs-dcst-terminal-mode-removal
  (let* ((limit 0) (byte-total 3) (msg '(1 2 3))
         (cursor (pgs-dcb-begin 0 0 byte-total :capture :lease (create-pgs-digest-state))))
    (and (pgs-dcs-invariantp limit byte-total msg cursor)
         (not (equal (pgs-dc-mode cursor) :done))
         (not (equal (pgs-dcb-result-octets cursor) (fn-blake3 msg)))))
  :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                                   pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
                                   pgs-dcs-phasep pgs-dcr-denote pgs-dcr-current pgs-dcr-span
                                   pgs-dcb-begin pgs-dc-begin pgs-dcb-result-octets)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
  :rule-classes nil)

(defthm pgs-dcst-terminal-invariant-removal-corrupted-output
  (let* ((limit 0) (byte-total 3) (msg '(1 2 3))
         (cursor (update-pgs-dc-output nil (pgs-dcst-done msg))))
    (and (not (pgs-dcs-invariantp limit byte-total msg cursor))
         (equal (pgs-dc-mode cursor) :done)
         (not (equal (pgs-dcb-result-octets cursor) (fn-blake3 msg)))))
  :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dcs-phasep pgs-dcr-denote
                                   pgs-dcr-current pgs-dcb-result-octets)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
  :rule-classes nil)

;; Every tested boundary is an actual machine trajectory, including exact
;; empty, full/partial block, leaf and uneven parent spans.
(defthm pgs-dcst-boundaries-positive
  (and (equal (pgs-dcb-result-octets (pgs-dcst-done nil)) (fn-blake3 nil))
       (equal (pgs-dcb-result-octets (pgs-dcst-done '(1 2 3))) (fn-blake3 '(1 2 3)))
       (equal (pgs-dcb-result-octets (pgs-dcst-done (make-list 64 :initial-element 9)))
              (fn-blake3 (make-list 64 :initial-element 9)))
       (equal (pgs-dcb-result-octets (pgs-dcst-done (make-list 65 :initial-element 9)))
              (fn-blake3 (make-list 65 :initial-element 9)))
       (equal (pgs-dcb-result-octets (pgs-dcst-done (make-list 1024 :initial-element 9)))
              (fn-blake3 (make-list 1024 :initial-element 9)))
       (equal (pgs-dcb-result-octets (pgs-dcst-done (make-list 1025 :initial-element 9)))
              (fn-blake3 (make-list 1025 :initial-element 9)))
       (equal (pgs-dcb-result-octets (pgs-dcst-done (make-list 2049 :initial-element 9)))
              (fn-blake3 (make-list 2049 :initial-element 9))))
  :hints (("Goal" :in-theory (enable pgs-dcb-result-octets)))
  :rule-classes nil)

;; Literal begin removals affirm every retained hypothesis. NATP byte-total
;; is redundant with len equality and was removed in the weakened theorem.
(defthm pgs-dcst-begin-limit-natural-removal
  (let ((limit -1) (byte-total 3) (msg '(1 2 3)))
    (and (not (natp limit))
         (<= limit 63)
         (fn-b3-octet-listp msg)
         (equal (len msg) byte-total)
         (<= (pgs-dcb-word-count byte-total) (* 128 (expt 2 limit)))
         (not (pgs-dcs-invariantp limit byte-total msg
                  (pgs-dcb-begin 0 0 byte-total :capture :lease (create-pgs-digest-state))))))
  :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                                   pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
                                   pgs-dcs-phasep pgs-dcr-denote pgs-dcr-current pgs-dcr-span
                                   pgs-dcb-begin pgs-dc-begin pgs-dcb-word-count)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
  :rule-classes nil)

(defthm pgs-dcst-begin-limit-capacity-removal
  (let ((limit 64) (byte-total 3) (msg '(1 2 3)))
    (and (natp limit)
         (not (<= limit 63))
         (fn-b3-octet-listp msg)
         (equal (len msg) byte-total)
         (<= (pgs-dcb-word-count byte-total) (* 128 (expt 2 limit)))
         (not (pgs-dcs-invariantp limit byte-total msg
                  (pgs-dcb-begin 0 0 byte-total :capture :lease (create-pgs-digest-state))))))
  :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                                   pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
                                   pgs-dcs-phasep pgs-dcr-denote pgs-dcr-current pgs-dcr-span
                                   pgs-dcb-begin pgs-dc-begin pgs-dcb-word-count)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
  :rule-classes nil)

(defthm pgs-dcst-begin-octet-source-removal
  (let ((limit 0) (byte-total 1) (msg '(999)))
    (and (natp limit)
         (<= limit 63)
         (not (fn-b3-octet-listp msg))
         (equal (len msg) byte-total)
         (<= (pgs-dcb-word-count byte-total) (* 128 (expt 2 limit)))
         (not (pgs-dcs-invariantp limit byte-total msg
                  (pgs-dcb-begin 0 0 byte-total :capture :lease (create-pgs-digest-state))))))
  :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                                   pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
                                   pgs-dcs-phasep pgs-dcr-denote pgs-dcr-current pgs-dcr-span
                                   pgs-dcb-begin pgs-dc-begin pgs-dcb-word-count)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
  :rule-classes nil)

(defthm pgs-dcst-begin-captured-length-removal
  (let ((limit 0) (byte-total 1) (msg '(1 2 3)))
    (and (natp limit)
         (<= limit 63)
         (fn-b3-octet-listp msg)
         (not (equal (len msg) byte-total))
         (<= (pgs-dcb-word-count byte-total) (* 128 (expt 2 limit)))
         (not (pgs-dcs-invariantp limit byte-total msg
                  (pgs-dcb-begin 0 0 byte-total :capture :lease (create-pgs-digest-state))))))
  :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                                   pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
                                   pgs-dcs-phasep pgs-dcr-denote pgs-dcr-current pgs-dcr-span
                                   pgs-dcb-begin pgs-dc-begin pgs-dcb-word-count)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
  :rule-classes nil)

(defthm pgs-dcst-begin-span-capacity-removal
  (let ((limit 0) (byte-total 1025) (msg (make-list 1025 :initial-element 9)))
    (and (natp limit)
         (<= limit 63)
         (fn-b3-octet-listp msg)
         (equal (len msg) byte-total)
         (not (<= (pgs-dcb-word-count byte-total) (* 128 (expt 2 limit))))
         (not (pgs-dcs-invariantp limit byte-total msg
                  (pgs-dcb-begin 0 0 byte-total :capture :lease (create-pgs-digest-state))))))
  :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                                   pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
                                   pgs-dcs-phasep pgs-dcr-denote pgs-dcr-current pgs-dcr-span
                                   pgs-dcb-begin pgs-dc-begin pgs-dcb-word-count)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
  :rule-classes nil)

(defthm pgs-dcst-complete-limit-natural-removal
  (let ((limit -1) (byte-total 3) (msg '(1 2 3)))
    (and (not (natp limit))
         (<= limit 63)
         (fn-b3-octet-listp msg)
         (equal (len msg) byte-total)
         (<= (pgs-dcb-word-count byte-total) (* 128 (expt 2 limit)))
         (not (equal (pgs-dcb-result-octets
                        (pgs-dcs-finish limit byte-total msg
                          (pgs-dcb-begin 0 0 byte-total :capture :lease (create-pgs-digest-state))))
                     (fn-blake3 msg)))))
  :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                                   pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
                                   pgs-dcs-phasep pgs-dcr-denote pgs-dcr-current pgs-dcr-span
                                   pgs-dcb-begin pgs-dc-begin pgs-dcb-word-count pgs-dcs-finish pgs-dcb-result-octets)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
  :rule-classes nil)

(defthm pgs-dcst-complete-limit-capacity-removal
  (let ((limit 64) (byte-total 3) (msg '(1 2 3)))
    (and (natp limit)
         (not (<= limit 63))
         (fn-b3-octet-listp msg)
         (equal (len msg) byte-total)
         (<= (pgs-dcb-word-count byte-total) (* 128 (expt 2 limit)))
         (not (equal (pgs-dcb-result-octets
                        (pgs-dcs-finish limit byte-total msg
                          (pgs-dcb-begin 0 0 byte-total :capture :lease (create-pgs-digest-state))))
                     (fn-blake3 msg)))))
  :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                                   pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
                                   pgs-dcs-phasep pgs-dcr-denote pgs-dcr-current pgs-dcr-span
                                   pgs-dcb-begin pgs-dc-begin pgs-dcb-word-count pgs-dcs-finish pgs-dcb-result-octets)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
  :rule-classes nil)

(defthm pgs-dcst-complete-octet-source-removal
  (let ((limit 0) (byte-total 1) (msg '(999)))
    (and (natp limit)
         (<= limit 63)
         (not (fn-b3-octet-listp msg))
         (equal (len msg) byte-total)
         (<= (pgs-dcb-word-count byte-total) (* 128 (expt 2 limit)))
         (not (equal (pgs-dcb-result-octets
                        (pgs-dcs-finish limit byte-total msg
                          (pgs-dcb-begin 0 0 byte-total :capture :lease (create-pgs-digest-state))))
                     (fn-blake3 msg)))))
  :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                                   pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
                                   pgs-dcs-phasep pgs-dcr-denote pgs-dcr-current pgs-dcr-span
                                   pgs-dcb-begin pgs-dc-begin pgs-dcb-word-count pgs-dcs-finish pgs-dcb-result-octets)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
  :rule-classes nil)

(defthm pgs-dcst-complete-captured-length-removal
  (let ((limit 0) (byte-total 1) (msg '(1 2 3)))
    (and (natp limit)
         (<= limit 63)
         (fn-b3-octet-listp msg)
         (not (equal (len msg) byte-total))
         (<= (pgs-dcb-word-count byte-total) (* 128 (expt 2 limit)))
         (not (equal (pgs-dcb-result-octets
                        (pgs-dcs-finish limit byte-total msg
                          (pgs-dcb-begin 0 0 byte-total :capture :lease (create-pgs-digest-state))))
                     (fn-blake3 msg)))))
  :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                                   pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
                                   pgs-dcs-phasep pgs-dcr-denote pgs-dcr-current pgs-dcr-span
                                   pgs-dcb-begin pgs-dc-begin pgs-dcb-word-count pgs-dcs-finish pgs-dcb-result-octets)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
  :rule-classes nil)

(defthm pgs-dcst-complete-span-capacity-removal
  (let ((limit 0) (byte-total 1025) (msg (make-list 1025 :initial-element 9)))
    (and (natp limit)
         (<= limit 63)
         (fn-b3-octet-listp msg)
         (equal (len msg) byte-total)
         (not (<= (pgs-dcb-word-count byte-total) (* 128 (expt 2 limit))))
         (not (equal (pgs-dcb-result-octets
                        (pgs-dcs-finish limit byte-total msg
                          (pgs-dcb-begin 0 0 byte-total :capture :lease (create-pgs-digest-state))))
                     (fn-blake3 msg)))))
  :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                                   pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
                                   pgs-dcs-phasep pgs-dcr-denote pgs-dcr-current pgs-dcr-span
                                   pgs-dcb-begin pgs-dc-begin pgs-dcb-word-count pgs-dcs-finish pgs-dcb-result-octets)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
  :rule-classes nil)

(defthm pgs-dcst-complete-and-finish-positive
  (let* ((limit 1) (byte-total 1025) (msg (make-list 1025 :initial-element 9))
         (initial (pgs-dcb-begin 0 0 byte-total :capture :lease (create-pgs-digest-state)))
         (final (pgs-dcs-finish limit byte-total msg initial)))
    (and (natp limit) (<= limit 63) (fn-b3-octet-listp msg) (equal (len msg) byte-total)
         (<= (pgs-dcb-word-count byte-total) (* 128 (expt 2 limit)))
         (pgs-dcs-invariantp limit byte-total msg initial)
         (pgs-dcs-invariantp limit byte-total msg final)
         (equal (pgs-dc-mode final) :done)
         (equal (pgs-dcb-result-octets final) (fn-blake3 msg))))
  :hints (("Goal"
            :use ((:instance pgs-dcs-begin-establishes-invariant
                    (limit 1) (byte-total 1025) (msg (make-list 1025 :initial-element 9))
                    (sel 0) (base 0) (capture :capture) (lease :lease)
                    (pgs-digest-state (create-pgs-digest-state)))
                  (:instance pgs-dcs-finish-preserves-invariant-and-reaches-done
                    (limit 1) (byte-total 1025) (msg (make-list 1025 :initial-element 9))
                    (pgs-digest-state (pgs-dcb-begin 0 0 1025 :capture :lease (create-pgs-digest-state))))
                  (:instance pgs-dcs-complete-byte-run-is-blake3
                    (limit 1) (byte-total 1025) (msg (make-list 1025 :initial-element 9))
                    (sel 0) (base 0) (capture :capture) (lease :lease)
                    (pgs-digest-state (create-pgs-digest-state))))
            :in-theory (disable pgs-dcs-invariantp pgs-dcs-finish pgs-dcb-begin pgs-dcb-result-octets
                                pgs-dcs-begin-establishes-invariant
                                pgs-dcs-finish-preserves-invariant-and-reaches-done)))
  :rule-classes nil)

(defthm pgs-dcst-finish-invariant-removal-corrupted-mode
  (let* ((limit 0) (byte-total 3) (msg '(1 2 3))
         (initial (update-pgs-dc-mode :broken (pgs-dcst-small-chunk)))
         (final (pgs-dcs-finish limit byte-total msg initial)))
    (and (not (pgs-dcs-invariantp limit byte-total msg initial))
         (not (pgs-dcs-invariantp limit byte-total msg final))
         (not (equal (pgs-dc-mode final) :done))))
  :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp pgs-dcs-finish)))
  :rule-classes nil)

(defthm pgs-dcst-counter-positive-right-child
  (let* ((limit 1) (byte-total 1025) (msg (make-list 1025 :initial-element 9))
         (cursor (pgs-dcst-run 20 byte-total msg
                   (pgs-dcb-begin 0 0 byte-total :capture :lease (create-pgs-digest-state))))
         (frame (pgs-dc-framesi 0 cursor)))
    (and (equal (pgs-dc-mode cursor) :node) (equal (pgs-dc-depth cursor) 1)
         (pgs-dbd-domainp limit byte-total cursor) (pgs-dcs-counterp cursor)
         (equal (pgs-dc-start cursor) 128) (equal (pgs-dc-counter cursor) 1)
         (equal (fn-b3-nthx 1 frame) 128) (equal (fn-b3-nthx 3 frame) 1)
         (<= (pgs-dc-total cursor) (expt 2 64))
         (<= (pgs-dc-counter cursor) (expt 2 57))
         (pgs-dcs-counterp (mv-nth 1 (pgs-dcb-step byte-total nil cursor)))))
  :hints (("Goal" :in-theory (enable pgs-dbd-domainp pgs-dcd-domainp pgs-dbd-framesp pgs-dcd-framesp
                                   pgs-dcs-counterp pgs-dcs-counter-framesp)
                  :expand ((:free (d l total cursor) (pgs-dcd-framesp d l total cursor)))))
  :rule-classes nil)

;; Counter carry removal: valid scalar/resource domain, forged current counter.
(defthm pgs-dcst-counter-carry-removal
  (let* ((limit 1) (byte-total 1025)
         (cursor (update-pgs-dc-pos 1 (update-pgs-dc-start 1
                   (pgs-dcb-begin 0 0 byte-total :capture :lease (create-pgs-digest-state)))))
         (next (mv-nth 1 (pgs-dcb-step byte-total nil cursor))))
    (and (pgs-dbd-domainp limit byte-total cursor)
         (not (pgs-dcs-counterp cursor)) (not (pgs-dcs-counterp next))))
  :hints (("Goal" :in-theory (enable pgs-dbd-domainp pgs-dcd-domainp pgs-dbd-framesp pgs-dcd-framesp
                                   pgs-dcs-counterp pgs-dcs-counter-framesp)
                  :expand ((:free (d l total cursor) (pgs-dcd-framesp d l total cursor)))))
  :rule-classes nil)

;; Domain removal, separately labelled corrupted fractional frame counter.
(defthm pgs-dcst-counter-domain-removal-corrupted-frame
  (let* ((limit 1) (byte-total 1025)
         (cursor (update-pgs-dc-mode :return (update-pgs-dc-depth 1
                   (update-pgs-dc-framesi 0 (list :left 1 2 1/128 nil)
                     (pgs-dcb-begin 0 0 byte-total :capture :lease (create-pgs-digest-state))))))
         (next (mv-nth 1 (pgs-dcb-step byte-total nil cursor))))
    (and (not (pgs-dbd-domainp limit byte-total cursor))
         (pgs-dcs-counterp cursor) (not (pgs-dcs-counterp next))))
  :hints (("Goal" :in-theory (enable pgs-dbd-domainp pgs-dcd-domainp pgs-dbd-framesp pgs-dcd-framesp
                                   pgs-dcs-counterp pgs-dcs-counter-framesp)
                  :expand ((:free (d l total cursor) (pgs-dcd-framesp d l total cursor)))))
  :rule-classes nil)

(defthm pgs-dcst-counter-bound-carry-removal
  (let ((cursor (update-pgs-dc-counter (expt 2 58)
                  (pgs-dcb-begin 0 0 3 :capture :lease (create-pgs-digest-state)))))
    (and (pgs-dbd-domainp 0 3 cursor)
         (not (pgs-dcs-counterp cursor))
         (<= (pgs-dc-total cursor) (expt 2 64))
         (not (<= (pgs-dc-counter cursor) (expt 2 57)))))
  :hints (("Goal" :in-theory (enable pgs-dbd-domainp pgs-dcd-domainp pgs-dbd-framesp
                                   pgs-dcd-framesp pgs-dcs-counterp pgs-dcs-counter-framesp)))
  :rule-classes nil)

(defthm pgs-dcst-counter-bound-domain-removal
  (let ((cursor (update-pgs-dc-pos (expt 2 65)
                  (update-pgs-dc-start (expt 2 65)
                    (update-pgs-dc-counter (expt 2 58)
                      (pgs-dcb-begin 0 0 3 :capture :lease (create-pgs-digest-state)))))))
    (and (not (pgs-dbd-domainp 0 3 cursor))
         (pgs-dcs-counterp cursor)
         (<= (pgs-dc-total cursor) (expt 2 64))
         (not (<= (pgs-dc-counter cursor) (expt 2 57)))))
  :hints (("Goal" :in-theory (enable pgs-dbd-domainp pgs-dcd-domainp pgs-dbd-framesp
                                   pgs-dcd-framesp pgs-dcs-counterp pgs-dcs-counter-framesp)))
  :rule-classes nil)

;; Scalar corrupted state, no allocation proportional to this forged total.
(defthm pgs-dcst-counter-bound-total-removal
  (let* ((byte-total (* 8 (expt 2 65)))
         (cursor (update-pgs-dc-pos (expt 2 65)
                   (update-pgs-dc-start (expt 2 65)
                     (update-pgs-dc-counter (expt 2 58)
                       (pgs-dcb-begin 0 0 byte-total :capture :lease (create-pgs-digest-state)))))))
    (and (pgs-dbd-domainp 59 byte-total cursor)
         (pgs-dcs-counterp cursor)
         (not (<= (pgs-dc-total cursor) (expt 2 64)))
         (not (<= (pgs-dc-counter cursor) (expt 2 57)))))
  :hints (("Goal" :in-theory (enable pgs-dbd-domainp pgs-dcd-domainp pgs-dbd-framesp
                                   pgs-dcd-framesp pgs-dcs-counterp pgs-dcs-counter-framesp)))
  :rule-classes nil)

(defthm pgs-dcst-contract-nondone-removal
  (let* ((msg '(1 2 3)) (cursor (pgs-dcst-done msg))
         (next (mv-nth 1 (pgs-dcb-step 3 nil cursor))))
    (and (pgs-dcs-invariantp 0 3 msg cursor)
         (pgs-dcs-blockp nil msg cursor)
         (equal (pgs-dc-mode cursor) :done)
         (not (equal (pgs-dcs-potential next) (- (pgs-dcs-potential cursor) 1)))
         (not (< (pgs-dcs-potential next) (pgs-dcs-potential cursor)))))
  :hints (("Goal" :in-theory (enable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcd-domainp
                                   pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
                                   pgs-dcs-phasep pgs-dcs-blockp pgs-dcr-denote pgs-dcr-current pgs-dcs-potential)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
  :rule-classes nil)
