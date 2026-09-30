(in-package "ACL2")
(include-book "../../books/pagestore-digest-cursor")

;; Test driver only; the served client yields after one tick, never calls RUN.
(defun pgs-dct-run (fuel pgs-mem pgs-digest-state)
  (declare (xargs :stobjs (pgs-mem pgs-digest-state) :measure (nfix fuel)
                  :guard (natp fuel) :verify-guards nil))
  (if (zp fuel) pgs-digest-state
    (mv-let (status pgs-digest-state) (pgs-dc-tick pgs-mem pgs-digest-state)
      (if (eq status :done) pgs-digest-state
        (pgs-dct-run (1- fuel) pgs-mem pgs-digest-state)))))

(defun-nx pgs-dct-example (nb words fuel)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((mem (update-nth *pgs-wi* words (create-pgs-mem)))
         (cursor (pgs-dc-begin 0 0 nb :capture-17 :lease-23 (create-pgs-digest-state)))
         (next (pgs-dct-run fuel mem cursor)))
    (list (pgs-dc-mode next) (pgs-dc-result next)
          (pgs-dc-capture next) (pgs-dc-lease next))))

(defthm pgs-dct-empty-positive
  (equal (pgs-dct-example 0 nil 8)
         (list :done
               (pgs-octets-be-nat (fn-blake3 nil)) :capture-17 :lease-23))
  :rule-classes nil)

(defthm pgs-dct-block-positive
  (let ((words '(#x0706050403020100 #x0f0e0d0c0b0a0908
                 #x1716151413121110 #x1f1e1d1c1b1a1918
                 #x2726252423222120 #x2f2e2d2c2b2a2928
                 #x3736353433323130 #x3f3e3d3c3b3a3938)))
    (and (equal (pgs-dct-example 1 words 8)
                (list :done #x4eed7141ea4a5cd4b788606bd23f46e212af9cacebacdc7d1f4c6dc7f2511b98
                      :capture-17 :lease-23))
         (equal (pgs-octets-be-nat (fn-blake3 (pgs-words-le-octets words)))
                #x4eed7141ea4a5cd4b788606bd23f46e212af9cacebacdc7d1f4c6dc7f2511b98)))
  :rule-classes nil)

(defthm pgs-dct-chunk-positive
  (let ((words (make-list 128 :initial-element #x8877665544332211)))
    (and (equal (car (pgs-dct-example 16 words 32)) :done)
         (equal (cadr (pgs-dct-example 16 words 32))
                (pgs-octets-be-nat (fn-blake3 (pgs-words-le-octets words))))))
  :rule-classes nil)

(defthm pgs-dct-uneven-tree-positive
  (let ((words (append (make-list 128 :initial-element 1)
                       (make-list 8 :initial-element 2))))
    (and (equal (car (pgs-dct-example 17 words 40)) :done)
         (equal (cadr (pgs-dct-example 17 words 40))
                (pgs-octets-be-nat (fn-blake3 (pgs-words-le-octets words))))))
  :rule-classes nil)

(defthm pgs-dct-three-chunks-positive
  (let ((words (append (make-list 128 :initial-element 1)
                       (make-list 128 :initial-element 2)
                       (make-list 8 :initial-element 3))))
    (and (equal (car (pgs-dct-example 33 words 100)) :done)
         (equal (cadr (pgs-dct-example 33 words 100))
                (pgs-octets-be-nat (fn-blake3 (pgs-words-le-octets words))))))
  :rule-classes nil)

(defthm pgs-dct-mutated-source-witness
  (let ((words (make-list 8 :initial-element 1))
        (altered (make-list 8 :initial-element 2)))
    (and (equal (car (pgs-dct-example 1 words 8)) :done)
         (equal (car (pgs-dct-example 1 altered 8)) :done)
         (not (equal (cadr (pgs-dct-example 1 words 8))
                     (cadr (pgs-dct-example 1 altered 8))))))
  :rule-classes nil)


;; Literal actual old host-called boundary; not only the BLAKE3 list twin.
(defthm pgs-dct-actual-word-digest-positive
  (let* ((words (append (make-list 128 :initial-element 1)
                        (make-list 8 :initial-element 2)))
         (mem (update-nth *pgs-wi* words (create-pgs-mem))))
    (and (natp 0) (natp 17)
         (equal (car (pgs-dct-example 17 words 40)) :done)
         (equal (cadr (pgs-dct-example 17 words 40))
                (mv-nth 0 (pgs-x-words-digest 0 0 17 mem (create-fn-octets-pg))))))
  :rule-classes nil)

;; A labeled corrupted continuation, distinct from source mutation.
(defthm pgs-dct-corrupted-depth-is-invalid
  (let* ((cursor (pgs-dc-begin 0 0 17 :capture-17 :lease-23 (create-pgs-digest-state)))
         (cursor (update-pgs-dc-mode :return cursor))
         (cursor (update-pgs-dc-depth 65 cursor)))
    (and (equal (mv-nth 0 (pgs-dc-step nil cursor)) :invalid)
         (equal (mv-nth 1 (pgs-dc-step nil cursor)) cursor)))
  :rule-classes nil)

;; Independent streaming driver: input is supplied only on demand. This is
;; proof/test vocabulary over lists, never the disk builder's representation.
(defun pgs-dct-stream-run (fuel words pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :measure (nfix fuel)
                  :guard (natp fuel) :verify-guards nil))
  (if (zp fuel) pgs-digest-state
    (let ((block (if (pgs-dc-needs-block pgs-digest-state)
                     (fn-b3-words 16
                       (pgs-words-le-octets
                         (take 8 (nthcdr (pgs-dc-next-word-offset pgs-digest-state) words))))
                   nil)))
      (mv-let (status pgs-digest-state) (pgs-dc-step block pgs-digest-state)
        (if (eq status :done) pgs-digest-state
          (pgs-dct-stream-run (1- fuel) words pgs-digest-state))))))

(defthm pgs-dct-external-stream-positive
  (let* ((words (append (make-list 128 :initial-element 1)
                        (make-list 128 :initial-element 2)
                        (make-list 8 :initial-element 3)))
         (cursor (pgs-dc-begin 0 0 33 :capture-17 :lease-23 (create-pgs-digest-state)))
         (next (pgs-dct-stream-run 100 words cursor)))
    (and (equal (pgs-dc-mode next) :done)
         (equal (pgs-dc-result next)
                (cadr (pgs-dct-example 33 words 100)))
         (equal (pgs-dc-capture next) :capture-17)
         (equal (pgs-dc-lease next) :lease-23)))
  :rule-classes nil)

(defthm pgs-dct-corrupted-split-power-is-invalid
  (let* ((cursor (pgs-dc-begin 0 0 17 :capture-17 :lease-23 (create-pgs-digest-state)))
         (cursor (update-pgs-dc-mode :split cursor))
         (cursor (update-pgs-dc-power 0 cursor)))
    (and (equal (mv-nth 0 (pgs-dc-step nil cursor)) :invalid)
         (equal (mv-nth 1 (pgs-dc-step nil cursor)) cursor)))
  :rule-classes nil)

(defthm pgs-dct-read-demand-positive
  (let* ((cursor (pgs-dc-begin 0 0 1 :capture-17 :lease-23 (create-pgs-digest-state)))
         (cursor (mv-nth 1 (pgs-dc-step nil cursor))))
    (and (pgs-dc-needs-block cursor)
         (natp (pgs-dc-read-demand cursor))
         (<= (pgs-dc-read-demand cursor) 8)
         (equal (pgs-dc-read-demand cursor) 8)))
  :rule-classes nil)
