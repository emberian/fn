(in-package "ACL2")
(include-book "../../books/pagestore-digest-cursor-refinement")

(defun-nx pgs-dcrt-left-entry ()
  (let ((cursor (pgs-dc-begin 0 0 17 :capture-17 :lease-23 (create-pgs-digest))))
    (mv-nth 1 (pgs-dc-step nil (mv-nth 1 (pgs-dc-step nil cursor))))))

(defthm pgs-dcrt-node-positive
  (let ((cursor (pgs-dcrt-left-entry))
        (msg (pgs-words-le-octets
              (append (make-list 128 :initial-element 1)
                      (make-list 8 :initial-element 2)))))
    (and (equal (pgs-dc-mode cursor) :node)
         (equal (pgs-dc-depth cursor) 1)
         (natp (pgs-dc-start cursor)) (natp (pgs-dc-end cursor))
         (<= (pgs-dc-start cursor) (pgs-dc-end cursor))
         (<= (* 8 (pgs-dc-end cursor)) (len msg))
         (equal (pgs-dcr-denote msg (mv-nth 1 (pgs-dc-step nil cursor)))
                (pgs-dcr-denote msg cursor))))
  :hints (("Goal" :in-theory (enable pgs-dcr-denote pgs-dcr-current pgs-dcr-parent
                                              pgs-dcr-span pgs-dcrt-left-entry)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 1 out msg cursor))
                           (:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
  :rule-classes nil)

(defthm pgs-dcrt-chunk-positive
  (let* ((cursor (mv-nth 1 (pgs-dc-step nil (pgs-dcrt-left-entry))))
         (msg (pgs-words-le-octets
                (append (make-list 128 :initial-element 1)
                        (make-list 8 :initial-element 2))))
         (block (fn-b3-words 16 (pgs-dcr-span (pgs-dc-pos cursor) (pgs-dc-end cursor) msg))))
    (and (equal (pgs-dc-mode cursor) :chunk)
         (equal (pgs-dc-depth cursor) 1)
         (natp (pgs-dc-start cursor)) (natp (pgs-dc-pos cursor)) (natp (pgs-dc-end cursor))
         (<= (pgs-dc-start cursor) (pgs-dc-pos cursor))
         (<= (pgs-dc-pos cursor) (pgs-dc-end cursor))
         (<= (* 8 (pgs-dc-end cursor)) (len msg))
         (true-listp (pgs-dc-cv cursor)) (equal (len (pgs-dc-cv cursor)) 8)
         (equal block (fn-b3-words 16 (pgs-dcr-span (pgs-dc-pos cursor) (pgs-dc-end cursor) msg)))
         (equal (pgs-dcr-denote msg (mv-nth 1 (pgs-dc-step block cursor)))
                (pgs-dcr-denote msg cursor))))
  :hints (("Goal" :in-theory (enable pgs-dcr-denote pgs-dcr-current pgs-dcr-parent
                                              pgs-dcr-span pgs-dcrt-left-entry)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 1 out msg cursor))
                           (:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
  :rule-classes nil)

;; Literal matching-block removal: valid reachable nonempty chunk state;
;; every retained antecedent affirmed, omitted antecedent and conclusion fail.
(defthm pgs-dcrt-chunk-block-removal
  (let* ((cursor (mv-nth 1 (pgs-dc-step nil
                   (pgs-dc-begin 0 0 1 :capture-17 :lease-23 (create-pgs-digest)))))
         (msg (pgs-words-le-octets (make-list 8 :initial-element 1)))
         (block nil))
    (and (equal (pgs-dc-mode cursor) :chunk)
         (natp (pgs-dc-start cursor)) (natp (pgs-dc-pos cursor)) (natp (pgs-dc-end cursor))
         (<= (pgs-dc-start cursor) (pgs-dc-pos cursor))
         (<= (pgs-dc-pos cursor) (pgs-dc-end cursor))
         (<= (* 8 (pgs-dc-end cursor)) (len msg))
         (true-listp (pgs-dc-cv cursor)) (equal (len (pgs-dc-cv cursor)) 8)
         (not (equal block (fn-b3-words 16 (pgs-dcr-span (pgs-dc-pos cursor) (pgs-dc-end cursor) msg))))
         (not (equal (pgs-dcr-denote msg (mv-nth 1 (pgs-dc-step block cursor)))
                     (pgs-dcr-denote msg cursor)))))
  :hints (("Goal" :in-theory (enable pgs-dcr-denote pgs-dcr-current pgs-dcr-parent
                                              pgs-dcr-span pgs-dcrt-left-entry)
                  :expand ((:free (out msg cursor) (pgs-dcr-fold 1 out msg cursor))
                           (:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
  :rule-classes nil)

;; Ground test driver only; no served path loops or materializes MSG.
(defun-nx pgs-dcrt-until (mode fuel msg pgs-digest)
  (declare (xargs :stobjs pgs-digest :measure (nfix fuel)
                  :verify-guards nil))
  (if (or (zp fuel) (eq mode (pgs-dc-mode pgs-digest))) pgs-digest
    (mv-let (status pgs-digest)
      (pgs-dc-step
         (fn-b3-words 16 (pgs-dcr-span (pgs-dc-pos pgs-digest) (pgs-dc-end pgs-digest) msg))
         pgs-digest)
      (declare (ignore status))
      (pgs-dcrt-until mode (1- fuel) msg pgs-digest))))

(defthm pgs-dcrt-terminal-positive
  (let* ((base 0) (nb 1)
         (words (make-list 8 :initial-element 1))
         (mem (update-nth *pgs-wi* words (create-pgs-mem)))
         (msg (pgs-words-le-octets (take (* 8 nb) (nthcdr base (pgs-x-arr 0 mem)))))
         (cursor (pgs-dcrt-until :root 8 msg
                   (pgs-dc-begin 0 base nb :capture-17 :lease-23 (create-pgs-digest)))))
    (and (natp base) (natp nb)
         (equal (pgs-dc-mode cursor) :root) (equal (pgs-dc-depth cursor) 0)
         (equal (pgs-dcr-denote msg cursor)
                (pgs-dcr-denote msg (pgs-dc-begin 0 base nb :capture-17 :lease-23 cursor)))
         (equal (pgs-dc-result (mv-nth 1 (pgs-dc-step nil cursor)))
                (mv-nth 0 (pgs-x-words-digest 0 base nb mem (create-fn-octets-pg))))))
  :hints (("Goal" :in-theory (enable pgs-dcrt-until pgs-dcr-span pgs-dcr-current pgs-dcr-denote pgs-dcr-parent)
                  :expand ((:free (mode fuel msg cursor) (pgs-dcrt-until mode fuel msg cursor))
                           (:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
  :rule-classes nil)

;; Literal semantic-carry removal: all other terminal hypotheses hold;
;; the omitted captured-source equality and the actual conclusion fail.
(defthm pgs-dcrt-terminal-carry-removal
  (let* ((base 0) (nb 1)
         (words (make-list 8 :initial-element 1))
         (mem (update-nth *pgs-wi* (make-list 8 :initial-element 2) (create-pgs-mem)))
         (msg (pgs-words-le-octets (take (* 8 nb) (nthcdr base (pgs-x-arr 0 mem)))))
         (cursor (pgs-dcrt-until :root 8 (pgs-words-le-octets words)
                   (pgs-dc-begin 0 base nb :capture-17 :lease-23 (create-pgs-digest)))))
    (and (natp base) (natp nb)
         (equal (pgs-dc-mode cursor) :root) (equal (pgs-dc-depth cursor) 0)
         (not (equal (pgs-dcr-denote msg cursor)
                     (pgs-dcr-denote msg (pgs-dc-begin 0 base nb :capture-17 :lease-23 cursor))))
         (not (equal (pgs-dc-result (mv-nth 1 (pgs-dc-step nil cursor)))
                     (mv-nth 0 (pgs-x-words-digest 0 base nb mem (create-fn-octets-pg)))))))
  :hints (("Goal" :in-theory (enable pgs-dcrt-until pgs-dcr-span pgs-dcr-current pgs-dcr-denote pgs-dcr-parent)
                  :expand ((:free (mode fuel msg cursor) (pgs-dcrt-until mode fuel msg cursor))
                           (:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
  :rule-classes nil)

;; Corrupted output descriptor, separately labelled from hypothesis removal.
(defthm pgs-dcrt-terminal-output-mutation
  (let* ((base 0) (nb 1)
         (mem (update-nth *pgs-wi* (make-list 8 :initial-element 1) (create-pgs-mem)))
         (msg (pgs-words-le-octets (take (* 8 nb) (nthcdr base (pgs-x-arr 0 mem)))))
         (good (pgs-dcrt-until :root 8 msg
                 (pgs-dc-begin 0 base nb :capture-17 :lease-23 (create-pgs-digest))))
         (cursor (update-pgs-dc-output nil good)))
    (and (natp base) (natp nb)
         (equal (pgs-dc-mode cursor) :root) (equal (pgs-dc-depth cursor) 0)
         (not (equal (pgs-dcr-denote msg cursor)
                     (pgs-dcr-denote msg (pgs-dc-begin 0 base nb :capture-17 :lease-23 cursor))))
         (not (equal (pgs-dc-result (mv-nth 1 (pgs-dc-step nil cursor)))
                     (mv-nth 0 (pgs-x-words-digest 0 base nb mem (create-fn-octets-pg)))))))
  :hints (("Goal" :in-theory (enable pgs-dcrt-until pgs-dcr-span pgs-dcr-current pgs-dcr-denote pgs-dcr-parent)
                  :expand ((:free (mode fuel msg cursor) (pgs-dcrt-until mode fuel msg cursor))
                           (:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
  :rule-classes nil)
