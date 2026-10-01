; fn: THE CONCURRENT CRASH POINT: the log relation R lifted to the segment's
; own pending operations, and the checkpoint publication's cuts with a batch
; in flight (lane recovery-refinement-2, 2026-10-01; PRF-1214;
; specs/recovery-refinement.md section 5).  Prefix fn-rrc-.
;
; R (fn-lgk-relp, books/store-log-kernel.lisp) names the segment's one write
; as the ONLY pending operation of the store.  The owner's publication thread
; writes the staged checkpoint off the mutex (STO-024) while a batch may be
; in flight, so a crash inside it has two pending sets: outside R.  The byte
; model orders nothing across inodes (fn-bs-crash-select tears each write by
; its own selectors; an entry operation touches no inode), so a crash image's
; content at the segment depends on the segment's own pending writes and
; their choices alone.  That is THE PROJECTION (section 2): the image's
; segment content is the segment content of the image of the PROJECTED store
; (the store whose pending list is the segment's own operations) under the
; projected choices.  The lifted relation fn-rrc-relp (section 1) is R with
; fn-bs-ops-for-ino in place of the whole pending list; the kernel's R
; implies it, and the projected store of a lifted-related store is related
; in the kernel's sense, so every theorem of books/recovery-refinement.lisp
; transfers (section 3): THE KEYSTONE over the lifted relation,
; fn-rrc-recovery-refines-a-prefix-with-every-acknowledged-record, the same
; statement as PRF-1212's with fn-rrc-relp for fn-lgk-relp.
;
; Section 4 is the concurrent half of PRF-1216: from a related state with a
; batch in flight (the kernel's R at log-written), every state of
; fn-bs-scp-program keeps the segment's content and its pending operations
; (the program creates, writes and fences the staged inode, renames it and
; fences the root: no segment octet, no segment write), so every state is
; lifted-related and every crash image of every one of the five cuts is
; covered by the keystone:
; fn-rrc-checkpoint-crash-point-refines-with-a-batch-in-flight.  The
; same route covers any program whose run keeps the segment
; (fn-rrc-keeping-the-segment-keeps-the-lifted-relation: a state that
; keeps the segment's presence, content, unit and own pending operations
; of a lifted-related state is lifted-related); the keep-the-segment
; proofs for the cut table's other programs (finish, stage cleanup, the
; segment rotation and drop, import, export, init) are owed under
; PRF-1221, and the spec's table says which rows cite what.
;
; What the host runs: host/native/io.lisp fnn-state-checkpoint-write (the
; publication, off the owner mutex) while fnn-log-append may hold a batch at
; log-written; the open after the crash is fnn-recover-log (MODEL-LEVEL as
; PRF-1212 records).
;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(in-package "ACL2")
(include-book "recovery-refinement")
(local (include-book "byte-store-invariants"))

; -----------------------------------------------------------------------------
; 1. The lifted relation: R over the segment's own pending operations.

(defun fn-rrc-relp (bs ks ino genesis max)
  (declare (xargs :guard t :verify-guards nil))
  (let ((unit (fn-bs-unit bs)))
    (and (posp unit) ino
         (assoc-equal ino (fn-bs-inodes bs))
         (fn-lgk-content-okp (fn-bs-durable-content bs ino) ks unit genesis max)
         (equal (fn-bs-ops-for-ino (fn-bs-pending bs) ino)
                (if (consp (fn-lgk-inflight ks))
                    (list (list :write ino (fn-lgk-frontier ks)
                                (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks) unit)))
                  nil)))))

; The kernel's R implies the lifted one: the segment's operations among the
; one write to it are that write, among none are none.
(defthm fn-lgk-relp-implies-fn-rrc-relp
  (implies (fn-lgk-relp bs ks ino genesis max)
           (fn-rrc-relp bs ks ino genesis max))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lgk-relp fn-rrc-relp fn-bs-ops-for-ino)
                           (fn-lgk-content-okp fn-lg-log fn-bs-durable-content
                            fn-lgk-inflight fn-lgk-frontier fn-lgk-last)))))

; -----------------------------------------------------------------------------
; 2. The projection.

; The store whose pending list is the segment's own operations.
(defun fn-rrc-project (bs ino)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-make (fn-bs-unit bs) (fn-bs-inodes bs) (fn-bs-dirs bs)
              (fn-bs-ops-for-ino (fn-bs-pending bs) ino) (fn-bs-next-ino bs)))

; The choices for the segment's operations, read off the choices for the
; whole pending list (parallel to it; a missing choice is conservative
; loss, so an exhausted choice list projects to none).
(defun fn-rrc-choices-for-ino (ops choices ino)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((atom ops) nil)
        ((atom choices) nil)
        ((and (equal (car (car ops)) :write) (equal (nth 1 (car ops)) ino))
         (cons (car choices) (fn-rrc-choices-for-ino (cdr ops) (cdr choices) ino)))
        (t (fn-rrc-choices-for-ino (cdr ops) (cdr choices) ino))))

(local
 (defthm fn-rrc-crash-select-of-no-choices
   (implies (not (consp choices))
            (equal (fn-bs-crash-select ops choices unit) nil))
   :hints (("Goal" :induct (fn-bs-crash-select ops choices unit)
            :in-theory (enable fn-bs-crash-select fn-bs-tear-write)))))

(local
 (defthm fn-rrc-ops-for-ino-of-tear-write-same
   (implies (equal (nth 1 op) ino)
            (equal (fn-bs-ops-for-ino (fn-bs-tear-write op sels i unit) ino)
                   (fn-bs-tear-write op sels i unit)))
   :hints (("Goal" :induct (fn-bs-tear-write op sels i unit)
            :in-theory (enable fn-bs-tear-write fn-bs-ops-for-ino)))))

(local
 (defthm fn-rrc-tear-write-of-no-selectors
   (implies (not (consp sels))
            (equal (fn-bs-tear-write op sels i unit) nil))
   :hints (("Goal" :expand ((fn-bs-tear-write op sels i unit))))))

; The selected operations for the segment are the selection over the
; segment's operations under the projected choices.
(local
 (defthm fn-rrc-ops-for-ino-of-crash-select
   (equal (fn-bs-ops-for-ino (fn-bs-crash-select ops choices unit) ino)
          (fn-bs-crash-select (fn-bs-ops-for-ino ops ino)
                              (fn-rrc-choices-for-ino ops choices ino) unit))
   :hints (("Goal" :induct (fn-bs-crash-select ops choices unit)
            :in-theory (e/d (fn-bs-crash-select fn-bs-ops-for-ino fn-rrc-choices-for-ino
                             fn-bs-ops-for-ino-of-append
                             fn-bs-tear-write-has-no-writes-for-other
                             fn-rrc-tear-write-of-no-selectors
                             fn-rrc-ops-for-ino-of-tear-write-same)
                            (fn-bs-tear-write))))))

; The projected choices are admissible when the whole list's are.
(local
 (defthm fn-rrc-choicesp-of-projection
   (implies (fn-bs-crash-choicesp choices ops unit)
            (fn-bs-crash-choicesp (fn-rrc-choices-for-ino ops choices ino)
                                  (fn-bs-ops-for-ino ops ino) unit))
   :hints (("Goal" :induct (fn-rrc-choices-for-ino ops choices ino)
            :in-theory (e/d (fn-bs-crash-choicesp fn-bs-ops-for-ino fn-rrc-choices-for-ino)
                            (fn-bs-crash-choicep))))))

; The content of one inode after a write list: its own writes spliced in order.
(local
 (defun fn-rrc-content-after (content ops ino)
   (cond ((atom ops) content)
         ((and (equal (car (car ops)) :write) (equal (nth 1 (car ops)) ino))
          (fn-rrc-content-after (fn-bs-splice content (nth 2 (car ops)) (nth 3 (car ops)))
                                (cdr ops) ino))
         (t (fn-rrc-content-after content (cdr ops) ino)))))

(local
 (defthm fn-rrc-assoc-of-put-assoc-same
   (implies k
            (equal (assoc-equal k (fn-bs-put-assoc k v a)) (cons k v)))
   :hints (("Goal" :in-theory (enable fn-bs-put-assoc)))))
(local
 (defthm fn-rrc-assoc-of-put-assoc-other
   (implies (not (equal k j))
            (equal (assoc-equal k (fn-bs-put-assoc j v a)) (assoc-equal k a)))
   :hints (("Goal" :in-theory (enable fn-bs-put-assoc)))))

(local
 (defthm fn-rrc-content-of-apply-writes
   (implies ino
            (equal (cdr (assoc-equal ino (fn-bs-apply-writes inodes ops)))
                   (fn-rrc-content-after (cdr (assoc-equal ino inodes)) ops ino)))
   :rule-classes nil
   :hints (("Goal" :induct (fn-bs-apply-writes inodes ops)
            :in-theory (e/d (fn-bs-apply-writes fn-rrc-content-after)
                            (fn-bs-splice fn-bs-put-assoc))))))

(local
 (defthm fn-rrc-content-after-of-own-ops
   (equal (fn-rrc-content-after content (fn-bs-ops-for-ino ops ino) ino)
          (fn-rrc-content-after content ops ino))
   :hints (("Goal" :induct (fn-rrc-content-after content ops ino)
            :in-theory (e/d (fn-rrc-content-after fn-bs-ops-for-ino) (fn-bs-splice))))))

; THE PROJECTION: a crash image's content at an inode is the content of the
; projected store's image under the projected choices.
(defthm fn-rrc-crash-content-is-the-projected-crash-content
  (implies ino
           (equal (fn-bs-durable-content (fn-bs-crash bs choices) ino)
                  (fn-bs-durable-content
                   (fn-bs-crash (fn-rrc-project bs ino)
                                (fn-rrc-choices-for-ino (fn-bs-pending bs) choices ino))
                   ino)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-rrc-content-of-apply-writes
                            (inodes (fn-bs-inodes bs))
                            (ops (fn-bs-crash-select (fn-bs-pending bs) choices (fn-bs-unit bs))))
                 (:instance fn-rrc-content-of-apply-writes
                            (inodes (fn-bs-inodes bs))
                            (ops (fn-bs-crash-select
                                  (fn-bs-ops-for-ino (fn-bs-pending bs) ino)
                                  (fn-rrc-choices-for-ino (fn-bs-pending bs) choices ino)
                                  (fn-bs-unit bs))))
                 (:instance fn-rrc-content-after-of-own-ops
                            (content (cdr (assoc-equal ino (fn-bs-inodes bs))))
                            (ops (fn-bs-crash-select (fn-bs-pending bs) choices (fn-bs-unit bs)))))
           :in-theory (e/d (fn-bs-crash fn-bs-durable-content fn-rrc-project fn-bs-make
                            fn-bs-unit fn-bs-inodes fn-bs-dirs fn-bs-pending fn-bs-next-ino
                            fn-bs-apply-ops-inodes-are-apply-writes
                            fn-rrc-ops-for-ino-of-crash-select)
                           (fn-bs-crash-select fn-bs-apply-writes fn-bs-apply-ops
                            fn-bs-ops-for-ino fn-rrc-choices-for-ino fn-rrc-content-after
                            fn-rrc-content-after-of-own-ops)))))

; -----------------------------------------------------------------------------
; 3. The transfer: the projected store of a lifted-related store is related,
;    its projected image is admissible with the same segment content, so the
;    generic book's theorems hold over the lifted relation.

(defthm fn-rrc-projection-is-related
  (implies (fn-rrc-relp bs ks ino genesis max)
           (fn-lgk-relp (fn-rrc-project bs ino) ks ino genesis max))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-rrc-relp fn-lgk-relp fn-rrc-project fn-bs-make
                            fn-bs-unit fn-bs-inodes fn-bs-dirs fn-bs-pending fn-bs-next-ino
                            fn-bs-durable-content)
                           (fn-lgk-content-okp fn-lg-log fn-bs-ops-for-ino
                            fn-lgk-inflight fn-lgk-frontier fn-lgk-last)))))

; The projected image of an admissible image: admissible for the projected
; store, with the same segment content.
(defun fn-rrc-projected-image (bs image ino)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-crash (fn-rrc-project bs ino)
               (fn-rrc-choices-for-ino (fn-bs-pending bs) (fn-bs-crash-imagep-witness bs image) ino)))

(defthm fn-rrc-projected-image-is-admissible-with-the-same-segment
  (implies (and ino (fn-bs-crash-imagep bs image))
           (and (fn-bs-crash-imagep (fn-rrc-project bs ino) (fn-rrc-projected-image bs image ino))
                (equal (fn-bs-durable-content (fn-rrc-projected-image bs image ino) ino)
                       (fn-bs-durable-content image ino))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-crash-imagep-suff
                            (s (fn-rrc-project bs ino))
                            (image (fn-rrc-projected-image bs image ino))
                            (choices (fn-rrc-choices-for-ino
                                      (fn-bs-pending bs) (fn-bs-crash-imagep-witness bs image) ino)))
                 (:instance fn-rrc-choicesp-of-projection
                            (ops (fn-bs-pending bs)) (choices (fn-bs-crash-imagep-witness bs image))
                            (unit (fn-bs-unit bs)))
                 (:instance fn-rrc-crash-content-is-the-projected-crash-content
                            (choices (fn-bs-crash-imagep-witness bs image))))
           :in-theory (e/d (fn-bs-crash-imagep fn-rrc-projected-image fn-rrc-project fn-bs-make
                            fn-bs-unit fn-bs-inodes fn-bs-dirs fn-bs-pending fn-bs-next-ino)
                           (fn-bs-crash fn-bs-crash-choicesp fn-bs-ops-for-ino
                            fn-rrc-choices-for-ino fn-bs-durable-content
                            fn-bs-crash-imagep-suff)))))

(local
 (defthm fn-rrc-relp-gives-ino
   (implies (fn-rrc-relp bs ks ino genesis max) ino)
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-rrc-relp) (fn-lgk-content-okp fn-lg-log))))))

; The log's half over the lifted relation.
(defthm fn-rrc-log-crash-image-recovers-a-tree-sequence-member
  (implies (and (fn-rrc-relp bs ks ino genesis max)
                (fn-bs-crash-imagep bs image)
                (fn-lg-platform-tears-p
                 (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content image ino))
                 (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs)))
           (fn-rr-tree-sequence-memberp
            (fn-rr-recovered-records image ino genesis (fn-bs-unit bs) max next-txid)
            (fn-lgk-committed ks) (fn-lgk-inflight ks)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-rr-log-crash-image-recovers-a-tree-sequence-member
                            (bs (fn-rrc-project bs ino))
                            (image (fn-rrc-projected-image bs image ino)))
                 (:instance fn-rrc-projected-image-is-admissible-with-the-same-segment)
                 (:instance fn-rrc-projection-is-related)
                 (:instance fn-rrc-relp-gives-ino))
           :in-theory (e/d (fn-rr-recovered-records fn-rrc-project fn-bs-make fn-bs-unit)
                           (fn-rrc-projected-image fn-rrc-relp fn-lgk-relp fn-bs-crash-imagep
                            fn-bs-durable-content fn-rr-tree-sequence-memberp
                            fn-lg-platform-tears-p fn-lgk-recover fn-lgk-committed
                            fn-lgk-frontier fn-lgk-inflight fn-lgk-last
                            fn-bs-crash fn-bs-inodes fn-bs-dirs fn-bs-pending fn-bs-next-ino
                            fn-bs-ops-for-ino fn-rrc-projection-is-related)))))

; THE KEYSTONE over the lifted relation: PRF-1212's statement with
; fn-rrc-relp for fn-lgk-relp.  Every crash point the kernel's R covers is
; covered (fn-lgk-relp-implies-fn-rrc-relp), and so is every state where
; other inodes have pending operations beside the segment's write.
(local
 (defthm fn-rrc-holds-across-equal
   (implies (and (equal a (fn-rr-medium-full-open configs frontier records))
                 (member-equal r records)
                 (fn-rr-medium-open-okp a))
            (fn-rr-medium-holds a r))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-rr-medium-full-open-holds-its-records))))))
(local
 (defthm fn-rrc-take-of-append-within
   (implies (and (natp s) (<= s (len a)))
            (equal (take s (append a b)) (take s a)))
   :hints (("Goal" :induct (take s a)))))
(defthm fn-rrc-recovery-refines-a-prefix-with-every-acknowledged-record
  (let ((recovered (fn-rr-recovered-records image ino genesis (fn-bs-unit bs) max next-txid)))
    (implies (and (fn-rrc-relp bs ks ino genesis max)
                  (fn-bs-crash-imagep bs image)
                  (fn-lg-platform-tears-p
                   (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content image ino))
                   (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs))
                  (natp s)
                  (<= s (len (fn-lgk-committed ks)))
                  (equal ckpt (fn-rr-medium-capture configs (take s (fn-lgk-committed ks)))))
             (and (fn-rr-tree-sequence-memberp recovered (fn-lgk-committed ks)
                                               (fn-lgk-inflight ks))
                  (equal (fn-rr-open status s ckpt configs frontier recovered k)
                         (fn-rr-medium-full-open configs frontier recovered))
                  (implies (member-equal r (take (fn-lgk-acked ks) (fn-lgk-committed ks)))
                           (and (member-equal r recovered)
                                (implies (fn-rr-medium-open-okp
                                          (fn-rr-open status s ckpt configs frontier recovered k))
                                         (fn-rr-medium-holds
                                          (fn-rr-open status s ckpt configs frontier recovered k)
                                          r)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-rrc-log-crash-image-recovers-a-tree-sequence-member)
                 (:instance fn-rr-acknowledged-record-is-in-every-tree-sequence-member
                            (bs (fn-rrc-project bs ino))
                            (recovered (fn-rr-recovered-records image ino genesis (fn-bs-unit bs)
                                                                max next-txid))
                            (inflight (fn-lgk-inflight ks)))
                 (:instance fn-rrc-projection-is-related)
                 (:instance fn-rr-open-is-the-full-open-of-the-recovered-records
                            (records (fn-rr-recovered-records image ino genesis (fn-bs-unit bs)
                                                              max next-txid)))
                 (:instance fn-rrc-holds-across-equal
                            (a (fn-rr-open status s ckpt configs frontier
                                           (fn-rr-recovered-records image ino genesis (fn-bs-unit bs)
                                                                    max next-txid)
                                           k))
                            (records (fn-rr-recovered-records image ino genesis (fn-bs-unit bs)
                                                              max next-txid)))
                 (:instance fn-rrc-take-of-append-within
                            (a (fn-lgk-committed ks))
                            (b (nthcdr (len (fn-lgk-committed ks))
                                       (fn-rr-recovered-records image ino genesis (fn-bs-unit bs)
                                                                max next-txid)))))
           :in-theory (union-theories '(fn-rr-tree-sequence-memberp)
                                      (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; 4. The checkpoint publication with a batch in flight (the concurrent half
;    of PRF-1216).  The publication's input: fn-bs-scp-inputp without its
;    quiet conjunct (the segment's write may be pending).

(defun fn-rrc-scp-inputp (bs stage old-ino)
  (declare (xargs :guard t :verify-guards nil))
  (and (stringp stage)
       (natp (fn-bs-next-ino bs))
       (or (null old-ino)
           (and (natp old-ino) (< old-ino (fn-bs-next-ino bs))))
       (equal (fn-bs-durable-entry bs :root *fn-bs-state-checkpoint-name*) old-ino)
       (not (fn-bs-lookup bs :staging stage))))

; The pending list a related state has: nothing, or the segment's one write.
(defun fn-rrc-segment-write-onlyp (pending ino)
  (declare (xargs :guard t :verify-guards nil))
  (or (null pending)
      (and (consp pending) (null (cdr pending))
           (equal (car (car pending)) :write)
           (equal (nth 1 (car pending)) ino))))

; Every state of a run keeps the segment: present, its durable content, the
; unit and its own pending operations unchanged.
(defun fn-rrc-all-keep-segment (pairs bs ino)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp pairs)
      (and (assoc-equal ino (fn-bs-inodes (car (car pairs))))
           (equal (fn-bs-durable-content (car (car pairs)) ino) (fn-bs-durable-content bs ino))
           (equal (fn-bs-unit (car (car pairs))) (fn-bs-unit bs))
           (equal (fn-bs-ops-for-ino (fn-bs-pending (car (car pairs))) ino)
                  (fn-bs-ops-for-ino (fn-bs-pending bs) ino))
           (fn-rrc-all-keep-segment (cdr pairs) bs ino))
    t))

(local
 (defthm fn-rrc-scp-run-keeps-the-segment
   (implies (and (fn-rrc-scp-inputp bs stage old-ino)
                 (fn-rrc-segment-write-onlyp (fn-bs-pending bs) ino)
                 (natp ino) (< ino (fn-bs-next-ino bs))
                 (assoc-equal ino (fn-bs-inodes bs)))
            (fn-rrc-all-keep-segment (fn-bs-run bs ks (fn-bs-scp-program stage octets)
                                                nil groups capacity)
                                     bs ino))
   :hints (("Goal" :do-not-induct t
            :expand ((:free (b k s o) (fn-bs-run b k s o groups capacity)))
            :in-theory (e/d (fn-bs-scp-program fn-rrc-scp-inputp fn-rrc-segment-write-onlyp
                             fn-rrc-all-keep-segment
                             fn-bs-step fn-bs-create fn-bs-write fn-bs-fsync-file
                             fn-bs-fsync-dir fn-bs-rename fn-bs-fence-file
                             fn-bs-fence-dir fn-bs-lookup fn-bs-view
                             fn-bs-durable-entry fn-bs-durable-content
                             fn-bs-ops-for-ino fn-bs-ops-not-for-ino
                             fn-bs-ops-for-dir fn-bs-ops-not-for-dir
                             fn-bs-apply-op fn-bs-apply-ops)
                            (fn-bs-splice fn-bs-put-assoc))))))

(local
 (defthm fn-rrc-all-keep-segment-member
   (implies (and (fn-rrc-all-keep-segment pairs bs ino) (member-equal p pairs))
            (and (assoc-equal ino (fn-bs-inodes (car p)))
                 (equal (fn-bs-durable-content (car p) ino) (fn-bs-durable-content bs ino))
                 (equal (fn-bs-unit (car p)) (fn-bs-unit bs))
                 (equal (fn-bs-ops-for-ino (fn-bs-pending (car p)) ino)
                        (fn-bs-ops-for-ino (fn-bs-pending bs) ino))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-rrc-all-keep-segment)
                                   (fn-bs-durable-content fn-bs-ops-for-ino))))))

; A state that keeps the segment (content, unit, presence, own pending
; operations) of a lifted-related state is lifted-related.
(defthm fn-rrc-keeping-the-segment-keeps-the-lifted-relation
  (implies (and (fn-rrc-relp bs ks ino genesis max)
                (assoc-equal ino (fn-bs-inodes bs2))
                (equal (fn-bs-durable-content bs2 ino) (fn-bs-durable-content bs ino))
                (equal (fn-bs-unit bs2) (fn-bs-unit bs))
                (equal (fn-bs-ops-for-ino (fn-bs-pending bs2) ino)
                       (fn-bs-ops-for-ino (fn-bs-pending bs) ino)))
           (fn-rrc-relp bs2 ks ino genesis max))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-rrc-relp)
                           (fn-lgk-content-okp fn-lg-log fn-bs-ops-for-ino fn-bs-durable-content
                            fn-lgk-inflight fn-lgk-frontier fn-lgk-last fn-bs-unit
                            fn-bs-inodes fn-bs-pending)))))

(local
 (defthm fn-rrc-relp-pending-shape-and-presence
   (implies (fn-lgk-relp bs ks ino genesis max)
            (and (fn-rrc-segment-write-onlyp (fn-bs-pending bs) ino)
                 (assoc-equal ino (fn-bs-inodes bs))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-lgk-relp fn-rrc-segment-write-onlyp)
                                   (fn-lgk-content-okp fn-lg-log fn-bs-durable-content
                                    fn-lgk-inflight fn-lgk-frontier fn-lgk-last))))))

; THE CONCURRENT CUTS: from a related state (the kernel's R; a batch may be
; in flight), at every state of the publication's run and for every
; admissible crash image of it, the keystone's conclusions.
(defthm fn-rrc-checkpoint-crash-point-refines-with-a-batch-in-flight
  (let ((recovered (fn-rr-recovered-records image ino genesis (fn-bs-unit bs) max next-txid)))
    (implies (and (fn-lgk-relp bs ks ino genesis max)
                  (fn-rrc-scp-inputp bs stage old-ino)
                  (natp ino) (< ino (fn-bs-next-ino bs))
                  (member-equal p (fn-bs-run bs ks2 (fn-bs-scp-program stage octets)
                                             nil groups capacity))
                  (fn-bs-crash-imagep (car p) image)
                  (fn-lg-platform-tears-p
                   (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content image ino))
                   (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs))
                  (natp s)
                  (<= s (len (fn-lgk-committed ks)))
                  (equal ckpt (fn-rr-medium-capture configs (take s (fn-lgk-committed ks)))))
             (and (fn-rr-tree-sequence-memberp recovered (fn-lgk-committed ks)
                                               (fn-lgk-inflight ks))
                  (equal (fn-rr-open status s ckpt configs frontier recovered k)
                         (fn-rr-medium-full-open configs frontier recovered))
                  (implies (member-equal r (take (fn-lgk-acked ks) (fn-lgk-committed ks)))
                           (and (member-equal r recovered)
                                (implies (fn-rr-medium-open-okp
                                          (fn-rr-open status s ckpt configs frontier recovered k))
                                         (fn-rr-medium-holds
                                          (fn-rr-open status s ckpt configs frontier recovered k)
                                          r)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-rrc-relp-pending-shape-and-presence)
                 (:instance fn-rrc-scp-run-keeps-the-segment (ks ks2))
                 (:instance fn-rrc-all-keep-segment-member
                            (pairs (fn-bs-run bs ks2 (fn-bs-scp-program stage octets)
                                              nil groups capacity)))
                 (:instance fn-lgk-relp-implies-fn-rrc-relp)
                 (:instance fn-rrc-keeping-the-segment-keeps-the-lifted-relation (bs2 (car p)))
                 (:instance fn-rrc-recovery-refines-a-prefix-with-every-acknowledged-record
                            (bs (car p))))
           :in-theory (union-theories '(fn-rr-recovered-records)
                                      (theory 'minimal-theory)))))

(in-theory (disable fn-rrc-relp fn-rrc-project fn-rrc-choices-for-ino fn-rrc-projected-image
                    fn-rrc-scp-inputp fn-rrc-segment-write-onlyp fn-rrc-all-keep-segment))
