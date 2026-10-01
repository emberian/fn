; fn: THE CHECKPOINT RESERVE (design 2026-10-01 "pages are the state", stage
; 7; specs/recovery-refinement.md section 4).  Prefix fn-ckr-.
;
; KeyKOS's rule (Landau, "The checkpoint mechanism in KeyKOS", IWOOOS 1992;
; Hardy, OSR 1985): the checkpoint area is RESERVED at format time, two
; alternating generations, and a checkpoint is FORCED by a dirty-set bound,
; so the system never observes free space to decide whether it may
; checkpoint.  fn's state checkpoint already has both halves of that rule,
; and this book states the first as a theorem about the existing publish
; program:
;
;   The two generations.  The publish program (fn-bs-scp-program: stage,
;   write, fsync, rename over the name, root fsync) holds at most TWO
;   images at any cut: the durable old file under the name and the staged
;   new one.  Each is within the reader's file bound B =
;   fn-sccr-file-read-bound (books/store-checkpoint-reader.lisp; the
;   capture budget fn-ock-capture-budget IS this bound over the profile,
;   books/owner-checkpoint-writer.lisp): the old one because the open
;   refuses a file past B, the new one because the decision plans only an
;   estimate within the budget (fn-ockp-decide) and the estimate is the
;   file's length (fn-ockp-estimate-is-len-file-octets).  KEYSTONE
;   fn-ckr-two-generations-fit-the-reserve-at-every-cut: at every cut state
;   of the program from a quiet store, the octets the two images take
;   through the view (pending writes included) are at most 2 B.  So a
;   FORMAT-TIME reserve of 2 B (fn-ckr-reserve-octets) is enough for every
;   publication the budget admits: the checkpoint never needs unreserved
;   space.
;
;   The forcing bound.  The owner publishes when the suffix since the
;   durable checkpoint reaches K/2 (fn-ock-publication-duep, K the profile's
;   max-open-suffix; books/owner-checkpoint-open.lisp);
;   fn-ock-not-due-keeps-the-checkpoint-open is the theorem that until
;   then a restart is served from the checkpoint.  K is a fast-path
;   threshold, not a maximum suffix (ember, 2026-09-26).
;
;   The decision under a funded reserve, over fn-ockp-decide, and the
;   equality of the reserve with two capture budgets are in
;   books/recovery-refinement-store.lisp (their books reach the node tower;
;   this book's chain stops at the byte model and the reader).
;
; The design's target medium (the page store) sizes a generation by K: the
; dirty pages of at most K commits since the last root.  That bound is the
; open obligation PRF-1215's, beside the page-store instance of the
; recovery refinement; here a generation is the whole-state image bounded
; by B (a function of the profile's history bound, not of K).
;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(in-package "ACL2")
(include-book "byte-store-state-checkpoint-program")
(include-book "store-checkpoint-reader")
(local (include-book "byte-store-invariants"))

; -----------------------------------------------------------------------------
; 1. The reserve: two image generations, each within the reader's bound.

(defun fn-ckr-reserve-octets (max-history-octets max-record-octets)
  (declare (xargs :guard t))
  (* 2 (fn-sccr-file-read-bound max-history-octets max-record-octets)))

; The octets the two checkpoint images take in a store state: the inode
; the name durably holds (OLD-INO, or none) and the staged inode (the next
; inode the program creates), each read through the view (its pending
; writes included: what the file system must hold for it).
(defun fn-ckr-generations-octets (s old-ino new-ino)
  (declare (xargs :guard t :verify-guards nil))
  (+ (if old-ino (len (fn-bs-content s old-ino)) 0)
     (len (fn-bs-content s new-ino))))

; -----------------------------------------------------------------------------
; 2. The keystone over the publish program: every state of the run (the
;    pairs fn-bs-run records after each step, the cuts included) fits.

(defun fn-ckr-all-fit (pairs old-ino new-ino bound)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp pairs)
      (and (<= (fn-ckr-generations-octets (car (car pairs)) old-ino new-ino) (* 2 bound))
           (fn-ckr-all-fit (cdr pairs) old-ino new-ino bound))
    t))

(local (in-theory (enable fn-bs-invariants-vocabulary)))

(local
 (defthm fn-ckr-take-len-bound
   (<= (len (fn-bs-take n x)) (nfix n))
   :rule-classes :linear))

(local
 (defthm fn-ckr-assoc-of-put-assoc-same
   (implies k
            (equal (assoc-equal k (fn-bs-put-assoc k v a)) (cons k v)))
   :hints (("Goal" :in-theory (enable fn-bs-put-assoc)))))
(local
 (defthm fn-ckr-assoc-of-put-assoc-other
   (implies (not (equal k j))
            (equal (assoc-equal k (fn-bs-put-assoc j v a)) (assoc-equal k a)))
   :hints (("Goal" :in-theory (enable fn-bs-put-assoc)))))
(local
 (defthm fn-ckr-nthcdr-of-nil
   (equal (nthcdr n nil) nil)))
(local
 (defthm fn-ckr-take-zero
   (equal (fn-bs-take 0 x) nil)
   :hints (("Goal" :expand ((fn-bs-take 0 x))))))
(local
 (defthm fn-ckr-len-splice-into-empty
   (implies (and (atom old) (zp offset))
            (equal (len (fn-bs-splice old offset octets)) (len octets)))
   :hints (("Goal" :in-theory (enable fn-bs-splice)))))
(defthm fn-ckr-two-generations-fit-the-reserve-at-every-cut
  (implies (and (fn-bs-scp-inputp bs stage old-ino)
                (fn-cbor-octet-listp octets)
                (consp octets)
                (<= (len octets) bound)
                (<= (if old-ino (len (fn-bs-durable-content bs old-ino)) 0) bound))
           (fn-ckr-all-fit (fn-bs-run bs ks (fn-bs-scp-program stage octets) nil groups capacity)
                           old-ino (fn-bs-next-ino bs) bound))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((:free (b k s o) (fn-bs-run b k s o groups capacity)))
           :in-theory (e/d (fn-bs-scp-program fn-bs-scp-inputp fn-ckr-generations-octets
                            fn-ckr-all-fit
                            fn-bs-step fn-bs-create fn-bs-write fn-bs-fsync-file
                            fn-bs-fsync-dir fn-bs-rename fn-bs-fence-file
                            fn-bs-fence-dir fn-bs-lookup fn-bs-view fn-bs-content
                            fn-bs-durable-entry fn-bs-durable-content
                            fn-bs-apply-op fn-bs-apply-ops)
                           (fn-bs-splice fn-bs-put-assoc fn-bs-take)))))

(in-theory (disable fn-ckr-reserve-octets fn-ckr-generations-octets fn-ckr-all-fit))
