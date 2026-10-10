; fn: the charged-totals header (Builder A, lane vertical, 2026-10-10;
; statement packet build/vertical-runs/ct2/packet-v31.md, Codex rounds 1-4
; in build/vertical-runs/codex/review-ct2/).
;
; The checkpoint file is the history image region, then a HEADER RUN H --
; one segment, the tree encoding of (SCHEMA S TOT), TOT the charged fold of
; the S records the checkpoint covers (books/charged-totals.lisp
; fn-ct-charged, Builder M's K-TOTALS fold) -- then the arena run A and the
; tables F, P, E, R (books/store-checkpoint-arena.lisp,
; store-checkpoint-tables.lisp), all framed and chained alike.  The reader
; admits H alone under one segment's framing, decodes TOT, and admits the
; rest under M's load bound at TOT and the configuration's octets
; (books/memory-model.lisp fn-mm-checkpoint-load-octets) with H's octets
; carried; the unchanged loader reads the file after H.  The writer counts H
; in its publication decision and admits every segment it writes with the
; reader's own admission (books/store-checkpoint-reader.lisp
; fn-sccr-admit-segment), the running total starting at H's octets.
;
; KEYSTONES (each the packet's statement verbatim, :rule-classes nil)
;   K1  fn-cth-header-decodes-to-the-charged-totals
;   K1w fn-cth-header-of-capture-is-well-formed
;   K2  fn-cth-header-plus-suffix-is-the-open
;   K3  fn-cth-installed-seed-is-valid
;   K4  fn-cth-header-rowp-rejects-the-malformed
;   K4b fn-cth-read-file-refuses-another-schema-by-name
;   K5  fn-cth-read-file-is-within-the-load-bound
;   K5b fn-cth-read-prefix-is-within-the-load-bound
;   K6  fn-cth-segment-is-within-every-load-bound
;   K7  fn-cth-reader-reads-the-admitted-file
;   K8  fn-cth-publication-setup-counts-the-header
;   K8c fn-cth-admit-run-of-append
;   K9  fn-cth-seed-of-one-capture-is-valid
;   K10 fn-cth-header-run-is-one-segment
; Stated in the packet, owed in this book: K8a fn-cth-arena-write-is-admitted
; and K8t fn-cth-table-write-is-admitted (the writer runs' admission from a
; carried total).

(in-package "ACL2")
(include-book "memory-model")
(include-book "history-totals-carried")
(include-book "store-checkpoint-tables")
(include-book "store-checkpoint-open")
(include-book "store-checkpoint-arena-writer")
(include-book "owner-checkpoint-pipeline")

; ---------------------------------------------------------------------------
; Definitions (the packet's, as reviewed).

; The header row: the codec's schema, S (the records the checkpoint covers)
; and TOT, their charged fold (books/charged-totals.lisp fn-ct-charged,
; Builder M's K-TOTALS fold) at the owner's residency.
(defun fn-cth-header-row (s tot)
  (declare (xargs :guard t))
  (list *fn-scc-schema* s tot))

; A well-formed header row: this schema, S a natural, TOT a tot whose RECORDS
; is S.  No numeric ceiling of its own; the tree codec's (naturals below
; 2^2040, fn-scc-treep) is a premise where it applies, stated as such.
(defun fn-cth-header-rowp (row)
  (declare (xargs :guard t))
  (and (true-listp row) (equal (len row) 3)
       (equal (car row) *fn-scc-schema*)
       (natp (cadr row))
       (fn-mm-tot-p (caddr row))
       (equal (fn-mm-tot-records (caddr row)) (cadr row))))

; The writer's header of a capture: its records' fold at :resident, the
; residency the owner folds at (host/owner-host.lisp fn-owner-record-totals;
; a header of another residency seeds the empty cache, fn-cth-installed-seed).
(defun fn-cth-header-of-capture (c)
  (declare (xargs :guard t :verify-guards nil))
  (let ((e (fn-sco-records c)))
    (fn-cth-header-row (len e) (fn-ct-charged-exec e :resident))))

; The header row's encodability as the writer checks it: the codec's
; writer recognizer (fn-sccb-treep, books/store-checkpoint-tables.lisp) and
; the program's length within the frame's u64 width.  K1's premise since the
; eighth seat's proof (v3 said fn-scc-treep; the writer's recognizer is the
; one the writer can check and defer on by name).
(defun fn-cth-header-encodablep (row)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-sccb-treep row)
       (< (+ 1 (len (fn-scc-program row))) *fn-scc-u64-bound*)))

; The header run's segments: the row's tree encoding as ONE chunk, framed and
; chained from the genesis with sequence S like every run (executed as that
; one frame; fn-sct-run-segments has no verified guard).
(defun fn-cth-header-segments (row s)
  (declare (xargs :guard (and (natp s) (fn-scc-treep row)) :verify-guards nil))
  (let ((prog (fn-scc-encode row)))
    (mbe :logic (fn-sct-run-segments prog (max 1 (len prog)) s)
         :exec (fn-scc-frames (list prog) 0 1 s *fn-scc-genesis*))))

; The reader's first step: the first segment alone, a run of count 1, its
; row decoded; the TOT when the row is well-formed and its S is the
; framing's S, else NIL.
(defun fn-cth-header-tot (segs)
  (declare (xargs :guard (fn-scc-segment-listp segs) :verify-guards nil))
  (let ((h (and (consp segs) (fn-scc-octet-listp (car segs)) (fn-scc-parse-header (car segs)))))
    (and h
         (equal (nth 1 h) 1)
         (let ((f (fn-sct-run-decode segs (nth 3 h))))   ; joins the run's count, 1, of segments
           (and (eq (car f) :ok)
                (let ((d (fn-scc-decode-tree (nth 1 f))))
                  (and (eq (car d) :ok)
                       (fn-cth-header-rowp (cadr d))
                       (equal (cadr (cadr d)) (nth 3 h))
                       (caddr (cadr d)))))))))

; A run of segments admitted in order with the running total: the final
; total, or (:refused REASON), REASON the lower admission's (:header,
; :schema, :exceeds-bound; books/store-checkpoint-reader.lisp
; fn-sccr-admit-segment).  The writer's steps and the reader's phases run
; this same admission (fn-ockp-admit-frames calls fn-sccr-admit-segment).
(defun fn-cth-admit-run (segs total segment-bound file-bound)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp segs)
      (let ((a (fn-sccr-admit-segment (car segs) total segment-bound file-bound)))
        (if (eq (car a) :ok)
            (fn-cth-admit-run (cdr segs) (+ (nfix total) (nfix (nth 1 a))) segment-bound file-bound)
          (list :refused (cadr a))))
    (nfix total)))

; One segment's framing at the profile's record bound: the header phase's
; file bound, and every segment's bound.
(defun fn-cth-segment-bound (profile)
  (declare (xargs :guard t :verify-guards nil))
  (fn-scc-segment-max-octets (nfix (fn-bs-profile-max-record-octets profile))))

; The reader over the file's segments (after the history image region): the
; header segment under one segment's framing from 0; its TOT; the rest (the
; arena run and the four tables, read by the unchanged loader) under M's load
; bound at that TOT and the configuration history's octets (CFG field 12),
; from the header's total.  (:ok TOTAL TOT) or (:refused PHASE REASON):
; PHASE :header-segment with the lower admission's REASON (:absent for an
; empty file), :header-row with :malformed, :rest with the lower REASON.
; The host maps a :schema REASON to `checkpoint-schema' (D34).
(defun fn-cth-read-file (segs profile cfg)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((sb (fn-cth-segment-bound profile))
         (t1 (fn-cth-admit-run (take 1 segs) 0 sb sb)))
    (cond ((not (consp segs)) (list :refused :header-segment :absent))
          ((not (natp t1)) (list :refused :header-segment (cadr t1)))
          (t
           (let ((tot (fn-cth-header-tot segs)))
             (if (not (fn-mm-tot-p tot))
                 (list :refused :header-row :malformed)
               (let ((t2 (fn-cth-admit-run (cdr segs) t1 sb
                                           (fn-mm-checkpoint-load-octets profile tot cfg))))
                 (if (not (natp t2))
                     (list :refused :rest (cadr t2))
                   (list :ok t2 tot)))))))))

; The reader's running total after the header segment and the first N
; segments of the rest, each admitted as fn-cth-read-file admits it: a
; natural, or the refusal.  K5b bounds every such prefix, including one
; read before a later refusal.
(defun fn-cth-read-prefix (segs n profile cfg)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((sb (fn-cth-segment-bound profile))
         (t1 (fn-cth-admit-run (take 1 segs) 0 sb sb)))
    (if (not (and (consp segs) (natp t1)))
        (list :refused :header-segment)
      (let ((tot (fn-cth-header-tot segs)))
        (if (not (fn-mm-tot-p tot))
            (list :refused :header-row)
          (fn-cth-admit-run (take (nfix n) (cdr segs)) t1 sb
                            (fn-mm-checkpoint-load-octets profile tot cfg)))))))

; The publication's budget: M's load bound at the capture's fold and the
; configuration history the writer holds.
(defun fn-cth-publication-budget (profile c cfg)
  (declare (xargs :guard t :verify-guards nil))
  (fn-mm-checkpoint-load-octets profile (fn-ct-charged (fn-sco-records c) :resident) cfg))

; The publication's setup with the header counted (Codex r3 F1): the
; existing setup (books/store-checkpoint-arena-writer.lisp
; fn-scka-publication-setup, its ALEN documented as the arena run's octets)
; is called with the header's octets HLEN added to ALEN and the budget the
; publication budget.  The plan's estimate is then H + A + the tables.
(defun fn-cth-publication-setup (next frontier revision log seg profile cfg free alen hlen)
  (declare (xargs :guard (natp seg) :verify-guards nil))
  (fn-scka-publication-setup next frontier revision log seg
                             (nfix (fn-cth-publication-budget profile next cfg))
                             free (+ (nfix hlen) (nfix alen))))

; The table pipeline's first state with the file's running total carried
; in (the arena run's last total), where fn-ockp-initial-state starts it at
; 0: the tables are admitted against the publication budget from the
; octets already written (Codex r3 F1: the running total begins with H and
; is preserved across A and the tables).
(defun fn-cth-table-initial-state (tables total fn-octets)
  (declare (xargs :stobjs fn-octets :guard (natp total)))
  (update-nth 6 total (fn-ockp-initial-state tables fn-octets)))

; The writer's header step (the host calls it once, after the history
; image region, before the arena run): the header run's octets for the
; capture NEXT, admitted from 0 under one segment's framing and the
; publication budget by the reader's own admission, with that total and the
; budget; or (:deferred REASON) and nothing is written.  (list :ok OCTETS
; TOTAL BUDGET) | (list :deferred :header-unencodable) | (list :deferred
; :header-bound EXTENT-OR-REASON).
(defun fn-cth-header-step (next profile cfg)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((row (fn-cth-header-of-capture next))
         (s (len (fn-sco-records next))))
    (if (not (and (fn-cth-header-encodablep row) (< s *fn-scc-u64-bound*)))
        (list :deferred :header-unencodable)
      (let* ((segs (fn-cth-header-segments row s))
             (budget (fn-cth-publication-budget profile next cfg))
             (sb (fn-cth-segment-bound profile))
             (total (fn-cth-admit-run segs 0 sb budget)))
        (if (natp total)
            (list :ok (fn-scc-concat segs) total budget)
          (list :deferred :header-bound (cadr total)))))))

; The owner's carried-totals cache seeded from the header: (S . TOT) when
; TOT is a tot for S records at the owner's residency, else the empty cache.
(defun fn-cth-seed (s header residency)
  (declare (xargs :guard t))
  (if (and (natp s) (fn-mm-tot-p header)
           (equal (fn-mm-tot-records header) s)
           (equal (fn-mm-tot-paged-p header) (equal residency :paged)))
      (cons s header)
    (cons 0 (fn-ct-zero-tot residency))))

; The seed the open installs: the header's only when the open went over THIS
; checkpoint (selected and opened :ok); the empty cache on every other path.
(defun fn-cth-installed-seed (over-checkpoint s header residency)
  (declare (xargs :guard t))
  (if over-checkpoint
      (fn-cth-seed s header residency)
    (cons 0 (fn-ct-zero-tot residency))))


; ---------------------------------------------------------------------------
; Lemmas (local).

(local
 (defthm k-records-of-capture
   (equal (fn-sco-records (fn-sco-capture configs records)) (true-list-fix records))
   :hints (("Goal" :in-theory (e/d (fn-sco-capture fn-sco-make fn-sco-records fn-sco-at)
                                   (fn-sco-cpr-prefix fn-replay-identity-loop
                                    fn-cpe-projection-replay fn-th-prefix-loop
                                    fn-cei-build-aux))))))

(local
 (defthm k-header-tot-of-capture
   (equal (caddr (fn-cth-header-of-capture (fn-sco-capture configs records)))
          (fn-ct-charged records :resident))
   :hints (("Goal" :in-theory (e/d (fn-cth-header-of-capture fn-cth-header-row fn-ct-charged-exec)
                                   (fn-sco-capture fn-ct-charged))))))

(local
 (defthm k-u64-octets (fn-scc-octet-listp (fn-scc-u64 n k))
   :hints (("Goal" :in-theory (enable fn-scc-u64 fn-scc-octetp)))))

(local
 (defthm k-octets-append
   (implies (and (fn-scc-octet-listp a) (fn-scc-octet-listp b))
            (fn-scc-octet-listp (append a b)))
   :hints (("Goal" :induct (fn-scc-octet-listp a)
            :in-theory (e/d (fn-scc-octet-listp) (fn-scc-octet-listp-facts))))))

(local
 (defthm k-header-octets (fn-scc-octet-listp (fn-scc-header i c l s))
   :hints (("Goal" :in-theory (enable fn-scc-header fn-scc-octetp)))))

(local
 (defthm k-seal-octets
   (implies (and (fn-scc-octet-listp prev) (fn-scc-octet-listp header) (fn-scc-octet-listp chunk))
            (fn-scc-octet-listp (fn-scc-seal prev header chunk)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-frame-trailer-is-a-digest (octets (append prev header chunk))))
            :in-theory (e/d (fn-scc-seal fn-frame-digestp) (fn-frame-trailer-is-a-digest))))))

(local
 (defthm k-frame-one-octets
   (implies (fn-scc-octet-listp p)
            (fn-scc-octet-listp (car (fn-scc-frames (list p) 0 1 s *fn-scc-genesis*))))
   :hints (("Goal" :expand ((fn-scc-frames (list p) 0 1 s *fn-scc-genesis*))
            :in-theory (disable fn-scc-header fn-scc-seal)))))

(local
 (defthm k-chunks-of-short
   (implies (and (true-listp prog) (<= (len prog) seg) (posp seg))
            (equal (fn-scc-chunks prog seg) (list prog)))
   :hints (("Goal" :expand ((fn-scc-chunks prog seg))
            :in-theory (enable fn-scc-long-enoughp)))))

(local
 (defthm k-header-segments-frames
   (equal (fn-cth-header-segments row s)
          (fn-scc-frames (list (fn-scc-program row)) 0 1 s *fn-scc-genesis*))
   :hints (("Goal" :in-theory (e/d (fn-cth-header-segments fn-sct-run-segments) (fn-scc-frames))
            :use ((:instance k-chunks-of-short (prog (fn-scc-program row)) (seg (max 1 (len (fn-scc-program row))))))))))

(local
 (defthm k-header-segments-shape
   (and (consp (fn-cth-header-segments row s))
        (not (consp (cdr (fn-cth-header-segments row s)))))
   :hints (("Goal" :in-theory (disable fn-scc-header fn-scc-seal)
            :expand ((fn-scc-frames (list (fn-scc-program row)) 0 1 s *fn-scc-genesis*))))))

(local
 (defthm k-header-rowp-facts2
   (implies (fn-cth-header-rowp row)
            (and (natp (cadr row)) (fn-mm-tot-p (caddr row)) (caddr row) (consp row)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-cth-header-rowp)))))

(local
 (defthm k-frames-true-listp
   (true-listp (fn-scc-frames chunks index count sequence prev))
   :hints (("Goal" :in-theory (enable fn-scc-frames)))))

(local
 (defthm k-list-car-of-singleton
   (implies (and (consp x) (not (consp (cdr x))) (true-listp x))
            (equal (list (car x)) x))
   :rule-classes nil))

(local
 (defthm k-program-of-cons-nonempty
   (implies (consp x) (posp (len (fn-scc-program x))))
   :rule-classes :type-prescription
   :hints (("Goal" :expand ((fn-scc-program x)) :in-theory (enable fn-scc-octets-valuep)))))

(local
 (defthm k-frames-one-consp
   (consp (fn-scc-frames (list p) 0 1 s g))
   :hints (("Goal" :expand ((fn-scc-frames (list p) 0 1 s g))
            :in-theory (disable fn-scc-header fn-scc-seal)))))

(local
 (defthm k-consp-append-of-consp
   (implies (consp a) (consp (append a b)))))

(local
 (defthm k-car-append-of-consp
   (implies (consp a) (equal (car (append a b)) (car a)))))

(local
 (defthm k-header-tot-of-row
   (implies (and (fn-sccb-treep row) (fn-cth-header-rowp row) (equal (cadr row) s)
                 (< (+ 1 (len (fn-scc-program row))) *fn-scc-u64-bound*)
                 (< s *fn-scc-u64-bound*))
            (equal (fn-cth-header-tot (append (fn-cth-header-segments row s) rest))
                   (caddr row)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-cth-header-tot fn-cth-header-segments)
                            (k-header-segments-frames fn-mm-tot-p fn-sct-run-decode fn-scc-parse-header
                             fn-scc-decode-tree fn-cth-header-rowp fn-sct-run-segments
                             fn-sct-run-decode-of-run-segments
                             fn-scc-decode-tree-of-encode fn-scc-encode-is-program))
            :use ((:instance fn-sccb-treep-encodes-octets (x row))
                  (:instance fn-sccb-treep-is-treep (x row))
                  (:instance fn-scc-decode-tree-of-encode (x row))
                  (:instance fn-scc-encode-is-program (x row))
                  (:instance k-header-rowp-facts2)
                  (:instance k-program-of-cons-nonempty (x row))
                  (:instance fn-sct-run-decode-of-run-segments
                             (prog (fn-scc-program row)) (seg (max 1 (len (fn-scc-program row)))))
                  (:instance fn-scc-parse-header-of-first-frame-sequence
                             (chunks (list (fn-scc-program row))) (n 1) (q s) (prev *fn-scc-genesis*))
                  (:instance fn-scc-parse-header-of-first-frame
                             (chunks (list (fn-scc-program row))) (n 1) (q s) (prev *fn-scc-genesis*))
                  (:instance k-header-segments-frames))))))

(local
 (defthm k-cadr-header-of-capture
   (equal (cadr (fn-cth-header-of-capture (fn-sco-capture configs records))) (len records))
   :hints (("Goal" :in-theory (e/d (fn-cth-header-of-capture fn-cth-header-row) (fn-sco-capture fn-sco-records))
            :use ((:instance k-records-of-capture))))))

(local
 (defthm k1w-try
   (fn-cth-header-rowp (fn-cth-header-of-capture c))
   :hints (("Goal" :in-theory (e/d (fn-cth-header-rowp fn-cth-header-of-capture fn-cth-header-row fn-ct-charged-exec)
                                   (fn-ct-charged fn-mm-tot-p fn-mm-tot-records fn-mm-tot-paged-p))))))

(local
 (defthm k1-try
   (implies (and (fn-sccb-treep (fn-cth-header-of-capture (fn-sco-capture configs records)))
                 (< (+ 1 (len (fn-scc-program (fn-cth-header-of-capture (fn-sco-capture configs records)))))
                    *fn-scc-u64-bound*)
                 (< (len records) *fn-scc-u64-bound*))
            (equal (fn-cth-header-tot
                    (append (fn-cth-header-segments
                             (fn-cth-header-of-capture (fn-sco-capture configs records))
                             (len records))
                            rest))
                   (fn-ct-charged records :resident)))
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-cth-header-tot fn-cth-header-segments fn-cth-header-of-capture
                                k-header-tot-of-row fn-sco-capture fn-ct-charged)
            :use ((:instance k-header-tot-of-row (row (fn-cth-header-of-capture (fn-sco-capture configs records)))
                             (s (len records)))
                  (:instance k1w-try (c (fn-sco-capture configs records)))
                  (:instance k-header-tot-of-capture)
                  (:instance k-cadr-header-of-capture))))))

(local
 (defthm k2-try
   (let ((o (fn-sco-open (fn-sco-capture configs prefix) configs frontier suffix)))
     (implies (fn-sn-open-okp o)
              (equal (fn-mm-tot-plus (caddr (fn-cth-header-of-capture (fn-sco-capture configs prefix)))
                                     (fn-ct-charged suffix :resident))
                     (fn-ct-charged (fn-sf-records (fn-sn-files (fn-sn-open-state o))) :resident))))
   :hints (("Goal" :in-theory (e/d (fn-sn-recover-from-checkpoint-equals-full-recover)
                                   (fn-sco-capture fn-ct-charged fn-cth-header-of-capture fn-sco-open
                                    fn-cpo-open-observed fn-mm-tot-plus fn-ct-charged-of-append))
            :use ((:instance fn-cpo-open-success-exact-image (events (append prefix suffix)))
                  (:instance fn-ct-charged-of-append (a prefix) (b suffix) (residency :resident)))))))

(local
 (defthm k-take-len-append
   (equal (take (len p) (append p s)) (true-list-fix p))))

(local
 (defthm k-seed-valid
   (implies (equal header (fn-ct-charged prefix header-residency))
            (fn-ct-totals-cache-validp (fn-cth-seed (len prefix) header residency)
                                       (append prefix suffix) residency))
   :hints (("Goal" :in-theory (e/d (fn-ct-totals-cache-validp fn-cth-seed) (fn-ct-charged))
            :use ((:instance fn-ct-charged-residency-word (records prefix) (r1 header-residency) (r2 residency))
                  (:instance fn-ct-totals-empty-cache-is-valid (records (append prefix suffix))))))))

(local
 (defthm k3-try
   (implies (or (not over-checkpoint)
                (and (equal records (append prefix suffix))
                     (equal header (fn-ct-charged prefix header-residency))
                     (equal s (len prefix))))
            (fn-ct-totals-cache-validp (fn-cth-installed-seed over-checkpoint s header residency)
                                       records residency))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-cth-installed-seed) (fn-cth-seed fn-ct-totals-cache-validp fn-ct-charged k-seed-valid))
            :use ((:instance k-seed-valid)
                  (:instance fn-ct-totals-empty-cache-is-valid))))))

(local
 (defthm k-admit-ok-naturals
   (implies (equal (car (fn-sccr-admit-segment header total sb fb)) :ok)
            (and (natp total) (natp fb) (natp sb)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-sccr-admit-segment)))))

(local
 (defthm k-admit-ok-bound
   (implies (equal (car (fn-sccr-admit-segment header total sb fb)) :ok)
            (and (natp (nth 1 (fn-sccr-admit-segment header total sb fb)))
                 (<= (+ total (nth 1 (fn-sccr-admit-segment header total sb fb))) fb)))
   :hints (("Goal" :use ((:instance fn-sccr-admitted-within-bounds (segment-bound sb) (file-bound fb)))
            :in-theory (disable fn-sccr-admitted-within-bounds)))))

(local
 (defthm k-admit-run-within
   (implies (and (natp (fn-cth-admit-run segs total sb fb))
                 (consp segs))
            (<= (fn-cth-admit-run segs total sb fb) fb))
   :hints (("Goal" :induct (fn-cth-admit-run segs total sb fb)
            :in-theory (e/d (fn-cth-admit-run) (fn-sccr-admit-segment)))
           ("Subgoal *1/2" :use ((:instance fn-sccr-admitted-within-bounds
                                            (header (car segs)) (segment-bound sb) (file-bound fb))))
           ("Subgoal *1/1" :use ((:instance fn-sccr-admitted-within-bounds
                                            (header (car segs)) (segment-bound sb) (file-bound fb)))))))

(local
 (defthm k6-try
   (<= (fn-cth-segment-bound profile)
       (fn-mm-checkpoint-load-octets profile tot cfg))
   :hints (("Goal" :in-theory (e/d (fn-cth-segment-bound fn-mm-checkpoint-load-octets fn-ock-capture-budget
                                    fn-sccr-file-read-bound fn-scc-segment-max-octets)
                                   (fn-bs-profile-max-history-octets fn-mm-tot-log fn-mm-cfg-config))))))

(local
 (defthm k8c-try
   (implies (and (natp t0) (natp (fn-cth-admit-run x t0 sb fb)))
            (equal (fn-cth-admit-run (append x y) t0 sb fb)
                   (fn-cth-admit-run y (fn-cth-admit-run x t0 sb fb) sb fb)))
   :rule-classes nil
   :hints (("Goal" :induct (fn-cth-admit-run x t0 sb fb)
            :expand ((fn-cth-admit-run x t0 sb fb) (fn-cth-admit-run (append x y) t0 sb fb)
                     (fn-cth-admit-run (cons (car x) (append (cdr x) y)) t0 sb fb))
            :in-theory (union-theories (quote ((:induction fn-cth-admit-run) (:definition binary-append) car-cons cdr-cons
                                                (:definition natp) (:definition nfix) (:definition not) k-admit-ok-bound))
                                       (theory (quote minimal-theory)))))))

(local
 (defthm k-admit-run-ge
   (implies (natp (fn-cth-admit-run segs total sb fb))
            (<= (nfix total) (fn-cth-admit-run segs total sb fb)))
   :rule-classes :linear
   :hints (("Goal" :induct (fn-cth-admit-run segs total sb fb)
            :in-theory (e/d (fn-cth-admit-run) (fn-sccr-admit-segment))))))

(local
 (defthm k-admit-segment-mono
   (implies (and (equal (car (fn-sccr-admit-segment h total sb fb)) :ok)
                 (natp fb2) (<= fb fb2))
            (equal (fn-sccr-admit-segment h total sb fb2)
                   (fn-sccr-admit-segment h total sb fb)))
   :hints (("Goal" :in-theory (enable fn-sccr-admit-segment)))))

(local
 (defthm k-admit-run-mono
   (implies (and (natp (fn-cth-admit-run segs total sb fb))
                 (natp fb2) (<= fb fb2))
            (equal (fn-cth-admit-run segs total sb fb2)
                   (fn-cth-admit-run segs total sb fb)))
   :rule-classes nil
   :hints (("Goal" :induct (fn-cth-admit-run segs total sb fb)
            :expand ((fn-cth-admit-run segs total sb fb) (fn-cth-admit-run segs total sb fb2))
            :in-theory (union-theories (quote ((:induction fn-cth-admit-run)
                                                (:definition natp) (:definition nfix) (:definition not)
                                                k-admit-ok-bound k-admit-segment-mono))
                                       (theory (quote minimal-theory)))))))

(local
 (defthm k10-try
   (equal (cdr (append (fn-cth-header-segments row s) rest)) rest)
   :hints (("Goal" :use ((:instance k-header-segments-shape))
            :in-theory (disable fn-cth-header-segments k-header-segments-shape)))))

(local
 (defthm k4b-try
   (implies (and (consp segs)
                 (fn-sccr-other-schemap (car segs))
                 (not (fn-scc-parse-header (car segs))))
            (equal (fn-cth-read-file segs profile cfg)
                   (list :refused :header-segment :schema)))
   :hints (("Goal" :expand ((fn-cth-admit-run (list (car segs)) 0 (fn-cth-segment-bound profile)
                                              (fn-cth-segment-bound profile)))
            :in-theory (e/d (fn-cth-read-file fn-sccr-admit-segment)
                            (fn-sccr-other-schemap fn-scc-parse-header fn-cth-segment-bound
                             fn-cth-header-tot))))))

(local
 (defthm k-admit-run-of-atom
   (implies (not (consp segs)) (equal (fn-cth-admit-run segs total sb fb) (nfix total)))
   :rule-classes nil
   :hints (("Goal" :expand ((fn-cth-admit-run segs total sb fb))))))

(local
 (defthm k-take1-consp
   (implies (consp segs) (consp (take 1 segs)))
   :rule-classes nil))

(local
 (defthm k4-try
   (and (implies (not (fn-mm-tot-p tot)) (not (fn-cth-header-rowp (fn-cth-header-row s tot))))
        (implies (not (equal (fn-mm-tot-records tot) s))
                 (not (fn-cth-header-rowp (fn-cth-header-row s tot))))
        (not (fn-cth-header-rowp (list (1- *fn-scc-schema*) s tot))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-cth-header-rowp fn-cth-header-row) (fn-mm-tot-p fn-mm-tot-records))))))

(local
 (defthm k5-try
   (let ((r (fn-cth-read-file segs profile cfg)))
     (implies (equal (car r) :ok)
              (and (<= (nth 1 r) (fn-mm-checkpoint-load-octets profile (nth 2 r) cfg))
                   (fn-mm-tot-p (nth 2 r))
                   (equal (nth 2 r) (fn-cth-header-tot segs)))))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories (quote ((:definition fn-cth-read-file) car-cons cdr-cons
                                               (:definition nth) (:definition natp) (:definition nfix) (:definition not)
                                               (:executable-counterpart equal) (:executable-counterpart zp)
                                               (:executable-counterpart nth) (:executable-counterpart car)
                                               (:executable-counterpart cdr) (:executable-counterpart not)
                                               (:executable-counterpart consp)))
                                       (theory (quote minimal-theory)))
            :cases ((consp (cdr segs)))
            :use ((:instance k-admit-run-within (segs (cdr segs))
                             (total (fn-cth-admit-run (take 1 segs) 0 (fn-cth-segment-bound profile)
                                                      (fn-cth-segment-bound profile)))
                             (sb (fn-cth-segment-bound profile))
                             (fb (fn-mm-checkpoint-load-octets profile (fn-cth-header-tot segs) cfg)))
                  (:instance k-admit-run-within (segs (take 1 segs)) (total 0)
                             (sb (fn-cth-segment-bound profile)) (fb (fn-cth-segment-bound profile)))
                  (:instance k-admit-run-of-atom
                             (segs (cdr segs))
                             (total (fn-cth-admit-run (take 1 segs) 0 (fn-cth-segment-bound profile)
                                                      (fn-cth-segment-bound profile)))
                             (sb (fn-cth-segment-bound profile))
                             (fb (fn-mm-checkpoint-load-octets profile (fn-cth-header-tot segs) cfg)))
                  (:instance k-take1-consp)
                  (:instance k6-try (tot (fn-cth-header-tot segs))))))))

(local
 (defthm k5b-try
   (let ((p (fn-cth-read-prefix segs n profile cfg)))
     (implies (natp p)
              (<= p (fn-mm-checkpoint-load-octets profile (fn-cth-header-tot segs) cfg))))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories (quote ((:definition fn-cth-read-prefix) car-cons cdr-cons
                                               (:definition natp) (:definition nfix) (:definition not)
                                               (:executable-counterpart equal) (:executable-counterpart not)
                                               (:executable-counterpart consp) (:executable-counterpart natp)))
                                       (theory (quote minimal-theory)))
            :cases ((consp (take (nfix n) (cdr segs))))
            :use ((:instance k-admit-run-within (segs (take (nfix n) (cdr segs)))
                             (total (fn-cth-admit-run (take 1 segs) 0 (fn-cth-segment-bound profile)
                                                      (fn-cth-segment-bound profile)))
                             (sb (fn-cth-segment-bound profile))
                             (fb (fn-mm-checkpoint-load-octets profile (fn-cth-header-tot segs) cfg)))
                  (:instance k-admit-run-within (segs (take 1 segs)) (total 0)
                             (sb (fn-cth-segment-bound profile)) (fb (fn-cth-segment-bound profile)))
                  (:instance k-admit-run-of-atom
                             (segs (take (nfix n) (cdr segs)))
                             (total (fn-cth-admit-run (take 1 segs) 0 (fn-cth-segment-bound profile)
                                                      (fn-cth-segment-bound profile)))
                             (sb (fn-cth-segment-bound profile))
                             (fb (fn-mm-checkpoint-load-octets profile (fn-cth-header-tot segs) cfg)))
                  (:instance k-take1-consp)
                  (:instance k6-try (tot (fn-cth-header-tot segs))))))))

(local
 (defthm k-hsegs-true-listp
   (true-listp (fn-cth-header-segments row s))
   :hints (("Goal" :in-theory (e/d () (fn-scc-frames))))))

(local
 (defthm k-take1-of-singleton-append
   (equal (take 1 (append (list a) rest)) (list a))))

(local
 (defthm k-take1-header
   (equal (take 1 (append (fn-cth-header-segments row s) rest)) (fn-cth-header-segments row s))
   :hints (("Goal" :do-not-induct t
            :use ((:instance k-header-segments-shape) (:instance k-hsegs-true-listp)
                  (:instance k-list-car-of-singleton (x (fn-cth-header-segments row s)))
                  (:instance k-take1-of-singleton-append (a (car (fn-cth-header-segments row s)))))
            :in-theory (disable fn-cth-header-segments k-header-segments-shape k-hsegs-true-listp
                                k-take1-of-singleton-append)))))

(local
 (defthm k-admit-one-segment-bound
   (implies (and (consp x) (not (consp (cdr x)))
                 (natp (fn-cth-admit-run x 0 sb fb)))
            (equal (fn-cth-admit-run x 0 sb sb) (fn-cth-admit-run x 0 sb fb)))
   :hints (("Goal" :expand ((fn-cth-admit-run x 0 sb sb) (fn-cth-admit-run x 0 sb fb)
                            (fn-cth-admit-run (cdr x) (nth 1 (fn-sccr-admit-segment (car x) 0 sb fb)) sb fb)
                            (fn-cth-admit-run (cdr x) (nth 1 (fn-sccr-admit-segment (car x) 0 sb sb)) sb sb))
            :in-theory (enable fn-sccr-admit-segment)))))

(local
 (defthm k-load-mono-cfg
   (implies (<= (fn-mm-cfg-config a) (fn-mm-cfg-config b))
            (<= (fn-mm-checkpoint-load-octets profile tot a) (fn-mm-checkpoint-load-octets profile tot b)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-mm-checkpoint-load-octets fn-sccr-file-read-bound)
                                   (fn-ock-capture-budget fn-scc-segment-max-octets fn-mm-tot-log
                                    fn-mm-cfg-config fn-bs-profile-max-record-octets))))))

(local
 (defthm k-open-records
   (let ((o (fn-sco-open (fn-sco-capture configs prefix) configs frontier suffix)))
     (implies (fn-sn-open-okp o)
              (equal (fn-sf-records (fn-sn-files (fn-sn-open-state o))) (append prefix suffix))))
   :hints (("Goal" :in-theory (e/d (fn-sn-recover-from-checkpoint-equals-full-recover)
                                   (fn-sco-capture fn-sco-open fn-cpo-open-observed))
            :use ((:instance fn-cpo-open-success-exact-image (events (append prefix suffix))))))))

(local
 (defthm k9-try
   (let* ((c (fn-sco-capture configs prefix))
          (segs (append (fn-cth-header-segments (fn-cth-header-of-capture c) (len prefix)) rest))
          (o (fn-sco-open c configs frontier suffix)))
     (implies (and (fn-cth-header-encodablep (fn-cth-header-of-capture c))
                   (< (len prefix) *fn-scc-u64-bound*))
              (fn-ct-totals-cache-validp
               (fn-cth-installed-seed (fn-sn-open-okp o) (len prefix) (fn-cth-header-tot segs) :resident)
               (if (fn-sn-open-okp o)
                   (fn-sf-records (fn-sn-files (fn-sn-open-state o)))
                 records)
               :resident)))
   :hints (("Goal" :do-not-induct t
            :cases ((fn-sn-open-okp (fn-sco-open (fn-sco-capture configs prefix) configs frontier suffix)))
            :in-theory (e/d (fn-cth-installed-seed fn-cth-header-encodablep)
                            (fn-cth-seed fn-ct-totals-cache-validp fn-ct-charged fn-sco-capture fn-sco-open
                             fn-cth-header-tot fn-cth-header-segments fn-cth-header-of-capture
                             k1-try k-open-records k-seed-valid fn-sn-open-okp))
            :use ((:instance k1-try (records prefix))
                  (:instance k-open-records)
                  (:instance k-seed-valid (header-residency :resident) (residency :resident)
                             (header (fn-ct-charged prefix :resident)))
                  (:instance fn-ct-totals-empty-cache-is-valid (residency :resident)))))))

(local
 (defthm k-cdr-append-of-consp
   (implies (consp a) (equal (cdr (append a b)) (append (cdr a) b)))))

(local
 (defthm k-admit-run-append-natp
   (implies (and (natp t0) (natp (fn-cth-admit-run (append x y) t0 sb fb)))
            (natp (fn-cth-admit-run x t0 sb fb)))
   :rule-classes nil
   :hints (("Goal" :induct (fn-cth-admit-run x t0 sb fb)
            :expand ((fn-cth-admit-run x t0 sb fb) (fn-cth-admit-run (append x y) t0 sb fb))
            :in-theory (union-theories (quote ((:induction fn-cth-admit-run) k-consp-append-of-consp
                                                k-car-append-of-consp k-cdr-append-of-consp
                                                (:definition natp) (:definition nfix) (:definition not) k-admit-ok-bound))
                                       (theory (quote minimal-theory)))))))

(local
 (defthm k-load-natp
   (natp (fn-mm-checkpoint-load-octets profile tot cfg))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-mm-checkpoint-load-octets fn-sccr-file-read-bound fn-ock-capture-budget)))))

(local
 (defthm k-budget-of-capture
   (equal (fn-cth-publication-budget profile (fn-sco-capture configs records) cfg)
          (fn-mm-checkpoint-load-octets profile (fn-ct-charged records :resident) cfg))
   :hints (("Goal" :in-theory (e/d (fn-cth-publication-budget) (fn-sco-capture fn-ct-charged fn-mm-checkpoint-load-octets))))))

(local
 (defthm k7-try
   (let* ((c (fn-sco-capture configs records))
          (segs (append (fn-cth-header-segments (fn-cth-header-of-capture c) (len records)) rest))
          (sb (fn-cth-segment-bound profile))
          (w (fn-cth-admit-run segs 0 sb (fn-cth-publication-budget profile c cfg-w))))
     (implies (and (fn-cth-header-encodablep (fn-cth-header-of-capture c))
                   (< (len records) *fn-scc-u64-bound*)
                   (natp w)
                   (<= (fn-mm-cfg-config cfg-w) (fn-mm-cfg-config cfg)))
              (equal (fn-cth-read-file segs profile cfg)
                     (list :ok w (fn-ct-charged records :resident)))))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories (quote ((:definition fn-cth-read-file) (:definition fn-cth-header-encodablep)
                                               car-cons cdr-cons k-take1-header k10-try k-budget-of-capture k-consp-append-of-consp
                                               (:definition natp) (:definition nfix) (:definition not)
                                               (:executable-counterpart equal) (:executable-counterpart not)
                                               (:executable-counterpart consp) (:executable-counterpart natp)))
                                       (theory (quote minimal-theory)))
            :use ((:instance k1-try)
                  (:instance fn-ct-charged-is-a-tot (residency :resident))
                  (:instance k-header-segments-shape (row (fn-cth-header-of-capture (fn-sco-capture configs records)))
                             (s (len records)))
                  (:instance k-admit-run-append-natp
                             (x (fn-cth-header-segments (fn-cth-header-of-capture (fn-sco-capture configs records)) (len records)))
                             (y rest) (t0 0) (sb (fn-cth-segment-bound profile))
                             (fb (fn-mm-checkpoint-load-octets profile (fn-ct-charged records :resident) cfg-w)))
                  (:instance k8c-try
                             (x (fn-cth-header-segments (fn-cth-header-of-capture (fn-sco-capture configs records)) (len records)))
                             (y rest) (t0 0) (sb (fn-cth-segment-bound profile))
                             (fb (fn-mm-checkpoint-load-octets profile (fn-ct-charged records :resident) cfg-w)))
                  (:instance k-admit-one-segment-bound
                             (x (fn-cth-header-segments (fn-cth-header-of-capture (fn-sco-capture configs records)) (len records)))
                             (sb (fn-cth-segment-bound profile))
                             (fb (fn-mm-checkpoint-load-octets profile (fn-ct-charged records :resident) cfg-w)))
                  (:instance k-load-mono-cfg (tot (fn-ct-charged records :resident)) (a cfg-w) (b cfg))
                  (:instance k-admit-run-mono (segs rest)
                             (total (fn-cth-admit-run (fn-cth-header-segments (fn-cth-header-of-capture (fn-sco-capture configs records)) (len records))
                                                      0 (fn-cth-segment-bound profile)
                                                      (fn-mm-checkpoint-load-octets profile (fn-ct-charged records :resident) cfg-w)))
                             (sb (fn-cth-segment-bound profile))
                             (fb (fn-mm-checkpoint-load-octets profile (fn-ct-charged records :resident) cfg-w))
                             (fb2 (fn-mm-checkpoint-load-octets profile (fn-ct-charged records :resident) cfg)))
                  (:instance k-load-natp (tot (fn-ct-charged records :resident))))))))

(local
 (defthm k-setup-tables
   (let ((setup (fn-scka-publication-setup next frontier revision log seg budget free alen)))
     (implies (not (equal (car setup) :unencodable))
              (and (equal (nth 1 setup) (fn-sct-tables-of-capture next frontier revision log))
                   (equal (nth 4 setup) (fn-sco-event-index next)))))
   :hints (("Goal" :in-theory (e/d (fn-scka-publication-setup fn-ockp-setup)
                                   (fn-sct-tables-of-capture fn-ockp-tables-encodablep fn-ockp-decide
                                    fn-ockp-estimate fn-ockp-counts fn-sco-event-index fn-cei-msgid-trie))))))

(local
 (defthm k8-try
   (let* ((setup (fn-cth-publication-setup next frontier revision log seg profile cfg free alen hlen))
          (tables (fn-sct-tables-of-capture next frontier revision log))
          (estimate (+ (nfix hlen) (nfix alen)
                       (len (fn-sct-file-octets
                             (fn-sct-table-programs tables (fn-sco-event-index next)) seg s)))))
     (implies (not (equal (car setup) :unencodable))
              (and (equal (nth 6 setup) estimate)
                   (iff (equal (car (car setup)) :plan)
                        (and (<= estimate (nfix (fn-cth-publication-budget profile next cfg)))
                             (natp free)
                             (<= estimate (fn-ockp-space free)))))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-cth-publication-setup)
                            (fn-scka-publication-setup fn-cth-publication-budget fn-sct-file-octets
                             fn-sct-table-programs fn-sct-tables-of-capture fn-sco-event-index
                             fn-ockp-space fn-scka-publication-setup-plans-within-the-disk k-setup-tables))
            :use ((:instance fn-scka-publication-setup-plans-within-the-disk
                             (budget (nfix (fn-cth-publication-budget profile next cfg)))
                             (alen (+ (nfix hlen) (nfix alen))))
                  (:instance k-setup-tables
                             (budget (nfix (fn-cth-publication-budget profile next cfg)))
                             (alen (+ (nfix hlen) (nfix alen)))))))))


; ---------------------------------------------------------------------------
; Guards of the host-called definitions.

(verify-guards fn-cth-header-of-capture)
(verify-guards fn-cth-header-encodablep)
(verify-guards fn-cth-admit-run)
(verify-guards fn-cth-segment-bound)
(verify-guards fn-cth-publication-budget)
(verify-guards fn-cth-header-segments
  :hints (("Goal" :use ((:instance k-chunks-of-short (prog (fn-scc-encode row))
                                   (seg (max 1 (len (fn-scc-encode row))))))
           :in-theory (e/d (fn-sct-run-segments) (fn-scc-frames k-chunks-of-short)))))
(verify-guards fn-cth-header-tot)
(verify-guards fn-cth-publication-setup)
(verify-guards fn-cth-header-step
  :hints (("Goal" :use ((:instance fn-sccb-treep-is-treep (x (fn-cth-header-of-capture next))))
           :in-theory (e/d (fn-cth-header-encodablep) (fn-sccb-treep-is-treep fn-cth-header-of-capture
                                                       fn-cth-header-segments fn-cth-admit-run)))))


; ---------------------------------------------------------------------------
; KEYSTONES, each the packet's statement verbatim.

; ---------------------------------------------------------------------------
; K1 (writer -> reader, the header): the header run written for the capture
; of RECORDS decodes, read alone and whatever follows it, to their fold.
(defthm fn-cth-header-decodes-to-the-charged-totals
  (implies (and (fn-cth-header-encodablep (fn-cth-header-of-capture (fn-sco-capture configs records)))
                (< (len records) *fn-scc-u64-bound*))
           (equal (fn-cth-header-tot
                   (append (fn-cth-header-segments
                            (fn-cth-header-of-capture (fn-sco-capture configs records))
                            (len records))
                           rest))
                  (fn-ct-charged records :resident)))
  :rule-classes nil
  :hints (("Goal" :use k1-try :in-theory (union-theories (quote (fn-cth-header-encodablep)) (theory (quote minimal-theory))))))

; K1w: the writer's header row is well-formed.
(defthm fn-cth-header-of-capture-is-well-formed
  (fn-cth-header-rowp (fn-cth-header-of-capture c))
  :rule-classes nil
  :hints (("Goal" :use k1w-try :in-theory (theory (quote minimal-theory)))))

; K2 (suffix): the header plus the suffix's fold is the fold of the store the
; open over the checkpoint recovers.
(defthm fn-cth-header-plus-suffix-is-the-open
  (let ((o (fn-sco-open (fn-sco-capture configs prefix) configs frontier suffix)))
    (implies (fn-sn-open-okp o)
             (equal (fn-mm-tot-plus (caddr (fn-cth-header-of-capture (fn-sco-capture configs prefix)))
                                    (fn-ct-charged suffix :resident))
                    (fn-ct-charged (fn-sf-records (fn-sn-files (fn-sn-open-state o))) :resident))))
  :rule-classes nil
  :hints (("Goal" :use k2-try :in-theory (theory (quote minimal-theory)))))

; K3 (seed): the installed seed is a valid carried-totals cache for the
; opened records on every path; over the checkpoint the records are
; PREFIX ++ SUFFIX and the header PREFIX's fold (K2's open gives both).
(defthm fn-cth-installed-seed-is-valid
  (implies (or (not over-checkpoint)
               (and (equal records (append prefix suffix))
                    (equal header (fn-ct-charged prefix header-residency))
                    (equal s (len prefix))))
           (fn-ct-totals-cache-validp (fn-cth-installed-seed over-checkpoint s header residency)
                                      records residency))
  :rule-classes nil
  :hints (("Goal" :use k3-try :in-theory (theory (quote minimal-theory)))))

; K4 (the row's refusals).
(defthm fn-cth-header-rowp-rejects-the-malformed
  (and (implies (not (fn-mm-tot-p tot)) (not (fn-cth-header-rowp (fn-cth-header-row s tot))))
       (implies (not (equal (fn-mm-tot-records tot) s))
                (not (fn-cth-header-rowp (fn-cth-header-row s tot))))
       (not (fn-cth-header-rowp (list (1- *fn-scc-schema*) s tot))))
  :rule-classes nil
  :hints (("Goal" :use k4-try :in-theory (theory (quote minimal-theory)))))

; K5 (reader memory): what the reader holds is within M's load bound at the
; TOT it read, the header's total carried into the rest.
(defthm fn-cth-read-file-is-within-the-load-bound
  (let ((r (fn-cth-read-file segs profile cfg)))
    (implies (equal (car r) :ok)
             (and (<= (nth 1 r) (fn-mm-checkpoint-load-octets profile (nth 2 r) cfg))
                  (fn-mm-tot-p (nth 2 r))
                  (equal (nth 2 r) (fn-cth-header-tot segs)))))
  :rule-classes nil
  :hints (("Goal" :use k5-try :in-theory (theory (quote minimal-theory)))))

; K6 (the header phase): one segment's framing is within every load bound,
; whatever the TOT and the configuration.
(defthm fn-cth-segment-is-within-every-load-bound
  (<= (fn-cth-segment-bound profile)
      (fn-mm-checkpoint-load-octets profile tot cfg))
  :rule-classes nil
  :hints (("Goal" :use k6-try :in-theory (theory (quote minimal-theory)))))

; K7 (the reader reads what the writer admitted; v3.1, Codex r3 F4): the
; file whose segments -- the header run, then REST -- the writer's own
; steps admitted from 0 under the reader's segment bound and the
; publication budget is read whole by the reader at any configuration
; history at least the writer's: the same total, TOT the fold.  v3's K7
; premise (every REST segment framed within the bound) is not what the
; arena writer guarantees (a first whole payload may exceed SEG); its
; successful admission is (K8a, K8t).
(defthm fn-cth-reader-reads-the-admitted-file
  (let* ((c (fn-sco-capture configs records))
         (segs (append (fn-cth-header-segments (fn-cth-header-of-capture c) (len records)) rest))
         (sb (fn-cth-segment-bound profile))
         (w (fn-cth-admit-run segs 0 sb (fn-cth-publication-budget profile c cfg-w))))
    (implies (and (fn-cth-header-encodablep (fn-cth-header-of-capture c))
                  (< (len records) *fn-scc-u64-bound*)
                  (natp w)
                  (<= (fn-mm-cfg-config cfg-w) (fn-mm-cfg-config cfg)))
             (equal (fn-cth-read-file segs profile cfg)
                    (list :ok w (fn-ct-charged records :resident)))))
  :rule-classes nil
  :hints (("Goal" :use k7-try :in-theory (theory (quote minimal-theory)))))

; K5b (every admitted prefix, Codex r3 F3): whatever the reader has
; admitted after the header and any number of the rest's segments -- also
; before a later refusal -- is within M's load bound at the header's TOT.
(defthm fn-cth-read-prefix-is-within-the-load-bound
  (let ((p (fn-cth-read-prefix segs n profile cfg)))
    (implies (natp p)
             (<= p (fn-mm-checkpoint-load-octets profile (fn-cth-header-tot segs) cfg))))
  :rule-classes nil
  :hints (("Goal" :use k5b-try :in-theory (theory (quote minimal-theory)))))

; K4b (the named schema refusal, Codex r3 F5): a first segment of this
; codec's magic under another schema is refused by name, the reason the
; host maps to checkpoint-schema.
(defthm fn-cth-read-file-refuses-another-schema-by-name
  (implies (and (consp segs)
                (fn-sccr-other-schemap (car segs))
                (not (fn-scc-parse-header (car segs))))
           (equal (fn-cth-read-file segs profile cfg)
                  (list :refused :header-segment :schema)))
  :rule-classes nil
  :hints (("Goal" :use k4b-try :in-theory (theory (quote minimal-theory)))))

; K8 (the publication decision counts the header, Codex r3 F1): the setup
; plans exactly when H + A + the tables fit the publication budget and the
; disk less the maintenance reservation; the plan names that sum.
(defthm fn-cth-publication-setup-counts-the-header
  (let* ((setup (fn-cth-publication-setup next frontier revision log seg profile cfg free alen hlen))
         (tables (fn-sct-tables-of-capture next frontier revision log))
         (estimate (+ (nfix hlen) (nfix alen)
                      (len (fn-sct-file-octets
                            (fn-sct-table-programs tables (fn-sco-event-index next)) seg s)))))
    (implies (not (equal (car setup) :unencodable))
             (and (equal (nth 6 setup) estimate)
                  (iff (equal (car (car setup)) :plan)
                       (and (<= estimate (nfix (fn-cth-publication-budget profile next cfg)))
                            (natp free)
                            (<= estimate (fn-ockp-space free)))))))
  :rule-classes nil
  :hints (("Goal" :use k8-try :in-theory (theory (quote minimal-theory)))))

; K8c (the three admissions compose): admitting X then Y from T0 is
; admitting X ++ Y from T0.  With K8a and K8t (each run's total carried
; into the next, the header's from 0) the whole file's admission is the
; writer's, which is K7's premise.  (natp T0): the running total is a
; natural at every executable call (0 or a carried total); without it X =
; NIL, T0 = -1 is a counterexample (the empty run answers 0, the -1 start
; refuses), found by the proof attempt, not by test? (rule 6b-1).
(defthm fn-cth-admit-run-of-append
  (implies (and (natp t0) (natp (fn-cth-admit-run x t0 sb fb)))
           (equal (fn-cth-admit-run (append x y) t0 sb fb)
                  (fn-cth-admit-run y (fn-cth-admit-run x t0 sb fb) sb fb)))
  :rule-classes nil
  :hints (("Goal" :use k8c-try :in-theory (theory (quote minimal-theory)))))

; K9 (the seed of a file written from one capture, Codex r3 F2): the open
; over the checkpoint of PREFIX, its suffix applied, installs from the
; header of the SAME capture's file the seed fn-cth-installed-seed gives
; with the open's own verdict as the flag, and that seed is a valid cache
; for the opened records.  Scope: writer provenance -- H and REST come
; from one capture (the atomic staged write; a deliberately mixed but
; correctly framed file is outside this statement).  On a refused open the
; seed is the empty cache, valid for whatever records the fallback replay
; opens (RECORDS).
(defthm fn-cth-seed-of-one-capture-is-valid
  (let* ((c (fn-sco-capture configs prefix))
         (segs (append (fn-cth-header-segments (fn-cth-header-of-capture c) (len prefix)) rest))
         (o (fn-sco-open c configs frontier suffix)))
    (implies (and (fn-cth-header-encodablep (fn-cth-header-of-capture c))
                  (< (len prefix) *fn-scc-u64-bound*))
             (fn-ct-totals-cache-validp
              (fn-cth-installed-seed (fn-sn-open-okp o) (len prefix) (fn-cth-header-tot segs) :resident)
              (if (fn-sn-open-okp o)
                  (fn-sf-records (fn-sn-files (fn-sn-open-state o)))
                records)
              :resident)))
  :rule-classes nil
  :hints (("Goal" :use k9-try :in-theory (theory (quote minimal-theory)))))

; K10 (the loader gets exactly REST, Codex r3 F6): the header run is one
; segment for every row and S, so the file after it is REST, the segments
; fn-scka-load-of-written-file (books/store-checkpoint-arena-load.lisp)
; loads; the host's plan omits H's frame and its octets.
(defthm fn-cth-header-run-is-one-segment
  (equal (cdr (append (fn-cth-header-segments row s) rest)) rest)
  :rule-classes nil
  :hints (("Goal" :use k10-try :in-theory (theory (quote minimal-theory)))))
