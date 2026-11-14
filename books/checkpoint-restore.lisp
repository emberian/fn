; Recovery input frontier over actual B-format bytes. No serving/readiness or
; allocator mutation occurs here. Boot must finish candidate selection, roots,
; exact allocator restore, reachability protections and ordered suffix replay.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "checkpoint")
(include-book "checkpoint-restore-read")
(include-book "checkpoint-geometry")
(fn2-book-layer :b)

; Private scratch references must be beyond the candidate reference bank.
; Capturing a link never overwrites an authenticated descriptor root.
(defun fn2-checkpoint-restore-capture-ref (f r base slot gen okind oslot ogen
                                         fn2-fields fn2-pool fn2-checkpoint-refs fn2-checkpoint-bytes)
 (declare (xargs :stobjs (fn2-fields fn2-pool fn2-checkpoint-refs fn2-checkpoint-bytes)
  :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool)
              (fn2-checkpoint-refs-wfp fn2-checkpoint-refs) (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes))))
 (b* (((unless (and (natp f) (natp base) (natp r)
                     (<= (+ base f 7) (fn2-fields-rows fn2-fields))
                     (< r (fn2-checkpoint-refs-rows fn2-checkpoint-refs))
                     (<= (* 32 (+ r 1)) (fn2-checkpoint-bytes-rows fn2-checkpoint-bytes))
                     (equal (fn2-fields-value (+ base f 6) fn2-fields) 1)))
       (mv :bounds fn2-checkpoint-refs fn2-checkpoint-bytes))
      ((mv code fn2-checkpoint-bytes)
       (fn2-checkpoint-copy-hash 32 (* 32 r) (fn2-fields-ref-off (+ base f 6) fn2-fields)
         slot gen okind oslot ogen fn2-pool fn2-checkpoint-bytes))
      ((unless (eq code :ok)) (mv code fn2-checkpoint-refs fn2-checkpoint-bytes))
      (fn2-checkpoint-refs (fn2-checkpoint-refs-set-storage-domain r (fn2-fields-value (+ base f 0) fn2-fields) fn2-checkpoint-refs))
      (fn2-checkpoint-refs (fn2-checkpoint-refs-set-physical-unit r (fn2-fields-value (+ base f 1) fn2-fields) fn2-checkpoint-refs))
      (fn2-checkpoint-refs (fn2-checkpoint-refs-set-writer-epoch r (fn2-fields-value (+ base f 2) fn2-fields) fn2-checkpoint-refs))
      (fn2-checkpoint-refs (fn2-checkpoint-refs-set-allocation r (fn2-fields-value (+ base f 3) fn2-fields) fn2-checkpoint-refs))
      (fn2-checkpoint-refs (fn2-checkpoint-refs-set-page-kind r (fn2-fields-value (+ base f 4) fn2-fields) fn2-checkpoint-refs))
      (fn2-checkpoint-refs (fn2-checkpoint-refs-set-encoded-length r (fn2-fields-value (+ base f 5) fn2-fields) fn2-checkpoint-refs))
      (fn2-checkpoint-refs (fn2-checkpoint-ref-clear-build r fn2-checkpoint-refs)))
  (mv :ok fn2-checkpoint-refs fn2-checkpoint-bytes)))

; Bounded anchor hash/framing check and candidate capture are inseparable.
; ROW's location is the actual anchor slot; its geometry digest must be loaded
; from the bootstrap-owned geometry before this call. This does not select a
; winner: every structurally valid target, including a singleton, must be read.
(defun fn2-checkpoint-restore-anchor-step (c anchor row slot gen len base okind oslot ogen budget
                                          fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
                                          fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
 (declare (xargs :stobjs (fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
                          fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
  :guard (and (let ((off 0)) (fn2-fc-guard)) (fn2-checkpoints-wfp fn2-checkpoints)
              (fn2-checkpoint-refs-wfp fn2-checkpoint-refs) (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes))))
 (b* (((unless (and (fn2-checkpoint-slotp c fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)
                     (equal (fn2-checkpoints-state c fn2-checkpoints) *fn2-checkpoint-state-free*)
                     (natp anchor) (< anchor 4) (posp len) (<= len *fn2-format-anchor-max-size*)
                     (equal (fn2-fc-context-location row fn2-fc-context) anchor)))
       (mv :state fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fc fn2-b3 fn2-fields fn2-pool fn2-digests))
      ((mv code fn2-fc fn2-b3 fn2-fields fn2-pool fn2-digests)
       (fn2-format-run :anchor nil row slot gen 0 len base okind oslot ogen budget
         fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
      ((unless (eq code :ok))
       (mv code fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fc fn2-b3 fn2-fields fn2-pool fn2-digests))
      (f *fn2-format-anchor-field-descriptor-storage-domain*)
      ((unless (and
         (posp (fn2-fields-value (+ base *fn2-format-anchor-field-checkpoint*) fn2-fields))
         (equal (fn2-fields-value (+ base f) fn2-fields) *fn2-checkpoint-served-storage-domain*)
         (equal (fn2-fields-value (+ base f 4) fn2-fields) *page-kind-checkpoint-descriptor*)
         (equal (fn2-fields-value (+ base f 5) fn2-fields) *fn2-format-sector-size*)
         (equal (mod (fn2-fields-value (+ base f 1) fn2-fields) *fn2-storage-extent-units*) 0)))
       (mv :descriptor fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fc fn2-b3 fn2-fields fn2-pool fn2-digests))
      ((mv code fn2-checkpoint-refs fn2-checkpoint-bytes)
       (fn2-checkpoint-restore-capture-ref f (* 6 c) base slot gen okind oslot ogen
         fn2-fields fn2-pool fn2-checkpoint-refs fn2-checkpoint-bytes))
      ((unless (eq code :ok))
       (mv code fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fc fn2-b3 fn2-fields fn2-pool fn2-digests))
      (fn2-checkpoints (fn2-checkpoints-put c
        (state *fn2-checkpoint-state-preparing*) (bank (floor anchor 2)) (anchor-mask (ash 1 anchor))
        (checkpoint (fn2-fields-value (+ base *fn2-format-anchor-field-checkpoint*) fn2-fields))
        (history (fn2-fields-value (+ base *fn2-format-anchor-field-history*) fn2-fields))
        (incarnation (fn2-fields-value (+ base *fn2-format-anchor-field-incarnation*) fn2-fields))
        (builder-token 0) (builder-owner-kind 0) (builder-owner-slot 0) (builder-owner-gen 0))))
  (mv :candidate fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fc fn2-b3 fn2-fields fn2-pool fn2-digests)))

; Read planner for the descriptor or an authenticated descriptor root. The
; target is returned from the candidate's concrete Ref, never recomputed by
; the host. A 64KiB page is consumed through sector-sized reads by the boot
; machine; this leaf returns one sector and the caller's next byte cursor.
(defun fn2-checkpoint-restore-read-target (c role cursor extents fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)
 (declare (xargs :stobjs (fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)
  :guard (and (fn2-checkpoints-wfp fn2-checkpoints) (fn2-checkpoint-refs-wfp fn2-checkpoint-refs)
              (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes))))
 (b* (((unless (and (fn2-checkpoint-slotp c fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)
                     (natp role) (< role 6) (natp cursor) (posp extents)
                     (if (equal role 0)
                       (equal (fn2-checkpoints-state c fn2-checkpoints) *fn2-checkpoint-state-preparing*)
                       (equal (fn2-checkpoints-state c fn2-checkpoints) *fn2-checkpoint-state-checked*))))
       (mv :state 0 0 0))
      (r (+ (* 6 c) role))
      (unit (fn2-checkpoint-refs-physical-unit r fn2-checkpoint-refs))
      (len (fn2-checkpoint-refs-encoded-length r fn2-checkpoint-refs))
      ((unless (and (equal (fn2-checkpoint-refs-storage-domain r fn2-checkpoint-refs) 0)
                     (equal (mod unit *fn2-storage-extent-units*) 0)
                     (< (floor unit *fn2-storage-extent-units*) extents)
                     (posp len) (<= len *fn2-format-page-size*) (< cursor len)
                     (equal (mod cursor *fn2-format-sector-size*) 0)))
       (mv :bounds 0 0 0))
      (n *fn2-format-sector-size*))
  (mv :read (+ (* unit *fn2-format-sector-size*) cursor) n (+ cursor n))))

; Load one immutable expected digest into checker-owned input storage. The
; stripe's FC-HASH region is outside its hash-engine mutable result/frontier.
(defun fn2-checkpoint-restore-load-hash (i r hash fn2-checkpoint-bytes fn2-digests)
 (declare (xargs :stobjs (fn2-checkpoint-bytes fn2-digests) :measure (nfix (- 8 (nfix i)))
  :guard (and (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes) (natp r)
              (<= (* 32 (+ r 1)) (fn2-checkpoint-bytes-rows fn2-checkpoint-bytes))
              (fn2-digest-rowp hash fn2-digests) (natp i) (<= i 8))))
 (if (or (not (natp i)) (>= i 8)) fn2-digests
  (let* ((at (+ (* 32 r) (* 4 i)))
         (word (+ (fn2-checkpoint-bytes-value at fn2-checkpoint-bytes)
                  (* 256 (fn2-checkpoint-bytes-value (+ at 1) fn2-checkpoint-bytes))
                  (* 65536 (fn2-checkpoint-bytes-value (+ at 2) fn2-checkpoint-bytes))
                  (* 16777216 (fn2-checkpoint-bytes-value (+ at 3) fn2-checkpoint-bytes))))
         (fn2-digests (fn2-digest-set-word hash i word fn2-digests)))
   (fn2-checkpoint-restore-load-hash (+ i 1) r hash fn2-checkpoint-bytes fn2-digests))))
