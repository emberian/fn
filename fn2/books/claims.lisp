; The identity claim table (layer D, quest D5; fn2/docs/d-machines-nntp.md
; section 14.4.2; D0's :identity-reservation, rank 12). One row per
; transaction slot. A transaction claims the exact octets of its
; Message-ID: at most one row holds a claim on given octets at a time, and
; a second claimant of the same octets waits in the holder's FIFO, holding
; nothing, until the holder releases; the release hands the claim to the
; FIFO's head in the same step (no barging, no lost wakeup). So
; same-Message-ID offers on one node never race through C's identity
; decision.
;
; Buckets are the rows themselves: row r's HEAD and STAMP are bucket r's
; (hash modulo the row count). A bucket chain is doubly linked through
; NEXT and PREV. A claimant walks its bucket at most BUDGET rows per call
; (the continuation is its CURSOR); every insertion or removal bumps the
; bucket's STAMP, and a walk whose stamp moved starts again from the head,
; so a walk never misses a claim inserted behind it. Octets are compared
; only on an equal hash and length, each under its own owner
; (fn2-pool-compare). A library; the transaction machine's core wrappers
; and their defcosts come with D5 1/n.
(in-package "ACL2")
(include-book "pool-ranges")
(include-book "std/util/bstar" :dir :system)
(fn2-book-layer :d)

(defcolumns fn2-claims
  ((state (:enum fn2-claim-state (:free :walking :held :waiting)))
   (hash :u32) (slot :u32) (gen :u60) (off :u32) (len :u32) (ok :u8) (os :u32) (og :u60)
   (next :link) (prev :link) (wait-head :link) (wait-tail :link) (wait-next :link)
   (head :link) (stamp :u60) (cursor :link) (wstamp :u60)))

(defun fn2-claim-rowp (c fn2-claims)
  (declare (xargs :stobjs fn2-claims :guard (fn2-claims-wfp fn2-claims)))
  (and (natp c) (< c (fn2-claims-rows fn2-claims)) (unsigned-byte-p 32 c)))
(defun fn2-claim-bucket (hash fn2-claims)
  (declare (xargs :stobjs fn2-claims :guard (fn2-claims-wfp fn2-claims)))
  (let ((n (fn2-claims-rows fn2-claims))) (if (posp n) (mod (nfix hash) n) 0)))

; Start row C's claim on [off, off+len) of SLOT under (ok os og), whose
; FNV-1a hash is HASH. Refused :state unless C is free.
(defun fn2-claim-begin (c hash slot gen off len ok os og fn2-claims)
  (declare (xargs :stobjs fn2-claims :guard (fn2-claims-wfp fn2-claims)))
  (b* (((unless (fn2-claim-rowp c fn2-claims)) (mv :bounds fn2-claims))
       ((unless (equal (fn2-claims-state c fn2-claims) *fn2-claim-state-free*)) (mv :state fn2-claims))
       ((unless (and (unsigned-byte-p 32 hash) (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
                     (unsigned-byte-p 32 off) (unsigned-byte-p 32 len) (unsigned-byte-p 8 ok)
                     (unsigned-byte-p 32 os) (unsigned-byte-p 60 og)))
        (mv :bounds fn2-claims))
       (b (fn2-claim-bucket hash fn2-claims))
       ((unless (fn2-claim-rowp b fn2-claims)) (mv :bounds fn2-claims))
       (fn2-claims (fn2-claims-put c (state *fn2-claim-state-walking*) (hash hash) (slot slot) (gen gen)
                                   (off off) (len len) (ok ok) (os os) (og og)
                                   (next *fn2-none*) (prev *fn2-none*) (wait-head *fn2-none*)
                                   (wait-tail *fn2-none*) (wait-next *fn2-none*)
                                   (cursor (fn2-claims-head b fn2-claims)) (wstamp (fn2-claims-stamp b fn2-claims)))))
    (mv :ok fn2-claims)))
(fn2-claims-preserves fn2-claim-begin (c hash slot gen off len ok os og fn2-claims) :position 1 :raw-rows t)

; Whether row X holds a claim on the same octets as row C.
(defun fn2-claim-same (c x fn2-claims fn2-pool)
  (declare (xargs :stobjs (fn2-claims fn2-pool)
                  :guard (and (fn2-claims-wfp fn2-claims) (fn2-pool-wfp fn2-pool)
                              (fn2-claim-rowp c fn2-claims) (fn2-claim-rowp x fn2-claims))))
  (and (equal (fn2-claims-state x fn2-claims) *fn2-claim-state-held*)
       (equal (fn2-claims-hash x fn2-claims) (fn2-claims-hash c fn2-claims))
       (equal (fn2-claims-len x fn2-claims) (fn2-claims-len c fn2-claims))
       (mv-let (code order at)
         (fn2-pool-compare (fn2-claims-slot c fn2-claims) (fn2-claims-gen c fn2-claims) (fn2-claims-off c fn2-claims)
                           (fn2-claims-ok c fn2-claims) (fn2-claims-os c fn2-claims) (fn2-claims-og c fn2-claims)
                           (fn2-claims-slot x fn2-claims) (fn2-claims-gen x fn2-claims) (fn2-claims-off x fn2-claims)
                           (fn2-claims-ok x fn2-claims) (fn2-claims-os x fn2-claims) (fn2-claims-og x fn2-claims)
                           (fn2-claims-len c fn2-claims) fn2-pool)
         (declare (ignore at))
         (and (eq code :ok) (eq order :equal)))))
(in-theory (disable fn2-claim-same))

; Link row C at the head of its bucket and mark it held.
(defun fn2-claim-link (c fn2-claims)
  (declare (xargs :stobjs fn2-claims :guard (fn2-claims-wfp fn2-claims)))
  (b* (((unless (fn2-claim-rowp c fn2-claims)) (mv :bounds fn2-claims))
       (b (fn2-claim-bucket (fn2-claims-hash c fn2-claims) fn2-claims))
       ((unless (fn2-claim-rowp b fn2-claims)) (mv :bounds fn2-claims))
       (h (fn2-claims-head b fn2-claims))
       (stamp (+ 1 (fn2-claims-stamp b fn2-claims)))
       ((unless (unsigned-byte-p 60 stamp)) (mv :bounds fn2-claims))
       (fn2-claims (if (fn2-claim-rowp h fn2-claims) (fn2-claims-set-prev h c fn2-claims) fn2-claims))
       (fn2-claims (fn2-claims-put c (state *fn2-claim-state-held*) (next h) (prev *fn2-none*) (cursor *fn2-none*)))
       (fn2-claims (fn2-claims-put b (head c) (stamp stamp))))
    (mv :ok fn2-claims)))
(fn2-claims-preserves fn2-claim-link (c fn2-claims) :position 1 :raw-rows t)

; Append C to X's FIFO and mark C waiting.
(defun fn2-claim-enqueue (x c fn2-claims)
  (declare (xargs :stobjs fn2-claims :guard (fn2-claims-wfp fn2-claims)))
  (if (not (and (fn2-claim-rowp x fn2-claims) (fn2-claim-rowp c fn2-claims))) fn2-claims
    (b* ((tail (fn2-claims-wait-tail x fn2-claims))
         (fn2-claims (if (fn2-claim-rowp tail fn2-claims) (fn2-claims-set-wait-next tail c fn2-claims)
                       (fn2-claims-set-wait-head x c fn2-claims)))
         (fn2-claims (fn2-claims-set-wait-tail x c fn2-claims)))
      (fn2-claims-put c (state *fn2-claim-state-waiting*) (wait-next *fn2-none*) (cursor *fn2-none*)))))
(fn2-claims-preserves fn2-claim-enqueue (x c fn2-claims) :raw-rows t)
; Move C's walk past row X.
(defun fn2-claim-advance (c x fn2-claims)
  (declare (xargs :stobjs fn2-claims :guard (fn2-claims-wfp fn2-claims)))
  (if (not (and (fn2-claim-rowp x fn2-claims) (fn2-claim-rowp c fn2-claims))) fn2-claims
    (fn2-claims-set-cursor c (fn2-claims-next x fn2-claims) fn2-claims)))
(fn2-claims-preserves fn2-claim-advance (c x fn2-claims) :raw-rows t)

; Walk C's bucket at most BUDGET rows: (mv code holder fn2-claims). :claimed
; (C now holds its octets), :wait (HOLDER holds them; C is appended to its
; FIFO and waits), :more (resume), or a refusal.
(defun fn2-claim-walk-loop (budget c fn2-claims fn2-pool)
  (declare (xargs :stobjs (fn2-claims fn2-pool) :measure (nfix budget)
                  :guard (and (fn2-claims-wfp fn2-claims) (fn2-pool-wfp fn2-pool) (natp budget)
                              (fn2-claim-rowp c fn2-claims))))
  (b* ((x (fn2-claims-cursor c fn2-claims))
       ((unless (fn2-claim-rowp x fn2-claims))
        (mv-let (code fn2-claims) (fn2-claim-link c fn2-claims)
          (mv (if (eq code :ok) :claimed code) *fn2-none* fn2-claims)))
       ((when (zp budget)) (mv :more *fn2-none* fn2-claims))
       ((when (and (not (equal x c)) (fn2-claim-same c x fn2-claims fn2-pool)))
        (let ((fn2-claims (fn2-claim-enqueue x c fn2-claims))) (mv :wait x fn2-claims)))
       (fn2-claims (fn2-claim-advance c x fn2-claims)))
    (fn2-claim-walk-loop (- budget 1) c fn2-claims fn2-pool)))
(fn2-claims-preserves fn2-claim-walk-loop (budget c fn2-claims fn2-pool) :position 2 :raw-rows t)

(defun fn2-claim-walk (c budget fn2-claims fn2-pool)
  (declare (xargs :stobjs (fn2-claims fn2-pool)
                  :guard (and (fn2-claims-wfp fn2-claims) (fn2-pool-wfp fn2-pool) (natp budget))))
  (b* (((unless (fn2-claim-rowp c fn2-claims)) (mv :bounds *fn2-none* fn2-claims))
       ((unless (equal (fn2-claims-state c fn2-claims) *fn2-claim-state-walking*)) (mv :state *fn2-none* fn2-claims))
       (b (fn2-claim-bucket (fn2-claims-hash c fn2-claims) fn2-claims))
       ((unless (fn2-claim-rowp b fn2-claims)) (mv :bounds *fn2-none* fn2-claims))
       ;; the bucket changed since the walk began: start again from its head
       (fn2-claims (if (equal (fn2-claims-stamp b fn2-claims) (fn2-claims-wstamp c fn2-claims)) fn2-claims
                     (fn2-claims-put c (cursor (fn2-claims-head b fn2-claims)) (wstamp (fn2-claims-stamp b fn2-claims))))))
    (fn2-claim-walk-loop budget c fn2-claims fn2-pool)))
(fn2-claims-preserves fn2-claim-walk (c budget fn2-claims fn2-pool) :position 2 :raw-rows t)

; Unlink held row C from its bucket chain and free it; (mv code w tail
; fn2-claims): W and TAIL its FIFO's head and tail before it was cleared.
(defun fn2-claim-unlink (c fn2-claims)
  (declare (xargs :stobjs fn2-claims :guard (fn2-claims-wfp fn2-claims)))
  (b* (((unless (fn2-claim-rowp c fn2-claims)) (mv :bounds *fn2-none* *fn2-none* fn2-claims))
       ((unless (equal (fn2-claims-state c fn2-claims) *fn2-claim-state-held*))
        (mv :state *fn2-none* *fn2-none* fn2-claims))
       (b (fn2-claim-bucket (fn2-claims-hash c fn2-claims) fn2-claims))
       ((unless (fn2-claim-rowp b fn2-claims)) (mv :bounds *fn2-none* *fn2-none* fn2-claims))
       (n (fn2-claims-next c fn2-claims)) (p (fn2-claims-prev c fn2-claims))
       (stamp (+ 1 (fn2-claims-stamp b fn2-claims)))
       ((unless (unsigned-byte-p 60 stamp)) (mv :bounds *fn2-none* *fn2-none* fn2-claims))
       (fn2-claims (if (fn2-claim-rowp n fn2-claims) (fn2-claims-set-prev n p fn2-claims) fn2-claims))
       (fn2-claims (if (fn2-claim-rowp p fn2-claims) (fn2-claims-set-next p n fn2-claims)
                     (fn2-claims-set-head b n fn2-claims)))
       (fn2-claims (fn2-claims-set-stamp b stamp fn2-claims))
       (w (fn2-claims-wait-head c fn2-claims)) (tail (fn2-claims-wait-tail c fn2-claims))
       (fn2-claims (fn2-claims-put c (state *fn2-claim-state-free*) (next *fn2-none*) (prev *fn2-none*)
                                   (wait-head *fn2-none*) (wait-tail *fn2-none*) (wait-next *fn2-none*)
                                   (cursor *fn2-none*))))
    (mv :ok w tail fn2-claims)))
(fn2-claims-preserves fn2-claim-unlink (c fn2-claims) :position 3 :raw-rows t)

; Hand the claim to waiter W, whose FIFO becomes the rest (TAIL the old tail).
(defun fn2-claim-handoff (w tail fn2-claims)
  (declare (xargs :stobjs fn2-claims :guard (fn2-claims-wfp fn2-claims)))
  (b* (((unless (fn2-claim-rowp w fn2-claims)) (mv :ok fn2-claims))
       ((unless (equal (fn2-claims-state w fn2-claims) *fn2-claim-state-waiting*)) (mv :state fn2-claims))
       (rest (fn2-claims-wait-next w fn2-claims))
       ((unless (unsigned-byte-p 32 tail)) (mv :bounds fn2-claims))
       (fn2-claims (fn2-claims-put w (wait-head rest) (wait-tail (if (fn2-claim-rowp rest fn2-claims) tail *fn2-none*))
                                   (wait-next *fn2-none*))))
    (fn2-claim-link w fn2-claims)))
(fn2-claims-preserves fn2-claim-handoff (w tail fn2-claims) :position 1 :raw-rows t)

; Release C's claim: unlink it; if a claimant waits, the FIFO's head W takes
; the claim with the rest of the FIFO in the same step. (mv code w
; fn2-claims), W *fn2-none* when nobody waited.
(defun fn2-claim-release (c fn2-claims)
  (declare (xargs :stobjs fn2-claims :guard (fn2-claims-wfp fn2-claims)))
  (b* (((mv code w tail fn2-claims) (fn2-claim-unlink c fn2-claims))
       ((unless (eq code :ok)) (mv code *fn2-none* fn2-claims))
       ((unless (fn2-claim-rowp w fn2-claims)) (mv :ok *fn2-none* fn2-claims))
       ((mv code fn2-claims) (fn2-claim-handoff w tail fn2-claims)))
    (mv code w fn2-claims)))
(fn2-claims-preserves fn2-claim-release (c fn2-claims) :position 2 :raw-rows t)

(defun fn2-claims-init-buckets (left fn2-claims)
  (declare (xargs :stobjs fn2-claims :measure (nfix left)
                  :guard (and (fn2-claims-wfp fn2-claims) (natp left) (<= left (fn2-claims-rows fn2-claims)))))
  (if (zp left) fn2-claims
    (let ((fn2-claims (fn2-claims-put (- left 1) (state *fn2-claim-state-free*) (head *fn2-none*) (next *fn2-none*)
                                      (prev *fn2-none*) (wait-head *fn2-none*) (wait-tail *fn2-none*)
                                      (wait-next *fn2-none*) (cursor *fn2-none*) (stamp 0))))
      (fn2-claims-init-buckets (- left 1) fn2-claims))))
(defun fn2-claims-table-init (n fn2-claims)
  (declare (xargs :stobjs fn2-claims :guard (unsigned-byte-p 32 n)))
  (let ((fn2-claims (fn2-claims-init n fn2-claims)))
    (fn2-claims-init-buckets (fn2-claims-rows fn2-claims) fn2-claims)))

(assert-event
 (fn2-assert-compliant-p '(fn2-claim-begin fn2-claim-same fn2-claim-link fn2-claim-enqueue fn2-claim-advance
                           fn2-claim-walk-loop fn2-claim-walk
                           fn2-claim-unlink fn2-claim-handoff fn2-claim-release fn2-claims-table-init)
                         (w state)))
