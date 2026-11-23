; The commit kind's span loops against their bytewise models.
; fn2-commit-zero, fn2-commit-copy-in and fn2-commit-copy-bytes each make one
; bulk span call on the pool (fn2-pool-zero-span, fn2-rd-copy-span). The
; models below are the per-octet loops they replaced, one checked
; fn2-core-write (and fn2-core-read) per octet. The theorems equate result
; code and core exactly, on accepted, refused and aliased spans alike; the
; executable checks run both on one scenario and compare every code, fill
; and octet with each other and with the stated values.
(in-package "ACL2")
(include-book "../books/assembly-callbacks-b2")
(include-book "std/util/bstar" :dir :system)

; ------------------------------------------------------------------------
; The bytewise models.
(defun fn2-commit-zero-bytewise-spec (left at slot gen id ogen fn2-core)
  (declare (xargs :stobjs fn2-core :measure (nfix left)
                  :guard (and (fn2-core-wfp fn2-core) (natp left) (natp at))))
  (if (or (zp left) (>= at *fn2-commit-unit-bytes*)) (mv :ok fn2-core)
    (mv-let (code fn2-core) (fn2-core-write slot gen at 0 *fn2-commit-kind* id ogen fn2-core)
      (if (eq code :ok) (fn2-commit-zero-bytewise-spec (- left 1) (+ at 1) slot gen id ogen fn2-core)
        (mv code fn2-core)))))

(defun fn2-commit-copy-in-bytewise-spec (left dst dg off from fg at fkind fid fgen id ogen fn2-core)
  (declare (xargs :stobjs fn2-core :measure (nfix left)
                  :guard (and (fn2-core-wfp fn2-core) (natp left) (natp off) (natp at))))
  (if (zp left) (mv :ok fn2-core)
    (b* (((mv code byte) (fn2-core-read from fg at fkind fid fgen fn2-core))
         ((unless (eq code :ok)) (mv code fn2-core))
         ((mv code fn2-core) (fn2-core-write dst dg off byte *fn2-commit-kind* id ogen fn2-core)))
      (if (eq code :ok)
          (fn2-commit-copy-in-bytewise-spec (- left 1) dst dg (+ off 1) from fg (+ at 1) fkind fid fgen id ogen fn2-core)
        (mv code fn2-core)))))

(defun fn2-commit-copy-bytes-bytewise-spec (left src sg off from fg at from-id from-ogen id ogen fn2-core)
  (declare (xargs :stobjs fn2-core :measure (nfix left)
                  :guard (and (fn2-core-wfp fn2-core) (natp left) (natp off) (natp at))))
  (if (zp left) (mv :ok fn2-core)
    (b* (((mv code byte) (fn2-core-read from fg at *fn2-commit-kind* from-id from-ogen fn2-core))
         ((unless (eq code :ok)) (mv code fn2-core))
         ((mv code fn2-core) (fn2-core-write src sg off byte *fn2-commit-kind* id ogen fn2-core)))
      (if (eq code :ok)
          (fn2-commit-copy-bytes-bytewise-spec (- left 1) src sg (+ off 1) from fg (+ at 1) from-id from-ogen id ogen fn2-core)
        (mv code fn2-core)))))

; ------------------------------------------------------------------------
; The pool field of the core: a read after a write returns the written pool,
; the last of two writes wins, and writing back the pool a core holds is
; that core.
(local (defthm fn2-csu-pool-of-update
  (equal (fn2-core-pool (update-fn2-core-pool p c)) p)
  :hints (("Goal" :in-theory (enable fn2-core-pool update-fn2-core-pool)))))
(local (defthm fn2-csu-update-update
  (equal (update-fn2-core-pool a (update-fn2-core-pool b c)) (update-fn2-core-pool a c))
  :hints (("Goal" :in-theory (enable update-fn2-core-pool)))))
(local (defthm fn2-csu-update-self
  (implies (fn2-corep c) (equal (update-fn2-core-pool (fn2-core-pool c) c) c))
  :hints (("Goal" :in-theory (enable fn2-corep fn2-core-pool update-fn2-core-pool)))))
(local (defthm fn2-csu-zero-bytes-zp
  (implies (zp n)
           (equal (fn2-pool-zero-bytes n slot gen off okind oslot ogen fn2-pool)
                  (mv :ok fn2-pool)))
  :hints (("Goal" :expand ((fn2-pool-zero-bytes n slot gen off okind oslot ogen fn2-pool))))))
(local (defthm fn2-csu-rd-copy-zp
  (implies (zp n)
           (equal (fn2-rd-copy n sslot sgen soff sk ss sg dslot dgen doff dk ds dg fn2-pool)
                  (mv :ok fn2-pool)))
  :hints (("Goal" :in-theory (enable fn2-rd-copy)))))

; ------------------------------------------------------------------------
; Each model is the pool's bytewise loop run on the core's pool. Zero holds
; for any core: a refused write still writes back the pool it read. The
; copies are stated over a core whose pool is P, since a refused read
; returns the core untouched.
(defthm fn2-commit-zero-bytewise-spec-is-zero-bytes
  (implies (natp at)
           (equal (fn2-commit-zero-bytewise-spec left at slot gen id ogen fn2-core)
                  (if (or (zp left) (>= at *fn2-commit-unit-bytes*)) (mv :ok fn2-core)
                    (mv (mv-nth 0 (fn2-pool-zero-bytes (min left (- *fn2-commit-unit-bytes* at)) slot gen at
                                                       *fn2-commit-kind* id ogen (fn2-core-pool fn2-core)))
                        (update-fn2-core-pool
                         (mv-nth 1 (fn2-pool-zero-bytes (min left (- *fn2-commit-unit-bytes* at)) slot gen at
                                                        *fn2-commit-kind* id ogen (fn2-core-pool fn2-core)))
                         fn2-core)))))
  :hints (("Goal" :induct (fn2-commit-zero-bytewise-spec left at slot gen id ogen fn2-core)
           :in-theory (e/d (fn2-core-write) (fn2-pool-write))
           :expand ((:free (p) (fn2-pool-zero-bytes left slot gen at *fn2-commit-kind* id ogen p))
                    (:free (a p) (fn2-pool-zero-bytes 1 slot gen a *fn2-commit-kind* id ogen p))
                    (:free (p) (fn2-pool-zero-bytes (+ *fn2-commit-unit-bytes* (- at)) slot gen at
                                                    *fn2-commit-kind* id ogen p))))))

(defthm fn2-commit-copy-in-bytewise-spec-is-rd-copy
  (equal (fn2-commit-copy-in-bytewise-spec left dst dg off from fg at fkind fid fgen id ogen
                                           (update-fn2-core-pool p c))
         (mv (mv-nth 0 (fn2-rd-copy left from fg at fkind fid fgen dst dg off *fn2-commit-kind* id ogen p))
             (update-fn2-core-pool
              (mv-nth 1 (fn2-rd-copy left from fg at fkind fid fgen dst dg off *fn2-commit-kind* id ogen p))
              c)))
  :hints (("Goal" :induct (fn2-rd-copy left from fg at fkind fid fgen dst dg off *fn2-commit-kind* id ogen p)
           :in-theory (e/d ((:induction fn2-rd-copy) fn2-core-write) (fn2-pool-read fn2-pool-write))
           :expand ((fn2-rd-copy left from fg at fkind fid fgen dst dg off *fn2-commit-kind* id ogen p)
                    (fn2-commit-copy-in-bytewise-spec left dst dg off from fg at fkind fid fgen id ogen
                                                      (update-fn2-core-pool p c))))))

(defthm fn2-commit-copy-bytes-bytewise-spec-is-rd-copy
  (equal (fn2-commit-copy-bytes-bytewise-spec left src sg off from fg at from-id from-ogen id ogen
                                              (update-fn2-core-pool p c))
         (mv (mv-nth 0 (fn2-rd-copy left from fg at *fn2-commit-kind* from-id from-ogen
                                    src sg off *fn2-commit-kind* id ogen p))
             (update-fn2-core-pool
              (mv-nth 1 (fn2-rd-copy left from fg at *fn2-commit-kind* from-id from-ogen
                                     src sg off *fn2-commit-kind* id ogen p))
              c)))
  :hints (("Goal" :induct (fn2-rd-copy left from fg at *fn2-commit-kind* from-id from-ogen
                                       src sg off *fn2-commit-kind* id ogen p)
           :in-theory (e/d ((:induction fn2-rd-copy) fn2-core-write) (fn2-pool-read fn2-pool-write))
           :expand ((fn2-rd-copy left from fg at *fn2-commit-kind* from-id from-ogen
                                 src sg off *fn2-commit-kind* id ogen p)
                    (fn2-commit-copy-bytes-bytewise-spec left src sg off from fg at from-id from-ogen id ogen
                                                         (update-fn2-core-pool p c))))))

; ------------------------------------------------------------------------
; The refinements: on a typed, well-formed core each span loop returns the
; model's code and the model's core, every byte and fill included, whether
; the span is accepted, refused or aliased.
(defthm fn2-commit-zero-refines-bytewise
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core) (natp at))
           (equal (fn2-commit-zero left at slot gen id ogen fn2-core)
                  (fn2-commit-zero-bytewise-spec left at slot gen id ogen fn2-core)))
  :hints (("Goal" :in-theory (e/d (fn2-commit-zero) (fn2-commit-zero-bytewise-spec)))))

(defthm fn2-commit-copy-in-refines-bytewise
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
           (equal (fn2-commit-copy-in left dst dg off from fg at fkind fid fgen id ogen fn2-core)
                  (fn2-commit-copy-in-bytewise-spec left dst dg off from fg at fkind fid fgen id ogen fn2-core)))
  :hints (("Goal" :in-theory (e/d (fn2-commit-copy-in)
                                  (fn2-commit-copy-in-bytewise-spec fn2-commit-copy-in-bytewise-spec-is-rd-copy))
           :use ((:instance fn2-commit-copy-in-bytewise-spec-is-rd-copy
                            (p (fn2-core-pool fn2-core)) (c fn2-core))))))

(defthm fn2-commit-copy-bytes-refines-bytewise
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
           (equal (fn2-commit-copy-bytes left src sg off from fg at from-id from-ogen id ogen fn2-core)
                  (fn2-commit-copy-bytes-bytewise-spec left src sg off from fg at from-id from-ogen id ogen fn2-core)))
  :hints (("Goal" :in-theory (e/d (fn2-commit-copy-bytes)
                                  (fn2-commit-copy-bytes-bytewise-spec fn2-commit-copy-bytes-bytewise-spec-is-rd-copy))
           :use ((:instance fn2-commit-copy-bytes-bytewise-spec-is-rd-copy
                            (p (fn2-core-pool fn2-core)) (c fn2-core))))))

; ------------------------------------------------------------------------
; Executable checks. The tiny profile with four 65536-octet pool slots.
(defconst *fn2-csu-profile*
  (put-assoc-equal :pool-classes '((8 . 64) (4 . 256) (4 . 65536)) *fn2-profile-tiny*))
(assert-event (fn2-core-profilep *fn2-csu-profile*))

; N octets from OFF: BYTE, BYTE+STEP, ... (mod 256), through the checked
; pool write under owner (OKIND OSLOT OGEN).
(defun fn2-csu-fill-pool (n slot gen off byte step okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix n)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp n) (natp off) (natp byte) (natp step))))
  (if (zp n) fn2-pool
    (mv-let (code fn2-pool) (fn2-pool-write slot gen off (mod byte 256) okind oslot ogen fn2-pool)
      (declare (ignore code))
      (fn2-csu-fill-pool (- n 1) slot gen (+ 1 off) (+ byte step) step okind oslot ogen fn2-pool))))
(defun fn2-csu-fill (n slot gen off byte step okind oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (fn2-pool)
    (fn2-csu-fill-pool n slot gen off byte step okind oslot ogen fn2-pool)
    fn2-core))

; Raw octets of the byte array from I, read past any fill.
(defun fn2-csu-octets-pool (i n fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix n)
                  :guard (and (fn2-poolp fn2-pool) (natp i) (natp n)
                              (<= (+ i n) (fn2-pool-data-length fn2-pool)))))
  (if (zp n) nil
    (cons (fn2-pool-datai i fn2-pool) (fn2-csu-octets-pool (+ 1 i) (- n 1) fn2-pool))))
(defun fn2-csu-octets (slot n fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (xs)
    (fn2-csu-octets-pool (fn2-pool-slot-base slot fn2-pool) n fn2-pool)
    xs))
(defun fn2-csu-fill-of (slot fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (x) (fn2-pool-slot-fill slot fn2-pool) x))

; MODE :span runs the commit kind's span loops, :model the bytewise models.
(defun fn2-csu-zero (mode left at slot gen id ogen fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (eq mode :span) (fn2-commit-zero left at slot gen id ogen fn2-core)
    (fn2-commit-zero-bytewise-spec left at slot gen id ogen fn2-core)))
(defun fn2-csu-copy-in (mode left dst dg off from fg at fkind fid fgen id ogen fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (eq mode :span) (fn2-commit-copy-in left dst dg off from fg at fkind fid fgen id ogen fn2-core)
    (fn2-commit-copy-in-bytewise-spec left dst dg off from fg at fkind fid fgen id ogen fn2-core)))
(defun fn2-csu-copy-bytes (mode left src sg off from fg at from-id from-ogen id ogen fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (eq mode :span) (fn2-commit-copy-bytes left src sg off from fg at from-id from-ogen id ogen fn2-core)
    (fn2-commit-copy-bytes-bytewise-spec left src sg off from fg at from-id from-ogen id ogen fn2-core)))

; Four 65536-octet slots (A B D E), one of 256 (S) and one of 64 (F). The
; commit row is (3 0 1) and owns all but B, which belongs to (5 2 9): the
; owner a transaction member's records are copied in from. A and E hold
; #xAB throughout, S its first 100 octets; B holds 1, 8, 15, ... (mod 256).
(defun fn2-csu-run (mode fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((fn2-core (fn2-core-init *fn2-csu-profile* fn2-core))
       ((mv & a ag fn2-core) (fn2-core-reserve 2 3 0 1 fn2-core))
       ((mv & b bg fn2-core) (fn2-core-reserve 2 5 2 9 fn2-core))
       ((mv & d dg fn2-core) (fn2-core-reserve 2 3 0 1 fn2-core))
       ((mv & e eg fn2-core) (fn2-core-reserve 2 3 0 1 fn2-core))
       ((mv & s sg fn2-core) (fn2-core-reserve 1 3 0 1 fn2-core))
       ((mv & f fg fn2-core) (fn2-core-reserve 0 3 0 1 fn2-core))
       (fn2-core (fn2-csu-fill 65536 a ag 0 171 0 3 0 1 fn2-core))
       (fn2-core (fn2-csu-fill 65536 b bg 0 1 7 5 2 9 fn2-core))
       (fn2-core (fn2-csu-fill 65536 e eg 0 171 0 3 0 1 fn2-core))
       (fn2-core (fn2-csu-fill 100 s sg 0 171 0 3 0 1 fn2-core))
       ; Zero: a 65536-octet request stops at the unit's end; one from
       ; inside the unit stops there too; one from the end writes nothing.
       ((mv z1 fn2-core) (fn2-csu-zero mode 65536 0 a ag 0 1 fn2-core))
       ((mv z2 fn2-core) (fn2-csu-zero mode 1000 4000 e eg 0 1 fn2-core))
       ((mv z3 fn2-core) (fn2-csu-zero mode 10 *fn2-commit-unit-bytes* e eg 0 1 fn2-core))
       ; Refused zero spans: another owner's slot; a stale generation; a
       ; span past S's 256-octet capacity, whose model zeroes the 256-octet
       ; prefix before refusing; a span opening a gap past F's fill.
       ((mv z4 fn2-core) (fn2-csu-zero mode 8 0 b bg 0 1 fn2-core))
       ((mv z5 fn2-core) (fn2-csu-zero mode 8 0 a (+ 1 ag) 0 1 fn2-core))
       ((mv z6 fn2-core) (fn2-csu-zero mode 4096 0 s sg 0 1 fn2-core))
       ((mv z7 fn2-core) (fn2-csu-zero mode 5 3 f fg 0 1 fn2-core))
       ; Copy in: B's 65536 octets into D across owners; D onto itself
       ; 4 octets on (an alias, run octet by octet: the copy re-reads what
       ; it wrote); B read under the wrong owner; a source span running past
       ; B's fill, whose model copies the 6-octet prefix before refusing.
       ((mv k1 fn2-core) (fn2-csu-copy-in mode 65536 d dg 0 b bg 0 5 2 9 0 1 fn2-core))
       ((mv k2 fn2-core) (fn2-csu-copy-in mode 8 d dg 4 d dg 0 3 0 1 0 1 fn2-core))
       ((mv k3 fn2-core) (fn2-csu-copy-in mode 16 f fg 0 b bg 0 3 0 1 0 1 fn2-core))
       ((mv k4 fn2-core) (fn2-csu-copy-in mode 10 f fg 0 b bg 65530 5 2 9 0 1 fn2-core))
       ; Copy bytes between the commit row's own slots; a stale
       ; destination; an empty span.
       ((mv k5 fn2-core) (fn2-csu-copy-bytes mode 32 e eg 8000 d dg 1000 0 1 0 1 fn2-core))
       ((mv k6 fn2-core) (fn2-csu-copy-bytes mode 4 e (+ 1 eg) 0 d dg 0 0 1 0 1 fn2-core))
       ((mv k7 fn2-core) (fn2-csu-copy-bytes mode 0 e eg 0 d dg 0 0 1 0 1 fn2-core)))
    (mv (list :codes (list z1 z2 z3 z4 z5 z6 z7 k1 k2 k3 k4 k5 k6 k7)
              :fills (list (fn2-csu-fill-of a fn2-core) (fn2-csu-fill-of b fn2-core)
                           (fn2-csu-fill-of d fn2-core) (fn2-csu-fill-of e fn2-core)
                           (fn2-csu-fill-of s fn2-core) (fn2-csu-fill-of f fn2-core))
              :a (fn2-csu-octets a 65536 fn2-core)
              :d (fn2-csu-octets d 65536 fn2-core)
              :e (fn2-csu-octets e 65536 fn2-core)
              :s (fn2-csu-octets s 256 fn2-core)
              :f (fn2-csu-octets f 64 fn2-core))
        fn2-core)))
(defun fn2-csu (mode)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core (mv-let (r fn2-core) (fn2-csu-run mode fn2-core) r)))

; B's pattern from octet I, N octets long.
(defun fn2-csu-pattern (i n)
  (declare (xargs :guard (and (natp i) (natp n)) :measure (nfix n)))
  (if (zp n) nil (cons (mod (+ 1 (* 7 i)) 256) (fn2-csu-pattern (+ 1 i) (- n 1)))))

(defconst *fn2-csu-expected*
  (list :codes '(:ok :ok :ok :owner :stale :bounds :bounds :ok :ok :owner :bounds :ok :stale :ok)
        :fills '(65536 65536 65536 65536 256 6)
        :a (append (make-list 4096 :initial-element 0) (make-list 61440 :initial-element 171))
        :d (append (fn2-csu-pattern 0 4) (fn2-csu-pattern 0 4) (fn2-csu-pattern 0 4)
                   (fn2-csu-pattern 12 65524))
        :e (append (make-list 4000 :initial-element 171) (make-list 96 :initial-element 0)
                   (make-list 3904 :initial-element 171) (fn2-csu-pattern 1000 32)
                   (make-list 57504 :initial-element 171))
        :s (make-list 256 :initial-element 0)
        :f (append (fn2-csu-pattern 65530 6) (make-list 58 :initial-element 0))))

; The span loops reach the stated codes, fills and octets.
(assert-event (equal (fn2-csu :span) *fn2-csu-expected*))
; And so do the bytewise models: every refusal and every written prefix agree.
(assert-event (equal (fn2-csu :model) (fn2-csu :span)))
(assert-event
 (fn2-assert-compliant-p '(fn2-commit-zero fn2-commit-copy-in fn2-commit-copy-bytes) (w state)))
(value-triple (cw "COMMIT SPAN: unit-clipped zero, 64 KiB cross-owner copy, alias and refused-prefix parity with the bytewise models PASS~%"))
