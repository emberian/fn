; Layer C: a Ribbon filter per sealed run (C2c; FILTERS-2026 item 2).
; Homogeneous Ribbon (Dillinger and Walzer): every key gives one equation
; c . Z = 0 over GF(2)^8, where c is 64 coefficient bits starting at the
; key's slot s and Z holds one byte per slot (r = 8). A homogeneous system
; is always solvable, so a build never fails and never retries; free slots
; take bytes from a generator seeded by the run, so a page is reproducible.
; A probe that finds c . Z /= 0 proves the key absent; zero answers :maybe
; and the reader then reads the run, so :found and :absent still come from
; byte comparisons only. The key is a 64-bit hash (two FNV-1a streams, each
; finalized) of one octet field, seeded per run. It is not cryptographic: a
; key aimed at a run's filter costs an extra run read, never a wrong answer.
;
; Page: B's header (page kind :partitioned-filter); at the header area the
; filter header (fn2-ribbon-header) in a region of the run page header's
; reserved size; Z from *fn2-ribbon-base*, one byte per slot; zero padding.
; Build: start (a writer row the caller opened on a fresh page), clear the
; band, add each key (bounded insertion, any order), finish, then work
; (back substitution from the top slot, the bytes, the close, the header,
; the seal) until :sealed. Every call is bounded; :more resumes.
(in-package "ACL2")
(local (include-book "pool-read-contracts"))
(include-book "runs-page")
(include-book "fnv")
(include-book "words")
(include-book "columns-call-guards")
(fn2-book-layer :c)
(local (in-theory (disable fn2-pool-rows fn2-fields-rows fn2-digests-rows fn2-fc-rows fn2-fc-context-rows fn2-b3-rows)))

(defconst *fn2-ribbon-width* 64)
(defconst *fn2-ribbon-bits* 8)
(deflayout fn2-ribbon-header
 '((schema (:id schema)) (run (:id run)) (seed :u32) (keys :varint) (slots :varint) (width :u8) (bits :u8)))
(assert-event (<= *fn2-ribbon-header-max-size* *fn2-run-page-header-max-size*))
; Z starts where a run page's entries start, so the writer's open is shared.
(defconst *fn2-ribbon-base* *fn2-run-entries-base*)
(defconst *fn2-ribbon-slots-max* (- *fn2-run-page-size* *fn2-ribbon-base*))
; Slots for N keys: an overhead of one sixteenth plus the band width, so
; every start s lies in [0, slots - 64].
(defun fn2-ribbon-slots (n)
 (declare (xargs :guard (natp n)))
 (+ (nfix n) (floor (+ (nfix n) 15) 16) (- *fn2-ribbon-width* 1)))
; The most keys one filter page holds (C-FILTER-ONE-PAGE).
(defconst *fn2-ribbon-keys-max*
 (floor (* 16 (- *fn2-ribbon-slots-max* (+ 15 (- *fn2-ribbon-width* 1)))) 17))
(assert-event (<= (fn2-ribbon-slots *fn2-ribbon-keys-max*) *fn2-ribbon-slots-max*))

;; A width fact in the forms the prover uses: the predicate, natp and the bound.
(defmacro fn2-ribbon-ub (name n hyps term &rest args)
 (let ((natp-name (fn2-columns-sym name "-NATP")) (bound-name (fn2-columns-sym name "-BOUND"))
       (th '(union-theories '(unsigned-byte-p integer-range-p natp (:executable-counterpart expt)) (theory 'minimal-theory))))
  `(progn
    (defthm ,name (implies ,hyps (unsigned-byte-p ,n ,term)) ,@args)
    (defthm ,natp-name (implies ,hyps (natp ,term))
     :rule-classes ,(if (eq hyps t) :type-prescription :rewrite)
     :hints (("Goal" :use ,name :in-theory ,th)))
    (defthm ,bound-name (implies ,hyps (< ,term ,(expt 2 n))) :rule-classes :linear
     :hints (("Goal" :use ,name :in-theory ,th))))))

; ---------------------------------------------------------------------------
; 32-bit words. Each operation's logic fixes its inputs, so its width holds
; unconditionally; under the guard the execution is the plain operation.
; The width facts come from bitops, inside this encapsulate only.
(encapsulate ()
 (local (include-book "centaur/bitops/ihsext-basics" :dir :system))
 (defun fn2-ribbon-xor32 (a b)
  (declare (xargs :guard (and (unsigned-byte-p 32 a) (unsigned-byte-p 32 b))))
  (mbe :logic (logxor (logand a 4294967295) (logand b 4294967295)) :exec (logxor a b)))
 (fn2-ribbon-ub fn2-ribbon-xor32-type 32 t (fn2-ribbon-xor32 a b))
 (defun fn2-ribbon-xor8 (a b)
  (declare (xargs :guard (and (unsigned-byte-p 8 a) (unsigned-byte-p 8 b))))
  (mbe :logic (logxor (logand a 255) (logand b 255)) :exec (logxor a b)))
 (fn2-ribbon-ub fn2-ribbon-xor8-type 8 t (fn2-ribbon-xor8 a b))
 (defun fn2-ribbon-odd32 (a)
  (declare (xargs :guard (unsigned-byte-p 32 a)))
  (mbe :logic (logior (logand a 4294967295) 1) :exec (logior a 1)))
 (fn2-ribbon-ub fn2-ribbon-odd32-type 32 t (fn2-ribbon-odd32 a))
 (defun fn2-ribbon-byte (a)
  (declare (xargs :guard (integerp a)))
  (logand a 255))
 (fn2-ribbon-ub fn2-ribbon-byte-type 8 t (fn2-ribbon-byte a))
 ;; A >> K.
 (defun fn2-ribbon-shr (a k)
  (declare (xargs :guard (and (unsigned-byte-p 32 a) (natp k))))
  (mbe :logic (logand (ash (logand a 4294967295) (- (nfix k))) 4294967295) :exec (ash a (- k))))
 (fn2-ribbon-ub fn2-ribbon-shr-type 32 t (fn2-ribbon-shr a k))
 ;; The low word of (hi:lo) >> 1.
 (defun fn2-ribbon-shr1 (lo hi)
  (declare (xargs :guard (and (unsigned-byte-p 32 lo) (unsigned-byte-p 32 hi))))
  (mbe :logic (logand (logior (ash (logand lo 4294967295) -1) (ash (logand hi 1) 31)) 4294967295)
       :exec (logior (ash lo -1) (ash (logand hi 1) 31))))
 (fn2-ribbon-ub fn2-ribbon-shr1-type 32 t (fn2-ribbon-shr1 lo hi)))
(in-theory (disable fn2-ribbon-xor32 fn2-ribbon-xor8 fn2-ribbon-odd32 fn2-ribbon-byte fn2-ribbon-shr fn2-ribbon-shr1))

; MurmurHash3's finalizer is A's fn2-prng-mix32 (words.lisp); its width in
; the forms this book's guards use.
(fn2-ribbon-ub fn2-prng-mix3232-width 32 t (fn2-prng-mix32 h) :hints (("Goal" :use fn2-prng-mix32-type)))
; A run's seed, from its identifier.
(defun fn2-ribbon-seed (run)
 (declare (xargs :guard (natp run)))
 (fn2-prng-mix32 (fn2-ribbon-xor32 (mod (nfix run) 4294967296)
                                   (fn2-prng-mix32 (mod (floor (nfix run) 4294967296) 4294967296)))))
(fn2-ribbon-ub fn2-ribbon-seed-type 32 t (fn2-ribbon-seed run))
(in-theory (disable fn2-ribbon-seed))

; The two FNV-1a streams over N octets at OFF, read under the owner.
(defun fn2-ribbon-hash-loop (n slot gen off h1 h2 okind oslot ogen fn2-pool)
 (declare (xargs :stobjs fn2-pool :measure (nfix n)
  :guard-hints ((fn2-columns-call-guard-hint 'fn2-ribbon-hash-loop '(fn2-pool-read-byte-type) nil world))
  :guard (and (fn2-pool-wfp fn2-pool) (natp n) (natp off) (unsigned-byte-p 32 h1) (unsigned-byte-p 32 h2))))
 (if (zp n) (mv :ok h1 h2)
  (mv-let (code byte) (fn2-pool-read slot gen off okind oslot ogen fn2-pool)
   (if (not (and (eq code :ok) (unsigned-byte-p 8 byte))) (mv (if (eq code :ok) :bounds code) h1 h2)
    (fn2-ribbon-hash-loop (- n 1) slot gen (+ 1 off) (fn2-fnv-step h1 byte) (fn2-fnv-step h2 byte)
                          okind oslot ogen fn2-pool)))))
(fn2-ribbon-ub fn2-ribbon-hash-loop-h1 32 (and (unsigned-byte-p 32 h1) (unsigned-byte-p 32 h2))
 (mv-nth 1 (fn2-ribbon-hash-loop n slot gen off h1 h2 okind oslot ogen fn2-pool)))
(fn2-ribbon-ub fn2-ribbon-hash-loop-h2 32 (and (unsigned-byte-p 32 h1) (unsigned-byte-p 32 h2))
 (mv-nth 2 (fn2-ribbon-hash-loop n slot gen off h1 h2 okind oslot ogen fn2-pool)))
(in-theory (disable fn2-ribbon-hash-loop))
(defun fn2-ribbon-hash (n slot gen off seed okind oslot ogen fn2-pool)
 (declare (xargs :stobjs fn2-pool
  :guard (and (fn2-pool-wfp fn2-pool) (natp n) (natp off) (unsigned-byte-p 32 seed))))
 (fn2-ribbon-hash-loop n slot gen off (fn2-ribbon-xor32 *fn2-fnv-offset-basis* seed)
                       (fn2-ribbon-xor32 *fn2-fnv-offset-basis* (fn2-prng-mix32 (fn2-ribbon-xor32 seed #x9e3779b9)))
                       okind oslot ogen fn2-pool))
(fn2-ribbon-ub fn2-ribbon-hash-h1 32 t (mv-nth 1 (fn2-ribbon-hash n slot gen off seed okind oslot ogen fn2-pool))
 :hints (("Goal" :use ((:instance fn2-ribbon-hash-loop-h1 (h1 (fn2-ribbon-xor32 *fn2-fnv-offset-basis* seed))
                      (h2 (fn2-ribbon-xor32 *fn2-fnv-offset-basis* (fn2-prng-mix32 (fn2-ribbon-xor32 seed #x9e3779b9)))))))))
(fn2-ribbon-ub fn2-ribbon-hash-h2 32 t (mv-nth 2 (fn2-ribbon-hash n slot gen off seed okind oslot ogen fn2-pool))
 :hints (("Goal" :use ((:instance fn2-ribbon-hash-loop-h2 (h1 (fn2-ribbon-xor32 *fn2-fnv-offset-basis* seed))
                      (h2 (fn2-ribbon-xor32 *fn2-fnv-offset-basis* (fn2-prng-mix32 (fn2-ribbon-xor32 seed #x9e3779b9)))))))))
(in-theory (disable fn2-ribbon-hash))
; A key's start S in [0, slots - 64] and its coefficient (hi:lo), bit 0 set.
(defun fn2-ribbon-place (h1 h2 slots)
 (declare (xargs :guard (and (unsigned-byte-p 32 h1) (unsigned-byte-p 32 h2) (natp slots))))
 (let* ((a (fn2-prng-mix32 h1)) (b (fn2-prng-mix32 h2)))
  (mv (floor (* a (nfix (- slots (- *fn2-ribbon-width* 1)))) 4294967296)
      (fn2-ribbon-odd32 b)
      (fn2-prng-mix32 (fn2-ribbon-xor32 a (fn2-ribbon-xor32 b #x9e3779b9))))))
(defthm fn2-ribbon-place-start (natp (car (fn2-ribbon-place h1 h2 slots))) :rule-classes :type-prescription)
(fn2-ribbon-ub fn2-ribbon-place-lo 32 (and (unsigned-byte-p 32 h1) (unsigned-byte-p 32 h2)) (mv-nth 1 (fn2-ribbon-place h1 h2 slots)))
(fn2-ribbon-ub fn2-ribbon-place-hi 32 (and (unsigned-byte-p 32 h1) (unsigned-byte-p 32 h2)) (mv-nth 2 (fn2-ribbon-place h1 h2 slots)))
(in-theory (disable fn2-ribbon-place))
