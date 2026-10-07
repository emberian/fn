; fn: the named assumption about the page store's host I/O, A-PGS-HOST-IO,
; a part of books/assumptions.lisp.
;
; books/assumptions.lisp includes this book, so the assumption is still
; reached through it and listed there.  This part is its own book because
; its in-place form (`fn-pgs-fill-frame', below) is stated over the page
; store's stobj `pgs-mem' (books/pagestore-words.lisp), which
; books/assumptions.lisp did not include.  The closure it adds is that one
; book: pagestore-words' own closure (blake3-stobj and below) was already
; assumptions', and there is no cycle -- nothing under pagestore-words
; includes assumptions (lane page-word-boundary, 2026-10-01).
(in-package "ACL2")
(include-book "pagestore-words")
(local (include-book "arithmetic/top" :dir :system))

; A-PGS-HOST-IO (lane arena-store, 2026-09-27; the page store,
; books/pagestore*.lisp; the host I/O half of what the prototype called
; A-PGS-OBSERVE).
;
; "The page file holds, at page ADDR, the 2048 little-endian u64 words the
; host last durably wrote there; and the host's fill answers them."
;
; What is PROVED at this boundary, and so not assumed: the word digest the
; host calls is BLAKE3 of the words' little-endian octets, copied into the
; page store's octet buffer fn-octets-pg and hashed in place
; (pgs-x-words-digest-is-blake3, books/pagestore-words-blake3.lisp; `fn-blake3'
; is the value of `fn-digest''s attachment, `fn-blake3-stobj'; SHA-256 until
; 2026-09-28); a table page's and the directory
; run's words are the encodings of the model's table pages and directory,
; and decoding them gives those back (pgs-x-table-page-words,
; pgs-x-dir-run-words, pgs-decode-encode-table); the open's verdicts over the
; decoded words are the model's (pgs-x-dir-verdict-is-model,
; pgs-x-table-verdict-is-model); the commit the host runs refines the model's
; (pgs-x-commit-refines) -- all in books/pagestore-exec.lisp.
;
; What is ASSUMED: `(fn-pgs-page-words file addr)' is the list of 2048 u64
; words the page file FILE holds at page ADDR (the logical model only: no
; executable path builds it), and `(fn-pgs-fill-frame file addr sel base
; pgs-mem)', the host's in-place fill (host/native/extent.lisp: one pread of
; the 16 KiB page into the worker's stationary page buffer `fn-pgb', short
; counts looped, EINTR retried, end of file and every other error a named
; condition, never a silent zero fill), leaves the state the put of those
; words at BASE in SEL's array.  The word order is no longer assumed of the
; host's code: `fn-pgb-frame-put', below, is the ACL2 function the host runs
; over the buffer, and `fn-pgb-frame-put-is-frame-put-of-words' proves it
; the put of the buffer's little-endian words.  What stays assumed is that
; the 16384 octets the pread leaves in the buffer are page ADDR's octets.
; Durability of what was written is A-DURABILITY's (a completed fdatasync);
; the page store's crash model is books/pagestore.lisp `pgs-crash'
; (any subset of the commit's writes), which the power-loss rig checks
; against dm-log-writes replays.
;
; Theorems that should take it (a page read by the host is the page the
; model's `pgs-lookup' answers): the composition of pgs-x-table-verdict-is-model
; and pgs-x-dir-verdict-is-model with the fill, not yet stated.
;
; History.  The assumption once also constrained a list realizer
; `fn-pgs-fill-realize' (the 2048 words crossing the boundary as a list: about
; 2,048 conses, a 16-octet bignum for every word at or above 2^62, and a put
; loop, per 16 KiB page; build/coordinator/scholar-representation-2026-10-01.md
; section 1.3).  Lane s-frame-fill (2026-10-06) removed it: the encapsulate
; lost `fn-pgs-fill-realize' and its equation to `fn-pgs-page-words', and every
; theorem that spoke of the realizer speaks of `fn-pgs-page-words', the term it
; was constrained equal to.  Nothing is added: the frame constraint
; `fn-pgs-fill-frame-is-frame-put' is the one that stood, and the
; consumer-facing facts (word-wise, outside the frame, type and lengths) are
; theorems derived from it below.  The u64 constraint
; `fn-pgs-page-words-u64' was added by the earlier lane (page-word-boundary)
; and stays: it lets the put preserve the stobj's type.

(defun fn-pgs-u64-listp (ws)
  (declare (xargs :guard t))
  (if (atom ws) (null ws) (and (unsigned-byte-p 64 (car ws)) (fn-pgs-u64-listp (cdr ws)))))

(defthm fn-pgs-u64-listp-true-listp
  (implies (fn-pgs-u64-listp ws) (true-listp ws))
  :rule-classes :forward-chaining)

(encapsulate
  (((fn-pgs-page-words * *) => *))

  (local (defun fn-pgs-page-words (file addr)
           (declare (ignore file addr))
           (make-list 2048 :initial-element 0)))

  (defthm fn-pgs-page-words-shape
    (and (true-listp (fn-pgs-page-words file addr))
         (equal (len (fn-pgs-page-words file addr)) 2048)))

  ; A-PGS-HOST-IO: added u64 constraint, not derived from the old shape.
  (defthm fn-pgs-page-words-u64
    (fn-pgs-u64-listp (fn-pgs-page-words file addr))))

; -----------------------------------------------------------------------------
; The frame: the put loop in the logic, over the three word arrays of
; pgs-mem.  SEL 0 is the image (pgs-w), 1 the metadata (pgs-m), 2 the
; table pages (pgs-t): the page store's own selectors (books/pagestore-words.lisp
; header), with the image added.  It is the put `fn-hrs-put'
; (books/history-records.lisp) does for the image and `pgs-x-fill'
; (books/pagestore-exec.lisp) does for the others, stated once here so the
; assumption can name it; those two are proved to be it where they live.
; GEN: def-loop (the generator had not landed when this was written).

(defun fn-pgs-frame-sel-p (sel)
  (declare (xargs :guard t))
  (or (equal sel 0) (equal sel 1) (equal sel 2)))

(defun fn-pgs-frame-len (sel pgs-mem)
  (declare (xargs :stobjs pgs-mem :guard (fn-pgs-frame-sel-p sel)))
  (cond ((equal sel 0) (pgs-w-length pgs-mem))
        ((equal sel 1) (pgs-m-length pgs-mem))
        (t (pgs-t-length pgs-mem))))

(defun fn-pgs-frame-put (sel base ws pgs-mem)
  ; words BASE .. BASE+|WS|-1 of SEL's array := WS; nothing else changes
  (declare (xargs :stobjs pgs-mem
                  :guard (and (fn-pgs-frame-sel-p sel) (natp base) (fn-pgs-u64-listp ws)
                              (<= (+ base (len ws)) (fn-pgs-frame-len sel pgs-mem)))))
  (if (atom ws)
      pgs-mem
    (let ((pgs-mem (cond ((equal sel 0) (update-pgs-wi base (car ws) pgs-mem))
                         ((equal sel 1) (update-pgs-mi base (car ws) pgs-mem))
                         (t (update-pgs-ti base (car ws) pgs-mem)))))
      (fn-pgs-frame-put sel (+ 1 base) (cdr ws) pgs-mem))))

(defthm fn-pgs-frame-put-lengths
  (implies (and (natp base) (<= (+ base (len ws)) (fn-pgs-frame-len sel pgs-mem)))
           (and (equal (pgs-w-length (fn-pgs-frame-put sel base ws pgs-mem)) (pgs-w-length pgs-mem))
                (equal (pgs-m-length (fn-pgs-frame-put sel base ws pgs-mem)) (pgs-m-length pgs-mem))
                (equal (pgs-t-length (fn-pgs-frame-put sel base ws pgs-mem)) (pgs-t-length pgs-mem))
                (equal (pgs-d-length (fn-pgs-frame-put sel base ws pgs-mem)) (pgs-d-length pgs-mem))
                (equal (pgs-v-length (fn-pgs-frame-put sel base ws pgs-mem)) (pgs-v-length pgs-mem))
                (equal (pgs-tv-length (fn-pgs-frame-put sel base ws pgs-mem)) (pgs-tv-length pgs-mem))))
  :hints (("Goal" :induct (fn-pgs-frame-put sel base ws pgs-mem))))

(defthm fn-pgs-frame-put-memp
  (implies (and (pgs-memp pgs-mem) (natp base) (fn-pgs-u64-listp ws)
                (<= (+ base (len ws)) (fn-pgs-frame-len sel pgs-mem)))
           (pgs-memp (fn-pgs-frame-put sel base ws pgs-mem)))
  :hints (("Goal" :induct (fn-pgs-frame-put sel base ws pgs-mem))))

(defthm fn-pgs-frame-put-other-fields
  ; the flags are never touched; the arrays SEL does not select are not
  (and (equal (nth *pgs-di* (fn-pgs-frame-put sel base ws pgs-mem)) (nth *pgs-di* pgs-mem))
       (equal (nth *pgs-vi* (fn-pgs-frame-put sel base ws pgs-mem)) (nth *pgs-vi* pgs-mem))
       (equal (nth *pgs-tvi* (fn-pgs-frame-put sel base ws pgs-mem)) (nth *pgs-tvi* pgs-mem))
       (implies (not (equal sel 0))
                (equal (nth *pgs-wi* (fn-pgs-frame-put sel base ws pgs-mem)) (nth *pgs-wi* pgs-mem)))
       (implies (not (equal sel 1))
                (equal (nth *pgs-mi* (fn-pgs-frame-put sel base ws pgs-mem)) (nth *pgs-mi* pgs-mem)))
       (implies (or (equal sel 0) (equal sel 1))
                (equal (nth *pgs-ti* (fn-pgs-frame-put sel base ws pgs-mem)) (nth *pgs-ti* pgs-mem))))
  :hints (("Goal" :induct (fn-pgs-frame-put sel base ws pgs-mem)
           :in-theory (enable update-pgs-wi update-pgs-mi update-pgs-ti))))

(in-theory (disable fn-pgs-frame-len))

; Word J of the array SEL selects, absolute (the frame's word I is word BASE+I).
(defun fn-pgs-frame-word (sel j pgs-mem)
  (declare (xargs :stobjs pgs-mem
                  :guard (and (fn-pgs-frame-sel-p sel) (natp j)
                              (< j (fn-pgs-frame-len sel pgs-mem)))
                  :guard-hints (("Goal" :in-theory (enable fn-pgs-frame-len)))))
  (cond ((equal sel 0) (pgs-wi j pgs-mem))
        ((equal sel 1) (pgs-mi j pgs-mem))
        (t (pgs-ti j pgs-mem))))

; What the put does to every word of every array: word J of SEL2 is the
; put's word J-BASE when it is SEL's and in the range, and was as it was
; otherwise.
(defthm fn-pgs-frame-word-of-frame-put
  (implies (and (fn-pgs-frame-sel-p sel) (fn-pgs-frame-sel-p sel2) (natp base) (natp j)
                (<= (+ base (len ws)) (fn-pgs-frame-len sel pgs-mem)))
           (equal (fn-pgs-frame-word sel2 j (fn-pgs-frame-put sel base ws pgs-mem))
                  (if (and (equal sel2 sel) (<= base j) (< j (+ base (len ws))))
                      (nth (- j base) ws)
                    (fn-pgs-frame-word sel2 j pgs-mem))))
  :hints (("Goal" :induct (fn-pgs-frame-put sel base ws pgs-mem)
           :in-theory (enable fn-pgs-frame-word fn-pgs-frame-len update-pgs-wi update-pgs-mi
                              update-pgs-ti pgs-wi pgs-mi pgs-ti
                              pgs-w-length pgs-m-length pgs-t-length))))

; A-PGS-HOST-IO, the frame form.  `(fn-pgs-fill-frame file addr sel base
; pgs-mem)' is the host's in-place fill: page ADDR of FILE into words
; BASE .. BASE+2047 of the array SEL selects.  Its raw definition is
; host/native/extent.lisp's fn-pgs-fill-frame (attached by stage-0-4): one
; pread of the page into the worker's stationary buffer, then `fn-pgb-frame-put'
; (below) over it; no list of the page's words exists.  It refuses by name a
; short read, an unknown file, a negative address, a selector or a range the
; guard excludes, never writing outside the range or answering made-up
; words.  The constraint: the state it leaves is the put of the page's
; words.  Whether those words are the page the committed table names is
; ACL2's digest check.
(encapsulate
  (((fn-pgs-fill-frame * * * * pgs-mem) => pgs-mem
    :formals (file addr sel base pgs-mem)
    :guard (and (fn-pgs-frame-sel-p sel) (natp base)
                (<= (+ base 2048) (fn-pgs-frame-len sel pgs-mem)))))

  (local (defun fn-pgs-fill-frame (file addr sel base pgs-mem)
           (declare (xargs :stobjs pgs-mem
                           :guard (and (fn-pgs-frame-sel-p sel) (natp base)
                                       (<= (+ base 2048) (fn-pgs-frame-len sel pgs-mem)))
                           :guard-hints (("Goal" :use ((:instance fn-pgs-page-words-shape)
                                                       (:instance fn-pgs-page-words-u64))))))
           (fn-pgs-frame-put sel base (fn-pgs-page-words file addr) pgs-mem)))

  (defthm fn-pgs-fill-frame-is-frame-put
    (equal (fn-pgs-fill-frame file addr sel base pgs-mem)
           (fn-pgs-frame-put sel base (fn-pgs-page-words file addr) pgs-mem))))

; A-PGS-HOST-IO (including fn-pgs-page-words-u64) discharges this guard.
; The fill as the logic says it (the witness, kept): what a test or an
; oracle attaches to `fn-pgs-fill-frame' once `fn-pgs-page-words' is
; attached to its page file as data (tests/acl2/history-records-disk-tests.lisp).
(defun fn-pgs-fill-frame-via-words (file addr sel base pgs-mem)
  (declare (xargs :stobjs pgs-mem
                  :guard (and (fn-pgs-frame-sel-p sel) (natp base)
                              (<= (+ base 2048) (fn-pgs-frame-len sel pgs-mem)))
                  :guard-hints (("Goal" :use ((:instance fn-pgs-page-words-shape)
                                              (:instance fn-pgs-page-words-u64))))))
  (fn-pgs-frame-put sel base (fn-pgs-page-words file addr) pgs-mem))

; What the consumers need of the fill, derived once from the constraint.
(defthm fn-pgs-fill-frame-lengths
  (implies (and (natp base) (<= (+ base 2048) (fn-pgs-frame-len sel pgs-mem)))
           (and (equal (pgs-w-length (fn-pgs-fill-frame file addr sel base pgs-mem)) (pgs-w-length pgs-mem))
                (equal (pgs-m-length (fn-pgs-fill-frame file addr sel base pgs-mem)) (pgs-m-length pgs-mem))
                (equal (pgs-t-length (fn-pgs-fill-frame file addr sel base pgs-mem)) (pgs-t-length pgs-mem))
                (equal (pgs-d-length (fn-pgs-fill-frame file addr sel base pgs-mem)) (pgs-d-length pgs-mem))
                (equal (pgs-v-length (fn-pgs-fill-frame file addr sel base pgs-mem)) (pgs-v-length pgs-mem))
                (equal (pgs-tv-length (fn-pgs-fill-frame file addr sel base pgs-mem)) (pgs-tv-length pgs-mem))))
  :hints (("Goal" :use ((:instance fn-pgs-page-words-shape)
                        (:instance fn-pgs-frame-put-lengths (ws (fn-pgs-page-words file addr)))))))

; A-PGS-HOST-IO: uses the added fn-pgs-page-words-u64 constraint
; and the assumed whole-state fill equation to preserve the stobj type.
(defthm fn-pgs-fill-frame-memp
  (implies (and (pgs-memp pgs-mem) (natp base) (<= (+ base 2048) (fn-pgs-frame-len sel pgs-mem)))
           (pgs-memp (fn-pgs-fill-frame file addr sel base pgs-mem)))
  :hints (("Goal" :use ((:instance fn-pgs-page-words-shape)
                        (:instance fn-pgs-page-words-u64)
                        (:instance fn-pgs-frame-put-memp (ws (fn-pgs-page-words file addr)))))))

; Word-wise: the fill leaves page word I at frame word I.
(defthm fn-pgs-fill-frame-word
  (implies (and (natp i) (< i 2048) (fn-pgs-frame-sel-p sel) (natp base)
                (<= (+ base 2048) (fn-pgs-frame-len sel pgs-mem)))
           (equal (fn-pgs-frame-word sel (+ base i) (fn-pgs-fill-frame file addr sel base pgs-mem))
                  (nth i (fn-pgs-page-words file addr))))
  :hints (("Goal" :use ((:instance fn-pgs-page-words-shape)
                        (:instance fn-pgs-fill-frame-is-frame-put)
                        (:instance fn-pgs-frame-word-of-frame-put
                                   (j (+ base i)) (sel2 sel) (ws (fn-pgs-page-words file addr))))
           :in-theory (disable fn-pgs-fill-frame-is-frame-put fn-pgs-frame-word-of-frame-put))))

; Nothing outside the frame moves: another array's word, or a word of SEL's
; array below BASE or from BASE+2048.
(defthm fn-pgs-fill-frame-word-outside
  (implies (and (natp j) (fn-pgs-frame-sel-p sel) (fn-pgs-frame-sel-p sel2) (natp base)
                (<= (+ base 2048) (fn-pgs-frame-len sel pgs-mem))
                (or (not (equal sel2 sel)) (< j base) (<= (+ base 2048) j)))
           (equal (fn-pgs-frame-word sel2 j (fn-pgs-fill-frame file addr sel base pgs-mem))
                  (fn-pgs-frame-word sel2 j pgs-mem)))
  :hints (("Goal" :use ((:instance fn-pgs-page-words-shape)
                        (:instance fn-pgs-fill-frame-is-frame-put)
                        (:instance fn-pgs-frame-word-of-frame-put
                                   (ws (fn-pgs-page-words file addr))))
           :in-theory (disable fn-pgs-fill-frame-is-frame-put fn-pgs-frame-word-of-frame-put))))

; The flags and the arrays SEL does not select are not touched.
(defthm fn-pgs-fill-frame-other-fields
  (implies (and (natp base) (<= (+ base 2048) (fn-pgs-frame-len sel pgs-mem)))
           (and (equal (nth *pgs-di* (fn-pgs-fill-frame file addr sel base pgs-mem)) (nth *pgs-di* pgs-mem))
                (equal (nth *pgs-vi* (fn-pgs-fill-frame file addr sel base pgs-mem)) (nth *pgs-vi* pgs-mem))
                (equal (nth *pgs-tvi* (fn-pgs-fill-frame file addr sel base pgs-mem)) (nth *pgs-tvi* pgs-mem))))
  :hints (("Goal" :use ((:instance fn-pgs-fill-frame-is-frame-put)
                        (:instance fn-pgs-frame-put-other-fields (ws (fn-pgs-page-words file addr))))
           :in-theory (disable fn-pgs-fill-frame-is-frame-put fn-pgs-frame-put-other-fields))))

; -----------------------------------------------------------------------------
; The host's page buffer and the put over it.
;
; The fill the host runs: one pread of the 16 KiB page into a stationary
; octet buffer (`fn-pgb', one per worker thread, allocated once: a def-buffer
; instance, books/def-buffer.lisp), then `fn-pgb-frame-put', an ACL2 function
; storing the buffer's 2048 little-endian words into SEL's array at BASE, a
; word at a time, straight from the buffer's array into the stobj's.  No list
; of the page's words, or of its octets, exists.  The word order is therefore
; a theorem (`fn-pgb-frame-put-is-frame-put-of-words'), not a promise of the
; host's code.
; GEN: def-loop (a stobj-threaded store loop: the `:fold' shape is not in the
; generator yet; `fn-pgs-frame-put' above is the same loop over a list).

(def-buffer fn-pgb)

(defun fn-pgb-words-from (i m oct)
  ; the M little-endian words of OCT's octets from I, the page's words as the
  ; octets say them
  (declare (xargs :guard (and (natp i) (natp m)) :measure (nfix m)))
  (if (zp m)
      nil
    (cons (fn-oct-word-at i 8 oct) (fn-pgb-words-from (+ i 8) (1- m) oct))))

(local
 (defthm fn-oct-nth-octet
   (implies (fn-cbor-octet-listp xs)
            (< (nth i xs) 256))
   :hints (("Goal" :induct (nth i xs) :in-theory (enable nth fn-cbor-octetp fn-cbor-octet-listp)))))

(local
 (defthm fn-oct-car-octet
   (implies (fn-cbor-octet-listp xs) (< (car xs) 256))
   :hints (("Goal" :in-theory (enable fn-cbor-octetp fn-cbor-octet-listp)))))

(local
 (defthm fn-oct-word-at-natp
   (natp (fn-oct-word-at i k oct))
   :hints (("Goal" :induct (fn-oct-word-at i k oct) :in-theory (enable fn-oct-word-at)))))

(local
 (defthm fn-oct-word-step
   (implies (and (natp a) (< a 256) (natp w) (natp e) (< w e))
            (< (+ a (* 256 w)) (* 256 e)))))

(defthm fn-oct-word-at-bound
  (implies (and (fn-cbor-octet-listp oct) (natp k))
           (< (fn-oct-word-at i k oct) (expt 256 k)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-oct-word-at i k oct)
           :in-theory (enable fn-oct-word-at))))

(defthm fn-oct-word-at-4-u32
  (implies (fn-cbor-octet-listp oct)
           (and (natp (fn-oct-word-at i 4 oct))
                (< (fn-oct-word-at i 4 oct) 4294967296)))
  :hints (("Goal" :use ((:instance fn-oct-word-at-bound (k 4))))))

(defthm fn-oct-word-at-8-u64
  (implies (fn-cbor-octet-listp oct)
           (and (natp (fn-oct-word-at i 8 oct))
                (< (fn-oct-word-at i 8 oct) 18446744073709551616)))
  :hints (("Goal" :use ((:instance fn-oct-word-at-bound (k 8))))))

(defthm fn-pgb-words-from-u64
  (implies (fn-cbor-octet-listp oct)
           (fn-pgs-u64-listp (fn-pgb-words-from i m oct)))
  :hints (("Goal" :induct (fn-pgb-words-from i m oct))))

(defthm fn-pgb-words-from-len
  (equal (len (fn-pgb-words-from i m oct)) (nfix m)))

; Word I/8 of the buffer, as two u32 halves.  `fn-pgb-get-word' of four octets
; is a fixnum, so the sum is one machine word and never boxed.
(defun fn-pgb-word (i fn-pgb)
  (declare (xargs :stobjs fn-pgb
                  :guard (and (natp i) (<= (+ i 8) (fn-pgb-len fn-pgb)))))
  (+ (the (unsigned-byte 32) (fn-pgb-get-word i 4 fn-pgb))
     (* 4294967296 (the (unsigned-byte 32) (fn-pgb-get-word (+ i 4) 4 fn-pgb)))))

(defthm fn-oct-word-at-split
  (implies (and (natp i))
           (equal (fn-oct-word-at i 8 oct)
                  (+ (fn-oct-word-at i 4 oct) (* 4294967296 (fn-oct-word-at (+ i 4) 4 oct)))))
  :hints (("Goal" :in-theory (disable fn-oct-word-at)
           :do-not-induct t
           :expand ((fn-oct-word-at i 8 oct) (fn-oct-word-at (+ 1 i) 7 oct)
                    (fn-oct-word-at (+ 2 i) 6 oct) (fn-oct-word-at (+ 3 i) 5 oct)
                    (fn-oct-word-at (+ 4 i) 4 oct) (fn-oct-word-at (+ 5 i) 3 oct)
                    (fn-oct-word-at (+ 6 i) 2 oct) (fn-oct-word-at (+ 7 i) 1 oct)
                    (fn-oct-word-at i 4 oct) (fn-oct-word-at (+ 1 i) 3 oct)
                    (fn-oct-word-at (+ 2 i) 2 oct) (fn-oct-word-at (+ 3 i) 1 oct)
                    (fn-oct-word-at (+ 8 i) 0 oct) (fn-oct-word-at (+ 4 i) 0 oct)
                    (fn-oct-word-at (+ 4 i) 4 oct)))))

(defthm fn-pgb-word-is-word-at
  (implies (natp i)
           (equal (fn-pgb-word i fn-pgb) (fn-oct-word-at i 8 fn-pgb)))
  :hints (("Goal" :in-theory (enable fn-pgb-word))))

(defthm fn-pgb-word-u64
  (implies (and (fn-pgb-p fn-pgb) (natp i))
           (unsigned-byte-p 64 (fn-pgb-word i fn-pgb)))
  :hints (("Goal" :in-theory (enable fn-pgb-p)
           :use ((:instance fn-oct-word-at-8-u64 (oct fn-pgb))
                 (:instance fn-pgb-word-is-word-at)))))

(in-theory (disable fn-pgb-word))

(defun fn-pgb-put-loop (sel base i m fn-pgb pgs-mem)
  ; words BASE .. BASE+M-1 of SEL's array := the M words of the buffer from octet I
  (declare (xargs :stobjs (fn-pgb pgs-mem)
                  :guard (and (fn-pgs-frame-sel-p sel) (natp base) (natp i) (natp m)
                              (<= (+ i (* 8 m)) (fn-pgb-len fn-pgb))
                              (<= (+ base m) (fn-pgs-frame-len sel pgs-mem)))
                  :measure (nfix m)
                  :guard-hints (("Goal" :in-theory (enable fn-pgs-frame-len)
                                 :use ((:instance fn-oct-word-at-8-u64 (oct fn-pgb))
                                              (:instance fn-oct-word-at-split (oct fn-pgb)))))))
  (if (zp m)
      pgs-mem
    (let* ((w (fn-pgb-word i fn-pgb))
           (pgs-mem (cond ((equal sel 0) (update-pgs-wi base w pgs-mem))
                          ((equal sel 1) (update-pgs-mi base w pgs-mem))
                          (t (update-pgs-ti base w pgs-mem)))))
      (fn-pgb-put-loop sel (+ 1 base) (+ 8 i) (1- m) fn-pgb pgs-mem))))

(defun fn-pgb-frame-put (sel base fn-pgb pgs-mem)
  ; the buffer's 2048 words at BASE of SEL's array
  (declare (xargs :stobjs (fn-pgb pgs-mem)
                  :guard (and (fn-pgs-frame-sel-p sel) (natp base)
                              (equal (fn-pgb-len fn-pgb) 16384)
                              (<= (+ base 2048) (fn-pgs-frame-len sel pgs-mem)))))
  (fn-pgb-put-loop sel base 0 2048 fn-pgb pgs-mem))

(local
 (defthm fn-pgs-frame-len-of-update
   (and (implies (and (natp i) (< i (pgs-w-length pgs-mem)))
                 (equal (fn-pgs-frame-len sel2 (update-pgs-wi i v pgs-mem)) (fn-pgs-frame-len sel2 pgs-mem)))
        (implies (and (natp i) (< i (pgs-m-length pgs-mem)))
                 (equal (fn-pgs-frame-len sel2 (update-pgs-mi i v pgs-mem)) (fn-pgs-frame-len sel2 pgs-mem)))
        (implies (and (natp i) (< i (pgs-t-length pgs-mem)))
                 (equal (fn-pgs-frame-len sel2 (update-pgs-ti i v pgs-mem)) (fn-pgs-frame-len sel2 pgs-mem))))
   :hints (("Goal" :in-theory (enable fn-pgs-frame-len)))))

(defthm fn-pgb-put-loop-is-frame-put
  (implies (and (fn-pgs-frame-sel-p sel) (natp base) (natp i) (natp m)
                (<= (+ i (* 8 m)) (len fn-pgb))
                (<= (+ base m) (fn-pgs-frame-len sel pgs-mem)))
           (equal (fn-pgb-put-loop sel base i m fn-pgb pgs-mem)
                  (fn-pgs-frame-put sel base (fn-pgb-words-from i m fn-pgb) pgs-mem)))
  :hints (("Goal" :induct (fn-pgb-put-loop sel base i m fn-pgb pgs-mem)
           :in-theory (enable fn-pgb-put-loop fn-pgs-frame-put fn-pgb-words-from fn-pgs-frame-len))))

; KEYSTONE: what the host runs over the buffer is the frame put of the
; buffer's little-endian words.
(defthm fn-pgb-frame-put-is-frame-put-of-words
  (implies (and (fn-pgs-frame-sel-p sel) (natp base)
                (equal (len fn-pgb) 16384)
                (<= (+ base 2048) (fn-pgs-frame-len sel pgs-mem)))
           (equal (fn-pgb-frame-put sel base fn-pgb pgs-mem)
                  (fn-pgs-frame-put sel base (fn-pgb-words-from 0 2048 fn-pgb) pgs-mem)))
  :hints (("Goal" :in-theory (enable fn-pgb-frame-put))))
