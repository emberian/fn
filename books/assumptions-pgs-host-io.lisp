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
; words the page file FILE holds at page ADDR, and
; `(fn-pgs-fill-realize file addr)', the host's fill
; (host/native/extent.lisp `fn-pgs-fill-realize': pread of the 16 KiB page,
; short counts looped, EINTR retried, end of file and
; every other error a named condition, never a silent zero fill; the
; little-endian check at load, A-PGS-LE), answers exactly those words.
; Durability of what was written is A-DURABILITY's (a completed fdatasync);
; the page store's crash model is books/pagestore.lisp `pgs-crash'
; (any subset of the commit's writes), which the power-loss rig checks
; against dm-log-writes replays.
;
; Theorems that should take it (a page read by the host is the page the
; model's `pgs-lookup' answers): the composition of pgs-x-table-verdict-is-model
; and pgs-x-dir-verdict-is-model with the fill, not yet stated.
;
; The in-place form (lane page-word-boundary, 2026-10-01; design
; planning/design-store-representation-2026-10-01.md stage 2).  A fill that
; crosses the boundary as a LIST of 2048 words costs about 2,048 conses, a
; 16-octet bignum for every word at or above 2^62, and a put loop into the
; stobj, per 16 KiB page (build/coordinator/scholar-representation-2026-10-01.md
; section 1.3: three copies, 50 to 60 KiB of garbage a page).
; The encapsulate GAINED the u64 constraint `fn-pgs-page-words-u64'.
; It is a strict strengthening: the old shape and realizer-equality
; constraints also admitted a constant list of 2048 negative words.
; The existing host realizer `fn-pgs-fill-realize' in host/native/extent.lisp
; reads 16384 (unsigned-byte 8) octets with `fnn-extent-pread' and assembles
; each word from eight octets, little-endian, so its words are u64 by
; construction.  It does not yet pread into a u64 array.  This host-code
; observation is the reason for the added assumption, not an ACL2 proof
; of that implementation.  The constraint lets the put preserve the
; stobj's type.
;
; `fn-pgs-fill-frame' extends this strengthened A-PGS-HOST-IO boundary:
; its whole-state equation is the put of `fn-pgs-page-words' at BASE in
; SEL's array.  Its local witness constructs that extension; it does not
; prove a raw host replacement correct.  The intended in-place realizer
; preads into the stobj's (unsigned-byte 64) array, avoiding boxed words
; and conses; the list form remains for proofs and tests taking word data.

(defun fn-pgs-u64-listp (ws)
  (declare (xargs :guard t))
  (if (atom ws) (null ws) (and (unsigned-byte-p 64 (car ws)) (fn-pgs-u64-listp (cdr ws)))))

(defthm fn-pgs-u64-listp-true-listp
  (implies (fn-pgs-u64-listp ws) (true-listp ws))
  :rule-classes :forward-chaining)

(encapsulate
  (((fn-pgs-page-words * *) => *)
   ((fn-pgs-fill-realize * *) => *))

  (local (defun fn-pgs-page-words (file addr)
           (declare (ignore file addr))
           (make-list 2048 :initial-element 0)))

  (local (defun fn-pgs-fill-realize (file addr)
           (fn-pgs-page-words file addr)))

  (defthm fn-pgs-page-words-shape
    (and (true-listp (fn-pgs-page-words file addr))
         (equal (len (fn-pgs-page-words file addr)) 2048)))

  ; A-PGS-HOST-IO: added u64 constraint, not derived from the old shape.
  (defthm fn-pgs-page-words-u64
    (fn-pgs-u64-listp (fn-pgs-page-words file addr)))

  (defthm fn-pgs-fill-realize-is-page-words
    (equal (fn-pgs-fill-realize file addr) (fn-pgs-page-words file addr))))

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

; A-PGS-HOST-IO, the frame form.  `(fn-pgs-fill-frame file addr sel base
; pgs-mem)' is the host's in-place fill: page ADDR of FILE into words
; BASE .. BASE+2047 of the array SEL selects.  Its raw definition
; is not yet present in host/native/extent.lisp; it must pread the 16 KiB into that array's
; storage at word BASE (sb-sys:vector-sap; A-PGS-LE for the word order),
; refusing by name a short read, an unknown file, a selector or a range the
; guard excludes, never writing outside the range or answering made-up
; words.  The constraint: the state it leaves is the put of the page's
; words.  Whether those words are the page the committed table names is
; ACL2's digest check, as for the list form.
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
