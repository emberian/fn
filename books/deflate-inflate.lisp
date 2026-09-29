; fn: the DEFLATE inflater for NNTP COMPRESS (RFC 8054, RFC 1951; lane
; compress, PRF-909 and PRF-910).  Prefix `fn-zin-'.
;
; WHAT IT IS.  RFC 8054 section 2.2.2 puts a raw DEFLATE stream (RFC 1951:
; no zlib header, no trailer) under every octet a client sends after the
; 206.  That stream is untrusted input on the served path, so it is decoded
; here, in ACL2: total, guard-verified, bounded and resumable per call, with
; the expansion of a hostile stream refused by name.  The server's own
; OUTBOUND stream is produced by zlib in C (host/native/fn-deflate.c): a
; fault there can only garble what the server sends, never what it reads.
;
; THE MACHINE.  The decoder follows zlib's reference inflater `puff'
; (zlib/contrib/puff/puff.c, Mark Adler): canonical Huffman codes decoded a
; bit at a time from per-length counts and a symbol table; stored, fixed
; and dynamic blocks.  Its state is split in four:
;
;   fn-zin-st   twenty naturals (a stobj; `fn-zin-reset'), the scalar state:
;               the bit buffer, the mode, the block's counters, the Huffman
;               decode in progress, the totals;
;   fn-zin-win  the 32 KiB history ring (RFC 1951 section 2: a distance
;               reaches at most 32,768 octets back);
;   fn-zin-tab  the code lengths and the three Huffman tables, two octets
;               per entry (`*fn-zin-tab-entries*' entries);
;   fn-zin-out  the plaintext produced by this call, appended to.
;
; The three buffers are abstract stobjs congruent to `fn-octets'
; (books/octets-stobj.lisp: one byte per octet at run time, the octet list
; logically); the host holds one private set per connection and passes it
; (a private `fn-octets$c' object each, as it passes render buffers).
; `fn-zin-buffers-ready' fills the window and the table to their fixed
; lengths once; every later call keeps them (`fn-zin-feed-keeps-buffers').
;
; THE HOST ENTRY.  `fn-zin-feed B ZS START END LIM fn-octets win tab out'
; decodes the input octets in `fn-octets' cells [START, END) and answers
; (mv STATUS B2 IP ZS win tab out): IP is the first input octet not
; consumed (an octet's unread bits are kept in ZS), B2 the budget left.
; STATUS is
;
;   :more       every input octet was consumed; send more;
;   :full       the output reached LIM octets; hand them on and call again;
;   :yield      the budget B (actions) ran out; call again (D27: a quantum
;               yields, it never truncates);
;   (:refused R) the stream is refused by name (`fn-zin-refusal-text'); the
;               connection closes (RFC 8054 section 2.2.2: "the receiving
;               end immediately closes the connection").
;
; One action reads at most one input octet and appends at most one output
; octet; a table construction is one action (bounded by the 320 code
; lengths).  So a call does work bounded by B, reads at most END - START
; octets, and never grows the output past LIM (`fn-zin-feed-out-bound').
;
; THE BOMB.  ZS counts the octets read (TOTAL-IN) and produced (TOTAL-OUT).
; A stream that would produce more than `*fn-zin-ratio*' times what it has
; read plus `*fn-zin-slack*' is refused (:refused :bomb) before the octet
; that would pass the bound is produced.  KEYSTONE `fn-zin-feed-bomb-bound':
; after any call that does not refuse, TOTAL-OUT <= R * TOTAL-IN + S.  The
; per-call bound (LIM) bounds the memory a step can take; the ratio bounds
; the plaintext work a client can make the server do per octet it sends.
; R = 256 is a quarter of DEFLATE's own ceiling (258 octets for the shortest
; match code, about 1032:1): ordinary NNTP commands and articles compress
; 2 to 10 times; a run of one octet is what passes 256.
;
; RESUMPTION.  The network cuts the stream anywhere; the host feeds whatever
; arrived.  KEYSTONES `fn-zin-feed-split-input' and `fn-zin-feed-split-budget':
; a call that stops at the end of its input (:more) or of its budget
; (:yield), resumed on the rest, is the call that saw everything at once.
;
; REACHABILITY.  `fn-zin-stored-stream' is an encoder (stored blocks, as a
; sync flush writes them); KEYSTONE `fn-zin-inflates-stored-stream': its
; output inflates to its input from the initial state, so the success arm is
; reached by every octet string.

(in-package "ACL2")
(include-book "octets-stobj")

(defabsstobj fn-zin-win
  :foundation fn-octets$c
  :recognizer (fn-zin-win-p :logic fn-octets$ap :exec fn-octets$cp)
  :creator (create-fn-zin-win :logic create-fn-octets$a :exec create-fn-octets$c)
  :exports ((fn-zin-win-len :logic fn-octets$a-len :exec fn-octets$c-len)
            (fn-zin-win-get :logic fn-octets$a-get :exec fn-octets$c-get)
            (fn-zin-win-put :logic fn-octets$a-put :exec fn-octets$c-put :protect t)
            (fn-zin-win-append-octet :logic fn-octets$a-append-octet
                                     :exec fn-octets$c-append-octet :protect t)
            (fn-zin-win-clear :logic fn-octets$a-clear :exec fn-octets$c-clear)
            (fn-zin-win-reserve :logic fn-octets$a-reserve :exec fn-octets$c-reserve
                                :protect t)
            (fn-zin-win-list :logic fn-octets$a-list :exec fn-octets$c-list)
            (fn-zin-win-from-list :logic fn-octets$a-from-list
                                  :exec fn-octets$c-from-list :protect t)
            (fn-zin-win-append-list :logic fn-octets$a-append-list
                                    :exec fn-oct-write-list :protect t)
            (fn-zin-win-append-back :logic fn-octets$a-append-back
                                    :exec fn-octets$c-append-back :protect t)
            (fn-zin-win-get-word :logic fn-octets$a-get-word :exec fn-octets$c-get-word)
            (fn-zin-win-append-word :logic fn-octets$a-append-word
                                    :exec fn-octets$c-append-word :protect t))
  :congruent-to fn-octets)

(defabsstobj fn-zin-tab
  :foundation fn-octets$c
  :recognizer (fn-zin-tab-p :logic fn-octets$ap :exec fn-octets$cp)
  :creator (create-fn-zin-tab :logic create-fn-octets$a :exec create-fn-octets$c)
  :exports ((fn-zin-tab-len :logic fn-octets$a-len :exec fn-octets$c-len)
            (fn-zin-tab-get :logic fn-octets$a-get :exec fn-octets$c-get)
            (fn-zin-tab-put :logic fn-octets$a-put :exec fn-octets$c-put :protect t)
            (fn-zin-tab-append-octet :logic fn-octets$a-append-octet
                                     :exec fn-octets$c-append-octet :protect t)
            (fn-zin-tab-clear :logic fn-octets$a-clear :exec fn-octets$c-clear)
            (fn-zin-tab-reserve :logic fn-octets$a-reserve :exec fn-octets$c-reserve
                                :protect t)
            (fn-zin-tab-list :logic fn-octets$a-list :exec fn-octets$c-list)
            (fn-zin-tab-from-list :logic fn-octets$a-from-list
                                  :exec fn-octets$c-from-list :protect t)
            (fn-zin-tab-append-list :logic fn-octets$a-append-list
                                    :exec fn-oct-write-list :protect t)
            (fn-zin-tab-append-back :logic fn-octets$a-append-back
                                    :exec fn-octets$c-append-back :protect t)
            (fn-zin-tab-get-word :logic fn-octets$a-get-word :exec fn-octets$c-get-word)
            (fn-zin-tab-append-word :logic fn-octets$a-append-word
                                    :exec fn-octets$c-append-word :protect t))
  :congruent-to fn-octets)

(defabsstobj fn-zin-out
  :foundation fn-octets$c
  :recognizer (fn-zin-out-p :logic fn-octets$ap :exec fn-octets$cp)
  :creator (create-fn-zin-out :logic create-fn-octets$a :exec create-fn-octets$c)
  :exports ((fn-zin-out-len :logic fn-octets$a-len :exec fn-octets$c-len)
            (fn-zin-out-get :logic fn-octets$a-get :exec fn-octets$c-get)
            (fn-zin-out-put :logic fn-octets$a-put :exec fn-octets$c-put :protect t)
            (fn-zin-out-append-octet :logic fn-octets$a-append-octet
                                     :exec fn-octets$c-append-octet :protect t)
            (fn-zin-out-clear :logic fn-octets$a-clear :exec fn-octets$c-clear)
            (fn-zin-out-reserve :logic fn-octets$a-reserve :exec fn-octets$c-reserve
                                :protect t)
            (fn-zin-out-list :logic fn-octets$a-list :exec fn-octets$c-list)
            (fn-zin-out-from-list :logic fn-octets$a-from-list
                                  :exec fn-octets$c-from-list :protect t)
            (fn-zin-out-append-list :logic fn-octets$a-append-list
                                    :exec fn-oct-write-list :protect t)
            (fn-zin-out-append-back :logic fn-octets$a-append-back
                                    :exec fn-octets$c-append-back :protect t)
            (fn-zin-out-get-word :logic fn-octets$a-get-word :exec fn-octets$c-get-word)
            (fn-zin-out-append-word :logic fn-octets$a-append-word
                                    :exec fn-octets$c-append-word :protect t))
  :congruent-to fn-octets)

(local
 (defthm fn-zin-stobj-recognizers
   (and (equal (fn-octets-p x) (fn-cbor-octet-listp x))
        (equal (fn-zin-win-p x) (fn-cbor-octet-listp x))
        (equal (fn-zin-tab-p x) (fn-cbor-octet-listp x))
        (equal (fn-zin-out-p x) (fn-cbor-octet-listp x)))
   :hints (("Goal" :in-theory (enable fn-octets-p)))))

(local
 (defthm fn-zin-nth-of-octet-list
   (implies (and (fn-cbor-octet-listp x) (natp i) (< i (len x)))
            (and (fn-cbor-octetp (nth i x))
                 (natp (nth i x))
                 (< (nth i x) 256)))
   :rule-classes
   ((:rewrite)
    (:type-prescription
     :corollary (implies (and (fn-cbor-octet-listp x) (natp i) (< i (len x)))
                         (natp (nth i x))))
    (:linear
     :corollary (implies (and (fn-cbor-octet-listp x) (natp i) (< i (len x)))
                         (and (<= 0 (nth i x)) (< (nth i x) 256)))))))

(local
 (defthm fn-zin-len-of-snoc
   (equal (len (fn-oct-snoc x o)) (1+ (len x)))))

(local
 (defthm fn-zin-len-of-update
   (implies (and (natp i) (< i (len x)))
            (equal (len (fn-oct-update i o x)) (len x)))))

(local
 (defthm fn-zin-octet-listp-of-update
   (implies (and (fn-cbor-octet-listp x) (fn-cbor-octetp o) (natp i) (< i (len x)))
            (fn-cbor-octet-listp (fn-oct-update i o x)))))

(local
 (defthm fn-zin-octet-listp-of-snoc
   (implies (and (fn-cbor-octet-listp x) (fn-cbor-octetp o))
            (fn-cbor-octet-listp (fn-oct-snoc x o)))))

; -----------------------------------------------------------------------------
; Constants.  The window, the table layout, the bomb bound.

(defconst *fn-zin-window* 32768)
; The window buffer: the 32 KiB ring, then a preset dictionary's last
; 32 KiB at most (RFC 1950 section 2.2's FDICT, as RFC 9842 names a
; dictionary by digest): a distance past the octets produced reaches into
; it.
(defconst *fn-zin-win-octets* 65536)
(defconst *fn-zin-ratio* 256)
(defconst *fn-zin-slack* 65536)

; The table, in two-octet entries:
;   [0, 320)     code lengths (literal/length then distance; the 19
;                code-length code lengths reuse [0, 19))
;   [320, 336)   literal/length counts per bit length 0..15
;   [336, 624)   literal/length symbols (288)
;   [624, 640)   distance counts
;   [640, 672)   distance symbols (32: the fixed code has 30 and 31, which
;                no stream may use, as zlib's does)
;   [672, 688)   code-length-code counts
;   [688, 707)   code-length-code symbols (19)
;   [707, 723)   scratch: the offsets while a table is built, then the
;                next canonical code of each length
;   [723, 1235)  literal/length lookup: 9 bits (LSB first) -> (L * 512 +
;                symbol) for a code of length L <= 9, 0 for none
;   [1235, 1747) distance lookup, the same
(defconst *fn-zin-tab-entries* 1747)
(defconst *fn-zin-tab-octets* 3494)

(defun fn-zin-buffer-sizes ()
  ; What the host reserves per connection: the window, the table (fixed
  ; lengths, established by `fn-zin-buffers-ready') and the output bound
  ; is LIM, the caller's.
  (declare (xargs :guard t))
  (list :window *fn-zin-win-octets* :table *fn-zin-tab-octets*))

; The three Huffman tables: (COUNT-BASE SYMBOL-BASE SYMBOLS).
(defun fn-zin-cnt-base (tb)
  (declare (xargs :guard t))
  (case tb (0 320) (1 624) (otherwise 672)))
(defun fn-zin-sym-base (tb)
  (declare (xargs :guard t))
  (case tb (0 336) (1 640) (otherwise 688)))
(defun fn-zin-sym-max (tb)
  (declare (xargs :guard t))
  (case tb (0 288) (1 32) (otherwise 19)))

(defthm fn-zin-table-bases
  (and (natp (fn-zin-cnt-base tb)) (<= (+ 16 (fn-zin-cnt-base tb)) 707)
       (natp (fn-zin-sym-base tb)) (natp (fn-zin-sym-max tb))
       (<= (+ (fn-zin-sym-base tb) (fn-zin-sym-max tb)) 707))
  :rule-classes ((:linear :corollary
                  (and (<= 0 (fn-zin-cnt-base tb)) (<= (+ 16 (fn-zin-cnt-base tb)) 707)
                       (<= 0 (fn-zin-sym-base tb)) (<= 0 (fn-zin-sym-max tb))
                       (<= (+ (fn-zin-sym-base tb) (fn-zin-sym-max tb)) 707)))
                 (:type-prescription :corollary (natp (fn-zin-cnt-base tb)))
                 (:type-prescription :corollary (natp (fn-zin-sym-base tb)))
                 (:type-prescription :corollary (natp (fn-zin-sym-max tb)))))

(in-theory (disable fn-zin-cnt-base fn-zin-sym-base fn-zin-sym-max))

; RFC 1951 section 3.2.5: the length and distance bases and extra bits.
(defconst *fn-zin-lbase*
  '(3 4 5 6 7 8 9 10 11 13 15 17 19 23 27 31 35 43 51 59 67 83 99 115 131 163
    195 227 258))
(defconst *fn-zin-lext*
  '(0 0 0 0 0 0 0 0 1 1 1 1 2 2 2 2 3 3 3 3 4 4 4 4 5 5 5 5 0))
(defconst *fn-zin-dbase*
  '(1 2 3 4 5 7 9 13 17 25 33 49 65 97 129 193 257 385 513 769 1025 1537 2049
    3073 4097 6145 8193 12289 16385 24577))
(defconst *fn-zin-dext*
  '(0 0 0 0 1 1 2 2 3 3 4 4 5 5 6 6 7 7 8 8 9 9 10 10 11 11 12 12 13 13))
; Section 3.2.7: the order of the code-length code lengths.
(defconst *fn-zin-clorder*
  '(16 17 18 0 8 7 9 6 10 5 11 4 12 3 13 2 14 1 15))

(defun fn-zin-at (i xs)
  ; A small constant table's entry, 0 past its end.
  (declare (xargs :guard (nat-listp xs)))
  (nfix (nth (nfix i) xs)))

(defthm fn-zin-at-natp
  (natp (fn-zin-at i xs))
  :rule-classes :type-prescription)

(local
 (defun fn-zin-maxl (xs)
   (if (consp xs) (max (nfix (car xs)) (fn-zin-maxl (cdr xs))) 0)))

(local
 (defthm fn-zin-nth-le-maxl
   (<= (nfix (nth i xs)) (fn-zin-maxl xs))
   :hints (("Goal" :in-theory (enable nth)))
   :rule-classes nil))

(local
 (defthm fn-zin-at-bounds
   (and (<= (fn-zin-at i *fn-zin-lext*) 5)
        (<= (fn-zin-at i *fn-zin-dext*) 13)
        (<= (fn-zin-at i *fn-zin-clorder*) 18)
        (<= (fn-zin-at i *fn-zin-dbase*) 24577)
        (<= (fn-zin-at i *fn-zin-lbase*) 258))
   :rule-classes :linear
   :hints (("Goal" :use ((:instance fn-zin-nth-le-maxl (i (nfix i)) (xs *fn-zin-lext*))
                         (:instance fn-zin-nth-le-maxl (i (nfix i)) (xs *fn-zin-dext*))
                         (:instance fn-zin-nth-le-maxl (i (nfix i)) (xs *fn-zin-clorder*))
                         (:instance fn-zin-nth-le-maxl (i (nfix i)) (xs *fn-zin-dbase*))
                         (:instance fn-zin-nth-le-maxl (i (nfix i)) (xs *fn-zin-lbase*)))))))

(in-theory (disable fn-zin-at))

; The same five tables as case dispatches (a jump, where `nth' walks the
; list), each equal to its `fn-zin-at' form; the machine reads these.
(local
 (defthm fn-zin-nth-past-end
   (implies (and (natp i) (<= (len xs) i))
            (equal (nth i xs) nil))
   :hints (("Goal" :in-theory (enable nth)))))

(defun fn-zin-max (xs)
  (declare (xargs :mode :program))
  (if (consp xs) (max (car xs) (fn-zin-max (cdr xs))) 0))

(defun fn-zin-case-arms (i xs)
  (declare (xargs :mode :program))
  (if (consp xs)
      (cons (list i (car xs)) (fn-zin-case-arms (1+ i) (cdr xs)))
    nil))

(defmacro fn-zin-deftable (name const values)
  (declare (ignore const))
  `(progn
     (defun ,name (i)
       (declare (xargs :guard t))
       (case i ,@(fn-zin-case-arms 0 values) (otherwise 0)))
     (defthm ,(intern-in-package-of-symbol
               (concatenate 'string (symbol-name name) "-BOUNDS") name)
       (and (natp (,name i)) (<= (,name i) ,(fn-zin-max values)))
       :rule-classes ((:type-prescription :corollary (natp (,name i)))
                      (:linear :corollary (<= (,name i) ,(fn-zin-max values)))))
     (in-theory (disable ,name))))

(fn-zin-deftable fn-zin-lext-of *fn-zin-lext*
  (0 0 0 0 0 0 0 0 1 1 1 1 2 2 2 2 3 3 3 3 4 4 4 4 5 5 5 5 0))
(fn-zin-deftable fn-zin-lbase-of *fn-zin-lbase*
  (3 4 5 6 7 8 9 10 11 13 15 17 19 23 27 31 35 43 51 59 67 83 99 115 131 163 195 227 258))
(fn-zin-deftable fn-zin-dext-of *fn-zin-dext*
  (0 0 0 0 1 1 2 2 3 3 4 4 5 5 6 6 7 7 8 8 9 9 10 10 11 11 12 12 13 13))
(fn-zin-deftable fn-zin-dbase-of *fn-zin-dbase*
  (1 2 3 4 5 7 9 13 17 25 33 49 65 97 129 193 257 385 513 769 1025 1537 2049 3073 4097 6145 8193 12289 16385 24577))
(fn-zin-deftable fn-zin-clorder-of *fn-zin-clorder*
  (16 17 18 0 8 7 9 6 10 5 11 4 12 3 13 2 14 1 15))

; -----------------------------------------------------------------------------
; The scalar state ZS: a list of naturals, each read through `nfix' and
; written only in range, so no guard depends on its shape.

(defconst *fn-zin-fields* 20)
(defmacro fn-zin-mode (fn-zin-st) `(fn-zin-fld 0 ,fn-zin-st))    ; the mode, below
(defmacro fn-zin-bits (fn-zin-st) `(fn-zin-fld 1 ,fn-zin-st))    ; the bit buffer
(defmacro fn-zin-nbits (fn-zin-st) `(fn-zin-fld 2 ,fn-zin-st))   ; bits in it
(defmacro fn-zin-n (fn-zin-st) `(fn-zin-fld 3 ,fn-zin-st))       ; octets left to copy
(defmacro fn-zin-dist (fn-zin-st) `(fn-zin-fld 4 ,fn-zin-st))    ; the match distance
(defmacro fn-zin-wpos (fn-zin-st) `(fn-zin-fld 5 ,fn-zin-st))    ; the window's next cell
(defmacro fn-zin-tout (fn-zin-st) `(fn-zin-fld 6 ,fn-zin-st))    ; octets produced, ever
(defmacro fn-zin-tin (fn-zin-st) `(fn-zin-fld 7 ,fn-zin-st))     ; octets read, ever
(defmacro fn-zin-dcode (fn-zin-st) `(fn-zin-fld 8 ,fn-zin-st))   ; the Huffman decode in
(defmacro fn-zin-dfirst (fn-zin-st) `(fn-zin-fld 9 ,fn-zin-st))  ;   progress: code, first,
(defmacro fn-zin-dindex (fn-zin-st) `(fn-zin-fld 10 ,fn-zin-st)) ;   index and length
(defmacro fn-zin-dlen (fn-zin-st) `(fn-zin-fld 11 ,fn-zin-st))
(defmacro fn-zin-final (fn-zin-st) `(fn-zin-fld 12 ,fn-zin-st))  ; this block is the last
(defmacro fn-zin-sym (fn-zin-st) `(fn-zin-fld 13 ,fn-zin-st))    ; a symbol awaiting its extra bits
(defmacro fn-zin-hlit (fn-zin-st) `(fn-zin-fld 14 ,fn-zin-st))
(defmacro fn-zin-hdist (fn-zin-st) `(fn-zin-fld 15 ,fn-zin-st))
(defmacro fn-zin-hclen (fn-zin-st) `(fn-zin-fld 16 ,fn-zin-st))
(defmacro fn-zin-idx (fn-zin-st) `(fn-zin-fld 17 ,fn-zin-st))    ; the code length being read
(defmacro fn-zin-preset (fn-zin-st) `(fn-zin-fld 18 ,fn-zin-st)) ; a preset dictionary's
                                                   ; octets (at most 32 KiB; reset keeps it)

(defstobj fn-zin-st
  (fn-zin-regs :type (array (integer 0 *) (20)) :initially 0))

(defun-inline fn-zin-fld (i fn-zin-st)
  (declare (xargs :stobjs fn-zin-st :guard (natp i)))
  (if (< (nfix i) 20) (nfix (fn-zin-regsi (nfix i) fn-zin-st)) 0))

(defthm fn-zin-fld-natp
  (natp (fn-zin-fld i fn-zin-st))
  :rule-classes :type-prescription)

(defun-inline fn-zin-set (i v fn-zin-st)
  (declare (xargs :stobjs fn-zin-st :guard (natp i)))
  (if (and (natp i) (< i 20))
      (update-fn-zin-regsi i (nfix v) fn-zin-st)
    fn-zin-st))

(defun fn-zin-reset-loop (i fn-zin-st)
  (declare (xargs :stobjs fn-zin-st :guard (natp i) :measure (nfix (- 20 (nfix i)))))
  (if (and (natp i) (< i 18))
      (let ((fn-zin-st (fn-zin-set i 0 fn-zin-st)))
        (fn-zin-reset-loop (1+ i) fn-zin-st))
    fn-zin-st))

(defun fn-zin-reset (fn-zin-st)
  ; The initial state: mode 0 (a block header), an empty bit buffer, nothing
  ; read or produced; the Huffman length starts at 1.  A preset dictionary
  ; loaded into the window (fn-zin-load-preset, field 18) is kept: one
  ; decoder serves every payload of that dictionary.
  (declare (xargs :stobjs fn-zin-st))
  (let ((fn-zin-st (fn-zin-reset-loop 0 fn-zin-st)))
    (fn-zin-set 11 1 fn-zin-st)))

(defthm fn-zin-fld-of-set
  (equal (fn-zin-fld i (fn-zin-set j v fn-zin-st))
         (if (and (equal (nfix i) j) (natp j) (< j 20))
             (nfix v)
           (fn-zin-fld i fn-zin-st))))

(in-theory (disable fn-zin-fld$inline fn-zin-set$inline))

; Modes.
(defconst *fn-zin-m-header* 0)      ; 3 bits: BFINAL, BTYPE
(defconst *fn-zin-m-stored-align* 1) ; drop to an octet boundary
(defconst *fn-zin-m-stored-len* 2)  ; 32 bits: LEN, NLEN
(defconst *fn-zin-m-stored* 3)      ; N literal octets
(defconst *fn-zin-m-dyn* 4)         ; 14 bits: HLIT, HDIST, HCLEN
(defconst *fn-zin-m-cl* 5)          ; the code-length code lengths
(defconst *fn-zin-m-lens* 6)        ; the code lengths, by the code-length code
(defconst *fn-zin-m-repeat* 7)      ; a repeat code's extra bits
(defconst *fn-zin-m-lit* 8)         ; a literal/length symbol
(defconst *fn-zin-m-lext* 9)        ; a length's extra bits
(defconst *fn-zin-m-dsym* 10)       ; a distance symbol
(defconst *fn-zin-m-dext* 11)       ; a distance's extra bits
(defconst *fn-zin-m-copy* 12)       ; N octets from DIST back
(defconst *fn-zin-m-ended* 13)      ; the final block ended

; -----------------------------------------------------------------------------
; The table buffer, two octets per entry.

(defun fn-zin-tab-okp (fn-zin-tab)
  (declare (xargs :stobjs fn-zin-tab))
  (eql (fn-zin-tab-len fn-zin-tab) *fn-zin-tab-octets*))

(defun-inline fn-zin-tget (e fn-zin-tab)
  (declare (xargs :stobjs fn-zin-tab
                  :guard (and (natp e) (< e *fn-zin-tab-entries*) (fn-zin-tab-okp fn-zin-tab))))
  (+ (nfix (fn-zin-tab-get (* 2 e) fn-zin-tab))
     (* 256 (nfix (fn-zin-tab-get (+ 1 (* 2 e)) fn-zin-tab)))))

(defthm fn-zin-tget-natp
  (natp (fn-zin-tget e fn-zin-tab))
  :rule-classes :type-prescription)

(encapsulate
  ()
  (local (include-book "arithmetic-5/top" :dir :system))

  (defun fn-zin-lo8 (v)
    (declare (xargs :guard t))
    (mod (nfix v) 256))

  (defun fn-zin-hi8 (v)
    (declare (xargs :guard t))
    (fn-zin-lo8 (floor (nfix v) 256)))

  (defthm fn-zin-lo8-octet
    (fn-cbor-octetp (fn-zin-lo8 v))
    :hints (("Goal" :in-theory (enable fn-cbor-octetp))))

  (defthm fn-zin-lo8-hi8-octets
    (and (fn-cbor-octetp (fn-zin-lo8 v)) (fn-cbor-octetp (fn-zin-hi8 v)))
    :hints (("Goal" :in-theory (disable fn-zin-lo8))))

  (defun fn-zin-lowb (x n)
    ; The low N bits of X.
    (declare (xargs :guard (and (natp x) (natp n))))
    (mod (nfix x) (expt 2 (nfix n))))

  (defun fn-zin-highb (x n)
    ; X without its low N bits.
    (declare (xargs :guard (and (natp x) (natp n))))
    (floor (nfix x) (expt 2 (nfix n))))

  (local
   (defthm fn-zin-mod-floor-pow2
     (implies (and (natp x) (natp n))
              (and (natp (mod x (expt 2 n)))
                   (natp (floor x (expt 2 n)))
                   (< (mod x (expt 2 n)) (expt 2 n))))
     :rule-classes nil))

  (defthm fn-zin-lowb-highb-natp
    (and (natp (fn-zin-lowb x n)) (natp (fn-zin-highb x n)))
    :hints (("Goal" :use ((:instance fn-zin-mod-floor-pow2 (x (nfix x)) (n (nfix n))))
             :in-theory (disable mod floor)))
    :rule-classes ((:type-prescription :corollary (natp (fn-zin-lowb x n)))
                   (:type-prescription :corollary (natp (fn-zin-highb x n)))))

  (defthm fn-zin-lowb-bound
    (< (fn-zin-lowb x n) (expt 2 (nfix n)))
    :hints (("Goal" :use ((:instance fn-zin-mod-floor-pow2 (x (nfix x)) (n (nfix n))))
             :in-theory (disable mod floor)))
    :rule-classes :linear)

  (defun-inline fn-zin-bit (x)
    (declare (xargs :guard t))
    (mod (nfix x) 2))

  (defun-inline fn-zin-half (x)
    (declare (xargs :guard t))
    (floor (nfix x) 2))

  (defthm fn-zin-bit-half-natp
    (and (natp (fn-zin-bit x)) (natp (fn-zin-half x)) (<= (fn-zin-bit x) 1))
    :rule-classes ((:type-prescription :corollary (natp (fn-zin-bit x)))
                   (:type-prescription :corollary (natp (fn-zin-half x)))
                   (:linear :corollary (<= (fn-zin-bit x) 1))))

  (defun fn-zin-shift-in (bits nbits o)
    ; An input octet above the NBITS bits already held (LSB first).
    (declare (xargs :guard (and (natp bits) (natp nbits) (natp o))))
    (+ (nfix bits) (* (nfix o) (expt 2 (nfix nbits)))))

  (defthm fn-zin-shift-in-natp
    (natp (fn-zin-shift-in bits nbits o))
    :rule-classes :type-prescription))

(in-theory (disable fn-zin-lo8 fn-zin-hi8 fn-zin-lowb fn-zin-highb fn-zin-shift-in
                    fn-zin-bit$inline fn-zin-half$inline))

(defun fn-zin-tput (e v fn-zin-tab)
  (declare (xargs :stobjs fn-zin-tab
                  :guard (and (natp e) (< e *fn-zin-tab-entries*) (fn-zin-tab-okp fn-zin-tab))))
  (let ((fn-zin-tab (fn-zin-tab-put (* 2 e) (fn-zin-lo8 v) fn-zin-tab)))
    (fn-zin-tab-put (+ 1 (* 2 e)) (fn-zin-hi8 v) fn-zin-tab)))

(defthm fn-zin-tput-keeps
  (implies (and (fn-cbor-octet-listp fn-zin-tab) (natp e) (< e *fn-zin-tab-entries*)
                (equal (len fn-zin-tab) *fn-zin-tab-octets*))
           (and (fn-cbor-octet-listp (fn-zin-tput e v fn-zin-tab))
                (equal (len (fn-zin-tput e v fn-zin-tab)) *fn-zin-tab-octets*)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-zin-lo8 fn-zin-hi8 fn-cbor-octet-listp update-nth))))

(in-theory (disable fn-zin-tget$inline fn-zin-tput))

; -----------------------------------------------------------------------------
; Building a canonical Huffman table (puff's `construct').  The code
; lengths of N symbols are the table entries [LB, LB + N); the counts and
; symbols go to table TB.  The answer is puff's LEFT: 0 for a complete
; code, positive for an incomplete one, negative for an over-subscribed
; one; an all-zero set of lengths answers 0 and decodes nothing.

(defun fn-zin-zero-counts (k cb fn-zin-tab)
  (declare (xargs :stobjs fn-zin-tab
                  :guard (and (natp k) (natp cb) (<= (+ cb 16) 707) (fn-zin-tab-okp fn-zin-tab))
                  :measure (nfix (- 16 (nfix k)))))
  (if (and (natp k) (< k 16) (natp cb) (<= (+ cb 16) 707))
      (let ((fn-zin-tab (fn-zin-tput (+ cb k) 0 fn-zin-tab)))
        (fn-zin-zero-counts (1+ k) cb fn-zin-tab))
    fn-zin-tab))

(defthm fn-zin-zero-counts-keeps
  (implies (and (fn-cbor-octet-listp fn-zin-tab) (equal (len fn-zin-tab) *fn-zin-tab-octets*))
           (and (fn-cbor-octet-listp (fn-zin-zero-counts k cb fn-zin-tab))
                (equal (len (fn-zin-zero-counts k cb fn-zin-tab)) *fn-zin-tab-octets*))))

(defun fn-zin-len-of (e fn-zin-tab)
  ; A code length, read as at most 15.
  (declare (xargs :stobjs fn-zin-tab
                  :guard (and (natp e) (< e *fn-zin-tab-entries*) (fn-zin-tab-okp fn-zin-tab))))
  (min 15 (fn-zin-tget e fn-zin-tab)))

(defthm fn-zin-len-of-bounds
  (implies (fn-cbor-octet-listp fn-zin-tab)
           (and (natp (fn-zin-len-of e fn-zin-tab))
                (<= (fn-zin-len-of e fn-zin-tab) 15)))
  :rule-classes ((:type-prescription :corollary
                  (implies (fn-cbor-octet-listp fn-zin-tab)
                           (natp (fn-zin-len-of e fn-zin-tab))))
                 (:linear :corollary
                  (implies (fn-cbor-octet-listp fn-zin-tab)
                           (<= (fn-zin-len-of e fn-zin-tab) 15)))))

(in-theory (disable fn-zin-len-of))

(defun fn-zin-count-lens (s n lb cb fn-zin-tab)
  (declare (xargs :stobjs fn-zin-tab
                  :guard (and (natp s) (natp n) (natp lb) (<= (+ lb n) 320)
                              (natp cb) (<= (+ cb 16) 707) (fn-zin-tab-okp fn-zin-tab))
                  :measure (nfix (- (nfix n) (nfix s)))))
  (if (and (natp s) (natp n) (< s n) (natp lb) (<= (+ lb n) 320)
           (natp cb) (<= (+ cb 16) 707))
      (let* ((l (fn-zin-len-of (+ lb s) fn-zin-tab))
             (fn-zin-tab (fn-zin-tput (+ cb l) (1+ (fn-zin-tget (+ cb l) fn-zin-tab))
                                      fn-zin-tab)))
        (fn-zin-count-lens (1+ s) n lb cb fn-zin-tab))
    fn-zin-tab))

(defthm fn-zin-count-lens-keeps
  (implies (and (fn-cbor-octet-listp fn-zin-tab) (equal (len fn-zin-tab) *fn-zin-tab-octets*))
           (and (fn-cbor-octet-listp (fn-zin-count-lens s n lb cb fn-zin-tab))
                (equal (len (fn-zin-count-lens s n lb cb fn-zin-tab)) *fn-zin-tab-octets*))))

(defun fn-zin-left (len left cb fn-zin-tab)
  ; Section 3.2.2's check, puff's loop: LEFT codes of length LEN - 1 unused.
  (declare (xargs :stobjs fn-zin-tab
                  :guard (and (natp len) (integerp left) (natp cb) (<= (+ cb 16) 707)
                              (fn-zin-tab-okp fn-zin-tab))
                  :measure (nfix (- 16 (nfix len)))))
  (if (and (natp len) (< len 16) (natp cb) (<= (+ cb 16) 707) (integerp left))
      (let ((left (- (* 2 left) (fn-zin-tget (+ cb len) fn-zin-tab))))
        (if (< left 0)
            left
          (fn-zin-left (1+ len) left cb fn-zin-tab)))
    (ifix left)))

(defun fn-zin-offsets (len off cb fn-zin-tab)
  ; The scratch offsets: the first symbol index of each length.
  (declare (xargs :stobjs fn-zin-tab
                  :guard (and (natp len) (natp off) (natp cb) (<= (+ cb 16) 707)
                              (fn-zin-tab-okp fn-zin-tab))
                  :measure (nfix (- 16 (nfix len)))))
  (if (and (natp len) (< len 16) (natp cb) (<= (+ cb 16) 707) (natp off))
      (let ((fn-zin-tab (fn-zin-tput (+ 707 len) off fn-zin-tab)))
        (fn-zin-offsets (1+ len) (+ off (fn-zin-tget (+ cb len) fn-zin-tab)) cb fn-zin-tab))
    fn-zin-tab))

(defthm fn-zin-offsets-keeps
  (implies (and (fn-cbor-octet-listp fn-zin-tab) (equal (len fn-zin-tab) *fn-zin-tab-octets*))
           (and (fn-cbor-octet-listp (fn-zin-offsets len off cb fn-zin-tab))
                (equal (len (fn-zin-offsets len off cb fn-zin-tab)) *fn-zin-tab-octets*))))

(defun fn-zin-place-syms (s n lb sb smax fn-zin-tab)
  (declare (xargs :stobjs fn-zin-tab
                  :guard (and (natp s) (natp n) (natp lb) (<= (+ lb n) 320)
                              (natp sb) (natp smax) (<= (+ sb smax) 707)
                              (fn-zin-tab-okp fn-zin-tab))
                  :measure (nfix (- (nfix n) (nfix s)))))
  (if (and (natp s) (natp n) (< s n) (natp lb) (<= (+ lb n) 320)
           (natp sb) (natp smax) (<= (+ sb smax) 707))
      (let ((l (fn-zin-len-of (+ lb s) fn-zin-tab)))
        (if (eql l 0)
            (fn-zin-place-syms (1+ s) n lb sb smax fn-zin-tab)
          (let ((o (fn-zin-tget (+ 707 l) fn-zin-tab)))
            (if (< o smax)
                (let* ((fn-zin-tab (fn-zin-tput (+ sb o) s fn-zin-tab))
                       (fn-zin-tab (fn-zin-tput (+ 707 l) (1+ o) fn-zin-tab)))
                  (fn-zin-place-syms (1+ s) n lb sb smax fn-zin-tab))
              (fn-zin-place-syms (1+ s) n lb sb smax fn-zin-tab)))))
    fn-zin-tab))

(defthm fn-zin-place-syms-keeps
  (implies (and (fn-cbor-octet-listp fn-zin-tab) (equal (len fn-zin-tab) *fn-zin-tab-octets*))
           (and (fn-cbor-octet-listp (fn-zin-place-syms s n lb sb smax fn-zin-tab))
                (equal (len (fn-zin-place-syms s n lb sb smax fn-zin-tab)) *fn-zin-tab-octets*))))

; The 9-bit lookup of tables 0 and 1 (zlib's first-level table): what the
; canonical walk decodes from a code of at most 9 bits, in one read.  It is
; a cache of the walk: fn-zin-decode-bit takes an entry only when its code
; is complete in the bits held, and walks otherwise.

(defconst *fn-zin-pow2* '(1 2 4 8 16 32 64 128 256 512))

(defun fn-zin-lk-base (tb)
  (declare (xargs :guard t))
  (if (eql tb 0) 723 1235))

(defthm fn-zin-lk-base-bounds
  (and (natp (fn-zin-lk-base tb)) (<= (+ 512 (fn-zin-lk-base tb)) 1747))
  :rule-classes ((:type-prescription :corollary (natp (fn-zin-lk-base tb)))
                 (:linear :corollary (<= (+ 512 (fn-zin-lk-base tb)) 1747))))

(in-theory (disable fn-zin-lk-base))

(defun fn-zin-zero-range (e k fn-zin-tab)
  (declare (xargs :stobjs fn-zin-tab
                  :guard (and (natp e) (natp k) (fn-zin-tab-okp fn-zin-tab))
                  :measure (nfix k)))
  (if (and (posp k) (natp e) (< e *fn-zin-tab-entries*))
      (let ((fn-zin-tab (fn-zin-tput e 0 fn-zin-tab)))
        (fn-zin-zero-range (1+ e) (1- k) fn-zin-tab))
    fn-zin-tab))

(defthm fn-zin-zero-range-keeps
  (implies (and (fn-cbor-octet-listp fn-zin-tab) (equal (len fn-zin-tab) *fn-zin-tab-octets*))
           (and (fn-cbor-octet-listp (fn-zin-zero-range e k fn-zin-tab))
                (equal (len (fn-zin-zero-range e k fn-zin-tab)) *fn-zin-tab-octets*))))

(defun fn-zin-next-codes (len code cb fn-zin-tab)
  ; RFC 1951 section 3.2.2 step 2: the first code of each length, into the
  ; scratch entries 707 + LEN.
  (declare (xargs :stobjs fn-zin-tab
                  :guard (and (natp len) (natp code) (natp cb) (<= (+ cb 16) 707)
                              (fn-zin-tab-okp fn-zin-tab))
                  :measure (nfix (- 16 (nfix len)))))
  (if (and (natp len) (<= 1 len) (< len 16) (natp cb) (<= (+ cb 16) 707) (natp code))
      (let* ((code (* 2 (+ code (if (eql len 1) 0 (fn-zin-tget (+ cb (1- len)) fn-zin-tab)))))
             (fn-zin-tab (fn-zin-tput (+ 707 len) code fn-zin-tab)))
        (fn-zin-next-codes (1+ len) code cb fn-zin-tab))
    fn-zin-tab))

(defthm fn-zin-next-codes-keeps
  (implies (and (fn-cbor-octet-listp fn-zin-tab) (equal (len fn-zin-tab) *fn-zin-tab-octets*))
           (and (fn-cbor-octet-listp (fn-zin-next-codes len code cb fn-zin-tab))
                (equal (len (fn-zin-next-codes len code cb fn-zin-tab)) *fn-zin-tab-octets*))))

(defun fn-zin-rev (c l acc)
  ; The L low bits of C, reversed.
  (declare (xargs :guard (and (natp c) (natp l) (natp acc)) :measure (nfix l)))
  (if (zp l)
      (nfix acc)
    (fn-zin-rev (fn-zin-half c) (1- l) (+ (* 2 (nfix acc)) (fn-zin-bit c)))))

(defthm fn-zin-rev-natp
  (natp (fn-zin-rev c l acc))
  :rule-classes :type-prescription)

(defun fn-zin-replicate (e step k v fn-zin-tab)
  ; Entries E, E + STEP, ... (K of them) of the lookup set to V.
  (declare (xargs :stobjs fn-zin-tab
                  :guard (and (natp e) (posp step) (natp k) (fn-zin-tab-okp fn-zin-tab))
                  :measure (nfix k)))
  (if (and (posp k) (natp e) (< e *fn-zin-tab-entries*) (posp step))
      (let ((fn-zin-tab (fn-zin-tput e v fn-zin-tab)))
        (fn-zin-replicate (+ e step) step (1- k) v fn-zin-tab))
    fn-zin-tab))

(defthm fn-zin-replicate-keeps
  (implies (and (fn-cbor-octet-listp fn-zin-tab) (equal (len fn-zin-tab) *fn-zin-tab-octets*))
           (and (fn-cbor-octet-listp (fn-zin-replicate e step k v fn-zin-tab))
                (equal (len (fn-zin-replicate e step k v fn-zin-tab)) *fn-zin-tab-octets*))))

(defun fn-zin-fill-lookup (s n lb base fn-zin-tab)
  ; Every symbol of a code of length 1..9 into the lookup at BASE, in
  ; symbol order (the canonical assignment).
  (declare (xargs :stobjs fn-zin-tab
                  :guard (and (natp s) (natp n) (natp lb) (<= (+ lb n) 320) (natp base)
                              (fn-zin-tab-okp fn-zin-tab))
                  :measure (nfix (- (nfix n) (nfix s)))))
  (if (and (natp s) (natp n) (< s n) (natp lb) (<= (+ lb n) 320) (natp base))
      (let ((l (fn-zin-len-of (+ lb s) fn-zin-tab)))
        (if (and (<= 1 l) (<= l 9))
            (let* ((c (fn-zin-tget (+ 707 l) fn-zin-tab))
                   (fn-zin-tab (fn-zin-tput (+ 707 l) (1+ c) fn-zin-tab))
                   (r (fn-zin-rev c l 0))
                   (step (max 1 (fn-zin-at l *fn-zin-pow2*)))
                   (fn-zin-tab (if (< r step)
                                   (fn-zin-replicate (+ base r) step
                                                     (fn-zin-at (- 9 l) *fn-zin-pow2*)
                                                     (+ (* 512 l) s) fn-zin-tab)
                                 fn-zin-tab)))
              (fn-zin-fill-lookup (1+ s) n lb base fn-zin-tab))
          (fn-zin-fill-lookup (1+ s) n lb base fn-zin-tab)))
    fn-zin-tab))

(defthm fn-zin-fill-lookup-keeps
  (implies (and (fn-cbor-octet-listp fn-zin-tab) (equal (len fn-zin-tab) *fn-zin-tab-octets*))
           (and (fn-cbor-octet-listp (fn-zin-fill-lookup s n lb base fn-zin-tab))
                (equal (len (fn-zin-fill-lookup s n lb base fn-zin-tab)) *fn-zin-tab-octets*))))

(defun fn-zin-construct (tb lb n fn-zin-tab)
  ; (mv LEFT fn-zin-tab).
  (declare (xargs :stobjs fn-zin-tab
                  :guard (and (natp lb) (natp n) (<= (+ lb n) 320)
                              (<= n (fn-zin-sym-max tb))
                              (fn-zin-tab-okp fn-zin-tab))))
  (let* ((cb (fn-zin-cnt-base tb))
         (lookp (or (eql tb 0) (eql tb 1)))
         (fn-zin-tab (if lookp (fn-zin-zero-range (fn-zin-lk-base tb) 512 fn-zin-tab) fn-zin-tab))
         (fn-zin-tab (fn-zin-zero-counts 0 cb fn-zin-tab))
         (fn-zin-tab (fn-zin-count-lens 0 n lb cb fn-zin-tab)))
    (if (eql (fn-zin-tget cb fn-zin-tab) (nfix n))
        (mv 0 fn-zin-tab)
      (let* ((left (fn-zin-left 1 1 cb fn-zin-tab)))
        (if (< left 0)
            (mv left fn-zin-tab)
          (let* ((fn-zin-tab (fn-zin-offsets 1 0 cb fn-zin-tab))
                 (fn-zin-tab (fn-zin-place-syms 0 n lb (fn-zin-sym-base tb)
                                                (fn-zin-sym-max tb) fn-zin-tab))
                 (fn-zin-tab (if lookp
                                 (let ((fn-zin-tab (fn-zin-next-codes 1 0 cb fn-zin-tab)))
                                   (fn-zin-fill-lookup 0 n lb (fn-zin-lk-base tb) fn-zin-tab))
                               fn-zin-tab)))
            (mv left fn-zin-tab)))))))

(defthm fn-zin-construct-keeps
  (implies (and (fn-cbor-octet-listp fn-zin-tab) (equal (len fn-zin-tab) *fn-zin-tab-octets*))
           (and (fn-cbor-octet-listp (mv-nth 1 (fn-zin-construct tb lb n fn-zin-tab)))
                (equal (len (mv-nth 1 (fn-zin-construct tb lb n fn-zin-tab)))
                       *fn-zin-tab-octets*))))

(defthm fn-zin-left-integerp
  (integerp (fn-zin-left len left cb fn-zin-tab))
  :rule-classes :type-prescription)

(defthm fn-zin-construct-left-integerp
  (integerp (car (fn-zin-construct tb lb n fn-zin-tab)))
  :rule-classes :type-prescription)

(in-theory (disable fn-zin-construct))

; -----------------------------------------------------------------------------
; Bits, octets in and out.

(defun fn-zin-take (n fn-zin-st)
  ; The low N bits of the bit buffer, and ZS without them.  The caller has
  ; checked that N bits are there.
  (declare (xargs :stobjs fn-zin-st :guard (natp n)))
  (let* ((v (fn-zin-lowb (fn-zin-bits fn-zin-st) n))
         (fn-zin-st (fn-zin-set 1 (fn-zin-highb (fn-zin-bits fn-zin-st) n) fn-zin-st))
         (fn-zin-st (fn-zin-set 2 (- (fn-zin-nbits fn-zin-st) (nfix n)) fn-zin-st)))
    (mv v fn-zin-st)))

(defthm fn-zin-take-natp
  (natp (car (fn-zin-take n fn-zin-st)))
  :rule-classes :type-prescription)

(defthm fn-zin-take-bound
  (< (car (fn-zin-take n fn-zin-st)) (expt 2 (nfix n)))
  :rule-classes :linear)

(in-theory (disable fn-zin-take))

(defun fn-zin-window-ready-p (fn-zin-win)
  (declare (xargs :stobjs fn-zin-win))
  (eql (fn-zin-win-len fn-zin-win) *fn-zin-win-octets*))

(defun-inline fn-zin-wrap (p)
  (declare (xargs :guard t))
  (let ((p (nfix p))) (if (< p *fn-zin-window*) p 0)))

(defthm fn-zin-wrap-bounds
  (and (natp (fn-zin-wrap p)) (< (fn-zin-wrap p) *fn-zin-window*))
  :rule-classes ((:type-prescription :corollary (natp (fn-zin-wrap p)))
                 (:linear :corollary (< (fn-zin-wrap p) *fn-zin-window*))))

(in-theory (disable fn-zin-wrap$inline))

(defun fn-zin-bomb-limit (fn-zin-st)
  (declare (xargs :stobjs fn-zin-st :guard t))
  (+ (* *fn-zin-ratio* (fn-zin-tin fn-zin-st)) *fn-zin-slack*))

(defun fn-zin-emit (o fn-zin-st fn-zin-win fn-zin-out)
  ; One output octet: into the output and the window, counted; refused
  ; (:bomb) when it would pass the ratio bound.  (mv refusal fn-zin-st win out).
  (declare (xargs :stobjs (fn-zin-win fn-zin-out fn-zin-st)
                  :guard (and (fn-cbor-octetp o) (fn-zin-window-ready-p fn-zin-win))))
  (if (< (fn-zin-bomb-limit fn-zin-st) (1+ (fn-zin-tout fn-zin-st)))
      (mv :bomb fn-zin-st fn-zin-win fn-zin-out)
    (let* ((w (fn-zin-wrap (fn-zin-wpos fn-zin-st)))
           (fn-zin-out (fn-zin-out-append-octet o fn-zin-out))
           (fn-zin-win (fn-zin-win-put w o fn-zin-win))
           (fn-zin-st (fn-zin-set 5 (fn-zin-wrap (1+ w)) fn-zin-st))
           (fn-zin-st (fn-zin-set 6 (1+ (fn-zin-tout fn-zin-st)) fn-zin-st)))
      (mv nil fn-zin-st fn-zin-win fn-zin-out))))

(defthm fn-zin-emit-keeps
  (implies (and (fn-cbor-octet-listp fn-zin-win) (equal (len fn-zin-win) *fn-zin-win-octets*)
                (fn-cbor-octet-listp fn-zin-out) (fn-cbor-octetp o))
           (and (fn-cbor-octet-listp (mv-nth 2 (fn-zin-emit o fn-zin-st fn-zin-win fn-zin-out)))
                (equal (len (mv-nth 2 (fn-zin-emit o fn-zin-st fn-zin-win fn-zin-out)))
                       *fn-zin-win-octets*)
                (fn-cbor-octet-listp (mv-nth 3 (fn-zin-emit o fn-zin-st fn-zin-win fn-zin-out))))))

(defthm fn-zin-emit-out
  (equal (mv-nth 3 (fn-zin-emit o fn-zin-st fn-zin-win fn-zin-out))
         (if (car (fn-zin-emit o fn-zin-st fn-zin-win fn-zin-out))
             fn-zin-out
           (fn-oct-snoc fn-zin-out o))))

(in-theory (disable fn-zin-emit))

(defun fn-zin-source (d tout h w fn-zin-win)
  ; The octet D back, TOUT octets having been produced and the preset
  ; holding H: the ring's (W its next cell) when D is within the output,
  ; else the preset's, D - TOUT octets back from its end.
  (declare (xargs :stobjs fn-zin-win
                  :guard (and (natp d) (natp tout) (natp h) (natp w)
                              (fn-zin-window-ready-p fn-zin-win))))
  (let* ((d (min (nfix d) *fn-zin-window*))
         (h (min (nfix h) *fn-zin-window*))
         (e (- d (nfix tout))))
    (if (and (< 0 e) (<= e h))
        (fn-zin-win-get (+ *fn-zin-window* (- h e)) fn-zin-win)
      (let ((w (fn-zin-wrap w)))
        (fn-zin-win-get (fn-zin-wrap (if (<= d w) (- w d) (- (+ w *fn-zin-window*) d)))
                        fn-zin-win)))))

(defthm fn-zin-source-octet
  (implies (and (fn-cbor-octet-listp fn-zin-win) (equal (len fn-zin-win) *fn-zin-win-octets*))
           (fn-cbor-octetp (fn-zin-source d tout h w fn-zin-win))))

(in-theory (disable fn-zin-source))

(defun fn-zin-back (fn-zin-st fn-zin-win)
  ; The octet DIST back.
  (declare (xargs :stobjs (fn-zin-win fn-zin-st) :guard (fn-zin-window-ready-p fn-zin-win)))
  (fn-zin-source (fn-zin-dist fn-zin-st) (fn-zin-tout fn-zin-st) (fn-zin-preset fn-zin-st)
                 (fn-zin-wpos fn-zin-st) fn-zin-win))

(defthm fn-zin-back-octet
  (implies (and (fn-cbor-octet-listp fn-zin-win) (equal (len fn-zin-win) *fn-zin-win-octets*))
           (fn-cbor-octetp (fn-zin-back fn-zin-st fn-zin-win))))

(in-theory (disable fn-zin-back))

; -----------------------------------------------------------------------------
; A Huffman decode (puff's `decode'), over the bits in hand: the walk
; consumes them one at a time from the bit buffer, in locals, until a code
; of some length matches, no code can (past length 15), or the bits run out
; -- then the decode state is written back once, and the next call resumes
; it after the loop has pulled another octet.  (mv KIND SYM ZS): KIND 0 go
; on (the bits ran out), 1 the symbol SYM (the decode state reset), 2 no
; code of any length matched.

(defun fn-zin-decode-reset (fn-zin-st)
  (declare (xargs :stobjs fn-zin-st :guard t))
  (let* ((fn-zin-st (fn-zin-set 8 0 fn-zin-st))
         (fn-zin-st (fn-zin-set 9 0 fn-zin-st))
         (fn-zin-st (fn-zin-set 10 0 fn-zin-st)))
    (fn-zin-set 11 1 fn-zin-st)))

(defun fn-zin-walk (tb bits nbits code first index len fn-zin-tab)
  ; (mv KIND SYM BITS NBITS CODE FIRST INDEX LEN).
  (declare (xargs :stobjs fn-zin-tab :guard (and (natp nbits) (fn-zin-tab-okp fn-zin-tab))
                  :measure (nfix nbits)))
  (if (zp nbits)
      (mv 0 0 bits 0 code first index len)
    (let* ((len (if (and (integerp len) (<= 1 len) (<= len 15)) len 1))
           (code (+ (nfix code) (fn-zin-bit bits)))
           (bits (fn-zin-half bits))
           (nbits (1- nbits))
           (first (nfix first))
           (index (nfix index))
           (count (fn-zin-tget (+ (fn-zin-cnt-base tb) len) fn-zin-tab)))
      (cond ((< (- code first) count)
             (let ((k (+ index (- code first))))
               (if (and (<= 0 k) (< k (fn-zin-sym-max tb)))
                   (mv 1 (fn-zin-tget (+ (fn-zin-sym-base tb) k) fn-zin-tab)
                       bits nbits 0 0 0 1)
                 (mv 2 0 bits nbits code first index len))))
            ((<= 15 len) (mv 2 0 bits nbits code first index len))
            (t (fn-zin-walk tb bits nbits (* 2 code) (* 2 (+ first count))
                            (+ index count) (1+ len) fn-zin-tab))))))

(defthm fn-zin-walk-sym-natp
  (natp (mv-nth 1 (fn-zin-walk tb bits nbits code first index len fn-zin-tab)))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-zin-walk tb bits nbits code first index len fn-zin-tab))))

(defun fn-zin-decode-bit (tb fn-zin-st fn-zin-tab)
  (declare (xargs :stobjs (fn-zin-tab fn-zin-st) :guard (fn-zin-tab-okp fn-zin-tab)))
  (let* ((bits (fn-zin-bits fn-zin-st))
         (nbits (fn-zin-nbits fn-zin-st))
         (e (if (and (or (eql tb 0) (eql tb 1))
                     (eql (fn-zin-dlen fn-zin-st) 1) (eql (fn-zin-dcode fn-zin-st) 0)
                     (eql (fn-zin-dfirst fn-zin-st) 0) (eql (fn-zin-dindex fn-zin-st) 0))
                (fn-zin-tget (+ (fn-zin-lk-base tb) (fn-zin-lowb bits 9)) fn-zin-tab)
              0))
         (l (fn-zin-highb e 9)))
    (if (and (<= 1 l) (<= l 9) (<= l nbits))
        ; A whole code of at most 9 bits is in hand: the lookup's symbol.
        (let* ((fn-zin-st (fn-zin-set 1 (fn-zin-highb bits l) fn-zin-st))
               (fn-zin-st (fn-zin-set 2 (- nbits l) fn-zin-st)))
          (mv 1 (fn-zin-lowb e 9) fn-zin-st))
      (mv-let (kind sym bits nbits code first index len)
        (fn-zin-walk tb bits nbits
                     (fn-zin-dcode fn-zin-st) (fn-zin-dfirst fn-zin-st)
                     (fn-zin-dindex fn-zin-st) (fn-zin-dlen fn-zin-st) fn-zin-tab)
        (let* ((fn-zin-st (fn-zin-set 1 bits fn-zin-st))
               (fn-zin-st (fn-zin-set 2 nbits fn-zin-st))
               (fn-zin-st (fn-zin-set 8 code fn-zin-st))
               (fn-zin-st (fn-zin-set 9 first fn-zin-st))
               (fn-zin-st (fn-zin-set 10 index fn-zin-st))
               (fn-zin-st (fn-zin-set 11 len fn-zin-st)))
          (mv kind sym fn-zin-st))))))

(defthm fn-zin-decode-bit-natp
  (natp (mv-nth 1 (fn-zin-decode-bit tb fn-zin-st fn-zin-tab)))
  :rule-classes :type-prescription)

(in-theory (disable fn-zin-decode-bit))

; -----------------------------------------------------------------------------
; Table fills: a run of equal code lengths.

(defun fn-zin-fill (e k v fn-zin-tab)
  ; Entries [E, E + K) of the code lengths set to V (within [0, 320)).
  (declare (xargs :stobjs fn-zin-tab
                  :guard (and (natp e) (natp k) (fn-zin-tab-okp fn-zin-tab))
                  :measure (nfix k)))
  (if (and (posp k) (natp e) (< e 320))
      (let ((fn-zin-tab (fn-zin-tput e v fn-zin-tab)))
        (fn-zin-fill (1+ e) (1- k) v fn-zin-tab))
    fn-zin-tab))

(defthm fn-zin-fill-keeps
  (implies (and (fn-cbor-octet-listp fn-zin-tab) (equal (len fn-zin-tab) *fn-zin-tab-octets*))
           (and (fn-cbor-octet-listp (fn-zin-fill e k v fn-zin-tab))
                (equal (len (fn-zin-fill e k v fn-zin-tab)) *fn-zin-tab-octets*))))

(defun fn-zin-zero-cl (i fn-zin-tab)
  ; The code-length code lengths not sent (positions I..18 of the order).
  (declare (xargs :stobjs fn-zin-tab
                  :guard (and (natp i) (fn-zin-tab-okp fn-zin-tab))
                  :measure (nfix (- 19 (nfix i)))))
  (if (and (natp i) (< i 19))
      (let ((fn-zin-tab (fn-zin-tput (fn-zin-clorder-of i) 0 fn-zin-tab)))
        (fn-zin-zero-cl (1+ i) fn-zin-tab))
    fn-zin-tab))

(defthm fn-zin-zero-cl-keeps
  (implies (and (fn-cbor-octet-listp fn-zin-tab) (equal (len fn-zin-tab) *fn-zin-tab-octets*))
           (and (fn-cbor-octet-listp (fn-zin-zero-cl i fn-zin-tab))
                (equal (len (fn-zin-zero-cl i fn-zin-tab)) *fn-zin-tab-octets*))))

(defun fn-zin-fixed-tables (fn-zin-tab)
  ; RFC 1951 section 3.2.6: literal/length lengths 8 (0-143), 9 (144-255),
  ; 7 (256-279), 8 (280-287); 32 distance codes of length 5.
  (declare (xargs :stobjs fn-zin-tab :guard (fn-zin-tab-okp fn-zin-tab)))
  (let* ((fn-zin-tab (fn-zin-fill 0 144 8 fn-zin-tab))
         (fn-zin-tab (fn-zin-fill 144 112 9 fn-zin-tab))
         (fn-zin-tab (fn-zin-fill 256 24 7 fn-zin-tab))
         (fn-zin-tab (fn-zin-fill 280 8 8 fn-zin-tab))
         (fn-zin-tab (fn-zin-fill 288 32 5 fn-zin-tab)))
    (mv-let (left fn-zin-tab) (fn-zin-construct 0 0 288 fn-zin-tab)
      (declare (ignore left))
      (mv-let (left fn-zin-tab) (fn-zin-construct 1 288 32 fn-zin-tab)
        (declare (ignore left))
        fn-zin-tab))))

(defthm fn-zin-fixed-tables-keeps
  (implies (and (fn-cbor-octet-listp fn-zin-tab) (equal (len fn-zin-tab) *fn-zin-tab-octets*))
           (and (fn-cbor-octet-listp (fn-zin-fixed-tables fn-zin-tab))
                (equal (len (fn-zin-fixed-tables fn-zin-tab)) *fn-zin-tab-octets*))))

(in-theory (disable fn-zin-fill fn-zin-zero-cl fn-zin-fixed-tables))

; A dynamic block's two tables, once its code lengths are read (puff's
; `dynamic' after the lengths).  An incomplete code is allowed only when it
; is a single code (count[0] + count[1] = n).  (mv refusal fn-zin-tab).
(defun fn-zin-dynamic-tables (hlit hdist fn-zin-tab)
  (declare (xargs :stobjs fn-zin-tab
                  :guard (and (natp hlit) (natp hdist) (fn-zin-tab-okp fn-zin-tab))))
  (let ((hlit (min (nfix hlit) 286)) (hdist (min (nfix hdist) 30)))
    (if (eql (fn-zin-tget 256 fn-zin-tab) 0)
        (mv :no-end-code fn-zin-tab)
      (mv-let (left fn-zin-tab) (fn-zin-construct 0 0 hlit fn-zin-tab)
        (if (and (not (eql left 0))
                 (or (< left 0)
                     (not (eql hlit (+ (fn-zin-tget 320 fn-zin-tab)
                                       (fn-zin-tget 321 fn-zin-tab))))))
            (mv :bad-literal-code fn-zin-tab)
          (mv-let (left fn-zin-tab) (fn-zin-construct 1 hlit hdist fn-zin-tab)
            (if (and (not (eql left 0))
                     (or (< left 0)
                         (not (eql hdist (+ (fn-zin-tget 624 fn-zin-tab)
                                            (fn-zin-tget 625 fn-zin-tab))))))
                (mv :bad-distance-code fn-zin-tab)
              (mv nil fn-zin-tab))))))))

(defthm fn-zin-dynamic-tables-keeps
  (implies (and (fn-cbor-octet-listp fn-zin-tab) (equal (len fn-zin-tab) *fn-zin-tab-octets*))
           (and (fn-cbor-octet-listp (mv-nth 1 (fn-zin-dynamic-tables hlit hdist fn-zin-tab)))
                (equal (len (mv-nth 1 (fn-zin-dynamic-tables hlit hdist fn-zin-tab)))
                       *fn-zin-tab-octets*))))

(in-theory (disable fn-zin-dynamic-tables))

; -----------------------------------------------------------------------------
; The bits the current mode needs before it can act.

(defun fn-zin-need (fn-zin-st)
  (declare (xargs :stobjs fn-zin-st :guard t))
  (let ((mode (fn-zin-mode fn-zin-st)))
    (case mode
      (0 3)
      (2 32)
      (3 (if (zp (fn-zin-n fn-zin-st)) 0 8))
      (4 14)
      (5 (if (< (fn-zin-idx fn-zin-st) (fn-zin-hclen fn-zin-st)) 3 0))
      (6 (if (< (fn-zin-idx fn-zin-st) (+ (fn-zin-hlit fn-zin-st) (fn-zin-hdist fn-zin-st))) 1 0))
      (7 (case (fn-zin-sym fn-zin-st) (16 2) (17 3) (otherwise 7)))
      (8 1)
      (9 (fn-zin-lext-of (fn-zin-sym fn-zin-st)))
      (10 1)
      (11 (fn-zin-dext-of (fn-zin-sym fn-zin-st)))
      (otherwise 0))))

(defthm fn-zin-need-bound
  (and (natp (fn-zin-need fn-zin-st)) (<= (fn-zin-need fn-zin-st) 32))
  :rule-classes ((:type-prescription :corollary (natp (fn-zin-need fn-zin-st)))
                 (:linear :corollary (<= (fn-zin-need fn-zin-st) 32))))

(in-theory (disable fn-zin-need))

(defun fn-zin-block-end (fn-zin-st)
  ; A block ended: the next header, or the end of the stream.
  (declare (xargs :stobjs fn-zin-st :guard t))
  (fn-zin-set 0 (if (eql (fn-zin-final fn-zin-st) 1) 13 0) fn-zin-st))

; -----------------------------------------------------------------------------
; One action of the machine, once the bits it needs are in hand:
; (mv STATUS ZS fn-zin-win fn-zin-tab fn-zin-out), STATUS nil or a refusal
; reason.  Emits at most one octet.

(defun fn-zin-go-bindings (sets)
  (declare (xargs :mode :program))
  (if (consp sets)
      (cons `(fn-zin-st (fn-zin-set ,(car (car sets)) ,(cadr (car sets)) fn-zin-st))
            (fn-zin-go-bindings (cdr sets)))
    nil))

(defmacro fn-zin-go (&rest sets)
  ; The next state, field writes in order, and no refusal.
  `(let* ,(fn-zin-go-bindings sets)
     (mv nil fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))

(defun fn-zin-act (fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
  (declare (xargs :stobjs (fn-zin-win fn-zin-tab fn-zin-out fn-zin-st)
                  :guard (and (fn-zin-window-ready-p fn-zin-win)
                              (fn-zin-tab-okp fn-zin-tab))))
  (case (fn-zin-mode fn-zin-st)
    (0 ; a block header
     (mv-let (h fn-zin-st) (fn-zin-take 3 fn-zin-st)
       (let ((fn-zin-st (fn-zin-set 12 (fn-zin-lowb h 1) fn-zin-st)))
         (case (fn-zin-highb h 1)
           (0 (fn-zin-go (0 1)))
           (1 (let* ((fn-zin-tab (fn-zin-fixed-tables fn-zin-tab))
                     (fn-zin-st (fn-zin-decode-reset fn-zin-st)))
                (fn-zin-go (0 8))))
           (2 (fn-zin-go (0 4)))
           (otherwise (mv :block-type fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))))
    (1 ; a stored block: to the octet boundary
     (mv-let (drop fn-zin-st) (fn-zin-take (fn-zin-lowb (fn-zin-nbits fn-zin-st) 3) fn-zin-st)
       (declare (ignore drop))
       (fn-zin-go (0 2))))
    (2 ; LEN and NLEN
     (mv-let (len fn-zin-st) (fn-zin-take 16 fn-zin-st)
       (mv-let (nlen fn-zin-st) (fn-zin-take 16 fn-zin-st)
         (if (eql (+ len nlen) 65535)
             (fn-zin-go (3 len) (0 3))
           (mv :stored-length fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))))
    (3 ; a stored block's octets
     (if (zp (fn-zin-n fn-zin-st))
         (let ((fn-zin-st (fn-zin-block-end fn-zin-st)))
           (mv nil fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
       (mv-let (o fn-zin-st) (fn-zin-take 8 fn-zin-st)
         (mv-let (why fn-zin-st fn-zin-win fn-zin-out) (fn-zin-emit o fn-zin-st fn-zin-win fn-zin-out)
           (if why
               (mv why fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
             (fn-zin-go (3 (1- (fn-zin-n fn-zin-st)))))))))
    (4 ; a dynamic block's header
     (mv-let (a fn-zin-st) (fn-zin-take 5 fn-zin-st)
       (mv-let (b fn-zin-st) (fn-zin-take 5 fn-zin-st)
         (mv-let (c fn-zin-st) (fn-zin-take 4 fn-zin-st)
           (if (or (< 29 a) (< 29 b))
               (mv :code-counts fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
             (fn-zin-go (14 (+ 257 a)) (15 (+ 1 b)) (16 (+ 4 c)) (17 0) (0 5)))))))
    (5 ; the code-length code lengths
     (let ((i (fn-zin-idx fn-zin-st)))
       (if (< i (fn-zin-hclen fn-zin-st))
           (mv-let (v fn-zin-st) (fn-zin-take 3 fn-zin-st)
             (let ((fn-zin-tab (fn-zin-tput (fn-zin-clorder-of i) v fn-zin-tab)))
               (fn-zin-go (17 (1+ i)))))
         (let ((fn-zin-tab (fn-zin-zero-cl i fn-zin-tab)))
           (mv-let (left fn-zin-tab) (fn-zin-construct 2 0 19 fn-zin-tab)
             (if (eql left 0)
                 (let ((fn-zin-st (fn-zin-decode-reset fn-zin-st)))
                   (fn-zin-go (17 0) (0 6)))
               (mv :code-length-code fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))))))
    (6 ; the code lengths
     (let ((i (fn-zin-idx fn-zin-st))
           (total (+ (fn-zin-hlit fn-zin-st) (fn-zin-hdist fn-zin-st))))
       (if (< i total)
           (mv-let (kind sym fn-zin-st) (fn-zin-decode-bit 2 fn-zin-st fn-zin-tab)
             (cond ((eql kind 0) (mv nil fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
                   ((eql kind 2) (mv :bad-code fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
                   ((< sym 16)
                    (let ((fn-zin-tab (fn-zin-fill i 1 sym fn-zin-tab)))
                      (fn-zin-go (17 (1+ i)))))
                   ((and (eql sym 16) (eql i 0))
                    (mv :repeat-without-length fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
                   (t (fn-zin-go (13 sym) (0 7)))))
         (mv-let (why fn-zin-tab)
           (fn-zin-dynamic-tables (fn-zin-hlit fn-zin-st) (fn-zin-hdist fn-zin-st) fn-zin-tab)
           (if why
               (mv why fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
             (let ((fn-zin-st (fn-zin-decode-reset fn-zin-st)))
               (fn-zin-go (0 8))))))))
    (7 ; a repeat code's extra bits
     (let* ((sym (fn-zin-sym fn-zin-st))
            (i (fn-zin-idx fn-zin-st))
            (total (+ (fn-zin-hlit fn-zin-st) (fn-zin-hdist fn-zin-st))))
       (mv-let (v fn-zin-st) (fn-zin-take (case sym (16 2) (17 3) (otherwise 7)) fn-zin-st)
         (let* ((rep (+ v (if (or (eql sym 16) (eql sym 17)) 3 11)))
                (val (if (and (eql sym 16) (posp i) (<= i 320))
                         (fn-zin-tget (1- i) fn-zin-tab)
                       0)))
           (if (< total (+ i rep))
               (mv :repeat-overflow fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
             (let ((fn-zin-tab (fn-zin-fill i rep val fn-zin-tab)))
               (fn-zin-go (17 (+ i rep)) (0 6))))))))
    (8 ; a literal/length symbol
     (mv-let (kind sym fn-zin-st) (fn-zin-decode-bit 0 fn-zin-st fn-zin-tab)
       (cond ((eql kind 0) (mv nil fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
             ((eql kind 2) (mv :bad-code fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
             ((< sym 256)
              (mv-let (why fn-zin-st fn-zin-win fn-zin-out)
                (fn-zin-emit sym fn-zin-st fn-zin-win fn-zin-out)
                (mv why fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
             ((eql sym 256)
              (let ((fn-zin-st (fn-zin-block-end fn-zin-st)))
                (mv nil fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
             ((< 285 sym) (mv :length-code fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
             (t (fn-zin-go (13 (- sym 257)) (0 9))))))
    (9 ; a length's extra bits
     (let ((s (fn-zin-sym fn-zin-st)))
       (mv-let (v fn-zin-st) (fn-zin-take (fn-zin-lext-of s) fn-zin-st)
         (fn-zin-go (3 (+ (fn-zin-lbase-of s) v)) (0 10)))))
    (10 ; a distance symbol
     (mv-let (kind sym fn-zin-st) (fn-zin-decode-bit 1 fn-zin-st fn-zin-tab)
       (cond ((eql kind 0) (mv nil fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
             ((eql kind 2) (mv :bad-code fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
             ((< 29 sym) (mv :distance-code fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
             (t (fn-zin-go (13 sym) (0 11))))))
    (11 ; a distance's extra bits
     (let ((s (fn-zin-sym fn-zin-st)))
       (mv-let (v fn-zin-st) (fn-zin-take (fn-zin-dext-of s) fn-zin-st)
         (let ((d (+ (fn-zin-dbase-of s) v)))
           (if (< (min (+ (fn-zin-tout fn-zin-st) (fn-zin-preset fn-zin-st)) *fn-zin-window*) d)
               (mv :distance-too-far fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
             (fn-zin-go (4 d) (0 12)))))))
    (12 ; a match: N octets from DIST back
     (if (zp (fn-zin-n fn-zin-st))
         (let ((fn-zin-st (fn-zin-decode-reset fn-zin-st)))
           (fn-zin-go (0 8)))
       (mv-let (why fn-zin-st fn-zin-win fn-zin-out)
         (fn-zin-emit (fn-zin-back fn-zin-st fn-zin-win) fn-zin-st fn-zin-win fn-zin-out)
         (if why
             (mv why fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
           (fn-zin-go (3 (1- (fn-zin-n fn-zin-st))))))))
    (13 (mv :stream-ended fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
    (otherwise (mv :mode fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))

(defthm fn-zin-act-keeps
  (implies (and (fn-cbor-octet-listp fn-zin-win) (equal (len fn-zin-win) *fn-zin-win-octets*)
                (fn-cbor-octet-listp fn-zin-tab) (equal (len fn-zin-tab) *fn-zin-tab-octets*)
                (fn-cbor-octet-listp fn-zin-out))
           (let ((r (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
             (and (fn-cbor-octet-listp (mv-nth 2 r))
                  (equal (len (mv-nth 2 r)) *fn-zin-win-octets*)
                  (fn-cbor-octet-listp (mv-nth 3 r))
                  (equal (len (mv-nth 3 r)) *fn-zin-tab-octets*)
                  (fn-cbor-octet-listp (mv-nth 4 r))))))

; The output of one action: extended by at most one octet.
(local
 (defthm fn-zin-take-of-append-own
   (implies (true-listp x)
            (equal (take (len x) (append x y)) x))))

(local
 (defthm fn-zin-len-of-append
   (equal (len (append x y)) (+ (len x) (len y)))))

(local
 (defthm fn-zin-take-own-len
   (implies (true-listp x)
            (equal (take (len x) x) x))))

(defthm fn-zin-act-out-extends
  (implies (true-listp fn-zin-out)
           (let ((out2 (mv-nth 4 (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
             (and (true-listp out2)
                  (<= (len fn-zin-out) (len out2))
                  (<= (len out2) (1+ (len fn-zin-out)))
                  (equal (take (len fn-zin-out) out2) fn-zin-out))))
  :hints (("Goal" :do-not-induct t))
  :rule-classes
  ((:rewrite :corollary
    (implies (true-listp fn-zin-out)
             (and (true-listp (mv-nth 4 (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
                  (equal (take (len fn-zin-out)
                               (mv-nth 4 (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
                         fn-zin-out))))
   (:linear :corollary
    (implies (true-listp fn-zin-out)
             (and (<= (len fn-zin-out)
                      (len (mv-nth 4 (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
                  (<= (len (mv-nth 4 (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
                      (1+ (len fn-zin-out))))))))

(in-theory (disable fn-zin-act))

; -----------------------------------------------------------------------------
; A match copied in one action: up to ROOM octets (what the call may still
; append), within the bomb bound, from DIST back in the window.  What K
; single-octet actions of mode 12 would do, in a tight loop over locals.

(defun fn-zin-copy (k w d tout h fn-zin-win fn-zin-out)
  ; K octets from D back, the ring's next cell W, TOUT produced so far, the
  ; preset holding H: (mv W2 fn-zin-win fn-zin-out).
  (declare (xargs :stobjs (fn-zin-win fn-zin-out)
                  :guard (and (natp k) (natp w) (natp d) (natp tout) (natp h)
                              (fn-zin-window-ready-p fn-zin-win))
                  :measure (nfix k)))
  (if (zp k)
      (mv (fn-zin-wrap w) fn-zin-win fn-zin-out)
    (let* ((w (fn-zin-wrap w))
           (o (fn-zin-source d tout h w fn-zin-win))
           (fn-zin-out (fn-zin-out-append-octet o fn-zin-out))
           (fn-zin-win (fn-zin-win-put w o fn-zin-win)))
      (fn-zin-copy (1- k) (fn-zin-wrap (1+ w)) d (1+ (nfix tout)) h fn-zin-win fn-zin-out))))

(defthm fn-zin-copy-keeps
  (implies (and (fn-cbor-octet-listp fn-zin-win) (equal (len fn-zin-win) *fn-zin-win-octets*)
                (fn-cbor-octet-listp fn-zin-out))
           (let ((r (fn-zin-copy k w d tout h fn-zin-win fn-zin-out)))
             (and (fn-cbor-octet-listp (mv-nth 1 r))
                  (equal (len (mv-nth 1 r)) *fn-zin-win-octets*)
                  (fn-cbor-octet-listp (mv-nth 2 r))))))

(local
 (defthm fn-zin-append-assoc-copy
   (equal (append (append a b) c) (append a (append b c)))))

(local
 (defthm fn-zin-true-listp-append-one
   (implies (true-listp b) (true-listp (append b (list o))))))

(local
 (defthm fn-zin-copy-out-prefix
   (implies (and (true-listp a) (true-listp b))
            (equal (fn-zin-copy k w d tout h fn-zin-win (append a b))
                   (let ((r (fn-zin-copy k w d tout h fn-zin-win b)))
                     (mv (car r) (mv-nth 1 r) (append a (mv-nth 2 r))))))
   :hints (("Goal" :induct (fn-zin-copy k w d tout h fn-zin-win b)
            :expand ((fn-zin-copy k w d tout h fn-zin-win (append a b)))
            :in-theory (enable fn-oct-snoc-is-append)))))

(defthm fn-zin-copy-out-free
  (implies (and (syntaxp (not (equal fn-zin-out ''nil))) (true-listp fn-zin-out))
           (equal (fn-zin-copy k w d tout h fn-zin-win fn-zin-out)
                  (let ((r (fn-zin-copy k w d tout h fn-zin-win nil)))
                    (mv (car r) (mv-nth 1 r) (append fn-zin-out (mv-nth 2 r))))))
  :hints (("Goal" :use ((:instance fn-zin-copy-out-prefix (a fn-zin-out) (b nil)))
           :in-theory (disable fn-zin-copy-out-prefix))))

(defthm fn-zin-copy-out-len
  (and (true-listp (mv-nth 2 (fn-zin-copy k w d tout h fn-zin-win nil)))
       (equal (len (mv-nth 2 (fn-zin-copy k w d tout h fn-zin-win nil))) (nfix k)))
  :hints (("Goal" :induct (fn-zin-copy k w d tout h fn-zin-win nil)
           :in-theory (enable fn-oct-snoc-is-append))))

(defthm fn-zin-copy-len
  (equal (len (mv-nth 2 (fn-zin-copy k w d tout h fn-zin-win fn-zin-out)))
         (+ (len fn-zin-out) (nfix k)))
  :hints (("Goal" :induct (fn-zin-copy k w d tout h fn-zin-win fn-zin-out))))

(defthm fn-zin-copy-wpos
  (natp (car (fn-zin-copy k w d tout h fn-zin-win fn-zin-out)))
  :rule-classes :type-prescription)

(in-theory (disable fn-zin-copy))

(defun fn-zin-match (room fn-zin-st fn-zin-win fn-zin-out)
  ; Mode 12 with N > 0: (mv REFUSAL fn-zin-st win out).
  (declare (xargs :stobjs (fn-zin-st fn-zin-win fn-zin-out)
                  :guard (and (natp room) (fn-zin-window-ready-p fn-zin-win))))
  (let* ((n (fn-zin-n fn-zin-st))
         (allow (- (fn-zin-bomb-limit fn-zin-st) (fn-zin-tout fn-zin-st)))
         (k (min n (min (nfix room) (nfix allow)))))
    (if (zp k)
        (mv :bomb fn-zin-st fn-zin-win fn-zin-out)
      (mv-let (w2 fn-zin-win fn-zin-out)
        (fn-zin-copy k (fn-zin-wpos fn-zin-st) (fn-zin-dist fn-zin-st) (fn-zin-tout fn-zin-st)
                     (fn-zin-preset fn-zin-st) fn-zin-win fn-zin-out)
        (let* ((fn-zin-st (fn-zin-set 5 w2 fn-zin-st))
               (fn-zin-st (fn-zin-set 6 (+ k (fn-zin-tout fn-zin-st)) fn-zin-st))
               (fn-zin-st (fn-zin-set 3 (- n k) fn-zin-st)))
          (mv nil fn-zin-st fn-zin-win fn-zin-out))))))

(defthm fn-zin-match-keeps
  (implies (and (fn-cbor-octet-listp fn-zin-win) (equal (len fn-zin-win) *fn-zin-win-octets*)
                (fn-cbor-octet-listp fn-zin-out))
           (let ((r (fn-zin-match room fn-zin-st fn-zin-win fn-zin-out)))
             (and (fn-cbor-octet-listp (mv-nth 2 r))
                  (equal (len (mv-nth 2 r)) *fn-zin-win-octets*)
                  (fn-cbor-octet-listp (mv-nth 3 r))))))

(defthm fn-zin-match-out-free
  (implies (and (syntaxp (not (equal fn-zin-out ''nil))) (true-listp fn-zin-out))
           (equal (fn-zin-match room fn-zin-st fn-zin-win fn-zin-out)
                  (let ((r (fn-zin-match room fn-zin-st fn-zin-win nil)))
                    (mv (car r) (mv-nth 1 r) (mv-nth 2 r)
                        (append fn-zin-out (mv-nth 3 r)))))))

(defthm fn-zin-match-out-len
  (and (true-listp (mv-nth 3 (fn-zin-match room fn-zin-st fn-zin-win nil)))
       (<= (len (mv-nth 3 (fn-zin-match room fn-zin-st fn-zin-win nil))) (nfix room)))
  :rule-classes ((:rewrite :corollary
                  (true-listp (mv-nth 3 (fn-zin-match room fn-zin-st fn-zin-win nil))))
                 (:linear :corollary
                  (<= (len (mv-nth 3 (fn-zin-match room fn-zin-st fn-zin-win nil))) (nfix room)))))

(defthm fn-zin-match-counts
  (let ((r (fn-zin-match room fn-zin-st fn-zin-win fn-zin-out)))
    (and (equal (fn-zin-fld 7 (mv-nth 1 r)) (fn-zin-fld 7 fn-zin-st))
         (equal (fn-zin-fld 6 (mv-nth 1 r))
                (+ (fn-zin-fld 6 fn-zin-st) (- (len (mv-nth 3 r)) (len fn-zin-out))))
         (implies (<= (fn-zin-fld 6 fn-zin-st) (+ (* 256 (fn-zin-fld 7 fn-zin-st)) 65536))
                  (<= (fn-zin-fld 6 (mv-nth 1 r))
                      (+ (* 256 (fn-zin-fld 7 (mv-nth 1 r))) 65536))))))

(in-theory (disable fn-zin-match))

;; -----------------------------------------------------------------------------
; A run of literals in one action (mode 8, no decode in progress): each one
; a whole code of at most 9 bits in hand, read through the lookup, emitted
; within ROOM and the bomb bound.  What that many single actions of mode 8
; (the lookup's arm of fn-zin-decode-bit, then fn-zin-emit) would do, in
; locals; it stops at the first symbol that is not such a literal and
; leaves it to the machine.

(defun fn-zin-lit-loop (k bits nbits w tout limit fn-zin-tab fn-zin-win fn-zin-out)
  ; (mv BITS NBITS W TOUT fn-zin-win fn-zin-out).
  (declare (xargs :stobjs (fn-zin-tab fn-zin-win fn-zin-out)
                  :guard (and (natp k) (natp bits) (natp nbits) (natp w) (natp tout)
                              (natp limit) (fn-zin-tab-okp fn-zin-tab)
                              (fn-zin-window-ready-p fn-zin-win))
                  :measure (nfix k)))
  (if (zp k)
      (mv bits nbits w tout fn-zin-win fn-zin-out)
    (let* ((e (fn-zin-tget (+ 723 (fn-zin-lowb bits 9)) fn-zin-tab))
           (l (fn-zin-highb e 9))
           (sym (fn-zin-lowb e 9)))
      (if (and (<= 1 l) (<= l 9) (<= l (nfix nbits)) (< sym 256) (< (nfix tout) (nfix limit)))
          (let* ((w (fn-zin-wrap w))
                 (fn-zin-out (fn-zin-out-append-octet sym fn-zin-out))
                 (fn-zin-win (fn-zin-win-put w sym fn-zin-win)))
            (fn-zin-lit-loop (1- k) (fn-zin-highb bits l) (- (nfix nbits) l)
                             (fn-zin-wrap (1+ w)) (1+ (nfix tout)) limit
                             fn-zin-tab fn-zin-win fn-zin-out))
        (mv bits nbits w tout fn-zin-win fn-zin-out)))))

(defthm fn-zin-lit-loop-keeps
  (implies (and (fn-cbor-octet-listp fn-zin-win) (equal (len fn-zin-win) *fn-zin-win-octets*)
                (fn-cbor-octet-listp fn-zin-out))
           (let ((r (fn-zin-lit-loop k bits nbits w tout limit fn-zin-tab fn-zin-win fn-zin-out)))
             (and (fn-cbor-octet-listp (mv-nth 4 r))
                  (equal (len (mv-nth 4 r)) *fn-zin-win-octets*)
                  (fn-cbor-octet-listp (mv-nth 5 r))))))

(defthm fn-zin-lit-loop-counts
  (implies (and (natp tout) (natp nbits))
           (let ((r (fn-zin-lit-loop k bits nbits w tout limit fn-zin-tab fn-zin-win fn-zin-out)))
             (and (natp (mv-nth 3 r))
                  (natp (mv-nth 1 r))
                  (equal (len (mv-nth 5 r)) (+ (len fn-zin-out) (- (mv-nth 3 r) tout)))
                  (<= tout (mv-nth 3 r))
                  (<= (- (mv-nth 3 r) tout) (nfix k))
                  (implies (<= tout (nfix limit))
                           (<= (mv-nth 3 r) (nfix limit))))))
  :hints (("Goal" :induct (fn-zin-lit-loop k bits nbits w tout limit fn-zin-tab fn-zin-win fn-zin-out))))

(local
 (defthm fn-zin-lit-loop-out-prefix
   (implies (and (true-listp a) (true-listp b))
            (equal (fn-zin-lit-loop k bits nbits w tout limit fn-zin-tab fn-zin-win (append a b))
                   (let ((r (fn-zin-lit-loop k bits nbits w tout limit fn-zin-tab fn-zin-win b)))
                     (mv (car r) (mv-nth 1 r) (mv-nth 2 r) (mv-nth 3 r) (mv-nth 4 r)
                         (append a (mv-nth 5 r))))))
   :hints (("Goal" :induct (fn-zin-lit-loop k bits nbits w tout limit fn-zin-tab fn-zin-win b)
            :expand ((fn-zin-lit-loop k bits nbits w tout limit fn-zin-tab fn-zin-win (append a b)))
            :in-theory (enable fn-oct-snoc-is-append)))))

(defthm fn-zin-lit-loop-out-free
  (implies (and (syntaxp (not (equal fn-zin-out ''nil))) (true-listp fn-zin-out))
           (equal (fn-zin-lit-loop k bits nbits w tout limit fn-zin-tab fn-zin-win fn-zin-out)
                  (let ((r (fn-zin-lit-loop k bits nbits w tout limit fn-zin-tab fn-zin-win nil)))
                    (mv (car r) (mv-nth 1 r) (mv-nth 2 r) (mv-nth 3 r) (mv-nth 4 r)
                        (append fn-zin-out (mv-nth 5 r))))))
  :hints (("Goal" :use ((:instance fn-zin-lit-loop-out-prefix (a fn-zin-out) (b nil)))
           :in-theory (disable fn-zin-lit-loop-out-prefix))))

(defthm fn-zin-lit-loop-out-shape
  (implies (true-listp fn-zin-out)
           (let ((out2 (mv-nth 5 (fn-zin-lit-loop k bits nbits w tout limit fn-zin-tab fn-zin-win
                                                  fn-zin-out))))
             (and (true-listp out2)
                  (equal (take (len fn-zin-out) out2) fn-zin-out))))
  :hints (("Goal" :induct (fn-zin-lit-loop k bits nbits w tout limit fn-zin-tab fn-zin-win fn-zin-out)
           :in-theory (enable fn-oct-snoc-is-append))))

(in-theory (disable fn-zin-lit-loop))

(defun fn-zin-freshp (fn-zin-st)
  ; No Huffman decode in progress.
  (declare (xargs :stobjs fn-zin-st))
  (and (eql (fn-zin-dlen fn-zin-st) 1) (eql (fn-zin-dcode fn-zin-st) 0)
       (eql (fn-zin-dfirst fn-zin-st) 0) (eql (fn-zin-dindex fn-zin-st) 0)))

(defun fn-zin-lit-ready-p (fn-zin-st fn-zin-tab)
  ; The next symbol is a literal the lookup decodes from the bits in hand,
  ; within the bomb bound: the literal run takes at least that one.
  (declare (xargs :stobjs (fn-zin-st fn-zin-tab) :guard (fn-zin-tab-okp fn-zin-tab)))
  (let* ((e (fn-zin-tget (+ 723 (fn-zin-lowb (fn-zin-bits fn-zin-st) 9)) fn-zin-tab))
         (l (fn-zin-highb e 9)))
    (and (<= 1 l) (<= l 9) (<= l (fn-zin-nbits fn-zin-st))
         (< (fn-zin-lowb e 9) 256)
         (< (fn-zin-tout fn-zin-st) (fn-zin-bomb-limit fn-zin-st)))))

(defun fn-zin-lits (room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
  ; (mv EMITTED fn-zin-st fn-zin-win fn-zin-out).
  (declare (xargs :stobjs (fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                  :guard (and (natp room) (fn-zin-window-ready-p fn-zin-win)
                              (fn-zin-tab-okp fn-zin-tab))))
  (let ((tout (fn-zin-tout fn-zin-st)))
    (mv-let (bits nbits w tout2 fn-zin-win fn-zin-out)
      (fn-zin-lit-loop room (fn-zin-bits fn-zin-st) (fn-zin-nbits fn-zin-st)
                       (fn-zin-wpos fn-zin-st) tout (fn-zin-bomb-limit fn-zin-st)
                       fn-zin-tab fn-zin-win fn-zin-out)
      (let* ((fn-zin-st (fn-zin-set 1 bits fn-zin-st))
             (fn-zin-st (fn-zin-set 2 nbits fn-zin-st))
             (fn-zin-st (fn-zin-set 5 w fn-zin-st))
             (fn-zin-st (fn-zin-set 6 tout2 fn-zin-st)))
        (mv (- tout2 tout) fn-zin-st fn-zin-win fn-zin-out)))))

(defthm fn-zin-lits-keeps
  (implies (and (fn-cbor-octet-listp fn-zin-win) (equal (len fn-zin-win) *fn-zin-win-octets*)
                (fn-cbor-octet-listp fn-zin-out))
           (let ((r (fn-zin-lits room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
             (and (fn-cbor-octet-listp (mv-nth 2 r))
                  (equal (len (mv-nth 2 r)) *fn-zin-win-octets*)
                  (fn-cbor-octet-listp (mv-nth 3 r))))))

(defthm fn-zin-lits-natp
  (natp (car (fn-zin-lits room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (disable fn-zin-lit-loop-counts)
           :use ((:instance fn-zin-lit-loop-counts
                            (k room) (bits (fn-zin-fld 1 fn-zin-st))
                            (nbits (fn-zin-fld 2 fn-zin-st))
                            (w (fn-zin-fld 5 fn-zin-st))
                            (tout (fn-zin-fld 6 fn-zin-st))
                            (limit (fn-zin-bomb-limit fn-zin-st)))))))

(defthm fn-zin-lits-out
  (let ((r (fn-zin-lits room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
    (and (natp (car r))
         (equal (len (mv-nth 3 r)) (+ (len fn-zin-out) (car r)))
         (<= (car r) (nfix room))
         (implies (true-listp fn-zin-out)
                  (and (true-listp (mv-nth 3 r))
                       (equal (take (len fn-zin-out) (mv-nth 3 r)) fn-zin-out)))))
  :hints (("Goal" :in-theory (disable fn-zin-lit-loop-counts)
           :use ((:instance fn-zin-lit-loop-counts
                            (k room) (bits (fn-zin-fld 1 fn-zin-st))
                            (nbits (fn-zin-fld 2 fn-zin-st))
                            (w (fn-zin-fld 5 fn-zin-st))
                            (tout (fn-zin-fld 6 fn-zin-st))
                            (limit (fn-zin-bomb-limit fn-zin-st)))))))

(defthm fn-zin-lits-room
  (<= (car (fn-zin-lits room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)) (nfix room))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-zin-lits-out)) :in-theory (disable fn-zin-lits-out))))

(defthm fn-zin-lits-counts
  (let ((r (fn-zin-lits room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
    (and (equal (fn-zin-fld 7 (mv-nth 1 r)) (fn-zin-fld 7 fn-zin-st))
         (equal (fn-zin-fld 6 (mv-nth 1 r)) (+ (fn-zin-fld 6 fn-zin-st) (car r)))
         (implies (<= (fn-zin-fld 6 fn-zin-st) (+ (* 256 (fn-zin-fld 7 fn-zin-st)) 65536))
                  (<= (fn-zin-fld 6 (mv-nth 1 r))
                      (+ (* 256 (fn-zin-fld 7 (mv-nth 1 r))) 65536)))))
  :hints (("Goal" :in-theory (disable fn-zin-lit-loop-counts)
           :use ((:instance fn-zin-lit-loop-counts
                            (k room) (bits (fn-zin-fld 1 fn-zin-st))
                            (nbits (fn-zin-fld 2 fn-zin-st))
                            (w (fn-zin-fld 5 fn-zin-st))
                            (tout (fn-zin-fld 6 fn-zin-st))
                            (limit (fn-zin-bomb-limit fn-zin-st)))))))

(defthm fn-zin-lits-out-free
  (implies (and (syntaxp (not (equal fn-zin-out ''nil))) (true-listp fn-zin-out))
           (equal (fn-zin-lits room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                  (let ((r (fn-zin-lits room fn-zin-st fn-zin-win fn-zin-tab nil)))
                    (mv (car r) (mv-nth 1 r) (mv-nth 2 r)
                        (append fn-zin-out (mv-nth 3 r)))))))

(in-theory (disable fn-zin-lits fn-zin-freshp fn-zin-lit-ready-p))

; One action: a match's octets in bulk (up to ROOM), or the machine's one
; step.
(defun fn-zin-step (room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
  (declare (xargs :stobjs (fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                  :guard (and (natp room) (fn-zin-window-ready-p fn-zin-win)
                              (fn-zin-tab-okp fn-zin-tab))))
  (cond ((and (eql (fn-zin-mode fn-zin-st) 12) (posp (fn-zin-n fn-zin-st)))
         (mv-let (why fn-zin-st fn-zin-win fn-zin-out)
           (fn-zin-match room fn-zin-st fn-zin-win fn-zin-out)
           (mv why fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
        ((and (eql (fn-zin-mode fn-zin-st) 8) (fn-zin-freshp fn-zin-st) (posp room)
              (fn-zin-lit-ready-p fn-zin-st fn-zin-tab))
         (mv-let (k fn-zin-st fn-zin-win fn-zin-out)
           (fn-zin-lits room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
           (declare (ignore k))
           (mv nil fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
        (t (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))

(defthm fn-zin-step-keeps
  (implies (and (fn-cbor-octet-listp fn-zin-win) (equal (len fn-zin-win) *fn-zin-win-octets*)
                (fn-cbor-octet-listp fn-zin-tab) (equal (len fn-zin-tab) *fn-zin-tab-octets*)
                (fn-cbor-octet-listp fn-zin-out))
           (let ((r (fn-zin-step room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
             (and (fn-cbor-octet-listp (mv-nth 2 r))
                  (equal (len (mv-nth 2 r)) *fn-zin-win-octets*)
                  (fn-cbor-octet-listp (mv-nth 3 r))
                  (equal (len (mv-nth 3 r)) *fn-zin-tab-octets*)
                  (fn-cbor-octet-listp (mv-nth 4 r))))))

(local
 (defthm fn-zin-take-of-append-step
   (implies (true-listp x)
            (equal (take (len x) (append x y)) x))))

(local
 (defthm fn-zin-len-of-append-step
   (equal (len (append x y)) (+ (len x) (len y)))))

(local
 (defthm fn-zin-true-listp-of-append-step
   (implies (true-listp b) (true-listp (append a b)))))

(defthm fn-zin-step-out-extends
  (implies (true-listp fn-zin-out)
           (let ((out2 (mv-nth 4 (fn-zin-step room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
             (and (true-listp out2)
                  (<= (len fn-zin-out) (len out2))
                  (<= (len out2) (+ (len fn-zin-out) (max 1 (nfix room))))
                  (equal (take (len fn-zin-out) out2) fn-zin-out))))
  :hints (("Goal" :do-not-induct t :in-theory (enable fn-zin-step)))
  :rule-classes
  ((:rewrite :corollary
    (implies (true-listp fn-zin-out)
             (and (true-listp (mv-nth 4 (fn-zin-step room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
                  (equal (take (len fn-zin-out)
                               (mv-nth 4 (fn-zin-step room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
                         fn-zin-out))))
   (:linear :corollary
    (implies (true-listp fn-zin-out)
             (<= (len fn-zin-out)
                 (len (mv-nth 4 (fn-zin-step room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))))
   (:linear :corollary
    (implies (and (true-listp fn-zin-out) (integerp room) (< 0 room))
             (<= (len (mv-nth 4 (fn-zin-step room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
                 (+ (len fn-zin-out) room))))))

(in-theory (disable fn-zin-step))

; -----------------------------------------------------------------------------
; The loop.  One iteration is one action: take an input octet into the bit
; buffer when the mode needs more bits than it holds, else act.  B counts
; iterations.  (mv STATUS B2 IP ZS fn-zin-win fn-zin-tab fn-zin-out).

(defun fn-zin-pull (ip fn-zin-st fn-octets)
  (declare (xargs :stobjs (fn-octets fn-zin-st)
                  :guard (and (natp ip) (< ip (fn-octets-len fn-octets)))))
  (let* ((o (fn-octets-get ip fn-octets))
         (fn-zin-st (fn-zin-set 1 (fn-zin-shift-in (fn-zin-bits fn-zin-st) (fn-zin-nbits fn-zin-st) o) fn-zin-st))
         (fn-zin-st (fn-zin-set 2 (+ 8 (fn-zin-nbits fn-zin-st)) fn-zin-st)))
    (fn-zin-set 7 (1+ (fn-zin-tin fn-zin-st)) fn-zin-st)))

(defun fn-zin-loop (b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
  (declare (xargs :stobjs (fn-octets fn-zin-win fn-zin-tab fn-zin-out fn-zin-st)
                  :guard (and (natp b) (natp ip) (natp end) (natp lim)
                              (<= end (fn-octets-len fn-octets))
                              (fn-zin-window-ready-p fn-zin-win)
                              (fn-zin-tab-okp fn-zin-tab))
                  :measure (nfix b)))
  (cond ((zp b) (mv :yield 0 ip fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
        ((<= (nfix lim) (fn-zin-out-len fn-zin-out))
         (mv :full b ip fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
        ((< (fn-zin-nbits fn-zin-st) (fn-zin-need fn-zin-st))
         (if (and (natp ip) (< ip (min (nfix end) (fn-octets-len fn-octets))))
             (let ((fn-zin-st (fn-zin-pull ip fn-zin-st fn-octets)))
               (fn-zin-loop (1- b) (1+ ip) end lim fn-zin-st
                            fn-octets fn-zin-win fn-zin-tab fn-zin-out))
           (mv :more b ip fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
        (t (mv-let (why fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
             (fn-zin-step (- (nfix lim) (fn-zin-out-len fn-zin-out))
                          fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
             (if why
                 (mv (list :refused why) (1- b) ip fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
               (fn-zin-loop (1- b) ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab
                            fn-zin-out))))))

(defthm fn-zin-loop-keeps
  (implies (and (fn-cbor-octet-listp fn-zin-win) (equal (len fn-zin-win) *fn-zin-win-octets*)
                (fn-cbor-octet-listp fn-zin-tab) (equal (len fn-zin-tab) *fn-zin-tab-octets*)
                (fn-cbor-octet-listp fn-zin-out))
           (let ((r (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
             (and (fn-cbor-octet-listp (mv-nth 4 r))
                  (equal (len (mv-nth 4 r)) *fn-zin-win-octets*)
                  (fn-cbor-octet-listp (mv-nth 5 r))
                  (equal (len (mv-nth 5 r)) *fn-zin-tab-octets*)
                  (fn-cbor-octet-listp (mv-nth 6 r))))))

;; -----------------------------------------------------------------------------
; The whole-payload loop (the store's decoder: a stored payload is decoded
; whole, never in reads the network cut).  The same actions as fn-zin-loop,
; but it takes input octets ahead while fewer than 24 bits are in hand, so a
; Huffman code is mostly read through the lookup in one action.  Its answer
; depends on where its input ends, which is why the COMPRESS wire uses
; fn-zin-loop (whose resumption keystones need no lookahead) and this loop
; decodes only a complete payload; the seal checks that this decoder gives
; the payload's octets before a payload is kept compressed.

(defun fn-zin-loop-ahead (b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
  (declare (xargs :stobjs (fn-octets fn-zin-win fn-zin-tab fn-zin-out fn-zin-st)
                  :guard (and (natp b) (natp ip) (natp end) (natp lim)
                              (<= end (fn-octets-len fn-octets))
                              (fn-zin-window-ready-p fn-zin-win)
                              (fn-zin-tab-okp fn-zin-tab))
                  :measure (nfix b)))
  (let ((avail (and (natp ip) (< ip (min (nfix end) (fn-octets-len fn-octets))))))
    (cond ((zp b) (mv :yield 0 ip fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
          ((<= (nfix lim) (fn-zin-out-len fn-zin-out))
           (mv :full b ip fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
          ((and avail (< (fn-zin-nbits fn-zin-st) 24))
           (let ((fn-zin-st (fn-zin-pull ip fn-zin-st fn-octets)))
             (fn-zin-loop-ahead (1- b) (1+ ip) end lim fn-zin-st
                                fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
          ((< (fn-zin-nbits fn-zin-st) (fn-zin-need fn-zin-st))
           (mv :more b ip fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
          (t (mv-let (why fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
               (fn-zin-step (- (nfix lim) (fn-zin-out-len fn-zin-out))
                            fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
               (if why
                   (mv (list :refused why) (1- b) ip fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                 (fn-zin-loop-ahead (1- b) ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab
                                    fn-zin-out)))))))

(defthm fn-zin-loop-ahead-keeps
  (implies (and (fn-cbor-octet-listp fn-zin-win) (equal (len fn-zin-win) *fn-zin-win-octets*)
                (fn-cbor-octet-listp fn-zin-tab) (equal (len fn-zin-tab) *fn-zin-tab-octets*)
                (fn-cbor-octet-listp fn-zin-out))
           (let ((r (fn-zin-loop-ahead b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab
                                       fn-zin-out)))
             (and (fn-cbor-octet-listp (mv-nth 4 r))
                  (equal (len (mv-nth 4 r)) *fn-zin-win-octets*)
                  (fn-cbor-octet-listp (mv-nth 5 r))
                  (equal (len (mv-nth 5 r)) *fn-zin-tab-octets*)
                  (fn-cbor-octet-listp (mv-nth 6 r))))))

; -----------------------------------------------------------------------------
; The buffers, once per connection, and the host entry.

(defun fn-zin-zeros (k fn-zin-win)
  (declare (xargs :stobjs fn-zin-win :guard (natp k) :measure (nfix k)))
  (if (zp k)
      fn-zin-win
    (let ((fn-zin-win (fn-zin-win-append-octet 0 fn-zin-win)))
      (fn-zin-zeros (1- k) fn-zin-win))))

(defun fn-zin-tab-zeros (k fn-zin-tab)
  (declare (xargs :stobjs fn-zin-tab :guard (natp k) :measure (nfix k)))
  (if (zp k)
      fn-zin-tab
    (let ((fn-zin-tab (fn-zin-tab-append-octet 0 fn-zin-tab)))
      (fn-zin-tab-zeros (1- k) fn-zin-tab))))

(defun fn-zin-buffers-ready (fn-zin-win fn-zin-tab)
  ; The window and the table at their fixed lengths, zeroed.
  (declare (xargs :stobjs (fn-zin-win fn-zin-tab)))
  (let* ((fn-zin-win (fn-zin-win-clear fn-zin-win))
         (fn-zin-win (fn-zin-win-reserve *fn-zin-win-octets* fn-zin-win))
         (fn-zin-win (fn-zin-zeros *fn-zin-win-octets* fn-zin-win))
         (fn-zin-tab (fn-zin-tab-clear fn-zin-tab))
         (fn-zin-tab (fn-zin-tab-reserve *fn-zin-tab-octets* fn-zin-tab))
         (fn-zin-tab (fn-zin-tab-zeros *fn-zin-tab-octets* fn-zin-tab)))
    (mv fn-zin-win fn-zin-tab)))

; A preset dictionary (RFC 1950 section 2.2 FDICT; the stored payloads'
; shipped dictionary, the COMPRESS extension's negotiated one): its last
; 32 KiB into the window's upper half, its length into field 18.  Once per
; decoder; fn-zin-reset keeps it.

(defun fn-zin-put-preset (i xs fn-zin-win)
  (declare (xargs :stobjs fn-zin-win
                  :guard (and (natp i) (fn-cbor-octet-listp xs)
                              (fn-zin-window-ready-p fn-zin-win))
                  :measure (len xs)))
  (if (and (consp xs) (natp i) (< i *fn-zin-window*))
      (let ((fn-zin-win (fn-zin-win-put (+ *fn-zin-window* i) (car xs) fn-zin-win)))
        (fn-zin-put-preset (1+ i) (cdr xs) fn-zin-win))
    fn-zin-win))

(defthm fn-zin-put-preset-keeps
  (implies (and (fn-cbor-octet-listp fn-zin-win) (equal (len fn-zin-win) *fn-zin-win-octets*)
                (fn-cbor-octet-listp xs))
           (and (fn-cbor-octet-listp (fn-zin-put-preset i xs fn-zin-win))
                (equal (len (fn-zin-put-preset i xs fn-zin-win)) *fn-zin-win-octets*))))

(defun fn-zin-load-preset (dict fn-zin-st fn-zin-win)
  ; (mv fn-zin-st fn-zin-win).
  (declare (xargs :stobjs (fn-zin-st fn-zin-win)
                  :guard (and (fn-cbor-octet-listp dict) (fn-zin-window-ready-p fn-zin-win))))
  (let* ((n (len dict))
         (tail (if (< *fn-zin-window* n) (nthcdr (- n *fn-zin-window*) dict) dict))
         (fn-zin-win (fn-zin-put-preset 0 tail fn-zin-win))
         (fn-zin-st (fn-zin-set 18 (len tail) fn-zin-st)))
    (mv fn-zin-st fn-zin-win)))

(defun fn-zin-feed (b fn-zin-st start end lim fn-octets fn-zin-win fn-zin-tab fn-zin-out)
  ; THE HOST ENTRY (host/native/mux.lisp, the COMPRESS DEFLATE layer).
  (declare (xargs :stobjs (fn-octets fn-zin-win fn-zin-tab fn-zin-out fn-zin-st)
                  :guard (and (natp b) (natp start) (natp end) (natp lim)
                              (<= end (fn-octets-len fn-octets)))))
  (if (and (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab))
      (fn-zin-loop b start end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
    (mv (list :refused :buffers) b start fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))

; The host entry is the loop once the buffers are ready: the resumption
; keystones below are stated over the loop and hold of the entry by this.
(defthm fn-zin-feed-unfolds
  (implies (and (equal (len fn-zin-win) *fn-zin-win-octets*)
                (equal (len fn-zin-tab) *fn-zin-tab-octets*))
           (equal (fn-zin-feed b fn-zin-st start end lim fn-octets fn-zin-win fn-zin-tab
                               fn-zin-out)
                  (fn-zin-loop b start end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab
                               fn-zin-out))))

(defun fn-zin-refusal-text (why)
  ; The service log's line for a refused stream (the connection closes;
  ; RFC 8054 section 2.2.2 sends nothing more).
  (declare (xargs :guard t))
  (case why
    (:bomb "compress-bomb: the DEFLATE stream expands past the ratio bound (256 x input + 64 KiB)")
    (:stream-ended "compress-ended: the client's DEFLATE stream ended (a final block); the layer never ends")
    (:block-type "compress-malformed: DEFLATE block type 3")
    (:stored-length "compress-malformed: a stored block's LEN and NLEN disagree")
    (:code-counts "compress-malformed: more than 286 literal/length or 30 distance codes")
    (:code-length-code "compress-malformed: the code-length code is not complete")
    (:repeat-without-length "compress-malformed: a repeat code before any code length")
    (:repeat-overflow "compress-malformed: a repeat runs past the code lengths")
    (:no-end-code "compress-malformed: no end-of-block code")
    (:bad-literal-code "compress-malformed: the literal/length code is over-subscribed or incomplete")
    (:bad-distance-code "compress-malformed: the distance code is over-subscribed or incomplete")
    (:bad-code "compress-malformed: a bit sequence matches no code")
    (:length-code "compress-malformed: literal/length code 286 or 287")
    (:distance-code "compress-malformed: distance code 30 or 31")
    (:distance-too-far "compress-malformed: a distance reaches before the stream's first octet")
    (:buffers "compress-fault: the inflater's buffers are not ready")
    (otherwise "compress-malformed: the DEFLATE stream is refused")))

; -----------------------------------------------------------------------------
; Over octet lists, on local buffers: the stream C from the initial state,
; with budget B and output bound LIM.  (list STATUS OUT ZS).  The witnesses
; and the reachability keystone read the machine through this.

(defun fn-zin-fields-list (i fn-zin-st)
  ; The scalar state, as a list (for the witnesses).
  (declare (xargs :stobjs fn-zin-st :guard (natp i) :measure (nfix (- 20 (nfix i)))))
  (if (and (natp i) (< i 20))
      (cons (fn-zin-fld i fn-zin-st) (fn-zin-fields-list (1+ i) fn-zin-st))
    nil))

(defun fn-zin-inflate-bufs (b dict fn-zin-st c lim fn-octets fn-zin-win fn-zin-tab fn-zin-out)
  (declare (xargs :stobjs (fn-octets fn-zin-win fn-zin-tab fn-zin-out fn-zin-st)
                  :guard (and (natp b) (natp lim) (fn-cbor-octet-listp c)
                              (fn-cbor-octet-listp dict))))
  (let* ((fn-octets (fn-octets-from-list c fn-octets))
         (fn-zin-out (fn-zin-out-clear fn-zin-out)))
    (mv-let (fn-zin-win fn-zin-tab) (fn-zin-buffers-ready fn-zin-win fn-zin-tab)
     (mv-let (fn-zin-st fn-zin-win) (fn-zin-load-preset dict fn-zin-st fn-zin-win)
      (mv-let (st b2 ip fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
        (fn-zin-feed b fn-zin-st 0 (fn-octets-len fn-octets) lim fn-octets fn-zin-win fn-zin-tab
                     fn-zin-out)
        (declare (ignore b2 ip))
        (mv (list st (fn-zin-out-list fn-zin-out) (fn-zin-fields-list 0 fn-zin-st))
            fn-octets fn-zin-win fn-zin-tab fn-zin-out fn-zin-st))))))

(defun fn-zin-inflate-with (b dict c lim)
  ; The stream C from the initial state over the preset DICT.
  (declare (xargs :guard (and (natp b) (natp lim) (fn-cbor-octet-listp c)
                              (fn-cbor-octet-listp dict))))
  (with-local-stobj fn-octets
    (mv-let (r fn-octets)
      (with-local-stobj fn-zin-win
        (mv-let (r fn-zin-win fn-octets)
          (with-local-stobj fn-zin-tab
            (mv-let (r fn-zin-tab fn-zin-win fn-octets)
              (with-local-stobj fn-zin-out
                (mv-let (r fn-zin-out fn-zin-tab fn-zin-win fn-octets)
                  (mv-let (r fn-octets fn-zin-win fn-zin-tab fn-zin-out)
                    (with-local-stobj fn-zin-st
                      (mv-let (r fn-octets fn-zin-win fn-zin-tab fn-zin-out fn-zin-st)
                        (let ((fn-zin-st (fn-zin-reset fn-zin-st)))
                          (fn-zin-inflate-bufs b dict fn-zin-st c lim fn-octets fn-zin-win
                                               fn-zin-tab fn-zin-out))
                        (mv r fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
                    (mv r fn-zin-out fn-zin-tab fn-zin-win fn-octets))
                  (mv r fn-zin-tab fn-zin-win fn-octets)))
              (mv r fn-zin-win fn-octets)))
          (mv r fn-octets)))
      r)))

(defun fn-zin-inflate (b c lim)
  (declare (xargs :guard (and (natp b) (natp lim) (fn-cbor-octet-listp c))))
  (fn-zin-inflate-with b nil c lim))

; -----------------------------------------------------------------------------
; KEYSTONE (the bomb, PRF-910).  The octets a call appends to the output
; are exactly what it adds to TOTAL-OUT, the octets it reads exactly what
; it adds to TOTAL-IN; and TOTAL-OUT <= R * TOTAL-IN + S holds after every
; call that started with it (`fn-zin-reset' does).

(defun fn-zin-bomb-okp (fn-zin-st)
  (declare (xargs :stobjs fn-zin-st :guard t))
  (<= (fn-zin-tout fn-zin-st) (fn-zin-bomb-limit fn-zin-st)))

(local
 (defthm fn-zin-reset-loop-below
   (implies (and (natp i) (natp j) (< j i))
            (equal (fn-zin-fld j (fn-zin-reset-loop i fn-zin-st)) (fn-zin-fld j fn-zin-st)))
   :hints (("Goal" :induct (fn-zin-reset-loop i fn-zin-st)))))

(local
 (defthm fn-zin-reset-loop-fields
   (implies (and (natp i) (natp j) (<= i j) (< j 18))
            (equal (fn-zin-fld j (fn-zin-reset-loop i fn-zin-st)) 0))
   :hints (("Goal" :induct (fn-zin-reset-loop i fn-zin-st)))))

(defthm fn-zin-reset-okp
  (fn-zin-bomb-okp (fn-zin-reset fn-zin-st)))

(local
 (defthm fn-zin-take-keeps-counts
   (and (equal (fn-zin-fld 6 (mv-nth 1 (fn-zin-take n fn-zin-st))) (fn-zin-fld 6 fn-zin-st))
        (equal (fn-zin-fld 7 (mv-nth 1 (fn-zin-take n fn-zin-st))) (fn-zin-fld 7 fn-zin-st))
        )
   :hints (("Goal" :in-theory (enable fn-zin-take)))))

(local
 (defthm fn-zin-decode-bit-keeps-counts
   (and (equal (fn-zin-fld 6 (mv-nth 2 (fn-zin-decode-bit tb fn-zin-st fn-zin-tab))) (fn-zin-fld 6 fn-zin-st))
        (equal (fn-zin-fld 7 (mv-nth 2 (fn-zin-decode-bit tb fn-zin-st fn-zin-tab))) (fn-zin-fld 7 fn-zin-st)))
   :hints (("Goal" :in-theory (enable fn-zin-decode-bit)))))

(local
 (defthm fn-zin-emit-refusal
   (equal (car (fn-zin-emit o fn-zin-st fn-zin-win fn-zin-out))
          (if (< (+ (* 256 (fn-zin-fld 7 fn-zin-st)) 65536) (1+ (fn-zin-fld 6 fn-zin-st))) :bomb nil))
   :hints (("Goal" :in-theory (enable fn-zin-emit)))))

(local
 (defthm fn-zin-emit-counts
   (let ((r (fn-zin-emit o fn-zin-st fn-zin-win fn-zin-out)))
     (and (equal (fn-zin-fld 7 (mv-nth 1 r)) (fn-zin-fld 7 fn-zin-st))
          (equal (fn-zin-fld 6 (mv-nth 1 r))
                 (if (car r) (fn-zin-fld 6 fn-zin-st) (1+ (fn-zin-fld 6 fn-zin-st))))
          (implies (not (car r))
                   (<= (1+ (fn-zin-fld 6 fn-zin-st))
                       (+ (* 256 (fn-zin-fld 7 fn-zin-st)) 65536)))))
   :hints (("Goal" :in-theory (enable fn-zin-emit)))))

(defthm fn-zin-act-counts
  (let ((r (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
             (and (equal (fn-zin-fld 7 (mv-nth 1 r)) (fn-zin-fld 7 fn-zin-st))
                  (equal (fn-zin-fld 6 (mv-nth 1 r))
                         (+ (fn-zin-fld 6 fn-zin-st)
                            (- (len (mv-nth 4 r)) (len fn-zin-out))))
                  (implies (fn-zin-bomb-okp fn-zin-st) (fn-zin-bomb-okp (mv-nth 1 r)))))
  :hints (("Goal" :in-theory (enable fn-zin-act) :do-not-induct t)))

(defthm fn-zin-match-bomb-okp
  (implies (fn-zin-bomb-okp fn-zin-st)
           (fn-zin-bomb-okp (mv-nth 1 (fn-zin-match room fn-zin-st fn-zin-win fn-zin-out))))
  :hints (("Goal" :use ((:instance fn-zin-match-counts))
           :in-theory (disable fn-zin-match-counts))))

(defthm fn-zin-lits-bomb-okp
  (implies (fn-zin-bomb-okp fn-zin-st)
           (fn-zin-bomb-okp (mv-nth 1 (fn-zin-lits room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
  :hints (("Goal" :use ((:instance fn-zin-lits-counts))
           :in-theory (disable fn-zin-lits-counts))))

(defthm fn-zin-step-counts
  (let ((r (fn-zin-step room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
    (and (equal (fn-zin-fld 7 (mv-nth 1 r)) (fn-zin-fld 7 fn-zin-st))
         (equal (fn-zin-fld 6 (mv-nth 1 r))
                (+ (fn-zin-fld 6 fn-zin-st)
                   (- (len (mv-nth 4 r)) (len fn-zin-out))))
         (implies (fn-zin-bomb-okp fn-zin-st) (fn-zin-bomb-okp (mv-nth 1 r)))))
  :hints (("Goal" :in-theory (e/d (fn-zin-step) (fn-zin-act fn-zin-match-out-free
                                                  fn-zin-bomb-okp)))))

(local
 (defthm fn-zin-pull-counts
   (let ((zs2 (fn-zin-pull ip fn-zin-st fn-octets)))
     (and (equal (fn-zin-fld 7 zs2) (1+ (fn-zin-fld 7 fn-zin-st)))
          (equal (fn-zin-fld 6 zs2) (fn-zin-fld 6 fn-zin-st))))))

(local
 (defthm fn-zin-pull-bomb-okp
   (implies (fn-zin-bomb-okp fn-zin-st)
            (fn-zin-bomb-okp (fn-zin-pull ip fn-zin-st fn-octets)))
   :hints (("Goal" :in-theory (disable fn-zin-pull)))))

(local (in-theory (disable fn-zin-pull fn-zin-need)))

(defthm fn-zin-loop-counts
  (let ((r (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
    (and (implies (natp ip)
                  (and (natp (mv-nth 2 r))
                       (<= ip (mv-nth 2 r))))
         (equal (fn-zin-fld 7 (mv-nth 3 r))
                (+ (fn-zin-fld 7 fn-zin-st) (- (mv-nth 2 r) ip)))
         (equal (fn-zin-fld 6 (mv-nth 3 r))
                (+ (fn-zin-fld 6 fn-zin-st) (- (len (mv-nth 6 r)) (len fn-zin-out))))
         (implies (fn-zin-bomb-okp fn-zin-st) (fn-zin-bomb-okp (mv-nth 3 r)))))
  :hints (("Goal" :induct (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
           :in-theory (disable fn-zin-bomb-okp))))

; KEYSTONE (PRF-910): the bomb bound at the host entry.  From a well-shaped
; state within the bound, a call stays within it, and the bound is about
; the real output: the octets appended are what TOTAL-OUT counts, the
; octets read what TOTAL-IN counts.
(defthm fn-zin-feed-bomb-bound
  (implies (fn-zin-bomb-okp fn-zin-st)
           (let ((r (fn-zin-feed b fn-zin-st start end lim fn-octets fn-zin-win fn-zin-tab
                                 fn-zin-out)))
             (and (fn-zin-bomb-okp (mv-nth 3 r))
                  (<= (fn-zin-fld 6 (mv-nth 3 r))
                      (+ (* *fn-zin-ratio* (fn-zin-fld 7 (mv-nth 3 r))) *fn-zin-slack*))
                  (equal (- (len (mv-nth 6 r)) (len fn-zin-out))
                         (- (fn-zin-fld 6 (mv-nth 3 r)) (fn-zin-fld 6 fn-zin-st)))
                  (equal (- (mv-nth 2 r) start)
                         (- (fn-zin-fld 7 (mv-nth 3 r)) (fn-zin-fld 7 fn-zin-st))))))
  :hints (("Goal" :in-theory (disable fn-zin-loop-counts)
           :use ((:instance fn-zin-loop-counts (ip start))))))

; -----------------------------------------------------------------------------
; KEYSTONE (PRF-909): the output bound.  A call never grows the output past
; LIM (or its starting length, if that was already past), and only appends.

(local
 (defun fn-zin-ind3 (a b c)
   (if (consp a) (fn-zin-ind3 (cdr a) (cdr b) (cdr c)) (list b c))))

(local
 (defthm fn-zin-prefix-trans
   (implies (and (equal (take (len b) c) b) (equal (take (len a) b) a)
                 (<= (len a) (len b)) (<= (len b) (len c)))
            (equal (take (len a) c) a))
   :hints (("Goal" :in-theory (enable take) :induct (fn-zin-ind3 a b c)))))

(local
 (defthm fn-zin-loop-out-extends
   (implies (true-listp fn-zin-out)
            (let ((out2 (mv-nth 6 (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab
                                               fn-zin-out))))
              (and (true-listp out2)
                   (<= (len out2) (max (nfix lim) (len fn-zin-out)))
                   (<= (len fn-zin-out) (len out2))
                   (equal (take (len fn-zin-out) out2) fn-zin-out))))
   :hints (("Goal" :induct (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab
                                        fn-zin-out)))
   :rule-classes
   ((:rewrite :corollary
     (implies (true-listp fn-zin-out)
              (let ((out2 (mv-nth 6 (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab
                                                 fn-zin-out))))
                (and (true-listp out2)
                     (equal (take (len fn-zin-out) out2) fn-zin-out)))))
    (:linear :corollary
     (implies (true-listp fn-zin-out)
              (let ((out2 (mv-nth 6 (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab
                                                 fn-zin-out))))
                (and (<= (len out2) (max (nfix lim) (len fn-zin-out)))
                     (<= (len fn-zin-out) (len out2)))))))))

; KEYSTONE: the host entry appends at most LIM octets in all (the output
; starts cleared per call on the host) and keeps what it had.
(defthm fn-zin-feed-out-bound
  (implies (true-listp fn-zin-out)
           (let ((out2 (mv-nth 6 (fn-zin-feed b fn-zin-st start end lim fn-octets fn-zin-win fn-zin-tab
                                              fn-zin-out))))
             (and (true-listp out2)
                  (<= (len out2) (max (nfix lim) (len fn-zin-out)))
                  (<= (len fn-zin-out) (len out2))
                  (equal (take (len fn-zin-out) out2) fn-zin-out))))
  :hints (("Goal" :in-theory (disable fn-zin-loop))))

; The stop statuses mean what they say.  :more: every input octet up to
; END was taken; :full: the output reached LIM.
(defthm fn-zin-loop-stops
  (let ((r (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
    (and (implies (and (equal (car r) :more) (natp ip))
                  (<= (min (nfix end) (len fn-octets)) (nfix (mv-nth 2 r))))
         (implies (equal (car r) :full)
                  (<= (nfix lim) (len (mv-nth 6 r))))
         (implies (equal (car r) :yield)
                  (equal (mv-nth 1 r) 0))))
  :hints (("Goal" :induct (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab
                                       fn-zin-out))))

; -----------------------------------------------------------------------------
; KEYSTONES (PRF-909): resumption.  The network cuts the stream anywhere and
; the host's quantum ends anywhere; the machine does not notice.

; A call whose budget ran out (:yield), resumed with more budget, is the
; call that had both budgets.
(defthm fn-zin-loop-split-budget
  (implies (and (natp b1) (natp b2)
                (equal (car (fn-zin-loop b1 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab
                                         fn-zin-out))
                       :yield))
           (equal (fn-zin-loop (+ b1 b2) ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
                  (let ((r (fn-zin-loop b1 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab
                                        fn-zin-out)))
                    (fn-zin-loop b2 (mv-nth 2 r) end lim (mv-nth 3 r) fn-octets
                                 (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r)))))
  :hints (("Goal" :induct (fn-zin-loop b1 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab
                                       fn-zin-out))))

; A call that took every octet up to M (:more), resumed on input up to a
; later END, is the call that saw input up to END at once.
(defthm fn-zin-loop-split-input
  (implies (and (<= (nfix m) (nfix end))
                (equal (car (fn-zin-loop b ip m lim fn-zin-st fn-octets fn-zin-win fn-zin-tab
                                         fn-zin-out))
                       :more))
           (equal (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
                  (let ((r (fn-zin-loop b ip m lim fn-zin-st fn-octets fn-zin-win fn-zin-tab
                                        fn-zin-out)))
                    (fn-zin-loop (mv-nth 1 r) (mv-nth 2 r) end lim (mv-nth 3 r) fn-octets
                                 (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r)))))
  :hints (("Goal" :induct (fn-zin-loop b ip m lim fn-zin-st fn-octets fn-zin-win fn-zin-tab
                                       fn-zin-out))))

; The output buffer is written, never read: a call over output O is the
; call over an empty output, appended to O, with LIM moved by |O|.  With
; the two splits above, a call stopped by LIM (:full) and resumed on a
; cleared output is the call that had both allowances.
(local
 (defthm fn-zin-emit-out-free
   (implies (and (syntaxp (not (equal fn-zin-out ''nil))) (true-listp fn-zin-out))
            (equal (fn-zin-emit o fn-zin-st fn-zin-win fn-zin-out)
                   (let ((r (fn-zin-emit o fn-zin-st fn-zin-win nil)))
                     (mv (car r) (mv-nth 1 r) (mv-nth 2 r)
                         (append fn-zin-out (mv-nth 3 r))))))
   :hints (("Goal" :in-theory (enable fn-zin-emit)))))

(local
 (defthm fn-zin-act-out-free
   (implies (and (syntaxp (not (equal fn-zin-out ''nil))) (true-listp fn-zin-out))
            (equal (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                   (let ((r (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab nil)))
                     (mv (car r) (mv-nth 1 r) (mv-nth 2 r) (mv-nth 3 r)
                         (append fn-zin-out (mv-nth 4 r))))))
   :hints (("Goal" :in-theory (e/d (fn-zin-act) (fn-zin-emit-out fn-zin-emit-refusal))
            :do-not-induct t))))

(local
 (defthm fn-zin-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(local
 (defthm fn-zin-cancel-inner
   (equal (+ y (- y) z) (fix z))))

(defthm fn-zin-step-out-free
  (implies (and (syntaxp (not (equal fn-zin-out ''nil))) (true-listp fn-zin-out))
           (equal (fn-zin-step room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                  (let ((r (fn-zin-step room fn-zin-st fn-zin-win fn-zin-tab nil)))
                    (mv (car r) (mv-nth 1 r) (mv-nth 2 r) (mv-nth 3 r)
                        (append fn-zin-out (mv-nth 4 r))))))
  :hints (("Goal" :in-theory (e/d (fn-zin-step) (fn-zin-act)))))

(local
 (defthm fn-zin-loop-out-prefix
   (implies (and (true-listp o) (true-listp p) (natp lim))
            (equal (fn-zin-loop b ip end (+ lim (len o)) fn-zin-st fn-octets fn-zin-win
                                fn-zin-tab (append o p))
                   (let ((r (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab p)))
                     (mv (car r) (mv-nth 1 r) (mv-nth 2 r) (mv-nth 3 r) (mv-nth 4 r)
                         (mv-nth 5 r) (append o (mv-nth 6 r))))))
   :hints (("Goal" :induct (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab p)
            :expand ((fn-zin-loop b ip end (+ lim (len o)) fn-zin-st fn-octets fn-zin-win
                                  fn-zin-tab (append o p)))))))

(defthm fn-zin-loop-out-free
  (implies (true-listp fn-zin-out)
           (equal (fn-zin-loop b ip end (+ (nfix lim) (len fn-zin-out)) fn-zin-st fn-octets fn-zin-win
                               fn-zin-tab fn-zin-out)
                  (let ((r (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)))
                    (mv (car r) (mv-nth 1 r) (mv-nth 2 r) (mv-nth 3 r) (mv-nth 4 r) (mv-nth 5 r)
                        (append fn-zin-out (mv-nth 6 r))))))
  :hints (("Goal" :use ((:instance fn-zin-loop-out-prefix (o fn-zin-out) (p nil)
                                    (lim (nfix lim))))
           :in-theory (disable fn-zin-loop-out-prefix))))

; -----------------------------------------------------------------------------
; The logical model over octet lists (the D27 boundary: the host calls the
; buffer entry, and this is the stream it means).  `fn-zin-run' decodes the
; list C from ZS.  KEYSTONE `fn-zin-loop-is-run': a call over any buffer
; cells [IP, END) is the run over exactly those octets (only the returned
; position is relative).  KEYSTONE `fn-zin-run-append': a run that took all
; of A (:more), resumed on B, is the run over A ++ B.  Together with the
; budget and output splits, any sequence of host calls over the reads the
; network delivered is one run over the concatenated stream.

(defun-nx fn-zin-run (b fn-zin-st c lim fn-zin-win fn-zin-tab fn-zin-out)
  (fn-zin-loop b 0 (len c) lim fn-zin-st c fn-zin-win fn-zin-tab fn-zin-out))

(local
 (defthm fn-zin-nth-of-take
   (implies (and (natp i) (natp n) (< i n))
            (equal (nth i (take n x)) (nth i x)))
   :hints (("Goal" :in-theory (enable nth take)))))

(local
 (defthm fn-zin-nth-of-nthcdr
   (implies (and (natp i) (natp k))
            (equal (nth i (nthcdr k x)) (nth (+ k i) x)))
   :hints (("Goal" :in-theory (enable nth nthcdr)))))

(local
 (defthm fn-zin-len-take
   (implies (natp n) (equal (len (take n x)) n))))

(local
 (defthm fn-zin-pull-reads-nth
   (equal (fn-zin-pull ip fn-zin-st fn-octets)
          (let* ((o (nth ip fn-octets))
                 (fn-zin-st (fn-zin-set 1 (fn-zin-shift-in (fn-zin-bits fn-zin-st) (fn-zin-nbits fn-zin-st) o) fn-zin-st))
                 (fn-zin-st (fn-zin-set 2 (+ 8 (fn-zin-nbits fn-zin-st)) fn-zin-st)))
            (fn-zin-set 7 (1+ (fn-zin-tin fn-zin-st)) fn-zin-st)))
   :hints (("Goal" :in-theory (enable fn-zin-pull)))))

(defthm fn-zin-loop-shift
  (implies (and (natp ip0) (natp ip) (<= ip0 ip) (natp end) (<= ip end) (<= end (len x)))
           (equal (fn-zin-loop b ip end lim fn-zin-st x fn-zin-win fn-zin-tab fn-zin-out)
                  (let ((r (fn-zin-loop b (- ip ip0) (- end ip0) lim fn-zin-st
                                        (take (- end ip0) (nthcdr ip0 x))
                                        fn-zin-win fn-zin-tab fn-zin-out)))
                    (mv (car r) (mv-nth 1 r) (+ ip0 (mv-nth 2 r)) (mv-nth 3 r) (mv-nth 4 r)
                        (mv-nth 5 r) (mv-nth 6 r)))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-zin-loop b ip end lim fn-zin-st x fn-zin-win fn-zin-tab fn-zin-out)
           :expand ((fn-zin-loop b (- ip ip0) (- end ip0) lim fn-zin-st
                                 (take (- end ip0) (nthcdr ip0 x))
                                 fn-zin-win fn-zin-tab fn-zin-out)))))

(defthm fn-zin-loop-is-run
  (implies (and (natp ip) (natp end) (<= ip end) (<= end (len x)))
           (equal (fn-zin-loop b ip end lim fn-zin-st x fn-zin-win fn-zin-tab fn-zin-out)
                  (let ((r (fn-zin-run b fn-zin-st (take (- end ip) (nthcdr ip x)) lim
                                       fn-zin-win fn-zin-tab fn-zin-out)))
                    (mv (car r) (mv-nth 1 r) (+ ip (mv-nth 2 r)) (mv-nth 3 r) (mv-nth 4 r)
                        (mv-nth 5 r) (mv-nth 6 r)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-zin-loop-shift (ip0 ip))))))

(local
 (defthm fn-zin-loop-ip-bound
   (implies (and (natp ip) (natp end) (<= ip end))
            (<= (mv-nth 2 (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
                end))
   :rule-classes :linear
   :hints (("Goal" :induct (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab
                                        fn-zin-out)))))

(local
 (defthm fn-zin-take-of-append-len
   (implies (true-listp a) (equal (take (len a) (append a c)) a))))

(local
 (defthm fn-zin-nthcdr-of-append-len
   (equal (nthcdr (len a) (append a c)) c)))

(local
 (defthm fn-zin-take-len-of-true-list
   (implies (true-listp c) (equal (take (len c) c) c))))

(local
 (defthm fn-zin-loop-ip-natp
   (implies (natp ip)
            (natp (mv-nth 2 (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab
                                         fn-zin-out))))
   :rule-classes :type-prescription
   :hints (("Goal" :induct (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab
                                        fn-zin-out)))))

(local
 (defthm fn-zin-loop-mv-shape
   (let ((r (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
     (equal (list (car r) (mv-nth 1 r) (mv-nth 2 r) (mv-nth 3 r) (mv-nth 4 r) (mv-nth 5 r)
                  (mv-nth 6 r))
            r))
   :hints (("Goal" :induct (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab
                                        fn-zin-out)))))

(local
 (defthm fn-zin-run-more-ip
   (implies (equal (car (fn-zin-loop b 0 (len a) lim fn-zin-st a fn-zin-win fn-zin-tab fn-zin-out))
                   :more)
            (equal (mv-nth 2 (fn-zin-loop b 0 (len a) lim fn-zin-st a fn-zin-win fn-zin-tab fn-zin-out))
                   (len a)))
   :hints (("Goal" :in-theory (disable fn-zin-loop fn-zin-loop-stops)
            :use ((:instance fn-zin-loop-stops (ip 0) (end (len a)) (fn-octets a)))))))

(local
 (defthm fn-zin-loop-prefix-of-append
   (implies (true-listp a)
            (equal (fn-zin-loop b 0 (len a) lim fn-zin-st (append a c) fn-zin-win fn-zin-tab fn-zin-out)
                   (fn-zin-run b fn-zin-st a lim fn-zin-win fn-zin-tab fn-zin-out)))
   :hints (("Goal" :in-theory (e/d (fn-zin-run) (fn-zin-loop))
            :do-not-induct t
            :use ((:instance fn-zin-loop-shift (ip0 0) (ip 0) (end (len a)) (x (append a c))))))))

(local
 (defthm fn-zin-plus-cancel
   (implies (acl2-numberp y) (equal (+ x (- x) y) y))))

(local
 (defthm fn-zin-loop-suffix-of-append
   (implies (true-listp c)
            (equal (fn-zin-loop b (len a) (+ (len a) (len c)) lim fn-zin-st (append a c)
                                fn-zin-win fn-zin-tab fn-zin-out)
                   (let ((r (fn-zin-run b fn-zin-st c lim fn-zin-win fn-zin-tab fn-zin-out)))
                     (mv (car r) (mv-nth 1 r) (+ (len a) (mv-nth 2 r)) (mv-nth 3 r) (mv-nth 4 r)
                         (mv-nth 5 r) (mv-nth 6 r)))))
   :hints (("Goal" :in-theory (e/d (fn-zin-run) (fn-zin-loop))
            :do-not-induct t
            :use ((:instance fn-zin-loop-shift (ip0 (len a)) (ip (len a))
                             (end (+ (len a) (len c))) (x (append a c))))))))

(defthm fn-zin-run-append
  (implies (and (true-listp a) (true-listp c)
                (equal (car (fn-zin-run bud fn-zin-st a lim fn-zin-win fn-zin-tab fn-zin-out)) :more))
           (let* ((r1 (fn-zin-run bud fn-zin-st a lim fn-zin-win fn-zin-tab fn-zin-out))
                  (r2 (fn-zin-run (mv-nth 1 r1) (mv-nth 3 r1) c lim
                                  (mv-nth 4 r1) (mv-nth 5 r1) (mv-nth 6 r1))))
             (equal (fn-zin-run bud fn-zin-st (append a c) lim fn-zin-win fn-zin-tab fn-zin-out)
                    (mv (car r2) (mv-nth 1 r2) (+ (len a) (mv-nth 2 r2)) (mv-nth 3 r2)
                        (mv-nth 4 r2) (mv-nth 5 r2) (mv-nth 6 r2)))))
  :hints (("Goal" :in-theory (e/d (fn-zin-run) (fn-zin-loop-split-input fn-zin-loop))
           :do-not-induct t
           :use ((:instance fn-zin-loop-split-input
                            (b bud) (ip 0) (m (len a)) (end (+ (len a) (len c)))
                            (fn-octets (append a c)))))))
