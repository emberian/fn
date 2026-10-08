; fn: the payload extent cache's decisions (lane s-extent-cache, Deputy S,
; planning: build/coordinator/STORAGE-PROGRAM-20261006.md section 1.5).
;
; Before this book the realizer (host/native/extent.lisp) decided its own
; cache: an alist searched by `find-if', moved to the front by `delete' and
; `cons', cut by `subseq' at the capacity, and the oldest `last'-ed off under
; pool pressure; the verified-window cache was a second list with the same
; moves.  Here every one of those decisions is ACL2's.  The host keeps, per
; slot number, the octet vector (and, for a window, its plan and buffer): the
; things ACL2 cannot hold.  It asks this book which slot holds a descriptor,
; which slot a new entry takes, which entry yields under pressure and which
; entries a retiring file takes with it, and it does exactly that.
;
; The table.  A fixed number of slots, NE for whole extent entries then NW
; for verified windows (both read from the profile, books/profile-limits.lisp
; row :extent-cache-entries, through `fn-arx-read-cache-entries'; 0 under the
; developer cache-off arm), one generated row per slot
; (books/def-representation.lisp, ruling 1: no hand stobj):
;
;   kind    0 free, 1 whole entry, 2 raw window, 3 decoded window
;   tokp    the entry holds a pool charge (a :cached ledger row); an entry
;           read in the offline context holds none
;   tid tcid  the token's read identity and connection (tcid is 0 for a window)
;   file eoff elen a b c d start trailer
;           the descriptor.  A whole entry: (file eoff elen trailer), a b c d
;           and start 0.  A raw window: a = poff, b = plen.  A decoded
;           window: a = poff, b = compressed, c = decoded, d = dictionary id.
;           START is the window's first payload offset.  The trailer is the
;           32-octet frame digest packed as a natural by fn-bch-pack (the
;           descriptor's trailer, fn-arx-trailer-nat): 256^32 plus the octets,
;           so up to 2^257-1, a 257-bit column.
;   stamp   the slot's recency: the value of the clock cell at its last
;           install or touch.  The clock (cell 0 of the second instance,
;           with NE and NW in cells 1 and 2) advances on every use, so the
;           stamps of the live slots are distinct and least-recently-used is
;           the live slot of least stamp.
;
; The policy is exact LRU, which is what the host's alist computed by
; move-to-front, now with a bound that is structural: the table has NE + NW
; rows and never gains one, so occupancy cannot exceed the profile's number.
; A hash index was not built: the scan is over NE <= 8 rows (profile row), a
; compare of at most ten columns each, under the same lock the host's find-if
; ran under.  If the profile row ever grows into the hundreds the index is a
; keyed instance of def-representation, and the statements below do not change.
;
; STATED INVARIANT (no pin column).  A cached row in the page-read ledger has
; no reader pin.  Every borrow of a slot's vector runs under the host's extent
; lock (*fnn-extent-lock*) from lookup to the last octet copied, and install,
; yield and free run under the same lock: that is why an install cannot evict
; a slot in use.  The host marks the borrow site with a comment naming this.
;
; :PRESENT AND THE CHARGE.  fn-xc-install answers :present (and keeps the old
; slot) when a concurrent cold read of the same descriptor already installed
; it; the host (fnn-extent-cache-store, host/native/extent.lisp) then returns the
; NEW read's own token in the list of charges to release.  That cannot be :stale
; or a double release: a token's ledger row is :issued until settlement and
; :cached after it (fn-prl-settle, page-read-ledger.lisp:154-174, with CACHEDP
; true), and fn-prl-evict (:178-191) accepts exactly a :cached row and removes it,
; so each token is released once.  The funded async path stores (owner.lisp:6025,
; the row still :issued), commits with CACHEDP true (:6148, which makes it
; :cached) and releases EVICTED last (:6153); the synchronous path settles
; with CACHEDP (fnn-extent-entry-direct) before releasing, and cannot reach
; :present at all, since it holds the extent lock from its miss to its install.
; The window path caches the row (fn-pwc-cache) before inserting.  The slot's
; own token is never released by :present: its slot is unchanged.
;
; The clock saturates at 2^64-1 (a slot's stamp is a u64 column).  A
; saturated clock leaves ties, which the victim choice breaks by position:
; recency order is then approximate, every other statement is unaffected.
; 2^64 cache uses is not a reachable count.

(in-package "ACL2")
(include-book "def-representation")
(include-book "page-read-ledger")
(include-book "profile-limits") ; the cache figures are rows there
(include-book "packed-octets")  ; the trailer column holds fn-bch-pack of 32 octets
(include-book "frame-octets")   ; *fn-frame-trailer-octets*

(local (in-theory (enable adt-val-okp)))

; The row: kind tokp tid tcid file eoff elen a b c d start trailer stamp.
(def-representation fn-xcs
  (kind (:nat 3)) (tokp :bool) (tid :u64) (tcid :u64)
  (file :u64) (eoff :u64) (elen :u64) (a :u64) (b :u64) (c :u64) (d :u64)
  (start :u64)
  (trailer (:nat 231584178474632390847141970017375815706539969331281128078915168015826259279871))
  (stamp :u64))

; Cells: 0 the clock, 1 NE (whole-entry slots), 2 NW (window slots).
(def-representation fn-xcc (cell :u64) :scalar t)

(defconst *fn-xc-trailer-max*
  231584178474632390847141970017375815706539969331281128078915168015826259279871)

; The column holds every descriptor trailer: fn-arx-trailer-nat is fn-bch-pack
; of the 32 trailer octets (books/payload-extent.lisp), which carries a sentinel
; digit above them, so it exceeds 2^256.  The first native run refused every
; window because this bound was 2^256-1.
(local
 (defthm fn-xc-bch-pack-bound
   (implies (fn-bch-octetsp xs)
            (<= (fn-bch-pack xs) (- (* 2 (expt 256 (len xs))) 1)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-bch-pack fn-bch-byte fn-bch-octetp)))))

(defthm fn-xc-trailer-column-holds-the-frame-trailer-commitment
  (implies (and (fn-bch-octetsp xs) (equal (len xs) *fn-frame-trailer-octets*))
           (and (natp (fn-bch-pack xs))
                (<= (fn-bch-pack xs) *fn-xc-trailer-max*)))
  :rule-classes nil
  :hints (("Goal" :use fn-xc-bch-pack-bound)))

(defconst *fn-xc-u64-max* (1- (expt 2 64)))

; A free row: kind 0, every other column zero.
(defconst *fn-xc-free-row* '(0 nil 0 0 0 0 0 0 0 0 0 0 0 0))

; --- typed reads.  The rows are the generated instance's; these say what a
; read of a well-formed table is.
(local
 (defthm fn-xc-u64-seq-nth
   (implies (and (adt-scalar-seq-p '(:u64) a) (natp i) (< i (len a)))
            (unsigned-byte-p 64 (nth i a)))
   :hints (("Goal" :in-theory (enable adt-scalar-seq-p adt-val-okp nth)
                   :induct (nth i a)))
   :rule-classes nil))

;;
(defthm fn-xcc-get-is-u64
  (implies (and (fn-xccp fn-xcc) (natp i) (< i (fn-xcc-count fn-xcc)))
           (unsigned-byte-p 64 (fn-xcc-get i fn-xcc)))
  :hints (("Goal" :in-theory (enable fn-xccp-is-scalar-seq-p fn-xcc-get-is-nth fn-xcc-count-is-len)
                  :use ((:instance fn-xc-u64-seq-nth (a fn-xcc))))))

(defthm fn-xcc-get-is-natp
  (implies (and (fn-xccp fn-xcc) (natp i) (< i (fn-xcc-count fn-xcc)))
           (natp (fn-xcc-get i fn-xcc)))
  :rule-classes :type-prescription
  :hints (("Goal" :use fn-xcc-get-is-u64 :in-theory (e/d () (fn-xcc-get-is-u64)))))

(local
 (defthm fn-xc-row-typed
   (implies (and (fn-xcsp fn-xcs) (natp i) (< i (fn-xcs-count fn-xcs)))
            (let ((r (nth i fn-xcs)))
              (and (member-equal (nth 0 r) '(0 1 2 3))
                   (booleanp (nth 1 r))
                   (unsigned-byte-p 64 (nth 2 r)) (unsigned-byte-p 64 (nth 3 r))
                   (unsigned-byte-p 64 (nth 4 r)) (unsigned-byte-p 64 (nth 5 r))
                   (unsigned-byte-p 64 (nth 6 r)) (unsigned-byte-p 64 (nth 7 r))
                   (unsigned-byte-p 64 (nth 8 r)) (unsigned-byte-p 64 (nth 9 r))
                   (unsigned-byte-p 64 (nth 10 r)) (unsigned-byte-p 64 (nth 11 r))
                   (natp (nth 12 r))
                   (<= (nth 12 r) *fn-xc-trailer-max*)
                   (unsigned-byte-p 64 (nth 13 r)))))
   :hints (("Goal" :in-theory (enable fn-xcsp-is-seq-p fn-xcs-count-is-len)
                   :use ((:instance adt-rec-p-of-nth (s *fn-xcs-schema*) (a fn-xcs)))))
   :rule-classes nil))

(defthm fn-xcs-get-kind-is-kind
  (implies (and (fn-xcsp fn-xcs) (natp i) (< i (fn-xcs-count fn-xcs)))
           (member-equal (fn-xcs-get-kind i fn-xcs) '(0 1 2 3)))
  :hints (("Goal" :in-theory (enable fn-xcs-get-kind-is-nth fn-xcs-count-is-len)
                  :use fn-xc-row-typed)))

(defthm fn-xcs-get-start-is-u64
  (implies (and (fn-xcsp fn-xcs) (natp i) (< i (fn-xcs-count fn-xcs)))
           (unsigned-byte-p 64 (fn-xcs-get-start i fn-xcs)))
  :hints (("Goal" :in-theory (enable fn-xcs-get-start-is-nth fn-xcs-count-is-len)
                  :use fn-xc-row-typed)))

(defthm fn-xcs-get-start-is-natp
  (implies (and (fn-xcsp fn-xcs) (natp i) (< i (fn-xcs-count fn-xcs)))
           (natp (fn-xcs-get-start i fn-xcs)))
  :rule-classes :type-prescription
  :hints (("Goal" :use fn-xcs-get-start-is-u64 :in-theory (e/d () (fn-xcs-get-start-is-u64)))))

(defthm fn-xcs-get-stamp-is-u64
  (implies (and (fn-xcsp fn-xcs) (natp i) (< i (fn-xcs-count fn-xcs)))
           (unsigned-byte-p 64 (fn-xcs-get-stamp i fn-xcs)))
  :hints (("Goal" :in-theory (enable fn-xcs-get-stamp-is-nth fn-xcs-count-is-len)
                  :use fn-xc-row-typed)))

(defthm fn-xcs-get-stamp-is-natp
  (implies (and (fn-xcsp fn-xcs) (natp i) (< i (fn-xcs-count fn-xcs)))
           (natp (fn-xcs-get-stamp i fn-xcs)))
  :rule-classes :type-prescription
  :hints (("Goal" :use fn-xcs-get-stamp-is-u64 :in-theory (e/d () (fn-xcs-get-stamp-is-u64)))))

; The generated -is- meanings stay disabled here: the decisions are stated and
; proved over the exports; a proof enables the meanings it needs.
(in-theory (disable fn-xcs-count fn-xcsp fn-xcs-append fn-xcc-count fn-xccp fn-xcc-get fn-xcc-set fn-xcc-append fn-xcs-get-kind fn-xcs-set-kind fn-xcs-get-tokp fn-xcs-set-tokp fn-xcs-get-tid fn-xcs-set-tid fn-xcs-get-tcid fn-xcs-set-tcid fn-xcs-get-file fn-xcs-set-file fn-xcs-get-eoff fn-xcs-set-eoff fn-xcs-get-elen fn-xcs-set-elen fn-xcs-get-a fn-xcs-set-a fn-xcs-get-b fn-xcs-set-b fn-xcs-get-c fn-xcs-set-c fn-xcs-get-d fn-xcs-set-d fn-xcs-get-start fn-xcs-set-start fn-xcs-get-trailer fn-xcs-set-trailer fn-xcs-get-stamp fn-xcs-set-stamp fn-xcs-count-is-len fn-xcsp-is-seq-p fn-xcs-append-is-append fn-xcs-clear-is-nil fn-xcs-reserve-is-identity fn-xcs-get-kind-is-nth fn-xcs-set-kind-is-update-nth fn-xcs-get-tokp-is-nth fn-xcs-set-tokp-is-update-nth fn-xcs-get-tid-is-nth fn-xcs-set-tid-is-update-nth fn-xcs-get-tcid-is-nth fn-xcs-set-tcid-is-update-nth fn-xcs-get-file-is-nth fn-xcs-set-file-is-update-nth fn-xcs-get-eoff-is-nth fn-xcs-set-eoff-is-update-nth fn-xcs-get-elen-is-nth fn-xcs-set-elen-is-update-nth fn-xcs-get-a-is-nth fn-xcs-set-a-is-update-nth fn-xcs-get-b-is-nth fn-xcs-set-b-is-update-nth fn-xcs-get-c-is-nth fn-xcs-set-c-is-update-nth fn-xcs-get-d-is-nth fn-xcs-set-d-is-update-nth fn-xcs-get-start-is-nth fn-xcs-set-start-is-update-nth fn-xcs-get-trailer-is-nth fn-xcs-set-trailer-is-update-nth fn-xcs-get-stamp-is-nth fn-xcs-set-stamp-is-update-nth fn-xcc-count-is-len fn-xccp-is-scalar-seq-p fn-xcc-get-is-nth fn-xcc-set-is-update-nth fn-xcc-append-is-append))

; --- the geometry cells
(defun fn-xc-cellsp (fn-xcc)
  (declare (xargs :stobjs fn-xcc :guard (fn-xccp fn-xcc)))
  (equal (fn-xcc-count fn-xcc) 3))

(defun fn-xc-tick (fn-xcc)
  (declare (xargs :stobjs fn-xcc :guard (and (fn-xccp fn-xcc) (fn-xc-cellsp fn-xcc))))
  (fn-xcc-get 0 fn-xcc))

(defun fn-xc-ne (fn-xcc)
  (declare (xargs :stobjs fn-xcc :guard (and (fn-xccp fn-xcc) (fn-xc-cellsp fn-xcc))))
  (fn-xcc-get 1 fn-xcc))

(defun fn-xc-nw (fn-xcc)
  (declare (xargs :stobjs fn-xcc :guard (and (fn-xccp fn-xcc) (fn-xc-cellsp fn-xcc))))
  (fn-xcc-get 2 fn-xcc))

(defthm fn-xc-tick-is-u64
  (implies (and (fn-xccp fn-xcc) (fn-xc-cellsp fn-xcc)) (unsigned-byte-p 64 (fn-xc-tick fn-xcc)))
  :hints (("Goal" :use ((:instance fn-xcc-get-is-u64 (i 0)))
                  :in-theory (e/d (fn-xc-cellsp fn-xc-tick fn-xcc-count-is-len) (fn-xcc-get-is-u64)))))

(defthm fn-xc-ne-is-u64
  (implies (and (fn-xccp fn-xcc) (fn-xc-cellsp fn-xcc)) (unsigned-byte-p 64 (fn-xc-ne fn-xcc)))
  :hints (("Goal" :use ((:instance fn-xcc-get-is-u64 (i 1)))
                  :in-theory (e/d (fn-xc-cellsp fn-xc-ne fn-xcc-count-is-len) (fn-xcc-get-is-u64)))))

(defthm fn-xc-nw-is-u64
  (implies (and (fn-xccp fn-xcc) (fn-xc-cellsp fn-xcc)) (unsigned-byte-p 64 (fn-xc-nw fn-xcc)))
  :hints (("Goal" :use ((:instance fn-xcc-get-is-u64 (i 2)))
                  :in-theory (e/d (fn-xc-cellsp fn-xc-nw fn-xcc-count-is-len) (fn-xcc-get-is-u64)))))

(defthm fn-xc-tick-is-natp
  (implies (and (fn-xccp fn-xcc) (fn-xc-cellsp fn-xcc)) (natp (fn-xc-tick fn-xcc)))
  :rule-classes :type-prescription
  :hints (("Goal" :use fn-xc-tick-is-u64 :in-theory (e/d () (fn-xc-tick-is-u64)))))

(defthm fn-xc-ne-is-natp
  (implies (and (fn-xccp fn-xcc) (fn-xc-cellsp fn-xcc)) (natp (fn-xc-ne fn-xcc)))
  :rule-classes :type-prescription
  :hints (("Goal" :use fn-xc-ne-is-u64 :in-theory (e/d () (fn-xc-ne-is-u64)))))

(defthm fn-xc-nw-is-natp
  (implies (and (fn-xccp fn-xcc) (fn-xc-cellsp fn-xcc)) (natp (fn-xc-nw fn-xcc)))
  :rule-classes :type-prescription
  :hints (("Goal" :use fn-xc-nw-is-u64 :in-theory (e/d () (fn-xc-nw-is-u64)))))

; The table is ready when the cells exist and the rows are exactly NE + NW.
(defun fn-xc-readyp (fn-xcs fn-xcc)
  (declare (xargs :stobjs (fn-xcs fn-xcc) :guard (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc))))
  (and (fn-xc-cellsp fn-xcc)
       (equal (fn-xcs-count fn-xcs) (+ (fn-xc-ne fn-xcc) (fn-xc-nw fn-xcc)))))

; KIND 1 slots are the first NE; windows (kinds 2 and 3) the NW after them.
(defun fn-xc-lo (kind fn-xcc)
  (declare (xargs :stobjs fn-xcc :guard (and (fn-xccp fn-xcc) (fn-xc-cellsp fn-xcc))))
  (if (equal kind 1) 0 (fn-xc-ne fn-xcc)))

(defun fn-xc-hi (kind fn-xcc)
  (declare (xargs :stobjs fn-xcc :guard (and (fn-xccp fn-xcc) (fn-xc-cellsp fn-xcc))))
  (if (equal kind 1) (fn-xc-ne fn-xcc) (+ (fn-xc-ne fn-xcc) (fn-xc-nw fn-xcc))))

; A descriptor the columns can hold.
(defun fn-xc-keyp (kind file eoff elen a b c d start trailer)
  (declare (xargs :guard t))
  (and (member-equal kind '(1 2 3))
       (unsigned-byte-p 64 file) (unsigned-byte-p 64 eoff) (unsigned-byte-p 64 elen)
       (unsigned-byte-p 64 a) (unsigned-byte-p 64 b) (unsigned-byte-p 64 c)
       (unsigned-byte-p 64 d) (unsigned-byte-p 64 start)
       (natp trailer) (<= trailer *fn-xc-trailer-max*)))

; --- the scans.  GEN: def-loop :step (an index loop over a stobj's rows; the
; generator has the list shapes only, and :step has not landed on origin/dev:
; owed item EXT-CACHE-SCAN-GEN).
(defun fn-xc-slot-matchp (i exactp kind file eoff elen a b c d trailer pos fn-xcs)
  (declare (xargs :stobjs fn-xcs
                  :guard (and (fn-xcsp fn-xcs) (natp i) (< i (fn-xcs-count fn-xcs)) (natp pos))))
  (and (equal (fn-xcs-get-kind i fn-xcs) kind)
       (equal (fn-xcs-get-file i fn-xcs) file)
       (equal (fn-xcs-get-eoff i fn-xcs) eoff)
       (equal (fn-xcs-get-elen i fn-xcs) elen)
       (equal (fn-xcs-get-a i fn-xcs) a)
       (equal (fn-xcs-get-b i fn-xcs) b)
       (equal (fn-xcs-get-c i fn-xcs) c)
       (equal (fn-xcs-get-d i fn-xcs) d)
       (equal (fn-xcs-get-trailer i fn-xcs) trailer)
       (if exactp
           (equal (fn-xcs-get-start i fn-xcs) pos)
         (<= (fn-xcs-get-start i fn-xcs) pos))))

; GEN: def-loop :step
(defun fn-xc-find (i hi exactp kind file eoff elen a b c d trailer pos fn-xcs)
  (declare (xargs :stobjs fn-xcs
                  :guard (and (fn-xcsp fn-xcs) (natp i) (natp hi) (<= hi (fn-xcs-count fn-xcs))
                              (natp pos))
                  :measure (nfix (- hi i))))
  (if (and (natp i) (natp hi) (< i hi))
      (if (fn-xc-slot-matchp i exactp kind file eoff elen a b c d trailer pos fn-xcs)
          i
        (fn-xc-find (1+ i) hi exactp kind file eoff elen a b c d trailer pos fn-xcs))
    nil))

; GEN: def-loop :step
(defun fn-xc-find-free (i hi fn-xcs)
  (declare (xargs :stobjs fn-xcs
                  :guard (and (fn-xcsp fn-xcs) (natp i) (natp hi) (<= hi (fn-xcs-count fn-xcs)))
                  :measure (nfix (- hi i))))
  (if (and (natp i) (natp hi) (< i hi))
      (if (equal (fn-xcs-get-kind i fn-xcs) 0) i (fn-xc-find-free (1+ i) hi fn-xcs))
    nil))

; The least-recently-used LIVE slot of [i, hi): BEST is the least so far (or NIL).
; GEN: def-loop :step
(defun fn-xc-lru (i hi best fn-xcs)
  (declare (xargs :stobjs fn-xcs
                  :guard (and (fn-xcsp fn-xcs) (natp i) (natp hi) (<= hi (fn-xcs-count fn-xcs))
                              (or (null best) (and (natp best) (< best (fn-xcs-count fn-xcs)))))
                  :measure (nfix (- hi i))))
  (if (and (natp i) (natp hi) (< i hi))
      (fn-xc-lru (1+ i) hi
                 (if (and (not (equal (fn-xcs-get-kind i fn-xcs) 0))
                          (or (null best)
                              (< (fn-xcs-get-stamp i fn-xcs) (fn-xcs-get-stamp best fn-xcs))))
                     i best)
                 fn-xcs)
    best))

; The next live slot at or after I (of FILE when FILE is a natural; any when NIL).
; GEN: def-loop :step
(defun fn-xc-next (i file fn-xcs)
  (declare (xargs :stobjs fn-xcs
                  :guard (and (fn-xcsp fn-xcs) (natp i))
                  :measure (nfix (- (fn-xcs-count fn-xcs) i))))
  (if (and (natp i) (< i (fn-xcs-count fn-xcs)))
      (if (and (not (equal (fn-xcs-get-kind i fn-xcs) 0))
               (or (null file) (equal (fn-xcs-get-file i fn-xcs) file)))
          i
        (fn-xc-next (1+ i) file fn-xcs))
    nil))

(local
 (defthm fn-xc-len-update-nth
   (implies (and (natp i) (< i (len s)))
            (equal (len (update-nth i v s)) (len s)))))

(defmacro fn-xc-def-set-lemmas (field k okp)
  (let ((setter (intern-in-package-of-symbol (concatenate 'string "FN-XCS-SET-" (symbol-name field)) 'acl2::fn-xcs))
        (setter-is (intern-in-package-of-symbol (concatenate 'string "FN-XCS-SET-" (symbol-name field) "-IS-UPDATE-NTH") 'acl2::fn-xcs))
        (thm-count (intern-in-package-of-symbol (concatenate 'string "FN-XCS-SET-" (symbol-name field) "-KEEPS-COUNT") 'acl2::fn-xcs))
        (thm-p (intern-in-package-of-symbol (concatenate 'string "FN-XCS-SET-" (symbol-name field) "-KEEPS-WELL-FORMED") 'acl2::fn-xcs)))
    `(progn
       (defthm ,thm-count
         (implies (and (fn-xcsp s) (natp i) (< i (fn-xcs-count s)))
                  (equal (fn-xcs-count (,setter i v s)) (fn-xcs-count s)))
         :hints (("Goal" :in-theory (enable ,setter-is fn-xcs-count-is-len fn-xcsp-is-seq-p)
                         :use ((:instance fn-xc-row-typed (fn-xcs s))))))
       (defthm ,thm-p
         (implies (and (fn-xcsp s) (natp i) (< i (fn-xcs-count s)) ,okp)
                  (fn-xcsp (,setter i v s)))
         :hints (("Goal" :in-theory (enable ,setter-is fn-xcs-count-is-len fn-xcsp-is-seq-p)
                         :use ((:instance adt-seq-p-of-update-nth (s *fn-xcs-schema*) (i i) (a s)
                                          (r (update-nth ,k v (nth i s))))
                               (:instance adt-rec-p-of-nth (s *fn-xcs-schema*) (a s))
                               (:instance adt-rec-p-of-update-nth (s *fn-xcs-schema*) (r (nth i s)) (j ,k) (v v)))))))))
(fn-xc-def-set-lemmas kind 0 (member-equal v '(0 1 2 3)))
(fn-xc-def-set-lemmas tokp 1 (booleanp v))
(fn-xc-def-set-lemmas tid 2 (unsigned-byte-p 64 v))
(fn-xc-def-set-lemmas tcid 3 (unsigned-byte-p 64 v))
(fn-xc-def-set-lemmas file 4 (unsigned-byte-p 64 v))
(fn-xc-def-set-lemmas eoff 5 (unsigned-byte-p 64 v))
(fn-xc-def-set-lemmas elen 6 (unsigned-byte-p 64 v))
(fn-xc-def-set-lemmas a 7 (unsigned-byte-p 64 v))
(fn-xc-def-set-lemmas b 8 (unsigned-byte-p 64 v))
(fn-xc-def-set-lemmas c 9 (unsigned-byte-p 64 v))
(fn-xc-def-set-lemmas d 10 (unsigned-byte-p 64 v))
(fn-xc-def-set-lemmas start 11 (unsigned-byte-p 64 v))
(fn-xc-def-set-lemmas trailer 12 (and (natp v) (<= v *fn-xc-trailer-max*)))
(fn-xc-def-set-lemmas stamp 13 (unsigned-byte-p 64 v))

(defthm fn-xc-readyp-facts
  (implies (fn-xc-readyp fn-xcs fn-xcc)
           (and (fn-xc-cellsp fn-xcc)
                (equal (fn-xcs-count fn-xcs) (+ (fn-xc-ne fn-xcc) (fn-xc-nw fn-xcc)))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-xc-readyp))))

(in-theory (disable fn-xc-cellsp fn-xc-ne fn-xc-nw fn-xc-tick fn-xc-readyp fn-xc-lo fn-xc-hi))

(defthm fn-xc-lo-le-hi
  (implies (and (fn-xccp fn-xcc) (fn-xc-readyp fn-xcs fn-xcc))
           (<= (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable fn-xc-lo fn-xc-hi) :use (fn-xc-readyp-facts))))

(defthm fn-xc-hi-le-count
  (implies (and (fn-xccp fn-xcc) (fn-xc-readyp fn-xcs fn-xcc))
           (<= (fn-xc-hi kind fn-xcc) (fn-xcs-count fn-xcs)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable fn-xc-lo fn-xc-hi) :use (fn-xc-readyp-facts))))

(defthm fn-xc-cellsp-count
  (implies (fn-xc-cellsp fn-xcc) (equal (fn-xcc-count fn-xcc) 3))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-xc-cellsp))))

(defthm fn-xcc-set-keeps-count
  (implies (and (fn-xccp fn-xcc) (natp i) (< i (fn-xcc-count fn-xcc)))
           (equal (fn-xcc-count (fn-xcc-set i v fn-xcc)) (fn-xcc-count fn-xcc)))
  :hints (("Goal" :in-theory (enable fn-xcc-set-is-update-nth fn-xcc-count-is-len fn-xccp-is-scalar-seq-p))))

(defthm fn-xcc-set-keeps-well-formed
  (implies (and (fn-xccp fn-xcc) (natp i) (< i (fn-xcc-count fn-xcc)) (unsigned-byte-p 64 v))
           (fn-xccp (fn-xcc-set i v fn-xcc)))
  :hints (("Goal" :in-theory (enable fn-xcc-set-is-update-nth fn-xcc-count-is-len fn-xccp-is-scalar-seq-p
                                     adt-val-okp)
                  :use ((:instance adt-scalar-seq-p-of-update-nth (k '(:u64)) (a fn-xcc))))))

(defthm fn-xc-lo-natp
  (implies (and (fn-xccp fn-xcc) (fn-xc-cellsp fn-xcc)) (natp (fn-xc-lo kind fn-xcc)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-xc-lo))))

(defthm fn-xc-hi-natp
  (implies (and (fn-xccp fn-xcc) (fn-xc-cellsp fn-xcc)) (natp (fn-xc-hi kind fn-xcc)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-xc-hi))))

(defthm fn-xc-tick-bound
  (implies (and (fn-xccp fn-xcc) (fn-xc-cellsp fn-xcc))
           (< (fn-xc-tick fn-xcc) 18446744073709551616))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (unsigned-byte-p) (fn-xc-tick-is-u64))
                  :use fn-xc-tick-is-u64)))

; --- the token a slot's charge is bound to (the ledger's :cached row key)
(defun fn-xc-token (kind tokp tid tcid file eoff elen a b c d start trailer)
  (declare (xargs :guard t))
  (if (not tokp) nil
    (cond ((equal kind 1) (list tid tcid file eoff elen trailer))
          ((equal kind 2) (list :window tid file eoff elen a b start trailer))
          ((equal kind 3) (list :decoded-window tid file eoff elen a b start trailer c d))
          (t nil))))

(defun fn-xc-slot-token (i fn-xcs)
  (declare (xargs :stobjs fn-xcs :guard (and (fn-xcsp fn-xcs) (natp i) (< i (fn-xcs-count fn-xcs)))))
  (fn-xc-token (fn-xcs-get-kind i fn-xcs) (fn-xcs-get-tokp i fn-xcs)
               (fn-xcs-get-tid i fn-xcs) (fn-xcs-get-tcid i fn-xcs)
               (fn-xcs-get-file i fn-xcs) (fn-xcs-get-eoff i fn-xcs)
               (fn-xcs-get-elen i fn-xcs) (fn-xcs-get-a i fn-xcs)
               (fn-xcs-get-b i fn-xcs) (fn-xcs-get-c i fn-xcs)
               (fn-xcs-get-d i fn-xcs) (fn-xcs-get-start i fn-xcs)
               (fn-xcs-get-trailer i fn-xcs)))

; First holder of TOKEN outside TARGET, across both regions. NIL is never
; a charge. A slot index of zero is a hit, just as it is for fn-xc-find.
(defun fn-xc-find-token-except (token target i fn-xcs)
  (declare (xargs :stobjs fn-xcs
                  :guard (and (fn-xcsp fn-xcs) (natp i))
                  :measure (nfix (- (fn-xcs-count fn-xcs) i))))
  (if (and token (natp i) (< i (fn-xcs-count fn-xcs)))
      (if (and (not (equal i target)) (equal token (fn-xc-slot-token i fn-xcs)))
          i
        (fn-xc-find-token-except token target (1+ i) fn-xcs))
    nil))


; --- the clock
(defun fn-xc-next-stamp (fn-xcc)
  (declare (xargs :stobjs fn-xcc :guard (and (fn-xccp fn-xcc) (fn-xc-cellsp fn-xcc))
                  :guard-hints (("Goal" :in-theory (enable unsigned-byte-p)))))
  (let ((tick (fn-xc-tick fn-xcc)))
    (let ((fn-xcc (fn-xcc-set 0 (if (< tick *fn-xc-u64-max*) (1+ tick) tick) fn-xcc)))
      (mv tick fn-xcc))))

(defthm fn-xc-next-stamp-results
  (implies (and (fn-xccp fn-xcc) (fn-xc-cellsp fn-xcc))
           (and (unsigned-byte-p 64 (mv-nth 0 (fn-xc-next-stamp fn-xcc)))
                (equal (mv-nth 0 (fn-xc-next-stamp fn-xcc)) (fn-xc-tick fn-xcc))
                (fn-xccp (mv-nth 1 (fn-xc-next-stamp fn-xcc)))
                (equal (fn-xcc-count (mv-nth 1 (fn-xc-next-stamp fn-xcc))) 3)))
  :hints (("Goal" :in-theory (enable fn-xc-next-stamp unsigned-byte-p)
                  :use ((:instance fn-xcc-set-keeps-well-formed (i 0) (v (if (< (fn-xc-tick fn-xcc) 18446744073709551615) (1+ (fn-xc-tick fn-xcc)) (fn-xc-tick fn-xcc))))))))

; A use of slot I makes it the most recent.
(defun fn-xc-touch (i fn-xcs fn-xcc)
  (declare (xargs :stobjs (fn-xcs fn-xcc) :guard (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc))))
  (if (and (fn-xc-readyp fn-xcs fn-xcc) (natp i) (< i (fn-xcs-count fn-xcs))
           (not (equal (fn-xcs-get-kind i fn-xcs) 0)))
      (mv-let (stamp fn-xcc) (fn-xc-next-stamp fn-xcc)
        (let ((fn-xcs (fn-xcs-set-stamp i stamp fn-xcs)))
          (mv :touched fn-xcs fn-xcc)))
    (mv :stale fn-xcs fn-xcc)))

; --- reading
; (mv :hit SLOT) when SLOT is the first live slot of KIND's region holding the
; descriptor (a whole entry: with POS = 0 its start; a window: covering POS); (mv :miss nil) when none does.
; FROM resumes after a candidate the caller declined.
(defun fn-xc-lookup (from kind file eoff elen a b c d trailer pos fn-xcs fn-xcc)
  (declare (xargs :stobjs (fn-xcs fn-xcc)
                  :guard (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc) (natp from) (natp pos))))
  (if (and (fn-xc-readyp fn-xcs fn-xcc) (member-equal kind '(1 2 3)))
      (let ((slot (fn-xc-find (if (< from (fn-xc-lo kind fn-xcc)) (fn-xc-lo kind fn-xcc) from) (fn-xc-hi kind fn-xcc) (equal kind 1)
                              kind file eoff elen a b c d trailer pos fn-xcs)))
        (if slot (mv :hit slot) (mv :miss nil)))
    (mv :miss nil)))

; --- writing a slot
(defun fn-xc-write (i kind tokp tid tcid file eoff elen a b c d start trailer stamp fn-xcs)
  (declare (xargs :stobjs fn-xcs
                  :guard (and (fn-xcsp fn-xcs) (natp i) (< i (fn-xcs-count fn-xcs))
                              (member-equal kind '(0 1 2 3)) (booleanp tokp)
                              (unsigned-byte-p 64 tid) (unsigned-byte-p 64 tcid)
                              (fn-xc-keyp (if (equal kind 0) 1 kind) file eoff elen a b c d start trailer)
                              (unsigned-byte-p 64 stamp))))
  (let* ((fn-xcs (fn-xcs-set-kind i kind fn-xcs))
         (fn-xcs (fn-xcs-set-tokp i tokp fn-xcs))
         (fn-xcs (fn-xcs-set-tid i tid fn-xcs))
         (fn-xcs (fn-xcs-set-tcid i tcid fn-xcs))
         (fn-xcs (fn-xcs-set-file i file fn-xcs))
         (fn-xcs (fn-xcs-set-eoff i eoff fn-xcs))
         (fn-xcs (fn-xcs-set-elen i elen fn-xcs))
         (fn-xcs (fn-xcs-set-a i a fn-xcs))
         (fn-xcs (fn-xcs-set-b i b fn-xcs))
         (fn-xcs (fn-xcs-set-c i c fn-xcs))
         (fn-xcs (fn-xcs-set-d i d fn-xcs))
         (fn-xcs (fn-xcs-set-start i start fn-xcs))
         (fn-xcs (fn-xcs-set-trailer i trailer fn-xcs))
         (fn-xcs (fn-xcs-set-stamp i stamp fn-xcs)))
    fn-xcs))

; --- install.  (mv WORD SLOT EVICTED fn-xcs fn-xcc):
;   :installed  a free slot took the entry
;   :replaced   the least recently used slot of the region took it, and
;               EVICTED is that slot's token (its pool charge, NIL if none)
;   :present    the descriptor already holds SLOT (now the most recent); the
;               caller keeps nothing of the new vector
;   :refused    the region is empty (the cache is off), the table is not
;               ready, or a column cannot hold the descriptor
(defun fn-xc-install-conflict (kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)
  (declare (xargs :stobjs (fn-xcs fn-xcc) :guard (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc))))
  (if (not (and (fn-xc-readyp fn-xcs fn-xcc)
                (fn-xc-keyp kind file eoff elen a b c d start trailer)
                (booleanp tokp) (unsigned-byte-p 64 tid) (unsigned-byte-p 64 tcid)
                (< (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc))))
      (mv nil nil)
    (let* ((lo (fn-xc-lo kind fn-xcc)) (hi (fn-xc-hi kind fn-xcc))
           (target (or (fn-xc-find lo hi t kind file eoff elen a b c d trailer start fn-xcs)
                       (fn-xc-find-free lo hi fn-xcs)
                       (fn-xc-lru lo hi nil fn-xcs))))
      (if (and (natp target) (< target (fn-xcs-count fn-xcs)))
          (mv target (fn-xc-find-token-except
                      (fn-xc-token kind tokp tid tcid file eoff elen a b c d start trailer)
                      target 0 fn-xcs))
        (mv nil nil)))))

(in-theory (disable fn-xc-install-conflict fn-xc-find-token-except))

(defun fn-xc-install (kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)
  (declare (xargs :stobjs (fn-xcs fn-xcc) :guard (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc))))
  (mv-let (target holder)
    (fn-xc-install-conflict kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)
    (if holder (mv :duplicate target nil fn-xcs fn-xcc)
      (if (not (and (fn-xc-readyp fn-xcs fn-xcc)
                (fn-xc-keyp kind file eoff elen a b c d start trailer)
                (booleanp tokp) (unsigned-byte-p 64 tid) (unsigned-byte-p 64 tcid)
                (< (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc))))
      (mv :refused nil nil fn-xcs fn-xcc)
    (let* ((lo (fn-xc-lo kind fn-xcc)) (hi (fn-xc-hi kind fn-xcc))
           (present (fn-xc-find lo hi t kind file eoff elen a b c d trailer start fn-xcs)))
      (if present
          (mv-let (word fn-xcs fn-xcc) (fn-xc-touch present fn-xcs fn-xcc)
            (declare (ignore word))
            (mv :present present nil fn-xcs fn-xcc))
        (let* ((free (fn-xc-find-free lo hi fn-xcs))
               (victim (or free (fn-xc-lru lo hi nil fn-xcs))))
          (if (not (and (natp victim) (< victim (fn-xcs-count fn-xcs))))
              (mv :refused nil nil fn-xcs fn-xcc)
            (let ((evicted (if free nil (fn-xc-slot-token victim fn-xcs))))
              (mv-let (stamp fn-xcc) (fn-xc-next-stamp fn-xcc)
                (let ((fn-xcs (fn-xc-write victim kind tokp tid tcid file eoff elen a b c d
                                           start trailer stamp fn-xcs)))
                  (mv (if free :installed :replaced) victim evicted fn-xcs fn-xcc))))))))))))

; --- leaving
; Free slot I; the token is its pool charge to release (NIL: it held none).
(defun fn-xc-free (i fn-xcs)
  (declare (xargs :stobjs fn-xcs :guard (and (fn-xcsp fn-xcs) (natp i))))
  (if (and (natp i) (< i (fn-xcs-count fn-xcs)) (not (equal (fn-xcs-get-kind i fn-xcs) 0)))
      (let ((token (fn-xc-slot-token i fn-xcs)))
        (let ((fn-xcs (fn-xcs-set-kind i 0 fn-xcs)))
          (mv :freed token fn-xcs)))
    (mv :stale nil fn-xcs)))

; Under pool pressure the least recently used whole entry yields, then the
; least recently used window; (mv :yielded SLOT TOKEN ...) or (mv :none ...)
; when the table holds nothing.
(defun fn-xc-yield (fn-xcs fn-xcc)
  (declare (xargs :stobjs (fn-xcs fn-xcc) :guard (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc))))
  (if (not (fn-xc-readyp fn-xcs fn-xcc))
      (mv :none nil nil fn-xcs)
    (let* ((e (fn-xc-lru (fn-xc-lo 1 fn-xcc) (fn-xc-hi 1 fn-xcc) nil fn-xcs))
           (victim (or e (fn-xc-lru (fn-xc-lo 2 fn-xcc) (fn-xc-hi 2 fn-xcc) nil fn-xcs))))
      (if (not (and (natp victim) (< victim (fn-xcs-count fn-xcs))))
          (mv :none nil nil fn-xcs)
        (mv-let (word token fn-xcs) (fn-xc-free victim fn-xcs)
          (declare (ignore word))
          (mv :yielded victim token fn-xcs))))))

; The next live slot at or after FROM, of FILE (a natural) or any (NIL):
; what a retiring file or the end of recovery takes with it.
(defun fn-xc-next-live (from file fn-xcs)
  (declare (xargs :stobjs fn-xcs :guard (and (fn-xcsp fn-xcs) (natp from))))
  (fn-xc-next from file fn-xcs))

; Does slot I hold the charge TOKEN?
(defun fn-xc-holds (i token fn-xcs)
  (declare (xargs :stobjs fn-xcs :guard (fn-xcsp fn-xcs)))
  (and token (natp i) (< i (fn-xcs-count fn-xcs))
       (equal (fn-xc-slot-token i fn-xcs) token)))

; --- installing from a token
(defun fn-xc-install-entry (file eoff elen trailer token fn-xcs fn-xcc)
  (declare (xargs :stobjs (fn-xcs fn-xcc) :guard (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc))))
  (cond ((null token)
         (fn-xc-install 1 nil 0 0 file eoff elen 0 0 0 0 0 trailer fn-xcs fn-xcc))
        ((and (true-listp token) (equal (len token) 6)
              (equal (nth 2 token) file) (equal (nth 3 token) eoff)
              (equal (nth 4 token) elen) (equal (nth 5 token) trailer))
         (fn-xc-install 1 t (nth 0 token) (nth 1 token) file eoff elen 0 0 0 0 0 trailer
                        fn-xcs fn-xcc))
        (t (mv :refused nil nil fn-xcs fn-xcc))))

(defun fn-xc-install-window (token fn-xcs fn-xcc)
  (declare (xargs :stobjs (fn-xcs fn-xcc) :guard (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc))))
  (cond ((and (true-listp token) (equal (len token) 9) (equal (nth 0 token) :window))
         (fn-xc-install 2 t (nth 1 token) 0 (nth 2 token) (nth 3 token) (nth 4 token)
                        (nth 5 token) (nth 6 token) 0 0 (nth 7 token) (nth 8 token) fn-xcs fn-xcc))
        ((and (true-listp token) (equal (len token) 11) (equal (nth 0 token) :decoded-window))
         (fn-xc-install 3 t (nth 1 token) 0 (nth 2 token) (nth 3 token) (nth 4 token)
                        (nth 5 token) (nth 6 token) (nth 9 token) (nth 10 token)
                        (nth 7 token) (nth 8 token) fn-xcs fn-xcc))
        (t (mv :refused nil nil fn-xcs fn-xcc))))

; --- the table, from the profile
(defun fn-xc-append-free (n fn-xcs)
  (declare (xargs :stobjs fn-xcs :guard (and (fn-xcsp fn-xcs) (natp n))
                  :measure (nfix n)))
  (if (zp n)
      fn-xcs
    (let ((fn-xcs (fn-xcs-append *fn-xc-free-row* fn-xcs)))
      (fn-xc-append-free (1- n) fn-xcs))))

; At most this many slots of either kind: a profile figure beyond it is
; refused.  The scans are linear, so the bound is the size at which a scan
; stops being cheaper than an index: past it the hash index (owed item
; EXT-CACHE-INDEX) must land first.
(defconst *fn-xc-max-slots* 32)

; The profile's figures are within it, or this book does not certify.
(defthm fn-xc-profile-figures-are-within-the-scan-bound
  (and (natp (fn-profile-limit :extent-cache-entries))
       (natp (fn-profile-limit :extent-cache-windows))
       (<= (fn-profile-limit :extent-cache-entries) *fn-xc-max-slots*)
       (<= (fn-profile-limit :extent-cache-windows) *fn-xc-max-slots*)
       ; the resource plan sizes the cache's charge by the entries figure alone
       ; (fn-prstartup-cache-capacity), for both kinds
       (<= (fn-profile-limit :extent-cache-windows) (fn-profile-limit :extent-cache-entries)))
  :rule-classes nil)

(defun fn-xc-init (ne nw fn-xcs fn-xcc)
  (declare (xargs :stobjs (fn-xcs fn-xcc) :guard (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc))))
  (cond ((not (and (natp ne) (natp nw) (<= ne *fn-xc-max-slots*) (<= nw *fn-xc-max-slots*)))
         (mv :refused fn-xcs fn-xcc))
        ((not (and (equal (fn-xcc-count fn-xcc) 0) (equal (fn-xcs-count fn-xcs) 0)))
         (mv :already fn-xcs fn-xcc))
        (t (let* ((fn-xcc (fn-xcc-append 0 fn-xcc))
                  (fn-xcc (fn-xcc-append ne fn-xcc))
                  (fn-xcc (fn-xcc-append nw fn-xcc))
                  (fn-xcs (fn-xc-append-free (+ ne nw) fn-xcs)))
             (mv :initialized fn-xcs fn-xcc)))))

; =============================================================================
; The decisions are right.

(in-theory (disable fn-xc-find fn-xc-find-free fn-xc-lru fn-xc-next fn-xc-slot-matchp))

; --- the scan
(defthm fn-xc-find-bounds
  (implies (and (natp i) (fn-xc-find i hi exactp kind file eoff elen a b c d trailer pos fn-xcs))
           (and (natp (fn-xc-find i hi exactp kind file eoff elen a b c d trailer pos fn-xcs))
                (<= i (fn-xc-find i hi exactp kind file eoff elen a b c d trailer pos fn-xcs))
                (< (fn-xc-find i hi exactp kind file eoff elen a b c d trailer pos fn-xcs) hi)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-xc-find) :induct (fn-xc-find i hi exactp kind file eoff elen a b c d trailer pos fn-xcs))))

(defthm fn-xc-find-matches
  (implies (fn-xc-find i hi exactp kind file eoff elen a b c d trailer pos fn-xcs)
           (fn-xc-slot-matchp (fn-xc-find i hi exactp kind file eoff elen a b c d trailer pos fn-xcs)
                              exactp kind file eoff elen a b c d trailer pos fn-xcs))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-xc-find) :induct (fn-xc-find i hi exactp kind file eoff elen a b c d trailer pos fn-xcs))))

; Complete: a matching slot in [i, hi) is found, and the one found is the first.
(defthm fn-xc-find-complete
  (implies (and (natp i) (natp j) (natp hi) (<= i j) (< j hi)
                (fn-xc-slot-matchp j exactp kind file eoff elen a b c d trailer pos fn-xcs))
           (and (fn-xc-find i hi exactp kind file eoff elen a b c d trailer pos fn-xcs)
                (<= (fn-xc-find i hi exactp kind file eoff elen a b c d trailer pos fn-xcs) j)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-xc-find) :induct (fn-xc-find i hi exactp kind file eoff elen a b c d trailer pos fn-xcs))))

(defthm fn-xc-find-first
  (implies (and (natp i) (natp j) (<= i j)
                (fn-xc-find i hi exactp kind file eoff elen a b c d trailer pos fn-xcs)
                (< j (fn-xc-find i hi exactp kind file eoff elen a b c d trailer pos fn-xcs)))
           (not (fn-xc-slot-matchp j exactp kind file eoff elen a b c d trailer pos fn-xcs)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-xc-find) :induct (fn-xc-find i hi exactp kind file eoff elen a b c d trailer pos fn-xcs))))

; --- KEYSTONES 1: lookup is exactly a search of the live slots.
; A hit is a live slot of the right region whose stored descriptor equals the key.
(defthm fn-xc-lookup-hit-is-the-descriptor
  (implies (and (fn-xccp fn-xcc) (fn-xc-readyp fn-xcs fn-xcc) (member-equal kind '(1 2 3))
                (natp from) (natp pos)
                (equal (mv-nth 0 (fn-xc-lookup from kind file eoff elen a b c d trailer pos fn-xcs fn-xcc))
                       :hit))
           (let ((i (mv-nth 1 (fn-xc-lookup from kind file eoff elen a b c d trailer pos fn-xcs fn-xcc))))
             (and (natp i) (<= from i)
                  (<= (fn-xc-lo kind fn-xcc) i) (< i (fn-xc-hi kind fn-xcc))
                  (equal (fn-xcs-get-kind i fn-xcs) kind)
                  (equal (fn-xcs-get-file i fn-xcs) file)
                  (equal (fn-xcs-get-eoff i fn-xcs) eoff)
                  (equal (fn-xcs-get-elen i fn-xcs) elen)
                  (equal (fn-xcs-get-a i fn-xcs) a)
                  (equal (fn-xcs-get-b i fn-xcs) b)
                  (equal (fn-xcs-get-c i fn-xcs) c)
                  (equal (fn-xcs-get-d i fn-xcs) d)
                  (equal (fn-xcs-get-trailer i fn-xcs) trailer)
                  (if (equal kind 1)
                      (equal (fn-xcs-get-start i fn-xcs) pos)
                    (<= (fn-xcs-get-start i fn-xcs) pos)))))
  :hints (("Goal" :in-theory (enable fn-xc-lookup fn-xc-slot-matchp)
                  :cases ((< from (fn-xc-lo kind fn-xcc)))
                  :use ((:instance fn-xc-find-bounds
                                   (i (if (< from (fn-xc-lo kind fn-xcc)) (fn-xc-lo kind fn-xcc) from))
                                   (hi (fn-xc-hi kind fn-xcc)) (exactp (equal kind 1)))
                        (:instance fn-xc-find-matches
                                   (i (if (< from (fn-xc-lo kind fn-xcc)) (fn-xc-lo kind fn-xcc) from))
                                   (hi (fn-xc-hi kind fn-xcc)) (exactp (equal kind 1)))))))

; A miss: no live slot of the region holds it (at or after FROM).
(defthm fn-xc-lookup-miss-is-absent
  (implies (and (fn-xccp fn-xcc) (fn-xc-readyp fn-xcs fn-xcc) (member-equal kind '(1 2 3))
                (natp from) (natp pos) (natp j)
                (<= from j) (<= (fn-xc-lo kind fn-xcc) j) (< j (fn-xc-hi kind fn-xcc))
                (equal (mv-nth 0 (fn-xc-lookup from kind file eoff elen a b c d trailer pos fn-xcs fn-xcc))
                       :miss))
           (not (fn-xc-slot-matchp j (equal kind 1) kind file eoff elen a b c d trailer pos fn-xcs)))
  :hints (("Goal" :in-theory (enable fn-xc-lookup)
                  :use ((:instance fn-xc-find-complete
                                   (i (if (< from (fn-xc-lo kind fn-xcc)) (fn-xc-lo kind fn-xcc) from))
                                   (hi (fn-xc-hi kind fn-xcc)) (exactp (equal kind 1)))))))

; Teeth: the lookup answers a hit exactly when some live slot of the region holds the key.
(defthm fn-xc-lookup-finds-every-held-descriptor
  (implies (and (fn-xccp fn-xcc) (fn-xc-readyp fn-xcs fn-xcc) (member-equal kind '(1 2 3))
                (natp pos) (natp j)
                (<= (fn-xc-lo kind fn-xcc) j) (< j (fn-xc-hi kind fn-xcc))
                (fn-xc-slot-matchp j (equal kind 1) kind file eoff elen a b c d trailer pos fn-xcs))
           (equal (mv-nth 0 (fn-xc-lookup 0 kind file eoff elen a b c d trailer pos fn-xcs fn-xcc))
                  :hit))
  :hints (("Goal" :in-theory (enable fn-xc-lookup)
                  :use ((:instance fn-xc-find-complete
                                   (i (fn-xc-lo kind fn-xcc))
                                   (hi (fn-xc-hi kind fn-xcc)) (exactp (equal kind 1)))))))

; --- what a write leaves: the slot as written, every other slot untouched.
(defun fn-xc-write-okp (i kind tokp tid tcid file eoff elen a b c d start trailer stamp fn-xcs)
  (declare (xargs :stobjs fn-xcs :guard (fn-xcsp fn-xcs)))
  (and (fn-xcsp fn-xcs) (natp i) (< i (fn-xcs-count fn-xcs))
       (member-equal kind '(0 1 2 3)) (booleanp tokp)
       (unsigned-byte-p 64 tid) (unsigned-byte-p 64 tcid)
       (fn-xc-keyp (if (equal kind 0) 1 kind) file eoff elen a b c d start trailer)
       (unsigned-byte-p 64 stamp)))

(defthm fn-xc-write-keeps-well-formed
  (implies (fn-xc-write-okp i kind tokp tid tcid file eoff elen a b c d start trailer stamp fn-xcs)
           (and (fn-xcsp (fn-xc-write i kind tokp tid tcid file eoff elen a b c d start trailer stamp fn-xcs))
                (equal (fn-xcs-count (fn-xc-write i kind tokp tid tcid file eoff elen a b c d start trailer stamp fn-xcs))
                       (fn-xcs-count fn-xcs))))
  :hints (("Goal" :in-theory (e/d (fn-xc-write fn-xc-write-okp fn-xc-keyp) (unsigned-byte-p)))))

(defmacro fn-xc-def-write-reads (f &rest more)
  (let ((getter (intern-in-package-of-symbol (concatenate 'string "FN-XCS-GET-" (symbol-name f)) 'fn-xcs))
        (getter-is (intern-in-package-of-symbol (concatenate 'string "FN-XCS-GET-" (symbol-name f) "-IS-NTH") 'fn-xcs))
        (name (intern-in-package-of-symbol (concatenate 'string "FN-XC-WRITE-READS-" (symbol-name f)) 'fn-xcs)))
    `(progn
       (defthm ,name
         (implies (and (fn-xc-write-okp i kind tokp tid tcid file eoff elen a b c d start trailer stamp fn-xcs)
                       (natp j))
                  (equal (,getter j (fn-xc-write i kind tokp tid tcid file eoff elen a b c d start trailer stamp fn-xcs))
                         (if (equal j i) ,f (,getter j fn-xcs))))
         :hints (("Goal" :in-theory (e/d (fn-xc-write fn-xc-write-okp fn-xc-keyp ,getter-is
                                          fn-xcs-set-kind-is-update-nth fn-xcs-set-tokp-is-update-nth
                                          fn-xcs-set-tid-is-update-nth fn-xcs-set-tcid-is-update-nth
                                          fn-xcs-set-file-is-update-nth fn-xcs-set-eoff-is-update-nth
                                          fn-xcs-set-elen-is-update-nth fn-xcs-set-a-is-update-nth
                                          fn-xcs-set-b-is-update-nth fn-xcs-set-c-is-update-nth
                                          fn-xcs-set-d-is-update-nth fn-xcs-set-start-is-update-nth
                                          fn-xcs-set-trailer-is-update-nth fn-xcs-set-stamp-is-update-nth
                                          fn-xcs-count-is-len fn-xcsp-is-seq-p)
                                         (unsigned-byte-p)))))
       ,@(and more `((fn-xc-def-write-reads ,@more))))))

(fn-xc-def-write-reads kind tokp tid tcid file eoff elen a b c d start trailer stamp)

(defthm fn-xc-write-reads-count
  (implies (fn-xc-write-okp i kind tokp tid tcid file eoff elen a b c d start trailer stamp fn-xcs)
           (equal (fn-xcs-count (fn-xc-write i kind tokp tid tcid file eoff elen a b c d start trailer stamp fn-xcs))
                  (fn-xcs-count fn-xcs)))
  :hints (("Goal" :use fn-xc-write-keeps-well-formed)))

; --- the free-slot and least-recently-used scans
(defthm fn-xc-find-free-is-free
  (implies (and (natp i) (fn-xc-find-free i hi fn-xcs))
           (and (natp (fn-xc-find-free i hi fn-xcs))
                (<= i (fn-xc-find-free i hi fn-xcs))
                (< (fn-xc-find-free i hi fn-xcs) hi)
                (equal (fn-xcs-get-kind (fn-xc-find-free i hi fn-xcs) fn-xcs) 0)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-xc-find-free) :induct (fn-xc-find-free i hi fn-xcs))))

(defthm fn-xc-find-free-complete
  (implies (and (natp i) (natp j) (natp hi) (<= i j) (< j hi)
                (equal (fn-xcs-get-kind j fn-xcs) 0))
           (fn-xc-find-free i hi fn-xcs))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-xc-find-free) :induct (fn-xc-find-free i hi fn-xcs))))

; The victim: live, in range, and no live slot of the range is older.
(defthm fn-xc-lru-is-least
  (implies (and (fn-xcsp fn-xcs) (natp i) (natp hi) (<= hi (fn-xcs-count fn-xcs))
                (or (null best)
                    (and (natp best) (< best (fn-xcs-count fn-xcs))
                         (not (equal (fn-xcs-get-kind best fn-xcs) 0)))))
           (let ((r (fn-xc-lru i hi best fn-xcs)))
             (and (implies (or best
                               (and (natp j) (<= i j) (< j hi)
                                    (not (equal (fn-xcs-get-kind j fn-xcs) 0))))
                           r)
                  (implies r
                           (and (natp r) (< r (fn-xcs-count fn-xcs))
                                (not (equal (fn-xcs-get-kind r fn-xcs) 0))
                                (or (equal r best) (and (<= i r) (< r hi)))
                                (implies best (<= (fn-xcs-get-stamp r fn-xcs) (fn-xcs-get-stamp best fn-xcs)))
                                (implies (and (natp j) (<= i j) (< j hi)
                                              (not (equal (fn-xcs-get-kind j fn-xcs) 0)))
                                         (<= (fn-xcs-get-stamp r fn-xcs) (fn-xcs-get-stamp j fn-xcs))))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-xc-lru) :induct (fn-xc-lru i hi best fn-xcs))))

; With no free slot in a nonempty range, someone is the oldest.
(defthm fn-xc-lru-exists-when-full
  (implies (and (fn-xcsp fn-xcs) (natp lo) (natp hi) (<= hi (fn-xcs-count fn-xcs)) (< lo hi)
                (not (fn-xc-find-free lo hi fn-xcs)))
           (fn-xc-lru lo hi nil fn-xcs))
  :hints (("Goal" :use ((:instance fn-xc-lru-is-least (i lo) (best nil) (j lo))
                        (:instance fn-xc-find-free-complete (i lo) (j lo))))))

(defthm fn-xc-lru-is-a-slot
  (implies (and (fn-xcsp fn-xcs) (natp i) (natp hi) (<= hi (fn-xcs-count fn-xcs))
                (fn-xc-lru i hi nil fn-xcs))
           (and (natp (fn-xc-lru i hi nil fn-xcs))
                (< (fn-xc-lru i hi nil fn-xcs) (fn-xcs-count fn-xcs))))
  :hints (("Goal" :use ((:instance fn-xc-lru-is-least (best nil) (j i))))))

; --- the clock cells after a use
(defthm fn-xcc-get-after-set
  (implies (and (fn-xccp fn-xcc) (natp i) (< i (fn-xcc-count fn-xcc)) (natp j))
           (equal (fn-xcc-get j (fn-xcc-set i v fn-xcc))
                  (if (equal j i) v (fn-xcc-get j fn-xcc))))
  :hints (("Goal" :in-theory (enable fn-xcc-get-is-nth fn-xcc-set-is-update-nth fn-xcc-count-is-len
                                     fn-xccp-is-scalar-seq-p))))

(defthm fn-xc-cellsp-of-count
  (implies (equal (fn-xcc-count fn-xcc) 3) (fn-xc-cellsp fn-xcc))
  :hints (("Goal" :in-theory (enable fn-xc-cellsp))))

(defthm fn-xc-next-stamp-geometry
  (implies (and (fn-xccp fn-xcc) (fn-xc-cellsp fn-xcc))
           (let ((c2 (mv-nth 1 (fn-xc-next-stamp fn-xcc))))
             (and (fn-xccp c2) (fn-xc-cellsp c2)
                  (equal (fn-xc-ne c2) (fn-xc-ne fn-xcc))
                  (equal (fn-xc-nw c2) (fn-xc-nw fn-xcc))
                  (equal (fn-xc-tick c2)
                         (if (< (fn-xc-tick fn-xcc) *fn-xc-u64-max*) (1+ (fn-xc-tick fn-xcc)) (fn-xc-tick fn-xcc))))))
  :hints (("Goal" :in-theory (e/d (fn-xc-next-stamp fn-xc-ne fn-xc-nw fn-xc-tick)
                                  (fn-xc-cellsp fn-xc-cellsp-of-count))
                  :use (fn-xc-next-stamp-results (:instance fn-xc-cellsp-of-count
                                                            (fn-xcc (mv-nth 1 (fn-xc-next-stamp fn-xcc))))))))

; --- what a touch leaves
(defmacro fn-xc-def-stamp-reads (f &rest more)
  (let ((getter (intern-in-package-of-symbol (concatenate 'string "FN-XCS-GET-" (symbol-name f)) 'fn-xcs))
        (getter-is (intern-in-package-of-symbol (concatenate 'string "FN-XCS-GET-" (symbol-name f) "-IS-NTH") 'fn-xcs))
        (name (intern-in-package-of-symbol (concatenate 'string "FN-XCS-SET-STAMP-READS-" (symbol-name f)) 'fn-xcs)))
    `(progn
       (defthm ,name
         (implies (and (fn-xcsp fn-xcs) (natp i) (< i (fn-xcs-count fn-xcs)) (natp j))
                  (equal (,getter j (fn-xcs-set-stamp i v fn-xcs))
                         ,(if (eq f 'stamp)
                              `(if (equal j i) v (,getter j fn-xcs))
                            `(,getter j fn-xcs))))
         :hints (("Goal" :in-theory (enable fn-xcs-set-stamp-is-update-nth ,getter-is))))
       ,@(and more `((fn-xc-def-stamp-reads ,@more))))))

(fn-xc-def-stamp-reads kind tokp tid tcid file eoff elen a b c d start trailer stamp)

(defthm fn-xcs-set-stamp-frame
  (implies (and (fn-xcsp fn-xcs) (natp i) (< i (fn-xcs-count fn-xcs)) (natp j) (not (equal j i)))
           (equal (nth j (fn-xcs-set-stamp i v fn-xcs)) (nth j fn-xcs)))
  :hints (("Goal" :in-theory (enable fn-xcs-set-stamp-is-update-nth))))

(defthm fn-xc-slot-matchp-after-set-stamp
  (implies (and (fn-xcsp fn-xcs) (natp i) (< i (fn-xcs-count fn-xcs)) (natp j))
           (equal (fn-xc-slot-matchp j exactp kind file eoff elen a b c d trailer pos (fn-xcs-set-stamp i v fn-xcs))
                  (fn-xc-slot-matchp j exactp kind file eoff elen a b c d trailer pos fn-xcs)))
  :hints (("Goal" :in-theory (enable fn-xc-slot-matchp))))

(defthm fn-xc-slot-token-after-set-stamp
  (implies (and (fn-xcsp fn-xcs) (natp i) (< i (fn-xcs-count fn-xcs)) (natp j))
           (equal (fn-xc-slot-token j (fn-xcs-set-stamp i v fn-xcs))
                  (fn-xc-slot-token j fn-xcs)))
  :hints (("Goal" :in-theory (enable fn-xc-slot-token))))

(defthm fn-xc-touch-effects
  (implies (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc) (fn-xc-readyp fn-xcs fn-xcc)
                (natp i) (< i (fn-xcs-count fn-xcs))
                (not (equal (fn-xcs-get-kind i fn-xcs) 0)))
           (let ((s2 (mv-nth 1 (fn-xc-touch i fn-xcs fn-xcc)))
                 (c2 (mv-nth 2 (fn-xc-touch i fn-xcs fn-xcc))))
             (and (equal (mv-nth 0 (fn-xc-touch i fn-xcs fn-xcc)) :touched)
                  (fn-xcsp s2) (fn-xccp c2)
                  (equal (fn-xcs-count s2) (fn-xcs-count fn-xcs))
                  (equal (fn-xcs-get-stamp i s2) (fn-xc-tick fn-xcc))
                  (equal (fn-xc-ne c2) (fn-xc-ne fn-xcc))
                  (equal (fn-xc-nw c2) (fn-xc-nw fn-xcc))
                  (fn-xc-readyp s2 c2))))
  :hints (("Goal" :in-theory (e/d (fn-xc-touch fn-xc-readyp) (fn-xc-next-stamp-geometry fn-xc-next-stamp-results))
                  :use (fn-xc-next-stamp-geometry fn-xc-next-stamp-results))))

(defthm fn-xc-readyp-transfer
  (implies (and (fn-xc-readyp fn-xcs fn-xcc) (fn-xc-cellsp c2)
                (equal (fn-xcs-count s2) (fn-xcs-count fn-xcs))
                (equal (fn-xc-ne c2) (fn-xc-ne fn-xcc))
                (equal (fn-xc-nw c2) (fn-xc-nw fn-xcc)))
           (fn-xc-readyp s2 c2))
  :hints (("Goal" :in-theory (enable fn-xc-readyp))))

(in-theory (disable fn-xc-write fn-xc-touch fn-xc-next-stamp))

; --- install
(defun fn-xc-install-okp (kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)
  (declare (xargs :stobjs (fn-xcs fn-xcc) :guard (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc))))
  (and (fn-xc-readyp fn-xcs fn-xcc)
       (fn-xc-keyp kind file eoff elen a b c d start trailer)
       (booleanp tokp) (unsigned-byte-p 64 tid) (unsigned-byte-p 64 tcid)))

(defthm fn-xc-install-conflict-geometry
  (implies (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc)
                (mv-nth 1 (fn-xc-install-conflict kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)))
           (and (natp (mv-nth 0 (fn-xc-install-conflict kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)))
                (< (mv-nth 0 (fn-xc-install-conflict kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) (fn-xcs-count fn-xcs))
                (< (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc))
                (<= (fn-xc-lo kind fn-xcc) (mv-nth 0 (fn-xc-install-conflict kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)))
                (< (mv-nth 0 (fn-xc-install-conflict kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) (fn-xc-hi kind fn-xcc))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-xc-install-conflict)
           :use ((:instance fn-xc-find-bounds (i (fn-xc-lo kind fn-xcc)) (hi (fn-xc-hi kind fn-xcc)) (exactp t) (pos start))
                 (:instance fn-xc-find-free-is-free (i (fn-xc-lo kind fn-xcc)) (hi (fn-xc-hi kind fn-xcc)))
                 (:instance fn-xc-lru-is-least (i (fn-xc-lo kind fn-xcc)) (hi (fn-xc-hi kind fn-xcc)) (best nil))))))

(defthm fn-xc-install-placement
  (implies (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc)
                (fn-xc-install-okp kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc))
           (let* ((r (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc))
                  (word (mv-nth 0 r)) (v (mv-nth 1 r)) (s2 (mv-nth 3 r)) (c2 (mv-nth 4 r)))
             (and (member-equal word '(:installed :replaced :present :refused :duplicate))
                  ; refused exactly when the region is empty: the cache is off for this kind
                  (iff (equal word :refused) (equal (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc)))
                  (implies (not (equal word :refused))
                           (and (natp v) (<= (fn-xc-lo kind fn-xcc) v) (< v (fn-xc-hi kind fn-xcc))))
                  (fn-xcsp s2) (fn-xccp c2)
                  (equal (fn-xcs-count s2) (fn-xcs-count fn-xcs))
                  (equal (fn-xc-ne c2) (fn-xc-ne fn-xcc))
                  (equal (fn-xc-nw c2) (fn-xc-nw fn-xcc))
                  (fn-xc-readyp s2 c2))))
  :hints (("Goal" :in-theory (enable fn-xc-install fn-xc-install-okp fn-xc-slot-matchp)
                  :do-not-induct t
                  :use (fn-xc-install-conflict-geometry
                        (:instance fn-xc-find-matches (i (fn-xc-lo kind fn-xcc)) (hi (fn-xc-hi kind fn-xcc))
                                   (exactp t) (pos start))
                        (:instance fn-xc-find-bounds (i (fn-xc-lo kind fn-xcc)) (hi (fn-xc-hi kind fn-xcc))
                                   (exactp t) (pos start))
                        (:instance fn-xc-find-free-is-free (i (fn-xc-lo kind fn-xcc)) (hi (fn-xc-hi kind fn-xcc)))
                        (:instance fn-xc-lru-is-least (i (fn-xc-lo kind fn-xcc)) (hi (fn-xc-hi kind fn-xcc))
                                   (best nil) (j (fn-xc-lo kind fn-xcc)))
                        (:instance fn-xc-find-free-complete (i (fn-xc-lo kind fn-xcc)) (j (fn-xc-lo kind fn-xcc))
                                   (hi (fn-xc-hi kind fn-xcc)))))))

; --- frames
(defthm fn-xc-write-frame
  (implies (and (fn-xc-write-okp i kind tokp tid tcid file eoff elen a b c d start trailer stamp fn-xcs)
                (natp j) (not (equal j i)))
           (equal (nth j (fn-xc-write i kind tokp tid tcid file eoff elen a b c d start trailer stamp fn-xcs))
                  (nth j fn-xcs)))
  :hints (("Goal" :in-theory (e/d (fn-xc-write fn-xc-write-okp fn-xc-keyp
                                   fn-xcs-set-kind-is-update-nth fn-xcs-set-tokp-is-update-nth
                                   fn-xcs-set-tid-is-update-nth fn-xcs-set-tcid-is-update-nth
                                   fn-xcs-set-file-is-update-nth fn-xcs-set-eoff-is-update-nth
                                   fn-xcs-set-elen-is-update-nth fn-xcs-set-a-is-update-nth
                                   fn-xcs-set-b-is-update-nth fn-xcs-set-c-is-update-nth
                                   fn-xcs-set-d-is-update-nth fn-xcs-set-start-is-update-nth
                                   fn-xcs-set-trailer-is-update-nth fn-xcs-set-stamp-is-update-nth
                                   fn-xcs-count-is-len fn-xcsp-is-seq-p)
                                  (unsigned-byte-p)))))

(defthm fn-xc-touch-frame
  (implies (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc) (fn-xc-readyp fn-xcs fn-xcc)
                (natp i) (< i (fn-xcs-count fn-xcs))
                (not (equal (fn-xcs-get-kind i fn-xcs) 0))
                (natp j) (not (equal j i)))
           (equal (nth j (mv-nth 1 (fn-xc-touch i fn-xcs fn-xcc))) (nth j fn-xcs)))
  :hints (("Goal" :in-theory (e/d (fn-xc-touch) (fn-xcs-set-stamp-frame))
                  :use ((:instance fn-xcs-set-stamp-frame (v (fn-xc-tick fn-xcc)))))))

; --- the matcher on a written table
(defthm fn-xc-matchp-after-write
  (implies (and (fn-xc-write-okp i kind tokp tid tcid file eoff elen a b c d start trailer stamp fn-xcs)
                (natp j))
           (equal (fn-xc-slot-matchp j exactp kd fl eo el aa bb cc dd tr pos
                                     (fn-xc-write i kind tokp tid tcid file eoff elen a b c d start trailer stamp fn-xcs))
                  (if (equal j i)
                      (and (equal kind kd) (equal file fl) (equal eoff eo) (equal elen el)
                           (equal a aa) (equal b bb) (equal c cc) (equal d dd) (equal trailer tr)
                           (if exactp (equal start pos) (<= start pos)))
                    (fn-xc-slot-matchp j exactp kd fl eo el aa bb cc dd tr pos fn-xcs))))
  :hints (("Goal" :in-theory (enable fn-xc-slot-matchp))))

(defthm fn-xc-matchp-after-touch
  (implies (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc) (fn-xc-readyp fn-xcs fn-xcc)
                (natp i) (< i (fn-xcs-count fn-xcs))
                (not (equal (fn-xcs-get-kind i fn-xcs) 0)) (natp j))
           (equal (fn-xc-slot-matchp j exactp kd fl eo el aa bb cc dd tr pos (mv-nth 1 (fn-xc-touch i fn-xcs fn-xcc)))
                  (fn-xc-slot-matchp j exactp kd fl eo el aa bb cc dd tr pos fn-xcs)))
  :hints (("Goal" :in-theory (enable fn-xc-touch))))

(defthm fn-xc-token-after-touch
  (implies (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc) (fn-xc-readyp fn-xcs fn-xcc)
                (natp i) (< i (fn-xcs-count fn-xcs))
                (not (equal (fn-xcs-get-kind i fn-xcs) 0)) (natp j))
           (equal (fn-xc-slot-token j (mv-nth 1 (fn-xc-touch i fn-xcs fn-xcc)))
                  (fn-xc-slot-token j fn-xcs)))
  :hints (("Goal" :in-theory (enable fn-xc-touch))))

;; an exact match is a covering match
(defthm fn-xc-exact-match-covers
  (implies (fn-xc-slot-matchp j t kind file eoff elen a b c d trailer pos fn-xcs)
           (fn-xc-slot-matchp j nil kind file eoff elen a b c d trailer pos fn-xcs))
  :hints (("Goal" :in-theory (enable fn-xc-slot-matchp))))

;; a slot that matches a (nonfree) key is live
(defthm fn-xc-matchp-is-live
  (implies (and (not (equal kind 0))
                (fn-xc-slot-matchp i exactp kind file eoff elen a b c d trailer pos fn-xcs))
           (not (equal (fn-xcs-get-kind i fn-xcs) 0)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :in-theory (enable fn-xc-slot-matchp))))

(defthm fn-xc-geometry-of-lo-hi
  (implies (and (equal (fn-xc-ne c2) (fn-xc-ne fn-xcc)) (equal (fn-xc-nw c2) (fn-xc-nw fn-xcc)))
           (and (equal (fn-xc-lo kind c2) (fn-xc-lo kind fn-xcc))
                (equal (fn-xc-hi kind c2) (fn-xc-hi kind fn-xcc))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-xc-lo fn-xc-hi))))

; --- the three ways an install can go, each as what it computes
(defmacro fn-xc-install-call ()
  '(fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc))

(defthm fn-xc-install-when-present
  (implies (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc)
                (fn-xc-install-okp kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)
                (< (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc))
                (fn-xc-find (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) t kind file eoff elen a b c d
                            trailer start fn-xcs)
                (not (equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) :duplicate)))
           (let ((p (fn-xc-find (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) t kind file eoff elen a b c d
                                trailer start fn-xcs)))
             (and (equal (mv-nth 0 (fn-xc-install-call)) :present)
                  (equal (mv-nth 1 (fn-xc-install-call)) p)
                  (equal (mv-nth 2 (fn-xc-install-call)) nil)
                  (equal (mv-nth 3 (fn-xc-install-call)) (mv-nth 1 (fn-xc-touch p fn-xcs fn-xcc)))
                  (equal (mv-nth 4 (fn-xc-install-call)) (mv-nth 2 (fn-xc-touch p fn-xcs fn-xcc))))))
  :hints (("Goal" :in-theory (enable fn-xc-install fn-xc-install-okp))))

(defthm fn-xc-install-when-free
  (implies (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc)
                (fn-xc-install-okp kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)
                (< (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc))
                (not (fn-xc-find (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) t kind file eoff elen a b c d
                                 trailer start fn-xcs))
                (fn-xc-find-free (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) fn-xcs)
                (not (equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) :duplicate)))
           (let ((f (fn-xc-find-free (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) fn-xcs)))
             (and (equal (mv-nth 0 (fn-xc-install-call)) :installed)
                  (equal (mv-nth 1 (fn-xc-install-call)) f)
                  (equal (mv-nth 2 (fn-xc-install-call)) nil)
                  (equal (mv-nth 3 (fn-xc-install-call))
                         (fn-xc-write f kind tokp tid tcid file eoff elen a b c d start trailer
                                      (fn-xc-tick fn-xcc) fn-xcs))
                  (equal (mv-nth 4 (fn-xc-install-call)) (mv-nth 1 (fn-xc-next-stamp fn-xcc))))))
  :hints (("Goal" :in-theory (enable fn-xc-install fn-xc-install-okp)
                  :use (fn-xc-next-stamp-results
                        (:instance fn-xc-find-free-is-free (i (fn-xc-lo kind fn-xcc)) (hi (fn-xc-hi kind fn-xcc)))))))

(defthm fn-xc-install-when-full
  (implies (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc)
                (fn-xc-install-okp kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)
                (< (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc))
                (not (fn-xc-find (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) t kind file eoff elen a b c d
                                 trailer start fn-xcs))
                (not (fn-xc-find-free (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) fn-xcs))
                (not (equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) :duplicate)))
           (let ((v (fn-xc-lru (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) nil fn-xcs)))
             (and (equal (mv-nth 0 (fn-xc-install-call)) :replaced)
                  (equal (mv-nth 1 (fn-xc-install-call)) v)
                  (equal (mv-nth 2 (fn-xc-install-call)) (fn-xc-slot-token v fn-xcs))
                  (equal (mv-nth 3 (fn-xc-install-call))
                         (fn-xc-write v kind tokp tid tcid file eoff elen a b c d start trailer
                                      (fn-xc-tick fn-xcc) fn-xcs))
                  (equal (mv-nth 4 (fn-xc-install-call)) (mv-nth 1 (fn-xc-next-stamp fn-xcc))))))
  :hints (("Goal" :in-theory (enable fn-xc-install fn-xc-install-okp)
                  :use (fn-xc-next-stamp-results))))

(in-theory (disable fn-xc-install fn-xc-lookup))

(defthm fn-xc-find-prefix
  (implies (and (natp lo) (natp v) (natp hi) (<= v hi)
                (not (fn-xc-find lo hi exactp kind file eoff elen a b c d trailer pos fn-xcs)))
           (not (fn-xc-find lo v exactp kind file eoff elen a b c d trailer pos fn-xcs)))
  :hints (("Goal" :use ((:instance fn-xc-find-bounds (i lo) (hi v))
                        (:instance fn-xc-find-matches (i lo) (hi v))
                        (:instance fn-xc-find-complete (i lo) (j (fn-xc-find lo v exactp kind file eoff elen a b c d trailer pos fn-xcs)))))))

; A write at V leaves the scan of the slots below V as it was.
(defthm fn-xc-find-below-write
  (implies (and (fn-xc-write-okp v wk tokp tid tcid wfile weoff welen wa wb wc wd wstart wtrailer stamp fn-xcs)
                (natp i) (natp hi) (<= hi v))
           (equal (fn-xc-find i hi exactp kind file eoff elen a b c d trailer pos
                              (fn-xc-write v wk tokp tid tcid wfile weoff welen wa wb wc wd wstart wtrailer stamp fn-xcs))
                  (fn-xc-find i hi exactp kind file eoff elen a b c d trailer pos fn-xcs)))
  :hints (("Goal" :in-theory (enable fn-xc-find)
                  :induct (fn-xc-find i hi exactp kind file eoff elen a b c d trailer pos fn-xcs))))

; A touch leaves every scan as it was.
(defthm fn-xc-find-after-touch
  (implies (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc) (fn-xc-readyp fn-xcs fn-xcc)
                (natp p) (< p (fn-xcs-count fn-xcs)) (not (equal (fn-xcs-get-kind p fn-xcs) 0))
                (natp i))
           (equal (fn-xc-find i hi exactp kind file eoff elen a b c d trailer pos
                              (mv-nth 1 (fn-xc-touch p fn-xcs fn-xcc)))
                  (fn-xc-find i hi exactp kind file eoff elen a b c d trailer pos fn-xcs)))
  :hints (("Goal" :in-theory (enable fn-xc-find)
                  :induct (fn-xc-find i hi exactp kind file eoff elen a b c d trailer pos fn-xcs))))

; The first slot at or after I that matches, when the slots before V do not and V does.
(defthm fn-xc-find-first-match-is-v
  (implies (and (natp lo) (natp hi) (natp v) (<= lo v) (< v hi)
                (fn-xc-slot-matchp v exactp kind file eoff elen a b c d trailer pos fn-xcs)
                (not (fn-xc-find lo v exactp kind file eoff elen a b c d trailer pos fn-xcs)))
           (equal (fn-xc-find lo hi exactp kind file eoff elen a b c d trailer pos fn-xcs) v))
  :hints (("Goal" :in-theory (enable fn-xc-find)
                  :induct (fn-xc-find lo hi exactp kind file eoff elen a b c d trailer pos fn-xcs))))

; A use of a held slot changes no answer of any lookup.
(defthm fn-xc-lookup-after-touch
  (implies (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc) (fn-xc-readyp fn-xcs fn-xcc)
                (natp p) (< p (fn-xcs-count fn-xcs)) (not (equal (fn-xcs-get-kind p fn-xcs) 0))
                (natp from))
           (equal (fn-xc-lookup from kind file eoff elen a b c d trailer pos
                                (mv-nth 1 (fn-xc-touch p fn-xcs fn-xcc)) (mv-nth 2 (fn-xc-touch p fn-xcs fn-xcc)))
                  (fn-xc-lookup from kind file eoff elen a b c d trailer pos fn-xcs fn-xcc)))
  :hints (("Goal" :in-theory (enable fn-xc-lookup)
                  :use (fn-xc-touch-effects
                        (:instance fn-xc-geometry-of-lo-hi (c2 (mv-nth 2 (fn-xc-touch p fn-xcs fn-xcc))))
                        (:instance fn-xc-find-after-touch
                                   (i (if (< from (fn-xc-lo kind fn-xcc)) (fn-xc-lo kind fn-xcc) from))
                                   (hi (fn-xc-hi kind fn-xcc)) (exactp (equal kind 1)))))))

; A fresh write of the key at V (no slot of the region held it) makes it the answer.
(defthm fn-xc-lookup-after-write
  (implies (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc) (fn-xc-readyp fn-xcs fn-xcc)
                (fn-xccp c2) (fn-xc-cellsp c2)
                (equal (fn-xc-ne c2) (fn-xc-ne fn-xcc)) (equal (fn-xc-nw c2) (fn-xc-nw fn-xcc))
                (fn-xc-write-okp v kind tokp tid tcid file eoff elen a b c d start trailer stamp fn-xcs)
                (member-equal kind '(1 2 3)) (natp start)
                (<= (fn-xc-lo kind fn-xcc) v) (< v (fn-xc-hi kind fn-xcc))
                (not (fn-xc-find (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) t kind file eoff elen a b c d
                                 trailer start fn-xcs)))
           (let ((s2 (fn-xc-write v kind tokp tid tcid file eoff elen a b c d start trailer stamp fn-xcs)))
             (and (equal (mv-nth 0 (fn-xc-lookup 0 kind file eoff elen a b c d trailer start s2 c2)) :hit)
                  (implies (equal kind 1)
                           (equal (mv-nth 1 (fn-xc-lookup 0 kind file eoff elen a b c d trailer start s2 c2)) v)))))
  :hints (("Goal" :in-theory (e/d (fn-xc-lookup) (fn-xc-lookup-finds-every-held-descriptor fn-xc-find-first-match-is-v))
                  :use ((:instance fn-xc-geometry-of-lo-hi)
                        (:instance fn-xc-readyp-transfer (s2 (fn-xc-write v kind tokp tid tcid file eoff elen a b c d start trailer stamp fn-xcs)))
                        (:instance fn-xc-find-prefix (lo (fn-xc-lo kind fn-xcc)) (hi (fn-xc-hi kind fn-xcc)) (exactp t) (pos start))
                        (:instance fn-xc-find-below-write (i (fn-xc-lo kind fn-xcc)) (hi v) (exactp t) (pos start)
                                   (wk kind) (wfile file) (weoff eoff) (welen elen) (wa a) (wb b) (wc c) (wd d)
                                   (wstart start) (wtrailer trailer))
                        (:instance fn-xc-find-first-match-is-v (lo (fn-xc-lo kind fn-xcc)) (hi (fn-xc-hi kind fn-xcc))
                                   (exactp t) (pos start)
                                   (fn-xcs (fn-xc-write v kind tokp tid tcid file eoff elen a b c d start trailer stamp fn-xcs)))
                        (:instance fn-xc-lookup-finds-every-held-descriptor (j v) (pos start)
                                   (fn-xcc c2)
                                   (fn-xcs (fn-xc-write v kind tokp tid tcid file eoff elen a b c d start trailer stamp fn-xcs)))))))

(defmacro fn-xc-case-hyps ()
  '(and (fn-xcsp fn-xcs) (fn-xccp fn-xcc)
        (fn-xc-install-okp kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)
        (< (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc))))

(defmacro fn-xc-key-find-nil ()
  '(not (fn-xc-find (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) t kind file eoff elen a b c d
                    trailer start fn-xcs)))

(defmacro fn-xc-lookup-after-install ()
  '(let ((r (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)))
     (and (equal (mv-nth 0 (fn-xc-lookup 0 kind file eoff elen a b c d trailer start (mv-nth 3 r) (mv-nth 4 r))) :hit)
          (implies (equal kind 1)
                   (equal (mv-nth 1 (fn-xc-lookup 0 kind file eoff elen a b c d trailer start (mv-nth 3 r) (mv-nth 4 r)))
                          (mv-nth 1 r))))))


; The first lookup is the scan of the whole region.
(defthm fn-xc-lookup-is-find
  (implies (and (fn-xccp fn-xcc) (fn-xc-readyp fn-xcs fn-xcc) (member-equal kind '(1 2 3)))
           (equal (fn-xc-lookup 0 kind file eoff elen a b c d trailer pos fn-xcs fn-xcc)
                  (let ((slot (fn-xc-find (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) (equal kind 1)
                                          kind file eoff elen a b c d trailer pos fn-xcs)))
                    (if slot (list :hit slot) (list :miss nil)))))
  :hints (("Goal" :in-theory (enable fn-xc-lookup))))

(defthm fn-xc-install-then-lookup-hits-present
  (implies (and (fn-xc-case-hyps)
                (fn-xc-find (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) t kind file eoff elen a b c d
                            trailer start fn-xcs)
                (not (equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) :duplicate)))
           (fn-xc-lookup-after-install))
  :hints (("Goal" :in-theory (e/d (fn-xc-install-okp) nil)
                  :use (fn-xc-install-when-present
                        (:instance fn-xc-find-bounds (i (fn-xc-lo kind fn-xcc)) (hi (fn-xc-hi kind fn-xcc))
                                   (exactp t) (pos start))
                        (:instance fn-xc-find-matches (i (fn-xc-lo kind fn-xcc)) (hi (fn-xc-hi kind fn-xcc))
                                   (exactp t) (pos start))
                        (:instance fn-xc-lookup-after-touch
                                   (p (fn-xc-find (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) t kind file eoff elen
                                                  a b c d trailer start fn-xcs))
                                   (from 0) (pos start))
                        (:instance fn-xc-matchp-is-live (exactp t) (pos start)
                                   (i (fn-xc-find (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) t kind file eoff elen
                                                  a b c d trailer start fn-xcs)))
                        (:instance fn-xc-find-complete (i (fn-xc-lo kind fn-xcc)) (hi (fn-xc-hi kind fn-xcc))
                                   (exactp nil) (pos start)
                                   (j (fn-xc-find (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) t kind file eoff elen
                                                  a b c d trailer start fn-xcs)))
                        (:instance fn-xc-lookup-is-find (pos start))))))

(defthm fn-xc-install-then-lookup-hits-free
  (implies (and (fn-xc-case-hyps) (fn-xc-key-find-nil)
                (fn-xc-find-free (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) fn-xcs)
                (not (equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) :duplicate)))
           (fn-xc-lookup-after-install))
  :hints (("Goal" :in-theory (e/d (fn-xc-install-okp fn-xc-write-okp) nil)
                  :use (fn-xc-install-when-free
                        fn-xc-next-stamp-geometry
                        fn-xc-tick-is-u64
                        (:instance fn-xc-find-free-is-free (i (fn-xc-lo kind fn-xcc)) (hi (fn-xc-hi kind fn-xcc)))
                        (:instance fn-xc-lookup-after-write
                                   (v (fn-xc-find-free (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) fn-xcs))
                                   (stamp (fn-xc-tick fn-xcc))
                                   (c2 (mv-nth 1 (fn-xc-next-stamp fn-xcc))))))))

(defthm fn-xc-install-then-lookup-hits-full
  (implies (and (fn-xc-case-hyps) (fn-xc-key-find-nil)
                (not (fn-xc-find-free (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) fn-xcs))
                (not (equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) :duplicate)))
           (fn-xc-lookup-after-install))
  :hints (("Goal" :in-theory (e/d (fn-xc-install-okp fn-xc-write-okp) nil)
                  :use (fn-xc-install-when-full
                        fn-xc-next-stamp-geometry
                        fn-xc-tick-is-u64
                        (:instance fn-xc-lru-is-least (i (fn-xc-lo kind fn-xcc)) (hi (fn-xc-hi kind fn-xcc))
                                   (best nil) (j (fn-xc-lo kind fn-xcc)))
                        (:instance fn-xc-find-free-complete (i (fn-xc-lo kind fn-xcc)) (j (fn-xc-lo kind fn-xcc))
                                   (hi (fn-xc-hi kind fn-xcc)))
                        (:instance fn-xc-lookup-after-write
                                   (v (fn-xc-lru (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) nil fn-xcs))
                                   (stamp (fn-xc-tick fn-xcc))
                                   (c2 (mv-nth 1 (fn-xc-next-stamp fn-xcc))))))))

(defthm fn-xc-install-nonempty
  (implies (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc)
                (fn-xc-install-okp kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)
                (not (equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer
                                                     fn-xcs fn-xcc))
                            :refused)))
           (< (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc)))
  :rule-classes nil
  :hints (("Goal" :use (fn-xc-install-placement) :in-theory (disable fn-xc-install-placement))))

; TEETH for the trailer column (the first native run refused every window): a
; raw window token of the shape fn-prw-admit builds, (:window TICKET FILE EOFF
; ELEN POFF PLEN OFFSET TRAILER), whose trailer is the packed commitment of 32
; octets, is accepted by a ready table with a window region.
(defthm fn-xc-install-window-accepts-a-descriptor-trailer
  (implies (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc) (fn-xc-readyp fn-xcs fn-xcc)
                (< 0 (fn-xc-nw fn-xcc))
                (unsigned-byte-p 64 tid) (unsigned-byte-p 64 file) (unsigned-byte-p 64 eoff)
                (unsigned-byte-p 64 elen) (unsigned-byte-p 64 poff) (unsigned-byte-p 64 plen)
                (unsigned-byte-p 64 offset)
                (fn-bch-octetsp xs) (equal (len xs) *fn-frame-trailer-octets*))
           (not (equal (mv-nth 0 (fn-xc-install-window
                                  (list :window tid file eoff elen poff plen offset (fn-bch-pack xs))
                                  fn-xcs fn-xcc))
                       :refused)))
  :hints (("Goal" :in-theory (e/d (fn-xc-install-window fn-xc-lo fn-xc-hi fn-xc-install-okp)
                                  (fn-xc-install-placement))
                  :use ((:instance fn-xc-trailer-column-holds-the-frame-trailer-commitment)
                        (:instance fn-xc-install-placement (kind 2) (tokp t) (tcid 0) (a poff) (b plen)
                                   (c 0) (d 0) (start offset) (trailer (fn-bch-pack xs)))))))

; KEYSTONE 2 (install then lookup).  Whatever an install does but refuse, the
; key is then found; a whole entry is found in exactly the slot the install
; answered.  (A refused install is the empty region: see fn-xc-install-placement.)
(defthm fn-xc-install-then-lookup-hits
  (implies (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc)
                (fn-xc-install-okp kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)
                (not (equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer
                                                      fn-xcs fn-xcc))
                            :refused))
                (not (equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) :duplicate)))
           (fn-xc-lookup-after-install))
  :hints (("Goal" :do-not-induct t
                  :use (fn-xc-install-nonempty fn-xc-install-then-lookup-hits-present
                        fn-xc-install-then-lookup-hits-free fn-xc-install-then-lookup-hits-full)
                  :in-theory (disable fn-xc-install-placement fn-xc-lookup-is-find
                                      fn-xc-install-then-lookup-hits-present fn-xc-install-then-lookup-hits-free
                                      fn-xc-install-then-lookup-hits-full)
                  :cases ((fn-xc-find (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) t kind file eoff elen a b c d
                                      trailer start fn-xcs)
                          (fn-xc-find-free (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) fn-xcs)))))

; =============================================================================
; Occupancy.  The table has NE + NW rows and never gains one, so the live
; slots of a region number at most the region's size, whatever the profile's N.
; GEN: def-loop :step
(defun fn-xc-live-count (i hi fn-xcs)
  (declare (xargs :stobjs fn-xcs
                  :guard (and (fn-xcsp fn-xcs) (natp i) (natp hi) (<= hi (fn-xcs-count fn-xcs)))
                  :measure (nfix (- hi i))))
  (if (and (natp i) (natp hi) (< i hi))
      (+ (if (equal (fn-xcs-get-kind i fn-xcs) 0) 0 1)
         (fn-xc-live-count (1+ i) hi fn-xcs))
    0))

(defthm fn-xc-occupancy-bounded
  (implies (and (natp i) (natp hi) (<= i hi))
           (<= (fn-xc-live-count i hi fn-xcs) (- hi i)))
  :hints (("Goal" :in-theory (enable fn-xc-live-count)
                  :induct (fn-xc-live-count i hi fn-xcs)))
  :rule-classes (:rewrite :linear))

(defthm fn-xc-region-occupancy-is-at-most-the-profile-figure
  (implies (and (fn-xccp fn-xcc) (fn-xc-readyp fn-xcs fn-xcc))
           (and (<= (fn-xc-live-count 0 (fn-xc-ne fn-xcc) fn-xcs) (fn-xc-ne fn-xcc))
                (<= (fn-xc-live-count (fn-xc-ne fn-xcc) (+ (fn-xc-ne fn-xcc) (fn-xc-nw fn-xcc)) fn-xcs)
                    (fn-xc-nw fn-xcc))
                (<= (fn-xc-live-count 0 (fn-xcs-count fn-xcs) fn-xcs)
                    (+ (fn-xc-ne fn-xcc) (fn-xc-nw fn-xcc)))))
  :hints (("Goal" :use ((:instance fn-xc-occupancy-bounded (i 0) (hi (fn-xc-ne fn-xcc)))
                        (:instance fn-xc-occupancy-bounded (i (fn-xc-ne fn-xcc))
                                   (hi (+ (fn-xc-ne fn-xcc) (fn-xc-nw fn-xcc))))
                        (:instance fn-xc-occupancy-bounded (i 0) (hi (fn-xcs-count fn-xcs))))
                  :in-theory (disable fn-xc-occupancy-bounded))))

; A write at V changes the count by what it makes live less what it frees.
(defthm fn-xc-live-count-after-write
  (implies (and (fn-xc-write-okp v wk tokp tid tcid wfile weoff welen wa wb wc wd wstart wtrailer stamp fn-xcs)
                (natp i) (natp hi))
           (equal (fn-xc-live-count i hi (fn-xc-write v wk tokp tid tcid wfile weoff welen wa wb wc wd wstart wtrailer
                                                       stamp fn-xcs))
                  (if (and (<= i v) (< v hi))
                      (+ (fn-xc-live-count i hi fn-xcs)
                         (if (equal wk 0) 0 1)
                         (if (equal (fn-xcs-get-kind v fn-xcs) 0) 0 -1))
                    (fn-xc-live-count i hi fn-xcs))))
  :hints (("Goal" :in-theory (enable fn-xc-live-count)
                  :induct (fn-xc-live-count i hi fn-xcs))))

(defthm fn-xc-live-count-after-touch
  (implies (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc) (fn-xc-readyp fn-xcs fn-xcc)
                (natp p) (< p (fn-xcs-count fn-xcs)) (not (equal (fn-xcs-get-kind p fn-xcs) 0))
                (natp i) (natp hi))
           (equal (fn-xc-live-count i hi (mv-nth 1 (fn-xc-touch p fn-xcs fn-xcc)))
                  (fn-xc-live-count i hi fn-xcs)))
  :hints (("Goal" :in-theory (enable fn-xc-live-count fn-xc-touch)
                  :induct (fn-xc-live-count i hi fn-xcs))))

; A free slot in the range leaves room.
(defthm fn-xc-occupancy-below-the-bound-when-a-slot-is-free
  (implies (and (natp i) (natp j) (natp hi) (<= i j) (< j hi)
                (equal (fn-xcs-get-kind j fn-xcs) 0))
           (<= (+ 1 (fn-xc-live-count i hi fn-xcs)) (- hi i)))
  :hints (("Goal" :in-theory (enable fn-xc-live-count)
                  :induct (fn-xc-live-count i hi fn-xcs))))

(defmacro fn-xc-install-hyps ()
  '(and (fn-xcsp fn-xcs) (fn-xccp fn-xcc)
        (fn-xc-install-okp kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)
        (not (equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc))
                    :refused))
        (not (equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) :duplicate))))


; KEYSTONE 3 (the bound).  An install that is not refused adds a live slot
; exactly when a free slot took it, and the region never holds more than it has.
(defthm fn-xc-install-occupancy
  (implies (fn-xc-install-hyps)
           (let ((n0 (fn-xc-live-count (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) fn-xcs))
                 (n1 (fn-xc-live-count (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) (mv-nth 3 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)))))
             (and (equal n1 (if (equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) :installed) (+ 1 n0) n0))
                  (<= n1 (- (fn-xc-hi kind fn-xcc) (fn-xc-lo kind fn-xcc))))))
  :hints (("Goal" :do-not-induct t
                  :use (fn-xc-install-nonempty
                        (:instance fn-xc-install-when-present) (:instance fn-xc-install-when-free)
                        (:instance fn-xc-install-when-full)
                        (:instance fn-xc-find-free-is-free (i (fn-xc-lo kind fn-xcc)) (hi (fn-xc-hi kind fn-xcc)))
                        (:instance fn-xc-find-bounds (i (fn-xc-lo kind fn-xcc)) (hi (fn-xc-hi kind fn-xcc))
                                   (exactp t) (pos start))
                        (:instance fn-xc-find-matches (i (fn-xc-lo kind fn-xcc)) (hi (fn-xc-hi kind fn-xcc))
                                   (exactp t) (pos start))
                        (:instance fn-xc-matchp-is-live (exactp t) (pos start)
                                   (i (fn-xc-find (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) t kind file eoff elen
                                                  a b c d trailer start fn-xcs)))
                        (:instance fn-xc-occupancy-below-the-bound-when-a-slot-is-free
                                   (i (fn-xc-lo kind fn-xcc)) (hi (fn-xc-hi kind fn-xcc))
                                   (j (fn-xc-find-free (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) fn-xcs)))
                        (:instance fn-xc-lru-is-least (i (fn-xc-lo kind fn-xcc)) (hi (fn-xc-hi kind fn-xcc))
                                   (best nil) (j (fn-xc-lo kind fn-xcc)))
                        (:instance fn-xc-find-free-complete (i (fn-xc-lo kind fn-xcc)) (j (fn-xc-lo kind fn-xcc))
                                   (hi (fn-xc-hi kind fn-xcc))))
                  :in-theory (e/d (fn-xc-install-okp fn-xc-write-okp)
                                  (fn-xc-install-when-present fn-xc-install-when-free fn-xc-install-when-full
                                   fn-xc-install-placement fn-xc-lookup-is-find))
                  :cases ((fn-xc-find (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) t kind file eoff elen a b c d
                                      trailer start fn-xcs)
                          (fn-xc-find-free (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) fn-xcs)))))

; =============================================================================
; What each outcome of an install does to the table and what it hands back.
; In all three, every slot but the answered one is untouched.

(defthm fn-xc-install-present
  (implies (and (fn-xc-case-hyps)
                (fn-xc-find (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) t kind file eoff elen a b c d
                            trailer start fn-xcs)
                (not (equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) :duplicate)))
           (let ((v (mv-nth 1 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc))))
             (and (equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) :present)
                  (equal (mv-nth 2 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) nil)
                  (fn-xc-slot-matchp v t kind file eoff elen a b c d trailer start fn-xcs)
                  (implies (and (natp j) (not (equal j v)))
                           (equal (nth j (mv-nth 3 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc))) (nth j fn-xcs))))))
  :hints (("Goal" :in-theory (e/d (fn-xc-install-okp) (fn-xc-install-when-present))
                  :use (fn-xc-install-when-present
                        (:instance fn-xc-find-bounds (i (fn-xc-lo kind fn-xcc)) (hi (fn-xc-hi kind fn-xcc))
                                   (exactp t) (pos start))
                        (:instance fn-xc-find-matches (i (fn-xc-lo kind fn-xcc)) (hi (fn-xc-hi kind fn-xcc))
                                   (exactp t) (pos start))
                        (:instance fn-xc-matchp-is-live (exactp t) (pos start)
                                   (i (fn-xc-find (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) t kind file eoff elen
                                                  a b c d trailer start fn-xcs)))
                        (:instance fn-xc-touch-frame
                                   (i (fn-xc-find (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) t kind file eoff elen
                                                  a b c d trailer start fn-xcs)))))))

(defthm fn-xc-install-fills-a-free-slot
  (implies (and (fn-xc-case-hyps) (fn-xc-key-find-nil)
                (fn-xc-find-free (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) fn-xcs)
                (not (equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) :duplicate)))
           (let ((v (mv-nth 1 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc))))
             (and (equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) :installed)
                  (equal (mv-nth 2 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) nil)
                  (equal (fn-xcs-get-kind v fn-xcs) 0)
                  (implies (and (natp j) (not (equal j v)))
                           (equal (nth j (mv-nth 3 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc))) (nth j fn-xcs))))))
  :hints (("Goal" :in-theory (e/d (fn-xc-install-okp fn-xc-write-okp) (fn-xc-install-when-free))
                  :use (fn-xc-install-when-free fn-xc-tick-is-u64
                        (:instance fn-xc-find-free-is-free (i (fn-xc-lo kind fn-xcc)) (hi (fn-xc-hi kind fn-xcc)))
                        (:instance fn-xc-write-frame
                                   (i (fn-xc-find-free (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) fn-xcs))
                                   (stamp (fn-xc-tick fn-xcc)))))))

; KEYSTONE 4 (eviction).  A full region gives up its least recently used slot,
; and hands back that slot's own token: the charge the caller releases.
(defthm fn-xc-install-evicts-the-least-recently-used
  (implies (and (fn-xc-case-hyps) (fn-xc-key-find-nil)
                (not (fn-xc-find-free (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) fn-xcs))
                (not (equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) :duplicate)))
           (let ((v (mv-nth 1 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc))))
             (and (equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) :replaced)
                  (natp v) (<= (fn-xc-lo kind fn-xcc) v) (< v (fn-xc-hi kind fn-xcc))
                  (not (equal (fn-xcs-get-kind v fn-xcs) 0))
                  (equal (mv-nth 2 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) (fn-xc-slot-token v fn-xcs))
                  ; every slot of the region was live, and none is older than the victim
                  (implies (and (natp j) (<= (fn-xc-lo kind fn-xcc) j) (< j (fn-xc-hi kind fn-xcc)))
                           (and (not (equal (fn-xcs-get-kind j fn-xcs) 0))
                                (<= (fn-xcs-get-stamp v fn-xcs) (fn-xcs-get-stamp j fn-xcs))))
                  (implies (and (natp j) (not (equal j v)))
                           (equal (nth j (mv-nth 3 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc))) (nth j fn-xcs))))))
  :hints (("Goal" :in-theory (e/d (fn-xc-install-okp fn-xc-write-okp) (fn-xc-install-when-full))
                  :use (fn-xc-install-when-full fn-xc-tick-is-u64
                        (:instance fn-xc-lru-is-least (i (fn-xc-lo kind fn-xcc)) (hi (fn-xc-hi kind fn-xcc))
                                   (best nil) (j (fn-xc-lo kind fn-xcc)))
                        (:instance fn-xc-lru-is-least (i (fn-xc-lo kind fn-xcc)) (hi (fn-xc-hi kind fn-xcc))
                                   (best nil))
                        (:instance fn-xc-find-free-complete (i (fn-xc-lo kind fn-xcc)) (hi (fn-xc-hi kind fn-xcc)))
                        (:instance fn-xc-write-frame
                                   (i (fn-xc-lru (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) nil fn-xcs))
                                   (stamp (fn-xc-tick fn-xcc)))))))

; =============================================================================
; Leaving: a retiring file, the end of recovery and pool pressure.

(defthm fn-xcs-set-kind-reads
  (implies (and (fn-xcsp fn-xcs) (natp i) (< i (fn-xcs-count fn-xcs)) (natp j))
           (equal (fn-xcs-get-kind j (fn-xcs-set-kind i v fn-xcs))
                  (if (equal j i) v (fn-xcs-get-kind j fn-xcs))))
  :hints (("Goal" :in-theory (enable fn-xcs-set-kind-is-update-nth fn-xcs-get-kind-is-nth
                                     fn-xcs-count-is-len fn-xcsp-is-seq-p))))

(defthm fn-xcs-set-kind-other-columns
  (implies (and (fn-xcsp fn-xcs) (natp i) (< i (fn-xcs-count fn-xcs)) (natp j))
           (and (equal (fn-xcs-get-file j (fn-xcs-set-kind i v fn-xcs)) (fn-xcs-get-file j fn-xcs))
                (equal (fn-xcs-get-tokp j (fn-xcs-set-kind i v fn-xcs)) (fn-xcs-get-tokp j fn-xcs))))
  :hints (("Goal" :in-theory (enable fn-xcs-set-kind-is-update-nth fn-xcs-get-file-is-nth fn-xcs-get-tokp-is-nth
                                     fn-xcs-count-is-len fn-xcsp-is-seq-p))))

(defthm fn-xcs-set-kind-frame
  (implies (and (fn-xcsp fn-xcs) (natp i) (< i (fn-xcs-count fn-xcs)) (natp j) (not (equal j i)))
           (equal (nth j (fn-xcs-set-kind i v fn-xcs)) (nth j fn-xcs)))
  :hints (("Goal" :in-theory (enable fn-xcs-set-kind-is-update-nth))))

(defthm fn-xc-live-count-after-free
  (implies (and (fn-xcsp fn-xcs) (natp i) (< i (fn-xcs-count fn-xcs)) (natp a) (natp b)
                (not (equal (fn-xcs-get-kind i fn-xcs) 0)))
           (equal (fn-xc-live-count a b (fn-xcs-set-kind i 0 fn-xcs))
                  (if (and (<= a i) (< i b))
                      (+ -1 (fn-xc-live-count a b fn-xcs))
                    (fn-xc-live-count a b fn-xcs))))
  :hints (("Goal" :in-theory (enable fn-xc-live-count)
                  :induct (fn-xc-live-count a b fn-xcs))))

(defthm fn-xc-free-effects
  (implies (and (fn-xcsp fn-xcs) (natp i) (< i (fn-xcs-count fn-xcs))
                (not (equal (fn-xcs-get-kind i fn-xcs) 0)))
           (let ((s2 (mv-nth 2 (fn-xc-free i fn-xcs))))
             (and (equal (mv-nth 0 (fn-xc-free i fn-xcs)) :freed)
                  ; the token is the slot's own: the charge to release
                  (equal (mv-nth 1 (fn-xc-free i fn-xcs)) (fn-xc-slot-token i fn-xcs))
                  (fn-xcsp s2) (equal (fn-xcs-count s2) (fn-xcs-count fn-xcs))
                  (equal (fn-xcs-get-kind i s2) 0)
                  (implies (and (natp j) (not (equal j i))) (equal (nth j s2) (nth j fn-xcs)))
                  (implies (and (natp a) (natp b))
                           (equal (fn-xc-live-count a b s2)
                                  (if (and (<= a i) (< i b))
                                      (+ -1 (fn-xc-live-count a b fn-xcs))
                                    (fn-xc-live-count a b fn-xcs)))))))
  :hints (("Goal" :in-theory (e/d (fn-xc-free) (fn-xcs-set-kind-reads fn-xc-live-count-after-free))
                  :use ((:instance fn-xcs-set-kind-keeps-well-formed (v 0))
                        (:instance fn-xcs-set-kind-keeps-count (v 0))
                        (:instance fn-xcs-set-kind-reads (v 0) (j i))
                        (:instance fn-xc-live-count-after-free)))))

(defthm fn-xc-free-of-a-free-slot-is-stale
  (implies (and (fn-xcsp fn-xcs) (natp i) (< i (fn-xcs-count fn-xcs))
                (equal (fn-xcs-get-kind i fn-xcs) 0))
           (equal (fn-xc-free i fn-xcs) (list :stale nil fn-xcs)))
  :hints (("Goal" :in-theory (enable fn-xc-free))))

; A freed slot answers no lookup.
(defthm fn-xc-freed-slot-matches-nothing
  (implies (and (fn-xcsp fn-xcs) (natp i) (< i (fn-xcs-count fn-xcs))
                (not (equal kind 0)) (natp j)
                (not (equal (fn-xcs-get-kind i fn-xcs) 0)))
           (not (fn-xc-slot-matchp i exactp kind file eoff elen a b c d trailer pos
                                   (mv-nth 2 (fn-xc-free i fn-xcs)))))
  :hints (("Goal" :in-theory (enable fn-xc-free fn-xc-slot-matchp fn-xcs-get-kind-is-nth
                                     fn-xcs-set-kind-is-update-nth fn-xcs-count-is-len fn-xcsp-is-seq-p)
                  :use ((:instance fn-xc-row-typed (fn-xcs fn-xcs))))))

; --- the next live slot (of a file) is the first one
(defthm fn-xc-next-is-live-and-first
  (implies (and (fn-xcsp fn-xcs) (natp from) (fn-xc-next from file fn-xcs))
           (let ((r (fn-xc-next from file fn-xcs)))
             (and (natp r) (<= from r) (< r (fn-xcs-count fn-xcs))
                  (not (equal (fn-xcs-get-kind r fn-xcs) 0))
                  (or (null file) (equal (fn-xcs-get-file r fn-xcs) file))
                  (implies (and (natp j) (<= from j) (< j r))
                           (or (equal (fn-xcs-get-kind j fn-xcs) 0)
                               (and file (not (equal (fn-xcs-get-file j fn-xcs) file))))))))
  :hints (("Goal" :in-theory (enable fn-xc-next) :induct (fn-xc-next from file fn-xcs))))

(defthm fn-xc-next-finds-every-held-slot
  (implies (and (fn-xcsp fn-xcs) (natp from) (natp j) (<= from j) (< j (fn-xcs-count fn-xcs))
                (not (equal (fn-xcs-get-kind j fn-xcs) 0))
                (or (null file) (equal (fn-xcs-get-file j fn-xcs) file)))
           (and (fn-xc-next from file fn-xcs) (<= (fn-xc-next from file fn-xcs) j)))
  :hints (("Goal" :in-theory (enable fn-xc-next) :induct (fn-xc-next from file fn-xcs))))

;; KEYSTONE 5 (pressure).  Under pool pressure the least recently used whole
;; entry yields; if there are none, the least recently used window; the caller
;; releases exactly the token it is handed.
(defmacro fn-xc-yield-ready ()
  '(and (fn-xcsp fn-xcs) (fn-xccp fn-xcc) (fn-xc-readyp fn-xcs fn-xcc)))

(defthm fn-xc-yield-an-entry
  (implies (and (fn-xc-yield-ready)
                (fn-xc-lru (fn-xc-lo 1 fn-xcc) (fn-xc-hi 1 fn-xcc) nil fn-xcs))
           (let* ((r (fn-xc-yield fn-xcs fn-xcc)) (v (mv-nth 1 r)) (s2 (mv-nth 3 r)))
             (and (equal (mv-nth 0 r) :yielded)
                  (natp v) (<= (fn-xc-lo 1 fn-xcc) v) (< v (fn-xc-hi 1 fn-xcc))
                  (not (equal (fn-xcs-get-kind v fn-xcs) 0))
                  (equal (mv-nth 2 r) (fn-xc-slot-token v fn-xcs))
                  (equal (fn-xcs-get-kind v s2) 0)
                  (equal (fn-xcs-count s2) (fn-xcs-count fn-xcs))
                  (implies (and (natp j) (not (equal j v))) (equal (nth j s2) (nth j fn-xcs)))
                  (implies (and (natp j) (<= (fn-xc-lo 1 fn-xcc) j) (< j (fn-xc-hi 1 fn-xcc))
                                (not (equal (fn-xcs-get-kind j fn-xcs) 0)))
                           (<= (fn-xcs-get-stamp v fn-xcs) (fn-xcs-get-stamp j fn-xcs))))))
  :hints (("Goal" :in-theory (e/d (fn-xc-yield) (fn-xc-free-effects))
                  :do-not-induct t
                  :use ((:instance fn-xc-lru-is-least (i (fn-xc-lo 1 fn-xcc)) (hi (fn-xc-hi 1 fn-xcc)) (best nil))
                        (:instance fn-xc-free-effects
                                   (i (fn-xc-lru (fn-xc-lo 1 fn-xcc) (fn-xc-hi 1 fn-xcc) nil fn-xcs)))))))

(defthm fn-xc-yield-a-window-when-no-entry
  (implies (and (fn-xc-yield-ready)
                (not (fn-xc-lru (fn-xc-lo 1 fn-xcc) (fn-xc-hi 1 fn-xcc) nil fn-xcs))
                (fn-xc-lru (fn-xc-lo 2 fn-xcc) (fn-xc-hi 2 fn-xcc) nil fn-xcs))
           (let* ((r (fn-xc-yield fn-xcs fn-xcc)) (v (mv-nth 1 r)) (s2 (mv-nth 3 r)))
             (and (equal (mv-nth 0 r) :yielded)
                  (natp v) (<= (fn-xc-lo 2 fn-xcc) v) (< v (fn-xc-hi 2 fn-xcc))
                  (not (equal (fn-xcs-get-kind v fn-xcs) 0))
                  (equal (mv-nth 2 r) (fn-xc-slot-token v fn-xcs))
                  (equal (fn-xcs-get-kind v s2) 0)
                  (implies (and (natp j) (not (equal j v))) (equal (nth j s2) (nth j fn-xcs)))
                  (implies (and (natp j) (<= (fn-xc-lo 2 fn-xcc) j) (< j (fn-xc-hi 2 fn-xcc))
                                (not (equal (fn-xcs-get-kind j fn-xcs) 0)))
                           (<= (fn-xcs-get-stamp v fn-xcs) (fn-xcs-get-stamp j fn-xcs))))))
  :hints (("Goal" :in-theory (e/d (fn-xc-yield) (fn-xc-free-effects))
                  :do-not-induct t
                  :use ((:instance fn-xc-lru-is-least (i (fn-xc-lo 2 fn-xcc)) (hi (fn-xc-hi 2 fn-xcc)) (best nil))
                        (:instance fn-xc-free-effects
                                   (i (fn-xc-lru (fn-xc-lo 2 fn-xcc) (fn-xc-hi 2 fn-xcc) nil fn-xcs)))))))

(defthm fn-xc-yield-none-means-empty
  (implies (and (fn-xc-yield-ready)
                (equal (mv-nth 0 (fn-xc-yield fn-xcs fn-xcc)) :none)
                (natp j) (< j (fn-xcs-count fn-xcs)))
           (equal (fn-xcs-get-kind j fn-xcs) 0))
  :hints (("Goal" :in-theory (enable fn-xc-yield fn-xc-lo fn-xc-hi)
                  :do-not-induct t
                  :use ((:instance fn-xc-lru-is-least (i (fn-xc-lo 1 fn-xcc)) (hi (fn-xc-hi 1 fn-xcc)) (best nil) (j j))
                        (:instance fn-xc-lru-is-least (i (fn-xc-lo 2 fn-xcc)) (hi (fn-xc-hi 2 fn-xcc)) (best nil) (j j))))))

; =============================================================================
; The ledger.  The token an eviction hands back is a :cached row's key; the
; ledger's eviction (fn-prl-evict) releases exactly that row's demand and
; removes exactly that binding.  The slot's token is rebuilt from its columns,
; so what the host hands the ledger is what ACL2 stored, never what the host
; remembers.
(local
 (defthm fn-xc-revappend-no-binding
   (implies (and (not (fn-prl-binding token a)) (not (fn-prl-binding token b)))
            (not (fn-prl-binding token (revappend a b))))
   :hints (("Goal" :in-theory (enable fn-prl-binding) :induct (revappend a b)))))

(local
 (defthm fn-xc-remove-aux-no-binding
   (implies (not (fn-prl-binding token rev))
            (not (fn-prl-binding token (fn-prl-remove-aux token rows rev))))
   :hints (("Goal" :in-theory (enable fn-prl-binding fn-prl-remove-aux)
                   :induct (fn-prl-remove-aux token rows rev)))))

(local
 (defthm fn-xc-removed-binding-is-absent
   (not (fn-prl-binding token (fn-prl-remove token rows)))
   :hints (("Goal" :in-theory (enable fn-prl-remove fn-prl-binding)))))

(defthm fn-xc-eviction-releases-exactly-the-slots-charge
  (implies (and (fn-xcsp fn-xcs) (natp v) (< v (fn-xcs-count fn-xcs))
                (fn-xc-slot-token v fn-xcs)
                (let ((row (cdr (fn-prl-binding (fn-xc-slot-token v fn-xcs) (fn-prl-nth 3 ledger)))))
                  (and (equal (fn-prl-nth 1 row) :cached)
                       (true-listp (fn-prl-nth 1 ledger))
                       (true-listp (fn-prl-nth 0 row)))))
           (let* ((token (fn-xc-slot-token v fn-xcs))
                  (row (cdr (fn-prl-binding token (fn-prl-nth 3 ledger))))
                  (r (fn-prl-evict ledger token))
                  (l2 (mv-nth 1 r)))
             (and (equal (mv-nth 0 r) :evicted)
                  (equal (fn-prl-nth 1 l2)
                         (fn-prs-release-reusable (fn-prl-nth 1 ledger) (fn-prl-nth 0 row)))
                  (not (fn-prl-binding token (fn-prl-nth 3 l2)))
                  (equal (fn-prl-nth 3 l2) (fn-prl-remove token (fn-prl-nth 3 ledger)))
                  (equal (fn-prl-nth 0 l2) (fn-prl-nth 0 ledger))
                  (equal (fn-prl-nth 2 l2) (fn-prl-nth 2 ledger))
                  (equal (fn-prl-baseline l2) (fn-prl-baseline ledger)))))
  :hints (("Goal" :in-theory (e/d (fn-prl-evict fn-prl-build fn-prl-nth fn-prl-baseline) (fn-prl-binding fn-prl-remove)))))

; A slot that holds no charge hands back nothing, so the host releases nothing for it.
(defthm fn-xc-chargeless-slot-hands-back-no-token
  (implies (and (fn-xcsp fn-xcs) (natp v) (< v (fn-xcs-count fn-xcs))
                (not (fn-xcs-get-tokp v fn-xcs)))
           (equal (fn-xc-slot-token v fn-xcs) nil))
  :hints (("Goal" :in-theory (enable fn-xc-slot-token))))


; =============================================================================
; The table, from the profile.  Init lays NE + NW free rows and the three
; cells; a fresh cache answers every lookup with a miss, and an empty region
; (N = 0, the cache off) refuses every install.
(defthm fn-xc-append-free-shape
  (implies (and (fn-xcsp fn-xcs) (natp n))
           (and (fn-xcsp (fn-xc-append-free n fn-xcs))
                (equal (fn-xcs-count (fn-xc-append-free n fn-xcs)) (+ n (fn-xcs-count fn-xcs)))))
  :hints (("Goal" :in-theory (enable fn-xc-append-free fn-xcs-append-is-append fn-xcsp-is-seq-p fn-xcs-count-is-len)
                  :induct (fn-xc-append-free n fn-xcs))))

(defun fn-xc-free-rows (n)
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (if (zp n) nil (cons *fn-xc-free-row* (fn-xc-free-rows (1- n)))))

(defthm fn-xc-append-free-is-free-rows
  (implies (and (natp n) (true-listp fn-xcs))
           (equal (fn-xc-append-free n fn-xcs)
                  (append fn-xcs (fn-xc-free-rows n))))
  :hints (("Goal" :in-theory (enable fn-xc-append-free fn-xcs-append-is-append fn-xc-free-rows)
                  :induct (fn-xc-append-free n fn-xcs))))

(defun fn-xc-rows-ind (i n)
  (declare (xargs :measure (nfix n)))
  (if (or (zp n) (zp i)) 0 (fn-xc-rows-ind (1- i) (1- n))))

(defthm fn-xc-free-rows-nth
  (implies (and (natp i) (natp n) (< i n))
           (equal (nth i (fn-xc-free-rows n)) *fn-xc-free-row*))
  :hints (("Goal" :in-theory (enable nth)
                  :expand ((fn-xc-free-rows n))
                  :induct (fn-xc-rows-ind i n))))
(defthm fn-xc-free-rows-len
  (equal (len (fn-xc-free-rows n)) (nfix n))
  :hints (("Goal" :in-theory (enable fn-xc-free-rows))))

(defthm fn-xc-find-in-free-rows
  (implies (and (member-equal kind '(1 2 3)) (natp i) (natp hi) (<= hi n) (natp n)
                (equal fn-xcs (fn-xc-free-rows n)))
           (not (fn-xc-find i hi exactp kind file eoff elen a b c d trailer pos fn-xcs)))
  :hints (("Goal" :in-theory (enable fn-xc-find fn-xc-slot-matchp fn-xcs-get-kind-is-nth)
                  :induct (fn-xc-find i hi exactp kind file eoff elen a b c d trailer pos fn-xcs))))
(defthm fn-xc-empty-stobjs-are-nil
  (and (implies (and (fn-xcsp fn-xcs) (equal (fn-xcs-count fn-xcs) 0)) (equal fn-xcs nil))
       (implies (and (fn-xccp fn-xcc) (equal (fn-xcc-count fn-xcc) 0)) (equal fn-xcc nil)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-xcsp-is-seq-p fn-xcs-count-is-len fn-xccp-is-scalar-seq-p fn-xcc-count-is-len)
                  :expand ((adt-seq-p *fn-xcs-schema* fn-xcs) (adt-scalar-seq-p '(:u64) fn-xcc)))))
(defthm fn-xc-init-initializes
  (implies (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc)
                (equal (fn-xcs-count fn-xcs) 0) (equal (fn-xcc-count fn-xcc) 0)
                (natp ne) (natp nw) (<= ne *fn-xc-max-slots*) (<= nw *fn-xc-max-slots*))
           (let ((r (fn-xc-init ne nw fn-xcs fn-xcc)))
             (and (equal (mv-nth 0 r) :initialized)
                  (fn-xcsp (mv-nth 1 r)) (fn-xccp (mv-nth 2 r))
                  (fn-xc-readyp (mv-nth 1 r) (mv-nth 2 r))
                  (equal (fn-xc-ne (mv-nth 2 r)) ne)
                  (equal (fn-xc-nw (mv-nth 2 r)) nw)
                  (equal (fn-xc-tick (mv-nth 2 r)) 0)
                  (equal (mv-nth 1 r) (fn-xc-free-rows (+ ne nw))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-xc-init fn-xc-readyp fn-xc-cellsp fn-xc-ne fn-xc-nw fn-xc-tick
                                     fn-xcc-append-is-append fn-xcc-count-is-len fn-xcs-count-is-len
                                     fn-xccp-is-scalar-seq-p fn-xcc-get-is-nth fn-xc-append-free-is-free-rows adt-scalar-seq-p adt-val-okp unsigned-byte-p)
                  :use ((:instance fn-xc-append-free-shape (n (+ ne nw))) fn-xc-empty-stobjs-are-nil))))
(defthm fn-xc-init-lookups-miss
  (implies (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc)
                (equal (fn-xcs-count fn-xcs) 0) (equal (fn-xcc-count fn-xcc) 0)
                (natp ne) (natp nw) (<= ne *fn-xc-max-slots*) (<= nw *fn-xc-max-slots*)
                (natp from) (natp pos))
           (equal (mv-nth 0 (fn-xc-lookup from kind file eoff elen a b c d trailer pos
                                          (mv-nth 1 (fn-xc-init ne nw fn-xcs fn-xcc))
                                          (mv-nth 2 (fn-xc-init ne nw fn-xcs fn-xcc))))
                  :miss))
  :hints (("Goal" :in-theory (enable fn-xc-lookup fn-xc-lo fn-xc-hi)
                  :use (fn-xc-init-initializes
                        (:instance fn-xc-find-in-free-rows (n (+ ne nw)) (hi ne) (i (if (< from 0) 0 from))
                                   (exactp t) (fn-xcs (fn-xc-free-rows (+ ne nw))))
                        (:instance fn-xc-find-in-free-rows (n (+ ne nw)) (hi (+ ne nw)) (i (if (< from ne) ne from))
                                   (exactp nil) (fn-xcs (fn-xc-free-rows (+ ne nw))))))))
(defthm fn-xc-init-install-refuses-in-an-empty-region
  (implies (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc)
                (equal (fn-xcs-count fn-xcs) 0) (equal (fn-xcc-count fn-xcc) 0)
                (natp ne) (natp nw) (<= ne *fn-xc-max-slots*) (<= nw *fn-xc-max-slots*)
                (or (and (equal kind 1) (equal ne 0))
                    (and (member-equal kind '(2 3)) (equal nw 0))))
           (equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer
                                           (mv-nth 1 (fn-xc-init ne nw fn-xcs fn-xcc))
                                           (mv-nth 2 (fn-xc-init ne nw fn-xcs fn-xcc))))
                  :refused))
  :hints (("Goal" :in-theory (enable fn-xc-install fn-xc-install-conflict fn-xc-lo fn-xc-hi)
                  :use (fn-xc-init-initializes))))

; p-xc-span round 1: the host supplies the plan/window stored at the selected
; slot under its extent lock. FROM may be the already selected slot: lookup
; then repeats that same decision without walking earlier declined slots.
(include-book "page-window-span")

(defun fn-xc-span-at (from ledger plan file eoff elen poff plen trailer p end
                         fn-xcs fn-xcc fn-ew-buffer fn-ew-span)
  (declare (xargs :stobjs (fn-xcs fn-xcc fn-ew-buffer fn-ew-span)
                  :guard (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc)
                              (true-listp plan) (natp from) (natp p)
                              (natp end) (natp plen))))
  (mv-let (word slot)
    (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p fn-xcs fn-xcc)
    (if (and (equal word :hit) (natp slot) (< slot (fn-xcs-count fn-xcs))
             (natp p) (natp end) (natp plen))
        (let* ((token (fn-xc-slot-token slot fn-xcs))
               (j (min (min end plen)
                       (min (+ p *fn-ew-span-capacity*)
                            (+ (nfix (fn-prl-nth 7 token)) (nfix (nth 5 plan)))))))
          (if (< p j)
              (mv-let (answer fn-ew-span)
                (fn-pwc-span-at ledger token plan file eoff elen poff plen trailer
                                p j fn-ew-buffer fn-ew-span)
                (if (equal answer :span)
                    (mv-let (touch fn-xcs fn-xcc) (fn-xc-touch slot fn-xcs fn-xcc)
                      (declare (ignore touch))
                      (mv :span (- j p) slot fn-ew-span fn-xcs fn-xcc))
                  (mv :miss 0 slot fn-ew-span fn-xcs fn-xcc)))
            (mv :miss 0 slot fn-ew-span fn-xcs fn-xcc)))
      (mv :miss 0 nil fn-ew-span fn-xcs fn-xcc))))

; Logical carried invariant, never a whole-table check on a served path.
; Use the generated slot-token projection: no second row/token encoding.
(defun fn-xc-token-apart-from (token i fn-xcs)
  (declare (xargs :stobjs fn-xcs
                  :guard (and (fn-xcsp fn-xcs) (natp i))
                  :measure (nfix (- (fn-xcs-count fn-xcs) i))))
  (if (and (natp i) (< i (fn-xcs-count fn-xcs)))
      (and (not (equal token (fn-xc-slot-token i fn-xcs)))
           (fn-xc-token-apart-from token (1+ i) fn-xcs))
    t))

(defun fn-xc-token-disjoint-from (i fn-xcs)
  (declare (xargs :stobjs fn-xcs
                  :guard (and (fn-xcsp fn-xcs) (natp i))
                  :measure (nfix (- (fn-xcs-count fn-xcs) i))))
  (if (and (natp i) (< i (fn-xcs-count fn-xcs)))
      (let ((token (fn-xc-slot-token i fn-xcs)))
        (and (or (not token) (fn-xc-token-apart-from token (1+ i) fn-xcs))
             (fn-xc-token-disjoint-from (1+ i) fn-xcs)))
    t))

(defun fn-xc-token-disjointp (fn-xcs)
  (declare (xargs :stobjs fn-xcs :guard (fn-xcsp fn-xcs)))
  (fn-xc-token-disjoint-from 0 fn-xcs))

(in-theory (disable fn-xc-token fn-xc-slot-token fn-xc-token-apart-from
                    fn-xc-token-disjoint-from fn-xc-token-disjointp))

(defthm fn-xc-find-token-except-sound
  (implies (fn-xc-find-token-except token target i fn-xcs)
           (let ((j (fn-xc-find-token-except token target i fn-xcs)))
             (and token (natp j) (<= (nfix i) j) (< j (fn-xcs-count fn-xcs))
                  (not (equal j target)) (fn-xc-holds j token fn-xcs))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-xc-find-token-except token target i fn-xcs)
           :in-theory (enable fn-xc-find-token-except fn-xc-holds))))

(defthm fn-xc-find-token-except-complete
  (implies (and (natp i) (natp j) (<= i j) (< j (fn-xcs-count fn-xcs))
                token (not (equal j target)) (equal token (fn-xc-slot-token j fn-xcs)))
           (fn-xc-find-token-except token target i fn-xcs))
  :rule-classes nil
  :hints (("Goal" :induct (fn-xc-find-token-except token target i fn-xcs)
           :in-theory (enable fn-xc-find-token-except))))

(defthm fn-xc-token-apart-from-member
  (implies (and (fn-xc-token-apart-from token i fn-xcs)
                (natp i) (natp j) (<= i j) (< j (fn-xcs-count fn-xcs)))
           (not (equal token (fn-xc-slot-token j fn-xcs))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-xc-token-apart-from token i fn-xcs)
           :in-theory (enable fn-xc-token-apart-from))))

(defthm fn-xc-token-disjoint-from-pair
  (implies (and (fn-xc-token-disjoint-from n fn-xcs)
                (natp n) (natp i) (natp k) (<= n i) (< i k)
                (< k (fn-xcs-count fn-xcs)) (fn-xc-slot-token i fn-xcs))
           (not (equal (fn-xc-slot-token i fn-xcs) (fn-xc-slot-token k fn-xcs))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-xc-token-disjoint-from n fn-xcs)
           :in-theory (enable fn-xc-token-disjoint-from))
          ("Subgoal *1/1" :use (:instance fn-xc-token-apart-from-member
                                  (token (fn-xc-slot-token n fn-xcs)) (i (1+ n)) (j k)))))

; KEYSTONE: one cached ledger row has at most one slot.
(defthm fn-xc-held-token-has-one-slot
  (implies (and (fn-xc-token-disjointp fn-xcs)
                (fn-xc-holds i token fn-xcs)
                (fn-xc-holds k token fn-xcs))
           (equal i k))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-xc-token-disjointp fn-xc-holds)
           :use ((:instance fn-xc-token-disjoint-from-pair (n 0))
                 (:instance fn-xc-token-disjoint-from-pair (n 0) (i k) (k i))))))

(defthm fn-xc-slot-token-after-write
  (implies (and (fn-xc-write-okp i kind tokp tid tcid file eoff elen a b c d start trailer stamp fn-xcs)
                (natp j))
           (equal (fn-xc-slot-token j (fn-xc-write i kind tokp tid tcid file eoff elen a b c d start trailer stamp fn-xcs))
                  (if (equal j i)
                      (fn-xc-token kind tokp tid tcid file eoff elen a b c d start trailer)
                    (fn-xc-slot-token j fn-xcs))))
  :hints (("Goal" :in-theory (enable fn-xc-slot-token))))
