; fn: the state checkpoint's file octets written into the octet buffer
; (D27, representation wave D-2; planning/evidence/rep-wave-d-2-2026-09-26.md).
;
; `fn-scc-file-octets' (books/store-checkpoint-codec.lisp) is what the host
; wrote as the P3 state checkpoint: the checkpoint value's postfix program
; (`fn-scc-encode'), cut into chunks of the profile's segment size, each
; framed by an FNSC header and a chained `fn-frame-trailer'.  As a list
; codec it holds the encoding as `fn-scc-renc''s reversed accumulator, then
; its reversal, then the chunks (`take'/`nthcdr'), then the frames, then
; their concatenation, and the host turns that list into a byte vector:
; five to six octet-list copies of the whole file at sixteen bytes per
; octet.  At N = 10,000 x 32 KiB (a 330 MB file) that is 33 GB, and `store
; checkpoint' dies by heap exhaustion (planning/evidence/rep-wave-d-2026-09-25.md
; section 1.2).  None of it is the retained payload.
;
; (Since lane checkpoint-pipeline, 2026-09-26, the whole-file plan
; `fn-sccb-plan' is gone: the schema-3 tables are written in batches by
; books/owner-checkpoint-pipeline.lisp; this book keeps the writers, the
; slice and the frame's octets.)
; This book wrote the program once, forward, into the octet buffer
; (books/octets-stobj.lisp; one byte per octet) and returned a PLAN: one
; entry per segment, (HEADER A B TRAILER), whose octets are the header, the
; buffer's cells A..B and the trailer.  A chunk is read from the buffer by
; index for its seal (a list of at most one segment, transient) and never
; as part of a whole-file list.  The host (host/store-node-host.lisp
; `fn-store-sco-publish-plan'; host/native/io.lisp
; `fnn-command-state-checkpoint') writes the plan's octets and nothing
; else; what those octets are is `fn-sccb-plan-octets', a function of this
; book, and the KEYSTONE `fn-sccb-plan-is-file-octets' says they are
; `fn-scc-file-octets' of the same value and segment size: the file on disk
; is the file the list codec specified, byte for byte, so the reader
; (`fn-scc-decode-segments', the checkpoint open) is untouched.
;
; Encodability.  `fn-scc-treep' admits an octets leaf or a string of any
; length, but the codec writes a length as `fn-scc-nat-octets': a digit
; count, then the digits, and the count is one octet on disk.  A tree with
; a length that needs 256 digits or more (2^2040 octets) encodes, as a
; list, to a list with a non-octet in it, which the host's byte vector
; cannot hold: a fault at the host.  `fn-sccb-treep' is `fn-scc-treep'
; with every leaf's octets octets (`fn-sccb-treep-encodes-octets'); the
; buffer plan refuses such a tree as :unencodable where the list codec
; faulted.  Every `fn-sccb-treep' is `fn-scc-treep' (`fn-sccb-treep-is-treep'),
; so the keystone covers every value the list codec encoded to octets.

(in-package "ACL2")
(include-book "store-checkpoint-codec")
(include-book "octets-stobj")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; List facts the correspondences rest on.

(local
 (defthm fn-sccb-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(local
 (defthm fn-sccb-true-listp-append
   (equal (true-listp (append a b)) (true-listp b))))

(local
 (defthm fn-sccb-octet-listp-append
   (implies (and (fn-scc-octet-listp a) (fn-scc-octet-listp b))
            (fn-scc-octet-listp (append a b)))))

(local
 (defthm fn-sccb-len-nthcdr
   (implies (and (natp n) (<= n (len xs)))
            (equal (len (nthcdr n xs)) (- (len xs) n)))))

(local
 (defthm fn-sccb-len-take
   (equal (len (take k x)) (nfix k))))

(local
 (defthm fn-sccb-take-len
   (implies (true-listp x) (equal (take (len x) x) x))))

; The last chunk, in the arithmetic normal form the prover leaves: the rest
; of a list from A, taken whole.
(local
 (defthm fn-sccb-take-rest-of-nthcdr
   (implies (and (natp a) (<= a (len x)) (true-listp x))
            (equal (take (+ (- a) (len x)) (nthcdr a x)) (nthcdr a x)))
   :hints (("Goal" :use ((:instance fn-sccb-take-len (x (nthcdr a x))))
            :in-theory (disable fn-sccb-take-len)))))

(local
 (defthm fn-sccb-nthcdr-nthcdr
   (implies (and (natp a) (natp b))
            (equal (nthcdr b (nthcdr a x)) (nthcdr (+ a b) x)))))

(local
 (defthm fn-sccb-true-listp-nthcdr
   (implies (true-listp x) (true-listp (nthcdr n x)))))

(local
 (defthm fn-sccb-long-enoughp-is-len
   (implies (natp n)
            (equal (fn-scc-long-enoughp n xs) (<= n (len xs))))))

(local
 (defthm fn-sccb-true-list-fix-of-true-list
   (implies (true-listp x) (equal (true-list-fix x) x))))

(local
 (defthm fn-sccb-true-listp-take
   (true-listp (take n x))))

; `fn-scc-chunks' by cases, so both sides of the frames correspondence step
; in lockstep without deciding `zp' of the segment size first.
(local
 (defthm fn-sccb-chunks-short
   (implies (or (zp seg) (<= (len p) seg))
            (equal (fn-scc-chunks p seg) (list p)))))

(local
 (defthm fn-sccb-chunks-long
   (implies (and (not (zp seg)) (< seg (len p)))
            (equal (fn-scc-chunks p seg)
                   (cons (take seg p) (fn-scc-chunks (nthcdr seg p) seg))))))

; The buffer's append export is `fn-oct-snoc' on its logical value, and that
; is `append' of one element on ANY object, not only a true list (which is
; how octets-stobj states it): the writers below need no hypothesis on the
; buffer's value.  Proved before the hypothesis was dropped, per the rule.
(local
 (defthm fn-sccb-snoc-is-append
   (equal (fn-oct-snoc xs o) (append xs (list o)))
   :hints (("Goal" :in-theory (enable fn-oct-snoc)))))

(defthm fn-sccb-scc-octetp-is-cbor-octetp
  (equal (fn-scc-octetp x) (fn-cbor-octetp x))
  :hints (("Goal" :in-theory (enable fn-scc-octetp fn-cbor-octetp))))

; -----------------------------------------------------------------------------
; Writing a list of octets at the end of the buffer: ONE export call for the
; whole list (`fn-octets-append-list', PKT-315; before it, one :protect'ed
; export call per octet at about 0.12 us each), the buffer's logical value
; growing by `append'.

(defun fn-sccb-append-list (xs fn-octets)
  (declare (xargs :stobjs fn-octets :guard (fn-scc-octet-listp xs)
                  :guard-hints (("Goal" :in-theory (enable fn-cbor-octetp)))))
  (fn-octets-append-list xs fn-octets))

; The export's logical value is `append' on ANY buffer value and any XS
; (`fn-oct-append-list-is-append', octets-stobj): the two hypotheses the
; per-octet writer needed (a true-list buffer for an empty write; a
; true-list XS) are gone, the weakened theorem proved before they were
; dropped (checkpoint-capture-stream, 2026-09-26).
(defthm fn-sccb-append-list-is-append
  (equal (fn-sccb-append-list xs fn-octets) (append fn-octets xs)))

(defthm fn-sccb-append-list-nonempty-is-append
  (implies (and (true-listp xs) (consp xs))
           (equal (fn-sccb-append-list xs fn-octets) (append fn-octets xs))))

(defun fn-sccb-cons-ops (n fn-octets)
  (declare (xargs :stobjs fn-octets :guard (natp n)))
  (if (zp n)
      fn-octets
    (let ((fn-octets (fn-octets-append-octet *fn-scc-op-cons* fn-octets)))
      (fn-sccb-cons-ops (1- n) fn-octets))))

(defthm fn-sccb-cons-ops-is-append-repeat
  (implies (true-listp fn-octets)
           (equal (fn-sccb-cons-ops n fn-octets)
                  (append fn-octets (fn-scc-repeat (nfix n) *fn-scc-op-cons*))))
  :hints (("Goal" :induct (fn-sccb-cons-ops n fn-octets)
           :in-theory (enable fn-scc-repeat))))

; -----------------------------------------------------------------------------
; Encodability: `fn-scc-treep' with every leaf's octets octets.

(defun fn-sccb-treep (x)
  (declare (xargs :guard t))
  (cond ((fn-scc-octets-valuep x)
         (fn-scc-octet-listp (fn-scc-nat-octets (len x))))
        ((consp x) (and (fn-sccb-treep (car x)) (fn-sccb-treep (cdr x))))
        (t (and (fn-scc-atomp x)
                (fn-scc-octet-listp (fn-scc-atom-octets x))))))

(defthm fn-sccb-treep-is-treep
  (implies (fn-sccb-treep x) (fn-scc-treep x))
  :hints (("Goal" :induct (fn-sccb-treep x))))

(defthm fn-sccb-treep-encodes-octets
  (implies (fn-sccb-treep x) (fn-scc-octet-listp (fn-scc-program x)))
  :hints (("Goal" :induct (fn-sccb-treep x))))

; -----------------------------------------------------------------------------
; The program written forward.  `fn-scc-renc' (the list encoder) writes the
; program reversed onto an accumulator with the cdr recursion in tail
; position and a count of the CONS ops it still owes; this is the same
; recursion writing forward into the buffer, so a history of any length
; costs no stack.

(local
 (defthm fn-sccb-atom-octets-true-listp
   (true-listp (fn-scc-atom-octets x))))

(local
 (defthm fn-sccb-nat-octets-true-listp
   (true-listp (fn-scc-nat-octets n))))

; Every atom's octets begin with its op: the write is never empty, so the
; encoder's equation needs no hypothesis on the buffer's value.
(local
 (defthm fn-sccb-atom-octets-consp
   (consp (fn-scc-atom-octets x))))

(defun fn-sccb-renc (x n fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (fn-sccb-treep x) (natp n))
                  :measure (acl2-count x)
                  :verify-guards nil))
  (cond ((fn-scc-octets-valuep x)
         (let* ((fn-octets (fn-octets-append-octet *fn-scc-op-octets* fn-octets))
                (fn-octets (fn-sccb-append-list (fn-scc-nat-octets (len x)) fn-octets))
                (fn-octets (fn-sccb-append-list x fn-octets)))
           (fn-sccb-cons-ops n fn-octets)))
        ((consp x)
         (let ((fn-octets (fn-sccb-renc (car x) 0 fn-octets)))
           (fn-sccb-renc (cdr x) (+ 1 (nfix n)) fn-octets)))
        (t
         (let ((fn-octets (fn-sccb-append-list (fn-scc-atom-octets x) fn-octets)))
           (fn-sccb-cons-ops n fn-octets)))))

; The leaf codecs stay closed: the equation is about the writers over
; opaque octet lists (an atom's octets are a nonempty true list, a length's
; octets a true list), and opening them split the proof 9 s wide.
(defthm fn-sccb-renc-is-program
  (equal (fn-sccb-renc x n fn-octets)
         (append fn-octets (fn-scc-program x)
                 (fn-scc-repeat (nfix n) *fn-scc-op-cons*)))
  :hints (("Goal" :induct (fn-sccb-renc x n fn-octets)
           :in-theory (e/d (fn-scc-repeat)
                           (fn-scc-atom-octets fn-scc-nat-octets fn-scc-le-digits
                            fn-scc-string-octets fn-scc-atomp fn-scc-treep
                            fn-sccb-treep fn-scc-octet-listp)))))

(verify-guards fn-sccb-renc)

; -----------------------------------------------------------------------------
; The segments as ranges of the buffer.  `fn-scc-chunks' cuts a list into
; pieces of SEG octets (one piece when SEG is 0 or the list is no longer
; than SEG); here a piece is the pair of its bounds.

(defun fn-sccb-chunk-count (l seg)
  (declare (xargs :guard (and (natp l) (natp seg)) :measure (nfix l)))
  (if (or (zp seg) (<= (nfix l) seg))
      1
    (+ 1 (fn-sccb-chunk-count (- l seg) seg))))

(defthm fn-sccb-chunk-count-is-len-chunks
  (implies (true-listp p)
           (equal (len (fn-scc-chunks p seg))
                  (fn-sccb-chunk-count (len p) seg)))
  :hints (("Goal" :induct (fn-scc-chunks p seg))))

; The chunk read back to front with an accumulator, tail-recursive.
; `fn-oct-slice-list' (octets-stobj's derived reader) conses on the way
; back up, and a chunk is a whole segment: at the profile's segment size it
; exhausted the control stack on the N = 1,000 x 32 KiB store (hbox
; native-ckpt2, 2026-09-26) where the list codec's `take' had not.
(defun fn-sccb-slice-acc (i n acc fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp n) (<= i n)
                              (<= n (fn-octets-len fn-octets)))
                  :measure (nfix (- n (nfix i)))))
  (if (or (not (natp i)) (not (natp n)) (<= n i))
      acc
    (fn-sccb-slice-acc i (1- n) (cons (fn-octets-get (1- n) fn-octets) acc)
                       fn-octets)))

(local
 (defthm fn-sccb-slice-list-snoc
   (implies (and (natp i) (natp n) (< i n))
            (equal (fn-oct-slice-list i n fn-octets)
                   (append (fn-oct-slice-list i (1- n) fn-octets)
                           (list (nth (1- n) fn-octets)))))
   :hints (("Goal" :induct (fn-oct-slice-list i n fn-octets)
            :in-theory (enable fn-oct-slice-list)))))

(local
 (defthm fn-sccb-slice-list-true-listp
   (true-listp (fn-oct-slice-list i n fn-octets))
   :hints (("Goal" :in-theory (enable fn-oct-slice-list)))))

(defthm fn-sccb-slice-acc-is-slice-list
  (implies (and (natp i) (natp n) (<= i n))
           (equal (fn-sccb-slice-acc i n acc fn-octets)
                  (append (fn-oct-slice-list i n fn-octets) acc)))
  :hints (("Goal" :induct (fn-sccb-slice-acc i n acc fn-octets)
           :in-theory (enable fn-oct-slice-list))))

; The snoc form served its one proof; as a rewrite it would keep pulling
; the last octet off every slice below.
(local (in-theory (disable fn-sccb-slice-list-snoc)))

; What the host writes for one frame and for the plan: the header, the
; buffer's cells A..B, the trailer.  This is the specification of the host's
; write (host/native/io.lisp `fnn-plan-octets'), never run on a served path.
(defun fn-sccb-frame-octets (frame fn-octets)
  (declare (xargs :stobjs fn-octets :guard (true-listp frame)))
  (let ((header (nth 0 frame)) (a (nth 1 frame)) (b (nth 2 frame))
        (trailer (nth 3 frame)))
    (append (true-list-fix header)
            (if (and (natp a) (natp b) (<= a b) (<= b (fn-octets-len fn-octets)))
                (fn-oct-slice-list a b fn-octets)
              nil)
            (true-list-fix trailer))))

(defun fn-sccb-plan-octets (plan fn-octets)
  (declare (xargs :stobjs fn-octets :guard (true-list-listp plan)))
  (if (consp plan)
      (append (fn-sccb-frame-octets (car plan) fn-octets)
              (fn-sccb-plan-octets (cdr plan) fn-octets))
    nil))

(local
 (defthm fn-sccb-header-true-listp
   (true-listp (fn-scc-header index count length sequence))
   :hints (("Goal" :in-theory (enable fn-scc-header)))))

(in-theory (disable fn-sccb-append-list fn-sccb-cons-ops fn-sccb-renc
                    fn-sccb-slice-acc))

;; Withdrawn from includers (lane rule-hygiene, tools/rule_cost.py).
;; Each is tried in includers' proofs and pays for its frames in
;; almost none (planning/evidence/rule-cost-*.json has the counts;
;; docs/proof-style.md section 8).  An includer that needs one
;; enables it where it is used.
(in-theory (disable (:definition fn-sccb-frame-octets)
                    (:definition fn-sccb-treep)
                    (:rewrite fn-sccb-cons-ops-is-append-repeat)
                    (:rewrite fn-sccb-scc-octetp-is-cbor-octetp)))
