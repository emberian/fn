; fn: the octet buffer, an abstract stobj (D27 boundary 6, wave B).
;
; The logical model of every codec in this tree is an octet list.  At the
; host boundary the octets are a byte array (a socket read, a file read),
; and today every call converts the array to a list (`fnn-octet-list',
; host/native/io.lisp).  This book is the one place where a byte array is
; the executable and the octet list stays the logical view: an abstract
; stobj `fn-octets' whose logical value IS the octet list (recognizer
; `fn-cbor-octet-listp', creator nil) and whose executable is a resizable
; `(unsigned-byte 8)' array with a fill count.
;
; The abstraction relation is `fn-octets$corr': the array's first FILL
; cells, read in order, are the logical list, the fill count is within the
; array, and the concrete object is well-formed.  It is established by the
; creator and preserved by every export, and every export's logical result
; equals the list-model operation on the abstraction: these are the
; {CORRESPONDENCE}, {PRESERVED} and {GUARD-THM} theorems below, each stated
; exactly as `defabsstobj-missing-events' prints it and proved before the
; `defabsstobj' event, which then admits them by name.  No `skip-proofs'.
;
; Exports (logic / exec):
;   fn-octets-len            (len st)                / the fill count
;   fn-octets-get i          (nth i st)              / one array read
;   fn-octets-put i o        (update-nth i o st)     / one array write
;   fn-octets-append-octet o (append st (list o))    / one array write
;   fn-octets-clear          nil                     / fill := 0
;   fn-octets-reserve n      st                      / grow the array to n
;   fn-octets-list           st                      / the list, consed once
;   fn-octets-from-list xs   xs                      / clear, then write xs
;   fn-octets-append-list xs (append st xs)         / one write per octet, in
;                                                     one export call (PKT-315)
;   fn-octets-append-back off n  (fn-oct-back-copy off n st): n octets, each
;                            the one OFF back when appended (overlap repeats)
;                                                   / one reserve, one loop
;   fn-octets-get-word i k   the k octets at i, little-endian / k reads
;   fn-octets-append-word w k (append st (fn-oct-word-octets w k))
;                                                   / one reserve, k writes
;
; Adding an export here adds it to every abstract stobj declared
; `:congruent-to fn-octets' (ACL2 requires their export lists to match
; exactly): payload-lz's fn-lz-dict and fn-lz-out, bp-node-rotation-buffer's
; fn-octets-bp, owner-checkpoint-writer's fn-octets-pub, and any driver's.
;
; The host fills the array from a byte vector in raw Lisp (`fnn-octets-fill',
; host/native/io.lisp): `fn-octets-reserve', one `replace', then the fill
; count.  That write is the host boundary, at the same trust as
; `fnn-octet-list' handing a list to the core today (A-HOST): the host
; asserts that the logical value is the list of the bytes it wrote, and
; nothing else can reach the array.
;
; Derived readers (`fn-oct-slice-list', `fn-oct-prefix-equalp',
; `fn-oct-suffix-equalp', `fn-oct-line-end') are the vocabulary a codec twin
; reads the buffer with; each is equal to its `take'/`nthcdr' term over the
; logical list, so a twin's boundary theorem reasons with the list model.

(in-package "ACL2")
(include-book "cbor")

; -----------------------------------------------------------------------------
; The concrete stobj.

(defstobj fn-octets$c
  (fn-octets$c-buf :type (array (unsigned-byte 8) (0)) :initially 0 :resizable t)
  (fn-octets$c-fill :type (integer 0 *) :initially 0)
  :inline t)

; -----------------------------------------------------------------------------
; The abstraction: buf[i..n) as a list, over the raw array list.  Every
; lemma the obligations need is a lemma about this function on lists.

(defun fn-oct-list-from (i n buf)
  (declare (xargs :guard (and (natp i) (natp n) (true-listp buf))
                  :measure (nfix (- n i))))
  (if (or (not (natp i)) (not (natp n)) (<= n i))
      nil
    (cons (nth i buf) (fn-oct-list-from (1+ i) n buf))))

(defthm fn-oct-len-of-list-from
  (equal (len (fn-oct-list-from i n buf))
         (if (and (natp i) (natp n) (< i n)) (- n i) 0)))

(defthm fn-oct-true-listp-of-list-from
  (true-listp (fn-oct-list-from i n buf)))

(local
 (defun fn-oct-ind-ik (i k n buf)
   (declare (xargs :measure (nfix (- n i))))
   (if (or (not (natp i)) (not (natp n)) (<= n i))
       (list i k buf)
     (fn-oct-ind-ik (1+ i) (1- k) n buf))))

(defthm fn-oct-nth-of-list-from
  (implies (and (natp i) (natp n) (natp k) (< (+ i k) n))
           (equal (nth k (fn-oct-list-from i n buf))
                  (nth (+ i k) buf)))
  :hints (("Goal" :induct (fn-oct-ind-ik i k n buf))))

(defthm fn-oct-list-from-empty
  (implies (and (natp i) (natp n) (<= n i))
           (equal (fn-oct-list-from i n buf) nil)))

; The split of buf[i..n+1) at its last cell.  Not a rewrite rule: as one it
; would unroll every constant range.
(defthm fn-oct-list-from-snoc
  (implies (and (natp i) (natp n) (<= i n))
           (equal (fn-oct-list-from i (1+ n) buf)
                  (append (fn-oct-list-from i n buf) (list (nth n buf)))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-oct-list-from i n buf))))

(defthm fn-oct-list-from-of-update-nth-outside
  (implies (and (natp j) (natp n) (or (< j (nfix i)) (<= n j)))
           (equal (fn-oct-list-from i n (update-nth j v buf))
                  (fn-oct-list-from i n buf))))

(defthm fn-oct-list-from-of-update-nth-inside
  (implies (and (natp i) (natp j) (natp n) (<= i j) (< j n))
           (equal (fn-oct-list-from i n (update-nth j v buf))
                  (update-nth (- j i) v (fn-oct-list-from i n buf)))))

(defthm fn-oct-len-of-resize-list
  (equal (len (resize-list buf m d)) (nfix m)))

(local
 (defun fn-oct-ind-resize (k m buf)
   (if (zp m)
       (list k buf)
     (fn-oct-ind-resize (1- k) (1- m) (if (consp buf) (cdr buf) buf)))))

(defthm fn-oct-nth-of-resize-list
  (implies (and (natp k) (< k (nfix m)) (< k (len buf)))
           (equal (nth k (resize-list buf m d)) (nth k buf)))
  :hints (("Goal" :induct (fn-oct-ind-resize k m buf))))

(defthm fn-oct-list-from-of-resize-list
  (implies (and (natp n) (<= n (len buf)) (<= n (nfix m)))
           (equal (fn-oct-list-from i n (resize-list buf m d))
                  (fn-oct-list-from i n buf))))

; The array recognizer: a cell within the array is an octet, and writes of
; octets and resizes keep it.

(defthm fn-oct-bufp-cell-is-octet
  (implies (and (fn-octets$c-bufp buf) (natp k) (< k (len buf)))
           (and (integerp (nth k buf))
                (<= 0 (nth k buf))
                (< (nth k buf) 256)))
  :rule-classes ((:rewrite :corollary
                  (implies (and (fn-octets$c-bufp buf) (natp k) (< k (len buf)))
                           (and (integerp (nth k buf))
                                (<= 0 (nth k buf))
                                (< (nth k buf) 256))))
                 (:rewrite :corollary
                  (implies (and (fn-octets$c-bufp buf) (natp k) (< k (len buf)))
                           (fn-cbor-octetp (nth k buf))))
                 (:rewrite :corollary
                  (implies (and (fn-octets$c-bufp buf) (natp k) (< k (len buf)))
                           (unsigned-byte-p 8 (nth k buf))))))

(defthm fn-oct-bufp-true-listp
  (implies (fn-octets$c-bufp buf) (true-listp buf)))

(defthm fn-oct-bufp-of-update-nth
  (implies (and (fn-octets$c-bufp buf) (natp k) (< k (len buf))
                (unsigned-byte-p 8 v))
           (fn-octets$c-bufp (update-nth k v buf))))

(defthm fn-oct-bufp-of-resize-list
  (implies (fn-octets$c-bufp buf)
           (fn-octets$c-bufp (resize-list buf m 0))))

(defthm fn-oct-octet-listp-of-list-from
  (implies (and (fn-octets$c-bufp buf) (natp n) (<= n (len buf)))
           (fn-cbor-octet-listp (fn-oct-list-from i n buf))))

; The abstraction stays closed from here on: opened at the constant index 0
; it turns into a cons no lemma above is about.
(local (in-theory (disable fn-oct-list-from)))

; -----------------------------------------------------------------------------
; The executable readers: buf[0..n) consed from the top down in a tail call
; (constant stack whatever the length; large-article, 2026-09-25).

(defun fn-oct-buf-list-down (n acc fn-octets$c)
  (declare (xargs :stobjs fn-octets$c
                  :guard (and (natp n) (<= n (fn-octets$c-buf-length fn-octets$c))
                              (true-listp acc))
                  :measure (nfix n)))
  (if (zp n)
      acc
    (fn-oct-buf-list-down (1- n)
                          (cons (fn-octets$c-bufi (1- n) fn-octets$c) acc)
                          fn-octets$c)))

(local
 (defthm fn-oct-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(defthm fn-oct-buf-list-down-is-list-from
  (implies (and (natp n) (true-listp acc))
           (equal (fn-oct-buf-list-down n acc fn-octets$c)
                  (append (fn-oct-list-from 0 n (nth 0 fn-octets$c)) acc)))
  :hints (("Goal" :induct (fn-oct-buf-list-down n acc fn-octets$c)
           :in-theory (disable fn-oct-list-from))
          ("Subgoal *1/2" :use ((:instance fn-oct-list-from-snoc
                                           (i 0) (n (1- n)) (buf (nth 0 fn-octets$c)))))))

; -----------------------------------------------------------------------------
; The exec functions, one per export.

(defun fn-octets$c-wfp (fn-octets$c)
  ; The concrete invariant: the fill count is within the array.
  (declare (xargs :stobjs fn-octets$c))
  (<= (fn-octets$c-fill fn-octets$c) (fn-octets$c-buf-length fn-octets$c)))

(defun fn-octets$c-len (fn-octets$c)
  (declare (xargs :stobjs fn-octets$c))
  (fn-octets$c-fill fn-octets$c))

(defun fn-octets$c-get (i fn-octets$c)
  (declare (xargs :stobjs fn-octets$c
                  :guard (and (natp i) (< i (fn-octets$c-fill fn-octets$c))
                              (fn-octets$c-wfp fn-octets$c))))
  (fn-octets$c-bufi i fn-octets$c))

(defun fn-octets$c-append-octet (o fn-octets$c)
  (declare (xargs :stobjs fn-octets$c
                  :guard (and (fn-cbor-octetp o) (fn-octets$c-wfp fn-octets$c))))
  (let* ((n (fn-octets$c-fill fn-octets$c))
         (fn-octets$c (if (< n (fn-octets$c-buf-length fn-octets$c))
                          fn-octets$c
                        (resize-fn-octets$c-buf (max 1024 (* 2 n)) fn-octets$c)))
         (fn-octets$c (update-fn-octets$c-bufi n o fn-octets$c)))
    (update-fn-octets$c-fill (1+ n) fn-octets$c)))

(defun fn-octets$c-put (i o fn-octets$c)
  (declare (xargs :stobjs fn-octets$c
                  :guard (and (natp i) (< i (fn-octets$c-fill fn-octets$c))
                              (fn-cbor-octetp o) (fn-octets$c-wfp fn-octets$c))))
  (update-fn-octets$c-bufi i o fn-octets$c))

(defun fn-octets$c-clear (fn-octets$c)
  (declare (xargs :stobjs fn-octets$c))
  (update-fn-octets$c-fill 0 fn-octets$c))

(defun fn-octets$c-reserve (n fn-octets$c)
  ; Grow the array so that N octets fit; the contents and the fill count
  ; are unchanged.  The host calls this before its raw fill.
  (declare (xargs :stobjs fn-octets$c :guard (natp n)))
  (if (<= n (fn-octets$c-buf-length fn-octets$c))
      fn-octets$c
    (resize-fn-octets$c-buf n fn-octets$c)))

(defun fn-octets$c-list (fn-octets$c)
  (declare (xargs :stobjs fn-octets$c :guard (fn-octets$c-wfp fn-octets$c)))
  (fn-oct-buf-list-down (fn-octets$c-fill fn-octets$c) nil fn-octets$c))

(defun fn-oct-write-list (xs fn-octets$c)
  ; Append XS at the fill point, one write per octet.
  (declare (xargs :stobjs fn-octets$c
                  :guard (and (fn-cbor-octet-listp xs) (fn-octets$c-wfp fn-octets$c))))
  (if (atom xs)
      fn-octets$c
    (let ((fn-octets$c (fn-octets$c-append-octet (car xs) fn-octets$c)))
      (fn-oct-write-list (cdr xs) fn-octets$c))))

(defun fn-octets$c-from-list (xs fn-octets$c)
  (declare (xargs :stobjs fn-octets$c
                  :guard (and (fn-cbor-octet-listp xs) (fn-octets$c-wfp fn-octets$c))))
  (let ((fn-octets$c (fn-octets$c-clear fn-octets$c)))
    (fn-oct-write-list xs fn-octets$c)))

; The octet arithmetic of a word, proved once here (arithmetic-5 stays
; local to this encapsulate).
(encapsulate
  ()
  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm fn-oct-mod-256-octet
    (implies (natp w)
             (and (natp (mod w 256))
                  (< (mod w 256) 256)
                  (unsigned-byte-p 8 (mod w 256))
                  (fn-cbor-octetp (mod w 256)))))

  (defthm fn-oct-floor-256-natp
    (implies (natp w) (natp (floor w 256)))
    :rule-classes ((:rewrite) (:type-prescription)))

  (defthm fn-oct-floor-256-ub56
    (implies (unsigned-byte-p 56 w) (unsigned-byte-p 56 (floor w 256))))

  (defthm fn-oct-mod-of-word
    (implies (and (fn-cbor-octetp a) (natp r))
             (equal (mod (+ a (* 256 r)) 256) a)))

  (defthm fn-oct-floor-of-word
    (implies (and (fn-cbor-octetp a) (natp r))
             (equal (floor (+ a (* 256 r)) 256) r))))

; Closed from here on: every fact this book needs of them is above.
(local (in-theory (disable mod floor)))

; The bulk exports (lane octets-bulk, 2026-09-27).  Before them every
; producer paid one export call per octet (6 to 20 ns each, measured by
; codec-c1), where the work is one array write.
;
; `fn-octets-append-back off n': append N octets, each the octet OFF back
; from the end at the time it is appended.  When N > OFF the run reads
; octets it has itself just written (an LZ match: offset 1 repeats one
; octet), so the logical definition is octet by octet
; (`fn-oct-back-copy'); the executable is one reservation and one loop of
; array writes (`fn-oct-back-loop'), which moves forward so that it reads
; exactly those octets.
;
; `fn-octets-get-word i k' / `fn-octets-append-word w k': the K octets at I
; read as one little-endian natural, and the K low octets of W appended.
; An export cannot take a second buffer (a `defabsstobj' :EXEC function is
; defined before the abstract stobj it serves, so it can name only the
; foundation), so a copy between two buffers moves words: at K <= 7 a
; word is a fixnum and two export calls carry seven octets
; (`fn-oct-word-octets-of-word-at' is the round trip).

(defun fn-oct-back-loop (src dst end fn-octets$c)
  ; buf[dst] := buf[src], both stepping, for DST below END.  SRC < DST.
  (declare (xargs :stobjs fn-octets$c
                  :guard (and (natp src) (natp dst) (natp end) (< src dst) (<= dst end)
                              (<= end (fn-octets$c-buf-length fn-octets$c)))
                  :measure (nfix (- (nfix end) (nfix dst)))))
  (if (and (mbt (and (natp src) (natp dst) (natp end) (< src dst)))
           (< dst end))
      (let ((fn-octets$c (update-fn-octets$c-bufi dst (fn-octets$c-bufi src fn-octets$c)
                                                  fn-octets$c)))
        (fn-oct-back-loop (1+ src) (1+ dst) end fn-octets$c))
    fn-octets$c))

(defun fn-octets$c-append-back (off n fn-octets$c)
  (declare (xargs :stobjs fn-octets$c
                  :guard (and (natp off) (<= 1 off) (<= off (fn-octets$c-fill fn-octets$c))
                              (natp n) (fn-octets$c-wfp fn-octets$c))))
  (let* ((top (fn-octets$c-fill fn-octets$c))
         (end (+ top n))
         (fn-octets$c (if (<= end (fn-octets$c-buf-length fn-octets$c))
                          fn-octets$c
                        (resize-fn-octets$c-buf (max 1024 (* 2 end)) fn-octets$c)))
         (fn-octets$c (fn-oct-back-loop (- top off) top end fn-octets$c)))
    (update-fn-octets$c-fill end fn-octets$c)))

(local
 (defthm fn-oct-bufp-cell-numberp
   (implies (and (fn-octets$c-bufp buf) (natp k) (< k (len buf)))
            (acl2-numberp (nth k buf)))))

(defun fn-oct-word-down (i k fn-octets$c)
  ; buf[i] + 256 buf[i+1] + ... over K cells.
  (declare (xargs :stobjs fn-octets$c
                  :guard (and (natp i) (natp k)
                              (<= (+ i k) (fn-octets$c-buf-length fn-octets$c)))
                  :measure (nfix k)))
  (if (zp k)
      0
    (+ (fn-octets$c-bufi i fn-octets$c)
       (* 256 (fn-oct-word-down (1+ i) (1- k) fn-octets$c)))))

(defun fn-oct-word7 (i fn-octets$c)
  ; The seven-octet word unrolled: each read is an octet, so the compiler
  ; keeps the whole sum in fixnum arithmetic.
  (declare (xargs :stobjs fn-octets$c
                  :guard (and (natp i) (<= (+ i 7) (fn-octets$c-buf-length fn-octets$c)))))
  (+ (fn-octets$c-bufi i fn-octets$c)
     (* 256 (+ (fn-octets$c-bufi (+ 1 i) fn-octets$c)
     (* 256 (+ (fn-octets$c-bufi (+ 2 i) fn-octets$c)
     (* 256 (+ (fn-octets$c-bufi (+ 3 i) fn-octets$c)
     (* 256 (+ (fn-octets$c-bufi (+ 4 i) fn-octets$c)
     (* 256 (+ (fn-octets$c-bufi (+ 5 i) fn-octets$c)
     (* 256 (fn-octets$c-bufi (+ 6 i) fn-octets$c))))))))))))))

(defthm fn-oct-word7-is-word-down
  (implies (natp i)
           (equal (fn-oct-word7 i fn-octets$c) (fn-oct-word-down i 7 fn-octets$c)))
  :hints (("Goal" :expand ((:free (i k) (fn-oct-word-down i k fn-octets$c))))))

(defun fn-octets$c-get-word (i k fn-octets$c)
  (declare (xargs :stobjs fn-octets$c
                  :guard (and (natp i) (natp k) (<= (+ i k) (fn-octets$c-fill fn-octets$c))
                              (fn-octets$c-wfp fn-octets$c))))
  (mbe :logic (fn-oct-word-down i k fn-octets$c)
       :exec (if (eql k 7)
                 (fn-oct-word7 i fn-octets$c)
               (fn-oct-word-down i k fn-octets$c))))

(defun fn-oct-word-loop (w dst end fn-octets$c)
  ; buf[dst] := w mod 256, w := w div 256, for DST below END.  W is a
  ; fixnum here (the export takes the octet-list path for a wider W).
  (declare (type (unsigned-byte 56) w)
           (xargs :stobjs fn-octets$c
                  :guard (and (natp dst) (natp end) (<= dst end)
                              (<= end (fn-octets$c-buf-length fn-octets$c)))
                  :measure (nfix (- (nfix end) (nfix dst)))))
  (if (and (mbt (and (natp dst) (natp end) (natp w))) (< dst end))
      (let ((fn-octets$c (update-fn-octets$c-bufi dst (mod w 256) fn-octets$c)))
        (fn-oct-word-loop (floor w 256) (1+ dst) end fn-octets$c))
    fn-octets$c))

; The K low octets of W, least significant first.
(defun fn-oct-word-octets (w k)
  (declare (xargs :guard t :measure (nfix k)))
  (if (posp k)
      (cons (mod (nfix w) 256) (fn-oct-word-octets (floor (nfix w) 256) (1- k)))
    nil))

(defthm fn-oct-len-of-word-octets
  (equal (len (fn-oct-word-octets w k)) (nfix k)))

(defthm fn-oct-true-listp-of-word-octets
  (true-listp (fn-oct-word-octets w k))
  :rule-classes ((:rewrite) (:type-prescription)))

(defthm fn-oct-octet-listp-of-word-octets
  (fn-cbor-octet-listp (fn-oct-word-octets w k)))

(defun fn-octets$c-append-word (w k fn-octets$c)
  (declare (xargs :stobjs fn-octets$c
                  :guard (and (natp w) (natp k) (fn-octets$c-wfp fn-octets$c))))
  (if (unsigned-byte-p 56 w)
      (let* ((top (fn-octets$c-fill fn-octets$c))
             (end (+ top k))
             (fn-octets$c (if (<= end (fn-octets$c-buf-length fn-octets$c))
                              fn-octets$c
                            (resize-fn-octets$c-buf (max 1024 (* 2 end)) fn-octets$c)))
             (fn-octets$c (fn-oct-word-loop w top end fn-octets$c)))
        (update-fn-octets$c-fill end fn-octets$c))
    (fn-oct-write-list (fn-oct-word-octets w k) fn-octets$c)))

; -----------------------------------------------------------------------------
; The logical side: the octet list itself.  The :logic functions never run
; (the exec twins do), so each is written over guard-free list helpers that
; equal `nth', `append' and `update-nth' on true lists, which every value of
; the stobj is (its recognizer is `fn-cbor-octet-listp').

(defun fn-oct-nth (i xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (if (or (not (natp i)) (= i 0)) (car xs) (fn-oct-nth (1- i) (cdr xs)))
    nil))

(defthm fn-oct-nth-is-nth
  (equal (fn-oct-nth i xs) (nth i xs)))

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-oct-snoc-loop (xs o acc)
  (declare (xargs :guard (true-listp acc) :verify-guards nil))
  (if (consp xs)
      (fn-oct-snoc-loop (cdr xs) o (cons (car xs) acc))
    (revappend acc (list o))))

(defun fn-oct-snoc (xs o)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp xs)
           (cons (car xs) (fn-oct-snoc (cdr xs) o))
         (list o))
       :exec (fn-oct-snoc-loop xs o nil)))

(local
 (defthm fn-oct-snoc-loop-is-revappend
   (equal (fn-oct-snoc-loop xs o acc)
          (revappend acc (fn-oct-snoc xs o)))
   :hints (("Goal" :induct (fn-oct-snoc-loop xs o acc)
                   :in-theory (union-theories '(fn-oct-snoc-loop fn-oct-snoc revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-oct-snoc-loop)

(verify-guards fn-oct-snoc
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-oct-snoc)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-oct-snoc-loop-is-revappend (acc nil))))))


(defthm fn-oct-snoc-is-append
  (implies (true-listp xs)
           (equal (fn-oct-snoc xs o) (append xs (list o)))))

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-oct-update-loop (i o xs acc)
  (declare (xargs :guard (true-listp acc) :verify-guards nil))
  (if (or (not (natp i)) (= i 0))
      (revappend acc (cons o (if (consp xs) (cdr xs) nil)))
    (fn-oct-update-loop (1- i)
                        o
                        (if (consp xs) (cdr xs) nil)
                        (cons (if (consp xs) (car xs) nil) acc))))

(defun fn-oct-update (i o xs)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (or (not (natp i)) (= i 0))
           (cons o (if (consp xs) (cdr xs) nil))
         (cons (if (consp xs) (car xs) nil)
               (fn-oct-update (1- i) o (if (consp xs) (cdr xs) nil))))
       :exec (fn-oct-update-loop i o xs nil)))

(local
 (defthm fn-oct-update-loop-is-revappend
   (equal (fn-oct-update-loop i o xs acc)
          (revappend acc (fn-oct-update i o xs)))
   :hints (("Goal" :induct (fn-oct-update-loop i o xs acc)
                   :in-theory (union-theories '(fn-oct-update-loop fn-oct-update revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-oct-update-loop)

(verify-guards fn-oct-update
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-oct-update)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-oct-update-loop-is-revappend (acc nil))))))


(defthm fn-oct-update-is-update-nth
  (implies (and (natp i) (< i (len xs)) (true-listp xs))
           (equal (fn-oct-update i o xs) (update-nth i o xs))))

(defthm fn-oct-octet-listp-of-update-nth
  (implies (and (fn-cbor-octet-listp xs) (fn-cbor-octetp o) (natp i) (< i (len xs)))
           (fn-cbor-octet-listp (update-nth i o xs))))

(defthm fn-oct-octet-listp-of-append-one
  (implies (and (fn-cbor-octet-listp xs) (fn-cbor-octetp o))
           (fn-cbor-octet-listp (append xs (list o)))))

(defun fn-octets$ap (x)
  (declare (xargs :guard t))
  (fn-cbor-octet-listp x))

(defun create-fn-octets$a ()
  (declare (xargs :guard t))
  nil)

(defun fn-octets$a-len (fn-octets$a)
  (declare (xargs :guard t))
  (len fn-octets$a))

(defun fn-octets$a-get (i fn-octets$a)
  (declare (xargs :guard (and (natp i) (< i (fn-octets$a-len fn-octets$a)))))
  (fn-oct-nth i fn-octets$a))

(defun fn-octets$a-put (i o fn-octets$a)
  (declare (xargs :guard (and (natp i) (< i (fn-octets$a-len fn-octets$a))
                              (fn-cbor-octetp o))))
  (fn-oct-update i o fn-octets$a))

(defun fn-octets$a-append-octet (o fn-octets$a)
  (declare (xargs :guard (fn-cbor-octetp o)))
  (fn-oct-snoc fn-octets$a o))

(defun fn-octets$a-clear (fn-octets$a)
  (declare (xargs :guard t) (ignore fn-octets$a))
  nil)

(defun fn-octets$a-reserve (n fn-octets$a)
  (declare (xargs :guard (natp n)) (ignore n))
  fn-octets$a)

(defun fn-octets$a-list (fn-octets$a)
  (declare (xargs :guard t))
  fn-octets$a)

(defun fn-octets$a-from-list (xs fn-octets$a)
  (declare (xargs :guard (fn-cbor-octet-listp xs)) (ignore fn-octets$a))
  xs)

; The bulk append (PKT-315): one export call writes a whole octet list at
; the fill point.  Its logical value is `append' on the list, written over
; the guard-free `fn-oct-cat' as the other :logic functions are; the
; executable is `fn-oct-write-list' above, whose lemma
; `fn-oct-write-list-steps' is the correspondence.  Before this export a
; codec twin made one :protect'ed `fn-octets-append-octet' call per octet.
(defun fn-oct-cat (xs ys)
  (declare (xargs :guard t))
  (if (consp xs) (cons (car xs) (fn-oct-cat (cdr xs) ys)) ys))

(defthm fn-oct-cat-is-append
  (equal (fn-oct-cat xs ys) (append xs ys)))

(defthm fn-oct-octet-listp-of-append
  (implies (and (fn-cbor-octet-listp xs) (fn-cbor-octet-listp ys))
           (fn-cbor-octet-listp (append xs ys))))

(defun fn-octets$a-append-list (xs fn-octets$a)
  (declare (xargs :guard (fn-cbor-octet-listp xs)))
  (fn-oct-cat fn-octets$a xs))

; The bulk exports' logical side (lane octets-bulk).  An LZ-shaped back
; copy is defined octet by octet: each appended octet is the one OFF back
; from the end AT THE TIME it is appended, so a run longer than OFF
; repeats what it has just written.
(defun fn-oct-back-copy (off n xs)
  (declare (xargs :guard t :measure (nfix n)))
  (if (and (posp n) (posp off) (<= off (len xs)))
      (fn-oct-back-copy off (1- n) (fn-oct-snoc xs (fn-oct-nth (- (len xs) off) xs)))
    xs))

; The K octets at I as one little-endian natural.
(defun fn-oct-word-at (i k xs)
  (declare (xargs :guard t :measure (nfix k)))
  (if (posp k)
      (+ (nfix (fn-oct-nth i xs)) (* 256 (fn-oct-word-at (1+ (nfix i)) (1- k) xs)))
    0))


(local
 (defthm fn-oct-nth-octetp-of-octet-listp
   (implies (and (fn-cbor-octet-listp xs) (natp j) (< j (len xs)))
            (fn-cbor-octetp (nth j xs)))))

(defthm fn-oct-octet-listp-of-back-copy
  (implies (fn-cbor-octet-listp xs)
           (fn-cbor-octet-listp (fn-oct-back-copy off n xs))))




(defthm fn-oct-natp-word-at
  (natp (fn-oct-word-at i k xs))
  :rule-classes :type-prescription)

(defun fn-octets$a-append-back (off n fn-octets$a)
  (declare (xargs :guard (and (natp off) (<= 1 off) (<= off (fn-octets$a-len fn-octets$a))
                              (natp n))))
  (fn-oct-back-copy off n fn-octets$a))

(defun fn-octets$a-get-word (i k fn-octets$a)
  (declare (xargs :guard (and (natp i) (natp k) (<= (+ i k) (fn-octets$a-len fn-octets$a)))))
  (fn-oct-word-at i k fn-octets$a))

(defun fn-octets$a-append-word (w k fn-octets$a)
  (declare (xargs :guard (and (natp w) (natp k))))
  (fn-oct-cat fn-octets$a (fn-oct-word-octets w k)))

; The round trip: the K octets of the word at I are the K octets at I.  A
; copy between two buffers by words is the copy of the octets.
(defthm fn-oct-word-octets-of-cons-word
  (implies (and (fn-cbor-octetp a) (natp r) (posp k))
           (equal (fn-oct-word-octets (+ a (* 256 r)) k)
                  (cons a (fn-oct-word-octets r (1- k)))))
  :hints (("Goal" :expand ((fn-oct-word-octets (+ a (* 256 r)) k)))))

(encapsulate
  ()
  (local
   (defthm fn-oct-nth-octet-of-listp
     (implies (and (fn-cbor-octet-listp xs) (natp i) (< i (len xs)))
              (and (fn-cbor-octetp (nth i xs))
                   (integerp (nth i xs))
                   (<= 0 (nth i xs))))))

  (local
   (defun fn-oct-rt-ind (i k xs)
     (declare (xargs :measure (nfix k)))
     (if (posp k) (fn-oct-rt-ind (1+ (nfix i)) (1- k) xs) (list i xs))))

  (local
   (defthm fn-oct-nthcdr-cons-split
     (implies (and (natp i) (< i (len xs)))
              (equal (nthcdr i xs) (cons (nth i xs) (nthcdr (1+ i) xs))))
     :hints (("Goal" :in-theory (enable nth nthcdr)))))

  (defthm fn-oct-word-octets-of-word-at
    (implies (and (fn-cbor-octet-listp xs) (natp i) (<= (+ i k) (len xs)))
             (equal (fn-oct-word-octets (fn-oct-word-at i k xs) k)
                    (take k (nthcdr i xs))))
    :hints (("Goal" :induct (fn-oct-rt-ind i k xs)
             :in-theory (disable nth nthcdr fn-cbor-octetp fn-oct-word-octets)
             :expand ((fn-oct-word-octets 0 k))))))

; -----------------------------------------------------------------------------
; The abstraction relation.

(defun fn-octets$corr (fn-octets$c fn-octets$a)
  ; The concrete object is an ordinary value here, so that its array can be
  ; read as the list it is.
  (declare (xargs :verify-guards nil))
  (and (fn-octets$cp fn-octets$c)
       (fn-cbor-octet-listp fn-octets$a)
       (<= (nth *fn-octets$c-fill* fn-octets$c) (len (nth *fn-octets$c-bufi* fn-octets$c)))
       (equal (fn-oct-list-from 0 (nth *fn-octets$c-fill* fn-octets$c)
                                (nth *fn-octets$c-bufi* fn-octets$c))
              fn-octets$a)))

; From here on `nth' and `update-nth' stay closed: opened at a constant
; index they turn the stobj into car/cdr/cons forms that no lemma is about
; (rep-sha256, 2026-09-25).  The built-in `nth-update-nth',
; `len-update-nth' and `true-listp-update-nth' read through the writers.
(local (in-theory (disable nth update-nth)))
(local (in-theory (enable update-nth-array)))

; What the concrete recognizer says about the two fields, and that the
; two writers and the resize keep it.

(defthm fn-oct-cp-fields
  (implies (fn-octets$cp fn-octets$c)
           (and (true-listp fn-octets$c)
                (equal (len fn-octets$c) 2)
                (fn-octets$c-bufp (nth 0 fn-octets$c))
                (integerp (nth 1 fn-octets$c))
                (<= 0 (nth 1 fn-octets$c))))
  :rule-classes ((:forward-chaining :trigger-terms ((fn-octets$cp fn-octets$c)))))

(defthm fn-oct-cp-of-update-buf
  ; Replacing the array by any well-formed array keeps the recognizer; the
  ; writes and the resize produce well-formed arrays by the list lemmas.
  (implies (and (fn-octets$cp fn-octets$c) (fn-octets$c-bufp buf))
           (fn-octets$cp (update-nth 0 buf fn-octets$c))))

(defthm fn-oct-cp-of-update-fill
  (implies (and (fn-octets$cp fn-octets$c) (natp n))
           (fn-octets$cp (update-nth 1 n fn-octets$c))))

(defthm fn-oct-octetp-is-unsigned-byte-p
  (implies (fn-cbor-octetp o) (unsigned-byte-p 8 o)))

(local (in-theory (disable fn-octets$cp)))

; One append at the fill point: the abstraction extends by one, the
; concrete invariant is kept.  The lemma every chain of writes uses.

(defthm fn-oct-append-octet-step
  (implies (and (fn-octets$cp fn-octets$c)
                (<= (nth 1 fn-octets$c) (len (nth 0 fn-octets$c)))
                (fn-cbor-octetp o))
           (let ((next (fn-octets$c-append-octet o fn-octets$c)))
             (and (fn-octets$cp next)
                  (<= (nth 1 next) (len (nth 0 next)))
                  (equal (fn-oct-list-from 0 (nth 1 next) (nth 0 next))
                         (append (fn-oct-list-from 0 (nth 1 fn-octets$c) (nth 0 fn-octets$c))
                                 (list o))))))
  :hints (("Goal" :use ((:instance fn-oct-list-from-snoc
                                   (i 0) (n (nth 1 fn-octets$c))
                                   (buf (update-nth (nth 1 fn-octets$c) o (nth 0 fn-octets$c))))
                        (:instance fn-oct-list-from-snoc
                                   (i 0) (n (nth 1 fn-octets$c))
                                   (buf (update-nth (nth 1 fn-octets$c) o
                                                    (resize-list (nth 0 fn-octets$c)
                                                                 (max 1024 (* 2 (nth 1 fn-octets$c)))
                                                                 0))))))))

(local (in-theory (disable fn-octets$c-append-octet)))

(defthm fn-oct-write-list-steps
  (implies (and (fn-octets$cp fn-octets$c)
                (<= (nth 1 fn-octets$c) (len (nth 0 fn-octets$c)))
                (fn-cbor-octet-listp xs))
           (let ((next (fn-oct-write-list xs fn-octets$c)))
             (and (fn-octets$cp next)
                  (<= (nth 1 next) (len (nth 0 next)))
                  (equal (fn-oct-list-from 0 (nth 1 next) (nth 0 next))
                         (append (fn-oct-list-from 0 (nth 1 fn-octets$c) (nth 0 fn-octets$c))
                                 xs)))))
  :hints (("Goal" :induct (fn-oct-write-list xs fn-octets$c)
           :in-theory (disable fn-oct-list-from))))

; The bulk exports' loops, each as its effect on the abstraction.

(local
 (defthmd fn-oct-back-copy-open
   (implies (and (posp n) (posp off) (natp j) (equal (+ j off) (len xs)) (true-listp xs))
            (equal (fn-oct-back-copy off n xs)
                   (fn-oct-back-copy off (1- n) (append xs (list (nth j xs))))))
   :hints (("Goal" :expand ((fn-oct-back-copy off n xs)) :do-not-induct t))))

(defthm fn-oct-back-loop-steps
  (implies (and (fn-octets$cp fn-octets$c)
                (natp src) (natp dst) (natp end) (< src dst) (<= dst end)
                (<= end (len (nth 0 fn-octets$c))))
           (let ((next (fn-oct-back-loop src dst end fn-octets$c)))
             (and (fn-octets$cp next)
                  (equal (nth 1 next) (nth 1 fn-octets$c))
                  (equal (len (nth 0 next)) (len (nth 0 fn-octets$c)))
                  (equal (fn-oct-list-from 0 end (nth 0 next))
                         (fn-oct-back-copy (- dst src) (- end dst)
                                           (fn-oct-list-from 0 dst (nth 0 fn-octets$c)))))))
  :hints (("Goal" :induct (fn-oct-back-loop src dst end fn-octets$c))
          ("Subgoal *1/1" :use ((:instance fn-oct-back-copy-open
                                           (off (- dst src)) (n (- end dst)) (j src)
                                           (xs (fn-oct-list-from 0 dst (nth 0 fn-octets$c))))
                                (:instance fn-oct-list-from-snoc
                                           (i 0) (n dst)
                                           (buf (update-nth dst (nth src (nth 0 fn-octets$c))
                                                            (nth 0 fn-octets$c))))
                                (:instance fn-oct-nth-of-list-from
                                           (i 0) (n dst) (k src)
                                           (buf (nth 0 fn-octets$c)))))))

(defthm fn-oct-word-loop-steps
  (implies (and (fn-octets$cp fn-octets$c)
                (natp w) (natp dst) (natp end) (<= dst end)
                (<= end (len (nth 0 fn-octets$c))))
           (let ((next (fn-oct-word-loop w dst end fn-octets$c)))
             (and (fn-octets$cp next)
                  (equal (nth 1 next) (nth 1 fn-octets$c))
                  (equal (len (nth 0 next)) (len (nth 0 fn-octets$c)))
                  (equal (fn-oct-list-from 0 end (nth 0 next))
                         (append (fn-oct-list-from 0 dst (nth 0 fn-octets$c))
                                 (fn-oct-word-octets w (- end dst)))))))
  :hints (("Goal" :induct (fn-oct-word-loop w dst end fn-octets$c))
          ("Subgoal *1/1" :use ((:instance fn-oct-list-from-snoc
                                           (i 0) (n dst)
                                           (buf (update-nth dst (mod w 256)
                                                            (nth 0 fn-octets$c))))))))

(defthm fn-oct-word-down-is-word-at
  (implies (and (fn-octets$cp fn-octets$c)
                (natp i) (natp k) (natp n) (<= (+ i k) n)
                (<= n (len (nth 0 fn-octets$c))))
           (equal (fn-oct-word-down i k fn-octets$c)
                  (fn-oct-word-at i k (fn-oct-list-from 0 n (nth 0 fn-octets$c)))))
  :hints (("Goal" :induct (fn-oct-word-down i k fn-octets$c))))

(local (in-theory (disable fn-oct-back-loop fn-oct-word-loop fn-oct-word-down)))

(local
 (defthm fn-oct-minus-minus
   (implies (acl2-numberp x) (equal (- (- x)) x))))

; -----------------------------------------------------------------------------
; The obligations, each as `defabsstobj-missing-events' states it.

(defthm create-fn-octets{correspondence}
  (fn-octets$corr (create-fn-octets$c) (create-fn-octets$a))
  :rule-classes nil)

(defthm create-fn-octets{preserved}
  (fn-octets$ap (create-fn-octets$a))
  :rule-classes nil)

(defthm fn-octets-len{correspondence}
  (implies (fn-octets$corr fn-octets$c fn-octets)
           (equal (fn-octets$c-len fn-octets$c) (fn-octets$a-len fn-octets)))
  :rule-classes nil)

(defthm fn-octets-get{correspondence}
  (implies (and (fn-octets$corr fn-octets$c fn-octets)
                (natp i) (< i (fn-octets$a-len fn-octets)))
           (equal (fn-octets$c-get i fn-octets$c) (fn-octets$a-get i fn-octets)))
  :rule-classes nil)

(defthm fn-octets-get{guard-thm}
  (implies (and (fn-octets$corr fn-octets$c fn-octets)
                (natp i) (< i (fn-octets$a-len fn-octets)))
           (and (natp i) (< i (fn-octets$c-fill fn-octets$c))
                (fn-octets$c-wfp fn-octets$c)))
  :rule-classes nil)

(defthm fn-octets-put{correspondence}
  (implies (and (fn-octets$corr fn-octets$c fn-octets)
                (natp i) (< i (fn-octets$a-len fn-octets)) (fn-cbor-octetp o))
           (fn-octets$corr (fn-octets$c-put i o fn-octets$c)
                           (fn-octets$a-put i o fn-octets)))
  :rule-classes nil)

(defthm fn-octets-put{guard-thm}
  (implies (and (fn-octets$corr fn-octets$c fn-octets)
                (natp i) (< i (fn-octets$a-len fn-octets)) (fn-cbor-octetp o))
           (and (natp i) (< i (fn-octets$c-fill fn-octets$c))
                (fn-cbor-octetp o) (fn-octets$c-wfp fn-octets$c)))
  :rule-classes nil)

(defthm fn-octets-put{preserved}
  (implies (and (fn-octets$ap fn-octets)
                (natp i) (< i (fn-octets$a-len fn-octets)) (fn-cbor-octetp o))
           (fn-octets$ap (fn-octets$a-put i o fn-octets)))
  :rule-classes nil)

(defthm fn-octets-append-octet{correspondence}
  (implies (and (fn-octets$corr fn-octets$c fn-octets) (fn-cbor-octetp o))
           (fn-octets$corr (fn-octets$c-append-octet o fn-octets$c)
                           (fn-octets$a-append-octet o fn-octets)))
  :rule-classes nil)

(defthm fn-octets-append-octet{guard-thm}
  (implies (and (fn-octets$corr fn-octets$c fn-octets) (fn-cbor-octetp o))
           (and (fn-cbor-octetp o) (fn-octets$c-wfp fn-octets$c)))
  :rule-classes nil)

(defthm fn-octets-append-octet{preserved}
  (implies (and (fn-octets$ap fn-octets) (fn-cbor-octetp o))
           (fn-octets$ap (fn-octets$a-append-octet o fn-octets)))
  :rule-classes nil)

(defthm fn-octets-clear{correspondence}
  (implies (fn-octets$corr fn-octets$c fn-octets)
           (fn-octets$corr (fn-octets$c-clear fn-octets$c) (fn-octets$a-clear fn-octets)))
  :rule-classes nil)

(defthm fn-octets-clear{preserved}
  (implies (fn-octets$ap fn-octets)
           (fn-octets$ap (fn-octets$a-clear fn-octets)))
  :rule-classes nil)

(defthm fn-octets-reserve{correspondence}
  (implies (and (fn-octets$corr fn-octets$c fn-octets) (natp n))
           (fn-octets$corr (fn-octets$c-reserve n fn-octets$c)
                           (fn-octets$a-reserve n fn-octets)))
  :rule-classes nil)

(defthm fn-octets-reserve{preserved}
  (implies (and (fn-octets$ap fn-octets) (natp n))
           (fn-octets$ap (fn-octets$a-reserve n fn-octets)))
  :rule-classes nil)

(defthm fn-octets-list{correspondence}
  (implies (fn-octets$corr fn-octets$c fn-octets)
           (equal (fn-octets$c-list fn-octets$c) (fn-octets$a-list fn-octets)))
  :rule-classes nil)

(defthm fn-octets-list{guard-thm}
  (implies (fn-octets$corr fn-octets$c fn-octets)
           (fn-octets$c-wfp fn-octets$c))
  :rule-classes nil)

(defthm fn-octets-from-list{correspondence}
  (implies (and (fn-octets$corr fn-octets$c fn-octets) (fn-cbor-octet-listp xs))
           (fn-octets$corr (fn-octets$c-from-list xs fn-octets$c)
                           (fn-octets$a-from-list xs fn-octets)))
  :rule-classes nil)

(defthm fn-octets-from-list{guard-thm}
  (implies (and (fn-octets$corr fn-octets$c fn-octets) (fn-cbor-octet-listp xs))
           (and (fn-cbor-octet-listp xs) (fn-octets$c-wfp fn-octets$c)))
  :rule-classes nil)

(defthm fn-octets-from-list{preserved}
  (implies (and (fn-octets$ap fn-octets) (fn-cbor-octet-listp xs))
           (fn-octets$ap (fn-octets$a-from-list xs fn-octets)))
  :rule-classes nil)

(defthm fn-octets-append-list{correspondence}
  (implies (and (fn-octets$corr fn-octets$c fn-octets) (fn-cbor-octet-listp xs))
           (fn-octets$corr (fn-oct-write-list xs fn-octets$c)
                           (fn-octets$a-append-list xs fn-octets)))
  :rule-classes nil)

(defthm fn-octets-append-list{guard-thm}
  (implies (and (fn-octets$corr fn-octets$c fn-octets) (fn-cbor-octet-listp xs))
           (and (fn-cbor-octet-listp xs) (fn-octets$c-wfp fn-octets$c)))
  :rule-classes nil)

(defthm fn-octets-append-list{preserved}
  (implies (and (fn-octets$ap fn-octets) (fn-cbor-octet-listp xs))
           (fn-octets$ap (fn-octets$a-append-list xs fn-octets)))
  :rule-classes nil)

(defthm fn-octets-append-back{correspondence}
  (implies (and (fn-octets$corr fn-octets$c fn-octets)
                (natp off) (<= 1 off) (<= off (fn-octets$a-len fn-octets)) (natp n))
           (fn-octets$corr (fn-octets$c-append-back off n fn-octets$c)
                           (fn-octets$a-append-back off n fn-octets)))
  :rule-classes nil)

(defthm fn-octets-append-back{guard-thm}
  (implies (and (fn-octets$corr fn-octets$c fn-octets)
                (natp off) (<= 1 off) (<= off (fn-octets$a-len fn-octets)) (natp n))
           (and (natp off) (<= 1 off) (<= off (fn-octets$c-fill fn-octets$c))
                (natp n) (fn-octets$c-wfp fn-octets$c)))
  :rule-classes nil)

(defthm fn-octets-append-back{preserved}
  (implies (and (fn-octets$ap fn-octets)
                (natp off) (<= 1 off) (<= off (fn-octets$a-len fn-octets)) (natp n))
           (fn-octets$ap (fn-octets$a-append-back off n fn-octets)))
  :rule-classes nil)

(defthm fn-octets-get-word{correspondence}
  (implies (and (fn-octets$corr fn-octets$c fn-octets)
                (natp i) (natp k) (<= (+ i k) (fn-octets$a-len fn-octets)))
           (equal (fn-octets$c-get-word i k fn-octets$c)
                  (fn-octets$a-get-word i k fn-octets)))
  :rule-classes nil)

(defthm fn-octets-get-word{guard-thm}
  (implies (and (fn-octets$corr fn-octets$c fn-octets)
                (natp i) (natp k) (<= (+ i k) (fn-octets$a-len fn-octets)))
           (and (natp i) (natp k) (<= (+ i k) (fn-octets$c-fill fn-octets$c))
                (fn-octets$c-wfp fn-octets$c)))
  :rule-classes nil)

(defthm fn-octets-append-word{correspondence}
  (implies (and (fn-octets$corr fn-octets$c fn-octets) (natp w) (natp k))
           (fn-octets$corr (fn-octets$c-append-word w k fn-octets$c)
                           (fn-octets$a-append-word w k fn-octets)))
  :rule-classes nil)

(defthm fn-octets-append-word{guard-thm}
  (implies (and (fn-octets$corr fn-octets$c fn-octets) (natp w) (natp k))
           (and (natp w) (natp k) (fn-octets$c-wfp fn-octets$c)))
  :rule-classes nil)

(defthm fn-octets-append-word{preserved}
  (implies (and (fn-octets$ap fn-octets) (natp w) (natp k))
           (fn-octets$ap (fn-octets$a-append-word w k fn-octets)))
  :rule-classes nil)

(defabsstobj fn-octets
  :foundation fn-octets$c
  :recognizer (fn-octets-p :logic fn-octets$ap :exec fn-octets$cp)
  :creator (create-fn-octets :logic create-fn-octets$a :exec create-fn-octets$c)
  :corr-fn fn-octets$corr
  :exports ((fn-octets-len :logic fn-octets$a-len :exec fn-octets$c-len)
            (fn-octets-get :logic fn-octets$a-get :exec fn-octets$c-get)
            (fn-octets-put :logic fn-octets$a-put :exec fn-octets$c-put :protect t)
            (fn-octets-append-octet :logic fn-octets$a-append-octet
                                    :exec fn-octets$c-append-octet :protect t)
            (fn-octets-clear :logic fn-octets$a-clear :exec fn-octets$c-clear)
            (fn-octets-reserve :logic fn-octets$a-reserve :exec fn-octets$c-reserve
                               :protect t)
            (fn-octets-list :logic fn-octets$a-list :exec fn-octets$c-list)
            (fn-octets-from-list :logic fn-octets$a-from-list
                                 :exec fn-octets$c-from-list :protect t)
            (fn-octets-append-list :logic fn-octets$a-append-list
                                   :exec fn-oct-write-list :protect t)
            (fn-octets-append-back :logic fn-octets$a-append-back
                                   :exec fn-octets$c-append-back :protect t)
            (fn-octets-get-word :logic fn-octets$a-get-word :exec fn-octets$c-get-word)
            (fn-octets-append-word :logic fn-octets$a-append-word
                                   :exec fn-octets$c-append-word :protect t)))

; -----------------------------------------------------------------------------
; The logical view, opened: the stobj's value is the list, its length is
; `len', a read is `nth'.  A cell of the logical list is an octet.

(defthm fn-oct-octets-p-is-octet-listp
  (equal (fn-octets-p x) (fn-cbor-octet-listp x)))

(defthm fn-oct-len-is-len
  (equal (fn-octets-len fn-octets) (len fn-octets)))

(defthm fn-oct-get-is-nth
  (equal (fn-octets-get i fn-octets) (nth i fn-octets)))

(defthm fn-oct-list-is-identity
  (equal (fn-octets-list fn-octets) fn-octets))

(defthm fn-oct-append-list-is-append
  (equal (fn-octets-append-list xs fn-octets) (append fn-octets xs)))

(defthm fn-oct-append-back-is-back-copy
  (equal (fn-octets-append-back off n fn-octets) (fn-oct-back-copy off n fn-octets)))

(defthm fn-oct-get-word-is-word-at
  (equal (fn-octets-get-word i k fn-octets) (fn-oct-word-at i k fn-octets)))

(defthm fn-oct-append-word-is-append
  (equal (fn-octets-append-word w k fn-octets)
         (append fn-octets (fn-oct-word-octets w k))))

(defthm fn-oct-nth-of-octet-listp-is-octet
  (implies (and (fn-cbor-octet-listp xs) (natp k) (< k (len xs)))
           (and (integerp (nth k xs))
                (<= 0 (nth k xs))
                (< (nth k xs) 256)))
  :rule-classes ((:rewrite :corollary
                  (implies (and (fn-cbor-octet-listp xs) (natp k) (< k (len xs)))
                           (and (integerp (nth k xs)) (<= 0 (nth k xs)) (< (nth k xs) 256))))
                 (:rewrite :corollary
                  (implies (and (fn-cbor-octet-listp xs) (natp k) (< k (len xs)))
                           (fn-cbor-octetp (nth k xs)))))
  :hints (("Goal" :in-theory (enable nth))))

; What a buffer value is, for every guard and theorem over the stobj.
(defthm fn-oct-octets-p-forward
  (implies (fn-octets-p x)
           (and (fn-cbor-octet-listp x) (true-listp x)))
  :rule-classes :forward-chaining)

(in-theory (disable fn-octets-p fn-octets-len fn-octets-get fn-octets-list
                    fn-octets-append-list fn-octets-append-back fn-octets-get-word
                    fn-octets-append-word fn-oct-octets-p-is-octet-listp))

; -----------------------------------------------------------------------------
; Derived readers over the abstract stobj: the vocabulary a codec twin reads
; the buffer with.  Each is equal to its list term over the logical value.

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-oct-slice-list-loop (i n fn-octets acc)
  (declare (xargs :stobjs fn-octets :measure (nfix (- n i)) :guard (and (and (natp i) (natp n) (<= i n) (<= n (fn-octets-len fn-octets))) (true-listp acc)) :verify-guards nil))
  (if (or (not (natp i)) (not (natp n)) (<= n i))
      (revappend acc nil)
    (fn-oct-slice-list-loop (1+ i) n fn-octets (cons (fn-octets-get i fn-octets) acc))))

(defun fn-oct-slice-list (i n fn-octets)
  ; st[i..n) as a list.
  (declare (xargs :verify-guards nil :stobjs fn-octets
                  :guard (and (natp i) (natp n) (<= i n) (<= n (fn-octets-len fn-octets)))
                  :measure (nfix (- n i))))
  (mbe :logic
       (if (or (not (natp i)) (not (natp n)) (<= n i))
           nil
         (cons (fn-octets-get i fn-octets)
               (fn-oct-slice-list (1+ i) n fn-octets)))
       :exec (fn-oct-slice-list-loop i n fn-octets nil)))

(local
 (defthm fn-oct-slice-list-loop-is-revappend
   (equal (fn-oct-slice-list-loop i n fn-octets acc)
          (revappend acc (fn-oct-slice-list i n fn-octets)))
   :hints (("Goal" :induct (fn-oct-slice-list-loop i n fn-octets acc)
                   :in-theory (union-theories '(fn-oct-slice-list-loop fn-oct-slice-list revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-oct-slice-list-loop)

(verify-guards fn-oct-slice-list
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-oct-slice-list)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-oct-slice-list-loop-is-revappend (acc nil))))))


(defun fn-oct-prefix-equalp (i xs fn-octets)
  ; Whether st[i..) opens with XS, read in place.  XS is any object.
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (<= i (fn-octets-len fn-octets)))
                  :measure (len xs)))
  (if (atom xs)
      t
    (and (< i (fn-octets-len fn-octets))
         (equal (fn-octets-get i fn-octets) (car xs))
         (fn-oct-prefix-equalp (1+ i) (cdr xs) fn-octets))))

(defun fn-oct-suffix-equalp (i xs fn-octets)
  ; Whether st[i..len) is exactly XS, read in place.  XS is any object: the
  ; walk is total over it, and a non-list answers nil at the buffer's end.
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (<= i (fn-octets-len fn-octets)))
                  :measure (nfix (- (fn-octets-len fn-octets) i))))
  (if (or (not (natp i)) (>= i (fn-octets-len fn-octets)))
      (null xs)
    (and (consp xs)
         (equal (fn-octets-get i fn-octets) (car xs))
         (fn-oct-suffix-equalp (1+ i) (cdr xs) fn-octets))))

(defun fn-oct-line-end (i fn-octets)
  ; The index just past the first LF at or after I, or the length.
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (<= i (fn-octets-len fn-octets)))
                  :measure (nfix (- (fn-octets-len fn-octets) i))))
  (if (or (not (natp i)) (>= i (fn-octets-len fn-octets)))
      (fn-octets-len fn-octets)
    (if (equal (fn-octets-get i fn-octets) 10)
        (1+ i)
      (fn-oct-line-end (1+ i) fn-octets))))

; The list facts the correspondences rest on.

(local
 (defthm fn-oct-nthcdr-of-true-listp
   (implies (true-listp xs) (true-listp (nthcdr i xs)))
   :hints (("Goal" :in-theory (enable nthcdr)))))

(local
 (defthm fn-oct-consp-nthcdr-within
   (implies (and (natp i) (true-listp xs) (< i (len xs)))
            (consp (nthcdr i xs)))
   :hints (("Goal" :in-theory (enable nthcdr)))))

(local
 (defthm fn-oct-consp-nthcdr-beyond
   (implies (and (natp i) (true-listp xs) (<= (len xs) i))
            (not (consp (nthcdr i xs))))
   :hints (("Goal" :in-theory (enable nthcdr)))))

(local
 (defthm fn-oct-nthcdr-beyond-is-nil
   (implies (and (natp i) (true-listp xs) (<= (len xs) i))
            (equal (nthcdr i xs) nil))
   :hints (("Goal" :in-theory (enable nthcdr)))))

(local
 (defthm fn-oct-car-nthcdr
   (equal (car (nthcdr i xs)) (nth i xs))
   :hints (("Goal" :in-theory (enable nth nthcdr)))))

(local
 (defthm fn-oct-cdr-nthcdr
   (implies (natp i)
            (equal (cdr (nthcdr i xs)) (nthcdr (1+ i) xs)))
   :hints (("Goal" :in-theory (enable nthcdr)))))

(local
 (defthm fn-oct-nthcdr-equal-split
   (implies (and (natp i) (< i (len l)) (true-listp l))
            (equal (equal (nthcdr i l) xs)
                   (and (consp xs) (equal (nth i l) (car xs))
                        (equal (nthcdr (1+ i) l) (cdr xs)))))
   :hints (("Goal" :in-theory (enable nth nthcdr)))))

(local (in-theory (disable nthcdr)))

(defthm fn-oct-slice-list-empty
  (implies (<= n i)
           (equal (fn-oct-slice-list i n fn-octets) nil)))

(defthm fn-oct-slice-list-is-take-nthcdr
  (implies (and (natp i) (natp n) (<= i n) (<= n (len fn-octets))
                (true-listp fn-octets))
           (equal (fn-oct-slice-list i n fn-octets)
                  (take (- n i) (nthcdr i fn-octets))))
  :hints (("Goal" :induct (fn-oct-slice-list i n fn-octets))))

; "L opens with XS", the list-model shape of a prefix test (the shape
; `fn-inj-strip' has).  Not `take': past the end `take' pads with nil, and
; a prefix holding nil would then match where the buffer has nothing.
(defun fn-oct-list-prefixp (xs l)
  (declare (xargs :guard t))
  (if (atom xs)
      t
    (and (consp l)
         (equal (car l) (car xs))
         (fn-oct-list-prefixp (cdr xs) (cdr l)))))

(defthm fn-oct-prefix-equalp-is-list-prefixp
  (implies (and (natp i) (true-listp fn-octets))
           (equal (fn-oct-prefix-equalp i xs fn-octets)
                  (fn-oct-list-prefixp xs (nthcdr i fn-octets))))
  :hints (("Goal" :induct (fn-oct-prefix-equalp i xs fn-octets))))

(defthm fn-oct-suffix-equalp-is-equal
  (implies (and (natp i) (true-listp fn-octets))
           (equal (fn-oct-suffix-equalp i xs fn-octets)
                  (equal (nthcdr i fn-octets) xs)))
  :hints (("Goal" :induct (fn-oct-suffix-equalp i xs fn-octets))))

(defthm fn-oct-line-end-bounds
  (implies (and (natp i) (<= i (len fn-octets)))
           (and (<= i (fn-oct-line-end i fn-octets))
                (<= (fn-oct-line-end i fn-octets) (len fn-octets))))
  ; The trigger is the walk itself, never `len': as a linear rule with
  ; `(len st)' among its trigger terms it would fire on every length with
  ; I free.
  :rule-classes ((:linear :trigger-terms ((fn-oct-line-end i fn-octets))))
  :hints (("Goal" :induct (fn-oct-line-end i fn-octets))))

(in-theory (disable fn-oct-slice-list fn-oct-prefix-equalp fn-oct-suffix-equalp
                    fn-oct-line-end))

;; Withdrawn from includers (lane rule-hygiene, tools/rule_cost.py).
;; Each is tried in includers' proofs and pays for its frames in
;; almost none (planning/evidence/rule-cost-*.json has the counts;
;; docs/proof-style.md section 8).  An includer that needs one
;; enables it where it is used.
(in-theory (disable (:rewrite fn-oct-bufp-cell-is-octet . 1)
                    (:rewrite fn-oct-bufp-true-listp)
                    (:rewrite fn-oct-nth-of-octet-listp-is-octet . 1)))
