; fn: the payload arena's PAGED implementation, `fn-arena-paged' (D27; lane
; arena-offheap 2026-09-27, stage 1; recover-memory-2's packet P1).
;
; `fn-arena-bytes' (books/payload-arena-bytes.lisp) keeps every payload in
; ONE resizable byte array and doubles it when full: on the 10k x 32 KiB
; fixture the open's 333.6 MB of payloads sat in a 512 MiB array, and at the
; last doubling the old 256 MiB array and the new 512 MiB one were live
; together (recover-memory-2's record, lane/recover-memory-2 655867c9b, section 3).
; This implementation keeps the payloads in fixed pages of *fn-arp-page*
; octets, an array of page stobjs that grows by one page: a sealed octet
; never moves, a seal never copies an older payload, growth allocates one
; page (and the page table's pointers), so the arena's footprint is its
; payload octets plus under one page, and nothing is live twice.
;
; The logical side is `fn-arena-bytes''s, verbatim (`fn-arena$ap',
; `create-fn-arena$a', the eight `fn-arena$a-*'), so `(attach-stobj
; fn-arena fn-arena-paged)' (books/payload-arena-attach.lisp) makes the
; generic (books/payload-arena.lisp) execute here while every certificate
; above it stays the generic's.
;
; The abstraction: the pages' byte lists, concatenated (`fn-arp-flat'), are
; the byte array of `fn-arena-bytes': the relation `fn-arena$pcorr' is
; `fn-arena$corr''s with that list in place of the array, every page is full
; (*fn-arp-page* octets, `fn-arp-pages-fullp'), and the fill is within the
; pages.  The reads, writes and growth are proved against the flat list
; once (`fn-arp-nth-flat', `fn-arp-flat-of-page-write', `fn-arp-flat-of-add-page'),
; and then the byte array's proof structure (its slices and ranges lemmas,
; which are about any list) carries over.  No `skip-proofs'.

(in-package "ACL2")
(include-book "payload-arena-bytes")
(local (include-book "arithmetic/top" :dir :system))

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:rewrite fn-arn-payload-listp-true-listp))))

(defconst *fn-arp-page* 262144)

; As in books/payload-arena-bytes.lisp: the list reader, the slices and the
; ranges stay closed; the lemmas that need one open it by name.
(local (in-theory (disable fn-oct-list-from fn-arn-slices fn-arn-rangesp)))

; -----------------------------------------------------------------------------
; The concrete stobjs: a page (a resizable byte array, sized to one page when
; the page is added) and the arena (the page table, an offset and size per
; handle, the count and the fill).

(defstobj fn-arena-page
  (fn-arena-page-bytes :type (array (unsigned-byte 8) (0)) :initially 0 :resizable t)
  :inline t)

(defstobj fn-arena$p
  (fn-arena$p-pages :type (array fn-arena-page (0)) :resizable t)
  (fn-arena$p-off :type (array (integer 0 *) (0)) :initially 0 :resizable t)
  (fn-arena$p-size :type (array (integer 0 *) (0)) :initially 0 :resizable t)
  (fn-arena$p-count :type (integer 0 *) :initially 0)
  (fn-arena$p-fill :type (integer 0 *) :initially 0)
  (fn-arena$p-npages :type (integer 0 *) :initially 0)
  :inline t)

; -----------------------------------------------------------------------------
; The flat view: the first NP pages' byte lists, concatenated, and the
; invariant that each of them is a full page.  Pages at or past NP are
; spare slots of the page table (a doubling of pointers, never of octets).

(defun fn-arp-flat (np pages)
  (declare (xargs :guard (natp np) :verify-guards nil))
  (if (or (zp np) (atom pages))
      nil
    (append (nth 0 (car pages)) (fn-arp-flat (1- np) (cdr pages)))))

(defun fn-arp-fullp (np pages)
  (declare (xargs :guard (natp np) :verify-guards nil))
  (if (zp np)
      t
    (and (consp pages)
         (equal (len (nth 0 (car pages))) *fn-arp-page*)
         (fn-arp-fullp (1- np) (cdr pages)))))

(defthm fn-arp-true-listp-flat
  (true-listp (fn-arp-flat np pages)))

(local
 (defthm fn-arp-len-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(defthm fn-arp-len-flat
  (implies (and (fn-arp-fullp np pages) (natp np))
           (equal (len (fn-arp-flat np pages)) (* *fn-arp-page* np))))

(defthm fn-arp-fullp-len
  (implies (and (fn-arp-fullp np pages) (natp np))
           (<= np (len pages)))
  :rule-classes :linear)

(local
 (defthm fn-arp-nth-append
   (equal (nth n (append a b))
          (if (< (nfix n) (len a)) (nth n a) (nth (- (nfix n) (len a)) b)))
   :hints (("Goal" :in-theory (enable nth)))))

(local
 (defthm fn-arp-update-nth-append
   (implies (natp n)
            (equal (update-nth n v (append a b))
                   (if (< n (len a))
                       (append (update-nth n v a) b)
                     (append a (update-nth (- n (len a)) v b)))))
   :hints (("Goal" :in-theory (enable update-nth)))))

; A read of the flat view at page K, index J is that page's octet J.
(defthm fn-arp-nth-flat
  (implies (and (fn-arp-fullp np pages) (natp np)
                (natp k) (< k np) (natp j) (< j *fn-arp-page*))
           (equal (nth (+ j (* *fn-arp-page* k)) (fn-arp-flat np pages))
                  (nth j (nth 0 (nth k pages)))))
  :hints (("Goal" :induct (list (fn-arp-flat np pages) (nth k pages))
           :in-theory (enable nth))))

; A write of page K's octet J is the flat view's update at the same place.
(defthm fn-arp-flat-of-page-write
  (implies (and (fn-arp-fullp np pages) (natp np)
                (natp k) (< k np) (natp j) (< j *fn-arp-page*))
           (equal (fn-arp-flat np (update-nth k (update-nth 0 (update-nth j o (nth 0 (nth k pages)))
                                                            (nth k pages))
                                              pages))
                  (update-nth (+ j (* *fn-arp-page* k)) o (fn-arp-flat np pages))))
  :hints (("Goal" :induct (list (fn-arp-flat np pages) (nth k pages))
           :in-theory (enable nth update-nth))))

(local
 (defthm fn-arp-len-update-nth-within
   (implies (< (nfix j) (len l))
            (equal (len (update-nth j v l)) (len l)))
   :hints (("Goal" :in-theory (enable update-nth)))))

(defthm fn-arp-nth-fullp
  (implies (and (fn-arp-fullp np pages) (natp np) (natp k) (< k np))
           (equal (len (nth 0 (nth k pages))) *fn-arp-page*))
  :hints (("Goal" :induct (list (fn-arp-fullp np pages) (nth k pages))
           :in-theory (enable nth))))

(defthm fn-arp-fullp-of-update-nth
  (implies (and (fn-arp-fullp np pages) (natp np) (natp k) (< k np)
                (equal (len (nth 0 v)) *fn-arp-page*))
           (fn-arp-fullp np (update-nth k v pages)))
  :hints (("Goal" :induct (list (fn-arp-fullp np pages) (nth k pages))
           :in-theory (enable nth update-nth))))

(defthm fn-arp-fullp-of-page-write
  (implies (and (fn-arp-fullp np pages) (natp np)
                (natp k) (< k np) (natp j) (< j *fn-arp-page*))
           (fn-arp-fullp np (update-nth k (update-nth 0 (update-nth j o (nth 0 (nth k pages)))
                                                      (nth k pages))
                                        pages)))
  :hints (("Goal" :use ((:instance fn-arp-nth-fullp)))))

; The flat view and the invariant read only the first NP pages: a write of a
; page at or past NP and a resize of the table keeping NP pages change
; neither; the view of NP+1 pages is the view of NP and page NP's octets.

(defthm fn-arp-flat-of-update-nth-above
  (implies (and (natp np) (natp k) (<= np k))
           (equal (fn-arp-flat np (update-nth k v pages))
                  (fn-arp-flat np pages)))
  :hints (("Goal" :induct (list (fn-arp-flat np pages) (update-nth k v pages))
           :in-theory (enable update-nth))))

(defthm fn-arp-fullp-of-update-nth-above
  (implies (and (natp np) (natp k) (<= np k) (<= np (len pages)))
           (equal (fn-arp-fullp np (update-nth k v pages))
                  (fn-arp-fullp np pages)))
  :hints (("Goal" :induct (list (fn-arp-fullp np pages) (update-nth k v pages))
           :in-theory (enable update-nth))))

(local
 (defun fn-arp-resize-ind (np pages m)
   (if (or (zp np) (atom pages))
       (list pages m)
     (fn-arp-resize-ind (1- np) (cdr pages) (1- m)))))

(defthm fn-arp-flat-of-resize-list
  (implies (and (natp np) (<= np (len pages)) (natp m) (<= np m))
           (equal (fn-arp-flat np (resize-list pages m d))
                  (fn-arp-flat np pages)))
  :hints (("Goal" :induct (fn-arp-resize-ind np pages m))))

(defthm fn-arp-fullp-of-resize-list
  (implies (and (natp np) (<= np (len pages)) (natp m) (<= np m))
           (equal (fn-arp-fullp np (resize-list pages m d))
                  (fn-arp-fullp np pages)))
  :hints (("Goal" :induct (fn-arp-resize-ind np pages m))))

(defthm fn-arp-flat-snoc
  (implies (and (natp np) (< np (len pages)) (true-listp (nth 0 (nth np pages))))
           (equal (fn-arp-flat (1+ np) pages)
                  (append (fn-arp-flat np pages) (nth 0 (nth np pages)))))
  :hints (("Goal" :induct (fn-arp-flat np pages) :in-theory (enable nth))))

(defthm fn-arp-fullp-snoc
  (implies (and (natp np) (< np (len pages)))
           (equal (fn-arp-fullp (1+ np) pages)
                  (and (fn-arp-fullp np pages)
                       (equal (len (nth 0 (nth np pages))) *fn-arp-page*))))
  :hints (("Goal" :induct (fn-arp-fullp np pages) :in-theory (enable nth))))

; A page's byte list is an octet buffer; the flat view of octet pages is one.
(defthm fn-arp-page-bytesp-is-octets-bufp
  (equal (fn-arena-page-bytesp x) (fn-octets$c-bufp x)))

(defthm fn-arp-pagesp-nth
  (implies (and (fn-arena$p-pagesp pages) (natp k) (< k (len pages)))
           (fn-arena-pagep (nth k pages)))
  :hints (("Goal" :in-theory (enable nth))))

(local
 (defthm fn-arp-bufp-of-append
   (implies (and (fn-octets$c-bufp a) (fn-octets$c-bufp b))
            (fn-octets$c-bufp (append a b)))))

(defthm fn-arp-bufp-of-flat
  (implies (fn-arena$p-pagesp pages)
           (fn-octets$c-bufp (fn-arp-flat np pages))))

(defthm fn-arp-pagesp-of-update-nth
  (implies (and (fn-arena$p-pagesp pages) (natp k) (< k (len pages)) (fn-arena-pagep v))
           (fn-arena$p-pagesp (update-nth k v pages)))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm fn-arp-pagesp-of-resize-list
  (implies (fn-arena$p-pagesp pages)
           (fn-arena$p-pagesp (resize-list pages m '(nil)))))

(defthm fn-arp-list-from-of-append-beyond
  (implies (and (natp n) (<= n (len buf)))
           (equal (fn-oct-list-from i n (append buf extra))
                  (fn-oct-list-from i n buf)))
  :hints (("Goal" :in-theory (enable fn-oct-list-from))))

; The division of a position into its page and its index.
(encapsulate
  ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm fn-arp-floor-mod
    (implies (and (natp p) (natp np) (< p (* 262144 np)))
             (and (natp (floor p 262144)) (< (floor p 262144) np)
                  (natp (mod p 262144)) (< (mod p 262144) 262144)
                  (equal (+ (mod p 262144) (* 262144 (floor p 262144))) p)))
    :rule-classes nil)
  (defthm fn-arp-floor-base
    (implies (natp x)
             (and (natp (floor x 262144))
                  (<= (* 262144 (floor x 262144)) x)
                  (< x (+ 262144 (* 262144 (floor x 262144))))))
    :rule-classes nil))

; The read and the write at a position, in the flat view.
(defthm fn-arp-nth-flat-at
  (implies (and (fn-arp-fullp np pages) (natp np) (natp p) (< p (* *fn-arp-page* np)))
           (equal (nth (mod p *fn-arp-page*) (nth 0 (nth (floor p *fn-arp-page*) pages)))
                  (nth p (fn-arp-flat np pages))))
  :hints (("Goal" :use ((:instance fn-arp-floor-mod)
                        (:instance fn-arp-nth-flat (k (floor p *fn-arp-page*))
                                   (j (mod p *fn-arp-page*))))
           :in-theory (disable fn-arp-nth-flat))))

(defthm fn-arp-flat-of-write-at
  (implies (and (fn-arp-fullp np pages) (natp np) (natp p) (< p (* *fn-arp-page* np)))
           (equal (fn-arp-flat np (update-nth (floor p *fn-arp-page*)
                                              (update-nth 0 (update-nth (mod p *fn-arp-page*) o
                                                                        (nth 0 (nth (floor p *fn-arp-page*) pages)))
                                                          (nth (floor p *fn-arp-page*) pages))
                                              pages))
                  (update-nth p o (fn-arp-flat np pages))))
  :hints (("Goal" :use ((:instance fn-arp-floor-mod)
                        (:instance fn-arp-flat-of-page-write (k (floor p *fn-arp-page*))
                                   (j (mod p *fn-arp-page*))))
           :in-theory (disable fn-arp-flat-of-page-write))))

(defthm fn-arp-fullp-of-write-at
  (implies (and (fn-arp-fullp np pages) (natp np) (natp p) (< p (* *fn-arp-page* np)))
           (fn-arp-fullp np (update-nth (floor p *fn-arp-page*)
                                        (update-nth 0 (update-nth (mod p *fn-arp-page*) o
                                                                  (nth 0 (nth (floor p *fn-arp-page*) pages)))
                                                    (nth (floor p *fn-arp-page*) pages))
                                        pages)))
  :hints (("Goal" :use ((:instance fn-arp-floor-mod)
                        (:instance fn-arp-fullp-of-page-write (k (floor p *fn-arp-page*))
                                   (j (mod p *fn-arp-page*))))
           :in-theory (disable fn-arp-fullp-of-page-write))))

(defthm fn-arp-floor-below
  (implies (and (natp p) (natp np) (< p (* *fn-arp-page* np)))
           (and (natp (floor p *fn-arp-page*)) (< (floor p *fn-arp-page*) np)
                (natp (mod p *fn-arp-page*)) (< (mod p *fn-arp-page*) *fn-arp-page*)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-arp-floor-mod)))))

; The concrete recognizer, field by field (forward), and its preservation
; by each field's update.

(defthm fn-arp-offp-is-c-offp
  (equal (fn-arena$p-offp x) (fn-arena$c-offp x)))

(defthm fn-arp-sizep-is-c-sizep
  (equal (fn-arena$p-sizep x) (fn-arena$c-sizep x)))

(defthm fn-arp-pp-fields
  (implies (fn-arena$pp fn-arena$p)
           (and (true-listp fn-arena$p)
                (equal (len fn-arena$p) 6)
                (fn-arena$p-pagesp (nth 0 fn-arena$p))
                (fn-arena$c-offp (nth 1 fn-arena$p))
                (fn-arena$c-sizep (nth 2 fn-arena$p))
                (integerp (nth 3 fn-arena$p)) (<= 0 (nth 3 fn-arena$p))
                (integerp (nth 4 fn-arena$p)) (<= 0 (nth 4 fn-arena$p))
                (integerp (nth 5 fn-arena$p)) (<= 0 (nth 5 fn-arena$p))))
  :rule-classes ((:forward-chaining :trigger-terms ((fn-arena$pp fn-arena$p)))))


(defthm fn-arp-pagep-of-resize
  (implies (fn-arena-pagep pg)
           (fn-arena-pagep (update-nth 0 (resize-list (nth 0 pg) m 0) pg)))
  :hints (("Goal" :in-theory (enable fn-arena-pagep))))

(defthm fn-arp-pagep-of-write
  (implies (and (fn-arena-pagep pg) (natp j) (< j (len (nth 0 pg))) (unsigned-byte-p 8 o))
           (fn-arena-pagep (update-nth 0 (update-nth j o (nth 0 pg)) pg)))
  :hints (("Goal" :in-theory (enable fn-arena-pagep))))

(local (in-theory (disable floor mod nth update-nth fn-arena-pagep)))
(local (in-theory (enable update-nth-array)))

; -----------------------------------------------------------------------------
; The exec functions.

(defun fn-arena$p-wfp (fn-arena$p)
  ; The executable invariant: the fill is within the pages, the pages within
  ; the table, the count within the handle arrays.
  (declare (xargs :stobjs fn-arena$p))
  (and (<= (fn-arena$p-fill fn-arena$p) (* *fn-arp-page* (fn-arena$p-npages fn-arena$p)))
       (<= (fn-arena$p-npages fn-arena$p) (fn-arena$p-pages-length fn-arena$p))
       (<= (fn-arena$p-count fn-arena$p) (fn-arena$p-off-length fn-arena$p))
       (<= (fn-arena$p-count fn-arena$p) (fn-arena$p-size-length fn-arena$p))))

; The octet at position P: its page's octet.
(defun fn-arp-byte (p fn-arena$p)
  (declare (xargs :stobjs fn-arena$p
                  :guard (and (natp p)
                              (<= (fn-arena$p-npages fn-arena$p) (fn-arena$p-pages-length fn-arena$p))
                              (< p (* *fn-arp-page* (fn-arena$p-npages fn-arena$p))))))
  (declare (xargs :guard-hints (("Goal" :use ((:instance fn-arp-floor-below
                                                            (np (fn-arena$p-npages fn-arena$p))))))))
  (let ((k (floor p *fn-arp-page*))
        (j (mod p *fn-arp-page*)))
    (stobj-let ((fn-arena-page (fn-arena$p-pagesi k fn-arena$p)))
               (v)
               (if (< j (fn-arena-page-bytes-length fn-arena-page))
                   (fn-arena-page-bytesi j fn-arena-page)
                 0)
               v)))

;; The payload reader: buf[i..n) consed from the top down, one page at a
;; time (one page lookup per page, one array read per octet).
(defun fn-arp-page-down (lo hi acc fn-arena-page)
  (declare (xargs :stobjs fn-arena-page
                  :guard (and (natp lo) (natp hi) (<= lo hi) (true-listp acc))
                  :measure (nfix (- (nfix hi) (nfix lo)))))
  (if (or (not (natp lo)) (not (natp hi)) (<= hi lo))
      acc
    (fn-arp-page-down lo (1- hi)
                      (cons (if (< (1- hi) (fn-arena-page-bytes-length fn-arena-page))
                                (fn-arena-page-bytesi (1- hi) fn-arena-page)
                              0)
                            acc)
                      fn-arena-page)))

(defthm fn-arp-true-listp-page-down
  (implies (true-listp acc)
           (true-listp (fn-arp-page-down lo hi acc fn-arena-page))))

(defun fn-arp-list-pages (i n acc fn-arena$p)
  (declare (xargs :stobjs fn-arena$p
                  :guard (and (natp i) (natp n) (<= i n)
                              (<= (fn-arena$p-npages fn-arena$p) (fn-arena$p-pages-length fn-arena$p))
                              (<= n (* *fn-arp-page* (fn-arena$p-npages fn-arena$p)))
                              (true-listp acc))
                  :measure (nfix (- (nfix n) (nfix i)))
                  :hints (("Goal" :use ((:instance fn-arp-floor-base (x (1- n))))))
                  :guard-hints (("Goal" :use ((:instance fn-arp-floor-base (x (1- n)))
                                              (:instance fn-arp-floor-below (p (1- n))
                                                         (np (fn-arena$p-npages fn-arena$p))))))))
  (if (or (not (natp i)) (not (natp n)) (<= n i))
      acc
    (let* ((k (floor (1- n) *fn-arp-page*))
           (base (* *fn-arp-page* k))
           (lo (max i base))
           (acc (stobj-let ((fn-arena-page (fn-arena$p-pagesi k fn-arena$p)))
                           (v)
                           (fn-arp-page-down (- lo base) (- n base) acc fn-arena-page)
                           v)))
      (fn-arp-list-pages i lo acc fn-arena$p))))
;
(defun fn-arena$p-payload-len (h fn-arena$p)
  (declare (xargs :stobjs fn-arena$p
                  :guard (and (natp h) (< h (fn-arena$p-count fn-arena$p))
                              (fn-arena$p-wfp fn-arena$p))))
  (fn-arena$p-sizei h fn-arena$p))

(defun fn-arena$p-get (h i fn-arena$p)
  (declare (xargs :stobjs fn-arena$p
                  :guard (and (fn-arena$p-wfp fn-arena$p)
                              (natp h) (< h (fn-arena$p-count fn-arena$p))
                              (natp i)
                              (natp (fn-arena$p-offi h fn-arena$p))
                              (natp (fn-arena$p-sizei h fn-arena$p))
                              (< i (fn-arena$p-sizei h fn-arena$p))
                              (<= (+ (fn-arena$p-offi h fn-arena$p) (fn-arena$p-sizei h fn-arena$p))
                                  (fn-arena$p-fill fn-arena$p)))))
  (fn-arp-byte (+ (fn-arena$p-offi h fn-arena$p) i) fn-arena$p))

(defun fn-arena$p-payload (h fn-arena$p)
  (declare (xargs :stobjs fn-arena$p
                  :guard (and (fn-arena$p-wfp fn-arena$p)
                              (natp h) (< h (fn-arena$p-count fn-arena$p))
                              (natp (fn-arena$p-offi h fn-arena$p))
                              (natp (fn-arena$p-sizei h fn-arena$p))
                              (<= (+ (fn-arena$p-offi h fn-arena$p) (fn-arena$p-sizei h fn-arena$p))
                                  (fn-arena$p-fill fn-arena$p)))))
  (fn-arp-list-pages (fn-arena$p-offi h fn-arena$p)
                    (+ (fn-arena$p-offi h fn-arena$p) (fn-arena$p-sizei h fn-arena$p))
                    nil fn-arena$p))

; The clear releases the pages: the table is emptied, so an arena rebuilt
; by the next open holds its own payloads and no earlier ones.
(defun fn-arena$p-clear (fn-arena$p)
  (declare (xargs :stobjs fn-arena$p))
  (let* ((fn-arena$p (update-fn-arena$p-count 0 fn-arena$p))
         (fn-arena$p (update-fn-arena$p-fill 0 fn-arena$p))
         (fn-arena$p (update-fn-arena$p-npages 0 fn-arena$p)))
    (resize-fn-arena$p-pages 0 fn-arena$p)))

; Page NP made a full page; the table doubles its POINTERS when it has no
; spare slot (a new slot is an empty page stobj, no octets).
(defun fn-arp-add-page (fn-arena$p)
  (declare (xargs :stobjs fn-arena$p
                  :guard (<= (fn-arena$p-npages fn-arena$p) (fn-arena$p-pages-length fn-arena$p))))
  (let* ((k (fn-arena$p-npages fn-arena$p))
         (fn-arena$p (if (< k (fn-arena$p-pages-length fn-arena$p))
                         fn-arena$p
                       (resize-fn-arena$p-pages (max 8 (* 2 k)) fn-arena$p)))
         (fn-arena$p (stobj-let ((fn-arena-page (fn-arena$p-pagesi k fn-arena$p)))
                                (fn-arena-page)
                                (resize-fn-arena-page-bytes *fn-arp-page* fn-arena-page)
                                fn-arena$p)))
    (update-fn-arena$p-npages (1+ k) fn-arena$p)))

; Octet O at position P, in its page.
(defun fn-arp-put (p o fn-arena$p)
  (declare (xargs :stobjs fn-arena$p
                  :guard (and (natp p) (fn-cbor-octetp o)
                              (<= (fn-arena$p-npages fn-arena$p) (fn-arena$p-pages-length fn-arena$p))
                              (< p (* *fn-arp-page* (fn-arena$p-npages fn-arena$p))))
                  :guard-hints (("Goal" :use ((:instance fn-arp-floor-below
                                                         (np (fn-arena$p-npages fn-arena$p))))))))
  (let ((k (floor p *fn-arp-page*))
        (j (mod p *fn-arp-page*)))
    (stobj-let ((fn-arena-page (fn-arena$p-pagesi k fn-arena$p)))
               (fn-arena-page)
               (if (< j (fn-arena-page-bytes-length fn-arena-page))
                   (update-fn-arena-page-bytesi j o fn-arena-page)
                 fn-arena-page)
               fn-arena$p)))

; One octet at the fill point, adding a page when the pages are full.
(defun fn-arp-write-octet (o fn-arena$p)
  (declare (xargs :stobjs fn-arena$p
                  :guard (and (fn-cbor-octetp o)
                              (<= (fn-arena$p-npages fn-arena$p) (fn-arena$p-pages-length fn-arena$p))
                              (<= (fn-arena$p-fill fn-arena$p)
                                  (* *fn-arp-page* (fn-arena$p-npages fn-arena$p))))
                  :verify-guards nil))
  (let* ((n (fn-arena$p-fill fn-arena$p))
         (fn-arena$p (if (< n (* *fn-arp-page* (fn-arena$p-npages fn-arena$p)))
                         fn-arena$p
                       (fn-arp-add-page fn-arena$p)))
         (fn-arena$p (fn-arp-put n o fn-arena$p)))
    (update-fn-arena$p-fill (1+ n) fn-arena$p)))

; -----------------------------------------------------------------------------
; The flat view of a concrete arena, its capacity and the page invariant.

(defun fn-arp-buf (fn-arena$p)
  (declare (xargs :guard t :verify-guards nil))
  (fn-arp-flat (nfix (nth 5 fn-arena$p)) (nth 0 fn-arena$p)))

(defun fn-arp-cap (fn-arena$p)
  (declare (xargs :guard t :verify-guards nil))
  (* *fn-arp-page* (nfix (nth 5 fn-arena$p))))

(defun fn-arp-okp (fn-arena$p)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-arena$pp fn-arena$p)
       (<= (nth 5 fn-arena$p) (len (nth 0 fn-arena$p)))
       (fn-arp-fullp (nth 5 fn-arena$p) (nth 0 fn-arena$p))))

(defthm fn-arp-okp-forward
  (implies (fn-arp-okp x)
           (and (fn-arena$pp x)
                (<= (nth 5 x) (len (nth 0 x)))
                (fn-arp-fullp (nth 5 x) (nth 0 x))))
  :rule-classes :forward-chaining)

(defthm fn-arp-len-buf
  (implies (fn-arp-okp x)
           (equal (len (fn-arp-buf x)) (fn-arp-cap x))))

(defthm fn-arp-bufp-of-buf
  (implies (fn-arp-okp x)
           (fn-octets$c-bufp (fn-arp-buf x))))

; The add-page: the invariant is kept, one page more, the other fields and
; every octet below the old capacity unchanged.
(defthm fn-arp-add-page-step
  (implies (fn-arp-okp fn-arena$p)
           (let ((next (fn-arp-add-page fn-arena$p)))
             (and (fn-arp-okp next)
                  (equal (nth 1 next) (nth 1 fn-arena$p))
                  (equal (nth 2 next) (nth 2 fn-arena$p))
                  (equal (nth 3 next) (nth 3 fn-arena$p))
                  (equal (nth 4 next) (nth 4 fn-arena$p))
                  (equal (nth 5 next) (1+ (nth 5 fn-arena$p)))
                  (implies (and (natp n) (<= n (fn-arp-cap fn-arena$p)))
                           (equal (fn-oct-list-from i n (fn-arp-buf next))
                                  (fn-oct-list-from i n (fn-arp-buf fn-arena$p)))))))
  :hints (("Goal" :in-theory (enable fn-arp-flat-snoc))))

(defthm fn-arp-cap-of-npages
  (implies (fn-arena$pp x)
           (equal (* 262144 (nth 5 x)) (fn-arp-cap x)))
  :hints (("Goal" :in-theory (enable fn-arp-cap))))

(local (in-theory (disable fn-arp-add-page fn-arp-buf fn-arp-cap)))

(defthm fn-arp-cap-of-add-page
  (implies (fn-arp-okp fn-arena$p)
           (equal (fn-arp-cap (fn-arp-add-page fn-arena$p))
                  (+ *fn-arp-page* (fn-arp-cap fn-arena$p))))
  :hints (("Goal" :in-theory (e/d (fn-arp-cap) (fn-arp-cap-of-npages))
           :use ((:instance fn-arp-add-page-step (n 0) (i 0))))))

(defthm fn-arp-nth-buf-of-add-page
  (implies (and (fn-arp-okp fn-arena$p) (natp p) (< p (fn-arp-cap fn-arena$p)))
           (equal (nth p (fn-arp-buf (fn-arp-add-page fn-arena$p)))
                  (nth p (fn-arp-buf fn-arena$p))))
  :hints (("Goal" :use ((:instance fn-arp-add-page-step (i p) (n (1+ p)))
                        (:instance fn-oct-nth-of-list-from (i p) (n (1+ p)) (k 0)
                                   (buf (fn-arp-buf (fn-arp-add-page fn-arena$p))))
                        (:instance fn-oct-nth-of-list-from (i p) (n (1+ p)) (k 0)
                                   (buf (fn-arp-buf fn-arena$p))))
           :in-theory (disable fn-arp-add-page-step fn-oct-nth-of-list-from))))

; The page write is the flat view's update at the same position.
(defthm fn-arp-put-step
  (implies (and (fn-arp-okp fn-arena$p) (natp p) (< p (fn-arp-cap fn-arena$p))
                (fn-cbor-octetp o))
           (let ((next (fn-arp-put p o fn-arena$p)))
             (and (fn-arp-okp next)
                  (equal (nth 1 next) (nth 1 fn-arena$p))
                  (equal (nth 2 next) (nth 2 fn-arena$p))
                  (equal (nth 3 next) (nth 3 fn-arena$p))
                  (equal (nth 4 next) (nth 4 fn-arena$p))
                  (equal (nth 5 next) (nth 5 fn-arena$p))
                  (equal (fn-arp-cap next) (fn-arp-cap fn-arena$p))
                  (equal (fn-arp-buf next) (update-nth p o (fn-arp-buf fn-arena$p))))))
  :hints (("Goal" :in-theory (e/d (fn-arp-buf fn-arp-cap) (fn-arp-cap-of-npages))
           :use ((:instance fn-arp-floor-below (np (nth 5 fn-arena$p)))))))

; The fields other than the page table and the page count change neither
; the flat view nor the capacity; each keeps the invariant with a value of
; its type.

(defthm fn-arp-buf-of-update-other
  (implies (and (natp k) (<= 1 k) (<= k 4))
           (and (equal (fn-arp-buf (update-nth k v x)) (fn-arp-buf x))
                (equal (fn-arp-cap (update-nth k v x)) (fn-arp-cap x))))
  :hints (("Goal" :in-theory (e/d (fn-arp-buf fn-arp-cap) (fn-arp-cap-of-npages)))))

(defthm fn-arp-pp-of-update-off
  (implies (and (fn-arena$pp x) (fn-arena$c-offp off))
           (fn-arena$pp (update-nth 1 off x)))
  :hints (("Goal" :in-theory (enable update-nth nth))))

(defthm fn-arp-pp-of-update-size
  (implies (and (fn-arena$pp x) (fn-arena$c-sizep size))
           (fn-arena$pp (update-nth 2 size x)))
  :hints (("Goal" :in-theory (enable update-nth nth))))

(defthm fn-arp-pp-of-update-count
  (implies (and (fn-arena$pp x) (natp n))
           (fn-arena$pp (update-nth 3 n x)))
  :hints (("Goal" :in-theory (enable update-nth nth))))

(defthm fn-arp-pp-of-update-fill
  (implies (and (fn-arena$pp x) (natp n))
           (fn-arena$pp (update-nth 4 n x)))
  :hints (("Goal" :in-theory (enable update-nth nth))))

(defthm fn-arp-pp-of-update-pages
  (implies (and (fn-arena$pp x) (fn-arena$p-pagesp pages))
           (fn-arena$pp (update-nth 0 pages x)))
  :hints (("Goal" :in-theory (enable update-nth nth))))

(defthm fn-arp-pp-of-update-npages
  (implies (and (fn-arena$pp x) (natp n))
           (fn-arena$pp (update-nth 5 n x)))
  :hints (("Goal" :in-theory (enable update-nth nth))))

(defthm fn-arp-okp-of-update-off
  (implies (and (fn-arp-okp x) (fn-arena$c-offp off))
           (fn-arp-okp (update-nth 1 off x))))

(defthm fn-arp-okp-of-update-size
  (implies (and (fn-arp-okp x) (fn-arena$c-sizep size))
           (fn-arp-okp (update-nth 2 size x))))

(defthm fn-arp-okp-of-update-count
  (implies (and (fn-arp-okp x) (natp n))
           (fn-arp-okp (update-nth 3 n x))))

(defthm fn-arp-okp-of-update-fill
  (implies (and (fn-arp-okp x) (natp n))
           (fn-arp-okp (update-nth 4 n x))))

(local (in-theory (disable fn-arp-okp fn-arp-put fn-arena$pp)))

; The write of one octet at the fill.
(defthm fn-arp-write-octet-step
  (implies (and (fn-arp-okp fn-arena$p)
                (<= (nth 4 fn-arena$p) (fn-arp-cap fn-arena$p))
                (fn-cbor-octetp o))
           (let ((next (fn-arp-write-octet o fn-arena$p)))
             (and (fn-arp-okp next)
                  (equal (nth 1 next) (nth 1 fn-arena$p))
                  (equal (nth 2 next) (nth 2 fn-arena$p))
                  (equal (nth 3 next) (nth 3 fn-arena$p))
                  (equal (nth 4 next) (1+ (nth 4 fn-arena$p)))
                  (<= (nth 4 next) (fn-arp-cap next))
                  (equal (nth (nth 4 fn-arena$p) (fn-arp-buf next)) o))))
  :hints (("Goal" :cases ((< (nth 4 fn-arena$p) (fn-arp-cap fn-arena$p)))
           :in-theory (disable fn-arp-add-page-step fn-arp-put-step))
          ("Subgoal 2" :use ((:instance fn-arp-add-page-step (n 0) (i 0))
                             (:instance fn-arp-put-step (p (nth 4 fn-arena$p))
                                        (fn-arena$p (fn-arp-add-page fn-arena$p)))))
          ("Subgoal 1" :use ((:instance fn-arp-put-step (p (nth 4 fn-arena$p)))))))

(defthm fn-arp-write-octet-room
  (implies (and (fn-arp-okp fn-arena$p)
                (<= (nth 4 fn-arena$p) (fn-arp-cap fn-arena$p))
                (fn-cbor-octetp o))
           (< (nth 4 fn-arena$p) (fn-arp-cap (fn-arp-write-octet o fn-arena$p))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use ((:instance fn-arp-write-octet-step))
           :in-theory (disable fn-arp-write-octet-step fn-arp-write-octet))))

(defthm fn-arp-write-octet-keeps-list-from-below-fill
  (implies (and (fn-arp-okp fn-arena$p)
                (<= (nth 4 fn-arena$p) (fn-arp-cap fn-arena$p))
                (fn-cbor-octetp o)
                (natp n) (<= n (nth 4 fn-arena$p)))
           (equal (fn-oct-list-from i n (fn-arp-buf (fn-arp-write-octet o fn-arena$p)))
                  (fn-oct-list-from i n (fn-arp-buf fn-arena$p))))
  :hints (("Goal" :cases ((< (nth 4 fn-arena$p) (fn-arp-cap fn-arena$p)))
           :in-theory (disable fn-arp-add-page-step fn-arp-put-step))
          ("Subgoal 2" :use ((:instance fn-arp-add-page-step)
                             (:instance fn-arp-put-step (p (nth 4 fn-arena$p))
                                        (fn-arena$p (fn-arp-add-page fn-arena$p)))))
          ("Subgoal 1" :use ((:instance fn-arp-put-step (p (nth 4 fn-arena$p)))))))

(local (in-theory (disable fn-arp-write-octet)))

; -----------------------------------------------------------------------------
; The writes, the seal entry and the seals: `fn-arena-bytes''s, over pages.

(defun fn-arp-write (xs fn-arena$p)
  ; XS at the fill point, one write per octet.
  (declare (xargs :stobjs fn-arena$p
                  :guard (and (fn-cbor-octet-listp xs) (fn-arena$p-wfp fn-arena$p))
                  :verify-guards nil))
  (if (atom xs)
      fn-arena$p
    (let ((fn-arena$p (fn-arp-write-octet (car xs) fn-arena$p)))
      (fn-arp-write (cdr xs) fn-arena$p))))

;; The bulk write (lane snapshot-open-2): fn-arp-write-buffer's executable
;; computes the page and column once per page (fn-arp-write-run), not the
;; generic FLOOR and MOD of fn-arp-put per octet (at a 100k checkpoint open the
;; seal of the payloads was 9.0 s, a third of it in FLOOR).  Its logic is the
;; octet-at-a-time definition; fn-arp-write-run-is-write-buffer is the
;; equality its guard proof uses.
; The octet at column J of page K (fn-arp-put with the page and column given).
(defun fn-arp-put-kj (k j o fn-arena$p)
  (declare (xargs :stobjs fn-arena$p
                  :guard (and (natp k) (natp j) (fn-cbor-octetp o)
                              (< k (fn-arena$p-pages-length fn-arena$p)))))
  (stobj-let ((fn-arena-page (fn-arena$p-pagesi k fn-arena$p)))
             (fn-arena-page)
             (if (< j (fn-arena-page-bytes-length fn-arena-page))
                 (update-fn-arena-page-bytesi j o fn-arena-page)
               fn-arena-page)
             fn-arena$p))

; Octets [i, i + (e - j)) of the buffer into columns [j, e) of page K, the fill
; advancing with each, as fn-arp-write-octet writes them when the fill is
; K * page + J: the page and column are computed once per page, not per octet.
(defun fn-arp-write-in-page (k j e i fn-octets fn-arena$p)
  (declare (xargs :stobjs (fn-octets fn-arena$p)
                  :guard (and (natp k) (natp j) (natp e) (natp i) (<= j e)
                              (<= (+ i (- e j)) (fn-octets-len fn-octets))
                              (< k (fn-arena$p-pages-length fn-arena$p)))
                  :measure (nfix (- (nfix e) (nfix j)))))
  (if (or (not (natp j)) (not (natp e)) (<= e j))
      fn-arena$p
    (let* ((fn-arena$p (fn-arp-put-kj k j (fn-octets-get i fn-octets) fn-arena$p))
           (fn-arena$p (update-fn-arena$p-fill (1+ (fn-arena$p-fill fn-arena$p)) fn-arena$p)))
      (fn-arp-write-in-page k (1+ j) e (1+ (nfix i)) fn-octets fn-arena$p))))

(encapsulate
  ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm fn-arp-mod-page-bounds
    (implies (natp f)
             (and (natp (mod f 262144)) (< (mod f 262144) 262144)
                  (natp (floor f 262144))))
    :rule-classes ((:rewrite) (:type-prescription :corollary (implies (natp f) (natp (mod f 262144))))
                   (:linear :corollary (implies (natp f) (< (mod f 262144) 262144))))))

; The run: the page and the column once per page.
(defun fn-arp-write-run (i n fn-octets fn-arena$p)
  (declare (xargs :stobjs (fn-octets fn-arena$p)
                  :guard (and (natp i) (natp n) (<= n (fn-octets-len fn-octets))
                              (fn-arena$p-wfp fn-arena$p))
                  :measure (nfix (- (nfix n) (nfix i)))
                  :hints (("Goal" :in-theory (disable fn-arp-add-page fn-arp-write-in-page
                                                      fn-arena$p-fill fn-arena$p-npages)))
                  :verify-guards nil))
  (if (or (not (natp i)) (not (natp n)) (<= n i))
      fn-arena$p
    (let* ((f (nfix (fn-arena$p-fill fn-arena$p)))
           (fn-arena$p (if (< f (* *fn-arp-page* (fn-arena$p-npages fn-arena$p)))
                           fn-arena$p
                         (fn-arp-add-page fn-arena$p)))
           (k (floor f *fn-arp-page*))
           (j (mod f *fn-arp-page*))
           (c (min (- n i) (- *fn-arp-page* j)))
           (fn-arena$p (fn-arp-write-in-page k j (+ j c) i fn-octets fn-arena$p)))
      (fn-arp-write-run (+ i c) n fn-octets fn-arena$p))))

(defun fn-arp-write-buffer (i n fn-octets fn-arena$p)
  ; The octet buffer's cells [i, n) at the fill point, read in place.
  (declare (xargs :stobjs (fn-octets fn-arena$p)
                  :guard (and (natp i) (natp n) (<= n (fn-octets-len fn-octets))
                              (fn-arena$p-wfp fn-arena$p))
                  :measure (nfix (- (nfix n) (nfix i)))
                  :verify-guards nil))
  (mbe :logic (if (or (not (natp i)) (not (natp n)) (<= n i))
                  fn-arena$p
                (let ((fn-arena$p (fn-arp-write-octet (fn-octets-get i fn-octets) fn-arena$p)))
                  (fn-arp-write-buffer (1+ i) n fn-octets fn-arena$p)))
       :exec (fn-arp-write-run i n fn-octets fn-arena$p)))

(defun fn-arp-seal-entry (start fn-arena$p)
  ; The octets written at [start, fill) become the next handle.
  (declare (xargs :stobjs fn-arena$p
                  :guard (and (natp start) (<= start (fn-arena$p-fill fn-arena$p))
                              (<= (fn-arena$p-count fn-arena$p) (fn-arena$p-off-length fn-arena$p))
                              (<= (fn-arena$p-count fn-arena$p) (fn-arena$p-size-length fn-arena$p)))))
  (let* ((h (fn-arena$p-count fn-arena$p))
         (fn-arena$p (if (< h (fn-arena$p-off-length fn-arena$p))
                         fn-arena$p
                       (resize-fn-arena$p-off (max 64 (* 2 h)) fn-arena$p)))
         (fn-arena$p (if (< h (fn-arena$p-size-length fn-arena$p))
                         fn-arena$p
                       (resize-fn-arena$p-size (max 64 (* 2 h)) fn-arena$p)))
         (fn-arena$p (update-fn-arena$p-offi h start fn-arena$p))
         (fn-arena$p (update-fn-arena$p-sizei h (- (fn-arena$p-fill fn-arena$p) start) fn-arena$p)))
    (update-fn-arena$p-count (1+ h) fn-arena$p)))

(defun fn-arena$p-seal-list (xs fn-arena$p)
  (declare (xargs :stobjs fn-arena$p
                  :guard (and (fn-cbor-octet-listp xs) (fn-arena$p-wfp fn-arena$p))
                  :verify-guards nil))
  (let* ((start (fn-arena$p-fill fn-arena$p))
         (fn-arena$p (fn-arp-write xs fn-arena$p)))
    (fn-arp-seal-entry start fn-arena$p)))

(defun fn-arena$p-seal-buffer (fn-octets fn-arena$p)
  (declare (xargs :stobjs (fn-octets fn-arena$p)
                  :guard (fn-arena$p-wfp fn-arena$p)
                  :verify-guards nil))
  (let* ((start (fn-arena$p-fill fn-arena$p))
         (fn-arena$p (fn-arp-write-buffer 0 (fn-octets-len fn-octets) fn-octets fn-arena$p)))
    (fn-arp-seal-entry start fn-arena$p)))

(defun fn-arena$p-seal-range (a b fn-octets fn-arena$p)
  (declare (xargs :stobjs (fn-octets fn-arena$p)
                  :guard (and (natp a) (natp b) (<= a b) (<= b (fn-octets-len fn-octets))
                              (fn-arena$p-wfp fn-arena$p))
                  :verify-guards nil))
  (let* ((start (fn-arena$p-fill fn-arena$p))
         (fn-arena$p (fn-arp-write-buffer a b fn-octets fn-arena$p)))
    (fn-arp-seal-entry start fn-arena$p)))

(defthm fn-arp-write-steps
  (implies (and (fn-arp-okp fn-arena$p)
                (<= (nth 4 fn-arena$p) (fn-arp-cap fn-arena$p))
                (fn-cbor-octet-listp xs))
           (let ((next (fn-arp-write xs fn-arena$p)))
             (and (fn-arp-okp next)
                  (equal (nth 1 next) (nth 1 fn-arena$p))
                  (equal (nth 2 next) (nth 2 fn-arena$p))
                  (equal (nth 3 next) (nth 3 fn-arena$p))
                  (equal (nth 4 next) (+ (nth 4 fn-arena$p) (len xs)))
                  (<= (+ (nth 4 fn-arena$p) (len xs)) (fn-arp-cap next)))))
  :hints (("Goal" :induct (fn-arp-write xs fn-arena$p))))

(defthm fn-arp-write-room
  (implies (and (fn-arp-okp fn-arena$p)
                (<= (nth 4 fn-arena$p) (fn-arp-cap fn-arena$p))
                (fn-cbor-octet-listp xs))
           (<= (+ (nth 4 fn-arena$p) (len xs)) (fn-arp-cap (fn-arp-write xs fn-arena$p))))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-arp-write-steps))
           :in-theory (disable fn-arp-write-steps fn-arp-write))))

(defthm fn-arp-write-keeps-list-from-below-fill
  (implies (and (fn-arp-okp fn-arena$p)
                (<= (nth 4 fn-arena$p) (fn-arp-cap fn-arena$p))
                (fn-cbor-octet-listp xs)
                (natp n) (<= n (nth 4 fn-arena$p)))
           (equal (fn-oct-list-from i n (fn-arp-buf (fn-arp-write xs fn-arena$p)))
                  (fn-oct-list-from i n (fn-arp-buf fn-arena$p))))
  :hints (("Goal" :induct (fn-arp-write xs fn-arena$p))))

(defthm fn-arp-write-keeps-nth-below-fill
  (implies (and (fn-arp-okp fn-arena$p)
                (<= (nth 4 fn-arena$p) (fn-arp-cap fn-arena$p))
                (fn-cbor-octet-listp xs)
                (natp k) (< k (nth 4 fn-arena$p)))
           (equal (nth k (fn-arp-buf (fn-arp-write xs fn-arena$p)))
                  (nth k (fn-arp-buf fn-arena$p))))
  :hints (("Goal" :use ((:instance fn-arp-write-keeps-list-from-below-fill (i k) (n (1+ k)))
                        (:instance fn-oct-nth-of-list-from (i k) (n (1+ k)) (k 0)
                                   (buf (fn-arp-buf (fn-arp-write xs fn-arena$p))))
                        (:instance fn-oct-nth-of-list-from (i k) (n (1+ k)) (k 0)
                                   (buf (fn-arp-buf fn-arena$p))))
           :in-theory (disable fn-arp-write-keeps-list-from-below-fill fn-oct-nth-of-list-from))))

(defthm fn-arp-write-appends
  (implies (and (fn-arp-okp fn-arena$p)
                (<= (nth 4 fn-arena$p) (fn-arp-cap fn-arena$p))
                (fn-cbor-octet-listp xs))
           (equal (fn-oct-list-from (nth 4 fn-arena$p) (+ (nth 4 fn-arena$p) (len xs))
                                    (fn-arp-buf (fn-arp-write xs fn-arena$p)))
                  xs))
  :hints (("Goal" :induct (fn-arp-write xs fn-arena$p)
           :in-theory (enable fn-oct-list-from))
          ("Subgoal *1/2" :use ((:instance fn-arp-write-keeps-nth-below-fill
                                           (xs (cdr xs))
                                           (fn-arena$p (fn-arp-write-octet (car xs) fn-arena$p))
                                           (k (nth 4 fn-arena$p))))
           :in-theory (e/d (fn-oct-list-from) (fn-arp-write-keeps-nth-below-fill)))))

(defthm fn-arp-write-keeps-slices
  (implies (and (fn-arp-okp fn-arena$p)
                (<= (nth 4 fn-arena$p) (fn-arp-cap fn-arena$p))
                (fn-cbor-octet-listp xs)
                (fn-arn-rangesp h count off size (nth 4 fn-arena$p)))
           (equal (fn-arn-slices h count off size (fn-arp-buf (fn-arp-write xs fn-arena$p)))
                  (fn-arn-slices h count off size (fn-arp-buf fn-arena$p))))
  :hints (("Goal" :in-theory (enable fn-arn-slices fn-arn-rangesp)
           :induct (fn-arn-slices h count off size (fn-arp-buf fn-arena$p)))))

(local (in-theory (disable fn-arp-write)))

; -----------------------------------------------------------------------------
; The shapes the guards need (no page invariant: the guards are executable).

(defthm fn-arp-add-page-shape
  (implies (and (fn-arena$pp fn-arena$p) (<= (nth 5 fn-arena$p) (len (nth 0 fn-arena$p))))
           (let ((next (fn-arp-add-page fn-arena$p)))
             (and (fn-arena$pp next)
                  (<= (nth 5 next) (len (nth 0 next)))
                  (equal (nth 1 next) (nth 1 fn-arena$p))
                  (equal (nth 2 next) (nth 2 fn-arena$p))
                  (equal (nth 3 next) (nth 3 fn-arena$p))
                  (equal (nth 4 next) (nth 4 fn-arena$p))
                  (equal (nth 5 next) (1+ (nth 5 fn-arena$p))))))
  :hints (("Goal" :in-theory (enable fn-arp-add-page))))

(defthm fn-arp-add-page-room
  (implies (and (fn-arena$pp fn-arena$p) (<= (nth 5 fn-arena$p) (len (nth 0 fn-arena$p))))
           (<= (+ 1 (nth 5 fn-arena$p)) (len (nth 0 (fn-arp-add-page fn-arena$p)))))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-arp-add-page-shape))
           :in-theory (disable fn-arp-add-page-shape))))

(defthm fn-arp-put-shape
  (implies (and (fn-arena$pp fn-arena$p) (<= (nth 5 fn-arena$p) (len (nth 0 fn-arena$p)))
                (natp p) (< p (* *fn-arp-page* (nth 5 fn-arena$p))) (fn-cbor-octetp o))
           (let ((next (fn-arp-put p o fn-arena$p)))
             (and (fn-arena$pp next)
                  (equal (len (nth 0 next)) (len (nth 0 fn-arena$p)))
                  (equal (nth 1 next) (nth 1 fn-arena$p))
                  (equal (nth 2 next) (nth 2 fn-arena$p))
                  (equal (nth 3 next) (nth 3 fn-arena$p))
                  (equal (nth 4 next) (nth 4 fn-arena$p))
                  (equal (nth 5 next) (nth 5 fn-arena$p)))))
  :hints (("Goal" :in-theory (e/d (fn-arp-put) (fn-arp-cap-of-npages))
           :use ((:instance fn-arp-floor-below (np (nth 5 fn-arena$p)))))))

(verify-guards fn-arp-write-octet
  :hints (("Goal" :in-theory (disable fn-arp-cap-of-npages))))

(defthm fn-arp-write-octet-shape
  (implies (and (fn-arena$pp fn-arena$p) (<= (nth 5 fn-arena$p) (len (nth 0 fn-arena$p)))
                (<= (nth 4 fn-arena$p) (* *fn-arp-page* (nth 5 fn-arena$p)))
                (fn-cbor-octetp o))
           (let ((next (fn-arp-write-octet o fn-arena$p)))
             (and (fn-arena$pp next)
                  (<= (nth 5 next) (len (nth 0 next)))
                  (<= (nth 4 next) (* *fn-arp-page* (nth 5 next)))
                  (equal (nth 1 next) (nth 1 fn-arena$p))
                  (equal (nth 2 next) (nth 2 fn-arena$p))
                  (equal (nth 3 next) (nth 3 fn-arena$p))
                  (equal (nth 4 next) (1+ (nth 4 fn-arena$p))))))
  :hints (("Goal" :in-theory (e/d (fn-arp-write-octet) (fn-arp-cap-of-npages)))))

(defthm fn-arp-write-octet-shape-room
  (implies (and (fn-arena$pp fn-arena$p) (<= (nth 5 fn-arena$p) (len (nth 0 fn-arena$p)))
                (<= (nth 4 fn-arena$p) (* *fn-arp-page* (nth 5 fn-arena$p)))
                (fn-cbor-octetp o))
           (and (<= (+ 1 (nth 4 fn-arena$p))
                    (* *fn-arp-page* (nth 5 (fn-arp-write-octet o fn-arena$p))))
                (<= (nth 5 (fn-arp-write-octet o fn-arena$p))
                    (len (nth 0 (fn-arp-write-octet o fn-arena$p))))))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-arp-write-octet-shape))
           :in-theory (disable fn-arp-write-octet-shape fn-arp-cap-of-npages))))

(verify-guards fn-arp-write
  :hints (("Goal" :in-theory (disable fn-arp-cap-of-npages))))


(defthm fn-arp-write-shape
  (implies (and (fn-arena$pp fn-arena$p) (<= (nth 5 fn-arena$p) (len (nth 0 fn-arena$p)))
                (<= (nth 4 fn-arena$p) (* *fn-arp-page* (nth 5 fn-arena$p)))
                (fn-cbor-octet-listp xs))
           (let ((next (fn-arp-write xs fn-arena$p)))
             (and (fn-arena$pp next)
                  (<= (nth 5 next) (len (nth 0 next)))
                  (<= (nth 4 next) (* *fn-arp-page* (nth 5 next)))
                  (equal (nth 1 next) (nth 1 fn-arena$p))
                  (equal (nth 2 next) (nth 2 fn-arena$p))
                  (equal (nth 3 next) (nth 3 fn-arena$p))
                  (equal (nth 4 next) (+ (nth 4 fn-arena$p) (len xs))))))
  :hints (("Goal" :induct (fn-arp-write xs fn-arena$p)
           :in-theory (e/d (fn-arp-write) (fn-arp-cap-of-npages)))))

; The buffer copy is the write of the buffer's slice, hence of its value.
(defthm fn-arp-write-buffer-is-write
  (equal (fn-arp-write-buffer i n fn-octets fn-arena$p)
         (fn-arp-write (fn-oct-slice-list i n fn-octets) fn-arena$p))
  :hints (("Goal" :induct (fn-arp-write-buffer i n fn-octets fn-arena$p)
           :in-theory (e/d (fn-arp-write fn-oct-slice-list) (fn-arp-write-octet))
           :expand ((fn-oct-slice-list i n fn-octets)))))

;; The bulk write's equality with the octet-at-a-time definition.
(defthm fn-arp-put-is-put-kj
  (equal (fn-arp-put p o fn-arena$p)
         (fn-arp-put-kj (floor p *fn-arp-page*) (mod p *fn-arp-page*) o fn-arena$p))
  :hints (("Goal" :in-theory (enable fn-arp-put))))

(encapsulate
  ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm fn-arp-floor-mod-of-kj
    (implies (and (natp k) (natp j) (< j 262144))
             (and (equal (floor (+ j (* 262144 k)) 262144) k)
                  (equal (mod (+ j (* 262144 k)) 262144) j)))))

(defthm fn-arp-put-kj-keeps-the-fields
  (and (equal (nth *fn-arena$p-fill* (fn-arp-put-kj k j o fn-arena$p))
              (nth *fn-arena$p-fill* fn-arena$p))
       (equal (nth *fn-arena$p-npages* (fn-arp-put-kj k j o fn-arena$p))
              (nth *fn-arena$p-npages* fn-arena$p)))
  :hints (("Goal" :in-theory (enable fn-arp-put-kj nth update-nth))))

(defthm fn-arp-write-buffer-step
  (implies (and (natp i) (natp n) (< i n))
           (equal (fn-arp-write-buffer i n fn-octets fn-arena$p)
                  (fn-arp-write-buffer (1+ i) n fn-octets
                                       (fn-arp-write-octet (fn-octets-get i fn-octets)
                                                           fn-arena$p))))
  :hints (("Goal" :in-theory (disable fn-arp-write-buffer-is-write)
           :expand ((fn-arp-write-buffer i n fn-octets fn-arena$p)))))

(defthm fn-arp-write-buffer-done
  (implies (<= (nfix n) (nfix i))
           (equal (fn-arp-write-buffer i n fn-octets fn-arena$p) fn-arena$p))
  :hints (("Goal" :in-theory (disable fn-arp-write-buffer-is-write)
           :expand ((fn-arp-write-buffer i n fn-octets fn-arena$p)))))

(defthm fn-arp-write-octet-inside
  (implies (and (natp (nth *fn-arena$p-fill* fn-arena$p))
                (< (nth *fn-arena$p-fill* fn-arena$p)
                   (* *fn-arp-page* (nfix (nth *fn-arena$p-npages* fn-arena$p)))))
           (equal (fn-arp-write-octet o fn-arena$p)
                  (update-nth *fn-arena$p-fill* (1+ (nth *fn-arena$p-fill* fn-arena$p))
                              (fn-arp-put (nth *fn-arena$p-fill* fn-arena$p) o fn-arena$p))))
  :hints (("Goal" :in-theory (e/d (fn-arp-write-octet) (fn-arp-put-is-put-kj)))))

(local
 (defthm fn-arp-floor-mod-of-fill
   (implies (and (equal (nth *fn-arena$p-fill* fn-arena$p) (+ j (* 262144 k)))
                 (natp k) (natp j) (< j 262144))
            (and (equal (floor (nth *fn-arena$p-fill* fn-arena$p) 262144) k)
                 (equal (mod (nth *fn-arena$p-fill* fn-arena$p) 262144) j)))))

(defthm fn-arp-write-in-page-is-write-buffer
  (implies (and (natp k) (natp j) (natp e) (natp i) (<= j e) (<= e *fn-arp-page*)
                (equal (nth 4 fn-arena$p) (+ j (* *fn-arp-page* k)))
                (< k (nfix (nth 5 fn-arena$p))))
           (equal (fn-arp-write-in-page k j e i fn-octets fn-arena$p)
                  (fn-arp-write-buffer i (+ i (- e j)) fn-octets fn-arena$p)))
  :hints (("Goal" :induct (fn-arp-write-in-page k j e i fn-octets fn-arena$p)
           :in-theory (e/d () (fn-arp-put-kj fn-arp-add-page fn-arp-write-octet
                               fn-arp-write-buffer-is-write)))))

(defthm fn-arp-add-page-fields
  (and (equal (nth *fn-arena$p-fill* (fn-arp-add-page fn-arena$p))
              (nth *fn-arena$p-fill* fn-arena$p))
       (equal (nth *fn-arena$p-npages* (fn-arp-add-page fn-arena$p))
              (+ 1 (nth *fn-arena$p-npages* fn-arena$p))))
  :hints (("Goal" :in-theory (enable fn-arp-add-page nth update-nth))))

(defthm fn-arp-write-in-page-fields
  (implies (and (natp j) (natp e) (<= j e) (acl2-numberp (nth *fn-arena$p-fill* fn-arena$p)))
           (and (equal (nth *fn-arena$p-fill* (fn-arp-write-in-page k j e i fn-octets fn-arena$p))
                       (+ (- e j) (nth *fn-arena$p-fill* fn-arena$p)))
                (equal (nth *fn-arena$p-npages* (fn-arp-write-in-page k j e i fn-octets fn-arena$p))
                       (nth *fn-arena$p-npages* fn-arena$p))))
  :hints (("Goal" :induct (fn-arp-write-in-page k j e i fn-octets fn-arena$p)
           :in-theory (disable fn-arp-put-kj))))

; Appending two buffer writes.
(defthm fn-arp-write-buffer-append
  (implies (and (natp i) (natp m) (natp n) (<= i m) (<= m n))
           (equal (fn-arp-write-buffer m n fn-octets (fn-arp-write-buffer i m fn-octets fn-arena$p))
                  (fn-arp-write-buffer i n fn-octets fn-arena$p)))
  :hints (("Goal" :induct (fn-arp-write-buffer i m fn-octets fn-arena$p)
           :in-theory (disable fn-arp-write-buffer-is-write fn-arp-write-octet))))

; A full arena: the first octet's write adds the page either way.
(defthm fn-arp-write-octet-at-full
  (implies (and (natp (nth *fn-arena$p-fill* fn-arena$p))
                (natp (nth *fn-arena$p-npages* fn-arena$p))
                (equal (nth *fn-arena$p-fill* fn-arena$p)
                       (* *fn-arp-page* (nth *fn-arena$p-npages* fn-arena$p))))
           (equal (fn-arp-write-octet o (fn-arp-add-page fn-arena$p))
                  (fn-arp-write-octet o fn-arena$p)))
  :hints (("Goal" :in-theory (e/d (fn-arp-write-octet) (fn-arp-add-page fn-arp-put
                                                          fn-arp-put-is-put-kj
                                                          fn-arp-write-octet-inside)))))


(defthm fn-arp-write-buffer-at-full
  (implies (and (natp i) (natp n) (< i n)
                (natp (nth *fn-arena$p-fill* fn-arena$p))
                (natp (nth *fn-arena$p-npages* fn-arena$p))
                (equal (nth *fn-arena$p-fill* fn-arena$p)
                       (* *fn-arp-page* (nth *fn-arena$p-npages* fn-arena$p))))
           (equal (fn-arp-write-buffer i n fn-octets (fn-arp-add-page fn-arena$p))
                  (fn-arp-write-buffer i n fn-octets fn-arena$p)))
  :hints (("Goal" :in-theory (disable fn-arp-write-buffer-is-write fn-arp-add-page
                                      fn-arp-write-octet))))

(encapsulate
  ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm fn-arp-floor-mod-split
    (implies (natp f)
             (equal (+ (mod f 262144) (* 262144 (floor f 262144))) f)))
  (defthm fn-arp-floor-below-np
    (implies (and (natp f) (natp np) (< f (* 262144 np)))
             (< (floor f 262144) np))
    :rule-classes (:rewrite :linear))
  (defthm fn-arp-floor-le
    (implies (natp f)
             (and (integerp (floor f 262144))
                  (<= 0 (floor f 262144))
                  (<= (* 262144 (floor f 262144)) f)
                  (< f (+ 262144 (* 262144 (floor f 262144))))))
    :rule-classes ((:linear :corollary (implies (natp f) (<= (* 262144 (floor f 262144)) f)))
                   (:linear :corollary (implies (natp f) (< f (+ 262144 (* 262144 (floor f 262144))))))
                   (:type-prescription :corollary (implies (natp f) (natp (floor f 262144))))))
  (defthm fn-arp-floor-of-full
    (implies (natp np)
             (and (equal (floor (* 262144 np) 262144) np)
                  (equal (mod (* 262144 np) 262144) 0)))))

(defthmd fn-arp-mod-is-difference
  (equal (mod f 262144) (- f (* 262144 (floor f 262144))))
  :hints (("Goal" :in-theory '(mod commutativity-of-*))))

(defthm fn-arp-write-buffer-fields-inside
  (implies (and (natp i) (natp m) (<= i m)
                (natp (nth *fn-arena$p-fill* fn-arena$p))
                (natp (nth *fn-arena$p-npages* fn-arena$p))
                (<= (+ (nth *fn-arena$p-fill* fn-arena$p) (- m i))
                    (* *fn-arp-page* (nth *fn-arena$p-npages* fn-arena$p))))
           (and (equal (nth *fn-arena$p-fill* (fn-arp-write-buffer i m fn-octets fn-arena$p))
                       (+ (nth *fn-arena$p-fill* fn-arena$p) (- m i)))
                (equal (nth *fn-arena$p-npages* (fn-arp-write-buffer i m fn-octets fn-arena$p))
                       (nth *fn-arena$p-npages* fn-arena$p))))
  :hints (("Goal" :induct (fn-arp-write-buffer i m fn-octets fn-arena$p)
           :in-theory (disable fn-arp-write-buffer-is-write fn-arp-put-kj))))

(defthm fn-arp-write-buffer-fill
  (implies (and (natp i) (natp m) (<= i m) (natp (nth *fn-arena$p-fill* fn-arena$p)))
           (equal (nth *fn-arena$p-fill* (fn-arp-write-buffer i m fn-octets fn-arena$p))
                  (+ (nth *fn-arena$p-fill* fn-arena$p) (- m i))))
  :hints (("Goal" :induct (fn-arp-write-buffer i m fn-octets fn-arena$p)
           :in-theory (e/d (fn-arp-write-octet)
                           (fn-arp-write-buffer-is-write fn-arp-put-kj fn-arp-add-page
                            fn-arp-write-octet-inside)))))

(defthm fn-arp-write-buffer-npages-from-full
  (implies (and (natp i) (natp m) (< i m)
                (natp (nth *fn-arena$p-fill* fn-arena$p))
                (natp (nth *fn-arena$p-npages* fn-arena$p))
                (equal (nth *fn-arena$p-fill* fn-arena$p)
                       (* *fn-arp-page* (nth *fn-arena$p-npages* fn-arena$p)))
                (<= (+ (nth *fn-arena$p-fill* fn-arena$p) (- m i))
                    (* *fn-arp-page* (+ 1 (nth *fn-arena$p-npages* fn-arena$p)))))
           (equal (nth *fn-arena$p-npages* (fn-arp-write-buffer i m fn-octets fn-arena$p))
                  (+ 1 (nth *fn-arena$p-npages* fn-arena$p))))
  :hints (("Goal" :in-theory (e/d (fn-arp-write-octet)
                                  (fn-arp-write-buffer-at-full fn-arp-write-buffer-is-write
                                   fn-arp-add-page fn-arp-put-kj fn-arp-write-octet-inside)))))

(defthm fn-arp-write-run-is-write-buffer
  (implies (and (natp (nth *fn-arena$p-fill* fn-arena$p))
                (natp (nth *fn-arena$p-npages* fn-arena$p))
                (<= (nth *fn-arena$p-fill* fn-arena$p)
                    (* *fn-arp-page* (nth *fn-arena$p-npages* fn-arena$p))))
           (equal (fn-arp-write-run i n fn-octets fn-arena$p)
                  (fn-arp-write-buffer i n fn-octets fn-arena$p)))
  :hints (("Goal" :induct (fn-arp-write-run i n fn-octets fn-arena$p)
           :in-theory (e/d (fn-arp-mod-is-difference)
                           (fn-arp-write-buffer-is-write fn-arp-add-page
                            fn-arp-write-octet fn-arp-write-in-page fn-arp-put-kj
                            fn-arp-write-buffer-step fn-arp-write-octet-inside)))))

(verify-guards fn-arp-write-run
  :hints (("Goal" :in-theory (e/d (fn-arp-mod-is-difference fn-oct-octets-p-is-octet-listp)
                                  (fn-arp-write-buffer-step fn-arp-write-octet fn-arp-write
                                   fn-arp-add-page fn-arp-put-kj fn-arp-write-octet-inside
                                   fn-arp-cap-of-npages fn-oct-slice-list-is-take-nthcdr
                                   fn-arp-write-shape))
           :use ((:instance fn-arp-write-shape (xs (fn-oct-slice-list i n fn-octets)))
                 (:instance fn-arp-write-shape
                            (xs (fn-oct-slice-list
                                 i (+ 262144 i (- (nth *fn-arena$p-fill* fn-arena$p))
                                      (* 262144 (floor (nth *fn-arena$p-fill* fn-arena$p) 262144)))
                                 fn-octets)))
                 (:instance fn-arp-write-shape (fn-arena$p (fn-arp-add-page fn-arena$p))
                            (xs (fn-oct-slice-list i n fn-octets)))
                 (:instance fn-arp-write-shape (fn-arena$p (fn-arp-add-page fn-arena$p))
                            (xs (fn-oct-slice-list i (+ 262144 i) fn-octets)))
                 (:instance fn-arp-add-page-shape)))))

(verify-guards fn-arp-write-buffer
  :hints (("Goal" :in-theory (disable fn-arp-cap-of-npages fn-arp-write-run
                                      fn-arp-write-buffer-is-write fn-arp-write-octet))))

(verify-guards fn-arena$p-seal-list
  :hints (("Goal" :in-theory (disable fn-arp-cap-of-npages))))

(verify-guards fn-arena$p-seal-buffer
  :hints (("Goal" :in-theory (e/d (fn-oct-octets-p-is-octet-listp) (fn-arp-cap-of-npages)))))

(verify-guards fn-arena$p-seal-range
  :hints (("Goal" :in-theory (e/d (fn-oct-octets-p-is-octet-listp)
                                  (fn-oct-slice-list-is-take-nthcdr fn-arp-cap-of-npages)))))

(defthm fn-arp-seal-range-is-seal-list
  (equal (fn-arena$p-seal-range a b fn-octets fn-arena$p)
         (fn-arena$p-seal-list (fn-oct-slice-list a b fn-octets) fn-arena$p))
  :hints (("Goal" :in-theory (e/d (fn-arena$p-seal-list fn-arena$p-seal-range)
                                  (fn-oct-slice-list-is-take-nthcdr)))))

; The seal entry: the new handle is the old count, its range is
; [start, fill), every older slice and range is kept; the pages untouched.
(defthm fn-arp-seal-entry-step
  (implies (and (fn-arp-okp fn-arena$p)
                (<= (nth 3 fn-arena$p) (len (nth 1 fn-arena$p)))
                (<= (nth 3 fn-arena$p) (len (nth 2 fn-arena$p)))
                (natp start) (<= start (nth 4 fn-arena$p)))
           (let ((next (fn-arp-seal-entry start fn-arena$p)))
             (and (fn-arp-okp next)
                  (equal (fn-arp-buf next) (fn-arp-buf fn-arena$p))
                  (equal (fn-arp-cap next) (fn-arp-cap fn-arena$p))
                  (equal (nth 3 next) (1+ (nth 3 fn-arena$p)))
                  (equal (nth 4 next) (nth 4 fn-arena$p))
                  (<= (nth 3 next) (len (nth 1 next)))
                  (<= (nth 3 next) (len (nth 2 next)))
                  (equal (nth (nth 3 fn-arena$p) (nth 1 next)) start)
                  (equal (nth (nth 3 fn-arena$p) (nth 2 next)) (- (nth 4 fn-arena$p) start))
                  (equal (fn-arn-slices 0 (nth 3 fn-arena$p) (nth 1 next) (nth 2 next) buf)
                         (fn-arn-slices 0 (nth 3 fn-arena$p) (nth 1 fn-arena$p) (nth 2 fn-arena$p) buf))
                  (equal (fn-arn-rangesp 0 (nth 3 fn-arena$p) (nth 1 next) (nth 2 next) top)
                         (fn-arn-rangesp 0 (nth 3 fn-arena$p) (nth 1 fn-arena$p) (nth 2 fn-arena$p) top)))))
  :hints (("Goal" :in-theory (enable fn-arp-seal-entry))))

(defthm fn-arp-seal-entry-room
  (implies (and (fn-arp-okp fn-arena$p)
                (<= (nth 3 fn-arena$p) (len (nth 1 fn-arena$p)))
                (<= (nth 3 fn-arena$p) (len (nth 2 fn-arena$p)))
                (natp start) (<= start (nth 4 fn-arena$p)))
           (and (< (nth 3 fn-arena$p) (len (nth 1 (fn-arp-seal-entry start fn-arena$p))))
                (< (nth 3 fn-arena$p) (len (nth 2 (fn-arp-seal-entry start fn-arena$p))))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use ((:instance fn-arp-seal-entry-step))
           :in-theory (disable fn-arp-seal-entry-step fn-arp-seal-entry))))

(defthm fn-arp-seal-entry-reads
  (implies (and (fn-arp-okp fn-arena$p)
                (<= (nth 3 fn-arena$p) (len (nth 1 fn-arena$p)))
                (<= (nth 3 fn-arena$p) (len (nth 2 fn-arena$p)))
                (natp start) (<= start (nth 4 fn-arena$p))
                (equal h (nth 3 fn-arena$p)))
           (and (equal (nth h (nth 1 (fn-arp-seal-entry start fn-arena$p))) start)
                (equal (nth h (nth 2 (fn-arp-seal-entry start fn-arena$p)))
                       (- (nth 4 fn-arena$p) start))
                (equal (fn-arn-slices 0 h (nth 1 (fn-arp-seal-entry start fn-arena$p))
                                      (nth 2 (fn-arp-seal-entry start fn-arena$p)) buf)
                       (fn-arn-slices 0 h (nth 1 fn-arena$p) (nth 2 fn-arena$p) buf))
                (equal (fn-arn-rangesp 0 h (nth 1 (fn-arp-seal-entry start fn-arena$p))
                                       (nth 2 (fn-arp-seal-entry start fn-arena$p)) top)
                       (fn-arn-rangesp 0 h (nth 1 fn-arena$p) (nth 2 fn-arena$p) top))))
  :hints (("Goal" :use ((:instance fn-arp-seal-entry-step))
           :in-theory (disable fn-arp-seal-entry-step fn-arp-seal-entry))))

(defthm fn-arp-write-appends-2
  (implies (and (fn-arp-okp fn-arena$p)
                (<= (nth 4 fn-arena$p) (fn-arp-cap fn-arena$p))
                (fn-cbor-octet-listp xs))
           (equal (fn-oct-list-from (nth 4 fn-arena$p) (+ (len xs) (nth 4 fn-arena$p))
                                    (fn-arp-buf (fn-arp-write xs fn-arena$p)))
                  xs))
  :hints (("Goal" :use ((:instance fn-arp-write-appends)))))

(local (in-theory (disable fn-arp-seal-entry)))

; The seal, in one lemma: the slices grow by the octets written.
(defthm fn-arp-seal-list-step
  (implies (and (fn-arp-okp fn-arena$p)
                (<= (nth 4 fn-arena$p) (fn-arp-cap fn-arena$p))
                (<= (nth 3 fn-arena$p) (len (nth 1 fn-arena$p)))
                (<= (nth 3 fn-arena$p) (len (nth 2 fn-arena$p)))
                (fn-arn-rangesp 0 (nth 3 fn-arena$p) (nth 1 fn-arena$p) (nth 2 fn-arena$p)
                                (nth 4 fn-arena$p))
                (fn-cbor-octet-listp xs))
           (let ((next (fn-arena$p-seal-list xs fn-arena$p)))
             (and (fn-arp-okp next)
                  (<= (nth 4 next) (fn-arp-cap next))
                  (<= (nth 3 next) (len (nth 1 next)))
                  (<= (nth 3 next) (len (nth 2 next)))
                  (fn-arn-rangesp 0 (nth 3 next) (nth 1 next) (nth 2 next) (nth 4 next))
                  (equal (fn-arn-slices 0 (nth 3 next) (nth 1 next) (nth 2 next) (fn-arp-buf next))
                         (append (fn-arn-slices 0 (nth 3 fn-arena$p) (nth 1 fn-arena$p)
                                                (nth 2 fn-arena$p) (fn-arp-buf fn-arena$p))
                                 (list xs))))))
  :hints (("Goal" :use ((:instance fn-arn-slices-snoc
                                   (h 0) (n (nth 3 fn-arena$p))
                                   (off (nth 1 (fn-arp-seal-entry (nth 4 fn-arena$p) (fn-arp-write xs fn-arena$p))))
                                   (size (nth 2 (fn-arp-seal-entry (nth 4 fn-arena$p) (fn-arp-write xs fn-arena$p))))
                                   (buf (fn-arp-buf (fn-arp-write xs fn-arena$p))))
                        (:instance fn-arn-rangesp-snoc
                                   (h 0) (n (nth 3 fn-arena$p))
                                   (off (nth 1 (fn-arp-seal-entry (nth 4 fn-arena$p) (fn-arp-write xs fn-arena$p))))
                                   (size (nth 2 (fn-arp-seal-entry (nth 4 fn-arena$p) (fn-arp-write xs fn-arena$p))))
                                   (top (+ (nth 4 fn-arena$p) (len xs)))))
           :do-not-induct t)))

(local (in-theory (disable fn-arena$p-seal-list)))

; -----------------------------------------------------------------------------
; The reads: an octet at a position is the flat view's, and the payload
; reader conses the flat view's range.

(defthm fn-arp-byte-is-nth
  (implies (and (fn-arp-okp fn-arena$p) (natp p) (< p (fn-arp-cap fn-arena$p)))
           (equal (fn-arp-byte p fn-arena$p) (nth p (fn-arp-buf fn-arena$p))))
  :hints (("Goal" :in-theory (e/d (fn-arp-byte fn-arp-buf fn-arp-cap fn-arp-okp)
                                  (fn-arp-cap-of-npages fn-arp-nth-flat-at))
           :use ((:instance fn-arp-floor-below (np (nth 5 fn-arena$p)))
                 (:instance fn-arp-nth-flat-at (np (nth 5 fn-arena$p)) (pages (nth 0 fn-arena$p)))
                 (:instance fn-arp-nth-fullp (np (nth 5 fn-arena$p)) (pages (nth 0 fn-arena$p))
                            (k (floor p *fn-arp-page*)))))))

(local
 (defthm fn-arp-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(defthm fn-arp-page-down-is-list-from
  (implies (and (natp lo) (natp hi) (<= lo hi) (<= hi (len (nth 0 pg))) (true-listp acc))
           (equal (fn-arp-page-down lo hi acc pg)
                  (append (fn-oct-list-from lo hi (nth 0 pg)) acc)))
  :hints (("Goal" :induct (fn-arp-page-down lo hi acc pg)
           :in-theory (enable fn-arp-page-down))
          ("Subgoal *1/2" :use ((:instance fn-oct-list-from-snoc
                                           (i lo) (n (1- hi)) (buf (nth 0 pg)))))))

(defthm fn-arp-list-from-split
  (implies (and (natp i) (natp m) (natp n) (<= i m) (<= m n))
           (equal (fn-oct-list-from i n buf)
                  (append (fn-oct-list-from i m buf) (fn-oct-list-from m n buf))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-oct-list-from i m buf) :in-theory (enable fn-oct-list-from))))

(local
 (defun fn-arp-ab-ind (a b)
   (declare (xargs :measure (nfix (- (nfix b) (nfix a)))))
   (if (or (not (natp a)) (not (natp b)) (<= b a))
       a
     (fn-arp-ab-ind (1+ a) b))))

(defthm fn-arp-list-from-flat-in-page
  (implies (and (fn-arp-fullp np pages) (natp np) (natp k) (< k np)
                (natp a) (natp b) (<= a b) (<= b *fn-arp-page*))
           (equal (fn-oct-list-from (+ a (* *fn-arp-page* k)) (+ b (* *fn-arp-page* k))
                                    (fn-arp-flat np pages))
                  (fn-oct-list-from a b (nth 0 (nth k pages)))))
  :hints (("Goal" :induct (fn-arp-ab-ind a b)
           :in-theory (enable fn-oct-list-from))))

(defthm fn-arp-list-pages-is-list-from
  (implies (and (fn-arp-okp fn-arena$p) (natp i) (natp n) (<= i n)
                (<= n (fn-arp-cap fn-arena$p)) (true-listp acc))
           (equal (fn-arp-list-pages i n acc fn-arena$p)
                  (append (fn-oct-list-from i n (fn-arp-buf fn-arena$p)) acc)))
  :hints (("Goal" :induct (fn-arp-list-pages i n acc fn-arena$p)
           :in-theory (e/d (fn-arp-list-pages fn-arp-buf fn-arp-cap fn-arp-okp)
                           (fn-arp-cap-of-npages)))
          ("Subgoal *1/2"
           :use ((:instance fn-arp-floor-base (x (1- n)))
                 (:instance fn-arp-floor-below (p (1- n)) (np (nth 5 fn-arena$p)))
                 (:instance fn-arp-list-from-split
                            (m (max i (* *fn-arp-page* (floor (1- n) *fn-arp-page*))))
                            (buf (fn-arp-flat (nth 5 fn-arena$p) (nth 0 fn-arena$p))))
                 (:instance fn-arp-list-from-flat-in-page
                            (np (nth 5 fn-arena$p)) (pages (nth 0 fn-arena$p))
                            (k (floor (1- n) *fn-arp-page*))
                            (a (- (max i (* *fn-arp-page* (floor (1- n) *fn-arp-page*)))
                                  (* *fn-arp-page* (floor (1- n) *fn-arp-page*))))
                            (b (- n (* *fn-arp-page* (floor (1- n) *fn-arp-page*))))))
           :in-theory (e/d (fn-arp-list-pages fn-arp-buf fn-arp-cap fn-arp-okp)
                           (fn-arp-cap-of-npages fn-arp-list-from-flat-in-page)))))

(local (in-theory (disable fn-arp-byte fn-arp-list-pages)))

; -----------------------------------------------------------------------------
; The abstraction relation: `fn-arena$corr''s, over the flat view.

(defun fn-arena$pcorr (fn-arena$p fn-arena$a)
  (declare (xargs :verify-guards nil))
  (and (fn-arp-okp fn-arena$p)
       (fn-arn-payload-listp fn-arena$a)
       (<= (nth *fn-arena$p-fill* fn-arena$p) (fn-arp-cap fn-arena$p))
       (<= (nth *fn-arena$p-count* fn-arena$p) (len (nth *fn-arena$p-offi* fn-arena$p)))
       (<= (nth *fn-arena$p-count* fn-arena$p) (len (nth *fn-arena$p-sizei* fn-arena$p)))
       (fn-arn-rangesp 0 (nth *fn-arena$p-count* fn-arena$p)
                       (nth *fn-arena$p-offi* fn-arena$p) (nth *fn-arena$p-sizei* fn-arena$p)
                       (nth *fn-arena$p-fill* fn-arena$p))
       (equal (fn-arn-slices 0 (nth *fn-arena$p-count* fn-arena$p)
                             (nth *fn-arena$p-offi* fn-arena$p) (nth *fn-arena$p-sizei* fn-arena$p)
                             (fn-arp-buf fn-arena$p))
              fn-arena$a)))

; -----------------------------------------------------------------------------
; The obligations, each as `defabsstobj-missing-events' states it.

(defthm create-fn-arena-paged{correspondence}
  (fn-arena$pcorr (create-fn-arena$p) (create-fn-arena$a))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-arena$pp fn-arp-okp fn-arp-buf fn-arp-cap
                                     fn-arn-slices fn-arn-rangesp))))

(defthm create-fn-arena-paged{preserved}
  (fn-arena$ap (create-fn-arena$a))
  :rule-classes nil)

(defthm fn-arena-paged-count{correspondence}
  (implies (fn-arena$pcorr fn-arena$p fn-arena-paged)
           (equal (fn-arena$p-count fn-arena$p) (fn-arena$a-count fn-arena-paged)))
  :rule-classes nil)

(defthm fn-arena-paged-payload-len{correspondence}
  (implies (and (fn-arena$pcorr fn-arena$p fn-arena-paged)
                (natp h) (< h (fn-arena$a-count fn-arena-paged)))
           (equal (fn-arena$p-payload-len h fn-arena$p) (fn-arena$a-payload-len h fn-arena-paged)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-arn-rangesp-at
                                   (h 0) (k h) (count (nth 3 fn-arena$p))
                                   (off (nth 1 fn-arena$p)) (size (nth 2 fn-arena$p))
                                   (top (nth 4 fn-arena$p)))))))

(defthm fn-arena-paged-payload-len{guard-thm}
  (implies (and (fn-arena$pcorr fn-arena$p fn-arena-paged)
                (natp h) (< h (fn-arena$a-count fn-arena-paged)))
           (and (natp h) (< h (fn-arena$p-count fn-arena$p))
                (fn-arena$p-wfp fn-arena$p)))
  :rule-classes nil)

(defthm fn-arena-paged-get{correspondence}
  (implies (and (fn-arena$pcorr fn-arena$p fn-arena-paged)
                (natp h) (< h (fn-arena$a-count fn-arena-paged))
                (natp i) (< i (fn-arena$a-payload-len h fn-arena-paged)))
           (equal (fn-arena$p-get h i fn-arena$p) (fn-arena$a-get h i fn-arena-paged)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-arn-rangesp-at
                                   (h 0) (k h) (count (nth 3 fn-arena$p))
                                   (off (nth 1 fn-arena$p)) (size (nth 2 fn-arena$p))
                                   (top (nth 4 fn-arena$p)))
                        (:instance fn-arp-byte-is-nth (p (+ i (nth h (nth 1 fn-arena$p)))))
                        (:instance fn-oct-nth-of-list-from
                                   (i (nth h (nth 1 fn-arena$p)))
                                   (n (+ (nth h (nth 1 fn-arena$p)) (nth h (nth 2 fn-arena$p))))
                                   (k i) (buf (fn-arp-buf fn-arena$p))))
           :in-theory (disable fn-arp-byte-is-nth fn-oct-nth-of-list-from))))

(defthm fn-arena-paged-get{guard-thm}
  (implies (and (fn-arena$pcorr fn-arena$p fn-arena-paged)
                (natp h) (< h (fn-arena$a-count fn-arena-paged))
                (natp i) (< i (fn-arena$a-payload-len h fn-arena-paged)))
           (and (fn-arena$p-wfp fn-arena$p)
                (natp h) (< h (fn-arena$p-count fn-arena$p))
                (natp i)
                (natp (fn-arena$p-offi h fn-arena$p))
                (natp (fn-arena$p-sizei h fn-arena$p))
                (< i (fn-arena$p-sizei h fn-arena$p))
                (<= (+ (fn-arena$p-offi h fn-arena$p) (fn-arena$p-sizei h fn-arena$p))
                    (fn-arena$p-fill fn-arena$p))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-arn-rangesp-at
                                   (h 0) (k h) (count (nth 3 fn-arena$p))
                                   (off (nth 1 fn-arena$p)) (size (nth 2 fn-arena$p))
                                   (top (nth 4 fn-arena$p)))))))

(local
 (defthm fn-arp-append-nil
   (implies (true-listp x) (equal (append x nil) x))))

(defthm fn-arena-paged-payload{correspondence}
  (implies (and (fn-arena$pcorr fn-arena$p fn-arena-paged)
                (natp h) (< h (fn-arena$a-count fn-arena-paged)))
           (equal (fn-arena$p-payload h fn-arena$p) (fn-arena$a-payload h fn-arena-paged)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-arn-rangesp-at
                                   (h 0) (k h) (count (nth 3 fn-arena$p))
                                   (off (nth 1 fn-arena$p)) (size (nth 2 fn-arena$p))
                                   (top (nth 4 fn-arena$p)))
                        (:instance fn-arp-list-pages-is-list-from
                                   (i (nth h (nth 1 fn-arena$p)))
                                   (n (+ (nth h (nth 1 fn-arena$p)) (nth h (nth 2 fn-arena$p))))
                                   (acc nil)))
           :in-theory (disable fn-arp-list-pages-is-list-from))))

(defthm fn-arena-paged-payload{guard-thm}
  (implies (and (fn-arena$pcorr fn-arena$p fn-arena-paged)
                (natp h) (< h (fn-arena$a-count fn-arena-paged)))
           (and (fn-arena$p-wfp fn-arena$p)
                (natp h) (< h (fn-arena$p-count fn-arena$p))
                (natp (fn-arena$p-offi h fn-arena$p))
                (natp (fn-arena$p-sizei h fn-arena$p))
                (<= (+ (fn-arena$p-offi h fn-arena$p) (fn-arena$p-sizei h fn-arena$p))
                    (fn-arena$p-fill fn-arena$p))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-arn-rangesp-at
                                   (h 0) (k h) (count (nth 3 fn-arena$p))
                                   (off (nth 1 fn-arena$p)) (size (nth 2 fn-arena$p))
                                   (top (nth 4 fn-arena$p)))))))

(defthm fn-arena-paged-seal-list{correspondence}
  (implies (and (fn-arena$pcorr fn-arena$p fn-arena-paged)
                (fn-cbor-octet-listp xs))
           (fn-arena$pcorr (fn-arena$p-seal-list xs fn-arena$p)
                           (fn-arena$a-seal-list xs fn-arena-paged)))
  :rule-classes nil)

(defthm fn-arena-paged-seal-list{guard-thm}
  (implies (and (fn-arena$pcorr fn-arena$p fn-arena-paged)
                (fn-cbor-octet-listp xs))
           (and (fn-cbor-octet-listp xs) (fn-arena$p-wfp fn-arena$p)))
  :rule-classes nil)

(defthm fn-arena-paged-seal-list{preserved}
  (implies (and (fn-arena$ap fn-arena-paged)
                (fn-cbor-octet-listp xs))
           (fn-arena$ap (fn-arena$a-seal-list xs fn-arena-paged)))
  :rule-classes nil)

(defthm fn-arena-paged-seal-buffer{correspondence}
  (implies (and (fn-arena$pcorr fn-arena$p fn-arena-paged)
                (fn-octets-p fn-octets))
           (fn-arena$pcorr (fn-arena$p-seal-buffer fn-octets fn-arena$p)
                           (fn-arena$a-seal-buffer fn-octets fn-arena-paged)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-arena$p-seal-list fn-oct-octets-p-is-octet-listp)
                                  (fn-arp-seal-list-step))
           :use ((:instance fn-arp-seal-list-step (xs fn-octets))))))

(defthm fn-arena-paged-seal-buffer{guard-thm}
  (implies (and (fn-arena$pcorr fn-arena$p fn-arena-paged)
                (fn-octets-p fn-octets))
           (fn-arena$p-wfp fn-arena$p))
  :rule-classes nil)

(defthm fn-arena-paged-seal-buffer{preserved}
  (implies (and (fn-arena$ap fn-arena-paged)
                (fn-octets-p fn-octets))
           (fn-arena$ap (fn-arena$a-seal-buffer fn-octets fn-arena-paged)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-oct-octets-p-is-octet-listp))))

(defthm fn-arena-paged-seal-range{correspondence}
  (implies (and (fn-arena$pcorr fn-arena$p fn-arena-paged)
                (fn-octets-p fn-octets)
                (natp a) (natp b) (<= a b) (<= b (fn-octets-len fn-octets)))
           (fn-arena$pcorr (fn-arena$p-seal-range a b fn-octets fn-arena$p)
                           (fn-arena$a-seal-range a b fn-octets fn-arena-paged)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-arena$p-seal-list fn-oct-octets-p-is-octet-listp)
                                  (fn-arp-seal-list-step fn-oct-slice-list-is-take-nthcdr))
           :use ((:instance fn-arp-seal-list-step (xs (fn-oct-slice-list a b fn-octets)))))))

(defthm fn-arena-paged-seal-range{guard-thm}
  (implies (and (fn-arena$pcorr fn-arena$p fn-arena-paged)
                (fn-octets-p fn-octets)
                (natp a) (natp b) (<= a b) (<= b (fn-octets-len fn-octets)))
           (and (natp a) (natp b) (<= a b) (<= b (fn-octets-len fn-octets))
                (fn-arena$p-wfp fn-arena$p)))
  :rule-classes nil)

(defthm fn-arena-paged-seal-range{preserved}
  (implies (and (fn-arena$ap fn-arena-paged)
                (fn-octets-p fn-octets)
                (natp a) (natp b) (<= a b) (<= b (fn-octets-len fn-octets)))
           (fn-arena$ap (fn-arena$a-seal-range a b fn-octets fn-arena-paged)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-oct-octets-p-is-octet-listp)
                                  (fn-oct-slice-list-is-take-nthcdr)))))

(defthm fn-arena-paged-clear{correspondence}
  (implies (fn-arena$pcorr fn-arena$p fn-arena-paged)
           (fn-arena$pcorr (fn-arena$p-clear fn-arena$p) (fn-arena$a-clear fn-arena-paged)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-arp-okp fn-arp-buf fn-arp-cap fn-arn-slices fn-arn-rangesp)
                                  (fn-arp-cap-of-npages)))))

(defthm fn-arena-paged-clear{preserved}
  (implies (fn-arena$ap fn-arena-paged)
           (fn-arena$ap (fn-arena$a-clear fn-arena-paged)))
  :rule-classes nil)

(defabsstobj fn-arena-paged
  :foundation fn-arena$p
  :recognizer (fn-arena-paged-p :logic fn-arena$ap :exec fn-arena$pp)
  :creator (create-fn-arena-paged :logic create-fn-arena$a :exec create-fn-arena$p)
  :corr-fn fn-arena$pcorr
  :exports ((fn-arena-paged-count :logic fn-arena$a-count :exec fn-arena$p-count)
            (fn-arena-paged-payload-len :logic fn-arena$a-payload-len :exec fn-arena$p-payload-len)
            (fn-arena-paged-get :logic fn-arena$a-get :exec fn-arena$p-get)
            (fn-arena-paged-payload :logic fn-arena$a-payload :exec fn-arena$p-payload)
            (fn-arena-paged-seal-list :logic fn-arena$a-seal-list :exec fn-arena$p-seal-list
                                      :protect t)
            (fn-arena-paged-seal-buffer :logic fn-arena$a-seal-buffer :exec fn-arena$p-seal-buffer
                                        :protect t)
            (fn-arena-paged-clear :logic fn-arena$a-clear :exec fn-arena$p-clear :protect t)
            (fn-arena-paged-seal-range :logic fn-arena$a-seal-range :exec fn-arena$p-seal-range
                                       :protect t)))
