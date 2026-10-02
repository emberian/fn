; fn: the payload arena with EXTENT handles, attached to the generic (lane
; arena-offheap-2, 2026-09-27; PRF-294; design:
; planning/evidence/arena-offheap-2026-09-27.md section 3).
;
; `fn-arena-extent' is an abstract stobj over `fn-arena$x', a concrete stobj
; with two fields: the paged arena `fn-arena-paged' (stage 1,
; books/payload-arena-paged.lisp) NESTED as a child, and one array EXT with
; an entry per handle: 0 for a resident handle, or the extent
; (FILE EOFF ELEN POFF PLEN TRAILER) of an extent handle.  A resident seal
; seals its octets into the paged child and marks the handle 0; an extent
; seal (`fn-arena$x-seal-extent') seals the EMPTY payload into the child
; (keeping the handle numbering: 16 octets of handle arrays, no payload
; octets) and records the extent.  A read of an extent handle calls the
; host's realizers `fn-durable-realize-octet' (one octet) and
; `fn-durable-realize-octets' (the payload) (A-DURABLE-EXTENT,
; books/assumptions.lisp): the host preads the entry into its bounded
; cache, ACL2 checks the entry's trailer, and a mismatch is refused by name
; (books/payload-extent.lisp; host/native/extent.lisp).
;
; The STAGE (lane arena-offheap-3, PRF-309): an array of page stobjs, one
; slot per handle, sized on demand.  A BUFFER seal (the owner's POST
; prepare, before its log batch is durable) copies the payload into the
; handle's own stage page and marks the handle :staged; once the batch is
; durable the owner RESEATS the handle as the extent the log wrote
; (`fn-arena$x-reseat-extent'), and later RELEASES its page
; (`fn-arena$x-release', which frees a page only under an extent entry).  So a
; committed payload leaves the heap after its barrier, and the staged octets
; are bounded by the batches not yet durable (the log's operator bounds).
;
; The abstraction.  The child's value, as a stobj field, is its LOGICAL
; value: the list of its payloads.  The relation `fn-arena$xcorr' says the
; generic's value is `fn-arx-view' of it: position h is the durable octets
; of EXT[h] when that is an extent, else the child's payload h.  Every
; obligation is a list lemma over that view (`fn-arx-view-extend',
; `-of-update-above', `-of-resize', `-of-append-beyond', `fn-arx-nth-view');
; no page arithmetic is re-proved: the paged arena's own correspondence is
; its certificate's.

(in-package "ACL2")
(include-book "payload-arena-paged")
(include-book "payload-arena-extent-logic")

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-arn-extent-guardp)
                          (:definition fn-arn-extentp)
                          (:definition fn-arn-lz-extentp)
                          (:definition fn-arn-lz-guardp)
                          (:rewrite fn-arn-payload-listp-true-listp)
                          (:rewrite fn-oct-nth-of-octet-listp-is-octet . 1))))

(defstobj fn-arena$x
  (fn-arena$x-inner :type fn-arena-paged)
  (fn-arena$x-ext :type (array t (0)) :initially 0 :resizable t)
  (fn-arena$x-stage :type (array fn-arena-page (0)) :resizable t)
  (fn-arena$x-files :type (array t (0)) :initially 0 :resizable t)
  :inline t)

; -----------------------------------------------------------------------------
; A stage page: the payload is the page's whole byte array.

(defun fn-arx-stage-octets (s)
  (declare (xargs :guard t :verify-guards nil))
  (fn-oct-list-from 0 (len (nth 0 s)) (nth 0 s)))

(defthm fn-arx-stage-octets-of-nil
  (equal (fn-arx-stage-octets nil) nil))

;; The copy of the buffer's cells [A+J, A+N) into the page's cells [J, N).
(defun fn-arx-page-copy (j n a fn-octets fn-arena-page)
  (declare (xargs :stobjs (fn-octets fn-arena-page)
                  :guard (and (natp j) (natp n) (natp a)
                              (<= n (fn-arena-page-bytes-length fn-arena-page))
                              (<= (+ a n) (fn-octets-len fn-octets)))
                  :measure (nfix (- (nfix n) (nfix j)))))
  (if (or (not (natp j)) (not (natp n)) (<= n j))
      fn-arena-page
    (let ((fn-arena-page (update-fn-arena-page-bytesi j (fn-octets-get (+ (nfix a) j) fn-octets)
                                                      fn-arena-page)))
      (fn-arx-page-copy (1+ j) n a fn-octets fn-arena-page))))

;; The page's cells [0, J) consed onto ACC, from the top down.
(defun fn-arx-page-down (j acc fn-arena-page)
  (declare (xargs :stobjs fn-arena-page
                  :guard (and (natp j) (<= j (fn-arena-page-bytes-length fn-arena-page))
                              (true-listp acc))))
  (if (zp j)
      acc
    (fn-arx-page-down (1- j) (cons (fn-arena-page-bytesi (1- j) fn-arena-page) acc)
                      fn-arena-page)))

(local
 (defthm fn-arx-list-from-snoc
   (implies (and (natp i) (natp n) (<= i n))
            (equal (fn-oct-list-from i (1+ n) buf)
                   (append (fn-oct-list-from i n buf) (list (nth n buf)))))
   :hints (("Goal" :use fn-oct-list-from-snoc))))

(local
 (defthm fn-arx-append-snoc
   (equal (append (append a (list x)) acc)
          (append a (cons x acc)))))

(defthm fn-arx-page-down-is-list-from
  (implies (natp j)
           (equal (fn-arx-page-down j acc fn-arena-page)
                  (append (fn-oct-list-from 0 j (car fn-arena-page)) acc)))
  :hints (("Goal" :induct (fn-arx-page-down j acc fn-arena-page)
           :in-theory (disable fn-arx-list-from-snoc fn-oct-list-from))
          ("Subgoal *1/2" :use ((:instance fn-arx-list-from-snoc
                                           (i 0) (n (1- j)) (buf (car fn-arena-page)))))))

(defthm fn-arx-page-copy-len
  (implies (<= (nfix n) (len (car fn-arena-page)))
           (equal (len (car (fn-arx-page-copy j n a fn-octets fn-arena-page)))
                  (len (car fn-arena-page))))
  :hints (("Goal" :induct (fn-arx-page-copy j n a fn-octets fn-arena-page))))

(defthm fn-arx-page-copy-below
  (implies (and (natp k) (< k (nfix j)))
           (equal (nth k (car (fn-arx-page-copy j n a fn-octets fn-arena-page)))
                  (nth k (car fn-arena-page))))
  :hints (("Goal" :induct (fn-arx-page-copy j n a fn-octets fn-arena-page))))

(defthm fn-arx-page-copy-other-fields
  (implies (not (equal (nfix k) 0))
           (equal (nth k (fn-arx-page-copy j n a fn-octets fn-arena-page))
                  (nth k fn-arena-page)))
  :hints (("Goal" :induct (fn-arx-page-copy j n a fn-octets fn-arena-page))))

(local
 (defthm fn-arx-list-from-of-page-copy-below
   (implies (and (natp j) (natp m) (<= m j))
            (equal (fn-oct-list-from i m (car (fn-arx-page-copy j n a fn-octets fn-arena-page)))
                   (fn-oct-list-from i m (car fn-arena-page))))
   :hints (("Goal" :induct (fn-arx-page-copy j n a fn-octets fn-arena-page)))))

(defthm fn-arx-page-copy-copies
  (implies (and (natp j) (natp n) (natp a) (<= n (len (car fn-arena-page))))
           (equal (fn-oct-list-from j n (car (fn-arx-page-copy j n a fn-octets fn-arena-page)))
                  (fn-oct-list-from (+ a j) (+ a n) fn-octets)))
  :hints (("Goal" :induct (fn-arx-page-copy j n a fn-octets fn-arena-page)
           :in-theory (enable fn-oct-get-is-nth))))

(local
 (defthm fn-arx-nthcdr-len-true-listp
   (implies (true-listp x) (equal (nthcdr (len x) x) nil))))

(local
 (defthm fn-arx-nthcdr-opens
   (implies (and (natp i) (< i (len x)))
            (equal (nthcdr i x) (cons (nth i x) (nthcdr (1+ i) x))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable nth nthcdr)))))

(local
 (defthm fn-arx-list-from-to-end
   (implies (and (natp i) (true-listp x) (<= i (len x)))
            (equal (fn-oct-list-from i (len x) x) (nthcdr i x)))
   :hints (("Goal" :induct (fn-oct-list-from i (len x) x)
            :in-theory (disable nthcdr))
           ("Subgoal *1/2" :use fn-arx-nthcdr-opens))))

(defthm fn-arx-list-from-whole
  (implies (true-listp x)
           (equal (fn-oct-list-from 0 (len x) x) x))
  :hints (("Goal" :use ((:instance fn-arx-list-from-to-end (i 0))))))

; -----------------------------------------------------------------------------
; The view.

(defun fn-arx-entry (e x s)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((fn-arn-extentp e) (fn-durable-octets (nth 0 e) (nth 3 e) (nth 4 e)))
        ((fn-arn-lz-extentp e)
         (fn-lzr-lz-value (nth 7 e) (fn-durable-octets (nth 0 e) (nth 3 e) (nth 4 e)) (nth 6 e)))
        ((eq e :staged) (fn-arx-stage-octets s))
        ((eq e :forgotten) nil)
        (t x)))

(defthm fn-arx-nth-of-payload-listp
  (implies (fn-arn-payload-listp a)
           (fn-cbor-octet-listp (nth h a)))
  :hints (("Goal" :in-theory (enable nth))))

(local
 (defthm fn-arx-nth-append-below
   (implies (and (natp k) (< k (len a)))
            (equal (nth k (append a b)) (nth k a)))
   :hints (("Goal" :in-theory (enable nth)))))

(defthm fn-arx-entry-of-extent
  (implies (fn-arn-extentp e)
           (equal (fn-arx-entry e x s)
                  (fn-durable-octets (nth 0 e) (nth 3 e) (nth 4 e)))))

(defthm fn-arx-entry-of-lz-extent
  (implies (fn-arn-lz-extentp e)
           (equal (fn-arx-entry e x s)
                  (fn-lzr-lz-value (nth 7 e) (fn-durable-octets (nth 0 e) (nth 3 e) (nth 4 e))
                                   (nth 6 e)))))

(defthm fn-arx-entry-of-staged
  (equal (fn-arx-entry :staged x s) (fn-arx-stage-octets s)))

(defthm fn-arx-entry-of-resident
  (implies (and (not (fn-arn-extentp e)) (not (fn-arn-lz-extentp e)) (not (equal e :staged))
                (not (equal e :forgotten)))
           (equal (fn-arx-entry e x s) x)))

;; A forgotten handle's payload is empty, whatever the child and the stage hold.
(defthm fn-arx-entry-of-forgotten
  (equal (fn-arx-entry :forgotten x s) nil))

;; The stage slot matters only through its payload.
(defthm fn-arx-entry-stage-congruence
  (implies (equal (fn-arx-stage-octets s1) (fn-arx-stage-octets s2))
           (equal (fn-arx-entry e x s1) (fn-arx-entry e x s2)))
  :rule-classes nil)

;; The stage slot matters only under a :staged entry.
(defthm fn-arx-entry-ignores-stage
  (implies (not (equal e :staged))
           (equal (fn-arx-entry e x s1) (fn-arx-entry e x nil)))
  :rule-classes nil)

(in-theory (disable fn-arx-entry fn-arx-stage-octets))

(defun fn-arx-view (h n ext a st)
  (declare (xargs :guard t :verify-guards nil :measure (nfix (- (nfix n) (nfix h)))))
  (if (or (not (natp h)) (not (natp n)) (<= n h))
      nil
    (cons (fn-arx-entry (nth h ext) (nth h a) (nth h st))
          (fn-arx-view (1+ h) n ext a st))))

(defthm fn-arx-len-view
  (equal (len (fn-arx-view h n ext a st))
         (if (and (natp h) (natp n) (< h n)) (- n h) 0)))

(defthm fn-arx-true-listp-view
  (true-listp (fn-arx-view h n ext a st)))

(local
 (defun fn-arx-ind-hk (h k n)
   (declare (xargs :measure (nfix (- (nfix n) (nfix h)))))
   (if (or (not (natp h)) (not (natp n)) (<= n h))
       (list h k)
     (fn-arx-ind-hk (1+ h) (1- k) n))))

(defthm fn-arx-nth-view
  (implies (and (natp h) (natp n) (natp k) (< (+ h k) n))
           (equal (nth k (fn-arx-view h n ext a st))
                  (fn-arx-entry (nth (+ h k) ext) (nth (+ h k) a) (nth (+ h k) st))))
  :hints (("Goal" :induct (fn-arx-ind-hk h k n))))

(defthm fn-arx-view-empty
  (implies (and (natp h) (natp n) (<= n h))
           (equal (fn-arx-view h n ext a st) nil)))

(defthm fn-arx-view-extend
  (implies (and (natp h) (natp n) (<= h n))
           (equal (fn-arx-view h (1+ n) ext a st)
                  (append (fn-arx-view h n ext a st)
                          (list (fn-arx-entry (nth n ext) (nth n a) (nth n st))))))
  :hints (("Goal" :induct (fn-arx-view h n ext a st))))

(defthm fn-arx-view-of-update-above
  (implies (and (natp k) (<= (nfix n) k))
           (equal (fn-arx-view h n (update-nth k v ext) a st)
                  (fn-arx-view h n ext a st))))

(defthm fn-arx-view-of-stage-update-above
  (implies (and (natp k) (<= (nfix n) k))
           (equal (fn-arx-view h n ext a (update-nth k v st))
                  (fn-arx-view h n ext a st))))

;; A stage slot whose entry is not :staged does not show.
(defthm fn-arx-view-of-stage-update-unstaged
  (implies (and (natp k) (not (equal (nth k ext) :staged)))
           (equal (fn-arx-view h n ext a (update-nth k v st))
                  (fn-arx-view h n ext a st)))
  :hints (("Goal" :induct (fn-arx-view h n ext a st))
          ("Subgoal *1/2" :use ((:instance fn-arx-entry-ignores-stage
                                           (e (nth h ext)) (x (nth h a))
                                           (s1 (nth h (update-nth k v st))))
                                (:instance fn-arx-entry-ignores-stage
                                           (e (nth h ext)) (x (nth h a))
                                           (s1 (nth h st)))))))

(defthm fn-arx-view-of-update-below
  (implies (and (natp k) (natp h) (< k h))
           (equal (fn-arx-view h n (update-nth k v ext) a st)
                  (fn-arx-view h n ext a st)))
  :hints (("Goal" :induct (fn-arx-view h n ext a st))))

;; Re-pointing entry K inside the view changes position K only.
(defthm fn-arx-view-of-update-inside
  (implies (and (natp h) (natp k) (natp n) (<= h k) (< k n))
           (equal (fn-arx-view h n (update-nth k v ext) a st)
                  (update-nth (- k h) (fn-arx-entry v (nth k a) (nth k st))
                              (fn-arx-view h n ext a st))))
  :hints (("Goal" :induct (fn-arx-view h n ext a st)
           :in-theory (enable update-nth))))

; Only the reseat's obligation uses it (it would split every seal's view).
(in-theory (disable fn-arx-view-of-update-inside))

;; A stage slot below the view does not show, and one inside it changes its
;; own position only (the forget's obligation: the slot of the handle it
;; empties).
(defthm fn-arx-view-of-stage-update-below
  (implies (and (natp k) (natp h) (< k h))
           (equal (fn-arx-view h n ext a (update-nth k s st))
                  (fn-arx-view h n ext a st)))
  :hints (("Goal" :induct (fn-arx-view h n ext a st))))

(defthm fn-arx-view-of-stage-update-inside
  (implies (and (natp h) (natp k) (natp n) (<= h k) (< k n))
           (equal (fn-arx-view h n ext a (update-nth k s st))
                  (update-nth (- k h) (fn-arx-entry (nth k ext) (nth k a) s)
                              (fn-arx-view h n ext a st))))
  :hints (("Goal" :induct (fn-arx-view h n ext a st)
           :in-theory (enable update-nth))))

(in-theory (disable fn-arx-view-of-stage-update-inside))

(local
 (defthm fn-arx-nth-resize-list
   (implies (and (natp k) (< k (len l)) (<= (len l) (nfix m)))
            (equal (nth k (resize-list l m d)) (nth k l)))
   :hints (("Goal" :in-theory (enable nth resize-list)))))

(defthm fn-arx-view-of-resize
  (implies (and (<= (nfix n) (len ext)) (<= (len ext) (nfix m)))
           (equal (fn-arx-view h n (resize-list ext m d) a st)
                  (fn-arx-view h n ext a st))))

(local
 (defun fn-arx-resize-ind (k l m)
   (if (or (zp m) (zp k))
       (list k l m)
     (fn-arx-resize-ind (1- k) (if (consp l) (cdr l) l) (1- m)))))

(local
 (defthm fn-arx-nth-resize-list-all
   (implies (natp k)
            (equal (nth k (resize-list l m d))
                   (if (< k (nfix m)) (if (< k (len l)) (nth k l) d) nil)))
   :hints (("Goal" :induct (fn-arx-resize-ind k l m)
            :expand ((resize-list l m d))
            :in-theory (enable nth resize-list)))))

(local
 (defthm fn-arx-nth-past-len
   (implies (and (natp k) (<= (len l) k))
            (equal (nth k l) nil))
   :hints (("Goal" :in-theory (enable nth)))))

;; The stage grows by fresh slots whose payload is empty, as an absent slot's.
(defthm fn-arx-stage-slot-of-resize
  (implies (and (natp k) (<= (len st) (nfix m)) (equal (fn-arx-stage-octets d) nil))
           (equal (fn-arx-stage-octets (nth k (resize-list st m d)))
                  (fn-arx-stage-octets (nth k st))))
  :hints (("Goal" :in-theory (disable resize-list) :cases ((< k (len st)) (< k (nfix m))))))

(defthm fn-arx-view-of-stage-resize
  (implies (and (<= (len st) (nfix m)) (equal (fn-arx-stage-octets d) nil))
           (equal (fn-arx-view h n ext a (resize-list st m d))
                  (fn-arx-view h n ext a st)))
  :hints (("Goal" :induct (fn-arx-view h n ext a st)
           :in-theory (disable resize-list))
          ("Subgoal *1/2" :use ((:instance fn-arx-entry-stage-congruence
                                           (e (nth h ext)) (x (nth h a))
                                           (s1 (nth h (resize-list st m d)))
                                           (s2 (nth h st)))
                                (:instance fn-arx-stage-slot-of-resize (k h))))))

(defthm fn-arx-view-of-append-beyond
  (implies (<= (nfix n) (len a))
           (equal (fn-arx-view h n ext (append a b) st)
                  (fn-arx-view h n ext a st))))

; -----------------------------------------------------------------------------
; The exec functions.

(defun fn-arena$x-count (fn-arena$x)
  (declare (xargs :stobjs fn-arena$x))
  (stobj-let ((fn-arena-paged (fn-arena$x-inner fn-arena$x)))
             (n)
             (fn-arena-paged-count fn-arena-paged)
             n))

(defun fn-arena$x-wfp (fn-arena$x)
  (declare (xargs :stobjs fn-arena$x))
  (<= (fn-arena$x-count fn-arena$x) (fn-arena$x-ext-length fn-arena$x)))

;; A stage slot's reads: its length, one octet, the payload.  A slot past the
;; stage's length reads as the empty payload (its entry is never :staged).
(defun fn-arx-stage-len (h fn-arena$x)
  (declare (xargs :stobjs fn-arena$x :guard (natp h)))
  (if (< h (fn-arena$x-stage-length fn-arena$x))
      (stobj-let ((fn-arena-page (fn-arena$x-stagei h fn-arena$x)))
                 (n)
                 (fn-arena-page-bytes-length fn-arena-page)
                 n)
    0))

(defun fn-arx-stage-get (h i fn-arena$x)
  (declare (xargs :stobjs fn-arena$x :guard (and (natp h) (natp i))))
  (if (< h (fn-arena$x-stage-length fn-arena$x))
      (stobj-let ((fn-arena-page (fn-arena$x-stagei h fn-arena$x)))
                 (v)
                 (if (< i (fn-arena-page-bytes-length fn-arena-page))
                     (fn-arena-page-bytesi i fn-arena-page)
                   0)
                 v)
    0))

(defun fn-arx-stage-payload (h fn-arena$x)
  (declare (xargs :stobjs fn-arena$x :guard (natp h)))
  (if (< h (fn-arena$x-stage-length fn-arena$x))
      (stobj-let ((fn-arena-page (fn-arena$x-stagei h fn-arena$x)))
                 (v)
                 (fn-arx-page-down (fn-arena-page-bytes-length fn-arena-page) nil fn-arena-page)
                 v)
    nil))

(defun fn-arena$x-payload-len (h fn-arena$x)
  (declare (xargs :stobjs fn-arena$x
                  :guard (and (natp h) (< h (fn-arena$x-count fn-arena$x))
                              (fn-arena$x-wfp fn-arena$x))))
  (let ((e (fn-arena$x-exti h fn-arena$x)))
    (cond ((fn-arn-extentp e) (nth 4 e))
          ((fn-arn-lz-extentp e) (nth 6 e))
          ((eq e :staged) (fn-arx-stage-len h fn-arena$x))
          ((eq e :forgotten) 0)
          (t (stobj-let ((fn-arena-paged (fn-arena$x-inner fn-arena$x)))
                        (n)
                        (fn-arena-paged-payload-len h fn-arena-paged)
                        n)))))

(defun fn-arena$x-get (h i fn-arena$x)
  (declare (xargs :stobjs fn-arena$x
                  :guard (and (natp h) (< h (fn-arena$x-count fn-arena$x))
                              (fn-arena$x-wfp fn-arena$x)
                              (natp i) (< i (fn-arena$x-payload-len h fn-arena$x)))))
  (let ((e (fn-arena$x-exti h fn-arena$x)))
    (cond ((fn-arn-extentp e)
           (fn-durable-realize-octet (nth 0 e) (nth 1 e) (nth 2 e) (nth 3 e) (nth 4 e) (nth 5 e) i))
          ((fn-arn-lz-extentp e)
           (fn-oct-nth i (fn-durable-realize-lz (nth 0 e) (nth 1 e) (nth 2 e) (nth 3 e) (nth 4 e)
                                                (nth 5 e) (nth 6 e) (nth 7 e))))
          ((eq e :staged) (fn-arx-stage-get h i fn-arena$x))
          ((eq e :forgotten) 0)
          (t (stobj-let ((fn-arena-paged (fn-arena$x-inner fn-arena$x)))
                        (v)
                        (fn-arena-paged-get h i fn-arena-paged)
                        v)))))

(defun fn-arena$x-payload (h fn-arena$x)
  (declare (xargs :stobjs fn-arena$x
                  :guard (and (natp h) (< h (fn-arena$x-count fn-arena$x))
                              (fn-arena$x-wfp fn-arena$x))))
  (let ((e (fn-arena$x-exti h fn-arena$x)))
    (cond ((fn-arn-extentp e)
           (fn-durable-realize-octets (nth 0 e) (nth 1 e) (nth 2 e) (nth 3 e) (nth 4 e) (nth 5 e)))
          ((fn-arn-lz-extentp e)
           (fn-durable-realize-lz (nth 0 e) (nth 1 e) (nth 2 e) (nth 3 e) (nth 4 e) (nth 5 e)
                                  (nth 6 e) (nth 7 e)))
          ((eq e :staged) (fn-arx-stage-payload h fn-arena$x))
          ((eq e :forgotten) nil)
          (t (stobj-let ((fn-arena-paged (fn-arena$x-inner fn-arena$x)))
                        (v)
                        (fn-arena-paged-payload h fn-arena-paged)
                        v)))))

; The FILE COUNT (lane composed-owner-4, row A6).  FILES holds, per durable
; file id F, how many EXT entries name F: kept by the mark (the entry it
; replaces loses one, the entry it writes gains one) and emptied by the
; clear, never recomputed.  The relation `fn-arena$xcorr' carries its
; agreement with EXT (`fn-arx-files-agree'), so every export preserves it,
; and a count of 0 means no handle names the file
; (`fn-arx-file-count-zero-names-none').
(defun fn-arx-entry-file (e)
  (declare (xargs :guard t))
  (if (or (fn-arn-extentp e) (fn-arn-lz-extentp e)) (nth 0 e) nil))

(defthm fn-arx-entry-file-type
  (or (null (fn-arx-entry-file e)) (natp (fn-arx-entry-file e)))
  :rule-classes :type-prescription)

(defthm fn-arx-entry-file-of-non-cons
  (implies (not (consp e)) (equal (fn-arx-entry-file e) nil)))

(in-theory (disable fn-arx-entry-file))

(defun fn-arx-tally (f ext)
  (declare (xargs :guard (true-listp ext)))
  (if (atom ext)
      0
    (+ (if (equal (fn-arx-entry-file (car ext)) f) 1 0)
       (fn-arx-tally f (cdr ext)))))

(defun fn-arx-files-get (f files)
  (declare (xargs :guard (and (natp f) (true-listp files))))
  (nfix (nth f files)))

(defthm fn-arx-files-get-of-nil
  (equal (fn-arx-files-get f nil) 0))

(in-theory (disable fn-arx-files-get))

(defun-sk fn-arx-files-agree (ext files)
  (forall f (implies (natp f)
                     (equal (fn-arx-files-get f files) (fn-arx-tally f ext)))))

(in-theory (disable fn-arx-files-agree))

(defun fn-arx-files-inc (f fn-arena$x)
  (declare (xargs :stobjs fn-arena$x :guard (natp f)))
  (let ((fn-arena$x (if (< f (fn-arena$x-files-length fn-arena$x))
                        fn-arena$x
                      (resize-fn-arena$x-files (max 64 (* 2 f)) fn-arena$x))))
    (update-fn-arena$x-filesi f (1+ (nfix (fn-arena$x-filesi f fn-arena$x))) fn-arena$x)))

(defun fn-arx-files-dec (f fn-arena$x)
  (declare (xargs :stobjs fn-arena$x :guard (natp f)))
  (if (< f (fn-arena$x-files-length fn-arena$x))
      (update-fn-arena$x-filesi f (nfix (1- (nfix (fn-arena$x-filesi f fn-arena$x)))) fn-arena$x)
    fn-arena$x))

(local
 (defthm fn-arx-car-update-nth
   (implies (not (zp k))
            (equal (car (update-nth k v x)) (car x)))
   :hints (("Goal" :in-theory (enable update-nth)))))

;; The count column's move, as a list.
(defun fn-arx-move-list (old new fs)
  (declare (xargs :guard (true-listp fs)))
  (let ((fs (if (and (natp old) (< old (len fs)))
                (update-nth old (nfix (1- (nfix (nth old fs)))) fs)
              fs)))
    (if (natp new)
        (update-nth new (1+ (nfix (nth new fs)))
                    (if (< new (len fs)) fs (resize-list fs (max 64 (* 2 new)) 0)))
      fs)))

; An entry naming OLD replaced by one naming NEW (either nil: no file).
(defun fn-arx-files-move (old new fn-arena$x)
  (declare (xargs :stobjs fn-arena$x))
  (let ((fn-arena$x (if (natp old) (fn-arx-files-dec old fn-arena$x) fn-arena$x)))
    (if (natp new) (fn-arx-files-inc new fn-arena$x) fn-arena$x)))

(defthm fn-arx-files-move-other-fields
  (implies (not (equal i *fn-arena$x-filesi*))
           (equal (nth i (fn-arx-files-move old new fn-arena$x))
                  (nth i fn-arena$x))))

(defthm fn-arx-files-move-inner
  (equal (car (fn-arx-files-move old new fn-arena$x))
         (car fn-arena$x)))

(defthm fn-arx-files-move-len
  (implies (fn-arena$xp fn-arena$x)
           (equal (len (fn-arx-files-move old new fn-arena$x)) (len fn-arena$x))))

(defthm fn-arx-files-move-true-listp
  (implies (true-listp fn-arena$x)
           (true-listp (fn-arx-files-move old new fn-arena$x))))

(defthm fn-arx-files-move-files
  (equal (nth *fn-arena$x-filesi* (fn-arx-files-move old new fn-arena$x))
         (fn-arx-move-list old new (nth *fn-arena$x-filesi* fn-arena$x))))

(defthm fn-arx-filesp-is-true-listp
  (equal (fn-arena$x-filesp x) (true-listp x))
  :hints (("Goal" :in-theory (enable fn-arena$x-filesp))))

(local
 (defthm fn-arx-files-true-listp-resize-list
   (implies (true-listp l) (true-listp (resize-list l m d)))
   :hints (("Goal" :in-theory (enable resize-list)))))

(defthm fn-arx-files-move-recognizer
  (implies (fn-arena$xp fn-arena$x)
           (fn-arena$xp (fn-arx-files-move old new fn-arena$x)))
  :hints (("Goal" :in-theory (enable fn-arena$xp))))

(in-theory (disable fn-arx-files-move))

; Handle H's entry E, the array grown (doubled) when H is past it; the file
; count follows the entry.
(defun fn-arx-mark (h e fn-arena$x)
  (declare (xargs :stobjs fn-arena$x :guard (natp h)))
  (let* ((fn-arena$x (if (< h (fn-arena$x-ext-length fn-arena$x))
                         fn-arena$x
                       (resize-fn-arena$x-ext (max 64 (* 2 h)) fn-arena$x)))
         (fn-arena$x (fn-arx-files-move (fn-arx-entry-file (fn-arena$x-exti h fn-arena$x))
                                        (fn-arx-entry-file e)
                                        fn-arena$x)))
    (update-fn-arena$x-exti h e fn-arena$x)))

; The stage covers slot H (grown, doubled, when H is past it: new slots are
; empty pages, no octets).
(defun fn-arx-stage-grow (h fn-arena$x)
  (declare (xargs :stobjs fn-arena$x :guard (natp h)))
  (if (< h (fn-arena$x-stage-length fn-arena$x))
      fn-arena$x
    (resize-fn-arena$x-stage (max 64 (* 2 h)) fn-arena$x)))

; Slot H holds a copy of the buffer: its page sized to the buffer, then
; filled from it.
(defun fn-arx-stage-write (h fn-octets fn-arena$x)
  (declare (xargs :stobjs (fn-octets fn-arena$x)
                  :guard (and (natp h) (< h (fn-arena$x-stage-length fn-arena$x)))))
  (stobj-let ((fn-arena-page (fn-arena$x-stagei h fn-arena$x)))
             (fn-arena-page)
             (let ((fn-arena-page (resize-fn-arena-page-bytes (fn-octets-len fn-octets)
                                                              fn-arena-page)))
               (fn-arx-page-copy 0 (fn-octets-len fn-octets) 0 fn-octets fn-arena-page))
             fn-arena$x))

(defun fn-arena$x-seal-list (xs fn-arena$x)
  (declare (xargs :stobjs fn-arena$x
                  :guard (and (fn-cbor-octet-listp xs) (fn-arena$x-wfp fn-arena$x))))
  (let* ((h (fn-arena$x-count fn-arena$x))
         (fn-arena$x (stobj-let ((fn-arena-paged (fn-arena$x-inner fn-arena$x)))
                                (fn-arena-paged)
                                (fn-arena-paged-seal-list xs fn-arena-paged)
                                fn-arena$x)))
    (fn-arx-mark h 0 fn-arena$x)))

; The buffer seal STAGES: the child seals the empty payload (keeping the
; handle numbering), the handle is marked :staged and its stage slot holds
; the copy.  The owner's POST prepare seals through here
; (host/native/io.lisp fnn-seal-live-buffer); the commit reseats it
; (fn-arena$x-reseat-extent) once the log made it durable.
(defun fn-arena$x-seal-buffer (fn-octets fn-arena$x)
  (declare (xargs :stobjs (fn-octets fn-arena$x)
                  :guard (fn-arena$x-wfp fn-arena$x)))
  (let* ((h (fn-arena$x-count fn-arena$x))
         (fn-arena$x (stobj-let ((fn-arena-paged (fn-arena$x-inner fn-arena$x)))
                                (fn-arena-paged)
                                (fn-arena-paged-seal-list nil fn-arena-paged)
                                fn-arena$x))
         (fn-arena$x (fn-arx-mark h :staged fn-arena$x))
         (fn-arena$x (fn-arx-stage-grow h fn-arena$x)))
    (fn-arx-stage-write h fn-octets fn-arena$x)))

(defun fn-arena$x-seal-range (a b fn-octets fn-arena$x)
  (declare (xargs :stobjs (fn-octets fn-arena$x)
                  :guard (and (natp a) (natp b) (<= a b) (<= b (fn-octets-len fn-octets))
                              (fn-arena$x-wfp fn-arena$x))))
  (let* ((h (fn-arena$x-count fn-arena$x))
         (fn-arena$x (stobj-let ((fn-arena-paged (fn-arena$x-inner fn-arena$x)))
                                (fn-arena-paged)
                                (fn-arena-paged-seal-range a b fn-octets fn-arena-paged)
                                fn-arena$x)))
    (fn-arx-mark h 0 fn-arena$x)))

(defun fn-arena$x-clear (fn-arena$x)
  (declare (xargs :stobjs fn-arena$x))
  (let* ((fn-arena$x (stobj-let ((fn-arena-paged (fn-arena$x-inner fn-arena$x)))
                                (fn-arena-paged)
                                (fn-arena-paged-clear fn-arena-paged)
                                fn-arena$x))
         (fn-arena$x (resize-fn-arena$x-stage 0 fn-arena$x))
         (fn-arena$x (resize-fn-arena$x-files 0 fn-arena$x)))
    (resize-fn-arena$x-ext 0 fn-arena$x)))

; The extent seal: the empty payload into the child, the extent into EXT.
(defun fn-arena$x-seal-extent (file eoff elen poff plen trailer fn-arena$x)
  (declare (xargs :stobjs fn-arena$x
                  :guard (and (fn-arn-extent-guardp file eoff elen poff plen trailer)
                              (fn-arena$x-wfp fn-arena$x))))
  (let* ((h (fn-arena$x-count fn-arena$x))
         (fn-arena$x (stobj-let ((fn-arena-paged (fn-arena$x-inner fn-arena$x)))
                                (fn-arena-paged)
                                (fn-arena-paged-seal-list nil fn-arena-paged)
                                fn-arena$x)))
    (fn-arx-mark h (list file eoff elen poff plen trailer) fn-arena$x)))

; The reseat: handle H's entry becomes the extent (its stage slot, if any,
; stays until the release: a reader that saw :staged still finds its copy).
(defun fn-arena$x-reseat-extent (h file eoff elen poff plen trailer fn-arena$x)
  (declare (xargs :stobjs fn-arena$x
                  :guard (and (natp h) (< h (fn-arena$x-count fn-arena$x))
                              (fn-arena$x-wfp fn-arena$x)
                              (fn-arn-extent-guardp file eoff elen poff plen trailer))))
  (fn-arx-mark h (list file eoff elen poff plen trailer) fn-arena$x))

; The compressed seal and reseat (lane compression-extents, PRF-326): as the
; extent's, with the compressed extent in EXT.
(defun fn-arena$x-seal-lz-extent (file eoff elen poff plen trailer n dict fn-arena$x)
  (declare (xargs :stobjs fn-arena$x
                  :guard (and (fn-arn-lz-guardp file eoff elen poff plen trailer n dict)
                              (fn-arena$x-wfp fn-arena$x))))
  (let* ((h (fn-arena$x-count fn-arena$x))
         (fn-arena$x (stobj-let ((fn-arena-paged (fn-arena$x-inner fn-arena$x)))
                                (fn-arena-paged)
                                (fn-arena-paged-seal-list nil fn-arena-paged)
                                fn-arena$x)))
    (fn-arx-mark h (list file eoff elen poff plen trailer n dict) fn-arena$x)))

(defun fn-arena$x-reseat-lz-extent (h file eoff elen poff plen trailer n dict fn-arena$x)
  (declare (xargs :stobjs fn-arena$x
                  :guard (and (natp h) (< h (fn-arena$x-count fn-arena$x))
                              (fn-arena$x-wfp fn-arena$x)
                              (fn-arn-lz-guardp file eoff elen poff plen trailer n dict))))
  (fn-arx-mark h (list file eoff elen poff plen trailer n dict) fn-arena$x))

; The release: the stage slot of an EXTENT handle is emptied (no other
; handle's slot is touched, and a staged handle keeps its copy).
(defun fn-arena$x-release (h fn-arena$x)
  (declare (xargs :stobjs fn-arena$x :guard (natp h)))
  (if (and (< h (fn-arena$x-ext-length fn-arena$x))
           (< h (fn-arena$x-stage-length fn-arena$x))
           (or (fn-arn-extentp (fn-arena$x-exti h fn-arena$x))
               (fn-arn-lz-extentp (fn-arena$x-exti h fn-arena$x))))
      (stobj-let ((fn-arena-page (fn-arena$x-stagei h fn-arena$x)))
                 (fn-arena-page)
                 (resize-fn-arena-page-bytes 0 fn-arena-page)
                 fn-arena$x)
    fn-arena$x))

; The forget (lane arena-forget, 2026-10-03): handle H's entry becomes
; :forgotten -- whatever it was: an extent (its file's count falls by one,
; fn-arx-mark), a staged copy or a resident payload -- and its stage slot is
; emptied.  No read of H reaches a realizer or the child again: its payload
; is the empty one.  A handle outside the arena is left alone.  One entry
; write, one count move, one page resize: no walk.
(defun fn-arena$x-forget (h fn-arena$x)
  (declare (xargs :stobjs fn-arena$x
                  :guard (and (natp h) (fn-arena$x-wfp fn-arena$x))))
  (if (< h (fn-arena$x-count fn-arena$x))
      (let ((fn-arena$x (fn-arx-mark h :forgotten fn-arena$x)))
        (if (< h (fn-arena$x-stage-length fn-arena$x))
            (stobj-let ((fn-arena-page (fn-arena$x-stagei h fn-arena$x)))
                       (fn-arena-page)
                       (resize-fn-arena-page-bytes 0 fn-arena-page)
                       fn-arena$x)
          fn-arena$x))
    fn-arena$x))

; -----------------------------------------------------------------------------
; The abstraction relation.

(defun fn-arena$xcorr (fn-arena$x fn-arena$a)
  (declare (xargs :verify-guards nil))
  (and (fn-arena$xp fn-arena$x)
       (fn-arx-files-agree (nth *fn-arena$x-exti* fn-arena$x)
                           (nth *fn-arena$x-filesi* fn-arena$x))
       (fn-arn-payload-listp fn-arena$a)
       (<= (len (nth *fn-arena$x-inner* fn-arena$x)) (len (nth *fn-arena$x-exti* fn-arena$x)))
       (equal (fn-arx-view 0 (len (nth *fn-arena$x-inner* fn-arena$x))
                           (nth *fn-arena$x-exti* fn-arena$x)
                           (nth *fn-arena$x-inner* fn-arena$x)
                           (nth *fn-arena$x-stagei* fn-arena$x))
              fn-arena$a)))

;; The mark: the child untouched, EXT updated at H (grown when H is past it).
(local
 (defthm fn-arx-extp-is-true-listp
   (equal (fn-arena$x-extp x) (true-listp x))
   :hints (("Goal" :in-theory (enable fn-arena$x-extp)))))

(local
 (defthm fn-arx-true-listp-resize-list
   (implies (true-listp l) (true-listp (resize-list l m d)))
   :hints (("Goal" :in-theory (enable resize-list)))))

(defthm fn-arx-mark-inner
  (implies (natp h)
           (equal (nth *fn-arena$x-inner* (fn-arx-mark h e fn-arena$x))
                  (nth *fn-arena$x-inner* fn-arena$x)))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-arx-mark-ext
  (implies (natp h)
           (equal (nth *fn-arena$x-exti* (fn-arx-mark h e fn-arena$x))
                  (update-nth h e (if (< h (len (nth *fn-arena$x-exti* fn-arena$x)))
                                      (nth *fn-arena$x-exti* fn-arena$x)
                                    (resize-list (nth *fn-arena$x-exti* fn-arena$x)
                                                 (max 64 (* 2 h)) 0)))))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-arx-mark-recognizer
  (implies (and (fn-arena$xp fn-arena$x) (natp h))
           (fn-arena$xp (fn-arx-mark h e fn-arena$x)))
  :hints (("Goal" :do-not-induct t)))

(local
 (defthm fn-arx-nth-len-append
   (implies (equal n (len a))
            (equal (nth n (append a (list x))) x))
   :hints (("Goal" :in-theory (enable nth)))))

(defthm fn-arx-mark-stage
  (implies (natp h)
           (equal (nth *fn-arena$x-stagei* (fn-arx-mark h e fn-arena$x))
                  (nth *fn-arena$x-stagei* fn-arena$x)))
  :hints (("Goal" :do-not-induct t)))

;; The file count's agreement, kept by the mark.
(defthm fn-arx-tally-of-update-nth
  (implies (and (natp h) (< h (len ext)))
           (equal (fn-arx-tally f (update-nth h e ext))
                  (+ (- (fn-arx-tally f ext)
                        (if (equal (fn-arx-entry-file (nth h ext)) f) 1 0))
                     (if (equal (fn-arx-entry-file e) f) 1 0))))
  :hints (("Goal" :in-theory (enable update-nth nth))))

(defthm fn-arx-tally-of-resize-list-zero
  (implies (and (natp f) (<= (len l) (nfix n)))
           (equal (fn-arx-tally f (resize-list l n 0))
                  (fn-arx-tally f l)))
  :hints (("Goal" :in-theory (enable resize-list))))

(defthm fn-arx-tally-of-empty
  (implies (equal (len ext) 0) (equal (fn-arx-tally f ext) 0)))

(defthm fn-arx-tally-positive-when-named
  (implies (and (natp h) (< h (len ext))
                (equal (fn-arx-entry-file (nth h ext)) f))
           (< 0 (fn-arx-tally f ext)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable nth))))

(defthm fn-arx-files-agree-of-nil
  (fn-arx-files-agree nil nil)
  :hints (("Goal" :in-theory (enable fn-arx-files-agree fn-arx-files-get))))

(local
 (defun fn-arx-zerosp (l)
   (if (atom l) t (and (equal (car l) 0) (fn-arx-zerosp (cdr l))))))

(local
 (defthm fn-arx-nth-of-zeros
   (implies (and (fn-arx-zerosp l) (natp f))
            (equal (nth f l) (if (< f (len l)) 0 nil)))
   :hints (("Goal" :in-theory (enable nth)))))

;; The mark's count column (the entry array grown first when H is past it).
(defthm fn-arx-mark-files
  (implies (natp h)
           (equal (nth *fn-arena$x-filesi* (fn-arx-mark h e fn-arena$x))
                  (fn-arx-move-list
                   (fn-arx-entry-file
                    (nth h (if (< h (len (nth *fn-arena$x-exti* fn-arena$x)))
                               (nth *fn-arena$x-exti* fn-arena$x)
                             (resize-list (nth *fn-arena$x-exti* fn-arena$x)
                                          (max 64 (* 2 h)) 0))))
                   (fn-arx-entry-file e)
                   (nth *fn-arena$x-filesi* fn-arena$x))))
  :hints (("Goal" :do-not-induct t)))

(defthm fn-arx-files-get-of-move-list
  (implies (and (natp f) (true-listp fs))
           (equal (fn-arx-files-get f (fn-arx-move-list old new fs))
                  (+ (- (fn-arx-files-get f fs)
                        (if (and (equal old f) (< 0 (fn-arx-files-get f fs))) 1 0))
                     (if (equal new f) 1 0))))
  :hints (("Goal" :in-theory (enable fn-arx-files-get))))

(defthm fn-arx-files-agree-of-resize
  (implies (and (fn-arx-files-agree ext fs) (<= (len ext) (nfix n)))
           (fn-arx-files-agree (resize-list ext n 0) fs))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-arx-files-agree) (fn-arx-files-agree-necc))
           :use ((:instance fn-arx-files-agree-necc (ext ext) (files fs)
                            (f (fn-arx-files-agree-witness (resize-list ext n 0) fs)))))))

(defthm fn-arx-xp-files-field
  (implies (fn-arena$xp fn-arena$x)
           (true-listp (nth *fn-arena$x-filesi* fn-arena$x)))
  :hints (("Goal" :in-theory (enable fn-arena$xp))))

(defthm fn-arx-files-agree-of-move
  (implies (and (fn-arx-files-agree ext fs) (true-listp fs)
                (natp h) (< h (len ext))
                (equal g (fn-arx-entry-file e)))
           (fn-arx-files-agree (update-nth h e ext)
                               (fn-arx-move-list (fn-arx-entry-file (nth h ext)) g fs)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-arx-files-agree) (fn-arx-move-list fn-arx-files-agree-necc))
           :use ((:instance fn-arx-files-agree-necc (ext ext) (files fs)
                            (f (fn-arx-entry-file (nth h ext))))
                 (:instance fn-arx-files-agree-necc (ext ext) (files fs)
                            (f (fn-arx-files-agree-witness
                                (update-nth h e ext)
                                (fn-arx-move-list (fn-arx-entry-file (nth h ext))
                                                  (fn-arx-entry-file e) fs))))))))

(defthm fn-arx-files-agree-of-move-fresh
  (implies (and (fn-arx-files-agree ext fs) (true-listp fs)
                (natp h) (<= (len ext) h) (< h (nfix n))
                (equal g (fn-arx-entry-file e)))
           (fn-arx-files-agree (update-nth h e (resize-list ext n 0))
                               (fn-arx-move-list nil g fs)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-arx-files-agree-of-move fn-arx-move-list)
           :use ((:instance fn-arx-files-agree-of-move (ext (resize-list ext n 0)))))))

(in-theory (disable fn-arx-move-list))

(defthm fn-arx-files-agree-of-mark
  (implies (and (fn-arena$xp fn-arena$x) (natp h)
                (fn-arx-files-agree (nth *fn-arena$x-exti* fn-arena$x)
                                    (nth *fn-arena$x-filesi* fn-arena$x)))
           (fn-arx-files-agree (nth *fn-arena$x-exti* (fn-arx-mark h e fn-arena$x))
                               (nth *fn-arena$x-filesi* (fn-arx-mark h e fn-arena$x))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-arena$xp) (fn-arx-mark)))))

; The mark is known by its fields from here on.
(in-theory (disable fn-arx-mark))

(defthm fn-arx-view-after-mark
  (implies (and (natp n) (equal n (len a0)) (<= n (len ext)))
           (equal (fn-arx-view 0 (1+ n)
                               (update-nth n e (if (< n (len ext))
                                                   ext
                                                 (resize-list ext (max 64 (* 2 n)) 0)))
                               (append a0 (list x))
                               st)
                  (append (fn-arx-view 0 n ext a0 st) (list (fn-arx-entry e x (nth n st))))))
  :hints (("Goal" :do-not-induct t :in-theory (disable fn-arx-view))))


;; The stage's growth: the other fields untouched, the view unchanged (new
;; slots are empty pages), slot H covered.
(defthm fn-arx-stage-octets-of-fresh-page
  (equal (fn-arx-stage-octets (create-fn-arena-page)) nil)
  :hints (("Goal" :in-theory (enable fn-arx-stage-octets))))

(defthm fn-arx-stage-grow-fields
  (and (equal (nth *fn-arena$x-inner* (fn-arx-stage-grow h fn-arena$x))
              (nth *fn-arena$x-inner* fn-arena$x))
       (equal (nth *fn-arena$x-exti* (fn-arx-stage-grow h fn-arena$x))
              (nth *fn-arena$x-exti* fn-arena$x))
       (equal (nth *fn-arena$x-filesi* (fn-arx-stage-grow h fn-arena$x))
              (nth *fn-arena$x-filesi* fn-arena$x)))
  :hints (("Goal" :in-theory (disable resize-list))))

(defthm fn-arx-view-of-stage-grow
  (implies (natp h)
           (equal (fn-arx-view i n ext a (nth *fn-arena$x-stagei* (fn-arx-stage-grow h fn-arena$x)))
                  (fn-arx-view i n ext a (nth *fn-arena$x-stagei* fn-arena$x))))
  :hints (("Goal" :in-theory (disable resize-list))))

(defthm fn-arx-stage-grow-covers
  (implies (natp h)
           (< h (len (nth *fn-arena$x-stagei* (fn-arx-stage-grow h fn-arena$x)))))
  :rule-classes (:rewrite :linear))

(local
 (defthm fn-arx-stagep-of-resize-list
   (implies (and (fn-arena$x-stagep l) (fn-arena-pagep d))
            (fn-arena$x-stagep (resize-list l m d)))
   :hints (("Goal" :in-theory (enable resize-list)))))

(local
 (defthm fn-arx-stagep-of-update-nth
   (implies (and (fn-arena$x-stagep l) (fn-arena-pagep v) (natp k) (< k (len l)))
            (fn-arena$x-stagep (update-nth k v l)))
   :hints (("Goal" :in-theory (enable update-nth)))))

(local
 (defthm fn-arx-pagep-of-nth-stage
   (implies (and (fn-arena$x-stagep l) (natp k) (< k (len l)))
            (fn-arena-pagep (nth k l)))
   :hints (("Goal" :in-theory (enable nth)))))

(defthm fn-arx-stage-grow-xp
  (implies (and (fn-arena$xp fn-arena$x) (natp h))
           (fn-arena$xp (fn-arx-stage-grow h fn-arena$x)))
  :hints (("Goal" :in-theory (disable resize-list))))

;; The stage write: the other fields untouched, slots other than H untouched,
;; slot H's payload the buffer's octets.
(local
 (defthm fn-arx-page-bytesp-of-copy
   (implies (and (fn-arena-page-bytesp (car fn-arena-page))
                 (fn-octets-p fn-octets)
                 (natp a) (<= (+ a (nfix n)) (len fn-octets))
                 (<= (nfix n) (len (car fn-arena-page))))
            (fn-arena-page-bytesp (car (fn-arx-page-copy j n a fn-octets fn-arena-page))))
   :hints (("Goal" :induct (fn-arx-page-copy j n a fn-octets fn-arena-page)
            :in-theory (enable update-nth fn-oct-get-is-nth)))))

(local
 (defthm fn-arx-bytesp-of-resize
   (implies (fn-arena-page-bytesp l)
            (fn-arena-page-bytesp (resize-list l m 0)))
   :hints (("Goal" :in-theory (enable resize-list)))))

(local
 (defthm fn-arx-pagep-of-copy
   (implies (and (fn-arena-pagep p) (fn-octets-p fn-octets)
                 (natp a) (<= (+ a (nfix n)) (len fn-octets))
                 (<= (nfix n) (len (car p))))
            (fn-arena-pagep (fn-arx-page-copy j n a fn-octets p)))
   :hints (("Goal" :induct (fn-arx-page-copy j n a fn-octets p)
            :in-theory (enable update-nth fn-oct-get-is-nth)))))

(local
 (defthm fn-arx-pagep-of-resized
   (implies (fn-arena-pagep p)
            (fn-arena-pagep (cons (resize-list (car p) m 0) (cdr p))))
   :hints (("Goal" :in-theory (disable resize-list)))))

(defthm fn-arx-stage-write-fields
  (and (equal (nth *fn-arena$x-inner* (fn-arx-stage-write h fn-octets fn-arena$x))
              (nth *fn-arena$x-inner* fn-arena$x))
       (equal (nth *fn-arena$x-exti* (fn-arx-stage-write h fn-octets fn-arena$x))
              (nth *fn-arena$x-exti* fn-arena$x))
       (equal (nth *fn-arena$x-filesi* (fn-arx-stage-write h fn-octets fn-arena$x))
              (nth *fn-arena$x-filesi* fn-arena$x)))
  :hints (("Goal" :in-theory (disable resize-list fn-arx-page-copy))))

(defthm fn-arx-view-of-stage-write-above
  (implies (and (natp h) (<= (nfix n) h))
           (equal (fn-arx-view i n ext a (nth *fn-arena$x-stagei* (fn-arx-stage-write h fn-octets fn-arena$x)))
                  (fn-arx-view i n ext a (nth *fn-arena$x-stagei* fn-arena$x)))))

(defthm fn-arx-stage-write-slot
  (implies (and (natp h) (< h (len (nth *fn-arena$x-stagei* fn-arena$x)))
                (fn-octets-p fn-octets))
           (equal (fn-arx-stage-octets
                   (nth h (nth *fn-arena$x-stagei* (fn-arx-stage-write h fn-octets fn-arena$x))))
                  fn-octets))
  :hints (("Goal" :in-theory (enable fn-arx-stage-octets fn-oct-len-is-len))))

(defthm fn-arx-stage-write-xp
  (implies (and (fn-arena$xp fn-arena$x) (natp h) (< h (len (nth *fn-arena$x-stagei* fn-arena$x)))
                (fn-octets-p fn-octets))
           (fn-arena$xp (fn-arx-stage-write h fn-octets fn-arena$x)))
  :hints (("Goal" :in-theory (enable fn-oct-len-is-len))))

(local
 (defthm fn-arx-nth-0-is-car
   (equal (nth 0 x) (car x))))

(defthm fn-arx-len-stage-octets
  (equal (len (fn-arx-stage-octets s)) (len (car s)))
  :hints (("Goal" :in-theory (enable fn-arx-stage-octets))))

(defthm fn-arx-nth-stage-octets
  (implies (and (natp i) (< i (len (car s))))
           (equal (nth i (fn-arx-stage-octets s)) (nth i (car s))))
  :hints (("Goal" :in-theory (enable fn-arx-stage-octets))))

;; The stage slot reads.
(defthm fn-arx-stage-len-is
  (implies (natp h)
           (equal (fn-arx-stage-len h fn-arena$x)
                  (len (fn-arx-stage-octets (nth h (nth *fn-arena$x-stagei* fn-arena$x))))))
  :hints (("Goal" :in-theory (e/d (fn-arx-stage-octets) (nth)))))

(defthm fn-arx-stage-get-is
  (implies (and (natp h) (natp i)
                (< i (len (fn-arx-stage-octets (nth h (nth *fn-arena$x-stagei* fn-arena$x))))))
           (equal (fn-arx-stage-get h i fn-arena$x)
                  (nth i (fn-arx-stage-octets (nth h (nth *fn-arena$x-stagei* fn-arena$x))))))
  :hints (("Goal" :in-theory (e/d (fn-arx-stage-octets) (nth)))))

(defthm fn-arx-stage-payload-is
  (implies (natp h)
           (equal (fn-arx-stage-payload h fn-arena$x)
                  (fn-arx-stage-octets (nth h (nth *fn-arena$x-stagei* fn-arena$x)))))
  :hints (("Goal" :in-theory (e/d (fn-arx-stage-octets) (nth)))))

(defthm fn-arx-len-after-mark
  (implies (natp n)
           (< n (len (update-nth n e (if (< n (len ext))
                                         ext
                                       (resize-list ext (max 64 (* 2 n)) 0))))))
  :rule-classes (:rewrite :linear))

(local (in-theory (disable fn-arx-nth-0-is-car)))

(defthm fn-arx-xp-of-update-inner
  (implies (and (fn-arena$xp fn-arena$x) (fn-arn-payload-listp v))
           (fn-arena$xp (update-nth *fn-arena$x-inner* v fn-arena$x))))

(defthm fn-arx-xp-of-update-ext
  (implies (and (fn-arena$xp fn-arena$x) (true-listp v))
           (fn-arena$xp (update-nth *fn-arena$x-exti* v fn-arena$x))))

(defthm fn-arx-xp-fields
  (implies (fn-arena$xp fn-arena$x)
           (and (fn-arn-payload-listp (nth *fn-arena$x-inner* fn-arena$x))
                (true-listp (nth *fn-arena$x-exti* fn-arena$x)))))

(defthm fn-arx-xp-of-update-stage
  (implies (and (fn-arena$xp fn-arena$x) (fn-arena$x-stagep v))
           (fn-arena$xp (update-nth *fn-arena$x-stagei* v fn-arena$x))))

(local
 (defthm fn-arx-len-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(defthm fn-arx-extentp-plen
  (implies (fn-arn-extentp e) (natp (nth 4 e)))
  :rule-classes (:rewrite :type-prescription))

(defthm fn-arx-not-extentp-0
  (not (fn-arn-extentp 0)))

(defthm fn-arx-lz-extentp-plen
  (implies (fn-arn-lz-extentp e) (natp (nth 6 e)))
  :rule-classes (:rewrite :type-prescription))

(defthm fn-arx-not-lz-extentp-0
  (not (fn-arn-lz-extentp 0)))

(defthm fn-arx-lz-extent-is-not-staged
  (implies (fn-arn-lz-extentp e) (not (equal e :staged))))

(in-theory (disable fn-arx-mark fn-arx-stage-grow fn-arx-stage-write fn-arx-stage-len
                    fn-arx-stage-get fn-arx-stage-payload
                    fn-arena$xp nth update-nth fn-arn-extentp fn-arn-lz-extentp fn-arx-view))

; -----------------------------------------------------------------------------
; The obligations, each as `defabsstobj-missing-events' states it.

(defthm create-fn-arena-extent{correspondence}
  (fn-arena$xcorr (create-fn-arena$x) (create-fn-arena$a))
  :rule-classes nil)

(defthm create-fn-arena-extent{preserved}
  (fn-arena$ap (create-fn-arena$a))
  :rule-classes nil)

(defthm fn-arena-extent-count{correspondence}
  (implies (fn-arena$xcorr fn-arena$x fn-arena-extent)
           (equal (fn-arena$x-count fn-arena$x) (fn-arena$a-count fn-arena-extent)))
  :rule-classes nil)

(defthm fn-arena-extent-payload-len{correspondence}
  (implies (and (fn-arena$xcorr fn-arena$x fn-arena-extent)
                (natp h) (< h (fn-arena$a-count fn-arena-extent)))
           (equal (fn-arena$x-payload-len h fn-arena$x) (fn-arena$a-payload-len h fn-arena-extent)))
  :rule-classes nil
  )

(defthm fn-arena-extent-payload-len{guard-thm}
  (implies (and (fn-arena$xcorr fn-arena$x fn-arena-extent)
                (natp h) (< h (fn-arena$a-count fn-arena-extent)))
           (and (natp h) (< h (fn-arena$x-count fn-arena$x))
                (fn-arena$x-wfp fn-arena$x)))
  :rule-classes nil)

(defthm fn-arena-extent-get{correspondence}
  (implies (and (fn-arena$xcorr fn-arena$x fn-arena-extent)
                (natp h) (< h (fn-arena$a-count fn-arena-extent))
                (natp i) (< i (fn-arena$a-payload-len h fn-arena-extent)))
           (equal (fn-arena$x-get h i fn-arena$x) (fn-arena$a-get h i fn-arena-extent)))
  :rule-classes nil
  )

(defthm fn-arena-extent-get{guard-thm}
  (implies (and (fn-arena$xcorr fn-arena$x fn-arena-extent)
                (natp h) (< h (fn-arena$a-count fn-arena-extent))
                (natp i) (< i (fn-arena$a-payload-len h fn-arena-extent)))
           (and (natp h) (< h (fn-arena$x-count fn-arena$x))
                (fn-arena$x-wfp fn-arena$x)
                (natp i) (< i (fn-arena$x-payload-len h fn-arena$x))))
  :rule-classes nil
  :hints (("Goal" :cases ((equal (nth h (nth *fn-arena$x-exti* fn-arena$x)) :forgotten)))))

(defthm fn-arena-extent-payload{correspondence}
  (implies (and (fn-arena$xcorr fn-arena$x fn-arena-extent)
                (natp h) (< h (fn-arena$a-count fn-arena-extent)))
           (equal (fn-arena$x-payload h fn-arena$x) (fn-arena$a-payload h fn-arena-extent)))
  :rule-classes nil
  )

(defthm fn-arena-extent-payload{guard-thm}
  (implies (and (fn-arena$xcorr fn-arena$x fn-arena-extent)
                (natp h) (< h (fn-arena$a-count fn-arena-extent)))
           (and (natp h) (< h (fn-arena$x-count fn-arena$x))
                (fn-arena$x-wfp fn-arena$x)))
  :rule-classes nil)

(defthm fn-arena-extent-seal-list{correspondence}
  (implies (and (fn-arena$xcorr fn-arena$x fn-arena-extent)
                (fn-cbor-octet-listp xs))
           (fn-arena$xcorr (fn-arena$x-seal-list xs fn-arena$x)
                           (fn-arena$a-seal-list xs fn-arena-extent)))
  :rule-classes nil
  )

(defthm fn-arena-extent-seal-list{guard-thm}
  (implies (and (fn-arena$xcorr fn-arena$x fn-arena-extent)
                (fn-cbor-octet-listp xs))
           (and (fn-cbor-octet-listp xs) (fn-arena$x-wfp fn-arena$x)))
  :rule-classes nil)

(defthm fn-arena-extent-seal-list{preserved}
  (implies (and (fn-arena$ap fn-arena-extent)
                (fn-cbor-octet-listp xs))
           (fn-arena$ap (fn-arena$a-seal-list xs fn-arena-extent)))
  :rule-classes nil)

(defthm fn-arena-extent-seal-buffer{correspondence}
  (implies (and (fn-arena$xcorr fn-arena$x fn-arena-extent)
                (fn-octets-p fn-octets))
           (fn-arena$xcorr (fn-arena$x-seal-buffer fn-octets fn-arena$x)
                           (fn-arena$a-seal-buffer fn-octets fn-arena-extent)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-oct-octets-p-is-octet-listp))))

(defthm fn-arena-extent-seal-buffer{guard-thm}
  (implies (and (fn-arena$xcorr fn-arena$x fn-arena-extent)
                (fn-octets-p fn-octets))
           (fn-arena$x-wfp fn-arena$x))
  :rule-classes nil)

(defthm fn-arena-extent-seal-buffer{preserved}
  (implies (and (fn-arena$ap fn-arena-extent)
                (fn-octets-p fn-octets))
           (fn-arena$ap (fn-arena$a-seal-buffer fn-octets fn-arena-extent)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-oct-octets-p-is-octet-listp))))

(defthm fn-arena-extent-seal-range{correspondence}
  (implies (and (fn-arena$xcorr fn-arena$x fn-arena-extent)
                (fn-octets-p fn-octets)
                (natp a) (natp b) (<= a b) (<= b (fn-octets-len fn-octets)))
           (fn-arena$xcorr (fn-arena$x-seal-range a b fn-octets fn-arena$x)
                           (fn-arena$a-seal-range a b fn-octets fn-arena-extent)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-oct-octets-p-is-octet-listp)
                                  (fn-oct-slice-list-is-take-nthcdr)))))

(defthm fn-arena-extent-seal-range{guard-thm}
  (implies (and (fn-arena$xcorr fn-arena$x fn-arena-extent)
                (fn-octets-p fn-octets)
                (natp a) (natp b) (<= a b) (<= b (fn-octets-len fn-octets)))
           (and (natp a) (natp b) (<= a b) (<= b (fn-octets-len fn-octets))
                (fn-arena$x-wfp fn-arena$x)))
  :rule-classes nil)

(defthm fn-arena-extent-seal-range{preserved}
  (implies (and (fn-arena$ap fn-arena-extent)
                (fn-octets-p fn-octets)
                (natp a) (natp b) (<= a b) (<= b (fn-octets-len fn-octets)))
           (fn-arena$ap (fn-arena$a-seal-range a b fn-octets fn-arena-extent)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-oct-octets-p-is-octet-listp)
                                  (fn-oct-slice-list-is-take-nthcdr)))))

(defthm fn-arena-extent-clear{correspondence}
  (implies (fn-arena$xcorr fn-arena$x fn-arena-extent)
           (fn-arena$xcorr (fn-arena$x-clear fn-arena$x) (fn-arena$a-clear fn-arena-extent)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-arena$xp fn-arena$x-extp fn-arena$x-stagep))))

(defthm fn-arena-extent-clear{preserved}
  (implies (fn-arena$ap fn-arena-extent)
           (fn-arena$ap (fn-arena$a-clear fn-arena-extent)))
  :rule-classes nil)

(defthm fn-arena-extent-seal-extent{correspondence}
  (implies (and (fn-arena$xcorr fn-arena$x fn-arena-extent)
                (fn-arn-extent-guardp file eoff elen poff plen trailer))
           (fn-arena$xcorr (fn-arena$x-seal-extent file eoff elen poff plen trailer fn-arena$x)
                           (fn-arena$a-seal-extent file eoff elen poff plen trailer fn-arena-extent)))
  :rule-classes nil
  )

(defthm fn-arena-extent-seal-extent{guard-thm}
  (implies (and (fn-arena$xcorr fn-arena$x fn-arena-extent)
                (fn-arn-extent-guardp file eoff elen poff plen trailer))
           (and (fn-arn-extent-guardp file eoff elen poff plen trailer)
                (fn-arena$x-wfp fn-arena$x)))
  :rule-classes nil)

(defthm fn-arena-extent-seal-extent{preserved}
  (implies (and (fn-arena$ap fn-arena-extent)
                (fn-arn-extent-guardp file eoff elen poff plen trailer))
           (fn-arena$ap (fn-arena$a-seal-extent file eoff elen poff plen trailer fn-arena-extent)))
  :rule-classes nil)

(defthm fn-arx-payload-listp-of-update-nth
  (implies (and (fn-arn-payload-listp a) (fn-cbor-octet-listp v) (natp h) (< h (len a)))
           (fn-arn-payload-listp (update-nth h v a)))
  :hints (("Goal" :in-theory (enable update-nth fn-arn-payload-listp))))

(defthm fn-arena-extent-reseat-extent{correspondence}
  (implies (and (fn-arena$xcorr fn-arena$x fn-arena-extent)
                (natp h) (< h (fn-arena$a-count fn-arena-extent))
                (fn-arn-extent-guardp file eoff elen poff plen trailer))
           (fn-arena$xcorr (fn-arena$x-reseat-extent h file eoff elen poff plen trailer fn-arena$x)
                           (fn-arena$a-reseat-extent h file eoff elen poff plen trailer
                                                     fn-arena-extent)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-arx-view-of-update-inside fn-oct-update-is-update-nth))))

(defthm fn-arena-extent-reseat-extent{guard-thm}
  (implies (and (fn-arena$xcorr fn-arena$x fn-arena-extent)
                (natp h) (< h (fn-arena$a-count fn-arena-extent))
                (fn-arn-extent-guardp file eoff elen poff plen trailer))
           (and (natp h) (< h (fn-arena$x-count fn-arena$x))
                (fn-arena$x-wfp fn-arena$x)
                (fn-arn-extent-guardp file eoff elen poff plen trailer)))
  :rule-classes nil)

(defthm fn-arena-extent-reseat-extent{preserved}
  (implies (and (fn-arena$ap fn-arena-extent)
                (natp h) (< h (fn-arena$a-count fn-arena-extent))
                (fn-arn-extent-guardp file eoff elen poff plen trailer))
           (fn-arena$ap (fn-arena$a-reseat-extent h file eoff elen poff plen trailer
                                                  fn-arena-extent)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-oct-update-is-update-nth))))

(defthm fn-arena-extent-seal-lz-extent{correspondence}
  (implies (and (fn-arena$xcorr fn-arena$x fn-arena-extent)
                (fn-arn-lz-guardp file eoff elen poff plen trailer n dict))
           (fn-arena$xcorr (fn-arena$x-seal-lz-extent file eoff elen poff plen trailer n dict
                                                      fn-arena$x)
                           (fn-arena$a-seal-lz-extent file eoff elen poff plen trailer n dict
                                                      fn-arena-extent)))
  :rule-classes nil)

(defthm fn-arena-extent-seal-lz-extent{guard-thm}
  (implies (and (fn-arena$xcorr fn-arena$x fn-arena-extent)
                (fn-arn-lz-guardp file eoff elen poff plen trailer n dict))
           (and (fn-arn-lz-guardp file eoff elen poff plen trailer n dict)
                (fn-arena$x-wfp fn-arena$x)))
  :rule-classes nil)

(defthm fn-arena-extent-seal-lz-extent{preserved}
  (implies (and (fn-arena$ap fn-arena-extent)
                (fn-arn-lz-guardp file eoff elen poff plen trailer n dict))
           (fn-arena$ap (fn-arena$a-seal-lz-extent file eoff elen poff plen trailer n dict
                                                   fn-arena-extent)))
  :rule-classes nil)

(defthm fn-arena-extent-reseat-lz-extent{correspondence}
  (implies (and (fn-arena$xcorr fn-arena$x fn-arena-extent)
                (natp h) (< h (fn-arena$a-count fn-arena-extent))
                (fn-arn-lz-guardp file eoff elen poff plen trailer n dict))
           (fn-arena$xcorr (fn-arena$x-reseat-lz-extent h file eoff elen poff plen trailer n dict
                                                        fn-arena$x)
                           (fn-arena$a-reseat-lz-extent h file eoff elen poff plen trailer n dict
                                                        fn-arena-extent)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-arx-view-of-update-inside fn-oct-update-is-update-nth))))

(defthm fn-arena-extent-reseat-lz-extent{guard-thm}
  (implies (and (fn-arena$xcorr fn-arena$x fn-arena-extent)
                (natp h) (< h (fn-arena$a-count fn-arena-extent))
                (fn-arn-lz-guardp file eoff elen poff plen trailer n dict))
           (and (natp h) (< h (fn-arena$x-count fn-arena$x))
                (fn-arena$x-wfp fn-arena$x)
                (fn-arn-lz-guardp file eoff elen poff plen trailer n dict)))
  :rule-classes nil)

(defthm fn-arena-extent-reseat-lz-extent{preserved}
  (implies (and (fn-arena$ap fn-arena-extent)
                (natp h) (< h (fn-arena$a-count fn-arena-extent))
                (fn-arn-lz-guardp file eoff elen poff plen trailer n dict))
           (fn-arena$ap (fn-arena$a-reseat-lz-extent h file eoff elen poff plen trailer n dict
                                                     fn-arena-extent)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-oct-update-is-update-nth))))

(defthm fn-arx-extent-is-not-staged
  (implies (fn-arn-extentp e) (not (equal e :staged)))
  :hints (("Goal" :in-theory (enable fn-arn-extentp))))

(defthm fn-arx-xp-stage-field
  (implies (fn-arena$xp fn-arena$x)
           (fn-arena$x-stagep (nth *fn-arena$x-stagei* fn-arena$x)))
  :hints (("Goal" :in-theory (enable fn-arena$xp))))

(local
 (defthm fn-arx-pagep-of-emptied
   (implies (fn-arena-pagep p)
            (fn-arena-pagep (update-nth 0 nil p)))
   :hints (("Goal" :in-theory (enable update-nth)))))

(defthm fn-arena-extent-release{correspondence}
  (implies (and (fn-arena$xcorr fn-arena$x fn-arena-extent)
                (natp h))
           (fn-arena$xcorr (fn-arena$x-release h fn-arena$x)
                           (fn-arena$a-release h fn-arena-extent)))
  :rule-classes nil)

(defthm fn-arena-extent-release{guard-thm}
  (implies (and (fn-arena$xcorr fn-arena$x fn-arena-extent)
                (natp h))
           (natp h))
  :rule-classes nil)

(defthm fn-arena-extent-release{preserved}
  (implies (and (fn-arena$ap fn-arena-extent)
                (natp h))
           (fn-arena$ap (fn-arena$a-release h fn-arena-extent)))
  :rule-classes nil)

(local
 (defthm fn-arx-update-nth-twice
   (equal (update-nth h v (update-nth h w l)) (update-nth h v l))
   :hints (("Goal" :in-theory (enable update-nth)))))

(defthm fn-arena-extent-forget{correspondence}
  (implies (and (fn-arena$xcorr fn-arena$x fn-arena-extent)
                (natp h))
           (fn-arena$xcorr (fn-arena$x-forget h fn-arena$x)
                           (fn-arena$a-forget h fn-arena-extent)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-arx-view-of-update-inside fn-arx-view-of-stage-update-inside
                                     fn-oct-update-is-update-nth))))

(defthm fn-arena-extent-forget{guard-thm}
  (implies (and (fn-arena$xcorr fn-arena$x fn-arena-extent)
                (natp h))
           (and (natp h) (fn-arena$x-wfp fn-arena$x)))
  :rule-classes nil)

(defthm fn-arena-extent-forget{preserved}
  (implies (and (fn-arena$ap fn-arena-extent)
                (natp h))
           (fn-arena$ap (fn-arena$a-forget h fn-arena-extent)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-oct-update-is-update-nth))))

(defabsstobj fn-arena-extent
  :foundation fn-arena$x
  :recognizer (fn-arena-extent-p :logic fn-arena$ap :exec fn-arena$xp)
  :creator (create-fn-arena-extent :logic create-fn-arena$a :exec create-fn-arena$x)
  :corr-fn fn-arena$xcorr
  :exports ((fn-arena-extent-count :logic fn-arena$a-count :exec fn-arena$x-count)
            (fn-arena-extent-payload-len :logic fn-arena$a-payload-len :exec fn-arena$x-payload-len)
            (fn-arena-extent-get :logic fn-arena$a-get :exec fn-arena$x-get)
            (fn-arena-extent-payload :logic fn-arena$a-payload :exec fn-arena$x-payload)
            (fn-arena-extent-seal-list :logic fn-arena$a-seal-list :exec fn-arena$x-seal-list
                                       :protect t)
            (fn-arena-extent-seal-buffer :logic fn-arena$a-seal-buffer :exec fn-arena$x-seal-buffer
                                         :protect t)
            (fn-arena-extent-clear :logic fn-arena$a-clear :exec fn-arena$x-clear :protect t)
            (fn-arena-extent-seal-range :logic fn-arena$a-seal-range :exec fn-arena$x-seal-range
                                        :protect t)
            (fn-arena-extent-seal-extent :logic fn-arena$a-seal-extent :exec fn-arena$x-seal-extent
                                         :protect t)
            (fn-arena-extent-reseat-extent :logic fn-arena$a-reseat-extent
                                           :exec fn-arena$x-reseat-extent :protect t)
            (fn-arena-extent-release :logic fn-arena$a-release :exec fn-arena$x-release
                                     :protect t)
            (fn-arena-extent-seal-lz-extent :logic fn-arena$a-seal-lz-extent
                                            :exec fn-arena$x-seal-lz-extent :protect t)
            (fn-arena-extent-reseat-lz-extent :logic fn-arena$a-reseat-lz-extent
                                              :exec fn-arena$x-reseat-lz-extent :protect t)
            (fn-arena-extent-forget :logic fn-arena$a-forget :exec fn-arena$x-forget
                                    :protect t)))

; -----------------------------------------------------------------------------
; The file count, read (lane composed-owner-4, row A6).  The host reads the
; live arena's count column under the owner mutex (host/native/owner.lisp,
; the checkpoint release) to decide which retired files' descriptors may
; close: one read per file, never a walk of the extent column.

(defun fn-arx-file-count (f fn-arena$x)
  (declare (xargs :stobjs fn-arena$x :guard (natp f)))
  (if (< f (fn-arena$x-files-length fn-arena$x))
      (nfix (fn-arena$x-filesi f fn-arena$x))
    0))

(defun fn-arx-files-unnamed-p (fs fn-arena$x)
  (declare (xargs :stobjs fn-arena$x :guard (nat-listp fs)))
  (if (atom fs)
      t
    (and (equal (fn-arx-file-count (car fs) fn-arena$x) 0)
         (fn-arx-files-unnamed-p (cdr fs) fn-arena$x))))

(defthm fn-arx-file-count-is-files-get
  (implies (natp f)
           (equal (fn-arx-file-count f fn-arena$x)
                  (fn-arx-files-get f (nth *fn-arena$x-filesi* fn-arena$x))))
  :hints (("Goal" :in-theory (enable fn-arx-files-get nth))))

(local
 (defthm fn-arx-nth-past-end-nil
   (implies (and (natp h) (<= (len l) h)) (equal (nth h l) nil))
   :hints (("Goal" :in-theory (enable nth)))))

; KEYSTONE: under the arena's correspondence (which every export keeps, so
; the live arena satisfies it), a file whose count is 0 is named by no entry
; of the extent column, at any handle: no realizer call reads it again.
(defthm fn-arx-file-count-zero-names-none
  (implies (and (fn-arena$xcorr fn-arena$x fn-arena$a)
                (natp f) (natp h)
                (equal (fn-arx-file-count f fn-arena$x) 0))
           (not (equal (fn-arx-entry-file (nth h (nth *fn-arena$x-exti* fn-arena$x))) f)))
  :hints (("Goal" :do-not-induct t
           :cases ((< h (len (nth *fn-arena$x-exti* fn-arena$x))))
           :in-theory (disable fn-arx-files-agree-necc fn-arx-tally-positive-when-named)
           :use ((:instance fn-arx-files-agree-necc
                            (ext (nth *fn-arena$x-exti* fn-arena$x))
                            (files (nth *fn-arena$x-filesi* fn-arena$x)))
                 (:instance fn-arx-tally-positive-when-named
                            (ext (nth *fn-arena$x-exti* fn-arena$x)))))))

(defthm fn-arx-files-unnamed-p-member
  (implies (and (fn-arx-files-unnamed-p fs fn-arena$x) (member-equal f fs) (natp f))
           (equal (fn-arx-file-count f fn-arena$x) 0))
  :hints (("Goal" :in-theory (disable fn-arx-file-count-is-files-get))))

(local
 (defthm fn-arx-member-of-nat-listp
   (implies (and (nat-listp fs) (member-equal f fs)) (natp f))
   :rule-classes :forward-chaining))

(local
 (defthm fn-arx-nth-non-natp
   (implies (not (natp h)) (equal (nth h l) (nth 0 l)))
   :hints (("Goal" :in-theory (enable nth)))))

(local
 (defthm fn-arx-files-unnamed-names-none-at-natp
   (implies (and (fn-arena$xcorr fn-arena$x fn-arena$a)
                 (nat-listp fs)
                 (fn-arx-files-unnamed-p fs fn-arena$x)
                 (member-equal f fs) (natp h))
            (not (equal (fn-arx-entry-file (nth h (nth *fn-arena$x-exti* fn-arena$x))) f)))
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-arena$xcorr fn-arx-file-count-is-files-get
                                fn-arx-file-count fn-arx-files-unnamed-p)
            :use ((:instance fn-arx-file-count-zero-names-none)
                  (:instance fn-arx-files-unnamed-p-member))))))

; KEYSTONE (the host-called subject): every file of FS the check passes is
; named by no entry at any handle H (a non-natural H reads entry 0).
(defthm fn-arx-files-unnamed-names-none
  (implies (and (fn-arena$xcorr fn-arena$x fn-arena$a)
                (nat-listp fs)
                (fn-arx-files-unnamed-p fs fn-arena$x)
                (member-equal f fs))
           (not (equal (fn-arx-entry-file (nth h (nth *fn-arena$x-exti* fn-arena$x))) f)))
  :hints (("Goal" :do-not-induct t :cases ((natp h))
           :in-theory (disable fn-arena$xcorr fn-arx-files-unnamed-names-none-at-natp
                               fn-arx-files-unnamed-p)
           :use ((:instance fn-arx-files-unnamed-names-none-at-natp)
                 (:instance fn-arx-files-unnamed-names-none-at-natp (h 0))))))

; What an entry names is the file its realizer reads (fn-arena$x-get passes
; (nth 0 E) to fn-durable-realize-octets / fn-durable-realize-lz).
(defthm fn-arx-entry-file-of-extent-by-definition
  (implies (or (fn-arn-extentp e) (fn-arn-lz-extentp e))
           (equal (fn-arx-entry-file e) (nth 0 e)))
  :hints (("Goal" :in-theory (enable fn-arx-entry-file))))

; -----------------------------------------------------------------------------
; The forget, over the concrete arena (lane arena-forget, 2026-10-03).

; The forget writes one entry: H's is :forgotten (it names no file and no
; realizer call reads through it), every other handle's is what it was.
(defthm fn-arx-forget-entries
  (implies (and (fn-arena$xcorr fn-arena$x fn-arena$a)
                (natp h) (< h (len fn-arena$a)) (natp k))
           (equal (nth k (nth *fn-arena$x-exti* (fn-arena$x-forget h fn-arena$x)))
                  (if (equal k h)
                      :forgotten
                    (nth k (nth *fn-arena$x-exti* fn-arena$x)))))
  :hints (("Goal" :do-not-induct t)))

; KEYSTONE (PRF-1235).  The forget gives back exactly H's name: the count of
; the file H's entry named falls by one and every other file's count is
; unchanged.  So once every handle that named a dropped file is reseated or
; forgotten its count is 0, fn-xrt-quiet-files answers it
; (books/extent-retire.lisp) and the host closes its descriptor while
; serving.  Host subject: host/native/io.lisp fnn-arena-forget-due calls
; fn-arena-forget on the live arena, whose attachment runs fn-arena$x-forget.
(defthm fn-arx-forget-file-count
  (implies (and (fn-arena$xcorr fn-arena$x fn-arena$a)
                (natp h) (< h (len fn-arena$a)) (natp f))
           (equal (fn-arx-file-count f (fn-arena$x-forget h fn-arena$x))
                  (- (fn-arx-file-count f fn-arena$x)
                     (if (equal (fn-arx-entry-file (nth h (nth *fn-arena$x-exti* fn-arena$x))) f)
                         1
                       0))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-arx-files-agree-necc fn-arx-tally-positive-when-named
                               fn-arx-file-count)
           :use ((:instance fn-arx-files-agree-necc
                            (ext (nth *fn-arena$x-exti* fn-arena$x))
                            (files (nth *fn-arena$x-filesi* fn-arena$x)))
                 (:instance fn-arx-tally-positive-when-named
                            (ext (nth *fn-arena$x-exti* fn-arena$x)))))))

(in-theory (disable fn-arena$x-forget))
