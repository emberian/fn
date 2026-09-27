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
; The STAGE (lane arena-offheap-3, PRF-296): an array of page stobjs, one
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

(defstobj fn-arena$x
  (fn-arena$x-inner :type fn-arena-paged)
  (fn-arena$x-ext :type (array t (0)) :initially 0 :resizable t)
  (fn-arena$x-stage :type (array fn-arena-page (0)) :resizable t)
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
        ((eq e :staged) (fn-arx-stage-octets s))
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

(defthm fn-arx-entry-of-staged
  (equal (fn-arx-entry :staged x s) (fn-arx-stage-octets s)))

(defthm fn-arx-entry-of-resident
  (implies (and (not (fn-arn-extentp e)) (not (equal e :staged)))
           (equal (fn-arx-entry e x s) x)))

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
          ((eq e :staged) (fn-arx-stage-len h fn-arena$x))
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
          ((eq e :staged) (fn-arx-stage-get h i fn-arena$x))
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
          ((eq e :staged) (fn-arx-stage-payload h fn-arena$x))
          (t (stobj-let ((fn-arena-paged (fn-arena$x-inner fn-arena$x)))
                        (v)
                        (fn-arena-paged-payload h fn-arena-paged)
                        v)))))

; Handle H's entry E, the array grown (doubled) when H is past it.
(defun fn-arx-mark (h e fn-arena$x)
  (declare (xargs :stobjs fn-arena$x :guard (natp h)))
  (let ((fn-arena$x (if (< h (fn-arena$x-ext-length fn-arena$x))
                        fn-arena$x
                      (resize-fn-arena$x-ext (max 64 (* 2 h)) fn-arena$x))))
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
         (fn-arena$x (resize-fn-arena$x-stage 0 fn-arena$x)))
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

; The release: the stage slot of an EXTENT handle is emptied (no other
; handle's slot is touched, and a staged handle keeps its copy).
(defun fn-arena$x-release (h fn-arena$x)
  (declare (xargs :stobjs fn-arena$x :guard (natp h)))
  (if (and (< h (fn-arena$x-ext-length fn-arena$x))
           (< h (fn-arena$x-stage-length fn-arena$x))
           (fn-arn-extentp (fn-arena$x-exti h fn-arena$x)))
      (stobj-let ((fn-arena-page (fn-arena$x-stagei h fn-arena$x)))
                 (fn-arena-page)
                 (resize-fn-arena-page-bytes 0 fn-arena-page)
                 fn-arena$x)
    fn-arena$x))

; -----------------------------------------------------------------------------
; The abstraction relation.

(defun fn-arena$xcorr (fn-arena$x fn-arena$a)
  (declare (xargs :verify-guards nil))
  (and (fn-arena$xp fn-arena$x)
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

(local
 (defthm fn-arx-car-update-nth
   (implies (not (zp k))
            (equal (car (update-nth k v x)) (car x)))
   :hints (("Goal" :in-theory (enable update-nth)))))

;; The stage's growth: the other fields untouched, the view unchanged (new
;; slots are empty pages), slot H covered.
(defthm fn-arx-stage-octets-of-fresh-page
  (equal (fn-arx-stage-octets (create-fn-arena-page)) nil)
  :hints (("Goal" :in-theory (enable fn-arx-stage-octets))))

(defthm fn-arx-stage-grow-fields
  (and (equal (nth *fn-arena$x-inner* (fn-arx-stage-grow h fn-arena$x))
              (nth *fn-arena$x-inner* fn-arena$x))
       (equal (nth *fn-arena$x-exti* (fn-arx-stage-grow h fn-arena$x))
              (nth *fn-arena$x-exti* fn-arena$x)))
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
              (nth *fn-arena$x-exti* fn-arena$x)))
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

(in-theory (disable fn-arx-mark fn-arx-stage-grow fn-arx-stage-write fn-arx-stage-len
                    fn-arx-stage-get fn-arx-stage-payload
                    fn-arena$xp nth update-nth fn-arn-extentp fn-arx-view))

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
  )

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
  :rule-classes nil)

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
                                     :protect t)))
