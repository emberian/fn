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
                  (append (fn-oct-list-from 0 j (nth 0 fn-arena-page)) acc)))
  :hints (("Goal" :induct (fn-arx-page-down j acc fn-arena-page)
           :in-theory (disable fn-arx-list-from-snoc fn-oct-list-from))
          ("Subgoal *1/2" :use ((:instance fn-arx-list-from-snoc
                                           (i 0) (n (1- j)) (buf (nth 0 fn-arena-page)))))))

(defthm fn-arx-page-copy-len
  (implies (<= (nfix n) (len (nth 0 fn-arena-page)))
           (equal (len (nth 0 (fn-arx-page-copy j n a fn-octets fn-arena-page)))
                  (len (nth 0 fn-arena-page))))
  :hints (("Goal" :induct (fn-arx-page-copy j n a fn-octets fn-arena-page))))

(defthm fn-arx-page-copy-below
  (implies (and (natp k) (< k (nfix j)))
           (equal (nth k (nth 0 (fn-arx-page-copy j n a fn-octets fn-arena-page)))
                  (nth k (nth 0 fn-arena-page))))
  :hints (("Goal" :induct (fn-arx-page-copy j n a fn-octets fn-arena-page))))

(defthm fn-arx-page-copy-other-fields
  (implies (not (equal (nfix k) 0))
           (equal (nth k (fn-arx-page-copy j n a fn-octets fn-arena-page))
                  (nth k fn-arena-page)))
  :hints (("Goal" :induct (fn-arx-page-copy j n a fn-octets fn-arena-page))))

(local
 (defthm fn-arx-list-from-of-page-copy-below
   (implies (and (natp j) (natp m) (<= m j))
            (equal (fn-oct-list-from i m (nth 0 (fn-arx-page-copy j n a fn-octets fn-arena-page)))
                   (fn-oct-list-from i m (nth 0 fn-arena-page))))
   :hints (("Goal" :induct (fn-arx-page-copy j n a fn-octets fn-arena-page)))))

(defthm fn-arx-page-copy-copies
  (implies (and (natp j) (natp n) (natp a) (<= n (len (nth 0 fn-arena-page))))
           (equal (fn-oct-list-from j n (nth 0 (fn-arx-page-copy j n a fn-octets fn-arena-page)))
                  (fn-oct-list-from (+ a j) (+ a n) fn-octets)))
  :hints (("Goal" :induct (fn-arx-page-copy j n a fn-octets fn-arena-page)
           :in-theory (enable fn-oct-get-is-nth))))

(local
 (defthm fn-arx-list-from-to-end
   (implies (and (natp i) (true-listp x) (<= i (len x)))
            (equal (fn-oct-list-from i (len x) x) (nthcdr i x)))
   :hints (("Goal" :induct (fn-oct-list-from i (len x) x)
            :in-theory (enable nth nthcdr)))))

(defthm fn-arx-list-from-whole
  (implies (true-listp x)
           (equal (fn-oct-list-from 0 (len x) x) x))
  :hints (("Goal" :use ((:instance fn-arx-list-from-to-end (i 0))))))

; -----------------------------------------------------------------------------
; The view.

(defun fn-arx-entry (e x)
  (declare (xargs :guard t))
  (if (fn-arn-extentp e)
      (fn-durable-octets (nth 0 e) (nth 3 e) (nth 4 e))
    x))

(defthm fn-arx-entry-octets
  (implies (fn-cbor-octet-listp x)
           (fn-cbor-octet-listp (fn-arx-entry e x))))

(defthm fn-arx-nth-of-payload-listp
  (implies (fn-arn-payload-listp a)
           (fn-cbor-octet-listp (nth h a)))
  :hints (("Goal" :in-theory (enable nth))))

(local
 (defthm fn-arx-nth-append-below
   (implies (and (natp k) (< k (len a)))
            (equal (nth k (append a b)) (nth k a)))
   :hints (("Goal" :in-theory (enable nth)))))

(in-theory (disable fn-arx-entry))

(defun fn-arx-view (h n ext a)
  (declare (xargs :guard t :verify-guards nil :measure (nfix (- (nfix n) (nfix h)))))
  (if (or (not (natp h)) (not (natp n)) (<= n h))
      nil
    (cons (fn-arx-entry (nth h ext) (nth h a))
          (fn-arx-view (1+ h) n ext a))))

(defthm fn-arx-len-view
  (equal (len (fn-arx-view h n ext a))
         (if (and (natp h) (natp n) (< h n)) (- n h) 0)))

(defthm fn-arx-true-listp-view
  (true-listp (fn-arx-view h n ext a)))

(local
 (defun fn-arx-ind-hk (h k n)
   (declare (xargs :measure (nfix (- (nfix n) (nfix h)))))
   (if (or (not (natp h)) (not (natp n)) (<= n h))
       (list h k)
     (fn-arx-ind-hk (1+ h) (1- k) n))))

(defthm fn-arx-nth-view
  (implies (and (natp h) (natp n) (natp k) (< (+ h k) n))
           (equal (nth k (fn-arx-view h n ext a))
                  (fn-arx-entry (nth (+ h k) ext) (nth (+ h k) a))))
  :hints (("Goal" :induct (fn-arx-ind-hk h k n))))

(defthm fn-arx-view-empty
  (implies (and (natp h) (natp n) (<= n h))
           (equal (fn-arx-view h n ext a) nil)))

(defthm fn-arx-view-extend
  (implies (and (natp h) (natp n) (<= h n))
           (equal (fn-arx-view h (1+ n) ext a)
                  (append (fn-arx-view h n ext a)
                          (list (fn-arx-entry (nth n ext) (nth n a))))))
  :hints (("Goal" :induct (fn-arx-view h n ext a))))

(defthm fn-arx-view-of-update-above
  (implies (and (natp k) (<= (nfix n) k))
           (equal (fn-arx-view h n (update-nth k v ext) a)
                  (fn-arx-view h n ext a))))

(local
 (defthm fn-arx-nth-resize-list
   (implies (and (natp k) (< k (len l)) (<= (len l) (nfix m)))
            (equal (nth k (resize-list l m d)) (nth k l)))
   :hints (("Goal" :in-theory (enable nth resize-list)))))

(defthm fn-arx-view-of-resize
  (implies (and (<= (nfix n) (len ext)) (<= (len ext) (nfix m)))
           (equal (fn-arx-view h n (resize-list ext m d) a)
                  (fn-arx-view h n ext a))))

(defthm fn-arx-view-of-append-beyond
  (implies (<= (nfix n) (len a))
           (equal (fn-arx-view h n ext (append a b))
                  (fn-arx-view h n ext a))))

(defthm fn-arx-payload-listp-view
  (implies (fn-arn-payload-listp a)
           (fn-arn-payload-listp (fn-arx-view h n ext a)))
  :hints (("Goal" :in-theory (disable fn-arn-payload-listp-true-listp))))

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

(defun fn-arena$x-payload-len (h fn-arena$x)
  (declare (xargs :stobjs fn-arena$x
                  :guard (and (natp h) (< h (fn-arena$x-count fn-arena$x))
                              (fn-arena$x-wfp fn-arena$x))))
  (let ((e (fn-arena$x-exti h fn-arena$x)))
    (if (fn-arn-extentp e)
        (nth 4 e)
      (stobj-let ((fn-arena-paged (fn-arena$x-inner fn-arena$x)))
                 (n)
                 (fn-arena-paged-payload-len h fn-arena-paged)
                 n))))

(defun fn-arena$x-get (h i fn-arena$x)
  (declare (xargs :stobjs fn-arena$x
                  :guard (and (natp h) (< h (fn-arena$x-count fn-arena$x))
                              (fn-arena$x-wfp fn-arena$x)
                              (natp i) (< i (fn-arena$x-payload-len h fn-arena$x)))))
  (let ((e (fn-arena$x-exti h fn-arena$x)))
    (if (fn-arn-extentp e)
        (fn-durable-realize-octet (nth 0 e) (nth 1 e) (nth 2 e) (nth 3 e) (nth 4 e) (nth 5 e) i)
      (stobj-let ((fn-arena-paged (fn-arena$x-inner fn-arena$x)))
                 (v)
                 (fn-arena-paged-get h i fn-arena-paged)
                 v))))

(defun fn-arena$x-payload (h fn-arena$x)
  (declare (xargs :stobjs fn-arena$x
                  :guard (and (natp h) (< h (fn-arena$x-count fn-arena$x))
                              (fn-arena$x-wfp fn-arena$x))))
  (let ((e (fn-arena$x-exti h fn-arena$x)))
    (if (fn-arn-extentp e)
        (fn-durable-realize-octets (nth 0 e) (nth 1 e) (nth 2 e) (nth 3 e) (nth 4 e) (nth 5 e))
      (stobj-let ((fn-arena-paged (fn-arena$x-inner fn-arena$x)))
                 (v)
                 (fn-arena-paged-payload h fn-arena-paged)
                 v))))

; Handle H's entry E, the array grown (doubled) when H is past it.
(defun fn-arx-mark (h e fn-arena$x)
  (declare (xargs :stobjs fn-arena$x :guard (natp h)))
  (let ((fn-arena$x (if (< h (fn-arena$x-ext-length fn-arena$x))
                        fn-arena$x
                      (resize-fn-arena$x-ext (max 64 (* 2 h)) fn-arena$x))))
    (update-fn-arena$x-exti h e fn-arena$x)))

(defun fn-arena$x-seal-list (xs fn-arena$x)
  (declare (xargs :stobjs fn-arena$x
                  :guard (and (fn-cbor-octet-listp xs) (fn-arena$x-wfp fn-arena$x))))
  (let* ((h (fn-arena$x-count fn-arena$x))
         (fn-arena$x (stobj-let ((fn-arena-paged (fn-arena$x-inner fn-arena$x)))
                                (fn-arena-paged)
                                (fn-arena-paged-seal-list xs fn-arena-paged)
                                fn-arena$x)))
    (fn-arx-mark h 0 fn-arena$x)))

(defun fn-arena$x-seal-buffer (fn-octets fn-arena$x)
  (declare (xargs :stobjs (fn-octets fn-arena$x)
                  :guard (fn-arena$x-wfp fn-arena$x)))
  (let* ((h (fn-arena$x-count fn-arena$x))
         (fn-arena$x (stobj-let ((fn-arena-paged (fn-arena$x-inner fn-arena$x)))
                                (fn-arena-paged)
                                (fn-arena-paged-seal-buffer fn-octets fn-arena-paged)
                                fn-arena$x)))
    (fn-arx-mark h 0 fn-arena$x)))

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
  (let ((fn-arena$x (stobj-let ((fn-arena-paged (fn-arena$x-inner fn-arena$x)))
                               (fn-arena-paged)
                               (fn-arena-paged-clear fn-arena-paged)
                               fn-arena$x)))
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

; -----------------------------------------------------------------------------
; The abstraction relation.

(defun fn-arena$xcorr (fn-arena$x fn-arena$a)
  (declare (xargs :verify-guards nil))
  (and (fn-arena$xp fn-arena$x)
       (fn-arn-payload-listp fn-arena$a)
       (<= (len (nth *fn-arena$x-inner* fn-arena$x)) (len (nth *fn-arena$x-exti* fn-arena$x)))
       (equal (fn-arx-view 0 (len (nth *fn-arena$x-inner* fn-arena$x))
                           (nth *fn-arena$x-exti* fn-arena$x)
                           (nth *fn-arena$x-inner* fn-arena$x))
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

(defthm fn-arx-view-after-mark
  (implies (and (natp n) (equal n (len a0)) (<= n (len ext)))
           (equal (fn-arx-view 0 (1+ n)
                               (update-nth n e (if (< n (len ext))
                                                   ext
                                                 (resize-list ext (max 64 (* 2 n)) 0)))
                               (append a0 (list x)))
                  (append (fn-arx-view 0 n ext a0) (list (fn-arx-entry e x)))))
  :hints (("Goal" :do-not-induct t :in-theory (disable fn-arx-view))))

(defthm fn-arx-len-after-mark
  (implies (natp n)
           (< n (len (update-nth n e (if (< n (len ext))
                                         ext
                                       (resize-list ext (max 64 (* 2 n)) 0))))))
  :rule-classes (:rewrite :linear))

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

(local
 (defthm fn-arx-len-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(defthm fn-arx-entry-of-extent
  (implies (fn-arn-extentp e)
           (equal (fn-arx-entry e x)
                  (fn-durable-octets (nth 0 e) (nth 3 e) (nth 4 e))))
  :hints (("Goal" :in-theory (enable fn-arx-entry))))

(defthm fn-arx-entry-of-resident
  (implies (not (fn-arn-extentp e))
           (equal (fn-arx-entry e x) x))
  :hints (("Goal" :in-theory (enable fn-arx-entry))))

(defthm fn-arx-extentp-plen
  (implies (fn-arn-extentp e) (natp (nth 4 e)))
  :rule-classes (:rewrite :type-prescription))

(defthm fn-arx-not-extentp-0
  (not (fn-arn-extentp 0)))

(in-theory (disable fn-arx-mark fn-arena$xp nth update-nth fn-arn-extentp fn-arx-view))

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
                                         :protect t)))
