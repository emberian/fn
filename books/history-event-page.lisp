; fn: fixed 256-reference all-event history leaf (D27, STO-10002).
; Internal mechanism only: source issuance, charges, directory and custody are
; the owner's obligations. No native caller/source authority is installed here.
; Epoch 0 is virgin; a registered source maps its epoch to a positive identity.
; The page size bounds ONE allocation/update, never total retained history.
(in-package "ACL2")

(defstobj fn-history-event-page
  (fn-hec-rows :type (array t (256)) :initially nil)
  (fn-hec-epoch :type (integer 0 *) :initially 0)
  (fn-hec-page-id :type (integer 0 *) :initially 0)
  (fn-hec-incarnation :type (integer 0 *) :initially 0)
  (fn-hec-base :type (integer 0 *) :initially 0)
  (fn-hec-committed :type (integer 0 256) :initially 0)
  :inline t)

(defun fn-hec-matches (epoch page-id incarnation fn-history-event-page)
  (declare (xargs :stobjs fn-history-event-page :guard t))
  (and (posp epoch) (posp page-id) (natp incarnation)
       (equal epoch (fn-hec-epoch fn-history-event-page))
       (equal page-id (fn-hec-page-id fn-history-event-page))
       (equal incarnation (fn-hec-incarnation fn-history-event-page))))

(defun fn-hec-initialize (epoch page-id incarnation base fn-history-event-page)
  (declare (xargs :stobjs fn-history-event-page :guard t))
  (if (and (posp epoch) (posp page-id) (natp incarnation) (natp base)
           (equal (fn-hec-epoch fn-history-event-page) 0)
           (equal (fn-hec-committed fn-history-event-page) 0))
      (let* ((fn-history-event-page (update-fn-hec-epoch epoch fn-history-event-page))
             (fn-history-event-page (update-fn-hec-page-id page-id fn-history-event-page))
             (fn-history-event-page (update-fn-hec-incarnation incarnation fn-history-event-page))
             (fn-history-event-page (update-fn-hec-base base fn-history-event-page)))
        (mv :initialized fn-history-event-page))
    (mv :stale fn-history-event-page)))

(defun fn-hec-append (epoch page-id incarnation expected event fn-history-event-page)
  (declare (xargs :stobjs fn-history-event-page :guard t))
  (let ((count (fn-hec-committed fn-history-event-page)))
    (cond ((not (and (fn-hec-matches epoch page-id incarnation fn-history-event-page)
                     (natp expected) (equal expected count)))
           (mv :stale fn-history-event-page))
          ((>= count 256) (mv :full fn-history-event-page))
          (t (let* ((fn-history-event-page
                     (update-fn-hec-rowsi count event fn-history-event-page))
                    (fn-history-event-page
                     (update-fn-hec-committed (1+ count) fn-history-event-page)))
               (mv :appended fn-history-event-page))))))

(defun fn-hec-read (epoch page-id incarnation slot captured-count fn-history-event-page)
  (declare (xargs :stobjs fn-history-event-page :guard t))
  (cond ((not (fn-hec-matches epoch page-id incarnation fn-history-event-page))
         (mv :stale nil))
        ((not (and (natp slot) (natp captured-count)
                   (< slot captured-count)
                   (<= captured-count (fn-hec-committed fn-history-event-page))
                   (<= (fn-hec-committed fn-history-event-page) 256)))
         (mv :range nil))
        (t (mv :row (fn-hec-rowsi slot fn-history-event-page)))))

; Boundary abstraction: each published ordinal denotes the corresponding
; logical history event. No event kind restriction: NIL is an actual row.
(defun fn-hec-relatedp (history page)
  (declare (xargs :guard t))
  (and (true-listp page) (true-listp (nth 0 page)) (true-listp history)
       (equal (len history) (nth 5 page))
       (equal (take (len history) (nth 0 page)) history)))

(local (defthm fn-hec-nth-update-nth
  (implies (and (natp i) (natp j))
           (equal (nth i (update-nth j v xs))
                  (if (equal i j) v (nth i xs))))))

; PRF-1187: effects on the actual concrete operation, not a model-only twin.
(defthm fn-hec-append-next-slot-and-count
  (implies (and (fn-hec-matches epoch page-id incarnation fn-history-event-page)
                (natp expected)
                (equal expected (fn-hec-committed fn-history-event-page))
                (< expected 256))
           (let ((after (mv-nth 1 (fn-hec-append epoch page-id incarnation expected event
                                               fn-history-event-page))))
             (and (equal (mv-nth 0 (fn-hec-append epoch page-id incarnation expected event
                                                fn-history-event-page)) :appended)
                  (equal (fn-hec-committed after) (1+ expected))
                  (equal (fn-hec-rowsi expected after) event))))
  :hints (("Goal" :in-theory (enable fn-hec-append fn-hec-committed
                                    update-fn-hec-committed fn-hec-rowsi update-fn-hec-rowsi))))

(defthm fn-hec-append-preserves-published-slot
  (implies (and (natp slot) (< slot (fn-hec-committed fn-history-event-page)))
           (equal (fn-hec-rowsi slot
                    (mv-nth 1 (fn-hec-append epoch page-id incarnation expected event
                                             fn-history-event-page)))
                  (fn-hec-rowsi slot fn-history-event-page)))
  :hints (("Goal" :in-theory (enable fn-hec-append fn-hec-committed
                                    update-fn-hec-committed fn-hec-rowsi update-fn-hec-rowsi))))

(defthm fn-hec-append-refusal-does-not-mutate
  (implies (not (equal (mv-nth 0 (fn-hec-append epoch page-id incarnation expected event
                                              fn-history-event-page)) :appended))
           (equal (mv-nth 1 (fn-hec-append epoch page-id incarnation expected event
                                          fn-history-event-page))
                  fn-history-event-page)))

(defthm fn-hec-append-keeps-captured-read
  (implies (equal (mv-nth 0 (fn-hec-read epoch page-id incarnation slot captured-count
                                            fn-history-event-page)) :row)
           (equal (fn-hec-read epoch page-id incarnation slot captured-count
                    (mv-nth 1 (fn-hec-append append-epoch append-page-id append-incarnation
                                             expected event fn-history-event-page)))
                  (fn-hec-read epoch page-id incarnation slot captured-count
                               fn-history-event-page)))
  :hints (("Goal" :in-theory (enable fn-hec-read fn-hec-append fn-hec-matches
                         fn-hec-epoch fn-hec-page-id fn-hec-incarnation
                         fn-hec-committed fn-hec-rowsi update-fn-hec-rowsi
                         update-fn-hec-committed))))

(local (defthm fn-hec-len-update-within
  (implies (and (natp n) (< n (len xs)))
           (equal (len (update-nth n v xs)) (len xs)))))

(local (defthm fn-hec-true-listp-update
  (implies (true-listp xs) (true-listp (update-nth n v xs)))))

(local (defthm fn-hec-take-update-at-end
  (implies (natp n)
           (equal (take (1+ n) (update-nth n v xs))
                  (append (take n xs) (list v))))
  :hints (("Goal" :in-theory (enable take update-nth)))))

(local (defthm fn-hec-nth-take
  (implies (and (natp n) (natp i) (< i n))
           (equal (nth i (take n xs)) (nth i xs)))
  :hints (("Goal" :in-theory (enable take nth)))))

(local (defthm fn-hec-rowsp-is-true-listp
  (equal (fn-hec-rowsp xs) (true-listp xs))))

(defthm fn-hec-append-preserves-concrete-invariant
  (implies (fn-history-event-pagep fn-history-event-page)
           (fn-history-event-pagep
            (mv-nth 1 (fn-hec-append epoch page-id incarnation expected event
                                     fn-history-event-page))))
  :hints (("Goal" :in-theory (enable fn-hec-append fn-history-event-pagep
                       fn-hec-committed update-fn-hec-committed
                       update-fn-hec-rowsi fn-hec-rowsp))))

(defthm fn-hec-initialize-preserves-concrete-invariant
  (implies (fn-history-event-pagep fn-history-event-page)
           (fn-history-event-pagep
            (mv-nth 1 (fn-hec-initialize epoch page-id incarnation base
                                         fn-history-event-page))))
  :hints (("Goal" :in-theory (enable fn-hec-initialize fn-history-event-pagep))))

(local (defthm fn-hec-len-append
  (equal (len (append a b)) (+ (len a) (len b)))))

(local (defthm fn-hec-len-take
  (equal (len (take n xs)) (nfix n))))

(local (defthm fn-hec-len-cons
  (equal (len (cons a b)) (1+ (len b)))))

(defthm fn-hec-append-refines-history-extension
  (implies (and (fn-hec-relatedp history fn-history-event-page)
                (equal (mv-nth 0 (fn-hec-append epoch page-id incarnation expected event
                                              fn-history-event-page)) :appended))
           (fn-hec-relatedp (append history (list event))
            (mv-nth 1 (fn-hec-append epoch page-id incarnation expected event
                                     fn-history-event-page))))
  :hints (("Goal" :in-theory (e/d (fn-hec-relatedp fn-hec-append
                         fn-history-event-pagep fn-hec-committed
                         update-fn-hec-rowsi update-fn-hec-committed fn-hec-rowsp)
                         (nth take len binary-append)))))

(defthm fn-hec-read-refines-logical-history
  (implies (and (fn-hec-relatedp history fn-history-event-page)
                (equal (mv-nth 0 (fn-hec-read epoch page-id incarnation slot captured-count
                                            fn-history-event-page)) :row))
           (equal (fn-hec-read epoch page-id incarnation slot captured-count
                               fn-history-event-page)
                  (mv :row (nth slot history))))
  :hints (("Goal" :in-theory (enable fn-hec-read fn-hec-relatedp fn-hec-committed
                                    fn-hec-rowsi)
           :use ((:instance fn-hec-nth-take (n (len history))
                           (i slot) (xs (nth 0 fn-history-event-page)))))))

(defthm fn-hec-initialize-never-rebinds-issued-page-by-definition
  (implies (not (equal (fn-hec-epoch fn-history-event-page) 0))
           (equal (fn-hec-initialize epoch page-id incarnation base fn-history-event-page)
                  (mv :stale fn-history-event-page))))

(defthm fn-hec-creator-is-empty-related
  (and (fn-history-event-pagep (create-fn-history-event-page))
       (fn-hec-relatedp nil (create-fn-history-event-page))))
