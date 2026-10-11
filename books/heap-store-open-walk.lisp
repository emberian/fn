; fn: the open term's log-walk components are the walk's own bounds
; (BATCH-ENTRY-UNDER-CHARGE, Builder M).  books/heap-store-figure.lisp
; fn-heap-store-open-octets prices the walk (host/native/io.lisp
; fnn-log-stream-segment) by its entry array, at most
; fn-heap-open-entry-array-bound, and one record as a list, at most
; fn-heap-open-record-bound.  The walk runs at MAX = (fn-lgu-log-max R)
; (host/native/io.lisp fnn-store-log-max), R the profile's record octets.
; The two keystones below tie those components to what the walk reads:
; - fn-heap-open-walk-entry-within-the-term: an entry the walk reads (its
;   length fn-lgw-entry-len-bounded) within an extent of at most OU octets is
;   within the entry array component.  Its teeth's mutation is the term this
;   landing replaces (the entry priced at the chunk bound, 1 MiB + R): a
;   batch entry of 16 MiB + 42 octets refutes it, the gate that would have
;   seen the under-charge.
; - fn-heap-open-walk-record-within-the-term: each record the cursor yields of
;   an accepted entry in a buffer of at most OU octets is within the record
;   component (L's KEYSTONE fn-lgb-span-within-max at that MAX).

(in-package "ACL2")
(include-book "heap-store-figure")
(include-book "store-log-buffer")
(include-book "store-log-entry-bound")
(include-book "store-log-durable")

(local
 (defthm fn-hsow-span-len-within-the-buffer
   (<= (mv-nth 1 (fn-lgb-span i fn-octets)) (fn-octets-len fn-octets))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-lgb-span)))))

(local
 (defthm fn-hsow-span-len-natp
   (natp (mv-nth 1 (fn-lgb-span i fn-octets)))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-lgb-span)))))

(defthm fn-heap-open-walk-record-within-the-term
  (implies (and (< (nfix j)
                   (mv-nth 1 (fn-lgb-decide-count
                              prev (fn-lgu-log-max (fn-bs-profile-max-record-octets profile)) fn-octets)))
                (<= (fn-octets-len fn-octets) (nfix ou)))
           (<= (mv-nth 1 (fn-lgb-span (fn-lgb-span-cursor j 42 fn-octets) fn-octets))
               (fn-heap-open-record-bound profile ou)))
  :hints (("Goal" :in-theory (union-theories '(fn-heap-open-record-bound fn-lgu-log-max nfix min
                                                 (:type-prescription fn-hsow-span-len-natp))
                                               (theory 'minimal-theory))
           :use ((:instance fn-lgb-span-within-max
                            (max (fn-lgu-log-max (fn-bs-profile-max-record-octets profile))))
                 (:instance fn-hsow-span-len-within-the-buffer
                            (i (fn-lgb-span-cursor j 42 fn-octets)))))))

(local
 (defthm fn-hsow-entry-len-within-extent-and-bound
   (let ((n (fn-lgw-entry-len-bounded h st extent max)))
     (implies n
              (and (natp n)
                   (<= n (nfix extent))
                   (<= n (fn-lg-entry-len-bound h max)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-lgw-entry-len-bounded fn-lgw-entry-len)))))

(local
 (defthm fn-hsow-entry-len-bound-at-the-log-max
   (<= (fn-lg-entry-len-bound h (fn-lgu-log-max r))
       (+ *fn-frame-overhead-octets*
          (max *fn-lg-batch-payload-max* (+ (nfix r) *fn-frame-trailer-octets*))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-lg-entry-len-bound fn-lg-open-bound fn-lgu-log-max)))))

(defthm fn-heap-open-walk-entry-within-the-term
  (let ((n (fn-lgw-entry-len-bounded h st extent
                                     (fn-lgu-log-max (fn-bs-profile-max-record-octets profile)))))
    (implies (and n (<= (nfix extent) (nfix ou)))
             (<= n (fn-heap-open-entry-array-bound profile ou))))
  :hints (("Goal" :in-theory (union-theories '(fn-heap-open-entry-array-bound min max nfix)
                                             (theory 'minimal-theory))
           :use ((:instance fn-hsow-entry-len-within-extent-and-bound
                            (max (fn-lgu-log-max (fn-bs-profile-max-record-octets profile))))
                 (:instance fn-hsow-entry-len-bound-at-the-log-max
                            (r (fn-bs-profile-max-record-octets profile)))))))
