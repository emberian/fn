; SAME registered child ONE to separately owned output storage.
; Constructor/claim/source authority and selected runtime remain unavailable.
(in-package "ACL2")
(include-book "index-range-render-active")
(include-book "octets-stobj")
(defthm fn-ohr-active-one-output-bounded
 (<= (len (mv-nth 0 (fn-ohr-active-one s fn-arena))) 1)
 :rule-classes :linear
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-npw-one-output-bounded (pieces (nth 4 s)) (pos (nth 5 s))))
  :in-theory (e/d (fn-ohr-active-one)
   (fn-npw-one fn-lpc-tick fn-obc-make fn-obc-begin fn-obc-row-ready)))))
(defthm fn-ohr-active-one-output-octets
 (implies (fn-ohr-active-p s fn-arena)
  (fn-cbor-octet-listp (mv-nth 0 (fn-ohr-active-one s fn-arena))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-npw-one-output-octets (pieces (nth 4 s)) (pos (nth 5 s))))
  :in-theory (e/d (fn-ohr-active-one fn-ohr-active-p)
   (fn-npw-one fn-npw-piecesp fn-lpc-tick fn-lpc-ready-p
    fn-obc-make fn-obc-begin fn-obc-row-ready)))))
(defthm fn-osh-one-output-octets
 (implies (fn-osh-ready-p cell fn-arena)
  (fn-cbor-octet-listp (mv-nth 0 (fn-osh-one cell fn-arena))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-ohr-active-one-output-octets (s (nth 5 cell)))
        (:instance fn-ohr-carried-active-is-active (s (nth 5 cell))))
  :in-theory (e/d (fn-osh-one fn-osh-ready-p)
   (fn-ohr-active-one fn-ohr-active-p fn-ohr-carried-p
    fn-hmid-one fn-ohr-selected-row-begin fn-osh-make fn-obc-begin fn-obc-next-range)))))
(defthm fn-osh-one-output-bounded
 (<= (len (mv-nth 0 (fn-osh-one cell fn-arena))) 1)
 :rule-classes :linear
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-ohr-active-one-output-bounded (s (nth 5 cell))))
  :in-theory (e/d (fn-osh-one)
   (fn-ohr-active-one fn-hmid-one fn-ohr-selected-row-begin
    fn-osh-make fn-obc-begin fn-obc-next-range)))))

(defthm fn-ibr-held-one-output-octets
 (implies (fn-ibr-held-current-ready-p control fn-arena)
  (fn-cbor-octet-listp (mv-nth 0 (fn-ibr-held-one control fn-arena))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-osh-one-output-octets
          (cell (fn-spp-at 4 (fn-spp-at 8 control)))))
  :in-theory (e/d (fn-ibr-held-one fn-ibr-held-current-ready-p)
   (fn-osh-one fn-osh-ready-p fn-osh-selected-source-p fn-ibr-restate
    fn-ibr-work fn-gns-number-begin fn-gns-group-selected-result)))))
(defthm fn-ibr-joint-held-one-output-octets
 (implies
  (and (fn-ibp-query-tokenp token)
       (implies (fn-ibp-query-slot-livep token fn-ibp-query-segment)
        (fn-ibr-held-current-ready-p
         (fn-ibp-qs-controlsi (nth 3 token) fn-ibp-query-segment) fn-arena)))
  (fn-cbor-octet-listp
   (mv-nth 0 (fn-ibr-joint-segment-held-one
    token fn-ibp-query-segment fn-query-payload-grants fn-arena))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-ibr-held-one-output-octets
   (control (fn-ibp-qs-controlsi (nth 3 token) fn-ibp-query-segment))))
  :in-theory (e/d (fn-ibr-joint-segment-held-one)
   (fn-ibr-joint-segment-demand fn-ibr-held-one fn-ibr-held-current-ready-p
    fn-ibp-query-tokenp fn-ibp-query-slot-livep)))))
; INTERNAL same admitted output-window storage. No native capacity/job setter.
; Actual factory must reserve/own the backing capacity BEFORE this callback;
; this book supplies no installation or physical allocation qualification.
(defun fn-ibr-joint-segment-held-output-one
 (capacity token fn-ibp-query-segment fn-query-payload-grants fn-arena fn-octets)
 (declare (xargs :stobjs
  (fn-ibp-query-segment fn-query-payload-grants fn-arena fn-octets)
  :guard (and (natp capacity) (fn-ibp-query-tokenp token)
    (implies (fn-ibp-query-slot-livep token fn-ibp-query-segment)
     (fn-ibr-held-current-ready-p
      (fn-ibp-qs-controlsi (nth 3 token) fn-ibp-query-segment) fn-arena)))
  :verify-guards nil))
 (if (<= capacity (fn-octets-len fn-octets))
  (mv :output-full fn-ibp-query-segment fn-octets)
  (mv-let (out phase fn-ibp-query-segment)
   (fn-ibr-joint-segment-held-one
    token fn-ibp-query-segment fn-query-payload-grants fn-arena)
   (let ((fn-octets (fn-octets-append-list out fn-octets)))
    (mv phase fn-ibp-query-segment fn-octets)))))
(verify-guards fn-ibr-joint-segment-held-output-one
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-ibr-joint-held-one-output-octets))
  :in-theory (e/d (fn-ibp-query-tokenp)
                     (fn-ibr-joint-segment-held-one fn-cbor-octet-listp
                      fn-ibp-query-slot-livep fn-ibr-held-current-ready-p)))))
(defthm fn-ibr-held-one-output-bounded
 (<= (len (mv-nth 0 (fn-ibr-held-one control fn-arena))) 1)
 :rule-classes :linear
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-osh-one-output-bounded
   (cell (fn-spp-at 4 (fn-spp-at 8 control)))))
  :in-theory (e/d (fn-ibr-held-one)
   (fn-osh-one fn-ibr-restate fn-ibr-work fn-gns-number-begin
    fn-gns-group-selected-result)))))
(defthm fn-ibr-joint-held-one-output-bounded
 (<= (len (mv-nth 0 (fn-ibr-joint-segment-held-one
  token fn-ibp-query-segment fn-query-payload-grants fn-arena))) 1)
 :rule-classes :linear
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-ibr-held-one-output-bounded
    (control (fn-ibp-qs-controlsi (nth 3 token) fn-ibp-query-segment))))
  :in-theory (e/d (fn-ibr-joint-segment-held-one)
   (fn-ibr-joint-segment-demand fn-ibr-held-one fn-ibp-query-slot-livep)))))


(defthm fn-ibr-held-output-one-is-actual-one-and-owned-buffer-prefix
 (let* ((answer (fn-ibr-joint-segment-held-output-one capacity token
                 fn-ibp-query-segment fn-query-payload-grants fn-arena fn-octets))
        (step (fn-ibr-joint-segment-held-one token fn-ibp-query-segment
               fn-query-payload-grants fn-arena)))
  (if (<= capacity (fn-octets-len fn-octets))
   (and (equal (mv-nth 0 answer) :output-full)
        (equal (mv-nth 1 answer) fn-ibp-query-segment)
        (equal (mv-nth 2 answer) fn-octets))
   (and (equal (mv-nth 0 answer) (mv-nth 1 step))
        (equal (mv-nth 1 answer) (mv-nth 2 step))
        (equal (fn-octets-list (mv-nth 2 answer))
          (append (fn-octets-list fn-octets) (mv-nth 0 step))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-ibr-joint-segment-held-output-one)
                 (fn-ibr-joint-segment-held-one)))))
(defthm fn-ibr-held-output-one-bounded-capacity
 (implies (and (natp capacity) (<= (fn-octets-len fn-octets) capacity))
  (<= (fn-octets-len
       (mv-nth 2 (fn-ibr-joint-segment-held-output-one capacity token
        fn-ibp-query-segment fn-query-payload-grants fn-arena fn-octets))) capacity))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-ibr-joint-held-one-output-bounded))
  :in-theory (e/d (fn-ibr-joint-segment-held-output-one)
                 (fn-ibr-joint-segment-held-one)))))
