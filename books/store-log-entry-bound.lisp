; fn: the entry length the host reads, bounded before the read (sweep
; 2026-10-03 S048).
;
; The log's stream and the damage probe ask ACL2 for the length of the
; entry at a position (books/store-log-stream.lisp fn-lgw-entry-len,
; books/store-log-damage.lisp fn-lgdm-entry-len): the header's declared
; length when the segment holds that many octets.  The header is not yet
; validated there, so one flipped bit of its u32 field, or payload octets
; that look like a header after a tear, had the host read up to the rest of
; the segment (GiBs) into one array, and the probe made an octet list of it.
; The frame open bounds the payload only after that read
; (fn-lg-open-bound: the record bound MAX, or the frame's own limit for a
; packed batch, kind 2).
;
; The host now calls the BOUNDED lengths here: NIL also when the declared
; length is past the overhead plus the bound the open would apply, decided
; from the header's own kind octet.  Nothing the stream or the probe decides
; changes: an entry that long never opens (fn-lg-entry-okp-within-bound),
; so the step over it is the step over no entry --
;   KEYSTONE fn-lgw-step-of-oversized-is-step-of-nil (the stream) and
;   KEYSTONE fn-lgdm-step-of-oversized-is-step-of-nil (the probe).
; The work and allocation of one read are at most the overhead plus that
; bound.
(in-package "ACL2")
(include-book "store-log-damage")
(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (disable (tau-system))))

; The longest entry the open could accept at a header H (its kind octet).
(defun fn-lg-entry-len-bound (h max)
  (declare (xargs :guard t))
  (+ *fn-frame-overhead-octets* (nfix (ec-call (fn-lg-open-bound h max)))))

(defun fn-lgw-entry-len-bounded (h st extent max)
  (declare (xargs :guard (true-listp st)))
  (let ((n (fn-lgw-entry-len h st extent)))
    (and n (<= n (fn-lg-entry-len-bound h max)) n)))

(defun fn-lgdm-entry-len-bounded (h ps extent max)
  (declare (xargs :guard (true-listp ps)))
  (let ((n (fn-lgdm-entry-len h ps extent)))
    (and n (<= n (fn-lg-entry-len-bound h max)) n)))

; The bounded length is the unbounded one whenever it answers.
(defthm fn-lgw-entry-len-bounded-is-entry-len
  (implies (fn-lgw-entry-len-bounded h st extent max)
           (equal (fn-lgw-entry-len-bounded h st extent max)
                  (fn-lgw-entry-len h st extent))))

(defthm fn-lgdm-entry-len-bounded-is-entry-len
  (implies (fn-lgdm-entry-len-bounded h ps extent max)
           (equal (fn-lgdm-entry-len-bounded h ps extent max)
                  (fn-lgdm-entry-len h ps extent))))

; -----------------------------------------------------------------------------
; An entry past the bound never opens.

(local
 (defthm fn-lgeb-at-mostp-is-len
   (implies (natp k) (equal (fn-cbor-at-mostp xs k) (<= (len xs) k)))
   :hints (("Goal" :in-theory (enable fn-cbor-at-mostp)))))

(local
 (defthm fn-lgeb-open-past-the-bound
   (implies (< (+ *fn-frame-overhead-octets* (nfix m)) (len e))
            (not (fn-frame-result-okp (fn-frame-open e m))))
   :hints (("Goal" :in-theory (enable fn-frame-open fn-frame-decode)))))

(defthm fn-lg-entry-okp-within-bound
  (implies (fn-lg-entry-okp e prev max)
           (<= (len e) (fn-lg-entry-len-bound e max)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-lg-entry-okp) (fn-frame-open fn-lg-open-bound))
           :use ((:instance fn-lgeb-open-past-the-bound (m (fn-lg-open-bound e max)))))))

; The kind octet is the header's: the bound at the header is the entry's.
(local
 (defthm fn-lgeb-bound-of-same-kind
   (implies (and (consp e) (consp h) (equal (nth 5 e) (nth 5 h)))
            (equal (fn-lg-entry-len-bound e max) (fn-lg-entry-len-bound h max)))
   :hints (("Goal" :in-theory (enable fn-lg-open-bound)))))

(local
 (defthm fn-lgeb-oversized-not-okp
   (implies (and (< (fn-lg-entry-len-bound h max) (len e))
                 (consp h) (equal (nth 5 e) (nth 5 h)))
            (not (fn-lg-entry-okp e prev max)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-lg-entry-okp-within-bound)
                  (:instance fn-lgeb-bound-of-same-kind))
            :in-theory (disable fn-lg-entry-okp fn-lg-entry-len-bound
                                fn-lgeb-bound-of-same-kind)))))

(local
 (defthm fn-lgeb-decide-oversized
   (implies (and (< (fn-lg-entry-len-bound h max) (len e))
                 (consp h) (equal (nth 5 e) (nth 5 h)))
            (not (mv-nth 0 (fn-lgw-decide e prev max))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-lgw-decide-is-okp-and-records)
                  (:instance fn-lgeb-oversized-not-okp))
            :in-theory (union-theories '(fn-lgw-decide-is-okp-and-records) (theory 'minimal-theory))))))

(local
 (defthm fn-lgeb-broken-oversized
   (implies (and (< (fn-lg-entry-len-bound h max) (len e))
                 (consp h) (equal (nth 5 e) (nth 5 h)))
            (not (fn-lgw-broken-slice-p e last max)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-lgeb-oversized-not-okp (prev (fn-lgs-claimed-prev e max))))
            :in-theory (union-theories '(fn-lgw-broken-slice-p) (theory 'minimal-theory))))))

(local
 (defthm fn-lgeb-nil-entry
   (and (not (mv-nth 0 (fn-lgw-decide nil prev max)))
        (not (fn-lgw-broken-slice-p nil last max)))
   :hints (("Goal" :in-theory (enable fn-lgw-decide fn-lgw-broken-slice-p fn-lg-entry-okp)))))

; KEYSTONE: the stream's step over an entry past the bound is its step over
; no entry (both stop at POS, not broken).
(defthm fn-lgw-step-of-oversized-is-step-of-nil
  (implies (and (< (fn-lg-entry-len-bound h max) (len e))
                (consp h) (equal (nth 5 e) (nth 5 h)))
           (equal (fn-lgw-step e st unit max extent)
                  (fn-lgw-step nil st unit max extent)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-lgeb-decide-oversized (prev (fn-lgw-prev st)))
                 (:instance fn-lgeb-broken-oversized (last (fn-lgw-prev st)))
                 (:instance fn-lgeb-nil-entry (prev (fn-lgw-prev st)) (last (fn-lgw-prev st))))
           :in-theory (union-theories '(fn-lgw-step) (theory 'minimal-theory)))))

; KEYSTONE: the probe's step likewise (it reads the header window H itself,
; which is unchanged).
(defthm fn-lgdm-step-of-oversized-is-step-of-nil
  (implies (and (< (fn-lg-entry-len-bound h max) (len e))
                (consp h) (equal (nth 5 e) (nth 5 h)))
           (equal (fn-lgdm-step h e ps unit max)
                  (fn-lgdm-step h nil ps unit max)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-lgeb-decide-oversized (prev (fn-lgs-claimed-prev e max)))
                 (:instance fn-lgeb-nil-entry (prev (fn-lgs-claimed-prev nil max)) (last nil)))
           :in-theory (union-theories '(fn-lgdm-step) (theory 'minimal-theory)))))

; KEYSTONES of the host-called entries: when the bounded length answers NIL
; where the unbounded one named an entry E (whose kind octet is the header
; window's), the step over E is the step over no entry (no "H is a header"
; hypothesis: the length named implies it, proved here) -- the stream and the probe the host runs with the bounded
; lengths decide exactly what they decided with the unbounded ones.
(defthm fn-lgw-entry-len-bounded-step
  (implies (and (not (fn-lgw-entry-len-bounded h st extent max))
                (equal (len e) (fn-lgw-entry-len h st extent))
                (equal (nth 5 e) (nth 5 h)))
           (equal (fn-lgw-step e st unit max extent)
                  (fn-lgw-step nil st unit max extent)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :cases ((consp h))
           :use ((:instance fn-lgw-step-of-oversized-is-step-of-nil))
           :in-theory (union-theories '(fn-lgw-entry-len-bounded fn-lgw-entry-len
                                        fn-lg-declared-len len (:type-prescription len))
                                      (theory 'minimal-theory)))))

(defthm fn-lgdm-entry-len-bounded-step
  (implies (and (not (fn-lgdm-entry-len-bounded h ps extent max))
                (equal (len e) (fn-lgdm-entry-len h ps extent))
                (equal (nth 5 e) (nth 5 h)))
           (equal (fn-lgdm-step h e ps unit max)
                  (fn-lgdm-step h nil ps unit max)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :cases ((consp h))
           :use ((:instance fn-lgdm-step-of-oversized-is-step-of-nil))
           :in-theory (union-theories '(fn-lgdm-entry-len-bounded fn-lgdm-entry-len
                                        fn-lg-declared-len len (:type-prescription len))
                                      (theory 'minimal-theory)))))

(in-theory (disable fn-lg-entry-len-bound fn-lgw-entry-len-bounded fn-lgdm-entry-len-bounded))
