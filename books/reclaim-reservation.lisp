; The live reclaim's reservation: the operator's opt-in
; (`[resources] reclaim_live = true'; lane reclaim-funding section 11,
; ember's ruling 2026-10-04).  Like the cold-read pool (cold-read-
; reservation.lisp) and the output pool (output-reservation.lisp) it extends
; the already composed store decision once, and only on the operator's word:
; without the key the decision is the store's, byte for byte, and a live
; reclaim is refused by name (books/owner-reclaim-pass.lisp
; fn-orcp-request-word); with it the dynamic space grows by the owner's work
; reserve beyond the open's transient (books/heap-store-figure.lisp
; fn-heap-reclaim-excess-octets) and holds the live figure.
(in-package "ACL2")
(include-book "cold-read-reservation")

; PROFILE and OBSERVED are the ones the base decision was made over (the
; operation's store and its observation); the excess is computed at the same
; observation as the open's term, so open + excess is the larger of the open
; and the reclaim (fn-heap-open-and-excess-is-the-larger).
(defun fn-rrv-extra-octets (profile observed)
  (declare (xargs :guard t))
  (fn-heap-reclaim-excess-octets profile
                                 (fn-heap-open-octets-bound profile observed)
                                 (fn-heap-open-records-bound profile observed)))

(defun fn-rrv-extend-reservation (base live profile observed core observations)
  (declare (xargs :guard t))
  (cond ((not live) base)
        ((not (equal (fn-crv-nth 0 base) :heap)) base)
        (t
         (let* ((mb (fn-heap-mb-of
                     (fn-heap-grow-runtime-dynamic (* *fn-heap-mib* (nfix (fn-crv-nth 1 base)))
                        (fn-rrv-extra-octets profile observed)
                        (* *fn-heap-mib* (fn-profile-limit :gc-nursery-mib)))))
                (stack (nfix (fn-crv-nth 4 base)))
                (threads (nfix (fn-crv-nth 5 base)))
                (total (fn-heap-reservation-octets mb core stack threads)))
           (if (<= total (fn-heap-machine-octets observations))
               (list :heap mb (fn-crv-nth 2 base) (fn-crv-nth 3 base) stack threads)
             (list :refused :machine-cannot-hold-reclaim-reserve (fn-heap-mb-of total)
                   (fn-crv-nth 3 base)))))))

; TEETH, off: no key, no term.
(defthm fn-rrv-without-the-opt-in-is-the-base-decision
  (equal (fn-rrv-extend-reservation base nil profile observed core observations) base)
  :hints (("Goal" :in-theory (enable fn-rrv-extend-reservation))))

; An accepted launch with the opt-in fits the observed machine.
(defthm fn-rrv-accepted-launch-fits-observed-machine
  (implies (equal (fn-crv-nth 0 (fn-rrv-extend-reservation base t profile observed core observations)) :heap)
           (let ((d (fn-rrv-extend-reservation base t profile observed core observations)))
             (or (equal d base)
                 (<= (fn-heap-reservation-octets (fn-crv-nth 1 d) core
                                                 (fn-crv-nth 4 d) (fn-crv-nth 5 d))
                     (fn-heap-machine-octets observations)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-rrv-extend-reservation fn-crv-nth)
                                  (fn-heap-reservation-octets fn-heap-machine-octets fn-heap-mb-of
                                   fn-heap-grow-runtime-dynamic fn-rrv-extra-octets)))))

; The reserve is funded: an accepted opt-in launch holds the base's dynamic
; space and the owner's work reserve beyond it.
(defthm fn-rrv-accepted-launch-funds-the-reclaim-reserve
  (implies (and (equal (fn-crv-nth 0 base) :heap)
                (equal (fn-crv-nth 0 (fn-rrv-extend-reservation base t profile observed core observations))
                       :heap))
           (<= (+ (* *fn-heap-mib* (nfix (fn-crv-nth 1 base)))
                  (fn-rrv-extra-octets profile observed))
               (* *fn-heap-mib*
                  (nfix (fn-crv-nth 1 (fn-rrv-extend-reservation base t profile observed core
                                                                 observations))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-heap-mb-of-covers
                            (octets (fn-heap-grow-runtime-dynamic
                                     (* *fn-heap-mib* (nfix (fn-crv-nth 1 base)))
                                     (fn-rrv-extra-octets profile observed)
                                     (* *fn-heap-mib* (fn-profile-limit :gc-nursery-mib))))))
           :in-theory (e/d (fn-rrv-extend-reservation fn-crv-nth)
                           (fn-heap-grow-runtime-dynamic fn-heap-mb-of fn-heap-reservation-octets
                            fn-heap-machine-octets fn-rrv-extra-octets)))))

;; The arithmetic: growing a dynamic space that holds a base with its nursery
;; room by EXTRA holds the base and EXTRA with theirs.
(local
 (defthm fn-rrv-grow-holds-the-grown-base
   (implies (and (natp d) (natp b) (natp extra)
                 (<= (fn-heap-with-nursery b nursery) d))
            (<= (fn-heap-with-nursery (+ b extra) nursery)
                (fn-heap-grow-runtime-dynamic d extra nursery)))
   :hints (("Goal" :in-theory (e/d (fn-heap-grow-runtime-dynamic)
                                   (fn-heap-with-nursery fn-heap-nursery-trigger))
            :use ((:instance fn-heap-with-nursery-holds-the-trigger (base b))
                  (:instance fn-heap-with-nursery-monotone
                             (b1 (+ b extra))
                             (b2 (+ (nfix (- d (* 2 (fn-heap-nursery-trigger d nursery)))) extra))))))))

;; The mebibyte count is a natural.
(local
 (defthm fn-rrv-mib-natp
   (natp (* *fn-heap-mib* (nfix x)))
   :rule-classes :type-prescription))

;; The extended space covers the grown dynamic space.
(local
 (defthm fn-rrv-extended-covers-the-grow
   (implies (and (equal (fn-crv-nth 0 base) :heap)
                 (equal (fn-crv-nth 0 (fn-rrv-extend-reservation base t profile observed core observations))
                        :heap))
            (<= (fn-heap-grow-runtime-dynamic (* *fn-heap-mib* (nfix (fn-crv-nth 1 base)))
                                              (fn-rrv-extra-octets profile observed)
                                              (* *fn-heap-mib* (fn-profile-limit :gc-nursery-mib)))
                (* *fn-heap-mib*
                   (nfix (fn-crv-nth 1 (fn-rrv-extend-reservation base t profile observed core
                                                                  observations))))))
   :hints (("Goal"
            :use ((:instance fn-heap-mb-of-covers
                             (octets (fn-heap-grow-runtime-dynamic
                                      (* *fn-heap-mib* (nfix (fn-crv-nth 1 base)))
                                      (fn-rrv-extra-octets profile observed)
                                      (* *fn-heap-mib* (fn-profile-limit :gc-nursery-mib))))))
            :in-theory (e/d (fn-rrv-extend-reservation fn-crv-nth)
                            (fn-heap-grow-runtime-dynamic fn-heap-mb-of fn-heap-reservation-octets
                             fn-heap-machine-octets fn-rrv-extra-octets))))))

;; KEYSTONE.  The opt-in launch holds the LIVE figure.  If the base decision's
;; dynamic space holds the store figure at the nursery the host sets, the
;; extended one holds the figure with the reclaim's reserve
;; (books/heap-store-figure.lisp fn-heap-store-live-figure-octets), so K4
;; (fn-heap-store-live-figure-holds-every-store-and-its-reclaim) applies to
;; the space the node runs in.
(defthm fn-rrv-accepted-launch-holds-the-live-figure
  (implies (and (equal (fn-crv-nth 0 base) :heap)
                (equal (fn-crv-nth 0 (fn-rrv-extend-reservation base t profile observed core observations))
                       :heap)
                (<= (fn-heap-store-figure-octets profile core
                                                 (* *fn-heap-mib* (fn-profile-limit :gc-nursery-mib))
                                                 observed)
                    (* *fn-heap-mib* (nfix (fn-crv-nth 1 base)))))
           (<= (fn-heap-store-live-figure-octets profile core
                                                 (* *fn-heap-mib* (fn-profile-limit :gc-nursery-mib))
                                                 observed)
               (* *fn-heap-mib*
                  (nfix (fn-crv-nth 1 (fn-rrv-extend-reservation base t profile observed core
                                                                 observations))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-rrv-grow-holds-the-grown-base
                            (d (* *fn-heap-mib* (nfix (fn-crv-nth 1 base))))
                            (b (fn-heap-store-base-octets profile core observed))
                            (extra (fn-rrv-extra-octets profile observed))
                            (nursery (* *fn-heap-mib* (fn-profile-limit :gc-nursery-mib))))
                 fn-rrv-extended-covers-the-grow)
           :in-theory (union-theories
                       '(fn-heap-store-figure-octets fn-heap-store-live-figure-octets
                         fn-heap-store-reclaim-base-octets fn-rrv-extra-octets
                         fn-heap-store-base-octets-natp natp-compound-recognizer
                         fn-rrv-mib-natp
                         (:type-prescription fn-heap-reclaim-excess-octets-natp))
                       (theory 'minimal-theory)))))

(in-theory (disable fn-rrv-extend-reservation fn-rrv-extra-octets))
