; The collector's trigger while a store opens, sized to the store it opens
; (lane f1-bisect, F1: the 1,000-post reopen's peak).
;
; An open (the owner's recovery, and every offline verb that replays)
; allocates in proportion to the store it reads: on the d5ab87aec image a
; 1,000 x 2 KiB store (4,388,380 octets on disk) conses 81.5 MB through the
; open, most of it in the checkpoint's decode.  At the figure's trigger
; (`fn-heap-nursery-trigger', a sixteenth of the dynamic space up to 64 MiB:
; 48.75 MiB at the small profile's 780 MB figure) that garbage piles up to
; the whole trigger before the first collection, so the open's peak resident
; set is the live heap plus the trigger, whatever the store's size: a trigger
; sized to the profile, not to the use.
;
; This trigger is at most a fixed multiple of the history the open reads (the
; octets of its log segments, checkpoints and state checkpoint, observed on
; disk before the open: host/native/heap.lisp fnn-heap-history-octets), at
; least 8 MiB, and never more than the figure's trigger.  The collections an
; open makes are then about (octets consed per history octet) / 4, whatever
; the store's size; the dead memory it carries is at most 4 x its history.
; Unobserved (NIL), it is the figure's trigger.
;
; host/native/io.lisp fnn-open-nursery sets SBCL's bytes-consed-between-gcs to
; `fn-heap-open-nursery-trigger' at the start of every open (fnn-recover).
;
; KEYSTONE `fn-heap-open-nursery-trigger-bounds': the trigger is at least
; 8 MiB, at most the figure's trigger, and with an observed history at most
; the larger of 8 MiB and 4 x that history.  `fn-heap-store-figure-holds-
; every-store-at-the-open-trigger' composes it with the figure's keystone
; (books/heap-store-figure.lisp fn-heap-store-figure-holds-every-store): the
; figure holds every store at the open's trigger too.

(in-package "ACL2")
(include-book "heap-store-figure")

(defconst *fn-heap-open-garbage-per-history-octet* 4)

(defun fn-heap-open-nursery-trigger (d nursery history)
  (declare (xargs :guard t))
  (if (natp history)
      (max *fn-heap-nursery-least-octets*
           (min (fn-heap-nursery-trigger d nursery)
                (* *fn-heap-open-garbage-per-history-octet* history)))
    (fn-heap-nursery-trigger d nursery)))

(local
 (defthm fn-hon-trigger-at-least-the-least
   (<= *fn-heap-nursery-least-octets* (fn-heap-nursery-trigger d nursery))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-heap-nursery-trigger)))))

(defthm fn-heap-open-nursery-trigger-natp
  (natp (fn-heap-open-nursery-trigger d nursery history))
  :rule-classes :type-prescription)

; KEYSTONE.
(defthm fn-heap-open-nursery-trigger-bounds
  (and (<= *fn-heap-nursery-least-octets*
           (fn-heap-open-nursery-trigger d nursery history))
       (<= (fn-heap-open-nursery-trigger d nursery history)
           (fn-heap-nursery-trigger d nursery))
       (implies (natp history)
                (<= (fn-heap-open-nursery-trigger d nursery history)
                    (max *fn-heap-nursery-least-octets*
                         (* *fn-heap-open-garbage-per-history-octet* history)))))
  :rule-classes nil)

(local
 (defthm fn-hon-at-most-the-trigger
   (<= (fn-heap-open-nursery-trigger d nursery history)
       (fn-heap-nursery-trigger d nursery))
   :rule-classes :linear
   :hints (("Goal" :use fn-heap-open-nursery-trigger-bounds))))

(local
 (defthm fn-hon-store-need-monotone-in-the-trigger
   (implies (<= (nfix t1) (nfix t2))
            (<= (fn-heap-store-need profile core used n m ou on t1)
                (fn-heap-store-need profile core used n m ou on t2)))
   :rule-classes nil
   :hints (("Goal" :in-theory (union-theories '(fn-heap-store-need nfix)
                                              (theory 'minimal-theory))))))

;; The trigger is a natural, so NFIX leaves it (the composition below runs in
;; the minimal theory).
(local
 (defthm fn-hon-nfix-of-open-trigger
   (equal (nfix (fn-heap-open-nursery-trigger d nursery history))
          (fn-heap-open-nursery-trigger d nursery history))))

; The figure holds every store at the open's trigger: the keystone of
; books/heap-store-figure.lisp at the figure's trigger, which bounds this one.
(defthm fn-heap-store-figure-holds-every-store-at-the-open-trigger
  (implies (and (natp d)
                (<= (fn-heap-store-figure-octets profile core nursery observed) d)
                (<= (nfix used) (nfix (fn-bs-profile-max-history-octets profile)))
                (<= (nfix n) (nfix (fn-bs-profile-max-transactions profile)))
                (<= (* *fn-sbud-membership-octets* (nfix m))
                    (nfix (fn-bs-profile-max-history-octets profile)))
                (<= (nfix ou) (fn-heap-open-octets-bound profile observed))
                (<= (nfix on) (fn-heap-open-records-bound profile observed)))
           (<= (fn-heap-store-need profile core used n m ou on
                                   (fn-heap-open-nursery-trigger d nursery history))
               d))
  :hints (("Goal" :in-theory (union-theories '(fn-hon-at-most-the-trigger
                                               fn-hon-nfix-of-open-trigger
                                               fn-heap-nfix-of-nursery-trigger)
                                             (theory 'minimal-theory))
           :use (fn-heap-store-figure-holds-every-store
                 (:instance fn-hon-store-need-monotone-in-the-trigger
                            (t1 (fn-heap-open-nursery-trigger d nursery history))
                            (t2 (fn-heap-nursery-trigger d nursery)))))))

(in-theory (disable fn-heap-open-nursery-trigger))
