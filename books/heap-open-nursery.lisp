; The collector's trigger while a store opens, sized to the store it opens
; (lane f1-bisect, F1: the 1,000-post reopen's peak).
;
; An open (the owner's recovery, and every offline verb that replays)
; allocates in proportion to the store it reads: on the d5ab87aec image a
; 1,000 x 2 KiB store (4,388,380 octets on disk) conses 81.5 MB through the
; open, most of it in the checkpoint's decode.  At the figure's trigger
; (`fn-heap-nursery-trigger', max(8 MiB, min(cap, a sixteenth of the dynamic
; space)); when this was measured the cap was 64 MiB, so 48.75 MiB at the small
; profile's 780 MB figure; since MEM-007 the cap is 8 MiB and the trigger is
; exactly 8 MiB at every reservation) that garbage piles up to
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
; the larger of 8 MiB and 4 x that history: an open's collector room is
; within the memory equation's (books/memory-model.lisp fn-mm-collector at
; the trigger in force).

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

(in-theory (disable fn-heap-open-nursery-trigger))
