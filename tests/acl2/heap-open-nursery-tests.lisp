; Teeth for books/heap-open-nursery (lane f1-bisect): the keystone
; fn-heap-open-nursery-trigger-bounds on the F1 store (1,000 x 2 KiB,
; 4,388,380 octets of history on the d5ab87aec image, the small profile's
; 780 MB figure), a history past the cap, an unobserved one and a tiny one;
; the hypothesis-removal witness for its one hypothesis; and one must-fail.
(in-package "ACL2")
(include-book "../../books/heap-open-nursery")
(include-book "must-fail-checked")
(include-book "std/testing/assert-bang" :dir :system)

(defconst *hont-d* (* 780 1024 1024))          ; the small profile's figure (MB = MiB here)
(defconst *hont-nursery* (* 64 1024 1024))     ; +fnn-gc-nursery-octets+
(defconst *hont-f1-history* 4388380)           ; journal/ + store-checkpoint.fnsc, hbox 2026-09-28

(defun hont-conclusion (d nursery history)
  (declare (xargs :mode :program))
  (let ((tr (fn-heap-open-nursery-trigger d nursery history)))
    (and (<= *fn-heap-nursery-least-octets* tr)
         (<= tr (fn-heap-nursery-trigger d nursery))
         (if (natp history)
             (<= tr (max *fn-heap-nursery-least-octets*
                         (* *fn-heap-open-garbage-per-history-octet* history)))
           t))))

; Reachable positive witnesses: the complete conclusion at each input, and
; the value the host sets.
; The F1 store: 4 x its history, under the figure's 48.75 MiB.
(assert! (equal (fn-heap-nursery-trigger *hont-d* *hont-nursery*) 51118080))
(assert! (equal (fn-heap-open-nursery-trigger *hont-d* *hont-nursery* *hont-f1-history*)
                17553520))
(assert! (hont-conclusion *hont-d* *hont-nursery* *hont-f1-history*))
; A history past the cap (40,000 x 2 KiB, F6's): the figure's trigger.
(assert! (equal (fn-heap-open-nursery-trigger *hont-d* *hont-nursery* 100000000)
                51118080))
(assert! (hont-conclusion *hont-d* *hont-nursery* 100000000))
; Unobserved: the figure's trigger.
(assert! (equal (fn-heap-open-nursery-trigger *hont-d* *hont-nursery* nil) 51118080))
(assert! (hont-conclusion *hont-d* *hont-nursery* nil))
; A fresh store: the least trigger.
(assert! (equal (fn-heap-open-nursery-trigger *hont-d* *hont-nursery* 1274)
                *fn-heap-nursery-least-octets*))
(assert! (hont-conclusion *hont-d* *hont-nursery* 1274))

; Hypothesis removal (NATP HISTORY): a history that is not a natural takes
; the figure's trigger, above 4 x the value: the retained conjuncts hold, the
; hypothesis fails, the history clause's conclusion fails.
(assert! (let ((tr (fn-heap-open-nursery-trigger *hont-d* *hont-nursery* -1)))
           (and (<= *fn-heap-nursery-least-octets* tr)
                (<= tr (fn-heap-nursery-trigger *hont-d* *hont-nursery*))
                (not (natp -1))
                (not (<= tr (max *fn-heap-nursery-least-octets*
                                 (* *fn-heap-open-garbage-per-history-octet* -1000000))))
                (not (<= (fn-heap-open-nursery-trigger *hont-d* *hont-nursery* -1000000)
                         (max *fn-heap-nursery-least-octets*
                              (* *fn-heap-open-garbage-per-history-octet* -1000000)))))))

(must-fail-checked
 (defthm hont-history-bound-without-natp
   (<= (fn-heap-open-nursery-trigger d nursery history)
       (max *fn-heap-nursery-least-octets*
            (* *fn-heap-open-garbage-per-history-octet* (ifix history))))
   :hints (("Goal" :in-theory (enable fn-heap-open-nursery-trigger
                                      fn-heap-nursery-trigger)))))
