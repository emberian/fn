(in-package "ACL2")
(include-book "../../books/reclaim-reservation")
(include-book "../../books/owner-credits")
(include-book "std/testing/assert-bang" :dir :system)

; The opt-in's reservation (books/reclaim-reservation.lisp), both settings.
; The small profile (T 16,384, H 8 MiB): the owner's work reserve beyond the
; open's transient is 358,006,784 octets at the empty observation.
(defconst *rrvt-profile* *fn-heap-small-profile*)
(defconst *rrvt-base* '(:heap 640 :development 4096 1024 12))
(defconst *rrvt-core* 268435456)
(defconst *rrvt-machine* '(8589934592))

(assert-event
 (and (eq (symbol-class 'fn-rrv-extend-reservation (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-mca-figure-octets (w state)) :common-lisp-compliant)))

; OFF: no key, no term -- the decision is the base, byte for byte, on every
; machine, and the owner's reserve is the open's alone.
(assert! (equal (fn-rrv-extend-reservation *rrvt-base* nil *rrvt-profile* nil *rrvt-core* *rrvt-machine*)
                *rrvt-base*))
(assert! (equal (fn-rrv-extend-reservation *rrvt-base* nil *rrvt-profile* nil *rrvt-core* '(1))
                *rrvt-base*))
(assert! (equal (fn-mca-reclaim-reserve-octets *rrvt-profile* nil) 0))
(assert! (equal (fn-mca-owner-octets *rrvt-profile* nil)
                (fn-heap-store-open-octets *rrvt-profile*
                                           (fn-heap-open-octets-bound *rrvt-profile* nil)
                                           (fn-heap-open-records-bound *rrvt-profile* nil))))
(assert! (equal (fn-mca-figure-octets *rrvt-profile* *rrvt-core* 67108864 nil)
                (fn-heap-figure-octets *rrvt-profile* *rrvt-core* 67108864)))

; ON: the dynamic space grows by at least the owner's reserve and holds the
; live figure; the figure is the larger one.
(defconst *rrvt-on*
  (fn-rrv-extend-reservation *rrvt-base* t *rrvt-profile* nil *rrvt-core* *rrvt-machine*))
(assert! (equal (fn-crv-nth 0 *rrvt-on*) :heap))
(assert! (<= (+ (* *fn-heap-mib* 640) (fn-rrv-extra-octets *rrvt-profile* nil))
             (* *fn-heap-mib* (fn-crv-nth 1 *rrvt-on*))))
(assert! (> (fn-crv-nth 1 *rrvt-on*) 640))
(assert! (> (fn-mca-reclaim-reserve-octets *rrvt-profile* t) 0))
(assert! (equal (fn-rrv-extra-octets *rrvt-profile* nil)
                (fn-mca-reclaim-reserve-octets *rrvt-profile* t)))
(assert! (equal (fn-mca-figure-octets *rrvt-profile* *rrvt-core* 67108864 t)
                (fn-heap-store-live-figure-octets *rrvt-profile* *rrvt-core* 67108864 nil)))
(assert! (< (fn-mca-figure-octets *rrvt-profile* *rrvt-core* 67108864 nil)
            (fn-mca-figure-octets *rrvt-profile* *rrvt-core* 67108864 t)))
; The premise inhabited: a base decision that holds the store figure, and the
; extended one holds the live figure.
(defconst *rrvt-fit*
  (list :heap (fn-heap-mb-of (fn-heap-store-figure-octets *rrvt-profile* *rrvt-core* 67108864 nil))
        :development 4096 1024 12))
(assert! (<= (fn-heap-store-figure-octets *rrvt-profile* *rrvt-core* 67108864 nil)
             (* *fn-heap-mib* (fn-crv-nth 1 *rrvt-fit*))))
(assert!
 (let ((d (fn-rrv-extend-reservation *rrvt-fit* t *rrvt-profile* nil *rrvt-core* *rrvt-machine*)))
   (and (equal (fn-crv-nth 0 d) :heap)
        (<= (fn-heap-store-live-figure-octets *rrvt-profile* *rrvt-core* 67108864 nil)
            (* *fn-heap-mib* (fn-crv-nth 1 d))))))
; Premise removed (a space short of the store figure): the extended space does
; not hold the live figure.
(assert!
 (let* ((short (list :heap (- (fn-heap-mb-of (fn-heap-store-figure-octets *rrvt-profile* *rrvt-core* 67108864 nil)) 64)
                     :development 4096 1024 12))
        (d (fn-rrv-extend-reservation short t *rrvt-profile* nil *rrvt-core* *rrvt-machine*)))
   (and (equal (fn-crv-nth 0 d) :heap)
        (not (<= (fn-heap-store-live-figure-octets *rrvt-profile* *rrvt-core* 67108864 nil)
                 (* *fn-heap-mib* (fn-crv-nth 1 d)))))))
; A machine too small for the reserve is refused by name (and not accepted).
(assert!
 (let ((d (fn-rrv-extend-reservation *rrvt-base* t *rrvt-profile* nil *rrvt-core* '(134217728))))
   (equal (list (fn-crv-nth 0 d) (fn-crv-nth 1 d)) '(:refused :machine-cannot-hold-reclaim-reserve))))
; A refused base passes through untouched (the extension never hides it).
(assert! (equal (fn-rrv-extend-reservation '(:refused :x 1 2) t *rrvt-profile* nil *rrvt-core* *rrvt-machine*)
                '(:refused :x 1 2)))
