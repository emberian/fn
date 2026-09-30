; PRF-1143 actual input backing reserve census, source-only boundary.
; Native fnn-octets-fill calls fn-octets$c-reserve before REPLACE. This book
; records that exact concrete capacity transition, not a bytes-only abstract
; capacity export or an allocator/GC/workspace adequacy claim.
(in-package "ACL2")
(include-book "octets-stobj")
(include-book "cold-read-layout")

(defun fn-ibc-next-capacity (requested old-capacity)
  (declare (xargs :guard t))
  (max (nfix requested) (nfix old-capacity)))

; Retain the old backing charge throughout uncertain replacement. The source
; vector is independently retained. These selected-layout components exclude
; constructor workspace, control/graph aliases and physical retirement debt.
(defun fn-ibc-backing-components (requested old-capacity source-capacity)
  (declare (xargs :guard t))
  (list (* 2 (fn-crl-array-octets (nfix old-capacity) 1))
        (if (< (nfix old-capacity) (nfix requested))
            (* 2 (fn-crl-array-octets (nfix requested) 1)) 0)
        (* 2 (fn-crl-array-octets (nfix source-capacity) 1))))

(defthm fn-ibc-actual-reserve-capacity
  (implies (natp requested)
           (equal (fn-octets$c-buf-length
                   (fn-octets$c-reserve requested fn-octets$c))
                  (fn-ibc-next-capacity requested
                                        (fn-octets$c-buf-length fn-octets$c))))
  :hints (("Goal" :in-theory (enable fn-octets$c-reserve
                                    fn-octets$c-buf-length
                                    fn-ibc-next-capacity))))

(defthm fn-ibc-retained-old-backing-independent-of-request-by-definition
  (equal (car (fn-ibc-backing-components requested old-capacity source-capacity))
         (* 2 (fn-crl-array-octets (nfix old-capacity) 1)))
  :hints (("Goal" :in-theory (enable fn-ibc-backing-components))))
