; Witnesses for books/memory-model (Builder M, landing 1, statements):
; per keystone one reachable witness (every hypothesis and the conclusion
; hold) and, per hypothesis, a removal witness (the others hold, it fails,
; and the conclusion fails).  The figures are the small preset's over the
; production image's measured floor (MEMORY-20261006 2.1 and 2.4: about
; 100 MiB of core pages resident after the open, 23 MiB anonymous at an
; empty open, 1.04 MiB a thread at --tls-limit 65536).
(in-package "ACL2")
(include-book "../../books/memory-model")
(include-book "std/testing/assert-bang" :dir :system)

(defconst *mmt-p* *fn-heap-small-profile*)
(defconst *mmt-img* (list (* 100 1048576) (* 23 1048576) 1090519))
(defconst *mmt-img-big* (list (* 101 1048576) (* 23 1048576) 1090519))
(defconst *mmt-cfg* (list 32 t 8388608 8388608 nil 0))
(defconst *mmt-t0* (fn-mm-make-tot 0 0 0 0 :resident))
; W13's store: 1,000 POSTs of 2,048 octets, 600 header octets of which 40
; are the Message-ID, one group each.
(defconst *mmt-t1k* (fn-mm-make-tot 1000 2048000 (* 1000 (+ (* 8 600) (* 12 40))) 1000 :resident))
(defconst *mmt-worst* (fn-mm-worst-record *mmt-p*))

(defun mmt-img-le (a b)
  (and (<= (fn-mm-img-file a) (fn-mm-img-file b))
       (<= (fn-mm-img-anon a) (fn-mm-img-anon b))
       (<= (fn-mm-img-thread a) (fn-mm-img-thread b))))

; ---------------------------------------------------------------------------
; K1 fn-mm-need-within-the-sum
(defun mmt-k1 (k s pub)
  (list (<= (nfix k) (fn-mm-cfg-connections *mmt-cfg*))
        (<= (nfix s) (fn-heap-article-slots *mmt-p*))
        (<= (fn-mm-need *mmt-p* *mmt-img* *mmt-cfg* *mmt-t1k* k s pub)
            (fn-mm-sum *mmt-p* *mmt-img* *mmt-cfg* *mmt-t1k*))))
(assert-event (equal (mmt-k1 32 (fn-heap-article-slots *mmt-p*) t) '(t t t)))
(assert-event (equal (mmt-k1 33 (fn-heap-article-slots *mmt-p*) t) '(nil t nil)))
(assert-event (equal (mmt-k1 32 (+ 1 (fn-heap-article-slots *mmt-p*)) t) '(t nil nil)))

; K2 fn-mm-sum-grows-with-the-store
(defun mmt-k2 (a b)
  (list (fn-mm-tot-le a b)
        (<= (fn-mm-sum *mmt-p* *mmt-img* *mmt-cfg* a) (fn-mm-sum *mmt-p* *mmt-img* *mmt-cfg* b))))
(assert-event (equal (mmt-k2 *mmt-t0* *mmt-t1k*) '(t t)))
(assert-event (equal (mmt-k2 *mmt-t1k* *mmt-t0*) '(nil nil)))

; K3 fn-mm-admitted-store-reopens
(defun mmt-k3 (limit hdr tot img2)
  (list (fn-mm-gate-p *mmt-p* *mmt-img* *mmt-cfg* limit tot)
        (fn-mm-tot-le hdr tot)
        (fn-mm-tot-le tot (fn-mm-tail-tot *mmt-p* hdr))
        (mmt-img-le img2 *mmt-img*)
        (and (<= (fn-mm-reopen-need *mmt-p* img2 *mmt-cfg* tot)
                 (fn-mm-reopen-sizing *mmt-p* img2 *mmt-cfg* hdr))
             (<= (fn-mm-reopen-sizing *mmt-p* img2 *mmt-cfg* hdr) (nfix limit)))))
(defconst *mmt-tot* (fn-mm-tot-add-n *mmt-t1k* *mmt-worst* 128))
(defconst *mmt-tot+1* (fn-mm-tot-add *mmt-tot* *mmt-worst*))
(defun mmt-gate-limit (tot)
  (max (fn-mm-sum *mmt-p* *mmt-img* *mmt-cfg* tot)
       (fn-mm-reopen-sizing *mmt-p* *mmt-img* *mmt-cfg* tot)))
(defconst *mmt-limit* (mmt-gate-limit *mmt-tot*))
; reachable: the checkpoint at W13's store, a full tail of worst records past it
(assert-event (equal (mmt-k3 *mmt-limit* *mmt-t1k* *mmt-tot* *mmt-img*) '(t t t t t)))
;; without the gate: a limit under the header's own sizing
(assert-event (equal (mmt-k3 (- (fn-mm-reopen-sizing *mmt-p* *mmt-img* *mmt-cfg* *mmt-t1k*) 1)
                             *mmt-t1k* *mmt-tot* *mmt-img*)
                     '(nil t t t nil)))
; without HDR within TOT: a header past the store (its sizing past the gate's)
(assert-event (equal (mmt-k3 *mmt-limit* *mmt-tot+1* *mmt-tot* *mmt-img*) '(t nil t t nil)))
; without the tail bound: 129 records past the checkpoint
(assert-event (equal (mmt-k3 (mmt-gate-limit (fn-mm-tot-add *mmt-tot* *mmt-worst*))
                             *mmt-t1k* (fn-mm-tot-add *mmt-tot* *mmt-worst*) *mmt-img*)
                     '(t t nil t nil)))
; without the image premise: the checkpoint is the store, admitted at its
; own limit, reopened on an image one MiB heavier
(assert-event (equal (mmt-k3 (mmt-gate-limit *mmt-t1k*) *mmt-t1k* *mmt-t1k* *mmt-img-big*)
                     '(t t t nil nil)))

; K4 fn-mm-launch-holds-the-store-and-the-reservation; K5 fn-mm-launch-
; refuses-only-by-the-model.  CORE the production image's (file . dynamic).
(defconst *mmt-core* '(200411640 . 114644864))
(defconst *mmt-nur* 8388608)
(defun mmt-launch (conf robs aobs)
  (fn-mm-launch-decide *mmt-p* *mmt-img* *mmt-cfg* conf robs aobs *mmt-core* *mmt-nur* *mmt-t0*))
(defun mmt-k4 (conf robs aobs)
  (let ((d (mmt-launch conf robs aobs)))
    (list (equal (car d) :launch)
          (and (natp (cadr d)) (natp (caddr d))
               (<= (fn-mm-sum *mmt-p* *mmt-img* *mmt-cfg* *mmt-t0*) (cadr d))
               (<= (fn-mm-reopen-sizing *mmt-p* *mmt-img* *mmt-cfg* *mmt-t0*) (cadr d))
               (if (posp conf) (<= (cadr d) conf) t)
               (if (posp (fn-heap-machine-octets robs))
                   (<= (cadr d) (fn-heap-machine-octets robs))
                 t)
               (if (posp (fn-heap-machine-octets aobs))
                   (<= (fn-mm-launch-reservation (cadr d) *mmt-nur* *mmt-core* *mmt-cfg* *mmt-p*)
                       (fn-heap-machine-octets aobs))
                 t)
               (<= (cadr d) (caddr d))))))
(defconst *mmt-1g* (* 1024 1048576))
(defconst *mmt-256m* (* 256 1048576))
; L-FRESH at 1 GB: a cgroup memory.max of 1 GiB, no address-space limit:
; the reservation (over 1 GiB: the dynamic space at the limit, the core,
; the threads' stacks and runtime areas) is compared with nothing resident.
(assert-event (equal (mmt-k4 nil (list *mmt-1g*) nil) '(t t)))
(assert-event (< *mmt-1g* (fn-mm-launch-reservation *mmt-1g* *mmt-nur* *mmt-core* *mmt-cfg* *mmt-p*)))
; A cgroup of 900 MiB: today's decision refuses it by the threads'
; reservation (575 MiB of dynamic space, the core file and 34 threads of
; 5 MiB against a RESIDENT limit); the model launches it.
(defconst *mmt-900m* (* 900 1048576))
(assert-event (equal (car (fn-heap-reserve-decide *mmt-p* *mmt-core* *mmt-nur* (list *mmt-900m*) 32))
                     :refused))
(assert-event (equal (car (mmt-launch nil (list *mmt-900m*) nil)) :launch))
; removal of the one hypothesis: a refused launch states no limit
(assert-event (equal (mmt-k4 (* 128 1048576) nil nil) '(nil nil)))
; L-FRESH at 256 MB is refused BY THE MODEL at today's terms: the empty
; small store's sum at C = 32 is past it (the figure the landing reports).
(assert-event (equal (cadr (mmt-launch nil (list *mmt-256m*) nil))
                     :configured-memory-cannot-hold-the-store))

(defun mmt-k5 (conf robs aobs)
  (let ((limit (fn-mm-resident-limit conf robs)))
    (list (fn-mm-gate-p *mmt-p* *mmt-img* *mmt-cfg* limit *mmt-t0*)
          (or (not (posp (fn-heap-machine-octets aobs)))
              (<= (fn-mm-launch-reservation limit *mmt-nur* *mmt-core* *mmt-cfg* *mmt-p*)
                  (fn-heap-machine-octets aobs)))
          (equal (car (mmt-launch conf robs aobs)) :launch))))
(assert-event (equal (mmt-k5 nil (list *mmt-1g*) nil) '(t t t)))
(assert-event (equal (mmt-k5 nil (list *mmt-256m*) nil) '(nil t nil)))
(assert-event (equal (mmt-k5 nil (list *mmt-1g*) (list *mmt-1g*)) '(t nil nil)))

; The figures the READY reports (evaluated, not asserted against a bar).
(value-triple
 (list :base (fn-mm-base *mmt-img* *mmt-cfg*)
       :owner-empty (fn-mm-owner *mmt-t0* *mmt-cfg*)
       :owner-w13 (fn-mm-owner *mmt-t1k* *mmt-cfg*)
       :connections (* 32 (fn-mm-connection *mmt-p* *mmt-cfg*))
       :inflight (fn-mm-inflight *mmt-p*)
       :maintenance-w13 (fn-mm-maintenance *mmt-t1k* *mmt-cfg*)
       :sum-empty (fn-mm-sum *mmt-p* *mmt-img* *mmt-cfg* *mmt-t0*)
       :sum-w13 (fn-mm-sum *mmt-p* *mmt-img* *mmt-cfg* *mmt-t1k*)
       :reopen-sizing-w13 (fn-mm-reopen-sizing *mmt-p* *mmt-img* *mmt-cfg* *mmt-t1k*)))
