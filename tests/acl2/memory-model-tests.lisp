; Witnesses for books/memory-model (Builder M, landing 1, revision 3): per
; keystone one reachable witness (every hypothesis and the conclusion hold)
; and, per hypothesis, a removal witness (the others hold, it fails, and the
; conclusion fails).  The figures are the small preset's over the production
; image's measured floor (MEMORY-20261006 2.1 and 2.4: about 100 MiB of core
; pages resident after the open, 23 MiB anonymous at an empty open, 1.04 MiB
; a thread at --tls-limit 65536).  Every store here is within the small
; profile's H = 8 MiB of charged history, so each is a store the node
; admits today.
(in-package "ACL2")
(include-book "../../books/memory-model")
(include-book "std/testing/assert-bang" :dir :system)

(defconst *mmt-p* *fn-heap-small-profile*)
(defconst *mmt-img* (list (* 100 1048576) (* 23 1048576) 1090519))
(defconst *mmt-img-big* (list (* 101 1048576) (* 23 1048576) 1090519))
(defconst *mmt-cfg* (list 32 t 8388608 8388608 nil 0 8388608 16 nil 64))
(defconst *mmt-t0* (fn-mm-make-tot 0 0 0 0 0 0 0 0 :resident))
; W13's store: 1,000 POSTs of 2,048 octets, 600 header octets of which 40
; are the Message-ID, one group each, 2,300 log octets and 2,400 octets of
; padded SCC encoding a record; its checkpoint at 900 records and the 100
; past it.  CHARGE is fn-sbud-bytes-used: payload, header charge, one
; membership.
(defun mmt-posts (k)
  (let ((hc (* k (+ (* 8 600) (* 12 40)))))
    (fn-mm-make-tot k (* k 2048) hc k 0 (* k 2300) (* k 2400) (+ (* k 2048) hc (* k 320))
                    :resident)))
(defconst *mmt-t1k* (mmt-posts 1000))
(defconst *mmt-hdr* (mmt-posts 900))
(defconst *mmt-suffix* (mmt-posts 100))
; What an observer that sizes by the profile's ceilings would charge: T
; records and H of history.
(defconst *mmt-ceiling* (fn-mm-make-tot 16384 8388608 8388608 26214 0 8388608 8388608 8388608 :resident))

(assert-event (<= (fn-mm-tot-charge *mmt-t1k*) 8388608))
(assert-event (equal (fn-mm-observed-tot *mmt-hdr* *mmt-suffix*) *mmt-t1k*))

; Codex review 3's live root: 257 retention events of 64 padded octets
; each; the canonical layout is 7 pages, the incrementally built live root
; holds 8 (one relocated event-column page left in the backing); the model
; charges twice the canonical layout.
(assert-event (equal (adt-end-l (list 2056 2056 2056 2056 16448) 1) 7))
(assert-event (<= 8 (fn-mm-hroot-npages 257 16448)))

; ---------------------------------------------------------------------------
; K1 fn-mm-need-within-the-sum
(defun mmt-k1 (k s h pub)
  (list (<= (nfix k) (fn-mm-cfg-connections *mmt-cfg*))
        (<= (nfix s) (fn-heap-article-slots *mmt-p*))
        (<= (nfix h) (fn-cbud-handshake-slots (fn-mm-cfg-tlsp *mmt-cfg*) (fn-mm-cfg-handshakes *mmt-cfg*)))
        (<= (fn-mm-need *mmt-p* *mmt-img* *mmt-cfg* *mmt-t1k* k s h pub)
            (fn-mm-sum *mmt-p* *mmt-img* *mmt-cfg* *mmt-t1k*))))
(defconst *mmt-slots* (fn-heap-article-slots *mmt-p*))
(defconst *mmt-hs* (fn-cbud-handshake-slots t 16))
(assert-event (equal (mmt-k1 32 *mmt-slots* *mmt-hs* t) '(t t t t)))
(assert-event (equal (mmt-k1 33 *mmt-slots* *mmt-hs* t) '(nil t t nil)))
(assert-event (equal (mmt-k1 32 (+ 1 *mmt-slots*) *mmt-hs* t) '(t nil t nil)))
(assert-event (equal (mmt-k1 32 *mmt-slots* (+ 1 *mmt-hs*) t) '(t t nil nil)))

; K2 fn-mm-sum-grows-with-the-store
(defun mmt-k2 (a b)
  (list (fn-mm-tot-le a b)
        (<= (fn-mm-sum *mmt-p* *mmt-img* *mmt-cfg* a) (fn-mm-sum *mmt-p* *mmt-img* *mmt-cfg* b))))
(assert-event (equal (mmt-k2 *mmt-hdr* *mmt-t1k*) '(t t)))
(assert-event (equal (mmt-k2 *mmt-t1k* *mmt-hdr*) '(nil nil)))

; K3 fn-mm-admitted-store-reopens.  Run with no connection and no TLS, where
; the reopen's workspace exceeds the serving sum, so the gate's limit is the
; reopen's and each removal bites on the reopen itself.
(defconst *mmt-cfg0* (list 0 nil 8388608 8388608 nil 0 8388608 16 nil 64))
(defun mmt-k3 (limit adm tot hdr suffix img2)
  (let ((obs (fn-mm-observed-tot hdr suffix)))
    (list (fn-mm-gate-p *mmt-p* *mmt-img* *mmt-cfg0* limit adm)
          (fn-mm-tot-le tot obs)
          (fn-mm-tot-le obs adm)
          (fn-mm-img-le img2 *mmt-img*)
          (and (<= (fn-mm-reopen-need *mmt-p* img2 *mmt-cfg0* tot)
                   (fn-mm-reopen-need *mmt-p* img2 *mmt-cfg0* obs))
               (natp limit)
               (<= (fn-mm-reopen-need *mmt-p* img2 *mmt-cfg0* obs) limit)))))
(defun mmt-gate-limit (tot)
  (max (fn-mm-sum *mmt-p* *mmt-img* *mmt-cfg0* tot)
       (fn-mm-reopen-need *mmt-p* *mmt-img* *mmt-cfg0* tot)))
(defconst *mmt-limit* (mmt-gate-limit *mmt-t1k*))
(assert-event (equal *mmt-limit* (fn-mm-reopen-need *mmt-p* *mmt-img* *mmt-cfg0* *mmt-t1k*)))
; reachable: W13's store crashed after its checkpoint at 900 with 100 records
; past it (more than the fast path's K = 128 would also be read: the suffix
; is observed, not bounded), observed exactly
(assert-event (equal (mmt-k3 *mmt-limit* *mmt-t1k* *mmt-t1k* *mmt-hdr* *mmt-suffix* *mmt-img*)
                     '(t t t t t)))
; without the gate: a limit under the store's reopen
(assert-event (equal (mmt-k3 (- (fn-mm-reopen-need *mmt-p* *mmt-img* *mmt-cfg0* *mmt-t1k*) 1)
                             *mmt-t1k* *mmt-t1k* *mmt-hdr* *mmt-suffix* *mmt-img*)
                     '(nil t t t nil)))
; without TOT within the observation: an observer that reads the header
; and not the log past it
(assert-event (equal (mmt-k3 *mmt-limit* *mmt-t1k* *mmt-t1k* *mmt-hdr* *mmt-t0* *mmt-img*)
                     '(t nil t t nil)))
; without the observation within the admitted store: an observer that
; charges the profile's ceilings (today's figure's defect)
(assert-event (equal (mmt-k3 *mmt-limit* *mmt-t1k* *mmt-t1k* *mmt-ceiling* *mmt-t0* *mmt-img*)
                     '(t t nil t nil)))
; without the image premise: a reopen on an image one MiB heavier
(assert-event (equal (mmt-k3 *mmt-limit* *mmt-t1k* *mmt-t1k* *mmt-hdr* *mmt-suffix* *mmt-img-big*)
                     '(t t t nil nil)))

; K4 fn-mm-launch-holds-the-store-and-the-reservation; K5 fn-mm-launch-
; refuses-only-by-the-model.  CORE the production image's (file . dynamic).
; At C = 32 the OVER quantum's octet lists alone are 4.0 GiB of the sum
; (the figures below), so no launch below that exists; the launch witnesses
; run one connection.
(defconst *mmt-cfg1* (list 1 t 8388608 8388608 nil 0 8388608 16 nil 64))
(defconst *mmt-core* '(200411640 . 114644864))
(defconst *mmt-nur* 8388608)
(defconst *mmt-1g* (* 1024 1048576))
(defconst *mmt-256m* (* 256 1048576))
(defconst *mmt-900m* (* 900 1048576))
(defun mmt-launch (conf robs aobs)
  (fn-mm-launch-decide *mmt-p* *mmt-img* *mmt-cfg1* conf robs aobs *mmt-core* *mmt-nur* *mmt-t1k*))
(defun mmt-k4 (conf robs aobs)
  (let ((d (mmt-launch conf robs aobs))
        (r (fn-mm-least-observation robs))
        (a (fn-mm-least-observation aobs)))
    (list (equal (car d) :launch)
          (and (natp (cadr d)) (natp (caddr d))
               (<= (fn-mm-sum *mmt-p* *mmt-img* *mmt-cfg1* *mmt-t1k*) (cadr d))
               (<= (fn-mm-reopen-need *mmt-p* *mmt-img* *mmt-cfg1* *mmt-t1k*) (cadr d))
               (if (natp conf) (<= (cadr d) conf) t)
               (if (natp r) (<= (cadr d) r) t)
               (if (natp a)
                   (<= (fn-mm-launch-reservation (cadr d) *mmt-core* *mmt-nur* *mmt-cfg1* *mmt-p*) a)
                 t)
               (<= (+ (fn-heap-core-dynamic *mmt-core*) (cadr d)) (caddr d))))))
; A cgroup of 1 GiB, no address-space limit: launches with a reservation
; over 1 GiB, since nothing resident is compared with it
(assert-event (equal (mmt-k4 nil (list *mmt-1g*) nil) '(t t)))
(assert-event (< *mmt-1g* (fn-mm-launch-reservation *mmt-1g* *mmt-core* *mmt-nur* *mmt-cfg1* *mmt-p*)))
; removal of the one hypothesis: a refused launch states no limit
(assert-event (equal (mmt-k4 (* 128 1048576) nil nil) '(nil nil)))
; a resident observation of 0 is a limit, not an absent one (Codex F8)
(assert-event (equal (car (mmt-launch nil (list 0) nil)) :refused))
(assert-event (equal (car (mmt-launch nil (list *mmt-1g*) (list 0))) :refused))
; A 900 MiB cgroup: today's decision refuses it by the threads' reservation
; (575 MiB of dynamic space, the core file and 34 threads of 5 MiB against
; a RESIDENT limit); the model launches it
(assert-event (equal (car (fn-heap-reserve-decide *mmt-p* *mmt-core* *mmt-nur* (list *mmt-900m*) 32))
                     :refused))
(assert-event (equal (car (mmt-launch nil (list *mmt-900m*) nil)) :launch))
; L-FRESH at 256 MB is refused BY THE MODEL at today's terms, even at one
; connection (the figure the landing reports)
(assert-event (equal (cadr (mmt-launch nil (list *mmt-256m*) nil))
                     :configured-memory-cannot-hold-the-store))

(defun mmt-k5 (conf robs aobs)
  (let ((limit (fn-mm-resident-limit conf robs))
        (a (fn-mm-least-observation aobs)))
    (list (fn-mm-gate-p *mmt-p* *mmt-img* *mmt-cfg1* limit *mmt-t1k*)
          (or (not (natp a))
              (<= (fn-mm-launch-reservation limit *mmt-core* *mmt-nur* *mmt-cfg1* *mmt-p*) a))
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
       :over-window (fn-mm-over-window-octets *mmt-p* *mmt-cfg*)
       :inflight (fn-mm-inflight *mmt-p* *mmt-cfg*)
       :cold-reads (fn-mm-cold-reads *mmt-p* *mmt-cfg*)
       :handshakes (fn-cbud-handshake-octets t 16)
       :maintenance-w13 (fn-mm-maintenance *mmt-t1k* *mmt-cfg*)
       :sum-empty (fn-mm-sum *mmt-p* *mmt-img* *mmt-cfg* *mmt-t0*)
       :sum-w13 (fn-mm-sum *mmt-p* *mmt-img* *mmt-cfg* *mmt-t1k*)
       :reopen-w13 (fn-mm-reopen-need *mmt-p* *mmt-img* *mmt-cfg* *mmt-t1k*)
       :reopen-ceiling (fn-mm-reopen-need *mmt-p* *mmt-img* *mmt-cfg* *mmt-ceiling*)
       :sum-w13-one-connection (fn-mm-sum *mmt-p* *mmt-img* (list 1 t 8388608 8388608 nil 0 8388608 16 nil 64) *mmt-t1k*)))
