; Teeth for books/memory-model (Builder M, landing 1, revision 3): each of
; K1-K5 carries a defteeth bound to the book's theorem, with one reachable
; witness (every hypothesis and the conclusion hold), per hypothesis a
; removal witness (the others hold, it fails, and the conclusion fails), and
; one checked mutation naming the fault it models.  The figures are the small preset's over the production
; image's measured floor (MEMORY-20261006 2.1 and 2.4: about 100 MiB of core
; pages resident after the open, 23 MiB anonymous at an empty open, 1.04 MiB
; a thread at --tls-limit 65536).  Every store here is within the small
; profile's H = 8 MiB of charged history, so each is a store the node
; admits today.
(in-package "ACL2")
(include-book "../../books/memory-model")
(include-book "../../books/defkeystone")
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
; The keystones' teeth (coordinator ruling (b), 2026-10-09), bound to the
; book's theorems as the world stores them: per keystone its reachable
; witness, one removal per hypothesis and one mutation naming the fault it
; models.
(defconst *mmt-slots* (fn-heap-article-slots *mmt-p*))
(defconst *mmt-hs* (fn-cbud-handshake-slots t 16))

; K1.  Every connection, every holder, article slot and handshake held,
; publishing; at P = 4 holders of C = 32 (contract v2.1's pool).
(defconst *mmt-cfg-p4* (list 32 t 8388608 8388608 nil 0 8388608 16 nil 64 4))
(assert-event (equal (fn-mm-cfg-holders *mmt-cfg-p4*) 4))
(assert-event (equal (fn-mm-cfg-holders *mmt-cfg*) 32))
(defteeth fn-mm-need-within-the-sum
  :claim (((connections (<= (nfix k) (fn-mm-cfg-connections cfg)))
           (holders (<= (nfix j) (fn-mm-cfg-holders cfg)))
           (slots (<= (nfix s) (fn-heap-article-slots profile)))
           (handshakes (<= (nfix h) (fn-cbud-handshake-slots (fn-mm-cfg-tlsp cfg) (fn-mm-cfg-handshakes cfg)))))
          (<= (fn-mm-need profile img cfg tot k j s h publishing)
              (fn-mm-sum profile img cfg tot)))
  :subject fn-mm-need
  :witness ((profile *mmt-p*) (img *mmt-img*) (cfg *mmt-cfg-p4*) (tot *mmt-t1k*)
                (k 32) (j 4) (s *mmt-slots*) (h *mmt-hs*) (publishing t))
  :breaks ((connections ((profile *mmt-p*) (img *mmt-img*) (cfg *mmt-cfg-p4*) (tot *mmt-t1k*)
                (k 33) (j 4) (s *mmt-slots*) (h *mmt-hs*) (publishing t)))
           (holders ((profile *mmt-p*) (img *mmt-img*) (cfg *mmt-cfg-p4*) (tot *mmt-t1k*)
                (k 32) (j 5) (s *mmt-slots*) (h *mmt-hs*) (publishing t)))
           (slots ((profile *mmt-p*) (img *mmt-img*) (cfg *mmt-cfg-p4*) (tot *mmt-t1k*)
                (k 32) (j 4) (s (+ 1 *mmt-slots*)) (h *mmt-hs*) (publishing t)))
           (handshakes ((profile *mmt-p*) (img *mmt-img*) (cfg *mmt-cfg-p4*) (tot *mmt-t1k*)
                (k 32) (j 4) (s *mmt-slots*) (h (+ 1 *mmt-hs*)) (publishing t))))
  :mutations ((sum-without-inflight
               (:conclusion (<= (fn-mm-need profile img cfg tot k j s h publishing)
                                (- (fn-mm-sum profile img cfg tot) (fn-mm-inflight profile cfg))))
               ((profile *mmt-p*) (img *mmt-img*) (cfg *mmt-cfg-p4*) (tot *mmt-t1k*)
                (k 32) (j 4) (s *mmt-slots*) (h *mmt-hs*) (publishing t))
               :fault "a sum that omits the in-flight term (capture buffers, article slots, handshakes, cold reads)")
              (sum-with-fixed-connections-only
               (:conclusion (<= (fn-mm-need profile img cfg tot k j s h publishing)
                                (- (fn-mm-sum profile img cfg tot) (fn-mm-large-pool profile cfg))))
               ((profile *mmt-p*) (img *mmt-img*) (cfg *mmt-cfg-p4*) (tot *mmt-t1k*)
                (k 32) (j 4) (s *mmt-slots*) (h *mmt-hs*) (publishing t))
               :fault "a sum that charges no connection a large reply (the holders' pool omitted)")))

; K2.  A checkpoint at 900 records within the store at 1,000.
(defteeth fn-mm-sum-grows-with-the-store
  :claim (((within (fn-mm-tot-le a b)))
          (<= (fn-mm-sum profile img cfg a) (fn-mm-sum profile img cfg b)))
  :subject fn-mm-sum
  :witness ((profile *mmt-p*) (img *mmt-img*) (cfg *mmt-cfg*) (a *mmt-hdr*) (b *mmt-t1k*))
  :breaks ((within ((profile *mmt-p*) (img *mmt-img*) (cfg *mmt-cfg*) (a *mmt-t1k*) (b *mmt-hdr*))))
  :mutations ((sum-falls-with-the-store
               (:conclusion (<= (fn-mm-sum profile img cfg b) (fn-mm-sum profile img cfg a)))
               ((profile *mmt-p*) (img *mmt-img*) (cfg *mmt-cfg*) (a *mmt-hdr*) (b *mmt-t1k*))
               :fault "a sum that charges a smaller store more (a term antitone in a total)")))

; K3.  Run with no connection and no TLS, where the reopen's workspace
; exceeds the serving sum, so the gate's limit is the reopen's and each
; removal bites on the reopen itself.  Reachable: W13's store crashed after
; its checkpoint at 900 with 100 records past it, observed exactly.
(defconst *mmt-cfg0* (list 0 nil 8388608 8388608 nil 0 8388608 16 nil 64))
(defun mmt-gate-limit (tot)
  (max (fn-mm-sum *mmt-p* *mmt-img* *mmt-cfg0* tot)
       (fn-mm-reopen-need *mmt-p* *mmt-img* *mmt-cfg0* tot)))
(defconst *mmt-limit* (mmt-gate-limit *mmt-t1k*))
(assert-event (equal *mmt-limit* (fn-mm-reopen-need *mmt-p* *mmt-img* *mmt-cfg0* *mmt-t1k*)))
(defkeystone mmt-admitted-store-reopens
  (implies (and (fn-mm-gate-p profile img cfg limit adm)
                (fn-mm-tot-le tot (fn-mm-observed-tot hdr suffix))
                (fn-mm-tot-le (fn-mm-observed-tot hdr suffix) adm)
                (fn-mm-img-le img2 img))
           (and (<= (fn-mm-reopen-need profile img2 cfg tot)
                    (fn-mm-reopen-need profile img2 cfg (fn-mm-observed-tot hdr suffix)))
                (natp limit)
                (<= (fn-mm-reopen-need profile img2 cfg (fn-mm-observed-tot hdr suffix))
                    limit)))
  :id "PRF-10001"
  :subject fn-mm-reopen-need
  :restates fn-mm-admitted-store-reopens
  :hyps (gate observes admitted image)
  :witness ((profile *mmt-p*) (img *mmt-img*) (cfg *mmt-cfg0*) (limit *mmt-limit*) (adm *mmt-t1k*)
            (tot *mmt-t1k*) (hdr *mmt-hdr*) (suffix *mmt-suffix*) (img2 *mmt-img*))
  ; gate: a limit under the store's reopen; observes: an observer that reads
  ; the header and not the log past it; admitted: an observer that charges
  ; the profile's ceilings (today's figure's defect); image: a reopen on an
  ; image one MiB heavier
  :breaks ((gate ((profile *mmt-p*) (img *mmt-img*) (cfg *mmt-cfg0*) (limit (- *mmt-limit* 1))
                  (adm *mmt-t1k*) (tot *mmt-t1k*) (hdr *mmt-hdr*) (suffix *mmt-suffix*) (img2 *mmt-img*)))
           (observes ((profile *mmt-p*) (img *mmt-img*) (cfg *mmt-cfg0*) (limit *mmt-limit*)
                      (adm *mmt-t1k*) (tot *mmt-t1k*) (hdr *mmt-hdr*) (suffix *mmt-t0*) (img2 *mmt-img*)))
           (admitted ((profile *mmt-p*) (img *mmt-img*) (cfg *mmt-cfg0*) (limit *mmt-limit*)
                      (adm *mmt-t1k*) (tot *mmt-t1k*) (hdr *mmt-ceiling*) (suffix *mmt-t0*) (img2 *mmt-img*)))
           (image ((profile *mmt-p*) (img *mmt-img*) (cfg *mmt-cfg0*) (limit *mmt-limit*)
                   (adm *mmt-t1k*) (tot *mmt-t1k*) (hdr *mmt-hdr*) (suffix *mmt-suffix*) (img2 *mmt-img-big*))))
  :mutations ((reopen-sized-from-the-header
               (:conclusion (<= (fn-mm-reopen-need profile img2 cfg tot)
                                (fn-mm-reopen-need profile img2 cfg hdr)))
               ((profile *mmt-p*) (img *mmt-img*) (cfg *mmt-cfg0*) (limit *mmt-limit*) (adm *mmt-t1k*)
                (tot *mmt-t1k*) (hdr *mmt-hdr*) (suffix *mmt-suffix*) (img2 *mmt-img*))
               :fault "a reopen sized from the checkpoint header alone, the log suffix past it unread"))
  :hints (("Goal" :by fn-mm-admitted-store-reopens)))

; K4 and K5.  CORE the production image's (file . dynamic).  At C = 32 the
; OVER quantum's octet lists alone are 4.0 GiB of the sum (the figures
; below), so no launch below that exists; the launch witnesses run one
; connection.
(defconst *mmt-cfg1* (list 1 t 8388608 8388608 nil 0 8388608 16 nil 64))
(defconst *mmt-core* '(200411640 . 114644864))
(defconst *mmt-nur* 8388608)
(defconst *mmt-1g* (* 1024 1048576))
(defconst *mmt-2g* (* 2 *mmt-1g*))
(defconst *mmt-1t* (* 1024 *mmt-1g*))
(defconst *mmt-256m* (* 256 1048576))
(defconst *mmt-900m* (* 900 1048576))
(defun mmt-launch (conf robs aobs)
  (fn-mm-launch-decide *mmt-p* *mmt-img* *mmt-cfg1* conf robs aobs *mmt-core* *mmt-nur* *mmt-t1k*))

; K4.  A configured 2 GiB under a 1 GiB cgroup and a 1 TiB address space
; launches at the cgroup's limit with a reservation over 1 GiB, since
; nothing resident is compared with it (every limit is a number so each
; conjunct runs under its guards); the removal: a configured 128 MiB the
; store does not fit is refused and states no limit.
(assert-event (< *mmt-1g* (fn-mm-launch-reservation *mmt-1g* *mmt-core* *mmt-nur* *mmt-cfg1* *mmt-p*)))
(defteeth fn-mm-launch-holds-the-store-and-the-reservation
  :claim (let ((d (fn-mm-launch-decide profile img cfg configured resident-obs address-obs
                                core nursery obs))
        (r (fn-mm-least-observation resident-obs))
        (a (fn-mm-least-observation address-obs)))
    (((launch (equal (car d) :launch)))
             (and (natp (cadr d))
                  (<= (fn-mm-sum profile img cfg obs) (cadr d))
                  (<= (fn-mm-reopen-need profile img cfg obs) (cadr d))
                  (implies (natp configured) (<= (cadr d) configured))
                  (implies (natp r) (<= (cadr d) r))
                  (implies (natp a)
                           (<= (fn-mm-launch-reservation (cadr d) core nursery cfg profile) a))
                  (<= (+ (fn-heap-core-dynamic core) (cadr d)) (caddr d)))))
  :subject fn-mm-launch-decide
  :witness ((profile *mmt-p*) (img *mmt-img*) (cfg *mmt-cfg1*) (configured *mmt-2g*)
            (resident-obs (list *mmt-1g*)) (address-obs (list *mmt-1t*)) (core *mmt-core*)
            (nursery *mmt-nur*) (obs *mmt-t1k*))
  :breaks ((launch ((profile *mmt-p*) (img *mmt-img*) (cfg *mmt-cfg1*) (configured (* 128 1048576))
                    (resident-obs nil) (address-obs nil) (core *mmt-core*) (nursery *mmt-nur*)
                    (obs *mmt-t1k*))
            :logical "a refused decision's second field is its reason, not a limit, so the conclusion's comparisons are evaluated for their logical value"))
  :mutations ((reservation-against-the-resident-limit
               (:conclusion (<= (fn-mm-launch-reservation (cadr d) core nursery cfg profile) (cadr d)))
               ((profile *mmt-p*) (img *mmt-img*) (cfg *mmt-cfg1*) (configured *mmt-2g*)
                (resident-obs (list *mmt-1g*)) (address-obs (list *mmt-1t*)) (core *mmt-core*)
                (nursery *mmt-nur*) (obs *mmt-t1k*))
               :fault "a launch that compares the address-space reservation with a resident limit (L-FRESH's refusals at 256 MB and 1 GB)")))

; K5.  A 1 GiB cgroup launches; removals: a 256 MiB cgroup the store does
; not pass the gate under, and a 1 GiB address-space limit under the
; reservation.  Mutation: a gate on the serving sum alone, at a limit
; between the sum and the reopen with no connection (where the reopen is
; the larger), which the launch refuses.
(defconst *mmt-sum0* (fn-mm-sum *mmt-p* *mmt-img* *mmt-cfg0* *mmt-t1k*))
(assert-event (< *mmt-sum0* *mmt-limit*))
(defteeth fn-mm-launch-refuses-only-by-the-model
  :claim (let ((limit (fn-mm-resident-limit configured resident-obs))
        (a (fn-mm-least-observation address-obs)))
    (((gate (fn-mm-gate-p profile img cfg limit obs))
      (address (or (not (natp a))
                   (<= (fn-mm-launch-reservation limit core nursery cfg profile) a))))
             (equal (car (fn-mm-launch-decide profile img cfg configured resident-obs
                                              address-obs core nursery obs))
                    :launch)))
  :subject fn-mm-launch-decide
  :witness ((profile *mmt-p*) (img *mmt-img*) (cfg *mmt-cfg1*) (configured nil)
            (resident-obs (list *mmt-1g*)) (address-obs nil) (core *mmt-core*) (nursery *mmt-nur*)
            (obs *mmt-t1k*))
  :breaks ((gate ((profile *mmt-p*) (img *mmt-img*) (cfg *mmt-cfg1*) (configured nil)
                  (resident-obs (list *mmt-256m*)) (address-obs nil) (core *mmt-core*) (nursery *mmt-nur*)
                  (obs *mmt-t1k*)))
           (address ((profile *mmt-p*) (img *mmt-img*) (cfg *mmt-cfg1*) (configured nil)
                     (resident-obs (list *mmt-1g*)) (address-obs (list *mmt-1g*)) (core *mmt-core*)
                     (nursery *mmt-nur*) (obs *mmt-t1k*))))
  :mutations ((gate-without-the-reopen
               (:hypothesis gate (<= (fn-mm-sum profile img cfg obs) limit))
               ((profile *mmt-p*) (img *mmt-img*) (cfg *mmt-cfg0*) (configured *mmt-sum0*)
                (resident-obs nil) (address-obs nil) (core *mmt-core*) (nursery *mmt-nur*)
                (obs *mmt-t1k*))
               :fault "a launch admitted by the serving sum alone, the store's reopen unchecked")))

; Beside the keystones: a resident observation of 0 is a limit, not an
; absent one (Codex F8); the tooth against today's decision; L-FRESH.
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

; The figures the READY reports (evaluated, not asserted against a bar).
(value-triple
 (list :base (fn-mm-base *mmt-img* *mmt-cfg*)
       :owner-empty (fn-mm-owner *mmt-t0* *mmt-cfg*)
       :owner-w13 (fn-mm-owner *mmt-t1k* *mmt-cfg*)
       :connections (fn-mm-connections *mmt-p* *mmt-cfg*)
       :connection-fixed (fn-mm-connection-fixed *mmt-p* *mmt-cfg*)
       :large-reply (fn-mm-large-reply *mmt-p* *mmt-cfg*)
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

; A-OVER-WINDOW-FIT (books/memory-model.lisp fn-mm-over-window-fit; owner
; Builder C; retirement: row O1's pool lease).  Witnesses per preset at the
; host's quantum (256) and a 20-octet server name: development's line prices
; 65,535 Xref memberships (17,579,912 octets), so W' = 1 and one holder's
; large reply is that line's list window, 562,557,184 octets, where 256 lines
; were 144,014,639,104; the default profile's W' is 1 too (a 35,656,320-octet
; window against 9,128,017,920).  The teeth: the fitted window is below the
; quantum's at both, and W' is the largest that fits (two lines do not).
(defconst *mmt-cfg-w256* (list 1 t 67108864 67108864 nil 0 0 16 256 20))
(defconst *mmt-dev-line* (fn-mm-nov-line-octets *fn-bs-profile-development* *mmt-cfg-w256*))
(assert-event (equal *mmt-dev-line* 17579912))
(assert-event (equal (fn-mm-over-window-fit *fn-bs-profile-development* *mmt-cfg-w256*) 1))
(assert-event (equal (fn-mm-large-reply *fn-bs-profile-development* *mmt-cfg-w256*) 562557184))
(assert-event (< (fn-mm-large-reply *fn-bs-profile-development* *mmt-cfg-w256*)
                 (* 2 *fn-heap-list-octets-per-octet* 256 *mmt-dev-line*)))
(assert-event (< (fn-mm-article-reply-octets *fn-bs-profile-development*)
                 (* 2 *fn-heap-list-octets-per-octet* 2 *mmt-dev-line*)))
(assert-event (equal (fn-mm-over-window-fit *fn-bs-profile-defaults* *mmt-cfg-w256*) 1))
(assert-event (equal (fn-mm-large-reply *fn-bs-profile-defaults* *mmt-cfg-w256*) 35656320))
; A quantum the article reply holds several lines of keeps them: a 128 MiB
; reply at a 1,000-octet line holds 4,194 lines, so W' is the host's 256.
(assert-event (equal (fn-mm-window-fit 256 1000 (* 2 67108864)) 256))
(assert-event (equal (fn-mm-window-fit 256 1000 100000) 3))
