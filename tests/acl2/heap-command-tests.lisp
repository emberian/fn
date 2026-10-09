; Teeth for books/heap-command (Builder M, landing 2, the observation form):
; D27's profile (1 TiB of history, the store `init --budget' writes for
; another machine) on a 16 GiB machine, the production image's core, W13's
; store of 1,000 POSTs as the observed totals.  Today's decision refuses
; both a stopped `status' and an `inspect' of it (machine-cannot-hold-
; profile, 69,306,331 MB); the observation form admits both.
(in-package "ACL2")
(include-book "../../books/heap-command")
(include-book "../../books/defkeystone")
(include-book "std/testing/assert-bang" :dir :system)

(defconst *hct-core* '(200411640 . 114644864))
(defconst *hct-nur* 8388608)
(defconst *hct-16g* (* 16 1024 1048576))
(defconst *hct-1t* (* 1024 1024 1048576))
(defconst *hct-256m* (* 256 1048576))
(defconst *hct-512m* (* 512 1048576))
(defconst *hct-d27* *fn-bs-profile-defaults*)
; the probe's image: the core file, 23 MiB of RssAnon, a 1 MiB stack and
; 512 KiB of thread-local storage a thread
(defconst *hct-img* (list 200411640 (* 23 1048576) (+ (* 1024 1024) 524288)))
(defun hct-posts (k)
  (let ((hc (* k (+ (* 8 600) (* 12 40)))))
    (fn-mm-make-tot k (* k 2048) hc k 0 (* k 2300) (* k 2400) (+ (* k 2048) hc (* k 320))
                    :resident)))
(defconst *hct-w13* (hct-posts 1000))
; what an observer at the profile's ceilings would charge: T records and H
; of history in every octet field
(defun hct-ceiling (profile)
  (let ((tt (nfix (fn-bs-profile-max-transactions profile)))
        (h (nfix (fn-bs-profile-max-history-octets profile))))
    (fn-mm-make-tot tt h h (floor h 320) 0 h h h :resident)))

; The teeth's against today: the same store refused by today's decision.
(assert-event (equal (car (fn-heap-reserve-operation-decide :status *hct-d27* *hct-core* *hct-nur*
                                                            (list *hct-16g*) 0 nil))
                     :refused))
(assert-event (equal (car (fn-heap-reserve-operation-decide :inspect *hct-d27* *hct-core* *hct-nur*
                                                            (list *hct-16g*) 0 nil))
                     :refused))
; The line a read prints while the header carries no totals.
(assert-event
 (equal (fn-heap-command-line (fn-heap-command-decide :inspect nil *hct-d27* *hct-core* *hct-nur*
                                                      (list *hct-16g*) 0 nil nil nil nil nil)
                              :inspect nil nil nil)
        "refused machine-cannot-hold-profile heap=69306331 MB machine=16384 MB totals=unobserved:arena,hcharge,memberships,events,log,history,charge,residency"))
; IMG from /proc/self/status ("Name: sbcl", "VmRSS: 135500 kB", "RssAnon: 23552 kB")
(defconst *hct-status* '(78 97 109 101 58 9 115 98 99 108 10 86 109 82 83 83 58 9 32 32 49 51 53 53 48 48 32 107 66 10 82 115 115 65 110 111 110 58 9 32 32 32 50 51 53 53 50 32 107 66 10))
(assert-event (equal (fn-mo-img-observed 200411640 *hct-status* 1024 524288)
                     (list 200411640 (* 23552 1024) (+ (* 1024 1024) 524288))))
(assert-event (equal (fn-mo-img-observed 200411640 nil 1024 524288) nil))

; K6.  A stopped status holds no store.
(defkeystone hct-stopped-status-holds-no-store
  (implies (not replayp)
           (equal (fn-heap-command-decide :status replayp profile core nursery observations connections
                                          observed totals img resident address)
                  (fn-heap-reserve-operation-decide :init profile core nursery observations connections nil)))
  :id "PRF-10000"
  :subject fn-heap-command-decide
  :restates fn-heap-stopped-status-holds-no-store
  :hyps (stopped)
  :witness ((replayp nil) (profile *hct-d27*) (core *hct-core*) (nursery *hct-nur*)
            (observations (list *hct-16g*)) (connections 0) (observed nil) (totals nil) (img nil)
            (resident nil) (address nil))
  :breaks ((stopped ((replayp t) (profile *hct-d27*) (core *hct-core*) (nursery *hct-nur*)
                     (observations (list *hct-16g*)) (connections 0) (observed nil) (totals nil) (img nil)
                     (resident nil) (address nil))))
  :mutations ((status-sized-as-the-profiles-store
               (:conclusion (equal (fn-heap-command-decide :status replayp profile core nursery observations
                                                           connections observed totals img resident address)
                                   (fn-heap-reserve-operation-decide :status profile core nursery observations
                                                                     connections nil)))
               ((replayp nil) (profile *hct-d27*) (core *hct-core*) (nursery *hct-nur*)
                (observations (list *hct-16g*)) (connections 0) (observed nil) (totals nil) (img nil)
                (resident nil) (address nil))
               :fault "a stopped status sized as the profile's store (OPERATOR-STATUS-OBSERVED-SIZING: refused at 69,306,331 MB)"))
  :hints (("Goal" :by fn-heap-stopped-status-holds-no-store)))

; K7 and K8': teeth bound to the book's theorems; registered as critical
; keystones in A's landing-2 train, when the observed branch first runs on
; a host (repair item MEMORY-OBSERVED-BRANCH-CRITICAL).
; K7.  An accepted read holds the observed store.
(defteeth fn-mo-read-holds-the-observed-store
  :claim (((accepted (equal (car (fn-mo-read-decide profile img core nursery totals resident address)) :heap)))
          (and (natp (fn-mm-least-observation resident))
               (<= (fn-mo-read-need profile img nursery totals) (fn-mm-least-observation resident))
               (<= (+ (fn-heap-core-dynamic core) (fn-mo-read-need profile img nursery totals))
                   (* *fn-heap-mib*
                      (fn-heap-decision-mb
                       (fn-mo-read-decide profile img core nursery totals resident address))))
               (implies (natp (fn-mm-least-observation address))
                        (<= (fn-mo-read-reservation profile img core nursery totals)
                            (fn-mm-least-observation address)))))
  :subject fn-mo-read-decide
  :witness ((profile *hct-d27*) (img *hct-img*) (core *hct-core*) (nursery *hct-nur*) (totals *hct-w13*)
            (resident (list *hct-16g*)) (address (list *hct-1t*)))
  :breaks ((accepted ((profile *hct-d27*) (img *hct-img*) (core *hct-core*) (nursery *hct-nur*)
                      (totals *hct-w13*) (resident (list *hct-256m*)) (address (list *hct-1t*)))))
  :mutations ((read-sized-at-the-ceilings
               (:conclusion (<= (fn-mo-read-need profile img nursery (hct-ceiling profile))
                                (fn-mm-least-observation resident)))
               ((profile *hct-d27*) (img *hct-img*) (core *hct-core*) (nursery *hct-nur*) (totals *hct-w13*)
                (resident (list *hct-16g*)) (address (list *hct-1t*)))
               :fault "a read sized by the profile's ceilings, not the store it observes (today's figure)"))
)

; K8.  A read refuses only by the resident and address-space observations.
(defteeth fn-mo-read-refuses-only-by-the-model
  :claim (((fits (<= (fn-mo-read-need profile img nursery totals) (fn-mm-least-observation resident)))
           (address-space (or (not (natp (fn-mm-least-observation address)))
                              (<= (fn-mo-read-reservation profile img core nursery totals)
                                  (fn-mm-least-observation address)))))
          (equal (car (fn-mo-read-decide profile img core nursery totals resident address)) :heap))
  :subject fn-mo-read-decide
  :witness ((profile *hct-d27*) (img *hct-img*) (core *hct-core*) (nursery *hct-nur*) (totals *hct-w13*)
            (resident (list *hct-16g*)) (address nil))
  :breaks ((fits ((profile *hct-d27*) (img *hct-img*) (core *hct-core*) (nursery *hct-nur*)
                  (totals *hct-w13*) (resident (list *hct-256m*)) (address nil)))
           (address-space ((profile *hct-d27*) (img *hct-img*) (core *hct-core*) (nursery *hct-nur*)
                           (totals *hct-w13*) (resident (list *hct-16g*)) (address (list *hct-512m*)))))
  :mutations ((held-to-the-owner-state-alone
               (:hypothesis fits (<= (fn-mm-owner totals (fn-mo-read-cfg nursery))
                                     (fn-mm-least-observation resident)))
               ((profile *hct-d27*) (img *hct-img*) (core *hct-core*) (nursery *hct-nur*) (totals *hct-w13*)
                (resident (list *hct-256m*)) (address nil))
               :fault "a read held to the store's owner state alone, the image and the open's workspace uncharged"))
)
