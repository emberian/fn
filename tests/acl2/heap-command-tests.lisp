; Teeth for books/heap-command (Builder M, landing 2, the observation form):
; D27's profile (1 TiB of history, the store `init --budget' writes for
; another machine) on a 16 GiB machine, the production image's core, W13's
; store of 1,000 POSTs as the observed totals.  Today's decision refuses
; both a stopped `status' and an `inspect' of it (machine-cannot-hold-
; profile); the observation form admits both, and an `inspect' while the
; header carries no totals is sized at the profile's bound (ruling (a)) and
; refused by name, saying so.
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
;; The offline adapter: a read while the header carries no totals is today's
;; decision, and its line says the adapter under-bounds the store.
(assert-event
 (equal (fn-heap-command-decide :inspect "inspect" nil *hct-d27* *hct-core* *hct-nur*
                                (list *hct-16g*) 0 nil nil *hct-img* 4096 512 (list *hct-16g*) nil)
        (fn-heap-reserve-operation-decide :inspect *hct-d27* *hct-core* *hct-nur* (list *hct-16g*) 0 nil)))
(assert-event
 (equal (fn-heap-command-line (fn-heap-command-decide :inspect "inspect" nil *hct-d27* *hct-core* *hct-nur*
                                                      (list *hct-16g*) 0 nil nil *hct-img* 4096 512
                                                      (list *hct-16g*) nil)
                              :inspect "inspect" nil nil *hct-img* 4096 512)
        (concatenate 'string
                     (fn-heap-reserve-report-line
                      (fn-heap-reserve-operation-decide :inspect *hct-d27* *hct-core* *hct-nur*
                                                        (list *hct-16g*) 0 nil))
                     *fn-mo-adapter-words* "header totals unseen")))
;; The adapter under-bounds: at the small preset the stated bound's need (the
;; equation at fn-mm-profile-bound-tot) is past the adapter's heap.
(assert-event
 (< (* *fn-heap-mib*
       (fn-heap-decision-mb (fn-heap-reserve-operation-decide :inspect *fn-heap-small-profile* *hct-core*
                                                              *hct-nur* (list *hct-1t*) 0 nil)))
    (fn-mo-read-need :inspect :reads *fn-heap-small-profile* *hct-img* *hct-nur*
                     (fn-mm-profile-bound-tot *fn-heap-small-profile* :resident) 4096)))
; IMG from /proc/self/status ("Name: sbcl", "VmRSS: 135500 kB", "RssAnon: 23552 kB")
(defconst *hct-status* '(78 97 109 101 58 9 115 98 99 108 10 86 109 82 83 83 58 9 32 32 49 51 53 53 48 48 32 107 66 10 82 115 115 65 110 111 110 58 9 32 32 32 50 51 53 53 50 32 107 66 10))
(assert-event (equal (fn-mo-img-observed 200411640 *hct-status* 1024 524288)
                     (list 200411640 (* 23552 1024) (+ (* 1024 1024) 524288))))
(assert-event (equal (fn-mo-img-observed 200411640 nil 1024 524288) nil))

;; K6.  A stopped status holds the header: init's store-less figure raised
;; by the configuration history it loads (4 KiB of it here), no store.
(defconst *hct-config* 4096)
(defconst *hct-card* 512)
(defkeystone hct-stopped-status-holds-the-header
  (implies (equal (car (fn-mo-header-decide profile core nursery observations connections config-octets))
                  :heap)
           (and (equal (car (fn-heap-reserve-operation-decide :init profile core nursery observations
                                                              connections nil))
                       :heap)
                (<= (+ (* *fn-heap-mib*
                          (fn-heap-decision-mb (fn-heap-reserve-operation-decide
                                                :init profile core nursery observations connections nil)))
                       (fn-mo-config-heap config-octets))
                    (* *fn-heap-mib*
                       (fn-heap-decision-mb (fn-mo-header-decide profile core nursery observations
                                                                 connections config-octets))))
                (<= (fn-heap-reservation-octets
                     (fn-heap-decision-mb (fn-mo-header-decide profile core nursery observations
                                                               connections config-octets))
                     core
                     (nth 4 (fn-mo-header-decide profile core nursery observations connections config-octets))
                     (nth 5 (fn-mo-header-decide profile core nursery observations connections config-octets)))
                    (fn-heap-machine-octets observations))))
  :id "PRF-10000"
  :subject fn-mo-header-decide
  :restates fn-mo-header-decide-holds-the-header
  :hyps (accepted)
  :witness ((profile *hct-d27*) (core *hct-core*) (nursery *hct-nur*) (observations (list *hct-16g*))
            (connections 0) (config-octets *hct-config*))
  :breaks ((accepted ((profile *hct-d27*) (core *hct-core*) (nursery *hct-nur*)
                      (observations (list *hct-256m*)) (connections 0) (config-octets *hct-config*))))
  :mutations ((configuration-history-uncharged
               (:conclusion (equal (fn-heap-decision-mb (fn-mo-header-decide profile core nursery observations
                                                                             connections config-octets))
                                   (fn-heap-decision-mb (fn-heap-reserve-operation-decide
                                                         :init profile core nursery observations
                                                         connections nil))))
               ((profile *hct-d27*) (core *hct-core*) (nursery *hct-nur*) (observations (list *hct-16g*))
                (connections 0) (config-octets *hct-config*))
               :fault "a stopped status sized as init with the configuration history it loads uncharged (Codex F2)"))
  :hints (("Goal" :by fn-mo-header-decide-holds-the-header)))

; The dispatch, and the tooth against today: the same stopped status of
; D27's store, refused by today's figure, is the header's decision, accepted.
(assert-event (equal (fn-heap-command-decide :status "status" nil *hct-d27* *hct-core* *hct-nur*
                                             (list *hct-16g*) 0 nil nil nil *hct-config* nil nil nil)
                     (fn-mo-header-decide *hct-d27* *hct-core* *hct-nur* (list *hct-16g*) 0 *hct-config*)))
(assert-event (equal (car (fn-mo-header-decide *hct-d27* *hct-core* *hct-nur* (list *hct-16g*) 0
                                               *hct-config*))
                     :heap))
; `pins' shares the action :status and replays: a read
(assert-event (equal (fn-heap-command-growth :status "pins" nil) :reads))
(assert-event (equal (car (fn-heap-command-decide :status "pins" nil *hct-d27* *hct-core* *hct-nur*
                                                  (list *hct-16g*) 0 nil nil nil *hct-config* nil nil nil))
                     :refused))

;; K7 and K8: teeth bound to the book's theorems (critical registration:
;; repair item MEMORY-OBSERVED-BRANCH-CRITICAL).
(defteeth fn-mo-read-holds-the-observed-store
  :claim (((accepted (equal (car (fn-mo-read-decide action class profile img core nursery tot config-octets card
                                                    resident address))
                            :heap)))
          (and (natp (fn-mm-least-observation resident))
               (<= (fn-mo-read-resident action class profile img core nursery tot config-octets card)
                   (fn-mm-least-observation resident))
               (<= (+ (fn-heap-core-dynamic core)
                      (fn-mo-read-need action class profile img nursery tot config-octets))
                   (* *fn-heap-mib*
                      (fn-heap-decision-mb
                       (fn-mo-read-decide action class profile img core nursery tot config-octets card
                                          resident address))))
               (implies (natp (fn-mm-least-observation address))
                        (<= (fn-mo-read-reservation action class profile img core nursery tot config-octets)
                            (fn-mm-least-observation address)))))
  :subject fn-mo-read-decide
  :witness ((action :inspect) (class :reads) (profile *hct-d27*) (img *hct-img*) (core *hct-core*) (nursery *hct-nur*) (tot *hct-w13*)
            (config-octets *hct-config*) (card *hct-card*)
            (resident (list *hct-16g*)) (address (list *hct-1t*)))
  :breaks ((accepted ((action :inspect) (class :reads) (profile *hct-d27*) (img *hct-img*) (core *hct-core*) (nursery *hct-nur*)
                      (tot *hct-w13*) (config-octets *hct-config*) (card *hct-card*)
                      (resident (list *hct-256m*)) (address (list *hct-1t*)))))
  :mutations ((read-sized-at-the-ceilings
               (:conclusion (<= (fn-mo-read-need action class profile img nursery (hct-ceiling profile) config-octets)
                                (fn-mm-least-observation resident)))
               ((action :inspect) (class :reads) (profile *hct-d27*) (img *hct-img*) (core *hct-core*) (nursery *hct-nur*) (tot *hct-w13*)
                (config-octets *hct-config*) (card *hct-card*)
                (resident (list *hct-16g*)) (address (list *hct-1t*)))
               :fault "a read with observed totals sized by the profile's ceilings, not the store it observes")))

(defteeth fn-mo-read-refuses-only-by-the-model
  :claim (((fits (<= (fn-mo-read-resident action class profile img core nursery tot config-octets card)
                     (fn-mm-least-observation resident)))
           (address-space (or (not (natp (fn-mm-least-observation address)))
                              (<= (fn-mo-read-reservation action class profile img core nursery tot config-octets)
                                  (fn-mm-least-observation address)))))
          (equal (car (fn-mo-read-decide action class profile img core nursery tot config-octets card
                                         resident address))
                 :heap))
  :subject fn-mo-read-decide
  :witness ((action :inspect) (class :reads) (profile *hct-d27*) (img *hct-img*) (core *hct-core*) (nursery *hct-nur*) (tot *hct-w13*)
            (config-octets *hct-config*) (card *hct-card*) (resident (list *hct-16g*)) (address nil))
  :breaks ((fits ((action :inspect) (class :reads) (profile *hct-d27*) (img *hct-img*) (core *hct-core*) (nursery *hct-nur*)
                  (tot *hct-w13*) (config-octets *hct-config*) (card *hct-card*)
                  (resident (list *hct-256m*)) (address nil)))
           (address-space ((action :inspect) (class :reads) (profile *hct-d27*) (img *hct-img*) (core *hct-core*) (nursery *hct-nur*)
                           (tot *hct-w13*) (config-octets *hct-config*) (card *hct-card*)
                           (resident (list *hct-16g*)) (address (list *hct-512m*)))))
  :mutations ((held-to-the-owner-state-alone
               (:hypothesis fits (<= (fn-mm-owner tot (fn-mo-read-cfg nursery config-octets))
                                     (fn-mm-least-observation resident)))
               ((action :inspect) (class :reads) (profile *hct-d27*) (img *hct-img*) (core *hct-core*) (nursery *hct-nur*) (tot *hct-w13*)
                (config-octets *hct-config*) (card *hct-card*) (resident (list *hct-256m*)) (address nil))
               :fault "a read held to the store's owner state alone, the image and the open's workspace uncharged")))

; Codex F4's input: ten million posts on a 1 TiB machine pick a dynamic
; space whose card table alone is past the old base; it is charged.
(assert-event
 (< (fn-mo-read-need :inspect :reads *hct-d27* *hct-img* *hct-nur* (hct-posts 10000000) *hct-config*)
    (fn-mo-read-resident :inspect :reads *hct-d27* *hct-img* *hct-core* *hct-nur* (hct-posts 10000000) *hct-config*
                         *hct-card*)))

;; K7b: `post' (a writer) decided by the equation at the small preset's
;; profile bound on a 16 GiB machine holds every store within the bound
;; (W13's here), the decision the host makes once A's header carries totals.
(defconst *hct-small* *fn-heap-small-profile*)
(defconst *hct-small-bound* (fn-mm-profile-bound-tot *hct-small* :resident))
(assert-event (fn-mm-tot-le *hct-w13* *hct-small-bound*))
(assert-event (equal (fn-heap-command-decide :post "post" nil *hct-small* *hct-core* *hct-nur*
                                             (list *hct-16g*) 0 nil *hct-small-bound* *hct-img* *hct-config*
                                             *hct-card* (list *hct-16g*) (list *hct-1t*))
                     (fn-mo-read-decide :post :grows *hct-small* *hct-img* *hct-core* *hct-nur*
                                        *hct-small-bound* *hct-config* *hct-card*
                                        (list *hct-16g*) (list *hct-1t*))))
(defteeth fn-mo-read-holds-every-store-within-its-totals
  :claim (((accepted (equal (car (fn-mo-read-decide action class profile img core nursery tot config-octets
                                                    card resident address))
                            :heap))
           (within (fn-mm-tot-le a tot)))
          (and (<= (fn-mo-read-need action class profile img nursery a config-octets)
                   (fn-mm-least-observation resident))
               (<= (+ (fn-heap-core-dynamic core)
                      (fn-mo-read-need action class profile img nursery a config-octets))
                   (* *fn-heap-mib*
                      (fn-heap-decision-mb
                       (fn-mo-read-decide action class profile img core nursery tot config-octets card
                                          resident address))))))
  :subject fn-mo-read-decide
  :witness ((action :post) (class :grows) (profile *hct-small*) (img *hct-img*) (core *hct-core*)
            (nursery *hct-nur*) (tot *hct-small-bound*) (a *hct-w13*) (config-octets *hct-config*)
            (card *hct-card*) (resident (list *hct-16g*)) (address (list *hct-1t*)))
  :breaks ((accepted ((action :post) (class :grows) (profile *hct-small*) (img *hct-img*) (core *hct-core*)
                      (nursery *hct-nur*) (tot *hct-small-bound*) (a *hct-w13*)
                      (config-octets *hct-config*) (card *hct-card*) (resident (list *hct-256m*))
                      (address (list *hct-1t*))))
           (within ((action :post) (class :grows) (profile *hct-small*) (img *hct-img*) (core *hct-core*)
                    (nursery *hct-nur*) (tot *hct-small-bound*) (a (hct-posts 10000000))
                    (config-octets *hct-config*) (card *hct-card*) (resident (list *hct-16g*))
                    (address (list *hct-1t*)))))
  :mutations ((memberships-unbounded
               (:hypothesis within (<= (fn-mm-tot-records a) (fn-mm-tot-records tot)))
               ((action :post) (class :grows) (profile *hct-small*) (img *hct-img*) (core *hct-core*)
                (nursery *hct-nur*) (tot *hct-small-bound*)
                (a (fn-mm-make-tot 16384 0 0 1000000000 0 0 0 0 :resident))
                (config-octets *hct-config*) (card *hct-card*) (resident (list *hct-16g*))
                (address (list *hct-1t*)))
               :fault "an offline figure that bounds the records but not their memberships (H no longer does)")))

;; THE RUN'S LAUNCH at C' (MEMORY-RUN-LAUNCH-MODEL, ruling (b)): the small
;; preset, the image and 32-connection configuration of
;; tests/acl2/admission-memory-tests.lisp, the empty store.
(defconst *hct-run-img* (list (* 100 1048576) (* 23 1048576) 1090519))
(defconst *hct-run-cfg* (list 32 t 8388608 8388608 nil 0 8388608 16 nil 64))
(defconst *hct-run-empty* (fn-mm-make-tot 0 0 0 0 0 0 0 0 :resident))
(defun hct-mib (n) (* n 1048576))
(defun hct-run (mb address)
  (fn-mo-run-decide *hct-small* *hct-run-img* *hct-run-cfg* nil (list (hct-mib mb)) address *hct-core*
                    *hct-nur* *hct-run-empty*))
;; the small preset at 2 GiB: C' is C (32 of 32), the heap the launch's dynamic
;; space, the threads those of C'
(assert-event (equal (hct-run 2048 nil) '(:heap 2174 "small" 2048 1024 35)))
(assert-event (equal (fn-adm-capacity *hct-small* *hct-run-img* *hct-run-cfg* (hct-mib 2048) *hct-run-empty*)
                     32))
;; 230 MiB: C' is 18 of 32 and the run launches at it ...
(assert-event (equal (fn-adm-capacity *hct-small* *hct-run-img* *hct-run-cfg* (hct-mib 230) *hct-run-empty*)
                     18))
(assert-event (equal (car (hct-run 230 nil)) :heap))
(assert-event (equal (nth 5 (hct-run 230 nil)) (fn-heap-thread-count 18)))
;; ... where the launch decided at the configured C refuses: "the launch at C
;; always agrees with the launch at C'" is false.
(assert-event (equal (car (fn-mm-launch-decide *hct-small* *hct-run-img* *hct-run-cfg* nil (list (hct-mib 230))
                                               nil *hct-core* *hct-nur* *hct-run-empty*))
                     :refused))
(assert-event (not (equal (car (fn-mm-launch-decide *hct-small* *hct-run-img* *hct-run-cfg* nil
                                                    (list (hct-mib 230)) nil *hct-core* *hct-nur*
                                                    *hct-run-empty*))
                          (car (hct-run 230 nil)))))
;; 128 MiB: no connection count holds the store; read's refusal shape, MB figures
(assert-event (null (fn-adm-capacity *hct-small* *hct-run-img* *hct-run-cfg* (hct-mib 128) *hct-run-empty*)))
(assert-event (equal (hct-run 128 nil) '(:refused :machine-cannot-hold-the-store 204 128)))
(assert-event (equal (fn-heap-command-line (hct-run 128 nil) :run "run" nil nil nil nil nil)
                     "refused machine-cannot-hold-the-store need=204 MB machine=128 MB"))
;; the address space below the reservation
(assert-event (equal (hct-run 2048 (list (hct-mib 100)))
                     '(:refused :address-space-cannot-hold-the-reservation 2541 100)))
;; no resident observation: refused by name, nothing launched
(assert-event (equal (fn-mo-run-decide *hct-small* *hct-run-img* *hct-run-cfg* nil nil nil *hct-core*
                                       *hct-nur* *hct-run-empty*)
                     '(:refused :machine-memory-unobserved 0 0)))
;; no connection at all (C = 0): the gate holds with none, nothing is served
(assert-event (equal (car (fn-mo-run-decide *hct-small* *hct-run-img* (update-nth 0 0 *hct-run-cfg*) nil
                                            (list (hct-mib 2048)) nil *hct-core* *hct-nur* *hct-run-empty*))
                     :refused))

(defkeystone hct-run-holds-the-store-at-its-capacity
  (implies (equal (car (fn-mo-run-decide profile img cfg configured resident address core nursery tot))
                  :heap)
           (let* ((d (fn-mo-run-decide profile img cfg configured resident address core nursery tot))
                  (limit (fn-mm-resident-limit configured resident))
                  (c (fn-adm-capacity profile img cfg limit tot)))
             (and (posp c)
                  (<= c (fn-mm-cfg-connections cfg))
                  (natp limit)
                  (<= (fn-mm-sum profile img (fn-adm-cfg-at cfg c) tot) limit)
                  (<= (fn-mm-reopen-need profile img (fn-adm-cfg-at cfg c) tot) limit)
                  (implies (natp (fn-mm-least-observation address))
                           (<= (fn-mm-launch-reservation limit core nursery (fn-adm-cfg-at cfg c) profile)
                               (fn-mm-least-observation address)))
                  (<= (+ (fn-heap-core-dynamic core) limit)
                      (* (cadr d) *fn-heap-mib*)))))
  :id "PRF-10004"
  :rule-classes nil
  :restates fn-mo-run-decide-holds-the-store-at-its-capacity
  :hyps (accepted)
  :subject fn-mo-run-decide
  :witness ((profile *hct-small*) (img *hct-run-img*) (cfg *hct-run-cfg*) (configured nil)
            (resident (list (hct-mib 230))) (address (list (* 1024 1048576 1024))) (core *hct-core*)
            (nursery *hct-nur*) (tot *hct-run-empty*))
  :breaks ((accepted ((profile *hct-small*) (img *hct-run-img*) (cfg *hct-run-cfg*) (configured nil)
                      (resident (list (hct-mib 128))) (address (list (* 1024 1048576 1024))) (core *hct-core*)
                      (nursery *hct-nur*) (tot *hct-run-empty*))))
  :mutations ((sum-at-the-configured-connections
               (:conclusion (let* ((limit (fn-mm-resident-limit configured resident))
                                   (c (fn-adm-capacity profile img cfg limit tot)))
                              (and (posp c) (<= (fn-mm-sum profile img cfg tot) limit))))
               ((profile *hct-small*) (img *hct-run-img*) (cfg *hct-run-cfg*) (configured nil)
                (resident (list (hct-mib 230))) (address (list (* 1024 1048576 1024))) (core *hct-core*) (nursery *hct-nur*)
                (tot *hct-run-empty*))
               :fault "a launch held to the store's sum at the configured C, which the capacity line does not promise"))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use fn-mo-run-decide-holds-the-store-at-its-capacity)))

(defkeystone hct-run-refuses-only-by-the-model
  (implies (and (posp (fn-adm-capacity profile img cfg (fn-mm-resident-limit configured resident) tot))
                (or (not (natp (fn-mm-least-observation address)))
                    (<= (fn-mm-launch-reservation
                         (fn-mm-resident-limit configured resident) core nursery
                         (fn-adm-cfg-at cfg (fn-adm-capacity profile img cfg
                                                             (fn-mm-resident-limit configured resident) tot))
                         profile)
                        (fn-mm-least-observation address))))
           (equal (car (fn-mo-run-decide profile img cfg configured resident address core nursery tot))
                  :heap))
  :id "PRF-10005"
  :rule-classes nil
  :restates fn-mo-run-decide-refuses-only-by-the-model
  :hyps (capacity address-space)
  :subject fn-mo-run-decide
  :witness ((profile *hct-small*) (img *hct-run-img*) (cfg *hct-run-cfg*) (configured nil)
            (resident (list (hct-mib 230))) (address nil) (core *hct-core*) (nursery *hct-nur*)
            (tot *hct-run-empty*))
  :breaks ((capacity ((profile *hct-small*) (img *hct-run-img*) (cfg *hct-run-cfg*) (configured nil)
                      (resident (list (hct-mib 128))) (address nil) (core *hct-core*) (nursery *hct-nur*)
                      (tot *hct-run-empty*)))
           (address-space ((profile *hct-small*) (img *hct-run-img*) (cfg *hct-run-cfg*) (configured nil)
                           (resident (list (hct-mib 2048))) (address (list (hct-mib 100))) (core *hct-core*)
                           (nursery *hct-nur*) (tot *hct-run-empty*))))
  :mutations ((zero-connections-taken-as-a-capacity
               (:hypothesis capacity (natp (fn-adm-capacity profile img cfg (fn-mm-resident-limit configured resident) tot)))
               ((profile *hct-small*) (img *hct-run-img*) (cfg (update-nth 0 0 *hct-run-cfg*))
                (configured nil) (resident (list (hct-mib 2048))) (address nil) (core *hct-core*)
                (nursery *hct-nur*) (tot *hct-run-empty*))
               :fault "a capacity of no connections taken as a capacity: the run holds the store and serves nobody"))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use fn-mo-run-decide-refuses-only-by-the-model)))

;; The run's configure line: the address-space refusal is named, every other
;; case keeps the capacity line's own words.
(assert-event (equal (fn-mo-run-capacity-line (hct-run 2048 (list (hct-mib 100))) "memory capacity=32 of 32")
                     "refused address-space-cannot-hold-the-reservation reservation=2541 MB address-space=100 MB"))
(assert-event (equal (fn-mo-run-capacity-line (hct-run 2048 nil) "memory capacity=32 of 32")
                     "memory capacity=32 of 32"))
(assert-event (equal (fn-mo-run-capacity-line (hct-run 128 nil) "refused memory-cannot-hold-the-store capacity=0")
                     "refused memory-cannot-hold-the-store capacity=0"))
