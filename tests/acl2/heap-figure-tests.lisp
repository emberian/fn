; Teeth for books/heap-figure (PRF-198, re-derived by reservation-after-flip):
; the figures of the presets on the 69046a76 image's core (a natural CORE:
; the whole file counted as dynamic content) and on the production image's
; observation (FILE . DYNAMIC), the keystones' reachable witnesses and one
; counterexample and one must-fail per hypothesis, the small preset's run on
; a small machine, init's default, and the report line the host prints.
(in-package "ACL2")
(include-book "../../books/heap-figure")
(include-book "../../books/codec-attach")
(include-book "must-fail-checked")
(include-book "std/testing/assert-bang" :dir :system)

(defconst *hft-core* 389141032)              ; the 69046a76 fn-host.core
(defconst *hft-nursery* (* 64 1024 1024))    ; +fnn-gc-nursery-octets+
(defconst *hft-2g* (* 2048 *fn-heap-mib*))

;; The production image's observation (hbox, 8ee846d9a): a 200,411,640-octet
;; core holding 114,644,864 octets of dynamic content.
(defconst *hft-prod-core* '(200411640 . 114644864))
(defconst *hft-big* 132000000000)
(defconst *hft-1536* (* 1536 *fn-heap-mib*))   ; OpenBSD's default login class
(defconst *hft-700m* (* 700 *fn-heap-mib*))    ; under the small store's unobserved figure (854 MiB)

; The keystone's conclusion, and its hypotheses one by one.
(defun hft-conclusion (profile core nursery observations used n m ou on)
  (declare (xargs :mode :program))
  (let* ((decision (fn-heap-decide profile core nursery observations))
         (d (* *fn-heap-mib* (fn-heap-decision-mb decision))))
    (and (<= (fn-heap-store-need profile core used n m ou on
                                 (fn-heap-nursery-trigger d nursery))
             d)
         (<= d (fn-heap-machine-octets observations)))))

(defun hft-hyps (profile core nursery observations used n m ou on)
  (declare (xargs :mode :program))
  (list (fn-bs-profile-admittedp profile)
        (equal (car (fn-heap-decide profile core nursery observations)) :heap)
        (<= (+ (nfix used) (* *fn-sbud-membership-octets* (nfix m)))
            (nfix (fn-bs-profile-max-history-octets profile)))
        (<= (nfix n) (nfix (fn-bs-profile-max-transactions profile)))
        (<= (nfix ou) (nfix (fn-bs-profile-max-history-octets profile)))
        (<= (nfix on) (nfix (fn-bs-profile-max-transactions profile)))))

; -----------------------------------------------------------------------------
; The figures (SBCL megabytes).  The small preset at its bounds: the state of
; 16,384 records with at most H / 320 = 26,214 memberships (each charged to
; the history budget), a full replay of them and 32 articles in flight
; (lane zero-copy-commit), 1,137 MB on the 69046a76 core, 854 MB on the
; production image (1,088 and 798 before the articles; before
; membership-budget, 16 groups on every record: 1,232 and 963).  development
; is refused under 2 GiB (2,483 MB; 2,434 before the articles, 7,506 before
; membership-budget); scale is held on hbox (10,768 MB; 10,719; 173,021
; before, refused); the defaults' 2^32 - 1 records are refused everywhere
; (120,790,326 MB: the per-record term; 10,856,110,899 before).

(assert! (equal (fn-heap-figure-octets *fn-heap-small-profile* *hft-core* *hft-nursery*)
                1844957938))
(assert! (equal (fn-heap-decide *fn-heap-small-profile* *hft-core* *hft-nursery*
                                (list *hft-2g*))
                '(:heap 1760 "small" 2048)))
(assert! (equal (fn-heap-decide *fn-heap-small-profile* *hft-prod-core* *hft-nursery*
                                (list *hft-big*))
                '(:heap 1498 "small" 125885)))
(assert! (equal (fn-heap-decide *fn-bs-profile-development* *hft-core* *hft-nursery*
                                (list *hft-2g*))
                '(:refused :machine-cannot-hold-profile 2588 2048)))
(assert! (equal (fn-heap-decide *fn-bs-profile-scale* *hft-core* *hft-nursery*
                                (list *hft-big*))
                '(:heap 14126 "scale" 125885)))
(assert! (equal (fn-heap-decide *fn-bs-profile-defaults* *hft-core* *hft-nursery*
                                (list *hft-big*))
                '(:refused :machine-cannot-hold-profile 218045622 125885)))
(assert! (equal (fn-heap-decide *fn-heap-small-profile* *hft-core* *hft-nursery* nil)
                '(:refused :machine-memory-unobserved 0 0)))

; The image observation: the least of the file and the dynamic space in use.
(assert! (equal (fn-heap-core-dynamic *hft-prod-core*) 114644864))
(assert! (equal (fn-heap-core-file *hft-prod-core*) 200411640))
(assert! (equal (fn-heap-core-dynamic '(100 . 500)) 100))
(assert! (equal (fn-heap-core-dynamic 389141032) 389141032))

; The collector's trigger the host sets: a sixteenth of the space, 8 MiB at
; least, the host's 64 MiB cap at most.
(assert! (equal (fn-heap-nursery-trigger (* 256 *fn-heap-mib*) *hft-nursery*) (* 16 *fn-heap-mib*)))
(assert! (equal (fn-heap-nursery-trigger (* 64 *fn-heap-mib*) *hft-nursery*) (* 8 *fn-heap-mib*)))
(assert! (equal (fn-heap-nursery-trigger (* 4096 *fn-heap-mib*) *hft-nursery*) *hft-nursery*))

; The machine is the least positive observation.
(assert! (equal (fn-heap-machine-octets (list 132000000000 nil 0 *hft-2g* 4294967296))
                *hft-2g*))

; A cgroup's memory.max: a decimal with or without its LF; `max' is none.
(assert! (equal (fn-heap-limit-of-octets '(50 49 52 55 52 56 51 54 52 56 10)) 2147483648))
(assert! (equal (fn-heap-limit-of-octets '(50 49 52 55 52 56 51 54 52 56)) 2147483648))
(assert! (equal (fn-heap-limit-of-octets '(109 97 120 10)) nil))
(assert! (equal (fn-heap-limit-of-octets nil) nil))

; The report lines and the exit codes (outcome-class: accepted 0, refused 1).
(assert! (equal (fn-heap-report-line
                 (fn-heap-decide *fn-heap-small-profile* *hft-core* *hft-nursery*
                                 (list *hft-2g*)))
                "heap=1760 MB profile=small machine=2048 MB"))
(assert! (equal (fn-heap-report-line
                 (fn-heap-decide *fn-bs-profile-development* *hft-core* *hft-nursery*
                                 (list *hft-2g*)))
                "refused machine-cannot-hold-profile heap=2588 MB machine=2048 MB"))
(assert! (equal (fn-heap-decision-exit-code '(:heap 1924 "small" 2048)) 0))
(assert! (equal (fn-heap-decision-exit-code
                 '(:refused :machine-cannot-hold-profile 7934 2048))
                1))

; -----------------------------------------------------------------------------
; The keystone: a reachable witness with every hypothesis and the conclusion
; (the small store full to H and T, and a full replay of it), then per
; hypothesis a counterexample where the others hold, it fails, and the
; conclusion fails, and the must-fail of the theorem without it (under the
; keystone's own hints).

(defconst *hft-h* 8388608)
(defconst *hft-t* 16384)
;; The memberships of the small store full to H (lane membership-budget):
;; each is charged 320 octets of the history budget, so at most H / 320.
(defconst *hft-m* (floor *hft-h* 320))
(assert! (equal *hft-m* 26214))
(assert! (equal (fn-heap-membership-bound *fn-heap-small-profile*) *hft-m*))
;; The memberships the small store could hold before the charge: 16 groups on
;; each of its T records.
(defconst *hft-m-uncharged* (* 16 *hft-t*))
;; The witness store full to H (lane f8-reservation): the payload and the
;; memberships share the history budget, so a full store is USED payload
;; octets and M memberships with USED + 320 M = H.  Since lane heap-bounds
;; (row B2) a payload octet that is a header octet costs its header columns
;; too (32 octets, twice for the collector), so the costliest such store
;; (the model's worst case: a membership costs 640 heap octets per 320 of
;; charge, a header octet of payload 65) holds no membership and H octets of
;; payload, every one of them a header octet (min(H, T x HDR) = H).
(defconst *hft-mw* 0)
(defconst *hft-used* (- *hft-h* (* 320 *hft-mw*)))
(assert! (equal (+ *hft-used* (* 320 *hft-mw*)) *hft-h*))
(assert! (equal *hft-used* *hft-h*))

(assert! (equal (hft-hyps *fn-heap-small-profile* *hft-prod-core* *hft-nursery* (list *hft-2g*) *hft-used* *hft-t* *hft-mw* *hft-h* *hft-t*)
                '(t t t t t t)))
(assert! (hft-conclusion *fn-heap-small-profile* *hft-prod-core* *hft-nursery* (list *hft-2g*) *hft-used* *hft-t* *hft-mw* *hft-h* *hft-t*))

(defmacro hft-must-fail (name &rest hyps)
  `(must-fail-checked
    (defthm ,name
      (let* ((decision (fn-heap-decide profile core nursery observations))
             (d (* *fn-heap-mib* (fn-heap-decision-mb decision))))
        (implies (and ,@hyps)
                 (<= (fn-heap-store-need profile core used n m ou on
                                         (fn-heap-nursery-trigger d nursery))
                     d)))
      :hints (("Goal" :in-theory (e/d () (fn-heap-profile-word fn-bs-profile-admittedp
                                          fn-bs-profile-max-history-octets
                                          fn-bs-profile-max-transactions
                                          fn-heap-machine-octets fn-heap-storeless-decide))
               :use ((:instance fn-heap-mb-of-covers
                                (octets (fn-heap-figure-octets profile core nursery)))
                     (:instance fn-heap-store-figure-holds-every-store
                                (observed nil)
                                (d (* *fn-heap-mib*
                                      (fn-heap-mb-of (fn-heap-figure-octets profile core
                                                                            nursery)))))))))))

; Without the admitted profile: no profile, whose decision is the store-less
; figure: a 100 MiB image, no nursery cap, a machine of exactly its room; the
; heap is the image, and the collector's 8 MiB least trigger does not fit.
(assert! (equal (hft-hyps nil (* 100 *fn-heap-mib*) 0 (list (* 206 *fn-heap-mib*)) 0 0 0 0 0)
                '(nil t t t t t)))
(assert! (not (hft-conclusion nil (* 100 *fn-heap-mib*) 0 (list (* 206 *fn-heap-mib*)) 0 0 0 0 0)))
(hft-must-fail hft-without-admitted
               (equal (car decision) :heap)
               (<= (+ (nfix used) (* *fn-sbud-membership-octets* (nfix m))) (nfix (fn-bs-profile-max-history-octets profile)))
               (<= (nfix n) (nfix (fn-bs-profile-max-transactions profile)))
               (<= (nfix ou) (nfix (fn-bs-profile-max-history-octets profile)))
               (<= (nfix on) (nfix (fn-bs-profile-max-transactions profile))))

; Without the accepted decision: the small store on 700 MiB, refused.
(assert! (equal (hft-hyps *fn-heap-small-profile* *hft-prod-core* *hft-nursery* (list *hft-700m*) *hft-used* *hft-t* *hft-mw* *hft-h* *hft-t*)
                '(t nil t t t t)))
(assert! (not (hft-conclusion *fn-heap-small-profile* *hft-prod-core* *hft-nursery* (list *hft-700m*) *hft-used* *hft-t* *hft-mw* *hft-h* *hft-t*)))
(hft-must-fail hft-without-heap
               (fn-bs-profile-admittedp profile)
               (<= (+ (nfix used) (* *fn-sbud-membership-octets* (nfix m))) (nfix (fn-bs-profile-max-history-octets profile)))
               (<= (nfix n) (nfix (fn-bs-profile-max-transactions profile)))
               (<= (nfix ou) (nfix (fn-bs-profile-max-history-octets profile)))
               (<= (nfix on) (nfix (fn-bs-profile-max-transactions profile))))

; Without the history's charges within H (the payload and the memberships
; together, the history budget's): a payload of 100 H.
(assert! (equal (hft-hyps *fn-heap-small-profile* *hft-prod-core* *hft-nursery* (list *hft-2g*) (* 100 *hft-h*) *hft-t* *hft-mw* *hft-h* *hft-t*)
                '(t t nil t t t)))
(assert! (not (hft-conclusion *fn-heap-small-profile* *hft-prod-core* *hft-nursery* (list *hft-2g*) (* 100 *hft-h*) *hft-t* *hft-mw* *hft-h* *hft-t*)))
(hft-must-fail hft-without-used
               (fn-bs-profile-admittedp profile)
               (equal (car decision) :heap)
               (<= (nfix n) (nfix (fn-bs-profile-max-transactions profile)))
               (<= (nfix ou) (nfix (fn-bs-profile-max-history-octets profile)))
               (<= (nfix on) (nfix (fn-bs-profile-max-transactions profile))))

; Without N within T: ten times T records.
(assert! (equal (hft-hyps *fn-heap-small-profile* *hft-prod-core* *hft-nursery* (list *hft-2g*) *hft-used* (* 10 *hft-t*) *hft-mw* *hft-h* *hft-t*)
                '(t t t nil t t)))
(assert! (not (hft-conclusion *fn-heap-small-profile* *hft-prod-core* *hft-nursery* (list *hft-2g*) *hft-used* (* 10 *hft-t*) *hft-mw* *hft-h* *hft-t*)))
(hft-must-fail hft-without-records
               (fn-bs-profile-admittedp profile)
               (equal (car decision) :heap)
               (<= (+ (nfix used) (* *fn-sbud-membership-octets* (nfix m))) (nfix (fn-bs-profile-max-history-octets profile)))
               (<= (nfix ou) (nfix (fn-bs-profile-max-history-octets profile)))
               (<= (nfix on) (nfix (fn-bs-profile-max-transactions profile))))

; The same hypothesis's second counterexample: 16 groups on every record
; (the store before lane membership-budget), 262,144 memberships whose charge
; is ten times H (its must-fail is hft-without-used's: one hypothesis).
(assert! (equal (hft-hyps *fn-heap-small-profile* *hft-prod-core* *hft-nursery* (list *hft-2g*) *hft-used* *hft-t* *hft-m-uncharged* *hft-h* *hft-t*)
                '(t t nil t t t)))
(assert! (not (hft-conclusion *fn-heap-small-profile* *hft-prod-core* *hft-nursery* (list *hft-2g*) *hft-used* *hft-t* *hft-m-uncharged* *hft-h* *hft-t*)))
; Without the replay's octets within H: a replay of 10 H.
(assert! (equal (hft-hyps *fn-heap-small-profile* *hft-prod-core* *hft-nursery* (list *hft-2g*) *hft-used* *hft-t* *hft-mw* (* 10 *hft-h*) *hft-t*)
                '(t t t t nil t)))
(assert! (not (hft-conclusion *fn-heap-small-profile* *hft-prod-core* *hft-nursery* (list *hft-2g*) *hft-used* *hft-t* *hft-mw* (* 10 *hft-h*) *hft-t*)))
(hft-must-fail hft-without-open-octets
               (fn-bs-profile-admittedp profile)
               (equal (car decision) :heap)
               (<= (+ (nfix used) (* *fn-sbud-membership-octets* (nfix m))) (nfix (fn-bs-profile-max-history-octets profile)))
               (<= (nfix n) (nfix (fn-bs-profile-max-transactions profile)))
               (<= (nfix on) (nfix (fn-bs-profile-max-transactions profile))))

; Without the replay's records within T: a replay of 10 T records.
(assert! (equal (hft-hyps *fn-heap-small-profile* *hft-prod-core* *hft-nursery* (list *hft-2g*) *hft-used* *hft-t* *hft-mw* *hft-h* (* 10 *hft-t*))
                '(t t t t t nil)))
(assert! (not (hft-conclusion *fn-heap-small-profile* *hft-prod-core* *hft-nursery* (list *hft-2g*) *hft-used* *hft-t* *hft-mw* *hft-h* (* 10 *hft-t*))))
(hft-must-fail hft-without-open-records
               (fn-bs-profile-admittedp profile)
               (equal (car decision) :heap)
               (<= (+ (nfix used) (* *fn-sbud-membership-octets* (nfix m))) (nfix (fn-bs-profile-max-history-octets profile)))
               (<= (nfix n) (nfix (fn-bs-profile-max-transactions profile)))
               (<= (nfix ou) (nfix (fn-bs-profile-max-history-octets profile))))

; -----------------------------------------------------------------------------
; The refusal theorem's witnesses: both arms reached on admitted profiles.

(assert! (equal (car (fn-heap-decide *fn-heap-small-profile* *hft-core* *hft-nursery*
                                     (list (* 1759 *fn-heap-mib*))))
                :refused))
(assert! (equal (car (fn-heap-decide *fn-heap-small-profile* *hft-core* *hft-nursery*
                                     (list (* 1760 *fn-heap-mib*))))
                :heap))

; -----------------------------------------------------------------------------
; The small machine: the run of an empty small store.  Witness at the bound,
; and per hypothesis a counterexample.

(assert! (equal (fn-heap-operation-decide :run *fn-heap-small-profile* (* 192 *fn-heap-mib*)
                                          *hft-nursery* (list *hft-1536*) '(0 . 0))
                '(:heap 1457 "small" 1536)))
(assert! (equal (fn-heap-operation-decide :run *fn-heap-small-profile* (* 512 *fn-heap-mib*)
                                          *hft-nursery* (list *hft-2g*) '(0 . 0))
                '(:heap 1777 "small" 2048)))
; a core of more than 192 MiB of dynamic content on 1,536 MiB, or of more
; than 512 MiB on 2,048 MiB (the 512 MiB core the first held before lane
; heap-bounds: the 12 KiB record constant's figure)
(assert! (equal (fn-heap-operation-decide :run *fn-heap-small-profile* (* 512 *fn-heap-mib*)
                                          *hft-nursery* (list *hft-1536*) '(0 . 0))
                '(:refused :machine-cannot-hold-profile 1777 1536)))
(assert! (equal (car (fn-heap-operation-decide :run *fn-heap-small-profile*
                                               (* 1024 *fn-heap-mib*) *hft-nursery*
                                               (list *hft-2g*) '(0 . 0)))
                :refused))
; (no nursery hypothesis: even a 1 GiB cap is accepted, the trigger being a
; sixteenth of the space)
(assert! (equal (car (fn-heap-operation-decide :run *fn-heap-small-profile*
                                               (* 192 *fn-heap-mib*) (* 1024 *fn-heap-mib*)
                                               (list *hft-1536*) '(0 . 0)))
                :heap))
(assert! (equal (car (fn-heap-operation-decide :run *fn-heap-small-profile*
                                               (* 512 *fn-heap-mib*) (* 1024 *fn-heap-mib*)
                                               (list *hft-2g*) '(0 . 0)))
                :heap))
; a machine under 1536 MiB
(assert! (equal (car (fn-heap-operation-decide :run *fn-heap-small-profile*
                                               (* 192 *fn-heap-mib*) *hft-nursery*
                                               (list (* 1024 *fn-heap-mib*)) '(0 . 0)))
                :refused))
; a machine that is not a positive integer is no observation
(assert! (equal (car (fn-heap-operation-decide :run *fn-heap-small-profile* *hft-core*
                                               *hft-nursery*
                                               (list (+ (* 1536 *fn-heap-mib*) 1/2))
                                               '(0 . 0)))
                :refused))
(must-fail-checked
 (defthm hft-small-without-machine-bound
   (implies (and (<= (fn-heap-core-dynamic core) (* 512 *fn-heap-mib*))
                 (posp machine))
            (equal (car (fn-heap-operation-decide :run *fn-heap-small-profile* core nursery
                                                  (list machine) '(0 . 0)))
                   :heap))
   :hints (("Goal" :in-theory (e/d (fn-heap-mb-of fn-heap-store-figure-octets)
                                   (fn-heap-profile-word))
            :use ((:instance fn-heap-with-nursery-is-at-most-an-eighth-more
                             (base (fn-heap-store-base-octets *fn-heap-small-profile* core
                                                              '(0 . 0)))))))))

; -----------------------------------------------------------------------------
; init's default.

(assert! (equal (fn-heap-init-request '(:default nil) *hft-2g*) *fn-heap-small-request*))
(assert! (equal (fn-bs-profile-resolve (fn-heap-init-request '(:default nil) *hft-2g*) nil)
                *fn-heap-small-profile*))
(assert! (equal (fn-heap-init-request '(:default nil) (* 8 1024 *fn-heap-mib*))
                '(:default nil)))
(assert! (equal (fn-heap-init-request '(:development nil) *hft-2g*) '(:development nil)))
(assert! (equal (fn-heap-init-request '(:default ((1 . 100))) *hft-2g*)
                '(:default ((1 . 100)))))

; -----------------------------------------------------------------------------
; The store-less figure (PKT-686 item 3).  fn-heap-storeless-decide-is-small-
; and-fits: the witness is `fn --version' under the OpenBSD guest's 4 GiB
; datasize on its 195,856,696-octet core (before: the whole 4,096 MB as heap,
; and mmap refused the core beside it); then each hypothesis.

(defconst *hft-bsd-core* 195856696)
(defconst *hft-4g* (* 4096 *fn-heap-mib*))

(defun hft-sl-conclusion (core nursery machine)
  (declare (xargs :mode :program))
  (let ((d (fn-heap-storeless-decide core nursery machine)))
    (and (<= (fn-heap-decision-mb d) *fn-heap-storeless-mb*)
         (<= (+ (nfix core) (nfix nursery)) (* *fn-heap-mib* (fn-heap-decision-mb d)))
         (<= (+ (* *fn-heap-mib* (fn-heap-decision-mb d)) (nfix core)
                *fn-heap-storeless-thread-octets*)
             machine))))

(defun hft-sl-hyps (core nursery machine)
  (declare (xargs :mode :program))
  (list (equal (car (fn-heap-storeless-decide core nursery machine)) :heap)))

(assert! (equal (fn-heap-decide nil *hft-bsd-core* *hft-nursery* (list *hft-4g*))
                '(:heap 1024 "none" 4096)))
(assert! (equal (hft-sl-hyps *hft-bsd-core* *hft-nursery* *hft-4g*) '(t)))
(assert! (hft-sl-conclusion *hft-bsd-core* *hft-nursery* *hft-4g*))
; A machine smaller than the fixed figure: the room beside the core and one
; thread, 1,536 - 187 - 6 whole MB.
(assert! (equal (fn-heap-storeless-decide *hft-bsd-core* *hft-nursery* (* 1100 *fn-heap-mib*))
                '(:heap 907 "none" 1100)))
(assert! (hft-sl-conclusion *hft-bsd-core* *hft-nursery* (* 1100 *fn-heap-mib*)))
; Without acceptance: the image does not fit 256 MiB (a refusal's MB is 0).
(assert! (equal (hft-sl-hyps *hft-core* *hft-nursery* (* 256 *fn-heap-mib*)) '(nil)))
(assert! (not (hft-sl-conclusion *hft-core* *hft-nursery* (* 256 *fn-heap-mib*))))
(must-fail-checked
 (defthm hft-sl-without-heap
   (let ((d (fn-heap-storeless-decide core nursery machine)))
     (<= (+ (nfix core) (nfix nursery))
         (* *fn-heap-mib* (fn-heap-decision-mb d))))
   :hints (("Goal" :do-not-induct t))))
; A natural machine is not a hypothesis: acceptance needs a natural room
; beside the core, so an accepted machine is a natural (the weakened theorem
; was proved first).  A negative or fractional machine is refused.
(assert! (equal (car (fn-heap-storeless-decide 0 0 -1)) :refused))
(assert! (equal (car (fn-heap-storeless-decide 0 0 (+ *hft-4g* 1/2))) :refused))

; -----------------------------------------------------------------------------
; The operation's figure (PKT-686, reconciled by reservation-after-flip).
; fn-heap-operation-decide-holds-the-operation: the offline verbs' measured
; list copies; reachable witnesses (`store reclaim' of the small store full
; to H on a 2 GiB machine with the 195,856,696-octet core the OpenBSD guest
; built, the same on the 69046a76 core on 4 GiB, and the measured
; 3,000-article store observed at 7,271,160 octets in 3,000 files), then per
; hypothesis a counterexample and the must-fail of the keystone without it.

(defun hft-op-conclusion (action profile core nursery observations observed used)
  (declare (xargs :mode :program))
  (let ((decision (fn-heap-operation-decide action profile core nursery observations
                                            observed)))
    (and (<= (+ (fn-heap-core-dynamic core) nursery
                (* 2 *fn-heap-octets-per-list-octet*
                   (+ (* (fn-heap-operation-history-copies action) used)
                      (fn-bs-profile-max-record-octets profile)
                      (* *fn-heap-header-copies* (fn-bs-profile-field 15 profile))))
                (* 2 (fn-ock-capture-budget profile)))
             (* *fn-heap-mib* (fn-heap-decision-mb decision)))
         (<= (* *fn-heap-mib* (fn-heap-decision-mb decision))
             (fn-heap-machine-octets observations)))))

(defun hft-op-hyps (action profile core nursery observations observed used)
  (declare (xargs :mode :program))
  (list (if (member-equal action *fn-heap-list-actions*) t nil)
        (fn-bs-profile-admittedp profile)
        (equal (car (fn-heap-operation-decide action profile core nursery observations
                                              observed))
               :heap)
        (<= used (fn-bs-profile-max-history-octets profile))
        (if (natp (fn-heap-observed-octets observed))
            (<= used (fn-heap-observed-octets observed))
          t)
        (natp nursery)))

; The compaction verbs count six copies, every other command two; any other
; command unobserved decides as fn-heap-decide, and observed as the run
; does; `init' judges an empty store whatever it was handed.
(assert! (equal (fn-heap-operation-history-copies :reclaim) 6))
(assert! (equal (fn-heap-operation-history-copies :compact) 6))
(assert! (equal (fn-heap-operation-history-copies :run) 2))
(assert! (equal (fn-heap-operation-decide :reclaim *fn-heap-small-profile* *hft-bsd-core*
                                          *hft-nursery* (list *hft-2g*) nil)
                '(:heap 1843 "small" 2048)))
(assert! (equal (fn-heap-operation-decide :status *fn-heap-small-profile* *hft-bsd-core*
                                          *hft-nursery* (list *hft-2g*) nil)
                (fn-heap-decide *fn-heap-small-profile* *hft-bsd-core* *hft-nursery*
                                (list *hft-2g*))))
(assert! (equal (fn-heap-operation-decide :status *fn-heap-small-profile* *hft-bsd-core*
                                          *hft-nursery* (list *hft-2g*) '(100000 . 50))
                (fn-heap-operation-decide :run *fn-heap-small-profile* *hft-bsd-core*
                                          *hft-nursery* (list *hft-2g*) '(100000 . 50))))
(assert! (equal (fn-heap-operation-decide :init *fn-heap-small-profile* *hft-bsd-core*
                                          *hft-nursery* (list *hft-2g*) nil)
                '(:heap 1452 "small" 2048)))
; By the store's observed history: an empty store reclaims in 888 MB, the
; measured 3,000-article store in 1,639 MB (its six list copies), a store of
; 100,000 octets in 50 files compacts, recovers and runs in 888 MB, where an
; unobserved run keeps the bounds' 942 MB (832 and 887 before the articles in
; flight, lane zero-copy-commit; 997 and 1,048 before membership-budget).  An observation past H or T
; changes nothing; octets without a count take T's records.
(assert! (equal (fn-heap-operation-decide :reclaim *fn-heap-small-profile* *hft-bsd-core*
                                          *hft-nursery* (list *hft-2g*) '(0 . 0))
                '(:heap 1452 "small" 2048)))
(assert! (equal (fn-heap-operation-decide :reclaim *fn-heap-small-profile* *hft-bsd-core*
                                          *hft-nursery* (list *hft-4g*) '(7271160 . 3000))
                '(:heap 1639 "small" 4096)))
(assert! (equal (fn-heap-operation-decide :compact *fn-heap-small-profile* *hft-bsd-core*
                                          *hft-nursery* (list *hft-2g*) '(100000 . 50))
                '(:heap 1458 "small" 2048)))
(assert! (equal (fn-heap-operation-decide :recover *fn-heap-small-profile* *hft-bsd-core*
                                          *hft-nursery* (list *hft-2g*) '(100000 . 50))
                '(:heap 1458 "small" 2048)))
(assert! (equal (fn-heap-operation-decide :run *fn-heap-small-profile* *hft-bsd-core*
                                          *hft-nursery* (list *hft-2g*) '(100000 . 50))
                '(:heap 1458 "small" 2048)))
(assert! (equal (fn-heap-operation-decide :run *fn-heap-small-profile* *hft-bsd-core*
                                          *hft-nursery* (list *hft-2g*) nil)
                '(:heap 1576 "small" 2048)))
(assert! (equal (fn-heap-operation-decide :recover *fn-heap-small-profile* *hft-bsd-core*
                                          *hft-nursery* (list *hft-2g*) 100000)
                '(:heap 1490 "small" 2048)))
(assert! (equal (fn-heap-operation-decide :reclaim *fn-heap-small-profile* *hft-bsd-core*
                                          *hft-nursery* (list *hft-2g*)
                                          (cons (* 2 8388608) (* 2 16384)))
                (fn-heap-operation-decide :reclaim *fn-heap-small-profile* *hft-bsd-core*
                                          *hft-nursery* (list *hft-2g*) nil)))
; Under OpenBSD's default 1,536 MiB data limit the small store's reclaim and
; run at the bounds are refused by name; observed empty, both are accepted.
(assert! (equal (fn-heap-operation-decide :reclaim *fn-heap-small-profile* *hft-bsd-core*
                                          *hft-nursery* (list *hft-1536*) nil)
                '(:refused :machine-cannot-hold-profile 1843 1536)))
(assert! (equal (fn-heap-operation-decide :reclaim *fn-heap-small-profile* *hft-bsd-core*
                                          *hft-nursery* (list *hft-1536*) '(0 . 0))
                '(:heap 1452 "small" 1536)))
(assert! (equal (fn-heap-operation-decide :run *fn-heap-small-profile* *hft-bsd-core*
                                          *hft-nursery* (list *hft-1536*) '(0 . 0))
                '(:heap 1452 "small" 1536)))
; The observation only lowers the figure.
(assert! (< (fn-heap-operation-figure-octets :reclaim *fn-heap-small-profile* *hft-bsd-core*
                                             *hft-nursery* '(7271160 . 3000))
            (fn-heap-operation-figure-octets :reclaim *fn-heap-small-profile* *hft-bsd-core*
                                             *hft-nursery* nil)))

; The witnesses: every hypothesis and the conclusion.
(assert! (equal (hft-op-hyps :reclaim *fn-heap-small-profile* *hft-bsd-core* *hft-nursery*
                             (list *hft-2g*) nil 8388608)
                '(t t t t t t)))
(assert! (hft-op-conclusion :reclaim *fn-heap-small-profile* *hft-bsd-core* *hft-nursery*
                            (list *hft-2g*) nil 8388608))
(assert! (equal (hft-op-hyps :compact *fn-heap-small-profile* *hft-core* *hft-nursery*
                             (list *hft-4g*) nil 8388608)
                '(t t t t t t)))
(assert! (hft-op-conclusion :compact *fn-heap-small-profile* *hft-core* *hft-nursery*
                            (list *hft-4g*) nil 8388608))
(assert! (equal (hft-op-hyps :reclaim *fn-heap-small-profile* *hft-bsd-core* *hft-nursery*
                             (list *hft-4g*) '(7271160 . 3000) 7271160)
                '(t t t t t t)))
(assert! (hft-op-conclusion :reclaim *fn-heap-small-profile* *hft-bsd-core* *hft-nursery*
                            (list *hft-4g*) '(7271160 . 3000) 7271160))

(defmacro hft-op-must-fail (name &rest hyps)
  `(must-fail-checked
    (defthm ,name
      (let ((decision (fn-heap-operation-decide action profile core nursery observations
                                                observed)))
        (implies (and ,@hyps)
                 (<= (+ (fn-heap-core-dynamic core) nursery
                        (* 2 *fn-heap-octets-per-list-octet*
                           (+ (* (fn-heap-operation-history-copies action) used)
                              (fn-bs-profile-max-record-octets profile)
                              (* *fn-heap-header-copies* (fn-bs-profile-field 15 profile))))
                        (* 2 (fn-ock-capture-budget profile)))
                     (* *fn-heap-mib* (fn-heap-decision-mb decision)))))
      :hints (("Goal" :in-theory (union-theories
                                  '(fn-heap-operation-list-figure-octets
                                    fn-heap-operation-list-octets fn-heap-buffer-octets
                                    fn-heap-mb-of-natp fn-heap-operation-figure-octets-natp
                                    fn-heap-nfix-of-operation-figure-octets natp nfix)
                                  (theory 'minimal-theory))
               :use (fn-heap-operation-decide-accepted
                     fn-heap-operation-figure-holds-the-parts
                     fn-heap-operation-used-within-the-history-octets
                     (:instance fn-heap-mb-of-covers
                                (octets (fn-heap-operation-figure-octets
                                         action profile core nursery observed)))))))))

; Without an offline verb: `run' under a 4 GiB nursery cap, which the list
; model counts whole and the store figure (the trigger the host sets) does not.
(defconst *hft-4g-nursery* (* 4096 *fn-heap-mib*))
(assert! (equal (hft-op-hyps :run *fn-heap-small-profile* *hft-bsd-core* *hft-4g-nursery*
                             (list *hft-big*) nil 0)
                '(nil t t t t t)))
(assert! (not (hft-op-conclusion :run *fn-heap-small-profile* *hft-bsd-core*
                                 *hft-4g-nursery* (list *hft-big*) nil 0)))
(hft-op-must-fail hft-op-without-offline-verb
                  (fn-bs-profile-admittedp profile)
                  (equal (car decision) :heap)
                  (<= used (fn-bs-profile-max-history-octets profile))
                  (implies (natp (fn-heap-observed-octets observed))
                           (<= used (fn-heap-observed-octets observed)))
                  (natp nursery))

; Without the admitted profile: no store, whose figure is the store-less
; one: an image of exactly 1,024 MiB with the nursery fills it, and the
; capture buffers of no profile do not fit beside.
(defconst *hft-full-core* (- (* 1024 *fn-heap-mib*) *hft-nursery*))
(assert! (equal (hft-op-hyps :reclaim nil *hft-full-core* *hft-nursery* (list *hft-4g*) nil 0)
                '(t nil t t t t)))
(assert! (not (hft-op-conclusion :reclaim nil *hft-full-core* *hft-nursery*
                                 (list *hft-4g*) nil 0)))
(hft-op-must-fail hft-op-without-admitted
                  (member-equal action *fn-heap-list-actions*)
                  (equal (car decision) :heap)
                  (<= used (fn-bs-profile-max-history-octets profile))
                  (implies (natp (fn-heap-observed-octets observed))
                           (<= used (fn-heap-observed-octets observed)))
                  (natp nursery))

; Without the accepted decision: the reclaim at H under 1,536 MiB.
(assert! (equal (hft-op-hyps :reclaim *fn-heap-small-profile* *hft-bsd-core* *hft-nursery*
                             (list *hft-1536*) nil 8388608)
                '(t t nil t t t)))
(assert! (not (hft-op-conclusion :reclaim *fn-heap-small-profile* *hft-bsd-core*
                                 *hft-nursery* (list *hft-1536*) nil 8388608)))
(hft-op-must-fail hft-op-without-heap
                  (member-equal action *fn-heap-list-actions*)
                  (fn-bs-profile-admittedp profile)
                  (<= used (fn-bs-profile-max-history-octets profile))
                  (implies (natp (fn-heap-observed-octets observed))
                           (<= used (fn-heap-observed-octets observed)))
                  (natp nursery))

; Without USED within H: a history twice H, unobserved.
(assert! (equal (hft-op-hyps :reclaim *fn-heap-small-profile* *hft-bsd-core* *hft-nursery*
                             (list *hft-2g*) nil (* 2 8388608))
                '(t t t nil t t)))
(assert! (not (hft-op-conclusion :reclaim *fn-heap-small-profile* *hft-bsd-core*
                                 *hft-nursery* (list *hft-2g*) nil (* 2 8388608))))
(hft-op-must-fail hft-op-without-used-within-h
                  (member-equal action *fn-heap-list-actions*)
                  (fn-bs-profile-admittedp profile)
                  (equal (car decision) :heap)
                  (implies (natp (fn-heap-observed-octets observed))
                           (<= used (fn-heap-observed-octets observed)))
                  (natp nursery))

; Without USED within the observed octets: the probe observed 100,000 octets
; in 50 files and the reclaim holds the measured store's 7,271,160.
(assert! (equal (hft-op-hyps :reclaim *fn-heap-small-profile* *hft-bsd-core* *hft-nursery*
                             (list *hft-2g*) '(100000 . 50) 7271160)
                '(t t t t nil t)))
(assert! (not (hft-op-conclusion :reclaim *fn-heap-small-profile* *hft-bsd-core*
                                 *hft-nursery* (list *hft-2g*) '(100000 . 50) 7271160)))
(hft-op-must-fail hft-op-without-used-within-observed
                  (member-equal action *fn-heap-list-actions*)
                  (fn-bs-profile-admittedp profile)
                  (equal (car decision) :heap)
                  (<= used (fn-bs-profile-max-history-octets profile))
                  (natp nursery))

; Without a natural nursery: a fractional nursery the figure reads as 0.
(assert! (equal (hft-op-hyps :reclaim *fn-heap-small-profile* *hft-bsd-core*
                             (+ 2000000000 1/2) (list *hft-4g*) nil 0)
                '(t t t t t nil)))
(assert! (not (hft-op-conclusion :reclaim *fn-heap-small-profile* *hft-bsd-core*
                                 (+ 2000000000 1/2) (list *hft-4g*) nil 0)))
(hft-op-must-fail hft-op-without-natp-nursery
                  (member-equal action *fn-heap-list-actions*)
                  (fn-bs-profile-admittedp profile)
                  (equal (car decision) :heap)
                  (<= used (fn-bs-profile-max-history-octets profile))
                  (implies (natp (fn-heap-observed-octets observed))
                           (<= used (fn-heap-observed-octets observed))))

; -----------------------------------------------------------------------------
; fn-heap-operation-decide-holds-the-store: the store model under every
; command's figure, the open's input within the observation.  Witnesses: the
; run of the measured 1,000-post store (2,465,160 octets in 1,000 files) at
; the production image's observation, with the store grown to H and T; the
; reclaim of the same; then per hypothesis a counterexample and a must-fail.

(defun hft-st-conclusion (action profile core nursery observations observed used n m ou on)
  (declare (xargs :mode :program))
  (let* ((decision (fn-heap-operation-decide action profile core nursery observations
                                             observed))
         (d (* *fn-heap-mib* (fn-heap-decision-mb decision))))
    (and (<= (fn-heap-store-need profile core used n m ou on
                                 (fn-heap-nursery-trigger d nursery))
             d)
         (<= d (fn-heap-machine-octets observations)))))

(defun hft-st-hyps (action profile core nursery observations observed used n m ou on)
  (declare (xargs :mode :program))
  (list (fn-bs-profile-admittedp profile)
        (equal (car (fn-heap-operation-decide action profile core nursery observations
                                              observed))
               :heap)
        (<= (+ (nfix used) (* *fn-sbud-membership-octets* (nfix m)))
            (nfix (fn-bs-profile-max-history-octets profile)))
        (<= (nfix n) (nfix (fn-bs-profile-max-transactions profile)))
        (<= (nfix ou) (fn-heap-open-octets-bound profile observed))
        (<= (nfix on) (fn-heap-open-records-bound profile observed))))

(defconst *hft-1000* '(2465160 . 1000))
(assert! (equal (fn-heap-operation-decide :run *fn-heap-small-profile* *hft-prod-core*
                                          *hft-nursery* (list *hft-2g*) *hft-1000*)
                '(:heap 1457 "small" 2048)))
(assert! (equal (hft-st-hyps :run *fn-heap-small-profile* *hft-prod-core* *hft-nursery* (list *hft-2g*) *hft-1000* *hft-used* *hft-t* *hft-mw* 2465160 1000)
                '(t t t t t t)))
(assert! (hft-st-conclusion :run *fn-heap-small-profile* *hft-prod-core* *hft-nursery* (list *hft-2g*) *hft-1000* *hft-used* *hft-t* *hft-mw* 2465160 1000))
(assert! (equal (hft-st-hyps :reclaim *fn-heap-small-profile* *hft-prod-core* *hft-nursery* (list *hft-2g*) *hft-1000* *hft-used* *hft-t* *hft-mw* 2465160 1000)
                '(t t t t t t)))
(assert! (hft-st-conclusion :reclaim *fn-heap-small-profile* *hft-prod-core* *hft-nursery* (list *hft-2g*) *hft-1000* *hft-used* *hft-t* *hft-mw* 2465160 1000))

(defmacro hft-st-must-fail (name &rest hyps)
  `(must-fail-checked
    (defthm ,name
      (let* ((decision (fn-heap-operation-decide action profile core nursery observations
                                                 observed))
             (d (* *fn-heap-mib* (fn-heap-decision-mb decision))))
        (implies (and ,@hyps)
                 (<= (fn-heap-store-need profile core used n m ou on
                                         (fn-heap-nursery-trigger d nursery))
                     d)))
      :hints (("Goal" :in-theory (union-theories
                                  '(fn-heap-mb-of-natp fn-heap-operation-figure-octets-natp
                                    fn-heap-nfix-of-operation-figure-octets natp)
                                  (theory 'minimal-theory))
               :use (fn-heap-operation-decide-accepted
                     fn-heap-operation-figure-holds-the-parts
                     (:instance fn-heap-mb-of-covers
                                (octets (fn-heap-operation-figure-octets
                                         action profile core nursery observed)))
                     (:instance fn-heap-store-figure-holds-every-store
                                (d (* *fn-heap-mib*
                                      (fn-heap-mb-of (fn-heap-operation-figure-octets
                                                      action profile core nursery
                                                      observed)))))))))))

; Without the admitted profile: no store; a 100 MiB image, no nursery cap, a
; machine of exactly the store-less room: the heap is the image, and the
; collector's 8 MiB least trigger does not fit beside it.
(assert! (equal (fn-heap-operation-decide :run nil (* 100 *fn-heap-mib*) 0
                                          (list (* 206 *fn-heap-mib*)) nil)
                '(:heap 100 "none" 206)))
(assert! (equal (hft-st-hyps :run nil (* 100 *fn-heap-mib*) 0 (list (* 206 *fn-heap-mib*)) nil 0 0 0 0 0)
                '(nil t t t t t)))
(assert! (not (hft-st-conclusion :run nil (* 100 *fn-heap-mib*) 0 (list (* 206 *fn-heap-mib*)) nil 0 0 0 0 0)))
(hft-st-must-fail hft-st-without-admitted
                  (equal (car decision) :heap)
                  (<= (+ (nfix used) (* *fn-sbud-membership-octets* (nfix m))) (nfix (fn-bs-profile-max-history-octets profile)))
                  (<= (nfix n) (nfix (fn-bs-profile-max-transactions profile)))
                  (<= (nfix ou) (fn-heap-open-octets-bound profile observed))
                  (<= (nfix on) (fn-heap-open-records-bound profile observed)))

; Without the accepted decision: the unobserved run under 700 MiB.
(assert! (equal (hft-st-hyps :run *fn-heap-small-profile* *hft-prod-core* *hft-nursery* (list *hft-700m*) nil *hft-used* *hft-t* *hft-mw* *hft-h* *hft-t*)
                '(t nil t t t t)))
(assert! (not (hft-st-conclusion :run *fn-heap-small-profile* *hft-prod-core* *hft-nursery* (list *hft-700m*) nil *hft-used* *hft-t* *hft-mw* *hft-h* *hft-t*)))
(hft-st-must-fail hft-st-without-heap
                  (fn-bs-profile-admittedp profile)
                  (<= (+ (nfix used) (* *fn-sbud-membership-octets* (nfix m))) (nfix (fn-bs-profile-max-history-octets profile)))
                  (<= (nfix n) (nfix (fn-bs-profile-max-transactions profile)))
                  (<= (nfix ou) (fn-heap-open-octets-bound profile observed))
                  (<= (nfix on) (fn-heap-open-records-bound profile observed)))

; Without the history's charges within H: the run's payload of 100 H.
(assert! (equal (hft-st-hyps :run *fn-heap-small-profile* *hft-prod-core* *hft-nursery* (list *hft-2g*) *hft-1000* (* 100 *hft-h*) *hft-t* *hft-mw* 0 0)
                '(t t nil t t t)))
(assert! (not (hft-st-conclusion :run *fn-heap-small-profile* *hft-prod-core* *hft-nursery* (list *hft-2g*) *hft-1000* (* 100 *hft-h*) *hft-t* *hft-mw* 0 0)))
(hft-st-must-fail hft-st-without-used
                  (fn-bs-profile-admittedp profile)
                  (equal (car decision) :heap)
                  (<= (nfix n) (nfix (fn-bs-profile-max-transactions profile)))
                  (<= (nfix ou) (fn-heap-open-octets-bound profile observed))
                  (<= (nfix on) (fn-heap-open-records-bound profile observed)))

; Without N within T: ten times T records.
(assert! (equal (hft-st-hyps :run *fn-heap-small-profile* *hft-prod-core* *hft-nursery* (list *hft-2g*) *hft-1000* *hft-used* (* 10 *hft-t*) *hft-mw* 0 0)
                '(t t t nil t t)))
(assert! (not (hft-st-conclusion :run *fn-heap-small-profile* *hft-prod-core* *hft-nursery* (list *hft-2g*) *hft-1000* *hft-used* (* 10 *hft-t*) *hft-mw* 0 0)))
(hft-st-must-fail hft-st-without-records
                  (fn-bs-profile-admittedp profile)
                  (equal (car decision) :heap)
                  (<= (+ (nfix used) (* *fn-sbud-membership-octets* (nfix m))) (nfix (fn-bs-profile-max-history-octets profile)))
                  (<= (nfix ou) (fn-heap-open-octets-bound profile observed))
                  (<= (nfix on) (fn-heap-open-records-bound profile observed)))

; The same hypothesis, 16 groups on every record (its must-fail is
; hft-st-without-used's).
(assert! (equal (hft-st-hyps :run *fn-heap-small-profile* *hft-prod-core* *hft-nursery* (list *hft-2g*) *hft-1000* *hft-used* *hft-t* *hft-m-uncharged* 0 0)
                '(t t nil t t t)))
(assert! (not (hft-st-conclusion :run *fn-heap-small-profile* *hft-prod-core* *hft-nursery* (list *hft-2g*) *hft-1000* *hft-used* *hft-t* *hft-m-uncharged* 0 0)))
; Without the open's octets within the observation: an empty store observed,
; a replay of H.
(assert! (equal (hft-st-hyps :run *fn-heap-small-profile* *hft-prod-core* *hft-nursery* (list *hft-2g*) '(0 . 0) *hft-used* *hft-t* *hft-mw* *hft-h* 0)
                '(t t t t nil t)))
(assert! (not (hft-st-conclusion :run *fn-heap-small-profile* *hft-prod-core* *hft-nursery* (list *hft-2g*) '(0 . 0) *hft-used* *hft-t* *hft-mw* *hft-h* 0)))
(hft-st-must-fail hft-st-without-open-octets
                  (fn-bs-profile-admittedp profile)
                  (equal (car decision) :heap)
                  (<= (+ (nfix used) (* *fn-sbud-membership-octets* (nfix m))) (nfix (fn-bs-profile-max-history-octets profile)))
                  (<= (nfix n) (nfix (fn-bs-profile-max-transactions profile)))
                  (<= (nfix on) (fn-heap-open-records-bound profile observed)))

; Without the open's records within the observation: an empty store
; observed, a replay of T records.
(assert! (equal (hft-st-hyps :run *fn-heap-small-profile* *hft-prod-core* *hft-nursery* (list *hft-2g*) '(0 . 0) *hft-used* *hft-t* *hft-mw* 0 *hft-t*)
                '(t t t t t nil)))
(assert! (not (hft-st-conclusion :run *fn-heap-small-profile* *hft-prod-core* *hft-nursery* (list *hft-2g*) '(0 . 0) *hft-used* *hft-t* *hft-mw* 0 *hft-t*)))
(hft-st-must-fail hft-st-without-open-records
                  (fn-bs-profile-admittedp profile)
                  (equal (car decision) :heap)
                  (<= (+ (nfix used) (* *fn-sbud-membership-octets* (nfix m))) (nfix (fn-bs-profile-max-history-octets profile)))
                  (<= (nfix n) (nfix (fn-bs-profile-max-transactions profile)))
                  (<= (nfix ou) (fn-heap-open-octets-bound profile observed)))

; -----------------------------------------------------------------------------
; books/heap-store-figure's keystones directly.  fn-heap-with-nursery-holds-
; the-trigger: witness at the small store's base (the trigger a sixteenth of
; the space), and without D at least the figure: one megabyte less than the
; base itself.  fn-heap-store-figure-holds-every-store: witness at the figure
; itself with the store full and a full replay of it; each hypothesis's
; counterexample (the others holding) and must-fail.

(defconst *hft-base* (fn-heap-store-base-octets *fn-heap-small-profile* *hft-prod-core* nil))
(defconst *hft-fig* (fn-heap-store-figure-octets *fn-heap-small-profile* *hft-prod-core*
                                                 *hft-nursery* nil))
(assert! (<= (+ *hft-base* (* 2 (fn-heap-nursery-trigger *hft-fig* *hft-nursery*))) *hft-fig*))
(assert! (< *hft-fig* (+ *hft-base* (* 2 (fn-heap-nursery-trigger *hft-fig* *hft-nursery*))
                         (* 1 *fn-heap-mib*))))
(assert! (not (<= (+ *hft-base* (* 2 (fn-heap-nursery-trigger (- *hft-base* *fn-heap-mib*)
                                                              *hft-nursery*)))
                  (- *hft-base* *fn-heap-mib*))))
(must-fail-checked
 (defthm hft-with-nursery-without-the-figure
   (implies (and (natp d) (natp base))
            (<= (+ base (* 2 (fn-heap-nursery-trigger d nursery))) d))
   :rule-classes nil))

(defun hft-sf-hyps (d observed used n m ou on)
  (declare (xargs :mode :program))
  (list (natp d)
        (<= (fn-heap-store-figure-octets *fn-heap-small-profile* *hft-prod-core*
                                         *hft-nursery* observed)
            d)
        (<= (+ (nfix used) (* *fn-sbud-membership-octets* (nfix m))) *hft-h*)
        (<= (nfix n) *hft-t*)
        (<= (nfix ou) (fn-heap-open-octets-bound *fn-heap-small-profile* observed))
        (<= (nfix on) (fn-heap-open-records-bound *fn-heap-small-profile* observed))))

(defun hft-sf-conclusion (d observed used n m ou on)
  (declare (xargs :mode :program))
  (declare (ignore observed))
  (<= (fn-heap-store-need *fn-heap-small-profile* *hft-prod-core* used n m ou on
                          (fn-heap-nursery-trigger d *hft-nursery*))
      d))

(assert! (equal (hft-sf-hyps *hft-fig* nil *hft-used* *hft-t* *hft-mw* *hft-h* *hft-t*) '(t t t t t t)))
(assert! (hft-sf-conclusion *hft-fig* nil *hft-used* *hft-t* *hft-mw* *hft-h* *hft-t*))
; D a fraction: the figure plus one half.
(assert! (equal (hft-sf-hyps (+ *hft-fig* 1/2) nil 0 0 0 0 0) '(nil t t t t t)))
; D under the figure: nine megabytes less, the store full.  (The figure is
; within H of the costliest store since lane heap-bounds: the history bound
; charges a payload octet two arena octets, fn-heap-arena-octets-slope, where
; the paged arena spends one; the store full of header octets, which the
; figure's worst case now is, leaves that H = 8 MiB of slack.)
(assert! (equal (- *hft-fig* (fn-heap-store-need *fn-heap-small-profile* *hft-prod-core* *hft-used*
                                                 *hft-t* *hft-mw* *hft-h* *hft-t*
                                                 (fn-heap-nursery-trigger *hft-fig* *hft-nursery*)))
                8387616))
(assert! (equal (hft-sf-hyps (- *hft-fig* (* 9 *fn-heap-mib*)) nil *hft-used* *hft-t* *hft-mw* *hft-h* *hft-t*)
                '(t nil t t t t)))
(assert! (not (hft-sf-conclusion (- *hft-fig* (* 9 *fn-heap-mib*)) nil *hft-used* *hft-t* *hft-mw* *hft-h* *hft-t*)))
(assert! (not (hft-sf-conclusion *hft-fig* nil (* 100 *hft-h*) *hft-t* *hft-mw* *hft-h* *hft-t*)))
(assert! (not (hft-sf-conclusion *hft-fig* nil *hft-used* (* 10 *hft-t*) *hft-mw* *hft-h* *hft-t*)))
(assert! (not (hft-sf-conclusion *hft-fig* nil *hft-used* *hft-t* *hft-mw* (* 10 *hft-h*) *hft-t*)))
(assert! (not (hft-sf-conclusion *hft-fig* nil *hft-used* *hft-t* *hft-mw* *hft-h* (* 10 *hft-t*))))
; Memberships past H / 320: the uncharged 16 groups a record.
(assert! (equal (hft-sf-hyps *hft-fig* nil *hft-used* *hft-t* *hft-m-uncharged* *hft-h* *hft-t*)
                '(t t nil t t t)))
(assert! (not (hft-sf-conclusion *hft-fig* nil *hft-used* *hft-t* *hft-m-uncharged* *hft-h* *hft-t*)))
; An observed empty store: its figure holds no replay of H.
(defconst *hft-fig0* (fn-heap-store-figure-octets *fn-heap-small-profile* *hft-prod-core*
                                                  *hft-nursery* '(0 . 0)))
(assert! (equal (hft-sf-hyps *hft-fig0* '(0 . 0) *hft-used* *hft-t* *hft-mw* *hft-h* 0) '(t t t t nil t)))
(assert! (not (hft-sf-conclusion *hft-fig0* '(0 . 0) *hft-used* *hft-t* *hft-mw* *hft-h* 0)))
(assert! (equal (hft-sf-hyps *hft-fig0* '(0 . 0) *hft-used* *hft-t* *hft-mw* 0 *hft-t*) '(t t t t t nil)))
(assert! (not (hft-sf-conclusion *hft-fig0* '(0 . 0) *hft-used* *hft-t* *hft-mw* 0 *hft-t*)))

(defmacro hft-sf-must-fail (name &rest hyps)
  `(must-fail-checked
    (defthm ,name
      (implies (and ,@hyps)
               (<= (fn-heap-store-need profile core used n m ou on
                                       (fn-heap-nursery-trigger d nursery))
                   d))
      :hints (("Goal" :in-theory (union-theories
                                  '(fn-heap-store-figure-octets fn-heap-store-base-octets-natp
                                    fn-heap-nfix-of-nursery-trigger)
                                  (theory 'minimal-theory))
               :use ((:instance fn-heap-with-nursery-holds-the-trigger
                                (base (fn-heap-store-base-octets profile core observed)))))))))

; (natp d) is redundant here (audit packet G3-6, lane audit-fixes): the
; weakened theorem is proved at the end of this book, so the former
; must-fail for it (a search failure under a minimal theory, not a
; counterexample) is withdrawn.
(hft-sf-must-fail hft-sf-without-the-figure
                  (natp d)
                  (<= (+ (nfix used) (* *fn-sbud-membership-octets* (nfix m))) (nfix (fn-bs-profile-max-history-octets profile)))
                  (<= (nfix n) (nfix (fn-bs-profile-max-transactions profile)))
                  (<= (nfix ou) (fn-heap-open-octets-bound profile observed))
                  (<= (nfix on) (fn-heap-open-records-bound profile observed)))
(hft-sf-must-fail hft-sf-without-used
                  (natp d)
                  (<= (fn-heap-store-figure-octets profile core nursery observed) d)
                  (<= (nfix n) (nfix (fn-bs-profile-max-transactions profile)))
                  (<= (nfix ou) (fn-heap-open-octets-bound profile observed))
                  (<= (nfix on) (fn-heap-open-records-bound profile observed)))
(hft-sf-must-fail hft-sf-without-records
                  (natp d)
                  (<= (fn-heap-store-figure-octets profile core nursery observed) d)
                  (<= (+ (nfix used) (* *fn-sbud-membership-octets* (nfix m))) (nfix (fn-bs-profile-max-history-octets profile)))
                  (<= (nfix ou) (fn-heap-open-octets-bound profile observed))
                  (<= (nfix on) (fn-heap-open-records-bound profile observed)))
(hft-sf-must-fail hft-sf-without-open-octets
                  (natp d)
                  (<= (fn-heap-store-figure-octets profile core nursery observed) d)
                  (<= (+ (nfix used) (* *fn-sbud-membership-octets* (nfix m))) (nfix (fn-bs-profile-max-history-octets profile)))
                  (<= (nfix n) (nfix (fn-bs-profile-max-transactions profile)))
                  (<= (nfix on) (fn-heap-open-records-bound profile observed)))
(hft-sf-must-fail hft-sf-without-open-records
                  (natp d)
                  (<= (fn-heap-store-figure-octets profile core nursery observed) d)
                  (<= (+ (nfix used) (* *fn-sbud-membership-octets* (nfix m))) (nfix (fn-bs-profile-max-history-octets profile)))
                  (<= (nfix n) (nfix (fn-bs-profile-max-transactions profile)))
                  (<= (nfix ou) (fn-heap-open-octets-bound profile observed)))

; -----------------------------------------------------------------------------
; Lane keystone-audit (2026-09-27).  fn-heap-store-figure-observed-is-at-most-
; unobserved (no hypothesis): the measured 3,000-article store's observation
; and an empty store's each give a figure below the unobserved one, and
; strictly (the observation matters).
(assert! (< (fn-heap-store-figure-octets *fn-heap-small-profile* *hft-prod-core* *hft-nursery*
                                         '(7271160 . 3000))
            (fn-heap-store-figure-octets *fn-heap-small-profile* *hft-prod-core* *hft-nursery*
                                         nil)))
(assert! (< (fn-heap-store-figure-octets *fn-heap-small-profile* *hft-prod-core* *hft-nursery*
                                         '(0 . 0))
            (fn-heap-store-figure-octets *fn-heap-small-profile* *hft-prod-core* *hft-nursery*
                                         '(7271160 . 3000))))

; -----------------------------------------------------------------------------
; Audit packet G3-6 (lane audit-fixes): the natp hypotheses of
; fn-heap-with-nursery-holds-the-trigger and fn-heap-store-figure-holds-
; every-store.
;
; (natp d) is redundant in both: a D at least the (natural) figure that is
; not an integer has trigger 8 MiB (nfix of a non-integer is 0), the least
; the figure's own trigger can be, and the figure holds the store at its own
; trigger.  The weakened theorems are proved here (the library statements
; are left as they are).
(local (defthm hft-trigger-of-a-non-integer
         (implies (not (integerp d))
                  (equal (fn-heap-nursery-trigger d nursery) 8388608))
         :hints (("Goal" :in-theory (enable fn-heap-nursery-trigger)))))
(local (defthm hft-trigger-at-least-the-least
         (<= 8388608 (fn-heap-nursery-trigger d nursery))
         :rule-classes nil
         :hints (("Goal" :in-theory (enable fn-heap-nursery-trigger)))))
(local (defthm hft-store-need-grows-with-the-trigger
         (implies (and (natp t1) (natp t2) (<= t1 t2))
                  (<= (fn-heap-store-need profile core used n m ou on t1)
                      (fn-heap-store-need profile core used n m ou on t2)))
         :rule-classes nil
         :hints (("Goal" :in-theory (union-theories '(fn-heap-store-need nfix natp)
                                                    (theory 'minimal-theory))))))
(defthm hft-with-nursery-holds-the-trigger-without-natp-d
  (implies (and (natp base) (<= (fn-heap-with-nursery base nursery) d))
           (<= (+ base (* 2 (fn-heap-nursery-trigger d nursery))) d))
  :rule-classes nil
  :hints (("Goal" :cases ((natp d)))
          ("Subgoal 1" :use ((:instance fn-heap-with-nursery-holds-the-trigger)))
          ("Subgoal 2" :in-theory (enable fn-heap-with-nursery fn-heap-nursery-trigger))))
(local (defthm hft-store-figure-holds-at-a-non-integer
  (implies (and (<= (fn-heap-store-figure-octets profile core nursery observed) d)
                (not (integerp d))
                (<= (+ (nfix used) (* *fn-sbud-membership-octets* (nfix m)))
                    (nfix (fn-bs-profile-max-history-octets profile)))
                (<= (nfix n) (nfix (fn-bs-profile-max-transactions profile)))
                (<= (nfix ou) (fn-heap-open-octets-bound profile observed))
                (<= (nfix on) (fn-heap-open-records-bound profile observed)))
           (<= (fn-heap-store-need profile core used n m ou on (fn-heap-nursery-trigger d nursery)) d))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(natp (:executable-counterpart natp)
                                               hft-trigger-of-a-non-integer
                                               (:type-prescription fn-heap-store-figure-octets)
                                               (:type-prescription fn-heap-nursery-trigger))
                                             (theory 'minimal-theory))
           :use ((:instance fn-heap-store-figure-holds-every-store
                            (d (fn-heap-store-figure-octets profile core nursery observed)))
                 (:instance hft-trigger-at-least-the-least
                            (d (fn-heap-store-figure-octets profile core nursery observed)))
                 (:instance hft-store-need-grows-with-the-trigger
                            (t1 8388608)
                            (t2 (fn-heap-nursery-trigger
                                 (fn-heap-store-figure-octets profile core nursery observed)
                                 nursery))))))))
(defthm hft-store-figure-holds-every-store-without-natp-d
  (implies (and (<= (fn-heap-store-figure-octets profile core nursery observed) d)
                (<= (+ (nfix used) (* *fn-sbud-membership-octets* (nfix m)))
                    (nfix (fn-bs-profile-max-history-octets profile)))
                (<= (nfix n) (nfix (fn-bs-profile-max-transactions profile)))
                (<= (nfix ou) (fn-heap-open-octets-bound profile observed))
                (<= (nfix on) (fn-heap-open-records-bound profile observed)))
           (<= (fn-heap-store-need profile core used n m ou on (fn-heap-nursery-trigger d nursery)) d))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(natp (:type-prescription fn-heap-store-figure-octets))
                                             (theory 'minimal-theory))
           :use ((:instance fn-heap-store-figure-holds-every-store)
                 (:instance hft-store-figure-holds-at-a-non-integer)))))
; The fractional D of the store-figure witnesses above, now with its
; conclusion evaluated: it holds.
(assert! (hft-sf-conclusion (+ *hft-fig* 1/2) nil 0 0 0 0 0))
(assert! (hft-sf-conclusion (+ *hft-fig* 1/2) nil *hft-used* *hft-t* *hft-mw* *hft-h* *hft-t*))

; (natp base) is needed in fn-heap-with-nursery-holds-the-trigger: the figure
; fixes BASE (nfix of a fraction is 0) and the conclusion does not.  A
; fractional base of about 1 MB, D its figure (a natural), the conclusion
; fails.
(defconst *hft-frac-base* 2000001/2)
(defconst *hft-frac-d* (fn-heap-with-nursery *hft-frac-base* *hft-nursery*))
(assert! (and (natp *hft-frac-d*)
              (not (natp *hft-frac-base*))
              (<= (fn-heap-with-nursery *hft-frac-base* *hft-nursery*) *hft-frac-d*)
              (not (<= (+ *hft-frac-base* (* 2 (fn-heap-nursery-trigger *hft-frac-d* *hft-nursery*)))
                       *hft-frac-d*))))

; Lane membership-budget (2026-09-27).  books/heap-store-figure.lisp
; fn-heap-membership-bound-holds-the-charged-memberships: witness, the small
; store's H / 320 memberships (charge within H, at the bound); counterexample,
; one more membership (charge past H) is past the bound: the hypothesis is
; what bounds them.  fn-heap-membership-term-is-at-most-twice-h: the small
; profile's membership term against 2 H.
(assert! (<= (* *fn-sbud-membership-octets* *hft-m*) *hft-h*))
(assert! (<= *hft-m* (fn-heap-membership-bound *fn-heap-small-profile*)))
(assert! (not (<= (* *fn-sbud-membership-octets* (1+ *hft-m*)) *hft-h*)))
(assert! (not (<= (1+ *hft-m*) (fn-heap-membership-bound *fn-heap-small-profile*))))
(must-fail-checked
 (defthm hft-membership-bound-without-the-charge
   (<= (nfix m) (fn-heap-membership-bound profile))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable fn-bs-profile-max-history-octets)))))
(assert! (<= (* 2 *fn-heap-membership-octets*
                (fn-heap-membership-bound *fn-heap-small-profile*))
             (* 2 *hft-h*)))


; Lane heap-bounds (row B2).  books/heap-store-figure.lisp
; fn-heap-records-retained-within-the-terms: the records' retained state
; within the figure's two record terms, for records admissible under the
; profile.  Reachable witness: the small profile, a record at every ceiling
; (a 250-octet Message-ID, a header of max-header-octets, a payload just
; that header) beside f8-reservation's two measured shapes (28-octet
; Message-ID and about 300 header octets; 250-octet Message-ID and a
; 900-octet Subject, about 1,350 header octets, in 2 KiB and 3 KiB
; payloads): the hypothesis holds and the conclusion holds.
(defun hft-rec-conclusion (profile recs)
  (declare (xargs :mode :program))
  (<= (fn-heap-records-retained-octets recs)
      (+ (* (len recs) *fn-heap-record-octets*)
         (fn-heap-record-headers-octets profile (fn-heap-records-payload-octets recs)
                                        (len recs)))))
(defconst *hft-hdr* (fn-bs-profile-field *fn-bs-pf-max-header-octets* *fn-heap-small-profile*))
(assert! (equal *hft-hdr* 16384))
(defconst *hft-recs* (list (list 250 *hft-hdr* *hft-hdr*)
                           (list 28 300 2443)
                           (list 250 1350 3072)))
(assert! (fn-heap-records-admissiblep *fn-heap-small-profile* *hft-recs*))
(assert! (hft-rec-conclusion *fn-heap-small-profile* *hft-recs*))
; The record at every ceiling is the term exactly (the witness is tight):
; 4,096 + 32 x 16,384 + 48 x 250 = 16,096 + 32 x 16,384.
(assert! (equal (fn-heap-record-retained-octets 250 *hft-hdr*)
                (+ *fn-heap-record-octets* (* 32 *hft-hdr*))))
(assert! (equal (fn-heap-record-retained-octets 250 *hft-hdr*) 540384))
; The long-header shape the 12 KiB constant was below: its term is 59,296
; octets against 23.5 KB measured over the short headers' state posting
; (f8-reservation's curve, 10,000 to 25,000 posts).
(assert! (equal (fn-heap-record-retained-octets 250 1350) 59296))
(assert! (< 12288 (fn-heap-record-retained-octets 250 1350)))
; Without the hypothesis, per conjunct (the other two holding), the
; conclusion fails: a Message-ID of 1,000 octets; a header past the
; profile's max-header-octets; a header that is not part of the payload.
(defconst *hft-rec-long-id* (list (list 1000 1000 1000)))
(assert! (and (not (fn-heap-records-admissiblep *fn-heap-small-profile* *hft-rec-long-id*))
              (<= 1000 *hft-hdr*)
              (not (hft-rec-conclusion *fn-heap-small-profile* *hft-rec-long-id*))))
(defconst *hft-rec-long-hdr* (list (list 0 100000 100000)))
(assert! (and (not (fn-heap-records-admissiblep *fn-heap-small-profile* *hft-rec-long-hdr*))
              (< *hft-hdr* 100000)
              (not (hft-rec-conclusion *fn-heap-small-profile* *hft-rec-long-hdr*))))
(defconst *hft-rec-no-payload* (list (list 0 16384 0)))
(assert! (and (not (fn-heap-records-admissiblep *fn-heap-small-profile* *hft-rec-no-payload*))
              (<= 16384 *hft-hdr*)
              (not (hft-rec-conclusion *fn-heap-small-profile* *hft-rec-no-payload*))))
(must-fail-checked
 (defthm hft-records-retained-without-admissible
   (<= (fn-heap-records-retained-octets recs)
       (+ (* (len recs) *fn-heap-record-octets*)
          (fn-heap-record-headers-octets
           profile (fn-heap-records-payload-octets recs) (len recs))))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable fn-bs-profile-field)))))
; MUTATION: the constant this lane replaced.  A record term of 12 KiB and no
; header term is below the long-header shape's retained state.
(assert! (< (* 2 12288) (fn-heap-records-retained-octets (list (list 250 1350 3072)
                                                               (list 250 1350 3072)))))

; Lane heap-bounds (row B4).  The open's chunk term is bounded by the input:
; an empty store's open holds no chunk, a store of 100 KiB at most its
; octets, and one past the quantum the quantum and R.
(assert! (equal (fn-heap-open-chunk-bound *fn-heap-small-profile* 0) 0))
(assert! (equal (fn-heap-open-chunk-bound *fn-heap-small-profile* 102400) 102400))
(assert! (equal (fn-heap-open-chunk-bound *fn-heap-small-profile* *hft-h*)
                (+ 1048576 196608)))
