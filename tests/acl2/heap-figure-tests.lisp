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
(include-book "../../books/defkeystone")
(include-book "std/testing/assert-bang" :dir :system)

(defconst *hft-core* 389141032)              ; the 69046a76 fn-host.core
(defconst *hft-nursery* (* 64 1024 1024))    ; the pre-MEM-007 +fnn-gc-nursery-octets+, passed as the explicit argument
(defconst *hft-2g* (* 2048 *fn-heap-mib*))

;; The production image's observation (hbox, 8ee846d9a): a 200,411,640-octet
;; core holding 114,644,864 octets of dynamic content.
(defconst *hft-prod-core* '(200411640 . 114644864))
(defconst *hft-big* 132000000000)
(defconst *hft-1536* (* 1536 *fn-heap-mib*))   ; OpenBSD's default login class
(defconst *hft-700m* (* 512 *fn-heap-mib*))    ; under the small store's unobserved figure (575 MiB; the name is the value before lane heap-pool)

; -----------------------------------------------------------------------------
; The figures (SBCL megabytes).  At this revision (the keyed Message-ID index
; resident, 2 x 64 x 16,384 octets in the launcher's base, PRF-1044) the
; small preset's figure is 918,886,750 octets: 877 MB on the 69046a76 core
; on a 2 GiB machine, 578 MB on the production image.
; Before the keyed index:  The small preset at its bounds: the state of
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
                983475258))
(assert! (equal (fn-heap-decide *fn-heap-small-profile* *hft-core* *hft-nursery*
                                (list *hft-2g*))
                '(:heap 938 "small" 2048)))
(assert! (equal (fn-heap-decide *fn-heap-small-profile* *hft-prod-core* *hft-nursery*
                                (list *hft-big*))
                '(:heap 639 "small" 125885)))
(assert! (equal (fn-heap-decide *fn-bs-profile-development* *hft-core* *hft-nursery*
                                (list *hft-2g*))
                '(:refused :machine-cannot-hold-profile 2750 2048)))
(assert! (equal (fn-heap-decide *fn-bs-profile-scale* *hft-core* *hft-nursery*
                                (list *hft-big*))
                '(:heap 20664 "scale" 125885)))
(assert! (equal (fn-heap-decide *fn-bs-profile-defaults* *hft-core* *hft-nursery*
                                (list *hft-big*))
                '(:refused :machine-cannot-hold-profile
                     69306705 125885)))
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
                "heap=938 MB profile=small machine=2048 MB"))
(assert! (equal (fn-heap-report-line
                 (fn-heap-decide *fn-bs-profile-development* *hft-core* *hft-nursery*
                                 (list *hft-2g*)))
                "refused machine-cannot-hold-profile heap=2750 MB machine=2048 MB"))
(assert! (equal (fn-heap-decision-exit-code '(:heap 1924 "small" 2048)) 0))
(assert! (equal (fn-heap-decision-exit-code
                 '(:refused :machine-cannot-hold-profile 7934 2048))
                1))

(defconst *hft-h* 8388608)
(defconst *hft-t* 16384)

; -----------------------------------------------------------------------------
; The refusal theorem's witnesses: both arms reached on admitted profiles.

(assert! (equal (car (fn-heap-decide *fn-heap-small-profile* *hft-core* *hft-nursery*
                                     (list (* 937 *fn-heap-mib*))))
                :refused))
(assert! (equal (car (fn-heap-decide *fn-heap-small-profile* *hft-core* *hft-nursery*
                                     (list (* 938 *fn-heap-mib*))))
                :heap))

; -----------------------------------------------------------------------------
; The small machine: the run of a small store.  A run is sized for the FULL
; store whatever the probe observed (fn-heap-operation-figure-octets-of-a-run:
; the heap must admit every later open under the same budget), so the empty
; store's run costs the open term at H = 8 MiB and T = 16,384, 130,023,424
; octets, more than before: 958 MB became 1,090 on a 512 MiB core, 586 became
; 728 on the OpenBSD core.  Witness at the bound,
; and per hypothesis a counterexample.

(assert! (equal (fn-heap-operation-decide :run *fn-heap-small-profile* (* 512 *fn-heap-mib*)
                                          *hft-nursery* (list *hft-1536*) '(0 . 0))
                '(:heap 1090 "small" 1536)))
(assert! (equal (fn-heap-operation-decide :run *fn-heap-small-profile* (* 512 *fn-heap-mib*)
                                          *hft-nursery* (list *hft-2g*) '(0 . 0))
                '(:heap 1090 "small" 2048)))
; a core of more than 512 MiB of dynamic content: 1,150 MiB on 1,536 and
; 1,700 MiB on 2,048 are refused.  (Lane heap-bounds' uncharged header term
; had even the 512 MiB core refused on 1,536 MiB: 1,777 MB.)
(assert! (equal (fn-heap-operation-decide :run *fn-heap-small-profile* (* 1150 *fn-heap-mib*)
                                          *hft-nursery* (list *hft-1536*) '(0 . 0))
                '(:refused :machine-cannot-hold-profile 1728 1536)))
(assert! (equal (fn-heap-operation-decide :run *fn-heap-small-profile* (* 1700 *fn-heap-mib*)
                                          *hft-nursery* (list *hft-2g*) '(0 . 0))
                '(:refused :machine-cannot-hold-profile 2278 2048)))
; (no nursery hypothesis: even a 1 GiB cap is accepted, the trigger being a
; sixteenth of the space)
(assert! (equal (car (fn-heap-operation-decide :run *fn-heap-small-profile*
                                               (* 512 *fn-heap-mib*) (* 1024 *fn-heap-mib*)
                                               (list *hft-1536*) '(0 . 0)))
                :heap))
; a machine under the figure (850 MiB)
(assert! (equal (fn-heap-operation-decide :run *fn-heap-small-profile* (* 512 *fn-heap-mib*)
                                          *hft-nursery* (list (* 850 *fn-heap-mib*)) '(0 . 0))
                '(:refused :machine-cannot-hold-profile 1090 850)))
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
                '(:heap 593 "small" 2048)))
; The run alone ignores what the probe saw: the same store, observed or not.
(assert! (equal (fn-heap-operation-decide :run *fn-heap-small-profile* *hft-bsd-core*
                                          *hft-nursery* (list *hft-2g*) '(100000 . 50))
                (fn-heap-operation-decide :run *fn-heap-small-profile* *hft-bsd-core*
                                          *hft-nursery* (list *hft-2g*) nil)))
; `init' holds no store: its decision is the store-less figure's megabytes
; (fn-heap-storeless-figure-octets: the store-less heap, or the image's dynamic
; content with the collector's room when larger), whatever profile it writes.
; 586 MB before lane b-init-heap (the small store's empty figure).
(assert! (equal (fn-heap-operation-decide :init *fn-heap-small-profile* *hft-bsd-core*
                                          *hft-nursery* (list *hft-2g*) nil)
                (list :heap (fn-heap-mb-of (fn-heap-storeless-figure-octets *hft-bsd-core*
                                                                             *hft-nursery*))
                      "small" 2048)))
; By the store's observed history: an empty store reclaims in 888 MB, the
; measured 3,000-article store in 1,639 MB (its six list copies), a store of
; 100,000 octets in 50 files compacts, recovers and runs in 888 MB, where an
; unobserved run keeps the bounds' 942 MB (832 and 887 before the articles in
; flight, lane zero-copy-commit; 997 and 1,048 before membership-budget).  An observation past H or T
; changes nothing; octets without a count take T's records.
(assert! (equal (fn-heap-operation-decide :reclaim *fn-heap-small-profile* *hft-bsd-core*
                                          *hft-nursery* (list *hft-2g*) '(0 . 0))
                '(:heap 586 "small" 2048)))
(assert! (equal (fn-heap-operation-decide :reclaim *fn-heap-small-profile* *hft-bsd-core*
                                          *hft-nursery* (list *hft-4g*) '(7271160 . 3000))
                '(:heap 1639 "small" 4096)))
(assert! (equal (fn-heap-operation-decide :compact *fn-heap-small-profile* *hft-bsd-core*
                                          *hft-nursery* (list *hft-2g*) '(100000 . 50))
                '(:heap 593 "small" 2048)))
(assert! (equal (fn-heap-operation-decide :recover *fn-heap-small-profile* *hft-bsd-core*
                                          *hft-nursery* (list *hft-2g*) '(100000 . 50))
                '(:heap 593 "small" 2048)))
(assert! (equal (fn-heap-operation-decide :run *fn-heap-small-profile* *hft-bsd-core*
                                          *hft-nursery* (list *hft-2g*) '(100000 . 50))
                '(:heap 728 "small" 2048)))
(assert! (equal (fn-heap-operation-decide :run *fn-heap-small-profile* *hft-bsd-core*
                                          *hft-nursery* (list *hft-2g*) nil)
                '(:heap 728 "small" 2048)))
(assert! (equal (fn-heap-operation-decide :recover *fn-heap-small-profile* *hft-bsd-core*
                                          *hft-nursery* (list *hft-2g*) 100000)
                '(:heap 630 "small" 2048)))
(assert! (equal (fn-heap-operation-decide :reclaim *fn-heap-small-profile* *hft-bsd-core*
                                          *hft-nursery* (list *hft-2g*)
                                          (cons (* 2 8388608) (* 2 16384)))
                (fn-heap-operation-decide :reclaim *fn-heap-small-profile* *hft-bsd-core*
                                          *hft-nursery* (list *hft-2g*) nil)))
; Under OpenBSD's default 1,536 MiB data limit the small store's reclaim and
; run at the bounds: the reclaim observed empty is accepted, and so is the run, which ignores the observation.
(assert! (equal (fn-heap-operation-decide :reclaim *fn-heap-small-profile* *hft-bsd-core*
                                          *hft-nursery* (list *hft-1536*) nil)
                '(:refused :machine-cannot-hold-profile 1843 1536)))
(assert! (equal (fn-heap-operation-decide :reclaim *fn-heap-small-profile* *hft-bsd-core*
                                          *hft-nursery* (list *hft-1536*) '(0 . 0))
                '(:heap 586 "small" 1536)))
(assert! (equal (fn-heap-operation-decide :run *fn-heap-small-profile* *hft-bsd-core*
                                          *hft-nursery* (list *hft-1536*) '(0 . 0))
                '(:heap 728 "small" 1536)))
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

; books/heap-store-figure's keystones directly.  fn-heap-with-nursery-holds-
; the-trigger: witness at the small store's base (the trigger a sixteenth of
; the space), and without D at least the figure: one megabyte less than the
; base itself.

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
; Audit packet G3-6 (lane audit-fixes): the natp hypothesis of
; fn-heap-with-nursery-holds-the-trigger.  (natp d) is redundant: a D at
; least the (natural) figure that is not an integer has trigger 8 MiB (nfix
; of a non-integer is 0).  The weakened theorem is proved here.
(local (defthm hft-trigger-of-a-non-integer
         (implies (not (integerp d))
                  (equal (fn-heap-nursery-trigger d nursery) 8388608))
         :hints (("Goal" :in-theory (enable fn-heap-nursery-trigger)))))
(local (defthm hft-trigger-at-least-the-least
         (<= 8388608 (fn-heap-nursery-trigger d nursery))
         :rule-classes nil
         :hints (("Goal" :in-theory (enable fn-heap-nursery-trigger)))))
(defthm hft-with-nursery-holds-the-trigger-without-natp-d
  (implies (and (natp base) (<= (fn-heap-with-nursery base nursery) d))
           (<= (+ base (* 2 (fn-heap-nursery-trigger d nursery))) d))
  :rule-classes nil
  :hints (("Goal" :cases ((natp d)))
          ("Subgoal 1" :use ((:instance fn-heap-with-nursery-holds-the-trigger)))
          ("Subgoal 2" :in-theory (enable fn-heap-with-nursery fn-heap-nursery-trigger))))
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

;; Lane heap-bounds (row B2), restated by lane heap-pool (B9).
;; books/heap-store-figure.lisp fn-heap-records-retained-within-the-terms:
;; the records' retained state, with the collector's copy, within the
;; figure's two record terms at N = their count and USED = their charged
;; octets (payloads and header charges, the history budget's).  Reachable
;; witness: a record at every ceiling (a 250-octet Message-ID, a header of
;; the small profile's max-header-octets, a payload just that header)
;; beside f8-reservation's two measured shapes (28-octet Message-ID and about
;; 300 header octets; 250-octet Message-ID and a 900-octet Subject, about
;; 1,350 header octets): the hypothesis and the conclusion hold.
(defun hft-rec-conclusion (recs)
  (declare (xargs :mode :program))
  (<= (* 2 (fn-heap-records-retained-octets recs))
      (+ (* 2 (len recs) *fn-heap-record-octets*)
         (* *fn-heap-charge-heap-octets* (fn-heap-records-charged-octets recs)))))
(defconst *hft-hdr* (fn-bs-profile-field *fn-bs-pf-max-header-octets* *fn-heap-small-profile*))
(assert! (equal *hft-hdr* 16384))
(defconst *hft-recs* (list (list 250 *hft-hdr* *hft-hdr*)
                           (list 28 300 2443)
                           (list 250 1350 3072)))
(assert! (fn-heap-records-admissiblep *hft-recs*))
(assert! (hft-rec-conclusion *hft-recs*))
; Every record is under its term: the header state twice is 8 heap octets a
; charged octet of header (2 x 32 = 8 x 8 a header octet); the Message-ID
; state twice (2 x 16, the keyed index's 64 octets a record, PRF-1044) is
; under its charge (8 x 12), so the bound is no longer tight.
(assert! (<= (* 2 (fn-heap-records-retained-octets *hft-recs*))
             (+ (* 2 3 *fn-heap-record-octets*)
                (* 8 (+ (fn-heap-record-charge 250 *hft-hdr*)
                        (fn-heap-record-charge 28 300)
                        (fn-heap-record-charge 250 1350))))))
(assert! (equal (* 2 (fn-heap-records-retained-octets *hft-recs*))
                1196032))
; The long-header shape the 12 KiB constant was below: 51,360 octets
; (51,360 twice is within 2 x 4,160 + 8 x 13,800, its charge 8 x 1,350 +
; 12 x 250 = 13,800 history octets beside its 3,072 of payload).
; THE SWITCH (PRF-1037): 4,096 fixed + 64 index words + 32 x 1,350 header
; octets + 16 x 250 Message-ID octets (was 59,296 at 48 an octet).
(assert! (equal (fn-heap-record-retained-octets 250 1350) 51360))
(assert! (equal (fn-heap-record-charge 250 1350) 13800))
; Without the hypothesis: a record without its payload's octets (two
; elements) is charged nothing and retains its header's state: the
; conclusion fails.
(defconst *hft-rec-short* (list (list 250 1350)))
(assert! (and (not (fn-heap-records-admissiblep *hft-rec-short*))
              (not (hft-rec-conclusion *hft-rec-short*))))
(must-fail-checked
 (defthm hft-records-retained-without-admissible
   (<= (* 2 (fn-heap-records-retained-octets recs))
       (+ (* 2 (len recs) *fn-heap-record-octets*)
          (* *fn-heap-charge-heap-octets* (fn-heap-records-charged-octets recs))))
   :rule-classes nil
   :hints (("Goal" :induct (fn-heap-records-retained-octets recs)
            :in-theory (enable fn-heap-record-retained-octets fn-heap-record-charge)))))
; A header past its payload is admissible now (the charge counts it): the
; conclusion holds.
(assert! (and (fn-heap-records-admissiblep (list (list 0 16384 0)))
              (hft-rec-conclusion (list (list 0 16384 0)))))
; MUTATION: the constant lane heap-bounds replaced.  A record term of 12 KiB
; and no header term is below the long-header shape's retained state.
(assert! (< (* 2 12288) (fn-heap-records-retained-octets (list (list 250 1350 3072)
                                                               (list 250 1350 3072)))))

; Lane heap-bounds (row B4).  The open's chunk term is bounded by the input:
; an empty store's open holds no chunk, a store of 100 KiB at most its
; octets, and one past the quantum the quantum and R.
(assert! (equal (fn-heap-open-chunk-bound *fn-heap-small-profile* 0) 0))
(assert! (equal (fn-heap-open-chunk-bound *fn-heap-small-profile* 102400) 102400))
(assert! (equal (fn-heap-open-chunk-bound *fn-heap-small-profile* *hft-h*)
                (+ 1048576 196608)))

; -----------------------------------------------------------------------------
; ADMISSION-RESERVES-NOT-REOPEN (N's ruling B): a run's heap is the full
; store's, so a heap decided on the EMPTY store reopens the store grown to
; the profile's bounds.  The F4 store of train 45 (development, 100,000
; transactions, 256 MiB of history, 196,608-octet records), the production
; image's core.  The run's figure no longer depends on what the probe saw:
; 7,867,993,434 octets either way, where the empty store's was 7,046,630,746
; -- 821,362,688 octets (783.3 MiB) of reserved dynamic space more, the open
; term at H and T (64 x min(H, 1 MiB + R) + 2 H + 2,048 T) where the empty
; store's is 0.
(defconst *hft-filled*
  (fn-bs-profile-resolve
   (list :development
         (list (cons *fn-bs-pf-max-transactions* 100000)
               (cons *fn-bs-pf-max-history-octets* 268435456)
               (cons *fn-bs-pf-max-record-octets* 196608)
               (cons *fn-bs-pf-max-groups-per-article* 16)
               (cons *fn-bs-pf-max-open-suffix* 128)))
   nil))

(defconst *hft-fixed-run*
  (fn-heap-operation-decide :run *hft-filled* *hft-prod-core* *hft-nursery*
                            (list *hft-big*) '(0 . 0)))

(assert! (equal *hft-fixed-run* '(:heap 7504 "custom" 125885)))
(assert! (equal (fn-heap-operation-figure-octets :run *hft-filled* *hft-prod-core*
                                                 *hft-nursery* '(0 . 0))
                7867993434))
(assert! (equal (- 7867993434 7046630746) 821362688))
; The witness: the heap decided on the empty store admits the figure of the
; store as F4 left it (a 9.4 MB state checkpoint and journal, the count not
; observed) and the store at the profile's bounds.
(assert! (<= (fn-heap-store-figure-octets *hft-filled* *hft-prod-core* *hft-nursery*
                                          '(9437184))
             (* *fn-heap-mib* (fn-heap-decision-mb *hft-fixed-run*))))
(assert! (<= (fn-heap-store-figure-octets *hft-filled* *hft-prod-core* *hft-nursery*
                                          '(268435456 . 100000))
             (* *fn-heap-mib* (fn-heap-decision-mb *hft-fixed-run*))))
(assert! (<= (fn-heap-store-figure-octets *hft-filled* *hft-prod-core* *hft-nursery* nil)
             (* *fn-heap-mib* (fn-heap-decision-mb *hft-fixed-run*))))
; The must-fail: sized by the observation (the rule before), the same fixed
; heap is below the grown store's figure, and the open refuses.
(assert! (< (* *fn-heap-mib*
               (fn-heap-decision-mb
                (fn-heap-operation-decide :status *hft-filled* *hft-prod-core*
                                          *hft-nursery* (list *hft-big*) '(0 . 0))))
            (fn-heap-store-figure-octets *hft-filled* *hft-prod-core* *hft-nursery*
                                         '(9437184))))
(must-fail-checked
 (defthm hft-run-observed-holds-every-later-open
   (<= (fn-heap-store-figure-octets profile core nursery later)
       (fn-heap-store-figure-octets profile core nursery '(0 . 0)))
   :rule-classes nil))

; THE LIVE-RECLAIM OPT-IN AT THE FULL-STORE RUN FIGURE (tests/test_native_reclaim_walk.py
; test_the_opt_in_is_the_only_change_to_the_figure).  The opt-in adds the pass's EXCESS over
; the open's transient at the bounds (fn-heap-store-reclaim-base-octets): one reserve holds the
; larger of the two (fn-heap-open-and-excess-is-the-larger).
; Positive instance: the native test's profile (development, T = 16384) -- the open term at the
; bounds (1,247,858,048) already covers the pass (559,333,376): excess 0, the two figures equal.
(assert! (let ((d (update-nth *fn-bs-pf-max-transactions* 16384 *fn-bs-profile-development*)))
           (and (fn-bs-profile-admittedp d)
                (equal (fn-heap-reclaim-excess-octets d (fn-heap-open-octets-bound d nil)
                                                      (fn-heap-open-records-bound d nil))
                       0)
                (equal (fn-heap-store-live-figure-octets d *hft-core* *hft-nursery* nil)
                       (fn-heap-store-figure-octets d *hft-core* *hft-nursery* nil)))))
; Tooth: the opt-in still matters.  At the scale preset the pass's demand (9,736,011,776)
; exceeds the open term at the bounds (2,782,973,312), so the opt-in figure is STRICTLY larger;
; a figure that dropped the opt-in's term would fail here.
(assert! (let ((d *fn-bs-profile-scale*))
           (and (< 0 (fn-heap-reclaim-excess-octets d (fn-heap-open-octets-bound d nil)
                                                    (fn-heap-open-records-bound d nil)))
                (< (fn-heap-store-figure-octets d *hft-core* *hft-nursery* nil)
                   (fn-heap-store-live-figure-octets d *hft-core* *hft-nursery* nil)))))

;; The evidence package of the store-less keystone (ruling 22): generated
;; teeth over the subject the host calls (host/native/heap.lisp
;; fnn-heap-reservation through fn-heap-reserve-operation-decide).
; The scale preset, the store-less action's witness profile.
(defconst *hft-scale* (fn-bs-profile-resolve '(:scale nil) nil))
(defteeth fn-heap-operation-decide-of-a-storeless-action
  :subject fn-heap-reserve-operation-decide
  :claim
  (let ((decision (fn-heap-operation-decide action profile core nursery observations
                                            observed)))
    (((storeless (fn-heap-storeless-action-p action))
      (admitted (fn-bs-profile-admittedp profile))
      (accepted (equal (car decision) :heap)))
     (and (equal (fn-heap-decision-mb decision)
                 (fn-heap-mb-of (fn-heap-storeless-figure-octets core nursery)))
          (<= (* *fn-heap-mib* (fn-heap-decision-mb decision))
              (fn-heap-machine-octets observations)))))
  :witness ((action :init) (profile *hft-scale*) (core *hft-prod-core*) (nursery *hft-nursery*)
            (observations (list (* 24576 *fn-heap-mib*))) (observed nil))
  :breaks
  ((storeless ((action :run) (profile *fn-heap-small-profile*) (observations (list *hft-2g*))))
   (admitted ((profile nil) (core (* 100 *fn-heap-mib*)) (nursery 0)
              (observations (list (* 900 *fn-heap-mib*)))))
   (accepted ((observations (list *hft-700m*)))))
  :mutations
  ((init-sized-as-the-store
    (:conclusion (and (equal (fn-heap-decision-mb decision)
                             (fn-heap-mb-of (fn-heap-store-figure-octets profile core nursery nil)))
                      (<= (* *fn-heap-mib* (fn-heap-decision-mb decision))
                          (fn-heap-machine-octets observations))))
    () :fault "init sized by the store figure of the profile it writes (before lane b-init-heap).")))

(defteeth-check (fn-heap-operation-decide-of-a-storeless-action))
