; Teeth for books/heap-figure (PRF-198): the figures of the presets on the
; 69046a76 image's core, the keystone's reachable witness and one
; counterexample and one must-fail per hypothesis, the small preset on a
; small machine, init's default, and the report line the host prints.
(in-package "ACL2")
(include-book "../../books/heap-figure")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/assert-bang" :dir :system)

(defconst *hft-core* 389141032)              ; the 69046a76 fn-host.core
(defconst *hft-nursery* (* 64 1024 1024))    ; +fnn-gc-nursery-octets+
(defconst *hft-2g* (* 2048 *fn-heap-mib*))

; The keystone's conclusion, and its hypotheses one by one.
(defun hft-conclusion (profile core nursery observations used)
  (declare (xargs :mode :program))
  (let ((decision (fn-heap-decide profile core nursery observations)))
    (and (<= (+ core nursery
                (* 2 *fn-heap-octets-per-list-octet*
                   (+ used used (fn-bs-profile-max-record-octets profile)))
                (* 2 (fn-ock-capture-budget profile)))
             (* *fn-heap-mib* (fn-heap-decision-mb decision)))
         (<= (* *fn-heap-mib* (fn-heap-decision-mb decision))
             (fn-heap-machine-octets observations)))))

(defun hft-hyps (profile core nursery observations used)
  (declare (xargs :mode :program))
  (list (fn-bs-profile-admittedp profile)
        (equal (car (fn-heap-decide profile core nursery observations)) :heap)
        (<= used (fn-bs-profile-max-history-octets profile))
        (natp core)
        (natp nursery)))

; -----------------------------------------------------------------------------
; The figures (SBCL megabytes; the machine 2 GiB).

(assert! (equal (fn-heap-figure-octets *fn-heap-small-profile* *hft-core* *hft-nursery*)
                1051710130))
(assert! (equal (fn-heap-decide *fn-heap-small-profile* *hft-core* *hft-nursery*
                                (list *hft-2g*))
                '(:heap 1003 "small" 2048)))
(assert! (equal (fn-heap-decide *fn-bs-profile-development* *hft-core* *hft-nursery*
                                (list *hft-2g*))
                '(:refused :machine-cannot-hold-profile 2673 2048)))
(assert! (equal (fn-heap-decide *fn-bs-profile-scale* *hft-core* *hft-nursery*
                                (list 132000000000))
                '(:heap 54753 "scale" 125885)))
(assert! (equal (fn-heap-decide *fn-bs-profile-defaults* *hft-core* *hft-nursery*
                                (list 132000000000))
                '(:refused :machine-cannot-hold-profile 73402933 125885)))
; No store: the image must fit, then the store-less figure, 1,024 MB
; whatever the machine (PKT-686 item 3), not the machine.
(assert! (equal (fn-heap-decide nil *hft-core* *hft-nursery* (list *hft-2g*))
                '(:heap 1024 "none" 2048)))
(assert! (equal (fn-heap-decide nil *hft-core* *hft-nursery* (list 132000000000))
                '(:heap 1024 "none" 125885)))
(assert! (equal (fn-heap-decide nil *hft-core* *hft-nursery* (list (* 256 *fn-heap-mib*)))
                '(:refused :machine-cannot-hold-image 436 256)))
(assert! (equal (fn-heap-decide *fn-heap-small-profile* *hft-core* *hft-nursery* nil)
                '(:refused :machine-memory-unobserved 0 0)))

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
                "heap=1003 MB profile=small machine=2048 MB"))
(assert! (equal (fn-heap-report-line
                 (fn-heap-decide *fn-bs-profile-development* *hft-core* *hft-nursery*
                                 (list *hft-2g*)))
                "refused machine-cannot-hold-profile heap=2673 MB machine=2048 MB"))
(assert! (equal (fn-heap-decision-exit-code '(:heap 1003 "small" 2048)) 0))
(assert! (equal (fn-heap-decision-exit-code
                 '(:refused :machine-cannot-hold-profile 2673 2048))
                1))

; -----------------------------------------------------------------------------
; The keystone: a reachable witness with every hypothesis and the conclusion
; (the small store full to H), then per hypothesis a counterexample where the
; others hold, it fails, and the conclusion fails, and the must-fail of the
; theorem without it.  Each must-fail runs under the keystone's own hints, so
; it shows the keystone's proof fails without that hypothesis (open, the five
; searches took 23.4, 3.6, 3.9, 3.9 and 3.9 s on persvati; hinted, 0.1 s each);
; the concrete counterexample above each one is the evidence of falsity.

(assert! (equal (hft-hyps *fn-heap-small-profile* *hft-core* *hft-nursery*
                          (list *hft-2g*) 8388608)
                '(t t t t t)))
(assert! (hft-conclusion *fn-heap-small-profile* *hft-core* *hft-nursery*
                         (list *hft-2g*) 8388608))

; Without the admitted profile: no profile, an image that exactly fills the
; store-less figure's 1,024 MiB; the capture buffer's framing no longer fits.
(assert! (equal (hft-hyps nil (- (* 1024 *fn-heap-mib*) *hft-nursery*) *hft-nursery*
                          (list *hft-2g*) 0)
                '(nil t t t t)))
(assert! (not (hft-conclusion nil (- (* 1024 *fn-heap-mib*) *hft-nursery*) *hft-nursery*
                              (list *hft-2g*) 0)))
(must-fail
 (defthm hft-without-admitted
   (let ((decision (fn-heap-decide profile core nursery observations)))
     (implies (and (equal (car decision) :heap)
                   (<= used (fn-bs-profile-max-history-octets profile))
                   (natp core) (natp nursery))
              (<= (+ core nursery
                     (* 2 *fn-heap-octets-per-list-octet*
                        (+ used used (fn-bs-profile-max-record-octets profile)))
                     (* 2 (fn-ock-capture-budget profile)))
                  (* *fn-heap-mib* (fn-heap-decision-mb decision)))))
   :hints (("Goal" :in-theory (e/d () (fn-ock-capture-budget
                                       fn-bs-profile-admittedp
                                       fn-bs-profile-max-history-octets
                                       fn-bs-profile-max-record-octets
                                       fn-bs-profile-field
                                       fn-heap-profile-word))
            :use ((:instance fn-heap-mb-of-covers
                             (octets (fn-heap-figure-octets profile core nursery))))))))

; Without the accepted decision: the development profile on 2 GiB is refused.
(assert! (equal (hft-hyps *fn-bs-profile-development* *hft-core* *hft-nursery*
                          (list *hft-2g*) 0)
                '(t nil t t t)))
(assert! (not (hft-conclusion *fn-bs-profile-development* *hft-core* *hft-nursery*
                              (list *hft-2g*) 0)))
(must-fail
 (defthm hft-without-heap
   (let ((decision (fn-heap-decide profile core nursery observations)))
     (implies (and (fn-bs-profile-admittedp profile)
                   (<= used (fn-bs-profile-max-history-octets profile))
                   (natp core) (natp nursery))
              (<= (+ core nursery
                     (* 2 *fn-heap-octets-per-list-octet*
                        (+ used used (fn-bs-profile-max-record-octets profile)))
                     (* 2 (fn-ock-capture-budget profile)))
                  (* *fn-heap-mib* (fn-heap-decision-mb decision)))))
   :hints (("Goal" :in-theory (e/d () (fn-ock-capture-budget
                                       fn-bs-profile-admittedp
                                       fn-bs-profile-max-history-octets
                                       fn-bs-profile-max-record-octets
                                       fn-bs-profile-field
                                       fn-heap-profile-word))
            :use ((:instance fn-heap-mb-of-covers
                             (octets (fn-heap-figure-octets profile core nursery))))))))

; Without the history bound: a history past H.
(assert! (equal (hft-hyps *fn-heap-small-profile* *hft-core* *hft-nursery*
                          (list *hft-2g*) (expt 2 40))
                '(t t nil t t)))
(assert! (not (hft-conclusion *fn-heap-small-profile* *hft-core* *hft-nursery*
                              (list *hft-2g*) (expt 2 40))))
(must-fail
 (defthm hft-without-history-bound
   (let ((decision (fn-heap-decide profile core nursery observations)))
     (implies (and (fn-bs-profile-admittedp profile)
                   (equal (car decision) :heap)
                   (natp core) (natp nursery))
              (<= (+ core nursery
                     (* 2 *fn-heap-octets-per-list-octet*
                        (+ used used (fn-bs-profile-max-record-octets profile)))
                     (* 2 (fn-ock-capture-budget profile)))
                  (* *fn-heap-mib* (fn-heap-decision-mb decision)))))
   :hints (("Goal" :in-theory (e/d () (fn-ock-capture-budget
                                       fn-bs-profile-admittedp
                                       fn-bs-profile-max-history-octets
                                       fn-bs-profile-max-record-octets
                                       fn-bs-profile-field
                                       fn-heap-profile-word))
            :use ((:instance fn-heap-mb-of-covers
                             (octets (fn-heap-figure-octets profile core nursery))))))))

; Without a natural core: a fractional core the figure reads as 0.
(assert! (equal (hft-hyps *fn-heap-small-profile* (+ 1000000000 1/2) *hft-nursery*
                          (list *hft-2g*) 0)
                '(t t t nil t)))
(assert! (not (hft-conclusion *fn-heap-small-profile* (+ 1000000000 1/2) *hft-nursery*
                              (list *hft-2g*) 0)))
(must-fail
 (defthm hft-without-natp-core
   (let ((decision (fn-heap-decide profile core nursery observations)))
     (implies (and (fn-bs-profile-admittedp profile)
                   (equal (car decision) :heap)
                   (<= used (fn-bs-profile-max-history-octets profile))
                   (natp nursery))
              (<= (+ core nursery
                     (* 2 *fn-heap-octets-per-list-octet*
                        (+ used used (fn-bs-profile-max-record-octets profile)))
                     (* 2 (fn-ock-capture-budget profile)))
                  (* *fn-heap-mib* (fn-heap-decision-mb decision)))))
   :hints (("Goal" :in-theory (e/d () (fn-ock-capture-budget
                                       fn-bs-profile-admittedp
                                       fn-bs-profile-max-history-octets
                                       fn-bs-profile-max-record-octets
                                       fn-bs-profile-field
                                       fn-heap-profile-word))
            :use ((:instance fn-heap-mb-of-covers
                             (octets (fn-heap-figure-octets profile core nursery))))))))

; Without a natural nursery: the same with the nursery.
(assert! (equal (hft-hyps *fn-heap-small-profile* *hft-core* (+ 1000000000 1/2)
                          (list *hft-2g*) 0)
                '(t t t t nil)))
(assert! (not (hft-conclusion *fn-heap-small-profile* *hft-core* (+ 1000000000 1/2)
                              (list *hft-2g*) 0)))
(must-fail
 (defthm hft-without-natp-nursery
   (let ((decision (fn-heap-decide profile core nursery observations)))
     (implies (and (fn-bs-profile-admittedp profile)
                   (equal (car decision) :heap)
                   (<= used (fn-bs-profile-max-history-octets profile))
                   (natp core))
              (<= (+ core nursery
                     (* 2 *fn-heap-octets-per-list-octet*
                        (+ used used (fn-bs-profile-max-record-octets profile)))
                     (* 2 (fn-ock-capture-budget profile)))
                  (* *fn-heap-mib* (fn-heap-decision-mb decision)))))
   :hints (("Goal" :in-theory (e/d () (fn-ock-capture-budget
                                       fn-bs-profile-admittedp
                                       fn-bs-profile-max-history-octets
                                       fn-bs-profile-max-record-octets
                                       fn-bs-profile-field
                                       fn-heap-profile-word))
            :use ((:instance fn-heap-mb-of-covers
                             (octets (fn-heap-figure-octets profile core nursery))))))))

; -----------------------------------------------------------------------------
; The refusal theorem's witnesses: both arms reached on admitted profiles.

(assert! (equal (car (fn-heap-decide *fn-heap-small-profile* *hft-core* *hft-nursery*
                                     (list (* 1002 *fn-heap-mib*))))
                :refused))
(assert! (equal (car (fn-heap-decide *fn-heap-small-profile* *hft-core* *hft-nursery*
                                     (list (* 1003 *fn-heap-mib*))))
                :heap))

; -----------------------------------------------------------------------------
; The small machine: witness at the bound, and per hypothesis a counterexample.

(assert! (equal (car (fn-heap-decide *fn-heap-small-profile* (* 512 *fn-heap-mib*)
                                     *hft-nursery* (list (* 1536 *fn-heap-mib*))))
                :heap))
; a core past 512 MiB
(assert! (equal (car (fn-heap-decide *fn-heap-small-profile* (* 1024 *fn-heap-mib*)
                                     *hft-nursery* (list (* 1536 *fn-heap-mib*))))
                :refused))
; a nursery past 64 MiB
(assert! (equal (car (fn-heap-decide *fn-heap-small-profile* *hft-core*
                                     (* 1024 *fn-heap-mib*) (list (* 1536 *fn-heap-mib*))))
                :refused))
; a machine under 1536 MiB
(assert! (equal (car (fn-heap-decide *fn-heap-small-profile* (* 512 *fn-heap-mib*)
                                     *hft-nursery* (list (* 1024 *fn-heap-mib*))))
                :refused))
; a machine that is not a positive integer is no observation
(assert! (equal (car (fn-heap-decide *fn-heap-small-profile* *hft-core* *hft-nursery*
                                     (list (+ (* 1536 *fn-heap-mib*) 1/2))))
                :refused))
(must-fail
 (defthm hft-small-without-machine-bound
   (implies (and (<= core (* 512 *fn-heap-mib*))
                 (<= nursery (* 64 *fn-heap-mib*))
                 (posp machine))
            (equal (car (fn-heap-decide *fn-heap-small-profile* core nursery
                                        (list machine)))
                   :heap))
   :hints (("Goal" :in-theory (enable fn-heap-mb-of)))))

; -----------------------------------------------------------------------------
; init's default.

(assert! (equal (fn-heap-init-request '(:default nil) *hft-2g*) *fn-heap-small-request*))
(assert! (equal (fn-bs-profile-resolve (fn-heap-init-request '(:default nil) *hft-2g*) nil)
                *fn-heap-small-profile*))
(assert! (equal (fn-heap-init-request '(:default nil) (* 8 1024 *fn-heap-mib*))
                '(:default nil)))
(assert! (equal (fn-heap-init-request '(:development nil) *hft-2g*) '(:development nil)))
(assert! (equal (fn-heap-init-request '(:default ((2 . 100))) *hft-2g*)
                '(:default ((2 . 100)))))

; -----------------------------------------------------------------------------
; The store-less figure (PKT-686 item 3).  fn-heap-storeless-decide-is-small-
; and-fits: the witness is `fn --version' under the OpenBSD guest's 4 GiB
; datasize on its 195,856,696-octet core (before: the whole 4,096 MB as heap,
; and mmap refused the core beside it); then each hypothesis.

(defconst *hft-bsd-core* 195856696)
(defconst *hft-4g* (* 4096 *fn-heap-mib*))
(defconst *hft-1536* (* 1536 *fn-heap-mib*))   ; OpenBSD's default login class

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
(must-fail
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
; The operation's figure (PKT-686).  fn-heap-operation-decide-holds-the-
; operation: reachable witnesses (`store reclaim' of the small store full to
; H on a 2 GiB machine with the 195,856,696-octet core the OpenBSD guest
; built, the same on the 69046a76 core on 4 GiB, and -- item 1 -- the
; measured 3,000-article store observed at 7,271,160 octets), then per
; hypothesis a counterexample where the others hold and the conclusion
; fails, and the must-fail of the keystone without it.

(defun hft-op-conclusion (action profile core nursery observations observed used)
  (declare (xargs :mode :program))
  (let ((decision (fn-heap-operation-decide action profile core nursery observations
                                            observed)))
    (and (<= (+ core nursery
                (* 2 *fn-heap-octets-per-list-octet*
                   (+ (* (fn-heap-operation-history-copies action) used)
                      (fn-bs-profile-max-record-octets profile)
                      (* *fn-heap-header-copies* (fn-bs-profile-field 17 profile))))
                (* 2 (fn-ock-capture-budget profile)))
             (* *fn-heap-mib* (fn-heap-decision-mb decision)))
         (<= (* *fn-heap-mib* (fn-heap-decision-mb decision))
             (fn-heap-machine-octets observations)))))

(defun hft-op-hyps (action profile core nursery observations observed used)
  (declare (xargs :mode :program))
  (list (fn-bs-profile-admittedp profile)
        (equal (car (fn-heap-operation-decide action profile core nursery observations
                                              observed))
               :heap)
        (<= used (fn-heap-operation-history-octets action profile observed))
        (natp core)
        (natp nursery)))

; The compaction verbs count six copies, every other command two; a
; serve-class command's decision is fn-heap-decide's, whatever it observed.
(assert! (equal (fn-heap-operation-history-copies :reclaim) 6))
(assert! (equal (fn-heap-operation-history-copies :compact) 6))
(assert! (equal (fn-heap-operation-history-copies :run) 2))
(assert! (equal (fn-heap-operation-decide :reclaim *fn-heap-small-profile* *hft-bsd-core*
                                          *hft-nursery* (list *hft-2g*) nil)
                '(:heap 1843 "small" 2048)))
(assert! (equal (fn-heap-operation-decide :run *fn-heap-small-profile* *hft-bsd-core*
                                          *hft-nursery* (list *hft-2g*) 100000)
                (fn-heap-decide *fn-heap-small-profile* *hft-bsd-core* *hft-nursery*
                                (list *hft-2g*))))
; Item 1: the offline verbs by the store's observed history.  An empty store
; reclaims in 307 MB, the measured 3,000-article store (7,271,160 octets) in
; 1,639 MB, a store of 100,000 octets in 325 MB; its recover in 313 MB where
; `run' keeps H's 819 MB.  An observation past H changes nothing.
(assert! (equal (fn-heap-operation-decide :reclaim *fn-heap-small-profile* *hft-bsd-core*
                                          *hft-nursery* (list *hft-2g*) 0)
                '(:heap 307 "small" 2048)))
(assert! (equal (fn-heap-operation-decide :reclaim *fn-heap-small-profile* *hft-bsd-core*
                                          *hft-nursery* (list *hft-2g*) 7271160)
                '(:heap 1639 "small" 2048)))
(assert! (equal (fn-heap-operation-decide :compact *fn-heap-small-profile* *hft-bsd-core*
                                          *hft-nursery* (list *hft-2g*) 100000)
                '(:heap 325 "small" 2048)))
(assert! (equal (fn-heap-operation-decide :recover *fn-heap-small-profile* *hft-bsd-core*
                                          *hft-nursery* (list *hft-2g*) 100000)
                '(:heap 313 "small" 2048)))
(assert! (equal (fn-heap-operation-decide :run *fn-heap-small-profile* *hft-bsd-core*
                                          *hft-nursery* (list *hft-2g*) 100000)
                '(:heap 819 "small" 2048)))
; A full store's files exceed H (the budget counts payloads, the files hold
; whole records): an observation past H is the figure's term, up to the
; recovery input bound.
(assert! (equal (fn-heap-operation-history-octets :reclaim *fn-heap-small-profile* 9000000)
                9000000))
(assert! (< (fn-heap-operation-figure-octets :reclaim *fn-heap-small-profile* *hft-bsd-core*
                                             *hft-nursery* nil)
            (fn-heap-operation-figure-octets :reclaim *fn-heap-small-profile* *hft-bsd-core*
                                             *hft-nursery* 9000000)))
(assert! (equal (fn-heap-operation-history-octets :reclaim *fn-heap-small-profile*
                                                  (expt 10 12))
                (fn-srb-replay-input-bound *fn-heap-small-profile*)))
(assert! (equal (fn-heap-operation-history-octets :run *fn-heap-small-profile* 100)
                8388608))
; Under OpenBSD's default 1,536 MiB data limit the small store's reclaim at H
; is refused by name, where `run' is accepted; observed empty, it is accepted.
(assert! (equal (fn-heap-operation-decide :reclaim *fn-heap-small-profile* *hft-bsd-core*
                                          *hft-nursery* (list *hft-1536*) nil)
                '(:refused :machine-cannot-hold-profile 1843 1536)))
(assert! (equal (car (fn-heap-operation-decide :reclaim *fn-heap-small-profile*
                                               *hft-bsd-core* *hft-nursery*
                                               (list *hft-1536*) 0))
                :heap))
(assert! (equal (car (fn-heap-operation-decide :run *fn-heap-small-profile* *hft-bsd-core*
                                               *hft-nursery* (list *hft-1536*) nil))
                :heap))
; An observation within H only lowers the figure.
(assert! (< (fn-heap-operation-figure-octets :reclaim *fn-heap-small-profile* *hft-bsd-core*
                                             *hft-nursery* 7271160)
            (fn-heap-operation-figure-octets :reclaim *fn-heap-small-profile* *hft-bsd-core*
                                             *hft-nursery* nil)))

; The witnesses: every hypothesis and the conclusion.
(assert! (equal (hft-op-hyps :reclaim *fn-heap-small-profile* *hft-bsd-core* *hft-nursery*
                             (list *hft-2g*) nil 8388608)
                '(t t t t t)))
(assert! (hft-op-conclusion :reclaim *fn-heap-small-profile* *hft-bsd-core* *hft-nursery*
                            (list *hft-2g*) nil 8388608))
(assert! (equal (hft-op-hyps :compact *fn-heap-small-profile* *hft-core* *hft-nursery*
                             (list *hft-4g*) nil 8388608)
                '(t t t t t)))
(assert! (hft-op-conclusion :compact *fn-heap-small-profile* *hft-core* *hft-nursery*
                            (list *hft-4g*) nil 8388608))
(assert! (equal (hft-op-hyps :reclaim *fn-heap-small-profile* *hft-bsd-core* *hft-nursery*
                             (list *hft-2g*) 7271160 7271160)
                '(t t t t t)))
(assert! (hft-op-conclusion :reclaim *fn-heap-small-profile* *hft-bsd-core* *hft-nursery*
                            (list *hft-2g*) 7271160 7271160))

(defmacro hft-op-must-fail (name &rest hyps)
  `(must-fail
    (defthm ,name
      (let ((decision (fn-heap-operation-decide action profile core nursery observations
                                                observed)))
        (implies (and ,@hyps)
                 (<= (+ core nursery
                        (* 2 *fn-heap-octets-per-list-octet*
                           (+ (* (fn-heap-operation-history-copies action) used)
                              (fn-bs-profile-max-record-octets profile)
                              (* *fn-heap-header-copies* (fn-bs-profile-field 17 profile))))
                        (* 2 (fn-ock-capture-budget profile)))
                     (* *fn-heap-mib* (fn-heap-decision-mb decision)))))
      :hints (("Goal" :in-theory (e/d (fn-heap-operation-figure-octets
                                       fn-heap-operation-list-octets fn-heap-buffer-octets
                                       fn-heap-operation-history-octets)
                                      (fn-ock-capture-budget
                                       fn-bs-profile-admittedp
                                       fn-bs-profile-max-history-octets
                                       fn-bs-profile-max-record-octets
                                       fn-bs-profile-field
                                       fn-heap-profile-word))
               :use ((:instance fn-heap-mb-of-covers
                                (octets (fn-heap-operation-figure-octets
                                         action profile core nursery observed)))))))))

; Without the admitted profile: no store, whose figure is the store-less
; one: an image of exactly 1,024 MiB with the nursery fills it, and the
; capture buffers of no profile do not fit beside.
(defconst *hft-full-core* (- (* 1024 *fn-heap-mib*) *hft-nursery*))
(assert! (equal (hft-op-hyps :reclaim nil *hft-full-core* *hft-nursery* (list *hft-4g*) nil 0)
                '(nil t t t t)))
(assert! (not (hft-op-conclusion :reclaim nil *hft-full-core* *hft-nursery*
                                 (list *hft-4g*) nil 0)))
(hft-op-must-fail hft-op-without-admitted
                  (equal (car decision) :heap)
                  (<= used (fn-heap-operation-history-octets action profile observed))
                  (natp core) (natp nursery))

; Without the accepted decision: the reclaim at H under 1,536 MiB.
(assert! (equal (hft-op-hyps :reclaim *fn-heap-small-profile* *hft-bsd-core* *hft-nursery*
                             (list *hft-1536*) nil 8388608)
                '(t nil t t t)))
(assert! (not (hft-op-conclusion :reclaim *fn-heap-small-profile* *hft-bsd-core*
                                 *hft-nursery* (list *hft-1536*) nil 8388608)))
(hft-op-must-fail hft-op-without-heap
                  (fn-bs-profile-admittedp profile)
                  (<= used (fn-heap-operation-history-octets action profile observed))
                  (natp core) (natp nursery))

; Without USED within the history term: a history twice H, unobserved.
(assert! (equal (hft-op-hyps :reclaim *fn-heap-small-profile* *hft-bsd-core* *hft-nursery*
                             (list *hft-2g*) nil (* 2 8388608))
                '(t t nil t t)))
(assert! (not (hft-op-conclusion :reclaim *fn-heap-small-profile* *hft-bsd-core*
                                 *hft-nursery* (list *hft-2g*) nil (* 2 8388608))))
(hft-op-must-fail hft-op-without-used-within-the-term
                  (fn-bs-profile-admittedp profile)
                  (equal (car decision) :heap)
                  (natp core) (natp nursery))

; The history hypothesis with an observation (item 1): the probe observed
; 100,000 octets and the reclaim holds the measured store's 7,271,160.
(assert! (equal (hft-op-hyps :reclaim *fn-heap-small-profile* *hft-bsd-core* *hft-nursery*
                             (list *hft-2g*) 100000 7271160)
                '(t t nil t t)))
(assert! (not (hft-op-conclusion :reclaim *fn-heap-small-profile* *hft-bsd-core*
                                 *hft-nursery* (list *hft-2g*) 100000 7271160)))

; Without a natural core: a fractional core the figure reads as 0.
(assert! (equal (hft-op-hyps :reclaim *fn-heap-small-profile* (+ 2000000000 1/2)
                             *hft-nursery* (list *hft-4g*) nil 0)
                '(t t t nil t)))
(assert! (not (hft-op-conclusion :reclaim *fn-heap-small-profile* (+ 2000000000 1/2)
                                 *hft-nursery* (list *hft-4g*) nil 0)))
(hft-op-must-fail hft-op-without-natp-core
                  (fn-bs-profile-admittedp profile)
                  (equal (car decision) :heap)
                  (<= used (fn-heap-operation-history-octets action profile observed))
                  (natp nursery))

; Without a natural nursery: the same with the nursery.
(assert! (equal (hft-op-hyps :reclaim *fn-heap-small-profile* *hft-bsd-core*
                             (+ 2000000000 1/2) (list *hft-4g*) nil 0)
                '(t t t t nil)))
(assert! (not (hft-op-conclusion :reclaim *fn-heap-small-profile* *hft-bsd-core*
                                 (+ 2000000000 1/2) (list *hft-4g*) nil 0)))
(hft-op-must-fail hft-op-without-natp-nursery
                  (fn-bs-profile-admittedp profile)
                  (equal (car decision) :heap)
                  (<= used (fn-heap-operation-history-octets action profile observed))
                  (natp core))
