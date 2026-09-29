; fn: the process heap a store profile needs, decided before the image starts
; (lane heap-from-profile, 2026-09-26; PKT-016; D27, D35; PRF-198, HST-013).
;
; The saved image's launcher passed SBCL `--dynamic-space-size 32000' whatever
; the store: a constant that bounds the data a node can hold (rep-heap named it
; a D27 defect) and, on a machine smaller than 32 GB with a data-size limit
; (OpenBSD's login classes), a reservation the kernel refuses.  The figure here
; is the profile's: the octets the profile admits at the current
; representation, plus the process's fixed terms, and it is refused by name
; when the machine cannot hold it.  The host observes (the core file's length,
; its collection trigger, the machine's memory in each form the OS gives it);
; ACL2 decides.  The host entries: host/native/heap.lisp `fnn-heap-reservation'
; (the installed launcher's probe, through books/heap-reservation.lisp) and
; `fnn-heap-print-store-line' (`status' and `health': fn-heap-status-decide).
;
; THE FIGURE, in octets (`fn-heap-figure-octets'):
;
;   CORE + NURSERY + 2 x L + B
;
;   CORE     the saved core's length: the image's own dynamic content is at
;            most that (the 69046a76 image: 389,141,032 octets).
;   NURSERY  the host's collection trigger (host/native/io.lisp
;            +fnn-gc-nursery-octets+, 64 MiB): what is consed between two
;            collections, garbage included.
;   L        the list octets: 16 x (2H + R + 3 x HDR), HDR the profile's
;            max-header-octets (field 17; the header in flight, below).  Sixteen bytes per octet, one
;            cons per octet (planning/evidence/rep-wave-d-2026-09-25.md
;            section 1.2, measured to 0.2%): the retained history H once, the
;            open's second copy of it (the checkpoint decode's payload copy,
;            or the recovery's record list beside the replay, the same
;            section), and one record of R octets in flight (the served
;            POST's record list; the owner serves one POST at a time under
;            its service mutex).
;   2 x L    the collector's worst case: SBCL's gencgc copies each live list
;            object once, so it needs free space equal to the live lists.
;   B        the buffer octets: 2 x F, F = `fn-ock-capture-budget' =
;            `fn-sccr-file-read-bound' (3H plus one segment's framing): the
;            publication buffer the automatic capture fills (fn-octets-pub,
;            books/owner-checkpoint-pipeline.lisp) and the reader's buffer at
;            open.  Byte vectors, one byte per octet, large objects the
;            collector does not copy.
;
; H bounds the history a store holds (the store budget refuses the commit past
; it, books/store-budget.lisp `fn-sbud-verdict-at'), so every store the
; profile admits fits the figure: `fn-heap-decide-admits-every-store-the-
; profile-admits'.  The figure in SBCL's megabytes (MiB) is the octets rounded
; up.  The machine is the least of the host's observations (physical memory;
; on Linux the cgroup's memory.max up the hierarchy and RLIMIT_AS; RLIMIT_DATA
; everywhere): a figure above it is refused by name, class :refused (exit 1,
; books/outcome-class.lisp), with both numbers
; (`fn-heap-decide-refuses-exactly-past-the-machine').
;
; The small preset: the development base with T = 16,384, H = 8 MiB,
; R = 196,608 (the least R the Store event kinds admit), G = 16 (so the article
; record for A = 32,768 is 38,027 octets, within R) and K = 128; A = 32,768 is
; the base's.  The development base's own R is 17,138,486 (the article record
; for its G = 65,535), past this H.  Its figure fits a 1,536 MiB machine
; for any core up to 512 MiB (`fn-heap-small-profile-run-fits-a-small-machine':
; OpenBSD's default login class allows 1536M of data; lane heap-bounds held
; it to 192 MiB until lane heap-pool charged the header) and so a 2,048 MiB
; one (`fn-heap-small-profile-run-fits-a-two-gib-machine': the friend's
; machine has about 2 GB).  `init' with no preset word
; and no field flag writes it on a machine under 4 GiB (`fn-heap-init-request').

(in-package "ACL2")
(include-book "owner-checkpoint-pipeline")
(include-book "outcome-class")
(include-book "heap-store-figure")

;; The tau system is off in this book (lane tau-pass, tools/tau_cost.py).
;; Its work is proof time no prover step counts (docs/proof-style.md
;; 9.1); planning/evidence/tau-cost-*.json has this book's figures.
(local (in-theory (disable (tau-system))))

(defconst *fn-heap-mib* 1048576)
(defconst *fn-heap-octets-per-list-octet* 16)

; -----------------------------------------------------------------------------
; The machine: the least positive observation, or 0 when there is none.

(defun fn-heap-machine-octets (observations)
  (declare (xargs :guard t))
  (if (consp observations)
      (let ((rest (fn-heap-machine-octets (cdr observations)))
            (x (car observations)))
        (cond ((not (posp x)) rest)
              ((zp rest) x)
              (t (min x rest))))
    0))

(defthm fn-heap-machine-octets-natp
  (natp (fn-heap-machine-octets observations))
  :rule-classes :type-prescription)

(defthm fn-heap-machine-octets-is-at-most-each-observation
  (implies (and (member-equal x observations) (posp x))
           (<= (fn-heap-machine-octets observations) x))
  :rule-classes nil)

(defthm fn-heap-machine-octets-is-an-observation
  (implies (posp (fn-heap-machine-octets observations))
           (member-equal (fn-heap-machine-octets observations) observations))
  :rule-classes nil)

; The contents of a Linux cgroup's memory.max as an observation: a decimal
; of 1 to 20 digits, with or without its LF, is that many octets; `max' (no
; limit) and anything else is no observation.  The host reads the file
; (host/native/heap.lisp `fnn-heap-cgroup-observations'); this reads it.
(defun fn-heap-decimal-octets-value (octets acc)
  (declare (xargs :guard (natp acc)))
  (if (consp octets)
      (let ((o (car octets)))
        (if (and (natp o) (<= 48 o) (<= o 57))
            (fn-heap-decimal-octets-value (cdr octets) (+ (* 10 acc) (- o 48)))
          nil))
    acc))

(defun fn-heap-limit-of-octets (octets)
  (declare (xargs :guard t))
  (let ((body (if (and (true-listp octets) (consp octets)
                       (equal (car (last octets)) 10))
                  (butlast octets 1)
                octets)))
    (if (and (true-listp body) (consp body) (<= (len body) 20))
        (fn-heap-decimal-octets-value body 0)
      nil)))

; -----------------------------------------------------------------------------
; The figure.

;; The header in flight (PRF-230, lane header-limits-profile): the served
;; POST's parse holds the header view, each field's raw lines and each
;; field's unfolded value, three list copies of at most the profile's
;; max-header-octets (field 17), beside the record R it becomes.
(defconst *fn-heap-header-copies* 3)

(defun fn-heap-list-octets (profile)
  (declare (xargs :guard t))
  (* *fn-heap-octets-per-list-octet*
     (+ (* 2 (fn-bs-profile-max-history-octets profile))
        (fn-bs-profile-max-record-octets profile)
        (* *fn-heap-header-copies* (fn-bs-profile-field *fn-bs-pf-max-header-octets* profile)))))

(defun fn-heap-buffer-octets (profile)
  (declare (xargs :guard t))
  (* 2 (fn-ock-capture-budget profile)))

;; The served figure since the records flip (lane reservation-after-flip):
;; books/heap-store-figure.lisp's, from the arena's state, the open's
;; transient, the request in flight, the buffers, the image's dynamic
;; content and the collector's room at the trigger the host sets.  The list
;; terms above remain the compaction verbs' (the operation figure below).
(defun fn-heap-figure-octets (profile core nursery)
  (declare (xargs :guard t))
  (fn-heap-store-figure-octets profile core nursery nil))

; Octets rounded up to SBCL's megabytes.
(defun fn-heap-mb-of (octets)
  (declare (xargs :guard t))
  (floor (+ (nfix octets) (1- *fn-heap-mib*)) *fn-heap-mib*))

(local (include-book "arithmetic-5/top" :dir :system))

(defthm fn-heap-mb-of-covers
  (<= (nfix octets) (* *fn-heap-mib* (fn-heap-mb-of octets)))
  :rule-classes :linear)

(defthm fn-heap-mb-of-natp
  (natp (fn-heap-mb-of octets))
  :rule-classes :type-prescription)

(in-theory (disable fn-heap-mb-of))

; The profile's name in the report: a preset's word, else `custom'.
(defconst *fn-heap-small-request*
  (list :development
        (list (cons *fn-bs-pf-max-transactions* 16384)
              (cons *fn-bs-pf-max-history-octets* 8388608)
              (cons *fn-bs-pf-max-record-octets* 196608)
              (cons *fn-bs-pf-max-groups-per-article* 16)
              (cons *fn-bs-pf-max-open-suffix* 128))))

(defconst *fn-heap-small-profile*
  (fn-bs-profile-resolve *fn-heap-small-request* nil))

(defun fn-heap-profile-word (profile)
  (declare (xargs :guard t))
  (let ((p (fn-bs-profile-of profile)))
    (cond ((equal p *fn-heap-small-profile*) "small")
          ((equal p *fn-bs-profile-development*) "development")
          ((equal p *fn-bs-profile-scale*) "scale")
          ((equal p *fn-bs-profile-defaults*) "default")
          (t "custom"))))

; -----------------------------------------------------------------------------
; A command naming no store (help, --version, a fresh configuration, every
; verb that opens none) holds no history, so its heap is a small fixed
; figure, not the machine: *fn-heap-storeless-mb*, lowered to what the
; machine holds beside the core and one thread (SBCL's default 2 MiB control
; stack and the 4 MiB runtime books/heap-reservation.lisp counts per
; thread).  Before (PKT-686's record, section 1), the whole machine was the
; heap: under OpenBSD's 4 GiB datasize `fn --version' died with `mmap:
; Cannot allocate memory', since the heap alone was the datasize and the
; core and the thread counted against it too.  Refused by name only when
; the machine cannot hold the image (core and nursery) in that room.
; Whole megabytes within X octets (rounded down; X's MB below it).
(defun fn-heap-mb-below (x)
  (declare (xargs :guard t))
  (floor (nfix x) *fn-heap-mib*))

(defthm fn-heap-mb-below-natp
  (natp (fn-heap-mb-below x))
  :rule-classes :type-prescription)

(defthm fn-heap-mb-below-is-below
  (implies (natp x)
           (<= (* *fn-heap-mib* (fn-heap-mb-below x)) x))
  :rule-classes :linear)

(in-theory (disable fn-heap-mb-below))

(defconst *fn-heap-storeless-mb* 1024)
(defconst *fn-heap-storeless-thread-octets* (* 6 *fn-heap-mib*))

(defun fn-heap-storeless-decide (core nursery machine)
  (declare (xargs :guard t))
  (let* ((machine-mb (floor (nfix machine) *fn-heap-mib*))
         (room (- (nfix machine) (+ (fn-heap-core-file core) *fn-heap-storeless-thread-octets*)))
         (mb (min *fn-heap-storeless-mb* (fn-heap-mb-below room)))
         (floor-mb (fn-heap-mb-of (+ (fn-heap-core-file core) (nfix nursery)))))
    (if (and (natp room) (<= floor-mb mb))
        (list :heap mb "none" machine-mb)
      (list :refused :machine-cannot-hold-image floor-mb machine-mb))))

; -----------------------------------------------------------------------------
; The decision.  PROFILE is the store's saved profile, or NIL when the
; command names no store that exists: then the store-less figure above.
; Answers
;   (:heap MB WORD MACHINE-MB)
;   (:refused REASON MB MACHINE-MB)   REASON :machine-cannot-hold-profile,
;                                     :machine-cannot-hold-image or
;                                     :machine-memory-unobserved.
(defun fn-heap-decide (profile core nursery observations)
  (declare (xargs :guard t))
  (let* ((machine (fn-heap-machine-octets observations))
         (machine-mb (floor machine *fn-heap-mib*)))
    (cond ((zp machine)
           (list :refused :machine-memory-unobserved 0 0))
          ((not (fn-bs-profile-admittedp profile))
           (fn-heap-storeless-decide core nursery machine))
          (t
           (let ((mb (fn-heap-mb-of (fn-heap-figure-octets profile core nursery))))
             (if (<= (* *fn-heap-mib* mb) machine)
                 (list :heap mb (fn-heap-profile-word profile) machine-mb)
               (list :refused :machine-cannot-hold-profile mb machine-mb)))))))

(defun fn-heap-decision-mb (decision)
  (declare (xargs :guard t))
  (if (and (consp decision) (equal (car decision) :heap)
           (consp (cdr decision)))
      (nfix (cadr decision))
    0))

; KEYSTONE (store-less, PKT-686 item 3).  An accepted store-less figure is at
; most *fn-heap-storeless-mb*, whatever the machine; it holds the core and
; the nursery; and with the core and one thread beside it fits the machine.
; (A hypothesis (natp machine) was removed after proving the weakened
; theorem: acceptance itself requires the room beside the core to be a
; natural.)
(defthm fn-heap-storeless-decide-is-small-and-fits
  (let ((d (fn-heap-storeless-decide core nursery machine)))
    (implies (equal (car d) :heap)
             (and (<= (fn-heap-decision-mb d) *fn-heap-storeless-mb*)
                  (<= (+ (fn-heap-core-file core) (nfix nursery))
                      (* *fn-heap-mib* (fn-heap-decision-mb d)))
                  (<= (+ (* *fn-heap-mib* (fn-heap-decision-mb d)) (fn-heap-core-file core)
                         *fn-heap-storeless-thread-octets*)
                      machine))))
  :hints (("Goal" :use ((:instance fn-heap-mb-of-covers
                                   (octets (+ (fn-heap-core-file core) (nfix nursery)))))
           :in-theory (disable fn-heap-mb-of-covers))))

; The store-less figure grows with the machine: accepted on a machine, it is
; accepted on every larger one.
(defthm fn-heap-mb-below-monotone
  (implies (and (integerp x) (integerp y) (<= x y))
           (<= (fn-heap-mb-below x) (fn-heap-mb-below y)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-heap-mb-below))))

(defthm fn-heap-storeless-decide-accepts-on-a-larger-machine
  (implies (and (equal (car (fn-heap-storeless-decide core nursery m1)) :heap)
                (<= m1 m2) (natp m1) (natp m2))
           (equal (car (fn-heap-storeless-decide core nursery m2)) :heap))
  :hints (("Goal" :use ((:instance fn-heap-mb-below-monotone
                                   (x (- m1 (+ (fn-heap-core-file core) *fn-heap-storeless-thread-octets*)))
                                   (y (- m2 (+ (fn-heap-core-file core) *fn-heap-storeless-thread-octets*)))))
           :in-theory (disable fn-heap-mb-below-monotone))))

(defthm fn-heap-decide-of-no-store-by-definition
  (implies (and (not (fn-bs-profile-admittedp profile))
                (posp (fn-heap-machine-octets observations)))
           (equal (fn-heap-decide profile core nursery observations)
                  (fn-heap-storeless-decide core nursery
                                            (fn-heap-machine-octets observations))))
  :hints (("Goal" :in-theory (disable fn-heap-storeless-decide fn-bs-profile-admittedp))))

; An accepted decision's megabytes are the figure's, within the machine.
(local
 (defthm fn-heap-decide-heap-is-the-figure-within-the-machine
   (implies (and (fn-bs-profile-admittedp profile)
                 (equal (car (fn-heap-decide profile core nursery observations)) :heap))
            (and (equal (fn-heap-decision-mb (fn-heap-decide profile core nursery observations))
                        (fn-heap-mb-of (fn-heap-figure-octets profile core nursery)))
                 (<= (* *fn-heap-mib* (fn-heap-decision-mb (fn-heap-decide profile core nursery
                                                                           observations)))
                     (fn-heap-machine-octets observations))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-heap-decide)
                                   (fn-heap-figure-octets fn-heap-mb-of fn-heap-machine-octets
                                    fn-bs-profile-admittedp fn-heap-profile-word
                                    fn-heap-storeless-decide))))))

; KEYSTONE (PRF-198, re-derived by reservation-after-flip).  An accepted
; figure holds every store the profile admits: in the dynamic space the
; launcher passes (the decision's megabytes), any store of USED payload
; octets within H and N records within T fits with its open's transient, the
; request in flight, both buffers, the image's dynamic content and the
; collector's room at the trigger the host sets in that space
; (books/heap-store-figure.lisp `fn-heap-store-need'); and that space fits
; the machine.
(defthm fn-heap-decide-admits-every-store-the-profile-admits
  (let* ((decision (fn-heap-decide profile core nursery observations))
         (d (* *fn-heap-mib* (fn-heap-decision-mb decision))))
    (implies (and (fn-bs-profile-admittedp profile)
                  (equal (car decision) :heap)
                  (<= (+ (nfix used) (* *fn-sbud-membership-octets* (nfix m)))
                      (nfix (fn-bs-profile-max-history-octets profile)))
                  (<= (nfix n) (nfix (fn-bs-profile-max-transactions profile)))
                  (<= (nfix ou) (nfix (fn-bs-profile-max-history-octets profile)))
                  (<= (nfix on) (nfix (fn-bs-profile-max-transactions profile))))
             (and (<= (fn-heap-store-need profile core used n m ou on
                                          (fn-heap-nursery-trigger d nursery))
                      d)
                  (<= d (fn-heap-machine-octets observations)))))
  :hints (("Goal" :in-theory (e/d (fn-heap-figure-octets)
                                  (fn-heap-decide fn-heap-store-need fn-heap-nursery-trigger
                                   fn-heap-mb-of fn-heap-store-figure-octets fn-heap-machine-octets
                                   fn-heap-decision-mb fn-bs-profile-admittedp
                                   fn-bs-profile-max-history-octets fn-bs-profile-max-transactions))
           :use (fn-heap-decide-heap-is-the-figure-within-the-machine
                 (:instance fn-heap-mb-of-covers
                            (octets (fn-heap-figure-octets profile core nursery)))
                 (:instance fn-heap-store-figure-holds-every-store
                            (observed nil)
                            (d (* *fn-heap-mib*
                                  (fn-heap-decision-mb
                                   (fn-heap-decide profile core nursery observations)))))))))

; The refusal is exact and names both numbers: an admitted profile is refused
; exactly when its figure exceeds the observed machine.
(defthm fn-heap-decide-refuses-exactly-past-the-machine
  (implies (and (fn-bs-profile-admittedp profile)
                (posp (fn-heap-machine-octets observations)))
           (equal (fn-heap-decide profile core nursery observations)
                  (let ((mb (fn-heap-mb-of (fn-heap-figure-octets profile core nursery)))
                        (machine-mb (floor (fn-heap-machine-octets observations)
                                           *fn-heap-mib*)))
                    (if (<= (* *fn-heap-mib* mb) (fn-heap-machine-octets observations))
                        (list :heap mb (fn-heap-profile-word profile) machine-mb)
                      (list :refused :machine-cannot-hold-profile mb machine-mb)))))
  :hints (("Goal" :in-theory (disable fn-heap-figure-octets fn-heap-profile-word
                                      fn-bs-profile-admittedp))))

;; -----------------------------------------------------------------------------
;; The operation's figure (lane openbsd-release-fixes, PKT-686).
;;
;; The figure above models the open and the served path: two list copies of
;; the history.  The offline compaction verbs hold more.  Measured on the
;; production image (planning/evidence/openbsd-release-fixes-2026-09-27.md
;; section 3: the least `--dynamic-space-size' at which each verb exits 0, by
;; bisection, on a store of 3,000 articles holding 7,271,160 history octets
;; under the small preset's fields with a 16-record open suffix, whose figure
;; is 821 MB): `store compact' 1,280 to 1,381 MB and `store reclaim' (which
;; compacts first) 1,179 to 1,447 MB on Linux, compact 1,256 MB on OpenBSD
;; 7.9; `recover' (a full replay) and the owner's open 666 to 716 MB.  Less
;; the core, the nursery, both checkpoint buffers and the record in flight,
;; that is at most 5.13 list copies of the history for the compaction verbs
;; (sixteen octets per octet, twice for the collector's copy) and at most
;; 1.61 for the open.  The compaction verbs' figure counts
;; *fn-heap-compaction-history-copies* = 6 copies; every other command keeps
;; the two copies of the figure above (`fn-heap-operation-decide-of-a-serve-
;; action-is-heap-decide').  The native action is ACL2's
;; (books/native-operator.lisp fn-native-operator-result-native-action).

(defconst *fn-heap-serve-history-copies* 2)
(defconst *fn-heap-compaction-history-copies* 6)

(defun fn-heap-operation-history-copies (action)
  (declare (xargs :guard t))
  (if (member-equal action '(:compact :reclaim))
      *fn-heap-compaction-history-copies*
    *fn-heap-serve-history-copies*))

; THE OBSERVED HISTORY (PKT-686 item 1, the coordinator's decision): an
; offline verb that never grows the store -- `recover', `store compact',
; `store reclaim' -- holds copies of the history the store HAS, not of the
; profile's bound H.  OBSERVED is the octets of the store's history files on
; disk the probe summed before the image started (host/native/heap.lisp
; fnn-heap-history-observation: the regular files under transactions/,
; packs/ and checkpoints/ and the state checkpoint; NIL when unobserved): an
; upper bound of the stored octets `fn-sbud-bytes-used' counts, since every
; retained record's encoding is in one of those files.  For those actions
; the history term is the least of OBSERVED and H; for every other action
; (`run' grows the store) it stays H.
;
; And (lane reservation-after-flip) every command: the open it starts with
; replays at most what is on disk, so its figure's OPEN term is the
; observed store's (books/heap-store-figure.lisp fn-heap-open-octets-bound,
; -records-bound), while its STATE term stays at the profile's bounds since
; a run grows the store (fn-heap-operation-figure-octets).  OBSERVED may also be (OCTETS . RECORDS), RECORDS
; the transaction files' count, which bounds the open's per-record term.
(defconst *fn-heap-list-actions* '(:recover :compact :reclaim))

; Whether the probe observes the history for ACTION (host/native/heap.lisp
; fnn-heap-operator-profile asks).
; Every command that names a store opens it, so the probe observes the store
; whatever the command (lane reservation-after-flip; before, only the offline
; verbs were observed).
(defun fn-heap-operation-observes-p (action)
  (declare (xargs :guard t) (ignore action))
  t)

; The probe lists each history directory to at most this many entries (the
; profile's transaction slots and 1,024 more for packs, checkpoint
; generations and markers); a larger directory is not observed (NIL: H).
(defun fn-heap-history-listing-bound (profile)
  (declare (xargs :guard t))
  (+ (nfix (fn-bs-profile-max-transactions profile)) 1024))

(defun fn-heap-operation-history-octets (action profile observed)
  (declare (xargs :guard t))
  (let ((h (fn-bs-profile-max-history-octets profile))
        (o (fn-heap-observed-octets observed)))
    (if (and (member-equal action *fn-heap-list-actions*)
             (natp o) (< o (nfix h)))
        o
      h)))

(defun fn-heap-operation-list-octets (action profile observed)
  (declare (xargs :guard t))
  (* *fn-heap-octets-per-list-octet*
     (+ (* (fn-heap-operation-history-copies action)
           (fn-heap-operation-history-octets action profile observed))
        (fn-bs-profile-max-record-octets profile)
        (* *fn-heap-header-copies* (fn-bs-profile-field *fn-bs-pf-max-header-octets* profile)))))

;; The offline verbs' measured list copies over the image's dynamic content,
;; and never less than the store figure over the same observation (the verbs
;; open the store first: its open transient and state hold for them too).
(defun fn-heap-operation-list-figure-octets (action profile core nursery observed)
  (declare (xargs :guard t))
  (+ (fn-heap-core-dynamic core) (nfix nursery)
     (* 2 (fn-heap-operation-list-octets action profile observed))
     (fn-heap-buffer-octets profile)))

;; `init' makes the store: its first run opens nothing on disk (ACL2 says
;; so, whatever the probe was handed).
(defconst *fn-heap-empty-store-observation* '(0 . 0))

(defun fn-heap-operation-observation (action observed)
  (declare (xargs :guard t))
  (if (equal action :init) *fn-heap-empty-store-observation* observed))

(defun fn-heap-operation-figure-octets (action profile core nursery observed)
  (declare (xargs :guard t))
  (if (member-equal action *fn-heap-list-actions*)
      (max (fn-heap-operation-list-figure-octets action profile core nursery observed)
           (fn-heap-store-figure-octets profile core nursery observed))
    (fn-heap-store-figure-octets profile core nursery
                                 (fn-heap-operation-observation action observed))))

(defthm fn-heap-operation-figure-octets-natp
  (natp (fn-heap-operation-figure-octets action profile core nursery observed))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (disable fn-heap-store-figure-octets fn-heap-figure-octets))))

(defthm fn-heap-nfix-of-operation-figure-octets
  (equal (nfix (fn-heap-operation-figure-octets action profile core nursery observed))
         (fn-heap-operation-figure-octets action profile core nursery observed))
  :hints (("Goal" :in-theory (union-theories '(nfix fn-heap-operation-figure-octets-natp)
                                             (theory 'minimal-theory)))))

(defun fn-heap-operation-decide (action profile core nursery observations observed)
  (declare (xargs :guard t))
  (let* ((machine (fn-heap-machine-octets observations))
         (machine-mb (floor machine *fn-heap-mib*)))
    (cond ((zp machine)
           (list :refused :machine-memory-unobserved 0 0))
          ((not (fn-bs-profile-admittedp profile))
           (fn-heap-storeless-decide core nursery machine))
          (t
           (let ((mb (fn-heap-mb-of
                      (fn-heap-operation-figure-octets action profile core nursery
                                                       observed))))
             (if (<= (* *fn-heap-mib* mb) machine)
                 (list :heap mb (fn-heap-profile-word profile) machine-mb)
               (list :refused :machine-cannot-hold-profile mb machine-mb)))))))

; Unobserved, every action but the offline verbs decides exactly as
; fn-heap-decide.
(defthm fn-heap-operation-decide-of-a-serve-action-is-heap-decide
  (implies (and (not (member-equal action *fn-heap-list-actions*))
                (not (equal action :init)))
           (equal (fn-heap-operation-decide action profile core nursery observations
                                            nil)
                  (fn-heap-decide profile core nursery observations)))
  :hints (("Goal" :in-theory (e/d (fn-heap-operation-figure-octets fn-heap-figure-octets
                                   fn-heap-operation-observation)
                                  (fn-heap-profile-word fn-bs-profile-admittedp
                                   fn-heap-store-figure-octets
                                   fn-heap-buffer-octets fn-heap-storeless-decide)))))

; An accepted operation decision for an admitted profile is its figure's
; megabytes, within the machine.
(defthm fn-heap-operation-decide-accepted
  (let ((decision (fn-heap-operation-decide action profile core nursery observations
                                            observed)))
    (implies (and (fn-bs-profile-admittedp profile)
                  (equal (car decision) :heap))
             (and (equal (fn-heap-decision-mb decision)
                         (fn-heap-mb-of (fn-heap-operation-figure-octets
                                         action profile core nursery observed)))
                  (<= (* *fn-heap-mib* (fn-heap-decision-mb decision))
                      (fn-heap-machine-octets observations)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-heap-operation-decide)
                                  (fn-heap-operation-figure-octets fn-heap-profile-word
                                   fn-bs-profile-admittedp fn-heap-storeless-decide
                                   fn-heap-machine-octets)))))

(defthm fn-heap-operation-figure-holds-the-parts
  (and (<= (fn-heap-store-figure-octets profile core nursery
                                        (fn-heap-operation-observation action observed))
           (fn-heap-operation-figure-octets action profile core nursery observed))
       (implies (member-equal action *fn-heap-list-actions*)
                (<= (fn-heap-operation-list-figure-octets action profile core nursery observed)
                    (fn-heap-operation-figure-octets action profile core nursery observed))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-heap-operation-figure-octets
                                   fn-heap-operation-observation)
                                  (fn-heap-store-figure-octets
                                   fn-heap-operation-list-figure-octets)))))

(defthm fn-heap-operation-used-within-the-history-octets
  (implies (and (<= used (fn-bs-profile-max-history-octets profile))
                (implies (natp (fn-heap-observed-octets observed))
                         (<= used (fn-heap-observed-octets observed))))
           (<= (* (fn-heap-operation-history-copies action) used)
               (* (fn-heap-operation-history-copies action)
                  (fn-heap-operation-history-octets action profile observed))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-heap-operation-history-octets)
                                  (fn-bs-profile-max-history-octets
                                   fn-heap-observed-octets)))))

; KEYSTONE (PKT-686).  An accepted operation figure of an offline verb holds
; the image's dynamic content, the nursery, the operation's measured list
; copies of every history USED within H -- and, with an observation, within
; the observed octets -- the record and headers in flight, and both
; checkpoint buffers; and it fits the machine.
(defthm fn-heap-operation-decide-holds-the-operation
  (let ((decision (fn-heap-operation-decide action profile core nursery observations
                                            observed)))
    (implies (and (member-equal action *fn-heap-list-actions*)
                  (fn-bs-profile-admittedp profile)
                  (equal (car decision) :heap)
                  (<= used (fn-bs-profile-max-history-octets profile))
                  (implies (natp (fn-heap-observed-octets observed))
                           (<= used (fn-heap-observed-octets observed)))
                  (natp nursery))
             (and (<= (+ (fn-heap-core-dynamic core) nursery
                         (* 2 *fn-heap-octets-per-list-octet*
                            (+ (* (fn-heap-operation-history-copies action) used)
                               (fn-bs-profile-max-record-octets profile)
                               (* *fn-heap-header-copies* (fn-bs-profile-field *fn-bs-pf-max-header-octets* profile))))
                         (* 2 (fn-ock-capture-budget profile)))
                      (* *fn-heap-mib* (fn-heap-decision-mb decision)))
                  (<= (* *fn-heap-mib* (fn-heap-decision-mb decision))
                      (fn-heap-machine-octets observations)))))
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
                                     action profile core nursery observed)))))))

; KEYSTONE (reservation-after-flip).  An accepted operation figure holds
; every store the profile admits -- USED within H, N within T, the collector's room at the trigger
; the host sets in the launcher's space -- with the open's transient over any
; input within the observation (OU octets, ON records: what is on disk when
; the probe ran; for a command that observes nothing its figure is the
; unobserved one, which holds every observation's); and it fits the machine.
; (A hypothesis (member action '(:recover :compact :reclaim :run)) was removed after
; proving the weakened theorem.)
(defthm fn-heap-operation-decide-holds-the-store
  (let* ((decision (fn-heap-operation-decide action profile core nursery observations
                                             observed))
         (d (* *fn-heap-mib* (fn-heap-decision-mb decision))))
    (implies (and (fn-bs-profile-admittedp profile)
                  (equal (car decision) :heap)
                  (<= (+ (nfix used) (* *fn-sbud-membership-octets* (nfix m)))
                      (nfix (fn-bs-profile-max-history-octets profile)))
                  (<= (nfix n) (nfix (fn-bs-profile-max-transactions profile)))
                  (<= (nfix ou) (fn-heap-open-octets-bound
                                 profile (fn-heap-operation-observation action observed)))
                  (<= (nfix on) (fn-heap-open-records-bound
                                 profile (fn-heap-operation-observation action observed))))
             (and (<= (fn-heap-store-need profile core used n m ou on
                                          (fn-heap-nursery-trigger d nursery))
                      d)
                  (<= d (fn-heap-machine-octets observations)))))
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
                            (observed (fn-heap-operation-observation action observed))
                            (d (* *fn-heap-mib*
                                  (fn-heap-mb-of (fn-heap-operation-figure-octets
                                                  action profile core nursery
                                                  observed)))))))))

; The observation only ever lowers the figure: the observed figure is at most
; the unobserved one (the H figure the verb had before), so no accepted
; command is refused because the probe observed its store.
(defthm fn-heap-operation-list-figure-observed-is-at-most-unobserved
  (<= (fn-heap-operation-list-figure-octets action profile core nursery observed)
      (fn-heap-operation-list-figure-octets action profile core nursery nil))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (fn-heap-operation-list-figure-octets
                                   fn-heap-operation-list-octets
                                   fn-heap-operation-history-octets)
                                  (fn-bs-profile-max-history-octets
                                   fn-bs-profile-max-record-octets
                                   fn-heap-core-dynamic fn-heap-observed-octets
                                   fn-bs-profile-field fn-heap-buffer-octets)))))

(defthm fn-heap-operation-figure-octets-observed-is-at-most-unobserved
  (<= (fn-heap-operation-figure-octets action profile core nursery observed)
      (fn-heap-operation-figure-octets action profile core nursery nil))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (fn-heap-operation-figure-octets fn-heap-figure-octets
                                   fn-heap-operation-observation)
                                  (fn-heap-store-figure-octets
                                   fn-heap-operation-list-figure-octets)))))

(defthm fn-heap-small-profile-is-admitted
  (fn-bs-profile-admittedp *fn-heap-small-profile*))

(defthm fn-heap-small-profile-fields
  (and (equal (fn-bs-profile-max-transactions *fn-heap-small-profile*) 16384)
       (equal (fn-bs-profile-max-history-octets *fn-heap-small-profile*) 8388608)
       (equal (fn-bs-profile-max-record-octets *fn-heap-small-profile*) 196608)
       (equal (fn-bs-profile-max-article-octets *fn-heap-small-profile*) 32768)
       (equal (fn-bs-profile-max-groups-per-article *fn-heap-small-profile*) 16)
       (equal (fn-bs-profile-max-open-suffix *fn-heap-small-profile*) 128)))

;; The small preset's figures since the records flip, with the streamed open
;; (lane reservation-figure), and the memberships charged to the history
;; budget (lane membership-budget: at most H / 320 = 26,214 of them, 16 MiB,
;; where 16 groups a record counted 160 MiB), and since lane f8-reservation
;; the payload and the memberships charged against the one H together (at
;; most 2 H, not 3 H).  Since lane heap-bounds (row B2) the records' term is
;; derived from the profile's limits (books/heap-store-figure.lisp,
;; KEYSTONE fn-heap-records-retained-within-the-terms) rather than a measured
;; 12 KiB a record, which records with long headers exceeded; and since lane
;; heap-pool (B9) the header state is CHARGED to the history budget (8 history
;; octets a header octet, 12 more a Message-ID octet: books/store-budget.lisp
;; fn-sbud-held-heap-charge), so at its bounds (T = 16,384 records, H = 8 MiB)
;; the retained state is 209 MiB -- 2 x 16,384 x 4,096 (the fixed part a
;; record), 8 x 8 MiB (the header charge's heap), 2 H, the empty arena's page,
;; the handles -- where lane heap-bounds' uncharged term made it 1,032 MiB; a
;; full replay of such a store adds at most 108 MiB (one chunk and one record
;; as lists, the input's vectors, 1 KiB a record); a `run' sizes the open by
;; the store on disk (`fn-heap-operation-decide', :run), so the empty store's
;; chunk term is 0 (lane heap-bounds, B4).  The articles in flight are
;; charged as packed submissions since lane chunked-body-2
;; (books/heap-store-figure.lisp fn-heap-article-reserve-octets), not as
;; lists; with heap-pool's header charge the base is 282,764,298 octets
;; (269.7 MiB), the value ACL2 evaluates.  The run of an empty small store
;; is accepted on every machine
;; of at least 1,536 MiB (OpenBSD's default login class) for any image up to
;; 512 MiB of dynamic content, and on 2,048 MiB too (the friend's machine
;; has about 2 GB).
(defthm fn-heap-small-run-base-of-an-empty-store
  (equal (fn-heap-store-base-octets *fn-heap-small-profile* core '(0 . 0))
         (+ (fn-heap-core-dynamic core) 282764298))
  :hints (("Goal" :in-theory (enable fn-heap-store-base-octets fn-heap-open-octets-bound
                                     fn-heap-open-records-bound))))

; (A hypothesis bounding the nursery cap was removed after proving the
; weakened theorem: the trigger is at most a sixteenth of the space.)
(local
 (defthm fn-heap-ceiling-8-7-below
   (implies (natp x) (< (ceiling (* 8 x) 7) (+ 1 (* 8/7 x))))
   :rule-classes :linear))

; The nursery's figure over BASE, without a ceiling (whose arithmetic
; depends on the base's residue mod 7).
(local
 (defthm fn-heap-with-nursery-below-eight-sevenths
   (implies (natp base)
            (< (fn-heap-with-nursery base nursery)
               (+ 1 (max (+ base (* 2 *fn-heap-nursery-least-octets*))
                         (* 8/7 base)))))
   :rule-classes :linear
   :hints (("Goal" :use (fn-heap-with-nursery-is-at-most-an-eighth-more
                         (:instance fn-heap-ceiling-8-7-below (x base)))
                   :in-theory (disable fn-heap-with-nursery-is-at-most-an-eighth-more
                                       fn-heap-ceiling-8-7-below)))))

(defthm fn-heap-small-profile-run-fits-a-small-machine
  (implies (and (<= (fn-heap-core-dynamic core) (* 512 *fn-heap-mib*))
                (posp machine) (<= (* 1536 *fn-heap-mib*) machine))
           (equal (car (fn-heap-operation-decide :run *fn-heap-small-profile* core nursery
                                                 (list machine) '(0 . 0)))
                  :heap))
  :hints (("Goal" :in-theory (e/d (fn-heap-mb-of fn-heap-store-figure-octets)
                                  (fn-heap-profile-word))
           :use ((:instance fn-heap-with-nursery-below-eight-sevenths
                            (base (fn-heap-store-base-octets *fn-heap-small-profile* core
                                                             '(0 . 0))))))))

(defthm fn-heap-small-profile-run-fits-a-two-gib-machine
  (implies (and (<= (fn-heap-core-dynamic core) (* 512 *fn-heap-mib*))
                (posp machine) (<= (* 2048 *fn-heap-mib*) machine))
           (equal (car (fn-heap-operation-decide :run *fn-heap-small-profile* core nursery
                                                 (list machine) '(0 . 0)))
                  :heap))
  :hints (("Goal" :in-theory (e/d (fn-heap-mb-of fn-heap-store-figure-octets)
                                  (fn-heap-profile-word))
           :use ((:instance fn-heap-with-nursery-below-eight-sevenths
                            (base (fn-heap-store-base-octets *fn-heap-small-profile* core
                                                             '(0 . 0))))))))

(defconst *fn-heap-small-machine-octets* (* 4 1024 *fn-heap-mib*))

; The request `init' resolves: a bare request (no preset word, no field flag;
; `--profile default' alone is the same request) on a machine under 4 GiB is
; the small preset; every other request is the operator's, unchanged.
(defun fn-heap-init-request (request machine)
  (declare (xargs :guard t))
  (if (and (equal request '(:default nil))
           (posp machine)
           (< machine *fn-heap-small-machine-octets*))
      *fn-heap-small-request*
    request))

(defthm fn-heap-init-request-on-a-small-machine-is-small
  (implies (and (posp machine) (< machine *fn-heap-small-machine-octets*))
           (equal (fn-bs-profile-resolve (fn-heap-init-request '(:default nil) machine)
                                         nil)
                  *fn-heap-small-profile*)))

(defthm fn-heap-init-request-keeps-the-operators-request
  (implies (or (not (equal request '(:default nil)))
               (not (posp machine))
               (<= *fn-heap-small-machine-octets* machine))
           (equal (fn-heap-init-request request machine) request)))

; -----------------------------------------------------------------------------
; The report line `status' and `health' print, and the launcher reads:
;   heap=MB MB profile=WORD machine=MACHINE-MB MB
;   refused REASON heap=MB MB machine=MACHINE-MB MB

(defun fn-heap-decimal (n)
  (declare (xargs :guard t))
  (coerce (explode-nonnegative-integer (nfix n) 10 nil) 'string))

(defun fn-heap-reason-word (reason)
  (declare (xargs :guard t))
  (case reason
    (:machine-cannot-hold-profile "machine-cannot-hold-profile")
    (:machine-cannot-hold-image "machine-cannot-hold-image")
    (:machine-memory-unobserved "machine-memory-unobserved")
    (otherwise "malformed")))

(defun fn-heap-report-line (decision)
  (declare (xargs :guard t))
  (let ((a (nth 1 (true-list-fix decision)))
        (b (nth 2 (true-list-fix decision)))
        (c (fn-heap-decimal (nth 3 (true-list-fix decision)))))
    (if (and (consp decision) (equal (car decision) :heap) (stringp b))
        (concatenate 'string "heap=" (fn-heap-decimal a) " MB profile=" b
                     " machine=" c " MB")
      (concatenate 'string "refused " (fn-heap-reason-word a)
                   " heap=" (fn-heap-decimal b) " MB machine=" c " MB"))))

; The exit code of a decision: the outcome algebra's one table.
(defun fn-heap-decision-exit-code (decision)
  (declare (xargs :guard t))
  (fn-outcome-code (if (and (consp decision) (equal (car decision) :heap))
                       :accepted
                     :refused)))

(defthm fn-heap-decision-exit-code-of-a-refusal
  (implies (not (equal (car decision) :heap))
           (equal (fn-heap-decision-exit-code decision) 1)))
