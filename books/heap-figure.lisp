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
; ACL2 decides.  The host entries: host/native/heap.lisp `fnn-heap-decision'
; (the installed launcher's probe, `status' and `health').
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
;   L        the list octets: 16 x (2H + R).  Sixteen bytes per octet, one
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
;            books/owner-checkpoint-stream.lisp) and the reader's buffer at
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
; for any core up to 512 MiB (`fn-heap-small-profile-fits-a-small-machine'):
; OpenBSD's default login class allows 1536M of data, and the friend's machine
; has about 2 GB.  `init' with no preset word and no field flag writes it on a
; machine under 4 GiB (`fn-heap-init-request').

(in-package "ACL2")
(include-book "owner-checkpoint-stream")
(include-book "outcome-class")

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

(defun fn-heap-list-octets (profile)
  (declare (xargs :guard t))
  (* *fn-heap-octets-per-list-octet*
     (+ (* 2 (fn-bs-profile-max-history-octets profile))
        (fn-bs-profile-max-record-octets profile))))

(defun fn-heap-buffer-octets (profile)
  (declare (xargs :guard t))
  (* 2 (fn-ock-capture-budget profile)))

(defun fn-heap-figure-octets (profile core nursery)
  (declare (xargs :guard t))
  (+ (nfix core) (nfix nursery)
     (* 2 (fn-heap-list-octets profile))
     (fn-heap-buffer-octets profile)))

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
  '(:development ((2 . 16384) (3 . 8388608) (4 . 196608) (6 . 16) (8 . 128))))

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
; The decision.  PROFILE is the store's saved profile, or NIL when the
; command names no store that exists (help, --version, a fresh
; configuration): then only the image must fit, and the process may use the
; machine.  Answers
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
           (let ((floor-mb (fn-heap-mb-of (+ (nfix core) (nfix nursery)))))
             (if (<= (* *fn-heap-mib* floor-mb) machine)
                 (list :heap machine-mb "none" machine-mb)
               (list :refused :machine-cannot-hold-image floor-mb machine-mb))))
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

; KEYSTONE (PRF-198).  An accepted figure holds every store the profile
; admits: for any history of USED octets within H (the store budget's bound),
; the image, the nursery, the lists at sixteen bytes per octet with the
; collector's copy, and both checkpoint buffers fit in the megabytes the
; launcher passes, and those fit the machine.
(defthm fn-heap-decide-admits-every-store-the-profile-admits
  (let ((decision (fn-heap-decide profile core nursery observations)))
    (implies (and (fn-bs-profile-admittedp profile)
                  (equal (car decision) :heap)
                  (<= used (fn-bs-profile-max-history-octets profile))
                  (natp core) (natp nursery))
             (and (<= (+ core nursery
                         (* 2 *fn-heap-octets-per-list-octet*
                            (+ used used (fn-bs-profile-max-record-octets profile)))
                         (* 2 (fn-ock-capture-budget profile)))
                      (* *fn-heap-mib* (fn-heap-decision-mb decision)))
                  (<= (* *fn-heap-mib* (fn-heap-decision-mb decision))
                      (fn-heap-machine-octets observations)))))
  :hints (("Goal" :in-theory (e/d () (fn-ock-capture-budget
                                      fn-bs-profile-admittedp
                                      fn-bs-profile-max-history-octets
                                      fn-bs-profile-max-record-octets
                                      fn-heap-profile-word))
           :use ((:instance fn-heap-mb-of-covers
                            (octets (fn-heap-figure-octets profile core nursery)))))))

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

; -----------------------------------------------------------------------------
; The small preset and init's default on a small machine.

(defthm fn-heap-small-profile-is-admitted
  (fn-bs-profile-admittedp *fn-heap-small-profile*))

(defthm fn-heap-small-profile-fields
  (and (equal (fn-bs-profile-max-transactions *fn-heap-small-profile*) 16384)
       (equal (fn-bs-profile-max-history-octets *fn-heap-small-profile*) 8388608)
       (equal (fn-bs-profile-max-record-octets *fn-heap-small-profile*) 196608)
       (equal (fn-bs-profile-max-article-octets *fn-heap-small-profile*) 32768)
       (equal (fn-bs-profile-max-groups-per-article *fn-heap-small-profile*) 16)
       (equal (fn-bs-profile-max-open-suffix *fn-heap-small-profile*) 128)))

; With any core up to 512 MiB and the 64 MiB nursery, the small preset is
; accepted on every machine of at least 1,536 MiB.
(defthm fn-heap-small-profile-fits-a-small-machine
  (implies (and (<= core (* 512 *fn-heap-mib*))
                (<= nursery (* 64 *fn-heap-mib*))
                (posp machine) (<= (* 1536 *fn-heap-mib*) machine))
           (equal (car (fn-heap-decide *fn-heap-small-profile* core nursery
                                       (list machine)))
                  :heap))
  :hints (("Goal" :in-theory (enable fn-heap-mb-of))))

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
