; When the owner collects while it is idle (MEM-003, lane mem3-idle).
;
; After a burst of POSTs the owner keeps freed pages resident: SBCL's
; collector frees a dead page inside the heap at every collection, but hands
; it back to the OS (madvise MADV_DONTNEED, gc-common.c zero_range_with_mmap)
; only after a collection of a generation above 1 (gencgc.c
; small_generation_limit, read in the sbcl-2.6.8 sources), and the automatic
; collections the nursery trigger makes are generation 0 and 1.  Measured on
; the gate-4 developer image and on fn-core (one run each, a filled small
; store, idle after 32 connections closed): a generation-1 collection leaves
; RssAnon where it was; a full one takes it from 56.7 to 19.8 MB (image) and
; from 45.1 to 17.7 MB (fn-core) in 10.3 and 9.1 ms, and leaves RssFile
; unchanged.
;
; ACL2 decides when; the host only observes and calls.  Each maintenance tick
; (host/native/owner.lisp fnn-owner-maintenance-tick, once a second) the host
; hands two facts, how many bytes the owner allocated since the previous
; tick and whether a publication or export job is in flight, to
; `fn-idle-gc-quiet', which counts consecutive quiet ticks; and then that
; count, the publication flag and the bytes allocated since the last idle
; collection to `fn-idle-gc-decide', which answers :wait or (:collect G).
; The host calls (sb-ext:gc :gen G) for the G the verdict names, and records
; the allocation counter as the new "since the last collection".
;
; KEYSTONE `fn-idle-gc-verdict-collects-only-when-owed': a :collect verdict
; implies the quiet count reached its limit, no publication is in flight, and
; at least the floor was allocated since the last collection; it names the
; configured generation.  `fn-idle-gc-verdict-collects-when-owed' is the
; converse (the premise is inhabited and the verdict is not vacuously :wait),
; and `fn-idle-gc-quiet-counts-only-quiet-ticks' says the count restarts at
; zero on a publication or an active tick, so a publication also ends the
; idle period the count measures.

(in-package "ACL2")
(include-book "profile-limits")

(defconst *fn-idle-gc-generation* (fn-profile-limit :idle-gc-generation))
(defconst *fn-idle-gc-quiet-ticks* (fn-profile-limit :idle-gc-quiet-ticks))
(defconst *fn-idle-gc-activity-octets* (* 1024 (fn-profile-limit :idle-gc-activity-kib)))
(defconst *fn-idle-gc-floor-octets* (* 1024 (fn-profile-limit :idle-gc-floor-kib)))

; SBCL's pseudo-static generation: a collection through it is a full one.
(defconst *fn-idle-gc-pseudo-static* 6)

; The quiet count after one tick: it restarts at zero when a publication is in
; flight or the tick allocated the activity limit or more, else it grows.
(defun fn-idle-gc-quiet-next (quiet publishingp tick-octets activity-octets)
  (declare (xargs :guard t))
  (if (or publishingp
          (not (natp tick-octets))
          (not (natp activity-octets))
          (<= activity-octets tick-octets))
      0
    (1+ (nfix quiet))))

(defun fn-idle-gc-quiet (quiet publishingp tick-octets)
  (declare (xargs :guard t))
  (fn-idle-gc-quiet-next quiet publishingp tick-octets *fn-idle-gc-activity-octets*))

; The verdict, over its limits: :wait, or (:collect GENERATION).
(defun fn-idle-gc-verdict (quiet-limit floor-octets generation
                                       quiet publishingp consed-octets)
  (declare (xargs :guard t))
  (if (and (not publishingp)
           (natp quiet) (natp quiet-limit) (<= quiet-limit quiet)
           (natp consed-octets) (natp floor-octets) (<= floor-octets consed-octets))
      (list :collect generation)
    :wait))

; The verdict at the profile's limits: the entry the host calls.
(defun fn-idle-gc-decide (quiet publishingp consed-octets)
  (declare (xargs :guard t))
  (fn-idle-gc-verdict *fn-idle-gc-quiet-ticks* *fn-idle-gc-floor-octets*
                      *fn-idle-gc-generation*
                      quiet publishingp consed-octets))

; KEYSTONE.
(defthm fn-idle-gc-verdict-collects-only-when-owed
  (implies (not (equal (fn-idle-gc-verdict quiet-limit floor-octets generation
                                           quiet publishingp consed-octets)
                       :wait))
           (and (not publishingp)
                (natp quiet) (natp quiet-limit) (<= quiet-limit quiet)
                (natp consed-octets) (natp floor-octets) (<= floor-octets consed-octets)
                (equal (fn-idle-gc-verdict quiet-limit floor-octets generation
                                           quiet publishingp consed-octets)
                       (list :collect generation))))
  :rule-classes nil)

(defthm fn-idle-gc-verdict-collects-when-owed
  (implies (and (not publishingp)
                (natp quiet) (natp quiet-limit) (<= quiet-limit quiet)
                (natp consed-octets) (natp floor-octets) (<= floor-octets consed-octets))
           (equal (fn-idle-gc-verdict quiet-limit floor-octets generation
                                      quiet publishingp consed-octets)
                  (list :collect generation)))
  :rule-classes nil)

(defthm fn-idle-gc-verdict-never-collects-during-a-publication
  (equal (fn-idle-gc-verdict quiet-limit floor-octets generation
                             quiet t consed-octets)
         :wait))

(defthm fn-idle-gc-quiet-counts-only-quiet-ticks
  (and (natp (fn-idle-gc-quiet-next quiet publishingp tick-octets activity-octets))
       (implies publishingp
                (equal (fn-idle-gc-quiet-next quiet t tick-octets activity-octets) 0))
       (implies (and (natp tick-octets) (natp activity-octets)
                     (<= activity-octets tick-octets))
                (equal (fn-idle-gc-quiet-next quiet publishingp tick-octets activity-octets)
                       0))
       (implies (and (not publishingp) (natp tick-octets) (natp activity-octets)
                     (< tick-octets activity-octets))
                (equal (fn-idle-gc-quiet-next quiet publishingp tick-octets activity-octets)
                       (1+ (nfix quiet)))))
  :rule-classes nil)

; The same at the entry the host calls (host/native/owner.lisp
; fnn-owner-maybe-collect-idle): a tick that allocates under the profile's
; :idle-gc-activity-kib grows the count, any other tick or a publication
; restarts it.  tests/acl2/idle-collection-tests.lisp evaluates both sides of
; the limit (524287 and 524288 octets).
(defthm fn-idle-gc-quiet-counts-only-quiet-ticks-at-the-limit
  (and (natp (fn-idle-gc-quiet quiet publishingp tick-octets))
       (implies publishingp
                (equal (fn-idle-gc-quiet quiet t tick-octets) 0))
       (implies (and (natp tick-octets)
                     (<= *fn-idle-gc-activity-octets* tick-octets))
                (equal (fn-idle-gc-quiet quiet publishingp tick-octets) 0))
       (implies (and (not publishingp) (natp tick-octets)
                     (< tick-octets *fn-idle-gc-activity-octets*))
                (equal (fn-idle-gc-quiet quiet publishingp tick-octets)
                       (1+ (nfix quiet)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-idle-gc-quiet-counts-only-quiet-ticks
                                   (activity-octets *fn-idle-gc-activity-octets*)))
                  :in-theory (e/d (fn-idle-gc-quiet) (fn-idle-gc-quiet-next)))))

(defthm fn-idle-gc-decide-never-collects-during-a-publication
  (equal (fn-idle-gc-decide quiet t consed-octets) :wait))

; The profile's generation is a collection that releases pages (above SBCL's
; small_generation_limit of 1) and within the generations SBCL has.
(defthm fn-idle-gc-generation-releases-pages
  (and (< 1 *fn-idle-gc-generation*)
       (<= *fn-idle-gc-generation* *fn-idle-gc-pseudo-static*))
  :rule-classes nil)

(in-theory (disable fn-idle-gc-quiet-next fn-idle-gc-verdict))
