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
                1050137266))
(assert! (equal (fn-heap-decide *fn-heap-small-profile* *hft-core* *hft-nursery*
                                (list *hft-2g*))
                '(:heap 1002 "small" 2048)))
(assert! (equal (fn-heap-decide *fn-bs-profile-development* *hft-core* *hft-nursery*
                                (list *hft-2g*))
                '(:refused :machine-cannot-hold-profile 2671 2048)))
(assert! (equal (fn-heap-decide *fn-bs-profile-scale* *hft-core* *hft-nursery*
                                (list 132000000000))
                '(:heap 54751 "scale" 125885)))
(assert! (equal (fn-heap-decide *fn-bs-profile-defaults* *hft-core* *hft-nursery*
                                (list 132000000000))
                '(:refused :machine-cannot-hold-profile 73402932 125885)))
; No store: the image must fit, then the machine is the figure.
(assert! (equal (fn-heap-decide nil *hft-core* *hft-nursery* (list *hft-2g*))
                '(:heap 2048 "none" 2048)))
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
                "heap=1002 MB profile=small machine=2048 MB"))
(assert! (equal (fn-heap-report-line
                 (fn-heap-decide *fn-bs-profile-development* *hft-core* *hft-nursery*
                                 (list *hft-2g*)))
                "refused machine-cannot-hold-profile heap=2671 MB machine=2048 MB"))
(assert! (equal (fn-heap-decision-exit-code '(:heap 1002 "small" 2048)) 0))
(assert! (equal (fn-heap-decision-exit-code
                 '(:refused :machine-cannot-hold-profile 2671 2048))
                1))

; -----------------------------------------------------------------------------
; The keystone: a reachable witness with every hypothesis and the conclusion
; (the small store full to H), then per hypothesis a counterexample where the
; others hold, it fails, and the conclusion fails, and the must-fail of the
; theorem without it.

(assert! (equal (hft-hyps *fn-heap-small-profile* *hft-core* *hft-nursery*
                          (list *hft-2g*) 8388608)
                '(t t t t t)))
(assert! (hft-conclusion *fn-heap-small-profile* *hft-core* *hft-nursery*
                         (list *hft-2g*) 8388608))

; Without the admitted profile: no profile, an image that exactly fills the
; machine; the capture buffer's framing no longer fits.
(assert! (equal (hft-hyps nil (- *hft-2g* *hft-nursery*) *hft-nursery* (list *hft-2g*) 0)
                '(nil t t t t)))
(assert! (not (hft-conclusion nil (- *hft-2g* *hft-nursery*) *hft-nursery*
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
                  (* *fn-heap-mib* (fn-heap-decision-mb decision)))))))

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
                  (* *fn-heap-mib* (fn-heap-decision-mb decision)))))))

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
                  (* *fn-heap-mib* (fn-heap-decision-mb decision)))))))

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
                  (* *fn-heap-mib* (fn-heap-decision-mb decision)))))))

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
                  (* *fn-heap-mib* (fn-heap-decision-mb decision)))))))

; -----------------------------------------------------------------------------
; The refusal theorem's witnesses: both arms reached on admitted profiles.

(assert! (equal (car (fn-heap-decide *fn-heap-small-profile* *hft-core* *hft-nursery*
                                     (list (* 1001 *fn-heap-mib*))))
                :refused))
(assert! (equal (car (fn-heap-decide *fn-heap-small-profile* *hft-core* *hft-nursery*
                                     (list (* 1002 *fn-heap-mib*))))
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
