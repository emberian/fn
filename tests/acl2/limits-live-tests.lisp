; Teeth for books/limits-live.lisp (row S1, lane limits-live-3, PRF-940).
; The development profile (T = 128) on a 64 GiB machine with the 69046a76
; core: a raise of T within the reservation the process started with is
; applied now; a raise beyond it is recorded for the next start; a lowering
; below the store's committed transactions is refused by name, with the use.

(in-package "ACL2")
(include-book "../../books/limits-live")
(include-book "std/testing/assert-bang" :dir :system)

(defconst *lim-t-core* 389141032)              ; the 69046a76 fn-host.core
(defconst *lim-t-nursery* (* 64 1024 1024))    ; +fnn-gc-nursery-octets+
(defconst *lim-t-machine* (list (* 65536 *fn-heap-mib*)))
(defconst *lim-t-p* *fn-bs-profile-development*)
(defconst *lim-t-use* '(100 1000000))          ; 100 transactions, 1 MB charged
(defconst *lim-t-run-mb*                       ; the reservation this profile's start took
  (fn-heap-decision-mb (fn-heap-status-decide *lim-t-p* *lim-t-core* *lim-t-nursery* *lim-t-machine* nil)))

(assert! (equal (fn-bs-pf *fn-bs-pf-max-transactions* *lim-t-p*) 128))
(assert! (posp *lim-t-run-mb*))

; -----------------------------------------------------------------------------
; fn-lim-decide-accepted-keeps-use-within

; REACHABLE, :applied.  Antecedent: the decision is accepted.  Conclusion:
; the field is live, the new profile is admitted, the use (100) is within the
; new T (129), and the figure fits the running reservation.
(defconst *lim-t-applied*
  (fn-lim-decide "max-transactions" 129 *lim-t-p* *lim-t-use*
                 *lim-t-run-mb* *lim-t-core* *lim-t-nursery* *lim-t-machine* nil))
(assert! (equal (car *lim-t-applied*) :applied))
(assert! (fn-lim-acceptedp *lim-t-applied*))
(assert! (fn-lim-fieldp "max-transactions"))
(assert! (fn-bs-profile-admittedp (fn-lim-apply-row *lim-t-p* "max-transactions" 129)))
(assert! (<= (fn-lim-use-of "max-transactions" *lim-t-use*) 129))
(assert! (<= (cadr *lim-t-applied*) *lim-t-run-mb*))

; REACHABLE, :at-restart.  A raise to 4096 needs more heap than the running
; reservation: recorded, and the conclusion's first three conjuncts hold.
(defconst *lim-t-later*
  (fn-lim-decide "max-transactions" 4096 *lim-t-p* *lim-t-use*
                 *lim-t-run-mb* *lim-t-core* *lim-t-nursery* *lim-t-machine* nil))
(assert! (equal (car *lim-t-later*) :at-restart))
(assert! (< *lim-t-run-mb* (cadr *lim-t-later*)))
(assert! (fn-bs-profile-admittedp (fn-lim-apply-row *lim-t-p* "max-transactions" 4096)))
(assert! (<= (fn-lim-use-of "max-transactions" *lim-t-use*) 4096))
; Offline (no process holds a reservation: run-mb 0) every accepted change is
; :at-restart.
(assert! (equal (car (fn-lim-decide "max-transactions" 129 *lim-t-p* *lim-t-use*
                                    0 *lim-t-core* *lim-t-nursery* *lim-t-machine* nil))
                :at-restart))

; CONCLUSION FAILURE, refused below the current use: T = 99 < 100 committed.
(assert! (equal (fn-lim-decide "max-transactions" 99 *lim-t-p* *lim-t-use*
                               *lim-t-run-mb* *lim-t-core* *lim-t-nursery* *lim-t-machine* nil)
                '(:refused :below-current-use "max-transactions" 100)))
(assert! (not (<= (fn-lim-use-of "max-transactions" *lim-t-use*) 99)))
; History octets likewise.
(assert! (equal (fn-lim-decide "max-history-octets" 999999 *lim-t-p* *lim-t-use*
                               *lim-t-run-mb* *lim-t-core* *lim-t-nursery* *lim-t-machine* nil)
                '(:refused :below-current-use "max-history-octets" 1000000)))
; A field that is not live (the log-scan bound R) is refused by name.
(assert! (equal (fn-lim-decide "max-record-octets" 4096 *lim-t-p* *lim-t-use*
                               *lim-t-run-mb* *lim-t-core* *lim-t-nursery* *lim-t-machine* nil)
                '(:refused :not-a-live-limit "max-record-octets" 0)))
(assert! (not (fn-lim-fieldp "max-record-octets")))
; An invalid profile (T = 0 fails the resolution) is refused with its reason.
(assert! (equal (car (fn-lim-decide "max-transactions" 0 *lim-t-p* '(0 0)
                                    *lim-t-run-mb* *lim-t-core* *lim-t-nursery* *lim-t-machine* nil))
                :refused))
; The machine cannot hold the figure: a 2 GiB machine refuses T = 4096 by the
; reservation's name, with both numbers.
(assert! (equal (cadr (fn-lim-decide "max-transactions" 4096 *lim-t-p* *lim-t-use* 0
                                     *lim-t-core* *lim-t-nursery*
                                     (list (* 2048 *fn-heap-mib*)) nil))
                :machine-cannot-hold-profile))
; The :applied conjunct fails when the reservation is smaller than the
; figure: the same raise with run-mb one below it is :at-restart, not applied.
(assert! (equal (car (fn-lim-decide "max-transactions" 129 *lim-t-p* *lim-t-use*
                                    (1- (cadr *lim-t-applied*))
                                    *lim-t-core* *lim-t-nursery* *lim-t-machine* nil))
                :at-restart))

; -----------------------------------------------------------------------------
; fn-lim-effective-of-append-record (a change replays identically)

(defconst *lim-t-stamp* *fn-cfg-default-stamp*)
(defconst *lim-t-r1*
  (fn-cfg-record-make 1 5 2 (fn-lim-deltas "max-transactions" 129) *lim-t-stamp*))
(defconst *lim-t-r2*
  (fn-cfg-record-make 2 9 3 (append (fn-lim-deltas "max-article-octets" 65536)
                                    (list (fn-cfg-set-capacity 20)))
                      *lim-t-stamp*))
(defconst *lim-t-history* (list *fn-cfg-default-record* *lim-t-r1*))

; REACHABLE: the profile an owner installs applying R2 over the one it serves
; is the one the next open computes from the history R2 ends; both change T
; and A and nothing else the fold reads (the capacity row is not a limit).
(assert! (equal (fn-lim-effective *lim-t-p* (append *lim-t-history* (list *lim-t-r2*)))
                (fn-lim-apply-deltas (fn-lim-effective *lim-t-p* *lim-t-history*)
                                     (fn-cfg-record-change *lim-t-r2*))))
(defconst *lim-t-served* (fn-lim-effective *lim-t-p* (append *lim-t-history* (list *lim-t-r2*))))
(assert! (equal (fn-bs-pf *fn-bs-pf-max-transactions* *lim-t-served*) 129))
(assert! (equal (fn-bs-pf *fn-bs-pf-max-article-octets* *lim-t-served*) 65536))
(assert! (equal (fn-bs-pf *fn-bs-pf-max-history-octets* *lim-t-served*)
                (fn-bs-pf *fn-bs-pf-max-history-octets* *lim-t-p*)))
; The last row of a field wins: a later lowering overrides the earlier raise.
(defconst *lim-t-r3*
  (fn-cfg-record-make 3 11 4 (fn-lim-deltas "max-transactions" 120) *lim-t-stamp*))
(assert! (equal (fn-bs-pf *fn-bs-pf-max-transactions*
                          (fn-lim-effective *lim-t-p* (list *lim-t-r1* *lim-t-r3*)))
                120))
; CONCLUSION FAILURE (order matters): applying the rows in the other order is
; a different profile, so the theorem's append-at-the-end is the content.
(assert! (not (equal (fn-lim-effective *lim-t-p* (list *lim-t-r1* *lim-t-r3*))
                     (fn-lim-effective *lim-t-p* (list *lim-t-r3* *lim-t-r1*)))))
; A lowered T drags the open-suffix bound K down with it (init's resolution).
(assert! (equal (fn-bs-pf *fn-bs-pf-max-open-suffix*
                          (fn-lim-apply-row *lim-t-p* "max-transactions" 3))
                (min 3 (fn-bs-pf *fn-bs-pf-max-open-suffix* *lim-t-p*))))

; fn-lim-apply-deltas-of-the-verb: the verb's row applied is fn-lim-apply-row;
; the hypothesis (a live field) removed, the verb's row for R is ignored by
; the fold while fn-lim-apply-row would write slot A.
(assert! (equal (fn-lim-apply-deltas *lim-t-p* (fn-lim-deltas "max-history-octets" 50000000))
                (fn-lim-apply-row *lim-t-p* "max-history-octets" 50000000)))
(assert! (not (fn-lim-fieldp "max-record-octets")))
(assert! (not (equal (fn-lim-apply-deltas *lim-t-p* (fn-lim-deltas "max-record-octets" 7))
                     (fn-lim-apply-row *lim-t-p* "max-record-octets" 7))))

; -----------------------------------------------------------------------------
; The words (fn-lim-decision-line) and the exit (fn-lim-decision-exit).
(assert! (equal (fn-lim-decision-line "max-transactions" 129 *lim-t-applied* 4200)
                (concatenate 'string "applied limit max-transactions=129 heap="
                             (fn-heap-decimal (cadr *lim-t-applied*))
                             " MB: served now, no data moved")))
(assert! (equal (fn-lim-decision-line "max-transactions" 4096 '(:at-restart 2688) 4200)
                "recorded limit max-transactions=4096 effective-at-next-start: takes effect at the next restart (about 5 s), no data moved; the next start reserves heap=2688 MB"))
(assert! (equal (fn-lim-decision-line "max-transactions" 99
                                      '(:refused :below-current-use "max-transactions" 100) 0)
                "refused limit max-transactions=99 below-current-use: the store holds 100"))
(assert! (equal (fn-lim-decision-line "max-transactions" 4096
                                      '(:refused :machine-cannot-hold-profile 2688 2048) 0)
                "refused limit max-transactions=4096 machine-cannot-hold-profile: heap=2688 MB machine=2048 MB"))
(assert! (equal (fn-lim-decision-exit *lim-t-applied*) 0))
(assert! (equal (fn-lim-decision-exit *lim-t-later*) 0))
(assert! (equal (fn-lim-decision-exit '(:refused :below-current-use "max-transactions" 100)) 1))

; The control reply's reason word (fn-lim-decision-word): the decision's
; class; the sentence is the reply's line (tests/acl2/native-control-line-tests).
(assert! (equal (fn-lim-decision-word '(:applied 2342)) "applied"))
(assert! (equal (fn-lim-decision-word '(:at-restart 2688)) "recorded"))
(assert! (equal (fn-lim-decision-word '(:refused :below-current-use "max-transactions" 100))
                "below-current-use"))
(assert! (equal (fn-lim-decision-word '(:refused :machine-cannot-hold-profile 2688 2048))
                "machine-cannot-hold-profile"))
(assert! (equal (fn-nctrl-reason-word (fn-lim-decision-reason '(:at-restart 2688)))
                '(114 101 99 111 114 100 101 100)))
(assert! (equal (fn-lim-decision-status *lim-t-later*) :accepted))
(assert! (equal (fn-lim-decision-status '(:refused :below-current-use "max-transactions" 100))
                :refused))

; -----------------------------------------------------------------------------
; Three values (PRF-996): requested, funded, ceiling.

; fn-lim-ceiling: the configuration row's u32 bounds every live field; A the
; article codec below it.
(assert! (equal (fn-lim-ceiling "max-transactions") 4294967295))
(assert! (equal (fn-lim-ceiling "max-history-octets") 4294967295))
(assert! (equal (fn-lim-ceiling "max-article-octets") *fn-record-max-payload*))
(assert! (< *fn-record-max-payload* 4294967295))
; Past the ceiling: refused by name with the ceiling, before the profile or
; the machine is consulted (the u32 row could not carry it).
(defconst *lim-t-past* (fn-lim-decide "max-history-octets" 4294967296 *lim-t-p* *lim-t-use*
                                      *lim-t-run-mb* *lim-t-core* *lim-t-nursery*
                                      *lim-t-machine* nil))
(assert! (equal *lim-t-past*
                '(:refused :above-representation-ceiling "max-history-octets" 4294967295)))
(assert! (not (fn-record-uint32p 4294967296)))
; At the ceiling the representation does not refuse (the machine decides).
(assert! (not (equal (cadr (fn-lim-decide "max-history-octets" 4294967295 *lim-t-p* *lim-t-use*
                                          *lim-t-run-mb* *lim-t-core* *lim-t-nursery*
                                          *lim-t-machine* nil))
                     :above-representation-ceiling)))

; fn-lim-funded-after-decide.  REACHABLE, :applied: the served profile after
; is the candidate, admitted, within use and ceiling, its figure within the
; reservation.
(defconst *lim-t-c129* (fn-lim-apply-row *lim-t-p* "max-transactions" 129))
(defconst *lim-t-funded* (fn-lim-apply-row *lim-t-p* "max-transactions" 120)) ; a sentinel: what the owner served before
(assert! (equal (fn-lim-funded-after *lim-t-applied* *lim-t-funded* *lim-t-c129*) *lim-t-c129*))
(assert! (fn-bs-profile-admittedp *lim-t-c129*))
(assert! (<= (fn-lim-use-of "max-transactions" *lim-t-use*) 129))
(assert! (<= 129 (fn-lim-ceiling "max-transactions")))
(assert! (<= (cadr *lim-t-applied*) *lim-t-run-mb*))
; REACHABLE, :at-restart (a recorded raise): the process keeps what it
; served; the recorded candidate differs from it, so the conclusion is not
; vacuous.
(defconst *lim-t-c4096* (fn-lim-apply-row *lim-t-p* "max-transactions" 4096))
(assert! (equal (fn-lim-funded-after *lim-t-later* *lim-t-funded* *lim-t-c4096*) *lim-t-funded*))
(assert! (not (equal *lim-t-funded* *lim-t-c4096*)))
; CONCLUSION FAILURE of the :applied arm off its hypothesis: the recorded
; decision's served profile is not the candidate.
(assert! (not (equal (fn-lim-funded-after *lim-t-later* *lim-t-funded* *lim-t-c4096*)
                     *lim-t-c4096*)))
; Refused: nothing is funded anew.
(assert! (equal (fn-lim-funded-after *lim-t-past* *lim-t-funded* *lim-t-c4096*) *lim-t-funded*))

; fn-lim-resource-refusal-is-the-reservations.  REACHABLE, :resource: a 2 GiB
; machine refuses T = 4096; every right-hand conjunct holds.
(defconst *lim-t-small* (list (* 2048 *fn-heap-mib*)))
(defconst *lim-t-res* (fn-lim-decide "max-transactions" 4096 *lim-t-p* *lim-t-use* 0
                                     *lim-t-core* *lim-t-nursery* *lim-t-small* nil))
(assert! (equal (fn-lim-refusal-class *lim-t-res*) :resource))
(assert! (fn-lim-fieldp "max-transactions"))
(assert! (<= 4096 (fn-lim-ceiling "max-transactions")))
(assert! (fn-bs-profile-admittedp *lim-t-c4096*))
(assert! (not (equal (car (fn-heap-status-decide *lim-t-c4096* *lim-t-core* *lim-t-nursery*
                                                 *lim-t-small* nil))
                     :heap)))
; Each other class fails exactly one conjunct: the policy (below use), the
; representation (past the ceiling; an invalid profile), and on the 64 GiB
; machine the reservation answers a heap.
(assert! (equal (fn-lim-refusal-class '(:refused :below-current-use "max-transactions" 100)) :policy))
(assert! (equal (fn-lim-refusal-class
                 (fn-lim-decide "max-record-octets" 4096 *lim-t-p* *lim-t-use*
                                *lim-t-run-mb* *lim-t-core* *lim-t-nursery* *lim-t-machine* nil))
                :policy))
(assert! (equal (fn-lim-refusal-class *lim-t-past*) :representation))
(assert! (not (<= 4294967296 (fn-lim-ceiling "max-history-octets"))))
(assert! (equal (fn-lim-refusal-class
                 (fn-lim-decide "max-transactions" 0 *lim-t-p* '(0 0)
                                *lim-t-run-mb* *lim-t-core* *lim-t-nursery* *lim-t-machine* nil))
                :representation))
(assert! (equal (fn-lim-refusal-class *lim-t-later*) nil))
(assert! (equal (car (fn-heap-status-decide *lim-t-c4096* *lim-t-core* *lim-t-nursery*
                                            *lim-t-machine* nil))
                :heap))

; The operator's lines.
(assert! (equal (fn-lim-values-line "max-transactions" *lim-t-c4096* *lim-t-funded*)
                "limit max-transactions requested=4096 funded=120 ceiling=4294967295"))
(assert! (equal (fn-lim-values-line "max-transactions" *lim-t-c4096* nil)
                "limit max-transactions requested=4096 funded=none ceiling=4294967295"))
(assert! (equal (len (fn-lim-values-lines *lim-t-p* nil)) 3))
; A recorded raise on a live owner: requested moves, funded does not.
(assert! (equal (fn-lim-reply-line "max-transactions" 4096 '(:at-restart 2688) 4200
                                   *lim-t-funded* *lim-t-funded*)
                "recorded limit max-transactions=4096 effective-at-next-start: takes effect at the next restart (about 5 s), no data moved; the next start reserves heap=2688 MB; limit max-transactions requested=4096 funded=120 ceiling=4294967295"))
; Applied: both move.
(assert! (equal (fn-lim-reply-line "max-transactions" 129 '(:applied 2342) 4200
                                   *lim-t-p* *lim-t-p*)
                "applied limit max-transactions=129 heap=2342 MB: served now, no data moved; limit max-transactions requested=129 funded=129 ceiling=4294967295"))
; Refused: neither moves.
(assert! (equal (fn-lim-reply-line "max-transactions" 99
                                   '(:refused :below-current-use "max-transactions" 100) 0
                                   *lim-t-p* nil)
                "refused limit max-transactions=99 below-current-use: the store holds 100; limit max-transactions requested=128 funded=none ceiling=4294967295"))
(assert! (equal (fn-lim-decision-line "max-history-octets" 4294967296 *lim-t-past* 0)
                "refused limit max-history-octets=4294967296 above-representation-ceiling: the format carries at most 4294967295"))

; -----------------------------------------------------------------------------
; The running owner's carried triple (PRF-996's live report).

; fn-lim-reported-triple-is-the-decisions.  REACHABLE (a recorded raise on a
; live owner): every hypothesis holds, the reply is the decision sentence
; then the report's line for the field, and that line is in the report.
(defconst *lim-t-after* (fn-lim-carry-after "max-transactions" 4096 '(:at-restart 2688)
                                            (cons *lim-t-p* *lim-t-funded*)))
(defconst *lim-t-after-line*
  (fn-lim-values-line "max-transactions" (fn-lim-carry-requested *lim-t-after*)
                      (fn-lim-carry-funded *lim-t-after*)))
(assert! (and (fn-lim-fieldp "max-transactions") *lim-t-p* *lim-t-funded*))
(assert! (equal (fn-lim-reply-line "max-transactions" 4096 '(:at-restart 2688) 4200
                                   *lim-t-p* *lim-t-funded*)
                (concatenate 'string
                             (fn-lim-decision-line "max-transactions" 4096 '(:at-restart 2688) 4200)
                             "; " *lim-t-after-line*)))
(assert! (member-equal *lim-t-after-line* (fn-lim-report-lines *lim-t-after*)))
(assert! (equal *lim-t-after-line*
                "limit max-transactions requested=4096 funded=120 ceiling=4294967295"))
(assert! (equal (car (fn-lim-report-lines *lim-t-after*)) *lim-t-after-line*))
(assert! (equal (take (+ 1 (length *lim-t-after-line*)) (fn-lim-report-octets *lim-t-after*))
                (append (fn-record-string-octets *lim-t-after-line*) (list 10))))
; HYPOTHESIS REMOVAL, FUNDED (offline: NIL).  The field is live and VALUES
; given; an :applied decision's carry funds the candidate, but the offline
; reply prints funded=none: the reply is not the report's line.
(defconst *lim-t-after-offline* (fn-lim-carry-after "max-transactions" 129 '(:applied 2342)
                                                    (cons *lim-t-p* nil)))
(assert! (and (fn-lim-fieldp "max-transactions") *lim-t-p*))
(assert! (not (equal (fn-lim-reply-line "max-transactions" 129 '(:applied 2342) 0 *lim-t-p* nil)
                     (concatenate 'string
                                  (fn-lim-decision-line "max-transactions" 129 '(:applied 2342) 0)
                                  "; "
                                  (fn-lim-values-line "max-transactions"
                                                      (fn-lim-carry-requested *lim-t-after-offline*)
                                                      (fn-lim-carry-funded *lim-t-after-offline*))))))
; HYPOTHESIS REMOVAL, VALUES (nothing carried yet).  The field is live and
; FUNDED given; a refusal leaves no requested profile, so the report has no
; line to carry the reply's triple.
(defconst *lim-t-after-none* (fn-lim-carry-after "max-transactions" 99
                                                 '(:refused :below-current-use "max-transactions" 100)
                                                 (cons nil *lim-t-funded*)))
(assert! (and (fn-lim-fieldp "max-transactions") *lim-t-funded*))
(assert! (equal (fn-lim-report-lines *lim-t-after-none*) nil))
(assert! (not (member-equal (fn-lim-values-line "max-transactions"
                                                (fn-lim-carry-requested *lim-t-after-none*)
                                                (fn-lim-carry-funded *lim-t-after-none*))
                            (fn-lim-report-lines *lim-t-after-none*))))
; HYPOTHESIS REMOVAL, FIELDP.  VALUES and FUNDED given; a field that is not a
; live limit has no line in the report.
(defconst *lim-t-after-bogus* (fn-lim-carry-after "max-payload" 5
                                                  '(:refused :not-a-live-limit "max-payload" 0)
                                                  (cons *lim-t-p* *lim-t-funded*)))
(assert! (and (not (fn-lim-fieldp "max-payload")) *lim-t-p* *lim-t-funded*))
(assert! (not (member-equal (fn-lim-values-line "max-payload"
                                                (fn-lim-carry-requested *lim-t-after-bogus*)
                                                (fn-lim-carry-funded *lim-t-after-bogus*))
                            (fn-lim-report-lines *lim-t-after-bogus*))))

; fn-lim-carry-after-is-the-history.  REACHABLE: an open's carry (the
; history's profile, here the sealed one under an empty history) and an
; accepted recorded raise: the carry becomes the history the verb's record
; ends; a refusal leaves it the history it was.
(defconst *lim-t-rec* (fn-cfg-record-make 1 1 2 (fn-lim-deltas "max-transactions" 4096) nil))
(assert! (equal (fn-lim-carry-requested (cons *lim-t-p* *lim-t-p*)) (fn-lim-effective *lim-t-p* nil)))
(assert! (fn-lim-acceptedp '(:at-restart 2688)))
(assert! (equal (fn-lim-carry-requested
                 (fn-lim-carry-after "max-transactions" 4096 '(:at-restart 2688)
                                     (cons *lim-t-p* *lim-t-p*)))
                (fn-lim-effective *lim-t-p* (list *lim-t-rec*))))
(assert! (not (equal (fn-lim-effective *lim-t-p* (list *lim-t-rec*)) *lim-t-p*)))
(assert! (equal (fn-lim-carry-requested
                 (fn-lim-carry-after "max-transactions" 99
                                     '(:refused :below-current-use "max-transactions" 100)
                                     (cons *lim-t-p* *lim-t-p*)))
                (fn-lim-effective *lim-t-p* nil)))
; HYPOTHESIS REMOVAL, THE CARRY IS THE HISTORY'S.  The field is live; a carry
; that is not the history's stays not the history's (the conclusion fails).
(assert! (not (equal (fn-lim-carry-requested (cons *lim-t-funded* *lim-t-p*))
                     (fn-lim-effective *lim-t-p* nil))))
(assert! (not (equal (fn-lim-carry-requested
                      (fn-lim-carry-after "max-transactions" 99
                                          '(:refused :below-current-use "max-transactions" 100)
                                          (cons *lim-t-funded* *lim-t-p*)))
                     (fn-lim-effective *lim-t-p* nil))))
; HYPOTHESIS REMOVAL, FIELDP.  The carry is the history's; an accepted
; decision over a slot that is not a live limit moves the carry (the row's
; index is the article field's) while the history ignores the row.
(defconst *lim-t-rec-bogus* (fn-cfg-record-make 1 1 2 (fn-lim-deltas "max-payload" 5) nil))
(assert! (not (fn-lim-fieldp "max-payload")))
(assert! (not (equal (fn-lim-carry-requested
                      (fn-lim-carry-after "max-payload" 5 '(:applied 2342)
                                          (cons *lim-t-p* *lim-t-p*)))
                     (fn-lim-effective *lim-t-p* (list *lim-t-rec-bogus*)))))
