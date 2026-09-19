; Executable logical checkpoint and suffix-replay assertions.
(in-package "ACL2")
(include-book "../../books/checkpoint")

(defconst *cp-groups* '("fn.letters" "fn.test"))
(defconst *cp-r0*
  (fn-record-make 0 0 0 "<cp0@example.invalid>" '(65 13 10)
                  '("fn.letters") "cp-pin-0" "cp-content-0" "cp-release-0" 2))
; Allocator txids 1, 2 and 3 do not occur in the journal.  They model known
; aborts before the suffix record at txid 4.
(defconst *cp-r1*
  (fn-record-make 1 4 4 "<cp1@example.invalid>" '(66 13 10)
                  '("fn.test") "cp-pin-1" "cp-content-1" "cp-release-1" 3))

(defconst *cp-capture*
  (fn-checkpoint-capture *cp-groups* 10 (list *cp-r0*) 3))
(defconst *cp-value* (fn-checkpoint-capture-value *cp-capture*))
(defconst *cp-restored*
  (fn-checkpoint-restore *cp-value* *cp-groups* 10 (list *cp-r1*) 6))

(assert-event (equal (car *cp-capture*) :ok))
(assert-event (fn-checkpointp *cp-value*))
(assert-event (equal *cp-restored*
                     (fn-checkpoint-full-replay
                      *cp-groups* 10 (list *cp-r0* *cp-r1*) 6)))
(assert-event (equal (car *cp-restored*) :ok))
(assert-event (equal (fn-state-next-txid
                      (fn-node-acceptance (cadr *cp-restored*))) 6))
(assert-event (equal (caddr *cp-restored*) 2))
(assert-event (equal (len (fn-state-articles
                           (fn-node-acceptance (cadr *cp-restored*)))) 2))

; The same checkpoint remains useful when there is no suffix: restoration
; still installs the consumed allocator frontier instead of reusing a gap.
(defconst *cp-empty-restored*
  (fn-checkpoint-restore *cp-value* *cp-groups* 10 nil 3))
(assert-event (equal (car *cp-empty-restored*) :ok))
(assert-event (equal (fn-state-next-txid
                      (fn-node-acceptance (cadr *cp-empty-restored*))) 3))

; Configuration and persistent-frontier mismatches fail before suffix replay.
(assert-event
 (equal (fn-checkpoint-restore *cp-value* '("fn.letters") 10 nil 3)
        '(:error :configuration)))
(assert-event
 (equal (fn-checkpoint-restore *cp-value* *cp-groups* 9 nil 3)
        '(:error :configuration)))
(assert-event
 (equal (fn-checkpoint-restore *cp-value* *cp-groups* 10 nil 2)
        '(:error :frontier)))
(defconst *cp-wrong-frontier*
  (fn-checkpoint-make 0 1 (fn-checkpoint-node *cp-value*)))
(assert-event (not (fn-checkpointp *cp-wrong-frontier*)))
(assert-event
 (equal (fn-checkpoint-restore *cp-wrong-frontier* *cp-groups* 10 nil 3)
        '(:error :checkpoint)))

; A suffix with the wrong next journal sequence is rejected before replay.
(defconst *cp-wrong-sequence-record*
  (fn-record-make 2 4 4 "<seq@example.invalid>" '(81 13 10)
                  '("fn.test") "cp-pin-seq" "cp-content-seq"
                  "cp-release-seq" 1))
(assert-event
 (equal (fn-checkpoint-restore *cp-value* *cp-groups* 10
                               (list *cp-wrong-sequence-record*) 6)
        '(:error :suffix)))

; A duplicate journal sequence and a fresh sequence using a stale txid are
; both rejected by the suffix interval before they reach core replay.
(assert-event
 (equal (fn-checkpoint-restore *cp-value* *cp-groups* 10
                               (list *cp-r0*) 6)
        '(:error :suffix)))
(defconst *cp-stale-txid*
  (fn-record-make 1 2 2 "<stale@example.invalid>" '(83 13 10)
                  '("fn.test") "cp-pin-stale" "cp-content-stale"
                  "cp-release-stale" 1))
(assert-event
 (equal (fn-checkpoint-restore *cp-value* *cp-groups* 10
                               (list *cp-stale-txid*) 6)
        '(:error :suffix)))

; Teeth for FN-CHECKPOINT-RESTORE-REJECTS-FRONTIER-REUSE: *CP-STALE-TXID*'s
; txid 2 is below *CP-VALUE*'s consumed frontier 3, a reachable non-degenerate
; witness reusing this same checkpoint. Each hypothesis is separately shown
; necessary elsewhere in this file: dropping "matching groups" or "matching
; capacity" instead yields :CONFIGURATION (above); dropping "valid/ordered
; frontier" yields :CHECKPOINT or :FRONTIER (above and below); and dropping
; the reuse condition itself (*CP-R1*'s txid 4 is at or above the frontier)
; yields :OK, not :SUFFIX, in the primary restore assertion above.
(assert-event
 (equal (fn-checkpoint-restore *cp-value* *cp-groups* 10
                               (list *cp-stale-txid* *cp-r1*) 6)
        '(:error :suffix)))

; A syntactically ordered suffix that the actual node refuses is a replay
; failure, preserving the distinction from stale/duplicate storage metadata.
(defconst *cp-over-capacity*
  (fn-record-make 1 4 4 "<large@example.invalid>" '(76 13 10)
                  '("fn.test") "cp-pin-large" "cp-content-large"
                  "cp-release-large" 9))
(assert-event
 (equal (fn-checkpoint-restore *cp-value* *cp-groups* 10
                               (list *cp-over-capacity*) 6)
        '(:error :replay)))

(assert-event
 (fn-checkpoint-admissible-splitp
  *cp-groups* 10 (list *cp-r0*) 3 (list *cp-r1*) 6))
