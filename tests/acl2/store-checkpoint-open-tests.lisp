; Teeth for books/store-checkpoint-open and books/store-checkpoint-codec.
;
; The witness is config-observed-tests' recovery image: two retention
; events (txids 0 and 1) and two configuration records, the second at txid 7
; after both events, so the configuration fold pauses with one configuration
; still to come.  Split after the first event, the checkpoint open equals
; the full open, and the full open succeeds.
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)
(include-book "../../books/store-checkpoint-open")
(include-book "../../books/store-checkpoint-codec")

(defconst *sco-t-events*
  (list (fn-store-retention-event-make :undertake 0 0 0
                                        "forward-cpo" "subject" "evidence" 10)
        (fn-store-retention-event-make :release 1 1 1
                                        "forward-cpo" "subject" "evidence" 0)))
(defconst *sco-t-configs*
  (list *fn-cfg-default-record*
        (fn-cfg-record-make 1 7 2 (list (fn-cfg-set-capacity 1))
                            *fn-cfg-default-stamp*)))
(defconst *sco-t-prefix* (list (car *sco-t-events*)))
(defconst *sco-t-suffix* (cdr *sco-t-events*))
(defconst *sco-t-full* (fn-cpo-open-observed *sco-t-configs* 8 *sco-t-events*))
(defconst *sco-t-capture* (fn-sco-capture *sco-t-configs* *sco-t-prefix*))

; The keystone, evaluated: a reachable, successful open, equal both ways.
(assert-event (fn-sn-open-okp *sco-t-full*))
(assert-event (equal (fn-sco-open *sco-t-capture* *sco-t-configs* 8 *sco-t-suffix*)
                     *sco-t-full*))
(assert-event (equal (fn-sco-sequence *sco-t-capture*) 1))
; The configuration fold paused with one configuration consumed.
(assert-event (equal (fn-sco-cpr *sco-t-capture*)
                     (fn-sco-paused (nth 1 (fn-sco-cpr *sco-t-capture*)) 1 1)))
; The owner's next checkpoint is the capture of the whole history.
(assert-event (equal (fn-sco-extend *sco-t-capture* *sco-t-configs* *sco-t-suffix*)
                     (fn-sco-capture *sco-t-configs* *sco-t-events*)))
; The configuration the opened Store serves is the full replay's.
(assert-event (equal (fn-sco-replay-result *sco-t-capture* *sco-t-configs* *sco-t-suffix*)
                     (fn-cpr-replay *sco-t-configs* *sco-t-events*)))

; Teeth: a checkpoint missing any one slot does not open to the full state.
(defun sco-t-drop-slot (c n)
  (declare (xargs :guard (natp n) :verify-guards nil))
  (update-nth n nil c))
(must-fail
 (defthm sco-t-without-consumer-slot
   (equal (fn-sco-open (sco-t-drop-slot *sco-t-capture* 4) *sco-t-configs* 8 *sco-t-suffix*)
          *sco-t-full*)))
(must-fail
 (defthm sco-t-without-topic-slot
   (equal (fn-sco-open (sco-t-drop-slot *sco-t-capture* 5) *sco-t-configs* 8 *sco-t-suffix*)
          *sco-t-full*)))
(must-fail
 (defthm sco-t-without-event-index-slot
   (equal (fn-sco-open (sco-t-drop-slot *sco-t-capture* 6) *sco-t-configs* 8 *sco-t-suffix*)
          *sco-t-full*)))
(must-fail
 (defthm sco-t-without-identity-slot
   (equal (fn-sco-open (sco-t-drop-slot *sco-t-capture* 3) *sco-t-configs* 8 *sco-t-suffix*)
          *sco-t-full*)))
(must-fail
 (defthm sco-t-without-configuration-slot
   (equal (fn-sco-open (sco-t-drop-slot *sco-t-capture* 2) *sco-t-configs* 8 *sco-t-suffix*)
          *sco-t-full*)))
(must-fail
 (defthm sco-t-without-records-slot
   (equal (fn-sco-open (sco-t-drop-slot *sco-t-capture* 1) *sco-t-configs* 8 *sco-t-suffix*)
          *sco-t-full*)))
; A checkpoint of another prefix does not open to this history.
(must-fail
 (defthm sco-t-stale-checkpoint
   (equal (fn-sco-open (fn-sco-capture *sco-t-configs* nil) *sco-t-configs* 8 *sco-t-suffix*)
          *sco-t-full*)))

; fn-sco-extend-of-capture: without a true-list suffix, extension keeps the
; improper tail and capture drops it.
(must-fail
 (defthm sco-t-extend-improper-suffix
   (equal (fn-sco-extend *sco-t-capture* *sco-t-configs* (cons (cadr *sco-t-events*) 5))
          (fn-sco-capture *sco-t-configs* (append *sco-t-prefix* (cons (cadr *sco-t-events*) 5))))))
; fn-sco-finalize-of-capture: without a true-list history, capture repairs it
; and the checkpoint would open what the full open refuses.
(must-fail
 (defthm sco-t-finalize-improper-history
   (equal (fn-sco-finalize (fn-sco-capture *sco-t-configs* (append *sco-t-events* 5))
                           *sco-t-configs* 8)
          (fn-cpo-open-observed *sco-t-configs* 8 (append *sco-t-events* 5)))))
; fn-sco-cpr-prefix-of-later-configs: a later configuration at txid 0 is
; interleaved before the first event, so the capture sees it.
(defconst *sco-t-early*
  (list (fn-cfg-record-make 1 0 2 (list (fn-cfg-set-capacity 1)) *fn-cfg-default-stamp*)))
(assert-event (not (fn-sco-later-configsp *sco-t-early* *sco-t-prefix*)))
(must-fail
 (defthm sco-t-capture-early-config
   (equal (fn-sco-capture (append (list *fn-cfg-default-record*) *sco-t-early*) *sco-t-prefix*)
          (fn-sco-capture (list *fn-cfg-default-record*) *sco-t-prefix*))))
(assert-event (fn-sco-later-configsp (cdr *sco-t-configs*) *sco-t-events*))
(assert-event (equal (fn-sco-capture *sco-t-configs* *sco-t-events*)
                     (fn-sco-capture (list *fn-cfg-default-record*) *sco-t-events*)))

; fn-sco-select: a verified checkpoint within K serves; every other case is a
; full replay with its reason.
(assert-event (equal (fn-sco-select :ok 1 2 1) '(:checkpoint 1)))
(assert-event (equal (fn-sco-select :absent 1 2 1) '(:full-replay :absent)))
(assert-event (equal (fn-sco-select :refused 1 2 1) '(:full-replay :corrupt)))
(assert-event (equal (fn-sco-select :ok 3 2 5) '(:full-replay :ahead-of-history)))
(assert-event (equal (fn-sco-select :ok 1 5 3) '(:full-replay :suffix-exceeds-k)))

; -----------------------------------------------------------------------------
; The codec, over the witness's checkpoint: it is a tree, it round-trips
; through segments of 64 octets, and the segment chain refuses reorder,
; truncation, splice and a corrupt octet.

; The segment trailer is fn-frame-trailer, which evaluates under its SHA-256
; attachment only outside defconst, so the segments are a macro.
(defmacro sco-t-segments () '(fn-scc-segments *sco-t-capture* 64))
(assert-event (fn-scc-treep *sco-t-capture*))
(assert-event (< 2 (len (sco-t-segments))))
(assert-event (equal (fn-scc-decode-segments (sco-t-segments))
                     (list :ok *sco-t-capture*)))
(assert-event (equal (fn-scc-file-octets *sco-t-capture* 64)
                     (fn-scc-concat (sco-t-segments))))
(assert-event (equal (fn-scc-segment-extent (take 37 (car (sco-t-segments))))
                     (len (car (sco-t-segments)))))
(assert-event (not (equal (car (fn-scc-decode-segments
                                (list* (cadr (sco-t-segments)) (car (sco-t-segments))
                                       (cddr (sco-t-segments)))))
                          :ok)))
(assert-event (not (equal (car (fn-scc-decode-segments (butlast (sco-t-segments) 1)))
                          :ok)))
(defmacro sco-t-other-segments ()
  '(fn-scc-segments (fn-sco-capture *sco-t-configs* *sco-t-events*) 64))
(assert-event (not (equal (car (fn-scc-decode-segments
                                (cons (car (sco-t-segments))
                                      (cdr (sco-t-other-segments)))))
                          :ok)))
(assert-event (not (equal (car (fn-scc-decode-segments
                                (cons (update-nth 40 (mod (+ 1 (nth 40 (car (sco-t-segments)))) 256)
                                                  (car (sco-t-segments)))
                                      (cdr (sco-t-segments)))))
                          :ok)))
; fn-scc-decode-segments-of-segments: a value outside the tree universe is
; not encoded.
(must-fail
 (defthm sco-t-codec-needs-a-tree
   (equal (fn-scc-decode-segments (fn-scc-segments (list 1/2) 64))
          (list :ok (list 1/2)))))
