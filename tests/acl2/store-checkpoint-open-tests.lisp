; Teeth for books/store-checkpoint-open and books/store-checkpoint-codec.
;
; The witness is config-observed-tests' recovery image: two retention
; events (txids 0 and 1) and two configuration records, the second at txid 7
; after both events, so the configuration fold pauses with one configuration
; still to come.  Split after the first event, the checkpoint open equals
; the full open, and the full open succeeds.
(in-package "ACL2")
(include-book "must-fail-checked")
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
(must-fail-checked
 (defthm sco-t-without-consumer-slot
   (equal (fn-sco-open (sco-t-drop-slot *sco-t-capture* 4) *sco-t-configs* 8 *sco-t-suffix*)
          *sco-t-full*)))
(must-fail-checked
 (defthm sco-t-without-topic-slot
   (equal (fn-sco-open (sco-t-drop-slot *sco-t-capture* 5) *sco-t-configs* 8 *sco-t-suffix*)
          *sco-t-full*)))
;; Lane history-columns-3: the open no longer installs the checkpoint's event
;; index into the Store (field 13 retired), so dropping slot 6 leaves the open
;; unchanged.  (The slot is still written: the schema-3 table writer reads it.)
(defthm sco-t-event-index-slot-is-not-read-by-the-open
  (equal (fn-sco-open (sco-t-drop-slot *sco-t-capture* 6) *sco-t-configs* 8 *sco-t-suffix*)
         *sco-t-full*)
  :rule-classes nil)
(must-fail-checked
 (defthm sco-t-without-identity-slot
   (equal (fn-sco-open (sco-t-drop-slot *sco-t-capture* 3) *sco-t-configs* 8 *sco-t-suffix*)
          *sco-t-full*)))
(must-fail-checked
 (defthm sco-t-without-configuration-slot
   (equal (fn-sco-open (sco-t-drop-slot *sco-t-capture* 2) *sco-t-configs* 8 *sco-t-suffix*)
          *sco-t-full*)))
(must-fail-checked
 (defthm sco-t-without-records-slot
   (equal (fn-sco-open (sco-t-drop-slot *sco-t-capture* 1) *sco-t-configs* 8 *sco-t-suffix*)
          *sco-t-full*)))
; A checkpoint of another prefix does not open to this history.
(must-fail-checked
 (defthm sco-t-stale-checkpoint
   (equal (fn-sco-open (fn-sco-capture *sco-t-configs* nil) *sco-t-configs* 8 *sco-t-suffix*)
          *sco-t-full*)))

; fn-sco-extend-of-capture: without a true-list suffix, extension keeps the
; improper tail and capture drops it.
(must-fail-checked
 (defthm sco-t-extend-improper-suffix
   (equal (fn-sco-extend *sco-t-capture* *sco-t-configs* (cons (cadr *sco-t-events*) 5))
          (fn-sco-capture *sco-t-configs* (append *sco-t-prefix* (cons (cadr *sco-t-events*) 5))))))
;; fn-sco-extend-of-capture has one hypothesis, a true-list suffix (the
;; witness above).  Reachable positive witness of the dropped history
;; hypothesis: a prefix holding a record that is not a Store event (a
;; negative sequence) extends to the capture of the concatenation.
(defconst *sco-t-bad* (update-nth 1 -1 (car *sco-t-events*)))
(assert-event
 (and (not (fn-store-event-p *sco-t-bad*))
      (equal (fn-sco-extend (fn-sco-capture *sco-t-configs* (list *sco-t-bad*))
                            *sco-t-configs* *sco-t-suffix*)
             (fn-sco-capture *sco-t-configs* (cons *sco-t-bad* *sco-t-suffix*)))))
;; fn-replay-identity-append-of-true-lists: positive witness over that prefix
;; (the fault is sticky); each hypothesis's removal witness: an improper
;; suffix faults the split with :improper-record-list but not the whole, and
;; an improper prefix the same way.
(assert-event
 (equal (fn-replay-identity-loop (append (list *sco-t-bad*) *sco-t-suffix*)
                                 (fn-stxk-initial-context 0))
        (fn-replay-identity-loop *sco-t-suffix*
                                 (fn-replay-identity-loop (list *sco-t-bad*)
                                                          (fn-stxk-initial-context 0)))))
(assert-event
 (let ((p (list *sco-t-bad*)) (s (cons (cadr *sco-t-events*) 5)))
   (and (true-listp p) (not (true-listp s))
        (not (equal (fn-replay-identity-loop (append p s) (fn-stxk-initial-context 0))
                    (fn-replay-identity-loop s (fn-replay-identity-loop
                                                p (fn-stxk-initial-context 0))))))))
(assert-event
 (let ((p (cons (car *sco-t-events*) 5)) (s *sco-t-suffix*))
   ;; (append p s) is (cons (car p) s) in the logic; spelled out, since
   ;; append's guard asks a true-list first argument.
   (and (not (true-listp p)) (true-listp s)
        (not (equal (fn-replay-identity-loop (cons (car p) s) (fn-stxk-initial-context 0))
                    (fn-replay-identity-loop s (fn-replay-identity-loop
                                                p (fn-stxk-initial-context 0))))))))
; fn-sco-finalize-of-capture: without a true-list history, capture repairs it
; and the checkpoint would open what the full open refuses.
(must-fail-checked
 (defthm sco-t-finalize-improper-history
   (equal (fn-sco-finalize (fn-sco-capture *sco-t-configs* (append *sco-t-events* 5))
                           *sco-t-configs* 8)
          (fn-cpo-open-observed *sco-t-configs* 8 (append *sco-t-events* 5)))))
; fn-sco-cpr-prefix-of-later-configs: a later configuration at txid 0 is
; interleaved before the first event, so the capture sees it.
(defconst *sco-t-early*
  (list (fn-cfg-record-make 1 0 2 (list (fn-cfg-set-capacity 1)) *fn-cfg-default-stamp*)))
(assert-event (not (fn-sco-later-configsp *sco-t-early* *sco-t-prefix*)))
(must-fail-checked
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
; rep-wave-d-3: a file the reader refused within the profile's bounds is
; named, and never serves.
(assert-event (equal (fn-sco-select :exceeds-bound 1 2 1)
                     '(:full-replay :checkpoint-exceeds-bound)))
(assert-event (equal (fn-sco-select :exceeds-bound 1 1 5)
                     '(:full-replay :checkpoint-exceeds-bound)))
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
;; fn-scc-decode-segments-of-segments
; Reachable positive witness: the capture the open writes satisfies all three
; hypotheses (a tree, its encoding and its record count inside the u64 header
; fields) and its segments decode to it.
(assert-event (and (fn-scc-treep *sco-t-capture*)
                   (< (+ 1 (len (fn-scc-encode *sco-t-capture*))) *fn-scc-u64-bound*)
                   (< (fn-scc-value-sequence *sco-t-capture*) *fn-scc-u64-bound*)
                   (< 0 (fn-scc-value-sequence *sco-t-capture*))
                   (equal (fn-scc-decode-segments (fn-scc-segments *sco-t-capture* 64))
                          (list :ok *sco-t-capture*))))
; Removal of the record-count width: a tree whose count is 2^64 keeps the
; tree and length hypotheses, and its segments are refused.
(defconst *sco-t-wide-sequence* (list :v (expt 2 64)))
(assert-event (and (fn-scc-treep *sco-t-wide-sequence*)
                   (< (+ 1 (len (fn-scc-encode *sco-t-wide-sequence*))) *fn-scc-u64-bound*)
                   (not (< (fn-scc-value-sequence *sco-t-wide-sequence*) *fn-scc-u64-bound*))
                   (not (equal (fn-scc-decode-segments
                                (fn-scc-segments *sco-t-wide-sequence* 64))
                               (list :ok *sco-t-wide-sequence*)))))
; Removal of fn-scc-treep beyond the rational case: an integer whose digit
; count reaches 256 keeps both width hypotheses and is not encoded.
(defconst *sco-t-wide-atom* (list :v 0 (expt 256 256)))
(assert-event (with-guard-checking
               :none
               (and (not (fn-scc-treep *sco-t-wide-atom*))
                    (< (+ 1 (len (fn-scc-encode *sco-t-wide-atom*))) *fn-scc-u64-bound*)
                    (< (fn-scc-value-sequence *sco-t-wide-atom*) *fn-scc-u64-bound*)
                    (not (equal (fn-scc-decode-segments
                                 (fn-scc-segments *sco-t-wide-atom* 64))
                                (list :ok *sco-t-wide-atom*))))))
; The encoding-length width: no value of 2^64 octets can be built, so this is
; a component witness, labelled apart: the header's length field cannot tell
; 2^64 from 0, so a longer chunk would be framed with a wrong length.
(assert-event (equal (fn-scc-header 0 1 (expt 2 64) 0) (fn-scc-header 0 1 0 0)))
; A rational is outside the tree universe too.
(must-fail-checked
 (defthm sco-t-codec-needs-a-tree
   (equal (fn-scc-decode-segments (fn-scc-segments (list 1/2) 64))
          (list :ok (list 1/2)))))

; Open u64 exhaustion: crafted checkpoint, exact boundary, and earlier gates.
(defun sco-o-checkpoint (next)
  (declare (xargs :guard t :verify-guards nil))
  (let ((base (fn-sco-capture (list *fn-cfg-default-record*) nil)))
    (fn-sco-make (fn-sco-records base) (fn-sco-cpr base)
                 (update-nth 1 next (fn-sco-identity base))
                 (fn-sco-consumer base) (fn-sco-topic base)
                 (fn-sco-event-index base))))
(defun sco-o-replayed (c)
  (declare (xargs :guard t :verify-guards nil))
  (fn-sco-cpr-finish (fn-sco-cpr c) (list *fn-cfg-default-record*)))
(with-guard-checking-event :none
 (assert-event
  (let* ((configs (list *fn-cfg-default-record*))
         (c (sco-o-checkpoint (expt 2 64)))
         (replayed (sco-o-replayed c)))
   (and (fn-sn-observed-historyp 0 (fn-sco-records c)) (equal (fn-replay-result-kind replayed) :ok) (fn-cnode-statep (fn-replay-result-node replayed)) (fn-replay-advance-okp (fn-cnode-node (fn-replay-result-node replayed)) 0) (equal (fn-stxk-context-next (fn-sco-identity c)) (expt 2 64)) (equal (fn-sco-finalize c configs 0) (fn-sn-open-error :identity)) (equal (fn-sco-finalize-from replayed c configs 0) (fn-sn-open-error :identity)) (equal (fn-sco-finalize c configs 0) (fn-sco-finalize-from replayed c configs 0))))))
(with-guard-checking-event :none
 (assert-event
  (let* ((configs (list *fn-cfg-default-record*))
         (c (sco-o-checkpoint (1- (expt 2 64))))
         (replayed (sco-o-replayed c)))
   (and (fn-sn-observed-historyp 0 (fn-sco-records c)) (equal (fn-replay-result-kind replayed) :ok) (fn-cnode-statep (fn-replay-result-node replayed)) (fn-replay-advance-okp (fn-cnode-node (fn-replay-result-node replayed)) 0) (equal (fn-stxk-context-next (fn-sco-identity c)) (1- (expt 2 64))) (equal (fn-sn-open-kind (fn-sco-finalize c configs 0)) :ok) (equal (fn-sn-identity-next (fn-sn-open-state (fn-sco-finalize c configs 0))) (1- (expt 2 64))) (equal (fn-sn-open-kind (fn-sco-finalize-from replayed c configs 0)) :ok) (equal (fn-sn-identity-next (fn-sn-open-state (fn-sco-finalize-from replayed c configs 0))) (1- (expt 2 64))) (equal (fn-sco-finalize c configs 0) (fn-sco-finalize-from replayed c configs 0))))))

; Full-path old-gate mutation.
(local (defun fn-sco-finalize-old-for-teeth (c configs frontier)
  (declare (xargs :guard t :verify-guards nil))
  (let ((events (fn-sco-records c)))
    (if (or (null configs)
            (not (fn-sn-observed-historyp frontier events)))
        (fn-sn-open-error :history)
      (let ((replayed (fn-sco-cpr-finish (fn-sco-cpr c) configs)))
        (if (not (equal (fn-replay-result-kind replayed) :ok))
            (fn-sn-open-error :replay)
          (let* ((cn (fn-replay-result-node replayed))
                 (node (fn-cnode-node cn)))
            (if (not (and (fn-cnode-statep cn)
                          (fn-replay-advance-okp node frontier)))
                (fn-sn-open-error :frontier)
              (let* ((advanced (fn-replay-advance-txid node frontier))
                     (config (fn-cnode-config cn))
                     (identity (fn-sco-identity c))
                     (consumer (fn-sco-consumer c))
                     (topic (fn-sco-topic c))
                     (files (fn-sf-make :recovering frontier nil events
                                        nil nil nil 0))
                     (seed (fn-sn-observed-seed
                            (fn-cnode-domain-of config)
                            (fn-cfg-capacity (fn-cfg-value config))
                            frontier events))
                     (opened (fn-sn-with-event-index
                              (fn-sn-with-topic
                               (fn-sn-with-consumer
                                (fn-cpo-install
                                 (fn-sn-update-replayed
                                  seed files advanced
                                  (fn-sn-index-of-rows events)
                                  identity)
                                 (fn-cnode-make advanced config) configs)
                                (fn-cp-nth 1 consumer))
                               topic)
                              ; field 13 retired (lane history-columns-3)
                              nil)))
                (if (and (equal (fn-stxk-context-kind identity) :ok)
                         (consp consumer) (eq (car consumer) :ok)
                         (eq (fn-th-at 0 topic) :ok)
                         (fn-sn-statep opened))
                    (fn-sn-open-ok opened)
                  (fn-sn-open-error :identity)))))))))))
(with-guard-checking-event :none
 (assert-event
  (let ((r (fn-sco-finalize-old-for-teeth
             (sco-o-checkpoint (expt 2 64)) (list *fn-cfg-default-record*) 0)))
   (and (equal (fn-sn-open-kind r) :ok)
        (not (fn-record-uint64p (fn-sn-identity-next (fn-sn-open-state r))))))))

; Replay reaches exactly 2^64, but the actual earlier history gate rejects
; this high sequence. The suffix count is zero, not the crafted identity NEXT.
(with-guard-checking-event :none
 (assert-event
  (let* ((configs (list *fn-cfg-default-record*))
         (c (sco-o-checkpoint (1- (expt 2 64))))
         (wire (fn-record-make (1- (expt 2 64)) 0 0 "<open@example>" '(65)
                  '("fn.test") "id" "subject" "evidence" 1 1))
         (suffix (list (fn-held-plain wire 0)))
         (extended (fn-sco-extend c configs suffix)))
   (and (fn-record-p wire)
        (equal (fn-stxk-context-kind (fn-sco-identity extended)) :ok)
        (equal (fn-stxk-context-next (fn-sco-identity extended)) (expt 2 64))
        (not (fn-sn-observed-historyp 1 (fn-sco-records extended)))
        (equal (fn-sco-finalize extended configs 1) (fn-sn-open-error :history))))))
