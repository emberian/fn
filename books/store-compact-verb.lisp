; fn: `operator CONFIG store compact', the offline compaction verb (M5).
;
; What the verb does.  One process, holding the exclusive Store lock after the
; ordinary open's full recovery, asks `fn-cverb-decide' what to do with the
; store it opened and carries out the answer and nothing else:
;
;   (:compact (:pack :select :reclaim :retire))
;       capture the whole committed history into one lossless pack
;       (books/checkpoint-compaction.lisp `fn-cc-capture'), publish it,
;       select it, unlink the transaction files it covers
;       (`fn-bs-pack-reclaim-plan', whose preservation theorem is
;       books/checkpoint-compaction-preservation.lisp) and retire the older
;       pack generations (`fn-cprt-retire-plan');
;   (:compact (:reclaim :retire))
;       the selected pack already covers every committed record (a retry
;       after a cut at or after the selection): finish the reclaim and the
;       retirement, write no new pack;
;   (:refused REASON)
;       nothing is written.  REASON is one of :profile, :observation,
;       :empty-history, :already-compact, :exceeds-compaction-unit and
;       :temporary-space.
;
; The host (host/native/checkpoint.lisp `fnn-command-compact') performs the
; observation and the I/O; the decision, its budget and its bounds are here.
;
; Temporary space.  At the verb's peak the store holds every transaction file
; and pack generation it held at open plus the new pack.  The persisted
; profile's aggregate history bound (field 3, `max_recovery_record_bytes':
; 24 MiB for development, 768 MiB for scale) is the budget that sum must fit;
; the pack is refused before any byte is written when it would not.  The pack
; octets are accounted by `fn-cverb-pack-octets', which
; `fn-cverb-capture-within-pack-octets' shows is at least the file the host
; seals.
;
; The compaction unit.  A pack holds at most `*fn-cc-max-events*' (4096)
; events and `*fn-cc-max-octets*' (4 MiB) of summary.  The event limit is not
; a restriction: `fn-cverb-profile-count-within-pack-events' shows every named
; profile's transaction budget is at most 4096.  The octet limit is kept, as
; the scale profile's compaction unit: the open reads the selected pack as one
; bounded read and decodes it as one value before any transaction file, so its
; bound is the open's largest single allocation, and nothing measured supports
; making it profile-sized (768 MiB).  A store whose history summary exceeds
; 4 MiB is refused by name (:exceeds-compaction-unit, exit 1); compacting
; beyond it needs chained packs, which is open.
(in-package "ACL2")
(include-book "checkpoint-compaction")
(include-book "checkpoint-pack-retire")
(include-book "byte-store-compaction-correspondence")
(include-book "store-observed")
(include-book "replay")

; The profile's fields are read through its accessors, closed here: every
; decision below needs only that they are naturals, never how a profile
; validates (books/byte-store-frame.lisp).
(local (in-theory (disable fn-bs-profile-admittedp
                           fn-bs-profile-max-history-octets
                           fn-bs-profile-max-transactions)))

(defconst *fn-cverb-pack-steps* '(:pack :select :reclaim :retire))
(defconst *fn-cverb-resume-steps* '(:reclaim :retire))

(defun fn-cverb-octet-sum (sizes)
  "The on-disk octets of the observed files, as lstat reported them."
  (declare (xargs :guard t))
  (if (consp sizes)
      (+ (nfix (car sizes)) (fn-cverb-octet-sum (cdr sizes)))
    0))

(defun fn-cverb-pack-octets (records)
  "The octets the pack of RECORDS is accounted at: the summary's size bound
plus the frame trailer the host's seal appends."
  (declare (xargs :guard t :verify-guards nil))
  (+ (fn-cc-event-octets-size records) *fn-frame-trailer-octets*))

(defun fn-cverb-space-budget (profile)
  "The persisted profile's aggregate history bound, in octets."
  (declare (xargs :guard t))
  (if (fn-bs-profile-admittedp profile)
      (fn-bs-profile-max-history-octets profile)
    0))

(defun fn-cverb-older-count (generations selected)
  (declare (xargs :guard t))
  (let ((plan (fn-cprt-retire-plan generations selected)))
    (if (equal plan :invalid) 0 (len plan))))

; PROFILE: the decoded persisted profile.  RECORDS: the committed history the
; open reconstructed (pack plus suffix).  LOWER: the selected pack's coverage
; boundary (0 without one).  NAMES: the sorted transaction namespace.
; GENERATIONS and SELECTED: the pack namespace plan and the selected
; generation (nil without one).  FOOTPRINT: the sizes of every transaction
; file and pack generation present.
(defun fn-cverb-decide (profile records lower names generations selected footprint)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((used (len records))
         (reclaim (fn-bs-pack-reclaim-plan names (fn-bs-profile-max-transactions profile)
                                           lower))
         (older (fn-cverb-older-count generations selected)))
    (cond ((not (fn-bs-profile-admittedp profile)) (list :refused :profile))
          ((or (not (natp lower)) (< used lower) (equal reclaim :invalid))
           (list :refused :observation))
          ((equal lower used)
           (cond ((zp used) (list :refused :empty-history))
                 ((and (atom reclaim) (zp older)) (list :refused :already-compact))
                 (t (list :compact *fn-cverb-resume-steps*))))
          ((or (< *fn-cc-max-events* used)
               (< *fn-cc-max-octets* (fn-cc-event-octets-size records)))
           (list :refused :exceeds-compaction-unit))
          ((< (fn-cverb-space-budget profile)
              (+ (fn-cverb-octet-sum footprint) (fn-cverb-pack-octets records)))
           (list :refused :temporary-space))
          (t (list :compact *fn-cverb-pack-steps*)))))

; -----------------------------------------------------------------------------
; The pack the host writes is at most the accounted octets

(local
 (defthm fn-cverb-u16-u32-lengths
   (and (equal (len (fn-cbor-u16-bytes n)) 2)
        (equal (len (fn-cbor-u32-bytes n)) 4))
   :hints (("Goal" :in-theory (enable fn-cbor-u16-bytes fn-cbor-u32-bytes)))))

(local
 (defthm fn-cverb-argument-length
   (<= (len (fn-cbor-encode-argument major n)) 5)
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-cbor-encode-argument)))))

(local
 (defthm fn-cverb-bytes-encoding-length
   (<= (len (fn-cbor-encode-bounded (cons :bytes x) max)) (+ 5 (len x)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-cbor-encode-bounded)))))

(local
 (defthm fn-cverb-uint-encoding-length
   (<= (len (fn-cbor-encode (cons :uint x))) 5)
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-cbor-encode fn-cbor-encode-bounded)))))

(local
 (defthm fn-cverb-encode-events-length
   (<= (+ 32 (len (fn-cc-encode-events events)))
       (fn-cc-event-octets-size events))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-cc-encode-events
                                      fn-cc-event-octets-size)))))

(local
 (defthm fn-cverb-capture-events
   (implies (equal (car (fn-cc-capture records frontier)) :ok)
            (equal (fn-cc-events (fn-cc-nth 1 (fn-cc-capture records frontier)))
                   records))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-cc-capture fn-cc-make fn-cc-events fn-cc-nth)
                            (fn-cc-octet-event-listp fn-cc-event-octets-size))))))

(local
 (defthm fn-cverb-capture-refused
   (implies (not (equal (car (fn-cc-capture records frontier)) :ok))
            (not (fn-cc-summaryp (fn-cc-nth 1 (fn-cc-capture records frontier)))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-cc-capture) (fn-cc-octet-event-listp
                                             fn-cc-event-octets-size))))))

; The host's capture (host/checkpoint-host.lisp
; `fn-store-checkpoint-compaction-capture', called by
; host/native/checkpoint.lisp `fnn-pack-publish') is `fn-cc-encode' of this
; summary; `fnn-seal' appends `*fn-frame-trailer-octets*'.  Whatever it
; captures, its payload is within the summary's accounted size.
(defthm fn-cverb-capture-within-pack-octets
  (<= (len (fn-cc-encode (fn-cc-nth 1 (fn-cc-capture records frontier))))
      (fn-cc-event-octets-size records))
  :rule-classes :linear
  :hints (("Goal" :cases ((equal (car (fn-cc-capture records frontier)) :ok))
           :in-theory (e/d (fn-cc-encode fn-cc-event-octets-size)
                           (fn-cc-capture fn-cc-summaryp)))))

; -----------------------------------------------------------------------------
; Keystones over the decision the verb carries out

; KEYSTONE (temporary space).  When the verb decides to pack, every file the
; store held at open plus the pack file the host then seals from the same
; records fits the persisted profile's aggregate history bound.  For every
; frontier: the pack's size does not depend on it beyond the encoding bound.
(defthm fn-cverb-pack-fits-the-profile-budget
  (implies (equal (fn-cverb-decide profile records lower names
                                   generations selected footprint)
                  (list :compact *fn-cverb-pack-steps*))
           (<= (+ (fn-cverb-octet-sum footprint)
                  (len (fn-cc-encode (fn-cc-nth 1 (fn-cc-capture records frontier))))
                  *fn-frame-trailer-octets*)
               (fn-bs-profile-max-history-octets profile)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cverb-decide fn-cverb-pack-octets
                                   fn-cverb-space-budget)
                                  (fn-cc-capture fn-cc-encode
                                   fn-cc-event-octets-size
                                   fn-bs-pack-reclaim-plan
                                   fn-cverb-older-count
                                   fn-bs-profile-admittedp)))))

; A history of exact Store events below the frontier has fewer events than
; the frontier: each takes a distinct txid in [lower, frontier).
(local
 (defthm fn-cverb-event-list-head-integer-fc
   (implies (and (fn-cc-octet-event-listp records sequence lower frontier)
                 (consp records))
            (integerp (fn-store-event-generation
                       (fn-cc-nth 1 (fn-store-event-decode-exact (car records))))))
   :rule-classes ((:forward-chaining
                   :trigger-terms ((fn-cc-octet-event-listp records sequence lower frontier))))
   :hints (("Goal" :in-theory (e/d (fn-cc-octet-event-listp)
                                   (fn-store-event-decode-exact))
            :use ((:instance fn-replay-record-counters-are-natural
                   (record (fn-cc-nth 1 (fn-store-event-decode-exact (car records))))))))))

(local
 (defthm fn-cverb-event-list-within-frontier
   (implies (and (natp lower) (integerp frontier)
                 (consp records)
                 (fn-cc-octet-event-listp records sequence lower frontier))
            (<= (+ lower (len records)) frontier))
   :rule-classes nil
   :hints (("Goal" :induct (fn-cc-octet-event-listp records sequence lower frontier)
            :in-theory (e/d (fn-cc-octet-event-listp)
                            (fn-store-event-decode-exact))))))

; KEYSTONE (the compaction unit covers the capture's size refusals).  When the
; verb decides to pack a history the open admitted (the records are the exact
; Store events from sequence 0 below the frontier), the capture the host then
; calls succeeds: its only other refusals are the size limits the decision
; already applied, so a pack decision is never refused by the capture.
(defthm fn-cverb-pack-decision-capture-succeeds
  (implies (and (equal (fn-cverb-decide profile records lower names
                                        generations selected footprint)
                       (list :compact *fn-cverb-pack-steps*))
                (fn-record-uint32p frontier)
                (fn-cc-octet-event-listp records 0 0 frontier))
           (equal (car (fn-cc-capture records frontier)) :ok))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-cverb-event-list-within-frontier
                                   (sequence 0) (lower 0)))
           :in-theory (e/d (fn-cverb-decide fn-cc-capture
                                   fn-record-uint32p)
                                  (fn-cc-octet-event-listp
                                   fn-cc-event-octets-size
                                   fn-bs-pack-reclaim-plan
                                   fn-cverb-older-count
                                   fn-bs-profile-admittedp)))))

; A store whose selected pack already covers every committed record is never
; packed again: a retry after a cut at or after the selection finishes the
; reclaim and the retirement, or is refused.  By definition of the decision.
(defthm fn-cverb-covered-history-writes-no-pack-by-definition
  (implies (equal lower (len records))
           (not (equal (fn-cverb-decide profile records lower names
                                        generations selected footprint)
                       (list :compact *fn-cverb-pack-steps*))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cverb-decide)
                                  (fn-bs-pack-reclaim-plan fn-cverb-older-count
                                   fn-bs-profile-admittedp)))))

; The pack's event limit is never the refusal under a preset: the open's
; namespace gate admits at most the profile's max_transactions, and each
; preset's (format 8 or its format-7 tuple) is at most the pack's 4096
; events.  Under an operator's profile with max_transactions above 4096 (the
; D27 default is 2^32-1) it can be: a history of more than 4096 events is
; refused by name (`:exceeds-compaction-unit'), a work bound of the one-unit
; pack, until chained packs (design 2026-09-25-bounds, P5).  The test book
; carries that witness.
(defthm fn-cverb-preset-count-within-pack-events
  (implies (member-equal profile (list *fn-bs-profile-development*
                                       *fn-bs-profile-scale*
                                       *fn-bs-meta-format-7-development-values*
                                       *fn-bs-meta-format-7-scale-values*))
           (<= (fn-bs-profile-max-transactions profile) *fn-cc-max-events*))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; Finding 3 of m5-compaction: what the open can and cannot detect
;
; The allocation frontier is a transaction ID, shared by the configuration and
; Store histories, and reserved BEFORE the record it names is written.  A
; reservation abandoned by a crash or a known pre-publication failure leaves
; the frontier above the last record's txid, and replay accepts that gap
; (books/replay.lisp `fn-replay-advance-okp', "a known-aborted transaction
; gap").  So the store in which the newest record file was lost and the store
; in which that record's reservation was abandoned present the same
; observation: the same names, the same record bytes, the same frontier.
; The open's history gate accepts every prefix of a history it accepts; no
; check over this observation, however evaluated, can refuse the one and not
; the other.  Detecting the loss needs a durable witness written after the
; record's commit, which the Store does not keep.

(local
 (defthm fn-cverb-record-list-prefix
   (implies (and (true-listp prefix)
                 (fn-sf-record-listp (append prefix suffix) sequence lower frontier))
            (fn-sf-record-listp prefix sequence lower frontier))
   :hints (("Goal" :in-theory (enable fn-sf-record-listp)))))

; The history gate of the open (`fn-cpo-open-observed', which
; host/store-node-host.lisp `fn-store-sn-recover' calls at every open) accepts
; the history with any suffix left out.
(defthm fn-cverb-open-history-gate-admits-a-lost-suffix
  (implies (and (true-listp prefix)
                (fn-sn-observed-historyp frontier (append prefix suffix)))
           (fn-sn-observed-historyp frontier prefix))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-sn-observed-historyp))))

(in-theory (disable fn-cverb-decide fn-cverb-pack-octets fn-cverb-space-budget
                    fn-cverb-older-count fn-cverb-octet-sum))
