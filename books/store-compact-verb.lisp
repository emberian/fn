; fn: `operator CONFIG store compact', the offline compaction verb (M5).
;
; What the verb does.  One process, holding the exclusive Store lock after the
; ordinary open's full recovery, asks `fn-cverb-decide' what to do with the
; store it opened and carries out the answer and nothing else:
;
;   (:compact (:pack :select :reclaim :retire))
;       extend the selected chain of lossless packs one link at a time
;       over the uncovered history (books/checkpoint-pack-chain.lisp
;       `fn-ccc-capture-link'), publishing and selecting each link, unlink the transaction files it covers
;       (`fn-bs-pack-reclaim-plan', whose preservation theorem is
;       books/checkpoint-compaction-preservation.lisp) and retire the older
;       pack generations (`fn-cprt-retire-plan');
;   (:compact (:reclaim :retire))
;       the selected pack already covers every committed record (a retry
;       after a cut at or after the selection): finish the reclaim and the
;       retirement, write no new pack;
;   (:refused REASON)
;       nothing is written.  REASON is one of :profile, :observation,
;       :empty-history, :already-compact and :temporary-space.
;
; The host (host/native/checkpoint.lisp `fnn-command-compact') performs the
; observation and the I/O; the decision, its budget and its bounds are here.
;
; Temporary space (PKT-169, decided 2026-09-26).  At the verb's peak the
; disk holds every file the store held at open plus the new pack; the files
; present are already on the disk, so the verb's added demand is the pack.
; The host reports the free octets of the store's filesystem
; (host/native/checkpoint.lisp `fnn-disk-free-octets', statvfs f_bavail *
; f_frsize) and ACL2 refuses the next link by name (:temporary-space) before
; any byte of it is written when its accounted octets
; (`fn-cverb-link-octets') exceed them, or when the host observed no
; natural.  The host asks again, with a fresh observation, before every
; link, so a chain of many links never needs its whole size free at once.
; The persisted profile's history bound H is not the budget here: H bounds
; the open's replay input (the transaction files past the selected chain,
; host/native/io.lisp `fnn-durable-records'), not the disk, and each link
; is read under `fn-ccc-link-octet-bound'.  The former check (the files
; present plus the pack within H) refused every store past half its history
; bound, so a store refused for history headroom could never compact or
; reclaim (reclaim-lifecycle F2).  The reclaiming pack (a whole-history
; summary, books/store-reclaim-pack.lisp) is accounted by
; `fn-cverb-pack-octets', which `fn-cverb-capture-within-pack-octets' shows
; is at least the file the host seals.
;
; The compaction unit is gone (P5).  One pack file is one link of a chain
; (books/checkpoint-pack-chain.lisp): at most `*fn-cc-max-events*' events and
; `*fn-cc-max-octets*' of summary, or one record of the profile's R, a
; scheduling quantum and the open's largest single pack read.  A pack
; decision extends the selected chain one link at a time until it covers the
; history (host/native/checkpoint.lisp `fnn-pack-extend-chain').
(in-package "ACL2")
(include-book "checkpoint-compaction")
(include-book "checkpoint-pack-retire")
(include-book "byte-store-compaction-correspondence")
(include-book "store-observed")
(include-book "replay")
(include-book "checkpoint-pack-chain")

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

(defun fn-cverb-disk-admitsp (disk-free octets)
  "The disk the host observed has room for OCTETS more: DISK-FREE, the free
octets the host reported, is a natural at least OCTETS."
  (declare (xargs :guard t))
  (and (natp disk-free) (natp octets) (<= octets disk-free)))

;; The octets the next link of the chain is accounted at: the link header
;; bound, the summary size of the records one quantum takes above the chain's
;; boundary LOWER (`fn-ccc-fit', the capture's own choice), and the frame
;; trailer the host's seal appends.  One link is what one pack step writes
;; (host/native/checkpoint.lisp `fnn-pack-extend-chain' asks this decision
;; again before every link), so the disk is asked for one link at a time.
(defun fn-cverb-link-octets (records lower)
  (declare (xargs :guard t :verify-guards nil))
  (let ((rest (nthcdr (nfix lower) records)))
    (+ *fn-ccc-link-header-octets*
       (fn-cc-event-octets-size (take (fn-ccc-fit rest) rest))
       *fn-frame-trailer-octets*)))

(defun fn-cverb-older-count (generations selected)
  (declare (xargs :guard t))
  (let ((plan (fn-cprt-retire-plan generations selected)))
    (if (equal plan :invalid) 0 (len plan))))

; PROFILE: the decoded persisted profile.  RECORDS: the committed history the
; open reconstructed (pack plus suffix).  LOWER: the selected pack's coverage
; boundary (0 without one).  NAMES: the sorted transaction namespace.
; GENERATIONS and SELECTED: the pack namespace plan and the selected
; generation (nil without one).  DISK-FREE: the free octets of the store's
; filesystem, as the host observed them (nil when it could not).
(defun fn-cverb-decide (profile records lower names generations selected disk-free)
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
          ((not (fn-cverb-disk-admitsp disk-free (fn-cverb-link-octets records lower)))
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

;; A link's encoding is its events' encoding and a header of nine items, the
;; predecessor digest among them, bounded at a frame trailer's 32 octets (a
;; longer one encodes to nothing).
(local
 (defthm fn-cverb-bounded-bytes-length
   (implies (fn-cbor-valuep-bounded (cons :bytes x) max)
            (<= (len x) max))
   :rule-classes :forward-chaining
   :hints (("Goal" :do-not-induct t :in-theory (enable fn-cbor-valuep-bounded)))))

(local
 (defthm fn-cverb-digest-encoding-length
   (<= (len (fn-cbor-encode-bounded (cons :bytes x) *fn-frame-trailer-octets*))
       (+ 5 *fn-frame-trailer-octets*))
   :rule-classes :linear
   :hints (("Goal" :do-not-induct t
            :cases ((fn-cbor-valuep-bounded (cons :bytes x) *fn-frame-trailer-octets*))
            :in-theory (enable fn-cbor-encode-bounded fn-cbor-encode-argument
                               fn-cbor-u16-bytes fn-cbor-u32-bytes)))))

(local
 (defthm fn-cverb-link-encoding-length
   (<= (len (fn-ccc-encode-link l))
       (+ 96 (len (fn-cc-encode-events (fn-ccc-events l)))))
   :rule-classes :linear
   :hints (("Goal" :in-theory (e/d (fn-ccc-encode-link)
                                   (fn-ccc-linkp fn-cc-encode-events
                                    fn-cbor-encode-bounded))))))

(local
 (defthm fn-cverb-captured-link-events
   (implies (and (natp lower)
                 (equal (car (fn-ccc-capture-link records lower lf gen digest)) :ok))
            (equal (fn-ccc-events (cadr (fn-ccc-capture-link records lower lf gen digest)))
                   (take (fn-ccc-fit (nthcdr lower records)) (nthcdr lower records))))
   :hints (("Goal" :in-theory (e/d (fn-ccc-capture-link fn-ccc-make fn-ccc-events
                                    fn-cc-nth)
                                   (fn-ccc-fit fn-ccc-linkp fn-ccc-event-txid))))))

(local
 (defthm fn-cverb-atom-is-no-link
   (implies (atom l) (not (fn-ccc-linkp l)))
   :hints (("Goal" :in-theory (enable fn-ccc-linkp)))))

(local
 (defthm fn-cverb-uncaptured-link-encodes-nothing
   (implies (not (equal (car (fn-ccc-capture-link records lower lf gen digest)) :ok))
            (equal (fn-ccc-encode-link (cadr (fn-ccc-capture-link records lower lf gen digest)))
                   nil))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-ccc-capture-link fn-ccc-encode-link)
                            (fn-ccc-linkp fn-ccc-fit fn-ccc-event-txid fn-ccc-make
                             fn-cc-octet-event-listp))))))

(local
 (defthm fn-cverb-link-file-within-link-octets
   (implies (natp lower)
            (<= (+ (len (fn-ccc-encode-link
                         (cadr (fn-ccc-capture-link records lower lf gen digest))))
                   *fn-frame-trailer-octets*)
                (fn-cverb-link-octets records lower)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :cases ((equal (car (fn-ccc-capture-link records lower lf gen digest)) :ok))
            :use ((:instance fn-cverb-link-encoding-length
                             (l (cadr (fn-ccc-capture-link records lower lf gen digest))))
                  (:instance fn-cverb-encode-events-length
                             (events (take (fn-ccc-fit (nthcdr lower records))
                                           (nthcdr lower records)))))
            :in-theory (e/d (fn-cverb-link-octets)
                            (fn-ccc-capture-link fn-ccc-encode-link fn-ccc-linkp
                             fn-ccc-pred-digest fn-ccc-events
                             fn-cc-encode-events fn-ccc-fit
                             fn-cc-event-octets-size take nthcdr))))))

;  KEYSTONE (temporary space against the disk, PKT-169, over the link).  When
; the verb decides to pack, the link the host then captures above the
; chain's boundary LOWER and seals (`fn-ccc-capture-link' through
; host/checkpoint-host.lisp `fn-store-checkpoint-chain-capture', called by
; host/native/checkpoint.lisp `fnn-pack-publish-generation'; its payload
; plus the frame trailer) fits the free octets the host reported for the
; store's filesystem.  For every lower frontier, predecessor generation and
; predecessor digest.
(defthm fn-cverb-pack-fits-the-disk
  (implies (equal (fn-cverb-decide profile records lower names
                                   generations selected disk-free)
                  (list :compact *fn-cverb-pack-steps*))
           (<= (+ (len (fn-ccc-encode-link
                        (cadr (fn-ccc-capture-link records lower lf gen digest))))
                  *fn-frame-trailer-octets*)
               disk-free))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cverb-link-file-within-link-octets))
           :in-theory (e/d (fn-cverb-decide fn-cverb-disk-admitsp)
                           (fn-ccc-capture-link fn-ccc-encode-link
                            fn-cverb-link-octets
                            fn-bs-pack-reclaim-plan
                            fn-cverb-older-count
                            fn-bs-profile-admittedp)))))

; The refusal is exactly the disk's: a history the verb would otherwise pack
; is refused :temporary-space when, and only when, the next link's
; accounted octets exceed the free octets observed.  No size of the history
; refuses it (P5, D27).  By definition of the decision.
(defthm fn-cverb-temporary-space-is-the-disk-by-definition
  (implies (and (fn-bs-profile-admittedp profile)
                (natp lower) (<= lower (len records))
                (not (equal (fn-bs-pack-reclaim-plan
                             names (fn-bs-profile-max-transactions profile) lower)
                            :invalid))
                (not (equal lower (len records))))
           (equal (fn-cverb-decide profile records lower names
                                   generations selected disk-free)
                  (if (fn-cverb-disk-admitsp disk-free (fn-cverb-link-octets records lower))
                      (list :compact *fn-cverb-pack-steps*)
                    (list :refused :temporary-space))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cverb-decide)
                                  (fn-cc-event-octets-size fn-cverb-link-octets
                                   fn-cverb-disk-admitsp
                                   fn-bs-pack-reclaim-plan fn-cverb-older-count
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

;; KEYSTONE (a pack decision is never refused by the capture).  When the
;; verb decides to pack, the host extends the selected chain
;; (host/native/checkpoint.lisp `fnn-pack-extend-chain'); the capture of the
;; next link (`fn-ccc-capture-link') succeeds on a history whose records above
;; the chain are valid from the chain's frontier, the open's own check.  There
;; is no compaction unit to refuse any more: a link takes one quantum and at
;; least one record (books/checkpoint-pack-chain, P5).
(defthm fn-cverb-pack-decision-capture-succeeds
  (implies (and (equal (fn-cverb-decide profile records lower names
                                        generations selected disk-free)
                       (list :compact *fn-cverb-pack-steps*))
                (fn-record-uint32p (len records))
                (fn-record-uint32p lf) (fn-record-uint32p frontier)
                (fn-cc-octet-event-listp (nthcdr lower records) lower lf frontier)
                (fn-record-uint32p gen) (fn-cbor-octet-listp digest))
           (equal (car (fn-ccc-capture-link records lower lf gen digest)) :ok))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-ccc-capture-link-succeeds))
           :in-theory (e/d (fn-cverb-decide)
                           (fn-ccc-capture-link-succeeds
                            fn-cc-octet-event-listp
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
                                        generations selected disk-free)
                       (list :compact *fn-cverb-pack-steps*))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cverb-decide)
                                  (fn-bs-pack-reclaim-plan fn-cverb-older-count
                                   fn-bs-profile-admittedp)))))

; The pack's event limit is never the refusal under a preset: the open's
; namespace gate admits at most the profile's max_transactions, and each
; preset's (format 8 or its format-7 tuple) is at most the pack's 4096
; events.  Under an operator's profile with max_transactions above 4096 (the
; D27 default is 2^32-1) the history takes more than one link of the chain
; (P5); the test book carries a 4097-event witness.
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

(in-theory (disable fn-cverb-decide fn-cverb-pack-octets fn-cverb-link-octets
                    fn-cverb-disk-admitsp
                    fn-cverb-older-count fn-cverb-octet-sum))
