; The Store's carried record tally (PRF-139 part 1).
;
; The owner's publication verdict needs the committed record count and the
; committed record octets (books/store-budget.lisp fn-sbud-used,
; fn-sbud-bytes-used: `len' of the history and the sum of its encodings).
; The served path reads them from the tally the Store carries
; (books/store-node.lisp fn-sn-record-tally) instead: extended by the one
; record the file kernel appends (fn-sn-io, :record-directory :ok), rebuilt
; from the records where the Store is built from them (fn-sn-update-replayed,
; which every open and recovery goes through), carried by every other
; transition.  The fold stays the specification: fn-srt-relatedp says the
; tally is the fold of the records, it is established at fn-sn-initial and
; by fn-sn-recover (and by the observed and checkpoint opens, whose Store
; comes out of fn-sn-update-replayed), and it is preserved by every Store
; transition this book names, as the derived event index's agreement is
; (books/consumer-event-index-store-invariants.lisp).  No served command
; evaluates it.
(in-package "ACL2")
(include-book "store-budget")
(include-book "consumer-event-index-store-invariants")

(defun fn-srt-relatedp (s)
  (declare (xargs :guard t :verify-guards nil))
  (if (member-eq (fn-sf-phase (fn-sn-files s)) '(:replaying :fault))
      t
    (equal (fn-sn-record-tally s)
           (fn-sn-tally-of (fn-sf-records (fn-sn-files s))))))

; -----------------------------------------------------------------------------
; The fold

(local
 (defthm fn-srt-tally-of-aux-append
   (equal (fn-sn-tally-of-aux (append records (list record)) tally)
          (fn-sn-tally-extend (fn-sn-tally-of-aux records tally) record))
   :hints (("Goal" :induct (fn-sn-tally-of-aux records tally)
            :in-theory (enable fn-sn-tally-of-aux)))))

; One more record is one extension of the history's tally.
(defthm fn-srt-tally-of-append
  (equal (fn-sn-tally-of (append records (list record)))
         (fn-sn-tally-extend (fn-sn-tally-of records) record))
  :hints (("Goal" :in-theory (enable fn-sn-tally-of))))

(local
 (defthm fn-srt-tally-of-aux-figures
   (and (equal (fn-sn-tally-count (fn-sn-tally-of-aux records tally))
               (+ (fn-sn-tally-count tally) (len records)))
        (equal (fn-sn-tally-octets (fn-sn-tally-of-aux records tally))
               (+ (fn-sn-tally-octets tally) (fn-sbud-record-octets records))))
   :hints (("Goal" :induct (fn-sn-tally-of-aux records tally)
            :in-theory (e/d (fn-sbud-record-octets fn-sn-tally-of-aux
                             fn-sn-tally-extend)
                            (fn-store-event-encode))))))

; KEYSTONE (the tally is the fold).  The carried figures of a history are
; its record count and the sum of its records' encodings: the logical
; count and sum the budget is specified over.
(defthm fn-srt-tally-is-the-fold
  (and (equal (fn-sn-tally-count (fn-sn-tally-of records)) (len records))
       (equal (fn-sn-tally-octets (fn-sn-tally-of records))
              (fn-sbud-record-octets records)))
  :hints (("Goal" :in-theory (enable fn-sn-tally-of))))

; -----------------------------------------------------------------------------
; Established

(defthm fn-srt-initial-related
  (fn-srt-relatedp (fn-sn-initial groups capacity))
  :hints (("Goal" :in-theory (enable fn-srt-relatedp fn-sn-initial
                                     fn-sn-make-v2 fn-sn-files fn-sn-record-tally
                                     fn-sf-phase fn-sf-records fn-store-event-nth))))

; Recovery rebuilds the tally from the records it replayed
; (fn-sn-update-replayed), as it rebuilds the event index; the observed and
; checkpoint opens build their Store through the same constructor.
(defthm fn-srt-recover-preserves-related
  (implies (and (fn-sn-statep s) (fn-srt-relatedp s))
           (fn-srt-relatedp (fn-sn-recover s)))
  :hints (("Goal" :in-theory
           (e/d (fn-srt-relatedp fn-sn-recover)
                (fn-sn-statep fn-sf-statep fn-sf-recover
                 fn-sn-make-v6 fn-sn-make-v7 fn-sn-tally-of
                 fn-sn-update-replayed fn-sn-with-consumer fn-sn-with-topic
                 fn-sn-with-event-index fn-sn-update
                 fn-sf-replay-node fn-replay-identity
                 fn-cpe-projection-replay fn-th-prefix-project
                 fn-cei-build fn-cei-build-aux)))))

; -----------------------------------------------------------------------------
; Preserved

; The file kernel appends only at the durable directory observation, and it
; appends the staged candidate: the tally extended by that candidate is the
; fold of the longer history.
(defthm fn-srt-record-directory-extension
  (implies (and (fn-sf-statep files)
                (equal (fn-sf-phase files) :record-attempted)
                (equal tally (fn-sn-tally-of (fn-sf-records files))))
           (equal (fn-sn-tally-extend tally (fn-sf-record-candidate files))
                  (fn-sn-tally-of (fn-sf-records (fn-sf-record-dir-result files :ok)))))
  :hints (("Goal" :in-theory (e/d (fn-sf-record-dir-result fn-sf-phase-shapep)
                                  (fn-sn-tally-extend fn-sn-tally-of fn-sf-statep
                                   fn-store-event-p)))))

(defthm fn-srt-io-preserves-related
  (implies (and (fn-sn-statep s) (fn-srt-relatedp s)
                (not (member-eq (fn-sf-phase (fn-sn-files s))
                                '(:replaying :fault))))
           (fn-srt-relatedp (fn-sn-io s operation result)))
  :hints (("Goal" :cases ((and (eq operation :record-directory)
                                (eq result :ok)
                                (eq (fn-sf-phase (fn-sn-files s))
                                    :record-attempted)))
           :use ((:instance fn-srt-record-directory-extension
                            (files (fn-sn-files s))
                            (tally (fn-sn-record-tally s))))
           :in-theory (e/d (fn-srt-relatedp fn-sn-io fn-sn-file-step
                            fn-sf-record-dir-result
                            fn-store-files-traces-vocabulary)
                           (fn-sn-update fn-sn-with-event-index fn-sn-with-record-tally
                            fn-sn-make-v6 fn-sn-make-v7
                            fn-sn-tally-extend fn-sn-tally-of
                            fn-srt-record-directory-extension
                            fn-sf-statep fn-store-event-p
                            fn-cei-put fn-sn-statep)))))

(defthm fn-srt-prepare-consumer-preserves-related
  (implies (and (fn-sn-statep s) (fn-srt-relatedp s)
                (not (member-eq (fn-sf-phase (fn-sn-files s))
                                '(:replaying :fault))))
           (fn-srt-relatedp (fn-sn-prepare-consumer s event)))
  :hints (("Goal" :in-theory
           (e/d (fn-srt-relatedp fn-sn-prepare-consumer
                  fn-store-files-traces-vocabulary)
                (fn-sn-update fn-sn-make-v6 fn-sn-make-v7 fn-sn-tally-of
                 fn-sn-statep fn-sf-statep fn-store-event-p)))))

(defthm fn-srt-prepare-retention-preserves-related
  (implies (and (fn-sn-statep s) (fn-srt-relatedp s)
                (not (member-eq (fn-sf-phase (fn-sn-files s))
                                '(:replaying :fault))))
           (fn-srt-relatedp (fn-sn-prepare-retention s event)))
  :hints (("Goal" :in-theory
           (e/d (fn-srt-relatedp fn-sn-prepare-retention
                  fn-store-files-traces-vocabulary)
                (fn-sn-update fn-sn-make-v6 fn-sn-make-v7 fn-sn-tally-of
                 fn-sn-statep fn-sf-statep fn-store-event-p)))))

(defthm fn-srt-prepare-identity-preserves-related
  (implies (and (fn-sn-statep s) (fn-srt-relatedp s)
                (not (member-eq (fn-sf-phase (fn-sn-files s))
                                '(:replaying :fault))))
           (fn-srt-relatedp (fn-sn-prepare-identity s event)))
  :hints (("Goal" :in-theory
           (e/d (fn-srt-relatedp fn-sn-prepare-identity
                  fn-store-files-traces-vocabulary)
                (fn-sn-update fn-sn-make-v6 fn-sn-make-v7 fn-sn-tally-of
                 fn-sn-statep fn-sf-statep fn-store-event-p
                 fn-stxe-p fn-stxk-p fn-stxa-p)))))

(defthm fn-srt-prepare-topic-preserves-related
  (implies (and (fn-sn-statep s) (fn-srt-relatedp s)
                (not (member-eq (fn-sf-phase (fn-sn-files s))
                                '(:replaying :fault))))
           (fn-srt-relatedp (fn-sn-prepare-topic s event)))
  :hints (("Goal" :in-theory
           (e/d (fn-srt-relatedp fn-sn-prepare-topic
                  fn-store-files-traces-vocabulary)
                (fn-sn-update fn-sn-make-v6 fn-sn-make-v7 fn-sn-tally-of
                 fn-sn-statep fn-sf-statep fn-store-event-p)))))

(defthm fn-srt-prepare-article-preserves-related
  (implies (and (fn-sn-statep s) (fn-srt-relatedp s)
                (not (member-eq (fn-sf-phase (fn-sn-files s))
                                '(:replaying :fault))))
           (fn-srt-relatedp (fn-sn-prepare s record)))
  :hints (("Goal" :in-theory
           (e/d (fn-srt-relatedp fn-sn-prepare
                  fn-store-files-traces-vocabulary)
                (fn-sn-update fn-sn-make-v6 fn-sn-make-v7 fn-sn-tally-of
                 fn-sn-statep fn-sf-statep fn-store-event-p)))))

(defthm fn-srt-finish-keeps-tally
  (equal (fn-sn-record-tally (fn-sn-finish s))
         (fn-sn-record-tally s))
  :hints (("Goal" :in-theory
           (e/d (fn-sn-finish fn-sn-finish-identity
                  fn-sn-advance-identity-next
                  fn-sn-with-topic fn-sn-with-consumer
                  fn-sn-update-indexed fn-sn-update-accepted)
                (fn-sn-make-v6 fn-sn-make-v7 fn-sn-record-tally
                 fn-sn-completion-enabledp fn-sn-completion-record
                 fn-store-retention-event-p fn-stxe-p fn-stxk-p
                 fn-stxa-p fn-cpe-eventp fn-th-topic-eventp
                 fn-replay-apply-record fn-replay-apply-retention-event
                 fn-replay-identity-step fn-sn-composite-delta
                 fn-sn-accepted-delta
                 fn-sf-core-completion fn-sf-emit-success)))))

(defthm fn-srt-finish-preserves-related
  (implies (and (fn-srt-relatedp s)
                (not (member-eq (fn-sf-phase (fn-sn-files s))
                                '(:replaying :fault))))
           (fn-srt-relatedp (fn-sn-finish s)))
  :hints (("Goal" :use (fn-srt-finish-keeps-tally
                         fn-ceis-finish-keeps-records)
           :in-theory (e/d (fn-srt-relatedp)
                           (fn-sn-finish fn-sn-tally-of
                            fn-srt-finish-keeps-tally
                            fn-ceis-finish-keeps-records)))))

(defthm fn-srt-crash-preserves-related
  (implies (fn-srt-relatedp s)
           (fn-srt-relatedp
            (fn-sn-crash s frontier-choice record-choice)))
  :hints (("Goal" :in-theory
           (e/d (fn-srt-relatedp fn-sn-crash fn-sf-crash)
                (fn-sn-statep fn-sf-statep fn-sn-tally-of
                 fn-sn-make-v6 fn-sn-make-v7)))))

; -----------------------------------------------------------------------------
; The served figures

; KEYSTONE (the carried figures are the kernel's).  The served owner's
; verdict (host/owner-host.lisp fn-owner-publication-verdict, through
; fn-owner-record-octets) reads fn-sbud-carried-used and
; fn-sbud-carried-bytes; on a Store whose tally is related (established at
; open, preserved by every transition above) and that is neither replaying
; nor faulted, they are the committed record count fn-sbud-used and the
; committed record octets fn-sbud-bytes-used: the same verdict, no walk.
(defthm fn-srt-carried-figures-are-the-kernel-figures
  (implies (and (fn-srt-relatedp s)
                (not (member-eq (fn-sf-phase (fn-sn-files s))
                                '(:replaying :fault))))
           (and (equal (fn-sbud-carried-used s) (fn-sbud-used s))
                (equal (fn-sbud-carried-bytes s) (fn-sbud-bytes-used s))))
  :hints (("Goal" :use ((:instance fn-srt-tally-is-the-fold
                                   (records (fn-sf-records (fn-sn-files s)))))
           :in-theory (e/d (fn-srt-relatedp fn-sbud-used fn-sbud-bytes-used)
                           (fn-srt-tally-is-the-fold fn-sn-tally-of
                            fn-sbud-record-octets)))))

(local
 (defthm fn-srt-record-octets-of-full-take
   (equal (fn-sbud-record-octets (take (len records) records))
          (fn-sbud-record-octets records))
   :hints (("Goal" :induct (len records)
            :in-theory (e/d (fn-sbud-record-octets) (fn-store-event-encode))))))
(local
 (defthm fn-srt-full-prefix-cache
   (fn-sbud-octets-cache-validp
    (cons (len records) (fn-sbud-record-octets records)) records)
   :hints (("Goal" :in-theory (e/d (fn-sbud-octets-cache-validp)
                                   (fn-sbud-record-octets))))))

; The status and health reports extend a (K . SUM) cache
; (fn-sbud-bytes-extend); the host hands them the carried figures, which are
; a valid cache for the carried records.
(defthm fn-srt-carried-figures-are-a-valid-octet-cache
  (implies (and (fn-srt-relatedp s)
                (not (member-eq (fn-sf-phase (fn-sn-files s))
                                '(:replaying :fault))))
           (fn-sbud-octets-cache-validp
            (cons (fn-sbud-carried-used s) (fn-sbud-carried-bytes s))
            (fn-sf-records (fn-sn-files s))))
  :hints (("Goal" :use ((:instance fn-srt-carried-figures-are-the-kernel-figures)
                        (:instance fn-srt-full-prefix-cache
                                   (records (fn-sf-records (fn-sn-files s)))))
           :in-theory (e/d (fn-sbud-used fn-sbud-bytes-used)
                           (fn-srt-carried-figures-are-the-kernel-figures
                            fn-srt-full-prefix-cache fn-sbud-carried-used
                            fn-sbud-carried-bytes fn-srt-relatedp)))))

(in-theory (disable fn-srt-relatedp fn-sbud-carried-used fn-sbud-carried-bytes))
