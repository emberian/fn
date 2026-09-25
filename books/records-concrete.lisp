; fn: the record recognizer over its strings, without the octet lists.
;
; fn-record-p (books/records-shape.lisp, fn-defrecord) tests a record's four
; text fields through the octet-list domain: fn-record-octet-stringp and
; fn-record-ascii-stringp convert the string to its list of char-codes
; (fn-record-string-octets: a coerce and one cons per character) and walk
; the list, and fn-record-msgidp and fn-record-metadata-bytes-p convert it a
; second time for the length bound.  Eight conversions per record, and the
; POST path recognises the same record on four paths (the prepare's
; candidate test, the commit's seek, its completion gate and its finish):
; 20 percent of POST CPU at N = 120, of which the conversions are the
; larger part (planning/evidence/advance-projection-2026-09-24.md,
; planning/design-2026-09-25-representation.md).
;
; The logical model does not move.  fn-record-p stays what it is, over
; octet lists, and every theorem stated over it stays true.  This book adds
; the concrete recognizer fn-rcon-record-p, which reads the strings in
; place: an ACL2 character has a code in 0..255, so the octet-domain test is
; stringp; the length bound is `length'; the ASCII test walks the string by
; index with `char'.  Nothing is allocated.  The correspondence theorem
; fn-rcon-record-p-is-record-p says the two recognizers are the same
; function, on every input, with no hypothesis.  The twins below it
; (fn-rcon-store-event-*, fn-rcon-sf-record-pair, fn-rcon-sn-record-bindsp,
; fn-rcon-cpe-projection-step, fn-rcon-th-prefix-step) are their references
; with fn-record-p replaced, and each equals its reference with no
; hypothesis.  books/owner-commit-carried.lisp (the commit the host calls,
; host/owner-host.lisp fn-owner-finish-submission) and
; books/owner-prepare-carried.lisp (the prepare) call the twins.
;
; The second section (lane/rep-records-2) carries the same replacement to
; the list dispatchers the host still reached at write: the encoder of the
; staged record (fn-rcon-store-event-encode), the staged record's sequence
; (fn-rcon-sbud-pending-sequence), and the transaction observation
; (fn-rcon-sn-io, whose :record-directory arm pairs the record's sequence
; and transaction id; books/records-concrete-owner.lisp lifts it to the
; owner event the host issues).  Each equals its reference with no
; hypothesis and is guard-verified; host/owner-host.lisp, host/store-node-host.lisp
; and host/store-host.lisp call the twins.
;
; What stays on the octet lists: the payload (fn-record-payloadp walks it,
; O(L)) and the group names (fn-record-group-namep converts each name for
; the RFC 5536 grammar).  Those are the next boundaries in the design.  The
; codec behind the seam, fn-record-encode-impl (books/records.lisp, attached
; in books/records-attach.lisp), still recognises its argument with
; fn-record-p; replacing that is an attachment change with the image-wide
; closure of records-attach, not a twin here.

(in-package "ACL2")
(include-book "store-node")
(include-book "consumer-store-projection")
(include-book "topic-history-prefix")

; -----------------------------------------------------------------------------
; The string domain, read in place.

; Every character of TEXT at index I or beyond has a code at most 127.
(defun fn-rcon-ascii-from (text i)
  (declare (xargs :guard (and (stringp text) (natp i) (<= i (length text)))
                  :measure (nfix (- (length text) (nfix i)))))
  (if (and (stringp text) (natp i) (< i (length text)))
      (and (<= (char-code (char text i)) 127)
           (fn-rcon-ascii-from text (1+ i)))
    t))

(defun fn-rcon-msgidp (text)
  (declare (xargs :guard t))
  (and (stringp text)
       (< 0 (length text))
       (<= (length text) *fn-record-max-msgid*)
       (fn-rcon-ascii-from text 0)))

(defun fn-rcon-metadata-bytes-p (text)
  (declare (xargs :guard t))
  (and (stringp text)
       (< 0 (length text))
       (<= (length text) *fn-record-max-metadata*)))

; fn-record-p's conjuncts in its order, with the three string tests
; replaced.  The payload and the group names are tested as before.
(defun fn-rcon-record-p (x)
  (declare (xargs :guard t))
  (and (fn-record-shapep x)
       (fn-record-uint32p (fn-record-sequence x))
       (fn-record-uint32p (fn-record-txid x))
       (fn-record-uint32p (fn-record-generation x))
       (fn-rcon-msgidp (fn-record-msgid x))
       (fn-record-payloadp (fn-record-payload x))
       (fn-record-groups-validp (fn-record-groups x))
       (fn-rcon-metadata-bytes-p (fn-record-obligation-id x))
       (fn-rcon-metadata-bytes-p (fn-record-content-subject x))
       (fn-rcon-metadata-bytes-p (fn-record-release-evidence x))
       (fn-record-uint32p (fn-record-charge x))
       (fn-record-stampp (fn-record-stamp x))))

; -----------------------------------------------------------------------------
; The correspondence, field by field.

(local (defthm fn-rcon-string-octets-aux-is-octets
  (fn-cbor-octet-listp (fn-record-string-octets-aux chars))))

(local (defthm fn-rcon-string-octets-aux-len
  (equal (len (fn-record-string-octets-aux chars)) (len chars))))

(local (defthm fn-rcon-string-octets-aux-consp
  (equal (consp (fn-record-string-octets-aux chars)) (consp chars))))

(local (defthm fn-rcon-positive-len-is-consp
  (equal (< 0 (len x)) (consp x))))

; KEYSTONE (the octet domain).  A string's characters are octets.
(defthm fn-rcon-octet-stringp-is-stringp
  (equal (fn-record-octet-stringp text) (stringp text))
  :hints (("Goal" :in-theory (enable fn-record-octet-stringp))))

(defthm fn-rcon-metadata-bytes-p-is-metadata-bytes-p
  (equal (fn-rcon-metadata-bytes-p text) (fn-record-metadata-bytes-p text))
  :hints (("Goal" :in-theory (enable fn-record-metadata-bytes-p
                                     fn-record-nonempty-at-mostp))))

(local (include-book "arithmetic/top" :dir :system))

(local (defthm fn-rcon-shift-less
  (implies (and (integerp i) (integerp n))
           (equal (< (+ -1 i) n) (< i (+ 1 n))))
  :hints (("Goal" :cases ((< i (+ 1 n)))))))

(local (defthm fn-rcon-consp-of-nthcdr
  (implies (natp i)
           (equal (consp (nthcdr i l)) (< i (len l))))
  :hints (("Goal" :induct (nthcdr i l) :in-theory (enable nthcdr len)))))

(local (defthm fn-rcon-nthcdr-past-true-list
  (implies (and (true-listp l) (natp i) (<= (len l) i))
           (equal (nthcdr i l) nil))
  :hints (("Goal" :induct (nthcdr i l) :in-theory (enable nthcdr len)))))

(local (defthm fn-rcon-car-of-nthcdr
  (equal (car (nthcdr i l)) (nth i l))
  :hints (("Goal" :induct (nthcdr i l) :in-theory (enable nthcdr nth)))))

(local (defthm fn-rcon-cdr-of-nthcdr
  (equal (cdr (nthcdr i l)) (nthcdr i (cdr l)))
  :hints (("Goal" :induct (nthcdr i l) :in-theory (enable nthcdr)))))

(local (defthm fn-rcon-nthcdr-of-1+
  (implies (natp i)
           (equal (nthcdr (+ 1 i) l) (nthcdr i (cdr l))))
  :hints (("Goal" :induct (nthcdr i l) :in-theory (enable nthcdr)))))

(local (defthm fn-rcon-character-listp-true-listp
  (implies (character-listp l) (true-listp l))))

(local (defthm fn-rcon-coerce-true-listp
  (true-listp (coerce text 'list))))

; The index walk is the list walk from index I: char I is nth I of the
; character list, and the rest of the walk is the rest of the list.
(local (defthm fn-rcon-ascii-from-is-ascii-octet-listp-of-nthcdr
  (implies (and (stringp text) (natp i))
           (equal (fn-rcon-ascii-from text i)
                  (fn-record-ascii-octet-listp
                   (fn-record-string-octets-aux (nthcdr i (coerce text 'list))))))
  :hints (("Goal" :induct (fn-rcon-ascii-from text i)
           :in-theory (e/d (fn-rcon-ascii-from) (nth fn-rcon-shift-less))
           :expand ((fn-record-string-octets-aux (nthcdr i (coerce text 'list)))
                    (fn-record-ascii-octet-listp
                     (fn-record-string-octets-aux
                      (nthcdr i (coerce text 'list)))))))))

(defthm fn-rcon-msgidp-is-msgidp
  (equal (fn-rcon-msgidp text) (fn-record-msgidp text))
  :hints (("Goal" :in-theory (enable fn-record-msgidp fn-record-ascii-stringp
                                     fn-record-nonempty-at-mostp))))

; KEYSTONE (the recognizer).  The concrete recognizer is fn-record-p, on
; every input.  Both are guard-verified with guard t, so the host's compiled
; code computes this one.
(defthm fn-rcon-record-p-is-record-p
  (equal (fn-rcon-record-p x) (fn-record-p x))
  :hints (("Goal" :in-theory (e/d (fn-record-p) (fn-record-shapep)))))

(in-theory (disable fn-rcon-ascii-from fn-rcon-msgidp fn-rcon-metadata-bytes-p
                    fn-rcon-record-p))

; -----------------------------------------------------------------------------
; The twins: each reference with fn-record-p replaced, equal to it with no
; hypothesis.  The dispatchers (books/store-events.lisp), the record pair
; (books/store-files.lisp), the binding test (books/store-node.lisp), and
; the two projection steps the completion gate runs
; (books/consumer-store-projection.lisp, books/topic-history-prefix.lisp).

(defun fn-rcon-store-event-p (x)
  (declare (xargs :guard t))
  (or (fn-rcon-record-p x) (fn-store-retention-event-p x)
      (fn-stxe-p x) (fn-stxk-p x) (fn-stxa-p x) (fn-cpe-eventp x)
      (fn-th-topic-eventp x)))

(defthm fn-rcon-store-event-p-is-store-event-p
  (equal (fn-rcon-store-event-p x) (fn-store-event-p x))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-rcon-store-event-p fn-store-event-p
                                fn-rcon-record-p-is-record-p)
                              (theory 'minimal-theory)))))

(defun fn-rcon-store-event-sequence (x)
  (declare (xargs :guard t))
  (cond ((fn-rcon-record-p x) (fn-record-sequence x))
        ((fn-store-retention-event-p x) (fn-store-event-nth 2 x))
        ((fn-stxe-p x) (fn-stxe-sequence x))
        ((fn-stxk-p x) (fn-stxk-sequence x))
        ((fn-stxa-p x) (fn-stxa-sequence x))
        ((fn-cpe-eventp x) (fn-cpe-sequence x))
        ((fn-th-topic-eventp x) (fn-th-at 1 x))
        (t nil)))

(defthm fn-rcon-store-event-sequence-is-store-event-sequence
  (equal (fn-rcon-store-event-sequence x) (fn-store-event-sequence x))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-rcon-store-event-sequence fn-store-event-sequence
                                fn-rcon-record-p-is-record-p)
                              (theory 'minimal-theory)))))

(defun fn-rcon-store-event-txid (x)
  (declare (xargs :guard t))
  (cond ((fn-rcon-record-p x) (fn-record-txid x))
        ((fn-store-retention-event-p x) (fn-store-event-nth 3 x))
        ((fn-stxe-p x) (fn-stxe-txid x))
        ((fn-stxk-p x) (fn-stxk-txid x))
        ((fn-stxa-p x) (fn-stxa-txid x))
        ((fn-cpe-eventp x) (fn-cpe-txid x))
        ((fn-th-topic-eventp x) (fn-th-at 2 x))
        (t nil)))

(defthm fn-rcon-store-event-txid-is-store-event-txid
  (equal (fn-rcon-store-event-txid x) (fn-store-event-txid x))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-rcon-store-event-txid fn-store-event-txid
                                fn-rcon-record-p-is-record-p)
                              (theory 'minimal-theory)))))

(defun fn-rcon-store-event-generation (x)
  (declare (xargs :guard t))
  (cond ((fn-rcon-record-p x) (fn-record-generation x))
        ((fn-store-retention-event-p x) (fn-store-event-nth 4 x))
        ((fn-stxe-p x) (fn-stxe-generation x))
        ((fn-stxk-p x) (fn-stxk-generation x))
        ((fn-stxa-p x) (fn-stxa-generation x))
        ((fn-cpe-eventp x) (fn-cpe-generation x))
        ((fn-th-topic-eventp x) (fn-th-at 3 x))
        (t nil)))

(defthm fn-rcon-store-event-generation-is-store-event-generation
  (equal (fn-rcon-store-event-generation x) (fn-store-event-generation x))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-rcon-store-event-generation fn-store-event-generation
                                fn-rcon-record-p-is-record-p)
                              (theory 'minimal-theory)))))

(in-theory (disable fn-rcon-store-event-p fn-rcon-store-event-sequence
                    fn-rcon-store-event-txid fn-rcon-store-event-generation))

(defun fn-rcon-sf-record-pair (record)
  (declare (xargs :guard t))
  (cons (fn-rcon-store-event-sequence record) (fn-rcon-store-event-txid record)))

(defthm fn-rcon-sf-record-pair-is-sf-record-pair
  (equal (fn-rcon-sf-record-pair record) (fn-sf-record-pair record))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-rcon-sf-record-pair fn-sf-record-pair
                                fn-rcon-store-event-sequence-is-store-event-sequence
                                fn-rcon-store-event-txid-is-store-event-txid)
                              (theory 'minimal-theory)))))

(in-theory (disable fn-rcon-sf-record-pair))

(defun fn-rcon-sn-record-bindsp (node record)
  (declare (xargs :guard (fn-node-statep node) :verify-guards nil))
  (and (fn-rcon-record-p record)
       (fn-node-pending-matchesp node (fn-record-txid record)
                                (fn-record-generation record))
       (equal record (fn-sn-pending-record node (fn-record-sequence record)))))

(defthm fn-rcon-sn-record-bindsp-is-sn-record-bindsp
  (equal (fn-rcon-sn-record-bindsp node record) (fn-sn-record-bindsp node record))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-rcon-sn-record-bindsp fn-sn-record-bindsp
                                fn-rcon-record-p-is-record-p)
                              (theory 'minimal-theory)))))

(verify-guards fn-rcon-sn-record-bindsp
  :hints (("Goal" :in-theory (enable fn-rcon-record-p-is-record-p
                                     fn-record-shape-vocabulary))))

(in-theory (disable fn-rcon-sn-record-bindsp))

(defun fn-rcon-cpe-projection-step (s event expected)
  (declare (xargs :guard t :verify-guards nil))
  (if (or (not (fn-rcon-store-event-p event))
          (not (fn-cp-uintp expected))
          (equal expected *fn-cbor-max-uint*)
          (not (equal (fn-rcon-store-event-sequence event) expected)))
      (list :refused :sequence)
    (if (not (fn-cpe-eventp event))
        (if (null s) (list :ok nil)
          (if (equal (fn-cp-nth 3 s) expected)
              (list :ok (fn-cpe-projection-advance s (1+ expected)))
            (list :refused :frontier)))
      (let* ((op (fn-cpe-operation event))
             (kind (fn-cp-nth 0 op)))
        (cond
         ((eq kind :bootstrap)
          (if (null s)
              (list :ok (fn-cp-initial (fn-cp-nth 1 op)
                                       (fn-cp-nth 2 op) (1+ expected)))
            (list :refused :duplicate-bootstrap)))
         ((null s) (list :refused :unbootstrapped))
         ((not (equal (fn-cp-nth 3 s) expected))
          (list :refused :frontier))
         ((eq kind :rollover)
          (if (equal (fn-cp-nth 1 op) (fn-cp-nth 2 s))
              (list :refused :same-incarnation)
            (list :ok
                  (fn-cp-state (fn-cp-nth 1 s) (fn-cp-nth 1 op)
                               (1+ expected) (fn-cp-nth 4 s) nil))))
         ((equal (fn-cpe-projection-decision s op) (list :write op))
          (list :ok (fn-cpe-projection-advance (fn-cp-apply s op)
                                                 (1+ expected))))
         (t (list :refused :operation)))))))

(defthm fn-rcon-cpe-projection-step-is-cpe-projection-step
  (equal (fn-rcon-cpe-projection-step s event expected)
         (fn-cpe-projection-step s event expected))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-rcon-cpe-projection-step fn-cpe-projection-step
                                fn-rcon-store-event-p-is-store-event-p
                                fn-rcon-store-event-sequence-is-store-event-sequence)
                              (theory 'minimal-theory)))))

(verify-guards fn-rcon-cpe-projection-step)

(in-theory (disable fn-rcon-cpe-projection-step))

(defun fn-rcon-th-prefix-step (projection event)
  (declare (xargs :guard t :verify-guards nil))
  (let ((status (fn-th-at 0 projection))
        (next (fn-th-at 1 projection))
        (snapshots (fn-th-at 2 projection))
        (accepted (fn-th-at 3 projection))
        (anchors (fn-th-at 4 projection))
        (installed (fn-th-at 5 projection)))
    (cond
     ((not (equal status :ok)) projection)
     ((or (not (fn-rcon-store-event-p event))
          (not (equal next (fn-rcon-store-event-sequence event))))
      (fn-th-prefix-state :fault next snapshots accepted anchors installed
                          :sequence))
     ((fn-stxk-p event)
      (fn-th-prefix-state :ok (1+ (nfix next)) (cons event snapshots)
                          accepted anchors installed nil))
     ((fn-stxa-p event)
      (fn-th-prefix-state :ok (1+ (nfix next)) snapshots
                          (cons event accepted) anchors installed nil))
     ((fn-th-local-admin-eventp event)
      (let ((updated (fn-th-local-admin-commit event installed)))
        (if (fn-stmt-okp updated)
            (fn-th-prefix-state :ok (1+ (nfix next)) snapshots accepted
                                anchors (fn-stmt-value updated) nil)
          (fn-th-prefix-state :fault next snapshots accepted anchors installed
                              :administrator-install))))
     ((fn-th-topic-eventp event)
      (let* ((ref (if (eq (fn-th-at 0 event) :topic-anchor)
                      (fn-th-at 5 event) (fn-th-at 7 event)))
             (source (fn-th-prefix-find-ref ref accepted))
             (snapshot (and source
                            (fn-stxk-find (fn-stxa-keyring-generation source)
                                          snapshots)))
             (updated
              (if (and source snapshot)
                  (if (eq (fn-th-at 0 event) :topic-anchor)
                      (if (fn-th-topic-v1-anchorp event)
                          (fn-th-commit-anchor event source snapshot
                                               (fn-th-at 5 installed) anchors)
                        (fn-th-commit-anchor-installed-v2
                         event source snapshot installed anchors))
                    (fn-th-commit-report event source snapshot anchors))
                (fn-stmt-error :missing-historical-authorship))))
        (if (fn-stmt-okp updated)
            (fn-th-prefix-state :ok (1+ (nfix next)) snapshots accepted
                                (fn-stmt-value updated) installed nil)
          (fn-th-prefix-state :fault next snapshots accepted anchors installed
                              (fn-stmt-value updated)))))
     (t (fn-th-prefix-state :ok (1+ (nfix next)) snapshots accepted anchors
                            installed nil)))))

(defthm fn-rcon-th-prefix-step-is-th-prefix-step
  (equal (fn-rcon-th-prefix-step projection event)
         (fn-th-prefix-step projection event))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-rcon-th-prefix-step fn-th-prefix-step
                                fn-rcon-store-event-p-is-store-event-p
                                fn-rcon-store-event-sequence-is-store-event-sequence)
                              (theory 'minimal-theory)))))

(verify-guards fn-rcon-th-prefix-step)

(in-theory (disable fn-rcon-th-prefix-step))

; -----------------------------------------------------------------------------
; The dispatchers at write (lane/rep-records-2).  The staged record is
; encoded and its sequence read by the host once per POST
; (host/owner-host.lisp fn-owner-pending-octets, fn-owner-pending-sequence);
; the transaction observation :record-directory pairs its sequence and
; transaction id (fn-sf-record-dir-result through fn-sn-io).  Each twin is
; its reference with the list dispatchers replaced by the twins above.

(include-book "store-budget-naming")

; The two references the encoder dispatches to that were admitted with
; :verify-guards nil; their guards (t) hold, so the twin's can be verified.
(verify-guards fn-store-event-kind-code)
(verify-guards fn-store-retention-event-encode)

(defun fn-rcon-store-event-encode (event)
  (declare (xargs :guard t))
  (cond ((fn-rcon-record-p event) (fn-record-encode event))
        ((fn-store-retention-event-p event)
         (fn-store-retention-event-encode event))
        ((fn-stxe-p event) (fn-stxe-encode event))
        ((fn-stxk-p event) (fn-stxk-encode event))
        ((fn-stxa-p event) (fn-stxa-encode event))
        ((fn-cpe-eventp event) (fn-cpe-encode event))
        ((fn-th-topic-eventp event) (fn-th-topic-event-encode event))
        (t nil)))
(defthm fn-rcon-store-event-encode-is-store-event-encode
  (equal (fn-rcon-store-event-encode event) (fn-store-event-encode event))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-rcon-store-event-encode fn-store-event-encode
                                fn-rcon-record-p-is-record-p)
                              (theory 'minimal-theory)))))
(defun fn-rcon-sbud-pending-sequence (s)
  (declare (xargs :guard t))
  (let ((record (fn-sf-record-candidate (fn-sn-files s))))
    (if (and record (natp (fn-rcon-store-event-sequence record)))
        (fn-rcon-store-event-sequence record)
      nil)))
(defthm fn-rcon-sbud-pending-sequence-is-sbud-pending-sequence
  (equal (fn-rcon-sbud-pending-sequence s) (fn-sbud-pending-sequence s))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-rcon-sbud-pending-sequence fn-sbud-pending-sequence
                                fn-rcon-store-event-sequence-is-store-event-sequence)
                              (theory 'minimal-theory)))))

(in-theory (disable fn-rcon-store-event-encode fn-rcon-sbud-pending-sequence))

(defun fn-rcon-sf-record-dir-result (s result)
  (declare (xargs :guard (fn-sf-statep s)))
  (if (and (mbe :logic (fn-sf-statep s) :exec t) (equal (fn-sf-phase s) :record-attempted))
      (cond
       ((equal result :ok)
        (let ((record (fn-sf-record-candidate s)))
          (fn-sf-make :completing (fn-sf-frontier s) nil
                      (append (fn-sf-records s) (list record)) nil
                      (fn-rcon-sf-record-pair record) (fn-sf-successes s)
                      (fn-sf-barriers s))))
       ((equal result :error)
        (fn-sf-make :fenced-record (fn-sf-frontier s) nil
                    (fn-sf-records s) (fn-sf-record-candidate s) nil
                    (fn-sf-successes s) (fn-sf-barriers s)))
       (t s))
    s))
(defthm fn-rcon-sf-record-dir-result-is-sf-record-dir-result
  (equal (fn-rcon-sf-record-dir-result s result) (fn-sf-record-dir-result s result))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-rcon-sf-record-dir-result fn-sf-record-dir-result
                                fn-rcon-sf-record-pair-is-sf-record-pair)
                              (theory 'minimal-theory)))))
(defun fn-rcon-sn-file-step (files operation result)
  (declare (xargs :guard (fn-sf-statep files)))
  (case operation
    (:start-frontier (fn-sf-start-frontier files))
    (:frontier-file (fn-sf-frontier-file-result files result))
    (:frontier-replace (fn-sf-frontier-replace-result files result))
    (:frontier-directory (fn-sf-frontier-dir-result files result))
    (:record-file (fn-sf-record-file-result files result))
    (:record-link (fn-sf-record-link-result files result))
    (:record-directory (fn-rcon-sf-record-dir-result files result))
    (:recovery-barrier (fn-sf-recovery-barrier files result))
    (otherwise files)))
(defthm fn-rcon-sn-file-step-is-sn-file-step
  (equal (fn-rcon-sn-file-step files operation result) (fn-sn-file-step files operation result))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-rcon-sn-file-step fn-sn-file-step
                                fn-rcon-sf-record-dir-result-is-sf-record-dir-result)
                              (theory 'minimal-theory)))))
(defun fn-rcon-sn-io (s operation result)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (if (mbe :logic (fn-sn-statep s) :exec t)
      (let* ((old-files (fn-sn-files s))
             (files (fn-rcon-sn-file-step old-files operation result))
             (updated (fn-sn-update s files (fn-sn-node s))))
        (if (and (eq operation :record-directory) (eq result :ok)
                 (eq (fn-sf-phase old-files) :record-attempted))
            (let* ((candidate (fn-sf-record-candidate old-files))
                   (sequence (fn-rcon-store-event-sequence candidate)))
              (fn-sn-with-event-index
               updated (fn-cei-put sequence candidate
                                   (fn-sn-event-index s))))
          updated))
    s))
(defthm fn-rcon-sn-io-is-sn-io
  (equal (fn-rcon-sn-io s operation result) (fn-sn-io s operation result))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-rcon-sn-io fn-sn-io
                                fn-rcon-sn-file-step-is-sn-file-step
                                fn-rcon-store-event-sequence-is-store-event-sequence)
                              (theory 'minimal-theory)))))
(verify-guards fn-rcon-sn-io
  :hints (("Goal" :use ((:guard-theorem fn-sn-io))
                  :in-theory (e/d (fn-rcon-sn-file-step-is-sn-file-step
                                   fn-rcon-store-event-sequence-is-store-event-sequence)
                                  (fn-sn-statep fn-sf-statep fn-node-statep)))))

(in-theory (disable fn-rcon-sf-record-dir-result fn-rcon-sn-file-step fn-rcon-sn-io))
