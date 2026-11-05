; Recovery's payload pass, the operations that read the shapes of layers C
; and D (b-durability.md S9a): one record of a chained commit's record
; stream, the claim of an article row's location, and one unit of a source
; manifest's entries. The recovery row's arms (recovery-machine.lisp) call
; them over the unit in its window; the claims are B's (fn2-recovery-claim),
; so adoption allocates each payload extent to its article with the
; identity it was written with, as the transaction's :batched did
; (fn2-upload-extent-commit), and a stored reference to it reads again.
(in-package "ACL2")
(include-book "assembly-callbacks-s")
(include-book "assembly-callbacks-d")
(fn2-book-layer :d)

; The record's fields are decoded at the recovery row's fields (unused once
; the chain is verified), room for the largest layout the stream holds.
(defconst *fn2-rp-room*
  (max (max *fn2-format-record-header-num-fields* *fn2-format-keyed-mutation-num-fields*)
       (max *fn2-format-article-acceptance-num-fields* *fn2-run-entry-rows*)))
(defmacro fn2-rp-roomp ()
  '(<= (+ *fn2-rec-field-base* *fn2-rp-room*) (fn2-fields-rows fn2-fields)))
(defconst *fn2-rp-article-kind* (+ *fn2-commit-txn-schema-record-kind-base* *fn2-txn-article-sid*))
(assert-event (equal *fn2-rp-article-kind* *record-kind-article*))

(defun fn2-rp-room-ok (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-fields (fn2-core-fields fn2-core))) (ok) (fn2-rp-roomp) ok))
(local (in-theory (disable fn2-fields-rows fn2-fieldsp fn2-fields-wfp fn2-poolp fn2-pool-wfp fn2-pool-rows)))

;; The record header at ROFF of the window SLOT GEN (owned by the recovery
;; row ID OGEN), the stream ending at REND: (mv code next kind event fn2-core).
(defun fn2-rp-header (roff rend slot gen id ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-fields (fn2-core-fields fn2-core)) (fn2-pool (fn2-core-pool fn2-core)))
    (code next kind version event fn2-fields)
    (if (and (fn2-rp-roomp) (unsigned-byte-p 32 roff) (unsigned-byte-p 32 rend)
             (unsigned-byte-p 32 id) (unsigned-byte-p 60 ogen))
        (mv-let (code next fn2-fields)
          (fn2-format-record-header-decode *fn2-rec-field-base* slot gen roff rend *fn2-recovery-machine-kind* id ogen
                                           fn2-fields fn2-pool)
          (mv code next
              (fn2-fields-value (+ *fn2-rec-field-base* *fn2-format-record-header-field-record-kind*) fn2-fields)
              (fn2-fields-value (+ *fn2-rec-field-base* *fn2-format-record-header-field-schema-version*) fn2-fields)
              (fn2-fields-value (+ *fn2-rec-field-base* *fn2-format-record-header-field-event*) fn2-fields)
              fn2-fields))
      (mv :bounds 0 0 0 0 fn2-fields))
    (mv (if (and (eq code :ok) (equal version 1)) :ok :invalid) (nfix next) (nfix kind) (nfix event) fn2-core)))
(fn2-core-preserves fn2-rp-header (roff rend slot gen id ogen fn2-core) :position 4 :rows nil)
(defthm fn2-rp-header-naturals
  (and (natp (mv-nth 1 (fn2-rp-header roff rend slot gen id ogen fn2-core)))
       (natp (mv-nth 2 (fn2-rp-header roff rend slot gen id ogen fn2-core)))
       (natp (mv-nth 3 (fn2-rp-header roff rend slot gen id ogen fn2-core))))
  :hints (("Goal" :in-theory (enable fn2-rp-header))))
(in-theory (disable fn2-rp-header))

;; The body of a record of KIND at OFF, in its kind's encoding (the kinds a
;; commit seals: a keyed mutation, an article acceptance, C's run schemas),
;; the stream ending at REND: (mv code next fn2-core).
(defun fn2-rp-body (kind off rend slot gen id ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)
                  :guard-hints (("Goal" :in-theory (disable fn2-format-article-acceptance-decode
                                                            fn2-format-keyed-mutation-decode fn2-run-layout-decode)))))
  (stobj-let ((fn2-fields (fn2-core-fields fn2-core)) (fn2-pool (fn2-core-pool fn2-core)))
    (code next fn2-fields)
    (let ((base *fn2-rec-field-base*) (okind *fn2-recovery-machine-kind*))
      (cond ((not (and (fn2-rp-roomp) (unsigned-byte-p 32 off) (unsigned-byte-p 32 rend)
                       (unsigned-byte-p 32 id) (unsigned-byte-p 60 ogen)))
             (mv :bounds 0 fn2-fields))
            ((equal kind *record-kind-keyed-mutation*)
             (fn2-format-keyed-mutation-decode base slot gen off rend okind id ogen fn2-fields fn2-pool))
            ((equal kind *record-kind-article-acceptance*)
             (fn2-format-article-acceptance-decode base slot gen off rend okind id ogen fn2-fields fn2-pool))
            ((and (natp kind) (<= *record-kind-identity-evidence* kind) (<= kind *record-kind-consumer-names*))
             (fn2-run-layout-decode (- kind *fn2-commit-txn-schema-record-kind-base*) 0 base slot gen off rend
                                    okind id ogen fn2-fields fn2-pool))
            (t (mv :kind 0 fn2-fields))))
    (mv (if (eq code :ok) :ok :invalid) (nfix next) fn2-core)))
(fn2-core-preserves fn2-rp-body (kind off rend slot gen id ogen fn2-core) :position 2 :rows nil
  :hints (("Goal" :in-theory (disable fn2-format-article-acceptance-decode fn2-format-keyed-mutation-decode
                                      fn2-run-layout-decode))))
(defthm fn2-rp-body-natp (natp (mv-nth 1 (fn2-rp-body kind off rend slot gen id ogen fn2-core)))
  :rule-classes :type-prescription :hints (("Goal" :in-theory (enable fn2-rp-body))))
(in-theory (disable fn2-rp-body))

;; The decoded article row's location: (mv unit epoch alloc lkind bytes).
(defun fn2-rp-location (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-fields (fn2-core-fields fn2-core)))
    (unit epoch alloc lkind bytes)
    (if (fn2-rp-roomp)
        (mv (nfix (fn2-fields-value (+ *fn2-rec-field-base* *fn2-article-entry-field-location-unit*) fn2-fields))
            (nfix (fn2-fields-value (+ *fn2-rec-field-base* *fn2-article-entry-field-location-epoch*) fn2-fields))
            (nfix (fn2-fields-value (+ *fn2-rec-field-base* *fn2-article-entry-field-location-allocation*) fn2-fields))
            (nfix (fn2-fields-value (+ *fn2-rec-field-base* *fn2-article-entry-field-location-kind*) fn2-fields))
            (nfix (fn2-fields-value (+ *fn2-rec-field-base* *fn2-article-entry-field-bytes*) fn2-fields)))
      (mv 0 0 0 0 0))
    (mv unit epoch alloc lkind bytes)))
(in-theory (disable fn2-rp-location))

;; One record of a chained commit's stream at ROFF; the window holds the
;; commit's records unit and the stream is [ROFF, REND), ended early by the
;; frame's zero padding (a record's schema version is never 0):
;; (mv code next unit epoch alloc bytes event fn2-core). :end; :other (a
;; record that names no payload); :raw or :manifest (an article row: its
;; location's unit and allocation handle, its stored length, its event);
;; :invalid (a record this recovery cannot decode, so the payload its stream
;; names cannot be known); :bounds when the fields have no room (a profile's).
(defun fn2-recovery-record-next (roff rend slot gen id ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* (((unless (fn2-rp-room-ok fn2-core)) (mv :bounds 0 0 0 0 0 0 fn2-core))
       ((unless (and (natp roff) (natp rend) (<= rend *fn2-commit-unit-bytes*))) (mv :invalid 0 0 0 0 0 0 fn2-core))
       ((when (<= rend roff)) (mv :end roff 0 0 0 0 0 fn2-core))
       ((mv vcode version)
        (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (vcode version)
          (fn2-rec-byte-at slot gen (if (< (+ 1 roff) rend) (+ 1 roff) roff) *fn2-recovery-machine-kind* id ogen fn2-pool)
          (mv vcode version)))
       ((unless (eq vcode :ok)) (mv :invalid 0 0 0 0 0 0 fn2-core))
       ((when (equal version 0)) (mv :end roff 0 0 0 0 0 fn2-core))
       ((mv code next kind event fn2-core) (fn2-rp-header roff rend slot gen id ogen fn2-core))
       ((unless (and (eq code :ok) (< roff next) (<= next rend))) (mv :invalid 0 0 0 0 0 0 fn2-core))
       ((mv code bnext fn2-core) (fn2-rp-body kind next rend slot gen id ogen fn2-core))
       ((unless (and (eq code :ok) (<= next bnext) (<= bnext rend))) (mv :invalid 0 0 0 0 0 0 fn2-core))
       ((unless (equal kind *fn2-rp-article-kind*)) (mv :other bnext 0 0 0 0 event fn2-core))
       ((mv unit epoch alloc lkind bytes) (fn2-rp-location fn2-core)))
    (cond ((equal lkind *fn2-txn-location-raw-source*) (mv :raw bnext unit epoch alloc bytes event fn2-core))
          ((equal lkind *fn2-txn-location-source-manifest*) (mv :manifest bnext unit epoch alloc bytes event fn2-core))
          (t (mv :invalid 0 0 0 0 0 0 fn2-core)))))
(fn2-core-preserves fn2-recovery-record-next (roff rend slot gen id ogen fn2-core) :position 7 :rows nil)
(defthm fn2-recovery-record-next-naturals
  (and (natp (mv-nth 1 (fn2-recovery-record-next roff rend slot gen id ogen fn2-core)))
       (natp (mv-nth 2 (fn2-recovery-record-next roff rend slot gen id ogen fn2-core)))
       (natp (mv-nth 3 (fn2-recovery-record-next roff rend slot gen id ogen fn2-core)))
       (natp (mv-nth 4 (fn2-recovery-record-next roff rend slot gen id ogen fn2-core)))
       (natp (mv-nth 5 (fn2-recovery-record-next roff rend slot gen id ogen fn2-core)))
       (natp (mv-nth 6 (fn2-recovery-record-next roff rend slot gen id ogen fn2-core))))
  :hints (("Goal" :in-theory (enable fn2-recovery-record-next))))
(in-theory (disable fn2-recovery-record-next))

;; An article row's location (its first UNIT, an extent's unit 0, and its
;; handle EPOCH ALLOC) claimed for the article (the transaction kind, its
;; EVENT), named by chained commit COMMIT: (mv code hi fn2-core).
(defun fn2-recovery-claim-article (unit epoch alloc event commit fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (not (and (natp unit) (equal (mod unit *fn2-commit-write-resources*) 0)))
      (mv :invalid 0 fn2-core)
    (fn2-recovery-claim (floor unit *fn2-commit-write-resources*) epoch alloc *fn2-txn-kind* event commit fn2-core)))
(fn2-core-preserves fn2-recovery-claim-article (unit epoch alloc event commit fn2-core) :position 2 :rows nil)
(defthm fn2-recovery-claim-article-hi-natp
  (natp (mv-nth 1 (fn2-recovery-claim-article unit epoch alloc event commit fn2-core)))
  :rule-classes :type-prescription :hints (("Goal" :in-theory (enable fn2-recovery-claim-article))))
(in-theory (disable fn2-recovery-claim-article))

;; The entries of a manifest unit (in the window) of TOTAL stored octets
;; from in-unit offset OFF (the packing rule keeps each entry in one unit):
;; the extent of each block at unit 0 of its extent is claimed for the
;; article (EVENT), named by COMMIT, FUEL entries at most. (mv code hi ep
;; fn2-core): :done after the last block's entry, :more when the unit ends
;; first; HI past the highest position claimed, EP the highest writer epoch.
(defun fn2-rp-entries (fuel off total event commit hi ep slot gen id ogen fn2-core)
  (declare (xargs :stobjs fn2-core :measure (nfix fuel) :guard (and (fn2-core-wfp fn2-core) (natp fuel))))
  (let ((at (fn2-am-entry-at off)) (hi (nfix hi)) (ep (nfix ep)))
    (cond ((<= *fn2-commit-unit-bytes* at) (mv :more hi ep fn2-core))
          ((zp fuel) (mv :invalid hi ep fn2-core))
          (t (b* (((mv code next lo len unit epoch alloc fn2-core)
                   (stobj-let ((fn2-fields (fn2-core-fields fn2-core)) (fn2-pool (fn2-core-pool fn2-core)))
                     (code next lo len unit epoch alloc fn2-fields)
                     (if (fn2-rp-roomp)
                         (fn2-am-get-entry *fn2-rec-field-base* slot gen at *fn2-commit-unit-bytes*
                                           *fn2-recovery-machine-kind* id ogen fn2-fields fn2-pool)
                       (mv :bounds 0 0 0 0 0 0 fn2-fields))
                     (mv code next lo len unit epoch alloc fn2-core)))
                  (total (nfix total)) (blk (floor lo *fn2-am-block-bytes*))
                  ((unless (and (eq code :ok) (< at next) (equal (mod lo *fn2-am-block-bytes*) 0) (< lo total)
                                (equal len (min *fn2-am-block-bytes* (- total lo)))))
                   (mv :invalid hi ep fn2-core))
                  ((mv code hi ep fn2-core)
                   (if (equal (mod unit *fn2-commit-write-resources*) 0)
                       (mv-let (code h fn2-core)
                         (fn2-recovery-claim (floor unit *fn2-commit-write-resources*) epoch alloc *fn2-txn-kind* event commit fn2-core)
                         (mv code (max hi (nfix h)) (max ep epoch) fn2-core))
                     (mv :ok hi ep fn2-core)))
                  ((unless (eq code :ok)) (mv (if (eq code :conflict) :conflict :invalid) hi ep fn2-core)))
               (if (equal (+ 1 blk) (fn2-am-blocks total)) (mv :done hi ep fn2-core)
                 (fn2-rp-entries (- fuel 1) next total event commit hi ep slot gen id ogen fn2-core)))))))
(fn2-core-preserves fn2-rp-entries (fuel off total event commit hi ep slot gen id ogen fn2-core) :position 3 :rows nil)
(defthm fn2-rp-entries-naturals
  (and (natp (mv-nth 1 (fn2-rp-entries fuel off total event commit hi ep slot gen id ogen fn2-core)))
       (natp (mv-nth 2 (fn2-rp-entries fuel off total event commit hi ep slot gen id ogen fn2-core))))
  :hints (("Goal" :in-theory (enable fn2-rp-entries))))
(in-theory (disable fn2-rp-entries))

;; Unit UNIT of the source manifest of TOTAL stored octets (in the window;
;; its header leads unit 0): its entries claimed (fn2-rp-entries).
(defun fn2-recovery-manifest-unit (unit total event commit slot gen id ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* (((unless (fn2-rp-room-ok fn2-core)) (mv :bounds 0 0 fn2-core))
       ((unless (and (fn2-am-manifestp total) (fn2-am-fits total) (natp unit))) (mv :invalid 0 0 fn2-core))
       ((mv code off)
        (if (zp unit)
            (stobj-let ((fn2-fields (fn2-core-fields fn2-core)) (fn2-pool (fn2-core-pool fn2-core)))
              (code next fn2-fields)
              (if (fn2-rp-roomp)
                  (fn2-am-get-header *fn2-rec-field-base* total slot gen 0 *fn2-commit-unit-bytes*
                                     *fn2-recovery-machine-kind* id ogen fn2-fields fn2-pool)
                (mv :bounds 0 fn2-fields))
              (mv code next))
          (mv :ok 0)))
       ((unless (eq code :ok)) (mv :invalid 0 0 fn2-core)))
    (fn2-rp-entries (+ 1 *fn2-am-entries-per-unit*) off total event commit 0 0 slot gen id ogen fn2-core)))
(fn2-core-preserves fn2-recovery-manifest-unit (unit total event commit slot gen id ogen fn2-core) :position 3 :rows nil)
(defthm fn2-recovery-manifest-unit-naturals
  (and (natp (mv-nth 1 (fn2-recovery-manifest-unit unit total event commit slot gen id ogen fn2-core)))
       (natp (mv-nth 2 (fn2-recovery-manifest-unit unit total event commit slot gen id ogen fn2-core))))
  :hints (("Goal" :in-theory (enable fn2-recovery-manifest-unit))))
(in-theory (disable fn2-recovery-manifest-unit))

(defcost fn2-am-units :doc "The units of the source manifest that names stored octets of a length.")
(defcost fn2-recovery-record-next :answers (:end :other :raw :manifest :invalid :bounds) :bytes 4096
  :tables (fn2-core-pool fn2-core-fields)
  :doc "Recovery's payload pass: one record of a chained commit's stream, and an article row's location.")
(defcost fn2-recovery-claim-article :answers (:ok :conflict :invalid :bounds) :tables (fn2-core-rec-cand)
  :doc "Recovery's payload pass: claim an article row's location extent for the article.")
(defcost fn2-recovery-manifest-unit :answers (:more :done :conflict :invalid :bounds) :bytes 4096
  :tables (fn2-core-pool fn2-core-fields fn2-core-rec-cand)
  :doc "Recovery's payload pass: claim the block extents one source manifest unit names.")
