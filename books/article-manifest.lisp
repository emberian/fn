; An article's source manifest (S-ARTICLE-LOCATION, b-durability.md B-S2):
; stored octets longer than one payload extent are named through one
; :source-manifest reference. The manifest is B's layouts, a
; fn2-format-source-manifest-header (the stored length, the block size, the
; source's content identity) and then one fn2-format-source-manifest-entry
; per block, a block being one storage unit of the stored octets: its logical
; offset and length, its BLOCK- reference (the unit it is stored in, the
; extent's writer epoch and allocation, :raw-source, the length, the block's
; own BLAKE3) and its chaining value in the stored octets' BLAKE3 tree (the
; subtree of its four chunks at chunk counter 4i; a final block shorter than a
; unit is no complete subtree, and its entry carries its own BLAKE3 there).
; Three consecutive blocks share one extent (an extent is
; *fn2-commit-write-resources* units), so block i is unit i mod 3 of its
; extent, and the entry of a block at unit 0 of its extent is the extent's
; only owner record the article keeps.
;
; The manifest is stored in an extent of its own, its units in order; an
; entry never straddles two units (one starts in the next unit when fewer
; than *fn2-am-entry-max* octets remain), so a reader holding one unit of it
; decodes the entry it needs. Its length is derived from the stored octets'
; (fn2-am-units), so the work a writer or reader spends per step is bounded
; by the window that holds the article, never by a fixed size.
(in-package "ACL2")
(include-book "upload-kind")
(fn2-book-layer :d)

; The block size, the layouts' largest sizes, the entries one unit holds and
; the largest stored length one manifest names (*fn2-am-stored-max*) are
; upload-kind.lisp's, where the profile's article bound is held within it.
(defconst *fn2-am-header-fields* *fn2-format-source-manifest-header-num-fields*)
(defconst *fn2-am-entry-fields* *fn2-format-source-manifest-entry-num-fields*)
(assert-event (equal *fn2-am-entries-per-unit* 31))
(assert-event (<= *fn2-am-entry-max* *fn2-commit-unit-bytes*))

;; The blocks of TOTAL stored octets, and the manifest's units.
(defun fn2-am-blocks (total)
  (declare (xargs :guard t))
  (ceiling (nfix total) *fn2-am-block-bytes*))
(defun fn2-am-units (total)
  (declare (xargs :guard t))
  (ceiling (fn2-am-blocks total) *fn2-am-entries-per-unit*))
(defthm fn2-am-units-natp (natp (fn2-am-units total)) :rule-classes :type-prescription)
;; Stored octets are named through a manifest when they exceed one extent;
;; the manifest is one extent at most (one reference per article, one level).
(defun fn2-am-manifestp (total)
  (declare (xargs :guard t))
  (< *fn2-commit-extent-bytes* (nfix total)))
(defun fn2-am-fits (total)
  (declare (xargs :guard t))
  (<= (fn2-am-units total) *fn2-commit-write-resources*))
(assert-event (and (fn2-am-fits *fn2-am-stored-max*) (not (fn2-am-fits (+ 1 *fn2-am-stored-max*)))))
;; Where the entry after manifest octet OFF starts (the packing rule).
(defun fn2-am-entry-at (off)
  (declare (xargs :guard t))
  (let* ((off (nfix off)) (room (- *fn2-commit-unit-bytes* (mod off *fn2-commit-unit-bytes*))))
    (if (< room *fn2-am-entry-max*) (+ off room) off)))
(defthm fn2-am-entry-at-natp (natp (fn2-am-entry-at off)) :rule-classes :type-prescription)
(defthm fn2-am-entry-at-bound (<= (nfix off) (fn2-am-entry-at off)) :rule-classes :linear)
(in-theory (disable fn2-am-blocks fn2-am-units fn2-am-manifestp fn2-am-fits fn2-am-entry-at))

(local (in-theory (disable fn2-fields-rows fn2-fieldsp fn2-fields-wfp fn2-poolp fn2-pool-wfp fn2-pool-rows)))
;; The header at OFF of SLOT GEN: TOTAL stored octets, the source identity at
;; DSLOT DGEN DOFF. Fields at BASE. (mv code end fn2-fields fn2-pool).
(defun fn2-am-put-header (base total dslot dgen doff slot gen off okind oslot ogen fn2-fields fn2-pool)
  (declare (xargs :stobjs (fn2-fields fn2-pool) :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
  (if (not (and (natp base) (<= (+ base *fn2-am-header-fields*) (fn2-fields-rows fn2-fields))
                (unsigned-byte-p 60 total) (unsigned-byte-p 32 dslot) (unsigned-byte-p 60 dgen)
                (unsigned-byte-p 32 doff)))
      (mv :bounds off fn2-fields fn2-pool)
    (let* ((r (+ base *fn2-format-source-manifest-header-field-source-identity*))
           (fn2-fields (fn2-fields-set-value (+ base *fn2-format-source-manifest-header-field-source-length*) total fn2-fields))
           (fn2-fields (fn2-fields-set-value (+ base *fn2-format-source-manifest-header-field-block-size*) *fn2-am-block-bytes* fn2-fields))
           (fn2-fields (fn2-fields-set-value r 1 fn2-fields))
           (fn2-fields (fn2-fields-set-ref-slot r dslot fn2-fields))
           (fn2-fields (fn2-fields-set-ref-gen r dgen fn2-fields))
           (fn2-fields (fn2-fields-set-ref-off r doff fn2-fields))
           (fn2-fields (fn2-fields-set-ref-len r 32 fn2-fields)))
      (mv-let (code end fn2-pool)
        (fn2-format-source-manifest-header-encode base slot gen off okind oslot ogen fn2-fields fn2-pool)
        (mv code end fn2-fields fn2-pool)))))
(fn2-fc-shape fn2-am-put-header-shape
  (fn2-am-put-header base total dslot dgen doff slot gen off okind oslot ogen fn2-fields fn2-pool)
  (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
  ((fn2-fields 2) (fn2-pool 3)))
(in-theory (disable fn2-am-put-header))

;; Block BLOCK's entry (LEN octets stored in unit UNIT, extent handle EPOCH
;; ALLOC; its BLAKE3 at HSLOT HGEN HOFF and its chaining value 32 octets
;; after it) at OFF of SLOT GEN. Fields at BASE. (mv code end fn2-fields fn2-pool).
(defun fn2-am-put-entry (base block len unit epoch alloc hslot hgen hoff slot gen off okind oslot ogen fn2-fields fn2-pool)
  (declare (xargs :stobjs (fn2-fields fn2-pool) :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
  (if (not (and (natp base) (<= (+ base *fn2-am-entry-fields*) (fn2-fields-rows fn2-fields))
                (unsigned-byte-p 48 block) (unsigned-byte-p 32 len) (unsigned-byte-p 60 unit)
                (unsigned-byte-p 60 epoch) (unsigned-byte-p 60 alloc)
                (unsigned-byte-p 32 hslot) (unsigned-byte-p 60 hgen) (unsigned-byte-p 31 hoff)))
      (mv :bounds off fn2-fields fn2-pool)
    (let* ((h (+ base *fn2-format-source-manifest-entry-field-block-expected-hash*))
           (cv (+ base *fn2-format-source-manifest-entry-field-subtree-cv*))
           (fn2-fields (fn2-fields-set-value (+ base *fn2-format-source-manifest-entry-field-logical-offset*) (* block *fn2-am-block-bytes*) fn2-fields))
           (fn2-fields (fn2-fields-set-value (+ base *fn2-format-source-manifest-entry-field-length*) len fn2-fields))
           (fn2-fields (fn2-fields-set-value (+ base *fn2-format-source-manifest-entry-field-block-storage-domain*) 0 fn2-fields))
           (fn2-fields (fn2-fields-set-value (+ base *fn2-format-source-manifest-entry-field-block-physical-unit*) unit fn2-fields))
           (fn2-fields (fn2-fields-set-value (+ base *fn2-format-source-manifest-entry-field-block-writer-epoch*) epoch fn2-fields))
           (fn2-fields (fn2-fields-set-value (+ base *fn2-format-source-manifest-entry-field-block-allocation*) alloc fn2-fields))
           (fn2-fields (fn2-fields-set-value (+ base *fn2-format-source-manifest-entry-field-block-page-kind*) *page-kind-raw-source* fn2-fields))
           (fn2-fields (fn2-fields-set-value (+ base *fn2-format-source-manifest-entry-field-block-encoded-length*) len fn2-fields))
           (fn2-fields (fn2-fields-set-value h 1 fn2-fields))
           (fn2-fields (fn2-fields-set-ref-slot h hslot fn2-fields))
           (fn2-fields (fn2-fields-set-ref-gen h hgen fn2-fields))
           (fn2-fields (fn2-fields-set-ref-off h hoff fn2-fields))
           (fn2-fields (fn2-fields-set-ref-len h 32 fn2-fields))
           (fn2-fields (fn2-fields-set-value cv 1 fn2-fields))
           (fn2-fields (fn2-fields-set-ref-slot cv hslot fn2-fields))
           (fn2-fields (fn2-fields-set-ref-gen cv hgen fn2-fields))
           (fn2-fields (fn2-fields-set-ref-off cv (+ hoff 32) fn2-fields))
           (fn2-fields (fn2-fields-set-ref-len cv 32 fn2-fields)))
      (mv-let (code end fn2-pool)
        (fn2-format-source-manifest-entry-encode base slot gen off okind oslot ogen fn2-fields fn2-pool)
        (mv code end fn2-fields fn2-pool)))))
(fn2-fc-shape fn2-am-put-entry-shape
  (fn2-am-put-entry base block len unit epoch alloc hslot hgen hoff slot gen off okind oslot ogen fn2-fields fn2-pool)
  (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
  ((fn2-fields 2) (fn2-pool 3)))
(in-theory (disable fn2-am-put-entry))

;; The entry at OFF of SLOT GEN (at most END): (mv code next logical-offset
;; length unit epoch alloc fn2-fields), NEXT the octet after it. Fields at BASE.
(defun fn2-am-get-entry (base slot gen off end okind oslot ogen fn2-fields fn2-pool)
  (declare (xargs :stobjs (fn2-fields fn2-pool) :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
  (if (not (and (natp base) (<= (+ base *fn2-am-entry-fields*) (fn2-fields-rows fn2-fields))))
      (mv :bounds 0 0 0 0 0 0 fn2-fields)
    (mv-let (code next fn2-fields)
      (fn2-format-source-manifest-entry-decode base slot gen off end okind oslot ogen fn2-fields fn2-pool)
      (if (not (eq code :ok)) (mv (if (eq code :more) :bounds code) 0 0 0 0 0 0 fn2-fields)
        (mv :ok (nfix next)
            (nfix (fn2-fields-value (+ base *fn2-format-source-manifest-entry-field-logical-offset*) fn2-fields))
            (nfix (fn2-fields-value (+ base *fn2-format-source-manifest-entry-field-length*) fn2-fields))
            (nfix (fn2-fields-value (+ base *fn2-format-source-manifest-entry-field-block-physical-unit*) fn2-fields))
            (nfix (fn2-fields-value (+ base *fn2-format-source-manifest-entry-field-block-writer-epoch*) fn2-fields))
            (nfix (fn2-fields-value (+ base *fn2-format-source-manifest-entry-field-block-allocation*) fn2-fields))
            fn2-fields)))))
(fn2-fc-shape fn2-am-get-entry-shape
  (fn2-am-get-entry base slot gen off end okind oslot ogen fn2-fields fn2-pool)
  (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))
  ((fn2-fields 7)))
(defthm fn2-am-get-entry-naturals
  (and (natp (mv-nth 1 (fn2-am-get-entry base slot gen off end okind oslot ogen fn2-fields fn2-pool)))
       (natp (mv-nth 2 (fn2-am-get-entry base slot gen off end okind oslot ogen fn2-fields fn2-pool)))
       (natp (mv-nth 3 (fn2-am-get-entry base slot gen off end okind oslot ogen fn2-fields fn2-pool)))
       (natp (mv-nth 4 (fn2-am-get-entry base slot gen off end okind oslot ogen fn2-fields fn2-pool)))
       (natp (mv-nth 5 (fn2-am-get-entry base slot gen off end okind oslot ogen fn2-fields fn2-pool)))
       (natp (mv-nth 6 (fn2-am-get-entry base slot gen off end okind oslot ogen fn2-fields fn2-pool)))))
(in-theory (disable fn2-am-get-entry))

;; The header's length at OFF of SLOT GEN (its stored length checked against
;; TOTAL): (mv code next fn2-fields).
(defun fn2-am-get-header (base total slot gen off end okind oslot ogen fn2-fields fn2-pool)
  (declare (xargs :stobjs (fn2-fields fn2-pool) :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
  (if (not (and (natp base) (<= (+ base *fn2-am-header-fields*) (fn2-fields-rows fn2-fields))))
      (mv :bounds 0 fn2-fields)
    (mv-let (code next fn2-fields)
      (fn2-format-source-manifest-header-decode base slot gen off end okind oslot ogen fn2-fields fn2-pool)
      (cond ((not (eq code :ok)) (mv (if (eq code :more) :bounds code) 0 fn2-fields))
            ((not (and (equal (fn2-fields-value (+ base *fn2-format-source-manifest-header-field-source-length*) fn2-fields) total)
                       (equal (fn2-fields-value (+ base *fn2-format-source-manifest-header-field-block-size*) fn2-fields)
                              *fn2-am-block-bytes*)))
             (mv :bounds 0 fn2-fields))
            (t (mv :ok (nfix next) fn2-fields))))))
(fn2-fc-shape fn2-am-get-header-shape
  (fn2-am-get-header base total slot gen off end okind oslot ogen fn2-fields fn2-pool)
  (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))
  ((fn2-fields 2)))
(defthm fn2-am-get-header-natp
  (natp (mv-nth 1 (fn2-am-get-header base total slot gen off end okind oslot ogen fn2-fields fn2-pool)))
  :rule-classes :type-prescription)
(in-theory (disable fn2-am-get-header))
