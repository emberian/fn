; fn: the payload arena, an ATTACHABLE abstract stobj (D27, representation
; wave D; the records freeze, lane records-freeze 2026-09-26; the
; consolidation design section 3, gpt-6's section 4: the byte owner behind
; an explicit abstraction).
;
; The heap census (planning/evidence/rep-heap-2026-09-25.md) found the one
; long-lived copy of every article: the store record's payload, an octet
; list, sixteen bytes per octet, shared by the archive, the views and the
; trie.  The arena is the retained payloads' concrete home, and the held
; record (books/catalog-record.lisp) refers to a payload by HANDLE, a
; position in the arena's logical list.
;
; `fn-arena' is the GENERIC: its logical value is the list of sealed
; payloads, oldest first, each an octet list (`fn-arn-payload-listp'), and
; its own foundation is the list-backed reference `fn-arena$l' (one field
; holding that list; every export a list operation).  The byte-array
; implementation is `fn-arena-bytes' (books/payload-arena-bytes.lisp), an
; abstract stobj with the SAME logical side (`fn-arena$ap',
; `create-fn-arena$a', the seven `fn-arena$a-*', defined there); an image
; evaluates `(attach-stobj fn-arena fn-arena-bytes)' before this book
; (books/payload-arena-attach.lisp) and the generic then executes over the
; byte array, one byte per payload octet.  A book certified against this
; generic (the catalog, books/catalog*.lisp) is included unchanged under
; the attachment: its certificate is the generic's, and no dependent
; recertifies when the implementation is chosen or replaced (a paged arena
; is a later attachment behind the same `fn-arena$a-*').
;
; Exports (logic / exec over the list foundation):
;   fn-arena-count             (len a)
;   fn-arena-payload-len h     (len (nth h a))
;   fn-arena-get h i           (nth i (nth h a))
;   fn-arena-payload h         (nth h a)
;   fn-arena-seal-list xs      (append a (list xs))      a new handle (the old count)
;   fn-arena-seal-buffer st    (append a (list st))      the octet buffer's value sealed
;   fn-arena-clear             nil
;   fn-arena-seal-range a b st (append a (list st[a..b)))   the buffer's cells [A, B) sealed as one
;                                                            payload: the intern from a buffer range
;
; What the arena guarantees, as theorems over the logical view (so of every
; implementation):
;   - a sealed handle is immutable: `fn-arena-seal-keeps-sealed' (one seal)
;     and `fn-arena-seals-keep-sealed' (any sequence): a reader that pinned
;     handle h before a seal reads the same octets after it;
;   - a handle is never reused: a seal's new handle is the old count and
;     denotes the sealed octets (`fn-arena-seal-new-handle'), and the count
;     only grows (`fn-arena-seal-count');
;   - the one export that re-points a handle is the reseat
;     (`fn-arena-reseat-extent', lane arena-offheap-3): the commit moves a
;     durable payload to its log extent, and under the faithful write the
;     arena is unchanged (`fn-arena-reseat-extent-keeps-a-faithful-arena');
;   - nothing removes a payload: the arena has no delete export, so no
;     reference held by a pinned reader, a feed, a consumer or a BP job can
;     dangle across a seal (the reclaim interface: a reclaimed record's
;     tombstone is a new seal, the old handle stays valid until the next
;     open rebuilds the arena from the retained records: books/records-freeze.lisp).
;   `fn-arn-store-corr' is the relation between an arena and a store
;   history: the arena is the history's payloads oldest first.  Commit
;   (a seal of the finished record's payload, `fn-arn-store-corr-of-commit')
;   and open (a seal per retained record, oldest first, from the empty
;   arena, `fn-arn-store-corr-of-open') establish the same relation.
;
; The host boundary: `fn-arena-seal-buffer' is the seal the served POST
; makes at the finish from the octet buffer the attempt filled
; (host/native/owner.lisp fnn-owner-attempt); no host code reaches an array.

(in-package "ACL2")
(include-book "payload-arena-extent-logic")

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-arn-extent-guardp)
                          (:definition fn-arn-lz-guardp)
                          (:rewrite fn-arn-payload-listp-true-listp))))

; -----------------------------------------------------------------------------
; The list-backed reference foundation.

(defstobj fn-arena$l
  (fn-arena$l-items :type t :initially nil)
  :inline t)

(defun fn-arena$l-wfp (fn-arena$l)
  (declare (xargs :stobjs fn-arena$l))
  (fn-arn-payload-listp (fn-arena$l-items fn-arena$l)))

(defun fn-arena$l-count (fn-arena$l)
  (declare (xargs :stobjs fn-arena$l :guard (fn-arena$l-wfp fn-arena$l)))
  (len (fn-arena$l-items fn-arena$l)))

(defun fn-arena$l-payload-len (h fn-arena$l)
  (declare (xargs :stobjs fn-arena$l
                  :guard (and (fn-arena$l-wfp fn-arena$l)
                              (natp h) (< h (fn-arena$l-count fn-arena$l)))))
  (len (fn-oct-nth h (fn-arena$l-items fn-arena$l))))

(defun fn-arena$l-get (h i fn-arena$l)
  (declare (xargs :stobjs fn-arena$l
                  :guard (and (fn-arena$l-wfp fn-arena$l)
                              (natp h) (< h (fn-arena$l-count fn-arena$l))
                              (natp i) (< i (fn-arena$l-payload-len h fn-arena$l)))))
  (fn-oct-nth i (fn-oct-nth h (fn-arena$l-items fn-arena$l))))

(defun fn-arena$l-payload (h fn-arena$l)
  (declare (xargs :stobjs fn-arena$l
                  :guard (and (fn-arena$l-wfp fn-arena$l)
                              (natp h) (< h (fn-arena$l-count fn-arena$l)))))
  (fn-oct-nth h (fn-arena$l-items fn-arena$l)))

(defun fn-arena$l-seal-list (xs fn-arena$l)
  (declare (xargs :stobjs fn-arena$l
                  :guard (and (fn-arena$l-wfp fn-arena$l) (fn-cbor-octet-listp xs))))
  (update-fn-arena$l-items (fn-oct-snoc (fn-arena$l-items fn-arena$l) xs) fn-arena$l))

(defun fn-arena$l-seal-buffer (fn-octets fn-arena$l)
  (declare (xargs :stobjs (fn-octets fn-arena$l) :guard (fn-arena$l-wfp fn-arena$l)))
  (update-fn-arena$l-items (fn-oct-snoc (fn-arena$l-items fn-arena$l) (fn-octets-list fn-octets))
                           fn-arena$l))

(defun fn-arena$l-clear (fn-arena$l)
  (declare (xargs :stobjs fn-arena$l))
  (update-fn-arena$l-items nil fn-arena$l))

(defun fn-arena$l-seal-range (a b fn-octets fn-arena$l)
  (declare (xargs :stobjs (fn-octets fn-arena$l)
                  :guard (and (fn-arena$l-wfp fn-arena$l)
                              (natp a) (natp b) (<= a b) (<= b (fn-octets-len fn-octets)))))
  (update-fn-arena$l-items (fn-oct-snoc (fn-arena$l-items fn-arena$l)
                                        (fn-oct-slice-list a b fn-octets))
                           fn-arena$l))

; The extent seal over the reference: the payload read through the host's
; whole-payload realizer (A-DURABLE-EXTENT: it is fn-durable-octets of the
; extent).
; The node's arena is the attachment (books/payload-arena-extent.lisp), which
; records the extent and holds no octets.
(defun fn-arena$l-seal-extent (file eoff elen poff plen trailer fn-arena$l)
  (declare (xargs :stobjs fn-arena$l
                  :guard (and (fn-arena$l-wfp fn-arena$l)
                              (fn-arn-extent-guardp file eoff elen poff plen trailer))))
  (update-fn-arena$l-items
   (fn-oct-snoc (fn-arena$l-items fn-arena$l)
                (fn-durable-realize-octets file eoff elen poff plen trailer))
   fn-arena$l))

; The reseat and the release over the reference (lane arena-offheap-3): the
; handle's payload becomes the extent's octets, read through the realizer;
; the release changes nothing.
(defun fn-arena$l-reseat-extent (h file eoff elen poff plen trailer fn-arena$l)
  (declare (xargs :stobjs fn-arena$l
                  :guard (and (fn-arena$l-wfp fn-arena$l)
                              (natp h) (< h (fn-arena$l-count fn-arena$l))
                              (fn-arn-extent-guardp file eoff elen poff plen trailer))))
  (update-fn-arena$l-items
   (fn-oct-update h (fn-durable-realize-octets file eoff elen poff plen trailer)
                  (fn-arena$l-items fn-arena$l))
   fn-arena$l))

; The compressed seal and reseat over the reference (lane compression-extents,
; PRF-326): the payload read through the host's compressed realizer
; (A-DURABLE-LZ: it is fn-lzr-lz-value of the block's durable octets).
(defun fn-arena$l-seal-lz-extent (file eoff elen poff plen trailer n dict fn-arena$l)
  (declare (xargs :stobjs fn-arena$l
                  :guard (and (fn-arena$l-wfp fn-arena$l)
                              (fn-arn-lz-guardp file eoff elen poff plen trailer n dict))))
  (update-fn-arena$l-items
   (fn-oct-snoc (fn-arena$l-items fn-arena$l)
                (fn-durable-realize-lz file eoff elen poff plen trailer n dict))
   fn-arena$l))

(defun fn-arena$l-reseat-lz-extent (h file eoff elen poff plen trailer n dict fn-arena$l)
  (declare (xargs :stobjs fn-arena$l
                  :guard (and (fn-arena$l-wfp fn-arena$l)
                              (natp h) (< h (fn-arena$l-count fn-arena$l))
                              (fn-arn-lz-guardp file eoff elen poff plen trailer n dict))))
  (update-fn-arena$l-items
   (fn-oct-update h (fn-durable-realize-lz file eoff elen poff plen trailer n dict)
                  (fn-arena$l-items fn-arena$l))
   fn-arena$l))

(defun fn-arena$l-release (h fn-arena$l)
  (declare (xargs :stobjs fn-arena$l :guard (natp h))
           (ignore h))
  fn-arena$l)

; The abstraction relation of the reference: the field is the logical value.
(defun fn-arena$lcorr (fn-arena$l fn-arena$a)
  (declare (xargs :stobjs fn-arena$l :verify-guards nil))
  (and (fn-arn-payload-listp fn-arena$a)
       (equal (fn-arena$l-items fn-arena$l) fn-arena$a)))

; -----------------------------------------------------------------------------
; The generic's obligations over its own foundation, each as
; `defabsstobj-missing-events' states it.

(defthm create-fn-arena{correspondence}
  (fn-arena$lcorr (create-fn-arena$l) (create-fn-arena$a))
  :rule-classes nil)

(defthm create-fn-arena{preserved}
  (fn-arena$ap (create-fn-arena$a))
  :rule-classes nil)

(defthm fn-arena-count{correspondence}
  (implies (fn-arena$lcorr fn-arena$l fn-arena)
           (equal (fn-arena$l-count fn-arena$l) (fn-arena$a-count fn-arena)))
  :rule-classes nil)

(defthm fn-arena-count{guard-thm}
  (implies (fn-arena$lcorr fn-arena$l fn-arena)
           (fn-arena$l-wfp fn-arena$l))
  :rule-classes nil)

(defthm fn-arena-payload-len{correspondence}
  (implies (and (fn-arena$lcorr fn-arena$l fn-arena)
                (natp h) (< h (fn-arena$a-count fn-arena)))
           (equal (fn-arena$l-payload-len h fn-arena$l) (fn-arena$a-payload-len h fn-arena)))
  :rule-classes nil)

(defthm fn-arena-payload-len{guard-thm}
  (implies (and (fn-arena$lcorr fn-arena$l fn-arena)
                (natp h) (< h (fn-arena$a-count fn-arena)))
           (and (fn-arena$l-wfp fn-arena$l)
                (natp h) (< h (fn-arena$l-count fn-arena$l))))
  :rule-classes nil)

(defthm fn-arena-get{correspondence}
  (implies (and (fn-arena$lcorr fn-arena$l fn-arena)
                (natp h) (< h (fn-arena$a-count fn-arena))
                (natp i) (< i (fn-arena$a-payload-len h fn-arena)))
           (equal (fn-arena$l-get h i fn-arena$l) (fn-arena$a-get h i fn-arena)))
  :rule-classes nil)

(defthm fn-arena-get{guard-thm}
  (implies (and (fn-arena$lcorr fn-arena$l fn-arena)
                (natp h) (< h (fn-arena$a-count fn-arena))
                (natp i) (< i (fn-arena$a-payload-len h fn-arena)))
           (and (fn-arena$l-wfp fn-arena$l)
                (natp h) (< h (fn-arena$l-count fn-arena$l))
                (natp i) (< i (fn-arena$l-payload-len h fn-arena$l))))
  :rule-classes nil)

(defthm fn-arena-payload{correspondence}
  (implies (and (fn-arena$lcorr fn-arena$l fn-arena)
                (natp h) (< h (fn-arena$a-count fn-arena)))
           (equal (fn-arena$l-payload h fn-arena$l) (fn-arena$a-payload h fn-arena)))
  :rule-classes nil)

(defthm fn-arena-payload{guard-thm}
  (implies (and (fn-arena$lcorr fn-arena$l fn-arena)
                (natp h) (< h (fn-arena$a-count fn-arena)))
           (and (fn-arena$l-wfp fn-arena$l)
                (natp h) (< h (fn-arena$l-count fn-arena$l))))
  :rule-classes nil)

(defthm fn-arena-seal-list{correspondence}
  (implies (and (fn-arena$lcorr fn-arena$l fn-arena)
                (fn-cbor-octet-listp xs))
           (fn-arena$lcorr (fn-arena$l-seal-list xs fn-arena$l)
                           (fn-arena$a-seal-list xs fn-arena)))
  :rule-classes nil)

(defthm fn-arena-seal-list{guard-thm}
  (implies (and (fn-arena$lcorr fn-arena$l fn-arena)
                (fn-cbor-octet-listp xs))
           (and (fn-arena$l-wfp fn-arena$l) (fn-cbor-octet-listp xs)))
  :rule-classes nil)

(defthm fn-arena-seal-list{preserved}
  (implies (and (fn-arena$ap fn-arena)
                (fn-cbor-octet-listp xs))
           (fn-arena$ap (fn-arena$a-seal-list xs fn-arena)))
  :rule-classes nil)

(defthm fn-arena-seal-buffer{correspondence}
  (implies (and (fn-arena$lcorr fn-arena$l fn-arena)
                (fn-octets-p fn-octets))
           (fn-arena$lcorr (fn-arena$l-seal-buffer fn-octets fn-arena$l)
                           (fn-arena$a-seal-buffer fn-octets fn-arena)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-oct-octets-p-is-octet-listp))))

(defthm fn-arena-seal-buffer{guard-thm}
  (implies (and (fn-arena$lcorr fn-arena$l fn-arena)
                (fn-octets-p fn-octets))
           (fn-arena$l-wfp fn-arena$l))
  :rule-classes nil)

(defthm fn-arena-seal-buffer{preserved}
  (implies (and (fn-arena$ap fn-arena)
                (fn-octets-p fn-octets))
           (fn-arena$ap (fn-arena$a-seal-buffer fn-octets fn-arena)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-oct-octets-p-is-octet-listp))))

(defthm fn-arena-clear{correspondence}
  (implies (fn-arena$lcorr fn-arena$l fn-arena)
           (fn-arena$lcorr (fn-arena$l-clear fn-arena$l) (fn-arena$a-clear fn-arena)))
  :rule-classes nil)

(defthm fn-arena-clear{preserved}
  (implies (fn-arena$ap fn-arena)
           (fn-arena$ap (fn-arena$a-clear fn-arena)))
  :rule-classes nil)

(defthm fn-arena-seal-range{correspondence}
  (implies (and (fn-arena$lcorr fn-arena$l fn-arena)
                (fn-octets-p fn-octets)
                (natp a) (natp b) (<= a b) (<= b (fn-octets-len fn-octets)))
           (fn-arena$lcorr (fn-arena$l-seal-range a b fn-octets fn-arena$l)
                           (fn-arena$a-seal-range a b fn-octets fn-arena)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-oct-octets-p-is-octet-listp)
                                  (fn-oct-slice-list-is-take-nthcdr)))))

(defthm fn-arena-seal-range{guard-thm}
  (implies (and (fn-arena$lcorr fn-arena$l fn-arena)
                (fn-octets-p fn-octets)
                (natp a) (natp b) (<= a b) (<= b (fn-octets-len fn-octets)))
           (and (fn-arena$l-wfp fn-arena$l)
                (natp a) (natp b) (<= a b) (<= b (fn-octets-len fn-octets))))
  :rule-classes nil)

(defthm fn-arena-seal-range{preserved}
  (implies (and (fn-arena$ap fn-arena)
                (fn-octets-p fn-octets)
                (natp a) (natp b) (<= a b) (<= b (fn-octets-len fn-octets)))
           (fn-arena$ap (fn-arena$a-seal-range a b fn-octets fn-arena)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-oct-octets-p-is-octet-listp)
                                  (fn-oct-slice-list-is-take-nthcdr)))))

(defthm fn-arena-seal-extent{correspondence}
  (implies (and (fn-arena$lcorr fn-arena$l fn-arena)
                (fn-arn-extent-guardp file eoff elen poff plen trailer))
           (fn-arena$lcorr (fn-arena$l-seal-extent file eoff elen poff plen trailer fn-arena$l)
                           (fn-arena$a-seal-extent file eoff elen poff plen trailer fn-arena)))
  :rule-classes nil)

(defthm fn-arena-seal-extent{guard-thm}
  (implies (and (fn-arena$lcorr fn-arena$l fn-arena)
                (fn-arn-extent-guardp file eoff elen poff plen trailer))
           (and (fn-arena$l-wfp fn-arena$l)
                (fn-arn-extent-guardp file eoff elen poff plen trailer)))
  :rule-classes nil)

(defthm fn-arena-seal-extent{preserved}
  (implies (and (fn-arena$ap fn-arena)
                (fn-arn-extent-guardp file eoff elen poff plen trailer))
           (fn-arena$ap (fn-arena$a-seal-extent file eoff elen poff plen trailer fn-arena)))
  :rule-classes nil)

(local
 (defthm fn-arn-payload-listp-of-update-nth
   (implies (and (fn-arn-payload-listp a) (fn-cbor-octet-listp v) (natp h) (< h (len a)))
            (fn-arn-payload-listp (update-nth h v a)))
   :hints (("Goal" :in-theory (enable update-nth fn-arn-payload-listp)))))

(defthm fn-arena-reseat-extent{correspondence}
  (implies (and (fn-arena$lcorr fn-arena$l fn-arena)
                (natp h) (< h (fn-arena$a-count fn-arena))
                (fn-arn-extent-guardp file eoff elen poff plen trailer))
           (fn-arena$lcorr (fn-arena$l-reseat-extent h file eoff elen poff plen trailer fn-arena$l)
                           (fn-arena$a-reseat-extent h file eoff elen poff plen trailer fn-arena)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-oct-update-is-update-nth))))

(defthm fn-arena-reseat-extent{guard-thm}
  (implies (and (fn-arena$lcorr fn-arena$l fn-arena)
                (natp h) (< h (fn-arena$a-count fn-arena))
                (fn-arn-extent-guardp file eoff elen poff plen trailer))
           (and (fn-arena$l-wfp fn-arena$l)
                (natp h) (< h (fn-arena$l-count fn-arena$l))
                (fn-arn-extent-guardp file eoff elen poff plen trailer)))
  :rule-classes nil)

(defthm fn-arena-reseat-extent{preserved}
  (implies (and (fn-arena$ap fn-arena)
                (natp h) (< h (fn-arena$a-count fn-arena))
                (fn-arn-extent-guardp file eoff elen poff plen trailer))
           (fn-arena$ap (fn-arena$a-reseat-extent h file eoff elen poff plen trailer fn-arena)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-oct-update-is-update-nth))))

(defthm fn-arena-seal-lz-extent{correspondence}
  (implies (and (fn-arena$lcorr fn-arena$l fn-arena)
                (fn-arn-lz-guardp file eoff elen poff plen trailer n dict))
           (fn-arena$lcorr (fn-arena$l-seal-lz-extent file eoff elen poff plen trailer n dict
                                                      fn-arena$l)
                           (fn-arena$a-seal-lz-extent file eoff elen poff plen trailer n dict
                                                      fn-arena)))
  :rule-classes nil)

(defthm fn-arena-seal-lz-extent{guard-thm}
  (implies (and (fn-arena$lcorr fn-arena$l fn-arena)
                (fn-arn-lz-guardp file eoff elen poff plen trailer n dict))
           (and (fn-arena$l-wfp fn-arena$l)
                (fn-arn-lz-guardp file eoff elen poff plen trailer n dict)))
  :rule-classes nil)

(defthm fn-arena-seal-lz-extent{preserved}
  (implies (and (fn-arena$ap fn-arena)
                (fn-arn-lz-guardp file eoff elen poff plen trailer n dict))
           (fn-arena$ap (fn-arena$a-seal-lz-extent file eoff elen poff plen trailer n dict
                                                   fn-arena)))
  :rule-classes nil)

(defthm fn-arena-reseat-lz-extent{correspondence}
  (implies (and (fn-arena$lcorr fn-arena$l fn-arena)
                (natp h) (< h (fn-arena$a-count fn-arena))
                (fn-arn-lz-guardp file eoff elen poff plen trailer n dict))
           (fn-arena$lcorr (fn-arena$l-reseat-lz-extent h file eoff elen poff plen trailer n dict
                                                        fn-arena$l)
                           (fn-arena$a-reseat-lz-extent h file eoff elen poff plen trailer n dict
                                                        fn-arena)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-oct-update-is-update-nth))))

(defthm fn-arena-reseat-lz-extent{guard-thm}
  (implies (and (fn-arena$lcorr fn-arena$l fn-arena)
                (natp h) (< h (fn-arena$a-count fn-arena))
                (fn-arn-lz-guardp file eoff elen poff plen trailer n dict))
           (and (fn-arena$l-wfp fn-arena$l)
                (natp h) (< h (fn-arena$l-count fn-arena$l))
                (fn-arn-lz-guardp file eoff elen poff plen trailer n dict)))
  :rule-classes nil)

(defthm fn-arena-reseat-lz-extent{preserved}
  (implies (and (fn-arena$ap fn-arena)
                (natp h) (< h (fn-arena$a-count fn-arena))
                (fn-arn-lz-guardp file eoff elen poff plen trailer n dict))
           (fn-arena$ap (fn-arena$a-reseat-lz-extent h file eoff elen poff plen trailer n dict
                                                     fn-arena)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-oct-update-is-update-nth))))

(defthm fn-arena-release{correspondence}
  (implies (and (fn-arena$lcorr fn-arena$l fn-arena)
                (natp h))
           (fn-arena$lcorr (fn-arena$l-release h fn-arena$l)
                           (fn-arena$a-release h fn-arena)))
  :rule-classes nil)

(defthm fn-arena-release{guard-thm}
  (implies (and (fn-arena$lcorr fn-arena$l fn-arena)
                (natp h))
           (natp h))
  :rule-classes nil)

(defthm fn-arena-release{preserved}
  (implies (and (fn-arena$ap fn-arena)
                (natp h))
           (fn-arena$ap (fn-arena$a-release h fn-arena)))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; The generic.  `:attachable t' is what lets (attach-stobj fn-arena IMPL),
; evaluated before this book is included, replace the foundation and the
; :exec functions; the :logic functions are the implementation's own.

(defabsstobj fn-arena
  :foundation fn-arena$l
  :recognizer (fn-arena-p :logic fn-arena$ap :exec fn-arena$lp)
  :creator (create-fn-arena :logic create-fn-arena$a :exec create-fn-arena$l)
  :corr-fn fn-arena$lcorr
  :exports ((fn-arena-count :logic fn-arena$a-count :exec fn-arena$l-count)
            (fn-arena-payload-len :logic fn-arena$a-payload-len :exec fn-arena$l-payload-len)
            (fn-arena-get :logic fn-arena$a-get :exec fn-arena$l-get)
            (fn-arena-payload :logic fn-arena$a-payload :exec fn-arena$l-payload)
            (fn-arena-seal-list :logic fn-arena$a-seal-list :exec fn-arena$l-seal-list
                                :protect t)
            (fn-arena-seal-buffer :logic fn-arena$a-seal-buffer :exec fn-arena$l-seal-buffer
                                  :protect t)
            (fn-arena-clear :logic fn-arena$a-clear :exec fn-arena$l-clear :protect t)
            (fn-arena-seal-range :logic fn-arena$a-seal-range :exec fn-arena$l-seal-range
                                 :protect t)
            (fn-arena-seal-extent :logic fn-arena$a-seal-extent :exec fn-arena$l-seal-extent
                                  :protect t)
            (fn-arena-reseat-extent :logic fn-arena$a-reseat-extent
                                    :exec fn-arena$l-reseat-extent :protect t)
            (fn-arena-release :logic fn-arena$a-release :exec fn-arena$l-release :protect t)
            (fn-arena-seal-lz-extent :logic fn-arena$a-seal-lz-extent
                                     :exec fn-arena$l-seal-lz-extent :protect t)
            (fn-arena-reseat-lz-extent :logic fn-arena$a-reseat-lz-extent
                                       :exec fn-arena$l-reseat-lz-extent :protect t))
  :attachable t)

; -----------------------------------------------------------------------------
; The logical view, opened: the value is the list of payloads, a handle is
; a position, a seal is an append.

(defthm fn-arena-p-is-payload-listp
  (equal (fn-arena-p x) (fn-arn-payload-listp x)))

(defthm fn-arena-count-is-len
  (equal (fn-arena-count fn-arena) (len fn-arena)))

(defthm fn-arena-payload-len-is-len-nth
  (equal (fn-arena-payload-len h fn-arena) (len (nth h fn-arena))))

(defthm fn-arena-get-is-nth
  (equal (fn-arena-get h i fn-arena) (nth i (nth h fn-arena))))

(defthm fn-arena-payload-is-nth
  (equal (fn-arena-payload h fn-arena) (nth h fn-arena)))

(defthm fn-arena-seal-list-is-append
  (implies (fn-arena-p fn-arena)
           (equal (fn-arena-seal-list xs fn-arena) (append fn-arena (list xs)))))

(defthm fn-arena-seal-buffer-is-append
  (implies (fn-arena-p fn-arena)
           (equal (fn-arena-seal-buffer fn-octets fn-arena) (append fn-arena (list fn-octets)))))

(defthm fn-arena-clear-is-nil
  (equal (fn-arena-clear fn-arena) nil))

; The range seal is the list seal of the slice (no hypothesis: both are
; fn-oct-snoc), and an append under the recognizer.  The intern from a
; buffer range (lane open-by-index's fn-obi-seal-range, batch AQ) is this
; export: its theorem fn-obi-seal-range-is-seal-of-slice is the first.
(defthm fn-arena-seal-range-is-seal-list
  (equal (fn-arena-seal-range a b fn-octets fn-arena)
         (fn-arena-seal-list (fn-oct-slice-list a b fn-octets) fn-arena)))

(defthm fn-arena-seal-range-is-append
  (implies (fn-arena-p fn-arena)
           (equal (fn-arena-seal-range a b fn-octets fn-arena)
                  (append fn-arena (list (fn-oct-slice-list a b fn-octets))))))

; The extent seal (stage 2, PRF-294): an append of the extent's durable
; octets (A-DURABLE-EXTENT).
(defthm fn-arena-seal-extent-is-append
  (implies (fn-arena-p fn-arena)
           (equal (fn-arena-seal-extent file eoff elen poff plen trailer fn-arena)
                  (append fn-arena (list (fn-durable-octets file poff plen))))))

(defthm fn-arena-p-forward
  (implies (fn-arena-p x)
           (and (fn-arn-payload-listp x) (true-listp x)))
  :rule-classes :forward-chaining)

(in-theory (disable fn-arena-p fn-arena-count fn-arena-payload-len fn-arena-get
                    fn-arena-payload fn-arena-seal-list fn-arena-seal-buffer fn-arena-clear
                    fn-arena-seal-range fn-arena-reseat-extent fn-arena-release
                    fn-arena-p-is-payload-listp))

; -----------------------------------------------------------------------------
; KEYSTONES.  What a reader holding a handle may rely on.

; A sealed handle is immutable: whatever a seal appends, every handle below
; the old count denotes the octets it denoted before.  A reader that pinned
; a handle sees the same payload after any later commit.
; The hypotheses are that the handle is a natural below the count: on the
; empty arena a negative handle reads the new payload (`nth' of a negative
; is `car'), so `natp' is not redundant.  No recognizer is needed: the
; seal walks the conses the value has.
(local
 (defthm fn-arn-nth-of-snoc-below
   (implies (and (natp h) (< h (len a)))
            (equal (nth h (fn-oct-snoc a xs)) (nth h a)))
   :hints (("Goal" :in-theory (enable nth)))))

(local
 (defthm fn-arn-nth-of-snoc-at
   (equal (nth (len a) (fn-oct-snoc a xs)) xs)
   :hints (("Goal" :in-theory (enable nth)))))

(local
 (defthm fn-arn-len-of-snoc
   (equal (len (fn-oct-snoc a xs)) (1+ (len a)))))

(defthm fn-arena-seal-keeps-sealed
  (implies (and (natp h) (< h (fn-arena-count fn-arena)))
           (equal (fn-arena-payload h (fn-arena-seal-list xs fn-arena))
                  (fn-arena-payload h fn-arena)))
  :hints (("Goal" :in-theory (enable fn-arena-payload fn-arena-seal-list fn-arena-count))))

(defthm fn-arena-seal-buffer-keeps-sealed
  (implies (and (natp h) (< h (fn-arena-count fn-arena)))
           (equal (fn-arena-payload h (fn-arena-seal-buffer fn-octets fn-arena))
                  (fn-arena-payload h fn-arena)))
  :hints (("Goal" :in-theory (enable fn-arena-payload fn-arena-seal-buffer fn-arena-count))))

; A handle is never reused: the seal's new handle is the old count, it
; denotes the sealed octets, and the count grows by one.  No hypothesis.
(defthm fn-arena-seal-new-handle
  (equal (fn-arena-payload (fn-arena-count fn-arena) (fn-arena-seal-list xs fn-arena))
         xs)
  :hints (("Goal" :in-theory (enable fn-arena-payload fn-arena-seal-list fn-arena-count))))

; KEYSTONE (PRF-294) fn-arena-seal-extent-payload: the extent seal's new
; handle is the old count and denotes the durable octets of its extent, every
; older handle keeps its payload, and the count grows by one.  No hypothesis:
; the extent's octets are what A-DURABLE-EXTENT says the file holds there.
(defthm fn-arena-seal-extent-payload
  (and (equal (fn-arena-payload (fn-arena-count fn-arena)
                                (fn-arena-seal-extent file eoff elen poff plen trailer fn-arena))
              (fn-durable-octets file poff plen))
       (implies (and (natp h) (< h (fn-arena-count fn-arena)))
                (equal (fn-arena-payload h (fn-arena-seal-extent file eoff elen poff plen trailer
                                                                 fn-arena))
                       (fn-arena-payload h fn-arena)))
       (equal (fn-arena-count (fn-arena-seal-extent file eoff elen poff plen trailer fn-arena))
              (1+ (fn-arena-count fn-arena))))
  :hints (("Goal" :in-theory (enable fn-arena-payload fn-arena-seal-extent fn-arena-count))))

; KEYSTONE (PRF-309) fn-arena-reseat-extent-payload: the reseat re-points
; handle H at the extent: H denotes the extent's durable octets, every other
; handle keeps its payload, the count is unchanged.
(defthm fn-arena-reseat-extent-payload
  (implies (and (fn-arena-p fn-arena) (natp h) (< h (fn-arena-count fn-arena)))
           (and (equal (fn-arena-payload h (fn-arena-reseat-extent h file eoff elen poff plen
                                                                   trailer fn-arena))
                       (fn-durable-octets file poff plen))
                (implies (and (natp k) (not (equal k h)))
                         (equal (fn-arena-payload k (fn-arena-reseat-extent h file eoff elen poff plen
                                                                             trailer fn-arena))
                                (fn-arena-payload k fn-arena)))
                (equal (fn-arena-count (fn-arena-reseat-extent h file eoff elen poff plen trailer
                                                               fn-arena))
                       (fn-arena-count fn-arena))))
  :hints (("Goal" :in-theory (enable fn-arena-payload fn-arena-reseat-extent fn-arena-count
                                     fn-oct-update-is-update-nth))))

(local
 (defthm fn-arn-update-nth-same
   (implies (and (natp h) (< h (len a)))
            (equal (update-nth h (nth h a) a) a))
   :hints (("Goal" :in-theory (enable update-nth nth)))))

; KEYSTONE (PRF-309) fn-arena-reseat-extent-keeps-a-faithful-arena: when the
; extent's durable octets are the payload H holds (the faithful write: the
; log wrote those octets there and fenced them), the reseat leaves the arena
; -- every handle's payload, so every theorem over it -- unchanged.  This is
; what lets the commit move a payload off the heap without a new theorem
; about any consumer.
(defthm fn-arena-reseat-extent-keeps-a-faithful-arena
  (implies (and (fn-arena-p fn-arena)
                (natp h) (< h (fn-arena-count fn-arena))
                (equal (fn-durable-octets file poff plen) (fn-arena-payload h fn-arena)))
           (equal (fn-arena-reseat-extent h file eoff elen poff plen trailer fn-arena)
                  fn-arena))
  :hints (("Goal" :in-theory (enable fn-arena-payload fn-arena-reseat-extent fn-arena-count
                                     fn-oct-update-is-update-nth fn-arena-p))))

; KEYSTONE (PRF-326) fn-arena-seal-lz-extent-payload: the compressed seal's
; new handle is the old count and denotes the value its block decodes to,
; every older handle keeps its payload, and the count grows by one.
(defthm fn-arena-seal-lz-extent-payload
  (and (equal (fn-arena-payload (fn-arena-count fn-arena)
                                (fn-arena-seal-lz-extent file eoff elen poff plen trailer n dict
                                                         fn-arena))
              (fn-lzr-lz-value dict (fn-durable-octets file poff plen) n))
       (implies (and (natp h) (< h (fn-arena-count fn-arena)))
                (equal (fn-arena-payload h (fn-arena-seal-lz-extent file eoff elen poff plen
                                                                    trailer n dict fn-arena))
                       (fn-arena-payload h fn-arena)))
       (equal (fn-arena-count (fn-arena-seal-lz-extent file eoff elen poff plen trailer n dict
                                                       fn-arena))
              (1+ (fn-arena-count fn-arena))))
  :hints (("Goal" :in-theory (enable fn-arena-payload fn-arena-seal-lz-extent fn-arena-count))))

; KEYSTONE (PRF-326) fn-arena-reseat-lz-extent-keeps-a-faithful-arena: when
; the block's durable octets decode to the payload H holds (the commit's
; check over the octets the log wrote, and the faithful write), the
; compressed reseat leaves the arena unchanged.
(defthm fn-arena-reseat-lz-extent-keeps-a-faithful-arena
  (implies (and (fn-arena-p fn-arena)
                (natp h) (< h (fn-arena-count fn-arena))
                (equal (fn-lzr-lz-value dict (fn-durable-octets file poff plen) n)
                       (fn-arena-payload h fn-arena)))
           (equal (fn-arena-reseat-lz-extent h file eoff elen poff plen trailer n dict fn-arena)
                  fn-arena))
  :hints (("Goal" :in-theory (enable fn-arena-payload fn-arena-reseat-lz-extent fn-arena-count
                                     fn-oct-update-is-update-nth fn-arena-p))))

; The compressed seal is an append (the view the consumers open).
(defthm fn-arena-seal-lz-extent-is-append
  (implies (fn-arena-p fn-arena)
           (equal (fn-arena-seal-lz-extent file eoff elen poff plen trailer n dict fn-arena)
                  (append fn-arena (list (fn-lzr-lz-value dict (fn-durable-octets file poff plen)
                                                          n)))))
  :hints (("Goal" :in-theory (enable fn-arena-seal-lz-extent fn-arena-p))))

(in-theory (disable fn-arena-seal-lz-extent fn-arena-reseat-lz-extent))

(defthm fn-arena-release-unfolds
  (equal (fn-arena-release h fn-arena) fn-arena)
  :hints (("Goal" :in-theory (enable fn-arena-release))))

(defthm fn-arena-seal-count
  (equal (fn-arena-count (fn-arena-seal-list xs fn-arena))
         (1+ (fn-arena-count fn-arena)))
  :hints (("Goal" :in-theory (enable fn-arena-seal-list fn-arena-count))))

; The same two facts in the `len' form the opened view leaves behind, so
; that a guard about a count after seals is arithmetic.
(defthm fn-arena-seal-list-len
  (equal (len (fn-arena-seal-list xs fn-arena)) (1+ (len fn-arena)))
  :hints (("Goal" :in-theory (enable fn-arena-seal-list))))

(defthm fn-arena-seal-buffer-len
  (equal (len (fn-arena-seal-buffer fn-octets fn-arena)) (1+ (len fn-arena)))
  :hints (("Goal" :in-theory (enable fn-arena-seal-buffer))))

; Any sequence of seals (the admitted transitions of a live arena: a commit
; is a seal, and nothing else changes the value between open and close)
; keeps every handle it found.
(defun fn-arn-seal-many (payloads fn-arena)
  (declare (xargs :stobjs fn-arena :guard (fn-arn-payload-listp payloads)))
  (if (atom payloads)
      fn-arena
    (let ((fn-arena (fn-arena-seal-list (car payloads) fn-arena)))
      (fn-arn-seal-many (cdr payloads) fn-arena))))

; The seal is `append' on any true list, whatever its elements: the
; recognizer is not needed here and is not what the fold preserves.
(local
 (defthm fn-arn-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(defthm fn-arn-seal-many-is-append
  (implies (and (true-listp fn-arena) (true-listp payloads))
           (equal (fn-arn-seal-many payloads fn-arena)
                  (append fn-arena payloads)))
  :hints (("Goal" :induct (fn-arn-seal-many payloads fn-arena)
           :in-theory (enable fn-arena-seal-list))))

; The immutability fact in the `nth' form the opened view leaves behind.
(defthm fn-arena-seal-list-keeps-nth-below
  (implies (and (natp h) (< h (len fn-arena)))
           (equal (nth h (fn-arena-seal-list xs fn-arena)) (nth h fn-arena)))
  :hints (("Goal" :in-theory (enable fn-arena-seal-list))))

(defthm fn-arena-seals-keep-sealed
  (implies (and (natp h) (< h (fn-arena-count fn-arena)))
           (equal (fn-arena-payload h (fn-arn-seal-many payloads fn-arena))
                  (fn-arena-payload h fn-arena)))
  :hints (("Goal" :induct (fn-arn-seal-many payloads fn-arena)
           :in-theory (disable fn-arn-seal-many-is-append))))

; -----------------------------------------------------------------------------
; The relation with a store history.  The history (fn-sf-records,
; books/store-files.lisp) is oldest first, a commit appending the finished
; record at its end (fn-sf-finish: `(append (fn-sf-records s) (list record))'),
; and so is the arena: handle k is the payload of the k-th record.

(defun fn-arn-payloads-of (records)
  (declare (xargs :guard t))
  (if (consp records)
      (cons (fn-record-payload (car records))
            (fn-arn-payloads-of (cdr records)))
    nil))

(defthm fn-arn-true-listp-of-payloads-of
  (true-listp (fn-arn-payloads-of records)))

(defthm fn-arn-payloads-of-append-one
  (equal (fn-arn-payloads-of (append records (list record)))
         (append (fn-arn-payloads-of records) (list (fn-record-payload record)))))

;; The octets at a payload handle, read in place; a handle outside the arena
;; reads as no bytes.  Only READS the arena (flip-L6-2's rule).
(defun fn-handle-bytes (h fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (and (natp h) (< h (fn-arena-count fn-arena)))
      (fn-arena-payload h fn-arena)
    nil))

; The relation itself is logical (defun-nx): the arena's value against the
; history.  Nothing executes it; a commit and an open establish it by the
; two theorems that follow, and nothing on a served path evaluates it.
(defun-nx fn-arn-store-corr (fn-arena records)
  (equal fn-arena (fn-arn-payloads-of records)))

; Commit: the finished record joins the head of the history and its
; payload is sealed; the relation is kept.
(defthm fn-arn-store-corr-of-commit
  (implies (fn-arn-store-corr fn-arena records)
           (fn-arn-store-corr (fn-arena-seal-list (fn-record-payload record) fn-arena)
                              (append records (list record))))
  :hints (("Goal" :in-theory (enable fn-arena-seal-list))))

; Open: every retained record's payload sealed oldest first from the empty
; arena establishes the same relation a history of commits would have.
(defthm fn-arn-store-corr-of-open
  (fn-arn-store-corr (fn-arn-seal-many (fn-arn-payloads-of records) nil) records)
  :hints (("Goal" :in-theory (enable fn-arena-seal-list))))
