;; fn: a checkpoint whose derived event index is not this image's shape is refused by name (PKT-395).
;
; The checkpoint file carries the Store's derived event index and, where the
; index yields the record list, only the record count (fn-sco-freeze): the
; records are read back out of the index at decode (fn-sco-thaw).  The
; index's shape has changed twice since the first checkpoints were written,
; and the file names no shape:
;
; - a249a699 (signed-history-index) made the index a pair, the sequence trie
;   and a Message-ID trie; a file written before it (the 20,000 fixture,
;   8cc3cd4c; the deployed bbf52159's) thaws a garbage record list, and the
;   open is refused only because a later check fails:
;   `open=full-replay reason=checkpoint-open-refused';
; - d0df09ed (hot-path-scans-2) added the count, (SEQ-TRIE MSGID-TRIE .
;   COUNT); a file written between the two (every image from a249a699 to
;   d0df09ed, dfa810fc among them) thaws the RIGHT record list, because the
;   sequence trie is still the index's car, but its Message-ID trie is read
;   as the car of the old one and its count as 0.  Nothing at open checks
;   the derived index (fn-sn-statep leaves it out by design, D21), so that
;   open succeeds and installs an index that does not correspond to the
;   history: the record count PRF-180's budget reads is the suffix's, and a
;   Message-ID lookup misses committed articles.  The model's open
;   (fn-osi-open) assumes the decoded checkpoint is this code's capture of
;   its prefix; across a shape change that assumption is false.
;
; The shape test below is O(1): the index this code builds counts every
; event it puts (fn-cei-count-of-build-aux), so the index of a checkpoint
; this image wrote holds exactly the file's record count, and an index of
; either older shape holds 0 (the pair's third field is a trie, the single
; trie's second is one).  A decoded checkpoint that fails it is refused as
; :index-shape, reported `open=full-replay reason=checkpoint-index-shape',
; and the journal replay decides.  No translation of an older index.
; host/store-node-host.lisp fn-store-sco-decode calls fn-sco-thaw-checked;
; fn-store-sco-select calls fn-sco-select-named.

(in-package "ACL2")
(include-book "store-checkpoint-open")

; The thawed checkpoint's index counts exactly its records.
(defun fn-sco-index-shape-okp (c)
  (declare (xargs :guard t))
  (equal (fn-cei-count (fn-sco-event-index c))
         (len (fn-sco-records c))))

; The decode's answer: (:ok C) with C the thawed checkpoint, or
; (:refused :index-shape).
(defun fn-sco-thaw-checked (f)
  (declare (xargs :guard t))
  (let ((c (fn-sco-thaw f)))
    (if (fn-sco-index-shape-okp c)
        (list :ok c)
      (list :refused :index-shape))))

; fn-sco-select with the refusal named.  Every other status is unchanged.
(defun fn-sco-select-named (status sequence count k)
  (declare (xargs :guard t))
  (if (eq status :index-shape)
      (list :full-replay :checkpoint-index-shape)
    (fn-sco-select status sequence count k)))

(defthm fn-sco-select-named-is-select-unless-index-shape
  (implies (not (eq status :index-shape))
           (equal (fn-sco-select-named status sequence count k)
                  (fn-sco-select status sequence count k))))

(defthm fn-sco-select-named-refuses-index-shape
  (equal (fn-sco-select-named :index-shape sequence count k)
         (list :full-replay :checkpoint-index-shape)))

; -----------------------------------------------------------------------------
; KEYSTONE: this image never refuses its own checkpoint.  The checkpoint
; every host open extends and publishes is fn-sco-extend of a capture
; (books/owner-checkpoint-open.lisp; host/store-node-host.lisp
; fn-store-sco-publish-octets writes fn-sco-freeze of it).  Its freeze
; thaws to a value that passes the shape test, whatever the configurations,
; prefix and suffix.

(local
 (defthm fn-sco-shape-of-extend-capture
   (fn-sco-index-shape-okp
    (fn-sco-extend (fn-sco-capture configs prefix) configs suffix))
   :hints (("Goal" :in-theory (enable fn-sco-extend fn-sco-capture
                                      fn-sco-make fn-sco-records
                                      fn-sco-event-index)))))

(local
 (defthm fn-sco-shapep-of-extend
   (implies (true-listp suffix)
            (fn-sco-shapep (fn-sco-extend c configs suffix)))
   :hints (("Goal" :in-theory (enable fn-sco-extend fn-sco-make fn-sco-records)))))

(defthm fn-sco-thaw-checked-accepts-own-publication
  (implies (true-listp suffix)
           (let ((c (fn-sco-extend (fn-sco-capture configs prefix) configs suffix)))
             (equal (fn-sco-thaw-checked (fn-sco-freeze c))
                    (list :ok c))))
  :hints (("Goal"
           :use ((:instance fn-sco-shapep-of-extend
                            (c (fn-sco-capture configs prefix)))
                 (:instance fn-sco-thaw-of-freeze
                            (c (fn-sco-extend (fn-sco-capture configs prefix)
                                              configs suffix)))
                 fn-sco-shape-of-extend-capture)
           :in-theory (e/d (fn-sco-thaw-checked)
                           (fn-sco-thaw fn-sco-freeze fn-sco-extend
                            fn-sco-capture fn-sco-index-shape-okp
                            fn-sco-thaw-of-freeze fn-sco-shapep
                            fn-sco-shapep-of-extend
                            fn-sco-shape-of-extend-capture)))))

(in-theory (disable fn-sco-index-shape-okp fn-sco-thaw-checked
                    fn-sco-select-named))
