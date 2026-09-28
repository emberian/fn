; fn prototype (lane proto-adt-2, 2026-09-27): a third real shape, O(signed
; articles): the topic projection's ACCEPTED signed statements (slot 3 of
; `fn-th-prefix-state', books/topic-history-prefix.lisp; entries
; `fn-stxa-p', books/stx-accept-records.lisp), the next-largest piece of the
; opened owner state after the history (lane snapshot-open-2 section 4:
; 1.90 M conses at 40k records, the statements' octets as LISTS).
; Declared with `defadt-keyed' and nothing else; NOT on a served path.
;
; An entry: four uint32s, four octet strings (the article record and the
; verdict event are the large ones, now pool slices), authored-source
; (:legacy or octets: a sum, (:alt :legacy (:octets))) and authored-id (an
; option).  The table is consed at the front (:stack) and looked up by the
; derived reference (sequence txid authored-id sequence keyring-generation
; profile), first match (`fn-th-prefix-find-ref').
;
; What changed for the model: the lookup is by the sequence, then the rest
; of the reference is compared exactly (`stxa-find-ref'), which IS
; `fn-th-prefix-find-ref' on every table whose entries are all `fn-stxa-p'
; and whose sequences are unique (fn-th-prefix-find-ref-is-by-sequence).
; The model states neither: find-ref skips non-stxa entries and takes the
; first of any duplicates.  Both are true of the fold that builds the table
; (a step conses only an `fn-hstxa-stxa' of a checked event, and a
; sequence is the Store's) but no theorem says so today: that is the open
; obligation this shape exposes.

(in-package "ACL2")
(include-book "adt-topic-accepted-type")
(include-book "../topic-history-prefix")
(local (include-book "arithmetic/top" :dir :system))


; -----------------------------------------------------------------------------
; 1. Every accepted statement is a record of the ADT.

(defthm stxa-octets-of-fn-cbor-octet-listp
  (implies (fn-cbor-octet-listp x) (adt-octetsp x))
  :hints (("Goal" :in-theory (enable fn-cbor-octetp))))

(local
 (defthm stxa-true-listp-len-0
   (implies (and (true-listp x) (equal (len x) 0)) (equal x nil))
   :rule-classes :forward-chaining))

(defthm fn-stxa-p-is-stxa-record
  (implies (fn-stxa-p e) (adt-nval :ks *stxa-nschema* e))
  :hints (("Goal" :in-theory (enable fn-stxa-p fn-stxa-internals fn-ag-car fn-ag-cdr
                                     fn-record-uint32p fn-stxe-bounded-octetsp adt-val-okp nth))))

; -----------------------------------------------------------------------------
; 2. The lookup: by the sequence, then the reference compared exactly.

(defun stxa-all-p (a)
  (declare (xargs :guard t))
  (if (atom a) t (and (fn-stxa-p (car a)) (stxa-all-p (cdr a)))))

(defthm fn-th-auth-ref-of-first
  (equal (car (fn-th-auth-ref-of e)) (nth 0 e))
  :hints (("Goal" :in-theory (enable fn-th-auth-ref-of fn-stxa-internals fn-ag-car nth))))

(defthm fn-th-prefix-find-ref-is-by-sequence
  (implies (and (stxa-all-p a) (adt-kunique 0 a))
           (equal (fn-th-prefix-find-ref ref a)
                  (let ((e (adt-kfind 0 (car ref) a)))
                    (if (and (consp e) (equal (fn-th-auth-ref-of e) ref)) e nil))))
  :hints (("Goal" :in-theory (e/d (fn-th-prefix-find-ref adt-kmem adt-kunique) (fn-th-auth-ref-of))
           :induct (fn-th-prefix-find-ref ref a))
          ("Subgoal *1/2" :use ((:instance fn-th-auth-ref-of-first (e (car a)))))
          ("Subgoal *1/1" :use ((:instance fn-th-auth-ref-of-first (e (car a)))))))

; The lookup on the columns.
(defun stxa-find-ref (ref stxa)
  (declare (xargs :stobjs stxa
                  :guard (and (consp ref) (unsigned-byte-p 32 (car ref)))
                  :guard-hints (("Goal" :in-theory (enable adt-val-okp)))))
  (let ((e (stxa-find (car ref) stxa)))
    (if (and (consp e) (equal (fn-th-auth-ref-of e) ref)) e nil)))

(defthm stxa-find-ref-is-the-model-lookup
  (implies (and (stxa-all-p stxa) (stxap stxa))
           (equal (stxa-find-ref ref stxa) (fn-th-prefix-find-ref ref stxa))))

; The accept step conses at the front: the ADT's insert.
(defthm stxa-insert-is-cons
  (equal (stxa-insert r stxa) (cons r stxa))
  :hints (("Goal" :in-theory (enable adt-kinsert))))
