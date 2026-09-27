; fn prototype (lane proto-adt, 2026-09-27): the invasiveness probe.  A real
; owner-state shape, the consumer-position entry table (books/consumer-
; position.lisp: `fn-cp-entry', `fn-cp-entriesp', O(consumers), capped by
; profile field 9), declared with `defadt' and nothing else.  NOT on a
; served path; no host calls it.
;
; The question is what happens to the existing theorems.  The declaration
; below makes the abstract stobj's logical value a true list of 8-element
; records (:entry consumer principal query qver view epoch ack): the very
; list `fn-cp-entriesp', `fn-cp-find', `fn-cp-remove' and every theorem
; about them already speak of.  So those theorems apply to the stobj's
; logical value UNCHANGED (they are about a variable); what a host-called
; function over the table needs is one bridge per stobj walk, below
; `cpent-find-from-is-fn-cp-find', after which an existing theorem is
; instantiated, not re-proved (`cpent-found-epoch-below-next').
;
; What does NOT carry over: the model's two table operations are a cons at
; the FRONT (register, rebase, ack) and `fn-cp-remove' by key (rebase, ack,
; unregister); the sequence constructor offers append at the back and
; update of a field in place.  See planning/evidence/proto-adt-2026-09-27.md.

(in-package "ACL2")
(include-book "adt")
(include-book "../consumer-position")

(defadt cpent
  (tag (:enum :entry))
  (consumer :octets) (principal :octets) (query :octets)
  (qver :u32) (view :u32) (epoch :u32) (ack :u32))

; The ADT type contains the model's well-formed tables: every table
; `fn-cp-entriesp' admits is a value of the abstract stobj.
(defthm cpent-octets-of-fn-cbor-octet-listp
  (implies (fn-cbor-octet-listp x) (adt-octetsp x))
  :hints (("Goal" :in-theory (enable fn-cbor-octetp))))

(defthm fn-cp-nth-is-nth
  (equal (fn-cp-nth n x) (nth n x))
  :hints (("Goal" :in-theory (enable nth))))

(local
 (defthm cpent-true-listp-len-0
   (implies (and (true-listp x) (equal (len x) 0)) (equal x nil))
   :rule-classes :forward-chaining))

; The epoch field is bounded by the TABLE's next epoch, not by the entry:
; `fn-cp-entryp' says (posp epoch) and epoch < next-epoch, and the u32
; bound comes from `fn-cp-statep' (next-epoch is a u32).  A dependent bound
; is a whole-state predicate over the logical value, not an ADT kind.
(defthm fn-cp-entryp-is-cpent-record
  (implies (and (fn-cp-entryp e frontier next-epoch) (fn-cp-uintp next-epoch))
           (adt-rec-p *cpent-schema* e))
  :hints (("Goal" :in-theory (enable adt-rec-p-open adt-schema-fns-of-atom
                                     adt-val-okp fn-cp-idp fn-cp-uintp nth))))

(defthm fn-cp-entriesp-is-cpentp
  (implies (and (fn-cp-entriesp entries frontier next-epoch) (fn-cp-uintp next-epoch))
           (cpentp entries))
  :hints (("Goal" :in-theory (disable fn-cp-entryp fn-cp-uintp adt-rec-p fn-cp-find)
           :induct (fn-cp-entriesp entries frontier next-epoch))))

(defthm fn-cp-statep-table-is-cpentp
  (implies (fn-cp-statep s) (cpentp (fn-cp-nth 5 s)))
  :hints (("Goal" :in-theory (disable fn-cp-entriesp fn-cp-nth-is-nth fn-cp-entriesp-is-cpentp)
           :use ((:instance fn-cp-entriesp-is-cpentp (entries (fn-cp-nth 5 s))
                            (frontier (fn-cp-nth 3 s)) (next-epoch (fn-cp-nth 4 s)))))))

; A host-side walk of the table, through the exports only: the first index
; whose consumer field is C.
(defun cpent-find-from (c i cpent)
  (declare (xargs :stobjs cpent
                  :guard (natp i)
                  :measure (nfix (- (cpent-count cpent) (nfix i)))))
  (if (and (natp i) (< i (cpent-count cpent)))
      (if (equal (cpent-get-consumer i cpent) c)
          i
        (cpent-find-from c (+ 1 i) cpent))
    nil))

(defthm cpent-find-from-bound
  (implies (cpent-find-from c i cpent)
           (and (natp (cpent-find-from c i cpent))
                (< (cpent-find-from c i cpent) (len cpent))))
  :rule-classes (:rewrite (:linear :corollary
                                   (implies (cpent-find-from c i cpent)
                                            (< (cpent-find-from c i cpent) (len cpent))))))

; Its one bridge: the record at the index it finds is the model's
; `fn-cp-find' over the logical value (and it finds nothing exactly when
; the model finds nothing), for any table of 8-field records.
(local
 (defthm cpent-nthcdr-open
   (implies (and (natp i) (< i (len x)))
            (and (consp (nthcdr i x))
                 (equal (car (nthcdr i x)) (nth i x))
                 (equal (cdr (nthcdr i x)) (nthcdr (+ 1 i) x))))
   :hints (("Goal" :in-theory (enable nth nthcdr)))))

(local
 (defthm cpent-nthcdr-past
   (implies (and (natp i) (<= (len x) i))
            (not (consp (nthcdr i x))))
   :hints (("Goal" :in-theory (enable nthcdr)))))

(defthm cpent-find-from-is-fn-cp-find
  (implies (natp i)
           (equal (if (cpent-find-from c i cpent)
                      (nth (cpent-find-from c i cpent) cpent)
                    nil)
                  (fn-cp-find c (nthcdr i cpent))))
  :hints (("Goal" :induct (cpent-find-from c i cpent)
           :in-theory (e/d (cpent$a-get-consumer) (cpentp-is-seq-p))
           :expand ((fn-cp-find c (nthcdr i cpent))))))

(defthm cpent-find-is-fn-cp-find
  (equal (if (cpent-find-from c 0 cpent)
             (nth (cpent-find-from c 0 cpent) cpent)
           nil)
         (fn-cp-find c cpent))
  :hints (("Goal" :use ((:instance cpent-find-from-is-fn-cp-find (i 0)))
           :in-theory (disable cpent-find-from-is-fn-cp-find))))

; An existing theorem, carried by instantiation: `fn-cp-find-epoch-less-next'
; (books/consumer-position.lisp), with no new induction.
(defthm cpent-found-epoch-below-next
  (implies (and (fn-cp-entriesp cpent frontier next-epoch)
                (cpent-find-from c 0 cpent))
           (< (nth 6 (nth (cpent-find-from c 0 cpent) cpent)) (nfix next-epoch)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-cp-find-epoch-less-next
                                   (consumer c) (entries cpent))
                        (:instance cpent-find-is-fn-cp-find))
           :in-theory (disable fn-cp-find-epoch-less-next cpent-find-is-fn-cp-find))))
