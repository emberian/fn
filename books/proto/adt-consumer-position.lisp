; fn prototype (lanes proto-adt and proto-adt-2, 2026-09-27): the
; invasiveness probe.  The consumer-position entry table (books/consumer-
; position.lisp: `fn-cp-entry', `fn-cp-entriesp', O(consumers), capped by
; profile field 9) declared with `defadt-keyed' and nothing else.  NOT on a
; served path; no host calls it.
;
; The first probe (lane proto-adt) declared the table as a sequence and
; found that the model's table operations -- a cons at the FRONT (register,
; rebase, ack) and `fn-cp-remove' by key (rebase, ack, unregister) -- were
; not the sequence's (append, update in place).  The keyed-set constructor
; closes that: its logical operations are the model's own shapes, so
;   fn-cp-find   = adt-kfind 1      (fn-cp-find-is-kfind, one induction)
;   fn-cp-remove = adt-kremove 1    (fn-cp-remove-is-kremove, one induction)
;   cons         = adt-kinsert :stack   (by definition)
; the model's well-formed tables are values of the abstract stobj
; (fn-cp-entriesp-is-cpentp), and the model's theorems carry to the stobj's
; exports by instantiation (section 3): nothing in consumer-position.lisp
; changes.  The model's rebase/ack table step, run on the columns
; (cpent-rebase), IS the model's (cons entry (fn-cp-remove consumer entries)).

(in-package "ACL2")
(include-book "adt-keyed")
(include-book "../consumer-position")
(local (include-book "arithmetic/top" :dir :system))

(defadt-keyed cpent :order :stack :key consumer
  (tag (:enum :entry))
  (consumer :octets) (principal :octets) (query :octets)
  (qver :u32) (view :u32) (epoch :u32) (ack :u32))

; -----------------------------------------------------------------------------
; 1. The model's table operations are the keyed set's logical operations.

(defthm fn-cp-nth-is-nth
  (equal (fn-cp-nth n x) (nth n x))
  :hints (("Goal" :in-theory (enable nth))))

(defthm fn-cp-find-is-kfind
  (equal (fn-cp-find c es) (adt-kfind 1 c es))
  :hints (("Goal" :in-theory (enable fn-cp-find))))

(defthm fn-cp-remove-is-kremove
  (equal (fn-cp-remove c es) (adt-kremove 1 c es))
  :hints (("Goal" :in-theory (enable fn-cp-remove))))

; -----------------------------------------------------------------------------
; 2. Every table the model admits is a value of the abstract stobj.  The
; epoch's u32 bound comes from the TABLE's next epoch (a whole-state
; predicate), which the entry recognizer does not carry by itself.

(defthm cpent-octets-of-fn-cbor-octet-listp
  (implies (fn-cbor-octet-listp x) (adt-octetsp x))
  :hints (("Goal" :in-theory (enable fn-cbor-octetp))))

(local
 (defthm cpent-true-listp-len-0
   (implies (and (true-listp x) (equal (len x) 0)) (equal x nil))
   :rule-classes :forward-chaining))

(local
 (defthm cpent-true-listp-atom
   (implies (and (true-listp x) (not (consp x))) (equal x nil))
   :rule-classes :forward-chaining))

; The model's entries come in two shapes since the Codex era: the eight
; fields above, or ten with the remote metadata (query groups, account) at
; 8 and 9 (books/consumer-position.lisp fn-cp-entryp).  A defadt-keyed
; record has one arity, so this pilot covers the eight-field tables: the
; hypothesis `cpent-eight-field-entriesp' says which, and a table with a
; remote-metadata entry is outside the pilot (deputy-1 fix-forward,
; 2026-10-01; a variable-arity record is a defadt limitation to record).
(defun cpent-eight-field-entriesp (es)
  (if (consp es)
      (and (equal (len (car es)) 8) (cpent-eight-field-entriesp (cdr es)))
    t))

(defthm fn-cp-entryp-is-cpent-record
  (implies (and (fn-cp-entryp e frontier next-epoch) (fn-cp-uintp next-epoch)
                (equal (len e) 8))
           (adt-rec-p *cpent-user-schema* e))
  :hints (("Goal" :in-theory (enable adt-rec-p-open adt-schema-fns-of-atom
                                     adt-val-okp fn-cp-idp fn-cp-uintp nth))))

(local
 (defthm cpent-kmem-when-kfind-nil
   (implies (and (not (adt-kfind 1 c es)) (true-list-listp es) (not (member-equal nil es)))
            (not (adt-kmem 1 c es)))
   :hints (("Goal" :in-theory (enable adt-kmem)))))

(local
 (defthm cpent-entriesp-shape
   (implies (fn-cp-entriesp es frontier next-epoch)
            (and (true-list-listp es) (not (member-equal nil es))))))

(defthm fn-cp-entriesp-is-cpentp
  (implies (and (fn-cp-entriesp entries frontier next-epoch) (fn-cp-uintp next-epoch)
                (cpent-eight-field-entriesp entries))
           (cpentp entries))
  :hints (("Goal" :in-theory (e/d (adt-kunique-cons) (fn-cp-entryp fn-cp-uintp adt-rec-p))
           :induct (fn-cp-entriesp entries frontier next-epoch))))

(defthm fn-cp-statep-table-is-cpentp
  (implies (and (fn-cp-statep s) (cpent-eight-field-entriesp (fn-cp-nth 5 s)))
           (cpentp (fn-cp-nth 5 s)))
  :hints (("Goal" :in-theory (disable fn-cp-entriesp fn-cp-nth-is-nth fn-cp-entriesp-is-cpentp)
           :use ((:instance fn-cp-entriesp-is-cpentp (entries (fn-cp-nth 5 s))
                            (frontier (fn-cp-nth 3 s)) (next-epoch (fn-cp-nth 4 s)))))))

; -----------------------------------------------------------------------------
; 3. Existing theorems, carried by instantiation (no new induction): each
; is the model's theorem at entries := the stobj's logical value.

(defthm cpent-found-epoch-below-next
  ; fn-cp-find-epoch-less-next
  (implies (and (fn-cp-entriesp cpent frontier next-epoch) (cpent-find c cpent))
           (< (nth 6 (cpent-find c cpent)) (nfix next-epoch)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-cp-find-epoch-less-next (consumer c) (entries cpent)))
           :in-theory (disable fn-cp-find-epoch-less-next))))

(defthm cpent-remove-keeps-entriesp
  ; fn-cp-entriesp-remove
  (implies (fn-cp-entriesp cpent frontier next-epoch)
           (fn-cp-entriesp (cpent-remove c cpent) frontier next-epoch))
  :hints (("Goal" :use ((:instance fn-cp-entriesp-remove (consumer c) (entries cpent)))
           :in-theory (disable fn-cp-entriesp-remove fn-cp-entriesp))))

(defthm cpent-find-after-remove-same
  ; fn-cp-find-after-remove-same
  (implies (fn-cp-entriesp cpent frontier next-epoch)
           (not (cpent-find c (cpent-remove c cpent))))
  :hints (("Goal" :use ((:instance fn-cp-find-after-remove-same (consumer c) (entries cpent)))
           :in-theory (disable fn-cp-find-after-remove-same fn-cp-entriesp))))

; -----------------------------------------------------------------------------
; 4. The model's rebase / ack table step, on the columns: remove the
; consumer's entry, cons the new one at the front.

(defun cpent-rebase (c e cpent)
  (declare (xargs :stobjs cpent
                  :guard (and (adt-rec-p *cpent-user-schema* e) (equal (nth 1 e) c))))
  (let ((cpent (cpent-remove c cpent)))
    (cpent-insert e cpent)))

(defthm cpent-rebase-is-the-model-step
  (equal (cpent-rebase c e cpent) (cons e (fn-cp-remove c cpent)))
  :hints (("Goal" :in-theory (enable adt-kinsert))))
