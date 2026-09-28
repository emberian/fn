; fn prototype (lane proto-adt-2, 2026-09-27): an O(config) real shape, the
; configuration's POLICY table (books/config.lisp: rows `fn-cfg-rowp' in
; slot `fn-cfg-policies' of the folded configuration value), declared with
; `defadt-keyed' and nothing else.  NOT on a served path; no host calls it.
;
; The table is keyed by the row's slot (row-a).  Its operations are the
; keyed set's, by one induction each:
;   fn-cfg-row-lookup       = adt-kfind 0              (the policy read)
;   fn-cfg-row-replace-key  = adt-kreplace :append 0   (:set-policy)
; so the model's theorems about them carry to the stobj's exports (section
; 3), including the set-policy keystone at the table level.
;
; What changed for the existing theorems: nothing in config.lisp or
; config-invariants.lisp.  What the ADT needs that the model does not state:
; unique slots (the keyed set's recognizer).  replace-key keeps it
; (adt-kunique-kreplace, the library's), so it is an invariant of every
; fold that starts from an empty table -- a theorem the model does not
; carry today (the value recognizer `fn-cfg-valuep' does not require it).

(in-package "ACL2")
(include-book "adt-keyed")
(include-book "../config-invariants")
(local (include-book "arithmetic/top" :dir :system))

(defadt-keyed cfpolicy :order :append :key slot
  (slot (:string)) (id (:string)) (c (:string)) (n :u32))

; -----------------------------------------------------------------------------
; 1. The model's table operations are the keyed set's.

(defthm fn-cfg-ag-car-is-nth-0
  (equal (fn-cfg-ag-car x) (nth 0 x))
  :hints (("Goal" :in-theory (enable nth fn-cfg-ag-car))))

(defthm fn-cfg-row-lookup-is-kfind
  (equal (fn-cfg-row-lookup rows a) (adt-kfind 0 a rows))
  :hints (("Goal" :in-theory (enable fn-cfg-row-lookup fn-cfg-row-a))))

(defthm fn-cfg-row-replace-key-is-kreplace
  (implies (true-listp rows)
           (equal (fn-cfg-row-replace-key rows row) (adt-kreplace :append 0 row rows)))
  :hints (("Goal" :in-theory (enable fn-cfg-row-replace-key fn-cfg-row-a adt-kreplace adt-kinsert
                                     adt-kmem))))

; -----------------------------------------------------------------------------
; 2. Every policy table with unique slots is a value of the abstract stobj.

(local
 (defthm cfpolicy-true-listp-len-0
   (implies (and (true-listp x) (equal (len x) 0)) (equal x nil))
   :rule-classes :forward-chaining))

(defthm fn-cfg-rowp-is-cfpolicy-record
  (implies (fn-cfg-rowp r) (adt-nval :ks *cfpolicy-nschema* r))
  :hints (("Goal" :in-theory (enable fn-cfg-rowp fn-cfg-row-shapep fn-cfg-row-a fn-cfg-row-b
                                     fn-cfg-row-c fn-cfg-row-n fn-cfg-labelp fn-record-ascii-stringp
                                     fn-record-uint32p fn-cfg-ag-cdr nth adt-val-okp))))

(defthm fn-cfg-row-listp-is-cfpolicy-seq
  (implies (fn-cfg-row-listp rows) (adt-nseq-p *cfpolicy-nschema* rows))
  :hints (("Goal" :in-theory (e/d (fn-cfg-row-listp) (fn-cfg-rowp adt-nval))
           :induct (fn-cfg-row-listp rows))))

(defthm fn-cfg-row-listp-true-listp
  (implies (fn-cfg-row-listp rows) (true-listp rows))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-cfg-row-listp))))

(defthm fn-cfg-row-listp-is-cfpolicyp
  (implies (and (fn-cfg-row-listp rows) (adt-kunique 0 rows))
           (cfpolicyp rows))
  :hints (("Goal" :in-theory (disable fn-cfg-row-listp adt-nseq-p))))

; -----------------------------------------------------------------------------
; 3. Existing theorems, carried by instantiation (no new induction).

(defthm cfpolicy-replace-looks-up-the-row
  ; fn-cfg-row-replace-key-looks-up-the-row
  (implies (cfpolicyp cfpolicy)
           (equal (cfpolicy-find (nth 0 row) (cfpolicy-replace row cfpolicy)) row))
  :hints (("Goal" :use ((:instance fn-cfg-row-replace-key-looks-up-the-row (rows cfpolicy)))
           :in-theory (e/d (fn-cfg-row-a) (fn-cfg-row-replace-key-looks-up-the-row)))))

(defthm cfpolicy-replace-keeps-row-listp
  ; fn-cfg-row-replace-key-preserves-row-listp
  (implies (and (fn-cfg-row-listp cfpolicy) (fn-cfg-rowp row))
           (fn-cfg-row-listp (cfpolicy-replace row cfpolicy)))
  :hints (("Goal" :use ((:instance fn-cfg-row-replace-key-preserves-row-listp (rows cfpolicy)))
           :in-theory (disable fn-cfg-row-replace-key-preserves-row-listp fn-cfg-row-listp fn-cfg-rowp))))

; The set-policy keystone at the table level: after the replace a slot's
; read is the value set last.
(defthm cfpolicy-set-policy-sets-the-policy
  (implies (cfpolicyp cfpolicy)
           (equal (cfpolicy-get-id slot (cfpolicy-replace (fn-cfg-row-make slot id "" 0) cfpolicy))
                  id))
  :hints (("Goal" :use ((:instance cfpolicy-replace-looks-up-the-row (row (fn-cfg-row-make slot id "" 0))))
           :in-theory (e/d (fn-cfg-row-make) (cfpolicy-replace-looks-up-the-row)))))
