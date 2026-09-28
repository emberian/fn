; fn prototype (lane proto-adt-2, 2026-09-27): an O(groups) real shape, the
; configuration's GROUP table (books/config.lisp: entries
; `fn-cfg-group-entryp' in slot `fn-cfg-groups' of the folded configuration
; value), declared with `defadt-keyed' and nothing else.  NOT on a served
; path; no host calls it.
;
; An entry is (name created-gen created-stamp retired-gen policy-id next):
; a string key, a nested product (the clock stamp, a tagged 5-list), an
; option (retired-gen: nil or a uint32), a string, and two uint32s.  The
; table's operations are the keyed set's:
;   fn-cfg-group-find       = adt-kfind 0         (arguments swapped)
;   fn-cfg-group-all-names  = adt-keys 0
;   fn-cfg-groups-create    = adt-kreplace :append 0 of the revived entry
;   fn-cfg-groups-retire    = adt-kreplace-found 0 of the entry, retired
; and the two table steps run on the columns (cfgroup-create,
; cfgroup-retire) ARE the model's steps.  The model's uniqueness of names
; (`fn-cfg-no-duplicate-namesp', part of `fn-cfg-valuep') is the keyed
; set's `adt-kunique'.  Nothing in config.lisp changes.

(in-package "ACL2")
(include-book "adt-keyed")
(include-book "../config-invariants")
(local (include-book "arithmetic/top" :dir :system))

(defadt-keyed cfgroup :order :append :key name
  (name (:string))
  (created-gen :u32)
  (created-stamp (:prod (:enum :fn-clock-observation) (:u64) (:u64) (:u64) (:bool)))
  (retired-gen (:alt nil (:u32)))
  (policy-id (:string))
  (next :u32))

; -----------------------------------------------------------------------------
; 1. The model's table operations are the keyed set's.

(defthm fn-cfg-ag-car-is-nth-0-g
  (equal (fn-cfg-ag-car x) (nth 0 x))
  :hints (("Goal" :in-theory (enable nth fn-cfg-ag-car))))

(defthm fn-cfg-ag-cdr-is-cdr
  (equal (fn-cfg-ag-cdr x) (cdr x))
  :hints (("Goal" :in-theory (enable fn-cfg-ag-cdr))))

(defthm fn-cfg-group-find-is-kfind
  (equal (fn-cfg-group-find es name) (adt-kfind 0 name es))
  :hints (("Goal" :in-theory (enable fn-cfg-group-find fn-cfg-group-name))))

(defthm fn-cfg-group-all-names-is-keys
  (equal (fn-cfg-group-all-names es) (adt-keys 0 es))
  :hints (("Goal" :in-theory (enable fn-cfg-group-all-names fn-cfg-group-name))))

(defthm fn-cfg-member-namep-is-member
  (iff (fn-cfg-member-namep x names) (member-equal x names))
  :hints (("Goal" :in-theory (enable fn-cfg-member-namep))))

(defthm fn-cfg-no-duplicate-namesp-is-no-dups
  (equal (fn-cfg-no-duplicate-namesp names) (no-duplicatesp-equal names))
  :hints (("Goal" :in-theory (enable fn-cfg-no-duplicate-namesp))))

(defthm fn-cfg-groups-create-is-kreplace
  (implies (true-listp es)
           (equal (fn-cfg-groups-create es gen stamp name policy)
                  (adt-kreplace :append 0
                                (list name gen stamp nil policy
                                      (if (adt-kmem 0 name es) (nth 5 (adt-kfind 0 name es)) 0))
                                es)))
  :hints (("Goal" :in-theory (enable fn-cfg-groups-create fn-cfg-group-make fn-cfg-group-name
                                     fn-cfg-group-next adt-kreplace adt-kinsert adt-kmem nth))))

(defthm adt-key-of-kfind
  (implies (adt-kmem j k a) (equal (nth j (adt-kfind j k a)) k))
  :hints (("Goal" :in-theory (enable adt-kmem))))

(defthm adt-car-of-kfind-0
  (implies (member-equal k (adt-keys 0 a)) (equal (car (adt-kfind 0 k a)) k)))

(local
 (defthm cfgroup-true-listp-len-0
   (implies (and (true-listp x) (equal (len x) 0)) (equal x nil))
   :rule-classes :forward-chaining))

(defun cfgroup-retired (gen e)
  ; entry E with retired-gen GEN (fn-cfg-groups-retire's rebuilt entry)
  (declare (xargs :guard (true-listp e)))
  (list (nth 0 e) (nth 1 e) (nth 2 e) gen (nth 4 e) (nth 5 e)))

(defthm fn-cfg-groups-retire-is-kreplace-found
  (implies (true-listp es)
           (equal (fn-cfg-groups-retire es gen name)
                  (if (adt-kmem 0 name es)
                      (adt-kreplace-found 0 (cfgroup-retired gen (adt-kfind 0 name es)) es)
                    es)))
  :hints (("Goal" :in-theory (enable fn-cfg-groups-retire fn-cfg-group-make fn-cfg-group-name
                                     fn-cfg-group-created-gen fn-cfg-group-created-stamp
                                     fn-cfg-group-policy-id fn-cfg-group-next adt-kmem))))

; -----------------------------------------------------------------------------
; 2. Every model table is a value of the abstract stobj.

(defthm fn-cfg-group-entryp-is-cfgroup-record
  (implies (fn-cfg-group-entryp e) (adt-nval :ks *cfgroup-nschema* e))
  :hints (("Goal" :in-theory (enable fn-cfg-group-entryp fn-cfg-group-shapep fn-cfg-group-name
                                     fn-cfg-group-created-gen fn-cfg-group-created-stamp
                                     fn-cfg-group-retired-gen fn-cfg-group-policy-id fn-cfg-group-next
                                     fn-cfg-stampp fn-clock-observationp fn-clock-observation-shapep
                                     fn-clock-monotonic fn-clock-wall fn-clock-wall-error
                                     fn-clock-has-wall fn-record-group-namep fn-record-ascii-stringp
                                     fn-cfg-labelp fn-record-uint32p fn-clock-timep adt-val-okp nth))))

(defthm fn-cfg-group-listp-is-cfgroup-seq
  (implies (fn-cfg-group-listp es) (adt-nseq-p *cfgroup-nschema* es))
  :hints (("Goal" :in-theory (e/d (fn-cfg-group-listp) (fn-cfg-group-entryp adt-nval))
           :induct (fn-cfg-group-listp es))))

(defthm fn-cfg-group-table-is-cfgroupp
  ; the value recognizer's two conjuncts about the group table
  (implies (and (fn-cfg-group-listp es)
                (fn-cfg-no-duplicate-namesp (fn-cfg-group-all-names es)))
           (cfgroupp es))
  :hints (("Goal" :in-theory (e/d (adt-kunique) (fn-cfg-group-listp adt-nseq-p)))))

; -----------------------------------------------------------------------------
; 3. The model's two table steps, on the columns.

(defthm adt-consp-when-nval-ks
  (implies (and (adt-nval :ks s r) (consp s)) (consp r))
  :hints (("Goal" :expand ((adt-nval :ks s r)))))

(defthm cfgroup-kfind-consp
  (implies (and (adt-nseq-p *cfgroup-nschema* a) (member-equal k (adt-keys 0 a)))
           (consp (adt-kfind 0 k a)))
  :hints (("Goal" :in-theory (disable adt-nval))))

(defun cfgroup-create (gen stamp name policy cfgroup)
  ; create-group's table step: revive NAME in place keeping its watermark,
  ; else append it
  (declare (xargs :stobjs cfgroup
                  :guard (and (stringp name) (stringp policy) (unsigned-byte-p 32 gen)
                              (adt-nval :k '(:prod (:enum :fn-clock-observation) (:u64) (:u64) (:u64) (:bool))
                                        stamp))
                  :guard-hints (("Goal" :use ((:instance adt-nseq-p-kfind (s *cfgroup-nschema*)
                                                         (j 0) (k name) (a cfgroup)))
                                 :in-theory (e/d (adt-val-okp) (adt-nseq-p-kfind))))))
  (let ((e (cfgroup-find name cfgroup)))
    (cfgroup-replace (list name gen stamp nil policy (if e (nth 5 e) 0)) cfgroup)))

(defthm cfgroup-create-is-the-model-step
  (implies (cfgroupp cfgroup)
           (equal (cfgroup-create gen stamp name policy cfgroup)
                  (fn-cfg-groups-create cfgroup gen stamp name policy)))
  :hints (("Goal" :in-theory (e/d (adt-kmem) (cfgroup-kfind-consp))
           :use ((:instance cfgroup-kfind-consp (a cfgroup) (k name))))))

(defun cfgroup-retire (gen name cfgroup)
  ; retire-group's table step: set retired-gen, keep the rest
  (declare (xargs :stobjs cfgroup
                  :guard (and (stringp name) (unsigned-byte-p 32 gen))
                  :guard-hints (("Goal" :use ((:instance adt-nseq-p-kfind (s *cfgroup-nschema*)
                                                         (j 0) (k name) (a cfgroup)))
                                 :in-theory (e/d (adt-val-okp) (adt-nseq-p-kfind))))))
  (let ((e (cfgroup-find name cfgroup)))
    (if e (cfgroup-replace (cfgroup-retired gen e) cfgroup) cfgroup)))

(defthm cfgroup-retire-is-the-model-step
  (implies (cfgroupp cfgroup)
           (equal (cfgroup-retire gen name cfgroup)
                  (fn-cfg-groups-retire cfgroup gen name)))
  :hints (("Goal" :in-theory (enable adt-kreplace adt-kmem))))

; -----------------------------------------------------------------------------
; 4. Existing theorems, carried by instantiation (no new induction).

(defthm cfgroup-retire-keeps-the-names
  ; fn-cfg-groups-retire-keeps-the-names
  (implies (cfgroupp cfgroup)
           (equal (adt-keys 0 (cfgroup-retire gen name cfgroup)) (adt-keys 0 cfgroup)))
  :hints (("Goal" :use ((:instance fn-cfg-groups-retire-keeps-the-names (es cfgroup)))
           :in-theory (disable fn-cfg-groups-retire-keeps-the-names cfgroup-retire))))

(defthm cfgroup-create-keeps-the-names-or-adds-one
  ; fn-cfg-groups-create-keeps-the-names-or-adds-one
  (implies (and (cfgroupp cfgroup) (fn-cfg-group-listp cfgroup))
           (equal (adt-keys 0 (cfgroup-create gen stamp name policy cfgroup))
                  (if (consp (cfgroup-find name cfgroup))
                      (adt-keys 0 cfgroup)
                    (append (adt-keys 0 cfgroup) (list name)))))
  :hints (("Goal" :use ((:instance fn-cfg-groups-create-keeps-the-names-or-adds-one (es cfgroup)))
           :in-theory (disable fn-cfg-groups-create-keeps-the-names-or-adds-one cfgroup-create
                               fn-cfg-groups-create-is-kreplace))))

(defthm cfgroup-create-resumes-the-watermark
  ; fn-cfg-groups-create-resumes-the-watermark
  (implies (and (cfgroupp cfgroup) (consp (cfgroup-find name cfgroup)))
           (equal (cfgroup-get-next name (cfgroup-create gen stamp name policy cfgroup))
                  (cfgroup-get-next name cfgroup)))
  :hints (("Goal" :use ((:instance fn-cfg-groups-create-resumes-the-watermark (es cfgroup)))
           :in-theory (e/d (fn-cfg-group-next) (fn-cfg-groups-create-resumes-the-watermark cfgroup-create)))))
