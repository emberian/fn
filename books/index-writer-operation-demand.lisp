; Finite actual writer operation census. Structural sizes are logical slots,
; never native octets. Runtime qualification and resource lowering are absent.
(in-package "ACL2")
(logic)
(include-book "snapshot-source-token")
(include-book "defrecord")

(defun fn-iwd-car (x) (declare (xargs :guard t)) (if (consp x) (car x) nil))
(defun fn-iwd-cdr (x) (declare (xargs :guard t)) (if (consp x) (cdr x) nil))

(fn-defrecord fn-iwd-operation
 :tag :writer-operation-census
 :constructor (fn-iwd-operation-make selector entry source tuples chunks
                                     traversal scalars retained costs)
 :fields ((fn-iwd-selector t) (fn-iwd-entry-name t) (fn-iwd-source t)
          (fn-iwd-tuples t) (fn-iwd-chunks t) (fn-iwd-traversal t)
          (fn-iwd-scalars t) (fn-iwd-retained t) (fn-iwd-costs t))
 :recognizer nil :car-fn fn-iwd-car :cdr-fn fn-iwd-cdr)

; The control test and case order are those of fn-ipa-writer-step, frozen
; in manifest 957dd74a... . This function neither runs nor authorizes a callee.
(defun fn-iwd-writer-entry (builder pending)
 (declare (xargs :guard t))
 (let ((phase (fn-omk-at 1 builder)) (control (fn-omk-at 18 builder)))
  (case phase
   (:arena-held 'fn-ibp-writer-assignment-begin)
   (:assigning 'fn-ibp-writer-assignment-one)
   (:numbers 'fn-ibp-writer-number-one)
   (:row-source 'fn-ibp-writer-row-source-one)
   (:layout
    (cond ((null control) 'fn-ibp-writer-row-source-begin)
          ((and (eq (fn-omk-at 6 pending) :rows)
                (eq (fn-omk-at 10 pending) :built)) 'fn-ipa-row-copy-one)
          ((and (eq (fn-omk-at 6 pending) :rows)
                (eq (fn-omk-at 10 pending) :copied)) 'fn-ipa-row-seal)
          ((and (eq (fn-omk-at 6 pending) :table)
                (eq (fn-omk-at 10 pending) :built)) 'fn-ipa-table-root-begin)
          (t :constructor-required)))
   (:row-root 'fn-ipa-row-root-one)
   (:table-layout
    (cond (pending 'fn-ipa-row-debt-transfer)
          ((eq (fn-omk-at 17 builder) :rows-shared) 'fn-ipa-table-layout-begin)
          (t 'fn-ipa-row-share-begin)))
   (:row-share 'fn-ipa-row-share-one)
   (:table-depth 'fn-ipa-table-depth-one)
   (:table-root 'fn-ipa-table-root-one)
   (:table-page-attached 'fn-ipa-table-page-advance)
   (:table-reinsert
    (if (equal control '(:table-reinsert 0 nil)) 'fn-ipa-reinsert-begin
      (case (fn-omk-at 2 control)
       ((:row-directory :table-directory) 'fn-ipa-reinsert-directory-one)
       (:row-read 'fn-ipa-reinsert-row-read)
       (:tag 'fn-ipa-reinsert-tag)
       (:place 'fn-ipa-reinsert-place-one)
       (otherwise :recovery-required))))
   (:table-seal 'fn-ipa-table-seal-one)
   (:ready :ready)
   (:recovery-required :recovery-required)
   (otherwise :unavailable))))

(defun fn-iwd-operation-entry (op builder pending)
 (declare (xargs :guard t))
 (case op
  (:generation-reserve 'fn-igr-reserve)
  (:generation-register 'fn-igr-register)
  (:page-reserve 'fn-ipa-reserve)
  (:page-register
   ; Frozen packet supplies fresh registration only. Recycled registration
   ; needs its joined old-stamp producer and is not silently priced as fresh.
   (if (eq (fn-omk-at 4 pending) :fresh) 'fn-ipa-register-fresh :unavailable))
  (:writer-step (fn-iwd-writer-entry builder pending))
  (:publish 'fn-ibp-writer-complete)
  (otherwise :unavailable)))

; Upper-path structural constructors only. UPDATE-NTH copies, generated
; default child images and all callee allocations belong to the cost closure.
(defun fn-iwd-tuple-sites (op)
 (declare (xargs :guard t))
 (case op
  (:generation-reserve '((:token 4 1) (:receipt 8 1) (:builder 20 1)))
  (:page-reserve '((:token 4 1) (:receipt 13 1)))
  (:page-register '((:token 4 1) (:page-owner 13 1)))
  (:publish '((:publication 19 1) (:installed-association 3 1)))
  (otherwise nil)))

(defun fn-iwd-traversal-domain (op builder pending depth capacity)
 (declare (xargs :guard (and (natp depth) (natp capacity))))
 (let ((new (fn-omk-at 2 builder)) (old (fn-omk-at 3 builder)))
  (case op
   (:generation-register
    (list :registered-generation depth capacity
          (fn-omk-at 3 (fn-omk-at 19 builder)) new
          '(create-fn-ibp-node-left create-fn-ibp-node-right
            create-fn-ibp-generation-segment)))
   (:page-register
    (list :registered-page-owner depth capacity (fn-omk-at 3 pending)
          '(create-fn-ibp-node-left create-fn-ibp-node-right
            create-fn-ibp-page-owner-segment)))
   (:publish
    ; New read+publish; an old generation adds read+current-reference drop.
    ; This is a traversal envelope, not a measured constructor request count.
    (list :publication-traversals depth capacity (if old 4 2) new old
          '(create-fn-ibp-node-left create-fn-ibp-node-right
            create-fn-ibp-generation-segment)))
   (otherwise
    (list :callee-closure-required depth capacity
          '(generated-child-defaults persistent-directory-copy shared-roots
            scalar-bignum-domain caller-frame first-use collector external control))))))

(defun fn-iwd-census (op pc builder pending depth capacity)
 (declare (xargs :guard (and (natp depth) (natp capacity))))
 (let ((entry (fn-iwd-operation-entry op builder pending)))
  (if (keywordp entry) (mv entry nil)
    (mv :census
     (fn-iwd-operation-make
      op entry
      ; NIL is an absent installed selector-domain coordinate, not authority.
      (list :operation-source
       "957dd74a4cba9c53e4a7d60124857b5fd874b6122ccb6a2520220ca33d09bf64" op nil)
      (fn-iwd-tuple-sites op)
      '((:table-words 2048 :u64) (:row-references 256 :retained)
        (:generation-rows 64 :retained) (:page-owner-rows 64 :retained))
      (fn-iwd-traversal-domain op builder pending depth capacity)
      ; Fixed-depth projections only; no Message-ID, groups or history scan.
      (list :carried-scalars (fn-omk-at 1 builder) (fn-omk-at 5 builder)
            (fn-omk-at 6 builder) (fn-omk-at 10 builder) (fn-omk-at 13 builder)
            (fn-omk-at 18 builder) (fn-omk-at 3 pending)
            (fn-omk-at 6 pending) (fn-omk-at 8 pending)
            (fn-omk-at 10 pending))
      (list :borrowed-retained pc (fn-omk-at 2 builder) (fn-omk-at 3 builder)
            (fn-omk-at 8 builder) (fn-omk-at 9 builder)
            (fn-omk-at 12 builder) (fn-omk-at 15 builder)
            (fn-omk-at 19 builder) pending)
      '(:primary :caller :first-use :collector :external :control
        :projection-control :retained-overlap :affine-lifetime :resource-components))))))

; Named action-derived nonresident contribution. These actual metadata
; actions perform no disk I/O, descriptor registration or worker creation.
; Reserve issues one process-local identity; resident demand remains absent.
(defun fn-iwd-resource-contribution (op)
 (declare (xargs :guard t))
 (if (member-eq op '(:generation-reserve :generation-register :page-reserve
                     :page-register :writer-step :publish))
     (list :resident-unavailable 0 0 0
           (if (member-eq op '(:generation-reserve :page-reserve)) 1 0))
   nil))

(defthm fn-iwd-writer-entry-fixed-projections-suffice
 (implies
  (and (equal (fn-omk-at 1 a) (fn-omk-at 1 b))
       (equal (fn-omk-at 18 a) (fn-omk-at 18 b))
       (equal (fn-omk-at 17 a) (fn-omk-at 17 b))
       (equal (fn-omk-at 6 p) (fn-omk-at 6 q))
       (equal (fn-omk-at 10 p) (fn-omk-at 10 q))
       (equal (not p) (not q)))
  (equal (fn-iwd-writer-entry a p) (fn-iwd-writer-entry b q)))
 :hints (("Goal" :in-theory (enable fn-iwd-writer-entry))))

; Family15/request5/role-table3 shape cannot establish installation or lower
; runtime request geometry to PRS5. The actual getters remain unavailable.
(defun fn-iwd-demand (census family role-table)
 (declare (xargs :guard t))
 (declare (ignore census family role-table))
 (mv :runtime-operation-unavailable nil))

(defthm fn-iwd-demand-never-issues-vector-by-definition
 (equal (fn-iwd-demand census family role-table)
        (mv :runtime-operation-unavailable nil)))
