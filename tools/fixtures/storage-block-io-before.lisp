(in-package "ACL2")
(defconst *unrelated-before* 3)
(defun fn2-block-issue-identity-events (names world)
 (declare (xargs :verify-guards nil))
 (if (atom names) nil
  (let* ((name (car names))
         (call (cons name (getpropc name 'formals nil world))))
   (if (not (fn2-issued-wrapper-ops-position name world))
       `((make-event (er soft 'fn2-block-issue-identity-events
                        "Unsupported issue identity ABI for ~x0." ',name)))
    (cons
     `(defthm ,(fn2-columns-sym name "-RESERVED-IDENTITY")
       (implies (equal (car ,call) :ok)
        (and (equal (mv-nth 1 ,call) (fn2-ops-free-head fn2-ops))
             (equal (mv-nth 2 ,call)
                    (fn2-ops-gen (fn2-ops-free-head fn2-ops) fn2-ops))))
       :hints (("Goal"
         ,@(and (eq name 'fn2-issue-children)
                '(:use ((:instance fn2-env-op-reserve-ok-facts (o fn2-ops)))))
         :in-theory (e/d (,name)
           (,@(and (not (eq name 'fn2-issue-children)) '(fn2-issue-children))
            fn2-op-reserve fn2-op-unreserve fn2-op-set-range
            fn2-op-set-capability fn2-op-set-storage fn2-op-set-cancel-target
            fn2-op-enqueue fn2-core-lease fn2-core-outbox-ready
            fn2-control-record-stop fn2-ops-free-head fn2-ops-gen)))))
     (fn2-block-issue-identity-events (cdr names) world))))))

(make-event
 (value (cons 'progn (fn2-block-issue-identity-events
          '(fn2-issue-children fn2-issue-read-children fn2-issue-write-children)
          (w state)))))

(defun fn2-pinned-block-io-children (writep pu epoch alloc off len lslot lgen boff okind oslot ogen principal
                                   fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control)
 (declare (xargs :stobjs (fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control)
                 :guard-hints
                 (("Goal" :in-theory
                   (e/d (fn2-alloc-handle-code fn2-alloc-slotp)
                    (fn2-ops-rows fn2-extents-rows fn2-alloc-edges-rows fn2-pool-rows
                     fn2-extentsp fn2-extents-wfp fn2-alloc-edgesp fn2-alloc-edges-wfp
                     fn2-poolp fn2-pool-wfp fn2-opsp fn2-ops-wfp
                     fn2-controlp fn2-control-wfp fn2-control-stop fn2-extents-state
                     fn2-ops-free-head fn2-ops-gen fn2-issue-read-children
                     fn2-issue-write-children fn2-alloc-edge-add fn2-b-read-pin-drop))))
                 :guard (and (fn2-extents-wfp fn2-extents) (fn2-alloc-edges-wfp fn2-alloc-edges)
                             (fn2-pool-wfp fn2-pool) (fn2-ops-wfp fn2-ops)
                             (fn2-control-wfp fn2-control))))
 (b* (((unless (and (booleanp writep) (unsigned-byte-p 32 boff) (natp pu) (natp off) (posp len) (<= (+ off len) *fn2-commit-unit-bytes*)
                    (unsigned-byte-p 60 epoch) (unsigned-byte-p 60 alloc)))
       (mv :bounds 0 0 fn2-pool fn2-ops fn2-control fn2-extents fn2-alloc-edges))
      (extent (floor pu *fn2-storage-extent-units*))
      (code (fn2-alloc-handle-code extent epoch alloc fn2-extents))
      ((unless (eq code :ok))
       (mv (if (eq code :bounds) :bounds :stale) 0 0 fn2-pool fn2-ops fn2-control fn2-extents fn2-alloc-edges))
      ; Published allocations are immutable. This entry constructs one full
      ; physical unit in a reserved allocation; publication uses the journal.
      ((when (and writep
                  (not (and (= off 0) (= len *fn2-commit-unit-bytes*)
                            (= (fn2-extents-state extent fn2-extents) *fn2-extent-state-reserved*)))))
       (mv :bounds 0 0 fn2-pool fn2-ops fn2-control fn2-extents fn2-alloc-edges))
      ; OP-RESERVE takes this head without interleaving. Acquire its pin before
      ; ISSUE can publish a descriptor; a normal refused issue drops the pin.
      (candidate (fn2-ops-free-head fn2-ops))
      ((unless (fn2-op-slotp candidate fn2-ops))
       (mv :exhausted 0 0 fn2-pool fn2-ops fn2-control fn2-extents fn2-alloc-edges))
      (generation (fn2-ops-gen candidate fn2-ops))
      ((mv pin fn2-extents fn2-alloc-edges)
       (fn2-alloc-edge-add (fn2-b-read-pin-edge candidate fn2-extents) generation
         extent epoch alloc :outstanding-io fn2-extents fn2-alloc-edges))
      ((unless (eq pin :ok))
       (let ((fn2-control (fn2-control-record-stop *fn2-stop-reason-issue-storage* fn2-control)))
        (mv :bounds 0 0 fn2-pool fn2-ops fn2-control fn2-extents fn2-alloc-edges)))
      ((mv code slot gen fn2-pool fn2-ops fn2-control)
       (if writep
           (fn2-issue-write-children (* pu *fn2-commit-unit-bytes*) lslot lgen boff len 0
                                    okind oslot ogen principal fn2-pool fn2-ops fn2-control)
         (fn2-issue-read-children (+ (* pu *fn2-commit-unit-bytes*) off) lslot lgen len okind oslot ogen principal
                                  fn2-pool fn2-ops fn2-control)))
      ((when (eq code :ok))
       (if (and (equal slot candidate) (equal gen generation))
           (mv :ok slot gen fn2-pool fn2-ops fn2-control fn2-extents fn2-alloc-edges)
         (let ((fn2-control (fn2-control-record-stop *fn2-stop-reason-issue-storage* fn2-control)))
          (mv :bounds slot gen fn2-pool fn2-ops fn2-control fn2-extents fn2-alloc-edges))))
      ; An uncertain/partially issued operation keeps its protection for
      ; recovery. Only an ordinary refusal before publication rolls it back.
      ((when (= (fn2-control-stop fn2-control) 1))
       (mv :bounds slot gen fn2-pool fn2-ops fn2-control fn2-extents fn2-alloc-edges))
      ((mv drop fn2-extents fn2-alloc-edges)
       (fn2-b-read-pin-drop candidate generation fn2-extents fn2-alloc-edges))
      (fn2-control (if (eq drop :ok) fn2-control
                     (fn2-control-record-stop *fn2-stop-reason-issue-storage* fn2-control))))
  (mv (if (eq code :exhausted) :exhausted :bounds) slot gen
      fn2-pool fn2-ops fn2-control fn2-extents fn2-alloc-edges)))

(encapsulate ()
 ; Carrier WFP specs supply their own hints; the shared opaque theory must
 ; surround the whole generated family, not only its TYPE theorem hints.
 (local (in-theory (disable
   fn2-ops-rows fn2-extents-rows fn2-alloc-edges-rows fn2-pool-rows
   fn2-extentsp fn2-extents-wfp fn2-alloc-edgesp fn2-alloc-edges-wfp
   fn2-poolp fn2-pool-wfp fn2-opsp fn2-ops-wfp fn2-controlp fn2-control-wfp
   fn2-control-stop fn2-extents-state fn2-ops-free-head fn2-ops-gen
   fn2-issue-read-children fn2-issue-write-children fn2-alloc-edge-add
   fn2-b-read-pin-drop fn2-b-read-pin-edge fn2-alloc-handle-code
   fn2-control-record-stop)))
(fn2-pool-preserves fn2-pinned-block-io-children (writep pu epoch alloc off len lslot lgen boff okind oslot ogen principal
                                             fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control)
  :carriers ((fn2-pool 3 :prefix "-POOL") (fn2-ops 4 :prefix "-OPS") (fn2-control 5 :prefix "-CONTROL")
             (fn2-extents 6 :prefix "-EXTENTS") (fn2-alloc-edges 7 :prefix "-EDGES")))
(assert-event
 (equal (getpropc 'fn2-pinned-block-io-children 'stobjs-out nil (w state))
        '(nil nil nil fn2-pool fn2-ops fn2-control fn2-extents fn2-alloc-edges)))
; Prove the owning eight-result primitive before closing it. These shared
; producers bind the operation carrier from its actual ABI (position 4), and
; retain the original queue/history equations on success and every refusal.
 (make-event
  (value (cons 'progn
   (append
    (fn2-block-issue-identity-events '(fn2-pinned-block-io-children) (w state))
    (fn2-issue-wrapper-effect-events '(fn2-pinned-block-io-children) (w state))
    (fn2-issued-wrapper-events '(fn2-pinned-block-io-children) (w state)))))))

(in-theory (disable fn2-pinned-block-io-children))

(defun fn2-block-read-children (pu epoch alloc off len lslot lgen okind oslot ogen principal
                                   fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control)
 (declare (xargs :stobjs (fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control)
                 :guard (and (fn2-extents-wfp fn2-extents) (fn2-alloc-edges-wfp fn2-alloc-edges)
                             (fn2-pool-wfp fn2-pool) (fn2-ops-wfp fn2-ops)
                             (fn2-control-wfp fn2-control))))
 (fn2-pinned-block-io-children nil pu epoch alloc off len lslot lgen 0 okind oslot ogen principal
                              fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control))

(fn2-pool-preserves fn2-block-read-children (pu epoch alloc off len lslot lgen okind oslot ogen principal
                                             fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control)
  :carriers ((fn2-pool 3 :prefix "-POOL") (fn2-ops 4 :prefix "-OPS") (fn2-control 5 :prefix "-CONTROL")
             (fn2-extents 6 :prefix "-EXTENTS") (fn2-alloc-edges 7 :prefix "-EDGES")))

(defun fn2-block-write-children (pu epoch alloc off len lslot lgen boff okind oslot ogen principal
                                   fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control)
 (declare (xargs :stobjs (fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control)
                 :guard (and (fn2-extents-wfp fn2-extents) (fn2-alloc-edges-wfp fn2-alloc-edges)
                             (fn2-pool-wfp fn2-pool) (fn2-ops-wfp fn2-ops)
                             (fn2-control-wfp fn2-control))))
 (fn2-pinned-block-io-children t pu epoch alloc off len lslot lgen boff okind oslot ogen principal
                              fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control))

(fn2-pool-preserves fn2-block-write-children (pu epoch alloc off len lslot lgen boff okind oslot ogen principal
                                             fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control)
  :carriers ((fn2-pool 3 :prefix "-POOL") (fn2-ops 4 :prefix "-OPS") (fn2-control 5 :prefix "-CONTROL")
             (fn2-extents 6 :prefix "-EXTENTS") (fn2-alloc-edges 7 :prefix "-EDGES")))

(make-event
 (value (cons 'progn
   (append (fn2-issue-wrapper-effect-events '(fn2-block-read-children fn2-block-write-children) (w state))
           (fn2-issued-wrapper-events '(fn2-block-read-children fn2-block-write-children) (w state))))))
(defun unrelated-reserve (x) x)
(defcost fn2-block-read :child fn2-block-read-children :doc "Retained registry cost.")
(defcost fn2-block-write :child fn2-block-write-children :doc "Retained registry cost.")
