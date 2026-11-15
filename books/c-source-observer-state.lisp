; Source observations are ephemeral actor-owned leases. A pending writer
; closes new admissions before waiting, so replacement cannot starve behind
; a stream of new readers. These are not disk durability/lifetime promises.
(in-package "ACL2")
(include-book "core-children")
(include-book "machines-directory")
(fn2-book-layer :c)
(defcolumns fn2-c-source-control
 ((phase (:enum fn2-c-source-writer-phase (:idle :pending :exclusive :uncertain)))
  (readers :u32) (serial :u60) (writer-kind :u8) (writer-id :u32) (writer-gen :u60)))
(defcolumns fn2-c-source-observers ((live :bool) (kind :u8) (generation :u60)))
(defcorechild fn2-core-c-source-control fn2-c-source-control
 :init (fn2-c-source-control-init 1 fn2-c-source-control) :profilep t
 :why "One writer-preference source publication session remains closed across replacement and uncertainty.")
(defcorechild fn2-core-c-source-observers fn2-c-source-observers
 :init (fn2-c-source-observers-init (fn2-machine-index-count profile) fn2-c-source-observers)
 :profilep (unsigned-byte-p 32 (fn2-machine-index-count profile))
 :why "Each actual global actor id retains its exact generation-bound source observation until copied or cancelled.")
