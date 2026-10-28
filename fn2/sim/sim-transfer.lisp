; The simulated adapter. Physical effects occur at completion, never at take.
; The flight table retains descriptors, including generations, independently
; of the outstanding table. Early BorrowReleased saves the terminal payload:
; the later terminal never reads bytes whose ownership was already returned.
(in-package "ACL2")
(include-book "network")
(include-book "storage")
(include-book "prng")
(include-book "check")

(defun fn2-sim-input-kindp (kind)
  (declare (xargs :guard t))
  (or (equal kind *fn2-action-receive*) (equal kind *fn2-action-read*)
      (equal kind *fn2-action-entropy*)))
(defun fn2-sim-output-kindp (kind)
  (declare (xargs :guard t))
  (or (equal kind *fn2-action-send*) (equal kind *fn2-action-write*)))

(defthm fn2-sim-pool-read-byte-u8
  (implies (and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
           (unsigned-byte-p 8 (mv-nth 1 (fn2-pool-read slot gen i kind owner ogen fn2-pool))))
  :hints (("Goal" :in-theory (enable fn2-pool-read fn2-pool-rows))))

(defthm fn2-sim-pool-read-byte-natural
  (implies (and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
           (natp (mv-nth 1 (fn2-pool-read slot gen i kind owner ogen fn2-pool))))
  :rule-classes :type-prescription
  :hints (("Goal" :use fn2-sim-pool-read-byte-u8
           :in-theory (disable fn2-sim-pool-read-byte-u8))))
(defthm fn2-sim-pool-read-byte-bound
  (implies (and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
           (< (mv-nth 1 (fn2-pool-read slot gen i kind owner ogen fn2-pool)) 256))
  :rule-classes :linear
  :hints (("Goal" :use fn2-sim-pool-read-byte-u8
           :in-theory (disable fn2-sim-pool-read-byte-u8))))
(in-theory (disable fn2-storage-read-byte))
(defthm fn2-sim-storage-read-byte-natural
  (implies (and (fn2-sim-storagep s) (fn2-sim-storage-wfp s))
           (natp (mv-nth 1 (fn2-storage-read-byte address physical fault s))))
  :rule-classes :type-prescription
  :hints (("Goal" :use fn2-storage-read-byte-u8
           :in-theory (disable fn2-storage-read-byte-u8))))
(defthm fn2-sim-storage-read-byte-bound
  (implies (and (fn2-sim-storagep s) (fn2-sim-storage-wfp s))
           (< (mv-nth 1 (fn2-storage-read-byte address physical fault s)) 256))
  :rule-classes :linear
  :hints (("Goal" :use fn2-storage-read-byte-u8
           :in-theory (disable fn2-storage-read-byte-u8))))

; This byte loop is the adapter's only pool access. Input evidence is recorded
; from the source before the physical store, and output is fetched at this
; instant (not copied at issue). The independent OWN issue digest checks it.
(defun fn2-sim-transfer
  (kind cap nonce rslot rgen off len okind oslot ogen opslot opgen
        offset redirect stamp fua fault salt i
        fn2-pool fn2-sim-network fn2-sim-storage fn2-own)
  (declare (xargs :stobjs (fn2-pool fn2-sim-network fn2-sim-storage fn2-own)
                  :measure (nfix (- (nfix len) (nfix i)))
                  :guard (and (fn2-pool-wfp fn2-pool)
                              (fn2-sim-network-wfp fn2-sim-network)
                              (fn2-sim-storage-wfp fn2-sim-storage)
                              (fn2-own-wfp fn2-own)
                              (natp len) (natp i) (natp off)
                              (natp offset) (natp redirect)
                              (unsigned-byte-p 60 stamp) (unsigned-byte-p 60 rgen)
                              (unsigned-byte-p 32 salt))))
  (if (or (not (natp len)) (not (natp i)) (>= i len))
      (mv :ok (nfix i) fn2-pool fn2-sim-network fn2-sim-storage fn2-own)
    (b* (((mv code byte fn2-sim-network)
          (cond
           ((equal kind *fn2-action-receive*)
            (fn2-network-receive-byte cap nonce fn2-sim-network))
           ((equal kind *fn2-action-read*)
            (mv-let (code byte)
              (fn2-storage-read-byte (+ offset i) (+ redirect i)
                                     (if (equal fault 6) :io :none) fn2-sim-storage)
              (mv code byte fn2-sim-network)))
           ((equal kind *fn2-action-entropy*)
            (mv :ok (mod (fn2-prng-mix32 (fn2-u32 (+ salt i))) 256)
                fn2-sim-network))
           (t (mv-let (code byte)
                (fn2-pool-read rslot rgen (+ off i) okind oslot ogen fn2-pool)
                (mv code byte fn2-sim-network)))))
         ((when (not (eq code :ok)))
          (mv code i fn2-pool fn2-sim-network fn2-sim-storage fn2-own))
         ((mv code fn2-pool fn2-sim-network fn2-sim-storage fn2-own)
          (cond
           ((fn2-sim-input-kindp kind)
            (let ((fn2-own (fn2-own-record-input-byte-parts
                           rslot rgen (+ off i) byte fn2-pool fn2-own)))
              (mv-let (code fn2-pool)
                (fn2-pool-adapter-write rslot rgen opslot opgen (+ off i) byte fn2-pool)
                (mv code fn2-pool fn2-sim-network fn2-sim-storage fn2-own))))
           ((equal kind *fn2-action-send*)
            (mv-let (code fn2-sim-network)
              (fn2-network-send-byte cap nonce byte fn2-sim-network)
              (mv code fn2-pool fn2-sim-network fn2-sim-storage fn2-own)))
           (t
            (mv-let (code fn2-sim-storage)
              (fn2-storage-write-byte (+ offset i) (+ redirect i) byte stamp fua
                                      (if (equal fault 12) :no-space :none) fn2-sim-storage)
              (mv code fn2-pool fn2-sim-network fn2-sim-storage fn2-own)))))
         ((when (not (eq code :ok)))
          (mv code i fn2-pool fn2-sim-network fn2-sim-storage fn2-own)))
      (fn2-sim-transfer kind cap nonce rslot rgen off len okind oslot ogen opslot opgen
                        offset redirect stamp fua fault salt (+ 1 i)
                        fn2-pool fn2-sim-network fn2-sim-storage fn2-own))))

; Shape-only helper facts. The state represented by a byte image is not a
; refinement claim; no simulator keystone is asserted by these facts.
(defmacro fn2-sim-transfer-shape (state p wfp position typep)
  (let ((hyps '(and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
                    (fn2-sim-networkp fn2-sim-network) (fn2-sim-network-wfp fn2-sim-network)
                    (fn2-sim-storagep fn2-sim-storage) (fn2-sim-storage-wfp fn2-sim-storage)
                    (fn2-ownp fn2-own) (fn2-own-wfp fn2-own)
                    (natp len) (natp i) (natp off) (natp offset) (natp redirect)
                    (unsigned-byte-p 60 stamp) (unsigned-byte-p 60 rgen)
                    (unsigned-byte-p 32 salt)))
        (call `(mv-nth ,position
                 (fn2-sim-transfer kind cap nonce rslot rgen off len okind oslot ogen
                   opslot opgen offset redirect stamp fua fault salt i
                   fn2-pool fn2-sim-network fn2-sim-storage fn2-own))))
    `(defthm ,(fn2-columns-sym state (if typep "-TRANSFER-TYPE" "-TRANSFER-WFP"))
       (implies ,hyps (,(if typep p wfp) ,call)))))
(fn2-sim-transfer-shape fn2-pool fn2-poolp fn2-pool-wfp 2 t)
(fn2-sim-transfer-shape fn2-pool fn2-poolp fn2-pool-wfp 2 nil)
(fn2-sim-transfer-shape fn2-sim-network fn2-sim-networkp fn2-sim-network-wfp 3 t)
(fn2-sim-transfer-shape fn2-sim-network fn2-sim-networkp fn2-sim-network-wfp 3 nil)
(fn2-sim-transfer-shape fn2-sim-storage fn2-sim-storagep fn2-sim-storage-wfp 4 t)
(fn2-sim-transfer-shape fn2-sim-storage fn2-sim-storagep fn2-sim-storage-wfp 4 nil)
(fn2-sim-transfer-shape fn2-own fn2-ownp fn2-own-wfp 5 t)
(fn2-sim-transfer-shape fn2-own fn2-ownp fn2-own-wfp 5 nil)
(in-theory (disable fn2-sim-transfer))


(assert-event
 (fn2-profile-exports-compliant-p
  '(fn2-sim-input-kindp fn2-sim-output-kindp fn2-sim-transfer) (w state)))
