; Serialization for the existing B lifecycle planner. This operation does not
; authorize a checkpoint: the producer must require its actual frozen-root/map
; builder completion. A checked recovery candidate is not that evidence.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "checkpoint")
(include-book "pool-ranges")
(include-book "layout-size-bounds")
(include-book "columns-guard-hints")
(include-book "owed")
(fn2-book-layer :b)
(defcodec-size-bounds fn2-format-checkpoint-installation)

(defun fn2-checkpoint-installation-member-capacity ()
 (declare (xargs :guard t))
 (+ 32 *fn2-format-txn-record-max-size* *fn2-format-checkpoint-installation-max-size*))

(defun fn2-checkpoint-member-hash (left at source slot gen okind oslot ogen fn2-checkpoint-bytes fn2-pool)
 (declare (xargs :stobjs (fn2-checkpoint-bytes fn2-pool) :measure (nfix left)
  :guard (and (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes) (fn2-pool-wfp fn2-pool)
              (natp left) (<= left 32) (natp at) (natp source)
              (<= (+ source left) (fn2-checkpoint-bytes-rows fn2-checkpoint-bytes)))))
 (if (zp left) (mv :ok fn2-pool)
  (mv-let (code fn2-pool)
   (fn2-pool-write slot gen at (fn2-checkpoint-bytes-value source fn2-checkpoint-bytes) okind oslot ogen fn2-pool)
   (if (not (eq code :ok)) (mv code fn2-pool)
    (fn2-checkpoint-member-hash (- left 1) (+ at 1) (+ source 1) slot gen okind oslot ogen fn2-checkpoint-bytes fn2-pool)))))
(fn2-pool-preserves fn2-checkpoint-member-hash
 (left at source slot gen okind oslot ogen fn2-checkpoint-bytes fn2-pool) :position 1
 :hints (("Goal" :in-theory (disable fn2-pool-write fn2-pool-rows))))
(in-theory (disable fn2-checkpoint-member-hash))

; One owned workspace, including 32 temporary digest bytes. Encode at offset32,
; then use the shared overlap-safe range primitive to move the complete framed
; member down to zero. Shrink fill only after that copy succeeds. The planner
; derives its containing batch; there is no caller-supplied commit/cut here.
(defun fn2-checkpoint-installation-pack-member (c base slot gen okind oslot ogen
                                              fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
                                              fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fields fn2-pool)
  :guard-hints ((fn2-columns-guard-hint
                 '(fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fields fn2-pool)
                 '(fn2-pool-reset fn2-pool-copy-range fn2-pool-truncate
                   fn2-checkpoint-member-hash fn2-format-checkpoint-installation-size)
                 nil world))
  :guard (and (fn2-checkpoints-wfp fn2-checkpoints) (fn2-checkpoint-refs-wfp fn2-checkpoint-refs)
              (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes) (fn2-fields-wfp fn2-fields)
              (fn2-pool-wfp fn2-pool))))
 (b* (((unless (and (fn2-checkpoint-slotp c fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)
                     (member-equal (fn2-checkpoints-state c fn2-checkpoints)
                       (list *fn2-checkpoint-state-checked* *fn2-checkpoint-state-installed* *fn2-checkpoint-state-promoted*))
                     (natp base) (<= (+ base *fn2-format-txn-record-num-fields*
                                            *fn2-format-checkpoint-installation-num-fields*) (fn2-fields-rows fn2-fields))
                     (unsigned-byte-p 32 slot) (< slot (fn2-pool-rows fn2-pool))
                     (unsigned-byte-p 60 gen) (unsigned-byte-p 8 okind)
                     (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen)
                     (<= (fn2-checkpoint-installation-member-capacity) (fn2-pool-cap slot fn2-pool))))
       (mv :bounds 0 fn2-fields fn2-pool))
      ((mv code fn2-pool) (fn2-pool-reset slot gen okind oslot ogen fn2-pool))
      ((unless (eq code :ok)) (mv code 0 fn2-fields fn2-pool))
      (r (* 6 c))
      ((mv code fn2-pool) (fn2-checkpoint-member-hash 32 0 (* 32 r) slot gen okind oslot ogen fn2-checkpoint-bytes fn2-pool))
      ((unless (eq code :ok)) (mv code 0 fn2-fields fn2-pool))
      (body (+ base *fn2-format-txn-record-num-fields*))
      (f (+ body *fn2-format-checkpoint-installation-field-descriptor-storage-domain*))
      (fn2-fields (fn2-fields-set-value (+ body *fn2-format-checkpoint-installation-field-checkpoint*) (fn2-checkpoints-checkpoint c fn2-checkpoints) fn2-fields))
      (fn2-fields (fn2-fields-set-value f (fn2-checkpoint-refs-storage-domain r fn2-checkpoint-refs) fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ f 1) (fn2-checkpoint-refs-physical-unit r fn2-checkpoint-refs) fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ f 2) (fn2-checkpoint-refs-writer-epoch r fn2-checkpoint-refs) fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ f 3) (fn2-checkpoint-refs-allocation r fn2-checkpoint-refs) fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ f 4) (fn2-checkpoint-refs-page-kind r fn2-checkpoint-refs) fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ f 5) (fn2-checkpoint-refs-encoded-length r fn2-checkpoint-refs) fn2-fields))
      (fn2-fields (fn2-fields-put (+ f 6) (value 1) (ref-slot slot) (ref-gen gen) (ref-off 0) (ref-len 32)))
      (bytes (fn2-format-checkpoint-installation-size body fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-format-txn-record-field-record-kind*) *record-kind-checkpoint-installation* fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-format-txn-record-field-length*) bytes fn2-fields))
      ((mv code next fn2-pool) (fn2-format-txn-record-encode base slot gen 32 okind oslot ogen fn2-fields fn2-pool))
      ((unless (eq code :ok)) (mv code 0 fn2-fields fn2-pool))
      ((mv code end fn2-pool) (fn2-format-checkpoint-installation-encode body slot gen next okind oslot ogen fn2-fields fn2-pool))
      ((unless (and (eq code :ok) (natp end) (<= 32 end) (unsigned-byte-p 32 end)))
       (mv :format 0 fn2-fields fn2-pool))
      (length (- end 32))
      ((mv code fn2-pool) (fn2-pool-copy-range slot gen 32 slot gen 0 length okind oslot ogen fn2-pool))
      ((unless (eq code :ok)) (mv code 0 fn2-fields fn2-pool))
      ((mv code fn2-pool) (fn2-pool-truncate slot gen length okind oslot ogen fn2-pool)))
  (mv code (if (eq code :ok) length 0) fn2-fields fn2-pool)))
; The served interface uses the actual stored guard, including all readonly
; input recognizers. The stronger off-guard FIELDS claim remains explicitly owed.
; New distinct served-domain interface. No old theorem is renamed/weakened.
(defcolumns-guarded-contracts fn2-checkpoint-installation-pack-member
 ; Pool preservation is independent of the copied values. Keep its branch
 ; tests opaque; the callee TYPE/WFP interfaces handle every return branch.
 :carriers ((fn2-fields 2 :prefix "-FIELDS")
            (fn2-pool 3 :prefix "-POOL"
             :hints ((fn2-columns-guard-hint
                      '(fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fields fn2-pool)
                      '(fn2-pool-reset fn2-pool-copy-range fn2-pool-truncate
                        fn2-checkpoint-member-hash fn2-format-checkpoint-installation-size
                        fn2-format-txn-record-encode fn2-format-checkpoint-installation-encode
                        fn2-checkpoint-slotp unsigned-byte-p integer-range-p natp member-equal)
                      '(fn2-checkpoint-installation-pack-member) world))))
 :hints ((append
          (fn2-columns-guard-hint
           '(fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fields fn2-pool)
           '(fn2-pool-reset fn2-pool-copy-range fn2-pool-truncate
             fn2-checkpoint-member-hash fn2-format-checkpoint-installation-size)
           '(fn2-checkpoint-installation-pack-member) world)
          '(:use (
   (:instance fn2-checkpoints-checkpoint-natp (i c))
   (:instance fn2-checkpoints-checkpoint-bound (i c))
   (:instance fn2-checkpoint-refs-storage-domain-natp (i (* 6 c)))
   (:instance fn2-checkpoint-refs-storage-domain-bound (i (* 6 c)))
   (:instance fn2-checkpoint-refs-physical-unit-natp (i (* 6 c)))
   (:instance fn2-checkpoint-refs-physical-unit-bound (i (* 6 c)))
   (:instance fn2-checkpoint-refs-writer-epoch-natp (i (* 6 c)))
   (:instance fn2-checkpoint-refs-writer-epoch-bound (i (* 6 c)))
   (:instance fn2-checkpoint-refs-allocation-natp (i (* 6 c)))
   (:instance fn2-checkpoint-refs-allocation-bound (i (* 6 c)))
   (:instance fn2-checkpoint-refs-page-kind-natp (i (* 6 c)))
   (:instance fn2-checkpoint-refs-page-kind-bound (i (* 6 c)))
   (:instance fn2-checkpoint-refs-encoded-length-natp (i (* 6 c)))
   (:instance fn2-checkpoint-refs-encoded-length-bound (i (* 6 c))))))))

; Preserve the other three original facets with their exact original H.
(make-event
 (let* ((world (w state)) (name 'fn2-checkpoint-installation-pack-member)
        (args (getpropc name 'formals :missing world))
        (inputs (getpropc name 'stobjs-in nil world))
        (outputs (getpropc name 'stobjs-out nil world))
        (carriers '((fn2-fields 2 :prefix "-FIELDS") (fn2-pool 3 :prefix "-POOL")))
        (hints '((fn2-columns-guard-hint
                  '(fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fields fn2-pool)
                  '(fn2-pool-reset fn2-pool-copy-range fn2-pool-truncate
                    fn2-checkpoint-member-hash fn2-format-checkpoint-installation-size)
                  '(fn2-checkpoint-installation-pack-member) world)))
        (hyps (fn2-columns-carrier-hyps carriers))
        (specs (fn2-columns-carrier-specs (fn2-columns-inherit-carrier-hints carriers hints)))
        (old (car (fn2-columns-preservation-facts name (cons name args) (list (car specs)) hyps nil)))
        (rest (fn2-columns-preserves (caar carriers) name args nil hyps (cdr specs)
                "-PRESERVES" t t hints t nil nil nil nil)))
  (if (or (eq args :missing)
          (not (fn2-columns-contract-carriersp carriers args inputs outputs world))
          (not (equal (caar specs) "-FIELDS-TYPE")))
      (er soft 'checkpoint-member-contract "Actual member carrier metadata changed.")
    (value
     `(progn
       (defthm-owed ,(cadr old) ,args ,(caddr old)
        :teeth (fn2-checkpoint-member-fields-type-positive-check
                fn2-checkpoint-member-fields-type-readonly-removal-check)
        :layer :b
        :doc "Original off-guard FIELDS-TYPE formula is unresolved, not proved or refuted. Guarded served-domain facts have distinct names. Evaluating diagnostic teeth are separately owed in the member unit.")
       ,@(cdr rest))))))
