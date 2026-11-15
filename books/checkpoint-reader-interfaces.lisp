; Named interfaces over the current checkpoint/format implementation.
; Matching donor bodies do not transfer certification to this closure.
(in-package "ACL2")
(include-book "checkpoint")
(include-book "columns-guard-hints")
(fn2-book-layer :b)

(fn2-fields-preserves fn2-checkpoint-decode
 (base slot gen off len okind oslot ogen fn2-fields fn2-pool) :position 1 :prefix "-FIELDS-ONLY" :raw-rows t
 :hints (("Goal" :in-theory (e/d (fn2-checkpoint-decode)
                                 (fn2-format-checkpoint-descriptor-decode fn2-fields-rows fn2-fields-value)))))

(defthm fn2-checkpoint-decode-fields-domain-value-type
 (implies
  (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
       (natp i) (< i (fn2-fields-rows fn2-fields)))
  (unsigned-byte-p 60
   (fn2-fields-value i
    (mv-nth 1 (fn2-checkpoint-decode base slot gen off len okind oslot ogen fn2-fields fn2-pool)))))
 :hints (("Goal"
  :use ((:instance fn2-fields-value-natp
          (fn2-fields (mv-nth 1 (fn2-checkpoint-decode base slot gen off len okind oslot ogen fn2-fields fn2-pool))))
        (:instance fn2-fields-value-bound
          (fn2-fields (mv-nth 1 (fn2-checkpoint-decode base slot gen off len okind oslot ogen fn2-fields fn2-pool)))))
  :in-theory (disable fn2-checkpoint-decode fn2-fields-value fn2-fields-rows))))

(defthm fn2-checkpoint-decode-fields-domain-value-integer
 (implies
  (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
       (natp i) (< i (fn2-fields-rows fn2-fields)))
  (integerp
   (fn2-fields-value i
    (mv-nth 1 (fn2-checkpoint-decode base slot gen off len okind oslot ogen fn2-fields fn2-pool)))))
 :hints (("Goal"
  :use ((:instance fn2-fields-value-natp
          (fn2-fields (mv-nth 1 (fn2-checkpoint-decode base slot gen off len okind oslot ogen fn2-fields fn2-pool)))))
  :in-theory (disable fn2-checkpoint-decode fn2-fields-value fn2-fields-rows))))

(fn2-fields-preserves fn2-format-run
 (kind sealp row slot gen off len base okind oslot ogen budget fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
 :position 3 :prefix "-FIELDS-ONLY" :raw-rows t
 :hints ((fn2-columns-guard-hint
          '(fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
          '(fn2-fc-run-bytes fn2-fc-decoded fn2-b3-init fn2-layout-range-code)
          '(fn2-format-run fn2-fc-step fn2-fc-start fn2-fc-decode-step) world)))

(defthm fn2-checkpoint-fc-byte-read-pool-frame
 (implies (not sealp) (equal (mv-nth 3 (fn2-fc-byte row kind sealp slot gen off len base okind oslot ogen fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)) fn2-pool))
 :hints (("Goal" :in-theory (e/d (fn2-fc-byte) (fn2-b3-byte fn2-b3-finalize fn2-b3-read fn2-fc-check-byte fn2-fc-digest-byte fn2-fc-context-hash-word fn2-pool-write)))))

(defthm fn2-checkpoint-fc-advance-read-pool-frame
 (implies (not sealp) (equal (mv-nth 4 (fn2-fc-advance fuel row kind sealp slot gen off len base okind oslot ogen fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)) fn2-pool))
 :hints (("Goal" :in-theory (e/d (fn2-fc-advance) (fn2-fc-byte fn2-fc-page-span)))))

(defthm fn2-checkpoint-fc-run-bytes-read-pool-frame
 (implies (not sealp) (equal (mv-nth 3 (fn2-fc-run-bytes fuel row kind sealp slot gen off len base okind oslot ogen fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)) fn2-pool))
 :hints (("Goal" :induct (fn2-fc-run-bytes fuel row kind sealp slot gen off len base okind oslot ogen fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests) :in-theory (e/d (fn2-fc-run-bytes) (fn2-fc-advance)))))

(defthm fn2-checkpoint-fc-step-read-pool-frame
 (implies (not sealp) (equal (mv-nth 4 (fn2-fc-step row kind sealp slot gen off len base okind oslot ogen budget fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)) fn2-pool))
 :hints (("Goal" :in-theory (e/d (fn2-fc-step) (fn2-fc-run-bytes fn2-fc-decoded fn2-fc-decode-step fn2-fc-start fn2-b3-init fn2-layout-range-code)))))

(defthm fn2-checkpoint-format-run-read-pool-frame
 (implies (not sealp) (equal (mv-nth 4 (fn2-format-run kind sealp row slot gen off len base okind oslot ogen budget fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)) fn2-pool))
 :hints (("Goal" :in-theory (e/d (fn2-format-run) (fn2-fc-step fn2-fc-reset)))))
