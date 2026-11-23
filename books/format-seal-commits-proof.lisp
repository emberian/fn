; Discharges fn2-format-seal-commits on top of format-binds-seal-proof.
; Seal identity and covered content come from fc-accepted-covered-hash and
; fc-same-trailer-same-digest. The predecessor needs the eight previous-seal words: the
; sealed-batch decoder places that reference inside the image, and the checker compares each
; of its 32 bytes with the expected word before it accepts.
(in-package "ACL2")
(include-book "format-binds-seal-proof")

; ---- the decoder: an accepted sealed-batch decode leaves field 7's reference with 32 bytes below end ----
(local (deftheory fcs-fields-theory
  (union-theories (theory 'minimal-theory)
   '(fn2-fields-value fn2-fields-set-value fn2-fields-value$ai update-fn2-fields-value$ai fn2-fields-ref-slot fn2-fields-set-ref-slot fn2-fields-ref-slot$ai update-fn2-fields-ref-slot$ai fn2-fields-ref-gen fn2-fields-set-ref-gen fn2-fields-ref-gen$ai update-fn2-fields-ref-gen$ai fn2-fields-ref-off fn2-fields-set-ref-off fn2-fields-ref-off$ai update-fn2-fields-ref-off$ai fn2-fields-ref-len fn2-fields-set-ref-len fn2-fields-ref-len$ai update-fn2-fields-ref-len$ai fn2-fields-status fn2-fields-set-status fn2-fields-status$ai update-fn2-fields-status$ai fn2-fields-decode-phase fn2-fields-set-decode-phase fn2-fields-decode-phase$ai update-fn2-fields-decode-phase$ai fn2-fields-decode-pos fn2-fields-set-decode-pos fn2-fields-decode-pos$ai update-fn2-fields-decode-pos$ai fn2-fields-decode-acc fn2-fields-set-decode-acc fn2-fields-decode-acc$ai update-fn2-fields-decode-acc$ai fn2-fields-decode-high fn2-fields-set-decode-high fn2-fields-decode-high$ai update-fn2-fields-decode-high$ai fn2-fields-decode-size fn2-fields-set-decode-size fn2-fields-decode-size$ai update-fn2-fields-decode-size$ai fn2-fields-decode-ref fn2-fields-set-decode-ref fn2-fields-decode-ref$ai update-fn2-fields-decode-ref$ai fn2-fields-decode-payload fn2-fields-set-decode-payload fn2-fields-decode-payload$ai update-fn2-fields-decode-payload$ai fn2-fields-decode-next fn2-fields-set-decode-next fn2-fields-decode-next$ai update-fn2-fields-decode-next$ai
     fn2-layout-store fn2-codec-save fn2-fields-rows update-nth-array nth-update-nth nfix natp
     (:executable-counterpart nfix) (:executable-counterpart natp) (:executable-counterpart equal)))))
(local (defthm fcs-store-ref-off
  (implies (natp j)
   (equal (fn2-fields-ref-off j (fn2-layout-store i v slot gen off size status fields))
         (if (and (natp i) (< i (fn2-fields-rows fields))
                  (unsigned-byte-p 60 v) (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
                  (unsigned-byte-p 32 off) (unsigned-byte-p 32 size) (unsigned-byte-p 8 status)
                  (equal j i))
             off
           (fn2-fields-ref-off j fields))))
  :hints (("Goal" :in-theory (theory 'fcs-fields-theory)))))
(local (defthm fcs-store-keeps-continuation
  (and (equal (fn2-fields-rows (fn2-layout-store i v slot gen off size status fields)) (fn2-fields-rows fields))
       (equal (fn2-fields-decode-phase b (fn2-layout-store i v slot gen off size status fields)) (fn2-fields-decode-phase b fields))
       (equal (fn2-fields-decode-pos b (fn2-layout-store i v slot gen off size status fields)) (fn2-fields-decode-pos b fields))
       (equal (fn2-fields-decode-acc b (fn2-layout-store i v slot gen off size status fields)) (fn2-fields-decode-acc b fields))
       (equal (fn2-fields-decode-high b (fn2-layout-store i v slot gen off size status fields)) (fn2-fields-decode-high b fields))
       (equal (fn2-fields-decode-size b (fn2-layout-store i v slot gen off size status fields)) (fn2-fields-decode-size b fields))
       (equal (fn2-fields-decode-ref b (fn2-layout-store i v slot gen off size status fields)) (fn2-fields-decode-ref b fields))
       (equal (fn2-fields-decode-payload b (fn2-layout-store i v slot gen off size status fields)) (fn2-fields-decode-payload b fields))
       (equal (fn2-fields-decode-next b (fn2-layout-store i v slot gen off size status fields)) (fn2-fields-decode-next b fields)))
  :hints (("Goal" :in-theory (theory 'fcs-fields-theory)))))
(local (defun-nx fcs-savedp (base phase pos acc high size ref payload next fields)
  (and (natp base) (< base (fn2-fields-rows fields))
       (unsigned-byte-p 32 phase) (unsigned-byte-p 32 pos)
       (unsigned-byte-p 60 acc) (unsigned-byte-p 32 high)
       (unsigned-byte-p 32 size) (unsigned-byte-p 32 ref)
       (unsigned-byte-p 8 payload) (unsigned-byte-p 32 next))))
(local (defthm fcs-save-effects
  (let ((saved (fn2-codec-save base phase pos acc high size ref payload next fields)))
    (and (equal (fn2-fields-ref-off j saved) (fn2-fields-ref-off j fields))
         (equal (fn2-fields-rows saved) (fn2-fields-rows fields))
         (implies (not (fcs-savedp base phase pos acc high size ref payload next fields))
                  (equal saved fields))
         (implies (fcs-savedp base phase pos acc high size ref payload next fields)
                  (and (equal (fn2-fields-decode-phase base saved) phase)
                       (equal (fn2-fields-decode-pos base saved) pos)
                       (equal (fn2-fields-decode-acc base saved) acc)
                       (equal (fn2-fields-decode-size base saved) size)
                       (equal (fn2-fields-decode-ref base saved) ref)
                       (equal (fn2-fields-decode-payload base saved) payload)
                       (equal (fn2-fields-decode-next base saved) next)))))
  :hints (("Goal" :in-theory (union-theories '(fcs-savedp) (theory 'fcs-fields-theory))))))
(local (in-theory (disable fcs-savedp)))
(local (defun fcs-after (phase) (not (member phase '(0 1 2 3 4 5 6 7)))))
(local (defun-nx fcs-rowbound (end fields)
  (and (natp (fn2-fields-ref-off 7 fields))
       (<= (+ 32 (fn2-fields-ref-off 7 fields)) end))))
(local (defun-nx fcs-cur (phase pos v size ref payload next end fields)
  (and (natp next) (<= next end)
       (implies (and (equal phase 7) (equal payload 1))
                (and (equal size 32) (unsigned-byte-p 60 v) (natp pos) (< pos 32)
                     (natp ref) (equal (+ ref pos) next)))
       (implies (fcs-after phase) (fcs-rowbound end fields)))))
(local (defun-nx fcs-saved (end fields)
  (fcs-cur (fn2-fields-decode-phase 0 fields) (fn2-fields-decode-pos 0 fields)
           (fn2-fields-decode-acc 0 fields) (fn2-fields-decode-size 0 fields)
           (fn2-fields-decode-ref 0 fields) (fn2-fields-decode-payload 0 fields)
           (fn2-fields-decode-next 0 fields) end fields)))
(local (defthm fcs-previous-seal-byte
  (equal (fn2-format-sealed-batch-byte 7 pos v hi size payload byte)
         (if (equal payload 1)
             (mv (if (>= (+ pos 1) size) :done :part) v hi size payload)
           (mv (if (= byte 1) :payload :unknown-tag) byte 0 32 1)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn2-format-sealed-batch-byte (:executable-counterpart equal)))))))
(local (defthm fcs-phase-order
  (and (implies (not (equal phase 7))
                (not (equal (fn2-format-sealed-batch-field-index phase) 7)))
       (implies (and (fcs-after (fn2-format-sealed-batch-next-phase phase))
                     (not (equal phase 7)))
                (fcs-after phase)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn2-format-sealed-batch-field-index fn2-format-sealed-batch-next-phase fcs-after
                (:executable-counterpart equal) (:executable-counterpart fcs-after)
                member-equal (:executable-counterpart member-equal) car-cons cdr-cons))))))
(local (in-theory (disable fcs-after (:executable-counterpart fcs-after))))
(local (deftheory fcs-base-theory
  (set-difference-theories (current-theory 'fc-u32-reconstruct)
    '(fn2-format-sealed-batch-byte fn2-format-sealed-batch-field-index
      fn2-format-sealed-batch-next-phase fn2-format-sealed-batch-empty-p
      fn2-layout-store fn2-codec-save mv-nth
      fn2-fields-rows fn2-fields-ref-off fn2-pool-read
      fn2-fields-decode-phase fn2-fields-decode-pos fn2-fields-decode-acc
      fn2-fields-decode-size fn2-fields-decode-ref fn2-fields-decode-payload
      fn2-fields-decode-next fn2-fields-value fn2-fields-ref-slot fn2-fields-ref-gen
      fn2-fields-ref-len fn2-fields-status))))
(local (defthm fcs-index-natural
  (natp (fn2-format-sealed-batch-field-index phase))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn2-format-sealed-batch-field-index (:executable-counterpart natp)))))))
(local (defthm fcs-cur-at-previous-seal
  (equal (fcs-cur 7 pos v size ref payload next end fields)
         (and (natp next) (<= next end)
              (implies (equal payload 1)
                       (and (equal size 32) (unsigned-byte-p 60 v) (natp pos) (< pos 32)
                            (natp ref) (equal (+ ref pos) next)))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fcs-cur (:executable-counterpart fcs-after) (:executable-counterpart equal)))))))
(local (defthm fcs-cur-elsewhere
  (implies (not (equal phase 7))
           (iff (fcs-cur phase pos v size ref payload next end fields)
                  (and (natp next) (<= next end)
                       (implies (fcs-after phase) (fcs-rowbound end fields)))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fcs-cur))))))
(local (defthm fcs-cur-fresh
  (iff (fcs-cur phase 0 0 0 0 0 next end fields)
         (and (natp next) (<= next end)
              (implies (fcs-after phase) (fcs-rowbound end fields))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fcs-cur (:executable-counterpart equal)))))))
(local (defthm fcs-save-keeps-rowbound
  (equal (fcs-rowbound end (fn2-codec-save base phase pos acc high size ref payload next fields))
         (fcs-rowbound end fields))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fcs-rowbound fcs-save-effects))))))
(local (defthm fcs-save-installs-saved
  (implies (and (fcs-cur phase pos v size ref payload next end fields)
                (fcs-saved end fields))
           (fcs-saved end (fn2-codec-save 0 phase pos v hi size ref payload next fields)))
  :hints (("Goal" :cases ((fcs-savedp 0 phase pos v hi size ref payload next fields))
                  :in-theory (union-theories (theory 'minimal-theory)
              '(fcs-saved fcs-cur fcs-rowbound fcs-save-effects))))))
(local (defthm fcs-store-elsewhere
  (implies (and (natp i) (not (equal i 7)))
           (and (equal (fcs-rowbound end (fn2-layout-store i v slot gen off size status fields))
                       (fcs-rowbound end fields))
                (equal (fcs-saved end (fn2-layout-store i v slot gen off size status fields))
                       (fcs-saved end fields))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fcs-saved fcs-cur fcs-rowbound fcs-store-ref-off fcs-store-keeps-continuation
                (:executable-counterpart natp)))))))
(local (defthm fcs-store-previous-seal
  (implies (and (natp ref) (<= (+ 32 ref) end) (unsigned-byte-p 32 end)
                (unsigned-byte-p 60 v) (< 7 (fn2-fields-rows fields)))
           (and (fcs-rowbound end (fn2-layout-store 7 v 0 1 ref 32 0 fields))
                (implies (fcs-saved end fields)
                         (fcs-saved end (fn2-layout-store 7 v 0 1 ref 32 0 fields)))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fcs-saved fcs-cur fcs-rowbound fcs-store-ref-off fcs-store-keeps-continuation
                unsigned-byte-p natp integer-range-p
                (:executable-counterpart natp) (:executable-counterpart unsigned-byte-p)
                (:executable-counterpart expt)))))))
(local (defthm fcs-done-is-after
  (implies (fcs-cur 78 pos v size ref payload next end fields)
           (fcs-rowbound end fields))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fcs-cur (:executable-counterpart fcs-after)))))))
(local (defthm fcs-byte-never-settles
  (and (not (equal (car (fn2-format-sealed-batch-byte phase pos v hi size payload byte)) :ok))
       (not (equal (car (fn2-format-sealed-batch-byte phase pos v hi size payload byte)) :more)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn2-format-sealed-batch-byte car-cons (:executable-counterpart equal)))))))
(local (defthm fcs-scan-binds-previous-seal
  (let ((r (fn2-format-sealed-batch-scan fuel 0 phase pos v hi size ref payload next
                                         0 1 end okind oslot ogen fields pool)))
    (implies (and (unsigned-byte-p 32 end)
                  (fcs-cur phase pos v size ref payload next end fields))
             (and (implies (and (or (eq (car r) :ok) (eq (car r) :more))
                                (fcs-rowbound end fields))
                           (fcs-rowbound end (mv-nth 2 r)))
                  (implies (eq (car r) :ok) (fcs-rowbound end (mv-nth 2 r)))
                  (implies (and (eq (car r) :more) (fcs-saved end fields))
                           (fcs-saved end (mv-nth 2 r))))))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-format-sealed-batch-scan fuel 0 phase pos v hi size ref payload next
                                         0 1 end okind oslot ogen fields pool)
           :expand ((:free (phase pos v hi size ref payload next) (fn2-format-sealed-batch-scan fuel 0 phase pos v hi size ref payload next
                                         0 1 end okind oslot ogen fields pool)))
           :do-not '(generalize eliminate-destructors fertilize)
           :in-theory (union-theories
                        (theory 'fcs-base-theory)
                        '((:induction fn2-format-sealed-batch-scan) fc-mv-cons fc-mv-zero
                          fcs-cur fcs-previous-seal-byte fcs-byte-never-settles fcs-phase-order fcs-index-natural
                          fcs-save-keeps-rowbound fcs-save-installs-saved fcs-store-elsewhere
                          fcs-store-previous-seal fcs-done-is-after
                          (:executable-counterpart fcs-after)
                          (:executable-counterpart fn2-format-sealed-batch-field-index)
                          (:executable-counterpart fn2-format-sealed-batch-next-phase)
                          (:executable-counterpart fn2-format-sealed-batch-empty-p)))))))
(local (defthm fcs-step-binds-previous-seal
  (let ((r (fn2-fc-decode-step :seal 0 0 1 0 end okind oslot ogen budget fields pool)))
    (implies (fcs-saved end fields)
             (and (implies (eq (car r) :ok) (fcs-rowbound end (mv-nth 2 r)))
                  (implies (eq (car r) :more) (fcs-saved end (mv-nth 2 r))))))
  :rule-classes nil
  :hints (("Goal"
    :cases ((equal (fn2-fields-decode-next 0 fields) 0))
    :use ((:instance fcs-scan-binds-previous-seal (fuel budget)
             (phase (fn2-fields-decode-phase 0 fields)) (pos (fn2-fields-decode-pos 0 fields))
             (v (fn2-fields-decode-acc 0 fields)) (hi (fn2-fields-decode-high 0 fields))
             (size (fn2-fields-decode-size 0 fields)) (ref (fn2-fields-decode-ref 0 fields))
             (payload (fn2-fields-decode-payload 0 fields))
             (next (fn2-fields-decode-next 0 fields))))
    :in-theory (union-theories (theory 'minimal-theory)
       '(fn2-fc-decode-step fn2-format-sealed-batch-decode-step fcs-saved
         fc-mv-cons fc-mv-zero car-cons cdr-cons (:executable-counterpart equal)
         (:executable-counterpart zp)))))))
(local (defthm fcs-start-saved
  (implies (and (natp end) (< 0 (fn2-fields-rows fields)))
           (fcs-saved end (fn2-fc-start :seal 0 fields)))
  :hints (("Goal"
    :use ((:instance fcs-save-effects (base 0) (phase 0) (pos 0) (acc 0) (high 0) (size 0)
                     (ref 0) (payload 0) (next 0) (j 7)))
    :in-theory (union-theories (theory 'minimal-theory)
       '(fn2-fc-start fn2-format-sealed-batch-start fcs-saved fcs-cur fcs-savedp natp
         (:executable-counterpart fcs-after) (:executable-counterpart equal)
         (:executable-counterpart natp) (:executable-counterpart unsigned-byte-p)))))))

; ---- the checker: each previous-seal byte is compared with the expected word ----
(local (defun fcs-word (i ctx)
  (declare (xargs :verify-guards nil))
  (case i
    (0 (fn2-fc-expected-previous-seal-0 ctx)) (1 (fn2-fc-expected-previous-seal-1 ctx))
    (2 (fn2-fc-expected-previous-seal-2 ctx)) (3 (fn2-fc-expected-previous-seal-3 ctx))
    (4 (fn2-fc-expected-previous-seal-4 ctx)) (5 (fn2-fc-expected-previous-seal-5 ctx))
    (6 (fn2-fc-expected-previous-seal-6 ctx)) (otherwise (fn2-fc-expected-previous-seal-7 ctx)))))
(local (defthm fcs-word-installed
  (equal (fn2-digest-word 128 i (fc-expected-digests ctx ds)) (fcs-word i ctx))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
             (append '(fcs-word fn2-digest-word nth-update-nth update-nth-array
                       (:executable-counterpart nfix) fn2-digests-w0 fn2-digests-w1 fn2-digests-w2 fn2-digests-w3 fn2-digests-w4 fn2-digests-w5 fn2-digests-w6 fn2-digests-w7 fn2-digests-w0$ai fn2-digests-w1$ai fn2-digests-w2$ai fn2-digests-w3$ai fn2-digests-w4$ai fn2-digests-w5$ai fn2-digests-w6$ai fn2-digests-w7$ai)
                     (theory 'fc-expected-digest-layout)))))))
(local (defthm fcs-word-settled
  (implies (equal (fc-expected-digests cx ds) ds)
           (equal (fn2-fc-context-previous-seal-word 0 i (fc-image-context cx) ds)
                  (fcs-word i cx)))
  :hints (("Goal" :use ((:instance fcs-word-installed (ctx cx)))
    :in-theory (union-theories (theory 'minimal-theory)
    '(fn2-fc-context-previous-seal-word
      fc-image-context fn2-fc-spec-context fc-mv-nth-zero car-cons nth-update-nth update-nth-array
      nfix (:executable-counterpart nfix) (:executable-counterpart fn2-digest-slot)
      fn2-fc-context-previous-seal fn2-fc-context-set-location fn2-fc-context-set-allocation fn2-fc-context-set-history fn2-fc-context-set-incarnation fn2-fc-context-set-writer-epoch fn2-fc-context-set-commit fn2-fc-context-set-page-kind fn2-fc-context-set-encoded-length fn2-fc-context-set-extent-writer-epoch fn2-fc-context-set-previous-commit fn2-fc-context-set-extent fn2-fc-context-set-hash fn2-fc-context-set-geometry fn2-fc-context-set-previous-seal update-fn2-fc-context-location$ai update-fn2-fc-context-allocation$ai update-fn2-fc-context-history$ai update-fn2-fc-context-incarnation$ai update-fn2-fc-context-writer-epoch$ai update-fn2-fc-context-commit$ai update-fn2-fc-context-page-kind$ai update-fn2-fc-context-encoded-length$ai update-fn2-fc-context-extent-writer-epoch$ai update-fn2-fc-context-previous-commit$ai update-fn2-fc-context-extent$ai update-fn2-fc-context-hash$ai update-fn2-fc-context-geometry$ai update-fn2-fc-context-previous-seal$ai fn2-fc-context-previous-seal$ai))))))
(local (defthm fcs-settled-digests-kept
  (implies (equal (fc-expected-digests cx ds) ds)
           (and (equal (fc-expected-digests cx (car (fn2-b3-byte 0 byte ds b3)))
                       (car (fn2-b3-byte 0 byte ds b3)))
                (equal (fc-expected-digests cx (fn2-b3-finalize 125 0 ds b3))
                       (fn2-b3-finalize 125 0 ds b3))
                (equal (fc-expected-digests cx (car (fn2-b3-init 0 0 1 ds b3)))
                       (car (fn2-b3-init 0 0 1 ds b3)))))
  :hints (("Goal" :use ((:instance fn2-b3-byte-fc-linked (a cx) (b cx) (da ds) (db ds))
                        (:instance fn2-b3-finalize-fc-linked (a cx) (b cx) (da ds) (db ds))
                        (:instance fn2-b3-init-fc-linked (a cx) (b cx) (da ds) (db ds)))
                  :in-theory (union-theories (theory 'minimal-theory) '(fc-linked-digests))))))
(local (defthm fcs-offset-updates
  (and (equal (fn2-fc-previous-seal-offset 0 (fn2-fc-set-phase 0 v fc)) (fn2-fc-previous-seal-offset 0 fc))
       (equal (fn2-fc-previous-seal-offset 0 (fn2-fc-set-pos 0 v fc)) (fn2-fc-previous-seal-offset 0 fc))
       (equal (fn2-fc-previous-seal-offset 0 (fn2-fc-set-zero 0 v fc)) (fn2-fc-previous-seal-offset 0 fc))
       (equal (fn2-fc-previous-seal-offset 0 (fn2-fc-set-pad 0 v fc)) (fn2-fc-previous-seal-offset 0 fc))
       (equal (fn2-fc-previous-seal-offset 0 (fn2-fc-set-pad-end 0 v fc)) (fn2-fc-previous-seal-offset 0 fc))
       (equal (fn2-fc-previous-seal-offset 0 (fn2-fc-set-previous-seal-offset 0 v fc)) v))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
             '(fn2-fc-previous-seal-offset fn2-fc-previous-seal-offset$ai fn2-fc-set-phase fn2-fc-set-pos
               fn2-fc-set-zero fn2-fc-set-pad fn2-fc-set-pad-end fn2-fc-set-previous-seal-offset
               update-fn2-fc-phase$ai update-fn2-fc-pos$ai update-fn2-fc-zero$ai
               update-fn2-fc-pad$ai update-fn2-fc-pad-end$ai update-fn2-fc-previous-seal-offset$ai
               update-nth-array nth-update-nth (:executable-counterpart nfix)))))))
(local (defun-nx fcs-match (k fields pool cx)
  (let ((input (fn2-b3-read 0 1 (+ (fn2-fields-ref-off 7 fields) k) 1 0 1 pool)))
    (and (eq (car input) :ok)
         (equal (mv-nth 1 input)
                (fn2-fc-word-byte (fcs-word (floor k 4) cx) (mod k 4)))))))
(local (defun-nx fcs-progress (k len fc fields pool ds cx)
  (let ((phase (fn2-fc-phase 0 fc)) (pos (fn2-fc-pos 0 fc)))
    (and (equal (fc-expected-digests cx ds) ds)
         (implies (equal phase *fn2-fc-phase-idle*) (< 0 (fn2-fields-rows fields)))
         (implies (equal phase *fn2-fc-phase-decode*) (fcs-saved len fields))
         (implies (or (equal phase *fn2-fc-phase-prefix*) (equal phase *fn2-fc-phase-hash*)
                      (equal phase *fn2-fc-phase-digest*))
                  (and (equal (fn2-fc-previous-seal-offset 0 fc) (fn2-fields-ref-off 7 fields))
                       (fcs-rowbound len fields)))
         (implies (equal phase *fn2-fc-phase-hash*)
                  (and (natp pos)
                       (or (<= pos (+ (fn2-fields-ref-off 7 fields) k))
                           (fcs-match k fields pool cx))))
         (implies (equal phase *fn2-fc-phase-digest*) (fcs-match k fields pool cx))))))
(local (defun-nx fcs-running (fc)
  (or (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-prefix*)
      (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-hash*)
      (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-digest*))))
(local (defmacro fcs-step-claim (call fc-index ds-index)
  `(let ((step ,call))
     (implies (and (natp k) (< k 32) (natp len) (fcs-progress k len fc fields pool ds cx))
              (and (implies (eq (car step) :ok) (fcs-match k fields pool cx))
                   (implies (or (eq (car step) :more) (eq (car step) :yield))
                            (and (fcs-progress k len (mv-nth ,fc-index step) fields pool
                                               (mv-nth ,ds-index step) cx)
                                 (implies (fcs-running fc)
                                          (fcs-running (mv-nth ,fc-index step))))))))))
(local (defthm fcs-byte-checks-previous-seal
  (fcs-step-claim
    (fn2-fc-byte 0 :seal nil 0 1 0 len base 1 0 1 fc (fc-image-context cx) b3 fields pool ds) 1 4)
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
          :cases ((equal (fn2-fc-phase 0 fc) 2) (equal (fn2-fc-phase 0 fc) 3) (equal (fn2-fc-phase 0 fc) 4))
          :in-theory (set-difference-theories (union-theories (theory 'fcs-base-theory)
                         '(fn2-fc-byte fn2-fc-check-byte fcs-progress fcs-match fcs-running fcs-rowbound
                           fc-phase-pos-updates fcs-offset-updates fcs-word-settled
                           fcs-settled-digests-kept fc-mv-cons fc-mv-zero
                           (:executable-counterpart fn2-digest-slot)))
                        '(fn2-fc-phase fn2-fc-pos fn2-fc-zero fn2-fc-pad fn2-fc-pad-end fn2-fc-geom
                          fn2-fc-previous-seal-offset fn2-fc-set-pos fn2-fc-set-phase floor mod))))))
(local (defmacro fcs-advance-call ()
  '(fn2-fc-advance fuel 0 :seal nil 0 1 0 len base 1 0 1 fc (fc-image-context cx) b3 fields pool ds)))
(local (defthm fcs-advance-checks-previous-seal
  (fcs-step-claim (fcs-advance-call) 2 5)
  :rule-classes nil
  :hints (("Goal" :use fcs-byte-checks-previous-seal
     :in-theory (union-theories (theory 'minimal-theory)
                  '(fn2-fc-advance fc-mv-cons fc-mv-zero car-cons cdr-cons member-equal
                    (:executable-counterpart member-equal) (:executable-counterpart equal)
                    (:executable-counterpart zp)))))))
(local (defmacro fcs-run-call ()
  '(fn2-fc-run-bytes fuel 0 :seal nil 0 1 0 len base 1 0 1 fc (fc-image-context cx) b3 fields pool ds)))
(local (defthm fcs-run-checks-previous-seal
  (fcs-step-claim (fcs-run-call) 1 4)
  :rule-classes nil
  :hints (("Goal" :induct (fcs-run-call) :expand (fcs-run-call)
                  :in-theory (e/d ((:induction fn2-fc-run-bytes))
                                  (mv-nth fcs-progress fcs-match fcs-running)))
          ("Subgoal *1/3" :use fcs-advance-checks-previous-seal)
          ("Subgoal *1/2" :use fcs-advance-checks-previous-seal))))
(local (defthm fcs-decoded-starts-checking
  (let ((step (fn2-fc-decoded 0 :seal 0 len 0 next fc (fc-image-context cx) b3 fields pool ds)))
    (implies (and (natp k) (< k 32) (natp len)
                  (equal (fc-expected-digests cx ds) ds) (fcs-rowbound len fields))
             (and (not (eq (car step) :ok))
                  (implies (eq (car step) :more)
                           (and (fcs-progress k len (mv-nth 1 step) fields pool ds cx)
                                (fcs-running (mv-nth 1 step)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'fcs-base-theory)
              '(fn2-fc-decoded fcs-progress fcs-running fcs-rowbound fc-phase-pos-updates
                fcs-offset-updates fc-identity-never-more fc-mv-cons fc-mv-zero))))))
(local (defmacro fcs-step-call ()
  '(fn2-fc-step 0 :seal nil 0 1 0 len 0 1 0 1 4096 fc (fc-image-context cx) b3 fields pool ds)))
(local (defmacro fcs-decode-call ()
  '(fn2-fc-decode-step :seal 0 0 1 0 len 1 0 1 4096 fields pool)))
(local (defmacro fcs-drive-claim (call)
  `(let ((step ,call))
     (implies (and (natp k) (< k 32) (natp len) (fcs-progress k len fc fields pool ds cx))
              (and (implies (eq (car step) :ok) (fcs-match k (mv-nth 3 step) pool cx))
                   (implies (eq (car step) :more)
                            (fcs-progress k len (mv-nth 1 step) (mv-nth 3 step) pool
                                          (mv-nth 5 step) cx))
                   (implies (fcs-running fc)
                            (and (equal (mv-nth 3 step) fields)
                                 (implies (eq (car step) :more) (fcs-running (mv-nth 1 step)))))
                   (implies (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-decode*)
                            (and (not (eq (car step) :ok))
                                 (implies (eq (car step) :more)
                                          (and (equal (mv-nth 3 step) (mv-nth 2 (fcs-decode-call)))
                                               (if (eq (car (fcs-decode-call)) :more)
                                                   (equal (fn2-fc-phase 0 (mv-nth 1 step))
                                                          *fn2-fc-phase-decode*)
                                                 (fcs-running (mv-nth 1 step))))))))))))
(local (defthm fcs-settled-digests-init
  (implies (equal (fc-expected-digests cx ds) ds)
           (equal (fc-expected-digests cx (car (fn2-b3-init 0 0 136 ds b3)))
                  (car (fn2-b3-init 0 0 136 ds b3))))
  :hints (("Goal" :use (fcs-settled-digests-kept (:instance fc-b3-init-key (key 1)))
                  :in-theory (theory 'minimal-theory)))))
(local (defthm fcs-step-checks-idle
  (implies (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-idle*)
           (fcs-drive-claim (fcs-step-call)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fcs-start-saved (end len)))
     :in-theory (union-theories (theory 'fcs-base-theory)
                  '(fn2-fc-step fcs-progress fcs-running fc-phase-pos-updates
                    fcs-settled-digests-init fc-mv-cons fc-mv-zero
                    (:executable-counterpart fn2-digest-slot)))))))
(local (defthm fcs-step-checks-decode
  (implies (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-decode*)
           (fcs-drive-claim (fcs-step-call)))
  :rule-classes nil
  :hints (("Goal"
     :use ((:instance fcs-decoded-starts-checking
             (next (mv-nth 1 (fcs-decode-call))) (fields (mv-nth 2 (fcs-decode-call))))
           (:instance fcs-step-binds-previous-seal (end len) (okind 1) (oslot 0) (ogen 1) (budget 4096)))
     :in-theory (union-theories (theory 'fcs-base-theory)
                  '(fn2-fc-step fcs-progress fcs-running fc-mv-cons fc-mv-zero fc-zero-plus-len))))))
(local (defthm fcs-step-checks-run
  (implies (and (not (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-idle*))
                (not (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-decode*)))
           (fcs-drive-claim (fcs-step-call)))
  :rule-classes nil
  :hints (("Goal"
     :use ((:instance fcs-run-checks-previous-seal (fuel 4096) (base 0)))
     :in-theory (union-theories (theory 'minimal-theory)
                  '(fn2-fc-step fc-mv-cons fc-mv-zero car-cons cdr-cons member-equal
                    (:executable-counterpart member-equal) (:executable-counterpart equal)
                    (:executable-counterpart zp) (:executable-counterpart posp)
                    (:executable-counterpart <) natp (:type-prescription len)))))))
(local (defthm fcs-step-checks-previous-seal
  (fcs-drive-claim (fcs-step-call))
  :rule-classes nil
  :hints (("Goal" :use (fcs-step-checks-idle fcs-step-checks-decode fcs-step-checks-run)
           :in-theory (theory 'minimal-theory)))))
(local (defthm fcs-step-from-idle
  (let ((step (fcs-step-call)))
    (implies (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-idle*)
             (and (not (eq (car step) :ok))
                  (implies (eq (car step) :more)
                           (and (equal (mv-nth 3 step) (fn2-fc-start :seal 0 fields))
                                (equal (fn2-fc-phase 0 (mv-nth 1 step)) *fn2-fc-phase-decode*))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (set-difference-theories
                  (union-theories (theory 'fcs-base-theory)
                    '(fn2-fc-step fc-phase-pos-updates fc-mv-cons fc-mv-zero fc-read-range-never-yields))
                  '(fn2-fc-phase))))))
(local (defmacro fcs-format-call ()
  '(fn2-format-run :seal nil 0 0 1 0 len 0 1 0 1 4096 fc (fc-image-context cx) b3 fields pool ds)))
(local (defthm fcs-format-checks-previous-seal
  (and (fcs-drive-claim (fcs-format-call))
       (let ((step (fcs-format-call)))
         (implies (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-idle*)
                  (and (not (eq (car step) :ok))
                       (implies (eq (car step) :more)
                                (and (equal (mv-nth 3 step) (fn2-fc-start :seal 0 fields))
                                     (equal (fn2-fc-phase 0 (mv-nth 1 step))
                                            *fn2-fc-phase-decode*)))))))
  :rule-classes nil
  :hints (("Goal" :use (fcs-step-checks-previous-seal fcs-step-from-idle)
                  :in-theory (union-theories (theory 'minimal-theory)
                     '(fn2-format-run fc-mv-cons fc-mv-zero car-cons cdr-cons
                       (:executable-counterpart zp) (:executable-counterpart equal)))))))
(local (defmacro fcs-drive-call ()
  '(fn2-format-drive fuel 0 :seal nil 0 1 0 len 0 1 0 1 4096 fc (fc-image-context cx) b3 fields pool ds)))
(local (defthm fcs-drive-checks-previous-seal
  (let ((step (fcs-drive-call)))
    (implies (and (natp k) (< k 32) (natp len) (fcs-progress k len fc fields pool ds cx)
                  (eq (car step) :ok))
             (and (fcs-match k (mv-nth 3 step) pool cx)
                  (implies (fcs-running fc) (equal (mv-nth 3 step) fields))
                  (implies (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-decode*)
                           (equal (mv-nth 3 step)
                                  (fc-decoded-fields fuel :seal len fields pool))))))
  :rule-classes nil
  :hints (("Goal" :induct (fcs-drive-call) :expand ((fcs-drive-call) (fc-decoded-fields fuel :seal len fields pool))
                  :in-theory (union-theories (theory 'minimal-theory)
                     '((:induction fn2-format-drive) fc-mv-cons fc-mv-zero car-cons cdr-cons
                       fc-format-keeps-pool (:executable-counterpart zp) (:executable-counterpart equal))))
          ("Subgoal *1/3" :use fcs-format-checks-previous-seal)
          ("Subgoal *1/2" :use fcs-format-checks-previous-seal))))
(local (defthm fcs-drive-from-idle
  (let ((step (fcs-drive-call)))
    (implies (and (natp k) (< k 32) (natp len) (fcs-progress k len fc fields pool ds cx)
                  (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-idle*)
                  (eq (car step) :ok))
             (fcs-match k (fc-decoded-fields (1- fuel) :seal len (fn2-fc-start :seal 0 fields) pool)
                        pool cx)))
  :rule-classes nil
  :hints (("Goal" :expand ((fcs-drive-call))
     :use (fcs-format-checks-previous-seal
           (:instance fcs-drive-checks-previous-seal (fuel (1- fuel))
              (fc (mv-nth 1 (fcs-format-call))) (b3 (mv-nth 2 (fcs-format-call)))
              (fields (mv-nth 3 (fcs-format-call))) (ds (mv-nth 5 (fcs-format-call)))))
     :in-theory (union-theories (theory 'minimal-theory)
                     '(fc-mv-cons fc-mv-zero car-cons cdr-cons
                       fc-format-keeps-pool (:executable-counterpart zp) (:executable-counterpart equal)))))))
(local (defthm fcs-initial-fields-rows
  (equal (fn2-fields-rows (fn2-fields-init *fn2-format-sealed-batch-num-fields* (create-fn2-fields))) 78)
  :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
              '(fn2-fields-init fn2-fields-rows create-fn2-fields nth-update-nth
                (:executable-counterpart fn2-fields-rows) (:executable-counterpart fn2-fields-init)
                (:executable-counterpart create-fn2-fields)))))))
(local (defthm fcs-accepted-previous-seal-byte
  (implies (and (natp k) (< k 32) (fn2-fc-acceptedp :seal bytes cx))
           (fcs-match k (fc-image-header :seal bytes) (fc-image-pool bytes) cx))
  :rule-classes nil
  :hints (("Goal"
     :use ((:instance fc-accepted-drive-ok (kind :seal) (ctx cx))
           (:instance fcs-drive-from-idle
             (fuel (fn2-format-fuel (len bytes))) (len (len bytes))
             (fc (fn2-fc-init 1 (create-fn2-fc)))
             (b3 (fn2-b3-table-init 1 (create-fn2-b3)))
             (fields (fn2-fields-init *fn2-format-sealed-batch-num-fields* (create-fn2-fields)))
             (pool (fc-image-pool bytes))
             (ds (fc-expected-digests cx (fn2-digests-init 144 (create-fn2-digests))))))
     :in-theory (union-theories (theory 'minimal-theory)
        '(fc-image-drive fc-image-header fc-image-pool fcs-progress fc-image-initially-idle
          fc-expected-digests-overwrite fcs-initial-fields-rows fc-length-natural
          (:executable-counterpart equal) (:executable-counterpart <)))))))

; ---- the eight words, then the obligation ----
(local (defmacro fcs-accepted-word (i)
  (let ((name (packn-pos (list 'fcs-accepted-word- i) 'fcs-word)))
    `(defthm ,name
       (implies (and (fn2-fc-expectedp a) (fn2-fc-expectedp b)
                     (fn2-fc-acceptedp :seal bytes a) (fn2-fc-acceptedp :seal bytes b))
                (equal (fcs-word ,i a) (fcs-word ,i b)))
       :rule-classes nil
       :hints (("Goal" :use ((:instance fc-u32-bytes-unique
                                (x (fcs-word ,i a)) (y (fcs-word ,i b)))
                             (:instance fcs-accepted-previous-seal-byte (k ,(+ 0 (* 4 i))) (cx a))
                             (:instance fcs-accepted-previous-seal-byte (k ,(+ 0 (* 4 i))) (cx b))
                             (:instance fcs-accepted-previous-seal-byte (k ,(+ 1 (* 4 i))) (cx a))
                             (:instance fcs-accepted-previous-seal-byte (k ,(+ 1 (* 4 i))) (cx b))
                             (:instance fcs-accepted-previous-seal-byte (k ,(+ 2 (* 4 i))) (cx a))
                             (:instance fcs-accepted-previous-seal-byte (k ,(+ 2 (* 4 i))) (cx b))
                             (:instance fcs-accepted-previous-seal-byte (k ,(+ 3 (* 4 i))) (cx a))
                             (:instance fcs-accepted-previous-seal-byte (k ,(+ 3 (* 4 i))) (cx b)))
                       :in-theory (union-theories (theory 'minimal-theory)
                                  '(fn2-fc-expectedp fcs-match fcs-word
                                    (:executable-counterpart floor) (:executable-counterpart mod)
                                    (:executable-counterpart natp) (:executable-counterpart <)
                                    (:executable-counterpart equal) (:executable-counterpart eql)))))))))
(local (fcs-accepted-word 0))
(local (fcs-accepted-word 1))
(local (fcs-accepted-word 2))
(local (fcs-accepted-word 3))
(local (fcs-accepted-word 4))
(local (fcs-accepted-word 5))
(local (fcs-accepted-word 6))
(local (fcs-accepted-word 7))
(defthm fn2-format-seal-commits-proved
  (fn2-format-seal-commits$owed a b ca cb)
  :rule-classes nil
  :hints (("Goal" :use ((:instance fc-accepted-covered-hash (kind :seal) (bytes a) (ctx ca))
                        (:instance fc-accepted-covered-hash (kind :seal) (bytes b) (ctx cb))
                        (:instance fc-same-trailer-same-digest (kind :seal))
                        fc-seal-covered-binds-identity
                        fc-seal-covered-and-trailer-bind-image
                        (:instance fc-seal-header-predecessor-commit (bytes a) (a ca) (b cb))
                        (:instance fcs-accepted-word-0 (bytes a) (a ca) (b cb))
                        (:instance fcs-accepted-word-1 (bytes a) (a ca) (b cb))
                        (:instance fcs-accepted-word-2 (bytes a) (a ca) (b cb))
                        (:instance fcs-accepted-word-3 (bytes a) (a ca) (b cb))
                        (:instance fcs-accepted-word-4 (bytes a) (a ca) (b cb))
                        (:instance fcs-accepted-word-5 (bytes a) (a ca) (b cb))
                        (:instance fcs-accepted-word-6 (bytes a) (a ca) (b cb))
                        (:instance fcs-accepted-word-7 (bytes a) (a ca) (b cb))
                        )
           :in-theory (union-theories (theory 'minimal-theory)
                         '(fn2-format-seal-commits$owed fn2-fc-collision-free-pairp
                           fn2-fc-seal-predecessor fcs-word (:executable-counterpart eql)
                           (:executable-counterpart equal))))))
(fn2-owed-discharge fn2-format-seal-commits fn2-format-seal-commits-proved)
