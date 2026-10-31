; Layer C in the served core, seam C-S3 (fn2/docs/c-ordered-runs.md §8 item 8):
; bind (every staged row into the batch's private overlays), release at the
; outcome, B's publish and drop, the defcosts, and the core wrappers of the
; whole seam (fn2-successor-prepare-events and -commit-events, materialized in
; assembly-callbacks-c.lisp). The tables and the :prepare half are
; machines-c-successor.lisp's, stage machines-c-stage.lisp's (C-SUCCESSOR-BOOK).
(in-package "ACL2")
(include-book "machines-c-stage")
(fn2-book-layer :c)
(local (in-theory (disable fn2-run-layout-fields fn2-run-layout-keys fn2-run-layout-merge fn2-run-layout-size
                           fn2-fold-key-arg fn2-fold-arity fn2-fold-assigned-p fn2-run-layout-octets-max
                           fn2-run-layout-value-ok fn2-run-layout-fold-p fn2-run-version fn2-succ-bit fn2-succ-has)))

; ---------------------------------------------------------------------------
; Bind (right after B's admission :ok, in the same transition): every slot's
; row enters BATCH's private overlay of its schema, the newest one with room
; or a held spare. Nothing here fails after an :ok stage but a broken
; invariant.

; Copy N bytes from [SOFF..) of SSLOT/SGEN (read under SK SS SG) to
; [DOFF..) of DSLOT/DGEN (written under the engine's owner). Interim until
; A-S8's fn2-pool-copy-across lands (D's interim is the same loop).
(defun fn2-idc-copy (n sslot sgen soff sk ss sg dslot dgen doff fn2-pool)
 (declare (xargs :stobjs fn2-pool :measure (nfix n) :guard (and (fn2-pool-wfp fn2-pool) (natp n) (natp soff) (natp doff)) :guard-hints (("Goal" :in-theory (disable fn2-pool-reserve fn2-pool-release fn2-pool-reset fn2-pool-read fn2-pool-write
                                             fn2-pool-class-for fn2-ov-start fn2-ov-advance fn2-id-record-insert fn2-ov-insert
                                             fn2-ov-locate fn2-ov-entry fn2-run-copy-row fn2-fold-apply fn2-fold-assign
                                             fn2-run-layout-size fn2-run-lookup-step fn2-run-cursor-start
                                             fn2-fields-rows fn2-succ-slots-rows fn2-succ-txns-rows fn2-overlays-rows)))))
 (if (zp n) (mv :ok fn2-pool)
  (b* (((mv code byte) (fn2-pool-read sslot sgen soff sk ss sg fn2-pool))
       ((unless (eq code :ok)) (mv code fn2-pool))
       ((mv code fn2-pool) (fn2-pool-write dslot dgen doff byte *fn2-idc-owner-kind* *fn2-idc-owner-slot* *fn2-idc-owner-gen* fn2-pool))
       ((unless (eq code :ok)) (mv code fn2-pool)))
   (fn2-idc-copy (- n 1) sslot sgen (+ 1 soff) sk ss sg dslot dgen (+ 1 doff) fn2-pool))))
(fn2-pool-preserves fn2-idc-copy (n sslot sgen soff sk ss sg dslot dgen doff fn2-pool) :position 1
 :hints (("Goal" :in-theory (disable fn2-pool-read fn2-pool-write fn2-pool-rows))))

; The record slot's entry rows (at ENTRY) take the decision's Message-ID and
; content copied into the scratch (content at 0, Message-ID at 32), so the
; fact encodes from the engine's own workspace; the decision's offer rows
; are left as they are (a dropped batch's transaction binds again).
(defun fn2-idc-rehome (tx entry b0 fn2-id-decides fn2-id-engine fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-id-decides fn2-id-engine fn2-fields fn2-pool)
  :guard (and (fn2-id-decides-wfp fn2-id-decides) (fn2-id-engine-wfp fn2-id-engine) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))
  :guard-hints (("Goal" :in-theory (disable fn2-pool-reserve fn2-pool-release fn2-pool-reset fn2-pool-read fn2-pool-write
                                            fn2-pool-class-for fn2-idc-copy fn2-fields-rows)))))
 (b* (((unless (and (natp tx) (< tx (fn2-id-decides-rows fn2-id-decides)) (< 0 (fn2-id-engine-rows fn2-id-engine))
                    (equal (fn2-id-engine-scratch 0 fn2-id-engine) 1) (natp entry) (natp b0)
                    (< (+ entry 1) (fn2-fields-rows fn2-fields)) (< (+ b0 *fn2-idc-q* 1) (fn2-fields-rows fn2-fields))))
       (mv :state fn2-fields fn2-pool))
      (mrow (+ b0 *fn2-idc-q* *fn2-id-mid*)) (crow (+ b0 *fn2-idc-q* *fn2-id-con*))
      (mlen (fn2-fields-ref-len mrow fn2-fields))
      ((unless (and (natp mlen) (<= mlen 250) (equal (fn2-fields-ref-len crow fn2-fields) 32))) (mv :bounds fn2-fields fn2-pool))
      (sslot (fn2-id-engine-slot 0 fn2-id-engine)) (sgen (fn2-id-engine-gen 0 fn2-id-engine))
      (qk (fn2-id-decides-qk tx fn2-id-decides)) (qs (fn2-id-decides-qs tx fn2-id-decides)) (qg (fn2-id-decides-qg tx fn2-id-decides))
      ((unless (and (unsigned-byte-p 32 sslot) (unsigned-byte-p 60 sgen)
                    (natp (fn2-fields-ref-off mrow fn2-fields)) (natp (fn2-fields-ref-off crow fn2-fields))))
       (mv :state fn2-fields fn2-pool))
      ((mv code fn2-pool) (fn2-pool-reset sslot sgen *fn2-idc-owner-kind* *fn2-idc-owner-slot* *fn2-idc-owner-gen* fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-fields fn2-pool))
      ((mv code fn2-pool) (fn2-idc-copy 32 (fn2-fields-ref-slot crow fn2-fields) (fn2-fields-ref-gen crow fn2-fields)
                                        (fn2-fields-ref-off crow fn2-fields) qk qs qg sslot sgen 0 fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-fields fn2-pool))
      ((mv code fn2-pool) (fn2-idc-copy mlen (fn2-fields-ref-slot mrow fn2-fields) (fn2-fields-ref-gen mrow fn2-fields)
                                        (fn2-fields-ref-off mrow fn2-fields) qk qs qg sslot sgen *fn2-idc-scratch-mid* fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-fields fn2-pool))
      (fn2-fields (fn2-fields-put (+ entry *fn2-id-con*) (value 1) (ref-slot sslot) (ref-gen sgen) (ref-off 0) (ref-len 32)))
      (fn2-fields (fn2-fields-put (+ entry *fn2-id-mid*) (value 0) (ref-slot sslot) (ref-gen sgen) (ref-off *fn2-idc-scratch-mid*) (ref-len mlen))))
  (mv :ok fn2-fields fn2-pool)))
(fn2-idc-fn-shape fn2-idc-rehome (tx entry b0 fn2-id-decides fn2-id-engine fn2-fields fn2-pool) (fn2-fields fn2-pool)
 (fn2-id-decides fn2-id-engine fn2-fields fn2-pool) t
 (fn2-fields-ref-len fn2-fields-ref-off fn2-fields-ref-slot fn2-fields-ref-gen fn2-id-decides-qk fn2-id-decides-qs
  fn2-id-decides-qg fn2-id-engine-slot fn2-id-engine-gen fn2-id-engine-scratch fn2-idc-copy))

; An insert's octet fields J.. of the row at ENTRY copied into the scratch
; from OFF on (read under SK SS SG), each field then naming its copy.
(defun fn2-succ-rehome-octets (k j sid entry off sk ss sg sslot sgen fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-fields fn2-pool) :measure (nfix k)
  :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (natp j) (natp entry) (natp off))
  :guard-hints (("Goal" :in-theory (disable fn2-idc-copy fn2-fields-rows fn2-run-layout-octets-max)))))
 (b* (((unless (and (posp k) (natp j) (natp entry) (natp off) (< (+ entry j) (fn2-fields-rows fn2-fields)))) (mv :ok fn2-fields fn2-pool))
      ((unless (fn2-run-layout-octets-max sid j))
       (fn2-succ-rehome-octets (- k 1) (+ 1 j) sid entry off sk ss sg sslot sgen fn2-fields fn2-pool))
      (row (+ entry j)) (len (fn2-fields-ref-len row fn2-fields))
      ((unless (and (natp (fn2-fields-ref-off row fn2-fields)) (natp len) (unsigned-byte-p 32 off) (unsigned-byte-p 32 (+ off len))
                    (unsigned-byte-p 32 sslot) (unsigned-byte-p 60 sgen)))
       (mv :bounds fn2-fields fn2-pool))
      ((mv code fn2-pool) (fn2-idc-copy len (fn2-fields-ref-slot row fn2-fields) (fn2-fields-ref-gen row fn2-fields)
                                        (fn2-fields-ref-off row fn2-fields) sk ss sg sslot sgen off fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-fields fn2-pool))
      (fn2-fields (fn2-fields-put row (ref-slot sslot) (ref-gen sgen) (ref-off off))))
  (fn2-succ-rehome-octets (- k 1) (+ 1 j) sid entry (+ off len) sk ss sg sslot sgen fn2-fields fn2-pool)))
(fn2-idc-fn-shape fn2-succ-rehome-octets (k j sid entry off sk ss sg sslot sgen fn2-fields fn2-pool) (fn2-fields fn2-pool)
 (fn2-fields fn2-pool) t (fn2-run-layout-octets-max fn2-fields-ref-len fn2-fields-ref-off fn2-fields-ref-slot fn2-fields-ref-gen fn2-idc-copy))

; Integer fields J.. of the row at ENTRY given :event take EVENT.
(defun fn2-succ-fill-events (k j entry events event fn2-fields)
 (declare (xargs :stobjs fn2-fields :measure (nfix k) :guard (and (fn2-fields-wfp fn2-fields) (natp j) (natp entry))))
 (cond ((not (and (posp k) (natp j) (natp entry) (< (+ entry j) (fn2-fields-rows fn2-fields)) (unsigned-byte-p 60 event))) fn2-fields)
       ((fn2-succ-has events j)
        (let ((fn2-fields (fn2-fields-set-value (+ entry j) event fn2-fields)))
         (fn2-succ-fill-events (- k 1) (+ 1 j) entry events event fn2-fields)))
       (t (fn2-succ-fill-events (- k 1) (+ 1 j) entry events event fn2-fields))))
(fn2-fields-preserves fn2-succ-fill-events (k j entry events event fn2-fields) :position nil :raw-rows t
 :hints (("Goal" :in-theory (disable fn2-succ-has))))

; BATCH's newest private overlay of SID (greatest SEQ) among rows O.. (K of
; them); BEST the row count when none.
(defun fn2-succ-newest-private (k o b sid best fn2-overlays)
 (declare (xargs :stobjs fn2-overlays :measure (nfix k) :guard (and (fn2-overlays-wfp fn2-overlays) (natp o))))
 (if (not (and (posp k) (natp o) (< o (fn2-overlays-rows fn2-overlays)))) best
  (fn2-succ-newest-private (- k 1) (+ 1 o) b sid
                           (if (and (equal (fn2-overlays-phase o fn2-overlays) *fn2-overlay-phase-private*)
                                    (equal (fn2-overlays-batch o fn2-overlays) b) (equal (fn2-overlays-schema o fn2-overlays) sid)
                                    (or (not (and (natp best) (< best (fn2-overlays-rows fn2-overlays))))
                                        (< (nfix (fn2-overlays-seq best fn2-overlays)) (nfix (fn2-overlays-seq o fn2-overlays)))))
                               o best)
                           fn2-overlays)))
; The overlay slot rows of SID and SIZE bytes go into for BATCH: its newest
; private one with room, else a spare that becomes BATCH's (its SEQ the
; engine's next). (mv code o engine overlays)
(defun fn2-succ-target (b sid size fn2-id-engine fn2-overlays)
 (declare (xargs :stobjs (fn2-id-engine fn2-overlays) :guard (and (fn2-id-engine-wfp fn2-id-engine) (fn2-overlays-wfp fn2-overlays))
  :guard-hints (("Goal" :in-theory (disable fn2-overlays-rows)))))
 (b* ((rows (fn2-overlays-rows fn2-overlays))
      (o (fn2-succ-newest-private rows 0 b sid rows fn2-overlays))
      ((when (and (natp o) (< o rows)
                  (<= (+ (nfix (fn2-overlays-fill o fn2-overlays)) (nfix size)) (nfix (fn2-overlays-cap o fn2-overlays)))
                  (< (nfix (fn2-overlays-count o fn2-overlays)) (nfix (fn2-overlays-icap o fn2-overlays)))))
       (mv :ok o fn2-id-engine fn2-overlays))
      (s (fn2-idc-find-overlay rows 0 *fn2-overlay-phase-spare* 0 fn2-overlays))
      ((unless (and (< s rows) (< 0 (fn2-id-engine-rows fn2-id-engine)) (unsigned-byte-p 60 b) (unsigned-byte-p 60 sid)))
       (mv :spare 0 fn2-id-engine fn2-overlays))
      (seq (+ 1 (nfix (fn2-id-engine-seq 0 fn2-id-engine))))
      ((unless (unsigned-byte-p 60 seq)) (mv :bounds 0 fn2-id-engine fn2-overlays))
      (fn2-id-engine (fn2-id-engine-set-seq 0 seq fn2-id-engine))
      (fn2-overlays (fn2-overlays-put s (phase *fn2-overlay-phase-private*) (batch b) (schema sid) (seq seq))))
  (mv :ok s fn2-id-engine fn2-overlays)))
(fn2-idc-op-shape fn2-succ-target (b sid size fn2-id-engine fn2-overlays) ((fn2-id-engine 2) (fn2-overlays 3))
 ((fn2-id-enginep fn2-id-engine) (fn2-id-engine-wfp fn2-id-engine) (fn2-overlaysp fn2-overlays) (fn2-overlays-wfp fn2-overlays)) :min
 (fn2-succ-newest-private fn2-idc-find-overlay fn2-overlays-fill fn2-overlays-cap fn2-overlays-count fn2-overlays-icap fn2-id-engine-seq))
(in-theory (disable fn2-succ-target))

;; Bind slot S (slot I) of TX into BATCH.
(defun fn2-succ-bind-slot (tx i s b0 b event fn2-succ-slots fn2-id-decides fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-succ-slots fn2-id-decides fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
  :guard (and (fn2-succ-slots-wfp fn2-succ-slots) (fn2-id-decides-wfp fn2-id-decides) (fn2-id-engine-wfp fn2-id-engine)
              (fn2-overlays-wfp fn2-overlays) (fn2-overlay-index-wfp fn2-overlay-index) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool)
              (natp s) (< s (fn2-succ-slots-rows fn2-succ-slots)) (natp i) (natp b0))
  :guard-hints (("Goal" :in-theory (disable fn2-idc-rehome fn2-succ-rehome-octets fn2-succ-fill-events fn2-succ-target
                                            fn2-id-record-insert fn2-ov-insert fn2-pool-reset fn2-fields-rows fn2-overlays-rows)))))
 (b* (((unless (and (natp s) (< s (fn2-succ-slots-rows fn2-succ-slots)) (natp i) (< i *fn2-succ-slots*) (natp b0)
                    (<= (+ b0 *fn2-idc-stride*) (fn2-fields-rows fn2-fields)) (< 0 (fn2-id-engine-rows fn2-id-engine))))
       (mv :bounds fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      (sid (fn2-succ-slots-sid s fn2-succ-slots)) (code (fn2-succ-slots-kind s fn2-succ-slots))
      (entry (+ b0 (* *fn2-succ-block* i)))
      ((when (equal (fn2-succ-slots-phase s fn2-succ-slots) *fn2-succ-slot-phase-empty*))
       (mv :ok fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      ((mv code2 fn2-fields fn2-pool)
       (cond ((equal code *fn2-succ-kind-record*)
              (b* ((fn2-fields (fn2-succ-fill-events 2 0 (+ entry *fn2-succ-eval*) (fn2-succ-slots-events s fn2-succ-slots) event fn2-fields)))
               (fn2-idc-rehome tx entry b0 fn2-id-decides fn2-id-engine fn2-fields fn2-pool)))
             ((equal code *fn2-succ-kind-insert*)
              (b* ((nf (nfix (fn2-run-layout-fields sid 0)))
                   (fn2-fields (fn2-succ-fill-events nf 0 entry (fn2-succ-slots-events s fn2-succ-slots) event fn2-fields))
                   (sslot (fn2-id-engine-slot 0 fn2-id-engine)) (sgen (fn2-id-engine-gen 0 fn2-id-engine))
                   ((unless (equal (fn2-succ-slots-oset s fn2-succ-slots) 1)) (mv :ok fn2-fields fn2-pool))
                   ((mv c fn2-pool) (fn2-pool-reset sslot sgen *fn2-idc-owner-kind* *fn2-idc-owner-slot* *fn2-idc-owner-gen* fn2-pool))
                   ((unless (eq c :ok)) (mv c fn2-fields fn2-pool)))
               (fn2-succ-rehome-octets nf 0 sid entry 0 (fn2-succ-slots-sk s fn2-succ-slots) (fn2-succ-slots-ss s fn2-succ-slots)
                                       (fn2-succ-slots-sg s fn2-succ-slots) sslot sgen fn2-fields fn2-pool)))
             ;; A fold row's octet key fields (C §4a) are copied into the
             ;; scratch as an insert's are.
             ((equal (fn2-succ-slots-oset s fn2-succ-slots) 1)
              (b* ((nk (nfix (fn2-run-layout-keys sid)))
                   (sslot (fn2-id-engine-slot 0 fn2-id-engine)) (sgen (fn2-id-engine-gen 0 fn2-id-engine))
                   ((mv c fn2-pool) (fn2-pool-reset sslot sgen *fn2-idc-owner-kind* *fn2-idc-owner-slot* *fn2-idc-owner-gen* fn2-pool))
                   ((unless (eq c :ok)) (mv c fn2-fields fn2-pool)))
               (fn2-succ-rehome-octets nk 0 sid entry 0 (fn2-succ-slots-sk s fn2-succ-slots) (fn2-succ-slots-ss s fn2-succ-slots)
                                       (fn2-succ-slots-sg s fn2-succ-slots) sslot sgen fn2-fields fn2-pool)))
             (t (mv :ok fn2-fields fn2-pool))))
      ((unless (eq code2 :ok)) (mv code2 fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      ((mv c o fn2-id-engine fn2-overlays) (fn2-succ-target b sid (fn2-succ-slots-size s fn2-succ-slots) fn2-id-engine fn2-overlays))
      ((unless (eq c :ok)) (mv c fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      ((unless (< (+ entry *fn2-succ-eval* 1) (fn2-fields-rows fn2-fields)))
       (mv :bounds fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      ((mv c fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
       (if (equal code *fn2-succ-kind-record*)
           (fn2-id-record-insert tx o (+ b0 *fn2-idc-rb*) entry
                                 (fn2-fields-value (+ entry *fn2-succ-eval*) fn2-fields) event
                                 (fn2-fields-value (+ entry *fn2-succ-eval* 1) fn2-fields)
                                 fn2-id-decides fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
         (fn2-ov-insert o entry (+ b0 *fn2-idc-eb*) fn2-overlays fn2-overlay-index fn2-fields fn2-pool))))
  (mv c fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)))
(fn2-idc-fn-shape fn2-succ-bind-slot (tx i s b0 b event fn2-succ-slots fn2-id-decides fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
 (fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
 (fn2-succ-slots fn2-id-decides fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool) t
 (fn2-succ-slots-sid fn2-succ-slots-kind fn2-succ-slots-phase fn2-succ-slots-events fn2-succ-slots-oset fn2-succ-slots-sk
  fn2-succ-slots-ss fn2-succ-slots-sg fn2-succ-slots-size fn2-run-layout-fields fn2-id-engine-slot fn2-id-engine-gen
  fn2-idc-rehome fn2-succ-fill-events fn2-succ-rehome-octets fn2-succ-target fn2-id-record-insert fn2-ov-insert fn2-fields-value
  fn2-run-layout-keys))
(defun fn2-succ-bind-slots (k i tx b0 b event fn2-succ-slots fn2-id-decides fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-succ-slots fn2-id-decides fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool) :measure (nfix k)
  :guard (and (fn2-succ-slots-wfp fn2-succ-slots) (fn2-id-decides-wfp fn2-id-decides) (fn2-id-engine-wfp fn2-id-engine)
              (fn2-overlays-wfp fn2-overlays) (fn2-overlay-index-wfp fn2-overlay-index) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool)
              (natp i) (natp tx) (natp b0))
  :guard-hints (("Goal" :in-theory (disable fn2-succ-bind-slot fn2-succ-slots-rows)))))
 (b* (((unless (and (posp k) (natp i) (< i *fn2-succ-slots*))) (mv :ok fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      (s (+ (* (nfix tx) *fn2-succ-slots*) i))
      ((unless (< s (fn2-succ-slots-rows fn2-succ-slots))) (mv :bounds fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      ((mv c fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
       (fn2-succ-bind-slot tx i s b0 b event fn2-succ-slots fn2-id-decides fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      ((unless (eq c :ok)) (mv c fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)))
  (fn2-succ-bind-slots (- k 1) (+ 1 i) tx b0 b event fn2-succ-slots fn2-id-decides fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)))
(fn2-idc-fn-shape fn2-succ-bind-slots (k i tx b0 b event fn2-succ-slots fn2-id-decides fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
 (fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
 (fn2-succ-slots fn2-id-decides fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool) t (fn2-succ-bind-slot))

; Whether some slot of TX from I (K of them) has a late octet arg not filled
; since its stage (C-S3a).
(defun fn2-succ-unfilled (k i tx fn2-succ-slots)
 (declare (xargs :stobjs fn2-succ-slots :measure (nfix k) :guard (and (fn2-succ-slots-wfp fn2-succ-slots) (natp i) (natp tx))))
 (and (posp k) (natp i) (< i *fn2-succ-slots*)
      (let ((s (+ (* (nfix tx) *fn2-succ-slots*) i)))
       (or (and (< s (fn2-succ-slots-rows fn2-succ-slots))
                (not (equal (fn2-succ-slots-phase s fn2-succ-slots) *fn2-succ-slot-phase-empty*))
                (not (equal (logand (nfix (fn2-succ-slots-late s fn2-succ-slots))
                                    (lognot (nfix (fn2-succ-slots-filled s fn2-succ-slots))))
                            0)))
           (fn2-succ-unfilled (- k 1) (+ 1 i) tx fn2-succ-slots)))))
(in-theory (disable fn2-succ-unfilled))

; Bind staged TX into BATCH at commit position EVENT (its :event args and
; its identity fact's binding): :ok, :state while a late octet arg is
; unfilled (C-S3a; nothing is bound), or an invariant failure by name.
(defun fn2-succ-bind (tx b event b0 fn2-succ-txns fn2-succ-slots fn2-id-decides fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-succ-txns fn2-succ-slots fn2-id-decides fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool) :guard t
  :guard-hints (("Goal" :in-theory (disable fn2-succ-bind-slots)))))
 (b* (((unless (and (fn2-succ-txns-wfp fn2-succ-txns) (fn2-succ-slots-wfp fn2-succ-slots) (fn2-id-decides-wfp fn2-id-decides)
                    (fn2-id-engine-wfp fn2-id-engine) (fn2-overlays-wfp fn2-overlays) (fn2-overlay-index-wfp fn2-overlay-index)
                    (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool)))
       (mv :state fn2-succ-txns fn2-id-decides fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      ((unless (and (natp tx) (< tx (fn2-succ-txns-rows fn2-succ-txns)) (< tx (fn2-id-decides-rows fn2-id-decides))
                    (posp b) (unsigned-byte-p 60 b) (unsigned-byte-p 60 event) (natp b0)))
       (mv :bounds fn2-succ-txns fn2-id-decides fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      ((unless (and (equal (fn2-succ-txns-phase tx fn2-succ-txns) *fn2-succ-phase-staged*)
                    (not (fn2-succ-unfilled *fn2-succ-slots* 0 tx fn2-succ-slots))))
       (mv :state fn2-succ-txns fn2-id-decides fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      ((mv code fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
       (fn2-succ-bind-slots *fn2-succ-slots* 0 tx b0 b event fn2-succ-slots fn2-id-decides fn2-id-engine fn2-overlays fn2-overlay-index
                            fn2-fields fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-succ-txns fn2-id-decides fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool))
      (fn2-id-decides (if (equal (fn2-succ-txns-record tx fn2-succ-txns) 0) fn2-id-decides
                        (fn2-id-decides-set-phase tx *fn2-id-decide-phase-held* fn2-id-decides)))
      (fn2-succ-txns (fn2-succ-txns-put tx (phase *fn2-succ-phase-bound*) (batch b) (event event))))
  (mv :ok fn2-succ-txns fn2-id-decides fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)))
(fn2-idc-fn-shape fn2-succ-bind (tx b event b0 fn2-succ-txns fn2-succ-slots fn2-id-decides fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
 (fn2-succ-txns fn2-id-decides fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
 (fn2-succ-txns fn2-succ-slots fn2-id-decides fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool) t
 (fn2-succ-txns-phase fn2-succ-txns-record fn2-succ-bind-slots fn2-succ-unfilled))

; Release TX at its outcome: its slots and its decision free again. A
; transaction bound to a batch not yet published or dropped is :state.
(defun fn2-succ-release-slots (k s fn2-succ-slots)
 (declare (xargs :stobjs fn2-succ-slots :measure (nfix k) :guard (and (fn2-succ-slots-wfp fn2-succ-slots) (natp s))))
 (if (not (and (posp k) (natp s) (< s (fn2-succ-slots-rows fn2-succ-slots)))) fn2-succ-slots
  (let ((fn2-succ-slots (fn2-succ-slots-put s (phase *fn2-succ-slot-phase-empty*) (set 0) (events 0) (outs 0) (found 0) (size 0) (oset 0))))
   (fn2-succ-release-slots (- k 1) (+ 1 s) fn2-succ-slots))))
(fn2-succ-slots-preserves fn2-succ-release-slots (k s fn2-succ-slots) :position nil :raw-rows t)
(defun fn2-succ-release (tx fn2-succ-txns fn2-succ-slots fn2-id-decides)
 (declare (xargs :stobjs (fn2-succ-txns fn2-succ-slots fn2-id-decides) :guard t))
 (b* (((unless (and (fn2-succ-txns-wfp fn2-succ-txns) (fn2-succ-slots-wfp fn2-succ-slots) (fn2-id-decides-wfp fn2-id-decides)))
       (mv :state fn2-succ-txns fn2-succ-slots fn2-id-decides))
      ((unless (and (natp tx) (< tx (fn2-succ-txns-rows fn2-succ-txns)) (< tx (fn2-id-decides-rows fn2-id-decides))))
       (mv :bounds fn2-succ-txns fn2-succ-slots fn2-id-decides))
      ((when (equal (fn2-succ-txns-phase tx fn2-succ-txns) *fn2-succ-phase-bound*)) (mv :state fn2-succ-txns fn2-succ-slots fn2-id-decides))
      (fn2-succ-slots (fn2-succ-release-slots *fn2-succ-slots* (* tx *fn2-succ-slots*) fn2-succ-slots))
      (fn2-succ-txns (fn2-succ-txns-put tx (phase *fn2-succ-phase-idle*) (record 0) (batch 0) (event 0) (ri 0)
                                        (rstate *fn2-succ-resolve-fresh*) (rbound 0)
                                        (lphase *fn2-succ-lookup-idle*) (lbound 0) (lrow 0) (lver 0)))
      (fn2-id-decides (fn2-id-decides-set-phase tx *fn2-id-decide-phase-idle* fn2-id-decides)))
  (mv :ok fn2-succ-txns fn2-succ-slots fn2-id-decides)))
(fn2-idc-fn-shape fn2-succ-release (tx fn2-succ-txns fn2-succ-slots fn2-id-decides) (fn2-succ-txns fn2-succ-slots fn2-id-decides)
 (fn2-succ-txns fn2-succ-slots fn2-id-decides) t (fn2-succ-txns-phase fn2-succ-release-slots))

; ---------------------------------------------------------------------------
; Publication of batch B (B, after the root swap, before any member result):
; every transaction bound to B is published (the bucket stamp of its
; identity fact moves, so a decision in flight around it refuses :stale) and
; every private overlay of B, of every schema, becomes readable in the same
; step, covering B's last commit position. Drop (B, a refused batch): its
; transactions are :open again (stage again) with their decisions done, its
; private overlays' arenas released.
;; Three passes over the transactions bound to B: their identity facts'
;; bucket stamps, their greatest commit position, their phase.
(defun fn2-succ-bound-to (tx b fn2-succ-txns)
 (declare (xargs :stobjs fn2-succ-txns :guard (fn2-succ-txns-wfp fn2-succ-txns)))
 (and (natp tx) (< tx (fn2-succ-txns-rows fn2-succ-txns))
      (equal (fn2-succ-txns-phase tx fn2-succ-txns) *fn2-succ-phase-bound*) (equal (fn2-succ-txns-batch tx fn2-succ-txns) b)))
(defun fn2-succ-publish-stamps (k tx b fn2-succ-txns fn2-id-decides fn2-id-stamps)
 (declare (xargs :stobjs (fn2-succ-txns fn2-id-decides fn2-id-stamps) :measure (nfix k)
  :guard (and (fn2-succ-txns-wfp fn2-succ-txns) (fn2-id-decides-wfp fn2-id-decides) (fn2-id-stamps-wfp fn2-id-stamps) (natp tx))))
 (b* (((unless (and (posp k) (natp tx) (< tx (fn2-succ-txns-rows fn2-succ-txns)))) (mv :ok fn2-id-stamps))
      ((unless (and (fn2-succ-bound-to tx b fn2-succ-txns) (not (equal (fn2-succ-txns-record tx fn2-succ-txns) 0))))
       (fn2-succ-publish-stamps (- k 1) (+ 1 tx) b fn2-succ-txns fn2-id-decides fn2-id-stamps))
      ((unless (< tx (fn2-id-decides-rows fn2-id-decides))) (mv :bounds fn2-id-stamps))
      (bucket (fn2-id-decides-bucket tx fn2-id-decides))
      ((unless (and (natp bucket) (< bucket (fn2-id-stamps-rows fn2-id-stamps)))) (mv :bounds fn2-id-stamps))
      (stamp (+ 1 (nfix (fn2-id-stamps-gen bucket fn2-id-stamps))))
      ((unless (unsigned-byte-p 60 stamp)) (mv :bounds fn2-id-stamps))
      (fn2-id-stamps (fn2-id-stamps-set-gen bucket stamp fn2-id-stamps)))
  (fn2-succ-publish-stamps (- k 1) (+ 1 tx) b fn2-succ-txns fn2-id-decides fn2-id-stamps)))
(fn2-id-stamps-preserves fn2-succ-publish-stamps (k tx b fn2-succ-txns fn2-id-decides fn2-id-stamps) :position 1
 :hints (("Goal" :in-theory (disable fn2-succ-bound-to fn2-succ-txns-record fn2-id-decides-bucket fn2-id-decides-rows fn2-succ-txns-rows))))
(defun fn2-succ-batch-cov (k tx b cov fn2-succ-txns)
 (declare (xargs :stobjs fn2-succ-txns :measure (nfix k) :guard (and (fn2-succ-txns-wfp fn2-succ-txns) (natp tx))))
 (if (not (and (posp k) (natp tx))) (nfix cov)
  (fn2-succ-batch-cov (- k 1) (+ 1 tx) b
                      (if (fn2-succ-bound-to tx b fn2-succ-txns) (max (nfix cov) (nfix (fn2-succ-txns-event tx fn2-succ-txns))) (nfix cov))
                      fn2-succ-txns)))
(defthm fn2-succ-batch-cov-natp (natp (fn2-succ-batch-cov k tx b cov fn2-succ-txns)) :rule-classes :type-prescription)
(defun fn2-succ-publish-marks (k tx b fn2-succ-txns)
 (declare (xargs :stobjs fn2-succ-txns :measure (nfix k) :guard (and (fn2-succ-txns-wfp fn2-succ-txns) (natp tx))))
 (cond ((not (and (posp k) (natp tx) (< tx (fn2-succ-txns-rows fn2-succ-txns)))) fn2-succ-txns)
       ((fn2-succ-bound-to tx b fn2-succ-txns)
        (let ((fn2-succ-txns (fn2-succ-txns-set-phase tx *fn2-succ-phase-published* fn2-succ-txns)))
         (fn2-succ-publish-marks (- k 1) (+ 1 tx) b fn2-succ-txns)))
       (t (fn2-succ-publish-marks (- k 1) (+ 1 tx) b fn2-succ-txns))))
(fn2-succ-txns-preserves fn2-succ-publish-marks (k tx b fn2-succ-txns) :position nil :raw-rows t
 :hints (("Goal" :in-theory (disable fn2-succ-bound-to))))
(in-theory (disable fn2-succ-bound-to fn2-succ-publish-stamps fn2-succ-batch-cov fn2-succ-publish-marks))
(defun fn2-succ-publish-overlays (k o b cov fn2-overlays)
 (declare (xargs :stobjs fn2-overlays :measure (nfix k) :guard (and (fn2-overlays-wfp fn2-overlays) (natp k) (natp o))))
 (cond ((or (zp k) (not (and (natp o) (< o (fn2-overlays-rows fn2-overlays)) (unsigned-byte-p 60 cov)))) (mv :ok fn2-overlays))
       ((not (and (equal (fn2-overlays-phase o fn2-overlays) *fn2-overlay-phase-private*)
                  (equal (fn2-overlays-batch o fn2-overlays) b)))
        (fn2-succ-publish-overlays (- k 1) (+ 1 o) b cov fn2-overlays))
       (t (let ((fn2-overlays (fn2-overlays-put o (phase *fn2-overlay-phase-frozen*) (batch 0) (cov cov))))
           (fn2-succ-publish-overlays (- k 1) (+ 1 o) b cov fn2-overlays)))))
(fn2-overlays-preserves fn2-succ-publish-overlays (k o b cov fn2-overlays) :position 1)
(in-theory (disable fn2-succ-publish-overlays))
(defun fn2-succ-publish (b fn2-succ-txns fn2-id-decides fn2-id-stamps fn2-overlays fn2-id-engine)
 (declare (xargs :stobjs (fn2-succ-txns fn2-id-decides fn2-id-stamps fn2-overlays fn2-id-engine) :guard t))
 (b* (((unless (and (fn2-succ-txns-wfp fn2-succ-txns) (fn2-id-decides-wfp fn2-id-decides) (fn2-id-stamps-wfp fn2-id-stamps)
                    (fn2-overlays-wfp fn2-overlays) (fn2-id-engine-wfp fn2-id-engine) (< 0 (fn2-id-engine-rows fn2-id-engine))))
       (mv :state fn2-succ-txns fn2-id-stamps fn2-overlays fn2-id-engine))
      ((unless (and (posp b) (unsigned-byte-p 60 b))) (mv :bounds fn2-succ-txns fn2-id-stamps fn2-overlays fn2-id-engine))
      (n (fn2-succ-txns-rows fn2-succ-txns))
      ((mv code fn2-id-stamps) (fn2-succ-publish-stamps n 0 b fn2-succ-txns fn2-id-decides fn2-id-stamps))
      ((unless (eq code :ok)) (mv code fn2-succ-txns fn2-id-stamps fn2-overlays fn2-id-engine))
      (cov (fn2-succ-batch-cov n 0 b 0 fn2-succ-txns))
      (fn2-succ-txns (fn2-succ-publish-marks n 0 b fn2-succ-txns))
      ((unless (unsigned-byte-p 60 cov)) (mv :bounds fn2-succ-txns fn2-id-stamps fn2-overlays fn2-id-engine))
      ((mv code fn2-overlays) (fn2-succ-publish-overlays (fn2-overlays-rows fn2-overlays) 0 b cov fn2-overlays))
      ;; The frontier: batches publish in commit order, so the greatest
      ;; position any bound transaction of this batch committed at.
      (fn2-id-engine (if (< (nfix (fn2-id-engine-published 0 fn2-id-engine)) cov)
                         (fn2-id-engine-set-published 0 cov fn2-id-engine)
                       fn2-id-engine)))
  (mv code fn2-succ-txns fn2-id-stamps fn2-overlays fn2-id-engine)))
(fn2-idc-fn-shape fn2-succ-publish (b fn2-succ-txns fn2-id-decides fn2-id-stamps fn2-overlays fn2-id-engine)
 (fn2-succ-txns fn2-id-stamps fn2-overlays fn2-id-engine)
 (fn2-succ-txns fn2-id-decides fn2-id-stamps fn2-overlays fn2-id-engine) t (fn2-id-engine-published fn2-succ-publish-stamps fn2-succ-batch-cov fn2-succ-publish-marks
  fn2-succ-publish-overlays))

; The greatest published commit position: (mv code position).
(defun fn2-succ-published (fn2-id-engine)
 (declare (xargs :stobjs fn2-id-engine :guard t))
 (if (and (fn2-id-engine-wfp fn2-id-engine) (< 0 (fn2-id-engine-rows fn2-id-engine)))
     (mv :ok (nfix (fn2-id-engine-published 0 fn2-id-engine)))
   (mv :state 0)))

(defun fn2-succ-drop-txns (k tx b fn2-succ-txns fn2-id-decides)
 (declare (xargs :stobjs (fn2-succ-txns fn2-id-decides) :measure (nfix k)
  :guard (and (fn2-succ-txns-wfp fn2-succ-txns) (fn2-id-decides-wfp fn2-id-decides) (natp tx))))
 (b* (((unless (and (posp k) (natp tx) (< tx (fn2-succ-txns-rows fn2-succ-txns)))) (mv :ok fn2-succ-txns fn2-id-decides))
      ((unless (and (equal (fn2-succ-txns-phase tx fn2-succ-txns) *fn2-succ-phase-bound*) (equal (fn2-succ-txns-batch tx fn2-succ-txns) b)))
       (fn2-succ-drop-txns (- k 1) (+ 1 tx) b fn2-succ-txns fn2-id-decides))
      (fn2-succ-txns (fn2-succ-txns-put tx (phase *fn2-succ-phase-open*) (batch 0) (event 0)))
      (fn2-id-decides (if (and (< tx (fn2-id-decides-rows fn2-id-decides))
                               (equal (fn2-id-decides-phase tx fn2-id-decides) *fn2-id-decide-phase-held*))
                          (fn2-id-decides-set-phase tx *fn2-id-decide-phase-done* fn2-id-decides)
                        fn2-id-decides)))
  (fn2-succ-drop-txns (- k 1) (+ 1 tx) b fn2-succ-txns fn2-id-decides)))
(fn2-idc-op-shape fn2-succ-drop-txns (k tx b fn2-succ-txns fn2-id-decides) ((fn2-succ-txns 1) (fn2-id-decides 2))
 ((fn2-succ-txnsp fn2-succ-txns) (fn2-succ-txns-wfp fn2-succ-txns) (fn2-id-decidesp fn2-id-decides) (fn2-id-decides-wfp fn2-id-decides)) :min
 (fn2-succ-txns-phase fn2-succ-txns-batch fn2-id-decides-phase fn2-succ-txns-rows fn2-id-decides-rows))
(in-theory (disable fn2-succ-drop-txns))
(defun fn2-succ-drop-overlays (k o b fn2-overlays fn2-pool)
 (declare (xargs :stobjs (fn2-overlays fn2-pool) :measure (nfix k)
  :guard (and (fn2-overlays-wfp fn2-overlays) (fn2-pool-wfp fn2-pool) (natp k) (natp o)) :guard-hints (("Goal" :in-theory (disable fn2-pool-reserve fn2-pool-release fn2-pool-reset fn2-pool-read fn2-pool-write
                                             fn2-pool-class-for fn2-ov-start fn2-ov-advance fn2-id-record-insert fn2-ov-insert
                                             fn2-ov-locate fn2-ov-entry fn2-run-copy-row fn2-fold-apply fn2-fold-assign
                                             fn2-run-layout-size fn2-run-lookup-step fn2-run-cursor-start
                                             fn2-fields-rows fn2-succ-slots-rows fn2-succ-txns-rows fn2-overlays-rows)))))
 (cond ((or (zp k) (not (and (natp o) (< o (fn2-overlays-rows fn2-overlays))))) (mv :ok fn2-overlays fn2-pool))
       ((not (and (equal (fn2-overlays-phase o fn2-overlays) *fn2-overlay-phase-private*)
                  (equal (fn2-overlays-batch o fn2-overlays) b)))
        (fn2-succ-drop-overlays (- k 1) (+ 1 o) b fn2-overlays fn2-pool))
       (t (b* ((slot (fn2-overlays-slot o fn2-overlays)) (gen (fn2-overlays-gen o fn2-overlays))
               ((unless (fn2-pool-release-countp slot fn2-pool)) (mv :bounds fn2-overlays fn2-pool))
               ((mv code fn2-pool) (fn2-pool-release slot gen *fn2-idc-owner-kind* *fn2-idc-owner-slot* *fn2-idc-owner-gen* fn2-pool))
               ((unless (eq code :ok)) (mv code fn2-overlays fn2-pool))
               (fn2-overlays (fn2-overlays-put o (phase *fn2-overlay-phase-free*) (batch 0) (count 0) (fill 0) (seq 0))))
           (fn2-succ-drop-overlays (- k 1) (+ 1 o) b fn2-overlays fn2-pool)))))
(fn2-overlays-preserves fn2-succ-drop-overlays (k o b fn2-overlays fn2-pool) :position 1 :disable nil
 :hints (("Goal" :in-theory (disable fn2-pool-release fn2-pool-release-countp fn2-pool-rows fn2-overlays-rows))))
(fn2-pool-preserves fn2-succ-drop-overlays (k o b fn2-overlays fn2-pool) :position 2 :prefix "-POOL-PRESERVES"
 :hints (("Goal" :in-theory (disable fn2-pool-release fn2-pool-release-countp fn2-pool-rows fn2-overlays-rows))))
(in-theory (disable fn2-succ-drop-overlays))
(defun fn2-succ-drop (b fn2-succ-txns fn2-id-decides fn2-overlays fn2-pool)
 (declare (xargs :stobjs (fn2-succ-txns fn2-id-decides fn2-overlays fn2-pool) :guard t))
 (b* (((unless (and (fn2-succ-txns-wfp fn2-succ-txns) (fn2-id-decides-wfp fn2-id-decides) (fn2-overlays-wfp fn2-overlays) (fn2-pool-wfp fn2-pool)))
       (mv :state fn2-succ-txns fn2-id-decides fn2-overlays fn2-pool))
      ((unless (and (posp b) (unsigned-byte-p 60 b))) (mv :bounds fn2-succ-txns fn2-id-decides fn2-overlays fn2-pool))
      ((mv & fn2-succ-txns fn2-id-decides) (fn2-succ-drop-txns (fn2-succ-txns-rows fn2-succ-txns) 0 b fn2-succ-txns fn2-id-decides))
      ((mv code fn2-overlays fn2-pool) (fn2-succ-drop-overlays (fn2-overlays-rows fn2-overlays) 0 b fn2-overlays fn2-pool)))
  (mv code fn2-succ-txns fn2-id-decides fn2-overlays fn2-pool)))
(fn2-idc-fn-shape fn2-succ-drop (b fn2-succ-txns fn2-id-decides fn2-overlays fn2-pool) (fn2-succ-txns fn2-id-decides fn2-overlays fn2-pool)
 (fn2-succ-txns fn2-id-decides fn2-overlays fn2-pool) t (fn2-succ-drop-txns fn2-succ-drop-overlays))

; ---------------------------------------------------------------------------
; Costs (the bases: fn2/docs/c-ordered-runs.md §7 C-SUCCESSOR).
(defcost fn2-successor-put :answers (:bounds :kind :ok :schema :state)
 :tables (fn2-core-succ-txns fn2-core-succ-slots)
 :doc "Declare one write slot of a transaction (schema and kind).")
(defcost fn2-successor-arg :answers (:bounds :kind :ok :state)
 :tables (fn2-core-succ-txns fn2-core-succ-slots fn2-core-fields)
 :doc "Give one argument of a write slot: a value, the member's commit position, or a field of an earlier slot's row.")
(defcost fn2-successor-arg-octets :answers (:bounds :kind :ok :owner :state)
 :tables (fn2-core-succ-txns fn2-core-succ-slots fn2-core-fields)
 :doc "Give one octet argument of an insert slot by reference.")
(defcost fn2-successor-arg-octets-late :answers (:bounds :kind :ok :state)
 :tables (fn2-core-succ-txns fn2-core-succ-slots fn2-core-fields)
 :doc "Declare one octet argument of an insert slot given after stage, with its bound.")
(defcost fn2-successor-fill-octets :answers (:bounds :kind :ok :owner :state)
 :tables (fn2-core-succ-slots fn2-core-fields)
 :doc "Give a staged slot's late octet argument by reference.")
(defcost fn2-successor-resolve :answers (:bad-magic :bounds :done :end :entry :format :invariant :length :lost :miss :more :noncanonical
  :ok :owner :part :payload :schema :stale :state :truncated :unknown-tag :wide)
 :bytes 4096
 :tables (fn2-core-succ-txns fn2-core-succ-slots fn2-core-run-cursors fn2-core-run-paths fn2-core-fields)
 :doc "One bounded step reading a write slot's key in the installed runs: one run selection or one lookup step of at most 4,096 pool reads.")
(defcost fn2-successor-stage :answers (:bounds :capacity :done :duplicate :event :evidence :full :identity-conflict-bound :invariant
  :length :more :noncanonical :ok :owner :part :payload :range :refused :schema :stale :state
  :truncated :unknown-tag :wide)
 :bytes 4096
 :tables (fn2-core-succ-txns fn2-core-succ-slots fn2-core-id-engine fn2-core-overlays fn2-core-fields fn2-core-pool)
 :doc "Stage every write slot against the tip (one located entry per overlay of its schema), apply its fold step, and hold room (at most one arena per schema written).")
(defcost fn2-successor-out :answers (:bounds :kind :ok :state)
 :doc "Read one field of a staged write slot's row.")
(defcost fn2-successor-bind :answers (:bounds :done :duplicate :full :invariant :length :more :noncanonical :ok :overlap :owner :part
  :payload :schema :spare :stale :state :truncated :unknown-tag :value :wide)
 :bytes 8192
 :tables (fn2-core-succ-txns fn2-core-id-decides fn2-core-id-engine fn2-core-overlays fn2-core-overlay-index fn2-core-fields fn2-core-pool)
 :doc "Insert every staged row into its batch's private overlays (octet arguments copied, at most 4 KiB per slot).")
(defcost fn2-successor-release :answers (:bounds :ok :state)
 :tables (fn2-core-succ-txns fn2-core-succ-slots fn2-core-id-decides)
 :doc "Free a transaction's write slots and its decision at its outcome.")
(defcost fn2-successor-published :answers (:ok :state)
 :doc "Read the greatest published commit position (D's read frontier, C-S4 (c)).")
(defcost fn2-successor-publish :answers (:bounds :ok :state)
 :tables (fn2-core-succ-txns fn2-core-id-stamps fn2-core-overlays fn2-core-id-engine)
 :doc "Make a batch's private overlays of every schema readable and move its identity facts' bucket stamps (one pass over transaction and overlay rows).")
(defcost fn2-successor-drop :answers (:bounds :ok :owner :retired :stale :state)
 :tables (fn2-core-succ-txns fn2-core-id-decides fn2-core-overlays fn2-core-pool)
 :doc "Free a refused batch's private overlays; its transactions stage again.")

; Core wrappers, materialized after the core instance (assembly-callbacks-c,
; after fn2-identity-core-events). The stripe base of a transaction is the
; identity decision's (fn2-idc-stripe); a transaction past the rows is
; :bounds before anything is read.
(defmacro fn2-succ-wrap (name args children outs call &optional (code 'code) prefix)
 `(progn
   (defun ,name (,@args fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (stobj-let ,children
     (,@prefix ,code ,@outs)
     ,call
     (mv ,@prefix ,code fn2-core)))
   (fn2-core-preserves ,name (,@args fn2-core) :position ,(+ 1 (len prefix)) :rows nil :hints (("Goal" :in-theory (enable fn2-core-wfp))))))
(defmacro fn2-successor-prepare-events ()
 '(progn
   (fn2-succ-wrap fn2-successor-put (tx i sid kind)
    ((fn2-succ-txns (fn2-core-succ-txns fn2-core)) (fn2-succ-slots (fn2-core-succ-slots fn2-core)))
    (fn2-succ-txns fn2-succ-slots)
    (fn2-succ-put tx i sid kind fn2-succ-txns fn2-succ-slots))
   (fn2-succ-wrap fn2-successor-arg (tx i j src value)
    ((fn2-succ-txns (fn2-core-succ-txns fn2-core)) (fn2-succ-slots (fn2-core-succ-slots fn2-core))
     (fn2-id-decides (fn2-core-id-decides fn2-core)) (fn2-fields (fn2-core-fields fn2-core)) (fn2-fc (fn2-core-fc fn2-core)))
    (fn2-succ-txns fn2-succ-slots fn2-fields)
    (mv-let (c b0) (fn2-idc-stripe tx (fn2-fc-rows fn2-fc) fn2-id-decides fn2-fields)
     (if (eq c :ok) (fn2-succ-arg tx i j src value b0 fn2-succ-txns fn2-succ-slots fn2-fields)
       (mv c fn2-succ-txns fn2-succ-slots fn2-fields))))
   (fn2-succ-wrap fn2-successor-arg-octets (tx i j slot gen off len okind oslot ogen)
    ((fn2-succ-txns (fn2-core-succ-txns fn2-core)) (fn2-succ-slots (fn2-core-succ-slots fn2-core))
     (fn2-id-decides (fn2-core-id-decides fn2-core)) (fn2-fields (fn2-core-fields fn2-core)) (fn2-fc (fn2-core-fc fn2-core)))
    (fn2-succ-txns fn2-succ-slots fn2-fields)
    (mv-let (c b0) (fn2-idc-stripe tx (fn2-fc-rows fn2-fc) fn2-id-decides fn2-fields)
     (if (eq c :ok) (fn2-succ-arg-octets tx i j slot gen off len okind oslot ogen b0 fn2-succ-txns fn2-succ-slots fn2-fields)
       (mv c fn2-succ-txns fn2-succ-slots fn2-fields))))
   (fn2-succ-wrap fn2-successor-arg-octets-late (tx i j max)
    ((fn2-succ-txns (fn2-core-succ-txns fn2-core)) (fn2-succ-slots (fn2-core-succ-slots fn2-core))
     (fn2-id-decides (fn2-core-id-decides fn2-core)) (fn2-fields (fn2-core-fields fn2-core)) (fn2-fc (fn2-core-fc fn2-core)))
    (fn2-succ-txns fn2-succ-slots fn2-fields)
    (mv-let (c b0) (fn2-idc-stripe tx (fn2-fc-rows fn2-fc) fn2-id-decides fn2-fields)
     (if (eq c :ok) (fn2-succ-arg-octets-late tx i j max b0 fn2-succ-txns fn2-succ-slots fn2-fields)
       (mv c fn2-succ-txns fn2-succ-slots fn2-fields))))
   (fn2-succ-wrap fn2-successor-resolve (tx budget)
    ((fn2-succ-txns (fn2-core-succ-txns fn2-core)) (fn2-succ-slots (fn2-core-succ-slots fn2-core))
     (fn2-id-decides (fn2-core-id-decides fn2-core)) (fn2-run-installed (fn2-core-run-installed fn2-core))
     (fn2-run-cursors (fn2-core-run-cursors fn2-core)) (fn2-run-paths (fn2-core-run-paths fn2-core))
     (fn2-run-cache (fn2-core-run-cache fn2-core)) (fn2-fields (fn2-core-fields fn2-core)) (fn2-pool (fn2-core-pool fn2-core))
     (fn2-fc (fn2-core-fc fn2-core)))
    (fn2-succ-txns fn2-succ-slots fn2-run-cursors fn2-run-paths fn2-fields)
    (mv-let (c b0) (fn2-idc-stripe tx (fn2-fc-rows fn2-fc) fn2-id-decides fn2-fields)
     (if (eq c :ok)
         (fn2-succ-resolve tx budget b0 fn2-succ-txns fn2-succ-slots fn2-id-decides fn2-run-installed fn2-run-cursors fn2-run-paths
                           fn2-run-cache fn2-fields fn2-pool)
       (mv c fn2-succ-txns fn2-succ-slots fn2-run-cursors fn2-run-paths fn2-fields)))
    answer)
   (in-theory (disable fn2-successor-put fn2-successor-arg fn2-successor-arg-octets fn2-successor-arg-octets-late fn2-successor-resolve))
   (assert-event (fn2-assert-compliant-p '(fn2-successor-put fn2-successor-arg fn2-successor-arg-octets fn2-successor-arg-octets-late fn2-successor-resolve) (w state)))))
; The stage-side wrappers, in their own assembly book (assembly-callbacks-c-
; commit): the one-minute rule (C-SUCCESSOR-BOOK).
(defmacro fn2-successor-commit-events ()
 '(progn
   (fn2-succ-wrap fn2-successor-stage (tx)
    ((fn2-succ-txns (fn2-core-succ-txns fn2-core)) (fn2-succ-slots (fn2-core-succ-slots fn2-core))
     (fn2-id-decides (fn2-core-id-decides fn2-core)) (fn2-id-stamps (fn2-core-id-stamps fn2-core))
     (fn2-run-installed (fn2-core-run-installed fn2-core)) (fn2-id-engine (fn2-core-id-engine fn2-core))
     (fn2-overlays (fn2-core-overlays fn2-core)) (fn2-overlay-index (fn2-core-overlay-index fn2-core))
     (fn2-fields (fn2-core-fields fn2-core)) (fn2-pool (fn2-core-pool fn2-core)) (fn2-fc (fn2-core-fc fn2-core)))
    (fn2-succ-txns fn2-succ-slots fn2-id-engine fn2-overlays fn2-fields fn2-pool)
    (mv-let (c b0) (fn2-idc-stripe tx (fn2-fc-rows fn2-fc) fn2-id-decides fn2-fields)
     (if (eq c :ok)
         (fn2-succ-stage tx b0 fn2-succ-txns fn2-succ-slots fn2-id-decides fn2-id-stamps fn2-run-installed fn2-id-engine
                         fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
       (mv c 0 fn2-succ-txns fn2-succ-slots fn2-id-engine fn2-overlays fn2-fields fn2-pool)))
    i (code))
   (defun fn2-successor-out (tx i f fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (stobj-let ((fn2-succ-txns (fn2-core-succ-txns fn2-core)) (fn2-succ-slots (fn2-core-succ-slots fn2-core))
                (fn2-id-decides (fn2-core-id-decides fn2-core)) (fn2-fields (fn2-core-fields fn2-core)) (fn2-fc (fn2-core-fc fn2-core)))
     (code value)
     (mv-let (c b0) (fn2-idc-stripe tx (fn2-fc-rows fn2-fc) fn2-id-decides fn2-fields)
      (if (eq c :ok) (fn2-succ-out tx i f b0 fn2-succ-txns fn2-succ-slots fn2-fields) (mv c 0)))
     (mv code value)))
   (fn2-succ-wrap fn2-successor-fill-octets (tx i j slot gen off len okind oslot ogen)
    ((fn2-succ-txns (fn2-core-succ-txns fn2-core)) (fn2-succ-slots (fn2-core-succ-slots fn2-core))
     (fn2-id-decides (fn2-core-id-decides fn2-core)) (fn2-fields (fn2-core-fields fn2-core)) (fn2-fc (fn2-core-fc fn2-core)))
    (fn2-succ-slots fn2-fields)
    (mv-let (c b0) (fn2-idc-stripe tx (fn2-fc-rows fn2-fc) fn2-id-decides fn2-fields)
     (if (eq c :ok) (fn2-succ-fill-octets tx i j slot gen off len okind oslot ogen b0 fn2-succ-txns fn2-succ-slots fn2-fields)
       (mv c fn2-succ-slots fn2-fields))))
   (fn2-succ-wrap fn2-successor-bind (tx batch event)
    ((fn2-succ-txns (fn2-core-succ-txns fn2-core)) (fn2-succ-slots (fn2-core-succ-slots fn2-core))
     (fn2-id-decides (fn2-core-id-decides fn2-core)) (fn2-id-engine (fn2-core-id-engine fn2-core))
     (fn2-overlays (fn2-core-overlays fn2-core)) (fn2-overlay-index (fn2-core-overlay-index fn2-core))
     (fn2-fields (fn2-core-fields fn2-core)) (fn2-pool (fn2-core-pool fn2-core)) (fn2-fc (fn2-core-fc fn2-core)))
    (fn2-succ-txns fn2-id-decides fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
    (mv-let (c b0) (fn2-idc-stripe tx (fn2-fc-rows fn2-fc) fn2-id-decides fn2-fields)
     (if (eq c :ok)
         (fn2-succ-bind tx batch event b0 fn2-succ-txns fn2-succ-slots fn2-id-decides fn2-id-engine fn2-overlays fn2-overlay-index
                        fn2-fields fn2-pool)
       (mv c fn2-succ-txns fn2-id-decides fn2-id-engine fn2-overlays fn2-overlay-index fn2-fields fn2-pool))))
   (fn2-succ-wrap fn2-successor-release (tx)
    ((fn2-succ-txns (fn2-core-succ-txns fn2-core)) (fn2-succ-slots (fn2-core-succ-slots fn2-core))
     (fn2-id-decides (fn2-core-id-decides fn2-core)))
    (fn2-succ-txns fn2-succ-slots fn2-id-decides)
    (fn2-succ-release tx fn2-succ-txns fn2-succ-slots fn2-id-decides))
   (fn2-succ-wrap fn2-succ-core-publish (batch)
    ((fn2-succ-txns (fn2-core-succ-txns fn2-core)) (fn2-id-decides (fn2-core-id-decides fn2-core))
     (fn2-id-stamps (fn2-core-id-stamps fn2-core)) (fn2-overlays (fn2-core-overlays fn2-core))
     (fn2-id-engine (fn2-core-id-engine fn2-core)))
    (fn2-succ-txns fn2-id-stamps fn2-overlays fn2-id-engine)
    (fn2-succ-publish batch fn2-succ-txns fn2-id-decides fn2-id-stamps fn2-overlays fn2-id-engine))
   ;; The greatest published commit position: (mv code position).
   (defun fn2-successor-published (fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (stobj-let ((fn2-id-engine (fn2-core-id-engine fn2-core)))
     (code position) (fn2-succ-published fn2-id-engine) (mv code position)))
   (fn2-succ-wrap fn2-succ-core-drop (batch)
    ((fn2-succ-txns (fn2-core-succ-txns fn2-core)) (fn2-id-decides (fn2-core-id-decides fn2-core))
     (fn2-overlays (fn2-core-overlays fn2-core)) (fn2-pool (fn2-core-pool fn2-core)))
    (fn2-succ-txns fn2-id-decides fn2-overlays fn2-pool)
    (fn2-succ-drop batch fn2-succ-txns fn2-id-decides fn2-overlays fn2-pool))
   ; B5-4: publish and drop are B's constrained hooks; these are their attachments.
   (defattach (fn2-successor-publish fn2-succ-core-publish)
    :hints (("Goal" :in-theory (enable fn2-succ-core-publish))))
   (defattach (fn2-successor-drop fn2-succ-core-drop)
    :hints (("Goal" :in-theory (enable fn2-succ-core-drop))))
   (in-theory (disable fn2-successor-stage fn2-successor-out fn2-successor-fill-octets fn2-successor-bind fn2-successor-release fn2-succ-core-publish fn2-successor-published fn2-succ-core-drop))
   (assert-event (fn2-assert-compliant-p '(fn2-successor-stage fn2-successor-out fn2-successor-fill-octets fn2-successor-bind fn2-successor-release fn2-succ-core-publish fn2-successor-published fn2-succ-core-drop) (w state)))))
