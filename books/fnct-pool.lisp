; The FNCT frame over a pool range (e-surface.md 4.2): the served side of
; consumer-codec.lisp's list specification. Every octet run is a generated
; codec (DEFLAYOUT's -DECODE and -ENCODE over a fields stripe); the BLAKE3-256
; trailer is B's hasher over the range and is compared, never a field.
;
; Pool writes append (an index at most the range's fill), so a frame is
; built forward: the octet fields a layout copies (a reason word, a cursor's
; IDs, a verb's result) are first written as SCRATCH at the range's start,
; then the frame at K = the fill after them: ten reserved header octets, the
; payload's layout (its octet fields referring back into the scratch), then
; the header encoded over the reserved octets and the trailer appended. The
; reply is sent from K. A frame and its scratch together fit the range; a
; reply that would not is refused :size by the encoders (never truncated).
(in-package "ACL2")
(include-book "consumer-codec")
(include-book "format-check")
(fn2-book-layer :e)
(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))
(local (in-theory (disable fn2-fields-rows fn2-fieldsp fn2-fields-wfp fn2-poolp fn2-pool-wfp fn2-pool-rows
                           fn2-pool-read fn2-pool-write)))

(defconst *fn2-fnct-header-octets* 10)
(defconst *fn2-fnct-trailer-octets* 32)
(defconst *fn2-fnct-overhead* 42)
; One hasher call covers a frame's protected prefix: the control range is at
; most *fn2-ctl-io-bytes* (4096) octets, so the prefix is at most 4064.
(defconst *fn2-fnct-max-prefix* 4096)
; fn1's native-control kinds (native-control.lisp): 1 a request, 2 its reply.
; fn2's control request is one command octet (1 status, 2 pause, 3 resume,
; 4 drain, 5 stop); its reply the posture octet after it (0 running, 1
; paused, 2 draining, 3 stopped).
(defconst *fn2-fnct-control-kind* 1)
(defconst *fn2-fnct-control-reply-kind* 2)
(deflayout fn2-fnct-k1 '((command :u8)))
(deflayout fn2-fnct-k2 '((posture :u8)))
(deflayout fn2-fnct-k4-head '((code :u8)))

; A range's fill and capacity (0 for no slot).
(defun fn2-fnct-fill (slot fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (if (and (natp slot) (< slot (fn2-pool-rows fn2-pool))) (nfix (fn2-pool-slot-fill slot fn2-pool)) 0))
(defun fn2-fnct-cap (slot fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (if (and (natp slot) (< slot (fn2-pool-rows fn2-pool))) (nfix (fn2-pool-slot-cap slot fn2-pool)) 0))
(defthm fn2-fnct-fill-natp (natp (fn2-fnct-fill slot fn2-pool)) :rule-classes :type-prescription)
(defthm fn2-fnct-cap-natp (natp (fn2-fnct-cap slot fn2-pool)) :rule-classes :type-prescription)
(in-theory (disable fn2-fnct-fill fn2-fnct-cap))

;; ---------------------------------------------------------------------------
;; Appending octets at the nfill: zeros, a big-endian number, a constant word.
(defun fn2-fnct-put-be (k n w slot gen okind oslot ogen fn2-pool)
  ; The low W octets of N, most significant first, from octet K of them.
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp k) (natp n) (natp w))
                  :measure (nfix (- (nfix w) (nfix k)))))
  (if (>= (nfix k) (nfix w)) (mv :ok fn2-pool)
    (mv-let (code fn2-pool)
      (fn2-pool-write slot gen (fn2-fnct-fill slot fn2-pool)
                      (mod (ash (nfix n) (- (* 8 (- (nfix w) (+ 1 (nfix k)))))) 256)
                      okind oslot ogen fn2-pool)
      (if (eq code :ok) (fn2-fnct-put-be (+ 1 (nfix k)) n w slot gen okind oslot ogen fn2-pool)
        (mv code fn2-pool)))))
(fn2-pool-preserves fn2-fnct-put-be (k n w slot gen okind oslot ogen fn2-pool) :position 1)
(in-theory (disable fn2-fnct-put-be))
(defun fn2-fnct-be-width (n)
  ; The octets of N's minimal big-endian form, at least one.
  (declare (xargs :guard t :measure (nfix n)))
  (if (< (nfix n) 256) 1 (+ 1 (fn2-fnct-be-width (ash (nfix n) -8)))))
(defthm fn2-fnct-be-width-posp (posp (fn2-fnct-be-width n)) :rule-classes :type-prescription)
(in-theory (disable fn2-fnct-be-width))
(defun fn2-fnct-put-word (i str slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp i) (stringp str))
                  :measure (nfix (- (length str) (nfix i)))))
  (if (or (not (stringp str)) (>= (nfix i) (length str))) (mv :ok fn2-pool)
    (mv-let (code fn2-pool)
      (fn2-pool-write slot gen (fn2-fnct-fill slot fn2-pool) (char-code (char str (nfix i)))
                      okind oslot ogen fn2-pool)
      (if (eq code :ok) (fn2-fnct-put-word (+ 1 (nfix i)) str slot gen okind oslot ogen fn2-pool)
        (mv code fn2-pool)))))
(fn2-pool-preserves fn2-fnct-put-word (i str slot gen okind oslot ogen fn2-pool) :position 1)
(in-theory (disable fn2-fnct-put-word))

;; ---------------------------------------------------------------------------
;; The trailer: BLAKE3 of [OFF, OFF+LEN) in hasher ROW, into its result slot.
(defun fn2-fnct-hash-loop (fuel row slot gen off len done okind oslot ogen fn2-digests fn2-b3 fn2-pool)
  (declare (xargs :stobjs (fn2-digests fn2-b3 fn2-pool) :measure (nfix fuel)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp fuel) (natp off) (natp len) (natp done))))
  (cond ((>= (nfix done) (nfix len)) (mv :ok fn2-digests fn2-b3))
        ((or (zp fuel) (not (fn2-b3-ready row fn2-b3 fn2-digests))
             (not (unsigned-byte-p 32 (+ (nfix off) (nfix done)))) (not (unsigned-byte-p 32 (nfix len))))
         (mv :bounds fn2-digests fn2-b3))
        (t (mv-let (code consumed fn2-digests fn2-b3)
             (fn2-b3-update row slot gen (+ (nfix off) (nfix done)) (- (nfix len) (nfix done))
                            okind oslot ogen fn2-digests fn2-b3 fn2-pool)
             (if (and (member-eq code '(:ok :more)) (posp consumed))
                 (fn2-fnct-hash-loop (- fuel 1) row slot gen off len (+ (nfix done) consumed)
                                     okind oslot ogen fn2-digests fn2-b3 fn2-pool)
               (mv :bounds fn2-digests fn2-b3))))))
(defmacro fn2-fnct-shape (name call guard outputs hints)
  `(defthm ,name (implies ,guard (and ,@(fn2-fc-shape-claims outputs call))) :hints ,hints))
(fn2-fnct-shape fn2-fnct-hash-loop-shape
  (fn2-fnct-hash-loop fuel row slot gen off len done okind oslot ogen fn2-digests fn2-b3 fn2-pool)
  (and (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests) (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3)
       (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
  ((fn2-digests 1) (fn2-b3 2))
  (("Goal" :induct (fn2-fnct-hash-loop fuel row slot gen off len done okind oslot ogen fn2-digests fn2-b3 fn2-pool)
           :in-theory (e/d (fn2-fnct-hash-loop) (fn2-digestsp fn2-digests-wfp fn2-b3p fn2-b3-wfp fn2-digests-rows fn2-b3-rows)))))
(defun fn2-fnct-hash (row slot gen off len okind oslot ogen fn2-digests fn2-b3 fn2-pool)
  (declare (xargs :stobjs (fn2-digests fn2-b3 fn2-pool)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp off) (natp len))))
  (let ((key (fn2-digest-slot (nfix row) *fn2-b3-key*)) (dst (fn2-digest-slot (nfix row) *fn2-b3-result*)))
    (if (not (and (natp row) (fn2-b3-ready row fn2-b3 fn2-digests) (fn2-digest-rowp key fn2-digests)
                  (<= (nfix len) *fn2-fnct-max-prefix*)))
        (mv :bounds fn2-digests fn2-b3)
      (mv-let (fn2-digests fn2-b3) (fn2-b3-init row 0 key fn2-digests fn2-b3)
        (mv-let (code fn2-digests fn2-b3)
          (fn2-fnct-hash-loop 4 row slot gen off len 0 okind oslot ogen fn2-digests fn2-b3 fn2-pool)
          (if (not (and (eq code :ok) (fn2-b3-ready row fn2-b3 fn2-digests) (fn2-digest-rowp dst fn2-digests)))
              (mv :bounds fn2-digests fn2-b3)
            (let ((fn2-digests (fn2-b3-finalize dst row fn2-digests fn2-b3))) (mv :ok fn2-digests fn2-b3))))))))
(fn2-fnct-shape fn2-fnct-hash-shape
  (fn2-fnct-hash row slot gen off len okind oslot ogen fn2-digests fn2-b3 fn2-pool)
  (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests) (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)) ((fn2-digests 1) (fn2-b3 2))
  (("Goal" :in-theory (e/d (fn2-fnct-hash) (fn2-fieldsp fn2-fields-wfp fn2-digestsp fn2-digests-wfp fn2-b3p fn2-b3-wfp fn2-poolp fn2-pool-wfp fn2-digests-rows fn2-b3-rows fn2-fields-rows fn2-pool-rows)))))
(in-theory (disable fn2-fnct-hash-loop fn2-fnct-hash))
(defun fn2-fnct-trailer-matchp (i dst slot gen off okind oslot ogen fn2-digests fn2-pool)
  ; The 32 octets at OFF are digest row DST's, in B's stored order (fn2-digest-store).
  (declare (xargs :stobjs (fn2-digests fn2-pool) :measure (nfix (- 32 (nfix i)))
                  :guard (and (fn2-digest-rowp dst fn2-digests) (fn2-pool-wfp fn2-pool) (natp i) (natp off))))
  (if (>= (nfix i) 32) t
    (mv-let (code b) (fn2-pool-read slot gen (+ (nfix off) (nfix i)) okind oslot ogen fn2-pool)
      (and (eq code :ok)
           (equal b (fn2-fc-word-byte (nfix (fn2-digest-word dst (floor (nfix i) 4) fn2-digests)) (mod (nfix i) 4)))
           (fn2-fnct-trailer-matchp (+ 1 (nfix i)) dst slot gen off okind oslot ogen fn2-digests fn2-pool)))))

(in-theory (disable fn2-fnct-trailer-matchp))
;; ---------------------------------------------------------------------------
;; Opening a received frame at the range's start (the fields at BASE, the
;; hasher ROW). (mv code kind plen fn2-fields fn2-digests fn2-b3), code :ok,
;; :need-more (a prefix of a frame that fits), :size (it cannot fit the range
;; or one hasher call), :frame (bad magic, version, extent or trailer) or :bounds.
(defun fn2-fnct-open-pool (base row slot gen okind oslot ogen fn2-fields fn2-digests fn2-b3 fn2-pool)
  (declare (xargs :stobjs (fn2-fields fn2-digests fn2-b3 fn2-pool)
                  :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
  (b* ((nfill (fn2-fnct-fill slot fn2-pool))
       (cap (fn2-fnct-cap slot fn2-pool))
       ((unless (and (natp base) (<= (+ base *fn2-fnct-header-num-fields*) (fn2-fields-rows fn2-fields))
                     (natp nfill) (natp cap)))
        (mv :bounds 0 0 fn2-fields fn2-digests fn2-b3))
       ((when (< nfill *fn2-fnct-header-octets*))
        (mv (if (<= cap nfill) :size :need-more) 0 0 fn2-fields fn2-digests fn2-b3))
       ((mv code & fn2-fields)
        (fn2-fnct-header-decode base slot gen 0 *fn2-fnct-header-octets* okind oslot ogen fn2-fields fn2-pool))
       ((unless (eq code :ok)) (mv :frame 0 0 fn2-fields fn2-digests fn2-b3))
       (magic (fn2-fields-value (+ base *fn2-fnct-header-field-magic*) fn2-fields))
       (version (fn2-fields-value (+ base *fn2-fnct-header-field-version*) fn2-fields))
       (kind (fn2-fields-value (+ base *fn2-fnct-header-field-kind*) fn2-fields))
       (plen (fn2-fields-value (+ base *fn2-fnct-header-field-length*) fn2-fields))
       ((unless (and (equal magic *fn2-fnct-magic*) (equal version *fn2-fnct-version*)
                     (natp kind) (natp plen)))
        (mv :frame 0 0 fn2-fields fn2-digests fn2-b3))
       (prefix (+ *fn2-fnct-header-octets* plen))
       (total (+ prefix *fn2-fnct-trailer-octets*))
       ((when (or (< cap total) (< *fn2-fnct-max-prefix* prefix)))
        (mv :size 0 0 fn2-fields fn2-digests fn2-b3))
       ((when (< nfill total)) (mv :need-more 0 0 fn2-fields fn2-digests fn2-b3))
       ((when (< total nfill)) (mv :frame 0 0 fn2-fields fn2-digests fn2-b3))
       ((mv hcode fn2-digests fn2-b3) (fn2-fnct-hash row slot gen 0 prefix okind oslot ogen fn2-digests fn2-b3 fn2-pool))
       (dst (fn2-digest-slot (nfix row) *fn2-b3-result*))
       ((unless (and (eq hcode :ok) (fn2-digest-rowp dst fn2-digests))) (mv :bounds 0 0 fn2-fields fn2-digests fn2-b3))
       ((unless (fn2-fnct-trailer-matchp 0 dst slot gen prefix okind oslot ogen fn2-digests fn2-pool))
        (mv :frame 0 0 fn2-fields fn2-digests fn2-b3)))
    (mv :ok kind plen fn2-fields fn2-digests fn2-b3)))

(fn2-fnct-shape fn2-fnct-open-pool-shape
  (fn2-fnct-open-pool base row slot gen okind oslot ogen fn2-fields fn2-digests fn2-b3 fn2-pool)
  (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests) (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)) ((fn2-fields 3) (fn2-digests 4) (fn2-b3 5))
  (("Goal" :in-theory (e/d (fn2-fnct-open-pool) (fn2-fieldsp fn2-fields-wfp fn2-digestsp fn2-digests-wfp fn2-b3p fn2-b3-wfp fn2-poolp fn2-pool-wfp fn2-digests-rows fn2-b3-rows fn2-fields-rows fn2-pool-rows)))))
(in-theory (disable fn2-fnct-open-pool))
;; Sealing the frame whose ten header octets were reserved at K and whose
;; payload runs from K+10 to the nfill: the header encoded over the reserved
;; octets, then the trailer appended. (mv code total fn2-fields fn2-digests fn2-b3 fn2-pool).
(defun fn2-fnct-seal-pool (base row k kind slot gen okind oslot ogen fn2-fields fn2-digests fn2-b3 fn2-pool)
  (declare (xargs :stobjs (fn2-fields fn2-digests fn2-b3 fn2-pool)
                  :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
  (b* ((nfill (fn2-fnct-fill slot fn2-pool))
       (cap (fn2-fnct-cap slot fn2-pool))
       ((unless (and (natp base) (<= (+ base *fn2-fnct-header-num-fields*) (fn2-fields-rows fn2-fields))
                     (natp k) (natp nfill) (natp cap) (unsigned-byte-p 8 kind)
                     (<= (+ k *fn2-fnct-header-octets*) nfill)))
        (mv :bounds 0 fn2-fields fn2-digests fn2-b3 fn2-pool))
       (prefix (- nfill k))
       (plen (- prefix *fn2-fnct-header-octets*))
       ((when (or (< cap (+ nfill *fn2-fnct-trailer-octets*)) (< *fn2-fnct-max-prefix* prefix)))
        (mv :size 0 fn2-fields fn2-digests fn2-b3 fn2-pool))
       (fn2-fields (fn2-fields-set-value (+ base *fn2-fnct-header-field-magic*) *fn2-fnct-magic* fn2-fields))
       (fn2-fields (fn2-fields-set-value (+ base *fn2-fnct-header-field-version*) *fn2-fnct-version* fn2-fields))
       (fn2-fields (fn2-fields-set-value (+ base *fn2-fnct-header-field-kind*) kind fn2-fields))
       (fn2-fields (fn2-fields-set-value (+ base *fn2-fnct-header-field-length*) plen fn2-fields))
       ((mv code & fn2-pool) (fn2-fnct-header-encode base slot gen k okind oslot ogen fn2-fields fn2-pool))
       ((unless (eq code :ok)) (mv code 0 fn2-fields fn2-digests fn2-b3 fn2-pool))
       ((mv hcode fn2-digests fn2-b3) (fn2-fnct-hash row slot gen k prefix okind oslot ogen fn2-digests fn2-b3 fn2-pool))
       (dst (fn2-digest-slot (nfix row) *fn2-b3-result*))
       ((unless (and (eq hcode :ok) (fn2-digest-rowp dst fn2-digests))) (mv :bounds 0 fn2-fields fn2-digests fn2-b3 fn2-pool))
       ((mv scode fn2-pool) (fn2-digest-store 32 dst slot gen nfill okind oslot ogen fn2-digests fn2-pool))
       ((unless (eq scode :ok)) (mv scode 0 fn2-fields fn2-digests fn2-b3 fn2-pool)))
    (mv :ok (+ prefix *fn2-fnct-trailer-octets*) fn2-fields fn2-digests fn2-b3 fn2-pool)))
(fn2-fnct-shape fn2-fnct-seal-pool-shape
  (fn2-fnct-seal-pool base row k kind slot gen okind oslot ogen fn2-fields fn2-digests fn2-b3 fn2-pool)
  (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests) (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)) ((fn2-fields 2) (fn2-digests 3) (fn2-b3 4) (fn2-pool 5))
  (("Goal" :in-theory (e/d (fn2-fnct-seal-pool) (fn2-fieldsp fn2-fields-wfp fn2-digestsp fn2-digests-wfp fn2-b3p fn2-b3-wfp fn2-poolp fn2-pool-wfp fn2-digests-rows fn2-b3-rows fn2-fields-rows fn2-pool-rows)))))
(in-theory (disable fn2-fnct-seal-pool))

;; ---------------------------------------------------------------------------
;; Replies. An octet field's fields row names its source range (B's layout
;; rows: value 1, the reference slot, generation, offset and length).
(defun fn2-fnct-set-ref (i slot gen off len fn2-fields)
  (declare (xargs :stobjs fn2-fields
                  :guard (and (fn2-fields-wfp fn2-fields) (natp i) (< i (fn2-fields-rows fn2-fields))
                              (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
                              (unsigned-byte-p 32 off) (unsigned-byte-p 32 len))))
  (let* ((fn2-fields (fn2-fields-set-value i 1 fn2-fields))
         (fn2-fields (fn2-fields-set-ref-slot i slot fn2-fields))
         (fn2-fields (fn2-fields-set-ref-gen i gen fn2-fields))
         (fn2-fields (fn2-fields-set-ref-off i off fn2-fields)))
    (fn2-fields-set-ref-len i len fn2-fields)))
(defthm fn2-fnct-set-ref-shape
  (implies (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (natp i) (< i (fn2-fields-rows fn2-fields))
                (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen) (unsigned-byte-p 32 off) (unsigned-byte-p 32 len))
           (and (fn2-fieldsp (fn2-fnct-set-ref i slot gen off len fn2-fields))
                (fn2-fields-wfp (fn2-fnct-set-ref i slot gen off len fn2-fields))
                (equal (fn2-fields-rows (fn2-fnct-set-ref i slot gen off len fn2-fields)) (fn2-fields-rows fn2-fields)))))
(in-theory (disable fn2-fnct-set-ref))
(defun fn2-fnct-handlep (slot gen off len)
  (declare (xargs :guard t))
  (and (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen) (unsigned-byte-p 32 off) (unsigned-byte-p 32 len)))

; The kind 28 reply at the fill: class (0 accepted, 1 refused, 2 uncertain,
; 3 fault), the reason word at [ROFF, ROFF+RLEN) and the verb's result at
; [QOFF, QOFF+QLEN) of the same range (scratch below the frame).
; (mv code k total fn2-fields fn2-digests fn2-b3 fn2-pool): the frame is [K, K+TOTAL).
(defun fn2-fnct-put-k28 (base row class roff rlen qoff qlen slot gen okind oslot ogen
                              fn2-fields fn2-digests fn2-b3 fn2-pool)
  (declare (xargs :stobjs (fn2-fields fn2-digests fn2-b3 fn2-pool)
                  :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
  (b* ((k (fn2-fnct-fill slot fn2-pool))
       ((unless (and (natp base) (<= (+ base *fn2-fnct-k28-reply-num-fields*) (fn2-fields-rows fn2-fields))
                     (<= (+ base *fn2-fnct-header-num-fields*) (fn2-fields-rows fn2-fields))
                     (natp class) (< class 4) (<= (nfix rlen) 64)
                     (fn2-fnct-handlep slot gen roff rlen) (fn2-fnct-handlep slot gen qoff qlen)))
        (mv :bounds 0 0 fn2-fields fn2-digests fn2-b3 fn2-pool))
       ((mv code fn2-pool) (fn2-fnct-put-be 0 0 *fn2-fnct-header-octets* slot gen okind oslot ogen fn2-pool))
       ((unless (eq code :ok)) (mv :size 0 0 fn2-fields fn2-digests fn2-b3 fn2-pool))
       (fn2-fields (fn2-fields-set-value (+ base *fn2-fnct-k28-reply-field-class*) class fn2-fields))
       (fn2-fields (fn2-fnct-set-ref (+ base *fn2-fnct-k28-reply-field-reason*) slot gen roff rlen fn2-fields))
       (fn2-fields (fn2-fnct-set-ref (+ base *fn2-fnct-k28-reply-field-result*) slot gen qoff qlen fn2-fields))
       ((mv code & fn2-pool)
        (fn2-fnct-k28-reply-encode base slot gen (+ k *fn2-fnct-header-octets*) okind oslot ogen fn2-fields fn2-pool))
       ((unless (eq code :ok)) (mv :size 0 0 fn2-fields fn2-digests fn2-b3 fn2-pool))
       ((mv code total fn2-fields fn2-digests fn2-b3 fn2-pool)
        (fn2-fnct-seal-pool base row k *fn2-fnct-port-reply-kind* slot gen okind oslot ogen
                            fn2-fields fn2-digests fn2-b3 fn2-pool)))
    (mv code k total fn2-fields fn2-digests fn2-b3 fn2-pool)))
(fn2-fnct-shape fn2-fnct-put-k28-shape
  (fn2-fnct-put-k28 base row class roff rlen qoff qlen slot gen okind oslot ogen fn2-fields fn2-digests fn2-b3 fn2-pool)
  (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests) (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
  ((fn2-fields 3) (fn2-digests 4) (fn2-b3 5) (fn2-pool 6))
  (("Goal" :in-theory (e/d (fn2-fnct-put-k28) (fn2-fieldsp fn2-fields-wfp fn2-digestsp fn2-digests-wfp fn2-b3p fn2-b3-wfp fn2-poolp fn2-pool-wfp fn2-digests-rows fn2-b3-rows fn2-fields-rows fn2-pool-rows)))))
(in-theory (disable fn2-fnct-put-k28))

; A verb's result (consumer-codec.lisp *fn2-fnct-results*), encoded at the
; fill as scratch for a kind 28 reply: (mv code off len fn2-fields fn2-pool).
; SETS: (FIELD VALUE) for a scalar, (FIELD :ref OFF LEN) for octets from this range.
(defun fn2-fnct-def-result-guards (sets)
  (declare (xargs :guard t))
  (cond ((atom sets) nil)
        ((and (consp (car sets)) (consp (cdar sets)) (eq (cadar sets) :ref) (consp (cddar sets)) (consp (cdddar sets)))
         (cons `(fn2-fnct-handlep slot gen ,(caddar sets) ,(car (cdddar sets))) (fn2-fnct-def-result-guards (cdr sets))))
        ((and (consp (car sets)) (consp (cdar sets)))
         (cons `(unsigned-byte-p 60 ,(cadar sets)) (fn2-fnct-def-result-guards (cdr sets))))
        (t (fn2-fnct-def-result-guards (cdr sets)))))
(defun fn2-fnct-def-result-binds (layout-name sets)
  (declare (xargs :guard (symbolp layout-name)))
  (if (or (atom sets) (not (consp (car sets))) (not (symbolp (caar sets))) (not (consp (cdar sets)))) nil
    (let ((idx (intern-in-package-of-symbol
                (concatenate 'string "*" (symbol-name layout-name) "-FIELD-" (symbol-name (caar sets)) "*") 'fn2-fnct-def-result)))
      (cons (if (and (eq (cadar sets) :ref) (consp (cddar sets)) (consp (cdddar sets)))
                `(fn2-fields (fn2-fnct-set-ref (+ base ,idx) slot gen ,(caddar sets) ,(car (cdddar sets)) fn2-fields))
              `(fn2-fields (fn2-fields-set-value (+ base ,idx) ,(cadar sets) fn2-fields)))
            (fn2-fnct-def-result-binds layout-name (cdr sets))))))
(defmacro fn2-fnct-def-result (name layout-name args sets)
  (let ((encode (intern-in-package-of-symbol (concatenate 'string (symbol-name layout-name) "-ENCODE") 'fn2-fnct-def-result))
        (nf (intern-in-package-of-symbol (concatenate 'string "*" (symbol-name layout-name) "-NUM-FIELDS*") 'fn2-fnct-def-result)))
    `(progn
       (defun ,name (base ,@args slot gen okind oslot ogen fn2-fields fn2-pool)
         (declare (xargs :stobjs (fn2-fields fn2-pool) :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
         (b* ((off (fn2-fnct-fill slot fn2-pool))
              ((unless (and (natp base) (<= (+ base ,nf) (fn2-fields-rows fn2-fields))
                            ,@(fn2-fnct-def-result-guards sets)))
               (mv :bounds 0 0 fn2-fields fn2-pool))
              ,@(fn2-fnct-def-result-binds layout-name sets)
              ((mv code next fn2-pool) (,encode base slot gen off okind oslot ogen fn2-fields fn2-pool))
              ((unless (and (eq code :ok) (natp next) (<= off next))) (mv :size 0 0 fn2-fields fn2-pool)))
           (mv :ok off (- next off) fn2-fields fn2-pool)))
       (fn2-fnct-shape ,(intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-SHAPE") name)
         (,name base ,@args slot gen okind oslot ogen fn2-fields fn2-pool)
         (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
         ((fn2-fields 3) (fn2-pool 4))
         (("Goal" :in-theory (e/d (,name) (fn2-fieldsp fn2-fields-wfp fn2-poolp fn2-pool-wfp fn2-fields-rows fn2-pool-rows)))))
       (defthm ,(intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-NATP") name)
         (and (natp (mv-nth 1 (,name base ,@args slot gen okind oslot ogen fn2-fields fn2-pool)))
              (natp (mv-nth 2 (,name base ,@args slot gen okind oslot ogen fn2-fields fn2-pool))))
         :rule-classes ((:type-prescription :corollary (natp (mv-nth 1 (,name base ,@args slot gen okind oslot ogen fn2-fields fn2-pool))))
                        (:type-prescription :corollary (natp (mv-nth 2 (,name base ,@args slot gen okind oslot ogen fn2-fields fn2-pool)))))
         :hints (("Goal" :in-theory (enable ,name))))
       (in-theory (disable ,name)))))
(fn2-fnct-def-result fn2-fnct-put-ack fn2-fnct-result-ack (domain position)
  ((domain domain) (position position)))
(fn2-fnct-def-result fn2-fnct-put-status fn2-fnct-result-status (domain position frontier gap)
  ((domain domain) (position position) (frontier frontier) (gap gap)))
(fn2-fnct-def-result fn2-fnct-put-page fn2-fnct-result-page (more noff nlen count ioff ilen)
  ((more more) (next :ref noff nlen) (count count) (items :ref ioff ilen)))
; A cursor (fncu v1) whose five IDs lie contiguous from START: HL, IL, CL, PL, QL octets.
(fn2-fnct-def-result fn2-fnct-put-cursor fn2-fncu-v1 (start hl il cl pl ql qver vver epoch position)
  ((magic *fn2-fncu-magic*) (version 1)
   (history :ref start hl) (incarnation :ref (+ start hl) il) (consumer :ref (+ start hl il) cl)
   (principal :ref (+ start hl il cl) pl) (query :ref (+ start hl il cl pl) ql)
   (query-version qver) (view-version vver) (epoch epoch) (position position)))
