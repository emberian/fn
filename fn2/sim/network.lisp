(in-package "ACL2")
(include-book "../books/profile")
(include-book "../books/columns")
(include-book "../books/vocab")

; A connection owns two bounded pipes. A full pipe returns :would-block;
; its consumer must drain it before more bytes can arrive. It never silently
; drops or truncates bytes. The server->client pipe is the unread wire record.
; Delays, fragmentation, and short operation lengths are chosen by sim.lisp;
; these one-byte physical transitions admit every byte boundary as a cut.
; A capability's peer is the simulated host's configuration of who connects
; there: family (vocab's fn2-peer-family, :none by default or :local) and,
; for :local, the credentials the kernel would report at accept (uid, gid).
; An Accept that lands on the capability carries that record.
(defcolumns fn2-sim-network
  ((nonce :u32) (base :u60) (cap :u32)
   (phase (:enum fn2-network-phase (:closed :open :reset :admission-refused)))
   (rx-head :u32) (rx-count :u32) (tx-head :u32) (tx-count :u32)
   (half-open :bool) (nonreading :bool)
   (reset-armed :bool) (reset-left :u60)
   (peer-family :u8) (peer-uid :u32) (peer-gid :u32))
  :init-name fn2-network-columns-init
  :extra-fields
  ((fn2-network-rx :type (array (unsigned-byte 8) (0)) :initially 0 :resizable t :why "Connection receive pipes have byte capacity independent of row count.")
   (fn2-network-tx :type (array (unsigned-byte 8) (0)) :initially 0 :resizable t :why "Connection transmit pipes have byte capacity independent of row count.")))

; Generated composition facts keep the concrete recognizer closed in users.

(defun fn2-network-init-rows (slot window fn2-sim-network)
  (declare (xargs :stobjs fn2-sim-network
                  :measure (nfix (- (fn2-sim-network-rows fn2-sim-network) (nfix slot)))
                  :guard (and (fn2-sim-network-wfp fn2-sim-network)
                              (natp slot) (unsigned-byte-p 32 window))))
  (if (or (not (natp slot))
          (not (natp (fn2-sim-network-rows fn2-sim-network)))
          (>= slot (fn2-sim-network-rows fn2-sim-network)))
      fn2-sim-network
    (let* ((base (* slot window))
           (fn2-sim-network
            (fn2-sim-network-put slot (nonce 0) (base (if (unsigned-byte-p 60 base) base 0))
                             (cap window) (phase *fn2-network-phase-closed*)
                             (rx-head 0) (rx-count 0) (tx-head 0) (tx-count 0)
                             (half-open 0) (nonreading 0) (reset-armed 0) (reset-left 0)
                             (peer-family *fn2-peer-family-none*) (peer-uid 0) (peer-gid 0))))
      (fn2-network-init-rows (+ 1 slot) window fn2-sim-network))))
(defthm fn2-network-init-rows-type
  (implies (and (fn2-sim-networkp fn2-sim-network)
                (fn2-sim-network-wfp fn2-sim-network)
                (unsigned-byte-p 32 window))
           (fn2-sim-networkp (fn2-network-init-rows slot window fn2-sim-network))))
(defthm fn2-network-init-rows-wfp
  (implies (fn2-sim-network-wfp fn2-sim-network)
           (fn2-sim-network-wfp (fn2-network-init-rows slot window fn2-sim-network))))
(in-theory (disable fn2-network-init-rows))

(defun fn2-network-init (n window fn2-sim-network)
  (declare (xargs :stobjs fn2-sim-network
                  :guard (and (unsigned-byte-p 32 n) (posp window)
                              (unsigned-byte-p 32 window)
                              (unsigned-byte-p 60 (* n window)))))
  (let* ((fn2-sim-network (fn2-network-columns-init n fn2-sim-network))
         (fn2-sim-network (resize-fn2-network-rx (* n window) fn2-sim-network))
         (fn2-sim-network (resize-fn2-network-tx (* n window) fn2-sim-network)))
    (fn2-network-init-rows 0 window fn2-sim-network)))
(defthm fn2-network-init-type
  (implies (and (fn2-sim-networkp fn2-sim-network)
                (unsigned-byte-p 32 n) (unsigned-byte-p 32 window))
           (fn2-sim-networkp (fn2-network-init n window fn2-sim-network))))
(defthm fn2-network-init-wfp
  (implies (unsigned-byte-p 32 n)
           (fn2-sim-network-wfp (fn2-network-init n window fn2-sim-network))))
(in-theory (disable fn2-network-init))

(defun fn2-network-cap-code (slot nonce fn2-sim-network)
  (declare (xargs :stobjs fn2-sim-network :guard (fn2-sim-network-wfp fn2-sim-network)))
  (cond ((not (and (natp slot) (< slot (fn2-sim-network-rows fn2-sim-network)))) :bounds)
        ((not (equal nonce (fn2-sim-network-nonce slot fn2-sim-network))) :stale)
        ((equal (fn2-sim-network-phase slot fn2-sim-network) *fn2-network-phase-reset*) :reset)
        ((equal (fn2-sim-network-phase slot fn2-sim-network) *fn2-network-phase-admission-refused*) :admission-refused)
        ((not (equal (fn2-sim-network-phase slot fn2-sim-network) *fn2-network-phase-open*)) :closed)
        (t :ok)))

(defun fn2-network-accept (slot fn2-sim-network)
  (declare (xargs :stobjs fn2-sim-network :guard (fn2-sim-network-wfp fn2-sim-network)))
  (cond ((not (and (natp slot) (< slot (fn2-sim-network-rows fn2-sim-network))))
         (mv :bounds 0 fn2-sim-network))
        ((equal (fn2-sim-network-phase slot fn2-sim-network) *fn2-network-phase-open*)
         (mv :busy 0 fn2-sim-network))
        ((equal (fn2-sim-network-nonce slot fn2-sim-network) #xffffffff)
         (mv :exhausted 0 fn2-sim-network))
        (t (let* ((nonce (+ 1 (fn2-sim-network-nonce slot fn2-sim-network)))
                  (fn2-sim-network
                   (fn2-sim-network-put slot (nonce nonce) (phase *fn2-network-phase-open*)
                                    (rx-head 0) (rx-count 0) (tx-head 0) (tx-count 0)
                                    (half-open 0) (nonreading 0) (reset-armed 0) (reset-left 0))))
             (mv :ok nonce fn2-sim-network)))))
(fn2-sim-network-preserves fn2-network-accept (slot fn2-sim-network) :position 2 :prefix "" :rows nil :wfp-type nil)

; Configure capability SLOT's peer: :none, or :local with its uid and gid
; (a record fn2-peer-recordp accepts). Anything else is refused by name and
; changes nothing.
(defun fn2-network-set-peer (slot family uid gid fn2-sim-network)
  (declare (xargs :stobjs fn2-sim-network :guard (fn2-sim-network-wfp fn2-sim-network)))
  (cond ((not (and (natp slot) (< slot (fn2-sim-network-rows fn2-sim-network))))
         (mv :bounds fn2-sim-network))
        ((not (and (or (equal family *fn2-peer-family-none*) (equal family *fn2-peer-family-local*))
                   (fn2-peer-recordp *fn2-outcome-done* family 0 uid gid 0 0)))
         (mv :peer fn2-sim-network))
        (t (let ((fn2-sim-network (fn2-sim-network-put slot (peer-family family) (peer-uid uid) (peer-gid gid))))
             (mv :ok fn2-sim-network)))))
(fn2-sim-network-preserves fn2-network-set-peer (slot family uid gid fn2-sim-network) :position 1 :prefix "" :rows nil :wfp-type nil)

; The peer record an Accept that landed on capability SLOT carries: (mv
; family port w0 w1 w2 w3), :none for a slot outside the table.
(defun fn2-network-peer (slot fn2-sim-network)
  (declare (xargs :stobjs fn2-sim-network :guard (fn2-sim-network-wfp fn2-sim-network)))
  (if (and (natp slot) (< slot (fn2-sim-network-rows fn2-sim-network))
           (equal (fn2-sim-network-peer-family slot fn2-sim-network) *fn2-peer-family-local*)
           (fn2-peer-recordp *fn2-outcome-done* *fn2-peer-family-local* 0
                             (fn2-sim-network-peer-uid slot fn2-sim-network)
                             (fn2-sim-network-peer-gid slot fn2-sim-network) 0 0))
      (mv *fn2-peer-family-local* 0 (fn2-sim-network-peer-uid slot fn2-sim-network)
          (fn2-sim-network-peer-gid slot fn2-sim-network) 0 0)
    (mv *fn2-peer-family-none* 0 0 0 0 0)))
(defthm fn2-network-peer-recordp
  (mv-let (family port w0 w1 w2 w3) (fn2-network-peer slot fn2-sim-network)
    (fn2-peer-recordp *fn2-outcome-done* family port w0 w1 w2 w3)))
(in-theory (disable fn2-network-peer))

(defun fn2-network-close (slot nonce fn2-sim-network)
  (declare (xargs :stobjs fn2-sim-network :guard (fn2-sim-network-wfp fn2-sim-network)))
  (if (or (not (and (natp slot) (< slot (fn2-sim-network-rows fn2-sim-network))))
          (not (equal nonce (fn2-sim-network-nonce slot fn2-sim-network))))
      (mv :stale fn2-sim-network)
    (let ((fn2-sim-network (fn2-sim-network-set-phase slot *fn2-network-phase-closed* fn2-sim-network)))
      (mv :ok fn2-sim-network))))
(fn2-sim-network-preserves fn2-network-close (slot nonce fn2-sim-network) :position 1 :prefix "" :rows nil :wfp-type nil)

; A listener Close is an executed admission refusal, attached to this nonce.
; Ordinary closes remain unexplained to the oracle unless another cause exists.
(defun fn2-network-refuse (slot nonce fn2-sim-network)
  (declare (xargs :stobjs fn2-sim-network :guard (fn2-sim-network-wfp fn2-sim-network)))
  (if (or (not (and (natp slot) (< slot (fn2-sim-network-rows fn2-sim-network))))
          (not (equal nonce (fn2-sim-network-nonce slot fn2-sim-network))))
      (mv :stale fn2-sim-network)
    (let ((fn2-sim-network
           (fn2-sim-network-set-phase slot *fn2-network-phase-admission-refused* fn2-sim-network)))
      (mv :ok fn2-sim-network))))
(fn2-sim-network-preserves fn2-network-refuse (slot nonce fn2-sim-network) :position 1 :prefix "" :rows nil :wfp-type nil)

; Set half-open (= peer stops providing input without sending a FIN),
; non-reading client, and reset after exactly LEFT physical byte transfers.
; Disabled reset ignores LEFT. Already-queued input remains receivable; once
; drained, a half-open pipe stalls with :would-block, never synthetic EOF.
; Nonreading is independent: it controls consumption of server output.
(defun fn2-network-faults (slot nonce half-open nonreading armed left fn2-sim-network)
  (declare (xargs :stobjs fn2-sim-network :guard (fn2-sim-network-wfp fn2-sim-network)))
  (let ((code (fn2-network-cap-code slot nonce fn2-sim-network)))
    (cond ((not (eq code :ok)) (mv code fn2-sim-network))
          ((not (and (unsigned-byte-p 1 half-open) (unsigned-byte-p 1 nonreading)
                     (unsigned-byte-p 1 armed) (unsigned-byte-p 60 left)))
           (mv :bounds fn2-sim-network))
          (t (let ((fn2-sim-network
                    (fn2-sim-network-put slot (half-open half-open) (nonreading nonreading)
                                     (reset-armed armed) (reset-left left))))
               (mv :ok fn2-sim-network))))))
(fn2-sim-network-preserves fn2-network-faults (slot nonce half-open nonreading armed left fn2-sim-network) :position 1 :prefix "" :rows nil :wfp-type nil)

(defun fn2-network-transfer-tick (slot fn2-sim-network)
  (declare (xargs :stobjs fn2-sim-network :guard (fn2-sim-network-wfp fn2-sim-network)))
  (if (not (and (natp slot) (< slot (fn2-sim-network-rows fn2-sim-network))))
      fn2-sim-network
    (if (and (= (fn2-sim-network-reset-armed slot fn2-sim-network) 1)
             (< 0 (fn2-sim-network-reset-left slot fn2-sim-network)))
        (fn2-sim-network-set-reset-left slot
          (- (fn2-sim-network-reset-left slot fn2-sim-network) 1) fn2-sim-network)
      fn2-sim-network)))
(fn2-sim-network-preserves fn2-network-transfer-tick (slot fn2-sim-network) :position nil :prefix "" :rows nil :wfp-type nil)

; These two pipe primitives have explicit bounds even for a malformed logical
; state. All positions are sums of u60 base and u32 offsets (fixnums). No
; multiplication, division, consing, or resizing occurs on the byte path.
(defun fn2-network-queue-put (rx slot byte fn2-sim-network)
  (declare (xargs :stobjs fn2-sim-network :guard (fn2-sim-network-wfp fn2-sim-network)))
  (if (not (and (natp slot) (< slot (fn2-sim-network-rows fn2-sim-network))
                (unsigned-byte-p 8 byte)))
      (mv :bounds fn2-sim-network)
    (let* ((cap (fn2-sim-network-cap slot fn2-sim-network))
           (head (if rx (fn2-sim-network-rx-head slot fn2-sim-network)
                   (fn2-sim-network-tx-head slot fn2-sim-network)))
           (count (if rx (fn2-sim-network-rx-count slot fn2-sim-network)
                    (fn2-sim-network-tx-count slot fn2-sim-network)))
           (tail (+ head count))
           (off (if (< tail cap) tail (- tail cap)))
           (pos (+ (fn2-sim-network-base slot fn2-sim-network) off)))
      (cond ((or (= cap 0) (>= count cap)) (mv :would-block fn2-sim-network))
            ((or (>= head cap) (not (natp pos))
                 (>= pos (if rx (fn2-network-rx-length fn2-sim-network)
                           (fn2-network-tx-length fn2-sim-network))))
             (mv :bounds fn2-sim-network))
            (rx (let* ((fn2-sim-network (update-fn2-network-rxi pos byte fn2-sim-network))
                       (fn2-sim-network (fn2-sim-network-set-rx-count slot (+ 1 count) fn2-sim-network)))
                  (mv :ok fn2-sim-network)))
            (t (let* ((fn2-sim-network (update-fn2-network-txi pos byte fn2-sim-network))
                      (fn2-sim-network (fn2-sim-network-set-tx-count slot (+ 1 count) fn2-sim-network)))
                 (mv :ok fn2-sim-network)))))))
(fn2-sim-network-preserves fn2-network-queue-put (rx slot byte fn2-sim-network) :position 1 :prefix "" :rows nil :wfp-type nil)

(defun fn2-network-queue-get (rx slot fn2-sim-network)
  (declare (xargs :stobjs fn2-sim-network :guard (fn2-sim-network-wfp fn2-sim-network)))
  (if (not (and (natp slot) (< slot (fn2-sim-network-rows fn2-sim-network))))
      (mv :bounds 0 fn2-sim-network)
    (let* ((cap (fn2-sim-network-cap slot fn2-sim-network))
           (head (if rx (fn2-sim-network-rx-head slot fn2-sim-network)
                   (fn2-sim-network-tx-head slot fn2-sim-network)))
           (count (if rx (fn2-sim-network-rx-count slot fn2-sim-network)
                    (fn2-sim-network-tx-count slot fn2-sim-network)))
           (next (if (< (+ 1 head) cap) (+ 1 head) 0))
           (pos (+ (fn2-sim-network-base slot fn2-sim-network) head)))
      (cond ((= count 0) (mv :would-block 0 fn2-sim-network))
            ((or (>= head cap) (>= pos (if rx (fn2-network-rx-length fn2-sim-network)
                                       (fn2-network-tx-length fn2-sim-network))))
             (mv :bounds 0 fn2-sim-network))
            (rx (let* ((byte (fn2-network-rxi pos fn2-sim-network))
                       (fn2-sim-network (fn2-sim-network-put slot (rx-head next) (rx-count (- count 1)))))
                  (mv :ok byte fn2-sim-network)))
            (t (let* ((byte (fn2-network-txi pos fn2-sim-network))
                      (fn2-sim-network (fn2-sim-network-put slot (tx-head next) (tx-count (- count 1)))))
                 (mv :ok byte fn2-sim-network)))))))
(fn2-sim-network-preserves fn2-network-queue-get (rx slot fn2-sim-network) :position 2 :prefix "" :rows nil :wfp-type nil)

(defun fn2-network-client-byte (slot nonce byte fn2-sim-network)
  (declare (xargs :stobjs fn2-sim-network :guard (fn2-sim-network-wfp fn2-sim-network)))
  (let ((code (fn2-network-cap-code slot nonce fn2-sim-network)))
    (cond ((not (eq code :ok)) (mv code fn2-sim-network))
          ((= (fn2-sim-network-half-open slot fn2-sim-network) 1) (mv :would-block fn2-sim-network))
          (t (fn2-network-queue-put t slot byte fn2-sim-network)))))
(fn2-sim-network-preserves fn2-network-client-byte (slot nonce byte fn2-sim-network) :position 1 :prefix "" :rows nil :wfp-type nil)

(defun fn2-network-client-read (slot nonce fn2-sim-network)
  (declare (xargs :stobjs fn2-sim-network :guard (fn2-sim-network-wfp fn2-sim-network)))
  (let ((code (fn2-network-cap-code slot nonce fn2-sim-network)))
    (cond ((not (eq code :ok)) (mv code 0 fn2-sim-network))
          ((= (fn2-sim-network-nonreading slot fn2-sim-network) 1) (mv :would-block 0 fn2-sim-network))
          (t (fn2-network-queue-get nil slot fn2-sim-network)))))
(fn2-sim-network-preserves fn2-network-client-read (slot nonce fn2-sim-network) :position 2 :prefix "" :rows nil :wfp-type nil)

(defun fn2-network-receive-byte (slot nonce fn2-sim-network)
  (declare (xargs :stobjs fn2-sim-network :guard (fn2-sim-network-wfp fn2-sim-network)))
  (let ((code (fn2-network-cap-code slot nonce fn2-sim-network)))
    (cond ((not (eq code :ok)) (mv code 0 fn2-sim-network))
          ((and (= (fn2-sim-network-reset-armed slot fn2-sim-network) 1)
                (= (fn2-sim-network-reset-left slot fn2-sim-network) 0))
           (let ((fn2-sim-network (fn2-sim-network-set-phase slot *fn2-network-phase-reset* fn2-sim-network)))
             (mv :reset 0 fn2-sim-network)))
          ((and (= (fn2-sim-network-half-open slot fn2-sim-network) 1)
                (= (fn2-sim-network-rx-count slot fn2-sim-network) 0))
           (mv :would-block 0 fn2-sim-network))
          (t (mv-let (code byte fn2-sim-network)
               (fn2-network-queue-get t slot fn2-sim-network)
               (let ((fn2-sim-network (if (eq code :ok)
                                       (fn2-network-transfer-tick slot fn2-sim-network)
                                       fn2-sim-network)))
                 (mv code byte fn2-sim-network)))))))
(fn2-sim-network-preserves fn2-network-receive-byte (slot nonce fn2-sim-network) :position 2 :prefix "" :rows nil :wfp-type nil)

(defun fn2-network-send-byte (slot nonce byte fn2-sim-network)
  (declare (xargs :stobjs fn2-sim-network :guard (fn2-sim-network-wfp fn2-sim-network)))
  (let ((code (fn2-network-cap-code slot nonce fn2-sim-network)))
    (cond ((not (eq code :ok)) (mv code fn2-sim-network))
          ((and (= (fn2-sim-network-reset-armed slot fn2-sim-network) 1)
                (= (fn2-sim-network-reset-left slot fn2-sim-network) 0))
           (let ((fn2-sim-network (fn2-sim-network-set-phase slot *fn2-network-phase-reset* fn2-sim-network)))
             (mv :reset fn2-sim-network)))
          (t (mv-let (code fn2-sim-network)
               (fn2-network-queue-put nil slot byte fn2-sim-network)
               (let ((fn2-sim-network (if (eq code :ok)
                                       (fn2-network-transfer-tick slot fn2-sim-network)
                                       fn2-sim-network)))
                 (mv code fn2-sim-network)))))))
(fn2-sim-network-preserves fn2-network-send-byte (slot nonce byte fn2-sim-network) :position 1 :prefix "" :rows nil :wfp-type nil)

; Independent boundary exercise: the third write is refused at a two-byte
; window; drain one, wrap, and obtain all accepted bytes in original order.
(local
 (defun fn2-network-pipe-test (rx)
   (declare (xargs :guard t))
   (with-local-stobj fn2-sim-network
     (mv-let (answer fn2-sim-network)
       (let ((fn2-sim-network (fn2-network-init 1 2 fn2-sim-network)))
         (mv-let (a fn2-sim-network) (fn2-network-queue-put rx 0 11 fn2-sim-network)
           (mv-let (b fn2-sim-network) (fn2-network-queue-put rx 0 22 fn2-sim-network)
             (mv-let (full fn2-sim-network) (fn2-network-queue-put rx 0 33 fn2-sim-network)
               (mv-let (c x fn2-sim-network) (fn2-network-queue-get rx 0 fn2-sim-network)
                 (mv-let (d fn2-sim-network) (fn2-network-queue-put rx 0 33 fn2-sim-network)
                   (mv-let (e y fn2-sim-network) (fn2-network-queue-get rx 0 fn2-sim-network)
                     (mv-let (f z fn2-sim-network) (fn2-network-queue-get rx 0 fn2-sim-network)
                       (mv-let (empty ignored fn2-sim-network) (fn2-network-queue-get rx 0 fn2-sim-network)
                         (declare (ignore ignored))
                         (mv (and (eq a :ok) (eq b :ok) (eq full :would-block)
                                  (eq c :ok) (equal x 11) (eq d :ok)
                                  (eq e :ok) (equal y 22) (eq f :ok) (equal z 33)
                                  (eq empty :would-block))
                             fn2-sim-network))))))))))
       answer))))
(local (assert-event (fn2-network-pipe-test t)))
(local (assert-event (fn2-network-pipe-test nil)))

; Expose separate type/linear facts because guard preprocessing opens
; unsigned-byte-p before a rewrite with that literal can match.
(defmacro fn2-network-byte-facts (name args u8-lemma)
  (let ((value `(mv-nth 1 (,name ,@args))))
    `(progn
       (defthm ,(intern-in-package-of-symbol
                  (concatenate 'string (symbol-name name) "-VALUE-NATP") name)
         (implies (and (fn2-sim-networkp fn2-sim-network)
                       (fn2-sim-network-wfp fn2-sim-network)) (natp ,value))
         :rule-classes :type-prescription
         :hints (("Goal" :use ,u8-lemma :in-theory (disable ,u8-lemma))))
       (defthm ,(intern-in-package-of-symbol
                  (concatenate 'string (symbol-name name) "-VALUE-BOUND") name)
         (implies (and (fn2-sim-networkp fn2-sim-network)
                       (fn2-sim-network-wfp fn2-sim-network)) (< ,value 256))
         :rule-classes :linear
         :hints (("Goal" :use ,u8-lemma :in-theory (disable ,u8-lemma)))))))

(defthm fn2-network-queue-get-byte-u8
  (implies (and (fn2-sim-networkp fn2-sim-network)
                (fn2-sim-network-wfp fn2-sim-network))
           (unsigned-byte-p 8 (mv-nth 1 (fn2-network-queue-get rx slot fn2-sim-network))))
  :hints (("Goal" :in-theory (enable fn2-network-queue-get))))
(fn2-network-byte-facts fn2-network-queue-get (rx slot fn2-sim-network)
  fn2-network-queue-get-byte-u8)
(defthm fn2-network-receive-byte-u8
  (implies (and (fn2-sim-networkp fn2-sim-network)
                (fn2-sim-network-wfp fn2-sim-network))
           (unsigned-byte-p 8 (mv-nth 1 (fn2-network-receive-byte slot nonce fn2-sim-network))))
  :hints (("Goal" :in-theory (enable fn2-network-receive-byte))))
(fn2-network-byte-facts fn2-network-receive-byte (slot nonce fn2-sim-network)
  fn2-network-receive-byte-u8)
(defthm fn2-network-client-read-byte-u8
  (implies (and (fn2-sim-networkp fn2-sim-network)
                (fn2-sim-network-wfp fn2-sim-network))
           (unsigned-byte-p 8 (mv-nth 1 (fn2-network-client-read slot nonce fn2-sim-network))))
  :hints (("Goal" :in-theory (enable fn2-network-client-read))))

(fn2-network-byte-facts fn2-network-client-read (slot nonce fn2-sim-network)
  fn2-network-client-read-byte-u8)

(local
 (defun fn2-network-fault-test-steps (scenario nonce fn2-sim-network)
   (declare (xargs :stobjs fn2-sim-network :guard (fn2-sim-network-wfp fn2-sim-network)))
   (mv-let (input fn2-sim-network) (fn2-network-client-byte 0 nonce 42 fn2-sim-network)
     (case scenario
       (:half-open
        (mv-let (fault fn2-sim-network) (fn2-network-faults 0 nonce 1 0 0 0 fn2-sim-network)
          (mv-let (got byte fn2-sim-network) (fn2-network-receive-byte 0 nonce fn2-sim-network)
            (mv-let (end ignored fn2-sim-network) (fn2-network-receive-byte 0 nonce fn2-sim-network)
              (declare (ignore ignored))
              (mv-let (late fn2-sim-network) (fn2-network-client-byte 0 nonce 43 fn2-sim-network)
                (mv (and (eq input :ok) (eq fault :ok) (eq got :ok)
                         (equal byte 42) (eq end :would-block) (eq late :would-block)) fn2-sim-network))))))
       (:nonreading
        (mv-let (fault fn2-sim-network) (fn2-network-faults 0 nonce 0 1 0 0 fn2-sim-network)
          (mv-let (sent fn2-sim-network) (fn2-network-send-byte 0 nonce 45 fn2-sim-network)
            (mv-let (blocked ignored fn2-sim-network) (fn2-network-client-read 0 nonce fn2-sim-network)
              (declare (ignore ignored))
              (mv-let (resume fn2-sim-network) (fn2-network-faults 0 nonce 0 0 0 0 fn2-sim-network)
                (mv-let (got byte fn2-sim-network) (fn2-network-client-read 0 nonce fn2-sim-network)
                  (mv (and (eq input :ok) (eq fault :ok) (eq sent :ok)
                           (eq blocked :would-block) (eq resume :ok)
                           (eq got :ok) (equal byte 45)) fn2-sim-network)))))))
       (:reset
        (mv-let (fault fn2-sim-network) (fn2-network-faults 0 nonce 0 0 1 1 fn2-sim-network)
          (mv-let (got byte fn2-sim-network) (fn2-network-receive-byte 0 nonce fn2-sim-network)
            (mv-let (reset fn2-sim-network) (fn2-network-send-byte 0 nonce 46 fn2-sim-network)
              (mv-let (accepted new-nonce fn2-sim-network) (fn2-network-accept 0 fn2-sim-network)
                (mv-let (stale ignored fn2-sim-network) (fn2-network-receive-byte 0 nonce fn2-sim-network)
                  (declare (ignore ignored))
                  (mv-let (empty ignored fn2-sim-network) (fn2-network-receive-byte 0 new-nonce fn2-sim-network)
                    (declare (ignore ignored))
                    (mv (and (eq input :ok) (eq fault :ok) (eq got :ok) (equal byte 42)
                             (eq reset :reset) (eq accepted :ok) (equal new-nonce 2)
                             (eq stale :stale) (eq empty :would-block)) fn2-sim-network))))))))
       (otherwise
        (mv-let (closed fn2-sim-network) (fn2-network-close 0 nonce fn2-sim-network)
          (mv-let (accepted new-nonce fn2-sim-network) (fn2-network-accept 0 fn2-sim-network)
            (mv-let (stale fn2-sim-network) (fn2-network-close 0 nonce fn2-sim-network)
              (mv-let (sent fn2-sim-network) (fn2-network-send-byte 0 new-nonce 47 fn2-sim-network)
                (mv (and (eq input :ok) (eq closed :ok) (eq accepted :ok)
                         (equal new-nonce 2) (eq stale :stale) (eq sent :ok)) fn2-sim-network))))))))))
(local
 (defun fn2-network-fault-test (scenario)
   (declare (xargs :guard t))
   (with-local-stobj fn2-sim-network
     (mv-let (answer fn2-sim-network)
       (let ((fn2-sim-network (fn2-network-init 1 2 fn2-sim-network)))
         (mv-let (code nonce fn2-sim-network) (fn2-network-accept 0 fn2-sim-network)
           (mv-let (passed fn2-sim-network)
             (fn2-network-fault-test-steps scenario nonce fn2-sim-network)
             (mv (and (eq code :ok) passed) fn2-sim-network))))
       answer))))
(local (assert-event (fn2-network-fault-test :half-open)))
(local (assert-event (fn2-network-fault-test :nonreading)))
(local (assert-event (fn2-network-fault-test :reset)))
(local (assert-event (fn2-network-fault-test :close)))

; Process death closes every pipe and drops queued bytes. Retaining each
; nonce means the next accept advances it, so a pre-death capability cannot
; alias a post-restart connection. No allocation or resizing occurs here.
(defun fn2-network-drop-all (slot fn2-sim-network)
  (declare (xargs :stobjs fn2-sim-network
                  :measure (nfix (- (fn2-sim-network-rows fn2-sim-network) (nfix slot)))
                  :guard (fn2-sim-network-wfp fn2-sim-network)))
  (if (or (not (natp slot))
          (not (natp (fn2-sim-network-rows fn2-sim-network)))
          (>= slot (fn2-sim-network-rows fn2-sim-network)))
      fn2-sim-network
    (let ((fn2-sim-network
            (fn2-sim-network-put slot (phase *fn2-network-phase-closed*)
                             (rx-head 0) (rx-count 0) (tx-head 0) (tx-count 0)
                             (half-open 0) (nonreading 0) (reset-armed 0) (reset-left 0))))
      (fn2-network-drop-all (+ 1 slot) fn2-sim-network))))
(fn2-sim-network-preserves fn2-network-drop-all (slot fn2-sim-network) :position nil :prefix "" :rows nil :wfp-type nil)
(defun fn2-network-restart (fn2-sim-network)
  (declare (xargs :stobjs fn2-sim-network :guard (fn2-sim-network-wfp fn2-sim-network)))
  (fn2-network-drop-all 0 fn2-sim-network))
(fn2-sim-network-preserves fn2-network-restart (fn2-sim-network) :position nil :prefix "" :rows nil :wfp-type nil)

(assert-event (fn2-assert-compliant-p
  '(fn2-network-init fn2-network-accept fn2-network-set-peer fn2-network-peer fn2-network-close fn2-network-refuse
    fn2-network-faults fn2-network-transfer-tick fn2-network-queue-put fn2-network-queue-get
    fn2-network-client-byte fn2-network-client-read fn2-network-receive-byte fn2-network-send-byte
    fn2-network-drop-all fn2-network-restart) (w state)))
