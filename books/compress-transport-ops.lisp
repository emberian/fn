; Actual per-call prefix admission is emitted by the shared codec generator.
(in-package "ACL2")
(include-book "compress-transport-state")
(include-book "compress-policy")
(fn2-book-layer :d)
(defcodec-transport-operations fn2-compress-transport
 :input-quantum-field input-quantum :output-quantum-field output-quantum)

; Encode only into an empty FULL private window. Socket backpressure drains
; that window first; neither network room nor receive-credit shrinks a flush.
; zlib's Z_SYNC_FLUSH contract requires more than six output octets per call.
(defun fn2-compress-transport-select-encode
 (cap nonce slot generation source-offset source-total flush-complete fn2-compress-transport)
 (declare (xargs :stobjs fn2-compress-transport :verify-guards nil
                 :guard (and (fn2-compress-transport-wfp fn2-compress-transport)
                             (= (fn2-compress-transport-rows fn2-compress-transport) 1))))
 (let ((iq (fn2-compress-transport-input-quantum 0 fn2-compress-transport))
       (oq (fn2-compress-transport-output-quantum 0 fn2-compress-transport)))
  (cond
   ((not (and (unsigned-byte-p 32 source-offset) (unsigned-byte-p 32 source-total)
              (<= source-offset source-total) (unsigned-byte-p 1 flush-complete) (posp iq) (<= *fn2-compress-min-output-window* oq)))
    (mv :bounds 0 fn2-compress-transport))
   ((not (equal (fn2-compress-transport-output-offset 0 fn2-compress-transport)
                (fn2-compress-transport-output-length 0 fn2-compress-transport)))
    (mv :need-output 0 fn2-compress-transport))
   ((equal flush-complete 1)
    (mv (if (equal source-offset source-total) :done :bounds) 0 fn2-compress-transport))
   (t (fn2-compress-transport-select cap nonce slot generation 11
        4 source-offset (min iq (- source-total source-offset)) source-total
        3 0 oq oq fn2-compress-transport)))))
(verify-guards fn2-compress-transport-select-encode
 :hints (("Goal" :in-theory (disable fn2-compress-transport-rows fn2-compress-transport-input-quantum fn2-compress-transport-output-quantum fn2-compress-transport-output-offset fn2-compress-transport-output-length))))

; Decode may expose one application octet at a time. It consumes retained
; upgrade input before asking the lower carrier to fill the input window.
(defun fn2-compress-transport-select-decode
 (cap nonce slot generation sink-offset sink-total fn2-compress-transport)
 (declare (xargs :stobjs fn2-compress-transport :verify-guards nil
                 :guard (and (fn2-compress-transport-wfp fn2-compress-transport)
                             (= (fn2-compress-transport-rows fn2-compress-transport) 1))))
 (if (not (and (unsigned-byte-p 32 sink-offset) (unsigned-byte-p 32 sink-total)
               (<= sink-offset sink-total)))
     (mv :bounds 0 fn2-compress-transport)
  (let* ((fed (fn2-compress-transport-fed 0 fn2-compress-transport))
         (copied (fn2-compress-transport-copied 0 fn2-compress-transport))
         (seed (< fed copied))
         (source-offset (if seed fed (fn2-compress-transport-input-offset 0 fn2-compress-transport)))
         (source-total (if seed copied (fn2-compress-transport-input-length 0 fn2-compress-transport))))
   (mv-let (code input output)
    (fn2-compress-plan (nfix (- source-total source-offset)) (- sink-total sink-offset)
      (fn2-compress-transport-input-quantum 0 fn2-compress-transport)
      (fn2-compress-transport-output-quantum 0 fn2-compress-transport)
      (fn2-compress-transport-credit 0 fn2-compress-transport))
    (if (not (eq code :transform)) (mv code 0 fn2-compress-transport)
     (fn2-compress-transport-select cap nonce slot generation 10
       (if seed 1 2) source-offset input source-total
       5 sink-offset output sink-total fn2-compress-transport))))))
(verify-guards fn2-compress-transport-select-decode
 :hints (("Goal" :in-theory (disable fn2-compress-transport-rows fn2-compress-transport-fed fn2-compress-transport-copied fn2-compress-transport-input-offset fn2-compress-transport-input-length fn2-compress-transport-input-quantum fn2-compress-transport-output-quantum fn2-compress-transport-credit))))

; Lower-carrier requests keep the parent serial pending until the child
; finishes. Wire prefixes never advance application progress.
(defun fn2-compress-transport-select-drain
 (cap nonce slot generation fn2-compress-transport)
 (declare (xargs :stobjs fn2-compress-transport :verify-guards nil
  :guard (and (fn2-compress-transport-wfp fn2-compress-transport)
              (= (fn2-compress-transport-rows fn2-compress-transport) 1))))
 (let ((offset (fn2-compress-transport-output-offset 0 fn2-compress-transport))
       (length (fn2-compress-transport-output-length 0 fn2-compress-transport)))
  (if (not (< offset length)) (mv :done 0 fn2-compress-transport)
   (fn2-compress-transport-select cap nonce slot generation 5
    3 offset (min (fn2-compress-transport-input-quantum 0 fn2-compress-transport)
                  (- length offset)) length
    0 0 0 0 fn2-compress-transport))))
(verify-guards fn2-compress-transport-select-drain
 :hints (("Goal" :in-theory (disable fn2-compress-transport-rows fn2-compress-transport-output-offset fn2-compress-transport-output-length fn2-compress-transport-input-quantum))))

(defun fn2-compress-transport-select-fill
 (cap nonce slot generation fn2-compress-transport)
 (declare (xargs :stobjs fn2-compress-transport :verify-guards nil
  :guard (and (fn2-compress-transport-wfp fn2-compress-transport)
              (= (fn2-compress-transport-rows fn2-compress-transport) 1))))
 (cond
  ((< (fn2-compress-transport-fed 0 fn2-compress-transport)
      (fn2-compress-transport-copied 0 fn2-compress-transport))
   (mv :have-input 0 fn2-compress-transport))
  ((not (equal (fn2-compress-transport-input-offset 0 fn2-compress-transport)
               (fn2-compress-transport-input-length 0 fn2-compress-transport)))
   (mv :have-input 0 fn2-compress-transport))
  (t (let ((iq (fn2-compress-transport-input-quantum 0 fn2-compress-transport))
           (oq (fn2-compress-transport-output-quantum 0 fn2-compress-transport)))
      (fn2-compress-transport-select cap nonce slot generation 6
       0 0 0 0 2 0 (min iq oq) iq fn2-compress-transport)))))
(verify-guards fn2-compress-transport-select-fill
 :hints (("Goal" :in-theory (disable fn2-compress-transport-rows fn2-compress-transport-fed fn2-compress-transport-copied fn2-compress-transport-input-offset fn2-compress-transport-input-length fn2-compress-transport-input-quantum fn2-compress-transport-output-quantum))))

; Export the same concrete type, invariant and row frames as other generated
; column consumers. NEXT need not unfold a selector or its transport updater.
(make-event
 (let* ((readers (cons 'fn2-compress-transport-rows
                  (fn2-columns-projection-readers 'fn2-compress-transport
                   (fn2-decl-get :columns
                    (fn2-decl-row '(:columns fn2-compress-transport) (w state))))))
        (hyps '((fn2-compress-transportp fn2-compress-transport)
                (fn2-compress-transport-wfp fn2-compress-transport)
                (= (fn2-compress-transport-rows fn2-compress-transport) 1)))
        (hints `(("Goal" :in-theory (disable ,@readers)))))
  (value `(progn
   (fn2-compress-transport-preserves fn2-compress-transport-select-encode
    (cap nonce slot generation source-offset source-total flush-complete fn2-compress-transport)
    :position 2 :hyps ,hyps :hints ,hints :forward t :disable nil)
   (fn2-compress-transport-preserves fn2-compress-transport-select-decode
    (cap nonce slot generation sink-offset sink-total fn2-compress-transport)
    :position 2 :hyps ,hyps :hints ,hints :forward t :disable nil)
   (fn2-compress-transport-preserves fn2-compress-transport-select-drain
    (cap nonce slot generation fn2-compress-transport)
    :position 2 :hyps ,hyps :hints ,hints :forward t :disable nil)
   (fn2-compress-transport-preserves fn2-compress-transport-select-fill
    (cap nonce slot generation fn2-compress-transport)
    :position 2 :hyps ,hyps :hints ,hints :forward t :disable nil)))))

(defthm-owed fn2-compress-encoder-window-full (cap nonce slot generation source-offset source-total flush-complete s)
 (implies (and (fn2-compress-transportp s) (fn2-compress-transport-wfp s)
               (equal (fn2-compress-transport-rows s) 1)
               (equal (mv-nth 0 (fn2-compress-transport-select-encode
                                  cap nonce slot generation source-offset source-total flush-complete s)) :ok))
  (let ((next (mv-nth 2 (fn2-compress-transport-select-encode
                           cap nonce slot generation source-offset source-total flush-complete s))))
   (and (equal (fn2-compress-transport-output-offset 0 s)
               (fn2-compress-transport-output-length 0 s))
        (equal (fn2-compress-transport-request-out-channel 0 next) 3)
        (equal (fn2-compress-transport-request-out-offset 0 next) 0)
        (<= *fn2-compress-min-output-window* (fn2-compress-transport-request-out-count 0 next))
        (equal (fn2-compress-transport-request-out-count 0 next)
               (fn2-compress-transport-output-quantum 0 next))
        (equal (fn2-compress-transport-request-out-extent 0 next)
               (fn2-compress-transport-output-quantum 0 next)))))
 :schema :bound
 :teeth (fn2-compress-selected-window-test fn2-compress-rejected-window-control)
 :doc "The actual compression selector never issues a sync flush into a partial, credit-clipped or sub-seven-octet output window.")
(defthm fn2-compress-encoder-window-full
 (implies (and (fn2-compress-transportp s) (fn2-compress-transport-wfp s)
               (equal (fn2-compress-transport-rows s) 1)
               (equal (mv-nth 0 (fn2-compress-transport-select-encode
                                  cap nonce slot generation source-offset source-total flush-complete s)) :ok))
  (let ((next (mv-nth 2 (fn2-compress-transport-select-encode
                           cap nonce slot generation source-offset source-total flush-complete s))))
   (and (equal (fn2-compress-transport-output-offset 0 s)
               (fn2-compress-transport-output-length 0 s))
        (equal (fn2-compress-transport-request-out-channel 0 next) 3)
        (equal (fn2-compress-transport-request-out-offset 0 next) 0)
        (<= *fn2-compress-min-output-window* (fn2-compress-transport-request-out-count 0 next))
        (equal (fn2-compress-transport-request-out-count 0 next)
               (fn2-compress-transport-output-quantum 0 next))
        (equal (fn2-compress-transport-request-out-extent 0 next)
               (fn2-compress-transport-output-quantum 0 next))))))
(fn2-owed-discharge fn2-compress-encoder-window-full fn2-compress-encoder-window-full)
