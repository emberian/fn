; Compression policy over the shared capability and application ledgers.
(in-package "ACL2")
(include-book "compress-transport-ops")
(include-book "compress-operation")
(include-book "std/util/bstar" :dir :system)
(fn2-book-layer :d)

; RECEIVE is a logical direction bit supplied by the admitted host boundary.
; Every physical request reserves the SAME serial in both shared ledgers.
(defun fn2-compress-record-next
 (cap nonce slot generation receive extent fn2-compress-operation fn2-compress-transport)
 (declare (xargs :stobjs (fn2-compress-operation fn2-compress-transport) :verify-guards nil
  :guard (and (fn2-compress-operation-wfp fn2-compress-operation)
              (fn2-compress-transport-wfp fn2-compress-transport)
              (= (fn2-compress-transport-rows fn2-compress-transport) 1))))
 (b* (((unless (unsigned-byte-p 1 receive))
       (mv :bounds 0 fn2-compress-operation fn2-compress-transport))
      ((mv code fn2-compress-operation)
       (fn2-compress-operation-bind cap nonce slot generation extent fn2-compress-operation))
      ((unless (eq code :ok)) (mv code 0 fn2-compress-operation fn2-compress-transport))
      ((when (not (= (fn2-compress-operation-pending-serial 0 fn2-compress-operation) 0)))
       (let ((serial (fn2-compress-operation-pending-serial 0 fn2-compress-operation)))
        (mv (if (and (fn2-compress-transport-match-p cap nonce slot generation serial fn2-compress-transport)
                     (member-equal (fn2-compress-transport-pending 0 fn2-compress-transport) '(5 6))
                     (equal (fn2-compress-transport-pending 0 fn2-compress-transport)
                            (fn2-compress-operation-pending-action 0 fn2-compress-operation))) :ok :pending)
            serial fn2-compress-operation fn2-compress-transport)))
      ((when (not (= (fn2-compress-transport-pending 0 fn2-compress-transport) 0)))
       (mv :pending 0 fn2-compress-operation fn2-compress-transport))
      (source (fn2-compress-operation-source-progress 0 fn2-compress-operation))
      (sink (fn2-compress-operation-sink-progress 0 fn2-compress-operation))
      ((unless (and (= (fn2-compress-transport-terminal 0 fn2-compress-transport) 3)
                    (= (fn2-compress-transport-alive 0 fn2-compress-transport) 1)))
       (mv :failed (if (= receive 1) sink source) fn2-compress-operation fn2-compress-transport))
      (iq (fn2-compress-transport-input-quantum 0 fn2-compress-transport))
      (oq (fn2-compress-transport-output-quantum 0 fn2-compress-transport))
      (drain (< (fn2-compress-transport-output-offset 0 fn2-compress-transport)
                (fn2-compress-transport-output-length 0 fn2-compress-transport)))
      ((when (and (not drain)
                  (or (= extent 0) (and (= receive 1) (< 0 sink))
                      (and (= receive 0) (= source extent)
                           (= (fn2-compress-operation-flush-complete 0 fn2-compress-operation) 1)))))
       (mv-let (finished fn2-compress-operation) (fn2-compress-operation-finish fn2-compress-operation)
        (mv (if (eq finished :ok) :done finished) (if (= receive 1) sink source)
            fn2-compress-operation fn2-compress-transport)))
      (serial (+ 1 (fn2-compress-transport-serial 0 fn2-compress-transport)))
      (action (if drain 5 (if (= receive 1)
                  (if (= (fn2-compress-operation-need-input 0 fn2-compress-operation) 1) 6 10) 11)))
      (source-count (if (= action 11) (min iq (nfix (- extent source))) 0))
      (sink-count (if (= action 10)
                      (min (nfix (- extent sink))
                           (min oq (fn2-compress-transport-credit 0 fn2-compress-transport))) 0))
      ((unless (fn2-compress-operation-requestable-p serial action source-count sink-count fn2-compress-operation))
       (mv :bounds 0 fn2-compress-operation fn2-compress-transport))
      ((mv code serial fn2-compress-transport)
       (cond (drain (fn2-compress-transport-select-drain cap nonce slot generation fn2-compress-transport))
             ((= action 6) (fn2-compress-transport-select-fill cap nonce slot generation fn2-compress-transport))
             ((= receive 1) (fn2-compress-transport-select-decode cap nonce slot generation sink extent fn2-compress-transport))
             (t (fn2-compress-transport-select-encode cap nonce slot generation source extent
                  (fn2-compress-operation-flush-complete 0 fn2-compress-operation) fn2-compress-transport))))
      ((unless (eq code :ok))
       (let ((fn2-compress-transport
              (if (eq code :limit) (fn2-compress-transport-put 0 (terminal 2)) fn2-compress-transport)))
        (mv (if (eq code :limit) :failed code) (if (= receive 1) sink source)
            fn2-compress-operation fn2-compress-transport)))
      ((mv code fn2-compress-operation)
       (fn2-compress-operation-request serial action source-count sink-count fn2-compress-operation)))
  (mv code serial fn2-compress-operation fn2-compress-transport)))

; Both observers validate before application policy changes. A stale or replayed
; completion cannot replenish credit, finish a flush or advance application work.
(defun fn2-compress-record-observe
 (cap nonce slot generation serial raw used made errno fn2-compress-operation fn2-compress-transport)
 (declare (xargs :stobjs (fn2-compress-operation fn2-compress-transport) :verify-guards nil
  :guard (and (fn2-compress-operation-wfp fn2-compress-operation)
              (= (fn2-compress-operation-rows fn2-compress-operation) 1)
              (fn2-compress-transport-wfp fn2-compress-transport)
              (= (fn2-compress-transport-rows fn2-compress-transport) 1))))
 (b* ((action (fn2-compress-transport-pending 0 fn2-compress-transport))
      (app-used (if (= action 11) used 0))
      (app-made (if (= action 10) made 0))
      ((unless (and (fn2-compress-transport-match-p cap nonce slot generation serial fn2-compress-transport)
                    (equal action (fn2-compress-operation-pending-action 0 fn2-compress-operation))
                    (equal cap (fn2-compress-operation-cap 0 fn2-compress-operation))
                    (equal nonce (fn2-compress-operation-nonce 0 fn2-compress-operation))
                    (equal slot (fn2-compress-operation-slot 0 fn2-compress-operation))
                    (equal generation (fn2-compress-operation-generation 0 fn2-compress-operation))
                    (member-equal action '(5 6 10 11))
                    (fn2-compress-operation-observable-p serial app-used app-made fn2-compress-operation)))
       (mv :stale fn2-compress-operation fn2-compress-transport))
      (requested-output (fn2-compress-transport-request-out-count 0 fn2-compress-transport))
      ((mv policy credit)
       (if (= action 10)
           (fn2-compress-observe raw used made
            (fn2-compress-transport-request-in-count 0 fn2-compress-transport) requested-output
            (fn2-compress-transport-credit 0 fn2-compress-transport)
            (fn2-compress-transport-ratio 0 fn2-compress-transport)
            (fn2-compress-transport-burst 0 fn2-compress-transport))
         (mv (if (member-equal action '(5 6))
                 (cond ((and (integerp raw) (< raw 0) (member-equal errno '(4 11 35))) :blocked)
                       ((and (integerp raw) (<= 0 raw) (< 0 (+ (nfix used) (nfix made)))) :progress)
                       (t :failed))
               (if (equal raw 0) :progress :failed))
             (fn2-compress-transport-credit 0 fn2-compress-transport))))
      ((when (eq policy :bounds)) (mv :bounds fn2-compress-operation fn2-compress-transport))
      ((mv code fn2-compress-transport)
       (fn2-compress-transport-observe-spans cap nonce slot generation serial raw used made errno fn2-compress-transport))
      ((unless (eq code :ok)) (mv code fn2-compress-operation fn2-compress-transport))
      ((mv code fn2-compress-operation)
       (fn2-compress-operation-observe serial app-used app-made fn2-compress-operation))
      (fn2-compress-transport
       (if (member-equal policy '(:failed :final))
           (fn2-compress-transport-put 0 (credit credit) (terminal 2))
         (fn2-compress-transport-put 0 (credit credit))))
      (fn2-compress-operation
       (if (and (= action 6) (not (eq policy :blocked)))
           (fn2-compress-operation-put 0 (need-input 0))
        (if (and (= action 10) (eq policy :need-input))
            (fn2-compress-operation-put 0 (need-input 1)) fn2-compress-operation)))
      (fn2-compress-operation
       (if (and (= action 11) (equal raw 0)
                (= (fn2-compress-operation-source-progress 0 fn2-compress-operation)
                   (fn2-compress-operation-extent 0 fn2-compress-operation))
                (< made requested-output))
           (fn2-compress-operation-put 0 (flush-complete 1))
         fn2-compress-operation))
      (fn2-compress-operation
       (fn2-compress-operation-put 0 (kick (if (eq policy :blocked) 0 1))
          (interest (if (= action 5) 4 1)))))
  (mv (if (eq code :ok) policy code) fn2-compress-operation fn2-compress-transport)))

; Carrier results arrive either from a completed TLS child or a raw syscall.
; A blocked child retains the SAME parent epoch; it never earns decode credit.
(defun fn2-compress-record-carrier-observe
 (status count fn2-compress-operation fn2-compress-transport)
 (declare (xargs :stobjs (fn2-compress-operation fn2-compress-transport) :verify-guards nil
  :guard (and (fn2-compress-operation-wfp fn2-compress-operation)
              (= (fn2-compress-operation-rows fn2-compress-operation) 1)
              (fn2-compress-transport-wfp fn2-compress-transport)
              (= (fn2-compress-transport-rows fn2-compress-transport) 1))))
 (b* ((action (fn2-compress-transport-pending 0 fn2-compress-transport))
      (serial (fn2-compress-operation-pending-serial 0 fn2-compress-operation))
      ((unless (member-equal action '(5 6))) (mv :state fn2-compress-operation fn2-compress-transport))
      ((when (member-equal status '(:progress :pending :blocked)))
       (mv :blocked fn2-compress-operation fn2-compress-transport))
      ((unless (and (unsigned-byte-p 32 count) (member-equal status '(:done :eof :failed))
                    (equal action (fn2-compress-operation-pending-action 0 fn2-compress-operation))
                    (fn2-compress-operation-observable-p serial 0 0 fn2-compress-operation)))
       (mv :bounds fn2-compress-operation fn2-compress-transport))
      ((mv code fn2-compress-transport)
       (fn2-compress-transport-advance-spans
        (fn2-compress-operation-cap 0 fn2-compress-operation)
        (fn2-compress-operation-nonce 0 fn2-compress-operation)
        (fn2-compress-operation-slot 0 fn2-compress-operation)
        (fn2-compress-operation-generation 0 fn2-compress-operation)
        serial (if (= action 5) count 0) (if (= action 6) count 0) fn2-compress-transport))
      ((unless (eq code :ok)) (mv code fn2-compress-operation fn2-compress-transport))
      ((mv code fn2-compress-operation) (fn2-compress-operation-observe serial 0 0 fn2-compress-operation))
      (productive (and (eq status :done) (< 0 count)))
      (fn2-compress-transport (if productive fn2-compress-transport
                               (fn2-compress-transport-put 0 (terminal 2))))
      (fn2-compress-operation
       (if (= action 6) (fn2-compress-operation-put 0 (need-input 0) (kick 1))
         (fn2-compress-operation-put 0 (kick 1)))))
  (mv (if (eq code :ok) (if productive :progress :failed) code)
      fn2-compress-operation fn2-compress-transport)))

(defun fn2-compress-record-socket-observe
 (raw errno fn2-compress-operation fn2-compress-transport)
 (declare (xargs :stobjs (fn2-compress-operation fn2-compress-transport) :verify-guards nil
  :guard (and (fn2-compress-operation-wfp fn2-compress-operation)
              (= (fn2-compress-operation-rows fn2-compress-operation) 1)
              (fn2-compress-transport-wfp fn2-compress-transport)
              (= (fn2-compress-transport-rows fn2-compress-transport) 1))))
 (let ((action (fn2-compress-transport-pending 0 fn2-compress-transport)))
  (if (not (and (integerp raw) (unsigned-byte-p 64 (abs raw))
                (unsigned-byte-p 32 errno) (member-equal action '(5 6))))
      (mv :bounds fn2-compress-operation fn2-compress-transport)
   (fn2-compress-record-observe
    (fn2-compress-operation-cap 0 fn2-compress-operation)
    (fn2-compress-operation-nonce 0 fn2-compress-operation)
    (fn2-compress-operation-slot 0 fn2-compress-operation)
    (fn2-compress-operation-generation 0 fn2-compress-operation)
    (fn2-compress-operation-pending-serial 0 fn2-compress-operation)
    raw (if (and (= action 5) (< 0 raw)) raw 0)
        (if (and (= action 6) (< 0 raw)) raw 0) errno
    fn2-compress-operation fn2-compress-transport))))

(defun fn2-compress-record-wait (fn2-compress-operation)
 (declare (xargs :stobjs fn2-compress-operation :verify-guards nil
                 :guard (fn2-compress-operation-wfp fn2-compress-operation)))
 (if (or (= (fn2-compress-operation-rows fn2-compress-operation) 0)
         (= (fn2-compress-operation-last-serial 0 fn2-compress-operation) 0))
     (mv 1 t)
   (mv (fn2-compress-operation-interest 0 fn2-compress-operation)
       (= (fn2-compress-operation-kick 0 fn2-compress-operation) 1))))

; Keep the generated scalar abstraction in guard proofs. Common row frames
; connect the two ledgers after observations without opening either updater.
(make-event
 (let* ((world (w state))
        (readers
         (append
          '(fn2-compress-transport-rows fn2-compress-operation-rows
            fn2-compress-operation-bind fn2-compress-operation-request fn2-compress-operation-observe
            fn2-compress-operation-requestable-p fn2-compress-operation-observable-p fn2-compress-observe
            fn2-compress-transport-observe-spans fn2-compress-transport-advance-spans fn2-compress-transport-select
            fn2-compress-transport-select-encode fn2-compress-transport-select-decode
            fn2-compress-transport-select-drain fn2-compress-transport-select-fill)
          (fn2-columns-projection-readers 'fn2-compress-transport
           (fn2-decl-get :columns (fn2-decl-row '(:columns fn2-compress-transport) world)))
          (fn2-columns-projection-readers 'fn2-compress-operation
           (fn2-decl-get :columns (fn2-decl-row '(:columns fn2-compress-operation) world)))))
        (hints `(("Goal" :in-theory (disable ,@readers))))
        (observe-hints
         `(("Goal" :in-theory
             (disable ,@readers fn2-compress-operation-observe-preserves-type
                      fn2-compress-operation-observe-wfp fn2-compress-operation-observe-rows
                      fn2-compress-transport-observe-spans-ok-inputs)
             :use ((:instance fn2-compress-transport-observe-spans-ok-inputs (raw-code raw))
                   (:instance fn2-compress-operation-observe-preserves-type
                      (used (if (= (fn2-compress-transport-pending 0 fn2-compress-transport) 11) used 0))
                      (made (if (= (fn2-compress-transport-pending 0 fn2-compress-transport) 10) made 0)))
                   (:instance fn2-compress-operation-observe-wfp
                      (used (if (= (fn2-compress-transport-pending 0 fn2-compress-transport) 11) used 0))
                      (made (if (= (fn2-compress-transport-pending 0 fn2-compress-transport) 10) made 0)))
                   (:instance fn2-compress-operation-observe-rows
                      (used (if (= (fn2-compress-transport-pending 0 fn2-compress-transport) 11) used 0))
                      (made (if (= (fn2-compress-transport-pending 0 fn2-compress-transport) 10) made 0)))))))
        (next-hints `(("Goal" :in-theory
                        (disable ,@readers fn2-compress-operation-bind-preserves-type
                         fn2-compress-operation-bind-ok-inputs fn2-compress-operation-bind-wfp
                         fn2-compress-operation-bind-rows-ok)
                       :use (fn2-compress-operation-bind-preserves-type
                             fn2-compress-operation-bind-ok-inputs fn2-compress-operation-bind-wfp
                             fn2-compress-operation-bind-rows-ok)))))
  (value `(progn
   (verify-guards fn2-compress-record-next :hints ,next-hints)
   (verify-guards fn2-compress-record-observe :hints ,observe-hints)
   (verify-guards fn2-compress-record-carrier-observe :hints ,hints)
   (verify-guards fn2-compress-record-socket-observe :hints ,hints)
   (verify-guards fn2-compress-record-wait :hints ,hints)))))
