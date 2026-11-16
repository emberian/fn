; Live-core authorization for the upper codec; private spans stay capability-owned.
(in-package "ACL2")
(include-book "host-codec")
(include-book "compress-close")
(fn2-book-layer :d)

(defun fn2-host-compress-start-op (op gen fn2-core)
 (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
 (mv-let (code kind cap nonce address length) (fn2-host-active-op op gen fn2-core)
  (cond ((not (eq code :ok)) (mv code 0 0 0 0))
        ((not (equal kind *fn2-action-compress-start*)) (mv :kind 0 0 0 0))
        (t (mv :ok cap nonce address length)))))

(defun fn2-host-compress-record-next
 (op gen fn2-compress-operation fn2-compress-transport fn2-core)
 (declare (xargs :stobjs (fn2-compress-operation fn2-compress-transport fn2-core) :verify-guards nil
  :guard (and (fn2-core-wfp fn2-core) (fn2-compress-operation-wfp fn2-compress-operation)
              (fn2-compress-transport-wfp fn2-compress-transport)
              (= (fn2-compress-transport-rows fn2-compress-transport) 1))))
 (mv-let (code kind cap nonce address length) (fn2-host-codec-op op gen fn2-core)
  (if (not (and (eq code :ok) (natp address) (unsigned-byte-p 32 length)))
      (mv (if (eq code :ok) :bounds code) 0 0 0 0 0 0 0 0 0 fn2-compress-operation fn2-compress-transport)
   (mv-let (status result fn2-compress-operation fn2-compress-transport)
    (fn2-compress-record-next cap nonce op gen (if (equal kind *fn2-action-receive*) 1 0)
                             length fn2-compress-operation fn2-compress-transport)
    (if (not (eq status :ok))
        (mv status result 0 0 0 0 0 0 0 0 fn2-compress-operation fn2-compress-transport)
     (let ((source (fn2-compress-transport-request-in-channel 0 fn2-compress-transport))
           (sink (fn2-compress-transport-request-out-channel 0 fn2-compress-transport))
           (in-offset (fn2-compress-transport-request-in-offset 0 fn2-compress-transport))
           (out-offset (fn2-compress-transport-request-out-offset 0 fn2-compress-transport)))
      (mv :act 0 (fn2-compress-transport-pending 0 fn2-compress-transport)
          source (if (= source 4) (+ address in-offset) in-offset)
          (fn2-compress-transport-request-in-count 0 fn2-compress-transport)
          sink (if (= sink 5) (+ address out-offset) out-offset)
          (fn2-compress-transport-request-out-count 0 fn2-compress-transport)
          result fn2-compress-operation fn2-compress-transport)))))))

(defcodec-host-closure fn2-host-compress fn2-compress-transport fn2-compress-operation)

(defun fn2-host-compress-close-owner (cap nonce fn2-compress-transport fn2-core)
 (declare (xargs :stobjs (fn2-compress-transport fn2-core) :verify-guards nil
  :guard (and (fn2-core-wfp fn2-core) (fn2-compress-transport-wfp fn2-compress-transport))))
 (cond
  ((= (fn2-compress-transport-rows fn2-compress-transport) 0) (mv :done 0 0))
  ((not (fn2-compress-transport-selected-p cap nonce fn2-compress-transport)) (mv :stale 0 0))
  ((= (fn2-compress-transport-pending 0 fn2-compress-transport) 0) (mv :done 0 0))
  ((not (member-equal (fn2-compress-transport-pending 0 fn2-compress-transport) '(5 6))) (mv :pending 0 0))
  (t
   (let ((op (fn2-compress-transport-slot 0 fn2-compress-transport))
         (gen (fn2-compress-transport-generation 0 fn2-compress-transport)))
    (mv-let (code kind actual-cap actual-nonce address length) (fn2-host-codec-op op gen fn2-core)
     (declare (ignore kind address length))
     (if (and (eq code :ok) (equal actual-cap cap) (equal actual-nonce nonce))
         (mv :child op gen) (mv (if (eq code :ok) :stale code) 0 0)))))))

(defun fn2-host-compress-close-child
 (op gen fn2-compress-operation fn2-compress-transport fn2-tls-transport fn2-tls-record fn2-core)
 (declare (xargs :stobjs (fn2-compress-operation fn2-compress-transport fn2-tls-transport fn2-tls-record fn2-core)
  :verify-guards nil
  :guard (and (fn2-core-wfp fn2-core) (fn2-compress-operation-wfp fn2-compress-operation)
              (fn2-compress-transport-wfp fn2-compress-transport)
              (= (fn2-compress-transport-rows fn2-compress-transport) 1)
              (fn2-tls-transport-wfp fn2-tls-transport) (fn2-tls-record-wfp fn2-tls-record))))
 (mv-let (code kind cap nonce address length) (fn2-host-codec-op op gen fn2-core)
  (declare (ignore kind address))
  (cond ((not (eq code :ok)) (mv code fn2-compress-operation fn2-compress-transport))
        ((not (= (fn2-compress-operation-rows fn2-compress-operation) 1))
         (mv :unbound fn2-compress-operation fn2-compress-transport))
        (t (mv-let (bound fn2-compress-operation)
            (fn2-compress-operation-bind cap nonce op gen length fn2-compress-operation)
            (if (not (eq bound :ok)) (mv bound fn2-compress-operation fn2-compress-transport)
             (fn2-compress-record-close-child cap nonce op gen fn2-compress-operation fn2-compress-transport
              fn2-tls-transport fn2-tls-record)))))))

; The shared accepted receipt supplies application effect coordinates. Core
; authorization excludes private TLS children and identifies the actual loan.
(defun fn2-host-compress-input-prefix
 (op gen serial action count fn2-compress-operation fn2-compress-transport fn2-core)
 (declare (xargs :stobjs (fn2-compress-operation fn2-compress-transport fn2-core) :verify-guards nil
  :guard (and (fn2-core-wfp fn2-core) (fn2-compress-operation-wfp fn2-compress-operation)
              (= (fn2-compress-operation-rows fn2-compress-operation) 1)
              (fn2-compress-transport-wfp fn2-compress-transport)
              (= (fn2-compress-transport-rows fn2-compress-transport) 1))))
 (mv-let (code kind cap nonce address length) (fn2-host-codec-op op gen fn2-core)
  (if (not (and (eq code :ok) (equal kind *fn2-action-receive*)
                (equal cap (fn2-compress-operation-cap 0 fn2-compress-operation))
                (equal nonce (fn2-compress-operation-nonce 0 fn2-compress-operation))
                (equal op (fn2-compress-operation-slot 0 fn2-compress-operation))
                (equal gen (fn2-compress-operation-generation 0 fn2-compress-operation))
                (equal length (fn2-compress-operation-extent 0 fn2-compress-operation))
                (equal serial (fn2-compress-transport-serial 0 fn2-compress-transport))
                (equal op (fn2-compress-transport-slot 0 fn2-compress-transport))
                (equal gen (fn2-compress-transport-generation 0 fn2-compress-transport))
                (equal cap (fn2-compress-transport-cap 0 fn2-compress-transport))
                (equal nonce (fn2-compress-transport-nonce 0 fn2-compress-transport))
                (= (fn2-compress-transport-pending 0 fn2-compress-transport) 0)
                (= (fn2-compress-transport-request-out-channel 0 fn2-compress-transport) 5)
                (equal count (fn2-compress-transport-raw-made 0 fn2-compress-transport))))
      (mv :none 0 0 0)
   (mv-let (effect offset made)
    (fn2-compress-operation-input-prefix serial action 10
     (fn2-compress-transport-request-out-offset 0 fn2-compress-transport) count fn2-compress-operation)
    (mv effect offset made (+ address offset))))))

(make-event
 (let* ((world (w state))
        (readers
         (append
          '(fn2-compress-operation-rows fn2-compress-transport-rows fn2-tls-transport-rows fn2-tls-record-rows
            fn2-compress-operation-bind fn2-compress-record-next fn2-compress-record-close-child)
          (fn2-columns-projection-readers 'fn2-compress-operation
           (fn2-decl-get :columns (fn2-decl-row '(:columns fn2-compress-operation) world)))
          (fn2-columns-projection-readers 'fn2-compress-transport
           (fn2-decl-get :columns (fn2-decl-row '(:columns fn2-compress-transport) world)))
          (fn2-columns-projection-readers 'fn2-tls-transport
           (fn2-decl-get :columns (fn2-decl-row '(:columns fn2-tls-transport) world)))
          (fn2-columns-projection-readers 'fn2-tls-record
           (fn2-decl-get :columns (fn2-decl-row '(:columns fn2-tls-record) world)))))
        (hints `(("Goal" :in-theory (disable ,@readers)))))
  (value `(progn
   (verify-guards fn2-host-compress-record-next :hints ,hints)
   (verify-guards fn2-host-compress-close-owner :hints ,hints)
   (verify-guards fn2-host-compress-close-child :hints ,hints)
   (verify-guards fn2-host-compress-input-prefix :hints ,hints)))))
