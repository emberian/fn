; Raw Common Lisp acceptance instrumentation, loaded after ACL2's :q and LD.
; No served definition or logical event changes. Only the scenario-bound
; concrete core is observed (its pool child, by identity); the separately
; allocated reference core is not. Observed at the pool's exports, so a
; machine that reads inside a stobj-let of the pool (fn2-conn, the grammar)
; is seen as one that calls fn2-core-read is: fn2-pool-read and every range
; primitive report the bytes they examined, fn2-pool-write and the moving
; ranges (copy-range, drop-prefix) the bytes they wrote. A new range
; primitive must be added here.
(in-package "ACL2")
(defvar *fn2-own-hook-originals* nil)
(defvar *fn2-own-hook-core* nil)
(defvar *fn2-own-hook-monitor* nil)
(defvar *fn2-own-hook-read-original* nil)
(defvar *fn2-own-hook-reads* (make-hash-table))

(defun fn2-own-hook-reset ()
  (clrhash *fn2-own-hook-reads*))

(defun fn2-own-hook-pool-p (pool)
  (and *fn2-own-hook-core* (eq pool (fn2-core-pool *fn2-own-hook-core*))))
(defun fn2-own-hook-original (name)
  (cdr (assoc name *fn2-own-hook-originals*)))
(defun fn2-own-hook-byte (slot index pool)
  (fn2-pool-datai (+ (fn2-pool-base slot pool) index) pool))
; One examined byte (BYTE as the primitive saw it) and one written byte.
(defun fn2-own-hook-saw (slot gen index byte kind pool)
  (assert *fn2-own-hook-monitor*)
  (incf (gethash kind *fn2-own-hook-reads* 0))
  (fn2-own-observe-read-parts slot gen index :ok byte pool *fn2-own-hook-monitor*))
(defun fn2-own-hook-wrote (slot gen index pool)
  (fn2-own-observe-core-write-parts slot gen index :ok (fn2-own-hook-byte slot index pool)
                                    pool *fn2-own-hook-monitor*))
(defun fn2-own-hook-saw-range (slot gen off n kind pool)
  (loop for i from off below (+ off n)
        do (fn2-own-hook-saw slot gen i (fn2-own-hook-byte slot i pool) kind pool)))
(defun fn2-own-hook-capture (slot off n pool)
  (loop for i from off below (+ off n) collect (fn2-own-hook-byte slot i pool)))

(defun fn2-own-hook-read (slot gen index kind owner owner-gen pool)
  (multiple-value-bind (code byte)
      (funcall *fn2-own-hook-read-original* slot gen index kind owner owner-gen pool)
    (when (fn2-own-hook-pool-p pool)
      (assert *fn2-own-hook-monitor*)
      (incf (gethash kind *fn2-own-hook-reads* 0))
      (fn2-own-observe-read-parts slot gen index code byte pool *fn2-own-hook-monitor*))
    (values code byte)))
(defun fn2-own-hook-write (slot gen index byte kind owner owner-gen pool)
  (multiple-value-bind (code pool)
      (funcall (fn2-own-hook-original 'fn2-pool-write) slot gen index byte kind owner owner-gen pool)
    (when (fn2-own-hook-pool-p pool)
      ; A legitimate scribe refill supersedes old received provenance.
      (fn2-own-observe-core-write-parts slot gen index code byte pool *fn2-own-hook-monitor*))
    (values code pool)))
; Scan examines its range up to and including the match (both bytes of CR LF).
(defun fn2-own-hook-scan (slot gen off len target kind owner owner-gen pool)
  (multiple-value-bind (code at)
      (funcall (fn2-own-hook-original 'fn2-pool-scan) slot gen off len target kind owner owner-gen pool)
    (when (and (fn2-own-hook-pool-p pool) (eq code :ok))
      (fn2-own-hook-saw-range slot gen off
        (if (< at len) (min len (+ at (if (eql target *fn2-pool-scan-crlf*) 2 1))) len) kind pool))
    (values code at)))
; Compare examines both ranges up to and including the first difference.
(defun fn2-own-hook-compare (s1 g1 off1 k1 os1 og1 s2 g2 off2 k2 os2 og2 len pool)
  (multiple-value-bind (code result at)
      (funcall (fn2-own-hook-original 'fn2-pool-compare) s1 g1 off1 k1 os1 og1 s2 g2 off2 k2 os2 og2 len pool)
    (when (and (fn2-own-hook-pool-p pool) (eq code :ok))
      (let ((n (min len (+ at 1))))
        (fn2-own-hook-saw-range s1 g1 off1 n k1 pool)
        (fn2-own-hook-saw-range s2 g2 off2 n k2 pool)))
    (values code result at)))
(defun fn2-own-hook-fold (slot gen off len hash kind owner owner-gen pool)
  (multiple-value-bind (code h)
      (funcall (fn2-own-hook-original 'fn2-pool-fold) slot gen off len hash kind owner owner-gen pool)
    (when (and (fn2-own-hook-pool-p pool) (eq code :ok))
      (fn2-own-hook-saw-range slot gen off len kind pool))
    (values code h)))
; The moving ranges: the source bytes as they were before the move, then
; the destination bytes as written.
(defun fn2-own-hook-copy-range (src sgen soff dst dgen doff len kind owner owner-gen pool)
  (let* ((watch (fn2-own-hook-pool-p pool))
         (before (and watch (natp soff) (natp len) (< src (fn2-pool-rows pool))
                      (<= (+ (fn2-pool-base src pool) soff len) (fn2-pool-data-length pool))
                      (fn2-own-hook-capture src soff len pool))))
    (multiple-value-bind (code pool)
        (funcall (fn2-own-hook-original 'fn2-pool-copy-range) src sgen soff dst dgen doff len kind owner owner-gen pool)
      (when (and watch (eq code :ok))
        (loop for i from soff for byte in before do (fn2-own-hook-saw src sgen i byte kind pool))
        (loop for i from doff below (+ doff len) do (fn2-own-hook-wrote dst dgen i pool)))
      (values code pool))))
; Drop-prefix shrinks the fill when it finishes, so its source bytes are
; observed before the move, under the export's own acceptance conditions
; (restated here and asserted against its answer: a hook out of step with
; the primitive fails loudly).
(defun fn2-own-hook-drop-prefix (slot gen k cursor limit kind owner owner-gen pool)
  (let* ((watch (and (fn2-own-hook-pool-p pool)
                     (eq (fn2-pool-workspace-code slot gen kind owner owner-gen pool) :ok)
                     (natp k) (natp cursor) (natp limit)
                     (<= k (fn2-pool-fill slot pool)) (<= cursor (- (fn2-pool-fill slot pool) k))
                     (fn2-pool-range-in slot 0 (fn2-pool-fill slot pool) pool)))
         (n (and watch (min limit (- (fn2-pool-fill slot pool) k cursor)))))
    (when watch (fn2-own-hook-saw-range slot gen (+ k cursor) n kind pool))
    (multiple-value-bind (code next pool)
        (funcall (fn2-own-hook-original 'fn2-pool-drop-prefix) slot gen k cursor limit kind owner owner-gen pool)
      (when (fn2-own-hook-pool-p pool)
        (assert (eq (and watch t) (and (member code '(:ok :more)) t)))
        (when watch
          (loop for i from cursor below (+ cursor n) do (fn2-own-hook-wrote slot gen i pool))))
      (values code next pool))))

(defparameter *fn2-own-hook-pool-hooks*
  '((fn2-pool-read . fn2-own-hook-read) (fn2-pool-write . fn2-own-hook-write)
    (fn2-pool-scan . fn2-own-hook-scan) (fn2-pool-compare . fn2-own-hook-compare)
    (fn2-pool-fold . fn2-own-hook-fold) (fn2-pool-copy-range . fn2-own-hook-copy-range)
    (fn2-pool-drop-prefix . fn2-own-hook-drop-prefix)))
(defun fn2-own-hook-install ()
  (assert (null *fn2-own-hook-originals*))
  (dolist (entry *fn2-own-hook-pool-hooks*)
    (push (cons (car entry) (symbol-function (car entry))) *fn2-own-hook-originals*))
  ; fn2-own-check-trace-turn is the A4 scenarios' (echo-scenario.lisp); a
  ; driver without it (D's sim-layer-d) binds the core and monitor itself.
  (when (fboundp 'fn2-own-check-trace-turn)
    (push (cons 'fn2-own-check-trace-turn (symbol-function 'fn2-own-check-trace-turn))
          *fn2-own-hook-originals*))
  (setf *fn2-own-hook-read-original* (fn2-own-hook-original 'fn2-pool-read))
  (dolist (entry *fn2-own-hook-pool-hooks*)
    (setf (symbol-function (car entry)) (symbol-function (cdr entry))))
  (let ((turn (fn2-own-hook-original 'fn2-own-check-trace-turn)))
    (when turn
      (setf (symbol-function 'fn2-own-check-trace-turn)
            (lambda (profile cursor queues core own reference)
              (let ((*fn2-own-hook-core* core) (*fn2-own-hook-monitor* own))
                (funcall turn profile cursor queues core own reference))))))
  (fn2-own-hook-reset))

(defun fn2-own-hook-restore ()
  (dolist (entry *fn2-own-hook-originals*)
    (setf (symbol-function (car entry)) (cdr entry)))
  (setf *fn2-own-hook-originals* nil *fn2-own-hook-read-original* nil))

(defun fn2-own-hook-report (label &optional require-scribe)
  (when require-scribe
    (assert (plusp (gethash *fn2-scribe-kind* *fn2-own-hook-reads* 0))))
  (format t "OWN READS ~A listener=~D echo/null=~D scribe=~D total=~D~%"
          label
          (gethash *fn2-listener-kind* *fn2-own-hook-reads* 0)
          (gethash *fn2-echo-kind* *fn2-own-hook-reads* 0)
          (gethash *fn2-scribe-kind* *fn2-own-hook-reads* 0)
          (loop for n being the hash-values of *fn2-own-hook-reads* sum n)))

; Mutate the raw read result, not the monitor: even when a broken reader
; claims :ok, the same installed hook must reject past-fill and leased-in.
; A legal positive and a separate-core exclusion control precede the faults.
(defun fn2-own-hook-control ()
  (assert *fn2-own-hook-originals*)
  (let* ((core (create-fn2-core)) (own (create-fn2-own))
         (*fn2-own-hook-core* core) (*fn2-own-hook-monitor* own))
    (fn2-core-init *fn2-profile-tiny* core)
    (fn2-own-init *fn2-profile-tiny* own)
    (multiple-value-bind (code slot gen) (fn2-core-reserve 0 1 0 1 core)
      (assert (eq code :ok))
      (assert (eq (fn2-core-write slot gen 0 99 1 0 1 core) :ok))
      (multiple-value-bind (code byte) (fn2-core-read slot gen 0 1 0 1 core)
        (assert (and (eq code :ok) (= byte 99) (eq (fn2-own-status own) :pass))))
      (let ((*fn2-own-hook-core* (create-fn2-core))
            (before (gethash 1 *fn2-own-hook-reads* 0)))
        (fn2-core-read slot gen 0 1 0 1 core)
        (assert (= before (gethash 1 *fn2-own-hook-reads* 0))))
      (assert (not (eq (fn2-core-read slot gen 1 1 0 1 core) :ok)))
      (assert (eq (fn2-own-status own) :pass))
      (let ((*fn2-own-hook-read-original*
              (lambda (&rest args) (declare (ignore args)) (values :ok 99))))
        (fn2-core-read slot gen 1 1 0 1 core)
        (assert (equal (fn2-own-status own) '(:fail :unreadable-input))))
      (update-fn2-own-error 0 own)
      (assert (eq (fn2-core-reset slot gen 1 0 1 core) :ok))
      (assert (eq (fn2-pool-lease-in slot gen 1 0 1 1 0 1 (fn2-core-pool core)) :ok))
      (assert (not (eq (fn2-core-read slot gen 0 1 0 1 core) :ok)))
      (assert (eq (fn2-own-status own) :pass))
      (let ((*fn2-own-hook-read-original*
              (lambda (&rest args) (declare (ignore args)) (values :ok 99))))
        (fn2-core-read slot gen 0 1 0 1 core)
        (assert (equal (fn2-own-status own) '(:fail :unreadable-input))))))
  (format t "OWN READ HOOK CONTROLS legal=PASS separate-core=PASS real-refusals=PASS past-fill=REJECTED leased-in=REJECTED~%")
  (fn2-own-hook-reset))

; The range hooks' controls (sim-layer-d-evidence runs them before D's sets):
; a machine-written line scanned for CR LF counts every examined byte and
; passes; with byte 0 marked as received 'A' (the input provenance the
; adapter records) the scan still passes; once the pool's byte is changed
; behind OWN's back, the scan and a drop-prefix over it each fail as an input
; byte mismatch; a legal drop-prefix of a machine-written tail passes.
(defun fn2-own-hook-range-control ()
  (assert *fn2-own-hook-originals*)
  (let* ((core (create-fn2-core)) (own (create-fn2-own))
         (*fn2-own-hook-core* core) (*fn2-own-hook-monitor* own))
    (fn2-core-init *fn2-profile-tiny* core)
    (fn2-own-init *fn2-profile-tiny* own)
    (multiple-value-bind (code slot gen) (fn2-core-reserve 0 1 0 1 core)
      (assert (eq code :ok))
      (loop for i from 0 for b in '(65 66 13 10)
            do (assert (eq (fn2-core-write slot gen i b 1 0 1 core) :ok)))
      (fn2-own-hook-reset)
      (multiple-value-bind (code at) (fn2-core-scan slot gen 0 4 *fn2-pool-scan-crlf* 1 0 1 core)
        (assert (and (eq code :ok) (= at 2) (= (gethash 1 *fn2-own-hook-reads* 0) 4)
                     (eq (fn2-own-status own) :pass))))
      (let* ((pool (fn2-core-pool core)) (base (fn2-pool-base slot pool)))
        (update-fn2-own-input-bytesi base 65 own)
        (update-fn2-own-input-statei base 2 own)
        (update-fn2-own-input-geni base gen own)
        (fn2-core-scan slot gen 0 4 *fn2-pool-scan-crlf* 1 0 1 core)
        (assert (eq (fn2-own-status own) :pass))
        (update-fn2-pool-datai base 90 pool)
        (fn2-core-scan slot gen 0 4 *fn2-pool-scan-crlf* 1 0 1 core)
        (assert (equal (fn2-own-status own) '(:fail :input-byte-mismatch)))
        (update-fn2-own-error 0 own)
        (multiple-value-bind (code next) (fn2-core-drop-prefix slot gen 0 0 4 1 0 1 core)
          (declare (ignore next))
          (assert (and (eq code :ok) (equal (fn2-own-status own) '(:fail :input-byte-mismatch)))))
        (update-fn2-own-error 0 own)
        (update-fn2-own-input-statei base 0 own)
        (multiple-value-bind (code next) (fn2-core-drop-prefix slot gen 1 0 4 1 0 1 core)
          (assert (and (eq code :ok) (= next 3) (eq (fn2-own-status own) :pass)))))))
  (format t "OWN RANGE HOOK CONTROLS scan-counted=PASS received=PASS scan-mismatch=REJECTED drop-mismatch=REJECTED drop-legal=PASS~%")
  (fn2-own-hook-reset))
