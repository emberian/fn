; Layer A continuations. Each run emits at most one descriptor; echo lends
; the exact RX bytes and waits for every borrow before resetting its window.
(in-package "ACL2")
(include-book "machines-a-access")
(include-book "machines-a-scribe")

(defmacro fn2-machine-a-events ()
 '(progn
; One credit per unretired row, held from successful Accept issue through
; admission and echo reclamation. Failed Accept/admission returns its credit.
; Thus free rows = credits + outstanding admission reservations. Only listener
; admission removes a free row; retirement never returns a credit.
(fn2-defoperation (:operation-set fn2-machine-resources) :callbacks :infer
(defun fn2-listener-return-credit (ord fn2-core)
  ; ORD is a listener's target ordinal; one outside the admitted kinds stops.
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (not (and (natp ord) (< ord *fn2-machine-admitted-max*))) (fn2-machine-refuse-write fn2-core)
    (fn2-machine-set-admission-credits ord
      (+ 1 (fn2-machine-admission-credits ord fn2-core)) fn2-core))))
(fn2-core-preserves fn2-listener-return-credit (ord fn2-core) :rows nil :prefix "")
(fn2-defoperation (:operation-set fn2-machine-resources) :callbacks :infer
(defun fn2-listener-take-credit (ord fn2-core)
  ; ORD is a listener's target ordinal; one outside the admitted kinds stops.
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  ; Taking a credit the partition does not hold is a caller's bug: stop
  ; before the field changes, never a count clamped at zero.
  (if (or (not (and (natp ord) (< ord *fn2-machine-admitted-max*)))
          (zp (fn2-machine-admission-credits ord fn2-core)))
      (fn2-machine-refuse-write fn2-core)
    (fn2-machine-set-admission-credits ord
      (- (fn2-machine-admission-credits ord fn2-core) 1) fn2-core))))
(fn2-core-preserves fn2-listener-take-credit (ord fn2-core) :rows nil :prefix "")

(defun fn2-machine-observe-terminal (id fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  ; A terminal for a row with nothing pending is a caller's bug: stop.
  (if (and (eq (fn2-machine-pending-read-code id fn2-core) :ok)
           (not (zp (fn2-machine-pending id fn2-core))))
      (fn2-machine-write-pending id (- (fn2-machine-pending id fn2-core) 1) fn2-core)
    (fn2-machine-refuse-write fn2-core)))
(fn2-core-preserves fn2-machine-observe-terminal (id fn2-core) :rows nil :prefix "")

; Handlers own their storage policy; generic routing never overwrites a
; machine event cell before its handler has consumed the completion.
(defmachine-callback fn2-listener-observe-accept fn2-listener (id event outcome reason count aux0 aux1) 1
  ; A failed Accept returns the row credit and releases the booking (D7's S1).
  (let ((target row-target) (ref row-account-ref))
    (if (equal outcome *fn2-outcome-done*)
        (mv-let (family port w0 w1 w2 w3) (fn2-core-observed-peer fn2-core)
          (let ((fn2-core (fn2-listener-put-core id (cap-index aux0) (cap-nonce aux1)
                            (peer-family family) (peer-port port) (peer-w0 w0) (peer-w1 w1)
                            (peer-w2 w2) (peer-w3 w3) (event-ready 1))))
            (mv id fn2-core)))
      (let ((fn2-core (fn2-listener-return-credit target fn2-core)))
        (mv-let (ucode fn2-core) (fn2-account-unbook-ref ref fn2-core)
          (declare (ignore ucode))
          (let ((fn2-core (fn2-listener-put-core id (phase *fn2-listener-state-accepting*) (event-ready 0)
                                                 (account-ref *fn2-none*))))
            (mv id fn2-core)))))))

(defmachine-callback fn2-echo-observe-receive fn2-echo (id event outcome reason count aux0 aux1) 1
  (let ((fn2-core
         (if (and (or (equal outcome *fn2-outcome-done*) (equal outcome *fn2-outcome-short*))
                  (unsigned-byte-p 32 count) (< 0 count))
             (fn2-echo-put-core id (length count) (off 0) (phase *fn2-echo-state-reply*))
           (fn2-echo-put-core id (phase *fn2-echo-state-closing*)))))
    (mv id fn2-core)))

(defmachine-callback fn2-echo-observe-send fn2-echo (id event outcome reason count aux0 aux1) 1
  (if (not (eq (fn2-machine-pool-borrows-read-code row-pool-slot fn2-core) :ok))
      (let ((fn2-core (fn2-core-stop *fn2-stop-reason-machine-observation* fn2-core)))
        (mv *fn2-none* fn2-core))
  (let* ((off row-off) (len row-length)
         (fn2-core (fn2-echo-put-core id (borrows (fn2-machine-pool-borrows row-pool-slot fn2-core))))
         (fn2-core
          (if (and (or (equal outcome *fn2-outcome-done*) (equal outcome *fn2-outcome-short*))
                   (natp count) (<= (+ off count) len))
              (fn2-echo-put-core id (off (+ off count)))
            (fn2-echo-put-core id (phase *fn2-echo-state-closing*)))))
    (mv id fn2-core))))

(defmachine-callback fn2-scribe-observe fn2-scribe (id event outcome reason count aux0 aux1) 1
  (let ((fn2-core (fn2-scribe-put-core id (event event) (outcome outcome) (count count)
                   (aux0 aux0) (aux1 aux1) (event-ready 1))))
    (mv id fn2-core)))

(defun fn2-machine-refuse-observation (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (let ((fn2-core (fn2-core-stop *fn2-stop-reason-machine-observation* fn2-core)))
    (mv *fn2-none* fn2-core)))
(fn2-core-preserves fn2-machine-refuse-observation (fn2-core) :position 1 :rows nil)

(defmachine-callback fn2-listener-observe-close fn2-listener (id event outcome reason count aux0 aux1) 1
  (let ((fn2-core (fn2-listener-put-core id (phase *fn2-listener-state-accepting*) (event-ready 0))))
    (mv id fn2-core)))
(defmachine-callback fn2-echo-observe-close fn2-echo (id event outcome reason count aux0 aux1) 1
  (let ((fn2-core (fn2-echo-put-core id (phase *fn2-echo-state-draining*)))) (mv id fn2-core)))
(defmachine-callback fn2-echo-observe-release fn2-echo (id event outcome reason count aux0 aux1) 1
  (if (not (eq (fn2-machine-pool-borrows-read-code row-pool-slot fn2-core) :ok))
      (fn2-machine-refuse-observation fn2-core)
  (let ((fn2-core (fn2-echo-put-core id
                    (borrows (fn2-machine-pool-borrows row-pool-slot fn2-core)))))
    (mv id fn2-core))))


(defun fn2-machine-issue-result (id code bytes fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (natp bytes) (<= bytes *fn2-echo-run-bytes*))))
  (if (eq code :ok)
      (let ((fn2-core (fn2-machine-put id (pending 1) (wait-reason *fn2-wait-completion*))))
        (fn2-machine-result bytes *fn2-work-mailbox* 1 nil fn2-core))
    (if (eq code :exhausted)
        (let ((fn2-core (fn2-machine-park id fn2-core)))
          (fn2-machine-result 0 *fn2-work-mailbox* 0 nil fn2-core))
      ; TODO R6-NONEXHAUSTION-REFUSAL: replace this retained stop with the
      ; named close/release or evidence posture chosen by R6.
      (let ((fn2-core (fn2-machine-put id (stopped 1) (wait-reason *fn2-wait-none*))))
        (fn2-machine-result 0 *fn2-work-mailbox* 0 nil fn2-core)))))
(fn2-core-preserves fn2-machine-issue-result (id code bytes fn2-core) :position 4 :rows nil)

; The listener reads its own row once, before any write.
(defmachine-callback fn2-listener-admit fn2-listener (id budget) 4
  :contract (:cost (:steps *fn2-work-transition*) :writes (event-ready account-ref)
             :tables (fn2-core-machines fn2-core-pool fn2-core-machine-tables fn2-core-accounts) :next (:accepting :closing)
             :uses (fn2-machine-admit fn2-listener-return-credit fn2-account-unbook-ref))
  (fn2-machine-with-work 0 *fn2-work-transition* 0
  (b* ((target row-target)
       (index row-cap-index)
       (nonce row-cap-nonce)
       (mode row-mode)
       (principal row-principal-slot)
       (ref row-account-ref)
       (family row-peer-family) (port row-peer-port)
       (w0 row-peer-w0) (w1 row-peer-w1) (w2 row-peer-w2) (w3 row-peer-w3))
    ; The admitted row copies the listener's principal, its booking and the
    ; Accept's peer record (layer doc 4.1.1), the fields its :copy names.
    (mv-let (code fn2-core) (fn2-machine-admit target index nonce mode principal ref
                                               family port w0 w1 w2 w3 fn2-core)
      (if (eq code :ok)
          (let ((fn2-core (fn2-listener-put-core id (phase *fn2-listener-state-accepting*) (event-ready 0)
                            (account-ref *fn2-none*))))
            (fn2-machine-result 0 *fn2-work-transition* 0 t fn2-core))
        (let ((fn2-core (fn2-listener-return-credit target fn2-core)))
          (mv-let (ucode fn2-core) (fn2-account-unbook-ref ref fn2-core)
            (declare (ignore ucode))
            (let ((fn2-core (fn2-listener-put-core id (phase *fn2-listener-state-closing*)
                              (account-ref *fn2-none*))))
              (fn2-machine-result 0 (if (eq code :no-row) *fn2-work-state* *fn2-work-refusal*) 0 t
                                  fn2-core)))))))))

; :accepting holds only the accept credit. A successful Accept issue takes
; one row credit (the reservation the admission will spend) and moves to
; :admitting; without a credit the listener parks on the admission FIFO.
(defmachine-callback fn2-listener-accept fn2-listener (id budget) 4
  (fn2-machine-with-work 0 *fn2-work-transition* 1
  (cond ((not (equal row-pending 0))
         (fn2-machine-result 0 *fn2-work-empty* 0 nil fn2-core))
        ((not (< row-target *fn2-machine-admitted-max*)) (fn2-machine-refuse-phase id fn2-core))
        ((zp (fn2-machine-admission-credits row-target fn2-core))
         (let ((fn2-core (fn2-machine-park-admission id row-target fn2-core)))
           (fn2-machine-result 0 *fn2-work-mailbox* 0 nil fn2-core)))
        ((not (and (natp budget) (< 0 budget))) (fn2-machine-result 0 *fn2-work-empty* 0 t fn2-core))
        (t
         ; D7's S1: for a target that carries a booking, the listener books
         ; its principal's :connection-row before the Accept issue. A refused
         ; booking (:limit, :shared) admits the connection unbooked (its
         ; greeting is the capacity 400); a ledger failure stops the core.
         (b* ((principal row-principal-slot)
              (target row-target)
              ((mv bcode fn2-core)
               (if (fn2-machine-admission-books-p target) (fn2-account-book principal fn2-core)
                 (mv :limit fn2-core))))
           (if (not (or (eq bcode :ok) (eq bcode :limit) (eq bcode :shared)))
               (let ((fn2-core (fn2-core-stop *fn2-stop-reason-account* fn2-core)))
                 (fn2-machine-result 0 *fn2-work-mailbox* 0 nil fn2-core))
             (mv-let (code op opgen fn2-core)
               (fn2-issue-accept 0 0 *fn2-listener-kind* id row-generation 0 fn2-core)
               (declare (ignore op opgen))
               (if (eq code :ok)
                   (let* ((fn2-core (fn2-listener-take-credit target fn2-core))
                          (fn2-core (fn2-listener-put-core id (phase *fn2-listener-state-admitting*)
                                      (account-ref (if (eq bcode :ok) principal *fn2-none*)))))
                     (fn2-machine-issue-result id code 0 fn2-core))
                 (mv-let (ucode fn2-core)
                   (fn2-account-unbook-ref (if (eq bcode :ok) principal *fn2-none*) fn2-core)
                   (declare (ignore ucode))
                   (fn2-machine-issue-result id code 0 fn2-core))))))))))

; :admitting holds the accept credit and one reserved row credit, with the
; Accept pending or its capability ready. Reached without either, the row is
; inconsistent: the run stops rather than parking forever.
(defmachine-callback fn2-listener-admitting fn2-listener (id budget) 4
  (cond ((not (equal row-pending 0))
         (fn2-machine-result 0 *fn2-work-empty* 0 nil fn2-core))
        ((equal row-event-ready 1) (fn2-call fn2-listener-admit id budget))
        (t (fn2-machine-refuse-phase id fn2-core))))

; :closing closes a capability whose admission was refused.
(defmachine-callback fn2-listener-close fn2-listener (id budget) 4
  (fn2-machine-with-work 0 *fn2-work-transition* 1
  (cond ((not (equal row-pending 0))
         (fn2-machine-result 0 *fn2-work-empty* 0 nil fn2-core))
        ((not (and (natp budget) (< 0 budget))) (fn2-machine-result 0 *fn2-work-empty* 0 t fn2-core))
        (t
         (mv-let (code op opgen fn2-core)
           (fn2-issue-close row-cap-index row-cap-nonce *fn2-listener-kind* id row-generation 0 fn2-core)
           (declare (ignore op opgen))
           (fn2-machine-issue-result id code 0 fn2-core))))))


(defmachine-callback fn2-connection-release fn2-echo (id budget) 4
  :contract (:cost (:steps *fn2-work-release*)
             :writes (generation pool-slot pool-gen cap-index cap-nonce off length next-free wait-reason)
             :tables (fn2-core-pool fn2-core-machines) :next (:free :retired)
             :uses ((fn2-core-release :effects ((:release (:rx-range)))) fn2-machine-gen-limit
                    fn2-machine-free-head fn2-machine-reclaim-fn2-echo fn2-core-stop))
  (let* ((kind *fn2-echo-kind*)
         (gen row-generation)
         (slot row-pool-slot)
         (pool-gen row-pool-gen))
    (mv-let (code fn2-core)
      (fn2-core-release slot pool-gen kind id gen fn2-core)
      (if (not (or (eq code :ok) (eq code :retired)))
          (let ((fn2-core (fn2-core-stop *fn2-stop-reason-pool-release* fn2-core)))
            (fn2-machine-result 0 *fn2-work-state* 0 nil fn2-core))
        (let* ((next (fn2-machine-free-head *fn2-echo-admission-ordinal* fn2-core))
               (retire (>= gen (fn2-machine-gen-limit fn2-core)))
               (fn2-core (fn2-echo-put-core id
                           (phase (if retire *fn2-echo-state-retired* *fn2-echo-state-free*))
                           (generation (if retire gen (+ 1 gen)))
                           (pool-slot *fn2-none*) (pool-gen 0)
                           (cap-index 0) (cap-nonce 0) (off 0) (length 0)
                           (next-free next) (wait-reason *fn2-wait-none*)))
               (fn2-core (fn2-machine-reclaim-fn2-echo id retire fn2-core)))
          (fn2-machine-result 0 *fn2-work-release* 0 nil fn2-core))))))


(defmachine-callback fn2-connection-reset fn2-echo (id budget) 4
  :contract (:cost (:steps *fn2-work-mailbox*) :writes (off length) :tables (fn2-core-pool)
             :next (:command :closing) :uses (fn2-core-reset))
  (mv-let (code fn2-core)
    (fn2-core-reset row-pool-slot
      row-pool-gen *fn2-echo-kind* id
      row-generation fn2-core)
    (let ((fn2-core (fn2-echo-put-core id
                      (phase (if (eq code :ok) *fn2-echo-state-command* *fn2-echo-state-closing*)) (off 0) (length 0))))
      (fn2-machine-result 0 *fn2-work-mailbox* 0 t fn2-core))))


(defmachine-callback fn2-connection-issue fn2-echo (id budget) 4
  :contract (:cost (:bytes *fn2-echo-run-bytes* :steps *fn2-work-mailbox* :descriptors 1)
             :writes (borrows pending stopped wait-reason ready-prev ready-next)
             :tables (fn2-core-ops fn2-core-pool fn2-core-machines fn2-core-machine-tables) :next ()
             :uses (fn2-machine-pool-capacity-read-code fn2-machine-pool-capacity fn2-machine-refuse-phase
                    fn2-issue-receive fn2-issue-send fn2-issue-close fn2-machine-issue-result))
  (fn2-machine-with-work *fn2-echo-run-bytes* *fn2-work-mailbox* 1
  (let* ((kind *fn2-echo-kind*)
         (gen row-generation)
         (principal row-principal-slot)
         (index row-cap-index)
         (nonce row-cap-nonce)
         (slot row-pool-slot)
         (poolgen row-pool-gen))
    (if (and (equal row-phase *fn2-echo-state-command*)
             (not (eq (fn2-machine-pool-capacity-read-code slot fn2-core) :ok)))
        (fn2-machine-refuse-phase id fn2-core)
      (let ((capacity (if (equal row-phase *fn2-echo-state-command*)
                          (min *fn2-echo-run-bytes* (fn2-machine-pool-capacity slot fn2-core)) 0)))
    (mv-let (code op opgen fn2-core)
      (cond ((equal row-phase *fn2-echo-state-command*)
             (fn2-issue-receive index nonce slot poolgen
               capacity
               kind id gen principal fn2-core))
            ((equal row-phase *fn2-echo-state-reply*)
             (let ((off row-off)
                   (len row-length))
               (fn2-issue-send index nonce slot poolgen off (min *fn2-echo-run-bytes* (nfix (- len off))) 1
                 kind id gen principal fn2-core)))
            (t (fn2-issue-close index nonce kind id gen principal fn2-core)))
      (declare (ignore op opgen))
      (let ((fn2-core (if (and (eq code :ok) (equal row-phase *fn2-echo-state-reply*))
                          (fn2-echo-put-core id (borrows 1)) fn2-core)))
        (fn2-machine-issue-result id code
          (cond ((equal row-phase *fn2-echo-state-command*)
                 capacity)
                ((equal row-phase *fn2-echo-state-reply*)
                 (min *fn2-echo-run-bytes* (nfix (- row-length
                                   row-off)))) (t 0)) fn2-core))))))))


(defmachine-callback fn2-connection-submit fn2-echo (id budget) 4
  (cond ((not (equal row-pending 0))
         (fn2-machine-result 0 *fn2-work-empty* 0 nil fn2-core))
        ((not (and (natp budget) (< 0 budget))) (fn2-machine-result 0 *fn2-work-poll* 0 t fn2-core))
        (t (fn2-call fn2-connection-issue id budget))))

(defmachine-callback fn2-connection-reply fn2-echo (id budget) 4
  (cond ((not (equal row-pending 0))
         (fn2-machine-result 0 *fn2-work-empty* 0 nil fn2-core))
        ((not (equal row-borrows 0))
         (fn2-machine-result 0 *fn2-work-poll* 0 nil fn2-core))
        ((or (equal row-mode 0)
             (>= row-off row-length))
         (fn2-call fn2-connection-reset id budget))
        (t (fn2-call fn2-connection-submit id budget))))

(defmachine-callback fn2-connection-drain fn2-echo (id budget) 4
  (cond ((not (equal row-pending 0))
         (fn2-machine-result 0 *fn2-work-empty* 0 nil fn2-core))
        ((equal row-borrows 0) (fn2-call fn2-connection-release id budget))
        (t (fn2-machine-result 0 *fn2-work-poll* 0 nil fn2-core))))


(defmachine-callback fn2-connection-idle fn2-echo (id budget) 4
  (fn2-machine-idle id fn2-core))

(defmachine-run fn2-listener)

(defmachine-run fn2-echo)

))
