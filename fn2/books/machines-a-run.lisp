; Layer A continuations. Each run emits at most one descriptor; echo lends
; the exact RX bytes and waits for every borrow before resetting its window.
(in-package "ACL2")
(include-book "machines-a-access")
(include-book "machines-a-scribe")

(defmacro fn2-machine-a-events ()
 '(progn
(defun fn2-machine-dec (n)
  (declare (xargs :guard (natp n)))
  (if (zp n) 0 (- n 1)))

 ; One credit per unretired row, held from successful Accept issue through
; admission and echo reclamation. Failed Accept/admission returns its credit.
; Thus free rows = credits + outstanding admission reservations. Only listener
; admission removes a free row; retirement never returns a credit.
(defun fn2-listener-return-credit (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (fn2-machine-set-admission-credits
    (+ 1 (fn2-machine-admission-credits fn2-core)) fn2-core))
(fn2-machine-core-shape fn2-listener-return-credit ())

(defun fn2-machine-observe-terminal (id fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (fn2-machine-write-pending id (fn2-machine-dec (fn2-machine-pending id fn2-core)) fn2-core))
(fn2-machine-core-shape fn2-machine-observe-terminal (id))

; Handlers own their storage policy; generic routing never overwrites a
; machine event cell before its handler has consumed the completion.
(defmachine-callback fn2-listener-observe-accept fn2-listener (id event outcome reason count aux0 aux1) 1
  (let ((fn2-core
         (if (equal outcome *fn2-outcome-done*)
             (fn2-listener-put-core id (cap-index aux0) (cap-nonce aux1) (event-ready 1))
           (let ((fn2-core (fn2-listener-return-credit fn2-core)))
             (fn2-listener-put-core id (event-ready 0))))))
    (mv id fn2-core)))

(defmachine-callback fn2-echo-observe-receive fn2-echo (id event outcome reason count aux0 aux1) 1
  (let ((fn2-core
         (if (and (or (equal outcome *fn2-outcome-done*) (equal outcome *fn2-outcome-short*))
                  (unsigned-byte-p 32 count) (< 0 count))
             (fn2-echo-put-core id (length count) (off 0) (phase *fn2-echo-state-reply*))
           (fn2-echo-put-core id (phase *fn2-echo-state-closing*)))))
    (mv id fn2-core)))

(defmachine-callback fn2-echo-observe-send fn2-echo (id event outcome reason count aux0 aux1) 1
  (let* ((off row-off) (len row-length)
         (fn2-core (fn2-echo-put-core id (borrows (fn2-machine-pool-borrows row-pool-slot fn2-core))))
         (fn2-core
          (if (and (or (equal outcome *fn2-outcome-done*) (equal outcome *fn2-outcome-short*))
                   (natp count) (<= (+ off count) len))
              (fn2-echo-put-core id (off (+ off count)))
            (fn2-echo-put-core id (phase *fn2-echo-state-closing*)))))
    (mv id fn2-core)))

(defmachine-callback fn2-scribe-observe fn2-scribe (id event outcome reason count aux0 aux1) 1
  (let ((fn2-core (fn2-scribe-put-core id (event event) (outcome outcome) (count count)
                   (aux0 aux0) (aux1 aux1) (event-ready 1))))
    (mv id fn2-core)))

(defun fn2-machine-refuse-observation (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (let ((fn2-core (fn2-core-stop *fn2-stop-reason-machine-observation* fn2-core)))
    (mv 4294967295 fn2-core)))
(fn2-core-shape-lemmas fn2-machine-refuse-observation () 1)

(defmachine-callback fn2-listener-observe-close fn2-listener (id event outcome reason count aux0 aux1) 1
  (let ((fn2-core (fn2-listener-put-core id (phase *fn2-listener-state-accepting*) (event-ready 0))))
    (mv id fn2-core)))
(defmachine-callback fn2-echo-observe-close fn2-echo (id event outcome reason count aux0 aux1) 1
  (let ((fn2-core (fn2-echo-put-core id (phase *fn2-echo-state-draining*)))) (mv id fn2-core)))
(defmachine-callback fn2-echo-observe-release fn2-echo (id event outcome reason count aux0 aux1) 1
  (let ((fn2-core (fn2-echo-put-core id
                    (borrows (fn2-machine-pool-borrows row-pool-slot fn2-core)))))
    (mv id fn2-core)))


(defun fn2-machine-issue-result (id code bytes fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (natp bytes) (<= bytes 4096))))
  (if (eq code :ok)
      (let ((fn2-core (fn2-machine-put id (pending 1) (wait-reason 1))))
        (fn2-machine-result bytes 8 1 nil fn2-core))
    (if (eq code :exhausted)
        (let ((fn2-core (fn2-machine-park id fn2-core)))
          (fn2-machine-result 0 8 0 nil fn2-core))
      ; TODO R6-NONEXHAUSTION-REFUSAL: replace this retained stop with the
      ; named close/release or evidence posture chosen by R6.
      (let ((fn2-core (fn2-machine-put id (stopped 1) (wait-reason 0))))
        (fn2-machine-result 0 8 0 nil fn2-core)))))
(fn2-core-shape-lemmas fn2-machine-issue-result (id code bytes) 4)

(defmachine-callback fn2-listener-admit fn2-listener (id budget) 4
  (fn2-machine-with-work 0 24 0
  (b* ((target (fn2-machine-free-head fn2-core))
       ((mv gen next) (fn2-echo-free-fields target fn2-core))
       (kind *fn2-echo-kind*))
    (if (or (equal target 4294967295)
            (>= (fn2-machine-active-count fn2-core) (fn2-machine-connection-count fn2-core)))
        (let* ((fn2-core (fn2-listener-return-credit fn2-core))
               (fn2-core (fn2-listener-put-core id (phase *fn2-listener-state-closing*))))
          (fn2-machine-result 0 4 0 t fn2-core))
      (mv-let (code slot poolgen fn2-core)
        (fn2-core-reserve 0 kind target gen fn2-core)
        (if (not (eq code :ok))
            (let* ((fn2-core (fn2-listener-return-credit fn2-core))
               (fn2-core (fn2-listener-put-core id (phase *fn2-listener-state-closing*))))
              (fn2-machine-result 0 6 0 t fn2-core))
          (let* ((index row-cap-index)
                 (nonce row-cap-nonce)
                 (fn2-core (fn2-machine-set-free-head next fn2-core))
                 (fn2-core (fn2-machine-set-active-count
                             (+ 1 (fn2-machine-active-count fn2-core)) fn2-core))
                 (fn2-core (fn2-echo-put-core target
                             (phase *fn2-echo-state-command*) (cap-index index) (cap-nonce nonce)
                             (pool-slot slot) (pool-gen poolgen) (off 0) (length 0)
                             (pending 0) (borrows 0) (wait-reason 0)
                             (mode row-mode)))
                 (fn2-core (fn2-listener-put-core id (event-ready 0)))
                 (fn2-core (fn2-machine-set-wake-id target fn2-core)))
            (fn2-machine-result 0 24 0 t fn2-core))))))))


(defmachine-callback fn2-listener-step fn2-listener (id budget) 4
  (fn2-machine-with-work 0 24 1
  (cond ((not (equal row-pending 0))
         (fn2-machine-result 0 1 0 nil fn2-core))
        ((and (equal row-phase *fn2-listener-state-accepting*) (equal row-event-ready 1))
         (fn2-listener-admit id budget row-phase row-generation row-principal-slot row-account-ref row-ready-prev row-ready-next row-wait-reason row-deadline row-cap-index row-cap-nonce row-pending row-stopped row-event-ready row-mode fn2-core))
        ; Park separately from op waiters so the adapter can make progress.
        ((and (equal row-phase *fn2-listener-state-accepting*)
              (zp (fn2-machine-admission-credits fn2-core)))
         (let ((fn2-core (fn2-machine-park-admission id fn2-core)))
           (fn2-machine-result 0 8 0 nil fn2-core)))
        ((not (and (natp budget) (< 0 budget))) (fn2-machine-result 0 1 0 t fn2-core))
        (t
         (mv-let (code op opgen fn2-core)
           (if (equal row-phase *fn2-listener-state-accepting*)
               (fn2-issue-accept 0 0 *fn2-listener-kind* id row-generation 0 fn2-core)
             (fn2-issue-close row-cap-index
               row-cap-nonce *fn2-listener-kind* id
               row-generation 0 fn2-core))
           (declare (ignore op opgen))
           (let ((fn2-core
                  (if (and (eq code :ok) (equal row-phase *fn2-listener-state-accepting*))
                      (fn2-machine-set-admission-credits
                        (fn2-machine-dec (fn2-machine-admission-credits fn2-core)) fn2-core)
                    fn2-core)))
             (fn2-machine-issue-result id code 0 fn2-core)))))))


(defmachine-callback fn2-connection-release fn2-echo (id budget) 4
  (let* ((kind *fn2-echo-kind*)
         (gen row-generation))
    (mv-let (code fn2-core)
      (fn2-core-release row-pool-slot
        row-pool-gen kind id gen fn2-core)
      (if (not (or (eq code :ok) (eq code :retired)))
          (let ((fn2-core (fn2-core-stop *fn2-stop-reason-pool-release* fn2-core)))
            (fn2-machine-result 0 4 0 nil fn2-core))
        (let* ((next (fn2-machine-free-head fn2-core))
               (retire (>= gen (fn2-machine-gen-limit fn2-core)))
               (fn2-core (fn2-echo-put-core id
                           (phase (if retire *fn2-echo-state-retired* *fn2-echo-state-free*))
                           (generation (if retire gen (+ 1 gen)))
                           (pool-slot 4294967295) (pool-gen 0)
                           (cap-index 0) (cap-nonce 0) (off 0) (length 0)
                           (next-free next) (wait-reason 0)))
               (fn2-core (if retire fn2-core (fn2-machine-set-free-head id fn2-core)))
               (fn2-core (if retire fn2-core (fn2-listener-return-credit fn2-core)))
               (fn2-core (fn2-machine-set-active-count
                           (fn2-machine-dec (fn2-machine-active-count fn2-core)) fn2-core)))
          (fn2-machine-result 0 20 0 nil fn2-core))))))


(defmachine-callback fn2-connection-reset fn2-echo (id budget) 4
  (mv-let (code fn2-core)
    (fn2-core-reset row-pool-slot
      row-pool-gen *fn2-echo-kind* id
      row-generation fn2-core)
    (let ((fn2-core (fn2-echo-put-core id
                      (phase (if (eq code :ok) *fn2-echo-state-command* *fn2-echo-state-closing*)) (off 0) (length 0))))
      (fn2-machine-result 0 8 0 t fn2-core))))


(defmachine-callback fn2-connection-issue fn2-echo (id budget) 4
  (fn2-machine-with-work 4096 8 1
  (let* ((kind *fn2-echo-kind*)
         (gen row-generation)
         (principal row-principal-slot)
         (index row-cap-index)
         (nonce row-cap-nonce)
         (slot row-pool-slot)
         (poolgen row-pool-gen))
    (mv-let (code op opgen fn2-core)
      (cond ((equal row-phase *fn2-echo-state-command*)
             (fn2-issue-receive index nonce slot poolgen
               (min 4096 (fn2-machine-pool-capacity slot fn2-core))
               kind id gen principal fn2-core))
            ((equal row-phase *fn2-echo-state-reply*)
             (let ((off row-off)
                   (len row-length))
               (fn2-issue-send index nonce slot poolgen off (min 4096 (nfix (- len off))) 1
                 kind id gen principal fn2-core)))
            (t (fn2-issue-close index nonce kind id gen principal fn2-core)))
      (declare (ignore op opgen))
      (let ((fn2-core (if (and (eq code :ok) (equal row-phase *fn2-echo-state-reply*))
                          (fn2-echo-put-core id (borrows 1)) fn2-core)))
        (fn2-machine-issue-result id code
          (cond ((equal row-phase *fn2-echo-state-command*)
                 (min 4096 (fn2-machine-pool-capacity slot fn2-core)))
                ((equal row-phase *fn2-echo-state-reply*)
                 (min 4096 (nfix (- row-length
                                   row-off)))) (t 0)) fn2-core))))))


(defmachine-callback fn2-connection-submit fn2-echo (id budget) 4
  (cond ((not (equal row-pending 0))
         (fn2-machine-result 0 1 0 nil fn2-core))
        ((not (and (natp budget) (< 0 budget))) (fn2-machine-result 0 2 0 t fn2-core))
        (t (fn2-connection-issue id budget row-phase row-generation row-principal-slot row-account-ref row-ready-prev row-ready-next row-wait-reason row-deadline row-cap-index row-cap-nonce row-pool-slot row-pool-gen row-off row-length row-pending row-borrows row-next-free row-stopped row-mode fn2-core))))

(defmachine-callback fn2-connection-reply fn2-echo (id budget) 4
  (cond ((not (equal row-pending 0))
         (fn2-machine-result 0 1 0 nil fn2-core))
        ((not (equal row-borrows 0))
         (fn2-machine-result 0 2 0 nil fn2-core))
        ((or (equal row-mode 0)
             (>= row-off row-length))
         (fn2-connection-reset id budget row-phase row-generation row-principal-slot row-account-ref row-ready-prev row-ready-next row-wait-reason row-deadline row-cap-index row-cap-nonce row-pool-slot row-pool-gen row-off row-length row-pending row-borrows row-next-free row-stopped row-mode fn2-core))
        (t (fn2-connection-submit id budget row-phase row-generation row-principal-slot row-account-ref row-ready-prev row-ready-next row-wait-reason row-deadline row-cap-index row-cap-nonce row-pool-slot row-pool-gen row-off row-length row-pending row-borrows row-next-free row-stopped row-mode fn2-core))))

(defmachine-callback fn2-connection-drain fn2-echo (id budget) 4
  (cond ((not (equal row-pending 0))
         (fn2-machine-result 0 1 0 nil fn2-core))
        ((equal row-borrows 0) (fn2-connection-release id budget row-phase row-generation row-principal-slot row-account-ref row-ready-prev row-ready-next row-wait-reason row-deadline row-cap-index row-cap-nonce row-pool-slot row-pool-gen row-off row-length row-pending row-borrows row-next-free row-stopped row-mode fn2-core))
        (t (fn2-machine-result 0 2 0 nil fn2-core))))


(defmachine-callback fn2-connection-idle fn2-echo (id budget) 4
  (fn2-machine-idle id fn2-core))

(defmachine-run fn2-listener)

(defmachine-run fn2-echo)

))
