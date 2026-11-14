; Concrete handshake transport ledger. SSL hidden state is an external
; primitive contract, including on WANT/error; this table owns staging,
; observable byte spans and action sequencing, not cryptographic truth.
(in-package "ACL2")
(include-book "tls-kind")

(defcolumns fn2-tls-transport
 ((nonce :u60) (slot :u32) (generation :u60)
  (seed-total :u32) (seed-capacity :u32) (quantum :u32)
  (budget :u32) (serial :u32) (copied :u32) (fed :u32)
  (input-length :u32) (input-offset :u32)
  (output-length :u32) (output-offset :u32)
  ;; SSL status: 0 complete, 1 WANT_READ, 2 WANT_WRITE, 5 must-call.
  (ssl-status :u8) (terminal :u8)
  ;; Action: 0 none, 1 copy, 2 seed feed, 3 input feed, 4 drain,
  ;; 5 send, 6 recv, 7 handshake. All actions are bounded by quantum.
  (pending :u8) (offset :u32) (requested :u32)
  ;; Exact physical return before normalization. Signed code is represented
  ;; by sign + magnitude; raw errno/count never substitute for one another.
  (raw-negative :bool) (raw-code :u32) (raw-count :u32) (raw-errno :u32))
 :rows-bound 2)

(defun fn2-tls-transport-start (nonce slot generation total capacity quantum budget fn2-tls-transport)
 (declare (xargs :stobjs fn2-tls-transport :guard t :verify-guards nil))
 (if (not (and (unsigned-byte-p 60 nonce) (unsigned-byte-p 32 slot)
               (unsigned-byte-p 60 generation) (unsigned-byte-p 32 total)
               (unsigned-byte-p 32 capacity) (<= total capacity)
               (posp quantum) (unsigned-byte-p 32 quantum)
               (posp budget) (unsigned-byte-p 32 budget)))
     (mv :bounds fn2-tls-transport)
  (let ((fn2-tls-transport (fn2-tls-transport-init 1 fn2-tls-transport)))
   (let ((fn2-tls-transport (fn2-tls-transport-put 0 (nonce nonce) (slot slot)
     (generation generation) (seed-total total) (seed-capacity capacity)
     (quantum quantum) (budget budget) (ssl-status 5))))
 (mv :ok fn2-tls-transport)))))

(defun fn2-tls-transport-plan
 (total copied fed input-length input-offset output-length output-offset ssl room pending quantum)
 (declare (xargs :guard t))
 (if (not (and (unsigned-byte-p 32 total) (natp copied) (<= copied total)
               (natp fed) (<= fed copied)
               (unsigned-byte-p 32 input-length) (natp input-offset) (<= input-offset input-length)
               (unsigned-byte-p 32 output-length) (natp output-offset) (<= output-offset output-length)
               (unsigned-byte-p 32 room) (unsigned-byte-p 32 pending)
               (posp quantum) (unsigned-byte-p 32 quantum)))
     (mv :bounds 0 0 0)
  (cond
   ((< copied total) (mv :act 1 copied (min quantum (- total copied))))
   ((< output-offset output-length) (mv :act 5 output-offset (min quantum (- output-length output-offset))))
   ((< 0 pending) (mv :act 4 0 (min quantum pending)))
   ((equal ssl 0) (mv :done 0 0 0))
   ((and (< input-offset input-length) (< 0 room))
    (mv :act 3 input-offset (min quantum (min room (- input-length input-offset)))))
   ((and (< fed copied) (< 0 room))
    (mv :act 2 fed (min quantum (min room (- copied fed)))))
   ;; Attempt SSL before fd receive. It may already hold a complete record.
   ((or (not (equal ssl 1)) (< fed copied) (< input-offset input-length) (zp room))
    (mv :act 7 0 0))
   (t (mv :act 6 0 (min quantum room))))))

(defthm fn2-tls-transport-plan-quantum
 (implies (equal (mv-nth 0 (fn2-tls-transport-plan total copied fed il io ol oo ssl room pending quantum)) :act)
  (and (natp (mv-nth 3 (fn2-tls-transport-plan total copied fed il io ol oo ssl room pending quantum)))
       (<= (mv-nth 3 (fn2-tls-transport-plan total copied fed il io ol oo ssl room pending quantum)) quantum))))
(defthm fn2-tls-transport-plan-copy-bound
 (implies (and (equal (mv-nth 0 (fn2-tls-transport-plan total copied fed il io ol oo ssl room pending quantum)) :act)
               (equal (mv-nth 1 (fn2-tls-transport-plan total copied fed il io ol oo ssl room pending quantum)) 1))
  (<= (+ (mv-nth 2 (fn2-tls-transport-plan total copied fed il io ol oo ssl room pending quantum))
         (mv-nth 3 (fn2-tls-transport-plan total copied fed il io ol oo ssl room pending quantum))) total)))

(defun fn2-tls-transport-next (room pending fn2-tls-transport)
 (declare (xargs :stobjs fn2-tls-transport :verify-guards nil
  :guard (and (fn2-tls-transport-wfp fn2-tls-transport) (= (fn2-tls-transport-rows fn2-tls-transport) 1))))
 (cond
  ((not (equal (fn2-tls-transport-pending 0 fn2-tls-transport) 0)) (mv :pending 0 0 0 0 fn2-tls-transport))
  ((equal (fn2-tls-transport-terminal 0 fn2-tls-transport) 1) (mv :done 0 0 0 0 fn2-tls-transport))
  ((not (equal (fn2-tls-transport-terminal 0 fn2-tls-transport) 0)) (mv :failed 0 0 0 0 fn2-tls-transport))
  (t
   (mv-let (code action offset count)
    (fn2-tls-transport-plan
      (fn2-tls-transport-seed-total 0 fn2-tls-transport)
      (fn2-tls-transport-copied 0 fn2-tls-transport) (fn2-tls-transport-fed 0 fn2-tls-transport)
      (fn2-tls-transport-input-length 0 fn2-tls-transport) (fn2-tls-transport-input-offset 0 fn2-tls-transport)
      (fn2-tls-transport-output-length 0 fn2-tls-transport) (fn2-tls-transport-output-offset 0 fn2-tls-transport)
      (fn2-tls-transport-ssl-status 0 fn2-tls-transport) room pending
      (fn2-tls-transport-quantum 0 fn2-tls-transport))
    (cond
     ((eq code :done)
      (let ((fn2-tls-transport (fn2-tls-transport-put 0 (terminal 1))))
 (mv :done 0 0 0 0 fn2-tls-transport)))
     ((or (not (eq code :act)) (zp (fn2-tls-transport-budget 0 fn2-tls-transport))
          (= (fn2-tls-transport-serial 0 fn2-tls-transport) #xffffffff))
      (let ((fn2-tls-transport (fn2-tls-transport-put 0 (terminal 2))))
 (mv :failed 0 0 0 0 fn2-tls-transport)))
     (t
      (let ((serial (+ 1 (fn2-tls-transport-serial 0 fn2-tls-transport)))
            (budget (- (fn2-tls-transport-budget 0 fn2-tls-transport) 1)))
       (let ((fn2-tls-transport (fn2-tls-transport-put 0 (pending action) (offset offset) (requested count)
          (serial serial) (budget budget))))
 (mv :act action offset count serial
        fn2-tls-transport)))))))))

(defun fn2-tls-transport-observe (nonce slot generation serial code count errno fn2-tls-transport)
 (declare (xargs :stobjs fn2-tls-transport :verify-guards nil
  :guard (and (fn2-tls-transport-wfp fn2-tls-transport) (= (fn2-tls-transport-rows fn2-tls-transport) 1))))
 ;; Malformed/stale returns change neither the pending action nor its ledger.
 (if (not (and (equal nonce (fn2-tls-transport-nonce 0 fn2-tls-transport))
               (equal slot (fn2-tls-transport-slot 0 fn2-tls-transport))
               (equal generation (fn2-tls-transport-generation 0 fn2-tls-transport))
               (equal serial (fn2-tls-transport-serial 0 fn2-tls-transport))
               (< 0 (fn2-tls-transport-pending 0 fn2-tls-transport))
               (integerp code) (unsigned-byte-p 32 (abs code))
               (unsigned-byte-p 32 count) (unsigned-byte-p 32 errno)))
     (mv :stale nil fn2-tls-transport)
  (let* ((action (fn2-tls-transport-pending 0 fn2-tls-transport))
         (offset (fn2-tls-transport-offset 0 fn2-tls-transport))
         (requested (fn2-tls-transport-requested 0 fn2-tls-transport))
         (total (fn2-tls-transport-seed-total 0 fn2-tls-transport))
         (copied (fn2-tls-transport-copied 0 fn2-tls-transport))
         (il (fn2-tls-transport-input-length 0 fn2-tls-transport))
         (ol (fn2-tls-transport-output-length 0 fn2-tls-transport))
         (fn2-tls-transport (fn2-tls-transport-put 0
           (raw-negative (if (< code 0) 1 0)) (raw-code (abs code))
           (raw-count count) (raw-errno errno) (pending 0))))
   (cond
    ((equal action 7)
     (if (and (member-equal code '(0 1 2)) (= count 0))
         (let ((fn2-tls-transport (fn2-tls-transport-put 0 (ssl-status code))))
 (mv :ok t fn2-tls-transport))
       (let ((fn2-tls-transport (fn2-tls-transport-put 0 (terminal 2))))
 (mv :failed nil fn2-tls-transport))))
    ((and (member-equal action '(5 6)) (< code 0) (member-equal errno '(4 11 35)))
     (mv :blocked nil fn2-tls-transport))
    ((not (and (natp code) (<= code requested) (= count 0)
               (unsigned-byte-p 32 (+ offset code))
               (or (not (member-equal action '(1 5 6))) (< 0 code))))
     (let ((fn2-tls-transport (fn2-tls-transport-put 0 (terminal 2))))
 (mv :failed nil fn2-tls-transport)))
    ((equal action 1)
     (if (<= (+ offset code) total)
         (let ((fn2-tls-transport (fn2-tls-transport-put 0 (copied (+ offset code)))))
 (mv :ok t fn2-tls-transport))
       (let ((fn2-tls-transport (fn2-tls-transport-put 0 (terminal 2))))
 (mv :failed nil fn2-tls-transport))))
    ((equal action 2)
     (if (<= (+ offset code) copied)
         (let ((fn2-tls-transport (fn2-tls-transport-put 0 (fed (+ offset code)) (ssl-status 5))))
 (mv :ok t fn2-tls-transport))
       (let ((fn2-tls-transport (fn2-tls-transport-put 0 (terminal 2))))
 (mv :failed nil fn2-tls-transport))))
    ((equal action 3)
     (if (<= (+ offset code) il)
         (let ((fn2-tls-transport (fn2-tls-transport-put 0 (input-offset (+ offset code)) (ssl-status 5))))
 (mv :ok t fn2-tls-transport))
       (let ((fn2-tls-transport (fn2-tls-transport-put 0 (terminal 2))))
 (mv :failed nil fn2-tls-transport))))
    ((equal action 4) (let ((fn2-tls-transport (fn2-tls-transport-put 0 (output-length code) (output-offset 0))))
 (mv :ok t fn2-tls-transport)))
    ((equal action 5)
     (if (<= (+ offset code) ol)
         (let ((fn2-tls-transport (fn2-tls-transport-put 0 (output-offset (+ offset code)))))
 (mv :ok t fn2-tls-transport))
       (let ((fn2-tls-transport (fn2-tls-transport-put 0 (terminal 2))))
 (mv :failed nil fn2-tls-transport))))
    ((equal action 6) (let ((fn2-tls-transport (fn2-tls-transport-put 0 (input-length code) (input-offset 0))))
 (mv :ok t fn2-tls-transport)))
    (t (let ((fn2-tls-transport (fn2-tls-transport-put 0 (terminal 2))))
 (mv :failed nil fn2-tls-transport)))))))

(defun fn2-tls-transport-action-interest (action)
 (declare (xargs :guard t))
 (if (equal action 5) 4 1))

(defthm fn2-tls-transport-plan-widths
 (and (unsigned-byte-p 8 (mv-nth 1 (fn2-tls-transport-plan total copied fed il io ol oo ssl room pending quantum)))
      (unsigned-byte-p 32 (mv-nth 2 (fn2-tls-transport-plan total copied fed il io ol oo ssl room pending quantum)))
      (unsigned-byte-p 32 (mv-nth 3 (fn2-tls-transport-plan total copied fed il io ol oo ssl room pending quantum)))))
(verify-guards fn2-tls-transport-start)
(verify-guards fn2-tls-transport-next
 :hints (("Goal" :in-theory (disable fn2-tls-transport-rows fn2-tls-transport-plan
  fn2-tls-transport-nonce fn2-tls-transport-slot fn2-tls-transport-generation fn2-tls-transport-seed-total fn2-tls-transport-seed-capacity fn2-tls-transport-quantum fn2-tls-transport-budget fn2-tls-transport-serial fn2-tls-transport-copied fn2-tls-transport-fed fn2-tls-transport-input-length fn2-tls-transport-input-offset fn2-tls-transport-output-length fn2-tls-transport-output-offset fn2-tls-transport-ssl-status fn2-tls-transport-terminal fn2-tls-transport-pending fn2-tls-transport-offset fn2-tls-transport-requested fn2-tls-transport-raw-negative fn2-tls-transport-raw-code fn2-tls-transport-raw-count fn2-tls-transport-raw-errno))))
(verify-guards fn2-tls-transport-observe
 :hints (("Goal" :in-theory (disable fn2-tls-transport-rows fn2-tls-transport-nonce fn2-tls-transport-slot fn2-tls-transport-generation fn2-tls-transport-seed-total fn2-tls-transport-seed-capacity fn2-tls-transport-quantum fn2-tls-transport-budget fn2-tls-transport-serial fn2-tls-transport-copied fn2-tls-transport-fed fn2-tls-transport-input-length fn2-tls-transport-input-offset fn2-tls-transport-output-length fn2-tls-transport-output-offset fn2-tls-transport-ssl-status fn2-tls-transport-terminal fn2-tls-transport-pending fn2-tls-transport-offset fn2-tls-transport-requested fn2-tls-transport-raw-negative fn2-tls-transport-raw-code fn2-tls-transport-raw-count fn2-tls-transport-raw-errno))))

(defthm fn2-tls-transport-next-wfp
 (implies (and (fn2-tls-transportp fn2-tls-transport)
               (= (fn2-tls-transport-rows fn2-tls-transport) 1)
               (fn2-tls-transport-wfp fn2-tls-transport))
  (fn2-tls-transport-wfp (mv-nth 5 (fn2-tls-transport-next room pending fn2-tls-transport)))))
(defthm fn2-tls-transport-observe-wfp
 (implies (and (fn2-tls-transportp fn2-tls-transport)
               (= (fn2-tls-transport-rows fn2-tls-transport) 1)
               (fn2-tls-transport-wfp fn2-tls-transport))
  (fn2-tls-transport-wfp
   (mv-nth 2 (fn2-tls-transport-observe nonce slot generation serial code count errno fn2-tls-transport)))))

(defun fn2-tls-transport-pending-valid-p (action offset requested total copied fed il io ol oo quantum)
 (declare (xargs :guard t))
 (and (natp requested) (natp quantum) (<= requested quantum)
  (case action
   (0 t)
   (1 (and (equal offset copied) (<= (+ (nfix offset) requested) (nfix total))))
   (2 (and (equal offset fed) (<= (+ (nfix offset) requested) (nfix copied))))
   (3 (and (equal offset io) (<= (+ (nfix offset) requested) (nfix il))))
   (4 (equal offset 0))
   (5 (and (equal offset oo) (<= (+ (nfix offset) requested) (nfix ol))))
   (6 (and (equal offset 0) (equal io il)))
   (7 (and (equal offset 0) (equal requested 0)))
   (otherwise nil))))

(defun fn2-tls-transport-invariant (fn2-tls-transport)
 (declare (xargs :stobjs fn2-tls-transport
  :guard (and (fn2-tls-transport-wfp fn2-tls-transport) (= (fn2-tls-transport-rows fn2-tls-transport) 1))))
 (and (<= (fn2-tls-transport-seed-total 0 fn2-tls-transport) (fn2-tls-transport-seed-capacity 0 fn2-tls-transport))
      (<= (fn2-tls-transport-copied 0 fn2-tls-transport) (fn2-tls-transport-seed-total 0 fn2-tls-transport))
      (<= (fn2-tls-transport-fed 0 fn2-tls-transport) (fn2-tls-transport-copied 0 fn2-tls-transport))
      (<= (fn2-tls-transport-input-offset 0 fn2-tls-transport) (fn2-tls-transport-input-length 0 fn2-tls-transport))
      (<= (fn2-tls-transport-output-offset 0 fn2-tls-transport) (fn2-tls-transport-output-length 0 fn2-tls-transport))
      (<= (fn2-tls-transport-input-length 0 fn2-tls-transport) (fn2-tls-transport-quantum 0 fn2-tls-transport))
      (<= (fn2-tls-transport-output-length 0 fn2-tls-transport) (fn2-tls-transport-quantum 0 fn2-tls-transport))
      (fn2-tls-transport-pending-valid-p
       (fn2-tls-transport-pending 0 fn2-tls-transport) (fn2-tls-transport-offset 0 fn2-tls-transport)
       (fn2-tls-transport-requested 0 fn2-tls-transport)
       (fn2-tls-transport-seed-total 0 fn2-tls-transport) (fn2-tls-transport-copied 0 fn2-tls-transport)
       (fn2-tls-transport-fed 0 fn2-tls-transport)
       (fn2-tls-transport-input-length 0 fn2-tls-transport) (fn2-tls-transport-input-offset 0 fn2-tls-transport)
       (fn2-tls-transport-output-length 0 fn2-tls-transport) (fn2-tls-transport-output-offset 0 fn2-tls-transport)
       (fn2-tls-transport-quantum 0 fn2-tls-transport))))

(defun fn2-tls-transport-handoff (nonce slot generation fn2-tls-transport)
 (declare (xargs :stobjs fn2-tls-transport
  :guard (and (fn2-tls-transport-wfp fn2-tls-transport) (= (fn2-tls-transport-rows fn2-tls-transport) 1))))
 (if (and (equal nonce (fn2-tls-transport-nonce 0 fn2-tls-transport))
          (equal slot (fn2-tls-transport-slot 0 fn2-tls-transport))
          (equal generation (fn2-tls-transport-generation 0 fn2-tls-transport))
          (= (fn2-tls-transport-terminal 0 fn2-tls-transport) 1)
          (= (fn2-tls-transport-pending 0 fn2-tls-transport) 0)
          (= (fn2-tls-transport-copied 0 fn2-tls-transport) (fn2-tls-transport-seed-total 0 fn2-tls-transport))
          (= (fn2-tls-transport-output-offset 0 fn2-tls-transport) (fn2-tls-transport-output-length 0 fn2-tls-transport)))
  (let* ((copied (fn2-tls-transport-copied 0 fn2-tls-transport))
         (fed (fn2-tls-transport-fed 0 fn2-tls-transport))
         (il (fn2-tls-transport-input-length 0 fn2-tls-transport))
         (io (fn2-tls-transport-input-offset 0 fn2-tls-transport))
         (ol (fn2-tls-transport-output-length 0 fn2-tls-transport))
         (oo (fn2-tls-transport-output-offset 0 fn2-tls-transport))
         (fn2-tls-transport (fn2-tls-transport-put 0 (terminal 3))))
   (mv :ok copied fed il io ol oo fn2-tls-transport))
  (mv :stale 0 0 0 0 0 0 fn2-tls-transport)))
