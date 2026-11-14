; Concrete handshake transport ledger. SSL hidden state is an external
; primitive contract, including on WANT/error; this table owns staging,
; observable byte spans and action sequencing, not cryptographic truth.
(in-package "ACL2")
(include-book "tls-kind")
(include-book "tls-transport-state")



(defun fn2-tls-transport-start (cap nonce slot generation total capacity quantum budget window fn2-tls-transport)
 (declare (xargs :stobjs fn2-tls-transport :verify-guards nil
                 :guard (fn2-tls-transport-wfp fn2-tls-transport)))
 (cond
  ((not (and (unsigned-byte-p 32 cap) (unsigned-byte-p 60 nonce) (unsigned-byte-p 32 slot)
             (unsigned-byte-p 60 generation) (unsigned-byte-p 32 total)
             (unsigned-byte-p 32 capacity) (<= total capacity)
             (posp quantum) (unsigned-byte-p 32 quantum)
             (posp budget) (unsigned-byte-p 32 budget)
             (posp window) (unsigned-byte-p 31 window)))
   (mv :bounds fn2-tls-transport))
  ((and (= (fn2-tls-transport-rows fn2-tls-transport) 1)
        (or (= (fn2-tls-transport-alive 0 fn2-tls-transport) 1)
            (and (equal cap (fn2-tls-transport-cap 0 fn2-tls-transport))
                 (equal nonce (fn2-tls-transport-nonce 0 fn2-tls-transport)))))
   (mv :state fn2-tls-transport))
  (t
   (let* ((fn2-tls-transport (fn2-tls-transport-init 1 fn2-tls-transport))
          (fn2-tls-transport (fn2-tls-transport-put 0 (cap cap) (nonce nonce) (slot slot)
            (generation generation) (seed-total total) (seed-capacity capacity)
            (quantum quantum) (budget budget) (window window) (cleanup-credit 1) (ssl-status 5))))
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
  ((member-equal (fn2-tls-transport-terminal 0 fn2-tls-transport) '(2 4))
   (if (= (fn2-tls-transport-alive 0 fn2-tls-transport) 0)
       (mv (if (= (fn2-tls-transport-terminal 0 fn2-tls-transport) 4) :retired :failed)
           0 0 0 0 fn2-tls-transport)
     (if (or (= (fn2-tls-transport-cleanup-credit 0 fn2-tls-transport) 0)
             (= (fn2-tls-transport-serial 0 fn2-tls-transport) #xfffffffffffffff))
         (mv :state 0 0 0 0 fn2-tls-transport)
       (let* ((serial (+ 1 (fn2-tls-transport-serial 0 fn2-tls-transport)))
              (fn2-tls-transport (fn2-tls-transport-put 0
                 (pending 9) (offset 0) (requested 0) (serial serial) (cleanup-credit 0))))
        (mv :cleanup 9 0 0 serial fn2-tls-transport)))))
  ((not (= (fn2-tls-transport-terminal 0 fn2-tls-transport) 0))
   (mv :state 0 0 0 0 fn2-tls-transport))
  (t
   (mv-let (code action offset count)
    (if (= (fn2-tls-transport-alive 0 fn2-tls-transport) 0)
        (mv :act 8 (fn2-tls-transport-window 0 fn2-tls-transport) 0)
     (fn2-tls-transport-plan
      (fn2-tls-transport-seed-total 0 fn2-tls-transport)
      (fn2-tls-transport-copied 0 fn2-tls-transport) (fn2-tls-transport-fed 0 fn2-tls-transport)
      (fn2-tls-transport-input-length 0 fn2-tls-transport) (fn2-tls-transport-input-offset 0 fn2-tls-transport)
      (fn2-tls-transport-output-length 0 fn2-tls-transport) (fn2-tls-transport-output-offset 0 fn2-tls-transport)
      (fn2-tls-transport-ssl-status 0 fn2-tls-transport) room pending
      (fn2-tls-transport-quantum 0 fn2-tls-transport)))
    (cond
     ((eq code :done)
      (let ((fn2-tls-transport (fn2-tls-transport-put 0 (terminal 1))))
 (mv :done 0 0 0 0 fn2-tls-transport)))
     ((or (not (eq code :act)) (zp (fn2-tls-transport-budget 0 fn2-tls-transport))
          (<= #xffffffffffffffe (fn2-tls-transport-serial 0 fn2-tls-transport)))
      (let ((fn2-tls-transport (fn2-tls-transport-put 0 (terminal 2))))
 (mv :closing 0 0 0 0 fn2-tls-transport)))
     (t
      (let ((serial (+ 1 (fn2-tls-transport-serial 0 fn2-tls-transport)))
            (budget (- (fn2-tls-transport-budget 0 fn2-tls-transport) 1)))
       (let ((fn2-tls-transport (fn2-tls-transport-put 0 (pending action) (offset offset) (requested count)
          (serial serial) (budget budget))))
 (mv :act action offset count serial
        fn2-tls-transport)))))))))

(defun fn2-tls-transport-observe (cap nonce slot generation serial code count errno fn2-tls-transport)
 (declare (xargs :stobjs fn2-tls-transport :verify-guards nil
  :guard (and (fn2-tls-transport-wfp fn2-tls-transport) (= (fn2-tls-transport-rows fn2-tls-transport) 1))))
 ;; Malformed/stale returns change neither the pending action nor its ledger.
 (if (not (and (equal cap (fn2-tls-transport-cap 0 fn2-tls-transport))
          (equal nonce (fn2-tls-transport-nonce 0 fn2-tls-transport))
               (equal slot (fn2-tls-transport-slot 0 fn2-tls-transport))
               (equal generation (fn2-tls-transport-generation 0 fn2-tls-transport))
               (equal serial (fn2-tls-transport-serial 0 fn2-tls-transport))
               (< 0 (fn2-tls-transport-pending 0 fn2-tls-transport))
               (integerp code) (unsigned-byte-p 64 (abs code))
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
    ((equal action 8)
     (cond
      ((or (< code 0) (not (= count 0)))
       (let ((fn2-tls-transport (fn2-tls-transport-put 0 (pending 8))))
        (mv :state nil fn2-tls-transport)))
      ((< 0 code)
       (let ((fn2-tls-transport (fn2-tls-transport-put 0 (alive 1) (handle-id code))))
        (mv :ok t fn2-tls-transport)))
      (t
       (let ((fn2-tls-transport (fn2-tls-transport-put 0 (terminal 2))))
        (mv :closing t fn2-tls-transport)))))
    ((equal action 9)
     (if (and (= code 0) (= count 0))
         (let ((fn2-tls-transport (fn2-tls-transport-put 0 (alive 0) (handle-id 0))))
          (mv :ok t fn2-tls-transport))
       (let ((fn2-tls-transport (fn2-tls-transport-put 0 (pending 9))))
        (mv :state nil fn2-tls-transport))))
    ((equal action 7)
     (if (and (member-equal code '(0 1 2)) (= count 0))
         (let ((fn2-tls-transport (fn2-tls-transport-put 0 (ssl-status code))))
 (mv :ok t fn2-tls-transport))
       (let ((fn2-tls-transport (fn2-tls-transport-put 0 (terminal 2))))
 (mv :closing t fn2-tls-transport))))
    ((and (member-equal action '(5 6)) (< code 0) (member-equal errno '(4 11 35)))
     (mv :blocked nil fn2-tls-transport))
    ((not (and (natp code) (<= code requested) (= count 0)
               (unsigned-byte-p 32 (+ offset code))
               (or (not (member-equal action '(1 5 6))) (< 0 code))))
     (let ((fn2-tls-transport (fn2-tls-transport-put 0 (terminal 2))))
 (mv :closing t fn2-tls-transport)))
    ((equal action 1)
     (if (<= (+ offset code) total)
         (let ((fn2-tls-transport (fn2-tls-transport-put 0 (copied (+ offset code)))))
 (mv :ok t fn2-tls-transport))
       (let ((fn2-tls-transport (fn2-tls-transport-put 0 (terminal 2))))
 (mv :closing t fn2-tls-transport))))
    ((equal action 2)
     (if (<= (+ offset code) copied)
         (let ((fn2-tls-transport (fn2-tls-transport-put 0 (fed (+ offset code)) (ssl-status 5))))
 (mv :ok t fn2-tls-transport))
       (let ((fn2-tls-transport (fn2-tls-transport-put 0 (terminal 2))))
 (mv :closing t fn2-tls-transport))))
    ((equal action 3)
     (if (<= (+ offset code) il)
         (let ((fn2-tls-transport (fn2-tls-transport-put 0 (input-offset (+ offset code)) (ssl-status 5))))
 (mv :ok t fn2-tls-transport))
       (let ((fn2-tls-transport (fn2-tls-transport-put 0 (terminal 2))))
 (mv :closing t fn2-tls-transport))))
    ((equal action 4) (let ((fn2-tls-transport (fn2-tls-transport-put 0 (output-length code) (output-offset 0))))
 (mv :ok t fn2-tls-transport)))
    ((equal action 5)
     (if (<= (+ offset code) ol)
         (let ((fn2-tls-transport (fn2-tls-transport-put 0 (output-offset (+ offset code)))))
 (mv :ok t fn2-tls-transport))
       (let ((fn2-tls-transport (fn2-tls-transport-put 0 (terminal 2))))
 (mv :closing t fn2-tls-transport))))
    ((equal action 6) (let ((fn2-tls-transport (fn2-tls-transport-put 0 (input-length code) (input-offset 0))))
 (mv :ok t fn2-tls-transport)))
    (t (let ((fn2-tls-transport (fn2-tls-transport-put 0 (terminal 2))))
 (mv :closing t fn2-tls-transport)))))))

(defun fn2-tls-transport-retire (cap nonce fn2-tls-transport)
 (declare (xargs :stobjs fn2-tls-transport :verify-guards nil
                 :guard (fn2-tls-transport-wfp fn2-tls-transport)))
 (cond
  ((= (fn2-tls-transport-rows fn2-tls-transport) 0) (mv :done fn2-tls-transport))
  ((or (not (equal cap (fn2-tls-transport-cap 0 fn2-tls-transport)))
       (not (equal nonce (fn2-tls-transport-nonce 0 fn2-tls-transport))))
   (mv :stale fn2-tls-transport))
  ((not (= (fn2-tls-transport-pending 0 fn2-tls-transport) 0))
   (mv :pending fn2-tls-transport))
  (t
   (let* ((alive (fn2-tls-transport-alive 0 fn2-tls-transport))
          (fn2-tls-transport (fn2-tls-transport-put 0 (terminal 4))))
    (mv (if (= alive 0) :done :closing) fn2-tls-transport)))))

(defun fn2-tls-transport-handle (fn2-tls-transport)
 (declare (xargs :stobjs fn2-tls-transport :verify-guards nil
                 :guard (fn2-tls-transport-wfp fn2-tls-transport)))
 (if (= (fn2-tls-transport-rows fn2-tls-transport) 0) 0
   (fn2-tls-transport-handle-id 0 fn2-tls-transport)))

(defun fn2-tls-transport-selected-p (cap nonce fn2-tls-transport)
 (declare (xargs :stobjs fn2-tls-transport :verify-guards nil
                 :guard (fn2-tls-transport-wfp fn2-tls-transport)))
 (and (= (fn2-tls-transport-rows fn2-tls-transport) 1)
      (equal cap (fn2-tls-transport-cap 0 fn2-tls-transport))
      (equal nonce (fn2-tls-transport-nonce 0 fn2-tls-transport))))

(defun fn2-tls-transport-status-kick (status)
 (declare (xargs :guard t))
 (eq status :closing))

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
  fn2-tls-transport-handle-id fn2-tls-transport-window fn2-tls-transport-alive fn2-tls-transport-cleanup-credit fn2-tls-transport-cap fn2-tls-transport-nonce fn2-tls-transport-slot fn2-tls-transport-generation fn2-tls-transport-seed-total fn2-tls-transport-seed-capacity fn2-tls-transport-quantum fn2-tls-transport-budget fn2-tls-transport-serial fn2-tls-transport-copied fn2-tls-transport-fed fn2-tls-transport-input-length fn2-tls-transport-input-offset fn2-tls-transport-output-length fn2-tls-transport-output-offset fn2-tls-transport-ssl-status fn2-tls-transport-terminal fn2-tls-transport-pending fn2-tls-transport-offset fn2-tls-transport-requested fn2-tls-transport-raw-negative fn2-tls-transport-raw-code fn2-tls-transport-raw-count fn2-tls-transport-raw-errno))))
(verify-guards fn2-tls-transport-observe
 :hints (("Goal" :in-theory (disable fn2-tls-transport-rows fn2-tls-transport-handle-id fn2-tls-transport-window fn2-tls-transport-alive fn2-tls-transport-cleanup-credit fn2-tls-transport-cap fn2-tls-transport-nonce fn2-tls-transport-slot fn2-tls-transport-generation fn2-tls-transport-seed-total fn2-tls-transport-seed-capacity fn2-tls-transport-quantum fn2-tls-transport-budget fn2-tls-transport-serial fn2-tls-transport-copied fn2-tls-transport-fed fn2-tls-transport-input-length fn2-tls-transport-input-offset fn2-tls-transport-output-length fn2-tls-transport-output-offset fn2-tls-transport-ssl-status fn2-tls-transport-terminal fn2-tls-transport-pending fn2-tls-transport-offset fn2-tls-transport-requested fn2-tls-transport-raw-negative fn2-tls-transport-raw-code fn2-tls-transport-raw-count fn2-tls-transport-raw-errno))))
(verify-guards fn2-tls-transport-retire
 :hints (("Goal" :in-theory (disable fn2-tls-transport-rows fn2-tls-transport-handle-id fn2-tls-transport-window fn2-tls-transport-alive fn2-tls-transport-cleanup-credit fn2-tls-transport-cap fn2-tls-transport-nonce fn2-tls-transport-slot fn2-tls-transport-generation fn2-tls-transport-seed-total fn2-tls-transport-seed-capacity fn2-tls-transport-quantum fn2-tls-transport-budget fn2-tls-transport-serial fn2-tls-transport-copied fn2-tls-transport-fed fn2-tls-transport-input-length fn2-tls-transport-input-offset fn2-tls-transport-output-length fn2-tls-transport-output-offset fn2-tls-transport-ssl-status fn2-tls-transport-terminal fn2-tls-transport-pending fn2-tls-transport-offset fn2-tls-transport-requested fn2-tls-transport-raw-negative fn2-tls-transport-raw-code fn2-tls-transport-raw-count fn2-tls-transport-raw-errno))))
(verify-guards fn2-tls-transport-handle
 :hints (("Goal" :in-theory (disable fn2-tls-transport-rows fn2-tls-transport-handle-id fn2-tls-transport-window fn2-tls-transport-alive fn2-tls-transport-cleanup-credit fn2-tls-transport-cap fn2-tls-transport-nonce fn2-tls-transport-slot fn2-tls-transport-generation fn2-tls-transport-seed-total fn2-tls-transport-seed-capacity fn2-tls-transport-quantum fn2-tls-transport-budget fn2-tls-transport-serial fn2-tls-transport-copied fn2-tls-transport-fed fn2-tls-transport-input-length fn2-tls-transport-input-offset fn2-tls-transport-output-length fn2-tls-transport-output-offset fn2-tls-transport-ssl-status fn2-tls-transport-terminal fn2-tls-transport-pending fn2-tls-transport-offset fn2-tls-transport-requested fn2-tls-transport-raw-negative fn2-tls-transport-raw-code fn2-tls-transport-raw-count fn2-tls-transport-raw-errno))))
(verify-guards fn2-tls-transport-selected-p
 :hints (("Goal" :in-theory (disable fn2-tls-transport-rows fn2-tls-transport-handle-id fn2-tls-transport-window fn2-tls-transport-alive fn2-tls-transport-cleanup-credit fn2-tls-transport-cap fn2-tls-transport-nonce fn2-tls-transport-slot fn2-tls-transport-generation fn2-tls-transport-seed-total fn2-tls-transport-seed-capacity fn2-tls-transport-quantum fn2-tls-transport-budget fn2-tls-transport-serial fn2-tls-transport-copied fn2-tls-transport-fed fn2-tls-transport-input-length fn2-tls-transport-input-offset fn2-tls-transport-output-length fn2-tls-transport-output-offset fn2-tls-transport-ssl-status fn2-tls-transport-terminal fn2-tls-transport-pending fn2-tls-transport-offset fn2-tls-transport-requested fn2-tls-transport-raw-negative fn2-tls-transport-raw-code fn2-tls-transport-raw-count fn2-tls-transport-raw-errno))))

; Keep generated accessor contracts intact instead of expanding array reads.
(local (in-theory (disable fn2-tls-transport-plan fn2-tls-transport-rows
 fn2-tls-transport-handle-id fn2-tls-transport-window fn2-tls-transport-alive fn2-tls-transport-cleanup-credit fn2-tls-transport-cap fn2-tls-transport-nonce fn2-tls-transport-slot fn2-tls-transport-generation fn2-tls-transport-seed-total fn2-tls-transport-seed-capacity fn2-tls-transport-quantum fn2-tls-transport-budget fn2-tls-transport-serial fn2-tls-transport-copied fn2-tls-transport-fed fn2-tls-transport-input-length fn2-tls-transport-input-offset fn2-tls-transport-output-length fn2-tls-transport-output-offset fn2-tls-transport-ssl-status fn2-tls-transport-terminal fn2-tls-transport-pending fn2-tls-transport-offset fn2-tls-transport-requested fn2-tls-transport-raw-negative fn2-tls-transport-raw-code fn2-tls-transport-raw-count fn2-tls-transport-raw-errno)))

(defthm fn2-tls-transport-next-wfp
 (implies (and (fn2-tls-transportp fn2-tls-transport)
               (= (fn2-tls-transport-rows fn2-tls-transport) 1)
               (fn2-tls-transport-wfp fn2-tls-transport))
  (fn2-tls-transport-wfp (mv-nth 5 (fn2-tls-transport-next room pending fn2-tls-transport))))
 :hints (("Goal" :in-theory (disable fn2-tls-transport-plan fn2-tls-transport-rows))))
(defthm fn2-tls-transport-observe-wfp
 (implies (and (fn2-tls-transportp fn2-tls-transport)
               (= (fn2-tls-transport-rows fn2-tls-transport) 1)
               (fn2-tls-transport-wfp fn2-tls-transport))
  (fn2-tls-transport-wfp
   (mv-nth 2 (fn2-tls-transport-observe cap nonce slot generation serial code count errno fn2-tls-transport))))
 :hints (("Goal" :in-theory (disable fn2-tls-transport-rows))))

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
   (8 (equal requested 0))
   (9 (and (equal offset 0) (equal requested 0)))
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

(defun fn2-tls-transport-handoff (cap nonce slot generation fn2-tls-transport)
 (declare (xargs :stobjs fn2-tls-transport
  :guard (and (fn2-tls-transport-wfp fn2-tls-transport) (= (fn2-tls-transport-rows fn2-tls-transport) 1))))
 (if (and (equal cap (fn2-tls-transport-cap 0 fn2-tls-transport))
          (equal nonce (fn2-tls-transport-nonce 0 fn2-tls-transport))
          (equal slot (fn2-tls-transport-slot 0 fn2-tls-transport))
          (equal generation (fn2-tls-transport-generation 0 fn2-tls-transport))
          (= (fn2-tls-transport-terminal 0 fn2-tls-transport) 1)
          (= (fn2-tls-transport-alive 0 fn2-tls-transport) 1)
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

(defthm fn2-tls-transport-stale-observation-frame-by-definition
 (implies (or (not (equal cap (fn2-tls-transport-cap 0 fn2-tls-transport)))
              (not (equal nonce (fn2-tls-transport-nonce 0 fn2-tls-transport)))
              (not (equal slot (fn2-tls-transport-slot 0 fn2-tls-transport)))
              (not (equal generation (fn2-tls-transport-generation 0 fn2-tls-transport)))
              (not (equal serial (fn2-tls-transport-serial 0 fn2-tls-transport)))
              (equal (fn2-tls-transport-pending 0 fn2-tls-transport) 0))
  (equal (mv-nth 2 (fn2-tls-transport-observe cap nonce slot generation serial code count errno fn2-tls-transport))
         fn2-tls-transport)))

(defthm fn2-tls-transport-handoff-refusal-frame-by-definition
 (implies (not (equal (mv-nth 0 (fn2-tls-transport-handoff cap nonce slot generation fn2-tls-transport)) :ok))
  (equal (mv-nth 7 (fn2-tls-transport-handoff cap nonce slot generation fn2-tls-transport)) fn2-tls-transport)))

(defthm fn2-tls-transport-handoff-loan-copied-by-definition
 (implies (equal (mv-nth 0 (fn2-tls-transport-handoff cap nonce slot generation fn2-tls-transport)) :ok)
  (and (equal cap (fn2-tls-transport-cap 0 fn2-tls-transport))
          (equal nonce (fn2-tls-transport-nonce 0 fn2-tls-transport))
       (equal slot (fn2-tls-transport-slot 0 fn2-tls-transport))
       (equal generation (fn2-tls-transport-generation 0 fn2-tls-transport))
       (equal (fn2-tls-transport-pending 0 fn2-tls-transport) 0)
       (equal (mv-nth 1 (fn2-tls-transport-handoff cap nonce slot generation fn2-tls-transport))
              (fn2-tls-transport-seed-total 0 fn2-tls-transport))
       (equal (mv-nth 2 (fn2-tls-transport-handoff cap nonce slot generation fn2-tls-transport))
              (fn2-tls-transport-fed 0 fn2-tls-transport))
       (equal (mv-nth 3 (fn2-tls-transport-handoff cap nonce slot generation fn2-tls-transport))
              (fn2-tls-transport-input-length 0 fn2-tls-transport))
       (equal (mv-nth 4 (fn2-tls-transport-handoff cap nonce slot generation fn2-tls-transport))
              (fn2-tls-transport-input-offset 0 fn2-tls-transport))
       (equal (mv-nth 5 (fn2-tls-transport-handoff cap nonce slot generation fn2-tls-transport))
              (mv-nth 6 (fn2-tls-transport-handoff cap nonce slot generation fn2-tls-transport)))))
 :rule-classes nil)

(defthm fn2-tls-transport-observe-preserves-invariant
 (implies (and (fn2-tls-transportp fn2-tls-transport)
               (fn2-tls-transport-wfp fn2-tls-transport)
               (= (fn2-tls-transport-rows fn2-tls-transport) 1)
               (fn2-tls-transport-invariant fn2-tls-transport))
  (fn2-tls-transport-invariant
   (mv-nth 2 (fn2-tls-transport-observe cap nonce slot generation serial code count errno fn2-tls-transport))))
 :hints (("Goal" :in-theory
            (disable fn2-tls-transport-invariant fn2-tls-transport-pending-valid-p))
         (and stable-under-simplificationp
              '(:in-theory (e/d (fn2-tls-transport-invariant fn2-tls-transport-pending-valid-p
                  fn2-tls-transport-rows fn2-tls-transport-handle-id fn2-tls-transport-window fn2-tls-transport-alive fn2-tls-transport-cleanup-credit fn2-tls-transport-cap fn2-tls-transport-nonce fn2-tls-transport-slot fn2-tls-transport-generation fn2-tls-transport-seed-total fn2-tls-transport-seed-capacity fn2-tls-transport-quantum fn2-tls-transport-budget fn2-tls-transport-serial fn2-tls-transport-copied fn2-tls-transport-fed fn2-tls-transport-input-length fn2-tls-transport-input-offset fn2-tls-transport-output-length fn2-tls-transport-output-offset fn2-tls-transport-ssl-status fn2-tls-transport-terminal fn2-tls-transport-pending fn2-tls-transport-offset fn2-tls-transport-requested fn2-tls-transport-raw-negative fn2-tls-transport-raw-code fn2-tls-transport-raw-count fn2-tls-transport-raw-errno) (nth update-nth))))))

(defthm fn2-tls-transport-plan-pending-valid
 (implies (equal (mv-nth 0 (fn2-tls-transport-plan total copied fed il io ol oo ssl room pending quantum)) :act)
  (fn2-tls-transport-pending-valid-p
   (mv-nth 1 (fn2-tls-transport-plan total copied fed il io ol oo ssl room pending quantum))
   (mv-nth 2 (fn2-tls-transport-plan total copied fed il io ol oo ssl room pending quantum))
   (mv-nth 3 (fn2-tls-transport-plan total copied fed il io ol oo ssl room pending quantum))
   total copied fed il io ol oo quantum))
 :hints (("Goal" :in-theory (enable fn2-tls-transport-plan))))

(defthm fn2-tls-transport-pending-allocation-or-free
 (and (equal (fn2-tls-transport-pending-valid-p 8 window 0 total copied fed il io ol oo quantum)
             (natp quantum))
      (equal (fn2-tls-transport-pending-valid-p 9 0 0 total copied fed il io ol oo quantum)
             (natp quantum))))

(defthm fn2-tls-transport-next-preserves-invariant
 (implies (and (fn2-tls-transportp fn2-tls-transport)
               (fn2-tls-transport-wfp fn2-tls-transport)
               (= (fn2-tls-transport-rows fn2-tls-transport) 1)
               (fn2-tls-transport-invariant fn2-tls-transport))
  (fn2-tls-transport-invariant
   (mv-nth 5 (fn2-tls-transport-next room pending fn2-tls-transport))))
 :hints (("Goal" :in-theory
            (disable fn2-tls-transport-invariant fn2-tls-transport-pending-valid-p))
         (and stable-under-simplificationp
              '(:in-theory (e/d (fn2-tls-transport-invariant
                  fn2-tls-transport-rows fn2-tls-transport-handle-id fn2-tls-transport-window fn2-tls-transport-alive fn2-tls-transport-cleanup-credit fn2-tls-transport-cap fn2-tls-transport-nonce fn2-tls-transport-slot fn2-tls-transport-generation fn2-tls-transport-seed-total fn2-tls-transport-seed-capacity fn2-tls-transport-quantum fn2-tls-transport-budget fn2-tls-transport-serial fn2-tls-transport-copied fn2-tls-transport-fed fn2-tls-transport-input-length fn2-tls-transport-input-offset fn2-tls-transport-output-length fn2-tls-transport-output-offset fn2-tls-transport-ssl-status fn2-tls-transport-terminal fn2-tls-transport-pending fn2-tls-transport-offset fn2-tls-transport-requested fn2-tls-transport-raw-negative fn2-tls-transport-raw-code fn2-tls-transport-raw-count fn2-tls-transport-raw-errno)
                  (nth update-nth fn2-tls-transport-pending-valid-p))))))

(defthm-owed fn2-tls-transport-observe-preserves-invariant (cap nonce slot generation serial code count errno fn2-tls-transport)
 (implies (and (fn2-tls-transportp fn2-tls-transport)
               (fn2-tls-transport-wfp fn2-tls-transport)
               (= (fn2-tls-transport-rows fn2-tls-transport) 1)
               (fn2-tls-transport-invariant fn2-tls-transport))
  (fn2-tls-transport-invariant
   (mv-nth 2 (fn2-tls-transport-observe cap nonce slot generation serial code count errno fn2-tls-transport))))
 :schema :invariant
 :teeth (fn2-tls-transport-invariant-positive fn2-tls-transport-observe-invariant-negative)
 :doc "The host-called observe preserves staged-seed conservation, bounded input/output buffers, unsent prefixes and the pending action span. Physical byte-prefix correspondence remains a separate primitive boundary obligation.")
(fn2-owed-discharge fn2-tls-transport-observe-preserves-invariant fn2-tls-transport-observe-preserves-invariant)

(defthm-owed fn2-tls-transport-next-preserves-invariant (room pending fn2-tls-transport)
 (implies (and (fn2-tls-transportp fn2-tls-transport)
               (fn2-tls-transport-wfp fn2-tls-transport)
               (= (fn2-tls-transport-rows fn2-tls-transport) 1)
               (fn2-tls-transport-invariant fn2-tls-transport))
  (fn2-tls-transport-invariant
   (mv-nth 5 (fn2-tls-transport-next room pending fn2-tls-transport))))
 :schema :invariant
 :teeth (fn2-tls-transport-invariant-positive fn2-tls-transport-next-invariant-negative)
 :doc "The host-called next preserves staged-seed conservation, bounded input/output buffers, unsent prefixes and the pending action span. Physical byte-prefix correspondence remains a separate primitive boundary obligation.")
(fn2-owed-discharge fn2-tls-transport-next-preserves-invariant fn2-tls-transport-next-preserves-invariant)

(defthm fn2-tls-transport-start-establishes-invariant
 (implies (and (fn2-tls-transportp fn2-tls-transport)
               (equal (mv-nth 0 (fn2-tls-transport-start cap nonce slot generation total capacity quantum budget window fn2-tls-transport)) :ok))
  (fn2-tls-transport-invariant
   (mv-nth 1 (fn2-tls-transport-start cap nonce slot generation total capacity quantum budget window fn2-tls-transport))))
 :hints (("Goal" :in-theory
            (disable fn2-tls-transport-invariant fn2-tls-transport-pending-valid-p fn2-tls-transport-init))
         (and stable-under-simplificationp
              '(:in-theory (e/d (fn2-tls-transport-invariant fn2-tls-transport-pending-valid-p
                  fn2-tls-transport-rows fn2-tls-transport-handle-id fn2-tls-transport-window fn2-tls-transport-alive fn2-tls-transport-cleanup-credit fn2-tls-transport-cap fn2-tls-transport-nonce fn2-tls-transport-slot fn2-tls-transport-generation fn2-tls-transport-seed-total fn2-tls-transport-seed-capacity fn2-tls-transport-quantum fn2-tls-transport-budget fn2-tls-transport-serial fn2-tls-transport-copied fn2-tls-transport-fed fn2-tls-transport-input-length fn2-tls-transport-input-offset fn2-tls-transport-output-length fn2-tls-transport-output-offset fn2-tls-transport-ssl-status fn2-tls-transport-terminal fn2-tls-transport-pending fn2-tls-transport-offset fn2-tls-transport-requested fn2-tls-transport-raw-negative fn2-tls-transport-raw-code fn2-tls-transport-raw-count fn2-tls-transport-raw-errno)
                  (nth update-nth fn2-tls-transport-init))))))

(defthm fn2-tls-transport-next-spends-one-action
 (implies (and (fn2-tls-transportp fn2-tls-transport)
               (fn2-tls-transport-wfp fn2-tls-transport)
               (= (fn2-tls-transport-rows fn2-tls-transport) 1)
               (equal (mv-nth 0 (fn2-tls-transport-next room pending fn2-tls-transport)) :act))
  (and (equal (fn2-tls-transport-budget 0 (mv-nth 5 (fn2-tls-transport-next room pending fn2-tls-transport)))
              (- (fn2-tls-transport-budget 0 fn2-tls-transport) 1))
       (equal (fn2-tls-transport-serial 0 (mv-nth 5 (fn2-tls-transport-next room pending fn2-tls-transport)))
              (+ (fn2-tls-transport-serial 0 fn2-tls-transport) 1))
       (< 0 (fn2-tls-transport-budget 0 fn2-tls-transport))))
 :hints (("Goal" :in-theory
  (e/d (fn2-tls-transport-budget fn2-tls-transport-serial fn2-tls-transport-rows)
       (nth update-nth)))))

(assert-event
 (fn2-assert-compliant-p
  '(fn2-tls-transport-start fn2-tls-transport-next fn2-tls-transport-observe
    fn2-tls-transport-handoff fn2-tls-transport-retire fn2-tls-transport-handle fn2-tls-transport-selected-p fn2-tls-transport-status-kick fn2-tls-transport-action-interest) (w state)))

(defthm-owed fn2-tls-transport-next-spends-one-action (room pending fn2-tls-transport)
 (implies (and (fn2-tls-transportp fn2-tls-transport)
               (fn2-tls-transport-wfp fn2-tls-transport)
               (= (fn2-tls-transport-rows fn2-tls-transport) 1)
               (equal (mv-nth 0 (fn2-tls-transport-next room pending fn2-tls-transport)) :act))
  (and (equal (fn2-tls-transport-budget 0 (mv-nth 5 (fn2-tls-transport-next room pending fn2-tls-transport)))
              (- (fn2-tls-transport-budget 0 fn2-tls-transport) 1))
       (equal (fn2-tls-transport-serial 0 (mv-nth 5 (fn2-tls-transport-next room pending fn2-tls-transport)))
              (+ (fn2-tls-transport-serial 0 fn2-tls-transport) 1))
       (< 0 (fn2-tls-transport-budget 0 fn2-tls-transport))))
 :schema :invariant
 :teeth (fn2-tls-transport-invariant-positive fn2-tls-transport-check-budget)
 :doc "Every action selected for the native handshake spends exactly one admitted budget unit and advances its serial without wrap; exhausted attempts select no physical work.")
(fn2-owed-discharge fn2-tls-transport-next-spends-one-action fn2-tls-transport-next-spends-one-action)


(defun fn2-tls-transport-handle-invariant (fn2-tls-transport)
 (declare (xargs :stobjs fn2-tls-transport
  :guard (and (fn2-tls-transport-wfp fn2-tls-transport) (= (fn2-tls-transport-rows fn2-tls-transport) 1))))
 (let ((alive (fn2-tls-transport-alive 0 fn2-tls-transport))
       (identity (fn2-tls-transport-handle-id 0 fn2-tls-transport))
       (credit (fn2-tls-transport-cleanup-credit 0 fn2-tls-transport))
       (pending (fn2-tls-transport-pending 0 fn2-tls-transport))
       (terminal (fn2-tls-transport-terminal 0 fn2-tls-transport)))
  (and (equal (= alive 0) (= identity 0))
       (implies (= terminal 0) (= credit 1))
       (implies (member-equal terminal '(1 3)) (= alive 1))
       (implies (member-equal pending '(1 2 3 4 5 6 7 9)) (= alive 1))
       (implies (= pending 8) (and (= alive 0) (= credit 1)))
       (implies (= pending 9) (and (= credit 0) (member-equal terminal '(2 4))))
       (implies (= credit 0) (or (= alive 0) (= pending 9))))))

(defthm fn2-tls-transport-next-preserves-handle-ownership
 (implies (and (fn2-tls-transportp fn2-tls-transport)
               (fn2-tls-transport-wfp fn2-tls-transport)
               (= (fn2-tls-transport-rows fn2-tls-transport) 1)
               (fn2-tls-transport-handle-invariant fn2-tls-transport))
  (fn2-tls-transport-handle-invariant (mv-nth 5 (fn2-tls-transport-next room pending fn2-tls-transport))))
 :hints (("Goal" :in-theory (disable fn2-tls-transport-handle-invariant))
         (and stable-under-simplificationp
          '(:in-theory (e/d (fn2-tls-transport-handle-invariant fn2-tls-transport-alive fn2-tls-transport-handle-id fn2-tls-transport-cleanup-credit fn2-tls-transport-pending fn2-tls-transport-terminal fn2-tls-transport-rows)
                           (nth update-nth))))))

(defthm fn2-tls-transport-observe-preserves-handle-ownership
 (implies (and (fn2-tls-transportp fn2-tls-transport)
               (fn2-tls-transport-wfp fn2-tls-transport)
               (= (fn2-tls-transport-rows fn2-tls-transport) 1)
               (fn2-tls-transport-handle-invariant fn2-tls-transport))
  (fn2-tls-transport-handle-invariant (mv-nth 2 (fn2-tls-transport-observe cap nonce slot generation serial code count errno fn2-tls-transport))))
 :hints (("Goal" :in-theory (disable fn2-tls-transport-handle-invariant))
         (and stable-under-simplificationp
          '(:in-theory (e/d (fn2-tls-transport-handle-invariant fn2-tls-transport-alive fn2-tls-transport-handle-id fn2-tls-transport-cleanup-credit fn2-tls-transport-pending fn2-tls-transport-terminal fn2-tls-transport-rows)
                           (nth update-nth))))))

(defthm fn2-tls-transport-retire-preserves-handle-ownership
 (implies (and (fn2-tls-transportp fn2-tls-transport)
               (fn2-tls-transport-wfp fn2-tls-transport)
               (= (fn2-tls-transport-rows fn2-tls-transport) 1)
               (fn2-tls-transport-handle-invariant fn2-tls-transport))
  (fn2-tls-transport-handle-invariant (mv-nth 1 (fn2-tls-transport-retire cap nonce fn2-tls-transport))))
 :hints (("Goal" :in-theory (disable fn2-tls-transport-handle-invariant))
         (and stable-under-simplificationp
          '(:in-theory (e/d (fn2-tls-transport-handle-invariant fn2-tls-transport-alive fn2-tls-transport-handle-id fn2-tls-transport-cleanup-credit fn2-tls-transport-pending fn2-tls-transport-terminal fn2-tls-transport-rows)
                           (nth update-nth))))))
