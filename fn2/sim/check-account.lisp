; ACCOUNT (ROUND2 section F.1; layer D, D7 3/n; design: layer doc 13.7):
; reservations and holdings conserve capacity, one principal cannot spend
; another's protected allocation, and charges match what the simulator
; itself saw. Independent of the ledger's code: its inputs are the
; simulator's per-connection records (the principal the scenario gave it,
; the octets the simulator delivered by Receive completions and moved by
; Send completions, the client's octets and the server octets it read,
; whether its capability is still open) and the ledger's rows as read by
; their column readers. Reply framing is WIRE's (check-wire.lisp).
(in-package "ACL2")
(include-book "check-wire")
(include-book "std/util/bstar" :dir :system)

; Requests after the greeting on one connection, counted by walking the
; server octets against the client's lines as WIRE does: one per answered
; command line, a multi-line body skipped to its terminator, an unfinished
; reply not counted. An article block (after 340 or 335) is one entry, as
; WIRE reads it, and its reply belongs to the command's request: it is
; not another one.
(defun fn2-acct-replies (wire lines fuel)
  (declare (xargs :verify-guards nil :measure (nfix fuel)))
  (if (or (zp fuel) (atom wire) (atom lines)) 0
    (mv-let (found status rest) (fn2-wire-take-line wire nil)
      (let* ((code (and found (fn2-wire-code status)))
             (keyword (fn2-wire-entry-keyword (car lines)))
             (one (if (member-eq (car lines) '(:post-block :ihave-block)) 0 1)))
        (cond ((not code) 0)
              ((and (not (fn2-wire-malformed-p (car lines)))
                    (fn2-wire-multiline-p keyword code))
               (mv-let (bstatus brest) (fn2-wire-body rest 100000)
                 (if (eq bstatus :ok) (+ one (fn2-acct-replies brest (cdr lines) (- fuel 1))) 0)))
              (t (mv-let (ok next) (fn2-wire-next-lines keyword code lines)
                   (+ one (if ok (fn2-acct-replies rest next (- fuel 1)) 0)))))))))

; A connection record: (principal client-octets wire open rx-delivered tx-moved).
; Its greeting: :greeted (200/201), :refused (400), or :none (nothing yet).
(defun fn2-acct-greeting (wire)
  (declare (xargs :verify-guards nil))
  (mv-let (found line rest) (fn2-wire-take-line wire nil)
    (declare (ignore rest))
    (let ((code (and found (fn2-wire-code line))))
      (cond ((member code '(200 201)) :greeted) ((equal code 400) :refused) (t :none)))))
(defun fn2-acct-requests (r)
  (declare (xargs :verify-guards nil))
  (let ((wire (nth 2 r)))
    (if (not (eq (fn2-acct-greeting wire) :greeted)) 0
      (mv-let (found line rest) (fn2-wire-take-line wire nil)
        (declare (ignore found line))
        (mv-let (lines tail) (fn2-wire-lines (nth 1 r) nil nil)
          (declare (ignore tail))
          (fn2-acct-replies rest lines (+ 1 (len lines))))))))

; Per principal P, the simulator's totals: (rx tx requests live refused).
(defun fn2-acct-totals (p records)
  (declare (xargs :verify-guards nil))
  (if (atom records) (list 0 0 0 0 0)
    (let ((r (car records)) (rest (fn2-acct-totals p (cdr records))))
      (if (not (equal (nth 0 r) p)) rest
        (list (+ (nfix (nth 4 r)) (nth 0 rest))
              (+ (nfix (nth 5 r)) (nth 1 rest))
              (+ (fn2-acct-requests r) (nth 2 rest))
              (+ (if (and (nth 3 r) (eq (fn2-acct-greeting (nth 2 r)) :greeted)) 1 0) (nth 3 rest))
              (+ (if (eq (fn2-acct-greeting (nth 2 r)) :refused) 1 0) (nth 4 rest)))))))

; A ledger row as read: (principal limit reserve hold rx tx requests
; listener-bookings), for the :connection-row dimension and the three
; charges; listener-bookings counts the listeners holding a booking on the
; principal for an Accept outstanding (A's S1), part of hold beside the live
; connections.
(defun fn2-acct-sum-committed (rows)
  (declare (xargs :verify-guards nil))
  (if (atom rows) 0
    (+ (max (nfix (nth 3 (car rows))) (nfix (nth 2 (car rows)))) (fn2-acct-sum-committed (cdr rows)))))

; Rows: every ledger row; RECORDS: every connection the run started;
; CAPACITY: the dimension's N. Returns :pass or (:fail what principal ...).
(defun fn2-acct-check-rows (rows records)
  (declare (xargs :verify-guards nil))
  (if (atom rows) :pass
    (b* ((row (car rows)) (p (nth 0 row))
         (totals (fn2-acct-totals p records))
         ((unless (<= (nfix (nth 3 row)) (nfix (nth 1 row)))) (list :fail :hold-over-limit p row))
         ((unless (equal (nth 4 row) (nth 0 totals))) (list :fail :rx-charge p (nth 4 row) (nth 0 totals)))
         ((unless (equal (nth 5 row) (nth 1 totals))) (list :fail :tx-charge p (nth 5 row) (nth 1 totals)))
         ((unless (equal (nth 6 row) (nth 2 totals))) (list :fail :requests p (nth 6 row) (nth 2 totals)))
         ((unless (equal (nth 3 row) (+ (nth 3 totals) (nfix (nth 7 row))))) (list :fail :holding p (nth 3 row) (nth 3 totals)))
         ; protected: a refused connection of a principal below its reserve
         ((when (and (< 0 (nth 4 totals)) (< (nfix (nth 3 row)) (nfix (nth 2 row)))))
          (list :fail :protected-refused p row)))
      (fn2-acct-check-rows (cdr rows) records))))
(defun fn2-account-check (rows records capacity)
  (declare (xargs :verify-guards nil))
  (if (> (fn2-acct-sum-committed rows) capacity)
      (list :fail :over-capacity (fn2-acct-sum-committed rows) capacity)
    (fn2-acct-check-rows rows records)))

; Mutation controls (each must be caught by fn2-account-check on readings
; that pass): a charge dropped, a drain that also clears charges, a refusal
; of a protected principal.
(defun fn2-acct-drop-charge (rows)
  (declare (xargs :verify-guards nil))
  (if (atom rows) nil
    (if (< 0 (nfix (nth 4 (car rows))))
        (cons (update-nth 4 (- (nth 4 (car rows)) 1) (car rows)) (cdr rows))
      (cons (car rows) (fn2-acct-drop-charge (cdr rows))))))
(defun fn2-acct-clear-charges (rows)
  (declare (xargs :verify-guards nil))
  (if (atom rows) nil
    (cons (update-nth 6 0 (update-nth 5 0 (update-nth 4 0 (car rows)))) (fn2-acct-clear-charges (cdr rows)))))
(defun fn2-acct-codes (cs)
  (declare (xargs :verify-guards nil))
  (if (atom cs) '(13 10) (cons (char-code (car cs)) (fn2-acct-codes (cdr cs)))))
(defun fn2-acct-protected-refusal (rows records)
  ; a principal with a reserve above its holding gets a 400'd connection
  (declare (xargs :verify-guards nil))
  (cond ((atom rows) records)
        ((< (nfix (nth 3 (car rows))) (nfix (nth 2 (car rows))))
         (cons (list (nth 0 (car rows)) nil (fn2-acct-codes (coerce "400 busy" (quote list))) nil 0 0) records))
        (t (fn2-acct-protected-refusal (cdr rows) records))))
(defun fn2-account-controls (rows records capacity)
  (declare (xargs :verify-guards nil))
  (list (not (eq (fn2-account-check (fn2-acct-drop-charge rows) records capacity) :pass))
        (not (eq (fn2-account-check (fn2-acct-clear-charges rows) records capacity) :pass))
        ;; applicable only when some principal holds less than its reserve
        (if (equal (fn2-acct-protected-refusal rows records) records) :n/a
          (not (eq (fn2-account-check rows (fn2-acct-protected-refusal rows records) capacity) :pass)))))
