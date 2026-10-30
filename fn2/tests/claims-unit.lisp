; D5 evidence for the identity claim table (fn2/books/claims.lisp;
; fn2/docs/d-machines-nntp.md section 14.4.2). The property the claims
; give the transaction machine: at most one row holds a claim on given
; Message-ID octets at any time, a same-octets claimant waits in the
; holder's FIFO, and a release hands the claim to the FIFO's head. The
; schedule's outcomes are written here by hand; after every step the number
; of rows holding each Message-ID is counted independently (each held row's
; octets read back and compared as lists). Every schedule runs with the real
; hash and with one hash for every offer (every claim collides, so octets
; decide), and with walk budgets 4 and 1. Negative tooth: a walk overtaken by
; a later claim, without the bucket stamp's restart, lets two rows hold
; one Message-ID.
; Run: sh fn2/tools/certify.sh tests/claims-unit.lisp
(in-package "ACL2")
(include-book "../books/claims")
(include-book "../books/grammar")

(defun fn2-clu-octets (cs)
  (declare (xargs :guard (character-listp cs)))
  (if (atom cs) nil (cons (char-code (car cs)) (fn2-clu-octets (cdr cs)))))
(defun fn2-clu-put (octets slot gen ok os og fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil))
  (if (atom octets) fn2-pool
    (mv-let (code fn2-pool) (fn2-gram-put (nfix (car octets)) slot gen ok os og fn2-pool)
      (declare (ignore code))
      (fn2-clu-put (cdr octets) slot gen ok os og fn2-pool))))
(defun fn2-clu-get (k n slot gen ok os og fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil :measure (nfix (- (nfix n) (nfix k)))))
  (if (>= (nfix k) (nfix n)) nil
    (mv-let (good b) (fn2-gram-read slot gen (nfix k) ok os og fn2-pool)
      (cons (if good b 999) (fn2-clu-get (+ 1 (nfix k)) n slot gen ok os og fn2-pool)))))

; Row R's offer: a slot of its own under owner (2 R 1) holding the octets.
(defun fn2-clu-place (r mids fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil))
  (if (atom mids) (mv nil fn2-pool)
    (mv-let (code slot gen fn2-pool) (fn2-pool-reserve 0 2 r 1 fn2-pool)
      (declare (ignore code))
      (let ((fn2-pool (fn2-clu-put (fn2-clu-octets (coerce (car mids) 'list)) slot gen 2 r 1 fn2-pool)))
        (mv-let (rest fn2-pool) (fn2-clu-place (+ 1 r) (cdr mids) fn2-pool)
          (mv (cons (list slot gen) rest) fn2-pool))))))

; How many held rows carry the octets of MID (read back independently).
(defun fn2-clu-holders (x mid fn2-claims fn2-pool)
  (declare (xargs :stobjs (fn2-claims fn2-pool) :verify-guards nil :measure (nfix x)))
  (if (zp x) 0
    (let ((r (- x 1)))
      (+ (if (and (equal (fn2-claims-state r fn2-claims) *fn2-claim-state-held*)
                  (equal (fn2-clu-get (fn2-claims-off r fn2-claims)
                                      (+ (fn2-claims-off r fn2-claims) (fn2-claims-len r fn2-claims))
                                      (fn2-claims-slot r fn2-claims) (fn2-claims-gen r fn2-claims)
                                      (fn2-claims-ok r fn2-claims) (fn2-claims-os r fn2-claims)
                                      (fn2-claims-og r fn2-claims) fn2-pool)
                         (fn2-clu-octets (coerce mid 'list))))
             1 0)
         (fn2-clu-holders r mid fn2-claims fn2-pool)))))

(defun fn2-clu-walk (fuel r budget restart fn2-claims fn2-pool)
  (declare (xargs :stobjs (fn2-claims fn2-pool) :verify-guards nil :measure (nfix fuel)))
  (mv-let (code holder fn2-claims)
    (if restart (fn2-claim-walk r budget fn2-claims fn2-pool) (fn2-claim-walk-loop budget r fn2-claims fn2-pool))
    (if (and (eq code :more) (not (zp fuel))) (fn2-clu-walk (- fuel 1) r budget restart fn2-claims fn2-pool)
      (mv (list code holder) fn2-claims))))

; Steps: (:begin r), (:walk r), (:release r). SAME: one hash for every
; offer. Returns, per step, its outcome and the holder counts of MIDS.
(defun fn2-clu-steps (steps mids slots rows same budget restart fn2-claims fn2-pool)
  (declare (xargs :stobjs (fn2-claims fn2-pool) :verify-guards nil))
  (if (atom steps) (mv nil fn2-claims)
    (b* ((r (cadr (car steps)))
         ((mv out fn2-claims)
          (case (car (car steps))
            (:begin (b* ((slot (car (nth r slots))) (gen (cadr (nth r slots))) (len (length (nth r mids)))
                         ((mv & h) (fn2-pool-fold slot gen 0 len 2166136261 2 r 1 fn2-pool))
                         ((mv code fn2-claims) (fn2-claim-begin r (if same 5 h) slot gen 0 len 2 r 1 fn2-claims)))
                      (mv (list :begin code) fn2-claims)))
            (:walk (fn2-clu-walk 64 r budget restart fn2-claims fn2-pool))
            (otherwise (mv-let (code w fn2-claims) (fn2-claim-release r fn2-claims) (mv (list code w) fn2-claims)))))
         (counts (list (fn2-clu-holders rows "<m1@x>" fn2-claims fn2-pool) (fn2-clu-holders rows "<m2@x>" fn2-claims fn2-pool)))
         ((mv rest fn2-claims) (fn2-clu-steps (cdr steps) mids slots rows same budget restart fn2-claims fn2-pool)))
      (mv (cons (list out counts) rest) fn2-claims))))

(defun fn2-clu-run (mids steps same budget restart)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-pool
    (mv-let (result fn2-pool)
      (with-local-stobj fn2-claims
        (mv-let (result fn2-claims fn2-pool)
          (b* ((rows (len mids))
               (fn2-claims (fn2-claims-table-init rows fn2-claims))
               (fn2-pool (fn2-pool-init '((8 . 256)) 1 1000 fn2-pool))
               ((mv slots fn2-pool) (fn2-clu-place 0 mids fn2-pool))
               ((mv out fn2-claims) (fn2-clu-steps steps mids slots rows same budget restart fn2-claims fn2-pool)))
            (mv out fn2-claims fn2-pool))
          (mv result fn2-pool)))
      result)))

(defconst *fn2-clu-mids* '("<m1@x>" "<m1@x>" "<m2@x>" "<m1@x>"))
(defconst *fn2-clu-none* *fn2-none*)
; Rows 0, 1 and 3 offer <m1@x>, row 2 <m2@x>.
(defconst *fn2-clu-schedule*
  '((:begin 0) (:walk 0) (:begin 1) (:walk 1) (:begin 2) (:walk 2) (:begin 3) (:walk 3)
    (:release 0) (:release 2) (:release 1) (:begin 0) (:walk 0) (:release 3) (:release 0)))
(defconst *fn2-clu-expect*
  `(((:begin :ok) (0 0)) ((:claimed ,*fn2-none*) (1 0))
    ((:begin :ok) (1 0)) ((:wait 0) (1 0))
    ((:begin :ok) (1 0)) ((:claimed ,*fn2-none*) (1 1))
    ((:begin :ok) (1 1)) ((:wait 0) (1 1))
    ((:ok 1) (1 1)) ((:ok ,*fn2-none*) (1 0)) ((:ok 3) (1 0))
    ((:begin :ok) (1 0)) ((:wait 3) (1 0))
    ((:ok 0) (1 0)) ((:ok ,*fn2-none*) (0 0))))

(assert-event
 (and (equal (fn2-clu-run *fn2-clu-mids* *fn2-clu-schedule* nil 4 t) *fn2-clu-expect*)
      (equal (fn2-clu-run *fn2-clu-mids* *fn2-clu-schedule* t 4 t) *fn2-clu-expect*)
      (equal (fn2-clu-run *fn2-clu-mids* *fn2-clu-schedule* nil 1 t) *fn2-clu-expect*)
      (equal (fn2-clu-run *fn2-clu-mids* *fn2-clu-schedule* t 1 t) *fn2-clu-expect*)))

; An overtaken walk: row 0 begins on an empty bucket, row 1 claims the same
; octets, then row 0 walks. With the stamp restart it waits on row 1; the
; tooth: without it, row 0 claims too and two rows hold <m1@x>.
(defconst *fn2-clu-overtaken* '((:begin 0) (:begin 1) (:walk 1) (:walk 0)))
(assert-event
 (and (equal (car (car (last (fn2-clu-run *fn2-clu-mids* *fn2-clu-overtaken* t 4 t)))) '(:wait 1))
      (equal (cadr (car (last (fn2-clu-run *fn2-clu-mids* *fn2-clu-overtaken* t 4 nil)))) '(2 0))))
