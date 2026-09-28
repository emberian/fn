; Witnesses for books/store-log-damage (the open tells a torn tail from damage;
; lane log-corruption, fuzz-nntp's F3).
;
; Keystones and their witnesses:
;   fn-lgdm-open-verdict-is-the-classification (unconditional): (1) both sides
;     evaluated and equal on a damaged, a torn, a clean and a spliced segment,
;     and the host's walk (header window, entry length, entry window, step) is
;     the probe's run.
;   fn-lgdm-no-silent-prefix (its implications' antecedents): (1) REACHABLE
;     the fuzz case at small scale -- one bit flipped at offset 0 of the first
;     entry of a three-entry segment: the stream reads nothing, a valid entry
;     starts one entry later, the antecedent holds and the verdict is
;     :damaged (valid-after 2); a flip in the second entry: :damaged at the
;     second entry with one valid after.  (2) The antecedent fails on a torn
;     tail and on a clean segment, and the verdict there is not refused: the
;     conclusion is not true of every segment.
;   fn-lgdm-damage-lies-in-the-last-write (hypotheses: the genesis is a
;     digest, the records are admitted, the segment is L ++ Y ++ zeros):
;     (1) REACHABLE torn tail (Y the third entry with its last octets
;     zeroed): :torn at L's end, not refused, the conclusion holds; a clean
;     segment (Y empty): :complete.  (3) HYPOTHESIS REMOVAL: the flipped
;     segment claimed as L = the three records' log with Y empty: the digest
;     and admission hypotheses hold, the shape hypothesis fails, and the
;     conclusion fails (the stop is before L's end and the verdict is
;     refused although Y is empty).
;   fn-lgdm-repair-is-only-the-confirmed-damage: (1) the confirmed repair of
;     the flipped segment is :repaired at the stop, not refused; (3) a repair
;     naming another offset, or of a read-only (closed) segment, changes
;     nothing.
(in-package "ACL2")
(include-book "../../books/store-log-damage")
; The record codec seam's attachment: since snapshot-open-3 the log's txid
; reads the record through fn-record-decode-exact (books/store-log-txid.lisp).
(include-book "../../books/codec-attach")

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-lg-declared-len))))

(defun sld-unit () (declare (xargs :guard t)) 4)
(defun sld-max () (declare (xargs :guard t)) 4096)
(defun sld-extent () (declare (xargs :guard t)) 2048)
(defun sld-rec (i) (declare (xargs :guard t :verify-guards nil)) (fn-lg-workload-record i 8))

(defun sld-pad (log)
  (declare (xargs :guard t :verify-guards nil))
  (append log (fn-bs-zeros (- (sld-extent) (len log)))))

(defun sld-t1 () (declare (xargs :guard t :verify-guards nil))
  (fn-lg-last-trailer (list (sld-rec 1)) *fn-lg-genesis*))
(defun sld-t2 () (declare (xargs :guard t :verify-guards nil))
  (fn-lg-last-trailer (list (sld-rec 2)) (sld-t1)))
(defun sld-e1 () (declare (xargs :guard t :verify-guards nil))
  (fn-lg-log (list (sld-rec 1)) *fn-lg-genesis* (sld-unit)))
(defun sld-e2 () (declare (xargs :guard t :verify-guards nil))
  (fn-lg-log (list (sld-rec 2)) (sld-t1) (sld-unit)))
(defun sld-e3 () (declare (xargs :guard t :verify-guards nil))
  (fn-lg-log (list (sld-rec 3)) (sld-t2) (sld-unit)))
(defun sld-log3 () (declare (xargs :guard t :verify-guards nil))
  (append (sld-e1) (sld-e2) (sld-e3)))
(defun sld-seg () (declare (xargs :guard t :verify-guards nil)) (sld-pad (sld-log3)))

; One bit flipped at offset AT of X (fuzz-nntp's "flip", bit 1).
(defun sld-flip (x at)
  (declare (xargs :guard t :verify-guards nil))
  (update-nth at (logxor 1 (nfix (nth at x))) x))

(defun sld-flip-first () (declare (xargs :guard t :verify-guards nil)) (sld-flip (sld-seg) 0))
(defun sld-flip-second () (declare (xargs :guard t :verify-guards nil))
  (sld-flip (sld-seg) (+ (len (sld-e1)) 20)))

; The torn tail: the third entry's last eight octets zeroed.
(defun sld-y-torn () (declare (xargs :guard t :verify-guards nil))
  (append (fn-bs-take (- (len (sld-e3)) 8) (sld-e3)) (fn-bs-zeros 8)))
(defun sld-l12 () (declare (xargs :guard t :verify-guards nil)) (append (sld-e1) (sld-e2)))
(defun sld-torn () (declare (xargs :guard t :verify-guards nil))
  (sld-pad (append (sld-l12) (sld-y-torn))))

; The splice: entry 1, then an entry chained from record 7's trailer.
(defun sld-splice () (declare (xargs :guard t :verify-guards nil))
  (sld-pad (append (sld-e1)
                   (fn-lg-log (list (sld-rec 2))
                              (fn-lg-last-trailer (list (sld-rec 7)) *fn-lg-genesis*)
                              (sld-unit)))))

(defun sld-open (c) (declare (xargs :guard t :verify-guards nil))
  (fn-lgdm-open c *fn-lg-genesis* 1 (sld-unit) (sld-max)))
(defun sld-classify (c) (declare (xargs :guard t :verify-guards nil))
  (fn-lgdm-classify c *fn-lg-genesis* (sld-unit) (sld-max)))

; The host's walk of the probe, spelled as host/native/io.lisp
; fnn-log-probe-tail does it (FUEL bounds it).
(defun sld-host-probe (c ps fuel)
  (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
  (if (or (zp fuel) (fn-lgdm-done-p ps (len c)))
      ps
    (let* ((q (fn-lgdm-q ps))
           (h (fn-bs-take (fn-lgdm-header-len ps (len c)) (nthcdr q c)))
           (n (fn-lgdm-entry-len h ps (len c)))
           (e (and n (fn-bs-take n (nthcdr q c)))))
      (sld-host-probe c (fn-lgdm-step h e ps (sld-unit) (sld-max)) (1- fuel)))))

(defun sld-host-verdict (c)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (records st) (fn-lgw-run c (fn-lgw-start *fn-lg-genesis* 1) (sld-unit) (sld-max))
    (declare (ignore records))
    (fn-lgdm-verdict st (sld-host-probe c (fn-lgdm-start st) 5000) (len c))))

(defun sld-valid-at (c q)
  (declare (xargs :guard t :verify-guards nil))
  (fn-lgdm-valid-p (fn-lg-slice (nthcdr q c)) (sld-max)))

; (1) REACHABLE: the fuzz case.  One bit flipped at offset 0: the stream stops
; at 0, the entry at (len e1) is valid (the antecedent of
; fn-lgdm-no-silent-prefix with k = (len e1)/unit), and the verdict is
; :damaged at 0, first valid at (len e1), two valid entries after, two records.
(assert-event
 (let* ((c (sld-flip-first)) (v (sld-open c)) (q (len (sld-e1))))
   (and (equal (mod q (sld-unit)) 0)
        (sld-valid-at c q)
        (< q (len c))
        (equal (cdr (fn-lg-scan c *fn-lg-genesis* (sld-unit) (sld-max))) 0)
        (equal v (list :damaged 0 q 2 2))
        (fn-lgdm-refused-p v)
        (equal (sld-host-verdict c) v)
        (equal (sld-classify c) (list :damaged 0 q))
        (equal (fn-lgdm-kind v) (car (sld-classify c)))
        (sld-valid-at c (nth 2 v))
        (equal (fn-lgdm-refusal-text v "000001.log")
               (concatenate 'string
                            "open refused reason=log-damaged at=000001.log:0 first-valid="
                            (fn-lgdm-dec q)
                            " valid-after=2 records=2: an entry of the record log does not validate and"
                            " valid entries follow it (damage, not a torn tail); nothing was written."
                            "  To keep the history before it and drop the rest (the segment is kept"
                            " under quarantine/ first): recover --repair truncate 000001.log:0")))))

; (1) A flip inside the second entry: one record read, :damaged at the
; second entry's start, one valid entry after.
(assert-event
 (let* ((c (sld-flip-second)) (v (sld-open c))
        (p (len (sld-e1))) (q (+ (len (sld-e1)) (len (sld-e2)))))
   (and (sld-valid-at c q)
        (equal v (list :damaged p q 1 1))
        (equal (sld-host-verdict c) v)
        (equal (sld-classify c) (list :damaged p q)))))

; (1) The torn tail: :torn at L's end (two entries), not refused; the
; hypotheses of fn-lgdm-damage-lies-in-the-last-write hold with L the log of
; records 1 and 2 as written (two entries), Y the torn third entry.
(assert-event
 (let* ((c (sld-torn)) (v (sld-open c)) (l (len (sld-l12))))
   (and (equal c (append (sld-l12) (sld-y-torn) (fn-bs-zeros (- (- (sld-extent) (len (sld-l12)))
                                                                   (len (sld-y-torn))))))
        (equal (car v) :torn)
        (equal (nth 1 v) l)
        (< 0 (nth 2 v))
        (not (fn-lgdm-refused-p v))
        (equal (sld-host-verdict c) v)
        (equal (sld-classify c) (list :intact l))
        (equal (fn-lgdm-report-text v "000001.log")
               (concatenate 'string "log torn-tail at=000001.log:" (fn-lgdm-dec l)
                            " debris-units=" (fn-lgdm-dec (nth 2 v))
                            " (dropped: the incomplete last write)")))))

; (1) The damage theorem's hypotheses with L one batch entry (fn-lg-log of
; two records) and Y the torn third entry chained from its last trailer.
(defun sld-batch-l () (declare (xargs :guard t :verify-guards nil))
  (fn-lg-log (list (sld-rec 1) (sld-rec 2)) *fn-lg-genesis* (sld-unit)))
(defun sld-batch-y () (declare (xargs :guard t :verify-guards nil))
  (let ((e (fn-lg-log (list (sld-rec 3))
                      (fn-lg-last-trailer (list (sld-rec 1) (sld-rec 2)) *fn-lg-genesis*)
                      (sld-unit))))
    (append (fn-bs-take (- (len e) 8) e) (fn-bs-zeros 8))))
(assert-event
 (let* ((z 1024)
        (c (append (sld-batch-l) (sld-batch-y) (fn-bs-zeros z)))
        (v (sld-open c)) (l (len (sld-batch-l))))
   (and (fn-frame-digestp *fn-lg-genesis*)
        (fn-lg-recordsp (list (sld-rec 1) (sld-rec 2)) (sld-max))
        (natp z)
        (consp (sld-batch-y))
        (<= l (nth 1 v))
        (equal (car v) :torn)
        (not (fn-lgdm-refused-p v)))))

; (1) A clean segment (Y empty): :complete at L's end.
(assert-event
 (let* ((c (sld-seg)) (v (sld-open c)))
   (and (equal v (list :complete (len (sld-log3))))
        (equal (sld-host-verdict c) v)
        (not (fn-lgdm-refused-p v))
        (not (fn-lgdm-report-text v "000001.log")))))

; (1) The splice stays the splice verdict, refused by its own name.
(assert-event
 (let* ((c (sld-splice)) (v (sld-open c)))
   (and (equal v (list :broken (len (sld-e1))))
        (equal (sld-classify c) (list :broken (len (sld-e1))))
        (fn-lgdm-refused-p v)
        (equal (fn-lgdm-refusal-text v "000001.log")
               (concatenate 'string "open refused reason=log-chain-broken at=000001.log:"
                            (fn-lgdm-dec (len (sld-e1)))
                            ": a log segment holds an entry chained from another history")))))

; (2) fn-lgdm-no-silent-prefix's antecedent fails on the torn and the clean
; segments (no valid entry at any unit past the stop), and they are not
; refused.
(defun sld-any-valid-past (c q fuel)
  (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
  (cond ((zp fuel) nil)
        ((<= (len c) (nfix q)) nil)
        ((sld-valid-at c q) t)
        (t (sld-any-valid-past c (+ (nfix q) (sld-unit)) (1- fuel)))))
(assert-event
 (and (not (sld-any-valid-past (sld-torn) (nth 1 (sld-open (sld-torn))) 1000))
      (not (fn-lgdm-refused-p (sld-open (sld-torn))))
      (not (sld-any-valid-past (sld-seg) (nth 1 (sld-open (sld-seg))) 1000))
      (not (fn-lgdm-refused-p (sld-open (sld-seg))))
      (sld-any-valid-past (sld-flip-first) 0 1000)))

; (3) HYPOTHESIS REMOVAL for fn-lgdm-damage-lies-in-the-last-write: the
; flipped segment claimed as L = the three records' log (one batch entry)
; followed by Y = nil and zeros.  The digest, admission and zero-count
; hypotheses hold; the shape hypothesis fails; the conclusion fails.
(assert-event
 (let* ((records (list (sld-rec 1) (sld-rec 2) (sld-rec 3)))
        (l (len (fn-lg-log records *fn-lg-genesis* (sld-unit))))
        (c (sld-flip-first))
        (v (sld-open c)))
   (and (fn-frame-digestp *fn-lg-genesis*)
        (fn-lg-recordsp records (sld-max))
        (natp (- (len c) l))
        (not (equal c (append (fn-lg-log records *fn-lg-genesis* (sld-unit)) nil
                              (fn-bs-zeros (- (len c) l)))))
        (not (<= l (nth 1 v)))
        (fn-lgdm-refused-p v))))

; (1) The confirmed repair: :repaired at the stop, not refused, the quarantine
; named; (3) a repair naming another offset, or of a closed (read-only)
; segment, changes nothing.
(assert-event
 (let* ((v (sld-open (sld-flip-first)))
        (e (fn-lgdm-effective v "000001.log" "000001.log:0" t)))
   (and (fn-lgdm-repair-admitsp v "000001.log" "000001.log:0" t)
        (equal e (list :repaired 0 2 2))
        (not (fn-lgdm-refused-p e))
        (equal (fn-lgdm-quarantine-name e "000001.log") "000001.log.damaged-at-0")
        (equal (fn-lgdm-repair-text e "000001.log")
               (concatenate 'string "log repaired at=000001.log:0 dropped-valid-entries=2 dropped-records=2"
                            " (the operator's truncate: the damaged entry and every entry after it;"
                            " the segment's octets were kept first)"))
        (equal (fn-lgdm-effective v "000001.log" "000001.log:4" t) v)
        (equal (fn-lgdm-effective v "000002.log" "000001.log:0" t) v)
        (equal (fn-lgdm-effective v "000001.log" "000001.log:0" nil) v)
        (fn-lgdm-refused-p (fn-lgdm-effective v "000001.log" "000001.log:0" nil))
        (equal (fn-lgdm-effective (sld-open (sld-torn)) "000001.log" "000001.log:0" t)
               (sld-open (sld-torn))))))
