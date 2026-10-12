; Witnesses and teeth for books/store-log-buffer (the log walk over the
; entry's octet buffer: the host preads the entry into fn-octets-lg, ACL2
; decides it in place and the host walks a cursor over it, one record at a
; time).
;
; The unconditional equalities (fn-lgw-step-buf-count-is-step,
; fn-lgb-decide-count-is-decide, fn-lgb-broken-is-broken-slice,
; fn-lgb-span-records-are-the-records) have no hypothesis to remove; the
; cursor's two (fn-lgb-span-within-max, fn-lgb-descriptor-is-the-attached-
; place) carry theirs, as do the chain-field packet's two
; (fn-lg-entry-okp-holds-the-chain-field: an accepted entry; and
; fn-lgb-descriptor-of-an-accepted-record: J below COUNT), whose removals
; run on the refused 42-octet empty frame and whose tight witness is the
; 74-octet entry of one empty record.  Witnesses, all REACHABLE (the host's own loop,
; spelled over the live buffer):
;   (1) three one-record entries chained from genesis, walked by the count
;       step and the cursor and by the list step: the same records, the
;       same extent descriptors (fn-arx-attach-trailers-buffer over
;       fn-arx-list-places) and state at every step, and the run's records;
;   (2) one batch entry (kind 2, three records): the count step takes all
;       three; the cursor slices each from the length prefix; each
;       descriptor is the list walk's and addresses the record's octets in
;       the entry;
;   (3) the torn tail and the splice stop the buffer walk exactly where the
;       list walk stops, BROKEN for the splice;
;   (4) the fast path's range: every entry above is at least 74 octets and
;       max a frame bound (fn-lgb-decide-count answers them); a 60-octet
;       window and an out-of-range bound go to the list fallback and answer
;       as the list decision does (the records by their count).
; The teeth (defteeth, one per keystone) follow the assertions.
(in-package "ACL2")
(include-book "../../books/store-log-buffer")
; The record codec seam's attachment: the log's txid reads the record through
; fn-record-decode-exact (books/store-log-txid.lisp).
(include-book "../../books/codec-attach")
(include-book "../../books/defkeystone")

(defun slb-unit () (declare (xargs :guard t)) 4)
(defun slb-max () (declare (xargs :guard t)) 4096)
(defun slb-extent () (declare (xargs :guard t)) 2048)
(defun slb-rec (i) (declare (xargs :guard t :verify-guards nil)) (fn-lg-workload-record i 8))

(defun slb-pad (log)
  (declare (xargs :guard t :verify-guards nil))
  (append log (fn-bs-zeros (- (slb-extent) (len log)))))

(defun slb-t1 () (declare (xargs :guard t :verify-guards nil))
  (fn-lg-last-trailer (list (slb-rec 1)) *fn-lg-genesis*))
(defun slb-t2 () (declare (xargs :guard t :verify-guards nil))
  (fn-lg-last-trailer (list (slb-rec 2)) (slb-t1)))
(defun slb-log3 () (declare (xargs :guard t :verify-guards nil))
  (append (fn-lg-log (list (slb-rec 1)) *fn-lg-genesis* (slb-unit))
          (fn-lg-log (list (slb-rec 2)) (slb-t1) (slb-unit))
          (fn-lg-log (list (slb-rec 3)) (slb-t2) (slb-unit))))
(defun slb-seg () (declare (xargs :guard t :verify-guards nil)) (slb-pad (slb-log3)))
(defun slb-batch () (declare (xargs :guard t :verify-guards nil))
  (slb-pad (fn-lg-log (list (slb-rec 1) (slb-rec 2) (slb-rec 3)) *fn-lg-genesis* (slb-unit))))
(defun slb-torn () (declare (xargs :guard t :verify-guards nil))
  (let ((l (slb-log3)))
    (slb-pad (append (fn-bs-take (- (len l) 8) l) (fn-bs-zeros 8)))))
(defun slb-splice () (declare (xargs :guard t :verify-guards nil))
  (slb-pad (append (fn-lg-log (list (slb-rec 1)) *fn-lg-genesis* (slb-unit))
                   (fn-lg-log (list (slb-rec 2))
                              (fn-lg-last-trailer (list (slb-rec 7)) *fn-lg-genesis*)
                              (slb-unit)))))

; The host's loop (host/native/io.lisp fnn-log-stream-segment): the header
; window, the entry length, the entry's octets into the buffer (none: an
; empty buffer), the count step, then COUNT times the cursor from 42
; (fn-lgb-span, fn-lgb-slice, and in the extent mode fn-lgb-descriptor).
; Beside it, the list step and fn-arx-attach-trailers-buffer over
; fn-arx-list-places on the same window; SAME is whether every step agreed.
(defun slb-cut (k i pos fn-octets-lg)
  (declare (xargs :stobjs fn-octets-lg :guard t :verify-guards nil :measure (nfix k)))
  (if (zp k)
      (mv nil nil)
    (mv-let (start len i2) (fn-lgb-span i fn-octets-lg)
      (let ((record (fn-lgb-slice start len fn-octets-lg))
            (desc (fn-lgb-descriptor pos start len fn-octets-lg)))
        (mv-let (records descs) (slb-cut (1- k) i2 pos fn-octets-lg)
          (mv (cons record records) (cons desc descs)))))))

(defun slb-walk (c st fuel acc descs same fn-octets-lg)
  (declare (xargs :stobjs fn-octets-lg :guard t :verify-guards nil :measure (nfix fuel)))
  (if (or (zp fuel) (fn-lgw-stop st))
      (mv (reverse acc) (reverse descs) same st fn-octets-lg)
    (let* ((pos (fn-lgw-pos st))
           (h (fn-bs-take (fn-lgw-header-len st (len c)) (nthcdr pos c)))
           (n (fn-lgw-entry-len h st (len c)))
           (e (and n (fn-bs-take n (nthcdr pos c))))
           (fn-octets-lg (fn-octets-lg-from-list e fn-octets-lg)))
      (mv-let (took count st2) (fn-lgw-step-buf-count st (slb-unit) (slb-max) (len c) fn-octets-lg)
        (mv-let (ltook lrecords lst2) (fn-lgw-step e st (slb-unit) (slb-max) (len c))
          (mv-let (records ds) (if took (slb-cut count 42 pos fn-octets-lg) (mv nil nil))
            (let* ((lds (and ltook
                             (fn-arx-attach-trailers-buffer
                              (fn-arx-list-places e pos (len lrecords) (slb-unit) 0 0 nil 0 0 nil)
                              pos fn-octets-lg)))
                   (same (and same (equal took ltook) (equal count (len lrecords))
                              (equal records lrecords) (equal st2 lst2) (equal ds lds)
                              (or (not n) (<= *fn-lgb-min* n)))))
              (slb-walk c st2 (1- fuel) (revappend records acc)
                        (revappend ds descs) same fn-octets-lg))))))))

; (1) Three one-record entries.
(assert-event
 (mv-let (records descs same st fn-octets-lg)
   (slb-walk (slb-seg) (fn-lgw-start *fn-lg-genesis* 1) 100 nil nil t fn-octets-lg)
   (mv (and same
            (equal records (list (slb-rec 1) (slb-rec 2) (slb-rec 3)))
            (equal (len descs) 3)
            (not (member nil descs))
            (mv-let (lrecords lst) (fn-lgw-run (slb-seg) (fn-lgw-start *fn-lg-genesis* 1)
                                               (slb-unit) (slb-max))
              (and (equal records lrecords) (equal st lst)))
            (equal (fn-lgw-count st) 3)
            (equal (fn-lgw-next st) 4)
            (fn-lgw-stop st)
            (not (fn-lgw-broken st)))
       fn-octets-lg))
 :stobjs-out '(nil fn-octets-lg))

; (2) One batch entry: three records by the cursor over the length-prefixed
; windows; each descriptor (POS N START LEN, the trailer attached) addresses
; its record's octets in the segment.
(defun slb-at (c place)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-take (nth 3 place) (nthcdr (nth 2 place) c)))

(assert-event
 (mv-let (records descs same st fn-octets-lg)
   (slb-walk (slb-batch) (fn-lgw-start *fn-lg-genesis* 1) 100 nil nil t fn-octets-lg)
   (mv (and same
            (equal records (list (slb-rec 1) (slb-rec 2) (slb-rec 3)))
            (equal (len descs) 3)
            (equal (slb-at (slb-batch) (nth 0 descs)) (slb-rec 1))
            (equal (slb-at (slb-batch) (nth 1 descs)) (slb-rec 2))
            (equal (slb-at (slb-batch) (nth 2 descs)) (slb-rec 3))
            (equal (fn-lgw-count st) 3)
            (fn-lgw-stop st)
            (not (fn-lgw-broken st)))
       fn-octets-lg))
 :stobjs-out '(nil fn-octets-lg))

; (3) The torn tail: two records, not broken.  The splice: one record, BROKEN.
(assert-event
 (mv-let (records descs same st fn-octets-lg)
   (slb-walk (slb-torn) (fn-lgw-start *fn-lg-genesis* 1) 100 nil nil t fn-octets-lg)
   (declare (ignore descs))
   (mv (and same
            (equal records (list (slb-rec 1) (slb-rec 2)))
            (fn-lgw-stop st)
            (not (fn-lgw-broken st)))
       fn-octets-lg))
 :stobjs-out '(nil fn-octets-lg))

(assert-event
 (mv-let (records descs same st fn-octets-lg)
   (slb-walk (slb-splice) (fn-lgw-start *fn-lg-genesis* 1) 100 nil nil t fn-octets-lg)
   (declare (ignore descs))
   (mv (and same
            (equal records (list (slb-rec 1)))
            (fn-lgw-stop st)
            (equal (fn-lgw-broken st) t))
       fn-octets-lg))
 :stobjs-out '(nil fn-octets-lg))

; (4) The fast path answers the first entry of the batch segment; a 60-octet
; window and a bound past the frame grammar's go to the list fallback, and
; every answer is the list decision's, its records by their count.
(defun slb-decide-count (e prev max)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (ok records) (fn-lgw-decide e prev max)
    (list ok (len records))))

(assert-event
 (let* ((c (slb-batch))
        (n (fn-lgw-entry-len (fn-bs-take 10 c) (fn-lgw-start *fn-lg-genesis* 1) (len c)))
        (e (fn-bs-take n c))
        (fn-octets-lg (fn-octets-lg-from-list e fn-octets-lg)))
   (mv (and (<= *fn-lgb-min* n)
            (equal (mv-list 2 (fn-lgb-decide-count *fn-lg-genesis* (slb-max) fn-octets-lg))
                   (slb-decide-count e *fn-lg-genesis* (slb-max)))
            (equal (mv-list 2 (fn-lgb-decide-count *fn-lg-genesis* (slb-max) fn-octets-lg))
                   (list t 3))
            (equal (mv-list 2 (fn-lgb-decide-count *fn-lg-genesis* (+ 1 *fn-frame-max-payload*)
                                                   fn-octets-lg))
                   (slb-decide-count e *fn-lg-genesis* (+ 1 *fn-frame-max-payload*)))
            ;; a wrong predecessor: refused before the digest, as the list refuses
            (equal (mv-list 2 (fn-lgb-decide-count (slb-t1) (slb-max) fn-octets-lg))
                   (slb-decide-count e (slb-t1) (slb-max)))
            (equal (mv-list 2 (fn-lgb-decide-count (slb-t1) (slb-max) fn-octets-lg))
                   (list nil 0))
            ;; the refusal's classification: a wrong predecessor is the splice
            (equal (fn-lgb-broken (slb-t1) (slb-max) fn-octets-lg)
                   (fn-lgw-broken-slice-p e (slb-t1) (slb-max))))
       fn-octets-lg))
 :stobjs-out '(nil fn-octets-lg))

(assert-event
 (let* ((e (fn-bs-take 60 (slb-batch)))
        (fn-octets-lg (fn-octets-lg-from-list e fn-octets-lg)))
   (mv (and (equal (mv-list 2 (fn-lgb-decide-count *fn-lg-genesis* (slb-max) fn-octets-lg))
                   (slb-decide-count e *fn-lg-genesis* (slb-max)))
            (equal (mv-list 2 (fn-lgb-decide-count *fn-lg-genesis* (slb-max) fn-octets-lg))
                   (list nil 0)))
       fn-octets-lg))
 :stobjs-out '(nil fn-octets-lg))

(assert-event
 (and (eq (symbol-class 'fn-lgw-step-buf-count (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-lgb-span (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-lgb-slice (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-lgb-descriptor (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-lgb-decide-count (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-lgb-broken (w state)) :common-lisp-compliant)))

; -----------------------------------------------------------------------------
; The teeth (books/defkeystone.lisp; docs/proof-style.md section 5).  The
; claims mention the stobj variable fn-octets, so each is stated with a local
; fn-octets built from the witness's BUFFER (:stobjs) and a native checker
; per conjunct (:stobj-checks), proved equal to the claim's term before any
; witness runs.  The sealed one-record entry is (fn-lg-frame genesis ((7)))
; (75 octets, kind 1); the batch is the three workload records, kind 2.
(defun slbt-one () (declare (xargs :guard t :verify-guards nil))
  (fn-lg-frame *fn-lg-genesis* (list (list 7))))
(defun slbt-batch3 () (declare (xargs :guard t :verify-guards nil))
  (fn-lg-frame *fn-lg-genesis* (list (slb-rec 1) (slb-rec 2) (slb-rec 3))))
; 75 zero octets with kind 1 and a declared payload of 33: no digest holds.
(defun slbt-b75 () (declare (xargs :guard t :verify-guards nil))
  (update-nth 9 33 (update-nth 5 1 (fn-bs-zeros 75))))
; The 42-octet frame with an empty payload, below the chain field: refused
; since LOG-DECIDE-SHORT-CHAIN-FIELD (it decided one empty record before).
(defun slbt-empty () (declare (xargs :guard t :verify-guards nil))
  (fn-frame-seal *fn-lg-magic* *fn-lg-version* 1 nil))

; Keystone fn-lgw-step-buf-count-is-step.
(defun slbt1-check (i st unit max extent fn-octets)
  (declare (xargs :stobjs fn-octets :guard t :verify-guards nil))
  (mv (mv-let (took records st2) (fn-lgw-step (fn-octets-list fn-octets) st unit max extent)
        (let ((counted (if (equal i 0)
                           (len records)
                         (fn-lgb-count 42 (- (fn-octets-len fn-octets) 32) fn-octets))))
          (equal (mv-list 3 (fn-lgw-step-buf-count st unit max extent fn-octets))
                 (list took counted st2))))
      fn-octets))

(defteeth fn-lgw-step-buf-count-is-step
  :claim (()
          (equal (fn-lgw-step-buf-count st unit max extent fn-octets)
                 (mv-let (took records st2) (fn-lgw-step fn-octets st unit max extent)
                   (mv took (len records) st2))))
  :subject fn-lgw-step-buf-count
  :witness ((st (fn-lgw-start *fn-lg-genesis* 1)) (unit 4) (max 33) (extent 2048)
            (buffer (slbt-one)))
  :stobjs ((fn-octets (fn-octets-from-list buffer fn-octets)))
  :stobj-checks
  (((equal (fn-lgw-step-buf-count st unit max extent fn-octets)
           (mv-let (took records st2) (fn-lgw-step fn-octets st unit max extent)
             (mv took (len records) st2)))
    (slbt1-check 0 st unit max extent fn-octets)
    :hints (("Goal" :in-theory (union-theories '(slbt1-check mv-list fn-oct-list-is-identity)
                                               (theory 'minimal-theory)))))
   ((equal (fn-lgw-step-buf-count st unit max extent fn-octets)
           (mv-let (took records st2) (fn-lgw-step fn-octets st unit max extent)
             (declare (ignore records))
             (mv took (fn-lgb-count 42 (- (len fn-octets) 32) fn-octets) st2)))
    (slbt1-check 1 st unit max extent fn-octets)
    :hints (("Goal" :in-theory (union-theories '(slbt1-check mv-list fn-oct-list-is-identity
                                                 fn-oct-len-is-len)
                                               (theory 'minimal-theory))))))
  :breaks ()
  :mutations ((count-from-the-record-prefix
               (:conclusion
                (equal (fn-lgw-step-buf-count st unit max extent fn-octets)
                       (mv-let (took records st2) (fn-lgw-step fn-octets st unit max extent)
                         (declare (ignore records))
                         (mv took (fn-lgb-count 42 (- (len fn-octets) 32) fn-octets) st2))))
               ()
               :fault "the step counts u32 prefixes in a single-record entry")))

; Keystone fn-lgb-decide-count-is-decide.
(defun slbt3-check (i prev max fn-octets)
  (declare (xargs :stobjs fn-octets :guard t :verify-guards nil))
  (mv (case i
        (0 (equal (mv-list 2 (fn-lgb-decide-count prev max fn-octets))
                  (mv-let (ok records) (fn-lgw-decide (fn-octets-list fn-octets) prev max)
                    (list ok (len records)))))
        (otherwise
         (equal (mv-list 2 (fn-lgb-decide-count prev max fn-octets))
                (mv-let (ok records) (fn-lgw-decide (fn-octets-list fn-octets) prev max)
                  (declare (ignore records))
                  (list ok (fn-lgb-count 42 (- (fn-octets-len fn-octets) 32) fn-octets))))))
      fn-octets))

(defteeth fn-lgb-decide-count-is-decide
  :claim (()
          (equal (fn-lgb-decide-count prev max fn-octets)
                 (mv-let (ok records) (fn-lgw-decide fn-octets prev max)
                   (mv ok (len records)))))
  :subject fn-lgb-decide-count
  :witness ((prev *fn-lg-genesis*) (max 33) (buffer (slbt-one)))
  :stobjs ((fn-octets (fn-octets-from-list buffer fn-octets)))
  :stobj-checks
  (((equal (fn-lgb-decide-count prev max fn-octets)
           (mv-let (ok records) (fn-lgw-decide fn-octets prev max)
             (mv ok (len records))))
    (slbt3-check 0 prev max fn-octets)
    :hints (("Goal" :in-theory (union-theories '(slbt3-check mv-list fn-oct-list-is-identity)
                                               (theory 'minimal-theory)))))
   ((equal (fn-lgb-decide-count prev max fn-octets)
           (mv (mv-nth 0 (fn-lgw-decide fn-octets prev max))
               (fn-lgb-count 42 (- (len fn-octets) 32) fn-octets)))
    (slbt3-check 1 prev max fn-octets)
    :hints (("Goal" :in-theory (union-theories '(slbt3-check mv-list fn-oct-list-is-identity fn-oct-len-is-len)
                                               (theory 'minimal-theory))))))
  :breaks ()
  :mutations ((count-from-the-record-prefix
               (:conclusion (equal (fn-lgb-decide-count prev max fn-octets)
                                   (mv (mv-nth 0 (fn-lgw-decide fn-octets prev max))
                                       (fn-lgb-count 42 (- (len fn-octets) 32) fn-octets))))
               ()
               :fault "the step counts u32 prefixes in a single-record entry")))

; Keystone fn-lgb-broken-is-broken-slice.
(defun slbt4-check (i last max fn-octets)
  (declare (xargs :stobjs fn-octets :guard t :verify-guards nil))
  (mv (equal (fn-lgb-broken last max fn-octets)
             (if (equal i 0)
                 (fn-lgw-broken-slice-p (fn-octets-list fn-octets) last max)
               (and (fn-lg-entry-okp (fn-octets-list fn-octets)
                                     (fn-lgs-claimed-prev (fn-octets-list fn-octets) max)
                                     max)
                    t)))
      fn-octets))

(defteeth fn-lgb-broken-is-broken-slice
  :claim (()
          (equal (fn-lgb-broken last max fn-octets)
                 (fn-lgw-broken-slice-p fn-octets last max)))
  :subject fn-lgb-broken
  :witness ((last *fn-lg-genesis*) (max 33) (buffer (slbt-one)))
  :stobjs ((fn-octets (fn-octets-from-list buffer fn-octets)))
  :stobj-checks
  (((equal (fn-lgb-broken last max fn-octets)
           (fn-lgw-broken-slice-p fn-octets last max))
    (slbt4-check 0 last max fn-octets)
    :hints (("Goal" :in-theory (union-theories '(slbt4-check fn-oct-list-is-identity (:type-prescription fn-lg-entry-okp))
                                               (theory 'minimal-theory)))))
   ((equal (fn-lgb-broken last max fn-octets)
           (and (fn-lg-entry-okp fn-octets (fn-lgs-claimed-prev fn-octets max) max) t))
    (slbt4-check 1 last max fn-octets)
    :hints (("Goal" :in-theory (union-theories '(slbt4-check fn-oct-list-is-identity (:type-prescription fn-lg-entry-okp))
                                               (theory 'minimal-theory))))))
  :breaks ()
  :mutations ((broken-without-the-chain-compare
               (:conclusion
                (equal (fn-lgb-broken last max fn-octets)
                       (and (fn-lg-entry-okp fn-octets (fn-lgs-claimed-prev fn-octets max) max) t)))
               ()
               :fault "every self-validating entry is classified broken")))

; Keystone fn-lgb-span-records-are-the-records.
; The mutant's cursor: each record taken as the window [I, END), I the
; cursor at the record's length prefix, END the trailer's start.
(defun slbt-windows (k i fn-octets)
  (declare (xargs :stobjs fn-octets :guard (natp i) :verify-guards nil :measure (nfix k)))
  (if (zp k)
      nil
    (mv-let (start len next) (fn-lgb-span i fn-octets)
      (declare (ignore start len))
      (cons (fn-lgb-slice-acc (nfix i) (nfix (- (fn-octets-len fn-octets) 32)) nil fn-octets)
            (slbt-windows (1- k) next fn-octets)))))

(defun slbt5-check (i prev max fn-octets)
  (declare (xargs :stobjs fn-octets :guard t :verify-guards nil))
  (mv-let (ok k) (fn-lgb-decide-count prev max fn-octets)
    (declare (ignore ok))
    (mv-let (ok2 records) (fn-lgw-decide (fn-octets-list fn-octets) prev max)
      (declare (ignore ok2))
      (mv (equal (if (equal i 0)
                     (fn-lgb-span-records k 42 fn-octets)
                   (slbt-windows k 42 fn-octets))
                 records)
          fn-octets))))

(defteeth fn-lgb-span-records-are-the-records
  :claim (()
          (equal (fn-lgb-span-records (mv-nth 1 (fn-lgb-decide-count prev max fn-octets)) 42 fn-octets)
                 (mv-nth 1 (fn-lgw-decide fn-octets prev max))))
  :subject fn-lgb-span
  :witness ((prev *fn-lg-genesis*) (max 4096) (buffer (slbt-batch3)))
  :stobjs ((fn-octets (fn-octets-from-list buffer fn-octets)))
  :stobj-checks
  (((equal (fn-lgb-span-records (mv-nth 1 (fn-lgb-decide-count prev max fn-octets)) 42 fn-octets)
           (mv-nth 1 (fn-lgw-decide fn-octets prev max)))
    (slbt5-check 0 prev max fn-octets)
    :hints (("Goal" :in-theory (union-theories '(slbt5-check fn-oct-list-is-identity)
                                               (theory 'minimal-theory)))))
   ((equal (slbt-windows (mv-nth 1 (fn-lgb-decide-count prev max fn-octets)) 42 fn-octets)
           (mv-nth 1 (fn-lgw-decide fn-octets prev max)))
    (slbt5-check 1 prev max fn-octets)
    :hints (("Goal" :in-theory (union-theories '(slbt5-check fn-oct-list-is-identity)
                                               (theory 'minimal-theory))))))
  :breaks ()
  :mutations ((batch-window-includes-the-prefix
               (:conclusion
                (equal (slbt-windows (mv-nth 1 (fn-lgb-decide-count prev max fn-octets)) 42 fn-octets)
                       (mv-nth 1 (fn-lgw-decide fn-octets prev max))))
               ()
               :fault "the cursor slices from the length prefix to the trailer")))

; The tight accepted entry: one empty record under genesis, 74 octets
; (header 10, chain field 32, trailer 32).
(defun slbt-e74 () (declare (xargs :guard t :verify-guards nil))
  (fn-lg-frame *fn-lg-genesis* (list nil)))

; Keystone fn-lg-entry-okp-holds-the-chain-field (C1).
(defteeth fn-lg-entry-okp-holds-the-chain-field
  :claim (((okp (fn-lg-entry-okp e prev max)))
          (<= 74 (len e)))
  :subject fn-lg-entry-okp
  :witness ((e (slbt-e74)) (prev *fn-lg-genesis*) (max 4096))
  :breaks ((okp ((e (slbt-empty)))))
  :mutations ((floor-one-octet-high
               (:conclusion (<= 75 (len e)))
               ()
               :fault "the floor counts a record octet the empty record does not have")))

; Keystone fn-lgb-span-within-max.
(defun slbt6-check (i j prev max fn-octets)
  (declare (xargs :stobjs fn-octets :guard t :verify-guards nil))
  (mv (if (equal i 0)
          (mv-let (ok k) (fn-lgb-decide-count prev max fn-octets)
            (declare (ignore ok))
            (< (nfix j) k))
        (mv-let (start len next) (fn-lgb-span (fn-lgb-span-cursor j 42 fn-octets) fn-octets)
          (declare (ignore start next))
          (if (equal i 1) (<= (+ 32 len) (nfix max)) (<= (+ 32 len) (1- max)))))
      fn-octets))

(defteeth fn-lgb-span-within-max
  :claim (((below-count (< (nfix j) (mv-nth 1 (fn-lgb-decide-count prev max fn-octets)))))
          (<= (+ 32 (mv-nth 1 (fn-lgb-span (fn-lgb-span-cursor j 42 fn-octets) fn-octets)))
              (nfix max)))
  :subject fn-lgb-span
  :witness ((prev *fn-lg-genesis*) (max 4096) (j 1) (buffer (slbt-batch3)))
  :stobjs ((fn-octets (fn-octets-from-list buffer fn-octets)))
  :stobj-checks
  (((< (nfix j) (mv-nth 1 (fn-lgb-decide-count prev max fn-octets)))
    (slbt6-check 0 j prev max fn-octets)
    :hints (("Goal" :in-theory (union-theories '(slbt6-check) (theory 'minimal-theory)))))
   ((<= (+ 32 (mv-nth 1 (fn-lgb-span (fn-lgb-span-cursor j 42 fn-octets) fn-octets)))
        (nfix max))
    (slbt6-check 1 j prev max fn-octets)
    :hints (("Goal" :in-theory (union-theories '(slbt6-check) (theory 'minimal-theory)))))
   ((<= (+ 32 (mv-nth 1 (fn-lgb-span (fn-lgb-span-cursor j 42 fn-octets) fn-octets)))
        (1- max))
    (slbt6-check 2 j prev max fn-octets)
    :hints (("Goal" :in-theory (union-theories '(slbt6-check) (theory 'minimal-theory))))))
  :breaks ((below-count ((prev nil) (max 0) (j 0) (buffer (slbt-b75)))))
  :mutations ((bound-one-below-max
               (:conclusion
                (<= (+ 32 (mv-nth 1 (fn-lgb-span (fn-lgb-span-cursor j 42 fn-octets) fn-octets)))
                    (1- max)))
               ((prev *fn-lg-genesis*) (max 33) (j 0) (buffer (slbt-one)))
               :fault "the hold charged one octet short (the tight record: 32 + 1 = MAX 33)")))

; Keystone fn-lgb-descriptor-is-the-attached-place.
(defun slbt7-check (i pos j unit prev max fn-octets)
  (declare (xargs :stobjs fn-octets :guard t :verify-guards nil))
  (mv (if (equal i 0)
          (mv-let (ok k) (fn-lgb-decide-count prev max fn-octets)
            (declare (ignore ok))
            (< (nfix j) k))
        (mv-let (ok k) (fn-lgb-decide-count prev max fn-octets)
          (declare (ignore ok))
          (mv-let (start len next) (fn-lgb-span (fn-lgb-span-cursor j 42 fn-octets) fn-octets)
            (declare (ignore next))
            (equal (nth j (fn-arx-attach-trailers-buffer
                           (fn-arx-list-places (fn-octets-list fn-octets) pos k unit 0 0 nil 0 0 nil)
                           pos fn-octets))
                   (if (equal i 2)
                       (fn-lgb-descriptor pos start len fn-octets)
                     (update-nth 1 len (fn-lgb-descriptor pos start len fn-octets)))))))
      fn-octets))

(defteeth fn-lgb-descriptor-is-the-attached-place
  :claim (((pos (natp pos))
           (below-count (< (nfix j) (mv-nth 1 (fn-lgb-decide-count prev max fn-octets)))))
          (equal (nth j (fn-arx-attach-trailers-buffer
                         (fn-arx-list-places fn-octets pos
                                             (mv-nth 1 (fn-lgb-decide-count prev max fn-octets))
                                             unit 0 0 nil 0 0 nil)
                         pos fn-octets))
                 (mv-let (start len next) (fn-lgb-span (fn-lgb-span-cursor j 42 fn-octets)
                                                       fn-octets)
                   (declare (ignore next))
                   (fn-lgb-descriptor pos start len fn-octets))))
  :subject fn-lgb-descriptor
  :witness ((pos 0) (j 1) (unit 4) (prev *fn-lg-genesis*) (max 4096) (buffer (slbt-batch3)))
  :stobjs ((fn-octets (fn-octets-from-list buffer fn-octets)))
  :stobj-checks
  (((< (nfix j) (mv-nth 1 (fn-lgb-decide-count prev max fn-octets)))
    (slbt7-check 0 pos j unit prev max fn-octets)
    :hints (("Goal" :in-theory (union-theories '(slbt7-check) (theory 'minimal-theory)))))
   ((equal (nth j (fn-arx-attach-trailers-buffer
                   (fn-arx-list-places fn-octets pos
                                       (mv-nth 1 (fn-lgb-decide-count prev max fn-octets))
                                       unit 0 0 nil 0 0 nil)
                   pos fn-octets))
           (mv-let (start len next) (fn-lgb-span (fn-lgb-span-cursor j 42 fn-octets)
                                                 fn-octets)
             (declare (ignore next))
             (fn-lgb-descriptor pos start len fn-octets)))
    (slbt7-check 2 pos j unit prev max fn-octets)
    :hints (("Goal" :in-theory (union-theories '(slbt7-check fn-oct-list-is-identity) (theory 'minimal-theory)))))
   ((equal (nth j (fn-arx-attach-trailers-buffer
                   (fn-arx-list-places fn-octets pos
                                       (mv-nth 1 (fn-lgb-decide-count prev max fn-octets))
                                       unit 0 0 nil 0 0 nil)
                   pos fn-octets))
           (mv-let (start len next) (fn-lgb-span (fn-lgb-span-cursor j 42 fn-octets)
                                                 fn-octets)
             (declare (ignore next))
             (update-nth 1 len (fn-lgb-descriptor pos start len fn-octets))))
    (slbt7-check 3 pos j unit prev max fn-octets)
    :hints (("Goal" :in-theory (union-theories '(slbt7-check fn-oct-list-is-identity) (theory 'minimal-theory))))))
  :breaks ((below-count ((buffer (slbt-b75)) (prev nil) (max 0) (j 0)))
           (pos ((buffer (slbt-one)) (max 33) (j 0) (pos -4))
                :logical "a negative position is outside the descriptor's guard (natp pos)"))
  :mutations ((descriptor-length-is-the-record
               (:conclusion
                (equal (nth j (fn-arx-attach-trailers-buffer
                               (fn-arx-list-places fn-octets pos
                                                   (mv-nth 1 (fn-lgb-decide-count prev max fn-octets))
                                                   unit 0 0 nil 0 0 nil)
                               pos fn-octets))
                       (mv-let (start len next) (fn-lgb-span (fn-lgb-span-cursor j 42 fn-octets)
                                                             fn-octets)
                         (declare (ignore next))
                         (update-nth 1 len (fn-lgb-descriptor pos start len fn-octets)))))
               ((buffer (slbt-one)) (max 33) (j 0))
               :fault "the extent descriptor names the record, not the entry")))

; Keystone fn-lgb-descriptor-of-an-accepted-record (C4).  The conclusion
; reads only the entry's header, so the below-count removal's witness is the
; refused 42-octet frame; the mutation adds that the record is non-empty,
; false at the tight 74-octet entry.
(defun slbt8-check (i pos j prev max fn-octets)
  (declare (xargs :stobjs fn-octets :guard t :verify-guards nil))
  (mv (if (equal i 0)
          (mv-let (ok k) (fn-lgb-decide-count prev max fn-octets)
            (declare (ignore ok))
            (< (nfix j) k))
        (mv-let (start len next) (fn-lgb-span (fn-lgb-span-cursor j 42 fn-octets) fn-octets)
          (declare (ignore next))
          (if (equal i 1)
              (consp (fn-lgb-descriptor pos start len fn-octets))
            (and (consp (fn-lgb-descriptor pos start len fn-octets)) (< 0 len)))))
      fn-octets))

(defteeth fn-lgb-descriptor-of-an-accepted-record
  :claim (((below-count (< (nfix j) (mv-nth 1 (fn-lgb-decide-count prev max fn-octets)))))
          (mv-let (start len next) (fn-lgb-span (fn-lgb-span-cursor j 42 fn-octets) fn-octets)
            (declare (ignore next))
            (consp (fn-lgb-descriptor pos start len fn-octets))))
  :subject fn-lgb-descriptor
  :witness ((pos 0) (j 0) (prev *fn-lg-genesis*) (max 4096) (buffer (slbt-e74)))
  :stobjs ((fn-octets (fn-octets-from-list buffer fn-octets)))
  :stobj-checks
  (((< (nfix j) (mv-nth 1 (fn-lgb-decide-count prev max fn-octets)))
    (slbt8-check 0 pos j prev max fn-octets)
    :hints (("Goal" :in-theory (union-theories '(slbt8-check) (theory 'minimal-theory)))))
   ((mv-let (start len next) (fn-lgb-span (fn-lgb-span-cursor j 42 fn-octets) fn-octets)
      (declare (ignore next))
      (consp (fn-lgb-descriptor pos start len fn-octets)))
    (slbt8-check 1 pos j prev max fn-octets)
    :hints (("Goal" :in-theory (union-theories '(slbt8-check) (theory 'minimal-theory)))))
   ((mv-let (start len next) (fn-lgb-span (fn-lgb-span-cursor j 42 fn-octets) fn-octets)
      (declare (ignore next))
      (and (consp (fn-lgb-descriptor pos start len fn-octets)) (< 0 len)))
    (slbt8-check 2 pos j prev max fn-octets)
    :hints (("Goal" :in-theory (union-theories '(slbt8-check) (theory 'minimal-theory))))))
  :breaks ((below-count ((buffer (slbt-empty)))))
  :mutations ((every-record-is-non-empty
               (:conclusion
                (mv-let (start len next) (fn-lgb-span (fn-lgb-span-cursor j 42 fn-octets) fn-octets)
                  (declare (ignore next))
                  (and (consp (fn-lgb-descriptor pos start len fn-octets)) (< 0 len))))
               ()
               :fault "the host takes a zero-length span for no record (the 74-octet entry)")))

; The positive witnesses of the cursor's two conditional keystones at every
; record of an accepted entry (J below COUNT, POS 0): the batch's three
; records, and the one-record entry's.
(defun slbt-js (j max fn-octets)
  (declare (xargs :stobjs fn-octets :guard t :verify-guards nil :measure (nfix j)))
  (if (zp j)
      (mv t fn-octets)
    (mv-let (hyp6 fn-octets) (slbt6-check 0 (1- j) *fn-lg-genesis* max fn-octets)
      (mv-let (concl6 fn-octets) (slbt6-check 1 (1- j) *fn-lg-genesis* max fn-octets)
        (mv-let (hyp7 fn-octets) (slbt7-check 0 0 (1- j) 4 *fn-lg-genesis* max fn-octets)
          (mv-let (concl7 fn-octets) (slbt7-check 2 0 (1- j) 4 *fn-lg-genesis* max fn-octets)
            (mv-let (rest fn-octets) (slbt-js (1- j) max fn-octets)
              (mv (and hyp6 concl6 hyp7 concl7 rest) fn-octets))))))))

(defun slbt-js-run (buffer max n)
  (declare (xargs :guard t :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (ok fn-octets)
      (let ((fn-octets (fn-octets-from-list buffer fn-octets)))
        (slbt-js n max fn-octets))
      ok)))

(assert-event (and (slbt-js-run (slbt-batch3) 4096 3)
                   (slbt-js-run (slbt-one) 33 1)))

(defteeth-check (fn-lgw-step-buf-count-is-step fn-lgb-decide-count-is-decide
                  fn-lgb-broken-is-broken-slice fn-lgb-span-records-are-the-records
                  fn-lgb-span-within-max fn-lgb-descriptor-is-the-attached-place
                  fn-lg-entry-okp-holds-the-chain-field fn-lgb-descriptor-of-an-accepted-record))

; Fused subject: NR-S2, NR-CUR, NR-S4, NR-S5, NR-C4.
; Every witness buffer is a live fn-octets.
(defun slbnr-claims (j pos extentp prev max unit fn-octets)
  (declare (xargs :stobjs fn-octets :guard t :verify-guards nil))
  (mv-let (ok k) (fn-lgb-decide-count prev max fn-octets)
    (mv-let (record desc next)
      (fn-lgb-next-record (fn-lgb-span-cursor j 42 fn-octets) pos extentp fn-octets)
      (list ok k
            (< (nfix j) k)
            (equal record (mv-let (took records) (fn-lgw-decide (fn-octets-list fn-octets) prev max)
                            (declare (ignore took)) (nth j records)))
            (equal next (fn-lgb-span-cursor (+ 1 (nfix j)) 42 fn-octets))
            (<= (+ 32 (len record)) (nfix max))
            (equal desc (nth j (fn-arx-attach-trailers-buffer
                               (fn-arx-list-places (fn-octets-list fn-octets) pos k unit 0 0 nil 0 0 nil)
                               pos fn-octets)))
            (consp desc)
            (if extentp (consp desc) (equal desc nil))))))

; Whole antecedents/conclusions for NR-S2, NR-CUR, NR-S4 and the
; EXTENTP=T NR-S5/NR-C4, plus the NIL descriptor in EXTENTP=NIL mode.
(with-guard-checking-event
 :all
 (assert-event
  (let ((fn-octets (fn-octets-from-list (slbt-batch3) fn-octets)))
    (mv (and
         (equal (slbnr-claims 0 17 t *fn-lg-genesis* 4096 4 fn-octets) '(t 3 t t t t t t t))
         (equal (slbnr-claims 1 17 t *fn-lg-genesis* 4096 4 fn-octets) '(t 3 t t t t t t t))
         (equal (slbnr-claims 2 17 t *fn-lg-genesis* 4096 4 fn-octets) '(t 3 t t t t t t t))
         (equal (slbnr-claims 0 17 nil *fn-lg-genesis* 4096 4 fn-octets) '(t 3 t t t t nil nil t))
         (equal (slbnr-claims 1 17 nil *fn-lg-genesis* 4096 4 fn-octets) '(t 3 t t t t nil nil t))
         (equal (slbnr-claims 2 17 nil *fn-lg-genesis* 4096 4 fn-octets) '(t 3 t t t t nil nil t)))
        fn-octets))
  :stobjs-out '(nil fn-octets)))

; Count removals for NR-S2, NR-S4 and NR-S5: refused kind-1 frame.
(with-guard-checking-event
 :none
 (assert-event
  (let ((fn-octets (fn-octets-from-list (slbt-b75) fn-octets)))
    (mv (equal (slbnr-claims 0 17 t nil 0 4 fn-octets) '(nil 0 nil nil t nil nil t t))
        fn-octets))
  :stobjs-out '(nil fn-octets)))

; Count removal for NR-C4: refused frame below the chain-field floor.
(with-guard-checking-event
 :none
 (assert-event
  (let ((fn-octets (fn-octets-from-list (slbt-empty) fn-octets)))
    (mv (equal (slbnr-claims 0 17 t *fn-lg-genesis* 4096 4 fn-octets)
               '(nil 0 nil t t t t nil nil))
        fn-octets))
  :stobjs-out '(nil fn-octets)))

; POS removal for NR-S5: all other hypotheses hold, but the places walk
; fixes POS and the descriptor retains the negative offset (logical input).
(with-guard-checking-event
 :none
 (assert-event
  (let ((fn-octets (fn-octets-from-list (slbt-batch3) fn-octets)))
    (mv (equal (slbnr-claims 0 -4 t *fn-lg-genesis* 4096 4 fn-octets)
               '(t 3 t t t t nil t t))
        fn-octets))
  :stobjs-out '(nil fn-octets)))

; EXTENTP removals for NR-S5 and NR-C4 are exactly the three NIL-mode
; calls in the positive trace: count/POS hold and both conclusions fail.

; Mutants of the fused answer, each checked with a satisfiable antecedent.
; S2 batch-window-includes-the-prefix; CUR next-one-too-far;
; S4 bound-one-below-max; S5 descriptor-length-is-the-record;
; C4 every-record-is-non-empty (the original mutation labels).
(with-guard-checking-event
 :all
 (assert-event
  (let ((fn-octets (fn-octets-from-list (slbt-batch3) fn-octets)))
    (mv (mv-let (ok k) (fn-lgb-decide-count *fn-lg-genesis* 4096 fn-octets)
          (mv-let (start len next) (fn-lgb-span 42 fn-octets)
            (declare (ignore next))
            (mv-let (record desc i2) (fn-lgb-next-record 42 17 t fn-octets)
              (and ok (equal k 3) (natp 17)
                   ; S2 mutant copies the length prefix with the record.
                   (not (equal record (fn-lgb-slice (- start 4) (+ len 4) fn-octets)))
                   ; CUR mutant advances one octet beyond the next span.
                   (not (equal (+ 1 i2) (fn-lgb-span-cursor 1 42 fn-octets)))
                   ; S5 mutant substitutes record length for entry length.
                   (not (equal (update-nth 1 (len record) desc)
                               (nth 0 (fn-arx-attach-trailers-buffer
                                       (fn-arx-list-places (fn-octets-list fn-octets) 17 k 4 0 0 nil 0 0 nil)
                                       17 fn-octets))))))))
        fn-octets))
  :stobjs-out '(nil fn-octets)))

(with-guard-checking-event
 :all
 (assert-event
  (let ((fn-octets (fn-octets-from-list (slbt-one) fn-octets)))
    (mv (mv-let (ok k) (fn-lgb-decide-count *fn-lg-genesis* 33 fn-octets)
          (mv-let (record desc next) (fn-lgb-next-record 42 17 t fn-octets)
            (declare (ignore desc next))
            (and ok (equal k 1) (equal (+ 32 (len record)) 33)
                 (not (<= (+ 32 (len record)) (1- 33))))))
        fn-octets))
  :stobjs-out '(nil fn-octets)))

(with-guard-checking-event
 :all
 (assert-event
  (let ((fn-octets (fn-octets-from-list (slbt-e74) fn-octets)))
    (mv (mv-let (ok k) (fn-lgb-decide-count *fn-lg-genesis* 32 fn-octets)
          (mv-let (record desc next) (fn-lgb-next-record 42 17 t fn-octets)
            (declare (ignore next))
            (and ok (equal k 1) (consp desc) (equal record nil)
                 (not (and (consp desc) (< 0 (len record)))))))
        fn-octets))
  :stobjs-out '(nil fn-octets)))

; Native checks for defteeth's exact world-bound claims. The generator
; emits assert-events under guard checking and records all five packages.
(defun slbnr-teeth-check (key j pos extentp prev max unit fn-octets)
  (declare (xargs :stobjs fn-octets :guard t :verify-guards nil))
  (mv
   (case key
     (0 (nth 2 (slbnr-claims j pos extentp prev max unit fn-octets)))
     (1 (nth 3 (slbnr-claims j pos extentp prev max unit fn-octets)))
     (2 (nth 4 (slbnr-claims j pos extentp prev max unit fn-octets)))
     (3 (nth 5 (slbnr-claims j pos extentp prev max unit fn-octets)))
     (4 (nth 6 (slbnr-claims j pos extentp prev max unit fn-octets)))
     (5 (nth 7 (slbnr-claims j pos extentp prev max unit fn-octets)))
     (otherwise
      (mv-let (record desc next)
        (fn-lgb-next-record (fn-lgb-span-cursor j 42 fn-octets) pos extentp fn-octets)
        (case key
          (8 (mv-let (ok records) (fn-lgw-decide (fn-octets-list fn-octets) prev max)
               (declare (ignore ok)) (equal record (cons 0 (nth j records)))))
          (9 (equal (+ 1 next) (fn-lgb-span-cursor (+ 1 (nfix j)) 42 fn-octets)))
          (10 (<= (+ 32 (len record)) (1- max)))
          (11 (mv-let (ok k) (fn-lgb-decide-count prev max fn-octets)
                (declare (ignore ok))
                (equal (update-nth 1 (len record) desc)
                       (nth j (fn-arx-attach-trailers-buffer
                               (fn-arx-list-places (fn-octets-list fn-octets) pos k unit 0 0 nil 0 0 nil)
                               pos fn-octets)))))
          (otherwise (and (consp desc) (< 0 (len record))))))))
   fn-octets))

(defteeth fn-lgb-next-record-yields-the-records
  :claim (((below-count (< (nfix j) (mv-nth 1 (fn-lgb-decide-count prev max fn-octets)))))
          (equal (mv-nth 0 (fn-lgb-next-record (fn-lgb-span-cursor j 42 fn-octets) pos extentp fn-octets)) (nth j (mv-nth 1 (fn-lgw-decide fn-octets prev max)))))
  :subject fn-lgb-next-record
  :witness ((j 1) (pos 17) (extentp t) (prev *fn-lg-genesis*) (max 4096) (unit 4) (buffer (slbt-batch3)))
  :stobjs ((fn-octets (fn-octets-from-list buffer fn-octets)))
  :stobj-checks
  (   ((< (nfix j) (mv-nth 1 (fn-lgb-decide-count prev max fn-octets)))
    (slbnr-teeth-check 0 j pos extentp prev max unit fn-octets)
    :hints (("Goal" :in-theory (union-theories
              '(slbnr-teeth-check slbnr-claims nth zp car-cons cdr-cons nth-0-cons nth-add1 mv-list fn-oct-list-is-identity)
              (theory 'minimal-theory)))))
   ((equal (mv-nth 0 (fn-lgb-next-record (fn-lgb-span-cursor j 42 fn-octets) pos extentp fn-octets)) (nth j (mv-nth 1 (fn-lgw-decide fn-octets prev max))))
    (slbnr-teeth-check 1 j pos extentp prev max unit fn-octets)
    :hints (("Goal" :in-theory (union-theories
              '(slbnr-teeth-check slbnr-claims nth zp car-cons cdr-cons nth-0-cons nth-add1 mv-list fn-oct-list-is-identity)
              (theory 'minimal-theory)))))
   ((equal (mv-nth 0 (fn-lgb-next-record (fn-lgb-span-cursor j 42 fn-octets) pos extentp fn-octets)) (cons 0 (nth j (mv-nth 1 (fn-lgw-decide fn-octets prev max)))))
    (slbnr-teeth-check 8 j pos extentp prev max unit fn-octets)
    :hints (("Goal" :in-theory (union-theories
              '(slbnr-teeth-check slbnr-claims nth zp car-cons cdr-cons nth-0-cons nth-add1 mv-list fn-oct-list-is-identity)
              (theory 'minimal-theory))))))
  :breaks ((below-count ((j 0) (prev nil) (max 0) (buffer (slbt-b75)))))
  :mutations ((batch-window-includes-the-prefix
               (:conclusion (equal (mv-nth 0 (fn-lgb-next-record (fn-lgb-span-cursor j 42 fn-octets) pos extentp fn-octets)) (cons 0 (nth j (mv-nth 1 (fn-lgw-decide fn-octets prev max))))))
               ()
               :fault "the fused record includes a leading prefix octet")))

(defteeth fn-lgb-next-record-advances-the-cursor
  :claim (()
          (equal (mv-nth 2 (fn-lgb-next-record (fn-lgb-span-cursor j 42 fn-octets) pos extentp fn-octets)) (fn-lgb-span-cursor (+ 1 (nfix j)) 42 fn-octets)))
  :subject fn-lgb-next-record
  :witness ((j 1) (pos 17) (extentp t) (prev *fn-lg-genesis*) (max 4096) (unit 4) (buffer (slbt-batch3)))
  :stobjs ((fn-octets (fn-octets-from-list buffer fn-octets)))
  :stobj-checks
  (
   ((equal (mv-nth 2 (fn-lgb-next-record (fn-lgb-span-cursor j 42 fn-octets) pos extentp fn-octets)) (fn-lgb-span-cursor (+ 1 (nfix j)) 42 fn-octets))
    (slbnr-teeth-check 2 j pos extentp prev max unit fn-octets)
    :hints (("Goal" :in-theory (union-theories
              '(slbnr-teeth-check slbnr-claims nth zp car-cons cdr-cons nth-0-cons nth-add1 mv-list fn-oct-list-is-identity)
              (theory 'minimal-theory)))))
   ((equal (+ 1 (mv-nth 2 (fn-lgb-next-record (fn-lgb-span-cursor j 42 fn-octets) pos extentp fn-octets))) (fn-lgb-span-cursor (+ 1 (nfix j)) 42 fn-octets))
    (slbnr-teeth-check 9 j pos extentp prev max unit fn-octets)
    :hints (("Goal" :in-theory (union-theories
              '(slbnr-teeth-check slbnr-claims nth zp car-cons cdr-cons nth-0-cons nth-add1 mv-list fn-oct-list-is-identity)
              (theory 'minimal-theory))))))
  :breaks ()
  :mutations ((next-one-too-far
               (:conclusion (equal (+ 1 (mv-nth 2 (fn-lgb-next-record (fn-lgb-span-cursor j 42 fn-octets) pos extentp fn-octets))) (fn-lgb-span-cursor (+ 1 (nfix j)) 42 fn-octets)))
               ()
               :fault "the fused next cursor is one octet too far")))

(defteeth fn-lgb-next-record-within-max
  :claim (((below-count (< (nfix j) (mv-nth 1 (fn-lgb-decide-count prev max fn-octets)))))
          (<= (+ 32 (len (mv-nth 0 (fn-lgb-next-record (fn-lgb-span-cursor j 42 fn-octets) pos extentp fn-octets)))) (nfix max)))
  :subject fn-lgb-next-record
  :witness ((j 1) (pos 17) (extentp t) (prev *fn-lg-genesis*) (max 4096) (unit 4) (buffer (slbt-batch3)))
  :stobjs ((fn-octets (fn-octets-from-list buffer fn-octets)))
  :stobj-checks
  (   ((< (nfix j) (mv-nth 1 (fn-lgb-decide-count prev max fn-octets)))
    (slbnr-teeth-check 0 j pos extentp prev max unit fn-octets)
    :hints (("Goal" :in-theory (union-theories
              '(slbnr-teeth-check slbnr-claims nth zp car-cons cdr-cons nth-0-cons nth-add1 mv-list fn-oct-list-is-identity)
              (theory 'minimal-theory)))))
   ((<= (+ 32 (len (mv-nth 0 (fn-lgb-next-record (fn-lgb-span-cursor j 42 fn-octets) pos extentp fn-octets)))) (nfix max))
    (slbnr-teeth-check 3 j pos extentp prev max unit fn-octets)
    :hints (("Goal" :in-theory (union-theories
              '(slbnr-teeth-check slbnr-claims nth zp car-cons cdr-cons nth-0-cons nth-add1 mv-list fn-oct-list-is-identity)
              (theory 'minimal-theory)))))
   ((<= (+ 32 (len (mv-nth 0 (fn-lgb-next-record (fn-lgb-span-cursor j 42 fn-octets) pos extentp fn-octets)))) (1- max))
    (slbnr-teeth-check 10 j pos extentp prev max unit fn-octets)
    :hints (("Goal" :in-theory (union-theories
              '(slbnr-teeth-check slbnr-claims nth zp car-cons cdr-cons nth-0-cons nth-add1 mv-list fn-oct-list-is-identity)
              (theory 'minimal-theory))))))
  :breaks ((below-count ((j 0) (prev nil) (max 0) (buffer (slbt-b75)))))
  :mutations ((bound-one-below-max
               (:conclusion (<= (+ 32 (len (mv-nth 0 (fn-lgb-next-record (fn-lgb-span-cursor j 42 fn-octets) pos extentp fn-octets)))) (1- max)))
               ((max 33) (j 0) (buffer (slbt-one)))
               :fault "the fused record bound is one octet short")))

(defteeth fn-lgb-next-record-descriptor-is-the-attached-place
  :claim (((pos (natp pos)) (extentp extentp) (below-count (< (nfix j) (mv-nth 1 (fn-lgb-decide-count prev max fn-octets)))))
          (equal (mv-nth 1 (fn-lgb-next-record (fn-lgb-span-cursor j 42 fn-octets) pos extentp fn-octets)) (nth j (fn-arx-attach-trailers-buffer (fn-arx-list-places fn-octets pos (mv-nth 1 (fn-lgb-decide-count prev max fn-octets)) unit 0 0 nil 0 0 nil) pos fn-octets))))
  :subject fn-lgb-next-record
  :witness ((j 1) (pos 17) (extentp t) (prev *fn-lg-genesis*) (max 4096) (unit 4) (buffer (slbt-batch3)))
  :stobjs ((fn-octets (fn-octets-from-list buffer fn-octets)))
  :stobj-checks
  (   ((< (nfix j) (mv-nth 1 (fn-lgb-decide-count prev max fn-octets)))
    (slbnr-teeth-check 0 j pos extentp prev max unit fn-octets)
    :hints (("Goal" :in-theory (union-theories
              '(slbnr-teeth-check slbnr-claims nth zp car-cons cdr-cons nth-0-cons nth-add1 mv-list fn-oct-list-is-identity)
              (theory 'minimal-theory)))))
   ((equal (mv-nth 1 (fn-lgb-next-record (fn-lgb-span-cursor j 42 fn-octets) pos extentp fn-octets)) (nth j (fn-arx-attach-trailers-buffer (fn-arx-list-places fn-octets pos (mv-nth 1 (fn-lgb-decide-count prev max fn-octets)) unit 0 0 nil 0 0 nil) pos fn-octets)))
    (slbnr-teeth-check 4 j pos extentp prev max unit fn-octets)
    :hints (("Goal" :in-theory (union-theories
              '(slbnr-teeth-check slbnr-claims nth zp car-cons cdr-cons nth-0-cons nth-add1 mv-list fn-oct-list-is-identity)
              (theory 'minimal-theory)))))
   ((equal (update-nth 1 (len (mv-nth 0 (fn-lgb-next-record (fn-lgb-span-cursor j 42 fn-octets) pos extentp fn-octets))) (mv-nth 1 (fn-lgb-next-record (fn-lgb-span-cursor j 42 fn-octets) pos extentp fn-octets))) (nth j (fn-arx-attach-trailers-buffer (fn-arx-list-places fn-octets pos (mv-nth 1 (fn-lgb-decide-count prev max fn-octets)) unit 0 0 nil 0 0 nil) pos fn-octets)))
    (slbnr-teeth-check 11 j pos extentp prev max unit fn-octets)
    :hints (("Goal" :in-theory (union-theories
              '(slbnr-teeth-check slbnr-claims nth zp car-cons cdr-cons nth-0-cons nth-add1 mv-list fn-oct-list-is-identity)
              (theory 'minimal-theory))))))
  :breaks ((pos ((pos -4)) :logical "negative POS is outside the fused entry guard")
           (extentp ((extentp nil)))
           (below-count ((j 0) (prev nil) (max 0) (buffer (slbt-b75)))))
  :mutations ((descriptor-length-is-the-record
               (:conclusion (equal (update-nth 1 (len (mv-nth 0 (fn-lgb-next-record (fn-lgb-span-cursor j 42 fn-octets) pos extentp fn-octets))) (mv-nth 1 (fn-lgb-next-record (fn-lgb-span-cursor j 42 fn-octets) pos extentp fn-octets))) (nth j (fn-arx-attach-trailers-buffer (fn-arx-list-places fn-octets pos (mv-nth 1 (fn-lgb-decide-count prev max fn-octets)) unit 0 0 nil 0 0 nil) pos fn-octets))))
               ()
               :fault "the fused descriptor names the record length as entry length")))

(defteeth fn-lgb-next-record-has-a-descriptor
  :claim (((extentp extentp) (below-count (< (nfix j) (mv-nth 1 (fn-lgb-decide-count prev max fn-octets)))))
          (consp (mv-nth 1 (fn-lgb-next-record (fn-lgb-span-cursor j 42 fn-octets) pos extentp fn-octets))))
  :subject fn-lgb-next-record
  :witness ((j 1) (pos 17) (extentp t) (prev *fn-lg-genesis*) (max 4096) (unit 4) (buffer (slbt-batch3)))
  :stobjs ((fn-octets (fn-octets-from-list buffer fn-octets)))
  :stobj-checks
  (   ((< (nfix j) (mv-nth 1 (fn-lgb-decide-count prev max fn-octets)))
    (slbnr-teeth-check 0 j pos extentp prev max unit fn-octets)
    :hints (("Goal" :in-theory (union-theories
              '(slbnr-teeth-check slbnr-claims nth zp car-cons cdr-cons nth-0-cons nth-add1 mv-list fn-oct-list-is-identity)
              (theory 'minimal-theory)))))
   ((consp (mv-nth 1 (fn-lgb-next-record (fn-lgb-span-cursor j 42 fn-octets) pos extentp fn-octets)))
    (slbnr-teeth-check 5 j pos extentp prev max unit fn-octets)
    :hints (("Goal" :in-theory (union-theories
              '(slbnr-teeth-check slbnr-claims nth zp car-cons cdr-cons nth-0-cons nth-add1 mv-list fn-oct-list-is-identity)
              (theory 'minimal-theory)))))
   ((and (consp (mv-nth 1 (fn-lgb-next-record (fn-lgb-span-cursor j 42 fn-octets) pos extentp fn-octets))) (< 0 (len (mv-nth 0 (fn-lgb-next-record (fn-lgb-span-cursor j 42 fn-octets) pos extentp fn-octets)))))
    (slbnr-teeth-check 12 j pos extentp prev max unit fn-octets)
    :hints (("Goal" :in-theory (union-theories
              '(slbnr-teeth-check slbnr-claims nth zp car-cons cdr-cons nth-0-cons nth-add1 mv-list fn-oct-list-is-identity)
              (theory 'minimal-theory))))))
  :breaks ((extentp ((extentp nil)))
           (below-count ((j 0) (buffer (slbt-empty)))))
  :mutations ((every-record-is-non-empty
               (:conclusion (and (consp (mv-nth 1 (fn-lgb-next-record (fn-lgb-span-cursor j 42 fn-octets) pos extentp fn-octets))) (< 0 (len (mv-nth 0 (fn-lgb-next-record (fn-lgb-span-cursor j 42 fn-octets) pos extentp fn-octets))))))
               ((max 32) (j 0) (buffer (slbt-e74)))
               :fault "the fused record is incorrectly required to be nonempty")))

(defteeth-check (fn-lgb-next-record-yields-the-records fn-lgb-next-record-advances-the-cursor fn-lgb-next-record-within-max fn-lgb-next-record-descriptor-is-the-attached-place fn-lgb-next-record-has-a-descriptor))
