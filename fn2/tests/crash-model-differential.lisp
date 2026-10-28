; Run from repo root: nohup env FN_ACL2_SLOT_DIR=/tmp/fn2-b1-acl2-slots FN_ACL2_SLOTS=4 timeout -k 5 1800 tools/acl2 < fn2/tests/crash-model-differential.lsp > build/b1-differential.log 2>&1 & echo $! > build/b1-differential.pid
; An LD driver, not a certified book. The concrete calls below are the same
; storage entry points used by sim-transfer.lisp and sim-adapter-base.lisp.
; Data and faults come from layer A's PRNG; model predicates judge outcomes.
(in-package "ACL2")
(include-book "../books/crash-model")
(include-book "../sim/storage")
(include-book "../sim/prng")
(include-book "std/util/bstar" :dir :system)
(set-guard-checking :none)

(defthm fn2-diff-countdown
  (implies (not (zp x)) (o< (nfix (- x 1)) (nfix x))) :rule-classes nil)
(defthm fn2-diff-count-op (o-p (nfix x)) :rule-classes nil)

(defun fn2-diff-random (rng)
  (declare (xargs :verify-guards nil))
  (mv-let (word a b c d)
    (fn2-prng-next (nth 0 rng) (nth 1 rng) (nth 2 rng) (nth 3 rng))
    (mv word (list a b c d))))

(defun fn2-diff-repeat (n x)
  (declare (xargs :verify-guards nil :measure (nfix n)))
  (if (zp n) nil (cons x (fn2-diff-repeat (- n 1) x))))

(defun fn2-diff-bytes (left address durable acc fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage :verify-guards nil
                  :measure (nfix left)))
  (if (zp left) (reverse acc)
    (fn2-diff-bytes (- left 1) (+ 1 address) durable
      (cons (if durable (fn2-sim-storage-durable address fn2-sim-storage)
              (fn2-sim-storage-pending address fn2-sim-storage)) acc)
      fn2-sim-storage)))

(defun fn2-diff-image-aux (left unit durable acc fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage :verify-guards nil
                  :measure (nfix left)))
  (if (zp left) (reverse acc)
    (fn2-diff-image-aux (- left 1) (+ unit 1) durable
      (cons (fn2-diff-bytes 512 (* 512 unit) durable nil fn2-sim-storage) acc)
      fn2-sim-storage)))

(defun fn2-diff-image (durable fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage :verify-guards nil))
  (fn2-diff-image-aux (floor (fn2-sim-storage-rows fn2-sim-storage) 512)
                      0 durable nil fn2-sim-storage))

(defun fn2-diff-write-bytes (bytes left address physical stamp fua fault fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage :verify-guards nil
                  :measure (nfix left)))
  (if (or (zp left) (atom bytes)) (mv :ok fn2-sim-storage)
    (mv-let (code fn2-sim-storage)
      (fn2-storage-write-byte address physical (car bytes) stamp fua fault fn2-sim-storage)
      (if (not (eq code :ok)) (mv code fn2-sim-storage)
        (fn2-diff-write-bytes (cdr bytes) (- left 1) (+ address 1) (+ physical 1)
                              stamp fua fault fn2-sim-storage)))))

(defun fn2-diff-read-bytes (left address physical fault acc fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage :verify-guards nil
                  :measure (nfix left)))
  (if (zp left) (mv :ok (reverse acc))
    (mv-let (code byte)
      (fn2-storage-read-byte address physical fault fn2-sim-storage)
      (if (not (eq code :ok)) (mv code nil)
        (fn2-diff-read-bytes (- left 1) (+ address 1) (+ physical 1) fault
                             (cons byte acc) fn2-sim-storage)))))

; Flights are (op byte-address byte-list fua). Complete a selected flight;
; an arbitrary byte prefix implements exactly sim-amount's short-write choice.
(defun fn2-diff-complete (flight fault word model profile stamp fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage :verify-guards nil))
  (b* ((op (nth 0 flight)) (address (nth 1 flight))
       (bytes (nth 2 flight)) (fua (nth 3 flight))
       (physical (if (eq fault :miswrite)
                     (mod (+ address 4096) (fn2-sim-storage-rows fn2-sim-storage)) address))
       (amount (if (eq fault :short) (mod word (+ 1 (len bytes))) (len bytes))))
    (mv-let (code fn2-sim-storage)
      (fn2-diff-write-bytes bytes amount address physical stamp fua fault fn2-sim-storage)
      (let* ((outcome (cond ((not (eq code :ok)) code)
                            ((< amount (len bytes)) (list :short amount physical))
                            (t (list :ok physical))))
             (model (fn2-cm-complete-write model op outcome profile)))
        (mv model fn2-sim-storage)))))

; Every selected flight is either omitted or written without completed-FUA
; guarantees, in a seeded permutation, just as fn2-sim-crash-flight-one does.
(defun fn2-diff-crash-flights (left flights rng stamp fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage :verify-guards nil :measure (nfix left)))
  (if (or (zp left) (atom flights)) (mv rng stamp fn2-sim-storage)
    (b* (((mv word rng) (fn2-diff-random rng))
         (flight (nth (mod (floor word 2) (len flights)) flights))
         ((mv & fn2-sim-storage)
          (if (equal (mod word 2) 1)
              (fn2-diff-write-bytes (nth 2 flight) (len (nth 2 flight))
                (nth 1 flight) (nth 1 flight) stamp nil nil fn2-sim-storage)
            (mv :ok fn2-sim-storage))))
      (fn2-diff-crash-flights (- left 1) (remove1-equal flight flights)
                              rng (+ stamp 1) fn2-sim-storage))))

(defun fn2-diff-crash-units (left rng fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage :verify-guards nil :measure (nfix left)))
  (if (zp left) (mv rng fn2-sim-storage)
    (mv-let (word rng) (fn2-diff-random rng)
      (let ((fn2-sim-storage
             (fn2-storage-crash-unit (- left 1) (mod word 4)
                                     (mod (floor word 4) 256) fn2-sim-storage)))
        (fn2-diff-crash-units (- left 1) rng fn2-sim-storage)))))

(defun fn2-diff-crash (model flights profile rng stamp fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage :verify-guards nil))
  (b* (((mv rng stamp fn2-sim-storage)
        (fn2-diff-crash-flights (len flights) flights rng stamp fn2-sim-storage))
       ((mv rng fn2-sim-storage)
        (fn2-diff-crash-units (floor (fn2-sim-storage-rows fn2-sim-storage) 512)
                              rng fn2-sim-storage))
       (image (fn2-diff-image t fn2-sim-storage))
       (allowed (fn2-cm-crash-image-allowedp model image profile))
       (ok allowed)
       (model (fn2-cm-crash model image profile))
       (fn2-sim-storage (fn2-storage-crash-reset fn2-sim-storage)))
    (mv ok model rng stamp fn2-sim-storage)))

(defun fn2-diff-free-fence (left fences)
  (declare (xargs :verify-guards nil :measure (nfix left)))
  (if (zp left) nil
    (if (assoc-equal (- left 1) fences) (fn2-diff-free-fence (- left 1) fences)
      (- left 1))))

(defun fn2-diff-fence-diagnostic-unit (expected observed address base fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage :verify-guards nil))
  (if (atom expected) nil
    (if (equal (car expected) (car observed))
        (fn2-diff-fence-diagnostic-unit (cdr expected) (cdr observed) (+ address 1) base fn2-sim-storage)
      (list address (car expected) (car observed)
            (fn2-storage-snapshoti (+ base address) fn2-sim-storage)
            (fn2-sim-storage-pending address fn2-sim-storage)
            (fn2-sim-storage-durable-stamp address fn2-sim-storage)
            (fn2-storage-snapshot-stampi (+ base address) fn2-sim-storage)))))

(defun fn2-diff-fence-diagnostic (expected observed address base fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage :verify-guards nil))
  (if (atom expected) nil
    (or (fn2-diff-fence-diagnostic-unit (car expected) (car observed) address base fn2-sim-storage)
        (fn2-diff-fence-diagnostic (cdr expected) (cdr observed) (+ address 512) base fn2-sim-storage))))

; Context = (model flights fences serial rng counters). Fence alist maps the
; concrete snapshot slot to its abstract op; slots are never reused in flight.
; 0 submit, 1 completion, 2 write, 3 read, 4 misread, 5 read-io, 6 capture,
; 7 fence-ok, 8 fence-io/reopen, 9 lying fence, 10 bitrot, 11 crash,
; 12 sticky death, 13 short write, 14 no-space, 15 fail-slow/delay,
; 16 extra flight, 17 FUA, 18 write-io, 19 tear before process death.
(defun fn2-diff-step (choice word ctx profile fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage :verify-guards nil))
  (b* ((model (nth 0 ctx)) (flights (nth 1 ctx)) (fences (nth 2 ctx))
       (serial (nth 3 ctx)) (rng (nth 4 ctx)) (counts (nth 5 ctx))
       (nbytes (fn2-sim-storage-rows fn2-sim-storage))
       (address (* 4096 (mod (floor word 32) (floor nbytes 4096))))
       (byte (+ 1 (mod (floor word 512) 254)))
       (bytes (if (member-equal choice '(0 2 13 14 16 17 18))
                  (fn2-diff-repeat 4096 byte) nil))
       (counts (update-nth choice (+ 1 (nfix (nth choice counts))) counts))
       ((mv ok model flights fences serial rng fn2-sim-storage)
        (cond
         ((member-equal choice '(0 16))
          (let* ((fua (equal (mod word 4) 0))
                 (model (fn2-cm-submit-write model serial address bytes fua)))
            (mv t model (cons (list serial address bytes fua) flights)
                fences (+ serial 1) rng fn2-sim-storage)))
         ((equal choice 1)
          (if (atom flights) (mv t model flights fences serial rng fn2-sim-storage)
            (let* ((flight (nth (mod word (len flights)) flights))
                   (fault (if (equal (mod (floor word 8) 4) 0) :miswrite nil)))
              (mv-let (model fn2-sim-storage)
                (fn2-diff-complete flight fault word model profile serial fn2-sim-storage)
                (mv t model (remove1-equal flight flights) fences (+ serial 1) rng fn2-sim-storage)))))
         ((member-equal choice '(2 13 14 17 18))
          (let* ((fua (equal choice 17))
                 (fault (cond ((equal choice 13) :short) ((equal choice 14) :no-space)
                              ((equal choice 18) :io)
                              ((equal (mod word 5) 0) :miswrite) (t nil)))
                 (model (fn2-cm-submit-write model serial address bytes fua)))
            (mv-let (model fn2-sim-storage)
              (fn2-diff-complete (list serial address bytes fua) fault word model profile
                                 (+ serial 1) fn2-sim-storage)
              (mv t model flights fences (+ serial 2) rng fn2-sim-storage))))
         ((member-equal choice '(3 4 5))
          (let* ((physical (if (equal choice 4) (mod (+ address 4096) nbytes) address))
                 (fault (if (equal choice 5) :io nil)))
            (mv-let (code result)
              (fn2-diff-read-bytes 4096 address physical fault nil fn2-sim-storage)
              (let ((outcome (if (not (eq code :ok)) code
                               (if (equal choice 4) (list :misdirect physical) :ok))))
                (mv (fn2-cm-read-allowedp model address outcome result profile)
                    model flights fences serial rng fn2-sim-storage)))))
         ((equal choice 6)
          (let ((slot (fn2-diff-free-fence 4 fences)))
            (if (not slot) (mv t model flights fences serial rng fn2-sim-storage)
              (mv-let (code fn2-sim-storage) (fn2-storage-fence-capture slot fn2-sim-storage)
                (mv (eq code :ok) (fn2-cm-submit-fence model serial) flights
                    (acons slot serial fences) (+ serial 1) rng fn2-sim-storage)))))
         ((member-equal choice '(7 8 9))
          (if (atom fences) (mv t model flights fences serial rng fn2-sim-storage)
            (b* ((fence (nth (mod word (len fences)) fences))
                 (lie (and (equal choice 9) (not (nth 1 profile))))
                 ((mv code fn2-sim-storage)
                  (fn2-storage-fence-complete (car fence) (equal choice 8) lie fn2-sim-storage))
                 (outcome (if (or (not (eq code :ok)) (nth 1 profile)) code
                            (if lie '(:ok :lie) '(:ok :persist))))
                 (image (fn2-diff-image t fn2-sim-storage))
                 (allowed (fn2-cm-fence-allowedp model (cdr fence) outcome image profile))
                 (expected (fn2-cm-fence-image model (cdr fence)))
                 (ok allowed)
                 (- (if ok nil
                      (cw "B1-FENCE-DETAIL [address expected observed snapshot pending durable-stamp snapshot-stamp]=~x0~%"
                          (fn2-diff-fence-diagnostic expected image 0 (* (car fence) nbytes) fn2-sim-storage))))
                 (model (fn2-cm-complete-fence model (cdr fence) outcome image profile))
                 (revert (and (eq code :io) (equal (mod word 2) 0)))
                 (model (if (eq code :io) (fn2-cm-reopen model revert) model))
                 (fn2-sim-storage (if (eq code :io) (fn2-storage-reopen revert fn2-sim-storage)
                                    fn2-sim-storage)))
              (mv ok model flights (remove1-equal fence fences) serial rng fn2-sim-storage))))
         ((equal choice 10)
          (let* ((address (mod word nbytes)) (unit (floor address 512))
                 (old (fn2-sim-storage-durable address fn2-sim-storage))
                 (fn2-sim-storage (fn2-storage-corrupt-byte address (logxor old 1) fn2-sim-storage))
                 (unit-bytes (fn2-diff-bytes 512 (* unit 512) t nil fn2-sim-storage))
                 (model (fn2-cm-corrupt model unit unit-bytes profile)))
            (mv t model flights fences serial rng fn2-sim-storage)))
         ((equal choice 11)
          (mv-let (ok model rng serial fn2-sim-storage)
            (fn2-diff-crash model flights profile rng serial fn2-sim-storage)
            (mv ok model nil nil serial rng fn2-sim-storage)))
         ((equal choice 12)
          (let* ((model (fn2-cm-kill-device model))
                (fn2-sim-storage (fn2-storage-kill-device fn2-sim-storage)))
            (mv t model flights fences serial rng fn2-sim-storage)))
         ; Delay/fail-slow has no storage observation and changes no model state.
         ((equal choice 15) (mv t model flights fences serial rng fn2-sim-storage))
         (t
          ; The simulator's tear event can precede process death. Check that
          ; intermediate durable image against the same crash relation, without
          ; throwing away cache, snapshots or flights.
          (let* ((unit (mod word (floor nbytes 512)))
                 (fn2-sim-storage (fn2-storage-crash-unit unit (+ 2 (mod word 2)) byte fn2-sim-storage))
                 (image (fn2-diff-image t fn2-sim-storage)))
            (mv (fn2-cm-crash-image-allowedp model image profile)
                (fn2-cm-land-live model image profile) flights fences serial rng fn2-sim-storage))))))
    (mv ok (list model flights fences serial rng counts) fn2-sim-storage)))

(defun fn2-diff-trace (left seed ctx profile fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage :verify-guards nil :measure (nfix left)
                  :hints (("Goal" :in-theory nil
                           :use ((:instance fn2-diff-countdown (x left))
                                 (:instance fn2-diff-count-op (x left)))))))
  (if (zp left)
      (mv-let (ok ctx fn2-sim-storage) (fn2-diff-step 11 seed ctx profile fn2-sim-storage)
        (prog2$ (if ok nil (cw "B1-DIFF-FAIL seed=~x0 final-crash~%" seed))
          (mv ok ctx fn2-sim-storage)))
    (b* (((mv word rng) (fn2-diff-random (nth 4 ctx)))
         (raw-choice (mod word 20))
         ; A device dies late enough that this trace can exercise other faults.
         (choice (if (and (equal raw-choice 12) (< 3 left)) 3 raw-choice))
         (ctx (update-nth 4 rng ctx))
         ((mv ok ctx fn2-sim-storage) (fn2-diff-step choice word ctx profile fn2-sim-storage)))
      (cond (ok (fn2-diff-trace (- left 1) seed ctx profile fn2-sim-storage))
            (t (prog2$ (cw "B1-DIFF-FAIL seed=~x0 remaining=~x1 choice=~x2 word=~x3~%"
                           seed left choice word)
                 (mv nil ctx fn2-sim-storage)))))))

(defun fn2-diff-add-counts (a b)
  (declare (xargs :verify-guards nil))
  (if (atom a) b (cons (+ (nfix (car a)) (nfix (car b)))
                       (fn2-diff-add-counts (cdr a) (cdr b)))))

(defun fn2-diff-all-positive (counts)
  (declare (xargs :verify-guards nil))
  (if (atom counts) t
    (and (< 0 (nfix (car counts))) (fn2-diff-all-positive (cdr counts)))))

(defun fn2-diff-traces (left seed totals fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage :verify-guards nil :measure (nfix left)
                  :hints (("Goal" :in-theory nil
                           :use ((:instance fn2-diff-countdown (x left))
                                 (:instance fn2-diff-count-op (x left)))))))
  (if (zp left) (mv (fn2-diff-all-positive totals) totals fn2-sim-storage)
    (b* ((nsectors (if (equal (mod seed 100) 0) 64 16))
         (profile (fn2-cm-profile (if (equal (mod seed 3) 0) :lying :broad)
                                  (not (equal (mod seed 3) 0)) t nil 0 64))
         (model (fn2-cm-init 4096 512 nsectors 0))
         (fn2-sim-storage (fn2-storage-init nsectors 4 fn2-sim-storage))
         ((mv a b c d) (fn2-prng-seed seed))
         (ctx (list model nil nil 1 (list a b c d) (fn2-diff-repeat 20 0)))
         ((mv ok ctx fn2-sim-storage)
          (fn2-diff-trace (+ 12 (mod seed 13)) seed ctx profile fn2-sim-storage))
         (totals (fn2-diff-add-counts totals (nth 5 ctx))))
      (if (not ok) (mv nil totals fn2-sim-storage)
        (fn2-diff-traces (- left 1) (+ seed 1) totals fn2-sim-storage)))))

; Deliberately alter observed results, with a positive control beside each.
; A plain FUA does NOT exclude an unrelated write from a later crash image:
; that write might land independently at the crash. The FUA mutant therefore
; tests its immediate deterministic durable effect, where the claim belongs.
(defun fn2-diff-negative-teeth-aux (fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage :verify-guards nil))
  (b* ((profile (fn2-cm-profile :crash-only t t nil 0 0))
         (s0 (fn2-cm-init 4096 512 16 0))
         (fn2-sim-storage (fn2-storage-init 16 1 fn2-sim-storage))
         (zero (fn2-diff-image t fn2-sim-storage))
         (garbage (fn2-diff-repeat 512 93))
         (bytes (fn2-diff-repeat 4096 17))
         (s1 (fn2-cm-submit-write s0 1 0 bytes nil))
         (s1 (fn2-cm-complete-write s1 1 '(:ok 0) profile))
         ((mv write-code fn2-sim-storage)
          (fn2-diff-write-bytes bytes 4096 0 0 1 nil nil fn2-sim-storage))
         ((mv read-code read-result)
          (fn2-diff-read-bytes 512 0 0 nil nil fn2-sim-storage))
         (sf (fn2-cm-submit-fence s1 2))
         ((mv capture-code fn2-sim-storage) (fn2-storage-fence-capture 0 fn2-sim-storage))
         ((mv fence-code fn2-sim-storage) (fn2-storage-fence-complete 0 nil nil fn2-sim-storage))
         (expected (fn2-diff-image t fn2-sim-storage))
         ; A new concrete device restores the pending unrelated-write premise.
         (fn2-sim-storage (fn2-storage-init 16 1 fn2-sim-storage))
         ((mv write2-code fn2-sim-storage)
          (fn2-diff-write-bytes bytes 4096 0 0 1 nil nil fn2-sim-storage))
         ((mv fua-code fn2-sim-storage)
          (fn2-diff-write-bytes (fn2-diff-repeat 4096 29) 4096 4096 4096 2 t nil fn2-sim-storage))
         (fua-image (fn2-diff-image t fn2-sim-storage))
         (s2 (fn2-cm-submit-write s1 3 4096 (fn2-diff-repeat 4096 29) t))
         (s2 (fn2-cm-complete-write s2 3 '(:ok 4096) profile))
         (fua-mutant (update-nth 0 (nth 0 expected) fua-image)))
    (mv (and (eq write-code :ok) (eq read-code :ok) (eq capture-code :ok)
         (eq fence-code :ok) (eq write2-code :ok) (eq fua-code :ok)
         (fn2-cm-crash-image-allowedp s0 zero profile)
         (not (fn2-cm-crash-image-allowedp s0 (update-nth 127 garbage zero) profile))
         (fn2-cm-fence-allowedp sf 2 :ok expected profile)
         (not (fn2-cm-fence-allowedp sf 2 :ok zero profile))
         (fn2-cm-read-allowedp s1 0 read-code read-result profile)
         (not (fn2-cm-read-allowedp s1 0 :ok garbage profile))
         (equal fua-image (fn2-cm-durable s2))
         (equal (nth 0 fua-image) (nth 0 zero))
         (equal (nth 8 fua-image) (fn2-diff-repeat 512 29))
         (not (equal fua-mutant (fn2-cm-durable s2)))) fn2-sim-storage)))

(defun fn2-diff-negative-teeth ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-sim-storage
    (mv-let (ok fn2-sim-storage) (fn2-diff-negative-teeth-aux fn2-sim-storage) ok)))

(assert-event (fn2-diff-negative-teeth))

; Regression for fault11 at a live action boundary followed by flush (B1's
; live-tear defect, fixed by layer A's S1): the torn landing is allowed, the
; fence then makes the fenced bytes (17) durable, never the tear (93), and
; the model accepts the simulator's fence result and image.
(defun fn2-diff-live-tear-regression-aux (fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage :verify-guards nil))
  (b* ((profile (fn2-cm-profile :broad t t nil 0 0))
       (model (fn2-cm-init 4096 512 16 0))
       (bytes (fn2-diff-repeat 4096 17))
       (model (fn2-cm-submit-write model 1 0 bytes nil))
       (model (fn2-cm-complete-write model 1 '(:ok 0) profile))
       (model (fn2-cm-submit-fence model 2))
       (fn2-sim-storage (fn2-storage-init 16 1 fn2-sim-storage))
       ((mv write-code fn2-sim-storage)
        (fn2-diff-write-bytes bytes 4096 0 0 1 nil nil fn2-sim-storage))
       ((mv capture-code fn2-sim-storage) (fn2-storage-fence-capture 0 fn2-sim-storage))
       (fn2-sim-storage (fn2-storage-crash-unit 0 3 93 fn2-sim-storage))
       (torn-image (fn2-diff-image t fn2-sim-storage))
       (landing-ok (fn2-cm-crash-image-allowedp model torn-image profile))
       (model (fn2-cm-land-live model torn-image profile))
       ((mv code fn2-sim-storage) (fn2-storage-fence-complete 0 nil nil fn2-sim-storage))
       (image (fn2-diff-image t fn2-sim-storage))
       (expected (fn2-cm-fence-image model 2)))
    (mv (and (eq write-code :ok) (eq capture-code :ok) landing-ok (eq code :ok)
             (equal (caar image) 17) (equal (caar expected) 17)
             (fn2-cm-fence-allowedp model 2 code image profile)) fn2-sim-storage)))

(defun fn2-diff-live-tear-regression ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-sim-storage
    (mv-let (ok fn2-sim-storage) (fn2-diff-live-tear-regression-aux fn2-sim-storage) ok)))

(assert-event (fn2-diff-live-tear-regression))

; A failed second fence permits reopen's old view. Completing the older
; submitted fence subsequently makes that snapshot durable. The stale cache
; is not a newer volatile write and must not authorize a crash tear (B1's
; stale-cache defect, fixed by layer A's S1: the crash keeps the durable 17
; and the model accepts the image).
(defun fn2-diff-stale-cache-regression-aux (fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage :verify-guards nil))
  (b* ((profile (fn2-cm-profile :broad t t nil 0 0))
       (model (fn2-cm-init 4096 512 16 0))
       (bytes (fn2-diff-repeat 4096 17))
       (model (fn2-cm-submit-write model 1 0 bytes nil))
       (model (fn2-cm-complete-write model 1 '(:ok 0) profile))
       (model (fn2-cm-submit-fence model 2))
       (model (fn2-cm-submit-fence model 3))
       (fn2-sim-storage (fn2-storage-init 16 2 fn2-sim-storage))
       ((mv c1 fn2-sim-storage)
        (fn2-diff-write-bytes bytes 4096 0 0 1 nil nil fn2-sim-storage))
       ((mv c2 fn2-sim-storage) (fn2-storage-fence-capture 0 fn2-sim-storage))
       ((mv c3 fn2-sim-storage) (fn2-storage-fence-capture 1 fn2-sim-storage))
       ((mv c4 fn2-sim-storage) (fn2-storage-fence-complete 1 t nil fn2-sim-storage))
       (image (fn2-diff-image t fn2-sim-storage))
       (failed-ok (fn2-cm-fence-allowedp model 3 c4 image profile))
       (model (fn2-cm-complete-fence model 3 c4 image profile))
       (model (fn2-cm-reopen model t))
       (fn2-sim-storage (fn2-storage-reopen t fn2-sim-storage))
       ((mv c5 fn2-sim-storage) (fn2-storage-fence-complete 0 nil nil fn2-sim-storage))
       (image (fn2-diff-image t fn2-sim-storage))
       (fence-ok (fn2-cm-fence-allowedp model 2 c5 image profile))
       (model (fn2-cm-complete-fence model 2 c5 image profile))
       (fn2-sim-storage (fn2-storage-crash-unit 0 2 0 fn2-sim-storage))
       (image (fn2-diff-image t fn2-sim-storage)))
    (mv (and (eq c1 :ok) (eq c2 :ok) (eq c3 :ok) (eq c4 :io) (eq c5 :ok)
             failed-ok fence-ok
             (equal (caar (fn2-cm-durable model)) 17) (equal (caar image) 17)
             (fn2-cm-crash-image-allowedp model image profile)) fn2-sim-storage)))

(defun fn2-diff-stale-cache-regression ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-sim-storage
    (mv-let (ok fn2-sim-storage) (fn2-diff-stale-cache-regression-aux fn2-sim-storage) ok)))

(assert-event (fn2-diff-stale-cache-regression))

; Actual-effect controls, distinct from random choice counts. Layer A fault
; IDs: 6 read-io, 7 bitrot, 8 misread, 9 miswrite, 10 lying-flush, 11 tear,
; 12 no-space, 13 dead, 15 process death, 23 flush-io, 24 short-write.
; IDs2/14 delay/fail-slow change latency, so this untimed storage oracle
; observes no effect. Network, clock and forged-result classes are outside
; this storage-kernel differential; no full-simulator coverage is claimed.
(defun fn2-diff-control-observation (check model fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage :verify-guards nil))
  (let ((last-write (car (last (fn2-cm-cache model)))))
    (case check
      (:miswrite (and (equal (fn2-sim-storage-pending 0 fn2-sim-storage) 0)
                      (equal (fn2-sim-storage-pending 4096 fn2-sim-storage) 1)))
      (:misread (mv-let (code byte) (fn2-storage-read-byte 0 4096 nil fn2-sim-storage)
                  (and (eq code :ok) (equal byte 1)
                       (equal (fn2-sim-storage-pending 0 fn2-sim-storage) 0))))
      (:read-io (mv-let (code byte) (fn2-storage-read-byte 4096 4096 :io fn2-sim-storage)
                  (declare (ignore byte)) (eq code :io)))
      ((:lying :cached) (and (equal (fn2-sim-storage-durable 4096 fn2-sim-storage) 0)
                             (equal (fn2-sim-storage-pending 4096 fn2-sim-storage) 1)))
      (:reverted (and (equal (fn2-sim-storage-durable 4096 fn2-sim-storage) 0)
                      (equal (fn2-sim-storage-pending 4096 fn2-sim-storage) 0)))
      (:short (and (eq (nth 9 last-write) :short) (equal (nth 7 last-write) 513)
                   (equal (fn2-sim-storage-pending 0 fn2-sim-storage) 2)
                   (equal (fn2-sim-storage-pending 512 fn2-sim-storage) 2)
                   (equal (fn2-sim-storage-pending 513 fn2-sim-storage) 0)))
      (:no-space (and (eq (nth 9 last-write) :no-space)
                      (equal (fn2-sim-storage-pending 0 fn2-sim-storage) 2)))
      (:write-io (eq (nth 9 last-write) :io))
      (:fua (and (equal (fn2-sim-storage-durable 4096 fn2-sim-storage) 1)
                 (equal (fn2-sim-storage-durable 0 fn2-sim-storage) 0)))
      (:bitrot (and (equal (fn2-sim-storage-durable 4096 fn2-sim-storage) 0)
                    (equal (fn2-sim-storage-pending 4096 fn2-sim-storage) 0)))
      (:tear (and (equal (fn2-sim-storage-durable 512 fn2-sim-storage) 1)
                  (equal (fn2-sim-storage-durable 513 fn2-sim-storage) 1)
                  (equal (fn2-sim-storage-pending 512 fn2-sim-storage) 2)
                  (equal (fn2-sim-storage-pending 513 fn2-sim-storage) 0)))
      (:dead (eq (fn2-storage-status nil fn2-sim-storage) :io))
      (otherwise t))))

(defun fn2-diff-control-script (commands ctx profile fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage :verify-guards nil))
  (if (atom commands) (mv t fn2-sim-storage)
    (mv-let (ok ctx fn2-sim-storage)
      (fn2-diff-step (nth 0 (car commands)) (nth 1 (car commands)) ctx profile fn2-sim-storage)
      (if (and (eq ok t)
               (fn2-diff-control-observation (nth 2 (car commands)) (nth 0 ctx) fn2-sim-storage))
          (fn2-diff-control-script (cdr commands) ctx profile fn2-sim-storage)
        (prog2$ (cw "B1-STORAGE-CONTROL-FAIL command=~x0~%" (car commands))
          (mv nil fn2-sim-storage))))))

(defun fn2-diff-storage-controls ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-sim-storage
    (mv-let (ok fn2-sim-storage)
      (let* ((profile (fn2-cm-profile :lying nil t nil 0 64))
             (fn2-sim-storage (fn2-storage-init 16 4 fn2-sim-storage))
             (ctx (list (fn2-cm-init 4096 512 16 0) nil nil 1 '(1 2 3 4)
                        (fn2-diff-repeat 20 0))))
        (fn2-diff-control-script
         '((0 1 nil) (1 1 :miswrite) (3 32 nil) (4 0 :misread) (5 32 :read-io)
           (6 0 nil) (9 0 :lying)
           (6 0 nil) (8 1 :cached)
           (6 0 nil) (8 0 :reverted)
           (2 0 nil) (13 513 :short) (14 0 :no-space) (18 0 :write-io)
           (17 32 :fua) (10 4096 :bitrot) (19 1 :tear) (15 0 nil)
           (11 0 nil) (12 0 :dead) (3 0 :dead) (11 0 :dead))
         ctx profile fn2-sim-storage))
      (prog2$ (cw "B1-STORAGE-CONTROLS actual-fault-effects and both reopen views=~x0~%"
                  (if ok :pass :fail)) ok))))

(assert-event (fn2-diff-storage-controls))

(defun fn2-diff-debug-seed (seed)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-sim-storage
    (mv-let (ok totals fn2-sim-storage)
      (fn2-diff-traces 1 seed (fn2-diff-repeat 20 1) fn2-sim-storage)
      (declare (ignore totals))
      (prog2$ (cw "B1-REPLAY seed=~x0 divergence-free=~x1~%" seed ok) ok))))

; Success means every trace's every simulator result is allowed by the model
; and every event selection was exercised. Any model/simulator disagreement
; fails the run at its seed; there is no class of tolerated divergence.
(defun fn2-diff-run ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-sim-storage
    (mv-let (ok totals fn2-sim-storage)
      (fn2-diff-traces 10000 20261028 (fn2-diff-repeat 20 0) fn2-sim-storage)
      (prog2$ (cw "B1-DIFF-COVERAGE event-counts[0..19]=~x0~%" totals)
        (prog2$ (if ok
                    (cw "B1-DIFF traces=10000 divergences=0 teeth=4/4~%")
                  (cw "B1-DIFFERENTIAL FAILED seed-range-start=20261028; see the failing seed above~%"))
          ok)))))

; The session driver invokes this admitted logic function through compiled
; Lisp, exactly as layer A's 10,000-scenario driver does. The concrete
; predicates and state transitions are the same admitted definitions.

; Isolate membership throughput from trace generation and simulator work.
; The candidate comes from a separately materialized concrete 64-sector
; image: EQUAL cannot use identity with the model's durable list as a shortcut.
(defun fn2-diff-memberships (left model image profile)
  (declare (xargs :verify-guards nil :measure (nfix left)
                  :hints (("Goal" :in-theory nil
                           :use ((:instance fn2-diff-countdown (x left))
                                 (:instance fn2-diff-count-op (x left)))))))
  (if (zp left) t
    (and (fn2-cm-crash-image-allowedp model image profile)
         (fn2-diff-memberships (- left 1) model image profile))))

(defun fn2-diff-benchmark64 ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-sim-storage
    (mv-let (ok fn2-sim-storage)
      (let* ((fn2-sim-storage (fn2-storage-init 64 1 fn2-sim-storage))
             (candidate (fn2-diff-image t fn2-sim-storage))
             (model (fn2-cm-init 4096 512 64 0))
             (profile (fn2-cm-profile :crash-only t t nil 0 0)))
        (mv (fn2-diff-memberships 10000 model candidate profile) fn2-sim-storage))
      (prog2$ (cw "B1-MEMBERSHIP sectors=64 checks=10000 independent-image result=~x0~%"
                  (if ok :pass :fail)) ok))))
