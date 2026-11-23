(in-package "ACL2")
(include-book "../sim/native-device-effects")
(defconst *fn2-nde-test-write* '(:submit 1 (17 4 7 :write 1 3 (8 9 10) 0 1 1)))
(assert-event
 (mv-let (code effects)
  (fn2-native-device-effects (list *fn2-nde-test-write* '(:begin 1) '(:return 1 2 0 nil)) 17)
  (and (eq code :ok) (equal effects '((:write 1 2 (8 9 10))))
       (fn2-native-device-image-slice-p effects 0 '(0 0 0 0 0) '(0 8 9 0 0))
       (not (fn2-native-device-image-slice-p effects 0 '(0 0 0 0 0) '(0 8 9 10 0)))
       (not (fn2-native-device-image-slice-p nil 0 '(0 0 0 0 0) '(0 8 9 0 0))))))
; A missing return is potentially effectful. It neither means zero bytes nor
; licenses arbitrary changes elsewhere in the image.
(assert-event
 (mv-let (code effects) (fn2-native-device-effects (list *fn2-nde-test-write* '(:begin 1)) 17)
  (and (eq code :ok) (equal effects '((:uncertain 1 3 :pending (8 9 10))))
       (fn2-native-device-image-slice-p effects 0 '(0 0 0 0 0) '(0 4 5 6 0))
       (not (fn2-native-device-image-slice-p effects 0 '(0 0 0 0 0) '(1 4 5 6 0))))))
(assert-event
 (mv-let (code effects) (fn2-native-device-effects (list *fn2-nde-test-write* '(:begin 1) '(:return 1 -1 5 nil)) 17)
  (and (eq code :ok) (equal effects '((:uncertain 1 3 (:error -1 5) (8 9 10)))))))
; No interpretation of malformed/missing identities or impossible counts.
(defun fn2-nde-test-verdict (records)
 (declare (xargs :verify-guards nil))
 (mv-let (code effects) (fn2-native-device-effects records 17)
  (declare (ignore effects)) code))
(assert-event
 (and (eq (fn2-nde-test-verdict (list *fn2-nde-test-write* '(:return 1 2 0 nil))) :malformed)
      (eq (fn2-nde-test-verdict (list *fn2-nde-test-write* '(:begin 1) '(:return 1 4 0 nil))) :malformed)
      (eq (fn2-nde-test-verdict (list *fn2-nde-test-write* '(:begin 1) '(:return 2 2 0 nil))) :malformed)
      (eq (fn2-nde-test-verdict (list *fn2-nde-test-write* '(:begin 1) '(:begin 1))) :malformed)))
; A Fence record is not itself a byte change or proof of power-loss truth.
(assert-event
 (mv-let (code effects)
  (fn2-native-device-effects
   (list *fn2-nde-test-write* '(:begin 1) '(:return 1 2 0 nil)
         '(:submit 2 (17 5 7 :fence 0 0 nil 0 1 1)) '(:begin 2) '(:return 2 0 0 nil)) 17)
  (and (eq code :ok) (equal effects '((:write 1 2 (8 9 10)) (:fence 0 0)))
       (fn2-native-device-image-slice-p effects 0 '(0 0 0 0) '(0 8 9 0))
       (not (fn2-native-device-image-slice-p effects 0 '(0 0 0 0) '(0 0 0 0))))))
; Requested bytes/offset matter, and physical order matters for overlaps.
(assert-event
 (and (not (fn2-native-device-image-slice-p '((:write 2 2 (8 9))) 0 '(0 0 0 0) '(0 8 9 0)))
      (not (fn2-native-device-image-slice-p '((:write 1 2 (9 8))) 0 '(0 0 0 0) '(0 8 9 0)))
      (fn2-native-device-image-slice-p '((:write 1 2 (8 9)) (:write 2 1 (7))) 0 '(0 0 0 0) '(0 8 7 0))
      (not (fn2-native-device-image-slice-p '((:write 2 1 (7)) (:write 1 2 (8 9))) 0 '(0 0 0 0) '(0 8 7 0)))))

; Read results are checked at their physical position, not against final image.
(assert-event
 (and (fn2-native-device-image-slice-p
        '((:write 1 2 (8 9)) (:read 1 2 (8 9)) (:write 1 1 (7)))
        0 '(0 0 0 0) '(0 7 9 0))
      (not (fn2-native-device-image-slice-p
        '((:write 1 2 (8 9)) (:read 1 2 (7 9)) (:write 1 1 (7)))
        0 '(0 0 0 0) '(0 7 9 0)))))
(assert-event
 (mv-let (code cursor)
  (fn2-native-device-image-chunk '((:write 1 2 (8 9))) 4 0 0 '(0 0) '(0 8))
  (and (eq code :ok) (equal cursor 2)
       (eq (fn2-native-device-image-finish nil 4 4 cursor) :incomplete-image)
       (mv-let (bad ignored) (fn2-native-device-image-chunk nil 4 cursor 3 '(0) '(0))
        (declare (ignore ignored)) (eq bad :mismatch))
       (mv-let (code cursor)
        (fn2-native-device-image-chunk '((:write 1 2 (8 9))) 4 cursor 2 '(0 0) '(9 0))
        (and (eq code :ok)
             (eq (fn2-native-device-image-finish nil 4 4 cursor) :exact-process-view)
             (eq (fn2-native-device-image-finish nil 4 5 cursor) :incomplete-image)
             (eq (fn2-native-device-image-finish '((:uncertain 1 1 :pending (8))) 4 4 cursor)
                 :uncertain-effect-bound))))))

; Submit order is FIFO, not merely a chosen serial physical order.
(assert-event
 (eq (fn2-nde-test-verdict
       (list *fn2-nde-test-write* '(:submit 2 (17 5 7 :read 1 1 nil 0 1 1)) '(:begin 2))) :malformed))
; A successful Read constrains an unknown byte until a later effect changes it.
(assert-event
 (and (fn2-native-device-image-slice-p
        '((:uncertain 0 1 (:error -1 5) (8)) (:read 0 1 (7)) (:read 0 1 (7)))
        0 '(0) '(7))
      (not (fn2-native-device-image-slice-p
        '((:uncertain 0 1 (:error -1 5) (8)) (:read 0 1 (7)) (:read 0 1 (8)))
        0 '(0) '(8)))
      (not (fn2-native-device-image-slice-p
        '((:uncertain 0 1 (:error -1 5) (8)) (:read 0 1 (7)))
        0 '(0) '(8)))))

; Whole-image completion cannot ignore successful bytes beyond/crossing EOF,
; including an empty image for which no chunk was processed.
(assert-event
 (and (eq (fn2-native-device-image-finish '((:read 4 1 (7))) 4 4 4) :out-of-image-effect)
      (eq (fn2-native-device-image-finish '((:read 3 2 (7 8))) 4 4 4) :out-of-image-effect)
      (eq (fn2-native-device-image-finish '((:write 4 1 (7))) 4 4 4) :out-of-image-effect)
      (eq (fn2-native-device-image-finish '((:read 0 1 (7))) 0 0 0) :out-of-image-effect)
      (eq (fn2-native-device-image-finish '((:write 0 1 (7))) 0 0 0) :out-of-image-effect)
      (eq (fn2-native-device-image-finish '((:read 9 0 nil)) 0 0 0) :exact-process-view)
      (eq (fn2-native-device-image-finish '((:uncertain 4 2 :pending (7 8))) 4 4 4) :uncertain-effect-bound)))

; The concurrent device: Reads overlap Reads and a Fence; Writes and Fences
; run one at a time in submission order; no Read overlaps a Write. Jobs 1..n
; are submitted first, one per kind in KINDS; EVENTS names begins as +id and
; returns as -id. Every Write and Read covers bytes 1..2.
(defun fn2-nde-test-submits (kinds id)
 (if (atom kinds) nil
  (cons (list :submit id (list 17 id 7 (car kinds) (if (eq (car kinds) :fence) 0 1)
                               (if (eq (car kinds) :fence) 0 2)
                               (if (eq (car kinds) :write) '(8 9) nil) 0 1 1))
        (fn2-nde-test-submits (cdr kinds) (+ 1 id)))))
(defun fn2-nde-test-events (kinds events)
 (if (atom events) nil
  (let* ((e (car events)) (id (if (< e 0) (- e) e)) (kind (nth (- id 1) kinds)))
   (cons (cond ((< 0 e) (list :begin id))
               ((eq kind :write) (list :return id 2 0 nil))
               ((eq kind :read) (list :return id 2 0 '(8 9)))
               (t (list :return id 0 0 nil)))
         (fn2-nde-test-events kinds (cdr events))))))
(defun fn2-nde-test-trace (kinds events)
 (append (fn2-nde-test-submits kinds 1) (fn2-nde-test-events kinds events)))
; A tooth: the legal schedule decodes, and its one-move mutant is refused.
(defun fn2-nde-test-tooth (kinds good bad)
 (declare (xargs :verify-guards nil))
 (and (eq (fn2-nde-test-verdict (fn2-nde-test-trace kinds good)) :ok)
      (eq (fn2-nde-test-verdict (fn2-nde-test-trace kinds bad)) :malformed)))

; Admitted overlap. Reads begin and return in any order among themselves, in
; flight beside a Fence, and a Fence passes an earlier Read still queued.
(assert-event
 (mv-let (code effects)
  (fn2-native-device-effects (fn2-nde-test-trace '(:write :read :read) '(1 -1 3 2 -2 -3)) 17)
  (and (eq code :ok)
       (equal effects '((:write 1 2 (8 9)) (:read 1 2 (8 9)) (:read 1 2 (8 9))))
       (fn2-native-device-image-slice-p effects 0 '(0 0 0 0) '(0 8 9 0)))))
(assert-event
 (mv-let (code effects)
  (fn2-native-device-effects (fn2-nde-test-trace '(:write :fence :read) '(1 -1 2 3 -3 -2)) 17)
  (and (eq code :ok) (equal effects '((:write 1 2 (8 9)) (:read 1 2 (8 9)) (:fence 0 0))))))
(assert-event
 (and (eq (fn2-nde-test-verdict (fn2-nde-test-trace '(:read :fence) '(2 1 -1 -2))) :ok)
      (eq (fn2-nde-test-verdict (fn2-nde-test-trace '(:read :fence) '(2 -2 1 -1))) :ok)))
; Only a begun, unreturned Write is an uncertain effect; in-flight Reads and
; Fences are none, and a Read never overlaps the uncertain Write.
(assert-event
 (and (equal (mv-list 2 (fn2-native-device-effects (fn2-nde-test-trace '(:read :read :fence) '(1 2 3)) 17))
             '(:ok nil))
      (equal (mv-list 2 (fn2-native-device-effects (fn2-nde-test-trace '(:read :write) '(1 -1 2)) 17))
             '(:ok ((:read 1 2 (8 9)) (:uncertain 1 2 :pending (8 9)))))))

; Teeth. Read after Write: a Read cannot begin before an earlier Write has
; returned, nor bypass a Fence to pass a Write submitted after that Fence.
(assert-event (fn2-nde-test-tooth '(:write :read) '(1 -1 2 -2) '(1 2 -1 -2)))
(assert-event (fn2-nde-test-tooth '(:write :read) '(1 -1 2 -2) '(2 -2 1 -1)))
(assert-event (fn2-nde-test-tooth '(:fence :write :read) '(1 -1 2 -2 3 -3) '(1 3 -3 -1 2 -2)))
; Write after Read: no Write begins while an earlier Read is in flight or
; still queued, including the second of two Reads.
(assert-event (fn2-nde-test-tooth '(:read :write) '(1 -1 2 -2) '(1 2 -1 -2)))
(assert-event (fn2-nde-test-tooth '(:read :write) '(1 -1 2 -2) '(2 -2 1 -1)))
(assert-event (fn2-nde-test-tooth '(:read :read :write) '(1 -1 2 -2 3 -3) '(1 -1 2 3 -2 -3)))
; Writes and Fences: never overlapping, never out of submission order.
(assert-event (fn2-nde-test-tooth '(:write :write) '(1 -1 2 -2) '(1 2 -1 -2)))
(assert-event (fn2-nde-test-tooth '(:write :write) '(1 -1 2 -2) '(2 -2 1 -1)))
(assert-event (fn2-nde-test-tooth '(:fence :write) '(1 -1 2 -2) '(2 -2 1 -1)))
(assert-event (fn2-nde-test-tooth '(:fence :write) '(1 -1 2 -2) '(1 2 -1 -2)))
(assert-event (fn2-nde-test-tooth '(:write :fence) '(1 -1 2 -2) '(2 -2 1 -1)))
(assert-event (fn2-nde-test-tooth '(:write :fence) '(1 -1 2 -2) '(1 2 -1 -2)))
(assert-event (fn2-nde-test-tooth '(:fence :fence) '(1 -1 2 -2) '(1 2 -1 -2)))
; One begin and one return per job, the return only from flight.
(assert-event (fn2-nde-test-tooth '(:read :read) '(1 2 -1 -2) '(1 1 -1 -2)))
(assert-event (fn2-nde-test-tooth '(:read :read) '(1 2 -1 -2) '(1 -2 2 -1)))
(assert-event (fn2-nde-test-tooth '(:read :read) '(1 2 -1 -2) '(1 2 -1 -1)))

; Reference: host/device.lisp's scheduler transliterated over job statuses
; (:queued :taken :begun :done) for jobs 1..n of KINDS, all submitted first.
; A finish only releases hazards and a take only adds them, so finishing at
; the return and taking at the begin lose no host schedule; Reads are taken
; from their ring's head, so earlier queued Reads are taken first. The pool
; size (4) never binds three jobs. MUTANT weakens or strengthens one rule.
(defun fn2-nde-ref-held-p (kinds st set)
 (and (consp kinds)
      (or (and (member-eq (car kinds) set) (member-eq (car st) '(:taken :begun)))
          (fn2-nde-ref-held-p (cdr kinds) (cdr st) set))))
; Greatest id below LIMIT of a KIND job (with STATUS, if given); 0 if none.
(defun fn2-nde-ref-last (kinds st kind status id limit best)
 (if (or (atom kinds) (not (natp id)) (not (natp limit)) (<= limit id)) best
  (fn2-nde-ref-last (cdr kinds) (cdr st) kind status (+ 1 id) limit
   (if (and (eq (car kinds) kind) (or (not status) (eq (car st) status))) id best))))
; Least queued id of a kind in SET: the head of its ring.
(defun fn2-nde-ref-head (kinds st set id)
 (if (atom kinds) nil
  (if (and (member-eq (car kinds) set) (eq (car st) :queued)) id
   (fn2-nde-ref-head (cdr kinds) (cdr st) set (+ 1 id)))))
; fn2-device-read-ready-p: no pwrite in progress, and every Write submitted
; before the Read has completed (write-completed >= after-write).
(defun fn2-nde-ref-read-ready-p (id kinds st mutant)
 (and (not (fn2-nde-ref-held-p kinds st '(:write)))
      (or (eq mutant :raw)
          (<= (fn2-nde-ref-last kinds st :write nil 1 id 0)
              (fn2-nde-ref-last kinds st :write :done 1 (+ 1 (len kinds)) 0)))
      (or (not (eq mutant :serial-reads)) (not (fn2-nde-ref-held-p kinds st '(:read))))))
; fn2-device-write-ready-p: no Read in pread, none older queued.
(defun fn2-nde-ref-write-ready-p (id kinds st mutant)
 (or (eq mutant :war)
     (and (not (fn2-nde-ref-held-p kinds st '(:read)))
          (let ((head (fn2-nde-ref-head kinds st '(:read) 1)))
           (not (and head (< head id)))))))
; fn2-device-take-write on the one writer thread: the queue head, once the
; thread is free; a Fence holds no Read.
(defun fn2-nde-ref-take-write-p (id kinds st mutant)
 (and (equal id (fn2-nde-ref-head kinds st '(:write :fence) 1))
      (or (eq mutant :writer-pool) (not (fn2-nde-ref-held-p kinds st '(:write :fence))))
      (if (and (eq (nth (- id 1) kinds) :fence) (not (eq mutant :fence-waits)))
          t
        (fn2-nde-ref-write-ready-p id kinds st mutant))))
; fn2-device-take-read from the ring head up to ID; NIL if a head is not ready.
(defun fn2-nde-ref-take-reads (id kinds st mutant fuel)
 (declare (xargs :measure (nfix fuel)))
 (if (zp fuel) nil
  (let ((head (fn2-nde-ref-head kinds st '(:read) 1)))
   (and head (posp head) (<= head id) (fn2-nde-ref-read-ready-p head kinds st mutant)
        (let ((st (update-nth (- head 1) :taken st)))
         (if (equal head id) st (fn2-nde-ref-take-reads id kinds st mutant (- fuel 1))))))))
(defun fn2-nde-ref-run (events kinds st mutant)
 (declare (xargs :verify-guards nil))
 (if (atom events) t
  (let* ((e (car events)) (id (if (< e 0) (- e) e)) (status (nth (- id 1) st)))
   (if (< 0 e)
       (let ((st (cond ((eq status :taken) st)
                       ((not (eq status :queued)) nil)
                       ((eq (nth (- id 1) kinds) :read)
                        (fn2-nde-ref-take-reads id kinds st mutant (len kinds)))
                       ((fn2-nde-ref-take-write-p id kinds st mutant) (update-nth (- id 1) :taken st))
                       (t nil))))
        (and st (fn2-nde-ref-run (cdr events) kinds (update-nth (- id 1) :begun st) mutant)))
     (and (eq status :begun)
          (fn2-nde-ref-run (cdr events) kinds (update-nth (- id 1) :done st) mutant))))))

; Every event sequence over jobs 1..n in which each job begins at most once
; and returns at most once, after its begin; every prefix included.
(defun fn2-nde-ref-moves (stage id)
 (if (atom stage) nil
  (append (case (car stage) (0 (list id)) (1 (list (- id))) (otherwise nil))
          (fn2-nde-ref-moves (cdr stage) (+ 1 id)))))
(mutual-recursion
 (defun fn2-nde-ref-sequences (stage rev)
  (declare (xargs :mode :program))
  (cons (reverse rev) (fn2-nde-ref-children (fn2-nde-ref-moves stage 1) stage rev)))
 (defun fn2-nde-ref-children (moves stage rev)
  (declare (xargs :mode :program))
  (if (atom moves) nil
   (let* ((e (car moves)) (i (- (if (< e 0) (- e) e) 1)))
    (append (fn2-nde-ref-sequences (update-nth i (+ 1 (nth i stage)) stage) (cons e rev))
            (fn2-nde-ref-children (cdr moves) stage rev))))))
(defun fn2-nde-ref-cons-all (x lists)
 (if (atom lists) nil (cons (cons x (car lists)) (fn2-nde-ref-cons-all x (cdr lists)))))
(defun fn2-nde-ref-kind-lists (n)
 (if (zp n) '(nil)
  (let ((shorter (fn2-nde-ref-kind-lists (- n 1))))
   (append (fn2-nde-ref-cons-all :read shorter)
           (fn2-nde-ref-cons-all :write shorter)
           (fn2-nde-ref-cons-all :fence shorter)))))
(defun fn2-nde-ref-initial (kinds)
 (if (atom kinds) nil (cons :queued (fn2-nde-ref-initial (cdr kinds)))))
; COUNTS: (disagreements decoder-accepted traces).
(defun fn2-nde-ref-census-1 (kinds sequences mutant counts)
 (declare (xargs :verify-guards nil))
 (if (atom sequences) counts
  (let ((decoded (eq (fn2-nde-test-verdict (fn2-nde-test-trace kinds (car sequences))) :ok))
        (host (fn2-nde-ref-run (car sequences) kinds (fn2-nde-ref-initial kinds) mutant)))
   (fn2-nde-ref-census-1 kinds (cdr sequences) mutant
    (list (+ (nfix (nth 0 counts)) (if (iff decoded host) 0 1))
          (+ (nfix (nth 1 counts)) (if decoded 1 0))
          (+ (nfix (nth 2 counts)) 1))))))
(defun fn2-nde-ref-census (kind-lists sequences mutant counts)
 (declare (xargs :verify-guards nil))
 (if (atom kind-lists) counts
  (fn2-nde-ref-census (cdr kind-lists) sequences mutant
   (fn2-nde-ref-census-1 (car kind-lists) sequences mutant counts))))
(defconst *fn2-nde-ref-kinds* (fn2-nde-ref-kind-lists 3))
(defconst *fn2-nde-ref-sequences* (fn2-nde-ref-sequences '(0 0 0) nil))
; The decoder admits exactly the host's schedules: 27 kind lists by 271 event
; sequences, 7317 traces, 1503 admitted by both, no disagreement.
(assert-event
 (equal (fn2-nde-ref-census *fn2-nde-ref-kinds* *fn2-nde-ref-sequences* nil '(0 0 0))
        '(0 1503 7317)))
; Teeth of that comparison: changing any one host rule makes it disagree. A
; Read ignoring earlier Writes, a Write ignoring earlier Reads, Reads one at a
; time, a second writer thread, a Fence that waits for Reads.
(defun fn2-nde-ref-mutant-teeth (mutants)
 (declare (xargs :verify-guards nil))
 (or (atom mutants)
     (and (< 0 (car (fn2-nde-ref-census *fn2-nde-ref-kinds* *fn2-nde-ref-sequences*
                                        (car mutants) '(0 0 0))))
          (fn2-nde-ref-mutant-teeth (cdr mutants)))))
(assert-event (fn2-nde-ref-mutant-teeth '(:raw :war :serial-reads :writer-pool :fence-waits)))
