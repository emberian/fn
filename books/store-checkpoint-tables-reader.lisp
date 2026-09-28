; fn: the schema-3 tables read from the octet buffer (lane checkpoint-pipeline,
; 2026-09-26; the buffer-level twin of books/store-checkpoint-tables.lisp's
; reader, in the shape rep-wave-d-3 gave the schema-2 reader, PRF-135).
;
; The host (host/native/io.lisp `fnn-state-checkpoint-plan') reads the file
; one segment at a time, each admitted by `fn-sccr-admit-segment' before it
; is read, appends every chunk into the buffer and hands the plan of frames
; (HEADER A B TRAILER) to `fn-store-sco-decode' (host/store-node-host.lisp),
; which calls `fn-sct-load' here.  A run is the plan's frames its first
; header counts, verified by the reader's chain check `fn-sccr-join'
; (unchanged); its program is the buffer's cells from its first frame's A
; to its last frame's B, run by `fn-sctr-run', the ref codec's stack
; machine by index, the codec's `fn-sccr-step' with the ref op.
;
; The twin `fn-sct-load-is-decode-file': for a well-shaped plan the buffer
; load is the list reader `fn-sct-decode-file' over the frames' octets, the
; same verdict on every input, corrupt ones included; so the tables book's
; keystone (the decode of the file written for a capture is the capture)
; transfers to what the host calls.

(in-package "ACL2")
(include-book "store-checkpoint-tables")
(include-book "store-checkpoint-reader")
(local (include-book "arithmetic/top" :dir :system))

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-sccb-frame-octets)
                          (:definition fn-sccr-plan-segments)
                          (:rewrite fn-sccr-cbor-octet-listp-is-scc-octet-listp)
                          (:rewrite fn-sccr-scc-octet-listp-is-cbor-octet-listp))))

; -----------------------------------------------------------------------------
; The slice, opened once (the reader's local facts, restated).

(local
 (defthm fn-sctr-slice-consp
   (equal (consp (fn-oct-slice-list i n fn-octets))
          (and (natp i) (natp n) (< i n)))
   :hints (("Goal" :expand ((fn-oct-slice-list i n fn-octets))))))

(local
 (defthm fn-sctr-slice-car
   (implies (and (natp i) (natp n) (< i n))
            (equal (car (fn-oct-slice-list i n fn-octets)) (nth i fn-octets)))
   :hints (("Goal" :expand ((fn-oct-slice-list i n fn-octets))
            :in-theory (enable fn-octets-get)))))

(local
 (defthm fn-sctr-slice-cdr
   (implies (and (natp i) (natp n))
            (equal (cdr (fn-oct-slice-list i n fn-octets))
                   (fn-oct-slice-list (1+ i) n fn-octets)))
   :hints (("Goal" :expand ((fn-oct-slice-list i n fn-octets)
                            (fn-oct-slice-list (1+ i) n fn-octets))))))

(local
 (defthm fn-sctr-slice-len
   (implies (and (natp i) (natp n) (<= i n))
            (equal (len (fn-oct-slice-list i n fn-octets)) (- n i)))
   :hints (("Goal" :induct (fn-oct-slice-list i n fn-octets)
            :in-theory (enable fn-oct-slice-list)))))

(local (in-theory (disable fn-oct-slice-list-is-take-nthcdr)))

; -----------------------------------------------------------------------------
; The stack machine by index with the ref op: (STACK . NEXT), NIL or
; :dangling, as `fn-sct-step' gives (STACK . REST), NIL or :dangling.

(defun fn-sctr-step (i end stack table fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp end) (< i end)
                              (<= end (fn-octets-len fn-octets)))
                  :guard-hints (("Goal" :use ((:instance fn-sccr-read-nat-facts (i (+ 1 i))))
                                 :in-theory (disable fn-sccr-read-nat-facts)))))
  (if (equal (fn-sccr-cell i fn-octets) *fn-sct-op-ref*)
      (let ((n (fn-sccr-read-nat (+ 1 i) end fn-octets)))
        (if (not n)
            nil
          (let ((v (fn-sct-ref-get (car n) table)))
            (if (not v) :dangling (cons (cons v stack) (cdr n))))))
    (fn-sccr-step i end stack fn-octets)))

; The codec's step by index is NIL or a cons (its every branch).
(local
 (defthm fn-sctr-sccr-step-shape
   (or (null (fn-sccr-step i end stack fn-octets))
       (consp (fn-sccr-step i end stack fn-octets)))
   :rule-classes ((:rewrite :corollary
                   (implies (not (consp (fn-sccr-step i end stack fn-octets)))
                            (equal (fn-sccr-step i end stack fn-octets) nil))))
   :hints (("Goal" :in-theory (e/d (fn-sccr-step)
                                   (fn-sccr-read-nat fn-sccr-read-string fn-sccr-cell
                                    fn-scc-intern fn-scc-package-index nth))))))

(defthm fn-sctr-step-is-step
  (implies (and (fn-octets-p fn-octets) (natp i) (natp end) (< i end)
                (<= end (len fn-octets)))
           (equal (fn-sct-step (fn-oct-slice-list i end fn-octets) stack table)
                  (let ((r (fn-sctr-step i end stack table fn-octets)))
                    (cond ((eq r :dangling) :dangling)
                          ((consp r) (cons (car r) (fn-oct-slice-list (cdr r) end fn-octets)))
                          (t nil)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-sccr-read-nat-facts (i (+ 1 i)))
                 (:instance fn-sccr-step-is-step)
                 (:instance fn-sctr-sccr-step-shape))
           :in-theory (e/d (fn-sct-step)
                           (nth fn-scc-read-nat fn-sccr-read-nat fn-scc-step fn-sccr-step
                            fn-sct-ref-get fn-sccr-read-nat-facts fn-sccr-step-is-step
                            fn-sctr-sccr-step-shape)))))

(defthm fn-sctr-step-advances
  (implies (and (fn-octets-p fn-octets) (natp i) (natp end) (< i end)
                (<= end (len fn-octets))
                (consp (fn-sctr-step i end stack table fn-octets)))
           (and (natp (cdr (fn-sctr-step i end stack table fn-octets)))
                (< i (cdr (fn-sctr-step i end stack table fn-octets)))
                (<= (cdr (fn-sctr-step i end stack table fn-octets)) end)))
  :rule-classes ((:rewrite)
                 (:linear :corollary
                  (implies (and (fn-octets-p fn-octets) (natp i) (natp end) (< i end)
                                (<= end (len fn-octets))
                                (consp (fn-sctr-step i end stack table fn-octets)))
                           (and (< i (cdr (fn-sctr-step i end stack table fn-octets)))
                                (<= (cdr (fn-sctr-step i end stack table fn-octets)) end)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-sccr-read-nat-facts (i (+ 1 i)))
                 (:instance fn-sccr-step-advances))
           :in-theory (e/d () (nth fn-sccr-read-nat fn-sccr-step fn-sct-ref-get
                               fn-sccr-read-nat-facts fn-sccr-step-advances)))))

(in-theory (disable fn-sctr-step))

(defun fn-sctr-run (i end stack table fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets)))
                  :measure (nfix (- end i))
                  :guard-hints (("Goal" :use ((:instance fn-sctr-step-advances))
                                 :in-theory (disable fn-sctr-step-advances)))))
  (if (or (not (natp i)) (not (natp end)) (>= i end))
      stack
    (let ((next (fn-sctr-step i end stack table fn-octets)))
      (cond ((eq next :dangling) :dangling)
            ((and (consp next)
                  (mbt (and (natp (cdr next)) (< i (cdr next)) (<= (cdr next) end))))
             (fn-sctr-run (cdr next) end (car next) table fn-octets))
            (t :refused)))))

(defthm fn-sctr-run-is-run
  (implies (and (fn-octets-p fn-octets) (natp i) (natp end) (<= i end)
                (<= end (len fn-octets)))
           (equal (fn-sctr-run i end stack table fn-octets)
                  (fn-sct-run (fn-oct-slice-list i end fn-octets) stack table)))
  :hints (("Goal" :induct (fn-sctr-run i end stack table fn-octets)
           :in-theory (e/d (fn-sct-run) (fn-sct-step floor mod nth)))))

(defun fn-sctr-decode-rows (start end table fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp start) (natp end) (<= start end)
                              (<= end (fn-octets-len fn-octets)))))
  (let ((st (fn-sctr-run start end nil table fn-octets)))
    (cond ((true-listp st) (list :ok (reverse st)))
          ((eq st :dangling) (list :refused :ref))
          (t (list :refused :tree)))))

(defthm fn-sctr-decode-rows-is-decode-rows
  (implies (and (fn-octets-p fn-octets) (natp start) (natp end) (<= start end)
                (<= end (len fn-octets)))
           (equal (fn-sctr-decode-rows start end table fn-octets)
                  (fn-sct-decode-rows (fn-oct-slice-list start end fn-octets) table)))
  :hints (("Goal" :in-theory (e/d (fn-sct-decode-rows) (fn-sct-run fn-sctr-run)))))

(in-theory (disable fn-sctr-run fn-sctr-decode-rows))

; -----------------------------------------------------------------------------
; A run over the plan: its first header's count of frames, joined by the
; reader's chain check from the genesis.  (:ok START END REST) or the
; refusal.

(defun fn-sctr-take-frames (n plan)
  (declare (xargs :guard (natp n)))
  (if (or (zp n) (not (consp plan)))
      nil
    (cons (car plan) (fn-sctr-take-frames (1- n) (cdr plan)))))

(defun fn-sctr-drop-frames (n plan)
  (declare (xargs :guard (natp n)))
  (if (or (zp n) (not (consp plan)))
      plan
    (fn-sctr-drop-frames (1- n) (cdr plan))))

(defun fn-sctr-plan-end (plan pos)
  ; Where the plan's frames end: the last frame's B, or POS when empty.
  (declare (xargs :guard t))
  (if (consp plan) (fn-sctr-plan-end (cdr plan) (fn-sccr-at 2 (car plan))) pos))

(local
 (defun fn-sctr-frames-ind (n plan pos)
   (if (or (zp n) (not (consp plan)))
       (list plan pos)
     (fn-sctr-frames-ind (1- n) (cdr plan) (fn-sccr-at 2 (car plan))))))

(defthm fn-sctr-take-frames-planp
  (implies (fn-sccr-planp plan pos fn-octets)
           (fn-sccr-planp (fn-sctr-take-frames n plan) pos fn-octets))
  :hints (("Goal" :induct (fn-sctr-frames-ind n plan pos)
           :in-theory (e/d (fn-sccr-planp) (fn-sccr-framep)))
          ("Subgoal *1/1" :use ((:instance fn-sccr-planp-pos)))))

(defthm fn-sctr-drop-frames-planp
  (implies (fn-sccr-planp plan pos fn-octets)
           (fn-sccr-planp (fn-sctr-drop-frames n plan)
                          (fn-sctr-plan-end (fn-sctr-take-frames n plan) pos)
                          fn-octets))
  :hints (("Goal" :induct (fn-sctr-frames-ind n plan pos)
           :in-theory (e/d (fn-sccr-planp) (fn-sccr-framep)))))

(local
 (defthm fn-sctr-parse-header-count-natp
   (implies (and (fn-scc-octet-listp seg) (fn-scc-parse-header seg))
            (natp (nth 1 (fn-scc-parse-header seg))))
   :hints (("Goal" :in-theory (enable fn-scc-parse-header fn-scc-u64-at)))))

; A plan's first frame: a true list whose header is 37 octets (the
; reader's local fact, restated for the guards below).
(local
 (defthm fn-sctr-planp-first-frame
   (implies (and (fn-sccr-planp plan pos fn-octets) (consp plan))
            (and (true-listp (car plan))
                 (consp (car plan))
                 (fn-scc-octet-listp (car (car plan)))
                 (fn-scc-octet-listp (fn-sccr-at 0 (car plan)))))
   :hints (("Goal" :expand ((fn-sccr-planp plan pos fn-octets))
            :in-theory (enable fn-sccr-framep)))))

(defun fn-sctr-run-decode (plan pos s fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (fn-sccr-planp plan pos fn-octets)
                  :guard-hints (("Goal" :in-theory (disable fn-scc-parse-header fn-sccr-join
                                                            fn-sccr-planp fn-sccr-framep)))))
  (let ((h (and (consp plan) (fn-scc-parse-header (fn-sccr-at 0 (car plan))))))
    (if (not h)
        (list :refused :header)
      (if (not (equal (nth 3 h) s))
          (list :refused :sequence)
        (let* ((count (nth 1 h))
               (run (fn-sctr-take-frames count plan))
               (j (fn-sccr-join run pos 0 count s *fn-scc-genesis* fn-octets)))
          (if (not (eq (car j) :ok))
              j
            (list :ok pos (nth 1 j) (fn-sctr-drop-frames count plan))))))))

(in-theory (disable fn-sctr-run-decode))

; -----------------------------------------------------------------------------
; The four runs' rows from their buffer ranges, and the tables: the list
; reader's `fn-sct-decode-programs' over ranges.

(defun fn-sctr-decode-programs (fa fb pa pb ea eb ra rb fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp fa) (natp fb) (<= fa fb) (<= fb (fn-octets-len fn-octets))
                              (natp pa) (natp pb) (<= pa pb) (<= pb (fn-octets-len fn-octets))
                              (natp ea) (natp eb) (<= ea eb) (<= eb (fn-octets-len fn-octets))
                              (natp ra) (natp rb) (<= ra rb) (<= rb (fn-octets-len fn-octets)))))
  (let ((f (fn-sctr-decode-rows fa fb nil fn-octets)))
    (if (not (eq (car f) :ok))
        f
      (let ((frows (cadr f)))
        (if (not (and (consp frows) (null (cdr frows)) (fn-sct-f-rowp (car frows))))
            (list :refused :f-row)
          (let* ((frow (car frows))
                 (s (cadr frow))
                 (p (fn-sctr-decode-rows pa pb nil fn-octets)))
            (if (not (eq (car p) :ok))
                p
              (if (not (equal (len (cadr p)) s))
                  (list :refused :close)
                (let* ((table (fn-cei-build (cadr p)))
                       (e (fn-sctr-decode-rows ea eb table fn-octets)))
                  (if (not (eq (car e) :ok))
                      e
                    (if (not (equal (len (cadr e)) s))
                        (list :refused :close)
                      (let ((r (fn-sctr-decode-rows ra rb table fn-octets)))
                        (if (not (eq (car r) :ok))
                            r
                          (if (not (equal (len (cadr r)) 4))
                              (list :refused :close)
                            (list :ok (list frow (cadr p) (cadr e) (cadr r)))))))))))))))))

(defthm fn-sctr-decode-programs-is-decode-programs
  (implies (and (fn-octets-p fn-octets)
                (natp fa) (natp fb) (<= fa fb) (<= fb (len fn-octets))
                (natp pa) (natp pb) (<= pa pb) (<= pb (len fn-octets))
                (natp ea) (natp eb) (<= ea eb) (<= eb (len fn-octets))
                (natp ra) (natp rb) (<= ra rb) (<= rb (len fn-octets)))
           (equal (fn-sctr-decode-programs fa fb pa pb ea eb ra rb fn-octets)
                  (fn-sct-decode-programs
                   (list (fn-oct-slice-list fa fb fn-octets) (fn-oct-slice-list pa pb fn-octets)
                         (fn-oct-slice-list ea eb fn-octets) (fn-oct-slice-list ra rb fn-octets)))))
  :hints (("Goal" :in-theory (e/d (fn-sct-decode-programs)
                                  (fn-sct-decode-rows fn-sctr-decode-rows fn-cei-build
                                   fn-sct-f-rowp)))))

(in-theory (disable fn-sctr-decode-programs))

; -----------------------------------------------------------------------------
; The host-called entry (host/store-node-host.lisp `fn-store-sco-decode'):
; the tables of the plan the host read, or the refusal by name.

; A run's END is where the rest of the plan begins (the plan is contiguous).
(local
 (defthm fn-sctr-plan-end-is-first-a
   (implies (and (fn-sccr-planp plan pos fn-octets)
                 (consp (fn-sctr-drop-frames n plan)))
            (equal (fn-sccr-at 1 (car (fn-sctr-drop-frames n plan)))
                   (fn-sctr-plan-end (fn-sctr-take-frames n plan) pos)))
   :hints (("Goal" :induct (fn-sctr-frames-ind n plan pos)
            :in-theory (e/d (fn-sccr-planp) (fn-sccr-framep fn-sccr-at-is-nth))))))

(local
 (defthm fn-sctr-join-end-is-plan-end
   (implies (and (fn-sccr-planp plan pos fn-octets)
                 (eq (car (fn-sccr-join plan pos index count sequence prev fn-octets)) :ok))
            (equal (nth 1 (fn-sccr-join plan pos index count sequence prev fn-octets))
                   (fn-sctr-plan-end plan pos)))
   :hints (("Goal" :induct (fn-sccr-join plan pos index count sequence prev fn-octets)
            :in-theory (e/d (fn-sccr-join fn-sccr-planp)
                            (fn-sccr-open-frame fn-sccr-framep fn-sccr-at-is-nth))))))

(local
 (defthm fn-sctr-run-decode-ok-shape
   (implies (and (fn-sccr-planp plan pos fn-octets)
                 (eq (car (fn-sctr-run-decode plan pos s fn-octets)) :ok))
            (and (equal (nth 1 (fn-sctr-run-decode plan pos s fn-octets)) pos)
                 (natp (nth 2 (fn-sctr-run-decode plan pos s fn-octets)))
                 (<= pos (nth 2 (fn-sctr-run-decode plan pos s fn-octets)))
                 (<= (nth 2 (fn-sctr-run-decode plan pos s fn-octets)) (len fn-octets))
                 (natp pos)
                 (fn-sccr-planp (nth 3 (fn-sctr-run-decode plan pos s fn-octets))
                                (nth 2 (fn-sctr-run-decode plan pos s fn-octets))
                                fn-octets)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-sccr-join-ok-end
                             (plan (fn-sctr-take-frames
                                    (nth 1 (fn-scc-parse-header (fn-sccr-at 0 (car plan)))) plan))
                             (index 0)
                             (count (nth 1 (fn-scc-parse-header (fn-sccr-at 0 (car plan)))))
                             (sequence s) (prev *fn-scc-genesis*))
                  (:instance fn-sctr-drop-frames-planp
                             (n (nth 1 (fn-scc-parse-header (fn-sccr-at 0 (car plan))))))
                  (:instance fn-sctr-join-end-is-plan-end
                             (plan (fn-sctr-take-frames
                                    (nth 1 (fn-scc-parse-header (fn-sccr-at 0 (car plan)))) plan))
                             (index 0)
                             (count (nth 1 (fn-scc-parse-header (fn-sccr-at 0 (car plan)))))
                             (sequence s) (prev *fn-scc-genesis*))
                  (:instance fn-sccr-planp-pos))
            :in-theory (e/d (fn-sctr-run-decode)
                            (fn-scc-parse-header fn-sccr-join fn-sccr-planp
                             fn-sccr-join-ok-end fn-sctr-drop-frames-planp
                             fn-sctr-join-end-is-plan-end fn-sccr-planp-pos
                             fn-sccr-at-is-nth))))))

; One run from where the rest of the plan begins (its first frame's A); no
; frames left is a missing header, as the list reader says.
; The rest of a plan: no frames, or a plan from its first frame's A.
(defun fn-sctr-restp (rest fn-octets)
  (declare (xargs :stobjs fn-octets :guard t))
  (or (not (consp rest))
      (fn-sccr-planp rest (fn-sccr-at 1 (car rest)) fn-octets)))

(defun fn-sctr-next-run (rest s fn-octets)
  (declare (xargs :stobjs fn-octets :guard (fn-sctr-restp rest fn-octets)))
  (if (consp rest)
      (fn-sctr-run-decode rest (fn-sccr-at 1 (car rest)) s fn-octets)
    (list :refused :header)))

(defun fn-sct-load (plan fn-octets)
  (declare (xargs :stobjs fn-octets :guard t :verify-guards nil))
  (let ((start (if (consp plan) (fn-sccr-at 1 (car plan)) 0)))
    (if (not (fn-sccr-planp plan start fn-octets))
        (list :refused :layout)
      (let ((h (and (consp plan) (fn-scc-parse-header (fn-sccr-at 0 (car plan))))))
        (if (not h)
            (list :refused :header)
          (let* ((s (nth 3 h))
                 (f (fn-sctr-next-run plan s fn-octets)))
            (if (not (eq (car f) :ok))
                f
              (let ((p (fn-sctr-next-run (nth 3 f) s fn-octets)))
                (if (not (eq (car p) :ok))
                    p
                  (let ((e (fn-sctr-next-run (nth 3 p) s fn-octets)))
                    (if (not (eq (car e) :ok))
                        e
                      (let ((r (fn-sctr-next-run (nth 3 e) s fn-octets)))
                        (if (not (eq (car r) :ok))
                            r
                          (if (consp (nth 3 r))
                              (list :refused :trailing)
                            (let ((tables (fn-sctr-decode-programs
                                           (nth 1 f) (nth 2 f) (nth 1 p) (nth 2 p)
                                           (nth 1 e) (nth 2 e) (nth 1 r) (nth 2 r) fn-octets)))
                              (if (not (eq (car tables) :ok))
                                  tables
                                (if (not (equal (fn-sco-at 1 (fn-sct-tables-f (cadr tables))) s))
                                    (list :refused :close)
                                  tables)))))))))))))))))

; -----------------------------------------------------------------------------
; The twin: the buffer load is the list reader over the frames' octets.

; List facts the reader keeps local, restated.
(local
 (defthm fn-sctr-len-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthm fn-sctr-long-enoughp-is-len
   (implies (natp n)
            (equal (fn-scc-long-enoughp n xs) (<= n (len xs))))))

(local
 (defthm fn-sctr-take-of-append-short
   (implies (and (natp k) (<= k (len a)))
            (equal (take k (append a b)) (take k a)))))

(local
 (defthm fn-sctr-nthcdr-of-append-short
   (implies (and (natp k) (<= k (len a)))
            (equal (nthcdr k (append a b)) (append (nthcdr k a) b)))))

(local
 (defthm fn-sctr-nth-of-append-short
   (implies (and (natp k) (< k (len a)))
            (equal (nth k (append a b)) (nth k a)))))

(local
 (defthm fn-sctr-take-all
   (implies (and (true-listp x) (equal k (len x)))
            (equal (take k x) x))))

(local
 (defthm fn-sctr-nthcdr-all
   (implies (and (true-listp x) (equal k (len x)))
            (equal (nthcdr k x) nil))))

(local
 (defthm fn-sctr-len-nthcdr
   (implies (and (natp n) (<= n (len xs)))
            (equal (len (nthcdr n xs)) (- (len xs) n)))))

(local
 (defthm fn-sctr-true-listp-nthcdr
   (implies (true-listp x) (true-listp (nthcdr n x)))))

; A 37-octet header in front of anything parses as itself with the rest
; behind it; a frame's octets parse as its header list (the reader's local
; facts, restated).
(local
 (defthm fn-sctr-parse-header-of-append
   (implies (and (fn-scc-octet-listp header)
                 (equal (len header) *fn-scc-segment-header-octets*))
            (equal (fn-scc-parse-header (append header rest))
                   (and (fn-scc-parse-header header)
                        (list (nth 0 (fn-scc-parse-header header))
                              (nth 1 (fn-scc-parse-header header))
                              (nth 2 (fn-scc-parse-header header))
                              (nth 3 (fn-scc-parse-header header))
                              rest))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-scc-parse-header fn-scc-u64-at)
                            (fn-scc-le-value))))))

(local
 (defthm fn-sctr-parse-header-of-frame-octets
   (implies (and (fn-octets-p fn-octets) (fn-sccr-framep frame fn-octets))
            (equal (fn-scc-parse-header (fn-sccb-frame-octets frame fn-octets))
                   (and (fn-scc-parse-header (nth 0 frame))
                        (list (nth 0 (fn-scc-parse-header (nth 0 frame)))
                              (nth 1 (fn-scc-parse-header (nth 0 frame)))
                              (nth 2 (fn-scc-parse-header (nth 0 frame)))
                              (nth 3 (fn-scc-parse-header (nth 0 frame)))
                              (append (fn-oct-slice-list (nth 1 frame) (nth 2 frame)
                                                         fn-octets)
                                      (nth 3 frame))))))
   :hints (("Goal" :in-theory (e/d (fn-sccb-frame-octets fn-sccr-framep)
                                   (fn-scc-parse-header))))))

(local
 (defthm fn-sctr-plan-segments-of-take
   (equal (fn-sccr-plan-segments (fn-sctr-take-frames n plan) fn-octets)
          (fn-sct-take-segs n (fn-sccr-plan-segments plan fn-octets)))
   :hints (("Goal" :in-theory (enable fn-sccr-plan-segments)))))

(local
 (defthm fn-sctr-plan-segments-of-drop
   (equal (fn-sccr-plan-segments (fn-sctr-drop-frames n plan) fn-octets)
          (fn-sct-drop-segs n (fn-sccr-plan-segments plan fn-octets)))
   :hints (("Goal" :in-theory (enable fn-sccr-plan-segments)))))

(local
 (defthm fn-sctr-plan-segments-consp
   (equal (consp (fn-sccr-plan-segments plan fn-octets)) (consp plan))
   :hints (("Goal" :in-theory (enable fn-sccr-plan-segments)))))

(local
 (defthm fn-sctr-plan-segments-car
   (implies (consp plan)
            (equal (car (fn-sccr-plan-segments plan fn-octets))
                   (fn-sccb-frame-octets (car plan) fn-octets)))
   :hints (("Goal" :in-theory (enable fn-sccr-plan-segments)))))

(local
 (defthm fn-sctr-planp-framep
   (implies (and (fn-sccr-planp plan pos fn-octets) (consp plan))
            (fn-sccr-framep (car plan) fn-octets))
   :hints (("Goal" :expand ((fn-sccr-planp plan pos fn-octets))))))

(local
 (defthm fn-sctr-genesis-octets
   (fn-scc-octet-listp *fn-scc-genesis*)))

; A plan is a plan from its own first frame's A.
(local
 (defthm fn-sctr-planp-from-first-a
   (implies (and (fn-sccr-planp plan pos fn-octets) (consp plan))
            (fn-sccr-planp plan (fn-sccr-at 1 (car plan)) fn-octets))
   :hints (("Goal" :expand ((fn-sccr-planp plan pos fn-octets)
                            (fn-sccr-planp plan (fn-sccr-at 1 (car plan)) fn-octets))))))

(defthm fn-sctr-run-decode-is-run-decode
  (implies (and (fn-octets-p fn-octets) (consp plan)
                (fn-sccr-planp plan (fn-sccr-at 1 (car plan)) fn-octets))
           (equal (fn-sct-run-decode (fn-sccr-plan-segments plan fn-octets) s)
                  (let ((r (fn-sctr-run-decode plan (fn-sccr-at 1 (car plan)) s fn-octets)))
                    (if (eq (car r) :ok)
                        (list :ok (fn-oct-slice-list (nth 1 r) (nth 2 r) fn-octets)
                              (fn-sccr-plan-segments (nth 3 r) fn-octets))
                      r))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-sccr-join-is-join
                            (plan (fn-sctr-take-frames
                                   (nth 1 (fn-scc-parse-header (fn-sccr-at 0 (car plan)))) plan))
                            (pos (fn-sccr-at 1 (car plan)))
                            (index 0)
                            (count (nth 1 (fn-scc-parse-header (fn-sccr-at 0 (car plan)))))
                            (sequence s) (prev *fn-scc-genesis*) (racc nil))
                 (:instance fn-sctr-planp-first-frame (pos (fn-sccr-at 1 (car plan))))
                 (:instance fn-sctr-planp-framep (pos (fn-sccr-at 1 (car plan)))))
           :in-theory (e/d (fn-sct-run-decode fn-sctr-run-decode)
                           (fn-scc-parse-header fn-scc-join fn-sccr-join fn-sccr-join-is-join
                            fn-sccr-planp fn-sccr-framep fn-sccb-frame-octets
                            fn-sctr-planp-first-frame fn-sctr-planp-framep
                            fn-sccr-at-is-nth)))))

(local
 (defthm fn-sctr-plan-segments-nil
   (implies (not (consp plan))
            (equal (fn-sccr-plan-segments plan fn-octets) nil))
   :hints (("Goal" :in-theory (enable fn-sccr-plan-segments)))))

(local
 (defthm fn-sctr-run-decode-of-nil
   (equal (fn-sct-run-decode nil s) (list :refused :header))
   :hints (("Goal" :in-theory (enable fn-sct-run-decode)))))

; The next run over the plan's rest, on both sides.
(local
 (defthm fn-sctr-next-run-is-run-decode
   (implies (and (fn-octets-p fn-octets) (fn-sctr-restp rest fn-octets))
            (equal (fn-sct-run-decode (fn-sccr-plan-segments rest fn-octets) s)
                   (let ((r (fn-sctr-next-run rest s fn-octets)))
                     (if (eq (car r) :ok)
                         (list :ok (fn-oct-slice-list (nth 1 r) (nth 2 r) fn-octets)
                               (fn-sccr-plan-segments (nth 3 r) fn-octets))
                       r))))
   :hints (("Goal" :do-not-induct t
            :cases ((consp rest))
            :in-theory (e/d (fn-sctr-next-run fn-sctr-restp)
                            (fn-sct-run-decode fn-sctr-run-decode fn-scc-parse-header
                             fn-sccb-frame-octets fn-sccr-planp fn-sccr-framep
                             fn-sccr-at-is-nth fn-sctr-planp-first-frame))))))

(local
 (defthm fn-sctr-next-run-ok-shape
   (implies (and (fn-sctr-restp rest fn-octets)
                 (eq (car (fn-sctr-next-run rest s fn-octets)) :ok))
            (and (natp (nth 1 (fn-sctr-next-run rest s fn-octets)))
                 (natp (nth 2 (fn-sctr-next-run rest s fn-octets)))
                 (<= (nth 1 (fn-sctr-next-run rest s fn-octets))
                     (nth 2 (fn-sctr-next-run rest s fn-octets)))
                 (<= (nth 2 (fn-sctr-next-run rest s fn-octets)) (len fn-octets))
                 (fn-sctr-restp (nth 3 (fn-sctr-next-run rest s fn-octets)) fn-octets)))
   :hints (("Goal" :use ((:instance fn-sctr-run-decode-ok-shape (plan rest)
                                    (pos (fn-sccr-at 1 (car rest))))
                         (:instance fn-sctr-planp-from-first-a
                                    (plan (nth 3 (fn-sctr-run-decode rest (fn-sccr-at 1 (car rest))
                                                                     s fn-octets)))
                                    (pos (nth 2 (fn-sctr-run-decode rest (fn-sccr-at 1 (car rest))
                                                                    s fn-octets)))))
            :in-theory (e/d (fn-sctr-next-run fn-sctr-restp)
                            (fn-sctr-run-decode fn-sctr-run-decode-ok-shape
                             fn-sctr-planp-from-first-a fn-sccr-planp fn-sccr-at-is-nth))))))

(local
 (defthm fn-sctr-restp-of-plan
   (implies (fn-sccr-planp plan (if (consp plan) (fn-sccr-at 1 (car plan)) 0) fn-octets)
            (fn-sctr-restp plan fn-octets))
   :hints (("Goal" :in-theory (enable fn-sctr-restp)))))

(in-theory (disable fn-sctr-next-run fn-sctr-restp))

; The host-called load is guard-verified: the reader runs raw from the
; host's plan (host/native/io.lisp fnn-state-checkpoint-load).
(verify-guards fn-sct-load)

(defthm fn-sct-load-is-decode-file
  (implies (and (fn-octets-p fn-octets)
                (fn-sccr-planp plan (if (consp plan) (fn-sccr-at 1 (car plan)) 0) fn-octets))
           (equal (fn-sct-load plan fn-octets)
                  (fn-sct-decode-file (fn-sccr-plan-segments plan fn-octets))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-sctr-planp-first-frame
                            (pos (if (consp plan) (fn-sccr-at 1 (car plan)) 0)))
                 (:instance fn-sctr-planp-framep
                            (pos (if (consp plan) (fn-sccr-at 1 (car plan)) 0))))
           :in-theory (e/d (fn-sct-load fn-sct-decode-file)
                           (fn-scc-parse-header fn-sctr-run-decode fn-sct-run-decode
                            fn-sccr-planp fn-sccr-framep fn-sccb-frame-octets
                            fn-sct-decode-programs fn-sctr-decode-programs
                            fn-sctr-planp-first-frame fn-sctr-planp-framep
                            fn-sccr-at-is-nth fn-sctr-restp)))))

(in-theory (disable fn-sct-load))
