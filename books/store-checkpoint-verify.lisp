; fn: the read-back of an installed state checkpoint before the log
; segments it covers are dropped (sweep 2026-10-03 S045).
;
; Once a checkpoint covers segments 1..K-1 the host unlinks them
; (host/native/io.lisp fnn-log-drop, T8): from then on the checkpoint is the
; only copy of that history, and an open that cannot use it refuses
; :checkpoint-damaged (books/store-log-segments.lisp fn-lgs-open-plan).  The
; rename that installs a checkpoint also replaces the previous one.  So the
; staged file is read back from disk and verified here BEFORE the rename
; (host/native/io.lisp fnn-state-checkpoint-stage): a file whose bytes on
; disk are not the frames the writer sealed is a known failure, the old
; checkpoint and every segment stay.
;
; The verify streams: the host reads one segment at a time (header, chunk,
; trailer; each admitted against the profile's segment and file bounds by
; fn-sccr-admit-segment first, as the open reads), puts the chunk alone in
; the publication buffer and calls `fn-sccv-step' with the frame
; (HEADER 0 N TRAILER).  Work and allocation per call are one segment's.
; The state V is (RUNS INDEX COUNT SEQUENCE PREV): the runs completed, the
; frame index within the current run, its count (0 at a run's start: the
; first frame's header names it), the sequence the writer wrote in every
; header (the host passes it), and the previous trailer of the chain
; (*fn-scc-genesis* at a run's start).  A refusal is (:refused REASON) and
; stays.  `fn-sccv-final' accepts exactly *fn-sccv-runs* complete runs.
;
; KEYSTONE `fn-sccv-final-ok-is-runs-ok': when the fold of the step over the
; file's segments (as octet lists) is accepted, the segments are exactly
; five consecutive runs, each joining under the list codec's own chain
; check `fn-scc-join' (books/store-checkpoint-codec.lisp) from index 0 with
; its first header's count, the given sequence and the genesis: the framing
; the open's reader checks (fn-sccr-join-is-join).  `fn-sccv-step-is-seg-
; step' is the buffer step's equality with the list step on the frame's
; octets (fn-sccb-frame-octets: the header, the chunk, the trailer).  What
; the verify does not decide: the decode of the runs' contents (the arena
; tag, the tables), which `fn-scka-load-of-written-file' says of every file
; the writer produces, and the history image region in front of the frames
; (its pages are checked at the open's first touch).
(in-package "ACL2")
(include-book "store-checkpoint-reader")
(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (disable (tau-system))))

; The arena run and the four tables (F, P, E, R): fn-scka-open-run takes
; one run, fn-scka-finish's fn-sct-load four and refuses anything after.
(defconst *fn-sccv-runs* 5)

(defun fn-sccv-livep (v)
  (declare (xargs :guard t))
  (and (true-listp v) (equal (len v) 5)
       (natp (nth 0 v)) (natp (nth 1 v)) (natp (nth 2 v)) (natp (nth 3 v))
       (fn-scc-octet-listp (nth 4 v))))

(defun fn-sccv-initial (sequence)
  (declare (xargs :guard t))
  (list 0 0 0 (nfix sequence) *fn-scc-genesis*))

; The count the frame is checked against: its own header's at a run's start.
(defun fn-sccv-count (v h)
  (declare (xargs :guard (and (fn-sccv-livep v) (true-listp h))))
  (if (zp (nth 1 v)) (nth 1 h) (nth 2 v)))

(defun fn-sccv-prev (v)
  (declare (xargs :guard (fn-sccv-livep v)))
  (if (zp (nth 1 v)) *fn-scc-genesis* (nth 4 v)))

; After a frame of COUNT whose trailer is O: the next frame, or the next
; run's start.
(defun fn-sccv-advance (v count o)
  (declare (xargs :guard (and (fn-sccv-livep v) (natp count))))
  (if (equal (+ 1 (nth 1 v)) count)
      (list (+ 1 (nth 0 v)) 0 0 (nth 3 v) *fn-scc-genesis*)
    (list (nth 0 v) (+ 1 (nth 1 v)) count (nth 3 v) o)))

; The list step: SEG is one segment's octets (header, chunk, trailer).
(defun fn-sccv-seg-step (v seg)
  (declare (xargs :guard (fn-scc-octet-listp seg)
                  :guard-hints (("Goal" :in-theory (disable fn-scc-parse-header
                                                            fn-scc-open-segment)))))
  (if (not (fn-sccv-livep v))
      v
    (let ((h (fn-scc-parse-header seg)))
      (if (not h)
          (list :refused :header)
        (let* ((count (fn-sccv-count v h))
               (o (and (posp count)
                       (fn-scc-open-segment seg (nth 1 v) count (nth 3 v)
                                            (fn-sccv-prev v)))))
          (if (not o)
              (list :refused :segment)
            (fn-sccv-advance v count (cadr o))))))))

(defun fn-sccv-segs (v segs)
  (declare (xargs :guard (fn-scc-segment-listp segs)))
  (if (consp segs)
      (fn-sccv-segs (fn-sccv-seg-step v (car segs)) (cdr segs))
    v))

; (:ok SEQUENCE) after exactly five complete runs, else the refusal.
(defun fn-sccv-final (v)
  (declare (xargs :guard t))
  (cond ((not (fn-sccv-livep v))
         (if (and (consp v) (eq (car v) :refused)) v (list :refused :malformed)))
        ((and (equal (nth 0 v) *fn-sccv-runs*) (zp (nth 1 v)))
         (list :ok (nth 3 v)))
        (t (list :refused :truncated))))

; -----------------------------------------------------------------------------
; The host-called step: the frame (HEADER A B TRAILER) over the buffer.

(defun fn-sccv-step (v frame fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (fn-sccr-framep frame fn-octets)
                  :guard-hints (("Goal" :in-theory (e/d (fn-sccr-framep)
                                                        (fn-scc-parse-header
                                                         fn-sccr-open-frame))))))
  (if (not (fn-sccv-livep v))
      v
    (let ((h (fn-scc-parse-header (nth 0 frame))))
      (if (not h)
          (list :refused :header)
        (let* ((count (fn-sccv-count v h))
               (o (and (posp count)
                       (fn-sccr-open-frame frame (nth 1 v) count (nth 3 v)
                                           (fn-sccv-prev v) fn-octets))))
          (if (not o)
              (list :refused :segment)
            (fn-sccv-advance v count o)))))))

; -----------------------------------------------------------------------------
; The step's twin: the buffer step is the list step on the frame's octets.

(local
 (defthm fn-sccv-true-list-fix-of-octets
   (implies (fn-scc-octet-listp x) (equal (true-list-fix x) x))
   :hints (("Goal" :in-theory (enable fn-scc-octet-listp)))))

(local
 (defthm fn-sccv-parse-frame-octets
   (implies (and (fn-octets-p fn-octets) (fn-sccr-framep frame fn-octets))
            (and (iff (fn-scc-parse-header (fn-sccb-frame-octets frame fn-octets))
                      (fn-scc-parse-header (nth 0 frame)))
                 (equal (nth 1 (fn-scc-parse-header (fn-sccb-frame-octets frame fn-octets)))
                        (nth 1 (fn-scc-parse-header (nth 0 frame))))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-sccr-parse-header-of-append (header (nth 0 frame))
                             (rest (append (fn-oct-slice-list (nth 1 frame) (nth 2 frame)
                                                              fn-octets)
                                           (nth 3 frame)))))
            :in-theory (e/d (fn-sccr-framep fn-sccb-frame-octets)
                            (fn-scc-parse-header fn-sccr-parse-header-of-append))))))

(defthm fn-sccv-step-is-seg-step
  (implies (and (fn-octets-p fn-octets) (fn-sccr-framep frame fn-octets))
           (equal (fn-sccv-step v frame fn-octets)
                  (fn-sccv-seg-step v (fn-sccb-frame-octets frame fn-octets))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-sccr-open-segment-of-frame)
                           (fn-scc-open-segment fn-sccr-open-frame fn-scc-parse-header
                            fn-sccb-frame-octets)))))

; -----------------------------------------------------------------------------
; The fold: an accepted file is five runs, each joining.

(local
 (defthm fn-sccv-segs-of-dead
   (implies (not (fn-sccv-livep v))
            (equal (fn-sccv-segs v segs) v))
   :hints (("Goal" :in-theory (enable fn-sccv-segs fn-sccv-seg-step)))))

(local
 (defthm fn-sccv-runs-monotone
   (implies (and (fn-sccv-livep v)
                 (fn-sccv-livep (fn-sccv-segs v segs)))
            (<= (nth 0 v) (nth 0 (fn-sccv-segs v segs))))
   :rule-classes :linear
   :hints (("Goal" :induct (fn-sccv-segs v segs)
            :in-theory (e/d (fn-sccv-segs fn-sccv-seg-step fn-sccv-advance)
                            (fn-scc-open-segment fn-scc-parse-header))))))

(local
 (defthm fn-sccv-segs-of-atom
   (implies (not (consp segs)) (equal (fn-sccv-segs v segs) v))
   :hints (("Goal" :in-theory (enable fn-sccv-segs)))))

(local
 (defthm fn-sccv-final-of-dead
   (implies (not (fn-sccv-livep v))
            (not (equal (car (fn-sccv-final v)) :ok)))
   :hints (("Goal" :in-theory (enable fn-sccv-final)))))

(local
 (defthm fn-sccv-final-ok-at-run-start
   (implies (equal (car (fn-sccv-final v)) :ok)
            (and (fn-sccv-livep v) (equal (nth 1 v) 0) (equal (nth 0 v) *fn-sccv-runs*)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-sccv-final)))))

(local
 (defthm fn-sccv-final-not-ok-mid-run
   (implies (not (equal (nth 1 v) 0))
            (not (equal (car (fn-sccv-final v)) :ok)))
   :hints (("Goal" :in-theory (enable fn-sccv-final)))))

(local
 (defthm fn-sccv-final-not-ok-short
   (implies (not (equal (nth 0 v) *fn-sccv-runs*))
            (not (equal (car (fn-sccv-final v)) :ok)))
   :hints (("Goal" :in-theory (enable fn-sccv-final)))))

(local
 (defun fn-sccv-mid-ind (segs r i c q p racc)
   (declare (xargs :measure (len segs) :verify-guards nil))
   (if (consp segs)
       (let ((o (fn-scc-open-segment (car segs) i c q p)))
         (if (and o (< (+ 1 i) c))
             (fn-sccv-mid-ind (cdr segs) r (+ 1 i) c q (cadr o) (revappend (car o) racc))
           (list r i c q p racc)))
     (list r i c q p racc))))

; Inside a run (frame I of C, I > 0): the run's last C - I frames join and
; the fold goes on from the next run's start.
(local
 (defthm fn-sccv-mid-run
   (implies (and (natp r) (posp i) (natp c) (< i c) (natp q) (fn-scc-octet-listp p)
                 (equal (car (fn-sccv-final (fn-sccv-segs (list r i c q p) segs))) :ok))
            (and (<= (- c i) (len segs))
                 (equal (car (fn-scc-join (take (- c i) segs) i c q p racc)) :ok)
                 (equal (car (fn-sccv-final (fn-sccv-segs (list (+ 1 r) 0 0 q *fn-scc-genesis*)
                                                          (nthcdr (- c i) segs))))
                        :ok)))
   :hints (("Goal" :induct (fn-sccv-mid-ind segs r i c q p racc)
            :expand ((fn-sccv-segs (list r i c q p) segs))
            :in-theory (e/d (fn-sccv-seg-step fn-sccv-advance fn-sccv-count fn-sccv-prev
                                              fn-scc-join)
                            (fn-scc-open-segment fn-scc-parse-header fn-sccv-final))))))

; At a run's start: the first header's count of frames join from index 0.
(local
 (defthm fn-sccv-first-frame
   (implies (and (consp segs) (natp r) (natp q)
                 (equal (car (fn-sccv-final (fn-sccv-segs (list r 0 0 q *fn-scc-genesis*) segs)))
                        :ok))
            (let* ((h (fn-scc-parse-header (car segs))) (count (nth 1 h)))
              (and h (posp count) (<= count (len segs))
                   (equal (car (fn-scc-join (take count segs) 0 count q *fn-scc-genesis* nil))
                          :ok)
                   (equal (car (fn-sccv-final
                                (fn-sccv-segs (list (+ 1 r) 0 0 q *fn-scc-genesis*)
                                              (nthcdr count segs))))
                          :ok))))
   :hints (("Goal" :do-not-induct t
            :expand ((fn-sccv-segs (list r 0 0 q *fn-scc-genesis*) segs)
                     (take (nth 1 (fn-scc-parse-header (car segs))) segs)
                     (nthcdr (nth 1 (fn-scc-parse-header (car segs))) segs)
                     (fn-scc-join (cons (car segs)
                                        (take (+ -1 (nth 1 (fn-scc-parse-header (car segs))))
                                              (cdr segs)))
                                  0 (nth 1 (fn-scc-parse-header (car segs))) q
                                  *fn-scc-genesis* nil))
            :use ((:instance fn-sccv-mid-run (segs (cdr segs)) (i 1)
                             (c (nth 1 (fn-scc-parse-header (car segs))))
                             (p (cadr (fn-scc-open-segment
                                       (car segs) 0 (nth 1 (fn-scc-parse-header (car segs)))
                                       q *fn-scc-genesis*)))
                             (racc (revappend (car (fn-scc-open-segment
                                                    (car segs) 0
                                                    (nth 1 (fn-scc-parse-header (car segs)))
                                                    q *fn-scc-genesis*))
                                              nil))))
            :in-theory (e/d (fn-sccv-seg-step fn-sccv-advance fn-sccv-count fn-sccv-prev
                                              fn-scc-join)
                            (fn-scc-open-segment fn-scc-parse-header fn-sccv-final
                                                 fn-sccv-mid-run))))))

(local
 (defthm fn-sccv-past-the-runs
   (implies (and (fn-sccv-livep v) (< *fn-sccv-runs* (nth 0 v)))
            (not (equal (car (fn-sccv-final (fn-sccv-segs v segs))) :ok)))
   :hints (("Goal" :do-not-induct t
            :cases ((fn-sccv-livep (fn-sccv-segs v segs)))
            :use ((:instance fn-sccv-runs-monotone)
                  (:instance fn-sccv-final-ok-at-run-start (v (fn-sccv-segs v segs))))
            :in-theory (disable fn-sccv-runs-monotone fn-sccv-final-ok-at-run-start
                                fn-sccv-segs fn-sccv-livep)))))

(local
 (defthm fn-sccv-nothing-after-the-runs
   (implies (and (consp segs) (natp q))
            (not (equal (car (fn-sccv-final (fn-sccv-segs (list 5 0 0 q *fn-scc-genesis*) segs)))
                        :ok)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-sccv-first-frame (r 5))
                  (:instance fn-sccv-past-the-runs
                             (v (list 6 0 0 q *fn-scc-genesis*))
                             (segs (nthcdr (nth 1 (fn-scc-parse-header (car segs))) segs))))
            :in-theory (disable fn-sccv-first-frame fn-sccv-past-the-runs fn-sccv-final
                                fn-sccv-segs fn-scc-parse-header fn-scc-join)))))

; N consecutive runs from SEGS's first segment, each its first header's
; count of segments joining under the list codec's chain from index 0 with
; SEQUENCE and the genesis, and nothing after the last.
(defun fn-sccv-runs-okp (segs n sequence)
  (declare (xargs :guard (and (fn-scc-segment-listp segs) (natp n))
                  :verify-guards nil :measure (nfix n)))
  (if (zp n)
      (atom segs)
    (let* ((h (and (consp segs) (fn-scc-parse-header (car segs))))
           (count (and h (nth 1 h))))
      (and h (posp count) (<= count (len segs))
           (equal (car (fn-scc-join (take count segs) 0 count sequence *fn-scc-genesis* nil))
                  :ok)
           (fn-sccv-runs-okp (nthcdr count segs) (1- n) sequence)))))

(local
 (defun fn-sccv-run-ind (segs r)
   (declare (xargs :measure (nfix (- 5 (nfix r))) :verify-guards nil))
   (if (and (natp r) (< r 5))
       (let* ((h (and (consp segs) (fn-scc-parse-header (car segs))))
              (count (and h (nth 1 h))))
         (fn-sccv-run-ind (nthcdr (nfix count) segs) (+ 1 r)))
     (list segs r))))

(local
 (defthm fn-sccv-run-start
   (implies (and (natp r) (<= r 5) (natp q)
                 (equal (car (fn-sccv-final (fn-sccv-segs (list r 0 0 q *fn-scc-genesis*) segs)))
                        :ok))
            (fn-sccv-runs-okp segs (- 5 r) q))
   :hints (("Goal" :induct (fn-sccv-run-ind segs r)
            :in-theory (e/d (fn-sccv-runs-okp)
                            (fn-sccv-final fn-scc-parse-header fn-scc-join fn-sccv-segs
                                           fn-sccv-first-frame)))
           ("Subgoal *1/1" :cases ((consp segs))
            :use ((:instance fn-sccv-first-frame))))))

; KEYSTONE.
(defthm fn-sccv-final-ok-is-runs-ok
  (implies (equal (car (fn-sccv-final (fn-sccv-segs (fn-sccv-initial sequence) segs))) :ok)
           (fn-sccv-runs-okp segs *fn-sccv-runs* (nfix sequence)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-sccv-run-start (r 0) (q (nfix sequence))))
           :in-theory (disable fn-sccv-run-start fn-sccv-final fn-sccv-segs fn-sccv-runs-okp))))

(in-theory (disable fn-sccv-livep fn-sccv-count fn-sccv-prev fn-sccv-advance
                    fn-sccv-seg-step fn-sccv-segs fn-sccv-final fn-sccv-step
                    fn-sccv-runs-okp))
