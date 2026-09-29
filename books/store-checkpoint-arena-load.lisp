; fn: the state checkpoint's LOAD under the records flip: the arena run
; opened and verified, its payloads sealed from the buffer a bounded number
; per step, then the four tables (lane checkpoint-arena; split from
; books/store-checkpoint-arena.lisp by checkpoint-arena-2 so that each book
; certifies under D26's ten seconds at two jobs).
;
; KEYSTONE `fn-scka-load-of-written-file': a plan whose segments are the
; arena run of PS (books/store-checkpoint-arena.lisp fn-scka-run-segments)
; followed by the tables' runs of the capture of RECORDS loads to
; (:ok TABLES) with the arena exactly PS.  What the host calls:
; host/store-node-host.lisp fn-store-sco-decode calls `fn-scka-open-run',
; then `fn-scka-seal-n' in steps of B payloads (fn-scka-seal-n-compose: the
; steps are one loop), then `fn-scka-finish'; `fn-scka-load' is that
; composition and `fn-scka-load-of-written-file' is about it.

(in-package "ACL2")
(include-book "store-checkpoint-arena")
(include-book "store-checkpoint-share")
(local (include-book "arithmetic/top" :dir :system))

;; The tau system is off in this book (lane tau-pass, tools/tau_cost.py).
;; Its work is proof time no prover step counts (docs/proof-style.md
;; 9.1); planning/evidence/tau-cost-*.json has this book's figures.
(local (in-theory (disable (tau-system))))

(local (in-theory (disable fn-cp-idp fn-cp-idp-true-listp
                           fn-sccr-scc-octet-listp-is-cbor-octet-listp
                           fn-sccr-cbor-octet-listp-is-scc-octet-listp)))

(local
 (defthm fn-scka-car-append
   (implies (consp a) (equal (car (append a b)) (car a)))))

(local
 (defthm fn-scka-consp-append
   (implies (consp a) (consp (append a b)))))

; -----------------------------------------------------------------------------
; 3. The load: the seal loop, the arena run opened, the tables after it.

(defun fn-scka-seal-n (i end n fn-octets fn-arena)
  (declare (xargs :stobjs (fn-octets fn-arena)
                  :guard (and (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets)) (natp n))
                  :measure (nfix n)
                  :guard-hints (("Goal" :use ((:instance fn-sccr-read-nat-facts))
                                 :in-theory (disable fn-sccr-read-nat-facts)))))
  (if (zp n)
      (mv t i fn-arena)
    (let ((r (fn-sccr-read-nat i end fn-octets)))
      (if (not r)
          (mv nil i fn-arena)
        (let ((j (cdr r)) (l (car r)))
          (if (> (+ j l) end)
              (mv nil i fn-arena)
            (let ((fn-arena (fn-arena-seal-range j (+ j l) fn-octets fn-arena)))
              (fn-scka-seal-n (+ j l) end (1- n) fn-octets fn-arena))))))))

(local
 (defthm fn-scka-take-of-cons
   (implies (and (natp n) (< 0 n))
            (equal (take n (cons a x)) (cons a (take (- n 1) x))))))

(local
 (defthm fn-scka-nthcdr-of-cons
   (implies (and (natp n) (< 0 n))
            (equal (nthcdr n (cons a x)) (nthcdr (- n 1) x)))))

(local
 (defthm fn-scka-slice-prefix
   (implies (and (natp j) (natp k) (natp end) (<= j k) (<= k end))
            (equal (fn-oct-slice-list j k o)
                   (take (- k j) (fn-oct-slice-list j end o))))
   :rule-classes nil
   :hints (("Goal" :induct (fn-oct-slice-list j k o)
            :in-theory (e/d (fn-oct-slice-list) (fn-oct-slice-list-is-take-nthcdr))
            :expand ((fn-oct-slice-list j end o) (fn-oct-slice-list j k o))))))

(local
 (defthm fn-scka-slice-suffix
   (implies (and (natp j) (natp k) (natp end) (<= j k) (<= k end))
            (equal (fn-oct-slice-list k end o)
                   (nthcdr (- k j) (fn-oct-slice-list j end o))))
   :rule-classes nil
   :hints (("Goal" :induct (fn-oct-slice-list j k o)
            :in-theory (e/d (fn-oct-slice-list) (fn-oct-slice-list-is-take-nthcdr))
            :expand ((fn-oct-slice-list j end o) (fn-oct-slice-list j k o))))))

(local
 (defthm fn-scka-slice-len
   (implies (and (natp i) (natp n) (<= i n))
            (equal (len (fn-oct-slice-list i n o)) (- n i)))
   :hints (("Goal" :induct (fn-oct-slice-list i n o)
            :in-theory (e/d (fn-oct-slice-list) (fn-oct-slice-list-is-take-nthcdr))))))

(local
 (defthm fn-scka-read-payload
   (implies (and (fn-octets-p o) (natp i) (natp end) (<= i end) (<= end (len o))
                 (equal (fn-oct-slice-list i end o) (append (fn-scka-payload-octets p) rest))
                 (true-listp p))
            (let ((r (fn-sccr-read-nat i end o)))
              (and r
                   (equal (car r) (len p))
                   (<= (+ (cdr r) (len p)) end)
                   (equal (fn-oct-slice-list (cdr r) (+ (cdr r) (len p)) o) p)
                   (equal (fn-oct-slice-list (+ (cdr r) (len p)) end o) rest))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-sccr-read-nat-is-read-nat (fn-octets o))
                  (:instance fn-sccr-read-nat-facts (fn-octets o))
                  (:instance fn-scc-read-nat-of-octets (n (len p)) (rest (append p rest)))
                  (:instance fn-scka-slice-len (i (cdr (fn-sccr-read-nat i end o))) (n end))
                  (:instance fn-scka-slice-prefix (j (cdr (fn-sccr-read-nat i end o)))
                             (k (+ (cdr (fn-sccr-read-nat i end o)) (len p))))
                  (:instance fn-scka-slice-suffix (j (cdr (fn-sccr-read-nat i end o)))
                             (k (+ (cdr (fn-sccr-read-nat i end o)) (len p)))))
            :in-theory (e/d (fn-scka-payload-octets)
                            (fn-sccr-read-nat-is-read-nat fn-sccr-read-nat-facts
                             fn-scc-read-nat-of-octets fn-scka-slice-len
                             fn-oct-slice-list-is-take-nthcdr fn-scc-nat-octets
                             fn-scc-read-nat))))))

(local
 (defun fn-scka-seal-ind (i end ps fn-octets a)
   (declare (xargs :measure (len ps) :stobjs fn-octets :verify-guards nil))
   (if (atom ps)
       (list i end a)
     (let* ((r (fn-sccr-read-nat i end fn-octets)) (j (cdr r)) (l (car r)))
       (fn-scka-seal-ind (+ (nfix j) (nfix l)) end (cdr ps) fn-octets
                         (append a (list (car ps))))))))

(local
 (defthm fn-scka-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(defthm fn-scka-seal-n-of-body
  (implies (and (fn-octets-p fn-octets) (natp i) (natp end) (<= i end)
                (<= end (len fn-octets))
                (equal (fn-oct-slice-list i end fn-octets) (append (fn-scka-body ps) rest))
                (true-list-listp ps) (true-listp fn-arena))
           (let ((r (fn-scka-seal-n i end (len ps) fn-octets fn-arena)))
             (and (mv-nth 0 r)
                  (natp (mv-nth 1 r))
                  (<= (mv-nth 1 r) end)
                  (equal (mv-nth 2 r) (append fn-arena ps))
                  (equal (fn-oct-slice-list (mv-nth 1 r) end fn-octets) rest))))
  :hints (("Goal" :induct (fn-scka-seal-ind i end ps fn-octets fn-arena)
           :in-theory (e/d (fn-scka-seal-n fn-scka-body)
                           (fn-scka-payload-octets fn-oct-slice-list-is-take-nthcdr
                            fn-arena-seal-range-is-append)))
          ("Subgoal *1/2" :use ((:instance fn-scka-read-payload (o fn-octets) (p (car ps))
                                           (rest (append (fn-scka-body (cdr ps)) rest)))
                                (:instance fn-sccr-read-nat-facts))
           :in-theory (e/d (fn-scka-seal-n fn-scka-body)
                           (fn-scka-payload-octets fn-oct-slice-list-is-take-nthcdr
                            fn-arena-seal-range-is-append fn-scka-read-payload
                            fn-sccr-read-nat-facts)))))

(local
 (defthm fn-scka-take-of-append-short
   (implies (and (natp k) (<= k (len a)))
            (equal (take k (append a b)) (take k a)))))

(local
 (defthm fn-scka-nthcdr-of-append-short
   (implies (and (natp k) (<= k (len a)))
            (equal (nthcdr k (append a b)) (append (nthcdr k a) b)))))

(local
 (defthm fn-scka-nth-of-append-short
   (implies (and (natp k) (< k (len a)))
            (equal (nth k (append a b)) (nth k a)))))

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

(defthm fn-scka-seal-n-compose
  (implies (and (natp n1) (natp n2))
           (equal (fn-scka-seal-n i end (+ n1 n2) fn-octets fn-arena)
                  (mv-let (ok i1 a1) (fn-scka-seal-n i end n1 fn-octets fn-arena)
                    (if ok
                        (fn-scka-seal-n i1 end n2 fn-octets a1)
                      (mv nil i1 a1)))))
  :hints (("Goal" :induct (fn-scka-seal-n i end n1 fn-octets fn-arena)
           :in-theory (e/d (fn-scka-seal-n) (fn-arena-seal-range-is-append)))))

; A plan's first frame carries the segment header octets (fn-sccr-framep):
; what fn-scka-open-run's header parse reads.
(defthm fn-sccr-planp-first-frame-octets
  (implies (and (consp plan) (fn-sccr-planp plan pos fn-octets))
           (fn-scc-octet-listp (car (car plan))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-sccr-framep)
           :expand ((fn-sccr-planp plan pos fn-octets)))))

(defun fn-scka-open-run (plan fn-octets)
  (declare (xargs :stobjs fn-octets :guard t :verify-guards nil))
  (let ((start (if (consp plan) (fn-sccr-at 1 (car plan)) 0)))
    (if (not (fn-sccr-planp plan start fn-octets))
        (list :refused :layout)
      (let ((h (and (consp plan) (fn-scc-parse-header (fn-sccr-at 0 (car plan))))))
        (if (not h)
            (list :refused :header)
          (let* ((s (nth 3 h))
                 (r (fn-sctr-next-run plan s fn-octets)))
            (if (not (eq (car r) :ok))
                r
              (let ((a (nth 1 r)) (b (nth 2 r)))
                (if (not (and (<= (+ a 4) b)
                              (equal (fn-oct-slice-list a (+ a 4) fn-octets) *fn-scka-tag*)))
                    (list :refused :arena)
                  (let ((n (fn-sccr-read-nat (+ a 4) b fn-octets)))
                    (if (not n)
                        (list :refused :arena)
                      (list :ok (cdr n) b (car n) (nth 3 r) s))))))))))))

(local
 (defun fn-sctr-frames-ind (n plan pos)
   (if (or (zp n) (not (consp plan)))
       (list plan pos)
     (fn-sctr-frames-ind (1- n) (cdr plan) (fn-sccr-at 2 (car plan))))))

(local
 (defthm fn-sctr-parse-header-count-natp
   (implies (and (fn-scc-octet-listp seg) (fn-scc-parse-header seg))
            (natp (nth 1 (fn-scc-parse-header seg))))
   :hints (("Goal" :in-theory (enable fn-scc-parse-header fn-scc-u64-at)))))

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

(local
 (defthm fn-sctr-restp-of-plan
   (implies (fn-sccr-planp plan (if (consp plan) (fn-sccr-at 1 (car plan)) 0) fn-octets)
            (fn-sctr-restp plan fn-octets))
   :hints (("Goal" :in-theory (enable fn-sctr-restp)))))

(local
 (defthm fn-scka-plan-segments-car
   (implies (consp plan)
            (equal (car (fn-sccr-plan-segments plan fn-octets))
                   (fn-sccb-frame-octets (car plan) fn-octets)))
   :hints (("Goal" :in-theory (enable fn-sccr-plan-segments)))))

(local
 (defthm fn-scka-plan-segments-consp
   (equal (consp (fn-sccr-plan-segments plan fn-octets)) (consp plan))
   :hints (("Goal" :in-theory (enable fn-sccr-plan-segments)))))

(local
 (defthm fn-scka-planp-framep
   (implies (and (fn-sccr-planp plan pos fn-octets) (consp plan))
            (fn-sccr-framep (car plan) fn-octets))
   :hints (("Goal" :expand ((fn-sccr-planp plan pos fn-octets))))))

(local
 (defthm fn-scka-run-chunks-consp
   (consp (fn-scka-run-chunks ps ks))))

(local
 (defthm fn-scka-run-segments-consp
   (consp (fn-scka-run-segments ps ks s))
   :hints (("Goal" :in-theory (union-theories '(fn-scka-run-segments fn-scc-frames-consp
                                                fn-scka-run-chunks-consp)
                                              (theory 'minimal-theory))))))

(local
 (defthm fn-scka-car-run-segments
   (equal (car (fn-scka-run-segments ps ks s))
          (car (fn-scc-frames (fn-scka-run-chunks ps ks) 0 (+ 1 (len ks)) s *fn-scc-genesis*)))
   :hints (("Goal" :in-theory (union-theories '(fn-scka-run-segments) (theory 'minimal-theory))))))

(local
 (defthm fn-scka-first-header
   (implies (and (fn-octets-p fn-octets)
                 (fn-sccr-planp plan pos fn-octets)
                 (equal (fn-sccr-plan-segments plan fn-octets)
                        (append (fn-scka-run-segments ps ks s) tsegs))
                 (fn-scc-chunk-listp (fn-scka-run-chunks ps ks))
                 (< (+ 1 (len ks)) *fn-scc-u64-bound*) (natp s) (< s *fn-scc-u64-bound*))
            (and (consp plan)
                 (fn-scc-parse-header (fn-sccr-at 0 (car plan)))
                 (equal (nth 3 (fn-scc-parse-header (fn-sccr-at 0 (car plan)))) s)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-scc-parse-header-of-first-frame-sequence
                             (chunks (fn-scka-run-chunks ps ks)) (n (+ 1 (len ks))) (q s)
                             (prev *fn-scc-genesis*))
                  (:instance fn-sctr-parse-header-of-frame-octets (frame (car plan)))
                  (:instance fn-scka-plan-segments-car)
                  (:instance fn-scka-plan-segments-consp)
                  (:instance fn-scka-planp-framep)
                  (:instance fn-scka-run-segments-consp)
                  (:instance fn-scka-consp-append (a (fn-scka-run-segments ps ks s)) (b tsegs)))
            :in-theory (e/d (fn-scka-car-append fn-scka-consp-append)
                            (fn-scka-run-segments fn-scc-parse-header-of-first-frame-sequence
                             fn-sctr-parse-header-of-frame-octets fn-scka-plan-segments-car
                             fn-scka-plan-segments-consp fn-scka-planp-framep
                             fn-scka-run-segments-consp
                             fn-scc-parse-header fn-scc-frames fn-scka-run-chunks
                             fn-sccb-frame-octets fn-sccr-framep fn-sccr-planp))))))

(local
 (defthm fn-scka-next-run-of-written
   (implies (and (fn-octets-p fn-octets)
                 (fn-sccr-planp plan (fn-sccr-at 1 (car plan)) fn-octets)
                 (consp plan)
                 (equal (fn-sccr-plan-segments plan fn-octets)
                        (append (fn-scka-run-segments ps ks s) tsegs))
                 (true-listp ps) (equal (fn-scka-sum ks) (len ps))
                 (fn-scc-chunk-listp (fn-scka-run-chunks ps ks))
                 (< (+ 1 (len ks)) *fn-scc-u64-bound*) (natp s) (< s *fn-scc-u64-bound*))
            (let ((r (fn-sctr-next-run plan s fn-octets)))
              (and (equal (car r) :ok)
                   (natp (nth 1 r)) (natp (nth 2 r))
                   (<= (nth 1 r) (nth 2 r)) (<= (nth 2 r) (len fn-octets))
                   (equal (fn-oct-slice-list (nth 1 r) (nth 2 r) fn-octets) (fn-scka-program ps))
                   (equal (fn-sccr-plan-segments (nth 3 r) fn-octets) tsegs)
                   (fn-sccr-planp (nth 3 r) (nth 2 r) fn-octets))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-sctr-run-decode-is-run-decode)
                  (:instance fn-scka-run-decode-of-run-segments (rest tsegs))
                  (:instance fn-sctr-run-decode-ok-shape (pos (fn-sccr-at 1 (car plan)))))
            :in-theory (e/d (fn-sctr-next-run)
                            (fn-sctr-run-decode-is-run-decode fn-scka-run-decode-of-run-segments
                             fn-sctr-run-decode-ok-shape fn-sctr-run-decode fn-sct-run-decode
                             fn-scka-program fn-scka-run-segments fn-sccr-planp
                             fn-oct-slice-list-is-take-nthcdr
                             fn-scc-le-digits fn-scka-run-chunks fn-scka-chunks fn-scc-frames
                             fn-scka-body fn-scc-chunk-listp fn-scka-payload-octets binary-append
                             fn-scka-first-header fn-scka-car-run-segments
                             floor mod))))))

(local
 (defthm fn-scka-program-split
   (and (equal (take 4 (fn-scka-program ps)) *fn-scka-tag*)
        (equal (nthcdr 4 (fn-scka-program ps))
               (append (fn-scc-nat-octets (len ps)) (fn-scka-body ps)))
        (<= 5 (len (fn-scka-program ps))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-scka-program fn-scka-head fn-scc-nat-octets)
                                   (fn-scka-body fn-scc-le-digits))))))

(local
 (defthm fn-scka-slice-head
   (implies (and (fn-octets-p o) (natp a) (natp b) (<= a b) (<= b (len o))
                 (equal (fn-oct-slice-list a b o) (fn-scka-program ps)))
            (let ((r (fn-sccr-read-nat (+ a 4) b o)))
              (and (<= (+ a 4) b)
                   (equal (fn-oct-slice-list a (+ a 4) o) *fn-scka-tag*)
                   r
                   (equal (car r) (len ps))
                   (natp (cdr r)) (<= (cdr r) b)
                   (equal (fn-oct-slice-list (cdr r) b o) (fn-scka-body ps)))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-scka-program-split)
                  (:instance fn-scka-slice-prefix (j a) (k (+ 4 a)) (end b))
                  (:instance fn-scka-slice-suffix (j a) (k (+ 4 a)) (end b))
                  (:instance fn-scka-slice-len (i a) (n b))
                  (:instance fn-sccr-read-nat-is-read-nat (i (+ 4 a)) (end b) (fn-octets o))
                  (:instance fn-sccr-read-nat-facts (i (+ 4 a)) (end b) (fn-octets o))
                  (:instance fn-scc-read-nat-of-octets (n (len ps)) (rest (fn-scka-body ps))))
            :in-theory (e/d ()
                            (fn-sccr-read-nat-is-read-nat fn-sccr-read-nat-facts
                             fn-scc-read-nat-of-octets fn-scka-slice-len
                             fn-scka-program fn-scka-body fn-scc-nat-octets fn-scc-read-nat
                             fn-oct-slice-list-is-take-nthcdr))))))

(verify-guards fn-scka-open-run)

(defthm fn-scka-open-run-of-written
  (implies (and (fn-octets-p fn-octets)
                (fn-sccr-planp plan (if (consp plan) (fn-sccr-at 1 (car plan)) 0) fn-octets)
                (equal (fn-sccr-plan-segments plan fn-octets)
                       (append (fn-scka-run-segments ps ks s) tsegs))
                (true-listp ps) (equal (fn-scka-sum ks) (len ps))
                (fn-scc-chunk-listp (fn-scka-run-chunks ps ks))
                (< (+ 1 (len ks)) *fn-scc-u64-bound*) (natp s) (< s *fn-scc-u64-bound*))
           (let ((o (fn-scka-open-run plan fn-octets)))
             (and (equal (nth 0 o) :ok)
                  (equal (nth 3 o) (len ps))
                  (equal (nth 5 o) s)
                  (natp (nth 1 o)) (natp (nth 2 o)) (<= (nth 1 o) (nth 2 o))
                  (<= (nth 2 o) (len fn-octets))
                  (equal (fn-oct-slice-list (nth 1 o) (nth 2 o) fn-octets) (fn-scka-body ps))
                  (equal (fn-sccr-plan-segments (nth 4 o) fn-octets) tsegs)
                  (fn-sccr-planp (nth 4 o) (nth 2 o) fn-octets))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-scka-first-header (pos (if (consp plan) (fn-sccr-at 1 (car plan)) 0)))
                 (:instance fn-scka-next-run-of-written)
                 (:instance fn-scka-slice-head
                            (a (nth 1 (fn-sctr-next-run plan s fn-octets)))
                            (b (nth 2 (fn-sctr-next-run plan s fn-octets)))
                            (o fn-octets)))
           :in-theory (union-theories '(fn-scka-open-run car-cons cdr-cons nth-0-cons
                                        nth-add1 (:executable-counterpart nth)
                                        (:executable-counterpart equal)
                                        (:executable-counterpart not)
                                        (:executable-counterpart car)
                                        (:executable-counterpart zp)
                                        (:executable-counterpart binary-+)
                                        nth zp natp fix nfix)
                                      (theory 'minimal-theory)))))

(defun fn-scka-finish (rest s i b fn-octets)
  (declare (xargs :stobjs fn-octets :guard t))
  (if (not (equal i b))
      (list :refused :arena)
    (let ((loaded (fn-sct-load rest fn-octets)))
      (if (not (eq (car loaded) :ok))
          loaded
        (if (not (equal (fn-sco-at 1 (fn-sct-tables-f (cadr loaded))) s))
            (list :refused :close)
          ; One object per string content (fn-sshr-share-is-identity): the
          ; R tables' strings are the E rows', as the full replay's are.
          (fn-sshr-share loaded))))))

(defun fn-scka-load (plan fn-octets fn-arena)
  (declare (xargs :stobjs (fn-octets fn-arena) :verify-guards nil))
  (let ((o (fn-scka-open-run plan fn-octets)))
    (if (not (eq (car o) :ok))
        (mv o fn-arena)
      (let ((fn-arena (fn-arena-clear fn-arena)))
        (mv-let (ok i fn-arena)
          (fn-scka-seal-n (nth 1 o) (nth 2 o) (nth 3 o) fn-octets fn-arena)
          (if (not ok)
              (mv (list :refused :arena) fn-arena)
            (mv (fn-scka-finish (nth 4 o) (nth 5 o) i (nth 2 o) fn-octets) fn-arena)))))))

(local
 (defthm fn-scka-f-of-tables-of-capture
   (equal (nth 1 (nth 0 (fn-sct-tables-of-capture (fn-sco-capture configs records)
                                                  frontier revision log)))
          (len records))
   :hints (("Goal" :in-theory (e/d (fn-sct-tables-of-capture fn-sco-capture fn-sco-make
                                    fn-sco-records fn-sco-at)
                                   (fn-sco-cpr-prefix fn-replay-identity-loop
                                    fn-cpe-projection-replay fn-th-prefix-loop
                                    fn-cei-build-aux))))))

(local
 (defthm fn-scka-planp-first-a
   (implies (and (fn-sccr-planp plan pos fn-octets) (consp plan))
            (equal (fn-sccr-at 1 (car plan)) pos))
   :hints (("Goal" :expand ((fn-sccr-planp plan pos fn-octets))))))

(local
 (defthm fn-scka-slice-nil-means-end
   (implies (and (natp i) (natp b) (<= i b) (equal (fn-oct-slice-list i b o) nil))
            (equal i b))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-scka-slice-len (n b)))
            :in-theory (disable fn-scka-slice-len fn-oct-slice-list-is-take-nthcdr)))))

(local
 (defthm fn-scka-seal-all
   (implies (and (fn-octets-p fn-octets) (natp i) (natp b) (<= i b) (<= b (len fn-octets))
                 (equal (fn-oct-slice-list i b fn-octets) (fn-scka-body ps))
                 (true-list-listp ps))
            (let ((r (fn-scka-seal-n i b (len ps) fn-octets nil)))
              (and (mv-nth 0 r)
                   (equal (mv-nth 1 r) b)
                   (equal (mv-nth 2 r) ps))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-scka-seal-n-of-body (end b) (rest nil) (fn-arena nil))
                  (:instance fn-scka-slice-nil-means-end
                             (i (mv-nth 1 (fn-scka-seal-n i b (len ps) fn-octets nil)))
                             (o fn-octets)))
            :in-theory (disable fn-scka-seal-n-of-body fn-scka-seal-n fn-scka-body
                                fn-oct-slice-list-is-take-nthcdr)))))

(local
 (defthm fn-scka-finish-when-load
   (implies (equal (fn-sct-load rest o) (list :ok tables))
            (equal (fn-scka-finish rest s b b o)
                   (if (equal (fn-sco-at 1 (fn-sct-tables-f tables)) s)
                       (list :ok tables)
                     (list :refused :close))))
   :hints (("Goal" :in-theory (e/d (fn-scka-finish) (fn-sct-load fn-sct-tables-f fn-sco-at))))))

(local
 (defthm fn-scka-chunks-consp
   (consp (fn-scc-chunks p seg))
   :hints (("Goal" :expand ((fn-scc-chunks p seg))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm fn-scka-file-segments-consp
   (consp (fn-sct-file-segments progs seg s))
   :hints (("Goal" :in-theory (union-theories '(fn-sct-file-segments fn-sct-run-segments
                                                fn-scka-chunks-consp fn-scc-frames-consp
                                                fn-scka-consp-append)
                                              (theory 'minimal-theory))))))

(local
 (defthm fn-scka-load-of-written-tables
   (let* ((c (fn-sco-capture configs records))
          (tables (fn-sct-tables-of-capture c frontier revision log))
          (progs (fn-sct-table-programs tables (fn-sco-event-index c))))
     (implies (and (fn-octets-p fn-octets)
                   (fn-sccr-planp rest b fn-octets)
                   (equal (fn-sccr-plan-segments rest fn-octets)
                          (fn-sct-file-segments progs seg (len records)))
                   (fn-sct-tables-treep tables)
                   (fn-sct-log-positionp log)
                   (<= (len records) (1+ *fn-cbor-max-uint*))
                   (fn-sct-programs-widthp progs))
              (equal (fn-sct-load rest fn-octets) (list :ok tables))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :cases ((consp rest))
            :use ((:instance fn-sct-load-is-decode-file (plan rest))
                  (:instance fn-sct-decode-file-of-file-is-the-capture)
                  (:instance fn-scka-planp-first-a (plan rest) (pos b))
                  (:instance fn-scka-plan-segments-consp (plan rest))
                  (:instance fn-scka-file-segments-consp (progs (fn-sct-table-programs
                     (fn-sct-tables-of-capture (fn-sco-capture configs records) frontier revision log)
                     (fn-sco-event-index (fn-sco-capture configs records)))) (s (len records))))
            :in-theory (e/d ()
                            (fn-sct-load-is-decode-file fn-sct-decode-file-of-file-is-the-capture
                             fn-scka-planp-first-a fn-scka-plan-segments-consp
                             fn-scka-file-segments-consp fn-sct-load fn-sct-decode-file
                              fn-sct-file-segments fn-sct-tables-of-capture fn-sco-capture
                             fn-sct-table-programs fn-sct-tables-treep fn-sct-programs-widthp
                             fn-sccr-planp fn-sco-event-index fn-sct-log-positionp))))))

(local
 (defthm fn-scka-f-count-of-tables-of-capture
   (equal (fn-sco-at 1 (fn-sct-tables-f (fn-sct-tables-of-capture (fn-sco-capture configs records)
                                                                  frontier revision log)))
          (len records))
   :hints (("Goal" :in-theory (e/d (fn-sct-tables-f fn-sct-tables-of-capture fn-sco-capture
                                    fn-sco-make fn-sco-records fn-sco-at)
                                   (fn-sco-cpr-prefix fn-replay-identity-loop
                                    fn-cpe-projection-replay fn-th-prefix-loop
                                    fn-cei-build-aux))))))

(defthm fn-scka-load-of-written-file
  (let* ((c (fn-sco-capture configs records))
         (tables (fn-sct-tables-of-capture c frontier revision log))
         (progs (fn-sct-table-programs tables (fn-sco-event-index c)))
         (s (len records)))
    (implies (and (fn-octets-p fn-octets)
                  (fn-sccr-planp plan (if (consp plan) (fn-sccr-at 1 (car plan)) 0) fn-octets)
                  (equal (fn-sccr-plan-segments plan fn-octets)
                         (append (fn-scka-run-segments ps ks s)
                                 (fn-sct-file-segments progs seg s)))
                  (true-list-listp ps) (equal (fn-scka-sum ks) (len ps))
                  (fn-scc-chunk-listp (fn-scka-run-chunks ps ks))
                  (< (+ 1 (len ks)) *fn-scc-u64-bound*) (< s *fn-scc-u64-bound*)
                  (fn-sct-tables-treep tables)
                  (fn-sct-log-positionp log)
                  (<= (len records) (1+ *fn-cbor-max-uint*))
                  (fn-sct-programs-widthp progs))
             (and (equal (mv-nth 0 (fn-scka-load plan fn-octets fn-arena)) (list :ok tables))
                  (equal (mv-nth 1 (fn-scka-load plan fn-octets fn-arena)) ps))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-scka-open-run-of-written (s (len records))
                            (tsegs (fn-sct-file-segments
                                    (fn-sct-table-programs
                                     (fn-sct-tables-of-capture (fn-sco-capture configs records)
                                                               frontier revision log)
                                     (fn-sco-event-index (fn-sco-capture configs records)))
                                    seg (len records))))
                 (:instance fn-scka-seal-all
                            (i (nth 1 (fn-scka-open-run plan fn-octets)))
                            (b (nth 2 (fn-scka-open-run plan fn-octets))))
                 (:instance fn-scka-load-of-written-tables
                            (rest (nth 4 (fn-scka-open-run plan fn-octets)))
                            (b (nth 2 (fn-scka-open-run plan fn-octets)))))
           :in-theory (e/d (fn-scka-load)
                           (fn-scka-open-run-of-written fn-scka-seal-all
                            fn-scka-open-run fn-scka-seal-n fn-scka-finish fn-sct-load
                            fn-sct-tables-of-capture fn-sco-capture fn-sct-table-programs
                            fn-sct-file-segments fn-scka-run-segments fn-scka-run-chunks
                            fn-sct-tables-treep fn-sct-programs-widthp fn-sccr-planp
                            fn-sco-event-index fn-sct-capture-of-tables fn-scka-body
                            fn-sct-tables-f fn-sco-at fn-oct-slice-list-is-take-nthcdr
                            fn-sccr-plan-segments fn-scka-sum fn-scka-car-run-segments
                            fn-scc-frames binary-append fn-cp-idp fn-scc-header
                            fn-sccr-scc-octet-listp-is-cbor-octet-listp
                            fn-sccr-cbor-octet-listp-is-scc-octet-listp
                            fn-sccr-at-is-nth fn-sccr-at fn-oct-bufp-true-listp
                            fn-scc-octet-listp-true fn-arn-payload-listp-true-listp
                            true-list-listp fn-scc-octet-listp-facts)))))


; -----------------------------------------------------------------------------
; 4. The open's choice with the arena refusal named.  A file whose first run
; is not the arena run (a tables-only file written before the records flip,
; or a later format's run with another tag) is refused by name: the open
; replays the journal and `status' says reason=checkpoint-arena, never
; `corrupt'.  host/store-node-host.lisp fn-store-sco-select calls it; the
; host's load answers the status :arena for fn-store-sco-decode's
; (:refused :arena).
(defun fn-scka-select-named (status sequence count k)
  (declare (xargs :guard t))
  (if (eq status :arena)
      (list :full-replay :checkpoint-arena)
    (fn-sco-select-named status sequence count k)))

(defthm fn-scka-select-named-refuses-the-arena-by-name
  (equal (fn-scka-select-named :arena sequence count k)
         (list :full-replay :checkpoint-arena)))

(defthm fn-scka-select-named-unfolds
  (implies (not (eq status :arena))
           (equal (fn-scka-select-named status sequence count k)
                  (fn-sco-select-named status sequence count k))))
