; The kind-19 held-row checkpoint read from an octet buffer by index (lane
; bp-checkpoint-open; D27).  Prefix `fn-bpnrb-'.
;
; `fn-bpnr-checkpoint-decode' (books/bp-node-rotation-codec.lisp) is the
; list reader: the host turned the selected file into an octet list and the
; tree decoder walked it.  Each u64 and counted read re-established
; `true-listp' of the WHOLE remaining input before splitting eight octets
; off it, so one decode walked the rest of the file once per token:
; quadratic in the file (763 s at 1,311 held rows, an 11.4 MB file; lane
; bp-catalog's measurement, planning/evidence/bp-checkpoint-open-2026-09-26.md).
;
; This book reads the same bytes from a buffer by index.  The host
; (host/native/bp-service.lisp `fnn-bps-selection-plan') copies the file
; into `fn-octets-bp', an abstract stobj congruent to `fn-octets'
; (books/octets-stobj.lisp; one byte per octet), and calls
; `fn-bpnrb-selection-plan'.  The tree decoder `fn-bpnrb-dec' carries an
; index; a u64 is eight cells, a counted run is its cells copied once into
; the list the checkpoint value holds (the held rows' wires stay octet
; lists: the replay's representation), and the frame trailer is the
; constrained digest over the prefix as a list, built once.
;
; What is proved.  `fn-bpnrb-dec-is-dec': the index decoder over the cells
; [i, end) is `fn-bpnr-dec' over that slice, the rest of the slice being
; the cells after the returned index.  KEYSTONE
; `fn-bpnrb-checkpoint-decode-is-decode': with no hypothesis, the buffer
; decode is `fn-bpnr-checkpoint-decode' of the buffer's value, so it takes
; every file the list decoder takes to the same checkpoint and refuses
; every file it refuses.  `fn-bpnrb-selection-plan-is-selection-plan': the
; host-called plan is `fn-bpnr-selection-plan', so PRF-081's recovery
; keystones and the round trip `fn-bpnr-checkpoint-decode-of-octets' are
; about what the host executes.
(in-package "ACL2")
(include-book "bp-node-rotation-codec")
(include-book "bp-node-rotation-slice")

; The slice is reasoned about as itself here, never as take/nthcdr.
(local (in-theory (disable fn-oct-slice-list-is-take-nthcdr)))

; The BP open's own buffer.  The store owner's `fn-octets' is filled under
; the owner's mutex by served attempts; the BP open never shares it.
(defabsstobj fn-octets-bp
  :foundation fn-octets$c
  :recognizer (fn-octets-bp-p :logic fn-octets$ap :exec fn-octets$cp)
  :creator (create-fn-octets-bp :logic create-fn-octets$a :exec create-fn-octets$c)
  :exports ((fn-octets-bp-len :logic fn-octets$a-len :exec fn-octets$c-len)
            (fn-octets-bp-get :logic fn-octets$a-get :exec fn-octets$c-get)
            (fn-octets-bp-put :logic fn-octets$a-put :exec fn-octets$c-put :protect t)
            (fn-octets-bp-append-octet :logic fn-octets$a-append-octet
                                       :exec fn-octets$c-append-octet :protect t)
            (fn-octets-bp-clear :logic fn-octets$a-clear :exec fn-octets$c-clear)
            (fn-octets-bp-reserve :logic fn-octets$a-reserve :exec fn-octets$c-reserve
                                  :protect t)
            (fn-octets-bp-list :logic fn-octets$a-list :exec fn-octets$c-list)
            (fn-octets-bp-from-list :logic fn-octets$a-from-list
                                    :exec fn-octets$c-from-list :protect t)
            (fn-octets-bp-append-list :logic fn-octets$a-append-list
                                      :exec fn-oct-write-list :protect t)
            (fn-octets-bp-append-back :logic fn-octets$a-append-back
                                      :exec fn-octets$c-append-back :protect t)
            (fn-octets-bp-get-word :logic fn-octets$a-get-word :exec fn-octets$c-get-word)
            (fn-octets-bp-append-word :logic fn-octets$a-append-word
                                      :exec fn-octets$c-append-word :protect t))
  :congruent-to fn-octets)

(local
 (defthm fn-bpnrb-read-u64-of-slice
   (implies (and (fn-cbor-octet-listp x) (natp i) (natp n) (<= i n)
                 (<= n (len x)))
            (equal (fn-bpnr-read-u64 (fn-oct-slice-list i n x))
                   (if (<= (+ i 8) n)
                       (cons (fn-bpc-u64-from (fn-oct-slice-list i (+ i 8) x))
                             (fn-oct-slice-list (+ i 8) n x))
                     nil)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-bpnr-read-u64) (fn-bpc-u64-from fn-frame-split))))))

(local
 (defthm fn-bpnrb-read-counted-of-slice
   (implies (and (fn-cbor-octet-listp x) (natp i) (natp n) (<= i n)
                 (<= n (len x)))
            (equal (fn-bpnr-read-counted (fn-oct-slice-list i n x))
                   (let ((m (nfix (fn-bpc-u64-from (fn-oct-slice-list i (+ i 8) x)))))
                     (if (and (<= (+ i 8) n) (<= (+ i 8 m) n))
                         (cons (fn-oct-slice-list (+ i 8) (+ i 8 m) x)
                               (fn-oct-slice-list (+ i 8 m) n x))
                       nil))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-bpnr-read-counted)
                            (fn-bpc-u64-from fn-frame-split fn-bpnr-read-u64))))))

; -----------------------------------------------------------------------------
; The tree decoder by index: (mv ok value next).

; A u64 at i (i + 8 <= end checked by the caller): the list reader over the
; eight cells.
(defun fn-bpnrb-u64 (i fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (<= (+ i 8) (fn-octets-len fn-octets)))))
  (car (fn-bpnr-read-u64 (fn-bpnrb-slice-acc i (+ i 8) nil fn-octets))))

(defun fn-bpnrb-counted (i end fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp end) (<= end (fn-octets-len fn-octets)))))
  (if (or (not (natp i)) (< end (+ i 8)))
      (mv nil nil 0)
    (let ((b (+ i 8 (nfix (fn-bpnrb-u64 i fn-octets)))))
      (if (< end b)
          (mv nil nil 0)
        (mv t (fn-bpnrb-slice-acc (+ i 8) b nil fn-octets) b)))))

(defun fn-bpnrb-dec (i end d fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp end) (natp d)
                              (<= end (fn-octets-len fn-octets)))
                  :measure (nfix d)
                  :verify-guards nil))
  (if (or (zp d) (not (natp i)) (not (natp end)) (<= end i))
      (mv nil nil 0)
    (let ((tag (fn-octets-get i fn-octets)) (j (1+ i)))
      (cond ((equal tag 0) (mv t nil j))
            ((equal tag 1) (mv t t j))
            ((or (equal tag 2) (equal tag 3) (equal tag 4) (equal tag 7))
             (mv-let (ok codes k) (fn-bpnrb-counted j end fn-octets)
               (if (not ok)
                   (mv nil nil 0)
                 (let ((s (coerce (fn-bpnr-chars codes) 'string)))
                   (mv t
                       (cond ((equal tag 2) (intern-in-package-of-symbol s :fn))
                             ((equal tag 3)
                              (intern-in-package-of-symbol s 'fn-bpnr-dec))
                             ((equal tag 4) (intern-in-package-of-symbol s 'car))
                             (t s))
                       k)))))
            ((equal tag 5)
             (if (< end (+ j 8))
                 (mv nil nil 0)
               (mv t (fn-bpnrb-u64 j fn-octets) (+ j 8))))
            ((equal tag 6)
             (if (< end (+ j 8))
                 (mv nil nil 0)
               (mv t (- (nfix (fn-bpnrb-u64 j fn-octets))) (+ j 8))))
            ((equal tag 8)
             (if (and (< j end) (fn-cbor-octetp (fn-octets-get j fn-octets)))
                 (mv t (code-char (fn-octets-get j fn-octets)) (1+ j))
               (mv nil nil 0)))
            ((equal tag 9) (fn-bpnrb-counted j end fn-octets))
            ((equal tag 10)
             (mv-let (ok a k) (fn-bpnrb-dec j end (1- d) fn-octets)
               (if (not ok)
                   (mv nil nil 0)
                 (mv-let (ok2 b k2) (fn-bpnrb-dec k end (1- d) fn-octets)
                   (if (not ok2)
                       (mv nil nil 0)
                     (mv t (cons a b) k2))))))
            (t (mv nil nil 0))))))

; One value that is not a pair (tag 10), without recursion: what the host's
; bounded machine (fn-bpnrb-mstep) executes, since the machine splits every
; pair into goals itself (lane depth-debt, PRF-919).  Equal to
; `fn-bpnrb-dec' there (fn-bpnrb-dec-leaf-is-dec), so the recursive decoder
; stays the specification and never runs on the host's stack.
(defun fn-bpnrb-dec-leaf (i end d fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp end) (natp d)
                              (<= end (fn-octets-len fn-octets)))
                  :verify-guards nil))
  (if (or (zp d) (not (natp i)) (not (natp end)) (<= end i))
      (mv nil nil 0)
    (let ((tag (fn-octets-get i fn-octets)) (j (1+ i)))
      (cond ((equal tag 0) (mv t nil j))
            ((equal tag 1) (mv t t j))
            ((or (equal tag 2) (equal tag 3) (equal tag 4) (equal tag 7))
             (mv-let (ok codes k) (fn-bpnrb-counted j end fn-octets)
               (if (not ok)
                   (mv nil nil 0)
                 (let ((s (coerce (fn-bpnr-chars codes) 'string)))
                   (mv t
                       (cond ((equal tag 2) (intern-in-package-of-symbol s :fn))
                             ((equal tag 3)
                              (intern-in-package-of-symbol s 'fn-bpnr-dec))
                             ((equal tag 4) (intern-in-package-of-symbol s 'car))
                             (t s))
                       k)))))
            ((equal tag 5)
             (if (< end (+ j 8))
                 (mv nil nil 0)
               (mv t (fn-bpnrb-u64 j fn-octets) (+ j 8))))
            ((equal tag 6)
             (if (< end (+ j 8))
                 (mv nil nil 0)
               (mv t (- (nfix (fn-bpnrb-u64 j fn-octets))) (+ j 8))))
            ((equal tag 8)
             (if (and (< j end) (fn-cbor-octetp (fn-octets-get j fn-octets)))
                 (mv t (code-char (fn-octets-get j fn-octets)) (1+ j))
               (mv nil nil 0)))
            ((equal tag 9) (fn-bpnrb-counted j end fn-octets))
            (t (mv nil nil 0))))))

(defthm fn-bpnrb-dec-leaf-is-dec
  (implies (not (and (not (zp d)) (natp i) (natp end) (< i end)
                     (equal (fn-octets-get i fn-octets) 10)))
           (equal (fn-bpnrb-dec-leaf i end d fn-octets)
                  (fn-bpnrb-dec i end d fn-octets)))
  :hints (("Goal" :expand ((fn-bpnrb-dec i end d fn-octets))
                  :in-theory (disable fn-bpnrb-counted fn-bpnrb-u64))))

(in-theory (disable fn-bpnrb-u64))

(defthm fn-bpnrb-counted-next
  (and (natp (mv-nth 2 (fn-bpnrb-counted i end x)))
       (implies (and (mv-nth 0 (fn-bpnrb-counted i end x)) (natp end))
                (<= (mv-nth 2 (fn-bpnrb-counted i end x)) end)))
  :rule-classes ((:type-prescription :corollary
                  (natp (mv-nth 2 (fn-bpnrb-counted i end x))))
                 (:linear :corollary
                  (implies (and (mv-nth 0 (fn-bpnrb-counted i end x)) (natp end))
                           (<= (mv-nth 2 (fn-bpnrb-counted i end x)) end))))
  :hints (("Goal" :in-theory (union-theories '(fn-bpnrb-counted nfix natp)
                                             (theory 'minimal-theory)))))

(defthm fn-bpnrb-dec-next
  (and (natp (mv-nth 2 (fn-bpnrb-dec i end d x)))
       (implies (and (mv-nth 0 (fn-bpnrb-dec i end d x)) (natp end))
                (<= (mv-nth 2 (fn-bpnrb-dec i end d x)) end)))
  :rule-classes ((:type-prescription :corollary
                  (natp (mv-nth 2 (fn-bpnrb-dec i end d x))))
                 (:linear :corollary
                  (implies (and (mv-nth 0 (fn-bpnrb-dec i end d x)) (natp end))
                           (<= (mv-nth 2 (fn-bpnrb-dec i end d x)) end))))
  :hints (("Goal" :induct (fn-bpnrb-dec i end d x)
           :in-theory (union-theories '(fn-bpnrb-dec fn-bpnrb-counted-next natp nfix zp
                                        (:e zp) (:e natp) (:t fn-bpnrb-u64))
                                      (theory 'minimal-theory)))))

(verify-guards fn-bpnrb-dec)
(verify-guards fn-bpnrb-dec-leaf)

(local
 (defthm fn-bpnrb-u64-is
   (implies (and (fn-cbor-octet-listp x) (natp i) (<= (+ i 8) (len x)))
            (equal (fn-bpnrb-u64 i x)
                   (fn-bpc-u64-from (fn-oct-slice-list i (+ i 8) x))))
   :hints (("Goal" :in-theory (e/d (fn-bpnrb-u64) (fn-bpc-u64-from fn-bpnr-read-u64))
            :use ((:instance fn-bpnrb-read-u64-of-slice (n (+ i 8))))))))

(local
 (defthm fn-bpnrb-append-nil
   (implies (true-listp x) (equal (append x nil) x))))

;; The index decoder is the list decoder over the slice [i, end): the same
;; verdict, the same value, and the rest of the slice is the cells from the
;; returned index.
(defthm fn-bpnrb-dec-is-dec
  (implies (and (fn-cbor-octet-listp x) (natp i) (natp end) (<= end (len x)))
           (equal (fn-bpnr-dec (fn-oct-slice-list i end x) d)
                  (if (mv-nth 0 (fn-bpnrb-dec i end d x))
                      (cons (mv-nth 1 (fn-bpnrb-dec i end d x))
                            (fn-oct-slice-list (mv-nth 2 (fn-bpnrb-dec i end d x))
                                               end x))
                    nil)))
  :hints (("Goal" :induct (fn-bpnrb-dec i end d x)
           :in-theory (disable fn-bpc-u64-from fn-bpnr-read-u64
                               fn-bpnr-read-counted)
           :expand ((fn-bpnr-dec (fn-oct-slice-list i end x) d)
                    (fn-bpnrb-dec i end d x)))))

; -----------------------------------------------------------------------------
; The decode as bounded steps (the producer/consumer discipline of the store
; checkpoint pipeline).  The recursion of `fn-bpnrb-dec' becomes an explicit
; machine: a position I, a list of GOALS (a natural D: decode one value with
; depth budget D here; :pair: combine the two values on top) and the stack
; VALS of decoded values.  The host runs it a quantum at a time
; (`fn-bpnrb-plan-step'): at most Q steps and about B octets per call, the
; continuation (E I GOALS VALS) handed back exactly; nothing is truncated,
; an exhausted quantum resumes.

;; Progress: a value decoded consumes at least one octet.
(defthm fn-bpnrb-counted-progress
  (implies (mv-nth 0 (fn-bpnrb-counted i end x))
           (< i (mv-nth 2 (fn-bpnrb-counted i end x))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (union-theories '(fn-bpnrb-counted nfix natp)
                                             (theory 'minimal-theory)))))

(defthm fn-bpnrb-dec-progress
  (implies (mv-nth 0 (fn-bpnrb-dec i end d x))
           (< i (mv-nth 2 (fn-bpnrb-dec i end d x))))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-bpnrb-dec i end d x)
           :in-theory (union-theories '(fn-bpnrb-dec fn-bpnrb-counted-next
                                        fn-bpnrb-counted-progress natp nfix zp
                                        (:e zp) (:e natp) (:t fn-bpnrb-u64))
                                      (theory 'minimal-theory)))))

(defun fn-bpnrb-mstep (i end goals vals fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp end) (<= end (fn-octets-len fn-octets)))))
  (if (or (atom goals) (not (natp i)))
      (mv nil 0 nil nil)
    (let ((g (car goals)) (rest (cdr goals)))
      (if (eq g :pair)
          (if (and (consp vals) (consp (cdr vals)))
              (mv t i rest (cons (cons (cadr vals) (car vals)) (cddr vals)))
            (mv nil 0 nil nil))
        (let ((d (nfix g)))
          (if (or (zp d) (<= end i))
              (mv nil 0 nil nil)
            (if (equal (fn-octets-get i fn-octets) 10)
                (mv t (1+ i) (list* (1- d) (1- d) :pair rest) vals)
              (mv-let (ok v k) (mbe :logic (fn-bpnrb-dec i end d fn-octets)
                                     :exec (fn-bpnrb-dec-leaf i end d fn-octets))
                (if ok
                    (mv t k rest (cons v vals))
                  (mv nil 0 nil nil))))))))))

(defun fn-bpnrb-measure (i end goals)
  (declare (xargs :guard t))
  (let ((r (nfix (- (nfix end) (nfix i)))))
    (+ r r r (len goals))))

(defthm fn-bpnrb-mstep-progress
  (implies (and (mv-nth 0 (fn-bpnrb-mstep i end goals vals x)) (natp end))
           (and (natp (mv-nth 1 (fn-bpnrb-mstep i end goals vals x)))
                (< (fn-bpnrb-measure (mv-nth 1 (fn-bpnrb-mstep i end goals vals x))
                                     end
                                     (mv-nth 2 (fn-bpnrb-mstep i end goals vals x)))
                   (fn-bpnrb-measure i end goals))))
  :hints (("Goal" :in-theory (disable fn-bpnrb-dec fn-bpnrb-dec-next)
           :use ((:instance fn-bpnrb-dec-next (d (nfix (car goals))))))))

; The whole run: the specification of the host's loop of quanta.
(defun fn-bpnrb-mrun-all (i end goals vals fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp end) (<= end (fn-octets-len fn-octets)))
                  :measure (fn-bpnrb-measure i end goals)
                  :hints (("Goal" :use ((:instance fn-bpnrb-mstep-progress (x fn-octets)))
                           :in-theory (disable fn-bpnrb-mstep fn-bpnrb-measure
                                               fn-bpnrb-mstep-progress)))
                  :verify-guards nil))
  (if (or (atom goals) (not (natp end)))
      (mv (natp end) i vals)
    (mv-let (ok i2 goals2 vals2) (fn-bpnrb-mstep i end goals vals fn-octets)
      (if ok
          (fn-bpnrb-mrun-all i2 end goals2 vals2 fn-octets)
        (mv nil 0 nil)))))

(local
 (defun-nx fn-bpnrb-dec-ind (i end d goals vals x)
   (declare (xargs :measure (nfix d)
                   :hints (("Goal" :in-theory (disable fn-bpnrb-dec)))))
   (if (or (zp d) (not (natp i)) (not (natp end)) (<= end i))
       (list goals vals)
     (if (equal (nth i x) 10)
         (mv-let (ok a k) (fn-bpnrb-dec (1+ i) end (1- d) x)
           (declare (ignore ok))
           (list (fn-bpnrb-dec-ind (1+ i) end (1- d) (list* (1- d) :pair goals) vals x)
                 (fn-bpnrb-dec-ind k end (1- d) (cons :pair goals) (cons a vals) x)))
       (list goals vals)))))

;; The pair case of the recursive decoder, stated once.
(local
 (defthm fn-bpnrb-dec-of-pair
   (implies (and (not (zp d)) (natp i) (natp end) (< i end)
                 (equal (nth i x) 10))
            (equal (fn-bpnrb-dec i end d x)
                   (mv-let (ok a k) (fn-bpnrb-dec (1+ i) end (1- d) x)
                     (if (not ok)
                         (mv nil nil 0)
                       (mv-let (ok2 b k2) (fn-bpnrb-dec k end (1- d) x)
                         (if (not ok2)
                             (mv nil nil 0)
                           (mv t (cons a b) k2)))))))
   :hints (("Goal" :expand ((fn-bpnrb-dec i end d x))))))

(local
 (defthm fn-bpnrb-dec-refuses-without-input
   (implies (or (zp d) (not (natp i)) (not (natp end)) (<= end i))
            (not (mv-nth 0 (fn-bpnrb-dec i end d x))))
   :hints (("Goal" :expand ((fn-bpnrb-dec i end d x))))))

;; The machine run from a decode goal is the recursive decoder's result
;; followed by the run of the remaining goals.
(defthm fn-bpnrb-mrun-all-of-dec-goal
  (implies (and (natp i) (natp end) (natp d))
           (equal (fn-bpnrb-mrun-all i end (cons d goals) vals x)
                  (if (mv-nth 0 (fn-bpnrb-dec i end d x))
                      (fn-bpnrb-mrun-all (mv-nth 2 (fn-bpnrb-dec i end d x)) end goals
                                         (cons (mv-nth 1 (fn-bpnrb-dec i end d x)) vals) x)
                    (mv nil 0 nil))))
  :hints (("Goal" :induct (fn-bpnrb-dec-ind i end d goals vals x)
           :in-theory (disable fn-bpnrb-dec)
           :expand ((fn-bpnrb-mrun-all i end (cons d goals) vals x)))))

; One quantum: at most Q machine steps, stopping once the steps have
; consumed B octets or more.
(defun fn-bpnrb-mrun (q b i end goals vals fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp q) (integerp b) (natp end)
                              (<= end (fn-octets-len fn-octets)))
                  :measure (nfix q)
                  :verify-guards nil))
  (if (or (zp q) (atom goals) (not (natp end)))
      (mv t i goals vals)
    (mv-let (ok i2 goals2 vals2) (fn-bpnrb-mstep i end goals vals fn-octets)
      (if (not ok)
          (mv nil 0 nil nil)
        (let ((b2 (- (ifix b) (- (nfix i2) (nfix i)))))
          (if (<= b2 0)
              (mv t i2 goals2 vals2)
            (fn-bpnrb-mrun (1- q) b2 i2 end goals2 vals2 fn-octets)))))))

;; A quantum keeps the run: the whole run from where it stops is the whole
;; run from where it started, and a refused quantum is a refused run.
(defthm fn-bpnrb-mrun-all-of-mrun
  (equal (fn-bpnrb-mrun-all i end goals vals x)
         (if (mv-nth 0 (fn-bpnrb-mrun q b i end goals vals x))
             (fn-bpnrb-mrun-all (mv-nth 1 (fn-bpnrb-mrun q b i end goals vals x)) end
                                (mv-nth 2 (fn-bpnrb-mrun q b i end goals vals x))
                                (mv-nth 3 (fn-bpnrb-mrun q b i end goals vals x)) x)
           (mv nil 0 nil)))
  :hints (("Goal" :induct (fn-bpnrb-mrun q b i end goals vals x)
           :in-theory (disable fn-bpnrb-mstep))))

(local
 (defthm fn-bpnrb-u64-from-natp
   (implies (fn-cbor-octet-listp xs)
            (natp (fn-bpc-u64-from xs)))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-bpc-u64-from fn-cbor-u32-from
                                      fn-cbor-octet-listp fn-cbor-octetp)))))

(local
 (defthm fn-bpnrb-slice-iff
   (iff (fn-oct-slice-list i n x)
        (and (natp i) (natp n) (< i n)))
   :hints (("Goal" :use fn-bpnrb-slice-consp
            :in-theory (disable fn-bpnrb-slice-consp)))))

; -----------------------------------------------------------------------------
; The file: head, u64 payload length, payload, 32-octet trailer.

; The frame: head, u64 payload length, trailer over the prefix.  The end
; of the payload, or nil.
(defun fn-bpnrb-frame-end (m budget fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp m) (<= m (fn-octets-len fn-octets)))))
  (if (or (not (natp budget)) (not (natp m)) (< m 14))
      nil
    (if (not (equal (fn-bpnrb-slice-acc 0 6 nil fn-octets) *fn-bpnr-head*))
        nil
      (let ((e (+ 14 (nfix (fn-bpnrb-u64 6 fn-octets)))))
        (if (< m e)
            nil
          (if (not (equal (fn-bpnrb-slice-acc e m nil fn-octets)
                          (fn-frame-trailer
                           (fn-bpnr-checkpoint-prefix
                            (fn-bpnrb-slice-acc 14 e nil fn-octets)))))
              nil
            e))))))

(defthm fn-bpnrb-frame-end-bound
  (implies (fn-bpnrb-frame-end m budget x)
           (and (natp (fn-bpnrb-frame-end m budget x))
                (<= 14 (fn-bpnrb-frame-end m budget x))
                (<= (fn-bpnrb-frame-end m budget x) m)))
  :rule-classes ((:rewrite :corollary
                  (implies (fn-bpnrb-frame-end m budget x)
                           (natp (fn-bpnrb-frame-end m budget x))))
                 (:linear :corollary
                  (implies (fn-bpnrb-frame-end m budget x)
                           (and (<= 14 (fn-bpnrb-frame-end m budget x))
                                (<= (fn-bpnrb-frame-end m budget x) m)))))
  :hints (("Goal" :in-theory (disable fn-frame-trailer fn-bpnr-checkpoint-prefix
                                      fn-bpnrb-slice-acc-is-slice))))

; The value's decode runs on the goal-stack machine (lane depth-debt-2,
; PRF-919): the recursive decoder took one control-stack frame per level of
; the value's cons structure, whose depth the budget caps -- 4096 plus four
; per job, operator data.  fn-bpnrb-mrun-all-of-dec-goal is the equality.
(verify-guards fn-bpnrb-mrun-all
  :hints (("Goal" :in-theory (disable fn-bpnrb-mstep))))

(defun fn-bpnrb-decode-range (m budget fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp m) (<= m (fn-octets-len fn-octets)))
                  :verify-guards nil))
  (let ((e (fn-bpnrb-frame-end m budget fn-octets)))
    (if (not e)
        nil
      (mbe :logic (mv-let (ok v k) (fn-bpnrb-dec 14 e budget fn-octets)
                    (if (and ok (<= e k) (fn-bpnr-checkpointp v)) v nil))
           :exec (mv-let (ok k vals) (fn-bpnrb-mrun-all 14 e (list budget) nil fn-octets)
                   (if (and ok (consp vals) (<= e k) (fn-bpnr-checkpointp (car vals)))
                       (car vals)
                     nil))))))

(defthm fn-bpnrb-frame-end-budget-natp
  (implies (fn-bpnrb-frame-end m budget x) (natp budget))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (disable fn-frame-trailer fn-bpnr-checkpoint-prefix
                                      fn-bpnrb-slice-acc-is-slice))))

(verify-guards fn-bpnrb-decode-range
  :hints (("Goal" :in-theory (disable fn-bpnrb-mrun-all fn-bpnrb-dec fn-bpnrb-frame-end
                                      fn-bpnr-checkpointp)
                  :use ((:instance fn-bpnrb-mrun-all-of-dec-goal
                                   (i 14) (end (fn-bpnrb-frame-end m budget fn-octets))
                                   (d budget) (goals nil) (vals nil) (x fn-octets))))))

(defthm fn-bpnrb-decode-range-is-decode
  (implies (and (fn-cbor-octet-listp x) (natp m) (<= m (len x)))
           (equal (fn-bpnrb-decode-range m budget x)
                  (fn-bpnr-checkpoint-decode (fn-oct-slice-list 0 m x) budget)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-bpc-u64-from fn-bpnr-read-u64 fn-bpnr-dec
                               fn-frame-trailer fn-bpnr-checkpoint-prefix
                               fn-bpnr-checkpointp fn-bpnrb-dec)
           :use ((:instance fn-bpnrb-dec-is-dec (i 14) (d budget)
                            (end (+ 14 (nfix (fn-bpc-u64-from
                                              (fn-oct-slice-list 6 14 x))))))))))

; The entry: the buffer's whole contents.
(defun fn-bpnrb-checkpoint-decode (budget fn-octets)
  (declare (xargs :stobjs fn-octets :guard t))
  (mbe :logic (if (fn-octets-p fn-octets)
                  (fn-bpnrb-decode-range (fn-octets-len fn-octets) budget fn-octets)
                nil)
       :exec (fn-bpnrb-decode-range (fn-octets-len fn-octets) budget fn-octets)))

;; KEYSTONE (boundary).  The buffer decode is the list decode of the
;; buffer's value: the same checkpoint on every file the list decoder
;; takes, nil on every file it refuses.
(defthm fn-bpnrb-checkpoint-decode-is-decode
  (equal (fn-bpnrb-checkpoint-decode budget x)
         (fn-bpnr-checkpoint-decode x budget))
  :hints (("Goal" :in-theory (e/d (fn-oct-octets-p-is-octet-listp fn-octets-len)
                                  (fn-bpnrb-decode-range fn-bpnr-checkpoint-decode))
           :cases ((fn-cbor-octet-listp x)))
          ("Subgoal 2" :in-theory (enable fn-oct-octets-p-is-octet-listp
                                          fn-bpnr-checkpoint-decode))))

(include-book "bp-node-rotation")

; What the host calls at open (host/native/bp-service.lisp
; fnn-bps-selection-plan, on `fn-octets-bp').
(defun fn-bpnrb-selection-plan (present budget fn-octets)
  (declare (xargs :stobjs fn-octets :guard t))
  (if (not present)
      (list :none)
    (let ((ck (fn-bpnrb-checkpoint-decode budget fn-octets)))
      (if ck (list :selected ck) (list :damaged)))))

(defthm fn-bpnrb-selection-plan-is-selection-plan
  (equal (fn-bpnrb-selection-plan present budget x)
         (fn-bpnr-selection-plan present x budget))
  :hints (("Goal" :in-theory (e/d (fn-bpnr-selection-plan)
                                  (fn-bpnrb-checkpoint-decode
                                   fn-bpnr-checkpoint-decode)))))

