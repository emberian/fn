; fn: the runtime contract's executable state, an abstract stobj.
;
; `fn-rtc-st' is the layer state of books/runtime-contract.lisp as one
; single-threaded object: its LOGICAL value is the list state
; (config slots pool uses mstates next-op) the contract's definitions and
; keystones are about, and its EXECUTABLE is arrays: the slot table and the
; machine states one cell per slot, each buffer's (generation owner fill) one
; cell per buffer, and every buffer's octets in ONE (unsigned-byte 8) array,
; buffer h at cells [base(h), base(h) + cap(h)).  No buffer's bytes are ever a list
; at run time; a worker's input lands in the array in place.
;
; Every export's :logic is the contract's own state operation (fn-rtc-slot,
; fn-rtc-with-slot, fn-rtc-with-buffer of the buffer's fields, fn-rtc-issue,
; fn-rtc-release-all, fn-rtc-view ...), so a function written over the
; exports IS, logically, the contract's function over the list state; the
; executable layer (books/runtime-contract-exec.lisp) proves that equality
; once and the keystones follow.

(in-package "ACL2")
(include-book "runtime-contract-pool-impl")
(local (include-book "arithmetic-5/top" :dir :system))
(local (in-theory (disable nth update-nth)))

; -----------------------------------------------------------------------------
; The defabsstobj obligations, as `defabsstobj-missing-events' states them,
; with the lemmas they use.

(defthm fn-rtc-c-get-is-nth
  (implies (true-listp l) (equal (fn-rtc-get i l) (nth (nfix i) l)))
  :hints (("Goal" :in-theory (enable nth))))

(defthm fn-rtc-c-get-non-natp
  (implies (not (natp i)) (equal (fn-rtc-get i l) (fn-rtc-get 0 l))))

(defthm fn-rtc-c-abs-accessors
  (and (equal (fn-rtc-config (fn-rtc-c-abs c)) (nth *fn-rtc-c-cfg* c))
       (equal (fn-rtc-slots (fn-rtc-c-abs c)) (nth *fn-rtc-c-slotsi* c))
       (equal (fn-rtc-mstates (fn-rtc-c-abs c)) (nth *fn-rtc-c-msi* c))
       (equal (fn-rtc-uses (fn-rtc-c-abs c)) (nth *fn-rtc-c-uses* c))
       (equal (fn-rtc-next-op (fn-rtc-c-abs c)) (nfix (nth *fn-rtc-c-nop* c)))
       (equal (fn-rtc-pool (fn-rtc-c-abs c))
              (fn-rtc-c-pool 0 (fn-rtc-nbufs (nth *fn-rtc-c-cfg* c))
                             (nth *fn-rtc-c-cfg* c)
                             (nth *fn-rtc-c-metai* c) (nth *fn-rtc-c-bytesi* c)))))

(in-theory (disable fn-rtc-c-get-is-nth fn-rtc-c-get-non-natp fn-rtc-c-abs))

(defthm fn-rtc-c-abs-buffer
  (equal (fn-rtc-buffer h (fn-rtc-c-abs c))
         (if (< (nfix h) (fn-rtc-nbufs (nth *fn-rtc-c-cfg* c)))
             (fn-rtc-c-buffer (nfix h) (nth *fn-rtc-c-cfg* c)
                              (nth *fn-rtc-c-metai* c) (nth *fn-rtc-c-bytesi* c))
           nil))
  :hints (("Goal" :do-not '(preprocess) :in-theory (e/d (fn-rtc-buffer fn-rtc-c-get-non-natp) (fn-rtc-c-buffer))
           :cases ((natp h)))))

(local (defun fn-rtc-c-ind-km (i k meta)
  (if (or (zp i) (atom meta)) (list i k meta) (fn-rtc-c-ind-km (- i 1) (+ 1 k) (cdr meta)))))

(local (defun fn-rtc-c-ind-nth (i j n)
  (if (or (zp i) (zp n)) (list i j n) (fn-rtc-c-ind-nth (- i 1) (+ 1 (nfix j)) (- n 1)))))

(defthm fn-rtc-c-nth-of-octets
  (equal (nth i (fn-rtc-c-octets j n b))
         (if (< (nfix i) (nfix n)) (nth (+ (nfix j) (nfix i)) b) nil))
  :hints (("Goal" :in-theory (enable nth) :induct (fn-rtc-c-ind-nth i j n) :expand ((fn-rtc-c-octets j n b)))))

(defthm fn-rtc-c-nthcdr-past-len
  (implies (and (true-listp l) (<= (len l) (nfix n)))
           (equal (nthcdr n l) nil))
  :hints (("Goal" :in-theory (enable nthcdr))))

(defthm fn-rtc-c-nthcdr-is-cons
  (implies (< (nfix i) (len l))
           (equal (nthcdr i l) (cons (nth i l) (nthcdr (+ 1 (nfix i)) l))))
  :hints (("Goal" :in-theory (enable nthcdr nth))))

(defthm fn-rtc-c-free-slot-loop-is
  (implies (fn-rtc-st$cp c)
           (equal (fn-rtc-c-free-slot-loop i c)
                  (fn-rtc-free-slot (nfix i) (nthcdr (nfix i) (nth *fn-rtc-c-slotsi* c)))))
  :hints (("Goal" :induct (fn-rtc-c-free-slot-loop i c)
           :in-theory (disable nthcdr))))

(local (defun fn-rtc-c-ind-vp (j k pool)
  (if (or (zp j) (atom pool)) (list j k pool) (fn-rtc-c-ind-vp (- j 1) (+ 1 k) (cdr pool)))))

(defthm fn-rtc-c-get-of-view-pool
  (implies (and (natp j) (natp k))
           (equal (fn-rtc-get j (fn-rtc-view-pool id inc cfg k pool))
                  (if (< j (len pool))
                      (let* ((b (fn-rtc-get j pool)) (o (fn-rtc-b-owner b)))
                        (cond ((fn-rtc-view-own-p o id inc) b)
                              ((fn-rtc-view-mine-p o (+ k j) id inc cfg) (list (fn-rtc-b-gen b) o nil))
                              (t '(0 (:other) nil))))
                    nil)))
  :hints (("Goal" :induct (fn-rtc-c-ind-vp j k pool)
           :in-theory (disable fn-rtc-view-own-p fn-rtc-view-mine-p fn-rtc-b-gen fn-rtc-b-owner)
           :expand ((fn-rtc-view-pool id inc cfg k pool)))))

(defthm fn-rtc-c-len-of-view-pool
  (equal (len (fn-rtc-view-pool id inc cfg k pool)) (len pool)))

(defthm fn-rtc-c-read-octets-is
  (implies (fn-rtc-st$cp c)
           (equal (fn-rtc-c-read-octets i n c)
                  (fn-rtc-c-octets i n (nth *fn-rtc-c-bytesi* c))))
  :hints (("Goal" :in-theory (enable nth))))

(in-theory (disable fn-rtc-c-nthcdr-is-cons))

(defthm fn-rtc-c-cp-of-meta-facts (implies (fn-rtc-st$cp c) (fn-rtc-c-bytesp (nth *fn-rtc-c-bytesi* c))) :rule-classes nil)

(defthm fn-rtc-c-v-pool-loop-is
  (implies (and (fn-rtc-st$cp c) (natp h)
                (<= (+ h (nfix n)) (len (nth *fn-rtc-c-metai* c))))
           (equal (fn-rtc-c-v-pool-loop h n id inc c)
                  (fn-rtc-view-pool id inc (nth *fn-rtc-c-cfg* c) h
                                    (fn-rtc-c-pool h n (nth *fn-rtc-c-cfg* c)
                                                   (nth *fn-rtc-c-metai* c) (nth *fn-rtc-c-bytesi* c)))))
  :hints (("Goal" :induct (fn-rtc-c-v-pool-loop h n id inc c)
           :in-theory (disable fn-rtc-get fn-rtc-st$cp fn-rtc-view-own-p fn-rtc-view-mine-p))
          ("Subgoal *1/2" :in-theory (e/d (fn-rtc-b-gen fn-rtc-b-owner) (fn-rtc-st$cp fn-rtc-view-own-p fn-rtc-view-mine-p)))))

(defthm fn-rtc-c-nth-past-len
  (implies (<= (len l) (nfix n)) (equal (nth n l) nil))
  :hints (("Goal" :in-theory (enable nth))))

(defthm fn-rtc-st-config{correspondence}
  (implies (fn-rtc-st$corr fn-rtc-st$c fn-rtc-st)
           (equal (fn-rtc-st$c-config fn-rtc-st$c) (fn-rtc-st$a-config fn-rtc-st)))
  :rule-classes nil)

(defthm fn-rtc-st-slot{correspondence}
  (implies (fn-rtc-st$corr fn-rtc-st$c fn-rtc-st)
           (equal (fn-rtc-st$c-slot id fn-rtc-st$c) (fn-rtc-st$a-slot id fn-rtc-st)))
  :hints (("Goal" :in-theory (enable fn-rtc-slot fn-rtc-c-get-is-nth)))
  :rule-classes nil)

(defthm fn-rtc-st-mstate{correspondence}
  (implies (fn-rtc-st$corr fn-rtc-st$c fn-rtc-st)
           (equal (fn-rtc-st$c-mstate id fn-rtc-st$c) (fn-rtc-st$a-mstate id fn-rtc-st)))
  :hints (("Goal" :in-theory (enable fn-rtc-mstate fn-rtc-c-get-is-nth)))
  :rule-classes nil)

(defthm fn-rtc-st-uses{correspondence}
  (implies (fn-rtc-st$corr fn-rtc-st$c fn-rtc-st)
           (equal (fn-rtc-st$c-uses fn-rtc-st$c) (fn-rtc-st$a-uses fn-rtc-st)))
  :rule-classes nil)

(defthm fn-rtc-st-next-op{correspondence}
  (implies (fn-rtc-st$corr fn-rtc-st$c fn-rtc-st)
           (equal (fn-rtc-st$c-next-op fn-rtc-st$c) (fn-rtc-st$a-next-op fn-rtc-st)))
  :rule-classes nil)

(defthm fn-rtc-st-owner{correspondence}
  (implies (fn-rtc-st$corr fn-rtc-st$c fn-rtc-st)
           (equal (fn-rtc-st$c-owner h fn-rtc-st$c) (fn-rtc-st$a-owner h fn-rtc-st)))
  :rule-classes nil)

(defthm fn-rtc-st-gen{correspondence}
  (implies (fn-rtc-st$corr fn-rtc-st$c fn-rtc-st)
           (equal (fn-rtc-st$c-gen h fn-rtc-st$c) (fn-rtc-st$a-gen h fn-rtc-st)))
  :rule-classes nil)

(defthm fn-rtc-st-fill{correspondence}
  (implies (fn-rtc-st$corr fn-rtc-st$c fn-rtc-st)
           (equal (fn-rtc-st$c-fill h fn-rtc-st$c) (fn-rtc-st$a-fill h fn-rtc-st)))
  :rule-classes nil)

(defthm fn-rtc-st-byte{correspondence}
  (implies (fn-rtc-st$corr fn-rtc-st$c fn-rtc-st)
           (equal (fn-rtc-st$c-byte h i fn-rtc-st$c) (fn-rtc-st$a-byte h i fn-rtc-st)))
  :rule-classes nil)

(defthm fn-rtc-st-free-slot{correspondence}
  (implies (fn-rtc-st$corr fn-rtc-st$c fn-rtc-st)
           (equal (fn-rtc-st$c-free-slot fn-rtc-st$c) (fn-rtc-st$a-free-slot fn-rtc-st)))
  :hints (("Goal" :in-theory (disable fn-rtc-c-free-slot-loop)))
  :rule-classes nil)

(defthm fn-rtc-c-vb-of-abs
  (implies (and (fn-rtc-st$cp c) (fn-rtc-c-wfp c))
           (equal (fn-rtc-vb h id inc (fn-rtc-c-abs c))
                  (if (< (nfix h) (fn-rtc-nbufs (nth *fn-rtc-c-cfg* c)))
                      (let* ((m (nth (nfix h) (nth *fn-rtc-c-metai* c))) (o (fn-rtc-get 1 m))
                             (b (fn-rtc-c-buffer (nfix h) (nth *fn-rtc-c-cfg* c)
                                                 (nth *fn-rtc-c-metai* c) (nth *fn-rtc-c-bytesi* c))))
                        (cond ((fn-rtc-view-own-p o id inc) b)
                              ((fn-rtc-view-mine-p o (nfix h) id inc (nth *fn-rtc-c-cfg* c))
                               (list (nfix (fn-rtc-get 0 m)) o nil))
                              (t '(0 (:other) nil))))
                    nil)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-vb fn-rtc-view fn-rtc-c-abs fn-rtc-c-get-non-natp fn-rtc-b-gen fn-rtc-b-owner)
                                  (fn-rtc-view-own-p fn-rtc-view-mine-p fn-rtc-view-pool))
           :cases ((natp h)))))

(defthm fn-rtc-st-v-owner{correspondence}
  (implies (fn-rtc-st$corr fn-rtc-st$c fn-rtc-st)
           (equal (fn-rtc-st$c-v-owner h id inc fn-rtc-st$c) (fn-rtc-st$a-v-owner h id inc fn-rtc-st)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-b-owner) (fn-rtc-view-own-p fn-rtc-view-mine-p fn-rtc-vb))))
  :rule-classes nil)

(defthm fn-rtc-st-v-gen{correspondence}
  (implies (fn-rtc-st$corr fn-rtc-st$c fn-rtc-st)
           (equal (fn-rtc-st$c-v-gen h id inc fn-rtc-st$c) (fn-rtc-st$a-v-gen h id inc fn-rtc-st)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-b-gen) (fn-rtc-view-own-p fn-rtc-view-mine-p fn-rtc-vb))))
  :rule-classes nil)

(defthm fn-rtc-st-v-fill{correspondence}
  (implies (fn-rtc-st$corr fn-rtc-st$c fn-rtc-st)
           (equal (fn-rtc-st$c-v-fill h id inc fn-rtc-st$c) (fn-rtc-st$a-v-fill h id inc fn-rtc-st)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-b-bytes) (fn-rtc-view-own-p fn-rtc-view-mine-p fn-rtc-vb))))
  :rule-classes nil)

(defthm fn-rtc-st-v-byte{correspondence}
  (implies (fn-rtc-st$corr fn-rtc-st$c fn-rtc-st)
           (equal (fn-rtc-st$c-v-byte h i id inc fn-rtc-st$c) (fn-rtc-st$a-v-byte h i id inc fn-rtc-st)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-b-bytes) (fn-rtc-view-own-p fn-rtc-view-mine-p fn-rtc-vb))
           :use (fn-rtc-st-byte{correspondence})))
  :rule-classes nil)

(defthm fn-rtc-st-v-pool{correspondence}
  (implies (fn-rtc-st$corr fn-rtc-st$c fn-rtc-st)
           (equal (fn-rtc-st$c-v-pool id inc fn-rtc-st$c) (fn-rtc-st$a-v-pool id inc fn-rtc-st)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-view fn-rtc-c-abs) (fn-rtc-c-v-pool-loop fn-rtc-view-pool))))
  :rule-classes nil)

(defthm fn-rtc-c-set-is-update-nth
  (implies (true-listp l)
           (equal (fn-rtc-set i v l)
                  (if (< (nfix i) (len l)) (update-nth (nfix i) v l) l)))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm fn-rtc-c-slotsp-of-update-nth
  (implies (and (fn-rtc-c-slotsp l) (< (nfix i) (len l))) (fn-rtc-c-slotsp (update-nth i v l)))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm fn-rtc-c-msp-of-update-nth
  (implies (and (fn-rtc-c-msp l) (< (nfix i) (len l))) (fn-rtc-c-msp (update-nth i v l)))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm fn-rtc-c-metap-of-update-nth
  (implies (and (fn-rtc-c-metap l) (< (nfix i) (len l))) (fn-rtc-c-metap (update-nth i v l)))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm fn-rtc-c-metas-okp-of-update-nth
  (implies (and (fn-rtc-c-metas-okp k meta cfg) (natp k) (natp i) (< i (len meta))
                (natp (fn-rtc-get 0 v)) (natp (fn-rtc-get 2 v)) (<= (fn-rtc-get 2 v) (fn-rtc-buf-cap (+ k i) cfg)))
           (fn-rtc-c-metas-okp k (update-nth i v meta) cfg))
  :hints (("Goal" :induct (fn-rtc-c-ind-km i k meta) :in-theory (e/d (update-nth) (fn-rtc-buf-cap)))))

(local (defun fn-rtc-c-ind-set (i k pool)
  (if (or (zp i) (atom pool)) (list i k pool) (fn-rtc-c-ind-set (- i 1) (+ 1 k) (cdr pool)))))

(defthm fn-rtc-c-pool-shapep-of-set
  (implies (and (fn-rtc-pool-shapep k pool cfg) (natp k) (natp i)
                (true-listp b) (equal (len b) 3) (natp (fn-rtc-get 0 b))
                (fn-cbor-octet-listp (fn-rtc-get 2 b)) (<= (len (fn-rtc-get 2 b)) (fn-rtc-buf-cap (+ k i) cfg)))
           (fn-rtc-pool-shapep k (fn-rtc-set i b pool) cfg))
  :hints (("Goal" :induct (fn-rtc-c-ind-set i k pool) :in-theory (disable fn-rtc-buf-cap fn-rtc-c-set-is-update-nth))))

; The same over update-nth, the form fn-rtc-c-set-is-update-nth leaves.
(defthm fn-rtc-c-pool-shapep-of-update-nth
  (implies (and (fn-rtc-pool-shapep k pool cfg) (natp k) (natp i) (< i (len pool))
                (true-listp b) (equal (len b) 3) (natp (fn-rtc-get 0 b))
                (fn-cbor-octet-listp (fn-rtc-get 2 b)) (<= (len (fn-rtc-get 2 b)) (fn-rtc-buf-cap (+ k i) cfg)))
           (fn-rtc-pool-shapep k (update-nth i b pool) cfg))
  :hints (("Goal" :use (fn-rtc-c-pool-shapep-of-set
                        (:instance fn-rtc-c-set-is-update-nth (v b) (l pool)))
           :in-theory (disable fn-rtc-c-pool-shapep-of-set fn-rtc-c-set-is-update-nth fn-rtc-buf-cap))))

(defthm fn-rtc-st-set-slot{correspondence}
  (implies (fn-rtc-st$corr fn-rtc-st$c fn-rtc-st)
           (fn-rtc-st$corr (fn-rtc-st$c-set-slot id slot fn-rtc-st$c)
                           (fn-rtc-st$a-set-slot id slot fn-rtc-st)))
  :hints (("Goal" :in-theory (enable fn-rtc-with-slot fn-rtc-c-abs)))
  :rule-classes nil)

(defthm fn-rtc-st-set-slot{preserved}
  (implies (fn-rtc-st$ap fn-rtc-st)
           (fn-rtc-st$ap (fn-rtc-st$a-set-slot id slot fn-rtc-st)))
  :hints (("Goal" :in-theory (enable fn-rtc-with-slot)))
  :rule-classes nil)

(defthm fn-rtc-st-set-mstate{correspondence}
  (implies (fn-rtc-st$corr fn-rtc-st$c fn-rtc-st)
           (fn-rtc-st$corr (fn-rtc-st$c-set-mstate id m fn-rtc-st$c)
                           (fn-rtc-st$a-set-mstate id m fn-rtc-st)))
  :hints (("Goal" :in-theory (enable fn-rtc-with-mstate fn-rtc-c-abs)))
  :rule-classes nil)

(defthm fn-rtc-st-set-mstate{preserved}
  (implies (fn-rtc-st$ap fn-rtc-st)
           (fn-rtc-st$ap (fn-rtc-st$a-set-mstate id m fn-rtc-st)))
  :hints (("Goal" :in-theory (enable fn-rtc-with-mstate)))
  :rule-classes nil)

(defthm fn-rtc-st-set-uses{correspondence}
  (implies (fn-rtc-st$corr fn-rtc-st$c fn-rtc-st)
           (fn-rtc-st$corr (fn-rtc-st$c-set-uses uses fn-rtc-st$c)
                           (fn-rtc-st$a-set-uses uses fn-rtc-st)))
  :hints (("Goal" :in-theory (enable fn-rtc-with-uses fn-rtc-c-abs)))
  :rule-classes nil)

(defthm fn-rtc-st-set-uses{preserved}
  (implies (fn-rtc-st$ap fn-rtc-st)
           (fn-rtc-st$ap (fn-rtc-st$a-set-uses uses fn-rtc-st)))
  :hints (("Goal" :in-theory (enable fn-rtc-with-uses)))
  :rule-classes nil)

(defthm fn-rtc-st-issue{correspondence}
  (implies (fn-rtc-st$corr fn-rtc-st$c fn-rtc-st)
           (fn-rtc-st$corr (fn-rtc-st$c-issue use fn-rtc-st$c)
                           (fn-rtc-st$a-issue use fn-rtc-st)))
  :hints (("Goal" :in-theory (enable fn-rtc-issue fn-rtc-c-abs)))
  :rule-classes nil)

(defthm fn-rtc-st-issue{preserved}
  (implies (fn-rtc-st$ap fn-rtc-st)
           (fn-rtc-st$ap (fn-rtc-st$a-issue use fn-rtc-st)))
  :hints (("Goal" :in-theory (enable fn-rtc-issue)))
  :rule-classes nil)

(defthm fn-rtc-st-set-meta{correspondence}
  (implies (fn-rtc-st$corr fn-rtc-st$c fn-rtc-st)
           (fn-rtc-st$corr (fn-rtc-st$c-set-meta h gen owner fn-rtc-st$c)
                           (fn-rtc-st$a-set-meta h gen owner fn-rtc-st)))
  :hints (("Goal" :in-theory (enable fn-rtc-with-buffer fn-rtc-c-abs)
           :use ((:instance fn-rtc-c-fill-of-metas-okp (j (nfix h))
                            (meta (nth *fn-rtc-c-metai* fn-rtc-st$c))
                            (cfg (nth *fn-rtc-c-cfg* fn-rtc-st$c))))))
  :rule-classes nil)

(defthm fn-rtc-c-pool-shapep-get
  (implies (and (fn-rtc-pool-shapep k pool cfg) (natp k))
           (and (fn-cbor-octet-listp (fn-rtc-get 2 (fn-rtc-get h pool)))
                (<= (len (fn-rtc-get 2 (fn-rtc-get h pool))) (fn-rtc-buf-cap (+ k (nfix h)) cfg))
                (implies (< (nfix h) (len pool))
                         (and (natp (fn-rtc-get 0 (fn-rtc-get h pool)))
                              (true-listp (fn-rtc-get h pool))
                              (equal (len (fn-rtc-get h pool)) 3))))))

(defthm fn-rtc-c-shapep-buffer
  (implies (fn-rtc-shapep s)
           (and (fn-cbor-octet-listp (fn-rtc-get 2 (fn-rtc-buffer h s)))
                (<= (len (fn-rtc-get 2 (fn-rtc-buffer h s))) (fn-rtc-buf-cap h (fn-rtc-config s)))
                (implies (< (nfix h) (fn-rtc-nbufs (fn-rtc-config s)))
                         (and (natp (fn-rtc-get 0 (fn-rtc-buffer h s)))
                              (true-listp (fn-rtc-buffer h s))
                              (equal (len (fn-rtc-buffer h s)) 3)))))
  :hints (("Goal" :in-theory (e/d () (fn-rtc-c-pool-shapep-get))
           :use ((:instance fn-rtc-c-pool-shapep-get (pool (fn-rtc-pool s)) (k 0)
                            (cfg (fn-rtc-config s)))))))

(defthm fn-rtc-st-set-meta{preserved}
  (implies (fn-rtc-st$ap fn-rtc-st)
           (fn-rtc-st$ap (fn-rtc-st$a-set-meta h gen owner fn-rtc-st)))
  :hints (("Goal" :in-theory (enable fn-rtc-with-buffer)
           :use ((:instance fn-rtc-c-shapep-buffer (s fn-rtc-st)))))
  :rule-classes nil)

(defthm fn-rtc-st-reset{correspondence}
  (implies (fn-rtc-st$corr fn-rtc-st$c fn-rtc-st)
           (fn-rtc-st$corr (fn-rtc-st$c-reset h gen owner fn-rtc-st$c)
                           (fn-rtc-st$a-reset h gen owner fn-rtc-st)))
  :hints (("Goal" :in-theory (enable fn-rtc-with-buffer fn-rtc-c-abs)
           :use ((:instance fn-rtc-c-fill-of-metas-okp (j (nfix h))
                            (meta (nth *fn-rtc-c-metai* fn-rtc-st$c))
                            (cfg (nth *fn-rtc-c-cfg* fn-rtc-st$c))))))
  :rule-classes nil)

(defthm fn-rtc-st-reset{preserved}
  (implies (fn-rtc-st$ap fn-rtc-st)
           (fn-rtc-st$ap (fn-rtc-st$a-reset h gen owner fn-rtc-st)))
  :hints (("Goal" :in-theory (enable fn-rtc-with-buffer)
           :use ((:instance fn-rtc-c-shapep-buffer (s fn-rtc-st)))))
  :rule-classes nil)

(defthm fn-rtc-c-fill-natp-of-metas-okp-at
  (implies (and (fn-rtc-c-metas-okp k meta cfg) (natp k) (natp j) (< j (len meta)))
           (natp (fn-rtc-get 2 (nth j meta))))
  :hints (("Goal" :induct (fn-rtc-c-ind-km j k meta) :in-theory (e/d (nth) (fn-rtc-buf-cap)))))

(defthm fn-rtc-c-fill-natp-of-metas-okp
  (implies (and (fn-rtc-c-metas-okp 0 meta cfg) (natp j) (< j (len meta)))
           (natp (fn-rtc-get 2 (nth j meta))))
  :hints (("Goal" :use ((:instance fn-rtc-c-fill-natp-of-metas-okp-at (k 0))))))

(defthm fn-rtc-c-set-of-set-same
  (equal (fn-rtc-set i v (fn-rtc-set i w l)) (fn-rtc-set i v l)))

(defthm fn-rtc-c-splice-region
  (implies (and (fn-rtc-configp cfg) (natp h) (< h (fn-rtc-nbufs cfg)) (natp off) (natp len)
                (<= (+ off len) (fn-rtc-buf-cap h cfg)))
           (and (<= (+ (fn-rtc-buf-base h cfg) off len) (fn-rtc-octets-total cfg))
                (<= (fn-rtc-buf-base h cfg) (+ (fn-rtc-buf-base h cfg) off))
                (<= (+ (fn-rtc-buf-base h cfg) off len) (+ (fn-rtc-buf-base h cfg) (fn-rtc-buf-cap h cfg)))))
  :hints (("Goal" :in-theory (disable fn-rtc-buf-base-monotone fn-rtc-buf-base-of-nbufs fn-rtc-buf-cap)
           :use ((:instance fn-rtc-buf-base-monotone (j h) (h (fn-rtc-nbufs cfg)))
                 fn-rtc-buf-base-of-nbufs)))
  :rule-classes nil)

(defthm fn-rtc-c-abs-of-splice
  (implies (and (fn-rtc-st$cp c) (fn-rtc-c-wfp c)
                (natp h) (< h (len (nth *fn-rtc-c-metai* c)))
                (natp off) (fn-cbor-octet-listp data)
                (<= off (nfix (fn-rtc-get 2 (nth h (nth *fn-rtc-c-metai* c)))))
                (<= (+ off (len data)) (fn-rtc-buf-cap h (nth *fn-rtc-c-cfg* c))))
           (equal (fn-rtc-c-pool 0 (fn-rtc-nbufs (nth *fn-rtc-c-cfg* c)) (nth *fn-rtc-c-cfg* c)
                                 (update-nth h (list (fn-rtc-get 0 (nth h (nth *fn-rtc-c-metai* c)))
                                                     (fn-rtc-get 1 (nth h (nth *fn-rtc-c-metai* c)))
                                                     (fn-rtc-c-max (nfix (fn-rtc-get 2 (nth h (nth *fn-rtc-c-metai* c))))
                                                          (+ off (len data))))
                                             (nth *fn-rtc-c-metai* c))
                                 (fn-rtc-c-write-list (+ (fn-rtc-buf-base h (nth *fn-rtc-c-cfg* c)) off) data
                                                      (nth *fn-rtc-c-bytesi* c)))
                  (fn-rtc-set h (list (fn-rtc-get 0 (nth h (nth *fn-rtc-c-metai* c)))
                                      (fn-rtc-get 1 (nth h (nth *fn-rtc-c-metai* c)))
                                      (fn-rtc-splice (fn-rtc-c-octets (fn-rtc-buf-base h (nth *fn-rtc-c-cfg* c))
                                                                      (nfix (fn-rtc-get 2 (nth h (nth *fn-rtc-c-metai* c))))
                                                                      (nth *fn-rtc-c-bytesi* c))
                                                     off data))
                              (fn-rtc-c-pool 0 (fn-rtc-nbufs (nth *fn-rtc-c-cfg* c)) (nth *fn-rtc-c-cfg* c)
                                             (nth *fn-rtc-c-metai* c) (nth *fn-rtc-c-bytesi* c)))))
  :hints (("Goal" :in-theory (disable fn-rtc-splice fn-rtc-c-octets-of-splice fn-rtc-get)
           :use ((:instance fn-rtc-c-splice-region (cfg (nth *fn-rtc-c-cfg* c)) (len (len data)))
                 (:instance fn-rtc-c-octets-of-splice (base (fn-rtc-buf-base h (nth *fn-rtc-c-cfg* c)))
                            (fl (nfix (fn-rtc-get 2 (nth h (nth *fn-rtc-c-metai* c)))))
                            (bytes (nth *fn-rtc-c-bytesi* c)))))))

(defthm fn-rtc-st-splice{correspondence}
  (implies (fn-rtc-st$corr fn-rtc-st$c fn-rtc-st)
           (fn-rtc-st$corr (fn-rtc-st$c-splice h off data fn-rtc-st$c)
                           (fn-rtc-st$a-splice h off data fn-rtc-st)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-with-buffer fn-rtc-c-abs) (fn-rtc-splice fn-rtc-c-write fn-rtc-c-pool-of-update-meta fn-rtc-c-pool-of-write fn-rtc-c-splice-of-octets fn-rtc-c-octets-of-splice fn-rtc-c-abs-of-splice
                                                  fn-cbor-octet-listp fn-cbor-octetp fn-rtc-get-out-of-range
                                                  fn-rtc-c-nth-past-len))
           :use ((:instance fn-rtc-c-abs-of-splice (c fn-rtc-st$c))
                 (:instance fn-rtc-c-fill-of-metas-okp (j h)
                            (meta (nth *fn-rtc-c-metai* fn-rtc-st$c))
                            (cfg (nth *fn-rtc-c-cfg* fn-rtc-st$c)))
                 (:instance fn-rtc-c-fill-natp-of-metas-okp (j h)
                            (meta (nth *fn-rtc-c-metai* fn-rtc-st$c))
                            (cfg (nth *fn-rtc-c-cfg* fn-rtc-st$c)))
                 (:instance fn-rtc-c-gen-of-metas-okp (j h)
                            (meta (nth *fn-rtc-c-metai* fn-rtc-st$c))
                            (cfg (nth *fn-rtc-c-cfg* fn-rtc-st$c))))))
  :rule-classes nil)

(defthm fn-rtc-c-l-octets-append
  (implies (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp b))
           (fn-cbor-octet-listp (append a b))))

(defthm fn-rtc-c-l-octets-take
  (implies (and (fn-cbor-octet-listp a) (natp n) (<= n (len a)))
           (fn-cbor-octet-listp (take n a))))

(defthm fn-rtc-c-l-octets-nthcdr
  (implies (fn-cbor-octet-listp a)
           (fn-cbor-octet-listp (nthcdr n a))))

(defthm fn-rtc-c-l-true-list-fix-identity
  (implies (true-listp a) (equal (true-list-fix a) a)))

(defthm fn-rtc-c-l-len-take
  (equal (len (take n a)) (nfix n)))

(defthm fn-rtc-c-l-len-nthcdr
  (equal (len (nthcdr n a)) (nfix (- (len a) (nfix n))))
  :hints (("Goal" :induct (nthcdr n a))))

(defthm fn-rtc-c-l-len-append
  (equal (len (append a b)) (+ (len a) (len b))))

(defthm fn-rtc-c-l-splice-octets
  (implies (and (fn-cbor-octet-listp bytes) (fn-cbor-octet-listp data)
                (natp off) (<= off (len bytes)))
           (fn-cbor-octet-listp (fn-rtc-splice bytes off data)))
  :hints (("Goal" :in-theory (disable fn-cbor-octet-listp take nthcdr true-list-fix))))

(defthm fn-rtc-c-l-splice-length
  (implies (and (true-listp bytes) (true-listp data)
                (natp off) (<= off (len bytes)))
           (equal (len (fn-rtc-splice bytes off data))
                  (max (len bytes) (+ off (len data)))))
  :hints (("Goal" :in-theory (disable take nthcdr true-list-fix))))

(defthm fn-rtc-st-splice{preserved}
  (implies (fn-rtc-st$ap fn-rtc-st)
           (fn-rtc-st$ap (fn-rtc-st$a-splice h off data fn-rtc-st)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-with-buffer) (fn-rtc-splice))
           :use ((:instance fn-rtc-c-shapep-buffer (s fn-rtc-st)))))
  :rule-classes nil)

(defun fn-rtc-c-release-meta (m id inc)
  (declare (xargs :guard t))
  (if (equal (fn-rtc-get 1 m) (list :workspace id inc))
      (list (fn-rtc-get 0 m) '(:free) (fn-rtc-get 2 m))
    m))

(defun fn-rtc-c-release-metas (h meta id inc)
  (declare (xargs :guard (natp h) :measure (nfix (- (len meta) (nfix h))) :verify-guards nil))
  (let ((h (nfix h)))
    (if (< h (len meta))
        (fn-rtc-c-release-metas (+ 1 h) (update-nth h (fn-rtc-c-release-meta (nth h meta) id inc) meta)
                                id inc)
      meta)))

(defthm fn-rtc-c-release-loop-is
  (implies (fn-rtc-st$cp c)
           (equal (fn-rtc-c-release-loop h id inc c)
                  (update-nth *fn-rtc-c-metai*
                              (fn-rtc-c-release-metas h (nth *fn-rtc-c-metai* c) id inc) c)))
  :hints (("Goal" :induct (fn-rtc-c-release-loop h id inc c))))

(defthm fn-rtc-c-len-of-release-metas
  (equal (len (fn-rtc-c-release-metas h meta id inc)) (len meta)))

(defthm fn-rtc-c-nth-of-release-metas-below
  (implies (and (natp j) (< j (nfix h)))
           (equal (nth j (fn-rtc-c-release-metas h meta id inc)) (nth j meta))))

(defthm fn-rtc-c-release-meta-fields
  (and (equal (fn-rtc-get 0 (fn-rtc-c-release-meta m id inc)) (fn-rtc-get 0 m))
       (equal (fn-rtc-get 2 (fn-rtc-c-release-meta m id inc)) (fn-rtc-get 2 m))))

(defthm fn-rtc-c-metas-okp-of-same-fields
  (implies (and (fn-rtc-c-metas-okp k meta cfg) (natp k) (natp j) (< j (len meta))
                (equal (fn-rtc-get 0 v) (fn-rtc-get 0 (nth j meta)))
                (equal (fn-rtc-get 2 v) (fn-rtc-get 2 (nth j meta))))
           (fn-rtc-c-metas-okp k (update-nth j v meta) cfg))
  :hints (("Goal" :induct (fn-rtc-c-ind-km j k meta)
           :in-theory (e/d (update-nth nth) (fn-rtc-get fn-rtc-buf-cap)))))

(defthm fn-rtc-c-metas-okp-of-release-meta
  (implies (and (fn-rtc-c-metas-okp 0 meta cfg) (natp j) (< j (len meta)))
           (fn-rtc-c-metas-okp 0 (update-nth j (fn-rtc-c-release-meta (nth j meta) id inc) meta) cfg))
  :hints (("Goal" :in-theory (disable fn-rtc-get fn-rtc-c-release-meta))))

(defthm fn-rtc-c-metas-okp-of-release-metas
  (implies (fn-rtc-c-metas-okp 0 meta cfg)
           (fn-rtc-c-metas-okp 0 (fn-rtc-c-release-metas h meta id inc) cfg))
  :hints (("Goal" :induct (fn-rtc-c-release-metas h meta id inc)
           :in-theory (disable fn-rtc-c-release-meta))))

(defthm fn-rtc-c-metap-of-release-metas
  (implies (fn-rtc-c-metap meta) (fn-rtc-c-metap (fn-rtc-c-release-metas h meta id inc))))

(defun fn-rtc-c-ind-release (k n meta id inc)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (list k meta)
    (fn-rtc-c-ind-release (+ 1 (nfix k)) (- n 1)
                          (update-nth (nfix k) (fn-rtc-c-release-meta (nth (nfix k) meta) id inc) meta)
                          id inc)))

(defthm fn-rtc-c-pool-of-release-metas
  (implies (and (fn-rtc-c-metas-okp 0 meta cfg) (natp k) (equal (+ k (nfix n)) (len meta)))
           (equal (fn-rtc-c-pool k n cfg (fn-rtc-c-release-metas k meta id inc) bytes)
                  (fn-rtc-release-all (fn-rtc-c-pool k n cfg meta bytes) id inc)))
  :hints (("Goal" :induct (fn-rtc-c-ind-release k n meta id inc))
          ("Subgoal *1/2" :expand ((fn-rtc-c-release-metas k meta id inc))
           :use ((:instance fn-rtc-c-gen-of-metas-okp (j k))))))

(defthm fn-rtc-c-pool-shapep-of-release-all
  (implies (fn-rtc-pool-shapep k pool cfg)
           (fn-rtc-pool-shapep k (fn-rtc-release-all pool id inc) cfg)))

(defthm fn-rtc-c-len-of-release-all
  (equal (len (fn-rtc-release-all pool id inc)) (len pool)))

(defthm fn-rtc-st-release-all{correspondence}
  (implies (fn-rtc-st$corr fn-rtc-st$c fn-rtc-st)
           (fn-rtc-st$corr (fn-rtc-st$c-release-all id inc fn-rtc-st$c)
                           (fn-rtc-st$a-release-all id inc fn-rtc-st)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-c-abs) (fn-rtc-c-release-loop fn-rtc-release-all))))
  :rule-classes nil)

(defthm fn-rtc-st-release-all{preserved}
  (implies (fn-rtc-st$ap fn-rtc-st)
           (fn-rtc-st$ap (fn-rtc-st$a-release-all id inc fn-rtc-st)))
  :hints (("Goal" :in-theory (disable fn-rtc-release-all)))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; The fresh state: the fill loops write one value from an index to the end.

(defun fn-rtc-c-rep (n v)
  (declare (xargs :guard (natp n)))
  (if (zp n) nil (cons v (fn-rtc-c-rep (- n 1) v))))

(defun fn-rtc-c-fill-list (i v l)
  (declare (xargs :guard (natp i) :measure (nfix (- (len l) (nfix i))) :verify-guards nil))
  (let ((i (nfix i)))
    (if (< i (len l)) (fn-rtc-c-fill-list (+ 1 i) v (update-nth i v l)) l)))

(defthm fn-rtc-c-take-of-update-nth-last
  (implies (and (natp i) (< i (len l)))
           (equal (take (+ 1 i) (update-nth i v l))
                  (append (take i l) (list v))))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm fn-rtc-c-rep-cons
  (implies (natp k) (equal (cons v (fn-rtc-c-rep k v)) (fn-rtc-c-rep (+ 1 k) v))))

(defthm fn-rtc-c-append-assoc
  (equal (append (append a b) c) (append a (append b c))))

(defthm fn-rtc-c-take-of-len
  (implies (true-listp l) (equal (take (len l) l) l)))

(defthm fn-rtc-c-true-list-len-zero
  (implies (and (true-listp l) (equal (len l) 0)) (equal l nil))
  :rule-classes :forward-chaining)

(defthm fn-rtc-c-fill-list-is
  (implies (and (natp i) (<= i (len l)) (true-listp l))
           (equal (fn-rtc-c-fill-list i v l)
                  (append (take i l) (fn-rtc-c-rep (- (len l) i) v))))
  :hints (("Goal" :induct (fn-rtc-c-fill-list i v l))
          ("Subgoal *1/1" :in-theory (disable fn-rtc-c-rep-cons)
           :use ((:instance fn-rtc-c-rep-cons (k (- (len l) (+ 1 i))))))))

(defthm fn-rtc-c-fill-slots-is
  (implies (fn-rtc-st$cp c)
           (equal (fn-rtc-c-fill-slots i v c)
                  (update-nth *fn-rtc-c-slotsi* (fn-rtc-c-fill-list i v (nth *fn-rtc-c-slotsi* c)) c)))
  :hints (("Goal" :induct (fn-rtc-c-fill-slots i v c) :in-theory (disable fn-rtc-c-fill-list-is))))
(defthm fn-rtc-c-fill-ms-is
  (implies (fn-rtc-st$cp c)
           (equal (fn-rtc-c-fill-ms i v c)
                  (update-nth *fn-rtc-c-msi* (fn-rtc-c-fill-list i v (nth *fn-rtc-c-msi* c)) c)))
  :hints (("Goal" :induct (fn-rtc-c-fill-ms i v c) :in-theory (disable fn-rtc-c-fill-list-is))))
(defthm fn-rtc-c-fill-meta-is
  (implies (fn-rtc-st$cp c)
           (equal (fn-rtc-c-fill-meta i v c)
                  (update-nth *fn-rtc-c-metai* (fn-rtc-c-fill-list i v (nth *fn-rtc-c-metai* c)) c)))
  :hints (("Goal" :induct (fn-rtc-c-fill-meta i v c) :in-theory (disable fn-rtc-c-fill-list-is))))

(in-theory (disable fn-rtc-c-rep-cons))

(defthm fn-rtc-c-free-slots-is-rep
  (equal (fn-rtc-free-slots k) (fn-rtc-c-rep k '(0 :free nil))))

(defthm fn-rtc-c-append-rep-cons
  (equal (append (fn-rtc-c-rep k v) (cons v acc))
         (cons v (append (fn-rtc-c-rep k v) acc)))
  :hints (("Goal" :in-theory (disable fn-rtc-c-rep-cons))))

(defthm fn-rtc-c-make-list-ac-is-rep
  (equal (make-list-ac n v acc) (append (fn-rtc-c-rep n v) acc))
  :hints (("Goal" :in-theory (disable fn-rtc-c-rep-cons))))

(defthm fn-rtc-c-len-of-rep
  (equal (len (fn-rtc-c-rep n v)) (nfix n)))

(defthm fn-rtc-c-true-listp-of-rep
  (true-listp (fn-rtc-c-rep n v)))

(defun fn-rtc-c-ind-rep (i n)
  (if (or (zp i) (zp n)) (list i n) (fn-rtc-c-ind-rep (- i 1) (- n 1))))



(defthm fn-rtc-c-nth-of-rep
  (equal (nth i (fn-rtc-c-rep n v)) (if (< (nfix i) (nfix n)) v nil))
  :hints (("Goal" :in-theory (enable nth) :induct (fn-rtc-c-ind-rep i n) :expand ((fn-rtc-c-rep n v)))))

(defthm fn-rtc-c-pool-of-rep-free
  (implies (and (natp k) (<= (+ k (nfix n)) (nfix bign)))
           (equal (fn-rtc-c-pool k n cfg (fn-rtc-c-rep bign '(0 (:free) 0)) bytes)
                  (fn-rtc-free-pool n))))

(local (defun fn-rtc-c-ind-rk (n k)
  (if (zp n) (list n k) (fn-rtc-c-ind-rk (- n 1) (+ 1 (nfix k))))))

(defthm fn-rtc-c-metas-okp-of-rep-free
  (fn-rtc-c-metas-okp k (fn-rtc-c-rep n '(0 (:free) 0)) cfg)
  :hints (("Goal" :induct (fn-rtc-c-ind-rk n k) :in-theory (disable fn-rtc-buf-cap))))

(defthm fn-rtc-c-len-of-resize-list
  (equal (len (resize-list l n d)) (nfix n)))

(defthm fn-rtc-c-true-listp-of-resize-list
  (true-listp (resize-list l n d)))

(defthm fn-rtc-c-array-recognizers-of-lists
  (and (equal (fn-rtc-c-slotsp x) (true-listp x))
       (equal (fn-rtc-c-msp x) (true-listp x))
       (equal (fn-rtc-c-metap x) (true-listp x))))

(defthm fn-rtc-c-bytesp-of-resize-list
  (implies (fn-rtc-c-bytesp l) (fn-rtc-c-bytesp (resize-list l n 0))))

(defthm fn-rtc-c-slots-after-init
  (implies (and (natp n) (<= 1 n) (true-listp l) (equal (len l) n))
           (equal (update-nth 0 v (append (take 1 l) (fn-rtc-c-rep (- n 1) w)))
                  (cons v (fn-rtc-c-rep (- n 1) w))))
  :hints (("Goal" :in-theory (enable update-nth) :expand ((take 1 l)))))

(defthm fn-rtc-c-free-pool-is-rep
  (equal (fn-rtc-free-pool n) (fn-rtc-c-rep n '(0 (:free) nil))))

(defthm fn-rtc-c-pool-shapep-of-rep-free
  (fn-rtc-pool-shapep k (fn-rtc-c-rep n '(0 (:free) nil)) cfg)
  :hints (("Goal" :induct (fn-rtc-c-ind-rk n k) :in-theory (disable fn-rtc-buf-cap))))

(verify-guards fn-rtc-st$c-init)

(defthm fn-rtc-st-init{correspondence}
  (implies (fn-rtc-st$corr fn-rtc-st$c fn-rtc-st)
           (fn-rtc-st$corr (fn-rtc-st$c-init cfg fn-rtc-st$c)
                           (fn-rtc-st$a-init cfg fn-rtc-st)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-c-abs) (fn-rtc-c-fill-slots fn-rtc-c-fill-ms fn-rtc-c-fill-meta
                                                  fn-rtc-free-slots fn-rtc-free-pool))))
  :rule-classes nil)

(defthm fn-rtc-st-init{preserved}
  (implies (fn-rtc-st$ap fn-rtc-st)
           (fn-rtc-st$ap (fn-rtc-st$a-init cfg fn-rtc-st)))
  :hints (("Goal" :in-theory (disable fn-rtc-free-slots fn-rtc-free-pool)))
  :rule-classes nil)

(defthm create-fn-rtc-st{correspondence}
  (fn-rtc-st$corr (create-fn-rtc-st$c) (create-fn-rtc-st$a))
  :hints (("Goal" :in-theory (enable fn-rtc-c-abs)))
  :rule-classes nil)

(defthm create-fn-rtc-st{preserved}
  (fn-rtc-st$ap (create-fn-rtc-st$a))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; The abstract stobj.

(defabsstobj fn-rtc-st
  :foundation fn-rtc-st$c
  :recognizer (fn-rtc-st-p :logic fn-rtc-st$ap :exec fn-rtc-st$cp)
  :creator (create-fn-rtc-st :logic create-fn-rtc-st$a :exec create-fn-rtc-st$c)
  :corr-fn fn-rtc-st$corr
  :exports ((fn-rtc-st-config :logic fn-rtc-st$a-config :exec fn-rtc-st$c-config)
            (fn-rtc-st-slot :logic fn-rtc-st$a-slot :exec fn-rtc-st$c-slot)
            (fn-rtc-st-mstate :logic fn-rtc-st$a-mstate :exec fn-rtc-st$c-mstate)
            (fn-rtc-st-uses :logic fn-rtc-st$a-uses :exec fn-rtc-st$c-uses)
            (fn-rtc-st-next-op :logic fn-rtc-st$a-next-op :exec fn-rtc-st$c-next-op)
            (fn-rtc-st-owner :logic fn-rtc-st$a-owner :exec fn-rtc-st$c-owner)
            (fn-rtc-st-gen :logic fn-rtc-st$a-gen :exec fn-rtc-st$c-gen)
            (fn-rtc-st-fill :logic fn-rtc-st$a-fill :exec fn-rtc-st$c-fill)
            (fn-rtc-st-byte :logic fn-rtc-st$a-byte :exec fn-rtc-st$c-byte)
            (fn-rtc-st-free-slot :logic fn-rtc-st$a-free-slot :exec fn-rtc-st$c-free-slot)
            (fn-rtc-st-v-owner :logic fn-rtc-st$a-v-owner :exec fn-rtc-st$c-v-owner)
            (fn-rtc-st-v-gen :logic fn-rtc-st$a-v-gen :exec fn-rtc-st$c-v-gen)
            (fn-rtc-st-v-fill :logic fn-rtc-st$a-v-fill :exec fn-rtc-st$c-v-fill)
            (fn-rtc-st-v-byte :logic fn-rtc-st$a-v-byte :exec fn-rtc-st$c-v-byte)
            (fn-rtc-st-v-pool :logic fn-rtc-st$a-v-pool :exec fn-rtc-st$c-v-pool)
            (fn-rtc-st-set-slot :logic fn-rtc-st$a-set-slot :exec fn-rtc-st$c-set-slot)
            (fn-rtc-st-set-mstate :logic fn-rtc-st$a-set-mstate :exec fn-rtc-st$c-set-mstate)
            (fn-rtc-st-set-uses :logic fn-rtc-st$a-set-uses :exec fn-rtc-st$c-set-uses)
            (fn-rtc-st-issue :logic fn-rtc-st$a-issue :exec fn-rtc-st$c-issue :protect t)
            (fn-rtc-st-set-meta :logic fn-rtc-st$a-set-meta :exec fn-rtc-st$c-set-meta)
            (fn-rtc-st-reset :logic fn-rtc-st$a-reset :exec fn-rtc-st$c-reset)
            (fn-rtc-st-splice :logic fn-rtc-st$a-splice :exec fn-rtc-st$c-splice :protect t)
            (fn-rtc-st-release-all :logic fn-rtc-st$a-release-all :exec fn-rtc-st$c-release-all :protect t)
            (fn-rtc-st-init :logic fn-rtc-st$a-init :exec fn-rtc-st$c-init :protect t)))
