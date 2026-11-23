; Discharges fn2-pool-byte-fill, fn2-pool-no-reuse and fn2-pool-generation.
; fn2-pool-stale is FALSE as stated and stays owed: on :release it holds exactly
; when the slot is not credit-held and release is admitted (see the end).
(in-package "ACL2")
(include-book "pool")
(include-book "owed-discharge")
(include-book "pool-release-admission")

; Readers stay opaque; each lemma opens the ones it reads through a writer.
(local
 (in-theory
  (disable fn2-pool-gen fn2-pool-base fn2-pool-cap fn2-pool-state
           fn2-pool-owner-kind fn2-pool-owner-slot fn2-pool-owner-gen
           fn2-pool-lease-op-slot fn2-pool-lease-op-gen fn2-pool-lease-off fn2-pool-lease-len
           fn2-pool-out-count fn2-pool-query-ref-count fn2-pool-fill
           fn2-pool-hand-to-kind fn2-pool-hand-to-slot fn2-pool-hand-to-gen
           fn2-pool-next-free fn2-pool-class fn2-pool-credit-group
           fn2-pool-datai fn2-pool-class-headsi fn2-pool-class-countsi fn2-pool-class-sizesi
           fn2-pool-nclasses fn2-pool-gen-limit fn2-pool-retired-count fn2-pool-rows
           fn2-pool-data-length fn2-pool-credit-configured fn2-pool-credit-protectedi
           fn2-pool-credit-protected-length
           fn2-pool-semanticp fn2-pool-row-invariantp fn2-pool-class-accountsp
           fn2-pool-release-countp fn2-pool-reservable-count fn2-pool-ownerp fn2-pool-mrefp
           fn2-pool-reserve fn2-pool-reserve-body fn2-pool-release fn2-pool-release-body
           fn2-pool-lease-in fn2-pool-adapter-write fn2-pool-complete-in fn2-pool-lease-out
           fn2-pool-release-out fn2-pool-query-acquire fn2-pool-query-release fn2-pool-hand
           fn2-pool-accept-hand fn2-pool-read fn2-pool-write fn2-pool-reset
           fn2-pool-logical-octets fn2-pool-operation
           fn2-pool-no-reuse-resultp fn2-pool-generation-resultp fn2-pool-byte-fill-resultp)))

; The clauses of one row of the semantic invariant that these theorems read.
(local
 (defun fn2-pool-owed-row-factp (i fn2-pool)
   (declare (xargs :stobjs fn2-pool :verify-guards nil))
   (and (iff (< 0 (fn2-pool-out-count i fn2-pool))
             (equal (fn2-pool-state i fn2-pool) *fn2-pool-state-leased-out*))
        (<= (fn2-pool-gen i fn2-pool) (fn2-pool-gen-limit fn2-pool))
        (implies (equal (fn2-pool-state i fn2-pool) *fn2-pool-state-leased-in*)
                 (and (equal (fn2-pool-fill i fn2-pool) (fn2-pool-lease-off i fn2-pool))
                      (<= (+ (fn2-pool-fill i fn2-pool) (fn2-pool-lease-len i fn2-pool))
                          (fn2-pool-cap i fn2-pool)))))))
(local
 (defthm fn2-pool-owed-row-invariant-at
   (implies (and (fn2-pool-row-invariantp n fn2-pool) (natp n) (natp i) (< i n))
            (fn2-pool-owed-row-factp i fn2-pool))
   :hints (("Goal" :induct (fn2-pool-row-invariantp n fn2-pool)
            :in-theory (e/d (fn2-pool-row-invariantp) (fn2-pool-owed-row-factp member-equal)))
           ("Subgoal *1/2" :cases ((equal i (+ -1 n))))
           ("Subgoal *1/2.1"
            :in-theory (e/d (fn2-pool-row-invariantp fn2-pool-owed-row-factp) (member-equal))))))
(local
 (defthm fn2-pool-owed-gen-limit-natp
   (implies (fn2-poolp fn2-pool) (natp (fn2-pool-gen-limit fn2-pool)))
   :hints (("Goal" :in-theory (enable fn2-poolp fn2-pool-gen-limit)))))
(local
 (defthm fn2-pool-owed-row-facts
   (implies (and (fn2-pool-semanticp fn2-pool) (natp i) (< i (fn2-pool-rows fn2-pool)))
            (and (natp (fn2-pool-gen i fn2-pool))
                 (natp (fn2-pool-gen-limit fn2-pool))
                 (iff (< 0 (fn2-pool-out-count i fn2-pool))
                      (equal (fn2-pool-state i fn2-pool) *fn2-pool-state-leased-out*))
                 (<= (fn2-pool-gen i fn2-pool) (fn2-pool-gen-limit fn2-pool))
                 (implies (equal (fn2-pool-state i fn2-pool) *fn2-pool-state-leased-in*)
                          (and (equal (fn2-pool-fill i fn2-pool) (fn2-pool-lease-off i fn2-pool))
                               (<= (+ (fn2-pool-fill i fn2-pool) (fn2-pool-lease-len i fn2-pool))
                                   (fn2-pool-cap i fn2-pool))))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn2-pool-semanticp fn2-pool-nslots fn2-pool-owed-row-factp)
                                   (fn2-pool-owed-row-invariant-at))
            :use ((:instance fn2-pool-owed-row-invariant-at (n (fn2-pool-rows fn2-pool))))))))
(local (in-theory (disable fn2-pool-owed-row-invariant-at fn2-pool-owed-row-factp)))
(local
 (defthm fn2-pool-owed-semantic-shape
   (implies (fn2-pool-semanticp fn2-pool)
            (and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn2-pool-semanticp)))))

; The semantic invariant funds release's constant-work admission premise, so
; release-body's mbt branch is never the one taken.
(local
 (defthm fn2-pool-owed-release-admitted
   (implies (fn2-pool-semanticp p) (fn2-pool-release-countp slot p))
   :hints (("Goal" :use ((:instance fn2-pool-semantic-workspace-admits-release (pool p)))
            :in-theory (enable fn2-pool-release-countp fn2-pool-logical-slotp fn2-pool-nslots)))))

(local
 (deftheory fn2-pool-owed-writers
   '(fn2-pool-set-gen update-fn2-pool-gen$ai fn2-pool-set-state update-fn2-pool-state$ai
     fn2-pool-set-fill update-fn2-pool-fill$ai
     fn2-pool-set-out-count update-fn2-pool-out-count$ai
     fn2-pool-set-query-ref-count update-fn2-pool-query-ref-count$ai
     fn2-pool-set-lease-off update-fn2-pool-lease-off$ai
     fn2-pool-set-lease-len update-fn2-pool-lease-len$ai
     fn2-pool-set-next-free update-fn2-pool-next-free$ai
     fn2-pool-set-owner-kind update-fn2-pool-owner-kind$ai
     fn2-pool-set-owner-slot update-fn2-pool-owner-slot$ai
     fn2-pool-set-owner-gen update-fn2-pool-owner-gen$ai
     fn2-pool-set-lease-op-slot update-fn2-pool-lease-op-slot$ai
     fn2-pool-set-lease-op-gen update-fn2-pool-lease-op-gen$ai
     fn2-pool-set-hand-to-kind update-fn2-pool-hand-to-kind$ai
     fn2-pool-set-hand-to-slot update-fn2-pool-hand-to-slot$ai
     fn2-pool-set-hand-to-gen update-fn2-pool-hand-to-gen$ai
     update-fn2-pool-class-headsi update-fn2-pool-class-countsi update-fn2-pool-datai
     update-fn2-pool-retired-count update-nth-array nth-update-nth)))
(local
 (deftheory fn2-pool-owed-ops
   '(fn2-pool-operation fn2-pool-reserve fn2-pool-reserve-body
     fn2-pool-release fn2-pool-release-body
     fn2-pool-lease-in fn2-pool-adapter-write fn2-pool-complete-in fn2-pool-lease-out
     fn2-pool-release-out fn2-pool-query-acquire fn2-pool-query-release fn2-pool-hand
     fn2-pool-accept-hand fn2-pool-read fn2-pool-write fn2-pool-reset
     fn2-pool-handle-code fn2-pool-workspace-code fn2-pool-input-code
     fn2-pool-readable-code)))

; An interval's octets read only the data field, so every writer of another
; field frames them by nth-update-nth.
(local
 (defun fn2-pool-owed-octs (n b data)
   (declare (xargs :measure (nfix n)))
   (if (zp n) nil
     (cons (nth b data) (fn2-pool-owed-octs (- n 1) (+ 1 b) data)))))
(local
 (defthm fn2-pool-owed-octets-as-octs
   (equal (fn2-pool-logical-octets n b fn2-pool)
          (fn2-pool-owed-octs n b (nth 25 fn2-pool)))
   :hints (("Goal" :induct (fn2-pool-logical-octets n b fn2-pool)
            :in-theory (enable fn2-pool-logical-octets fn2-pool-datai)))))
(local (in-theory (disable fn2-pool-owed-octets-as-octs)))
(local
 (defthm fn2-pool-owed-octs-append
   (implies (and (natp a) (natp c) (natp b))
            (equal (fn2-pool-owed-octs (+ a c) b data)
                   (append (fn2-pool-owed-octs a b data)
                           (fn2-pool-owed-octs c (+ b a) data))))
   :rule-classes nil))

;; ---------------------------------------------------------------------------
;; FN2-POOL-BYTE-FILL. The row invariant gives fill = lease-off and
;; fill + lease-len <= cap on a leased-in row, so completion is admitted and
;; the new prefix is the old prefix followed by the first n loan octets.
(local
 (defthm fn2-pool-byte-fill-holds
   (implies (fn2-pool-byte-fill-hyps op a p)
            (fn2-pool-byte-fill-conclusion op a p))
   :hints (("Goal"
            :use ((:instance fn2-pool-owed-row-facts (i (nth 0 a)) (fn2-pool p))
                  (:instance fn2-pool-owed-semantic-shape (fn2-pool p))
                  (:instance fn2-pool-lease-off-natp (i (nth 0 a)) (fn2-pool p))
                  (:instance fn2-pool-base-natp (i (nth 0 a)) (fn2-pool p))
                  (:instance fn2-pool-owed-octs-append
                             (a (fn2-pool-lease-off (nth 0 a) p)) (c (nth 4 a))
                             (b (fn2-pool-base (nth 0 a) p)) (data (nth 25 p))))
            :in-theory (e/d (fn2-pool-owed-writers fn2-pool-owed-octets-as-octs
                             fn2-pool-operation fn2-pool-adapter-write fn2-pool-complete-in
                             fn2-pool-handle-code fn2-pool-input-code
                             fn2-pool-state fn2-pool-state$ai fn2-pool-fill fn2-pool-fill$ai
                             fn2-pool-byte-fill-resultp fn2-pool-logical-slotp fn2-pool-nslots)
                            (fn2-pool-lease-off-natp fn2-pool-base-natp))))))
(defthm fn2-pool-byte-fill-proved
  (fn2-pool-byte-fill$owed op a p)
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-pool-byte-fill$owed) :use fn2-pool-byte-fill-holds)))
(fn2-owed-discharge fn2-pool-byte-fill fn2-pool-byte-fill-proved)

;; ---------------------------------------------------------------------------
;; One row's generation and state across one operation: the whole generation
;; conclusion, and for a leased-out row the generation/state half of no-reuse.
;; The operations are opened once here; both theorems below only use it.
(local
 (defthm fn2-pool-owed-row-step
   (implies (and (fn2-pool-semanticp p) (member-eq op *fn2-pool-operations*)
                 (fn2-pool-logical-slotp slot p))
            (let* ((r (fn2-pool-operation op a p)) (q (cadr r)))
              (and (fn2-pool-generation-resultp
                    op (equal slot (nth 0 a)) (car r)
                    (fn2-pool-gen slot p) (fn2-pool-gen slot q)
                    (fn2-pool-state slot p) (fn2-pool-state slot q) (fn2-pool-gen-limit p))
                   (implies (equal (fn2-pool-state slot p) *fn2-pool-state-leased-out*)
                            (and (equal (fn2-pool-gen slot q) (fn2-pool-gen slot p))
                                 (not (equal (fn2-pool-state slot q) *fn2-pool-state-free*))
                                 (not (equal (fn2-pool-state slot q)
                                             *fn2-pool-state-retired*)))))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance fn2-pool-owed-row-facts (i (nth 0 a)) (fn2-pool p)))
            :in-theory (enable fn2-pool-owed-writers fn2-pool-owed-ops
                               fn2-pool-gen fn2-pool-gen$ai fn2-pool-state fn2-pool-state$ai
                               fn2-pool-generation-resultp fn2-pool-logical-slotp
                               fn2-pool-nslots)))))

;; FN2-POOL-GENERATION.
(local
 (defthm fn2-pool-generation-holds
   (implies (fn2-pool-generation-hyps slot op a p)
            (fn2-pool-generation-conclusion slot op a p))
   :hints (("Goal" :use fn2-pool-owed-row-step))))
(defthm fn2-pool-generation-proved
  (fn2-pool-generation$owed slot op a p)
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-pool-generation$owed) :use fn2-pool-generation-holds)))
(fn2-owed-discharge fn2-pool-generation fn2-pool-generation-proved)

;; ---------------------------------------------------------------------------
;; FN2-POOL-NO-REUSE. Only :write and :adapter-write store a byte. Through the
;; borrowed row itself both refuse (it is leased-out, neither workspace nor
;; leased-in); through any other row the byte lands in that row's extent,
;; which pool.lisp proves apart from this one.
(local
 (defthm fn2-pool-owed-write-keeps-borrowed-extent
   (implies (and (fn2-pool-semanticp p) (natp slot) (< slot (fn2-pool-rows p))
                 (equal (fn2-pool-state slot p) *fn2-pool-state-leased-out*))
            (equal (fn2-pool-owed-octs
                    (fn2-pool-cap slot p) (fn2-pool-base slot p)
                    (nth 25 (mv-nth 1 (fn2-pool-write s g idx byte ok os og p))))
                   (fn2-pool-owed-octs (fn2-pool-cap slot p) (fn2-pool-base slot p)
                                       (nth 25 p))))
   :hints (("Goal" :cases ((equal s slot)))
           ("Subgoal 2"
            :use ((:instance fn2-pool-write-other-extent (other slot) (slot s) (gen g)
                             (okind ok) (oslot os) (ogen og) (fn2-pool p)))
            :in-theory (e/d (fn2-pool-owed-octets-as-octs) (fn2-pool-write-other-extent)))
           ("Subgoal 1"
            :in-theory (enable fn2-pool-write fn2-pool-workspace-code fn2-pool-handle-code)))))
(local
 (defthm fn2-pool-owed-adapter-write-keeps-borrowed-extent
   (implies (and (fn2-pool-semanticp p) (natp slot) (< slot (fn2-pool-rows p))
                 (equal (fn2-pool-state slot p) *fn2-pool-state-leased-out*))
            (equal (fn2-pool-owed-octs
                    (fn2-pool-cap slot p) (fn2-pool-base slot p)
                    (nth 25 (mv-nth 1 (fn2-pool-adapter-write s g opslot opgen idx byte p))))
                   (fn2-pool-owed-octs (fn2-pool-cap slot p) (fn2-pool-base slot p)
                                       (nth 25 p))))
   :hints (("Goal" :cases ((equal s slot)))
           ("Subgoal 2"
            :use ((:instance fn2-pool-adapter-write-other-extent (other slot) (slot s) (gen g)
                             (fn2-pool p)))
            :in-theory (e/d (fn2-pool-owed-octets-as-octs)
                            (fn2-pool-adapter-write-other-extent)))
           ("Subgoal 1"
            :in-theory (enable fn2-pool-adapter-write fn2-pool-input-code
                               fn2-pool-handle-code)))))
(local
 (defthm fn2-pool-owed-borrowed-extent
   (implies (and (fn2-pool-semanticp p) (member-eq op *fn2-pool-operations*)
                 (natp slot) (< slot (fn2-pool-rows p))
                 (equal (fn2-pool-state slot p) *fn2-pool-state-leased-out*))
            (equal (fn2-pool-logical-octets (fn2-pool-cap slot p) (fn2-pool-base slot p)
                                            (cadr (fn2-pool-operation op a p)))
                   (fn2-pool-logical-octets (fn2-pool-cap slot p) (fn2-pool-base slot p) p)))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (e/d (fn2-pool-owed-writers fn2-pool-owed-ops
                             fn2-pool-owed-octets-as-octs)
                            (fn2-pool-write fn2-pool-adapter-write))))))
(local
 (defthm fn2-pool-no-reuse-holds
   (implies (fn2-pool-no-reuse-hyps slot op a p)
            (fn2-pool-no-reuse-conclusion slot op a p))
   :hints (("Goal"
            :use ((:instance fn2-pool-owed-row-facts (i slot) (fn2-pool p))
                  fn2-pool-owed-row-step fn2-pool-owed-borrowed-extent)
            :in-theory (enable fn2-pool-no-reuse-resultp fn2-pool-logical-slotp
                               fn2-pool-nslots)))))
(defthm fn2-pool-no-reuse-proved
  (fn2-pool-no-reuse$owed slot op a p)
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn2-pool-no-reuse$owed) :use fn2-pool-no-reuse-holds)))
(fn2-owed-discharge fn2-pool-no-reuse fn2-pool-no-reuse-proved)

;; ---------------------------------------------------------------------------
;; FN2-POOL-STALE is FALSE as stated; it is NOT discharged and stays (:owed).
;;
;; fn2-pool-release decides two things before the generation: the credit-group
;; test (:credit), and release-body's mbt on fn2-pool-release-countp (:ok, pool
;; unchanged). fn2-pool-stale-hyps asks only fn2-pool-wfp, so neither is
;; excluded. Every other handle operation tests the generation first.
;;
;; Counterexample 1 (a semantic pool, inside every guard; evaluated below):
;;   p  = (fn2-pool-set-credit-group 0 0 (fn2-pool-init '((1 . 4)) 0 5 fn2-pool))
;;   op = :release   a = '(0 7 0 0 0)
;;   (fn2-pool-stale-hyps op a p) = T: wfp, slot 0 < 1 row, gen 7 /= stored 0.
;;   (fn2-pool-semanticp p) = T and (fn2-pool-release-countp 0 p) = T.
;;   (fn2-pool-release 0 7 0 0 0 p) = (mv :CREDIT p), so the code is not :STALE.
;;   A credit-held row arises in service: fn2-pool-reserve-credit (pool-credit.lisp)
;;   writes credit-group on the row it reserves.
;;
;; Counterexample 2 (wfp and fn2-poolp but not semantic; outside release's guard,
;; unreachable-in-composition; evaluated with guard checking off, not in this book):
;;   p  = (update-fn2-pool-retired-count 1 p1), p1 = the pool after
;;        (fn2-pool-reserve 0 1 2 3 (fn2-pool-init '((1 . 4)) 0 5 fn2-pool))
;;   op = :release   a = '(0 7 1 2 3)
;;   hyps = T, (fn2-pool-release-countp 0 p) = NIL (retired-count 1 = rows 1),
;;   (fn2-pool-release 0 7 1 2 3 p) = (mv :OK p), so the code is not :STALE.
;;   So adding only "not credit-held" to the hypotheses leaves the row false.
;;
;; The two theorems below fix the boundary exactly and are not a discharge.
(defthm fn2-pool-stale-off-release
  (implies (and (fn2-pool-stale-hyps op a p) (not (eq op :release)))
           (fn2-pool-stale-conclusion op a p))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-pool-owed-ops fn2-pool-logical-slotp
                                     fn2-pool-nslots))))
(defthm fn2-pool-stale-on-release
  (implies (fn2-pool-stale-hyps :release a p)
           (iff (fn2-pool-stale$owed :release a p)
                (and (equal (fn2-pool-credit-group (nth 0 a) p) *fn2-none*)
                     (fn2-pool-release-countp (nth 0 a) p))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn2-pool-owed-ops fn2-pool-stale$owed
                                   fn2-pool-logical-slotp fn2-pool-nslots)
                                  (fn2-pool-owed-release-admitted)))))
; Counterexample 1, evaluated: (hyps semanticp release-countp code).
(local
 (defun fn2-pool-owed-stale-witness ()
   (declare (xargs :verify-guards nil))
   (with-local-stobj fn2-pool
     (mv-let (r fn2-pool)
       (let* ((fn2-pool (fn2-pool-init '((1 . 4)) 0 5 fn2-pool))
              (fn2-pool (fn2-pool-set-credit-group 0 0 fn2-pool))
              (hyps (fn2-pool-stale-hyps :release '(0 7 0 0 0) fn2-pool))
              (semantic (fn2-pool-semanticp fn2-pool))
              (admitted (fn2-pool-release-countp 0 fn2-pool)))
         (mv-let (code fn2-pool) (fn2-pool-release 0 7 0 0 0 fn2-pool)
           (mv (list hyps semantic admitted code) fn2-pool)))
       r))))
(local (assert-event (equal (fn2-pool-owed-stale-witness) '(t t t :credit))))
