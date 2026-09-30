; Logical observation of the native executor's fixed 16384 accessor copy.
; This is not a new served codec, native scratch allocation or I/O authority.
(in-package "ACL2")
(include-book "history-image-canonical-payload")
(include-book "history-image-private-trace")

(defun fn-hpicopy-page (i c effect stage ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
 (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
  :verify-guards nil :measure (nfix (- 16384 (nfix i)))
  :hints (("Goal" :in-theory (disable fn-hie-page-byte)))))
 (if (>= (nfix i) 16384) (mv :complete nil)
  (mv-let (word byte)
   (fn-hie-page-byte c effect stage ledger (nfix i) fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
   (if (not (eq word :octet)) (mv :refused nil)
    (mv-let (status bytes)
     (fn-hpicopy-page (+ 1 (nfix i)) c effect stage ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
     (if (eq status :complete) (mv :complete (cons byte bytes)) (mv status nil)))))))

(local (defthm fn-hpicopy-word-octet-length
 (equal (len (pgs-word-le-octets w)) 8)
 :hints (("Goal" :in-theory (enable pgs-word-le-octets)))))
(local (defthm fn-hpicopy-octet-length
 (equal (len (pgs-words-le-octets ws)) (* 8 (len ws)))
 :hints (("Goal" :induct (pgs-words-le-octets ws)
  :in-theory (e/d (pgs-words-le-octets) (pgs-word-le-octets pgs-words-le-octets-loop))))))
(local (defthm fn-hpicopy-octet-list
 (true-listp (pgs-words-le-octets ws))
 :hints (("Goal" :induct (pgs-words-le-octets ws)
  :in-theory (e/d (pgs-words-le-octets pgs-word-le-octets) (pgs-words-le-octets-loop))))))
(local (defthm fn-hpicopy-prefix-length
 (implies (natp k) (equal (len (fn-hpb-prefix-aux i k fn-hpb)) k))
 :hints (("Goal" :induct (fn-hpb-prefix-aux i k fn-hpb)
  :in-theory (e/d (fn-hpb-prefix-aux) (fn-hpb-wi))))))
(local (defthm fn-hpicopy-full-prefix-length
 (implies (equal (fn-hpb-used fn-hpb) 2048) (equal (len (fn-hpb-prefix fn-hpb)) 2048))
 :hints (("Goal" :use ((:instance fn-hpicopy-prefix-length (i 0) (k 2048)))
  :in-theory (e/d (fn-hpb-prefix) (fn-hpb-prefix-aux fn-hpb-used))))))
(local (defthm fn-hpicopy-context-length
 (implies (fn-hpib-page-byte-contextp c effect stage ledger 0 fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
  (equal (len (pgs-words-le-octets
    (fn-hpib-selected-prefix (fn-omk-at 5 (fn-hie-plan c effect stage ledger))
      fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))) 16384))
 :hints (("Goal" :cases ((equal (fn-omk-at 5 (fn-hie-plan c effect stage ledger)) 0)
                       (equal (fn-omk-at 5 (fn-hie-plan c effect stage ledger)) 1)
                       (equal (fn-omk-at 5 (fn-hie-plan c effect stage ledger)) 2)
                       (equal (fn-omk-at 5 (fn-hie-plan c effect stage ledger)) 3))
  :in-theory (e/d (fn-hpib-page-byte-contextp fn-hpib-selected-prefix fn-hpi-region-used)
   (fn-hie-plan fn-omk-at fn-hpb-prefix fn-hpb-used pgs-words-le-octets))))))
(local (defthm fn-hpicopy-context-at-index
 (implies (and (fn-hpib-page-byte-contextp c effect stage ledger 0 fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
               (natp i) (< i 16384))
  (fn-hpib-page-byte-contextp c effect stage ledger i fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
 :hints (("Goal" :in-theory (e/d (fn-hpib-page-byte-contextp) (fn-hie-plan fn-omk-at fn-hpi-region-used))))))
(local (defthm fn-hpicopy-tail-step
 (implies (and (natp i) (< i (len xs)))
  (equal (nthcdr i xs) (cons (nth i xs) (nthcdr (+ 1 i) xs))))
 :rule-classes nil
 :hints (("Goal" :induct (nthcdr i xs) :in-theory (enable nthcdr nth)))))
(local (defthm fn-hpicopy-tail-at-end
 (implies (and (true-listp xs) (natp i) (equal i (len xs))) (equal (nthcdr i xs) nil))
 :hints (("Goal" :induct (nthcdr i xs) :in-theory (enable nthcdr)))))

(local (defthm fn-hpicopy-current-byte
 (implies (and (fn-hpib-page-byte-contextp c effect stage ledger 0 fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
               (natp i) (< i 16384))
  (equal (fn-hie-page-byte c effect stage ledger i fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
   (mv :octet (nth i (pgs-words-le-octets
    (fn-hpib-selected-prefix (fn-omk-at 5 (fn-hie-plan c effect stage ledger))
     fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))))))
 :hints (("Goal" :use (fn-hie-page-byte-refines-retained-page-serialization)
  :in-theory (disable fn-hie-page-byte fn-hpib-page-byte-contextp fn-hpib-selected-prefix fn-hie-plan fn-omk-at pgs-words-le-octets nth)))))

(local (defthm fn-hpicopy-page-refines-complete-native-accessor-loop
 (implies (and (fn-hpib-page-byte-contextp c effect stage ledger 0 fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
               (natp i) (<= i 16384))
  (equal (fn-hpicopy-page i c effect stage ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
   (mv :complete (nthcdr i (pgs-words-le-octets
     (fn-hpib-selected-prefix (fn-omk-at 5 (fn-hie-plan c effect stage ledger))
       fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))))))
 :rule-classes nil
 :hints (("Goal" :induct (fn-hpicopy-page i c effect stage ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
  :expand ((fn-hpicopy-page i c effect stage ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
  :in-theory (disable (:definition fn-hpicopy-page) fn-hie-page-byte fn-hpib-page-byte-contextp fn-hpib-selected-prefix fn-hie-plan fn-omk-at
    pgs-words-le-octets fn-hpicopy-octet-length nth nthcdr))
  ("Subgoal *1/3" :use ((:instance fn-hpicopy-tail-step
   (xs (pgs-words-le-octets (fn-hpib-selected-prefix (fn-omk-at 5 (fn-hie-plan c effect stage ledger))
    fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))))))
  ("Subgoal *1/2" :use ((:instance fn-hpicopy-tail-step
   (xs (pgs-words-le-octets (fn-hpib-selected-prefix (fn-omk-at 5 (fn-hie-plan c effect stage ledger))
    fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))))))))
)

(local (defthm fn-hpicopy-take-length
 (equal (len (take n xs)) (nfix n))
 :hints (("Goal" :induct (take n xs) :in-theory (enable take)))))
(local (defthm fn-hpicopy-take-list
 (true-listp (take n xs))
 :hints (("Goal" :induct (take n xs) :in-theory (enable take)))))
(local (defthm fn-hpicopy-canonical-current-byte
 (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-hpiz-writer-ready-p h c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) (fn-hpib-page-byte-contextp (mv-nth 2 r) (mv-nth 1 r) stage (mv-nth 3 r) 0 (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r) (mv-nth 7 r) (mv-nth 8 r)) (natp i) (< i 16384))
   (equal (fn-hie-page-byte (mv-nth 2 r) (mv-nth 1 r) stage (mv-nth 3 r) i (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r) (mv-nth 7 r) (mv-nth 8 r))
    (mv :octet (nth i (pgs-words-le-octets (take 2048 (nthcdr (* 2048 (nfix (fn-omk-at (fn-omk-at 18 c) (fn-omk-at 15 c)))) (fn-hp-wpad (nth (fn-omk-at 18 c) (fn-hp-regs h (fn-omk-at 12 c))))))))))))
 :hints (("Goal" :use (fn-hie-padding-page-byte-is-original-canonical-octet)
  :in-theory (disable fn-hpi-tick fn-hie-page-byte fn-hpib-page-byte-contextp fn-hpiz-writer-ready-p
   fn-hp-regs fn-hp-wpad fn-omk-at pgs-words-le-octets take nth nthcdr mv-nth)))))
(local (defun fn-hpicopy-index-ind (i)
 (declare (xargs :measure (nfix (- 16384 (nfix i)))))
 (if (>= (nfix i) 16384) i (fn-hpicopy-index-ind (+ 1 (nfix i))))))
(local (defthm fn-hpicopy-canonical-suffix
 (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-hpiz-writer-ready-p h c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) (fn-hpib-page-byte-contextp (mv-nth 2 r) (mv-nth 1 r) stage (mv-nth 3 r) 0 (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r) (mv-nth 7 r) (mv-nth 8 r)) (natp i) (<= i 16384))
   (equal (fn-hpicopy-page i (mv-nth 2 r) (mv-nth 1 r) stage (mv-nth 3 r) (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r) (mv-nth 7 r) (mv-nth 8 r)) (mv :complete (nthcdr i (pgs-words-le-octets (take 2048 (nthcdr (* 2048 (nfix (fn-omk-at (fn-omk-at 18 c) (fn-omk-at 15 c)))) (fn-hp-wpad (nth (fn-omk-at 18 c) (fn-hp-regs h (fn-omk-at 12 c))))))))))))
 :rule-classes nil
 :hints (("Goal" :induct (fn-hpicopy-index-ind i)
  :expand ((fn-hpicopy-page i (mv-nth 2 (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)) (mv-nth 1 (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)) stage (mv-nth 3 (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)) (mv-nth 4 (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)) (mv-nth 5 (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)) (mv-nth 6 (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)) (mv-nth 7 (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)) (mv-nth 8 (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))))
  :in-theory (disable (:definition fn-hpicopy-page) fn-hie-page-byte fn-hpi-tick
   fn-hpib-page-byte-contextp fn-hpiz-writer-ready-p fn-hp-regs fn-hp-wpad fn-omk-at
   pgs-words-le-octets fn-hpicopy-current-byte nfix nth nthcdr))
  ("Subgoal *1/3" :use ((:instance fn-hpicopy-tail-step (xs (pgs-words-le-octets (take 2048 (nthcdr (* 2048 (nfix (fn-omk-at (fn-omk-at 18 c) (fn-omk-at 15 c)))) (fn-hp-wpad (nth (fn-omk-at 18 c) (fn-hp-regs h (fn-omk-at 12 c)))))))))))
  ("Subgoal *1/2" :use ((:instance fn-hpicopy-tail-step (xs (pgs-words-le-octets (take 2048 (nthcdr (* 2048 (nfix (fn-omk-at (fn-omk-at 18 c) (fn-omk-at 15 c)))) (fn-hp-wpad (nth (fn-omk-at 18 c) (fn-hp-regs h (fn-omk-at 12 c))))))))))))))

(defthm fn-hpicopy-issued-padding-payload-is-original-canonical-page
 (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-hpiz-writer-ready-p h c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) (fn-hpib-page-byte-contextp (mv-nth 2 r) (mv-nth 1 r) stage (mv-nth 3 r) 0 (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r) (mv-nth 7 r) (mv-nth 8 r)))
   (equal (fn-hpicopy-page 0 (mv-nth 2 r) (mv-nth 1 r) stage (mv-nth 3 r) (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r) (mv-nth 7 r) (mv-nth 8 r)) (mv :complete (pgs-words-le-octets (take 2048 (nthcdr (* 2048 (nfix (fn-omk-at (fn-omk-at 18 c) (fn-omk-at 15 c)))) (fn-hp-wpad (nth (fn-omk-at 18 c) (fn-hp-regs h (fn-omk-at 12 c)))))))))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-hpicopy-canonical-suffix (i 0)))
  :in-theory (e/d (nthcdr) (fn-hpicopy-page fn-hpi-tick fn-hie-page-byte fn-hpib-page-byte-contextp
   fn-hpiz-writer-ready-p fn-hp-regs fn-hp-wpad fn-omk-at pgs-words-le-octets take mv-nth)))))

(local (defthm fn-hpicopy-private-step-offset-is-natural
 (implies (fn-hpit-private-write-step-p before (list after 0 offset payload got) files)
  (natp offset))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-assume-hpi-full-write-is-visible-byte-splice
  (file (nth 0 files)) (octets payload) (outcome :ok)))
  :in-theory (e/d (fn-hpit-private-write-step-p)
   (fn-bs-content fn-bs-splice))))))
(local (defthm fn-hpicopy-nonwrite-padding-has-no-effect
 (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-hpiz-writer-ready-p h c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) (not (equal (car r) :write))) (equal (mv-nth 1 r) nil)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-hpiz-writer-ready-p fn-hpi-tick fn-hpi-buffer-step fn-hpi-await-region fn-hpi-await-page)
   (fn-hpiz-region-invariantp fn-hpi-grant-matchesp fn-hpi-growth-request fn-hpi-supply fn-hpi-written
    fn-hpi-stream-step fn-hpcx-tick fn-hpcx-supply fn-hpi-region-used fn-hpi-region-cap fn-hpi-region-start
    fn-hpq-put fn-hpb-put fn-hpb-prefix fn-hpb-used fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at
    fn-hp-regs fn-hp-wpad fn-hpi-write-effect nfix nth nthcdr mv-nth fn-osj-native-grow))))))
(local (defthm fn-hpicopy-no-effect-has-no-natural-plan-offset
 (not (natp (fn-omk-at 3 (fn-hie-plan c nil stage ledger))))
 :hints (("Goal" :in-theory (e/d (fn-hie-plan fn-omk-at)
   (fn-hie-currentp fn-osj-native-slicep fn-hpi-octets-p))))))
(local
 (defun fn-hpicopy-struct-field-ind (j k c)
  (if (or (zp j) (zp k)) (list j k c)
    (fn-hpicopy-struct-field-ind (1- j) (1- k) (if (consp c) (cdr c) nil)))))
(local
 (defthm fn-hpicopy-struct-set-field
  (implies (and (natp k) (< k 25) (natp j) (< j 25))
   (equal (fn-omk-at j (fn-hpi-set k value c))
          (if (equal j k) value (fn-omk-at j c))))
  :hints (("Goal" :induct (fn-hpicopy-struct-field-ind j k c)
           :expand ((fn-hpi-set k value c)
                    (fn-omk-at j c)
                    (fn-omk-at j (fn-hpi-set k value c))
                    (:free (a d) (fn-omk-at j (cons a d))))
           :in-theory (e/d (fn-omk-at fn-hpi-set) (fn-hpi-set-is-update-by-definition))))))
(local (defthm fn-hpicopy-struct-at-cons-by-definition
 (equal (fn-omk-at j (cons a b)) (if (zp j) a (fn-omk-at (1- j) b)))
 :hints (("Goal" :in-theory (enable fn-omk-at)))))
(local (defthm fn-hpicopy-struct-issued-padding-selects-original-region
 (let ((a (fn-hpi-await-region region :pad c)))
  (implies (and (natp region) (< region 5) (equal (car a) :write))
   (and (equal (fn-omk-at 0 (mv-nth 1 a)) :write-page)
        (equal (fn-omk-at 0 (fn-omk-at 17 (mv-nth 2 a))) region))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-hpi-await-region fn-hpi-await-page fn-hpi-write-effect mv-nth)
   (fn-hpi-set fn-hpi-set-is-update-by-definition fn-omk-at fn-hpi-region-cap fn-hpi-region-start))))))
(local (defthm fn-hpicopy-struct-page-plan-selects-retained-buffer
 (implies (and (equal (fn-omk-at 0 effect) :write-page)
               (equal (fn-omk-at 0 (fn-hie-plan c effect stage ledger)) :io))
  (equal (fn-omk-at 5 (fn-hie-plan c effect stage ledger)) (fn-omk-at 0 (fn-omk-at 17 c))))
 :hints (("Goal" :in-theory (e/d (fn-hie-plan) (fn-hie-currentp fn-omk-at fn-osj-native-slicep))))))
(local (defthm fn-hpicopy-struct-ready-region-issuer-is-write
 (implies (fn-hpiz-writer-ready-p h c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
  (equal (car (fn-hpi-await-region (fn-omk-at 18 c) :pad c)) :write))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-hpiz-writer-ready-p fn-hpi-await-region fn-hpi-await-page)
   (nfix fn-hp-regs fn-omk-at fn-hpi-region-cap fn-hpiz-region-invariantp fn-hpi-set fn-hpi-set-is-update-by-definition fn-hpi-write-effect fn-hpi-region-start))))))
(local (defthm fn-hpicopy-struct-actual-padding-issued-region
 (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-hpiz-writer-ready-p h c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) (equal (car r) :write))
   (and (equal (fn-omk-at 0 (mv-nth 1 r)) :write-page)
        (equal (fn-omk-at 0 (fn-omk-at 17 (mv-nth 2 r))) (fn-omk-at 18 c))
        (equal (mv-nth 4 r) fn-hpq0) (equal (mv-nth 5 r) fn-hpq1)
        (equal (mv-nth 6 r) fn-hpq2) (equal (mv-nth 7 r) fn-hpq3) (equal (mv-nth 8 r) fn-hpb))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-hpi-padding-page-handoff-is-original-canonical-page fn-hpicopy-struct-ready-region-issuer-is-write
        (:instance fn-hpicopy-struct-issued-padding-selects-original-region (region (fn-omk-at 18 c))))
  :in-theory (e/d (fn-hpiz-writer-ready-p)
   (nfix fn-hp-regs fn-hpi-tick fn-hpi-await-region fn-hpiz-region-invariantp fn-omk-at fn-hpi-set fn-hpi-set-is-update-by-definition mv-nth))))))
(local (defthm fn-hpicopy-private-step-implies-padding-write
 (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-hpiz-writer-ready-p h c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) (fn-hpit-private-write-step-p before (list after 0 (fn-omk-at 3 (fn-hie-plan (mv-nth 2 r) (mv-nth 1 r) stage (mv-nth 3 r))) (mv-nth 1 (fn-hpicopy-page 0 (mv-nth 2 r) (mv-nth 1 r) stage (mv-nth 3 r) (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r) (mv-nth 7 r) (mv-nth 8 r))) got) files)) (equal (car r) :write)))
 :rule-classes nil
 :hints (("Goal" :use (fn-hpicopy-nonwrite-padding-has-no-effect
  (:instance fn-hpicopy-private-step-offset-is-natural
   (offset (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))) (fn-omk-at 3 (fn-hie-plan (mv-nth 2 r) (mv-nth 1 r) stage (mv-nth 3 r)))))
   (payload (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))) (mv-nth 1 (fn-hpicopy-page 0 (mv-nth 2 r) (mv-nth 1 r) stage (mv-nth 3 r) (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r) (mv-nth 7 r) (mv-nth 8 r)))))))
  :in-theory (disable fn-hpi-tick fn-hpit-private-write-step-p fn-hpicopy-page fn-hpiz-writer-ready-p
   fn-hie-plan fn-omk-at mv-nth)))))
(local (defthm fn-hpicopy-issued-write-context-from-private-step
 (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-hpiz-writer-ready-p h c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) (fn-hpit-private-write-step-p before (list after 0 (fn-omk-at 3 (fn-hie-plan (mv-nth 2 r) (mv-nth 1 r) stage (mv-nth 3 r))) (mv-nth 1 (fn-hpicopy-page 0 (mv-nth 2 r) (mv-nth 1 r) stage (mv-nth 3 r) (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r) (mv-nth 7 r) (mv-nth 8 r))) got) files)) (fn-hpib-page-byte-contextp (mv-nth 2 r) (mv-nth 1 r) stage (mv-nth 3 r) 0 (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r) (mv-nth 7 r) (mv-nth 8 r))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-hpicopy-private-step-implies-padding-write fn-hpi-padding-page-handoff-is-original-canonical-page
    fn-hpicopy-struct-actual-padding-issued-region
    (:instance fn-hpicopy-private-step-offset-is-natural
     (offset (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))) (fn-omk-at 3 (fn-hie-plan (mv-nth 2 r) (mv-nth 1 r) stage (mv-nth 3 r)))))
     (payload (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))) (mv-nth 1 (fn-hpicopy-page 0 (mv-nth 2 r) (mv-nth 1 r) stage (mv-nth 3 r) (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r) (mv-nth 7 r) (mv-nth 8 r)))))))
  :cases ((equal (fn-omk-at 18 c) 0) (equal (fn-omk-at 18 c) 1) (equal (fn-omk-at 18 c) 2)
          (equal (fn-omk-at 18 c) 3) (equal (fn-omk-at 18 c) 4))
  :in-theory (e/d (fn-hpiz-writer-ready-p fn-hpib-page-byte-contextp fn-hie-plan fn-hpi-region-used fn-hpq-model-select)
   (fn-hpit-private-write-step-p fn-hpicopy-page fn-hpi-tick fn-hpiz-region-invariantp fn-hie-currentp fn-osj-native-slicep
    fn-hpi-octets-p fn-hpi-set fn-omk-at fn-hp-regs fn-hp-wpad fn-hpb-used fn-hpb-prefix nfix nth nthcdr mv-nth))))))

; FILES is the actual held non-aliasing (target data-spool table-spool)
; identity triple. Its correspondence to native retained FDs remains explicit.
; The private-step predicate includes the named full write and all three
; other-role frame assumptions; native full counts never establish them.
(defthm fn-hpicopy-issued-padding-write-has-canonical-visible-roles
 (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  (implies (and (fn-hpiz-writer-ready-p h c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
    (fn-hpit-private-write-step-p before (list after 0 (fn-omk-at 3 (fn-hie-plan (mv-nth 2 r) (mv-nth 1 r) stage (mv-nth 3 r))) (mv-nth 1 (fn-hpicopy-page 0 (mv-nth 2 r) (mv-nth 1 r) stage (mv-nth 3 r) (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r) (mv-nth 7 r) (mv-nth 8 r))) got) files))
   (equal (fn-hpit-role-view after files)
    (fn-hpit-model-role-write (fn-hpit-role-view before files) (list after 0 (fn-omk-at 3 (fn-hie-plan (mv-nth 2 r) (mv-nth 1 r) stage (mv-nth 3 r))) (pgs-words-le-octets (take 2048 (nthcdr (* 2048 (nfix (fn-omk-at (fn-omk-at 18 c) (fn-omk-at 15 c)))) (fn-hp-wpad (nth (fn-omk-at 18 c) (fn-hp-regs h (fn-omk-at 12 c))))))) got)))))
 :rule-classes nil
 :hints (("Goal" :use (fn-hpicopy-issued-padding-payload-is-original-canonical-page fn-hpicopy-issued-write-context-from-private-step
   (:instance fn-hpit-private-write-updates-exactly-three-retained-roles
    (step (let ((r (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))) (list after 0 (fn-omk-at 3 (fn-hie-plan (mv-nth 2 r) (mv-nth 1 r) stage (mv-nth 3 r))) (mv-nth 1 (fn-hpicopy-page 0 (mv-nth 2 r) (mv-nth 1 r) stage (mv-nth 3 r) (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r) (mv-nth 7 r) (mv-nth 8 r))) got)))))
  :in-theory (disable fn-hpicopy-page fn-hpi-tick fn-hie-plan fn-omk-at fn-hp-regs fn-hp-wpad
   fn-hpiz-writer-ready-p fn-hpib-page-byte-contextp pgs-words-le-octets take nth nthcdr
   fn-hpit-private-write-step-p fn-hpit-role-view fn-hpit-model-role-write mv-nth))))
