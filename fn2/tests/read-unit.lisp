; C-S4's first half (books/machines-c-read.lisp) over a store seeded through
; C-S3's own operations (owed-cursor.lisp's seeds: identity fact, article row,
; group-count accept and overview row, one published batch an article): the
; exact lookup of a read row (groups by name, group counts by group), range
; reads over a group's overview with and without a position limit, the
; positioned seek, staleness across the sealer (amendment (b)), and the
; refusals of a row out of range, a step with no read, a second owner.
(in-package "ACL2")
(include-book "../books/owed-cursor")
(include-book "std/util/bstar" :dir :system)

; Reading served with two read rows (two transactions: rows t + 2 and
; t + 18), three groups; the sealer's checker row (3 + one window, below
; :format-slots 5) and 64 KiB pages for its runs, which stay resident
; (C-SEAL-RESIDENT): owed-cursor.lisp's *fn2-read-profile*.
(defconst *fn2-rdu-profile* *fn2-read-profile*)
(defconst *fn2-rdu-seeds*
 '((1 "<a@example.invalid>" "first	a@example.invalid") (2 "<z@example.invalid>" "other group")
   (1 "<b@example.invalid>" "second") (1 "<c@example.invalid>" "third line")))
(defconst *fn2-rdu-max* 2147483647)

(defun fn2-rdu-chars (cs) (declare (xargs :verify-guards nil)) (if (atom cs) nil (cons (char-code (car cs)) (fn2-rdu-chars (cdr cs)))))
(defun fn2-rdu-codes (bs) (declare (xargs :verify-guards nil)) (if (atom bs) nil (cons (code-char (nfix (car bs))) (fn2-rdu-codes (cdr bs)))))
(defun fn2-rdu-string (bs) (declare (xargs :verify-guards nil)) (coerce (fn2-rdu-codes bs) 'string))
(defun fn2-rdu-bytes (slot gen i n fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix (- (nfix n) (nfix i)))))
 (if (not (and (natp i) (natp n) (< i n))) nil
  (mv-let (c b) (fn2-core-read slot gen i 200 0 1 fn2-core)
   (cons (if (eq c :ok) b c) (fn2-rdu-bytes slot gen (+ 1 i) n fn2-core)))))
(defun fn2-rdu-lookup-loop (fuel x sid fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (if (zp fuel) (mv :fuel fn2-core)
  (mv-let (code fn2-core) (fn2-read-lookup x sid 4096 fn2-core)
   (if (eq code :more) (fn2-rdu-lookup-loop (- fuel 1) x sid fn2-core) (mv code fn2-core)))))
; The group of NAME through read row X: (code group).
(defun fn2-rdu-group (x name fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((octets (fn2-rdu-chars (coerce name 'list)))
      ((mv & slot gen fn2-core) (fn2-cs-fill octets fn2-core))
      ((mv c fn2-core) (fn2-read-key-octets x 0 slot gen 0 (len octets) 200 0 1 fn2-core))
      ((unless (eq c :ok)) (mv (list :key c) fn2-core))
      ((mv c fn2-core) (fn2-rdu-lookup-loop 40 x *fn2-groups-sid* fn2-core))
      ((mv vc group) (fn2-read-value x *fn2-groups-entry-field-group* fn2-core))
      ((mv & fn2-core) (fn2-core-release slot gen 200 0 1 fn2-core))
      ((mv & fn2-core) (fn2-read-release x fn2-core)))
  (mv (if (eq c :ok) (list c vc group) (list c)) fn2-core)))
; Group G's counts through read row X: (code count low high).
(defun fn2-rdu-counts (x g fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* (((mv c fn2-core) (fn2-read-key x :lo 0 g fn2-core))
      ((unless (eq c :ok)) (mv (list :key c) fn2-core))
      ((mv c fn2-core) (fn2-rdu-lookup-loop 40 x *fn2-txn-counts-sid* fn2-core))
      ((mv & n) (fn2-read-value x *fn2-group-counts-entry-field-count* fn2-core))
      ((mv & lo) (fn2-read-value x *fn2-group-counts-entry-field-low* fn2-core))
      ((mv & hi) (fn2-read-value x *fn2-group-counts-entry-field-high* fn2-core))
      ((mv & fn2-core) (fn2-read-release x fn2-core)))
  (mv (if (eq c :ok) (list c n lo hi) (list c)) fn2-core)))
; The delivered overview entry as (number position line), the line copied
; into SLOT in two pieces (the first at most 4 octets: a row rendered in
; pieces, the second over the first's tail).
(defun fn2-rdu-entry (x slot gen fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* (((mv & n) (fn2-read-value x *fn2-overview-entry-field-number* fn2-core))
      ((mv & p) (fn2-read-value x *fn2-overview-entry-field-position* fn2-core))
      ((mv c1 k1 left1 fn2-core) (fn2-read-octets x *fn2-overview-entry-field-line* 0 4 slot gen 0 200 0 1 fn2-core))
      ((mv c2 k2 left2 fn2-core) (fn2-read-octets x *fn2-overview-entry-field-line* k1 4096 slot gen k1 200 0 1 fn2-core))
      (line (fn2-rdu-bytes slot gen 0 (+ k1 k2) fn2-core)))
  (mv (if (and (eq c1 :ok) (eq c2 :ok) (equal left1 k2) (equal left2 0))
          (list n p (fn2-rdu-string line))
        (list :octets c1 c2 k1 k2 left1 left2))
      fn2-core)))
; Step read row X's range to its end, the sealer run to idle after AFTER
; deliveries (when a number): (entries-or-refusal stale-code).
(defun fn2-rdu-seal (fuel fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (if (zp fuel) (mv :fuel fn2-core)
  (mv-let (code fn2-core) (fn2-sealer-step 4096 fn2-core)
   (if (member-eq code '(:more :retired :done)) (fn2-rdu-seal (- fuel 1) fn2-core) (mv code fn2-core)))))
(defun fn2-rdu-walk (fuel x after slot gen acc stale fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (if (zp fuel) (mv (list :fuel (reverse acc)) stale fn2-core)
  (b* (((mv code fn2-core) (fn2-read-next x 512 fn2-core)))
   (case code
    (:more (fn2-rdu-walk (- fuel 1) x after slot gen acc stale fn2-core))
    (:end (mv (reverse acc) stale fn2-core))
    (:entry
     (b* (((mv e fn2-core) (fn2-rdu-entry x slot gen fn2-core))
          (acc (cons e acc))
          ((unless (equal (len acc) after)) (fn2-rdu-walk (- fuel 1) x after slot gen acc stale fn2-core))
          ((mv sc fn2-core) (fn2-rdu-seal 4000 fn2-core))
          ((mv vc &) (fn2-read-value x *fn2-overview-entry-field-number* fn2-core))
          ((mv oc & & fn2-core) (fn2-read-octets x *fn2-overview-entry-field-line* 0 8 slot gen 0 200 0 1 fn2-core)))
      (fn2-rdu-walk (- fuel 1) x after slot gen acc (list sc vc oc) fn2-core)))
    (otherwise (mv (list code (reverse acc)) stale fn2-core))))))
; Range over group G's overview, numbers LO..HI, position limit PLIMIT
; (nil: none), through read row X.
(defun fn2-rdu-range (x g lo hi plimit after fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* (((mv & slot gen fn2-core) (fn2-core-reserve 0 200 0 1 fn2-core))
      ((mv c fn2-core)
       (fn2-cs-chain (fn2-read-key x :lo 0 g fn2-core) (fn2-read-key x :lo 1 lo fn2-core)
                     (fn2-read-key x :hi 0 g fn2-core) (fn2-read-key x :hi 1 hi fn2-core)
                     (fn2-read-range x *fn2-cursor-overview-sid*
                                     (if plimit *fn2-overview-entry-field-position* *fn2-range-no-position*)
                                     (nfix plimit) fn2-core)))
      ((unless (eq c :ok)) (mv (list :start c) nil fn2-core))
      ((mv es stale fn2-core) (fn2-rdu-walk 200 x after slot gen nil nil fn2-core))
      ((mv & fn2-core) (fn2-core-release slot gen 200 0 1 fn2-core))
      ((mv & fn2-core) (fn2-read-release x fn2-core)))
  (mv es stale fn2-core)))
(defun fn2-rdu-seek-loop (fuel x fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (if (zp fuel) (mv :fuel 0 fn2-core)
  (mv-let (code answer fn2-core) (fn2-read-seek-step x 4096 fn2-core)
   (if (eq code :more) (fn2-rdu-seek-loop (- fuel 1) x fn2-core) (mv code (list answer (- 100000 fuel)) fn2-core)))))
; The positioned seek over group G's overview after position P: (code n).
(defun fn2-rdu-seek (x g p fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* (((mv c fn2-core)
       (fn2-cs-chain (fn2-read-key x :lo 0 g fn2-core) (fn2-read-key x :hi 0 g fn2-core)
                     (fn2-read-seek x *fn2-cursor-overview-sid* 1 (+ 1 *fn2-rdu-max*) p *fn2-overview-entry-field-position*
                                    fn2-core)))
      ((unless (eq c :ok)) (mv (list :start c) fn2-core))
      ((mv c n fn2-core) (fn2-rdu-seek-loop 100000 x fn2-core))
      ((mv & fn2-core) (fn2-read-release x fn2-core)))
  (mv (if (consp n) (list c (car n) (cadr n)) (list c n)) fn2-core)))
;; (code answer) of each seek; the steps it took are printed beside.
(defun fn2-rdu-answers (seeks)
 (declare (xargs :verify-guards nil))
 (if (atom seeks) nil (cons (list (car (car seeks)) (cadr (car seeks))) (fn2-rdu-answers (cdr seeks)))))
(defun fn2-rdu-overview-runs (r k fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix k)))
 (if (zp k) 0
  (+ (stobj-let ((fn2-run-installed (fn2-core-run-installed fn2-core)))
      (v) (if (and (< (nfix r) (fn2-run-installed-rows fn2-run-installed))
                   (equal (fn2-run-installed-state r fn2-run-installed) *fn2-run-installed-state-live*)
                   (equal (fn2-run-installed-schema r fn2-run-installed) *fn2-cursor-overview-sid*))
              1 0)
      v)
     (fn2-rdu-overview-runs (+ 1 (nfix r)) (- k 1) fn2-core))))
; Refusals: a row past the profile's, a step with no read, a seek step with
; no seek, an octet key under a second owner.
(defun fn2-rdu-refusals (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* (((mv c1 fn2-core) (fn2-read-key 2 :lo 0 1 fn2-core))
      ((mv c2 fn2-core) (fn2-read-next 0 512 fn2-core))
      ((mv c3 & fn2-core) (fn2-read-seek-step 1 512 fn2-core))
      ((mv c4 fn2-core) (fn2-read-key-octets 1 0 0 1 0 4 200 0 1 fn2-core))
      ((mv c5 fn2-core) (fn2-read-key-octets 1 1 0 1 0 4 201 0 1 fn2-core))
      ((mv c6 &) (fn2-read-value 1 0 fn2-core))
      ((mv c7 fn2-core) (fn2-read-range 0 *fn2-groups-sid* *fn2-range-no-position* 0 fn2-core))
      ((mv & fn2-core) (fn2-read-release 1 fn2-core)))
  (mv (list c1 c2 c3 c4 c5 c6 c7) fn2-core)))

;; C-S4 (d): a whole-schema scan through read row X, its resume key in a
;; workspace of its own; the sealer run to idle after AFTER deliveries.
;; FIELDS picks what each entry yields: :groups (name group), :overview
;; (group number).
(defun fn2-rdu-scan-walk (fuel x what after slot gen acc fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (if (zp fuel) (mv (list :fuel (reverse acc)) fn2-core)
  (b* (((mv code fn2-core) (fn2-read-scan-next x 512 fn2-core)))
   (case code
    (:more (fn2-rdu-scan-walk (- fuel 1) x what after slot gen acc fn2-core))
    (:end (mv (reverse acc) fn2-core))
    (:entry
     (b* (((mv e fn2-core)
           (if (eq what :groups)
               (b* (((mv & g) (fn2-read-value x *fn2-groups-entry-field-group* fn2-core))
                    ((mv c k left fn2-core) (fn2-read-octets x *fn2-groups-entry-field-name* 0 4096 slot gen 0 200 0 1 fn2-core)))
                (mv (if (and (eq c :ok) (equal left 0)) (list (fn2-rdu-string (fn2-rdu-bytes slot gen 0 k fn2-core)) g) (list :octets c))
                    fn2-core))
             (b* (((mv & g) (fn2-read-value x *fn2-overview-entry-field-group* fn2-core))
                  ((mv & n) (fn2-read-value x *fn2-overview-entry-field-number* fn2-core)))
              (mv (list g n) fn2-core))))
          (acc (cons e acc))
          ((mv & fn2-core) (if (equal (len acc) after) (fn2-rdu-seal 4000 fn2-core) (mv :no fn2-core))))
      (fn2-rdu-scan-walk (- fuel 1) x what after slot gen acc fn2-core)))
    (otherwise (mv (list code (reverse acc)) fn2-core))))))
(defun fn2-rdu-scan (x sid what after fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* (((mv & wslot wgen fn2-core) (fn2-core-reserve 0 200 0 1 fn2-core))
      ((mv & slot gen fn2-core) (fn2-core-reserve 0 200 0 1 fn2-core))
      ((mv c fn2-core) (fn2-read-scan x sid wslot wgen 200 0 1 fn2-core))
      ((unless (eq c :ok)) (mv (list :start c) fn2-core))
      ((mv es fn2-core) (fn2-rdu-scan-walk 200 x what after slot gen nil fn2-core))
      ((mv & fn2-core) (fn2-core-release slot gen 200 0 1 fn2-core))
      ((mv & fn2-core) (fn2-core-release wslot wgen 200 0 1 fn2-core))
      ((mv & fn2-core) (fn2-read-release x fn2-core)))
  (mv es fn2-core)))
;; C-S4 (e): the identity read of MID through read row X: (code [article] candidates).

(defun fn2-rdu-identity (x mid fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((octets (fn2-rdu-chars (coerce mid 'list)))
      ((mv & slot gen fn2-core) (fn2-cs-fill octets fn2-core))
      ((mv code article candidates fn2-core) (fn2-ri-loop 400 x slot gen (len octets) fn2-core))
      ((mv & fn2-core) (fn2-core-release slot gen 200 0 1 fn2-core))
      ((mv & fn2-core) (fn2-read-release x fn2-core)))
  (mv (if (eq code :found) (list code article candidates) (list code candidates)) fn2-core)))
(defun fn2-rdu-run (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((fn2-core (fn2-init-executor *fn2-rdu-profile* :null nil fn2-core))
      (rows (list (stobj-let ((fn2-reads (fn2-core-reads fn2-core))) (n) (fn2-reads-rows fn2-reads) n)
                  (stobj-let ((fn2-succ-txns (fn2-core-succ-txns fn2-core))) (n) (fn2-succ-txns-rows fn2-succ-txns) n)
                  (stobj-let ((fn2-run-cursors (fn2-core-run-cursors fn2-core))) (n) (fn2-run-cursors-rows fn2-run-cursors) n)))
      ((mv seeded fn2-core) (fn2-cs-seed-all *fn2-rdu-seeds* 1 fn2-core))
      ((mv g1 fn2-core) (fn2-rdu-group 0 "local.test" fn2-core))
      ((mv g2 fn2-core) (fn2-rdu-group 1 "local.empty" fn2-core))
      ((mv g3 fn2-core) (fn2-rdu-group 0 "local.tests" fn2-core))
      ((mv n1 fn2-core) (fn2-rdu-counts 1 1 fn2-core))
      ((mv n2 fn2-core) (fn2-rdu-counts 0 2 fn2-core))
      ((mv n3 fn2-core) (fn2-rdu-counts 0 3 fn2-core))
      ((mv all & fn2-core) (fn2-rdu-range 0 1 1 *fn2-rdu-max* nil nil fn2-core))
      ((mv lim & fn2-core) (fn2-rdu-range 1 1 1 *fn2-rdu-max* 3 nil fn2-core))
      ((mv mid & fn2-core) (fn2-rdu-range 0 1 2 2 nil nil fn2-core))
      ((mv other & fn2-core) (fn2-rdu-range 1 2 1 *fn2-rdu-max* nil nil fn2-core))
      ((mv s0 fn2-core) (fn2-rdu-seek 0 1 0 fn2-core))
      ((mv s1 fn2-core) (fn2-rdu-seek 1 1 2 fn2-core))
      ((mv s2 fn2-core) (fn2-rdu-seek 0 1 3 fn2-core))
      ((mv s3 fn2-core) (fn2-rdu-seek 0 1 9 fn2-core))
      (runs-before (fn2-rdu-overview-runs 0 64 fn2-core))
      ((mv sealed stale fn2-core) (fn2-rdu-range 0 1 1 *fn2-rdu-max* nil 1 fn2-core))
      (runs-after (fn2-rdu-overview-runs 0 64 fn2-core))
      ((mv after-seal & fn2-core) (fn2-rdu-range 1 1 1 *fn2-rdu-max* nil nil fn2-core))
      ((mv g4 fn2-core) (fn2-rdu-group 1 "local.test" fn2-core))
      ((mv scan1 fn2-core) (fn2-rdu-scan 1 *fn2-groups-sid* :groups nil fn2-core))
      ((mv id4 fn2-core) (fn2-rdu-identity 0 "<a@example.invalid>" fn2-core))
      ((mv n4 fn2-core) (fn2-rdu-counts 0 1 fn2-core))
      ((mv s4 fn2-core) (fn2-rdu-seek 1 1 3 fn2-core))
      ((mv scan0 fn2-core) (fn2-rdu-scan 0 *fn2-groups-sid* :groups nil fn2-core))
      ((mv scanov fn2-core) (fn2-rdu-scan 1 *fn2-cursor-overview-sid* :overview nil fn2-core))
      ((mv id0 fn2-core) (fn2-rdu-identity 0 "<a@example.invalid>" fn2-core))
      ((mv id1 fn2-core) (fn2-rdu-identity 1 "<c@example.invalid>" fn2-core))
      ((mv id2 fn2-core) (fn2-rdu-identity 0 "<nobody@example.invalid>" fn2-core))
      ((mv conflict fn2-core) (fn2-cs-conflict "<a@example.invalid>" 0 5 fn2-core))
      ((mv id3 fn2-core) (fn2-rdu-identity 1 "<a@example.invalid>" fn2-core))
      ((mv refused fn2-core) (fn2-rdu-refusals fn2-core)))
  (mv (list :rows rows :seeded seeded :groups (list g1 g2 g3) :counts (list n1 n2 n3) :all all :limit lim :mid mid
            :other other :seeks (list s0 s1 s2 s3) :runs (list runs-before runs-after) :sealed sealed :stale stale
            :after-seal after-seal :after (list g4 n4 s4) :refused refused
            :scans (list scan0 scanov scan1) :identity (list id0 id1 id2 conflict id3 id4)
            :stop (fn2-core-stop-reason fn2-core))
      fn2-core)))
;; A second instance with no seeds: the group directory's genesis overlay
;; sealed into a run between the first and second entries of a LIST scan,
;; then a seed's overlays sealed between the second and third of an
;; overview scan; then the identity read of a seeded Message-ID before the
;; seal and of it again after.
(defun fn2-rdu-run2 (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((fn2-core (fn2-init-executor *fn2-rdu-profile* :null nil fn2-core))
      ((mv f0code f0) (fn2-read-frontier fn2-core))
      ((mv groups fn2-core) (fn2-rdu-scan 0 *fn2-groups-sid* :groups 1 fn2-core))
      ((mv seeded fn2-core) (fn2-cs-seed-all *fn2-rdu-seeds* 1 fn2-core))
      ((mv f1code f1) (fn2-read-frontier fn2-core))
      ((mv id0 fn2-core) (fn2-rdu-identity 1 "<b@example.invalid>" fn2-core))
      ((mv over fn2-core) (fn2-rdu-scan 1 *fn2-cursor-overview-sid* :overview 2 fn2-core))
      ((mv id1 fn2-core) (fn2-rdu-identity 0 "<b@example.invalid>" fn2-core)))
  (mv (list :groups groups :seeded seeded :overview over :identity (list id0 id1)
            :frontier (list f0code f0 f1code f1) :stop (fn2-core-stop-reason fn2-core))
      fn2-core)))
(defun fn2-rdu-result2 ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core (mv-let (r fn2-core) (fn2-rdu-run2 fn2-core) r)))
(make-event (value `(defconst *fn2-rdu-result2* ',(fn2-rdu-result2))))
(value-triple (cw "READ-UNIT-2 ~x0~%" *fn2-rdu-result2*))
;; The frontier (C-S4 (c)): served before any batch, and strictly past it
;; once the seeds' batches are published.
(assert-event (let ((f (cadr (member :frontier *fn2-rdu-result2*))))
                (and (eq (nth 0 f) :ok) (eq (nth 2 f) :ok) (natp (nth 1 f)) (natp (nth 3 f))
                     (< (nth 1 f) (nth 3 f)))))

(defun fn2-rdu-result ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core (mv-let (r fn2-core) (fn2-rdu-run fn2-core) r)))
(make-event (value `(defconst *fn2-rdu-result* ',(fn2-rdu-result))))
(value-triple (cw "READ-UNIT ~x0~%" *fn2-rdu-result*))

(defconst *fn2-rdu-three*
 '((1 1 "first	a@example.invalid") (2 3 "second") (3 4 "third line")))
(assert-event (equal (cadr (member :rows *fn2-rdu-result*)) (list 2 (+ 2 2) (+ 2 (* 9 2)))))
(assert-event (equal (cadr (member :seeded *fn2-rdu-result*)) :ok))
(assert-event (equal (cadr (member :groups *fn2-rdu-result*)) '((:ok :ok 1) (:ok :ok 2) (:absent))))
(assert-event (equal (cadr (member :counts *fn2-rdu-result*)) '((:ok 3 1 3) (:ok 1 1 1) (:absent))))
;; Every entry of group 1, never group 2's: the range reads stored keys only
;; (three deliveries over numbers 1..2^31-1).
(assert-event (equal (cadr (member :all *fn2-rdu-result*)) *fn2-rdu-three*))
;; The position limit stops at the first entry past it (position 4 > 3).
(assert-event (equal (cadr (member :limit *fn2-rdu-result*)) (take 2 *fn2-rdu-three*)))
(assert-event (equal (cadr (member :mid *fn2-rdu-result*)) (list (nth 1 *fn2-rdu-three*))))
(assert-event (equal (cadr (member :other *fn2-rdu-result*)) '((1 2 "other group"))))
;; The least number from which every entry is newer than P.
;; (C-POSITION-SEEK bisects [1, 2^31): 31 probes, 93 steps over overlays and
;; 431 over the four runs the sealer makes of them; a cursor bounds hi by the
;; group's high.)
(assert-event (equal (fn2-rdu-answers (cadr (member :seeks *fn2-rdu-result*))) '((:done 1) (:done 2) (:done 3) (:done 4))))
;; Amendment (b): the sealer moved every published overlay (group 1's
;; overview among them, one run each) into runs between two steps of a read;
;; the read went on from its resume key and delivered exactly the same
;; entries, and the entry held across the seal answers :stale to both its
;; value and its octets.
(assert-event (equal (cadr (member :runs *fn2-rdu-result*)) '(0 4)))
(assert-event (equal (cadr (member :sealed *fn2-rdu-result*)) *fn2-rdu-three*))
(assert-event (equal (cadr (member :stale *fn2-rdu-result*)) '(:idle :stale :stale)))
(assert-event (equal (cadr (member :after-seal *fn2-rdu-result*)) *fn2-rdu-three*))
(assert-event (equal (take 2 (cadr (member :after *fn2-rdu-result*))) '((:ok :ok 1) (:ok 3 1 3))))
(assert-event (equal (fn2-rdu-answers (cddr (cadr (member :after *fn2-rdu-result*)))) '((:done 3))))
(assert-event (equal (cadr (member :refused *fn2-rdu-result*)) '(:bounds :state :state :ok :owner :state :key-kind)))
(assert-event (equal (cadr (member :stop *fn2-rdu-result*)) 0))
;; C-S4 (d): LIST's scan delivers every group once in name order, over
;; the genesis overlay and over its run; the overview scan every entry in
;; (group, number) order, across groups.
(assert-event (equal (car (cadr (member :scans *fn2-rdu-result*)))
                     '(("alt.misc" 3) ("local.empty" 2) ("local.test" 1))))
(assert-event (equal (cadr (cadr (member :scans *fn2-rdu-result*))) '((1 1) (1 2) (1 3) (2 1))))
(assert-event (equal (caddr (cadr (member :scans *fn2-rdu-result*)))
                     '(("alt.misc" 3) ("local.empty" 2) ("local.test" 1))))
;; ...and across the sealer moving its source between two steps: the
;; groups overlay into a run after the first name, the seeds' overlays after
;; the second overview entry; each key once, none lost.
(assert-event (equal (cadr (member :groups *fn2-rdu-result2*)) '(("alt.misc" 3) ("local.empty" 2) ("local.test" 1))))
(assert-event (equal (cadr (member :seeded *fn2-rdu-result2*)) :ok))
(assert-event (equal (cadr (member :overview *fn2-rdu-result2*)) '((1 1) (1 2) (1 3) (2 1))))
(assert-event (equal (cadr (member :identity *fn2-rdu-result2*)) '((:found 3 0) (:found 3 0))))
(assert-event (equal (cadr (member :stop *fn2-rdu-result2*)) 0))
;; C-S4 (e): the identity read's selection (the article is the seed's
;; commit position) and its candidates; conflict evidence of content 0 sorts
;; before the accepted content and is counted, never selected.
(assert-event (equal (cadr (member :identity *fn2-rdu-result*))
                     '((:found 1 0) (:found 4 0) (:absent 0) :ok (:found 1 1) (:found 1 0))))

;; The owed row's teeth (owed-cursor.lisp fn2-read-identity-typed-exact).
;; Positive: the served selection and candidates are the reference's, with
;; and without conflict evidence, and for an absent name; the other three
;; fields are not served yet. Negative: the reference tells a store with
;; conflict evidence from one without (the candidates), and an absent name
;; from a selected one.
(defconst *fn2-rdu-tooth-seeds* '((1 "<a@example.invalid>" "first") (1 "<b@example.invalid>" "second")))
(defun fn2-read-identity-test-selection ()
 (declare (xargs :verify-guards nil))
 (and (equal (take 2 (fn2-read-identity-typed *fn2-rdu-tooth-seeds* nil "<b@example.invalid>"))
             (take 2 (fn2-read-identity-spec *fn2-rdu-tooth-seeds* nil "<b@example.invalid>")))
      (equal (take 2 (fn2-read-identity-typed *fn2-rdu-tooth-seeds* '(("<a@example.invalid>" 0)) "<a@example.invalid>"))
             (take 2 (fn2-read-identity-spec *fn2-rdu-tooth-seeds* '(("<a@example.invalid>" 0)) "<a@example.invalid>")))
      (equal (take 2 (fn2-read-identity-typed *fn2-rdu-tooth-seeds* nil "<z@example.invalid>"))
             (take 2 (fn2-read-identity-spec *fn2-rdu-tooth-seeds* nil "<z@example.invalid>")))
      (equal (nthcdr 2 (fn2-read-identity-typed *fn2-rdu-tooth-seeds* nil "<b@example.invalid>"))
             '(:not-served :not-served :not-served))))
(defun fn2-read-identity-test-negative ()
 (declare (xargs :verify-guards nil))
 (and (not (equal (fn2-read-identity-spec *fn2-rdu-tooth-seeds* '(("<a@example.invalid>" 0)) "<a@example.invalid>")
                  (fn2-read-identity-spec *fn2-rdu-tooth-seeds* nil "<a@example.invalid>")))
      (not (equal (fn2-read-identity-spec *fn2-rdu-tooth-seeds* nil "<z@example.invalid>")
                  (fn2-read-identity-spec *fn2-rdu-tooth-seeds* nil "<a@example.invalid>")))
      (not (equal (fn2-read-identity-typed *fn2-rdu-tooth-seeds* nil "<b@example.invalid>")
                  (fn2-read-identity-spec *fn2-rdu-tooth-seeds* nil "<b@example.invalid>")))))
(assert-event (fn2-read-identity-test-selection))
(assert-event (fn2-read-identity-test-negative))
(value-triple (cw "READ-UNIT PASS~%"))
