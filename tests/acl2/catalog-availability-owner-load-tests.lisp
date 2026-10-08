; SCN-1092: real recovery loader fills missing availability from its arena.
; Program fixture setup; actual loader/readers are guard verified.
(in-package "ACL2")
(include-book "../../books/catalog-availability-refinement")
(include-book "catalog-available-readers-tests")

(defun cav-loader-prepare (i n survivors rows index fn-arena)
  (declare (xargs :mode :program :stobjs fn-arena))
  (if (>= i n) (mv (reverse rows) index fn-arena)
    (let* ((bytes (cav-bytes i (not (member-equal (+ 1 i) survivors))))
           (h (fn-held-with-facts (cav-row i nil) (fn-hf-make 0 nil 0 nil)))
           (index (fn-midx-put-chars (fn-midx-key-chars (fn-record-msgid h)) t index))
           (fn-arena (fn-arena-seal-list bytes fn-arena)))
      (cav-loader-prepare (+ 1 i) n survivors (cons h rows) index fn-arena))))

(defun cav-loader-run (survivors fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let ((fn-arena (fn-arena-clear fn-arena)))
    (mv-let (rows index fn-arena)
      (cav-loader-prepare 0 34 survivors nil nil fn-arena)
      (let* ((fn-cat (fn-sca-load-held-rows rows index fn-arena fn-cat))
             (before (cav-reader-observe 34 fn-cat))
             (fn-cat (fn-cat-withdraw 1 33 fn-cat))
             (after (cav-reader-observe 35 fn-cat)))
        (mv (list before after) fn-arena fn-cat)))))

(defun cav-loader-local (survivors)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (answer fn-arena)
      (with-local-stobj fn-cat
        (mv-let (answer fn-arena fn-cat)
          (cav-loader-run survivors fn-arena fn-cat) (mv answer fn-arena)))
      answer)))

(assert-event
 (equal (cav-loader-local '(1 34))
        '(((2 1 34) 1 (1 34) 34 1 0 0 35 1 (1))
          ((2 1 34) 1 (1 34) 34 1 0 0 35 1 (1)))))
(assert-event
 (equal (cav-loader-local '(33 34))
        '(((2 33 34) 33 (33 34) 33 33 0 0 35 1 (1))
          ((2 33 34) 33 (33 34) 33 33 0 0 35 1 (1)))))
(assert-event
 (equal (cav-loader-local '(1))
        '(((1 1 1) 1 (1) 0 1 0 0 35 1 (1))
          ((1 1 1) 1 (1) 0 1 0 0 35 1 (1)))))
(assert-event
 (equal (cav-loader-local nil)
        '(((0 35 34) 0 nil 0 0 0 0 35 1 (1))
          ((0 35 34) 0 nil 0 0 0 0 35 1 (1)))))

(defun cav-loader-invalid-local ()
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (answer fn-arena)
      (let* ((h (fn-held-with-facts (cav-row 0 nil) (fn-hf-make 0 nil 0 nil)))
             (prepared (fn-cat-prepare-row-availability h fn-arena)))
        (mv (and (equal prepared h)
                 (not (fn-cat-row-facts-decidedp prepared))
                 (not (fn-cat-row-availablep prepared))) fn-arena))
      answer)))
(assert-event (cav-loader-invalid-local))
(assert-event
 (and (eq (symbol-class 'fn-cat-prepare-row-availability (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-sca-load-held-rows (w state)) :common-lisp-compliant)))

; Literal producer theorem teeth over the immutable abstraction values.
; The live loader fixtures above execute the same entry and reader exports.
(defconst *cav-loader-legacy-h*
  (fn-held-with-facts (cav-row 0 nil) (fn-hf-make 0 nil 0 nil)))
(defconst *cav-loader-legacy-rows* (list *cav-loader-legacy-h*))
(defconst *cav-loader-legacy-arena* (list (cav-bytes 0 nil)))

(defthm cav-loader-decided-positive
  (and (fn-sca-held-rowsp *cav-loader-legacy-rows*)
       (fn-sca-load-availability-ready-p *cav-loader-legacy-rows* *cav-loader-legacy-arena*)
       (fn-cat-availability-decidedp
         (fn-sca-load-held-rows *cav-loader-legacy-rows* nil *cav-loader-legacy-arena* nil)))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (enable fn-sca-load-availability-ready-p fn-cat-availability-decidedp
                   fn-cat-rows-availability-decidedp))))

; Omit readiness: held row remains valid, missing handle stays undecided.
; No necessity of the held-rowsp premise is claimed.
(defthm cav-loader-decided-without-ready-corrupted-state
  (and (fn-sca-held-rowsp *cav-loader-legacy-rows*)
       (not (fn-sca-load-availability-ready-p *cav-loader-legacy-rows* nil))
       (not (fn-cat-availability-decidedp
         (fn-sca-load-held-rows *cav-loader-legacy-rows* nil nil nil))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (enable fn-sca-load-availability-ready-p fn-cat-availability-decidedp
                   fn-cat-rows-availability-decidedp))))

(defthm cav-loader-byte-facts-positive
  (and (fn-arena-p *cav-loader-legacy-arena*)
       (fn-scol-history-okp *cav-loader-legacy-rows* *cav-loader-legacy-arena*)
       (fn-scol-okp *cav-loader-legacy-arena*
         (fn-sca-load-held-rows *cav-loader-legacy-rows* nil *cav-loader-legacy-arena* nil)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-scol-okp fn-scol-history-okp fn-scol-row-okp))))

(defconst *cav-loader-stale-rows* (list (cav-row 0 nil)))
(defconst *cav-loader-tomb-arena* (list (cav-bytes 0 t)))
; Corrupted state: retained arena premise true, omitted byte-fact premise false,
; and decided stale facts remain stale. Loader must not silently claim repair.
(defthm cav-loader-byte-facts-without-history-corrupted-state
  (and (fn-arena-p *cav-loader-tomb-arena*)
       (not (fn-scol-history-okp *cav-loader-stale-rows* *cav-loader-tomb-arena*))
       (not (fn-scol-okp *cav-loader-tomb-arena*
         (fn-sca-load-held-rows *cav-loader-stale-rows* nil *cav-loader-tomb-arena* nil))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-scol-okp fn-scol-history-okp fn-scol-row-okp))))

(include-book "../../books/defkeystone")
; The snapshot checker is proved equal to the invariant on logical catalogs.
(defun p7-cat-rows (i fn-cat)
  (declare (xargs :stobjs fn-cat :verify-guards nil
                  :measure (nfix (- (fn-cat-count fn-cat) (nfix i)))))
  (if (and (natp i) (< i (fn-cat-count fn-cat)))
      (cons (fn-cat-at i fn-cat) (p7-cat-rows (+ 1 i) fn-cat))
    nil))
(defthm p7-nthcdr-at-end
  (implies (and (natp i) (<= (len xs) i))
    (equal (true-list-fix (nthcdr i xs)) nil))
  :hints (("Goal" :induct (nthcdr i xs) :in-theory (enable true-list-fix))))
(defthm p7-nthcdr-within
  (implies (and (natp i) (< i (len xs)))
    (equal (true-list-fix (nthcdr i xs))
           (cons (nth i xs) (true-list-fix (nthcdr (+ 1 i) xs)))))
  :hints (("Goal" :induct (nthcdr i xs) :in-theory (enable true-list-fix))))
(defthm p7-cat-rows-is-nthcdr
  (implies (natp i)
    (equal (p7-cat-rows i fn-cat) (true-list-fix (nthcdr i fn-cat))))
  :hints (("Goal" :induct (p7-cat-rows i fn-cat)
           :in-theory (e/d (fn-cat-count-is-len fn-cat-at-is-nth) (nthcdr true-list-fix)))))
(defthm p7-facts-of-list-fix
  (equal (fn-scol-rows-okp (true-list-fix rows) fn-arena)
         (fn-scol-rows-okp rows fn-arena))
  :hints (("Goal" :induct (true-list-fix rows) :in-theory (enable true-list-fix))))
(defun p7-loaded-facts-check (rows view-index fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (let* ((fn-cat (fn-sca-load-held-rows rows view-index fn-arena fn-cat))
         (ok (and (fn-arena-p fn-arena)
                  (fn-scol-rows-okp (p7-cat-rows 0 fn-cat) fn-arena))))
    (mv ok fn-arena fn-cat)))
(defthm p7-loaded-facts-check-refines
  (equal (mv-nth 0 (p7-loaded-facts-check rows view-index fn-arena fn-cat))
         (fn-scol-okp fn-arena (fn-sca-load-held-rows rows view-index fn-arena fn-cat)))
  :hints (("Goal" :in-theory (e/d (fn-scol-okp) (fn-sca-load-held-rows)))))

; Host recovery and fnn-owner-reclaim-pass: tests/test_native_reclaim_walk.py::
; test_a_pass_longer_than_two_chunks_installs_and_counts_the_available.
; Every witness starts with an empty local arena and seals its payloads.
(defteeth fn-sca-load-held-rows-establishes-byte-facts
  :claim (((arena (fn-arena-p fn-arena))
           (history (fn-scol-history-okp rows fn-arena)))
          (fn-scol-okp fn-arena (fn-sca-load-held-rows rows view-index fn-arena fn-cat)))
  :subject fn-sca-load-held-rows
  :witness ((rows *cav-loader-legacy-rows*) (view-index nil)
            (payloads *cav-loader-tomb-arena*))
  :stobjs ((fn-arena (fn-arn-seal-many payloads fn-arena))
           (fn-cat (fn-cat-clear fn-cat)))
  :stobj-checks
  (((fn-scol-okp fn-arena (fn-sca-load-held-rows rows view-index fn-arena fn-cat))
    (p7-loaded-facts-check rows view-index fn-arena fn-cat)
    :hints (("Goal" :use p7-loaded-facts-check-refines)))
   ((fn-scol-okp fn-arena
      (fn-sca-load-held-rows *cav-loader-stale-rows* view-index fn-arena fn-cat))
    (p7-loaded-facts-check *cav-loader-stale-rows* view-index fn-arena fn-cat)
    :hints (("Goal" :use ((:instance p7-loaded-facts-check-refines
                                    (rows *cav-loader-stale-rows*)))))))
  :breaks ((arena ((rows nil) (view-index nil) (payloads '((999))))
                  :logical "corrupted arena contains a value outside the octet domain")
           (history ((rows *cav-loader-stale-rows*) (view-index nil)
                     (payloads *cav-loader-tomb-arena*))))
  :mutations ((stale-byte-facts
               (:conclusion
                (fn-scol-okp fn-arena
                  (fn-sca-load-held-rows *cav-loader-stale-rows* view-index fn-arena fn-cat)))
               ((rows *cav-loader-legacy-rows*) (view-index nil)
                (payloads *cav-loader-tomb-arena*))
               :fault "the loader publishes old live-byte facts over a tombstone payload"))
  :hints (("Goal" :in-theory (enable fn-scol-okp fn-scol-history-okp))))
