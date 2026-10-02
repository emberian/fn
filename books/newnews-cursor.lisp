;; fn: NEWNEWS selected through a carried stamp index and replied in quanta
;; (audit-incremental-2026-10-02 R3).
;
; books/nntp-responses.lisp fn-nntp-newnews-scan walks the whole committed
; article list (newest first) for every NEWNEWS, never stopping at the date,
; reads a payload head (fn-nntp-article-tombstonep) per candidate, and
; fn-nntp-newnews-response materializes the whole reply in one step.  The
; scan has to be the reference's: an article's instant is its own stamp, or
; the nearest NEWER natural stamp, or the reader's clock (the horizon the
; scan carries); stamps are NOT assumed monotone (the clock may step back).
;
; 1. The index.  fn-nnw-maxes ARTS is the list, parallel to ARTS, of the
;    largest natural stamp of each suffix (fn-nnw-smax; 0 when none).  Every
;    instant the scan of a suffix T computes, with a natural horizon H, is at
;    most (max (smax T) H) (fn-nnw-scan-nil-past-bound), so once
;    1000 * (max (car maxes) H) is below the threshold the rest of the list
;    lists nothing and the walk stops.  With arrival-ordered stamps that is
;    right after the last new article: the walk visits the articles newer
;    than the date, plus one.
;    The carry is (ARTS . INDEX), an :exact view DECLARED through
;    books/def-carried-view.lisp (lane generators-2, the second pilot):
;    fn-nnw-carryp says INDEX is the fold (fn-nnw-maxes ARTS).
;    fn-nnw-refresh brings it to a list by walking to the tail EQUAL to the
;    carried list and folding the walked prefix oldest-first onto the
;    carried maxima (the view's article list grows by consing the new
;    article, books/control-visible.lisp fn-ctl-visible-add); else it
;    rebuilds.  It keeps fn-nnw-carryp, nil has it, and the walk steps
;    exactly the delta (fn-nnw-carryp-of-refresh, fn-nnw-carryp-of-nil,
;    fn-nnw-refresh-walks-the-delta; all generated).
; 2. The cursor (:newnews GROUPS THRESHOLD TAIL MAXES HORIZON): what the
;    reply still owes is (fn-nntp-newnews-scan GROUPS THRESHOLD TAIL HORIZON)
;    (fn-nnw-owes).  MAXES is (fn-nnw-maxes TAIL) or nil (no index: the
;    cursor walks to the end, still in quanta).  fn-nnw-step visits at most
;    (max 1 Q) articles (fn-nnw-step-lines-at-most-q) and always progresses
;    (fn-nnw-step-progresses); RESIDUAL: the lines it emits followed by what
;    the next cursor owes are what the cursor owed
;    (fn-nnw-step-residual), so a reply in quanta never truncates and never
;    repeats.  fn-nnw-run is the steps to the end.
; KEYSTONES:
;   fn-nnw-run-is-newnews-scan: for a cursor whose MAXES is nil or exact,
;     the run is the reference scan, for every quantum.
;   fn-nnw-response-is-newnews-response: under fn-nnw-carryp, the NEWNEWS
;     response with the run in the scan's place is
;     fn-nntp-newnews-response, byte for byte.
; The served subject: fn-nnw-response is called by nothing served yet.  Its
; host path (the -cat dispatcher's NEWNEWS arm emitting the cursor as a
; plan cursor effect, books/served-plan-cursor.lisp stepping it, the host
; refreshing the carry) waits for stage 0 and the dispatcher's owners
; (build/coordinator/lanedumps/served-incremental-4.md NEXT).

(in-package "ACL2")
(include-book "nntp-responses")
(include-book "def-carried-view")

(local (in-theory (disable (tau-system))))
(local (in-theory (enable fn-nntp-newnews-scan)))

; -----------------------------------------------------------------------------
; 1. The suffix maxima.

(defun fn-nnw-s (article)
  (declare (xargs :guard t))
  (let ((stamp (fn-article-stamp article)))
    (if (natp stamp) stamp 0)))

(defun fn-nnw-smax (arts)
  (declare (xargs :guard t))
  (if (consp arts)
      (max (fn-nnw-s (car arts)) (fn-nnw-smax (cdr arts)))
    0))

(defun fn-nnw-top (maxes)
  (declare (xargs :guard t))
  (if (consp maxes) (nfix (car maxes)) 0))

; The index: the suffix maxima, an :exact fold.  fn-nnw-maxes is the
; generated build (oldest-first, tail-recursive); fn-nnw-maxes-unfolds is
; its newest-first reading, a definition rule for the cursor's proofs.
(def-carried-view fn-nnw
  :key arts
  :indexes ((index :kind :exact
                   :put (lambda (e idx) (cons (max (fn-nnw-s e) (fn-nnw-top idx)) idx))
                   :empty nil))
  :build fn-nnw-maxes)

(local
 (defthm fn-nnw-smax-natp
   (natp (fn-nnw-smax arts))
   :rule-classes :type-prescription))

(local
 (defthm fn-nnw-top-of-build-onto
   (equal (fn-nnw-top (fn-nnw-build-onto zs nil)) (fn-nnw-smax zs))
   :hints (("Goal" :in-theory (enable fn-nnw-build-onto fn-nnw-put)))))

(defthm fn-nnw-maxes-unfolds
  (equal (fn-nnw-maxes arts)
         (if (consp arts)
             (cons (fn-nnw-smax arts) (fn-nnw-maxes (cdr arts)))
           nil))
  :rule-classes :definition
  :hints (("Goal" :in-theory (enable fn-nnw-maxes-is-build-onto fn-nnw-build-onto
                                     fn-nnw-put fn-nnw-empty))))

; -----------------------------------------------------------------------------
; 2. The bound: past it the scan lists nothing.

(local
 (defthm fn-nnw-stamp-at-most-smax
   (implies (and (consp arts) (natp (fn-article-stamp (car arts))))
            (<= (fn-article-stamp (car arts)) (fn-nnw-smax arts)))
   :rule-classes :linear))

(defthm fn-nnw-scan-nil-past-bound
  (implies (and (natp horizon) (natp b)
                (<= (fn-nnw-smax arts) b)
                (<= horizon b)
                (< (* 1000 b) threshold))
           (equal (fn-nntp-newnews-scan groups threshold arts horizon fn-arena) nil))
  :rule-classes nil
  :hints (("Goal" :induct (fn-nntp-newnews-scan groups threshold arts horizon fn-arena)
           :in-theory (e/d (fn-nntp-newnews-newp)
                           (fn-nntp-newnews-candidatep fn-nntp-article-tombstonep
                            fn-nntp-string-octets fn-article-msgid)))))

; -----------------------------------------------------------------------------
; 3. The carry: generated (fn-nnw-carryp, fn-nnw-refresh, fn-nnw-arts,
; fn-nnw-index and their keystones, section 1).

; -----------------------------------------------------------------------------
; 4. The cursor.

(defun fn-nnw-cursor (groups threshold tail maxes horizon)
  (declare (xargs :guard t))
  (list :newnews groups threshold tail maxes horizon))
(defun fn-nnw-cursorp (cur)
  (declare (xargs :guard t))
  (and (true-listp cur) (equal (len cur) 6) (eq (car cur) :newnews)))
(defun fn-nnw-at (n x)
  (declare (xargs :guard t :measure (nfix n)))
  (if (consp x)
      (if (zp (nfix n)) (car x) (fn-nnw-at (1- (nfix n)) (cdr x)))
    nil))
(defun fn-nnw-groups (cur) (declare (xargs :guard t)) (fn-nnw-at 1 cur))
(defun fn-nnw-threshold (cur) (declare (xargs :guard t)) (fn-nnw-at 2 cur))
(defun fn-nnw-tail (cur) (declare (xargs :guard t)) (fn-nnw-at 3 cur))
(defun fn-nnw-maxes-of (cur) (declare (xargs :guard t)) (fn-nnw-at 4 cur))
(defun fn-nnw-horizon (cur) (declare (xargs :guard t)) (fn-nnw-at 5 cur))

; MAXES is nil (no index) or exact.
(defun fn-nnw-maxes-okp (tail maxes)
  (declare (xargs :guard t))
  (or (null maxes) (equal maxes (fn-nnw-maxes tail))))

(defun fn-nnw-cursor-okp (cur)
  (declare (xargs :guard t))
  (and (fn-nnw-cursorp cur)
       (fn-nnw-maxes-okp (fn-nnw-tail cur) (fn-nnw-maxes-of cur))))

; What the reply still owes at CUR (nil: done).
(defun fn-nnw-owes (cur fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (fn-nnw-cursorp cur)
      (fn-nntp-newnews-scan (fn-nnw-groups cur) (fn-nnw-threshold cur)
                            (fn-nnw-tail cur) (fn-nnw-horizon cur) fn-arena)
    nil))

; Past the bound: the index says nothing older can be new.
(defun fn-nnw-pastp (threshold maxes horizon)
  (declare (xargs :guard t))
  (and (consp maxes) (natp horizon)
       (< (* 1000 (max (nfix (car maxes)) horizon)) (rfix threshold))))

; At most Q articles visited; (mv LINES NEXT), NEXT nil when the reply is
; done.
(defun fn-nnw-loop (groups threshold tail maxes horizon q fn-arena acc)
  (declare (xargs :stobjs fn-arena :guard (and (natp q) (true-listp acc))
                  :measure (acl2-count tail)))
  (cond ((or (atom tail) (fn-nnw-pastp threshold maxes horizon))
         (mv (revappend acc nil) nil))
        ((zp q)
         (mv (revappend acc nil) (fn-nnw-cursor groups threshold tail maxes horizon)))
        (t (let* ((article (car tail))
                  (stamp (fn-article-stamp article)))
             (fn-nnw-loop groups threshold (cdr tail) (fn-ag-cdr maxes)
                          (if (natp stamp) stamp horizon) (1- q) fn-arena
                          (if (and (fn-nntp-newnews-candidatep groups article)
                                   (not (fn-nntp-article-tombstonep article fn-arena))
                                   (fn-nntp-newnews-newp threshold stamp horizon))
                              (cons (fn-nntp-string-octets (fn-article-msgid article)) acc)
                            acc))))))

(defun fn-nnw-step (cur q fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (fn-nnw-cursorp cur)
      (fn-nnw-loop (fn-nnw-groups cur) (fn-nnw-threshold cur) (fn-nnw-tail cur)
                   (fn-nnw-maxes-of cur) (fn-nnw-horizon cur)
                   (max 1 (nfix q)) fn-arena nil)
    (mv nil nil)))

(local
 (defthm fn-nnw-maxes-okp-of-cdr
   (implies (fn-nnw-maxes-okp tail maxes)
            (fn-nnw-maxes-okp (cdr tail) (cdr maxes)))
   :hints (("Goal" :in-theory (enable fn-nnw-maxes-unfolds)))))

(local
 (defthm fn-nnw-car-maxes
   (implies (consp tail)
            (equal (car (fn-nnw-maxes tail)) (fn-nnw-smax tail)))
   :hints (("Goal" :in-theory (enable fn-nnw-maxes-unfolds)))))

(local
 (defthm fn-nnw-consp-maxes
   (equal (consp (fn-nnw-maxes tail)) (consp tail))
   :hints (("Goal" :in-theory (enable fn-nnw-maxes-unfolds)))))

; Past the bound, the scan of the tail is nil.
(local
 (defthm fn-nnw-past-scan-nil
   (implies (and (fn-nnw-maxes-okp tail maxes)
                 (fn-nnw-pastp threshold maxes horizon))
            (equal (fn-nntp-newnews-scan groups threshold tail horizon fn-arena) nil))
   :hints (("Goal" :cases ((consp tail))
            :in-theory (disable fn-nntp-newnews-scan fn-nnw-smax fn-nnw-maxes-unfolds)
            :use ((:instance fn-nnw-scan-nil-past-bound
                             (arts tail) (b (max (fn-nnw-smax tail) horizon))))))))

(local
 (defthm fn-nnw-append-revappend
   (equal (append (revappend acc z) y) (revappend acc (append z y)))
   :hints (("Goal" :induct (revappend acc z) :in-theory (disable revappend-removal)))))

(local
 (defthm fn-nnw-loop-residual
   (implies (fn-nnw-maxes-okp tail maxes)
            (let ((r (fn-nnw-loop groups threshold tail maxes horizon q fn-arena acc)))
              (and (equal (append (mv-nth 0 r) (fn-nnw-owes (mv-nth 1 r) fn-arena))
                          (revappend acc (fn-nntp-newnews-scan groups threshold tail
                                                               horizon fn-arena)))
                   (or (null (mv-nth 1 r)) (fn-nnw-cursor-okp (mv-nth 1 r))))))
   :hints (("Goal" :induct (fn-nnw-loop groups threshold tail maxes horizon q fn-arena acc)
            :in-theory (e/d (revappend)
                            (revappend-removal fn-nntp-newnews-candidatep fn-nntp-article-tombstonep
                             fn-nntp-newnews-newp fn-nntp-string-octets fn-article-msgid
                             fn-nnw-pastp fn-nnw-maxes-okp fn-nnw-maxes-unfolds))))))

; RESIDUAL: the quantum's lines, then what the next cursor owes, are what
; the cursor owed.
(defthm fn-nnw-step-residual
  (implies (fn-nnw-cursor-okp cur)
           (and (equal (append (mv-nth 0 (fn-nnw-step cur q fn-arena))
                               (fn-nnw-owes (mv-nth 1 (fn-nnw-step cur q fn-arena)) fn-arena))
                       (fn-nnw-owes cur fn-arena))
                (or (null (mv-nth 1 (fn-nnw-step cur q fn-arena)))
                    (fn-nnw-cursor-okp (mv-nth 1 (fn-nnw-step cur q fn-arena))))))
  :hints (("Goal" :in-theory (disable fn-nnw-loop fn-nntp-newnews-scan fn-nnw-maxes-okp)
           :use ((:instance fn-nnw-loop-residual
                            (groups (fn-nnw-groups cur)) (threshold (fn-nnw-threshold cur))
                            (tail (fn-nnw-tail cur)) (maxes (fn-nnw-maxes-of cur))
                            (horizon (fn-nnw-horizon cur)) (q (max 1 (nfix q))) (acc nil))))))

; BUDGET: at most (max 1 Q) articles visited, so at most that many lines.
(local
 (defthm fn-nnw-loop-lines-bound
   (<= (len (mv-nth 0 (fn-nnw-loop groups threshold tail maxes horizon q fn-arena acc)))
       (+ (len acc) (nfix q)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (disable fn-nntp-newnews-candidatep fn-nntp-article-tombstonep
                                       fn-nntp-newnews-newp fn-nntp-string-octets
                                       fn-article-msgid fn-nnw-pastp)))))

(defthm fn-nnw-step-lines-at-most-q
  (<= (len (mv-nth 0 (fn-nnw-step cur q fn-arena))) (max 1 (nfix q)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-nnw-loop fn-nnw-loop-lines-bound)
           :use ((:instance fn-nnw-loop-lines-bound
                            (groups (fn-nnw-groups cur)) (threshold (fn-nnw-threshold cur))
                            (tail (fn-nnw-tail cur)) (maxes (fn-nnw-maxes-of cur))
                            (horizon (fn-nnw-horizon cur)) (q (max 1 (nfix q))) (acc nil))))))

; PROGRESS: a next cursor has a strictly shorter tail.
(local
 (defthm fn-nnw-loop-progress
   (let ((next (mv-nth 1 (fn-nnw-loop groups threshold tail maxes horizon q fn-arena acc))))
     (implies (and next (posp q))
              (< (acl2-count (fn-nnw-tail next)) (acl2-count tail))))
   :rule-classes :linear
   :hints (("Goal" :in-theory (disable fn-nntp-newnews-candidatep fn-nntp-article-tombstonep
                                       fn-nntp-newnews-newp fn-nntp-string-octets
                                       fn-article-msgid fn-nnw-pastp)))))

(defthm fn-nnw-step-progresses
  (let ((next (mv-nth 1 (fn-nnw-step cur q fn-arena))))
    (implies next
             (< (acl2-count (fn-nnw-tail next)) (acl2-count (fn-nnw-tail cur)))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-nnw-loop fn-nnw-tail fn-nnw-loop-progress)
           :use ((:instance fn-nnw-loop-progress
                            (groups (fn-nnw-groups cur)) (threshold (fn-nnw-threshold cur))
                            (tail (fn-nnw-tail cur)) (maxes (fn-nnw-maxes-of cur))
                            (horizon (fn-nnw-horizon cur)) (q (max 1 (nfix q))) (acc nil))))))

(local
 (defthm fn-nnw-loop-lines-true-listp
   (true-listp (car (fn-nnw-loop groups threshold tail maxes horizon q fn-arena acc)))
   :hints (("Goal" :in-theory (disable fn-nntp-newnews-candidatep fn-nntp-article-tombstonep
                                       fn-nntp-newnews-newp fn-nntp-string-octets
                                       fn-article-msgid fn-nnw-pastp)))))

(defthm fn-nnw-step-lines-true-listp
  (true-listp (car (fn-nnw-step cur q fn-arena)))
  :hints (("Goal" :in-theory (disable fn-nnw-loop))))

(defthm fn-nnw-owes-of-nil
  (equal (fn-nnw-owes nil fn-arena) nil))

(local
 (defthm fn-nnw-append-nil-of-true-list
   (implies (true-listp x) (equal (append x nil) x))))

(in-theory (disable fn-nnw-step fn-nnw-owes))

; The steps to the end.
(defun fn-nnw-run (cur q fn-arena)
  (declare (xargs :stobjs fn-arena :guard t
                  :measure (acl2-count (fn-nnw-tail cur))
                  :hints (("Goal" :use ((:instance fn-nnw-step-progresses))
                           :in-theory (disable fn-nnw-step-progresses fn-nnw-tail)))))
  (mv-let (lines next)
    (fn-nnw-step cur q fn-arena)
    (if next
        (append lines (fn-nnw-run next q fn-arena))
      lines)))

(local
 (defthm fn-nnw-run-is-owes
   (implies (fn-nnw-cursor-okp cur)
            (equal (fn-nnw-run cur q fn-arena) (fn-nnw-owes cur fn-arena)))
   :hints (("Goal" :induct (fn-nnw-run cur q fn-arena)
            :in-theory (disable fn-nnw-cursor-okp))
           ("Subgoal *1/1" :use ((:instance fn-nnw-step-residual)))
           ("Subgoal *1/2" :use ((:instance fn-nnw-step-residual))))))

; KEYSTONE (the run is the reference scan).
(defthm fn-nnw-run-is-newnews-scan
  (implies (fn-nnw-maxes-okp arts maxes)
           (equal (fn-nnw-run (fn-nnw-cursor groups threshold arts maxes horizon) q fn-arena)
                  (fn-nntp-newnews-scan groups threshold arts horizon fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-nnw-owes) (fn-nnw-run fn-nnw-maxes-okp))
           :use ((:instance fn-nnw-run-is-owes
                            (cur (fn-nnw-cursor groups threshold arts maxes horizon)))))))

; -----------------------------------------------------------------------------
; 5. The response.

; The cursor a NEWNEWS starts: the carry's maxima when it describes ARTS.
(defun fn-nnw-start (groups threshold arts horizon carry)
  (declare (xargs :guard t))
  (fn-nnw-cursor groups threshold arts
                 (if (equal arts (fn-nnw-arts carry)) (fn-nnw-index carry) nil)
                 horizon))

(defthm fn-nnw-start-okp
  (implies (fn-nnw-carryp carry)
           (fn-nnw-cursor-okp (fn-nnw-start groups threshold arts horizon carry)))
  :hints (("Goal" :in-theory (enable fn-nnw-carryp fn-nnw-okp fn-nnw-arts fn-nnw-index
                                     fn-nnw-index-of fn-cv-car fn-cv-cdr
                                     fn-nnw-maxes-is-build-onto))))

; fn-nntp-newnews-response with the run of the started cursor in the scan's
; place (QUANTUM is the reply's quantum; a host that serves the cursor in
; plan quanta writes these lines, fn-nnw-step-residual).
(defun fn-nnw-response (session archive env args carry quantum fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (not (and (consp args) (consp (cdr args)) (consp (cdr (cdr args)))
                (or (null (cdr (cdr (cdr args))))
                    (and (consp (cdr (cdr (cdr args))))
                         (null (cdr (cdr (cdr (cdr args)))))
                         (fn-nntp-keywordp (car (cdr (cdr (cdr args))))
                                           "GMT")))))
      (fn-nntp-single session (fn-proto-text * :syntax))
    (let ((date (fn-nntp-newgroups-date-parse
                 (car (cdr args))
                 (fn-nntp-observed-year (fn-nntp-env-observation env))))
          (time (fn-nntp-newgroups-time-parse (car (cdr (cdr args)))))
          (patterns (fn-wildmat-parse (car args))))
      (if (and (not (fn-nntp-parse-okp date))
               (equal (car (cdr date)) :no-century))
          (fn-nntp-single
           session (fn-proto-text * :no-century))
        (if (or (not (fn-nntp-parse-okp date))
                (not (fn-nntp-parse-okp time))
                (not (fn-wildmat-result-okp patterns)))
            (fn-nntp-single session (fn-proto-text * :syntax))
          (fn-nntp-multi
           session (fn-proto-text "NEWNEWS" :listed)
           (fn-nnw-run
            (fn-nnw-start
             (fn-nntp-filter-groups-by-wildmat
              (fn-wildmat-result-value patterns)
              (fn-state-groups archive))
             (fn-nntp-civil-dtn-ms
              (fn-nntp-parse-1 date) (fn-nntp-parse-2 date)
              (fn-nntp-parse-3 date) (fn-nntp-parse-1 time)
              (fn-nntp-parse-2 time) (fn-nntp-parse-3 time))
             (fn-state-articles archive)
             (fn-nntp-newnews-reader-horizon env) carry)
            quantum fn-arena)))))))

(defthm fn-nnw-run-of-start
  (implies (fn-nnw-carryp carry)
           (equal (fn-nnw-run (fn-nnw-start groups threshold arts horizon carry) q fn-arena)
                  (fn-nntp-newnews-scan groups threshold arts horizon fn-arena)))
  :hints (("Goal" :use ((:instance fn-nnw-run-is-newnews-scan
                                   (maxes (if (equal arts (fn-nnw-arts carry))
                                              (fn-nnw-index carry)
                                            nil))))
           :in-theory (e/d (fn-nnw-start fn-nnw-carryp fn-nnw-okp fn-nnw-arts fn-nnw-index
                            fn-nnw-index-of fn-cv-car fn-cv-cdr fn-nnw-maxes-is-build-onto
                            fn-nnw-maxes-okp)
                           (fn-nnw-run fn-nnw-run-is-newnews-scan fn-nnw-run-is-owes
                            fn-nnw-cursor fn-nntp-newnews-scan fn-nnw-maxes)))))

(in-theory (disable fn-nnw-start))

; KEYSTONE (the reply bytes are the reference's).
(defthm fn-nnw-response-is-newnews-response
  (implies (fn-nnw-carryp carry)
           (equal (fn-nnw-response session archive env args carry quantum fn-arena)
                  (fn-nntp-newnews-response session archive env args fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-newnews-response fn-nnw-response)
                                  (fn-nnw-run fn-nntp-newnews-scan fn-nntp-multi fn-nntp-single
                                   fn-nntp-newgroups-date-parse fn-nntp-newgroups-time-parse
                                   fn-wildmat-parse fn-nntp-parse-okp fn-wildmat-result-okp
                                   fn-nntp-filter-groups-by-wildmat fn-nntp-civil-dtn-ms
                                   fn-nntp-keywordp fn-nntp-newnews-reader-horizon
                                   fn-wildmat-result-value)))))
