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
;    The carry is (ARTS . MAXES), fn-nnw-carryp: MAXES is (fn-nnw-maxes
;    ARTS).  fn-nnw-refresh brings it to a list by walking to the tail EQUAL
;    to the carried list and folding the walked prefix onto the carried
;    maxes (the view's article list grows by consing the new article,
;    books/control-visible.lisp fn-ctl-visible-add); else it rebuilds.  It
;    keeps fn-nnw-carryp, and nil has it (fn-nnw-carryp-of-refresh,
;    fn-nnw-carryp-of-nil).
; 2. The cursor (:newnews GROUPS THRESHOLD TAIL MAXES HORIZON): what the
;    reply still owes is (fn-nntp-newnews-scan GROUPS THRESHOLD TAIL HORIZON)
;    (fn-nnw-owes).  MAXES is (fn-nnw-maxes TAIL) or nil (no index: the
;    cursor walks to the end, still in quanta).  fn-nnw-step reads at most
;    (max 1 Q) articles (fn-nnw-step-reads-at-most-q, fn-nnw-step-consumes-q;
;    fn-nnw-step-lines-at-most-q bounds its lines) and always progresses
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
; The served subject: the -cat dispatcher's NEWNEWS arm
; (books/served-catalog.lisp fn-nntp-newnews-ovw) emits section 7's plan
; cursor, which books/served-plan-cursor.lisp steps (fn-nnwp-step).  The arm
; passes the carry NIL for now (not threaded to the dispatcher): the cursor
; then walks to the end in bounded quanta.  fn-nnw-response is the list
; model of the reply with the carry.

(in-package "ACL2")
(include-book "nntp-responses")

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

; Oldest-first fold: YS reversed onto the maxima of what follows them.
(defun fn-nnw-fold (ys acc)
  (declare (xargs :guard t))
  (if (consp ys)
      (fn-nnw-fold (cdr ys) (cons (max (fn-nnw-s (car ys)) (fn-nnw-top acc)) acc))
    acc))

(defun fn-nnw-maxes-rec (arts)
  (declare (xargs :guard t))
  (if (consp arts)
      (cons (fn-nnw-smax arts) (fn-nnw-maxes-rec (cdr arts)))
    nil))

(local
 (defthm fn-nnw-smax-natp
   (natp (fn-nnw-smax arts))
   :rule-classes :type-prescription))

(local
 (defthm fn-nnw-top-of-maxes-rec
   (equal (fn-nnw-top (fn-nnw-maxes-rec zs)) (fn-nnw-smax zs))))

(local
 (defthm fn-nnw-fold-onto-maxes
   (equal (fn-nnw-fold ys (fn-nnw-maxes-rec zs))
          (fn-nnw-maxes-rec (revappend ys zs)))
   :hints (("Goal" :induct (revappend ys zs)
            :in-theory (disable fn-nnw-s revappend-removal)))))

(local
 (defthm fn-nnw-smax-of-true-list-fix
   (equal (fn-nnw-smax (append x nil)) (fn-nnw-smax x))))

(local
 (defthm fn-nnw-maxes-rec-of-true-list-fix
   (equal (fn-nnw-maxes-rec (append x nil)) (fn-nnw-maxes-rec x))))

(local
 (defthm fn-nnw-maxes-rec-of-revappend-revappend
   (equal (fn-nnw-maxes-rec (revappend (revappend arts nil) nil))
          (fn-nnw-maxes-rec arts))
   :hints (("Goal" :in-theory (disable fn-nnw-maxes-rec)))))

(defun fn-nnw-rev (x acc)
  (declare (xargs :guard t))
  (if (consp x) (fn-nnw-rev (cdr x) (cons (car x) acc)) acc))

(local
 (defthm fn-nnw-rev-is-revappend
   (equal (fn-nnw-rev x acc) (revappend x acc))))

; The index, built by one oldest-first fold.
(defun fn-nnw-maxes (arts)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :use ((:instance fn-nnw-fold-onto-maxes
                                                         (ys (revappend arts nil)) (zs nil)))
                                 :in-theory (disable fn-nnw-fold-onto-maxes revappend-removal
                                                     fn-nnw-fold fn-nnw-maxes-rec)))))
  (mbe :logic (fn-nnw-maxes-rec arts)
       :exec (fn-nnw-fold (fn-nnw-rev arts nil) nil)))

(defthm fn-nnw-maxes-unfolds
  (equal (fn-nnw-maxes arts)
         (if (consp arts)
             (cons (fn-nnw-smax arts) (fn-nnw-maxes (cdr arts)))
           nil))
  :rule-classes :definition)

(in-theory (disable fn-nnw-maxes))

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
; 3. The carry.

(defun fn-nnw-carryp (carry)
  (declare (xargs :guard t))
  (equal (fn-ag-cdr carry) (fn-nnw-maxes (fn-ag-car carry))))

(defthm fn-nnw-carryp-of-nil
  (fn-nnw-carryp nil)
  :hints (("Goal" :in-theory (enable fn-nnw-maxes))))

; Walk TAIL until it is EQUAL to OLD, collecting the walked articles
; reversed (oldest first).  (mv FOUND ACC).
(defun fn-nnw-collect (tail old acc)
  (declare (xargs :guard t))
  (cond ((equal tail old) (mv t acc))
        ((atom tail) (mv nil acc))
        (t (fn-nnw-collect (cdr tail) old (cons (car tail) acc)))))

(local
 (defthm fn-nnw-collect-found
   (implies (mv-nth 0 (fn-nnw-collect tail old acc))
            (equal (revappend (mv-nth 1 (fn-nnw-collect tail old acc)) old)
                   (revappend acc tail)))
   :hints (("Goal" :induct (fn-nnw-collect tail old acc)
            :in-theory (disable revappend-removal)))))

(local
 (defthm fn-nnw-refresh-found-maxes
   (implies (and (mv-nth 0 (fn-nnw-collect arts old nil))
                 (equal m (fn-nnw-maxes-rec old)))
            (equal (fn-nnw-fold (mv-nth 1 (fn-nnw-collect arts old nil)) m)
                   (fn-nnw-maxes-rec arts)))
   :hints (("Goal" :use ((:instance fn-nnw-collect-found (tail arts) (acc nil))
                         (:instance fn-nnw-fold-onto-maxes
                                    (ys (mv-nth 1 (fn-nnw-collect arts old nil)))
                                    (zs old)))
            :in-theory (disable fn-nnw-collect-found fn-nnw-fold-onto-maxes
                                fn-nnw-collect fn-nnw-fold fn-nnw-maxes-rec
                                revappend-removal)))))

(defun fn-nnw-refresh (carry arts)
  (declare (xargs :guard t))
  (if (equal arts (fn-ag-car carry))
      carry
    (mv-let (found acc)
      (fn-nnw-collect arts (fn-ag-car carry) nil)
      (if found
          (cons arts (fn-nnw-fold acc (fn-ag-cdr carry)))
        (cons arts (fn-nnw-maxes arts))))))

(defthm fn-nnw-carryp-of-refresh
  (implies (fn-nnw-carryp carry)
           (fn-nnw-carryp (fn-nnw-refresh carry arts)))
  :hints (("Goal" :in-theory (e/d (fn-nnw-maxes) (fn-nnw-collect fn-nnw-fold fn-nnw-smax
                                                   revappend-removal fn-nnw-maxes-unfolds
                                                   fn-nnw-maxes-rec)))))

(defthm fn-nnw-car-of-refresh
  (equal (car (fn-nnw-refresh carry arts)) arts))

(in-theory (disable fn-nnw-carryp fn-nnw-refresh))

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
   :hints (("Goal" :in-theory (enable fn-nnw-maxes)))))

(local
 (defthm fn-nnw-car-maxes
   (implies (consp tail)
            (equal (car (fn-nnw-maxes tail)) (fn-nnw-smax tail)))
   :hints (("Goal" :in-theory (enable fn-nnw-maxes)))))

(local
 (defthm fn-nnw-consp-maxes
   (equal (consp (fn-nnw-maxes tail)) (consp tail))
   :hints (("Goal" :in-theory (enable fn-nnw-maxes)))))

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
                 (if (equal arts (fn-ag-car carry)) (fn-ag-cdr carry) nil)
                 horizon))

(defthm fn-nnw-start-okp
  (implies (fn-nnw-carryp carry)
           (fn-nnw-cursor-okp (fn-nnw-start groups threshold arts horizon carry)))
  :hints (("Goal" :in-theory (enable fn-nnw-carryp))))

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
                                   (maxes (if (equal arts (fn-ag-car carry))
                                              (fn-ag-cdr carry)
                                            nil))))
           :in-theory (e/d (fn-nnw-start fn-nnw-carryp fn-nnw-maxes-okp)
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

; -----------------------------------------------------------------------------
; 6. ARTICLES VISITED (Codex r59 F1).  fn-nnw-step-lines-at-most-q bounds the
; lines a quantum emits; these bound the articles it reads.  A quantum reads
; at most the first (max 1 Q) articles of its tail: its lines are the lines of
; the step over that prefix alone (fn-nnw-step-reads-at-most-q), and a
; quantum that leaves a cursor consumed exactly that many
; (fn-nnw-step-consumes-q).  Per article the work is the candidate test over
; the selected groups (fn-nntp-newnews-candidatep: one membership probe per
; group of GROUPS), the tombstone probe (the payload's fixed head) and the
; stamp test; GROUPS is selected once, at the command's step, by
; fn-nntp-filter-groups-by-wildmat over the configured groups.  So a quantum
; is O(max(1,Q) x |GROUPS|) and the command's step O(G x |wildmat|), G the
; configured group count: bounded by the operator's group profile (D27: an
; admission limit, not a data ceiling), not by the article count.

(defun fn-nnw-firstn (n x)
  (declare (xargs :guard (natp n)))
  (if (or (zp n) (atom x)) nil (cons (car x) (fn-nnw-firstn (1- n) (cdr x)))))

(local
 (defthm fn-nnw-loop-reads-firstn
   (equal (car (fn-nnw-loop groups threshold (fn-nnw-firstn q tail) maxes horizon q
                            fn-arena acc))
          (car (fn-nnw-loop groups threshold tail maxes horizon q fn-arena acc)))
   :hints (("Goal" :induct (fn-nnw-loop groups threshold tail maxes horizon q fn-arena acc)
            :in-theory (disable fn-nntp-newnews-candidatep fn-nntp-article-tombstonep
                                fn-nntp-newnews-newp fn-nntp-string-octets
                                fn-article-msgid fn-nnw-pastp)))))

(local
 (defthm fn-nnw-loop-next-tail
   (let ((next (mv-nth 1 (fn-nnw-loop groups threshold tail maxes horizon q fn-arena acc))))
     (implies next
              (equal (fn-nnw-tail next) (nthcdr (nfix q) tail))))
   :hints (("Goal" :induct (fn-nnw-loop groups threshold tail maxes horizon q fn-arena acc)
            :in-theory (disable fn-nntp-newnews-candidatep fn-nntp-article-tombstonep
                                fn-nntp-newnews-newp fn-nntp-string-octets
                                fn-article-msgid fn-nnw-pastp)))))

; KEYSTONE (articles read): the quantum's lines depend on the first
; (max 1 Q) articles of the tail and on nothing after them.
(defthm fn-nnw-step-reads-at-most-q
  (equal (mv-nth 0 (fn-nnw-step (fn-nnw-cursor groups threshold
                                               (fn-nnw-firstn (max 1 (nfix q)) tail)
                                               maxes horizon)
                                q fn-arena))
         (mv-nth 0 (fn-nnw-step (fn-nnw-cursor groups threshold tail maxes horizon)
                                q fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-nnw-step) (fn-nnw-loop fn-nnw-firstn))
           :use ((:instance fn-nnw-loop-reads-firstn (q (max 1 (nfix q))) (acc nil))))))

(local
 (defthm fn-nnw-tail-of-cursor-list
   (equal (fn-nnw-tail (list :newnews groups threshold tail maxes horizon)) tail)))

; A quantum that leaves a cursor consumed exactly (max 1 Q) articles.
(defthm fn-nnw-step-consumes-q
  (let ((next (mv-nth 1 (fn-nnw-step (fn-nnw-cursor groups threshold tail maxes horizon)
                                     q fn-arena))))
    (implies next
             (equal (fn-nnw-tail next) (nthcdr (max 1 (nfix q)) tail))))
  :hints (("Goal" :in-theory (e/d (fn-nnw-step) (fn-nnw-loop mv-nth fn-nnw-tail))
           :use ((:instance fn-nnw-loop-next-tail (q (max 1 (nfix q))) (acc nil))))))

; -----------------------------------------------------------------------------
; 7. THE PLAN CURSOR: the NEWNEWS reply as a cursor in the connection's render
; plan (books/served-plan-cursor.lisp steps it; books/served-catalog.lisp
; fn-ovw-cursor-octets is what it stands for).  (:nnw-reply OWEDP CUR): CUR the
; scan cursor above, OWEDP whether the 230 status line is still owed.  Its
; third element is a scan cursor, which an OVER cursor's (its clamped TOP, a
; number) never is: fn-nnwp-cursorp tells the two apart.
;
; THE PIN (Codex r59): the cursor reads the arena between quanta (the
; tombstone probe of each candidate's payload head).  It is held where OVER's
; is, in the connection's response plan, and the host takes the plan's
; reader hold after every served step (host/native/owner.lisp
; fnn-owner-response-pin, books/response-plan-pins.lisp fn-rpin-step,
; PRF-1059), which reclaim's swap excludes while the plan lives: a reclaim
; between quanta cannot retire a payload a later quantum probes.  The tail is
; the pinned archive's own article list (an immutable value), so a commit or
; withdrawal between quanta changes no quantum either.

(defun fn-nnwp-cursor (owedp cur)
  (declare (xargs :guard t))
  (list :nnw-reply owedp cur))

(defun fn-nnwp-cursorp (pc)
  (declare (xargs :guard t))
  (and (true-listp pc) (fn-nnw-cursorp (nth 2 pc))))

(defun fn-nnwp-cursor-okp (pc)
  (declare (xargs :guard t))
  (and (fn-nnwp-cursorp pc) (fn-nnw-cursor-okp (nth 2 pc))))

(defun fn-nnwp-status ()
  (declare (xargs :guard t))
  (fn-nntp-crlf (fn-nntp-string-octets (fn-proto-text "NEWNEWS" :listed))))

; What the plan cursor stands for: the status line if owed, the stuffed lines
; the scan cursor owes, the terminator.
(defun fn-nnwp-octets (pc fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (append (if (nth 1 pc) (fn-nnwp-status) nil)
          (fn-nntp-stuff-lines (fn-nnw-owes (nth 2 pc) fn-arena))
          '(46 13 10)))

; One quantum: at most (max 1 W) articles read (section 6).
(defun fn-nnwp-step (pc w fn-arena)
  (declare (xargs :stobjs fn-arena :guard (true-listp pc)))
  (mv-let (lines next)
    (fn-nnw-step (nth 2 pc) w fn-arena)
    (mv (append (if (nth 1 pc) (fn-nnwp-status) nil)
                (fn-nntp-stuff-lines lines)
                (if next nil '(46 13 10)))
        (if next (fn-nnwp-cursor nil next) nil))))

(defthm fn-nnwp-step-next-is-cursor
  (let ((next (mv-nth 1 (fn-nnwp-step pc w fn-arena))))
    (implies next
             (and (consp next) (equal (car next) :nnw-reply)
                  (implies (fn-nnwp-cursor-okp pc) (fn-nnwp-cursor-okp next)))))
  :hints (("Goal" :use ((:instance fn-nnw-step-residual (cur (nth 2 pc)) (q w)))
           :in-theory (e/d (fn-nnw-cursor-okp) (fn-nnw-step-residual fn-nntp-stuff-lines)))))

(local
 (defthm fn-nnw-loop-next-cursorp
   (let ((next (mv-nth 1 (fn-nnw-loop groups threshold tail maxes horizon q fn-arena acc))))
     (implies next (fn-nnw-cursorp next)))
   :hints (("Goal" :induct (fn-nnw-loop groups threshold tail maxes horizon q fn-arena acc)
            :in-theory (disable fn-nntp-newnews-candidatep fn-nntp-article-tombstonep
                                fn-nntp-newnews-newp fn-nntp-string-octets
                                fn-article-msgid fn-nnw-pastp)))))

; Every plan cursor a quantum leaves is a NEWNEWS plan cursor.
(defthm fn-nnwp-step-next-cursorp
  (let ((next (mv-nth 1 (fn-nnwp-step pc w fn-arena))))
    (implies next (fn-nnwp-cursorp next)))
  :hints (("Goal" :in-theory (e/d (fn-nnw-step fn-nnwp-step fn-nnwp-cursor) (fn-nnw-loop))
           :use ((:instance fn-nnw-loop-next-cursorp
                            (groups (fn-nnw-groups (nth 2 pc))) (threshold (fn-nnw-threshold (nth 2 pc)))
                            (tail (fn-nnw-tail (nth 2 pc))) (maxes (fn-nnw-maxes-of (nth 2 pc)))
                            (horizon (fn-nnw-horizon (nth 2 pc))) (q (max 1 (nfix w))) (acc nil))))))

(defun fn-nnwp-run (pc w fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil
                  :measure (acl2-count (fn-nnw-tail (nth 2 pc)))
                  :hints (("Goal" :use ((:instance fn-nnw-step-progresses (cur (nth 2 pc)) (q w)))
                           :in-theory (disable fn-nnw-step-progresses fn-nnw-tail)))))
  (mv-let (octets next)
    (fn-nnwp-step pc w fn-arena)
    (if next
        (append octets (fn-nnwp-run next w fn-arena))
      octets)))

(local
 (defthm fn-nnwp-stuff-lines-append
   (equal (fn-nntp-stuff-lines (append a b))
          (append (fn-nntp-stuff-lines a) (fn-nntp-stuff-lines b)))
   :hints (("Goal" :induct (fn-nntp-stuff-lines a)
            :in-theory (e/d (fn-nntp-stuff-lines) (fn-nntp-crlf fn-wire-stuff-line))))))

(local
 (defthm fn-nnwp-append-assoc
   (equal (append (append x y) z) (append x (append y z)))))

(local
 (defthm fn-nnwp-stuff-split
   (implies (equal (append l r) o)
            (equal (append (fn-nntp-stuff-lines l) (append (fn-nntp-stuff-lines r) tl))
                   (append (fn-nntp-stuff-lines o) tl)))
   :hints (("Goal" :in-theory (disable fn-nntp-stuff-lines)
            :use ((:instance fn-nnwp-stuff-lines-append (a l) (b r)))))))

; RESIDUAL: a quantum's octets followed by what the next plan cursor stands
; for are what the plan cursor stood for.
(defthm fn-nnwp-step-residual
  (implies (fn-nnwp-cursor-okp pc)
           (equal (append (mv-nth 0 (fn-nnwp-step pc w fn-arena))
                          (if (mv-nth 1 (fn-nnwp-step pc w fn-arena))
                              (fn-nnwp-octets (mv-nth 1 (fn-nnwp-step pc w fn-arena)) fn-arena)
                            nil))
                  (fn-nnwp-octets pc fn-arena)))
  :hints (("Goal" :use ((:instance fn-nnw-step-residual (cur (nth 2 pc)) (q w)))
           :in-theory (e/d (fn-nnw-cursor-okp fn-nnwp-step fn-nnwp-octets fn-nnwp-cursor)
                           (fn-nnw-step-residual fn-nntp-stuff-lines fn-nnwp-status
                            fn-nnwp-stuff-lines-append)))))

(defthm fn-nnwp-step-octets-true-listp
  (true-listp (car (fn-nnwp-step pc w fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-nnwp-step) (fn-nntp-stuff-lines fn-nnwp-status)))))

; KEYSTONE (the plan cursor's run is what it stands for), every quantum W.
(defthm fn-nnwp-run-is-octets
  (implies (fn-nnwp-cursor-okp pc)
           (equal (fn-nnwp-run pc w fn-arena) (fn-nnwp-octets pc fn-arena)))
  :hints (("Goal" :induct (fn-nnwp-run pc w fn-arena)
           :in-theory (e/d (fn-nnwp-run) (fn-nnwp-step fn-nnwp-octets fn-nnwp-cursor-okp)))
          ("Subgoal *1/2" :use ((:instance fn-nnwp-step-residual)
                                (:instance fn-nnwp-step-next-is-cursor)))
          ("Subgoal *1/1" :use ((:instance fn-nnwp-step-residual)
                                (:instance fn-nnwp-step-next-is-cursor)))))

; The fresh plan cursor a NEWNEWS starts stands for the reference's reply
; octets: the status line, the scan's stuffed lines, the terminator.
(defthm fn-nnwp-octets-of-start
  (implies (fn-nnw-carryp carry)
           (equal (fn-nnwp-octets (fn-nnwp-cursor t (fn-nnw-start groups threshold arts
                                                                  horizon carry))
                                  fn-arena)
                  (append (fn-nnwp-status)
                          (fn-nntp-stuff-lines
                           (fn-nntp-newnews-scan groups threshold arts horizon fn-arena))
                          '(46 13 10))))
  :hints (("Goal" :use ((:instance fn-nnw-run-of-start (q 1))
                        (:instance fn-nnw-run-is-owes
                                   (cur (fn-nnw-start groups threshold arts horizon carry))
                                   (q 1))
                        (:instance fn-nnw-start-okp))
           :in-theory (e/d (fn-nnwp-octets fn-nnwp-cursor) (fn-nnw-run fn-nnw-run-of-start fn-nnw-run-is-owes
                               fn-nnw-start-okp fn-nntp-stuff-lines fn-nnwp-status
                               fn-nntp-newnews-scan)))))

(in-theory (disable fn-nnwp-step fn-nnwp-run fn-nnwp-octets fn-nnwp-status))
