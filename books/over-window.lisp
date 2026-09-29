; over-window.lisp -- OVER/XOVER of a range answered in bounded windows
; (lane join-f2-10, 2026-09-29; PKT-733 (4), D27).
;
; fn-nntp-over-range-cat (books/served-catalog.lisp) probes every number of
; the clamped range and builds every NOV line in one served step: the work
; one step does grows with the range.  This book answers the same range as
; a CURSOR advanced one window of at most W numbers per quantum:
;
;   fn-ovw-start (session v token legacyp fn-cat) -> (mv octets cursor)
;     the command's step: O(1) work (the range is parsed and clamped to the
;     group's next number; no number is probed).  A cursor is NIL when the
;     reply is complete (no group selected).
;   fn-ovw-step (cursor w fn-arena fn-cat) -> (mv octets cursor')
;     one quantum: at most W numbers probed and at most W NOV lines built.
;     The status line is decided lazily: 224 before the first line, or 423
;     (420 for XOVER) once the range is exhausted with no line; the
;     terminating dot follows the last window of a 224 reply.
;
; KEYSTONE fn-ovw-run-is-over-range-cat: for every W >= 1, the octets of the
; start followed by the steps until the cursor is NIL are exactly the reply
; octets of fn-nntp-over-range-cat over the same catalog and view: the
; windowed reply is the unbounded reader's, never truncated.  The progress
; measure fn-ovw-remaining strictly decreases at every step of a live
; cursor (fn-ovw-step-progresses), and a step's probes are the window's
; (fn-ovw-step-window-at-most-w: at most W numbers probed, at most W lines).
; FRAME fn-ovw-step-of-commit-pinned / fn-ovw-step-of-withdraw-pinned: a
; quantum run after a commit, or after a withdrawal marked at a later
; version, answers what it answered before, for a cursor pinned at or below
; the catalog's count (through fn-ovw-lines-is-view: a window's lines are a
; function of the pinned view's articles and the arena).

(in-package "ACL2")

(include-book "served-catalog")
(include-book "catalog-number-window")
(include-book "catalog-refresh")

(local (in-theory (disable (tau-system))))

; -----------------------------------------------------------------------------
; The cursor and one window

(defun fn-ovw-status (text)
  (declare (xargs :guard t))
  (fn-nntp-crlf (fn-nntp-string-octets text)))

; The lines of the numbers K..HI of GROUP in view V: the old reader's lines
; restricted to one window.
(defun fn-ovw-lines (group k hi v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp k) (natp hi) (fn-scat-guard))))
  (fn-nov-lines-for-numbers-cat
   group (fn-scat-range-keep group (fn-cnx-range-aux group k hi v fn-cat) fn-cat)
   v fn-arena fn-cat))

; (GROUP K TOP V LEGACYP OWEDP): the next number to probe, the range's last
; number (clamped once, at the start), the pinned view, XOVER or OVER, and
; whether the status line is still owed (no line sent yet).
(defun fn-ovw-cursor (group k top v legacyp owedp)
  (declare (xargs :guard t))
  (list group k top v legacyp owedp))

(defun fn-ovw-cursorp (cur)
  (declare (xargs :guard t))
  (and (true-listp cur) (natp (nth 3 cur))))

(defun fn-ovw-empty-text (legacyp)
  (declare (xargs :guard t))
  (if legacyp (fn-proto-text * :none-selected) (fn-proto-text * :empty-range)))

; The command's step: O(1), no number probed.
(defun fn-ovw-start (session v token legacyp fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (let ((group (fn-nntp-session-group session))
        (range (fn-nntp-parse-range token)))
    (if (null group)
        (mv (fn-ovw-status (fn-proto-text * :no-group-selected)) nil)
      (mv nil
          (fn-ovw-cursor group (nfix (fn-nntp-range-low range))
                         (min (nfix (fn-nntp-range-high range))
                              (nfix (- (fn-cat-group-next group fn-cat) 1)))
                         v legacyp t)))))

(defun fn-ovw-remaining (cur)
  (declare (xargs :guard (true-listp cur)))
  (if (consp cur)
      (nfix (- (+ 1 (nfix (nth 2 cur))) (nfix (nth 1 cur))))
    0))

(defun fn-ovw-hi (k top w)
  (declare (xargs :guard t))
  (min (nfix top) (+ (nfix k) (if (posp w) w 1) -1)))

; One quantum: the window K..HI (at most W numbers).
(defun fn-ovw-step (cur w fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (fn-ovw-cursorp cur)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :verify-guards nil))
  (let* ((group (nth 0 cur)) (k (nfix (nth 1 cur))) (top (nfix (nth 2 cur)))
         (v (nth 3 cur)) (legacyp (nth 4 cur)) (owedp (nth 5 cur))
         (hi (fn-ovw-hi k top w))
         (lines (fn-ovw-lines group k hi v fn-arena fn-cat))
         (owed2 (and owedp (not (consp lines))))
         (donep (<= top hi)))
    (mv (append (if (and owedp (consp lines))
                    (fn-ovw-status (fn-proto-text * :overview))
                  nil)
                (fn-nntp-stuff-lines lines)
                (if donep
                    (if owed2 (fn-ovw-status (fn-ovw-empty-text legacyp)) '(46 13 10))
                  nil))
        (if donep nil (fn-ovw-cursor group (+ 1 hi) top v legacyp owed2)))))

(defthm fn-ovw-step-progresses
  (let ((next (mv-nth 1 (fn-ovw-step cur w fn-arena fn-cat))))
    (implies next
             (and (consp next)
                  (< (fn-ovw-remaining next) (fn-ovw-remaining cur)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-ovw-lines fn-nntp-stuff-lines fn-ovw-status))))

(defthm fn-ovw-step-keeps-cursorp
  (implies (and (fn-ovw-cursorp cur)
                (mv-nth 1 (fn-ovw-step cur w fn-arena fn-cat)))
           (fn-ovw-cursorp (mv-nth 1 (fn-ovw-step cur w fn-arena fn-cat))))
  :hints (("Goal" :in-theory (disable fn-ovw-lines fn-nntp-stuff-lines fn-ovw-status))))

(defthm fn-ovw-start-cursorp
  (implies (and (natp v)
                (mv-nth 1 (fn-ovw-start session v token legacyp fn-cat)))
           (fn-ovw-cursorp (mv-nth 1 (fn-ovw-start session v token legacyp fn-cat)))))

(verify-guards fn-ovw-step
  :hints (("Goal" :in-theory (disable fn-ovw-lines fn-nntp-stuff-lines fn-ovw-status))))

; -----------------------------------------------------------------------------
; The list model: the start, then steps until the cursor is NIL.

(defun fn-ovw-run (cur w fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil
                  :measure (fn-ovw-remaining cur)
                  :hints (("Goal" :use ((:instance fn-ovw-step-progresses))
                           :in-theory (disable fn-ovw-step fn-ovw-remaining)))))
  (if (consp cur)
      (mv-let (octets next) (fn-ovw-step cur w fn-arena fn-cat)
        (if next
            (append octets (fn-ovw-run next w fn-arena fn-cat))
          octets))
    nil))

(defun fn-ovw-octets (session v token legacyp w fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (mv-let (octets cursor)
    (fn-ovw-start session v token legacyp fn-cat)
    (append octets (fn-ovw-run cursor w fn-arena fn-cat))))

; -----------------------------------------------------------------------------
; The windows are the range

(defthm fn-ovw-range-keep-of-append
  (equal (fn-scat-range-keep group (append a b) fn-cat)
         (append (fn-scat-range-keep group a fn-cat)
                 (fn-scat-range-keep group b fn-cat)))
  :hints (("Goal" :induct (fn-scat-range-keep group a fn-cat)
           :in-theory (enable fn-scat-range-keep))))

(defthm fn-ovw-nov-lines-of-append
  (equal (fn-nov-lines-for-numbers-cat group (append a b) v fn-arena fn-cat)
         (append (fn-nov-lines-for-numbers-cat group a v fn-arena fn-cat)
                 (fn-nov-lines-for-numbers-cat group b v fn-arena fn-cat)))
  :hints (("Goal" :induct (fn-nov-lines-for-numbers-cat group a v fn-arena fn-cat)
           :in-theory (e/d (fn-nov-lines-for-numbers-cat)
                           (fn-scat-available-article fn-nov-overview fn-nov-okp fn-nov-line
                            fn-nntp-article-tombstonep)))))

(defthm fn-ovw-stuff-lines-of-append
  (equal (fn-nntp-stuff-lines (append a b))
         (append (fn-nntp-stuff-lines a) (fn-nntp-stuff-lines b)))
  :hints (("Goal" :induct (fn-nntp-stuff-lines a)
           :in-theory (e/d (fn-nntp-stuff-lines) (fn-wire-stuff-line fn-nntp-crlf)))))

(defthm fn-ovw-lines-split
  (implies (and (natp k) (natp hi) (natp top) (<= k hi) (< hi top))
           (equal (fn-ovw-lines group k top v fn-arena fn-cat)
                  (append (fn-ovw-lines group k hi v fn-arena fn-cat)
                          (fn-ovw-lines group (+ 1 hi) top v fn-arena fn-cat))))
  :hints (("Goal" :in-theory (e/d (fn-ovw-lines) (fn-cnx-range-aux
                                                  fn-scat-range-keep fn-nov-lines-for-numbers-cat))
           :use ((:instance fn-cnxw-range-is-windows (b (+ 1 hi)))))))

(defun fn-ovw-reply (lines legacyp owedp)
  (declare (xargs :guard t :verify-guards nil))
  (if owedp
      (if (consp lines)
          (append (fn-ovw-status (fn-proto-text * :overview))
                  (fn-nntp-stuff-lines lines)
                  '(46 13 10))
        (fn-ovw-status (fn-ovw-empty-text legacyp)))
    (append (fn-nntp-stuff-lines lines) '(46 13 10))))

(local
 (defun fn-ovw-ind (group k top v legacyp owedp w fn-arena fn-cat)
   (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil
                   :measure (nfix (- (+ 1 (nfix top)) (nfix k)))))
   (if (and (natp k) (natp top) (<= k top) (< (fn-ovw-hi k top w) top))
       (fn-ovw-ind group (+ 1 (fn-ovw-hi k top w)) top v legacyp
                   (and owedp (not (consp (fn-ovw-lines group k (fn-ovw-hi k top w) v fn-arena fn-cat))))
                   w fn-arena fn-cat)
     (list group k top v legacyp owedp w))))

(local
 (defthm fn-ovw-lines-empty-above
   (implies (and (natp k) (natp top) (< top k))
            (equal (fn-ovw-lines group k top v fn-arena fn-cat) nil))
   :hints (("Goal" :in-theory (enable fn-ovw-lines)))))

(local
 (defthm fn-ovw-cursor-fields
   (and (consp (fn-ovw-cursor group k top v legacyp owedp))
        (equal (nth 0 (fn-ovw-cursor group k top v legacyp owedp)) group)
        (equal (nth 1 (fn-ovw-cursor group k top v legacyp owedp)) k)
        (equal (nth 2 (fn-ovw-cursor group k top v legacyp owedp)) top)
        (equal (nth 3 (fn-ovw-cursor group k top v legacyp owedp)) v)
        (equal (nth 4 (fn-ovw-cursor group k top v legacyp owedp)) legacyp)
        (equal (nth 5 (fn-ovw-cursor group k top v legacyp owedp)) owedp))))

(local
 (defthm fn-ovw-hi-natp
   (implies (natp top) (natp (fn-ovw-hi k top w)))
   :rule-classes :type-prescription))

(local
 (defthm fn-ovw-hi-bounds
   (implies (and (natp k) (natp top) (<= k top))
            (and (<= k (fn-ovw-hi k top w))
                 (<= (fn-ovw-hi k top w) top)))
   :rule-classes :linear))

(local
 (defthm fn-ovw-hi-above
   (implies (and (natp k) (natp top) (< top k))
            (equal (fn-ovw-hi k top w) top))))

(local
 (defthm fn-ovw-hi-at-top
   (implies (and (natp k) (natp top) (<= top (fn-ovw-hi k top w)))
            (equal (fn-ovw-hi k top w) top))
   :hints (("Goal" :in-theory (enable fn-ovw-hi)))))


(local (in-theory (disable fn-ovw-cursor fn-ovw-hi)))

(defthm fn-ovw-run-is-reply
  (implies (and (natp k) (natp top))
           (equal (fn-ovw-run (fn-ovw-cursor group k top v legacyp owedp) w fn-arena fn-cat)
                  (fn-ovw-reply (fn-ovw-lines group k top v fn-arena fn-cat) legacyp owedp)))
  :hints (("Goal" :induct (fn-ovw-ind group k top v legacyp owedp w fn-arena fn-cat)
           :in-theory (e/d (fn-ovw-step)
                           (fn-ovw-run fn-ovw-lines fn-nntp-stuff-lines fn-ovw-status fn-ovw-empty-text
                            fn-ovw-lines-split))
           :expand ((:free (owedp) (fn-ovw-run (fn-ovw-cursor group k top v legacyp owedp) w fn-arena fn-cat))))
          ("Subgoal *1/1" :expand ((:free (owedp) (fn-ovw-run (fn-ovw-cursor group k top v legacyp owedp) w fn-arena fn-cat)))
                          :use ((:instance fn-ovw-lines-split (hi (fn-ovw-hi k top w)))))))

; -----------------------------------------------------------------------------
; The old reader, as the same specification

(defun fn-ovw-spec (session v token legacyp fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (let ((group (fn-nntp-session-group session))
        (range (fn-nntp-parse-range token)))
    (if (null group)
        (fn-ovw-status (fn-proto-text * :no-group-selected))
      (fn-ovw-reply (fn-ovw-lines group (nfix (fn-nntp-range-low range))
                                  (min (nfix (fn-nntp-range-high range))
                                       (nfix (- (fn-cat-group-next group fn-cat) 1)))
                                  v fn-arena fn-cat)
                    legacyp t))))

(defthm fn-ovw-octets-is-spec
  (equal (fn-ovw-octets session v token legacyp w fn-arena fn-cat)
         (fn-ovw-spec session v token legacyp fn-arena fn-cat))
  :hints (("Goal" :do-not-induct t
           :expand ((fn-ovw-run nil w fn-arena fn-cat))
           :in-theory (union-theories '(fn-ovw-octets fn-ovw-start fn-ovw-spec fn-ovw-run-is-reply
                                        natp-compound-recognizer nfix min (:e fn-ovw-status) append-to-nil binary-append
                                        (:e fn-proto-text-of) (:e fn-proto-shared-text))
                                      (theory 'minimal-theory)))))

(local
 (defthm fn-ovw-status-is-crlf
   (equal (fn-nntp-crlf (fn-nntp-string-octets text)) (fn-ovw-status text))))

(local
 (defthm fn-ovw-reply-octets-of-one
   (equal (fn-served-reply-octets (list (list :reply x))) (append x nil))
   :hints (("Goal" :in-theory (enable fn-served-reply-octets)))))

(defthm fn-ovw-over-range-cat-is-spec
  (and (equal (car (fn-nntp-over-range-cat session v token legacyp fn-arena fn-cat))
              session)
       (equal (fn-served-reply-octets
               (cdr (fn-nntp-over-range-cat session v token legacyp fn-arena fn-cat)))
              (fn-ovw-spec session v token legacyp fn-arena fn-cat)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-over-range-cat fn-scat-range-numbers fn-cnx-view-range
                            fn-ovw-spec fn-ovw-reply fn-ovw-lines
                            fn-nntp-single fn-nntp-multi fn-nntp-make-result fn-nntp-reply-effect
                            fn-ovw-empty-text)
                           (fn-cat-group-next-is-high fn-cat-group-next fn-cnx-range-aux
                            fn-scat-range-keep fn-nov-lines-for-numbers-cat fn-nntp-stuff-lines
                            fn-nntp-parse-range fn-ovw-status fn-nntp-crlf fn-nntp-string-octets
 fn-served-reply-octets)))))

; -----------------------------------------------------------------------------
; KEYSTONE and the per-quantum bound

(defthm fn-ovw-run-is-over-range-cat
  (and (equal (car (fn-nntp-over-range-cat session v token legacyp fn-arena fn-cat))
              session)
       (equal (fn-ovw-octets session v token legacyp w fn-arena fn-cat)
              (fn-served-reply-octets
               (cdr (fn-nntp-over-range-cat session v token legacyp fn-arena fn-cat)))))
  :hints (("Goal" :in-theory (union-theories '(fn-ovw-octets-is-spec fn-ovw-over-range-cat-is-spec)
                                             (theory 'minimal-theory)))))

(local
 (defthm fn-ovw-len-range-aux
   (<= (len (fn-cnx-range-aux group k top v fn-cat))
       (nfix (- (+ 1 (nfix top)) (nfix k))))
   :rule-classes :linear
   :hints (("Goal" :induct (fn-cnx-range-aux group k top v fn-cat)
            :in-theory (e/d (fn-cnx-range-aux) (fn-cnx-view-seq))))))

(local
 (defthm fn-ovw-len-range-keep
   (<= (len (fn-scat-range-keep group seqs fn-cat)) (len seqs))
   :rule-classes :linear
   :hints (("Goal" :induct (fn-scat-range-keep group seqs fn-cat)
            :in-theory (enable fn-scat-range-keep)))))

(local
 (defthm fn-ovw-len-nov-lines
   (<= (len (fn-nov-lines-for-numbers-cat group numbers v fn-arena fn-cat)) (len numbers))
   :rule-classes :linear
   :hints (("Goal" :induct (fn-nov-lines-for-numbers-cat group numbers v fn-arena fn-cat)
            :in-theory (e/d (fn-nov-lines-for-numbers-cat)
                            (fn-scat-available-article fn-nov-overview fn-nov-okp fn-nov-line
                             fn-nntp-article-tombstonep))))))

; A quantum's work: the window it probes is at most W numbers (at least one),
; so it builds at most W NOV lines, whatever the range.
(local
 (defthm fn-ovw-len-lines
   (<= (len (fn-ovw-lines group k hi v fn-arena fn-cat))
       (nfix (- (+ 1 (nfix hi)) (nfix k))))
   :rule-classes :linear
   :hints (("Goal" :in-theory (e/d (fn-ovw-lines)
                                   (fn-cnx-range-aux fn-scat-range-keep fn-nov-lines-for-numbers-cat
                                    fn-ovw-len-range-aux fn-ovw-len-range-keep fn-ovw-len-nov-lines))
            :use ((:instance fn-ovw-len-range-aux (top hi))
                  (:instance fn-ovw-len-range-keep (seqs (fn-cnx-range-aux group k hi v fn-cat)))
                  (:instance fn-ovw-len-nov-lines
                             (numbers (fn-scat-range-keep group (fn-cnx-range-aux group k hi v fn-cat)
                                                          fn-cat))))))))

(defthm fn-ovw-step-window-at-most-w
  (let* ((k (nfix (nth 1 cur))) (top (nfix (nth 2 cur))) (hi (fn-ovw-hi k top w)))
    (and (<= (- (+ 1 hi) k) (if (posp w) w 1))
         (<= (len (fn-ovw-lines (nth 0 cur) k hi (nth 3 cur) fn-arena fn-cat))
             (if (posp w) w 1))))
  :hints (("Goal" :in-theory (e/d (fn-ovw-hi) (fn-ovw-lines fn-ovw-len-lines))
           :use ((:instance fn-ovw-len-lines (group (nth 0 cur)) (k (nfix (nth 1 cur)))
                            (hi (fn-ovw-hi (nfix (nth 1 cur)) (nfix (nth 2 cur)) w))
                            (v (nth 3 cur)))))))

; -----------------------------------------------------------------------------
; FRAME: a cursor pinned at V resumes over a catalog that grew or withdrew
; rows at later versions

(local
 (defthm fn-ovw-range-aux-is-walk
   (implies (fn-cnx-freshp fn-cat)
            (equal (fn-cnx-range-aux group k top v fn-cat)
                   (fn-cnx-walk-range group k top v fn-cat)))
   :hints (("Goal" :induct (fn-cnx-walk-range group k top v fn-cat)
            :in-theory (e/d (fn-cnx-range-aux fn-cnx-walk-range)
                            (fn-cnx-view-seq fn-cat-view-number-find fn-cnx-freshp))
            :expand ((fn-cnx-range-aux group k top v fn-cat))))))

; A window's lines are a function of the view's articles and the arena
; alone: the served fold's lines over the numbers K..HI of the view.
(defthm fn-ovw-lines-is-view
  (implies (and (fn-cnx-freshp fn-cat) group)
           (equal (fn-ovw-lines group k hi v fn-arena fn-cat)
                  (fn-nov-lines-for-numbers
                   group
                   (fn-scat-kf group k hi (fn-cat-view-articles v fn-arena fn-cat))
                   (fn-cat-view-articles v fn-arena fn-cat) fn-arena)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-ovw-lines)
                           (fn-cnx-range-aux fn-cnx-walk-range fn-scat-range-keep fn-scat-kf
                            fn-nov-lines-for-numbers-cat fn-nov-lines-for-numbers
                            fn-cat-view-articles fn-cnx-freshp))
           :use ((:instance fn-scat-range-keep-of-walk (top hi))))))

; FRAME: a commit (the catalog grows past the view) or a withdrawal marked
; at a later version leaves a pinned view's window unchanged -- what lets a
; cursor pinned at V resume after owner transitions.
(defthm fn-ovw-lines-of-commit-pinned
  (implies (and (fn-cnx-freshp fn-cat) group
                (natp v) (<= v (fn-cat-count fn-cat)))
           (equal (fn-ovw-lines group k hi v fn-arena (fn-cat-commit h fn-cat))
                  (fn-ovw-lines group k hi v fn-arena fn-cat)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-ovw-lines fn-cat-view-articles fn-scat-kf fn-cat-commit-is-append fn-cat-view-articles-of-commit-pinned
                               fn-nov-lines-for-numbers fn-cnx-freshp fn-ovw-lines-is-view)
           :use ((:instance fn-ovw-lines-is-view)
                 (:instance fn-ovw-lines-is-view (fn-cat (fn-cat-commit h fn-cat)))
                 (:instance fn-cnx-freshp-of-commit (c fn-cat))
                 (:instance fn-cat-view-articles-of-commit-pinned)))))

(defthm fn-ovw-lines-of-withdraw-pinned
  (implies (and (fn-cnx-freshp fn-cat) group
                (natp v) (<= v (fn-cat-count fn-cat))
                (natp target) (< target (fn-cat-count fn-cat)))
           (equal (fn-ovw-lines group k hi v fn-arena (fn-cat-withdraw target by fn-cat))
                  (fn-ovw-lines group k hi v fn-arena fn-cat)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-ovw-lines fn-cat-view-articles fn-scat-kf fn-cat-withdraw-is-mark fn-cat-view-articles-of-withdraw-pinned
                               fn-nov-lines-for-numbers fn-cnx-freshp fn-ovw-lines-is-view)
           :use ((:instance fn-ovw-lines-is-view)
                 (:instance fn-ovw-lines-is-view (fn-cat (fn-cat-withdraw target by fn-cat)))
                 (:instance fn-cnx-freshp-of-withdraw (c fn-cat))
                 (:instance fn-cat-view-articles-of-withdraw-pinned)))))

; A quantum after a commit or a later withdrawal answers what it would have
; answered before it, for a cursor pinned at or below the catalog's count.
(defthm fn-ovw-step-of-commit-pinned
  (implies (and (fn-cnx-freshp fn-cat) (nth 0 cur)
                (natp (nth 3 cur)) (<= (nth 3 cur) (fn-cat-count fn-cat)))
           (equal (fn-ovw-step cur w fn-arena (fn-cat-commit h fn-cat))
                  (fn-ovw-step cur w fn-arena fn-cat)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-ovw-step)
                           (fn-ovw-lines fn-cat-commit-is-append fn-nntp-stuff-lines fn-ovw-status
                            fn-cnx-freshp fn-cat-count-is-len)))))

(defthm fn-ovw-step-of-withdraw-pinned
  (implies (and (fn-cnx-freshp fn-cat) (nth 0 cur)
                (natp (nth 3 cur)) (<= (nth 3 cur) (fn-cat-count fn-cat))
                (natp target) (< target (fn-cat-count fn-cat)))
           (equal (fn-ovw-step cur w fn-arena (fn-cat-withdraw target by fn-cat))
                  (fn-ovw-step cur w fn-arena fn-cat)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-ovw-step)
                           (fn-ovw-lines fn-cat-withdraw-is-mark fn-nntp-stuff-lines fn-ovw-status
                            fn-cnx-freshp fn-cat-count-is-len)))))
