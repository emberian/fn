; over-window.lisp -- OVER/XOVER of a range answered in bounded windows
; (lanes join-f2-10 and join-f2-12, 2026-09-29; PKT-733 (4), D27).
;
; The served step answers an OVER/XOVER range with a CURSOR (books/served-
; catalog.lisp fn-nntp-over-range-ovw: fn-ovw-start parses and clamps the
; range once, no number probed, and the step's one effect is (:over-cursor
; CUR)).  This book is the host's continuation and its proof:
;
;   fn-ovw-step (cursor w fn-arena fn-cat) -> (mv octets cursor')
;     one quantum: at most W numbers probed and at most W NOV lines built.
;     The status line is decided lazily: 224 before the first line, or 423
;     (420 for XOVER) once the range is exhausted with no line; the
;     terminating dot follows the last window of a 224 reply.
;   fn-ovw-run: the steps until the cursor is NIL (the list model).
;
; KEYSTONE fn-ovw-run-is-over-range-cat: for every W >= 1, the octets of the
; start followed by the steps until the cursor is NIL are exactly the reply
; octets of fn-nntp-over-range-cat (the unbounded reader) over the same
; catalog and view: the windowed reply is never truncated.
; fn-ovw-cursor-effect-expands-to-run: the served arm's effects, expanded
; (fn-ovw-expand, what the chain equations of books/served-catalog-chain.lisp
; are stated modulo), are the one reply effect carrying that run's octets,
; for every W; fn-ovw-run-of-start-is-cursor-octets is the same fact on the
; cursor the arm emits (what the host's continuation runs).  The progress
; measure fn-ovw-remaining strictly decreases at every step of a live cursor
; (fn-ovw-step-progresses), and a step's probes are the window's
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
(include-book "cold-line-quanta")

(local (in-theory (disable (tau-system))))

; -----------------------------------------------------------------------------
; The cursor and one window

(defun fn-ovw-remaining (cur)
  (declare (xargs :guard (true-listp cur)))
  (if (consp cur)
      (nfix (- (+ 1 (nfix (nth 2 cur))) (nfix (nth 1 cur))))
    0))

(defun fn-ovw-hi (k top w)
  (declare (xargs :guard t))
  (min (nfix top) (+ (nfix k) (if (posp w) w 1) -1)))

; -----------------------------------------------------------------------------
; The header cursor's quantum (lane cold-line; books/served-catalog.lisp
; fn-ovw-hdr-cursor).  A source whose field is in the overview column (and
; is not the compatibility arm's Xref) reads no payload on a row whose column
; is decided; any other source reads the article's payload for each number,
; so its window is at most fn-clq-payload-quantum numbers: one quantum's
; reads fit the realizer's cache with margin.

(defun fn-ovw-hdr-free-sourcep (src)
  (declare (xargs :guard t))
  (and (not (nth 4 src)) (fn-scol-field-index (nth 2 src)) t))

(defun fn-ovw-hdr-quantum (src w)
  (declare (xargs :guard t))
  (if (fn-ovw-hdr-free-sourcep src)
      (if (posp w) w 1)
    (min (if (posp w) w 1) (fn-clq-payload-quantum))))

(defthm fn-ovw-hdr-quantum-posp
  (posp (fn-ovw-hdr-quantum src w))
  :rule-classes :type-prescription)

(defun fn-ovw-hdr-step (cur w fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (fn-ovw-cursorp cur)
                  :verify-guards nil))
  (let* ((group (nth 0 cur)) (k (nfix (nth 1 cur))) (top (nfix (nth 2 cur)))
         (v (nth 3 cur)) (owedp (nth 5 cur)) (src (nth 7 cur))
         (hi (fn-ovw-hi k top (fn-ovw-hdr-quantum src w)))
         (lines (fn-ovw-hdr-lines group k hi src v fn-arena fn-cat))
         (owed2 (and owedp (not (consp lines))))
         (donep (<= top hi)))
    (mv (append (if (and owedp (consp lines)) (fn-ovw-hdr-status src) nil)
                (fn-nntp-stuff-lines lines)
                (if donep
                    (if owed2 (fn-ovw-hdr-empty src) '(46 13 10))
                  nil))
        (if donep nil (fn-ovw-hdr-cursor group (+ 1 hi) top v owed2 src)))))

; One quantum: the window K..HI (at most W numbers).
(defun fn-ovw-step (cur w fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  ;; No fact about the whole catalog (Codex r67 F1): a quantum
                  ;; reads the rows of its own window, each through a reader
                  ;; that checks its handle, so the guard a guard-checked host
                  ;; call evaluates per quantum is O(1), not a walk of N rows.
                  :guard (fn-ovw-cursorp cur)
                  :verify-guards nil))
  (if (nth 7 cur)
      (fn-ovw-hdr-step cur w fn-arena fn-cat)
    (let* ((group (nth 0 cur)) (k (nfix (nth 1 cur))) (top (nfix (nth 2 cur)))
           (v (nth 3 cur)) (legacyp (nth 4 cur)) (owedp (nth 5 cur)) (server (nth 6 cur))
           (hi (fn-ovw-hi k top w))
           (lines (fn-ovw-lines group k hi server v fn-arena fn-cat))
           (owed2 (and owedp (not (consp lines))))
           (donep (<= top hi)))
      (mv (append (if (and owedp (consp lines))
                      (fn-ovw-status (fn-proto-text * :overview))
                    nil)
                  (fn-nntp-stuff-lines lines)
                  (if donep
                      (if owed2 (fn-ovw-status (fn-ovw-empty-text legacyp)) '(46 13 10))
                    nil))
          (if donep nil (fn-ovw-cursor group (+ 1 hi) top v legacyp owed2 server))))))

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

(defun fn-ovw-octets (session v token legacyp server w fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (mv-let (octets cursor)
    (fn-ovw-start session v token legacyp server fn-cat)
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

(defthm fn-ovw-nov-served-lines-of-append
  (equal (fn-nov-served-lines-for-numbers-cat group (append a b) server v fn-arena fn-cat)
         (append (fn-nov-served-lines-for-numbers-cat group a server v fn-arena fn-cat)
                 (fn-nov-served-lines-for-numbers-cat group b server v fn-arena fn-cat)))
  :hints (("Goal" :induct (fn-nov-served-lines-for-numbers-cat group a server v fn-arena fn-cat)
           :in-theory (e/d (fn-nov-served-lines-for-numbers-cat)
                           (fn-scat-available-article fn-scol-overview-of fn-nov-okp
                            fn-nov-served-line fn-scol-tombstonep)))))

(defthm fn-ovw-stuff-lines-of-append
  (equal (fn-nntp-stuff-lines (append a b))
         (append (fn-nntp-stuff-lines a) (fn-nntp-stuff-lines b)))
  :hints (("Goal" :induct (fn-nntp-stuff-lines a)
           :in-theory (e/d (fn-nntp-stuff-lines) (fn-wire-stuff-line fn-nntp-crlf)))))

(defthm fn-ovw-lines-split
  (implies (and (natp k) (natp hi) (natp top) (<= k hi) (< hi top))
           (equal (fn-ovw-lines group k top server v fn-arena fn-cat)
                  (append (fn-ovw-lines group k hi server v fn-arena fn-cat)
                          (fn-ovw-lines group (+ 1 hi) top server v fn-arena fn-cat))))
  :hints (("Goal" :in-theory (e/d (fn-ovw-lines) (fn-cnx-range-aux
                                                  fn-scat-range-keep fn-nov-lines-for-numbers-cat
                                                  fn-nov-served-lines-for-numbers-cat))
           :use ((:instance fn-cnxw-range-is-windows (b (+ 1 hi)))))))

(local
 (defun fn-ovw-ind (group k top v legacyp owedp server w fn-arena fn-cat)
   (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil
                   :measure (nfix (- (+ 1 (nfix top)) (nfix k)))))
   (if (and (natp k) (natp top) (<= k top) (< (fn-ovw-hi k top w) top))
       (fn-ovw-ind group (+ 1 (fn-ovw-hi k top w)) top v legacyp
                   (and owedp (not (consp (fn-ovw-lines group k (fn-ovw-hi k top w) server v
                                                        fn-arena fn-cat))))
                   server w fn-arena fn-cat)
     (list group k top v legacyp owedp server w))))

(local
 (defthm fn-ovw-lines-empty-above
   (implies (and (natp k) (natp top) (< top k))
            (equal (fn-ovw-lines group k top server v fn-arena fn-cat) nil))
   :hints (("Goal" :in-theory (enable fn-ovw-lines)))))

(local
 (defthm fn-ovw-cursor-consp
   (consp (fn-ovw-cursor group k top v legacyp owedp server))
   :hints (("Goal" :in-theory (enable fn-ovw-cursor)))))

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


(local (in-theory (disable fn-ovw-hi)))

(defthm fn-ovw-run-is-reply
  (implies (and (natp k) (natp top))
           (equal (fn-ovw-run (fn-ovw-cursor group k top v legacyp owedp server) w fn-arena fn-cat)
                  (fn-ovw-reply (fn-ovw-lines group k top server v fn-arena fn-cat) legacyp owedp)))
  :hints (("Goal" :induct (fn-ovw-ind group k top v legacyp owedp server w fn-arena fn-cat)
           :in-theory (e/d (fn-ovw-step fn-ovw-reply)
                           (fn-ovw-run fn-ovw-lines fn-nntp-stuff-lines fn-ovw-status fn-ovw-empty-text
                            fn-ovw-lines-split))
           :expand ((:free (owedp) (fn-ovw-run (fn-ovw-cursor group k top v legacyp owedp server) w fn-arena fn-cat))))
          ("Subgoal *1/1" :expand ((:free (owedp) (fn-ovw-run (fn-ovw-cursor group k top v legacyp owedp server) w fn-arena fn-cat)))
                          :use ((:instance fn-ovw-lines-split (hi (fn-ovw-hi k top w)))))))

(defthm fn-ovw-octets-is-spec
  (equal (fn-ovw-octets session v token legacyp server w fn-arena fn-cat)
         (fn-ovw-spec session v token legacyp server fn-arena fn-cat))
  :hints (("Goal" :do-not-induct t
           :expand ((fn-ovw-run nil w fn-arena fn-cat))
           :in-theory (union-theories '(fn-ovw-octets fn-ovw-start fn-ovw-spec fn-ovw-run-is-reply
                                        natp-compound-recognizer nfix min (:e fn-ovw-status) append-to-nil binary-append
                                        (:e fn-proto-text-of) (:e fn-proto-shared-text))
                                      (theory 'minimal-theory)))))

(local
 (defthm fn-ovw-spec-true-listp
   (true-listp (fn-ovw-spec session v token legacyp server fn-arena fn-cat))
   :hints (("Goal" :in-theory (e/d (fn-ovw-spec fn-ovw-reply fn-ovw-status fn-ovw-empty-text)
                                   (fn-ovw-lines fn-nntp-stuff-lines fn-nntp-string-octets))))))

(local
 (defthm fn-ovw-reply-octets-of-one-listp
   (implies (true-listp x)
            (equal (fn-served-reply-octets (list (fn-nntp-reply-effect x))) x))
   :hints (("Goal" :in-theory (enable fn-served-reply-octets fn-nntp-reply-effect)))))

; -----------------------------------------------------------------------------
; KEYSTONE and the per-quantum bound

(defthm fn-ovw-run-is-over-range-cat
  (and (equal (car (fn-nntp-over-range-cat session v token legacyp fn-arena fn-cat))
              session)
       (equal (fn-ovw-octets session v token legacyp nil w fn-arena fn-cat)
              (fn-served-reply-octets
               (cdr (fn-nntp-over-range-cat session v token legacyp fn-arena fn-cat)))))
  :hints (("Goal" :in-theory (union-theories '(fn-ovw-octets-is-spec fn-ovw-over-range-cat-is-spec
                                               fn-ovw-reply-octets-of-one-listp fn-ovw-spec-true-listp)
                                             (theory 'minimal-theory)))))

; KEYSTONE (a node with an Xref server name, which every configured node
; has): the windowed run at SERVER is the served unbounded reader's reply,
; for every W >= 1.
(defthm fn-ovw-run-is-over-range-served-cat
  (implies server
           (and (equal (car (fn-nntp-over-range-served-cat session v token legacyp server
                                                           fn-arena fn-cat))
                       session)
                (equal (fn-ovw-octets session v token legacyp server w fn-arena fn-cat)
                       (fn-served-reply-octets
                        (cdr (fn-nntp-over-range-served-cat session v token legacyp server
                                                            fn-arena fn-cat))))))
  :hints (("Goal" :in-theory (union-theories '(fn-ovw-octets-is-spec
                                               fn-ovw-over-range-served-cat-is-spec
                                               fn-ovw-reply-octets-of-one-listp fn-ovw-spec-true-listp)
                                             (theory 'minimal-theory)))))

; The served arm's effects, expanded, carry the windowed run's octets, for
; every W (books/served-catalog.lisp fn-nntp-over-range-ovw-expands-to-over-
; range-cat with the keystone).
(defthm fn-ovw-cursor-effect-expands-to-run
  (equal (fn-ovw-expand (cdr (fn-nntp-over-range-ovw session v token legacyp server fn-cat))
                        fn-arena fn-cat)
         (list (fn-nntp-reply-effect (fn-ovw-octets session v token legacyp server w fn-arena fn-cat))))
  :hints (("Goal" :in-theory (union-theories '(fn-nntp-over-range-ovw-expands-to-spec
                                               fn-ovw-octets-is-spec)
                                             (theory 'minimal-theory)))))

; The cursor the arm emits (fn-ovw-start's, its status line owed) runs to
; exactly the reply the cursor effect stands for, for every W: the host's
; continuation writes what the expansion says.
(defthm fn-ovw-run-of-start-is-cursor-octets
  (implies (mv-nth 1 (fn-ovw-start session v token legacyp server fn-cat))
           (equal (fn-ovw-run (mv-nth 1 (fn-ovw-start session v token legacyp server fn-cat)) w fn-arena fn-cat)
                  (fn-ovw-cursor-octets (mv-nth 1 (fn-ovw-start session v token legacyp server fn-cat))
                                        fn-arena fn-cat)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-ovw-start fn-ovw-cursor-octets fn-ovw-run-is-reply)
                           (fn-ovw-run fn-ovw-lines fn-ovw-reply fn-nntp-parse-range fn-cat-group-next)))))

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

(local
 (defthm fn-ovw-len-nov-served-lines
   (<= (len (fn-nov-served-lines-for-numbers-cat group numbers server v fn-arena fn-cat))
       (len numbers))
   :rule-classes :linear
   :hints (("Goal" :induct (fn-nov-served-lines-for-numbers-cat group numbers server v fn-arena fn-cat)
            :in-theory (e/d (fn-nov-served-lines-for-numbers-cat)
                            (fn-scat-available-article fn-scol-overview-of fn-nov-okp
                             fn-nov-served-line fn-scol-tombstonep))))))

; A quantum's work: the window it probes is at most W numbers (at least one),
; so it builds at most W NOV lines, whatever the range.
(local
 (defthm fn-ovw-len-lines
   (<= (len (fn-ovw-lines group k hi server v fn-arena fn-cat))
       (nfix (- (+ 1 (nfix hi)) (nfix k))))
   :rule-classes :linear
   :hints (("Goal" :in-theory (e/d (fn-ovw-lines)
                                   (fn-cnx-range-aux fn-scat-range-keep fn-nov-lines-for-numbers-cat
                                    fn-nov-served-lines-for-numbers-cat
                                    fn-ovw-len-range-aux fn-ovw-len-range-keep fn-ovw-len-nov-lines
                                    fn-ovw-len-nov-served-lines))
            :use ((:instance fn-ovw-len-range-aux (top hi))
                  (:instance fn-ovw-len-range-keep (seqs (fn-cnx-range-aux group k hi v fn-cat)))
                  (:instance fn-ovw-len-nov-lines
                             (numbers (fn-scat-range-keep group (fn-cnx-range-aux group k hi v fn-cat)
                                                          fn-cat)))
                  (:instance fn-ovw-len-nov-served-lines
                             (numbers (fn-scat-range-keep group (fn-cnx-range-aux group k hi v fn-cat)
                                                          fn-cat))))))))

(defthm fn-ovw-step-window-at-most-w
  (let* ((k (nfix (nth 1 cur))) (top (nfix (nth 2 cur))) (hi (fn-ovw-hi k top w)))
    (and (<= (- (+ 1 hi) k) (if (posp w) w 1))
         (<= (len (fn-ovw-lines (nth 0 cur) k hi (nth 6 cur) (nth 3 cur) fn-arena fn-cat))
             (if (posp w) w 1))))
  :hints (("Goal" :in-theory (e/d (fn-ovw-hi) (fn-ovw-lines fn-ovw-len-lines))
           :use ((:instance fn-ovw-len-lines (group (nth 0 cur)) (k (nfix (nth 1 cur)))
                            (hi (fn-ovw-hi (nfix (nth 1 cur)) (nfix (nth 2 cur)) w))
                            (server (nth 6 cur)) (v (nth 3 cur)))))))

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
; alone: the reference fold's lines over the numbers K..HI of the view (the
; plain fold with no server name; the served fold, Xref field included, with
; one, where the overview column is the bytes' (fn-scol-okp) and the view's
; articles are articles of some configured groups).
(defun fn-ovw-view-lines (group k hi server articles fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (if server
      (fn-nov-served-lines-numbered
       (fn-scat-kf group k hi articles)
       (fn-gidx-bucket-numbers group (fn-gidx-build articles))
       (fn-midx-build articles) server fn-arena)
    (fn-nov-lines-for-numbers group (fn-scat-kf group k hi articles) articles fn-arena)))

; What the served lines need beyond a fresh catalog.
(defmacro fn-ovw-served-okp (server configured v fn-arena fn-cat)
  `(implies ,server
            (and (fn-scol-okp ,fn-arena ,fn-cat)
                 (fn-article-listp ,configured (fn-cat-view-articles ,v ,fn-arena ,fn-cat)))))

(defthm fn-ovw-lines-is-view
  (implies (and (fn-cnx-freshp fn-cat) group
                (fn-ovw-served-okp server configured v fn-arena fn-cat))
           (equal (fn-ovw-lines group k hi server v fn-arena fn-cat)
                  (fn-ovw-view-lines group k hi server
                                     (fn-cat-view-articles v fn-arena fn-cat) fn-arena)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-ovw-lines fn-nov-served-lines-for-numbers-cat-is-col
                            fn-nov-served-lines-numbered-col-is-served)
                           (fn-cnx-range-aux fn-cnx-walk-range fn-scat-range-keep fn-scat-kf
                            fn-nov-lines-for-numbers-cat fn-nov-lines-for-numbers
                            fn-nov-served-lines-for-numbers-cat fn-nov-served-lines-numbered
                            fn-nov-served-lines-numbered-col fn-gidx-build fn-midx-build
                            fn-gidx-bucket-numbers fn-scol-okp fn-article-listp
                            fn-cat-view-articles fn-cnx-freshp))
           :use ((:instance fn-scat-range-keep-of-walk (top hi))))))

; FRAME: a commit (the catalog grows past the view) or a withdrawal marked
; at a later version leaves a pinned view's window unchanged -- what lets a
; cursor pinned at V resume after owner transitions.  With a server name the
; committed row's overview column must be the bytes' (fn-scol-row-okp, what
; every commit establishes: fn-scol-okp-of-commit).
(defthm fn-ovw-lines-of-commit-pinned
  (implies (and (fn-cnx-freshp fn-cat) group
                (natp v) (<= v (fn-cat-count fn-cat))
                (fn-ovw-served-okp server configured v fn-arena fn-cat)
                (implies server (fn-scol-row-okp h fn-arena)))
           (equal (fn-ovw-lines group k hi server v fn-arena (fn-cat-commit h fn-cat))
                  (fn-ovw-lines group k hi server v fn-arena fn-cat)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-ovw-lines fn-ovw-view-lines fn-cat-view-articles fn-scat-kf
                               fn-cat-commit-is-append fn-cat-view-articles-of-commit-pinned
                               fn-nov-lines-for-numbers fn-cnx-freshp fn-ovw-lines-is-view
                               fn-scol-okp fn-scol-row-okp fn-article-listp fn-scol-okp-of-commit)
           :use ((:instance fn-ovw-lines-is-view)
                 (:instance fn-ovw-lines-is-view (fn-cat (fn-cat-commit h fn-cat)))
                 (:instance fn-cnx-freshp-of-commit (c fn-cat))
                 (:instance fn-scol-okp-of-commit)
                 (:instance fn-cat-view-articles-of-commit-pinned)))))

(defthm fn-ovw-lines-of-withdraw-pinned
  (implies (and (fn-cnx-freshp fn-cat) group
                (natp v) (<= v (fn-cat-count fn-cat))
                (natp target) (< target (fn-cat-count fn-cat))
                (fn-ovw-served-okp server configured v fn-arena fn-cat))
           (equal (fn-ovw-lines group k hi server v fn-arena (fn-cat-withdraw target by fn-cat))
                  (fn-ovw-lines group k hi server v fn-arena fn-cat)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-ovw-lines fn-ovw-view-lines fn-cat-view-articles fn-scat-kf
                               fn-cat-withdraw-is-mark fn-cat-view-articles-of-withdraw-pinned
                               fn-nov-lines-for-numbers fn-cnx-freshp fn-ovw-lines-is-view
                               fn-scol-okp fn-article-listp fn-scol-okp-of-withdraw)
           :use ((:instance fn-ovw-lines-is-view)
                 (:instance fn-ovw-lines-is-view (fn-cat (fn-cat-withdraw target by fn-cat)))
                 (:instance fn-cnx-freshp-of-withdraw (c fn-cat))
                 (:instance fn-scol-okp-of-withdraw)
                 (:instance fn-cat-view-articles-of-withdraw-pinned)))))

; A quantum after a commit or a later withdrawal answers what it would have
; answered before it, for a cursor pinned at or below the catalog's count.
(defthm fn-ovw-step-of-commit-pinned
  (implies (and (fn-cnx-freshp fn-cat) (nth 0 cur) (not (nth 7 cur))
                (natp (nth 3 cur)) (<= (nth 3 cur) (fn-cat-count fn-cat))
                (fn-ovw-served-okp (nth 6 cur) configured (nth 3 cur) fn-arena fn-cat)
                (implies (nth 6 cur) (fn-scol-row-okp h fn-arena)))
           (equal (fn-ovw-step cur w fn-arena (fn-cat-commit h fn-cat))
                  (fn-ovw-step cur w fn-arena fn-cat)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-ovw-step)
                           (fn-ovw-lines fn-cat-commit-is-append fn-nntp-stuff-lines fn-ovw-status
                            fn-cnx-freshp fn-cat-count-is-len fn-scol-okp fn-scol-row-okp
                            fn-article-listp fn-cat-view-articles fn-ovw-lines-of-commit-pinned))
           :use ((:instance fn-ovw-lines-of-commit-pinned
                            (group (nth 0 cur)) (k (nfix (nth 1 cur)))
                            (hi (fn-ovw-hi (nfix (nth 1 cur)) (nfix (nth 2 cur)) w))
                            (server (nth 6 cur)) (v (nth 3 cur)))))))

(defthm fn-ovw-step-of-withdraw-pinned
  (implies (and (fn-cnx-freshp fn-cat) (nth 0 cur) (not (nth 7 cur))
                (natp (nth 3 cur)) (<= (nth 3 cur) (fn-cat-count fn-cat))
                (natp target) (< target (fn-cat-count fn-cat))
                (fn-ovw-served-okp (nth 6 cur) configured (nth 3 cur) fn-arena fn-cat))
           (equal (fn-ovw-step cur w fn-arena (fn-cat-withdraw target by fn-cat))
                  (fn-ovw-step cur w fn-arena fn-cat)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-ovw-step)
                           (fn-ovw-lines fn-cat-withdraw-is-mark fn-nntp-stuff-lines fn-ovw-status
                            fn-cnx-freshp fn-cat-count-is-len fn-scol-okp
                            fn-article-listp fn-cat-view-articles fn-ovw-lines-of-withdraw-pinned))
           :use ((:instance fn-ovw-lines-of-withdraw-pinned
                            (group (nth 0 cur)) (k (nfix (nth 1 cur)))
                            (hi (fn-ovw-hi (nfix (nth 1 cur)) (nfix (nth 2 cur)) w))
                            (server (nth 6 cur)) (v (nth 3 cur)))))))
