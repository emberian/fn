; served-catalog-chain.lisp -- the served read over the catalog (step 8 of the
; catalog slice; planning/evidence/catalog-slice-2026-09-26.md).
;
; The host's served read is host/owner-host.lisp fn-owner-chunk-span, which
; runs the carried chain fn-scar-ocfg-read-span -> ... -> fn-scar-dispatch-core
; -> fn-scar-auth-step-pinned -> ... -> fn-pix-archive-command-pinned
; (books/served-span, served-carried, peer-offer-indexed), a twin of the
; reference fn-nntp-archive-command-pinned that walks the pinned archive.
; This book is the same chain with the catalog stobjs carried down to the
; dispatcher, where the retrieval arms are books/served-catalog.lisp's
; fn-nntp-archive-command-cat: the article at a number is one probe of the
; number table and a range is the view's rows, never a walk of the archive.
;
; Each layer fn-scc-X mirrors its scar/pix layer text for text, with the
; catalog view V and the two stobjs added, and each theorem fn-scc-X-is-Y
; equates it to THAT layer (not the far reference) under one hypothesis, the
; -cat keystone's: the connection's pinned archive is the catalog's view at
; the connection's pin, with the pin correspondences and the number table
; fresh (fn-scc-catalogp).  The existing chain of -is- theorems then carries
; the equation to fn-ocfg-read-tls-prefix
; (fn-scc-ocfg-read-span-is-reference-under-ocl-relation).
;
; The view a pin names.  A connection pins the owner's view version, which is
; the count of RECORDS in the history (books/owner.lisp fn-own-refresh: (len
; (fn-sf-records ...))); a catalog view is a count of ROWS, one per article
; record.  Rows carry their record's sequence (fn-held-sequence) and stand in
; history order, so the view of a pinned version is the number of rows whose
; sequence is below it, found by bisection: O(log count) per command, no new
; state in the connection, the owner or the catalog (fn-scc-view-of).  That
; the bisection names the pinned archive's rows is the JOIN, the R-side
; equation of the catalog relation with the owner's view; it is the
; hypothesis fn-scc-catalogp carries, proved at the owner's entries in
; books/served-catalog-owner.lisp (step 8's R), not here.
;
; A read-restricted session (PRF-222, fn-auth-access-read) is served the
; RESTRICTED archive and index by the reference walks: the catalog holds the
; whole view and knows no access rule, so the -cat arms would answer with
; articles the rule hides.  fn-scc-auth-delegate splits there; an unrestricted
; session's view is its archive by definition (fn-auth-view-archive).
;
; Guards.  fn-nntp-archive-command-cat's guard names fn-cat-handles-inp over
; the whole catalog (every row's payload handle is inside the arena); it is
; part of R (books/catalog-relation.lisp fn-cat-history-relation) and so a
; proof obligation the entries discharge, never a served-path check: the host
; calls these functions from :program-mode entries, and ACL2 runs a
; guard-verified callee raw there (measured 2026-09-27, the record's step-8
; section: a 200M-step guard costs 0.90 s at the top level and 0.00 s through
; a :program entry with or without a stobj update).

(in-package "ACL2")

(include-book "served-span")
(include-book "served-catalog")

; -----------------------------------------------------------------------------
; The view a pinned version names: rows whose record sequence is below it.

; The midpoint of [lo, hi): in it, so the bisection halves the interval.
(defun fn-scc-mid (lo hi)
  (declare (xargs :guard (and (natp lo) (natp hi) (<= lo hi))))
  (+ lo (nonnegative-integer-quotient (- hi lo) 2)))

; niq-bounds is rational (niq <= i/2); the integer form closes the bisection.
(local (defthm fn-scc-twice-niq-2
  (implies (natp i) (<= (* 2 (nonnegative-integer-quotient i 2)) i))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance niq-bounds (i i) (j 2)))))))

(defthm fn-scc-mid-bounds
  (implies (and (natp lo) (natp hi) (< lo hi))
           (and (<= lo (fn-scc-mid lo hi))
                (< (fn-scc-mid lo hi) hi)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-scc-mid)
           :use ((:instance fn-scc-twice-niq-2 (i (- hi lo)))))))

(defthm natp-of-fn-scc-mid
  (implies (and (natp lo) (natp hi) (<= lo hi))
           (natp (fn-scc-mid lo hi)))
  :rule-classes :type-prescription)

(in-theory (disable fn-scc-mid))

(defun fn-scc-seq-bound (lo hi version fn-cat)
  (declare (xargs :stobjs fn-cat
                  :guard (and (natp lo) (natp hi) (<= lo hi)
                              (<= hi (fn-cat-count fn-cat)) (natp version))
                  :measure (nfix (- hi lo))
                  :verify-guards nil))
  (if (or (not (natp lo)) (not (natp hi)) (>= lo hi))
      (nfix lo)
    (let ((mid (fn-scc-mid lo hi)))
      ;; nfix: the identity on a row (fn-held-sequence is a uint64 under
      ;; fn-held-p); it keeps the probe's guard at the row's existence.
      (if (< (nfix (fn-held-sequence (fn-cat-at mid fn-cat))) version)
          (fn-scc-seq-bound (+ mid 1) hi version fn-cat)
        (fn-scc-seq-bound lo mid version fn-cat)))))

(defthm natp-of-fn-scc-seq-bound
  (natp (fn-scc-seq-bound lo hi version fn-cat))
  :rule-classes (:rewrite :type-prescription))

(defthm fn-scc-seq-bound-below-hi
  (implies (and (natp lo) (natp hi) (<= lo hi))
           (<= (fn-scc-seq-bound lo hi version fn-cat) hi))
  :rule-classes (:rewrite :linear))

(verify-guards fn-scc-seq-bound)

(defun fn-scc-view-of (version fn-cat)
  (declare (xargs :stobjs fn-cat :guard t))
  (fn-scc-seq-bound 0 (fn-cat-count fn-cat) (nfix version) fn-cat))

(defthm natp-of-fn-scc-view-of
  (natp (fn-scc-view-of version fn-cat))
  :rule-classes (:rewrite :type-prescription))

(in-theory (disable fn-scc-seq-bound fn-scc-view-of))

; -----------------------------------------------------------------------------
; The hypothesis: the -cat keystone's (fn-nntp-archive-command-cat-is-pinned).

(defun-nx fn-scc-catalogp (archive index v fn-arena fn-cat)
  (and (equal (fn-state-articles archive)
              (fn-cat-view-articles v fn-arena fn-cat))
       (fn-nntp-projectionp archive)
       (fn-gidx-pin-correspondencep index archive)
       (fn-midx-correspondencep (fn-gidx-pin-trie index)
                                (fn-state-articles archive))
       (fn-cnx-freshp fn-cat)))

; The same over a connection's fields, and over the live view a re-pin
; takes them from.
(defun-nx fn-scc-fields-catalogp (archive index group-index control pinned fn-arena fn-cat)
  (fn-scc-catalogp archive
                   (if group-index
                       (fn-gidx-pin-with-control index group-index control)
                     index)
                   (fn-scc-view-of (fn-served-pinned-version pinned) fn-cat)
                   fn-arena fn-cat))

(defun-nx fn-scc-conn-catalogp (conn fn-arena fn-cat)
  (fn-scc-fields-catalogp (fn-served-conn-archive conn) (fn-served-conn-index conn)
                          (fn-served-conn-group-index conn) (fn-served-conn-control conn)
                          (fn-served-conn-pinned conn) fn-arena fn-cat))

(defun-nx fn-scc-live-catalogp (live fn-arena fn-cat)
  (fn-scc-fields-catalogp (fn-served-live-archive live) (fn-served-live-index live)
                          (fn-served-live-buckets live) (fn-served-live-control live)
                          (fn-served-pinned-make (fn-served-live-version live)
                                                 (fn-served-live-frontier live) t)
                          fn-arena fn-cat))

; The connection and what it re-pins to.
(defun-nx fn-scc-conn-okp (conn fn-arena fn-cat)
  (and (fn-scc-conn-catalogp conn fn-arena fn-cat)
       (implies (fn-served-conn-live conn)
                (fn-scc-live-catalogp (fn-served-conn-live conn) fn-arena fn-cat))))

(defthm fn-scc-conn-catalogp-unfolds
  (equal (fn-scc-conn-catalogp conn fn-arena fn-cat)
         (fn-scc-catalogp (fn-served-conn-archive conn)
                          (fn-served-conn-pinned-index conn)
                          (fn-scc-view-of (fn-served-pinned-version (fn-served-conn-pinned conn))
                                          fn-cat)
                          fn-arena fn-cat))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scc-conn-catalogp fn-scc-fields-catalogp
                                fn-served-conn-pinned-index)
                              (theory 'minimal-theory)))))

(defthm fn-scc-conn-catalogp-of-make-conn-live
  (equal (fn-scc-conn-catalogp
          (fn-served-make-conn-live wire session archive config observation injection
                                    verdicts index buckets control pinned live)
          fn-arena fn-cat)
         (fn-scc-fields-catalogp archive index buckets control pinned fn-arena fn-cat))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scc-conn-catalogp fn-served-conn-fields-of-make-conn-live)
                              (theory 'minimal-theory)))))

(defthm fn-scc-conn-catalogp-of-with-wire
  (equal (fn-scc-conn-catalogp (fn-served-conn-with-wire conn wire) fn-arena fn-cat)
         (fn-scc-conn-catalogp conn fn-arena fn-cat))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scc-conn-catalogp fn-served-conn-fields-of-with-wire)
                              (theory 'minimal-theory)))))

(defthm fn-scc-conn-catalogp-of-repin
  (equal (fn-scc-conn-catalogp (fn-served-repin conn) fn-arena fn-cat)
         (if (fn-served-conn-live conn)
             (fn-scc-live-catalogp (fn-served-conn-live conn) fn-arena fn-cat)
           (fn-scc-conn-catalogp conn fn-arena fn-cat)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-served-repin fn-scc-live-catalogp
                                fn-scc-conn-catalogp-of-make-conn-live)
                              (theory 'minimal-theory)))))

(defthm fn-scc-conn-okp-of-repin
  (implies (fn-scc-conn-okp conn fn-arena fn-cat)
           (fn-scc-conn-okp (fn-served-repin conn) fn-arena fn-cat))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scc-conn-okp fn-scc-conn-catalogp-of-repin
                                fn-served-repin-keeps-live)
                              (theory 'minimal-theory)))))

(defthm fn-scc-conn-okp-of-with-wire
  (equal (fn-scc-conn-okp (fn-served-conn-with-wire conn wire) fn-arena fn-cat)
         (fn-scc-conn-okp conn fn-arena fn-cat))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scc-conn-okp fn-scc-conn-catalogp-of-with-wire
                                fn-served-conn-fields-of-with-wire)
                              (theory 'minimal-theory)))))

(in-theory (disable fn-scc-conn-catalogp-unfolds))

; -----------------------------------------------------------------------------
; The dispatcher lifted: fn-nntp-command-pinned with the -cat dispatcher.

(defun fn-scc-command (session archive index verdicts env tokens v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp v)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :verify-guards nil))
  (let ((keyword (mbe :logic (car tokens) :exec (fn-ag-car tokens)))
        (args (mbe :logic (cdr tokens) :exec (fn-ag-cdr tokens))))
    (if (not (fn-nntp-keyword-tokenp keyword))
        (fn-nntp-single session "501 syntax error")
      (if (not (fn-nntp-archive-keywordp keyword))
          (fn-nntp-session-command session env keyword args)
        (if (fn-nntp-session-projected session)
            (fn-nntp-archive-command-cat
             session archive index verdicts env keyword args v fn-arena fn-cat)
          (fn-nntp-single session "503 archive projection unavailable"))))))

(defthm fn-scc-command-is-command-pinned
  (implies (fn-scc-catalogp archive index v fn-arena fn-cat)
           (equal (fn-scc-command session archive index verdicts env tokens v fn-arena fn-cat)
                  (fn-nntp-command-pinned session archive index verdicts env tokens)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scc-command fn-nntp-command-pinned fn-scc-catalogp
                                fn-nntp-archive-command-cat-is-pinned)
                              (theory 'minimal-theory)))))

(verify-guards fn-scc-command)

(defun fn-scc-step (session archive index verdicts env wire-event v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp v)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :verify-guards nil))
  (if (or (not (fn-nntp-sessionp session))
          (not (equal (fn-nntp-session-openp session) t)))
      (fn-nntp-make-result session nil)
    (if (and (consp wire-event)
             (equal (car wire-event) :command)
             (consp (cdr wire-event))
             (null (cdr (cdr wire-event))))
        (let ((line (car (cdr wire-event))))
          (if (not (fn-nntp-command-inputp line))
              (fn-nntp-single session "501 syntax error")
            (let ((tokens (fn-nntp-tokenize line)))
              (if (and (consp tokens)
                       (fn-nntp-command-arguments-at-mostp tokens))
                  (fn-scc-command
                   session archive index verdicts env tokens v fn-arena fn-cat)
                (fn-nntp-single session "501 syntax error")))))
      (fn-nntp-single session "501 syntax error"))))

(defthm fn-scc-step-is-step-pinned
  (implies (fn-scc-catalogp archive index v fn-arena fn-cat)
           (equal (fn-scc-step session archive index verdicts env wire-event v fn-arena fn-cat)
                  (fn-nntp-step-pinned session archive index verdicts env wire-event)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scc-step fn-nntp-step-pinned
                                fn-scc-command-is-command-pinned)
                              (theory 'minimal-theory)))))

(verify-guards fn-scc-step)

(defun fn-scc-post-step
    (ps archive index verdicts config observation injection wire-event v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp v)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :verify-guards nil))
  (if (or (not (fn-post-sessionp ps)) (fn-post-session-awaiting ps))
      (fn-nntp-post-step ps archive config observation injection wire-event)
    (let ((r (fn-scc-step
              (fn-post-session-base ps) archive index verdicts
              (fn-post-reader-env config observation)
              wire-event v fn-arena fn-cat)))
      (if (fn-post-offeredp (fn-nntp-result-effects r))
          (if (fn-inj-config-allow config)
              (fn-post-make-result
               (fn-post-make-session (fn-nntp-result-session r) t)
               (fn-nntp-result-effects r) nil)
            (fn-post-make-result
             (fn-post-make-session (fn-nntp-result-session r) nil)
             (fn-post-single ps "440 posting not permitted") nil))
        (fn-post-make-result
         (fn-post-make-session (fn-nntp-result-session r) nil)
         (fn-nntp-result-effects r) nil)))))

(defthm fn-scc-post-step-is-post-step-pinned
  (implies (fn-scc-catalogp archive index v fn-arena fn-cat)
           (equal (fn-scc-post-step ps archive index verdicts config observation injection
                                    wire-event v fn-arena fn-cat)
                  (fn-nntp-post-step-pinned ps archive index verdicts config observation
                                            injection wire-event)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scc-post-step fn-nntp-post-step-pinned
                                fn-scc-step-is-step-pinned)
                              (theory 'minimal-theory)))))

(verify-guards fn-scc-post-step)

(defun fn-scc-peer-delegate
    (ps archive index verdicts config observation injection wire-event v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp v)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :verify-guards nil))
  (let ((r (fn-scc-post-step
            (fn-peer-session-base ps) archive index verdicts config
            observation injection wire-event v fn-arena fn-cat)))
    (fn-post-make-result (fn-peer-with-base ps (fn-post-result-session r))
                         (fn-post-result-effects r)
                         (fn-post-result-submission r))))

(defthm fn-scc-peer-delegate-is-peer-delegate-pinned
  (implies (fn-scc-catalogp archive index v fn-arena fn-cat)
           (equal (fn-scc-peer-delegate ps archive index verdicts config observation injection
                                        wire-event v fn-arena fn-cat)
                  (fn-pix-peer-delegate-pinned ps archive index verdicts config observation
                                               injection wire-event)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scc-peer-delegate fn-pix-peer-delegate-pinned
                                fn-scc-post-step-is-post-step-pinned
                                fn-pix-post-step-pinned-is-post-step-pinned)
                              (theory 'minimal-theory)))))

(verify-guards fn-scc-peer-delegate)

; -----------------------------------------------------------------------------
; The carried layers (books/served-carried.lisp) with the catalog.

(defun fn-scc-peer-step
    (ps live trie arts archive index verdicts config observation injection wire-event
        v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp v)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :verify-guards nil))
  (cond
   ((not (fn-scar-peer-sessionp ps live)) (fn-post-make-result ps nil nil))
   ((null (fn-peer-session-peer ps))
    (fn-scc-peer-delegate ps archive index verdicts config observation
                          injection wire-event v fn-arena fn-cat))
   (t (fn-pgc-peer-arm ps trie arts archive index verdicts config
                       observation injection wire-event))))

(defthm fn-scc-peer-step-is-scar-peer-step-pinned
  (implies (fn-scc-catalogp archive index v fn-arena fn-cat)
           (equal (fn-scc-peer-step ps live trie arts archive index verdicts config
                                    observation injection wire-event v fn-arena fn-cat)
                  (fn-scar-peer-step-pinned ps live trie arts archive index verdicts config
                                            observation injection wire-event)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scc-peer-step fn-scar-peer-step-pinned
                                fn-scc-peer-delegate-is-peer-delegate-pinned)
                              (theory 'minimal-theory)))))

(verify-guards fn-scc-peer-step
  :hints (("Goal" :in-theory (disable fn-scar-peer-sessionp))))

; An unrestricted session's views are its arguments (books/nntp-auth.lisp).
(local (defthm fn-scc-auth-view-archive-unrestricted
  (implies (not (fn-auth-access-read as config))
           (equal (fn-auth-view-archive as config archive) archive))
  :hints (("Goal" :in-theory (union-theories '(fn-auth-view-archive)
                                             (theory 'minimal-theory))))))

(local (defthm fn-scc-auth-view-index-unrestricted
  (implies (not (fn-auth-access-read as config))
           (equal (fn-auth-view-index as config archive index) index))
  :hints (("Goal" :in-theory (union-theories '(fn-auth-view-index)
                                             (theory 'minimal-theory))))))

(defun fn-scc-auth-delegate
    (as live trie arts archive index verdicts config observation injection wire-event
        v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp v)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :verify-guards nil))
  (if (fn-auth-access-read as config)
      ;; PRF-222: the rule's view of the archive, by the reference walks.
      (fn-scar-auth-delegate-pinned as live trie arts archive index verdicts config
                                    observation injection wire-event)
    (let ((r (fn-scc-peer-step
              (fn-auth-view-session as config) live trie arts archive index verdicts
              (fn-auth-view-config as (fn-auth-moderation-config as config) archive)
              observation injection wire-event v fn-arena fn-cat)))
      (fn-post-make-result (fn-auth-with-base as (fn-post-result-session r))
                           (fn-post-result-effects r)
                           (fn-post-result-submission r)))))

(defthm fn-scc-auth-delegate-is-scar-auth-delegate-pinned
  (implies (fn-scc-catalogp archive index v fn-arena fn-cat)
           (equal (fn-scc-auth-delegate as live trie arts archive index verdicts config
                                        observation injection wire-event v fn-arena fn-cat)
                  (fn-scar-auth-delegate-pinned as live trie arts archive index verdicts config
                                                observation injection wire-event)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scc-auth-delegate fn-scar-auth-delegate-pinned
                                fn-scc-peer-step-is-scar-peer-step-pinned
                                fn-scc-auth-view-archive-unrestricted
                                fn-scc-auth-view-index-unrestricted)
                              (theory 'minimal-theory)))))

(verify-guards fn-scc-auth-delegate)

(defun fn-scc-auth-step
    (as live trie arts archive index verdicts config observation injection wire-event
        v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp v)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :verify-guards nil))
  (cond
   ((not (fn-scar-auth-sessionp as live)) (fn-post-make-result as nil nil))
   ((fn-auth-tls-eventp wire-event) (fn-auth-tls-established as))
   ((and (fn-auth-redeem-eventp wire-event) (fn-auth-redeem-waitp as))
    (fn-auth-redeem-outcome as wire-event))
   ((fn-auth-session-handshakingp as) (fn-post-make-result as nil nil))
   ((and (consp wire-event)
         (equal (car wire-event) :command)
         (consp (cdr wire-event))
         (null (cdr (cdr wire-event)))
         (fn-nntp-command-inputp (car (cdr wire-event))))
    (let ((tokens (fn-nntp-tokenize (car (cdr wire-event)))))
      (if (and (consp tokens)
               (fn-nntp-keyword-tokenp (car tokens))
               (fn-nntp-command-arguments-at-mostp tokens))
          (let ((r (fn-auth-command as config (car tokens) (cdr tokens))))
            (if r r
              (fn-scc-auth-delegate as live trie arts archive index verdicts config
                                    observation injection wire-event v fn-arena fn-cat)))
        (fn-scc-auth-delegate as live trie arts archive index verdicts config observation
                              injection wire-event v fn-arena fn-cat))))
   (t (fn-scc-auth-delegate as live trie arts archive index verdicts config observation
                            injection wire-event v fn-arena fn-cat))))

(defthm fn-scc-auth-step-is-scar-auth-step-pinned
  (implies (fn-scc-catalogp archive index v fn-arena fn-cat)
           (equal (fn-scc-auth-step as live trie arts archive index verdicts config
                                    observation injection wire-event v fn-arena fn-cat)
                  (fn-scar-auth-step-pinned as live trie arts archive index verdicts config
                                            observation injection wire-event)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scc-auth-step fn-scar-auth-step-pinned
                                fn-scc-auth-delegate-is-scar-auth-delegate-pinned)
                              (theory 'minimal-theory)))))

(verify-guards fn-scc-auth-step)

(defun fn-scc-dispatch-core (conn event live trie arts fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)
                  :verify-guards nil))
  (let* ((v (fn-scc-view-of (fn-served-pinned-version (fn-served-conn-pinned conn)) fn-cat))
         (r (fn-scc-auth-step (fn-served-conn-session conn) live trie arts
                              (fn-served-conn-archive conn)
                              (fn-served-conn-pinned-index conn)
                              (fn-served-conn-verdicts conn)
                              (fn-served-conn-config conn)
                              (fn-served-conn-observation conn)
                              (fn-served-conn-injection conn)
                              event v fn-arena fn-cat))
         (effects (fn-post-result-effects r))
         (submission (fn-post-result-submission r))
         (wire (fn-served-conn-wire conn))
         (wire2 (if (fn-post-offeredp effects)
                    (fn-wire-result-state
                     (fn-wire-begin-article-with-line-limit
                      wire (fn-wire-article-line-limit wire)))
                  wire)))
    (fn-served-make-result
     (fn-served-make-conn-live wire2 (fn-post-result-session r)
                          (fn-served-conn-archive conn)
                          (fn-served-conn-config conn)
                          (fn-served-conn-observation conn)
                          (fn-served-conn-injection conn)
                          (fn-served-conn-verdicts conn)
                          (fn-served-conn-index conn)
                          (fn-served-conn-group-index conn) (fn-served-conn-control conn)
                          (fn-served-conn-pinned conn) (fn-served-conn-live conn))
     (mbe :logic (append effects
                         (if submission
                             (list (fn-served-submit-effect submission (fn-served-login (fn-served-conn-session conn))
                                (fn-served-account (fn-served-conn-session conn))))
                           nil))
          :exec (fn-ag-append effects
                              (if submission
                                  (list (fn-served-submit-effect submission (fn-served-login (fn-served-conn-session conn))
                                (fn-served-account (fn-served-conn-session conn))))
                                nil))))))

(defthm fn-scc-dispatch-core-is-scar-dispatch-core
  (implies (fn-scc-conn-catalogp conn fn-arena fn-cat)
           (equal (fn-scc-dispatch-core conn event live trie arts fn-arena fn-cat)
                  (fn-scar-dispatch-core conn event live trie arts)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scc-dispatch-core fn-scar-dispatch-core
                                fn-scc-conn-catalogp-unfolds
                                fn-scc-auth-step-is-scar-auth-step-pinned)
                              (theory 'minimal-theory)))))

(verify-guards fn-scc-dispatch-core)

; The step keeps every field the hypothesis reads, and the live view.
(defthm fn-scc-conn-okp-of-scar-dispatch-core
  (implies (fn-scc-conn-okp conn fn-arena fn-cat)
           (fn-scc-conn-okp (fn-served-result-conn (fn-scar-dispatch-core conn event live trie arts))
                            fn-arena fn-cat))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scar-dispatch-core fn-scc-conn-okp fn-scc-conn-catalogp
                                fn-served-result-conn-of-fn-served-make-result
                                fn-served-conn-fields-of-make-conn-live)
                              (theory 'minimal-theory)))))

(defun fn-scc-dispatch (conn event live trie arts fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)
                  :verify-guards nil))
  (if (fn-served-advance-eventp event)
      (let ((r (fn-scc-dispatch-core (fn-served-repin conn) event live trie arts fn-arena fn-cat)))
        (if (fn-served-selectedp (fn-served-result-effects r))
            r
          (fn-served-make-result
           (fn-served-conn-with-wire conn (fn-served-conn-wire (fn-served-result-conn r)))
           (fn-served-result-effects r))))
    (fn-scc-dispatch-core conn event live trie arts fn-arena fn-cat)))

(defthm fn-scc-dispatch-is-scar-dispatch
  (implies (fn-scc-conn-okp conn fn-arena fn-cat)
           (equal (fn-scc-dispatch conn event live trie arts fn-arena fn-cat)
                  (fn-scar-dispatch conn event live trie arts)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scc-dispatch fn-scar-dispatch fn-scc-conn-okp
                                fn-scc-dispatch-core-is-scar-dispatch-core
                                fn-scc-conn-catalogp-of-repin)
                              (theory 'minimal-theory)))))

(verify-guards fn-scc-dispatch)

(defthm fn-scc-conn-okp-of-scar-dispatch
  (implies (fn-scc-conn-okp conn fn-arena fn-cat)
           (fn-scc-conn-okp (fn-served-result-conn (fn-scar-dispatch conn event live trie arts))
                            fn-arena fn-cat))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scar-dispatch fn-scc-conn-okp-of-scar-dispatch-core
                                fn-scc-conn-okp-of-repin fn-scc-conn-okp-of-with-wire
                                fn-served-result-conn-of-fn-served-make-result)
                              (theory 'minimal-theory)))))

(defun fn-scc-dispatch-events (conn events live trie arts fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)
                  :verify-guards nil))
  (if (consp events)
      (let* ((here (fn-scc-dispatch conn (car events) live trie arts fn-arena fn-cat))
             (tail (fn-scc-dispatch-events (fn-served-result-conn here)
                                           (cdr events) live trie arts fn-arena fn-cat)))
        (fn-served-make-result
         (fn-served-result-conn tail)
         (mbe :logic (append (fn-served-result-effects here)
                             (fn-served-result-effects tail))
              :exec (fn-ag-append (fn-served-result-effects here)
                                  (fn-served-result-effects tail)))))
    (fn-served-make-result conn nil)))

(defthm fn-scc-dispatch-events-is-scar-dispatch-events
  (implies (fn-scc-conn-okp conn fn-arena fn-cat)
           (equal (fn-scc-dispatch-events conn events live trie arts fn-arena fn-cat)
                  (fn-scar-dispatch-events conn events live trie arts)))
  :hints (("Goal" :induct (fn-scc-dispatch-events conn events live trie arts fn-arena fn-cat)
           :in-theory (union-theories
                       '(fn-scc-dispatch-events fn-scar-dispatch-events
                         fn-scc-dispatch-is-scar-dispatch fn-scc-conn-okp-of-scar-dispatch)
                       (theory 'minimal-theory)))))

(verify-guards fn-scc-dispatch-events)

(defthm fn-scc-conn-okp-of-scar-dispatch-events
  (implies (fn-scc-conn-okp conn fn-arena fn-cat)
           (fn-scc-conn-okp (fn-served-result-conn
                             (fn-scar-dispatch-events conn events live trie arts))
                            fn-arena fn-cat))
  :hints (("Goal" :induct (fn-scar-dispatch-events conn events live trie arts)
           :in-theory (union-theories
                       '(fn-scar-dispatch-events fn-scc-conn-okp-of-scar-dispatch
                         fn-served-result-conn-of-fn-served-make-result)
                       (theory 'minimal-theory)))))

(defun fn-scc-feed-byte (conn byte live trie arts fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (fn-wire-fast-statep (fn-served-conn-wire conn))
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :verify-guards nil))
  (let ((fed (fn-wire-feed-byte (fn-served-conn-wire conn) byte)))
    (fn-scc-dispatch-events
     (fn-served-conn-with-wire conn (fn-wire-result-state fed))
     (fn-wire-result-events fed) live trie arts fn-arena fn-cat)))

(defthm fn-scc-feed-byte-is-scar-feed-byte
  (implies (fn-scc-conn-okp conn fn-arena fn-cat)
           (equal (fn-scc-feed-byte conn byte live trie arts fn-arena fn-cat)
                  (fn-scar-feed-byte conn byte live trie arts)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scc-feed-byte fn-scar-feed-byte
                                fn-scc-dispatch-events-is-scar-dispatch-events
                                fn-scc-conn-okp-of-with-wire)
                              (theory 'minimal-theory)))))

(verify-guards fn-scc-feed-byte)

(defthm fn-scc-conn-okp-of-scar-feed-byte
  (implies (fn-scc-conn-okp conn fn-arena fn-cat)
           (fn-scc-conn-okp (fn-served-result-conn (fn-scar-feed-byte conn byte live trie arts))
                            fn-arena fn-cat))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scar-feed-byte fn-scc-conn-okp-of-scar-dispatch-events
                                fn-scc-conn-okp-of-with-wire)
                              (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; The span layers (books/served-span.lisp) with the catalog.

(defun fn-scc-feed-span (conn i end live trie arts fn-octets fn-arena fn-cat)
  (declare (xargs :stobjs (fn-octets fn-arena fn-cat)
                  :guard (and (fn-wire-fast-statep (fn-served-conn-wire conn))
                              (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets))
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :measure (nfix (- end i))
                  :verify-guards nil
                  :hints (("Goal" :in-theory (disable fn-scc-feed-byte
                                                      fn-served-submission)))))
  (if (or (not (natp i)) (not (natp end)) (>= i end)
          (fn-served-closed-wirep (fn-served-conn-wire conn))
          (fn-served-tls-handshakingp conn))
      (fn-served-counted-make 0 (fn-served-make-result conn nil))
    (let ((here (fn-scc-feed-byte conn (fn-octets-get i fn-octets) live trie arts fn-arena fn-cat)))
      (if (fn-served-submission (fn-served-result-effects here))
          (fn-served-counted-make
           1 (fn-served-make-result (fn-served-result-conn here)
                                    (fn-served-result-effects here)))
        (let* ((tail (fn-scc-feed-span (fn-served-result-conn here) (+ 1 i) end
                                       live trie arts fn-octets fn-arena fn-cat))
               (result (fn-served-counted-result tail)))
          (fn-served-counted-make
           (+ 1 (fn-served-counted-consumed tail))
           (fn-served-make-result
            (fn-served-result-conn result)
            (mbe :logic (append (fn-served-result-effects here)
                                (fn-served-result-effects result))
                 :exec (fn-ag-append (fn-served-result-effects here)
                                     (fn-served-result-effects result))))))))))

(defthm fn-scc-feed-span-is-scar-feed-span
  (implies (fn-scc-conn-okp conn fn-arena fn-cat)
           (equal (fn-scc-feed-span conn i end live trie arts fn-octets fn-arena fn-cat)
                  (fn-scar-feed-span conn i end live trie arts fn-octets)))
  :hints (("Goal" :induct (fn-scc-feed-span conn i end live trie arts fn-octets fn-arena fn-cat)
           :in-theory (union-theories
                       '(fn-scc-feed-span fn-scar-feed-span
                         fn-scc-feed-byte-is-scar-feed-byte fn-scc-conn-okp-of-scar-feed-byte)
                       (theory 'minimal-theory)))))

; The wire stays fast through the catalog chain, unconditionally (the guards
; of the folds need it without the catalog hypothesis).
(defthm fn-scc-dispatch-preserves-fast-statep
  (implies (fn-wire-fast-statep (fn-served-conn-wire conn))
           (fn-wire-fast-statep
            (fn-served-conn-wire
             (fn-served-result-conn (fn-scc-dispatch conn event live trie arts fn-arena fn-cat)))))
  :hints (("Goal"
           :in-theory (disable fn-wire-fast-statep
                               fn-wire-begin-article-with-line-limit
                               fn-wire-article-line-limit
                               fn-scc-auth-step fn-post-offeredp
                               fn-wire-begin-article-with-line-limit-preserves-fast-statep)
           :use ((:instance fn-wire-begin-article-with-line-limit-preserves-fast-statep
                            (wire-state (fn-served-conn-wire conn))
                            (article-line-limit
                             (fn-wire-article-line-limit
                              (fn-served-conn-wire conn))))))))

(defthm fn-scc-dispatch-events-preserves-fast-statep
  (implies (fn-wire-fast-statep (fn-served-conn-wire conn))
           (fn-wire-fast-statep
            (fn-served-conn-wire
             (fn-served-result-conn
              (fn-scc-dispatch-events conn events live trie arts fn-arena fn-cat)))))
  :hints (("Goal" :induct (fn-scc-dispatch-events conn events live trie arts fn-arena fn-cat)
           :in-theory (disable fn-scc-dispatch fn-wire-fast-statep))))

(defthm fn-scc-feed-byte-preserves-fast-statep
  (implies (fn-wire-fast-statep (fn-served-conn-wire conn))
           (fn-wire-fast-statep
            (fn-served-conn-wire
             (fn-served-result-conn (fn-scc-feed-byte conn byte live trie arts fn-arena fn-cat)))))
  :hints (("Goal"
           :in-theory (e/d (fn-scc-feed-byte)
                           (fn-served-feed-byte-preserves-fast-statep
                            fn-served-feed-byte fn-scc-dispatch-events
                            fn-wire-feed-byte fn-wire-fast-statep))
           :use ((:instance fn-wire-feed-byte-preserves-fast-statep
                            (wire-state (fn-served-conn-wire conn)))
                 (:instance fn-scc-dispatch-events-preserves-fast-statep
                            (conn (fn-served-conn-with-wire
                                   conn (fn-wire-result-state
                                         (fn-wire-feed-byte (fn-served-conn-wire conn) byte))))
                            (events (fn-wire-result-events
                                     (fn-wire-feed-byte (fn-served-conn-wire conn) byte))))))))

(defthm fn-scc-feed-span-consumed-is-natural
  (natp (fn-served-counted-consumed
         (fn-scc-feed-span conn i end live trie arts fn-octets fn-arena fn-cat)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :induct (fn-scc-feed-span conn i end live trie arts fn-octets fn-arena fn-cat)
           :in-theory (e/d (fn-served-counted-make fn-served-counted-consumed)
                           (fn-scc-feed-byte fn-wire-fast-statep)))))

(local
 (defthm fn-scc-span-feed-preserves-fast-statep
   (implies (fn-wire-fast-statep (fn-served-conn-wire conn))
            (fn-wire-fast-statep
             (fn-served-conn-wire
              (fn-served-result-conn
               (fn-served-counted-result
                (fn-scc-feed-span conn i end live trie arts fn-octets fn-arena fn-cat))))))
   :hints (("Goal" :induct (fn-scc-feed-span conn i end live trie arts fn-octets fn-arena fn-cat)
            :in-theory (e/d (fn-served-counted-make fn-served-counted-result)
                            (fn-scc-feed-byte fn-wire-fast-statep))))))

(verify-guards fn-scc-feed-span
  :hints (("Goal"
           :in-theory (e/d (fn-served-counted-make fn-served-counted-result)
                           (fn-scc-feed-byte fn-wire-fast-statep
                            fn-served-counted-consumed))
           :use ((:instance fn-scc-feed-byte-preserves-fast-statep
                            (byte (fn-octets-get i fn-octets)))))))

(in-theory (disable fn-scc-feed-span))

(defun fn-scc-step-span-core (conn i end live trie arts fn-octets fn-arena fn-cat)
  (declare (xargs :stobjs (fn-octets fn-arena fn-cat)
                  :guard (and (fn-wire-fast-statep (fn-served-conn-wire conn))
                              (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets))
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))))
  (let* ((wire (fn-served-conn-wire conn))
         (fed (fn-scc-feed-span conn i end live trie arts fn-octets fn-arena fn-cat))
         (result (fn-served-counted-result fed))
         (wire2 (fn-served-conn-wire (fn-served-result-conn result))))
    (fn-served-counted-make
     (fn-served-counted-consumed fed)
     (fn-served-make-result
      (fn-served-result-conn result)
      (mbe :logic
           (append (fn-served-result-effects result)
                   (if (and (not (fn-served-closed-wirep wire))
                            (fn-served-closed-wirep wire2))
                       (list (fn-nntp-close-effect))
                     nil))
           :exec
           (fn-ag-append
            (fn-served-result-effects result)
            (if (and (not (fn-served-closed-wirep wire))
                     (fn-served-closed-wirep wire2))
                (list (fn-nntp-close-effect))
              nil)))))))

(defthm fn-scc-step-span-core-is-scar-step-span-core
  (implies (fn-scc-conn-okp conn fn-arena fn-cat)
           (equal (fn-scc-step-span-core conn i end live trie arts fn-octets fn-arena fn-cat)
                  (fn-scar-step-span-core conn i end live trie arts fn-octets)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scc-step-span-core fn-scar-step-span-core
                                fn-scc-feed-span-is-scar-feed-span)
                              (theory 'minimal-theory)))))

(defun fn-scc-step-span-fast (conn i end live trie arts fn-octets fn-arena fn-cat)
  (declare (xargs :stobjs (fn-octets fn-arena fn-cat)
                  :guard (and (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets))
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))))
  (if (not (fn-wire-fast-statep (fn-served-conn-wire conn)))
      (fn-served-counted-make 0 (fn-served-make-result conn nil))
    (fn-scc-step-span-core conn i end live trie arts fn-octets fn-arena fn-cat)))

(defthm fn-scc-step-span-fast-is-scar-step-span-fast
  (implies (fn-scc-conn-okp conn fn-arena fn-cat)
           (equal (fn-scc-step-span-fast conn i end live trie arts fn-octets fn-arena fn-cat)
                  (fn-scar-step-span-fast conn i end live trie arts fn-octets)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scc-step-span-fast fn-scar-step-span-fast
                                fn-scc-step-span-core-is-scar-step-span-core)
                              (theory 'minimal-theory)))))

(in-theory (disable fn-scc-step-span-core fn-scc-step-span-fast))

; The owner's connection ID, as the served machine sees it.
(defun-nx fn-scc-owner-catalogp (o id fn-arena fn-cat)
  (let ((conn (fn-own-find-conn id (fn-own-conns o))))
    (implies conn
             (fn-scc-conn-okp (fn-own-tls-served-conn o conn) fn-arena fn-cat))))

(defun fn-scc-own-read-span (o id i end fn-octets fn-arena fn-cat)
  (declare (xargs :stobjs (fn-octets fn-arena fn-cat)
                  :guard (and (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets))
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))))
  (let ((conn (fn-own-find-conn id (fn-own-conns o)))
        (live (fn-sn-node (fn-own-store o)))
        (trie (fn-own-view-index (fn-own-view o)))
        (arts (fn-state-articles (fn-own-view-archive (fn-own-view o)))))
    (if conn
        (let* ((counted
                 (fn-scc-step-span-fast
                  (fn-own-tls-served-conn o conn) i end live trie arts fn-octets fn-arena fn-cat))
               (result
                 (fn-scar-finish-read
                  o conn (fn-served-counted-result counted) live)))
          (fn-own-tls-make-result
           (fn-served-counted-consumed counted) (car result) (cdr result)
           (fn-own-result-repinned (fn-served-counted-result counted))))
      (fn-own-tls-make-result (nfix (- end i)) nil o nil))))

(defthm fn-scc-own-read-span-is-scar-own-read-span
  (implies (fn-scc-owner-catalogp o id fn-arena fn-cat)
           (equal (fn-scc-own-read-span o id i end fn-octets fn-arena fn-cat)
                  (fn-scar-own-read-span o id i end fn-octets)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scc-own-read-span fn-scar-own-read-span fn-scc-owner-catalogp
                                fn-scc-step-span-fast-is-scar-step-span-fast)
                              (theory 'minimal-theory)))))

(defun fn-scc-ocfg-read-span (oc id i end fn-octets fn-arena fn-cat)
  (declare (xargs :stobjs (fn-octets fn-arena fn-cat)
                  :guard (and (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets))
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))))
  (let ((result (fn-scc-own-read-span (fn-ocfg-owner oc) id i end fn-octets fn-arena fn-cat)))
    (fn-own-tls-make-result
     (fn-own-tls-result-consumed result)
     (fn-own-tls-result-effects result)
     (fn-ocfg-with-read-owner oc id (fn-own-tls-result-owner result)
                              (fn-own-tls-result-repinned result))
     (fn-own-tls-result-repinned result))))

(defthm fn-scc-ocfg-read-span-is-scar-ocfg-read-span
  (implies (fn-scc-owner-catalogp (fn-ocfg-owner oc) id fn-arena fn-cat)
           (equal (fn-scc-ocfg-read-span oc id i end fn-octets fn-arena fn-cat)
                  (fn-scar-ocfg-read-span oc id i end fn-octets)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scc-ocfg-read-span fn-scar-ocfg-read-span
                                fn-scc-own-read-span-is-scar-own-read-span)
                              (theory 'minimal-theory)))))

; KEYSTONE.  The host's served read over the catalog is the reference read
; over the octet slice: fn-scar-ocfg-read-span-is-reference-under-ocl-relation
; (books/served-span.lisp) through the equation above.
(defthm fn-scc-ocfg-read-span-is-reference-under-ocl-relation
  (implies (and (fn-ocl-relation oc)
                (fn-scar-view-indexedp (fn-ocfg-owner oc))
                (fn-scc-owner-catalogp (fn-ocfg-owner oc) id fn-arena fn-cat)
                (natp i) (natp end))
           (equal (fn-scc-ocfg-read-span oc id i end fn-octets fn-arena fn-cat)
                  (fn-ocfg-read-tls-prefix oc id (fn-oct-slice-list i end fn-octets))))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scc-ocfg-read-span-is-scar-ocfg-read-span
                                fn-scar-ocfg-read-span-is-reference-under-ocl-relation)
                              (theory 'minimal-theory)))))

(in-theory (disable fn-scc-own-read-span fn-scc-ocfg-read-span))
