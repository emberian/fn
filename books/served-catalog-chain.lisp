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
; Each layer fn-scr-X mirrors its scar/pix layer text for text, with the
; catalog view V and the two stobjs added, and each theorem fn-scr-X-is-Y
; equates it to THAT layer (not the far reference) under one hypothesis, the
; -cat keystone's: the connection's pinned archive is the catalog's view at
; the connection's pin, with the pin correspondences and the number table
; fresh (fn-scr-catalogp).  The existing chain of -is- theorems then carries
; the equation to fn-ocfg-read-tls-prefix
; (fn-scr-ocfg-read-span-is-reference-under-ocl-relation).
;
; The view a pin names.  A connection pins the owner's view version, which is
; the count of RECORDS in the history (books/owner.lisp fn-own-refresh: (len
; (fn-sf-records ...))); a catalog view is a count of ROWS, one per article
; record.  Rows carry their record's sequence (fn-held-sequence) and stand in
; history order, so the view of a pinned version is the number of rows whose
; sequence is below it, found by bisection: O(log count) per command, no new
; state in the connection, the owner or the catalog (fn-scr-view-of).  That
; the bisection names the pinned archive's rows is the JOIN, the R-side
; equation of the catalog relation with the owner's view; it is the
; hypothesis fn-scr-catalogp carries, proved at the owner's entries in
; books/served-catalog-owner.lisp (step 8's R), not here.
;
; A read-restricted session (PRF-222, fn-auth-access-read) is served the
; RESTRICTED archive and index by the reference walks: the catalog holds the
; whole view and knows no access rule, so the -cat arms would answer with
; articles the rule hides.  fn-scr-auth-delegate splits there; an unrestricted
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
(include-book "protocol-table") ; reply texts: (fn-proto-text ROW KEY)
(include-book "served-catalog")
(include-book "group-access-cache")

;; The tau system is off in this book (lane tau-pass, tools/tau_cost.py).
;; Its work is proof time no prover step counts (docs/proof-style.md
;; 9.1); planning/evidence/tau-cost-*.json has this book's figures.
(local (in-theory (disable (tau-system))))

; -----------------------------------------------------------------------------
; The view a pinned version names: rows whose record sequence is below it.

; The midpoint of [lo, hi): in it, so the bisection halves the interval.
(defun fn-scr-mid (lo hi)
  (declare (xargs :guard (and (natp lo) (natp hi) (<= lo hi))))
  (+ lo (nonnegative-integer-quotient (- hi lo) 2)))

; niq-bounds is rational (niq <= i/2); the integer form closes the bisection.
(local (defthm fn-scr-twice-niq-2
  (implies (natp i) (<= (* 2 (nonnegative-integer-quotient i 2)) i))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance niq-bounds (i i) (j 2)))))))

(defthm fn-scr-mid-bounds
  (implies (and (natp lo) (natp hi) (< lo hi))
           (and (<= lo (fn-scr-mid lo hi))
                (< (fn-scr-mid lo hi) hi)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-scr-mid)
           :use ((:instance fn-scr-twice-niq-2 (i (- hi lo)))))))

(defthm natp-of-fn-scr-mid
  (implies (and (natp lo) (natp hi) (<= lo hi))
           (natp (fn-scr-mid lo hi)))
  :rule-classes :type-prescription)

(in-theory (disable fn-scr-mid))

(defun fn-scr-seq-bound (lo hi version fn-cat)
  (declare (xargs :stobjs fn-cat
                  :guard (and (natp lo) (natp hi) (<= lo hi)
                              (<= hi (fn-cat-count fn-cat)) (natp version))
                  :measure (nfix (- hi lo))
                  :verify-guards nil))
  (if (or (not (natp lo)) (not (natp hi)) (>= lo hi))
      (nfix lo)
    (let ((mid (fn-scr-mid lo hi)))
      ;; nfix: the identity on a row (fn-held-sequence is a uint64 under
      ;; fn-held-p); it keeps the probe's guard at the row's existence.
      (if (< (nfix (fn-held-sequence (fn-cat-at mid fn-cat))) version)
          (fn-scr-seq-bound (+ mid 1) hi version fn-cat)
        (fn-scr-seq-bound lo mid version fn-cat)))))

(defthm natp-of-fn-scr-seq-bound
  (natp (fn-scr-seq-bound lo hi version fn-cat))
  :rule-classes (:rewrite :type-prescription))

(defthm fn-scr-seq-bound-below-hi
  (implies (and (natp lo) (natp hi) (<= lo hi))
           (<= (fn-scr-seq-bound lo hi version fn-cat) hi))
  :rule-classes (:rewrite :linear))

(verify-guards fn-scr-seq-bound)

(defun fn-scr-view-of (version fn-cat)
  (declare (xargs :stobjs fn-cat :guard t))
  (fn-scr-seq-bound 0 (fn-cat-count fn-cat) (nfix version) fn-cat))

(defthm natp-of-fn-scr-view-of
  (natp (fn-scr-view-of version fn-cat))
  :rule-classes (:rewrite :type-prescription))

(in-theory (disable fn-scr-seq-bound fn-scr-view-of))

; -----------------------------------------------------------------------------
; The hypothesis: the -cat keystone's (fn-nntp-archive-command-cat-is-pinned).

(defun-nx fn-scr-catalogp (archive index v fn-arena fn-cat)
  (and (equal (fn-state-articles archive)
              (fn-cat-view-articles v fn-arena fn-cat))
       (fn-statep archive)
       (fn-gidx-pin-correspondencep index archive)
       (fn-midx-correspondencep (fn-gidx-pin-trie index)
                                (fn-state-articles archive))
       (fn-cnx-freshp fn-cat)))

; The same over a connection's fields, and over the live view a re-pin
; takes them from.
(defun-nx fn-scr-fields-catalogp (archive index group-index control pinned fn-arena fn-cat)
  (fn-scr-catalogp archive
                   (fn-served-pinned-index archive index group-index control)
                   (fn-scr-view-of (fn-served-pinned-version pinned) fn-cat)
                   fn-arena fn-cat))

(defun-nx fn-scr-conn-catalogp (conn fn-arena fn-cat)
  (fn-scr-fields-catalogp (fn-served-conn-archive conn) (fn-served-conn-index conn)
                          (fn-served-conn-group-index conn) (fn-served-conn-control conn)
                          (fn-served-conn-pinned conn) fn-arena fn-cat))

(defun-nx fn-scr-live-catalogp (live fn-arena fn-cat)
  (fn-scr-fields-catalogp (fn-served-live-archive live) (fn-served-live-index live)
                          (fn-served-live-buckets live) (fn-served-live-control live)
                          (fn-served-pinned-make (fn-served-live-version live)
                                                 (fn-served-live-frontier live) t)
                          fn-arena fn-cat))

; The connection and what it re-pins to.
(defun-nx fn-scr-conn-okp (conn fn-arena fn-cat)
  (and (fn-scr-conn-catalogp conn fn-arena fn-cat)
       (implies (fn-served-conn-live conn)
                (fn-scr-live-catalogp (fn-served-conn-live conn) fn-arena fn-cat))))

(defthm fn-scr-conn-catalogp-unfolds
  (equal (fn-scr-conn-catalogp conn fn-arena fn-cat)
         (fn-scr-catalogp (fn-served-conn-archive conn)
                          (fn-served-conn-pinned-index conn)
                          (fn-scr-view-of (fn-served-pinned-version (fn-served-conn-pinned conn))
                                          fn-cat)
                          fn-arena fn-cat))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scr-conn-catalogp fn-scr-fields-catalogp
                                fn-served-conn-pinned-index)
                              (theory 'minimal-theory)))))

(defthm fn-scr-conn-catalogp-of-make-conn-live
  (equal (fn-scr-conn-catalogp
          (fn-served-make-conn-live wire session archive config observation injection
                                    verdicts index buckets control pinned live)
          fn-arena fn-cat)
         (fn-scr-fields-catalogp archive index buckets control pinned fn-arena fn-cat))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scr-conn-catalogp fn-served-conn-fields-of-make-conn-live)
                              (theory 'minimal-theory)))))

(defthm fn-scr-conn-catalogp-of-with-wire
  (equal (fn-scr-conn-catalogp (fn-served-conn-with-wire conn wire) fn-arena fn-cat)
         (fn-scr-conn-catalogp conn fn-arena fn-cat))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scr-conn-catalogp fn-served-conn-fields-of-with-wire)
                              (theory 'minimal-theory)))))

(defthm fn-scr-conn-catalogp-of-repin
  (equal (fn-scr-conn-catalogp (fn-served-repin conn) fn-arena fn-cat)
         (if (fn-served-conn-live conn)
             (fn-scr-live-catalogp (fn-served-conn-live conn) fn-arena fn-cat)
           (fn-scr-conn-catalogp conn fn-arena fn-cat)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-served-repin fn-scr-live-catalogp
                                fn-scr-conn-catalogp-of-make-conn-live)
                              (theory 'minimal-theory)))))

(defthm fn-scr-conn-okp-of-repin
  (implies (fn-scr-conn-okp conn fn-arena fn-cat)
           (fn-scr-conn-okp (fn-served-repin conn) fn-arena fn-cat))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scr-conn-okp fn-scr-conn-catalogp-of-repin
                                fn-served-repin-keeps-live)
                              (theory 'minimal-theory)))))

(defthm fn-scr-conn-okp-of-with-wire
  (equal (fn-scr-conn-okp (fn-served-conn-with-wire conn wire) fn-arena fn-cat)
         (fn-scr-conn-okp conn fn-arena fn-cat))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scr-conn-okp fn-scr-conn-catalogp-of-with-wire
                                fn-served-conn-fields-of-with-wire)
                              (theory 'minimal-theory)))))

(in-theory (disable fn-scr-conn-catalogp-unfolds))

; -----------------------------------------------------------------------------
; The dispatcher lifted: fn-nntp-command-pinned with the -cat dispatcher.

(defun fn-scr-command (session archive index verdicts env tokens v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp v)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :verify-guards nil))
  (fn-nntp-command-dispatch
   (fn-nntp-archive-command-cat
    session archive index verdicts env keyword args v fn-arena fn-cat)
   :pinned t))

(defthm fn-scr-command-is-command-pinned
  (implies (and (fn-scr-catalogp archive index v fn-arena fn-cat) (fn-scol-okp fn-arena fn-cat))
           (equal (fn-scr-command session archive index verdicts env tokens v fn-arena fn-cat)
                  (fn-nntp-command-pinned session archive index verdicts env tokens fn-arena)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scr-command fn-nntp-command-pinned fn-scr-catalogp
                                fn-nntp-archive-command-cat-is-pinned)
                              (theory 'minimal-theory)))))

(verify-guards fn-scr-command)

(defun fn-scr-step (session archive index verdicts env wire-event v fn-arena fn-cat)
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
              (fn-nntp-single session (fn-proto-text * :syntax))
            (let ((tokens (fn-nntp-tokenize line)))
              (if (and (consp tokens)
                       (fn-nntp-command-arguments-at-mostp tokens))
                  (fn-scr-command
                   session archive index verdicts env tokens v fn-arena fn-cat)
                (fn-nntp-single session (fn-proto-text * :syntax))))))
      (fn-nntp-single session (fn-proto-text * :syntax)))))

(defthm fn-scr-step-is-step-pinned
  (implies (and (fn-scr-catalogp archive index v fn-arena fn-cat) (fn-scol-okp fn-arena fn-cat))
           (equal (fn-scr-step session archive index verdicts env wire-event v fn-arena fn-cat)
                  (fn-nntp-step-pinned session archive index verdicts env wire-event fn-arena)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scr-step fn-nntp-step-pinned
                                fn-scr-command-is-command-pinned)
                              (theory 'minimal-theory)))))

(verify-guards fn-scr-step)

(defun fn-scr-post-step
    (ps archive index verdicts config observation injection wire-event v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp v)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :verify-guards nil))
  (if (or (not (fn-post-sessionp ps)) (fn-post-session-awaiting ps))
      (fn-nntp-post-step ps archive config observation injection wire-event fn-arena)
    (let ((r (fn-scr-step
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
             (fn-post-single ps (fn-proto-text "POST" :not-permitted)) nil))
        (fn-post-make-result
         (fn-post-make-session (fn-nntp-result-session r) nil)
         (fn-nntp-result-effects r) nil)))))

(defthm fn-scr-post-step-is-post-step-pinned
  (implies (and (fn-scr-catalogp archive index v fn-arena fn-cat) (fn-scol-okp fn-arena fn-cat))
           (equal (fn-scr-post-step ps archive index verdicts config observation injection
                                    wire-event v fn-arena fn-cat)
                  (fn-nntp-post-step-pinned ps archive index verdicts config observation
                                            injection wire-event fn-arena)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scr-post-step fn-nntp-post-step-pinned
                                fn-scr-step-is-step-pinned)
                              (theory 'minimal-theory)))))

(verify-guards fn-scr-post-step)

(defun fn-scr-peer-delegate
    (ps archive index verdicts config observation injection wire-event v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp v)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :verify-guards nil))
  (let ((r (fn-scr-post-step
            (fn-peer-session-base ps) archive index verdicts config
            observation injection wire-event v fn-arena fn-cat)))
    (fn-post-make-result (fn-peer-with-base ps (fn-post-result-session r))
                         (fn-post-result-effects r)
                         (fn-post-result-submission r))))

(defthm fn-scr-peer-delegate-is-peer-delegate-pinned
  (implies (and (fn-scr-catalogp archive index v fn-arena fn-cat) (fn-scol-okp fn-arena fn-cat))
           (equal (fn-scr-peer-delegate ps archive index verdicts config observation injection
                                        wire-event v fn-arena fn-cat)
                  (fn-pix-peer-delegate-pinned ps archive index verdicts config observation
                                               injection wire-event fn-arena)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scr-peer-delegate fn-pix-peer-delegate-pinned
                                fn-scr-post-step-is-post-step-pinned
                                fn-pix-post-step-pinned-is-post-step-pinned)
                              (theory 'minimal-theory)))))

(verify-guards fn-scr-peer-delegate)

; -----------------------------------------------------------------------------
; The carried layers (books/served-carried.lisp) with the catalog.

;; The peer arm with its history test read from the catalog (lane
;; join-f2-midx, the fn-midx retirement).  fn-pgc-peer-arm's IHAVE/CHECK
;; history test (books/peer-offer-indexed.lisp fn-pix-history-hasp) walks the
;; owner's view trie when the session node's article list IS the view's
;; visible list; here that branch asks the catalog's Message-ID column at the
;; view's version LVER (fn-scr-view-of, one bisection, taken only on that
;; branch).  fn-scr-live-joinp is what makes the two one test: the trie is
;; the index of ARTS and ARTS is the catalog's view at LVER -- the owner's
;; live view record carries both (fn-scr-live-catalogp, which
;; fn-scr-owner-catalogp gives at every connection).
(defun-nx fn-scr-live-joinp (trie lver arts fn-arena fn-cat)
  (and (fn-midx-correspondencep trie arts)
       (equal arts (fn-cat-view-articles (fn-scr-view-of lver fn-cat) fn-arena fn-cat))))

(defun fn-scr-history-hasp (msgid node lver arts fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)))
  (if (and (stringp msgid)
           (< 0 (length msgid))
           (equal (fn-state-articles (fn-node-acceptance node)) arts))
      (if (fn-scat-msgid-article msgid (fn-scr-view-of lver fn-cat) fn-arena fn-cat) t nil)
    (fn-peer-history-hasp msgid node)))

(local (defthm fn-scr-nonempty-key-is-positive-length
  (implies (stringp msgid)
           (equal (consp (fn-midx-key-chars msgid)) (< 0 (length msgid))))
  :hints (("Goal" :in-theory (enable fn-midx-key-chars length)
           :expand ((len (coerce msgid 'list)))))))

(defthm fn-scr-history-hasp-is-pix-history-hasp
  (implies (fn-scr-live-joinp trie lver arts fn-arena fn-cat)
           (equal (fn-scr-history-hasp msgid node lver arts fn-arena fn-cat)
                  (fn-pix-history-hasp msgid node trie arts)))
  :hints (("Goal" :in-theory (e/d (fn-scr-history-hasp fn-pix-history-hasp fn-scr-live-joinp
                                   fn-midx-correspondencep fn-midx-concrete-lookup-is-lookup
                                   fn-scat-msgid-article-is-find-article)
                                  (fn-peer-history-hasp fn-midx-lookup fn-midx-build
                                   fn-midx-key-chars fn-scat-msgid-article fn-find-article
                                   fn-cat-view-articles fn-scr-view-of))
           :use ((:instance fn-midx-lookup-of-build-is-find-article-for-nonempty
                            (articles arts))))))

(in-theory (disable fn-scr-history-hasp))

(defun fn-scr-decide-offer (node cfg peer session msgid clock inflight lver arts fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
           (ignorable clock))
  (let ((record (fn-cfg-peer-find peer (fn-cfg-peers (fn-cfg-value cfg)))))
    (cond ((not record) (fn-peer-decision :refuse :not-a-peer))
          ((null (fn-cfg-peer-inbound record))
           (fn-peer-decision :refuse :no-inbound))
          ((not (fn-af-message-idp msgid))
           (fn-peer-decision :refuse :message-id-syntax))
          ; PKT-858: the disk-slow posture, as fn-peer-decide-offer.
          ((fn-peer-shed-p session)
           (fn-peer-decision :defer :disk-slow))
          ((fn-scr-history-hasp (fn-record-octets-string msgid) node lver arts fn-arena fn-cat)
           (fn-peer-decision :have :history))
          ; PRF-235: the refused-offer memory, as fn-peer-decide-offer.
          ((fn-peer-remembered-reason msgid session)
           (fn-peer-decision :refuse (fn-peer-remembered-reason msgid session)))
          ((fn-peer-stagedp (fn-record-octets-string msgid) node)
           (fn-peer-decision :defer :staged))
          ((equal (fn-state-fenced (fn-node-acceptance node)) t)
           (fn-peer-decision :defer :fenced))
          ((<= (fn-cfg-peer-inbound-max-inflight record) (nfix inflight))
           (fn-peer-decision :defer :inflight-limit))
          ((not (fn-pgc-retain-admissiblep (fn-node-retention node)
                                           (fn-peer-probe-obligation-id msgid)
                                           (fn-peer-probe-subject) :archive
                                           (fn-peer-evidence peer cfg)
                                           (fn-charge-for-payload 0)))
           (fn-peer-decision :defer :capacity))
          (t (fn-peer-decision :want nil)))))

(defthm fn-scr-decide-offer-is-pgc-decide-offer
  (implies (fn-scr-live-joinp trie lver arts fn-arena fn-cat)
           (equal (fn-scr-decide-offer node cfg peer session msgid clock inflight lver arts
                                       fn-arena fn-cat)
                  (fn-pgc-decide-offer node cfg peer session msgid clock inflight trie arts)))
  :hints (("Goal" :in-theory (e/d (fn-scr-decide-offer fn-pgc-decide-offer
                                   fn-scr-history-hasp-is-pix-history-hasp)
                                  (fn-peer-shed-p fn-pgc-retain-admissiblep fn-scr-live-joinp
                                   fn-scr-history-hasp fn-pix-history-hasp
                                   fn-peer-stagedp fn-cfg-peer-find
                                   fn-af-message-idp fn-record-octets-string)))))

(in-theory (disable fn-scr-decide-offer))

(defun fn-scr-peer-command (ps keyword args lver arts fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (fn-pgc-peer-sessionp ps)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :verify-guards nil))
  (let ((node (fn-peer-session-node ps))
        (cfg (fn-peer-session-cfg ps))
        (peer (fn-peer-session-peer ps))
        (inflight (fn-peer-session-inflight ps)))
    (cond
     ((fn-nntp-keywordp keyword "IHAVE")
      (if (not (fn-peer-msgid-argp args))
          (fn-post-make-result ps (fn-peer-single ps (fn-proto-text * :syntax)) nil)
        (let ((d (fn-scr-decide-offer node cfg peer ps (car args) nil inflight
                                      lver arts fn-arena fn-cat)))
          (if (equal (fn-peer-decision-kind d) :want)
              (fn-post-make-result
               (fn-peer-with-transfer ps (list :ihave (car args)) inflight)
               (append (fn-peer-single ps (fn-peer-ihave-offer-line d))
                       (list (fn-nntp-begin-article-effect)))
               nil)
            (fn-post-make-result ps (fn-peer-single ps (fn-peer-ihave-offer-line d))
                                 nil)))))
     ((fn-nntp-keywordp keyword "CHECK")
      (if (not (fn-peer-msgid-argp args))
          (fn-post-make-result ps (fn-peer-single ps (fn-proto-text * :syntax)) nil)
        (let ((d (fn-scr-decide-offer node cfg peer ps (car args) nil inflight
                                      lver arts fn-arena fn-cat)))
          (fn-post-make-result
           (if (equal (fn-peer-decision-kind d) :want)
               (fn-peer-with-transfer ps nil (+ 1 (nfix inflight)))
             ps)
           (fn-peer-echo-reply (fn-peer-check-code d) (car args))
           nil))))
     ((fn-nntp-keywordp keyword "TAKETHIS")
      (if (not (fn-peer-msgid-argp args))
          (fn-post-make-result ps (fn-peer-single ps (fn-proto-text * :syntax)) nil)
        (fn-post-make-result
         (fn-peer-with-transfer ps (list :takethis (car args))
                                (nfix (- (nfix inflight) 1)))
         (list (fn-nntp-begin-article-effect))
         nil)))
     ((and (fn-nntp-keywordp keyword "MODE")
           (consp args) (null (cdr args))
           (fn-nntp-keywordp (car args) "STREAM"))
      (fn-post-make-result ps (fn-peer-single ps (fn-proto-text "MODE" :streaming)) nil))
     ((and (fn-nntp-keywordp keyword "CAPABILITIES")
           (or (null args)
               (and (consp args) (null (cdr args))
                    (fn-nntp-keyword-tokenp (car args)))))
      (fn-post-make-result
       ps
       (fn-nntp-result-effects
        (fn-nntp-multi (fn-peer-reader-session ps)
                       (fn-proto-text "CAPABILITIES" :list)
                       (fn-peer-capability-lines
                        (fn-cfg-peer-find peer (fn-cfg-peers (fn-cfg-value cfg)))
                        nil)))
       nil))
     (t nil))))

(defthm fn-scr-peer-command-is-pgc-peer-command
  (implies (fn-scr-live-joinp trie lver arts fn-arena fn-cat)
           (equal (fn-scr-peer-command ps keyword args lver arts fn-arena fn-cat)
                  (fn-pgc-peer-command ps keyword args trie arts)))
  :hints (("Goal" :in-theory (e/d (fn-scr-peer-command fn-pgc-peer-command
                                   fn-scr-decide-offer-is-pgc-decide-offer)
                                  (fn-scr-decide-offer fn-pgc-decide-offer fn-scr-live-joinp
                                   fn-nntp-keywordp fn-peer-msgid-argp
                                   fn-peer-single fn-peer-echo-reply
                                   fn-peer-ihave-offer-line fn-peer-check-code
                                   fn-peer-with-transfer fn-peer-capability-lines)))))

(local (defthm fn-scr-msgid-argp-forward
  (implies (fn-peer-msgid-argp args)
           (and (consp args) (null (cdr args))
                (fn-nntp-printable-tokenp (car args))
                (fn-af-message-idp (car args))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-peer-msgid-argp)))))

(local (defthm fn-scr-peer-single-true-listp
  (true-listp (fn-peer-single ps text))
  :hints (("Goal" :in-theory (enable fn-peer-single fn-nntp-result-effects
                                     fn-nntp-single fn-nntp-make-result)))))

(verify-guards fn-scr-peer-command
  :hints (("Goal" :in-theory (disable fn-scr-decide-offer fn-peer-command
                                      fn-peer-single fn-peer-msgid-argp))))

(in-theory (disable fn-scr-peer-command))

(defun fn-scr-peer-arm
    (ps lver arts archive index verdicts config observation injection wire-event fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (fn-pgc-peer-sessionp ps)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :verify-guards nil))
  (cond
   ((not (equal (fn-nntp-session-openp (fn-peer-reader-session ps)) t))
    (fn-pix-peer-delegate-pinned ps archive index verdicts config observation
                                 injection wire-event fn-arena))
   ((fn-peer-session-transfer ps) (fn-pgc-transfer-step ps wire-event))
   ((and (consp wire-event)
         (equal (car wire-event) :command)
         (consp (cdr wire-event))
         (null (cdr (cdr wire-event)))
         (fn-nntp-command-inputp (car (cdr wire-event))))
    (let ((tokens (fn-nntp-tokenize (car (cdr wire-event)))))
      (if (and (consp tokens)
               (fn-nntp-keyword-tokenp (car tokens))
               (fn-nntp-command-arguments-at-mostp tokens))
          (let ((r (fn-scr-peer-command ps (car tokens) (cdr tokens) lver arts fn-arena fn-cat)))
            (if r r
              (fn-pix-peer-delegate-pinned ps archive index verdicts config
                                           observation injection wire-event fn-arena)))
        (fn-pix-peer-delegate-pinned ps archive index verdicts config observation
                                     injection wire-event fn-arena))))
   (t (fn-pix-peer-delegate-pinned ps archive index verdicts config observation
                                   injection wire-event fn-arena))))


(defthm fn-scr-peer-arm-is-pgc-peer-arm
  (implies (fn-scr-live-joinp trie lver arts fn-arena fn-cat)
           (equal (fn-scr-peer-arm ps lver arts archive index verdicts config
                                   observation injection wire-event fn-arena fn-cat)
                  (fn-pgc-peer-arm ps trie arts archive index verdicts config
                                   observation injection wire-event fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-scr-peer-arm fn-pgc-peer-arm
                                   fn-scr-peer-command-is-pgc-peer-command)
                                  (fn-scr-peer-command fn-pgc-peer-command fn-scr-live-joinp
                                   fn-pgc-transfer-step fn-pix-peer-delegate-pinned
                                   fn-nntp-tokenize fn-nntp-keyword-tokenp
                                   fn-nntp-command-arguments-at-mostp fn-nntp-command-inputp)))))

(verify-guards fn-scr-peer-arm
  :hints (("Goal" :in-theory (disable fn-scr-peer-command fn-pgc-transfer-step
                                      fn-pix-peer-delegate-pinned))))

(in-theory (disable fn-scr-peer-arm))

(defun fn-scr-peer-step
    (ps live trie lver arts archive index verdicts config observation injection wire-event
        v fn-arena fn-cat)
  ; TRIE is kept for the equation with the scar layer (whose peer arm reads
  ; it); the catalog's arm reads LVER instead.
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp v)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :verify-guards nil)
           (ignorable trie))
  (cond
   ((not (fn-scar-peer-sessionp ps live)) (fn-post-make-result ps nil nil))
   ((null (fn-peer-session-peer ps))
    (fn-scr-peer-delegate ps archive index verdicts config observation
                          injection wire-event v fn-arena fn-cat))
   (t (fn-scr-peer-arm ps lver arts archive index verdicts config
                       observation injection wire-event fn-arena fn-cat))))

(defthm fn-scr-peer-step-is-scar-peer-step-pinned
  (implies (and (fn-scr-live-joinp trie lver arts fn-arena fn-cat) (fn-scr-catalogp archive index v fn-arena fn-cat) (fn-scol-okp fn-arena fn-cat))
           (equal (fn-scr-peer-step ps live trie lver arts archive index verdicts config
                                    observation injection wire-event v fn-arena fn-cat)
                  (fn-scar-peer-step-pinned ps live trie arts archive index verdicts config
                                            observation injection wire-event fn-arena)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scr-peer-step fn-scar-peer-step-pinned
                                fn-scr-peer-arm-is-pgc-peer-arm
                                fn-scr-peer-delegate-is-peer-delegate-pinned)
                              (theory 'minimal-theory)))))

(verify-guards fn-scr-peer-step
  :hints (("Goal" :in-theory (disable fn-scar-peer-sessionp))))

; An unrestricted session's views are its arguments (books/nntp-auth.lisp).
(local (defthm fn-scr-auth-view-archive-unrestricted
  (implies (not (fn-auth-access-read as config))
           (equal (fn-auth-view-archive as config archive) archive))
  :hints (("Goal" :in-theory (union-theories '(fn-auth-view-archive)
                                             (theory 'minimal-theory))))))

(local (defthm fn-scr-auth-view-index-unrestricted
  (implies (not (fn-auth-access-read as config))
           (equal (fn-auth-view-index as config archive index) index))
  :hints (("Goal" :in-theory (union-theories '(fn-auth-view-index)
                                             (theory 'minimal-theory))))))

; PKT-643: the restricted view the host prepared for this session's rule at
; its pin (books/group-access-cache.lisp fn-gacc-prepare, from
; host/owner-host.lisp), or nil.  Under fn-gacc-okp it is the view
; fn-auth-view-archive and fn-auth-view-index build per command
; (fn-scr-cached-view-is-the-view).
(defun fn-scr-cached-view (as config archive index cache)
  (declare (xargs :guard t))
  (let ((read (fn-auth-access-read as config)))
    (and read
         (fn-gidx-pinp index)
         (fn-gacc-view read archive (fn-gidx-pin-control index) cache))))

(defthm fn-scr-cached-view-is-the-view
  (implies (and (fn-gacc-okp cache)
                (fn-scr-cached-view as config archive index cache))
           (and (equal (fn-ag-car (fn-scr-cached-view as config archive index cache))
                       (fn-auth-view-archive as config archive))
                (equal (fn-ag-cdr (fn-scr-cached-view as config archive index cache))
                       (fn-auth-view-index as config archive index))))
  :hints (("Goal" :in-theory (e/d (fn-scr-cached-view fn-auth-view-archive fn-auth-view-index)
                                  (fn-gacc-view fn-gac-view-entry fn-gac-restrict-state
                                   fn-gac-restrict-index fn-auth-access-read fn-gidx-pinp
                                   fn-gidx-pin-control))
           :use ((:instance fn-gacc-view-is-the-view-entry
                            (text (fn-auth-access-read as config))
                            (control (fn-gidx-pin-control index)))
                 (:instance fn-gac-view-entry-is-per-command
                            (text (fn-auth-access-read as config)))))))

(defun fn-scr-auth-delegate
    (as live trie lver arts cache archive index verdicts config observation injection wire-event
        v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp v)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :verify-guards nil))
  (if (fn-auth-access-read as config)
      ;; PRF-222: the rule's view of the archive, by the reference walks;
      ;; PKT-643: the view the host prepared at this pin, when it has one, so
      ;; no command of the session builds it.
      (let ((view (fn-scr-cached-view as config archive index cache)))
        (if view
            (let ((r (fn-scar-peer-step-pinned
                      (fn-auth-view-session as config) live trie arts
                      (fn-ag-car view) (fn-ag-cdr view) verdicts
                      (fn-auth-view-config as (fn-auth-moderation-config as config) archive)
                      observation injection wire-event fn-arena)))
              (fn-post-make-result (fn-auth-with-base as (fn-post-result-session r))
                                   (fn-post-result-effects r)
                                   (fn-post-result-submission r)))
          (fn-scar-auth-delegate-pinned as live trie arts archive index verdicts config
                                        observation injection wire-event fn-arena)))
    (let ((r (fn-scr-peer-step
              (fn-auth-view-session as config) live trie lver arts archive index verdicts
              (fn-auth-view-config as (fn-auth-moderation-config as config) archive)
              observation injection wire-event v fn-arena fn-cat)))
      (fn-post-make-result (fn-auth-with-base as (fn-post-result-session r))
                           (fn-post-result-effects r)
                           (fn-post-result-submission r)))))

(defthm fn-scr-auth-delegate-is-scar-auth-delegate-pinned
  (implies (and (fn-gacc-okp cache) (fn-scr-live-joinp trie lver arts fn-arena fn-cat) (fn-scr-catalogp archive index v fn-arena fn-cat) (fn-scol-okp fn-arena fn-cat))
           (equal (fn-scr-auth-delegate as live trie lver arts cache archive index verdicts config
                                        observation injection wire-event v fn-arena fn-cat)
                  (fn-scar-auth-delegate-pinned as live trie arts archive index verdicts config
                                                observation injection wire-event fn-arena)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scr-auth-delegate fn-scar-auth-delegate-pinned
                                fn-scr-peer-step-is-scar-peer-step-pinned
                                fn-scr-auth-view-archive-unrestricted
                                fn-scr-auth-view-index-unrestricted
                                fn-scr-cached-view-is-the-view)
                              (theory 'minimal-theory)))))

(verify-guards fn-scr-auth-delegate)

(defun fn-scr-auth-step
    (as live trie lver arts cache archive index verdicts config observation injection wire-event
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
              (fn-scr-auth-delegate as live trie lver arts cache archive index verdicts config
                                    observation injection wire-event v fn-arena fn-cat)))
        (fn-scr-auth-delegate as live trie lver arts cache archive index verdicts config observation
                              injection wire-event v fn-arena fn-cat))))
   (t (fn-scr-auth-delegate as live trie lver arts cache archive index verdicts config observation
                            injection wire-event v fn-arena fn-cat))))

(defthm fn-scr-auth-step-is-scar-auth-step-pinned
  (implies (and (fn-gacc-okp cache) (fn-scr-live-joinp trie lver arts fn-arena fn-cat) (fn-scr-catalogp archive index v fn-arena fn-cat) (fn-scol-okp fn-arena fn-cat))
           (equal (fn-scr-auth-step as live trie lver arts cache archive index verdicts config
                                    observation injection wire-event v fn-arena fn-cat)
                  (fn-scar-auth-step-pinned as live trie arts archive index verdicts config
                                            observation injection wire-event fn-arena)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scr-auth-step fn-scar-auth-step-pinned
                                fn-scr-auth-delegate-is-scar-auth-delegate-pinned)
                              (theory 'minimal-theory)))))

(verify-guards fn-scr-auth-step)

(defun fn-scr-dispatch-core (conn event live trie lver arts cache fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)
                  :verify-guards nil))
  (let* ((v (fn-scr-view-of (fn-served-pinned-version (fn-served-conn-pinned conn)) fn-cat))
         (r (fn-scr-auth-step (fn-served-conn-session conn) live trie lver arts cache
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

(defthm fn-scr-dispatch-core-is-scar-dispatch-core
  (implies (and (fn-gacc-okp cache) (fn-scr-live-joinp trie lver arts fn-arena fn-cat) (fn-scr-conn-catalogp conn fn-arena fn-cat) (fn-scol-okp fn-arena fn-cat))
           (equal (fn-scr-dispatch-core conn event live trie lver arts cache fn-arena fn-cat)
                  (fn-scar-dispatch-core conn event live trie arts fn-arena)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scr-dispatch-core fn-scar-dispatch-core
                                fn-scr-conn-catalogp-unfolds
                                fn-scr-auth-step-is-scar-auth-step-pinned)
                              (theory 'minimal-theory)))))

(verify-guards fn-scr-dispatch-core)

; The step keeps every field the hypothesis reads, and the live view.
(defthm fn-scr-conn-okp-of-scar-dispatch-core
  (implies (fn-scr-conn-okp conn fn-arena fn-cat)
           (fn-scr-conn-okp (fn-served-result-conn (fn-scar-dispatch-core conn event live trie arts fn-arena))
                            fn-arena fn-cat))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scar-dispatch-core fn-scr-conn-okp fn-scr-conn-catalogp
                                fn-served-result-conn-of-fn-served-make-result
                                fn-served-conn-fields-of-make-conn-live)
                              (theory 'minimal-theory)))))

;; F2 (lane sca-join-5): the re-pin reads the catalog.  GROUP and LISTGROUP
;; re-pin the connection to the live view before they answer
;; (books/served.lisp fn-served-repin), and the reference's re-selection
;; fn-served-reselect computes the selected group's first article with
;; fn-nntp-group-low over EVERY article of the live archive.  The twin reads
;; it from the catalog at the live view (fn-scat-group-low: the live table
;; at the top view, the probe pass otherwise); KEYSTONE
;; fn-scr-repin-is-served-repin equates the two under the live view's
;; catalog hypothesis, which fn-scr-conn-okp carries.
(defun fn-scr-reselect (inner archive v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (let* ((group (fn-nntp-session-group inner))
         (group2 (if (and group
                          (fn-ag-member group (fn-state-groups archive)))
                     group
                   nil))
         (low (if group2 (fn-scat-group-low group2 v fn-cat) nil))
         (current (if (posp low) low nil)))
    (fn-nntp-set-cursor inner group2 current)))

(defthm fn-scr-reselect-is-served-reselect
  (implies (and (equal (fn-state-articles archive)
                       (fn-cat-view-articles v fn-arena fn-cat))
                (fn-cnx-freshp fn-cat))
           (equal (fn-scr-reselect inner archive v fn-cat)
                  (fn-served-reselect inner archive)))
  :hints (("Goal" :in-theory (e/d (fn-scr-reselect fn-served-reselect)
                                  (fn-scat-group-low fn-nntp-group-low fn-cat-view-articles
                                   fn-cnx-freshp fn-nntp-set-cursor
                                   fn-scat-group-low-is-pass fn-scat-group-low-pass)))))

(defun fn-scr-repin-session (as archive v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)))
  (let* ((pold (fn-auth-session-base as))
         (told (fn-peer-session-base pold)))
    (fn-auth-with-base
     as
     (fn-peer-with-base
      pold
      (fn-post-make-session (fn-scr-reselect (fn-post-session-base told) archive v fn-cat)
                            (fn-post-session-awaiting told))))))

(defun fn-scr-repin (conn fn-cat)
  (declare (xargs :stobjs fn-cat :guard t))
  (let ((live (fn-served-conn-live conn)))
    (if (not live)
        conn
      (fn-served-make-conn-live
       (fn-served-conn-wire conn)
       (fn-scr-repin-session (fn-served-conn-session conn)
                             (fn-served-live-archive live)
                             (fn-scr-view-of (fn-served-live-version live) fn-cat)
                             fn-cat)
       (fn-served-live-archive live)
       (fn-served-conn-config conn)
       (fn-served-conn-observation conn)
       (fn-served-conn-injection conn)
       (fn-served-live-verdicts live)
       (fn-served-live-index live)
       (fn-served-live-buckets live)
       (fn-served-live-control live)
       (fn-served-pinned-make (fn-served-live-version live)
                              (fn-served-live-frontier live) t)
       live))))

(defthm fn-scr-repin-is-served-repin
  (implies (fn-scr-conn-okp conn fn-arena fn-cat)
           (equal (fn-scr-repin conn fn-cat)
                  (fn-served-repin conn)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scr-repin fn-served-repin fn-scr-repin-session
                                fn-served-repin-session fn-scr-conn-okp fn-scr-live-catalogp
                                fn-scr-fields-catalogp fn-scr-catalogp fn-served-pinned-fields)
                              (theory 'minimal-theory))
           :use ((:instance fn-scr-reselect-is-served-reselect
                            (inner (fn-post-session-base
                                    (fn-peer-session-base
                                     (fn-auth-session-base (fn-served-conn-session conn)))))
                            (archive (fn-served-live-archive (fn-served-conn-live conn)))
                            (v (fn-scr-view-of (fn-served-live-version (fn-served-conn-live conn))
                                               fn-cat)))))))

(defun fn-scr-dispatch (conn event live trie lver arts cache fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)
                  :verify-guards nil))
  (if (fn-served-advance-eventp event)
      (let ((r (fn-scr-dispatch-core (fn-scr-repin conn fn-cat) event live trie lver arts cache fn-arena fn-cat)))
        (if (fn-served-selectedp (fn-served-result-effects r))
            r
          (fn-served-make-result
           (fn-served-conn-with-wire conn (fn-served-conn-wire (fn-served-result-conn r)))
           (fn-served-result-effects r))))
    (fn-scr-dispatch-core conn event live trie lver arts cache fn-arena fn-cat)))

(defthm fn-scr-dispatch-is-scar-dispatch
  (implies (and (fn-gacc-okp cache) (fn-scr-live-joinp trie lver arts fn-arena fn-cat) (fn-scr-conn-okp conn fn-arena fn-cat) (fn-scol-okp fn-arena fn-cat))
           (equal (fn-scr-dispatch conn event live trie lver arts cache fn-arena fn-cat)
                  (fn-scar-dispatch conn event live trie arts fn-arena)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scr-dispatch fn-scar-dispatch fn-scr-conn-okp
                                fn-scr-dispatch-core-is-scar-dispatch-core
                                fn-scr-conn-catalogp-of-repin)
                              (theory 'minimal-theory))
           :use ((:instance fn-scr-repin-is-served-repin)))))

(verify-guards fn-scr-dispatch)

(defthm fn-scr-conn-okp-of-scar-dispatch
  (implies (fn-scr-conn-okp conn fn-arena fn-cat)
           (fn-scr-conn-okp (fn-served-result-conn (fn-scar-dispatch conn event live trie arts fn-arena))
                            fn-arena fn-cat))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scar-dispatch fn-scr-conn-okp-of-scar-dispatch-core
                                fn-scr-conn-okp-of-repin fn-scr-conn-okp-of-with-wire
                                fn-served-result-conn-of-fn-served-make-result)
                              (theory 'minimal-theory)))))

; The event fold and the span scan execute by loops (lane depth-debt,
; PRF-919): the recursion took one control-stack frame per event and per
; framed event of a read (up to 262,708 octets).  Each loop threads the
; connection forward as the recursion does and carries the effects reversed
; (fn-ag-rev-onto); the :logic is the recursion, unchanged.
(local
 (defthm fn-scr-rev-onto-of-rev-onto
   (equal (fn-ag-rev-onto (fn-ag-rev-onto a acc) b)
          (fn-ag-rev-onto acc (append a b)))))

(defun fn-scr-dispatch-events-loop (conn events live trie lver arts cache fn-arena fn-cat acc)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)
                  :verify-guards nil))
  (if (consp events)
      (let ((here (fn-scr-dispatch conn (car events) live trie lver arts cache fn-arena fn-cat)))
        (fn-scr-dispatch-events-loop
         (fn-served-result-conn here) (cdr events) live trie lver arts cache fn-arena fn-cat
         (fn-ag-rev-onto (fn-served-result-effects here) acc)))
    (fn-served-make-result conn (fn-ag-rev-onto acc nil))))

(defun fn-scr-dispatch-events (conn events live trie lver arts cache fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)
                  :verify-guards nil))
  (mbe :logic
  (if (consp events)
      (let* ((here (fn-scr-dispatch conn (car events) live trie lver arts cache fn-arena fn-cat))
             (tail (fn-scr-dispatch-events (fn-served-result-conn here)
                                           (cdr events) live trie lver arts cache fn-arena fn-cat)))
        (fn-served-make-result
         (fn-served-result-conn tail)
         (mbe :logic (append (fn-served-result-effects here)
                             (fn-served-result-effects tail))
              :exec (fn-ag-append (fn-served-result-effects here)
                                  (fn-served-result-effects tail)))))
    (fn-served-make-result conn nil))
  :exec (fn-scr-dispatch-events-loop conn events live trie lver arts cache fn-arena fn-cat nil)))

(defthm fn-scr-dispatch-events-loop-is-rev-onto
  (equal (fn-scr-dispatch-events-loop conn events live trie lver arts cache fn-arena fn-cat acc)
         (fn-served-make-result
          (fn-served-result-conn
           (fn-scr-dispatch-events conn events live trie lver arts cache fn-arena fn-cat))
          (fn-ag-rev-onto acc (fn-served-result-effects
                               (fn-scr-dispatch-events conn events live trie lver arts
                                                       cache fn-arena fn-cat)))))
  :hints (("Goal" :induct (fn-scr-dispatch-events-loop conn events live trie lver arts
                                                       cache fn-arena fn-cat acc)
                  :in-theory (disable fn-scr-dispatch))))

(defthm fn-scr-dispatch-events-is-scar-dispatch-events
  (implies (and (fn-gacc-okp cache) (fn-scr-live-joinp trie lver arts fn-arena fn-cat) (fn-scr-conn-okp conn fn-arena fn-cat) (fn-scol-okp fn-arena fn-cat))
           (equal (fn-scr-dispatch-events conn events live trie lver arts cache fn-arena fn-cat)
                  (fn-scar-dispatch-events conn events live trie arts fn-arena)))
  :hints (("Goal" :induct (fn-scr-dispatch-events conn events live trie lver arts cache fn-arena fn-cat)
           :in-theory (union-theories
                       '(fn-scr-dispatch-events fn-scar-dispatch-events
                         fn-scr-dispatch-is-scar-dispatch fn-scr-conn-okp-of-scar-dispatch)
                       (theory 'minimal-theory)))))

(verify-guards fn-scr-dispatch-events-loop)

(verify-guards fn-scr-dispatch-events
  :hints (("Goal" :expand ((fn-scr-dispatch-events conn events live trie lver arts cache fn-arena fn-cat))
                  :in-theory (disable fn-scr-dispatch))))

(defthm fn-scr-conn-okp-of-scar-dispatch-events
  (implies (fn-scr-conn-okp conn fn-arena fn-cat)
           (fn-scr-conn-okp (fn-served-result-conn
                             (fn-scar-dispatch-events conn events live trie arts fn-arena))
                            fn-arena fn-cat))
  :hints (("Goal" :induct (fn-scar-dispatch-events conn events live trie arts fn-arena)
           :in-theory (union-theories
                       '(fn-scar-dispatch-events fn-scr-conn-okp-of-scar-dispatch
                         fn-served-result-conn-of-fn-served-make-result)
                       (theory 'minimal-theory)))))

(defun fn-scr-feed-byte (conn byte live trie lver arts cache fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (fn-wire-fast-statep (fn-served-conn-wire conn))
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :verify-guards nil))
  (let ((fed (fn-wire-feed-byte (fn-served-conn-wire conn) byte)))
    (fn-scr-dispatch-events
     (fn-served-conn-with-wire conn (fn-wire-result-state fed))
     (fn-wire-result-events fed) live trie lver arts cache fn-arena fn-cat)))

(defthm fn-scr-feed-byte-is-scar-feed-byte
  (implies (and (fn-gacc-okp cache) (fn-scr-live-joinp trie lver arts fn-arena fn-cat) (fn-scr-conn-okp conn fn-arena fn-cat) (fn-scol-okp fn-arena fn-cat))
           (equal (fn-scr-feed-byte conn byte live trie lver arts cache fn-arena fn-cat)
                  (fn-scar-feed-byte conn byte live trie arts fn-arena)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scr-feed-byte fn-scar-feed-byte
                                fn-scr-dispatch-events-is-scar-dispatch-events
                                fn-scr-conn-okp-of-with-wire)
                              (theory 'minimal-theory)))))

(verify-guards fn-scr-feed-byte)

(defthm fn-scr-conn-okp-of-scar-feed-byte
  (implies (fn-scr-conn-okp conn fn-arena fn-cat)
           (fn-scr-conn-okp (fn-served-result-conn (fn-scar-feed-byte conn byte live trie arts fn-arena))
                            fn-arena fn-cat))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scar-feed-byte fn-scr-conn-okp-of-scar-dispatch-events
                                fn-scr-conn-okp-of-with-wire)
                              (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; The span layers (books/served-span.lisp) with the catalog.

(defun fn-scr-feed-span (conn i end live trie lver arts cache fn-octets fn-arena fn-cat)
  (declare (xargs :stobjs (fn-octets fn-arena fn-cat)
                  :guard (and (fn-wire-fast-statep (fn-served-conn-wire conn))
                              (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets))
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :measure (nfix (- end i))
                  :verify-guards nil
                  :hints (("Goal" :in-theory (disable fn-scr-feed-byte
                                                      fn-served-submission)))))
  (if (or (not (natp i)) (not (natp end)) (>= i end)
          (fn-served-closed-wirep (fn-served-conn-wire conn))
          (fn-served-haltedp conn))
      (fn-served-counted-make 0 (fn-served-make-result conn nil))
    (let ((here (fn-scr-feed-byte conn (fn-octets-get i fn-octets) live trie lver arts cache fn-arena fn-cat)))
      (if (fn-served-submission (fn-served-result-effects here))
          (fn-served-counted-make
           1 (fn-served-make-result (fn-served-result-conn here)
                                    (fn-served-result-effects here)))
        (let* ((tail (fn-scr-feed-span (fn-served-result-conn here) (+ 1 i) end
                                       live trie lver arts cache fn-octets fn-arena fn-cat))
               (result (fn-served-counted-result tail)))
          (fn-served-counted-make
           (+ 1 (fn-served-counted-consumed tail))
           (fn-served-make-result
            (fn-served-result-conn result)
            (mbe :logic (append (fn-served-result-effects here)
                                (fn-served-result-effects result))
                 :exec (fn-ag-append (fn-served-result-effects here)
                                     (fn-served-result-effects result))))))))))

(defthm fn-scr-feed-span-is-scar-feed-span
  (implies (and (fn-gacc-okp cache) (fn-scr-live-joinp trie lver arts fn-arena fn-cat) (fn-scr-conn-okp conn fn-arena fn-cat) (fn-scol-okp fn-arena fn-cat))
           (equal (fn-scr-feed-span conn i end live trie lver arts cache fn-octets fn-arena fn-cat)
                  (fn-scar-feed-span conn i end live trie arts fn-octets fn-arena)))
  :hints (("Goal" :induct (fn-scr-feed-span conn i end live trie lver arts cache fn-octets fn-arena fn-cat)
           :in-theory (union-theories
                       '(fn-scr-feed-span fn-scar-feed-span
                         fn-scr-feed-byte-is-scar-feed-byte fn-scr-conn-okp-of-scar-feed-byte)
                       (theory 'minimal-theory)))))

; The wire stays fast through the catalog chain, unconditionally (the guards
; of the folds need it without the catalog hypothesis).
(defthm fn-scr-repin-keeps-wire
  (equal (fn-served-conn-wire (fn-scr-repin conn fn-cat))
         (fn-served-conn-wire conn))
  :hints (("Goal" :in-theory (e/d (fn-scr-repin) (fn-scr-repin-session)))))

(defthm fn-scr-dispatch-preserves-fast-statep
  (implies (fn-wire-fast-statep (fn-served-conn-wire conn))
           (fn-wire-fast-statep
            (fn-served-conn-wire
             (fn-served-result-conn (fn-scr-dispatch conn event live trie lver arts cache fn-arena fn-cat)))))
  :hints (("Goal"
           :in-theory (disable fn-wire-fast-statep
                               fn-wire-begin-article-with-line-limit
                               fn-wire-article-line-limit
                               fn-scr-auth-step fn-post-offeredp fn-scr-repin
                               fn-wire-begin-article-with-line-limit-preserves-fast-statep
                               ;; the -is- equations open fn-scr-catalogp on
                               ;; every auth arm (4.6 s -> 0.1 s without them)
                               fn-scr-auth-step-is-scar-auth-step-pinned fn-scr-catalogp
                               fn-gidx-pin-correspondencep fn-scat-article-idp-is-msgid-idp
                               fn-nntp-article-idp-is-consp fn-nntp-index-msgid-okp-stringp
                               fn-cp-id-length-bound)
           :use ((:instance fn-wire-begin-article-with-line-limit-preserves-fast-statep
                            (wire-state (fn-served-conn-wire conn))
                            (article-line-limit
                             (fn-wire-article-line-limit
                              (fn-served-conn-wire conn))))))))

(defthm fn-scr-dispatch-events-preserves-fast-statep
  (implies (fn-wire-fast-statep (fn-served-conn-wire conn))
           (fn-wire-fast-statep
            (fn-served-conn-wire
             (fn-served-result-conn
              (fn-scr-dispatch-events conn events live trie lver arts cache fn-arena fn-cat)))))
  :hints (("Goal" :induct (fn-scr-dispatch-events conn events live trie lver arts cache fn-arena fn-cat)
           :in-theory (disable fn-scr-dispatch fn-wire-fast-statep))))

(defthm fn-scr-feed-byte-preserves-fast-statep
  (implies (fn-wire-fast-statep (fn-served-conn-wire conn))
           (fn-wire-fast-statep
            (fn-served-conn-wire
             (fn-served-result-conn (fn-scr-feed-byte conn byte live trie lver arts cache fn-arena fn-cat)))))
  :hints (("Goal"
           :in-theory (e/d (fn-scr-feed-byte)
                           (fn-served-feed-byte-preserves-fast-statep
                            fn-served-feed-byte fn-scr-dispatch-events
                            fn-wire-feed-byte fn-wire-fast-statep))
           :use ((:instance fn-wire-feed-byte-preserves-fast-statep
                            (wire-state (fn-served-conn-wire conn)))
                 (:instance fn-scr-dispatch-events-preserves-fast-statep
                            (conn (fn-served-conn-with-wire
                                   conn (fn-wire-result-state
                                         (fn-wire-feed-byte (fn-served-conn-wire conn) byte))))
                            (events (fn-wire-result-events
                                     (fn-wire-feed-byte (fn-served-conn-wire conn) byte))))))))

; The span's two inductions run in the definition and these two field
; equations alone (served-catalog's enabled theory cost 6.9 s and 5.2 s).
(local (defthm fn-scr-consumed-of-counted-make
   (equal (fn-served-counted-consumed (fn-served-counted-make n r)) n)
   :hints (("Goal" :in-theory (enable fn-served-counted-make fn-served-counted-consumed)))))

(local (defthm fn-scr-result-of-counted-make
   (equal (fn-served-counted-result (fn-served-counted-make n r)) r)
   :hints (("Goal" :in-theory (enable fn-served-counted-make fn-served-counted-result)))))

(defthm fn-scr-feed-span-consumed-is-natural
  (natp (fn-served-counted-consumed
         (fn-scr-feed-span conn i end live trie lver arts cache fn-octets fn-arena fn-cat)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :induct (fn-scr-feed-span conn i end live trie lver arts cache fn-octets fn-arena fn-cat)
           :in-theory (union-theories '(fn-scr-feed-span fn-scr-consumed-of-counted-make natp)
                                      (theory 'minimal-theory)))))

(local
 (defthm fn-scr-span-feed-preserves-fast-statep
   (implies (fn-wire-fast-statep (fn-served-conn-wire conn))
            (fn-wire-fast-statep
             (fn-served-conn-wire
              (fn-served-result-conn
               (fn-served-counted-result
                (fn-scr-feed-span conn i end live trie lver arts cache fn-octets fn-arena fn-cat))))))
   :hints (("Goal" :induct (fn-scr-feed-span conn i end live trie lver arts cache fn-octets fn-arena fn-cat)
            :in-theory (union-theories '(fn-scr-feed-span fn-scr-result-of-counted-make
                                         fn-served-result-conn-of-fn-served-make-result
                                         fn-scr-feed-byte-preserves-fast-statep)
                                       (theory 'minimal-theory))))))

(verify-guards fn-scr-feed-span
  :hints (("Goal"
           :in-theory (e/d (fn-served-counted-make fn-served-counted-result)
                           (fn-scr-feed-byte fn-wire-fast-statep
                            fn-served-counted-consumed))
           :use ((:instance fn-scr-feed-byte-preserves-fast-statep
                            (byte (fn-octets-get i fn-octets)))))))

(in-theory (disable fn-scr-feed-span))

; -----------------------------------------------------------------------------
; The span fold one framed event at a time (PKT-479 on the catalog chain).
;
; books/served-scan.lisp fn-scar-scan-span with the catalog carried: the wire
; machine runs over the range until its first event (books/wire-scan.lisp
; fn-wire-scan, a line at a time), and the connection is rebuilt and the event
; dispatched once per event, as fn-scr-feed-byte dispatches it.  The PKT-600
; yield after a submission and the stops at a closed wire and a TLS handshake
; are fn-scr-feed-span's.  fn-scr-step-span-core runs it as the executable of
; fn-scr-feed-span (KEYSTONE fn-scr-scan-span-is-feed-span, no hypothesis).

; The scan and its correspondence need none of the catalog relation: the -is-
; equations above would open fn-scr-catalogp on every rewrite of the fold
; (the split lemma cost 4.9 M prover steps with them, 0.9 M without).
(local (in-theory (disable fn-scr-conn-okp fn-scr-catalogp fn-scr-conn-catalogp
                          fn-scr-live-catalogp fn-scr-fields-catalogp
                          fn-gidx-pin-correspondencep fn-scr-conn-okp-of-with-wire
                          fn-scr-feed-span-is-scar-feed-span fn-scr-feed-byte-is-scar-feed-byte
                          fn-scr-dispatch-events-is-scar-dispatch-events
                          fn-nntp-article-idp-is-consp fn-scat-article-idp-is-msgid-idp)))

(defun fn-scr-scan-span-loop (conn i end live trie lver arts cache fn-octets fn-arena fn-cat
                                   consumed acc)
  (declare (xargs :stobjs (fn-octets fn-arena fn-cat)
                  :guard (and (fn-wire-fast-statep (fn-served-conn-wire conn))
                              (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets))
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)
                              (acl2-numberp consumed))
                  :measure (nfix (- end i))
                  :verify-guards nil
                  :hints (("Goal" :in-theory (disable fn-scr-dispatch-events
                                                      fn-served-submission)))))
  (if (or (not (natp i)) (not (natp end)) (>= i end)
          (fn-served-closed-wirep (fn-served-conn-wire conn))
          (fn-served-haltedp conn))
      (fn-served-counted-make consumed (fn-served-make-result conn (fn-ag-rev-onto acc nil)))
    (let* ((w (fn-wire-scan (fn-served-conn-wire conn) i end fn-octets))
           (next (fn-wsp-next w))
           (here (fn-scr-dispatch-events
                  (fn-served-conn-with-wire conn (fn-wsp-state w))
                  (fn-wsp-events w) live trie lver arts cache fn-arena fn-cat)))
      (if (fn-served-submission (fn-served-result-effects here))
          (fn-served-counted-make
           (+ consumed (- next i))
           (fn-served-make-result (fn-served-result-conn here)
                                  (fn-ag-rev-onto acc (fn-served-result-effects here))))
        (fn-scr-scan-span-loop (fn-served-result-conn here) next end
                               live trie lver arts cache fn-octets fn-arena fn-cat
                               (+ consumed (- next i))
                               (fn-ag-rev-onto (fn-served-result-effects here) acc))))))

(defun fn-scr-scan-span (conn i end live trie lver arts cache fn-octets fn-arena fn-cat)
  (declare (xargs :stobjs (fn-octets fn-arena fn-cat)
                  :guard (and (fn-wire-fast-statep (fn-served-conn-wire conn))
                              (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets))
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :measure (nfix (- end i))
                  :verify-guards nil
                  :hints (("Goal" :in-theory (disable fn-scr-dispatch-events
                                                      fn-served-submission)))))
  (mbe :logic
  (if (or (not (natp i)) (not (natp end)) (>= i end)
          (fn-served-closed-wirep (fn-served-conn-wire conn))
          (fn-served-haltedp conn))
      (fn-served-counted-make 0 (fn-served-make-result conn nil))
    (let* ((w (fn-wire-scan (fn-served-conn-wire conn) i end fn-octets))
           (next (fn-wsp-next w))
           (here (fn-scr-dispatch-events
                  (fn-served-conn-with-wire conn (fn-wsp-state w))
                  (fn-wsp-events w) live trie lver arts cache fn-arena fn-cat)))
      ;; PKT-600: yield after the event that completed a submission; the host
      ;; re-enters at i + consumed.
      (if (fn-served-submission (fn-served-result-effects here))
          (fn-served-counted-make
           (- next i)
           (fn-served-make-result (fn-served-result-conn here)
                                  (fn-served-result-effects here)))
        (let* ((tail (fn-scr-scan-span (fn-served-result-conn here) next end
                                       live trie lver arts cache fn-octets fn-arena fn-cat))
               (tail-result (fn-served-counted-result tail)))
          (fn-served-counted-make
           (+ (- next i) (fn-served-counted-consumed tail))
           (fn-served-make-result
            (fn-served-result-conn tail-result)
            (mbe :logic (append (fn-served-result-effects here)
                                (fn-served-result-effects tail-result))
                 :exec (fn-ag-append (fn-served-result-effects here)
                                     (fn-served-result-effects tail-result)))))))))
  :exec (fn-scr-scan-span-loop conn i end live trie lver arts cache fn-octets fn-arena fn-cat 0 nil)))

(defthm fn-scr-scan-span-loop-is-rev-onto
  (implies (acl2-numberp consumed)
           (equal (fn-scr-scan-span-loop conn i end live trie lver arts cache fn-octets fn-arena fn-cat
                                         consumed acc)
                  (let ((r (fn-scr-scan-span conn i end live trie lver arts cache fn-octets fn-arena
                                             fn-cat)))
                    (fn-served-counted-make
                     (+ consumed (fn-served-counted-consumed r))
                     (fn-served-make-result
                      (fn-served-result-conn (fn-served-counted-result r))
                      (fn-ag-rev-onto acc (fn-served-result-effects
                                           (fn-served-counted-result r))))))))
  :hints (("Goal" :induct (fn-scr-scan-span-loop conn i end live trie lver arts cache fn-octets
                                                 fn-arena fn-cat consumed acc)
                  :in-theory (e/d (fn-served-counted-make fn-served-counted-result
                                   fn-served-counted-consumed)
                                  (fn-scr-dispatch-events fn-wire-scan
                                   fn-served-submission fn-served-closed-wirep
                                   fn-served-haltedp fn-wire-fast-statep)))))

(defthm fn-scr-scan-span-consumed-is-natural
  (natp (fn-served-counted-consumed
         (fn-scr-scan-span conn i end live trie lver arts cache fn-octets fn-arena fn-cat)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :induct (fn-scr-scan-span conn i end live trie lver arts cache fn-octets fn-arena fn-cat)
           :in-theory (e/d (fn-served-counted-make fn-served-counted-consumed)
                           (fn-scr-dispatch-events fn-wire-fast-statep)))))

(verify-guards fn-scr-scan-span-loop
  :hints (("Goal"
           :in-theory (e/d (fn-served-counted-make fn-served-counted-result)
                           (fn-scr-dispatch-events fn-wire-fast-statep
                            fn-served-counted-consumed))
           :use ((:instance fn-scr-dispatch-events-preserves-fast-statep
                            (conn (fn-served-conn-with-wire
                                   conn (fn-wsp-state (fn-wire-scan (fn-served-conn-wire conn)
                                                                    i end fn-octets))))
                            (events (fn-wsp-events (fn-wire-scan (fn-served-conn-wire conn)
                                                                 i end fn-octets))))))))

(local
 (defthm fn-scr-scan-span-is-its-counted-parts
   (let ((r (fn-scr-scan-span conn i end live trie lver arts cache fn-octets fn-arena fn-cat)))
     (equal (fn-served-counted-make
             (+ 0 (fn-served-counted-consumed r))
             (fn-served-make-result
              (fn-served-result-conn (fn-served-counted-result r))
              (fn-ag-rev-onto nil (fn-served-result-effects (fn-served-counted-result r)))))
            r))
   :hints (("Goal" :expand ((fn-scr-scan-span conn i end live trie lver arts cache fn-octets fn-arena fn-cat))
                   :in-theory (e/d (fn-served-counted-make fn-served-counted-result
                                    fn-served-counted-consumed)
                                   (fn-scr-dispatch-events fn-wire-scan
                                    fn-served-submission fn-served-closed-wirep
                                    fn-served-haltedp fn-wire-fast-statep
                                    fn-scr-scan-span-loop-is-rev-onto))))))

(local
 (defthm fn-scr-scan-span-loop-at-zero
   (equal (fn-scr-scan-span-loop conn i end live trie lver arts cache fn-octets fn-arena fn-cat 0 nil)
          (fn-scr-scan-span conn i end live trie lver arts cache fn-octets fn-arena fn-cat))
   :hints (("Goal" :use ((:instance fn-scr-scan-span-loop-is-rev-onto (consumed 0) (acc nil))
                         fn-scr-scan-span-is-its-counted-parts)
                   :in-theory (disable fn-scr-scan-span-loop-is-rev-onto
                                       fn-scr-scan-span-is-its-counted-parts
                                       fn-scr-scan-span fn-scr-scan-span-loop
                                       fn-served-counted-make fn-served-make-result
                                       fn-ag-rev-onto)))))

(verify-guards fn-scr-scan-span
  :hints (("Goal"
           :in-theory (e/d (fn-served-counted-make fn-served-counted-result)
                           (fn-scr-dispatch-events fn-wire-fast-statep
                            fn-served-counted-consumed))
           :use ((:instance fn-scr-dispatch-events-preserves-fast-statep
                            (conn (fn-served-conn-with-wire
                                   conn (fn-wsp-state (fn-wire-scan (fn-served-conn-wire conn)
                                                                    i end fn-octets))))
                            (events (fn-wsp-events (fn-wire-scan (fn-served-conn-wire conn)
                                                                 i end fn-octets))))))))

; The correspondence: the scan is the byte fold, split at the wire's first event.

(local
 (defthm fn-scrs-with-wire-twice
   (equal (fn-served-conn-with-wire (fn-served-conn-with-wire conn w1) w2)
          (fn-served-conn-with-wire conn w2))
   :hints (("Goal" :in-theory (enable fn-served-conn-with-wire)))))

(local
 (defthm fn-scrs-handshaking-of-with-wire
   (equal (fn-served-haltedp (fn-served-conn-with-wire conn w))
          (fn-served-haltedp conn))
   :hints (("Goal" :in-theory (enable fn-served-haltedp fn-served-quitp fn-served-tls-handshakingp)))))

(local
 (defthm fn-scrs-feed-byte-without-event-keeps-open
   (implies (and (not (equal (fn-wire-state-mode wire-state) :closed))
                 (not (consp (fn-wire-result-events
                              (fn-wire-feed-byte wire-state byte)))))
            (not (equal (fn-wire-state-mode
                         (fn-wire-result-state (fn-wire-feed-byte wire-state byte)))
                        :closed)))
   :hints (("Goal" :in-theory (enable fn-wire-feed-byte fn-wire-after-line
                                      fn-wire-close)))))

(local
 (defthm fn-scrs-dispatch-no-events
   (implies (not (consp events))
            (equal (fn-scr-dispatch-events conn events live trie lver arts cache fn-arena fn-cat)
                   (fn-served-make-result conn nil)))
   :hints (("Goal" :expand ((fn-scr-dispatch-events conn events live trie lver arts cache fn-arena fn-cat))))))

(local
 (defun fn-scrs-ind (conn i end fn-octets)
   (declare (xargs :stobjs fn-octets :measure (nfix (- end i))
                   :verify-guards nil))
   (if (or (not (natp i)) (not (natp end)) (>= i end))
       (list conn i end)
     (let ((r (fn-wire-feed-byte (fn-served-conn-wire conn)
                                 (fn-octets-get i fn-octets))))
       (if (consp (fn-wire-result-events r))
           (list conn i end)
         (fn-scrs-ind (fn-served-conn-with-wire conn (fn-wire-result-state r))
                      (+ 1 i) end fn-octets))))))

; The byte fold over [i, end) splits at the wire's first event: every octet
; before it only moves the wire, and the event is dispatched where
; fn-scr-feed-byte dispatches it.
(local
 (defthm fn-scrs-feed-span-splits
   (implies (and (not (fn-served-closed-wirep (fn-served-conn-wire conn)))
                 (not (fn-served-haltedp conn))
                 (natp i) (natp end) (< i end))
            (equal
             (fn-scr-feed-span conn i end live trie lver arts cache fn-octets fn-arena fn-cat)
             (let* ((w (fn-wire-span-fold (fn-served-conn-wire conn) i end
                                          fn-octets))
                    (next (fn-wsp-next w))
                    (here (fn-scr-dispatch-events
                           (fn-served-conn-with-wire conn (fn-wsp-state w))
                           (fn-wsp-events w) live trie lver arts cache fn-arena fn-cat)))
               (if (fn-served-submission (fn-served-result-effects here))
                   (fn-served-counted-make
                    (- next i)
                    (fn-served-make-result (fn-served-result-conn here)
                                           (fn-served-result-effects here)))
                 (let* ((tail (fn-scr-feed-span (fn-served-result-conn here) next end
                                                live trie lver arts cache fn-octets fn-arena fn-cat))
                        (tail-result (fn-served-counted-result tail)))
                   (fn-served-counted-make
                    (+ (- next i) (fn-served-counted-consumed tail))
                    (fn-served-make-result
                     (fn-served-result-conn tail-result)
                     (append (fn-served-result-effects here)
                             (fn-served-result-effects tail-result)))))))))
   :hints (("Goal" :induct (fn-scrs-ind conn i end fn-octets)
            :in-theory (e/d (fn-scr-feed-byte fn-served-closed-wirep
                             fn-served-counted-make fn-served-counted-consumed
                             fn-served-counted-result)
                            (fn-wire-feed-byte fn-wire-fast-statep
                             fn-scr-dispatch-events
                             fn-served-submission fn-served-haltedp fn-served-quitp fn-served-tls-handshakingp))
            :expand ((fn-wire-span-fold (fn-served-conn-wire conn)
                                        i end fn-octets)
                     (fn-scr-feed-span conn i end live trie lver arts cache fn-octets fn-arena fn-cat))))))

; KEYSTONE (PKT-479 on the catalog chain), no hypothesis: the event-at-a-time
; scan the host-called read runs is the catalog chain's byte fold, on every
; connection and every range.
(defthm fn-scr-scan-span-is-feed-span
  (equal (fn-scr-scan-span conn i end live trie lver arts cache fn-octets fn-arena fn-cat)
         (fn-scr-feed-span conn i end live trie lver arts cache fn-octets fn-arena fn-cat))
  :hints (("Goal" :induct (fn-scr-scan-span conn i end live trie lver arts cache fn-octets fn-arena fn-cat)
           :in-theory (e/d (fn-scr-scan-span fn-wire-scan-is-span-fold)
                           (fn-scr-dispatch-events fn-wire-fast-statep
                            fn-served-submission fn-served-closed-wirep
                            fn-served-haltedp fn-served-quitp fn-served-tls-handshakingp)))
          (and stable-under-simplificationp
               '(:expand ((fn-scr-feed-span conn i end live trie lver arts cache fn-octets
                                            fn-arena fn-cat))))))

(in-theory (disable fn-scr-scan-span))

(local (in-theory (enable fn-scr-conn-okp fn-scr-catalogp fn-scr-conn-catalogp
                          fn-scr-live-catalogp fn-scr-fields-catalogp
                          fn-gidx-pin-correspondencep fn-scr-conn-okp-of-with-wire
                          fn-scr-feed-span-is-scar-feed-span fn-scr-feed-byte-is-scar-feed-byte
                          fn-scr-dispatch-events-is-scar-dispatch-events
                          fn-nntp-article-idp-is-consp fn-scat-article-idp-is-msgid-idp)))

(defun fn-scr-step-span-core (conn i end live trie lver arts cache fn-octets fn-arena fn-cat)
  (declare (xargs :stobjs (fn-octets fn-arena fn-cat)
                  :guard (and (fn-wire-fast-statep (fn-served-conn-wire conn))
                              (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets))
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))))
  (let* ((wire (fn-served-conn-wire conn))
         ;; PKT-479: executed one framed event at a time (fn-scr-scan-span,
         ;; equal to the byte fold by fn-scr-scan-span-is-feed-span).
         (fed (mbe :logic (fn-scr-feed-span conn i end live trie lver arts cache fn-octets fn-arena fn-cat)
                   :exec (fn-scr-scan-span conn i end live trie lver arts cache fn-octets fn-arena fn-cat)))
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

(defthm fn-scr-step-span-core-is-scar-step-span-core
  (implies (and (fn-gacc-okp cache) (fn-scr-live-joinp trie lver arts fn-arena fn-cat) (fn-scr-conn-okp conn fn-arena fn-cat) (fn-scol-okp fn-arena fn-cat))
           (equal (fn-scr-step-span-core conn i end live trie lver arts cache fn-octets fn-arena fn-cat)
                  (fn-scar-step-span-core conn i end live trie arts fn-octets fn-arena)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scr-step-span-core fn-scar-step-span-core
                                fn-scr-feed-span-is-scar-feed-span)
                              (theory 'minimal-theory)))))

(defun fn-scr-step-span-fast (conn i end live trie lver arts cache fn-octets fn-arena fn-cat)
  (declare (xargs :stobjs (fn-octets fn-arena fn-cat)
                  :guard (and (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets))
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))))
  (if (not (fn-wire-fast-statep (fn-served-conn-wire conn)))
      (fn-served-counted-make 0 (fn-served-make-result conn nil))
    (fn-scr-step-span-core conn i end live trie lver arts cache fn-octets fn-arena fn-cat)))

(defthm fn-scr-step-span-fast-is-scar-step-span-fast
  (implies (and (fn-gacc-okp cache) (fn-scr-live-joinp trie lver arts fn-arena fn-cat) (fn-scr-conn-okp conn fn-arena fn-cat) (fn-scol-okp fn-arena fn-cat))
           (equal (fn-scr-step-span-fast conn i end live trie lver arts cache fn-octets fn-arena fn-cat)
                  (fn-scar-step-span-fast conn i end live trie arts fn-octets fn-arena)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scr-step-span-fast fn-scar-step-span-fast
                                fn-scr-step-span-core-is-scar-step-span-core)
                              (theory 'minimal-theory)))))

(in-theory (disable fn-scr-step-span-core fn-scr-step-span-fast))

; The owner's connection ID, as the served machine sees it.
(defun-nx fn-scr-owner-catalogp (o id fn-arena fn-cat)
  (let ((conn (fn-own-find-conn id (fn-own-conns o))))
    (implies conn
             (fn-scr-conn-okp (fn-own-tls-served-conn o conn) fn-arena fn-cat))))

(defun fn-scr-own-read-span (o id i end cache fn-octets fn-arena fn-cat)
  (declare (xargs :stobjs (fn-octets fn-arena fn-cat)
                  :guard (and (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets))
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))))
  (let ((conn (fn-own-find-conn id (fn-own-conns o)))
        (live (fn-sn-node (fn-own-store o)))
        (trie (fn-own-view-index (fn-own-view o)))
        (lver (fn-own-view-version (fn-own-view o)))
        (arts (fn-state-articles (fn-own-view-archive (fn-own-view o)))))
    (if conn
        (let* ((counted
                 (fn-scr-step-span-fast
                  (fn-own-tls-served-conn o conn) i end live trie lver arts cache fn-octets fn-arena fn-cat))
               (result
                 (fn-scar-finish-read
                  o conn (fn-served-counted-result counted) live)))
          (fn-own-tls-make-result
           (fn-served-counted-consumed counted) (car result) (cdr result)
           (fn-own-result-repinned (fn-served-counted-result counted))))
      (fn-own-tls-make-result (nfix (- end i)) nil o nil))))

(defthm fn-scr-served-conn-live-is-view-live
  (equal (fn-served-conn-live (fn-own-tls-served-conn o conn))
         (fn-own-view-live (fn-own-view o)))
  :hints (("Goal" :in-theory (e/d (fn-own-tls-served-conn fn-own-served-conn)
                                  (fn-served-make-conn-live fn-own-view-live)))))

(defthm fn-scr-owner-catalogp-gives-live-joinp
  (implies (and (fn-scr-owner-catalogp o id fn-arena fn-cat)
                (fn-scar-view-indexedp o)
                (fn-own-find-conn id (fn-own-conns o)))
           (fn-scr-live-joinp (fn-own-view-index (fn-own-view o))
                              (fn-own-view-version (fn-own-view o))
                              (fn-state-articles (fn-own-view-archive (fn-own-view o)))
                              fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-scr-owner-catalogp fn-scr-conn-okp fn-scr-live-catalogp
                                   fn-scr-fields-catalogp fn-scr-catalogp fn-scr-live-joinp fn-scar-view-indexedp
                                   fn-gidx-pin-trie-of-pin-with-control)
                                  (fn-own-tls-served-conn fn-cat-view-articles fn-scr-view-of
                                   fn-midx-correspondencep fn-scr-conn-catalogp
                                   fn-own-view-live fn-statep fn-gidx-pin-correspondencep))
           :use ((:instance fn-own-view-live-fields (view (fn-own-view o)))))))
;; With the peer arm reading the catalog (fn-scr-peer-arm), the chain is the
;; scar chain when the view's trie is its visible list's index as well
;; (fn-scar-view-indexedp): the scar arm reads that trie.  The host's owner
;; carries it: fn-sjh-okp (books/served-catalog-join-host.lisp) has it as a
;; conjunct, and join-f2-2 proves fn-sjh-okp kept at every owner-installing
;; host entry (books/served-catalog-join-host-entries.lisp and siblings), so
;; the hypothesis is discharged at the host level.
(defthm fn-scr-own-read-span-is-scar-own-read-span
  (implies (and (fn-gacc-okp cache) (fn-scr-owner-catalogp o id fn-arena fn-cat) (fn-scol-okp fn-arena fn-cat)
                (fn-scar-view-indexedp o))
           (equal (fn-scr-own-read-span o id i end cache fn-octets fn-arena fn-cat)
                  (fn-scar-own-read-span o id i end fn-octets fn-arena)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scr-own-read-span fn-scar-own-read-span fn-scr-owner-catalogp
                                fn-scr-step-span-fast-is-scar-step-span-fast)
                              (theory 'minimal-theory))
           :use ((:instance fn-scr-owner-catalogp-gives-live-joinp)))))

(defun fn-scr-ocfg-read-span (oc id i end cache fn-octets fn-arena fn-cat)
  (declare (xargs :stobjs (fn-octets fn-arena fn-cat)
                  :guard (and (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets))
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))))
  (let ((result (fn-scr-own-read-span (fn-ocfg-owner oc) id i end cache fn-octets fn-arena fn-cat)))
    (fn-own-tls-make-result
     (fn-own-tls-result-consumed result)
     (fn-own-tls-result-effects result)
     (fn-ocfg-with-read-owner oc id (fn-own-tls-result-owner result)
                              (fn-own-tls-result-repinned result))
     (fn-own-tls-result-repinned result))))

(defthm fn-scr-ocfg-read-span-is-scar-ocfg-read-span
  (implies (and (fn-gacc-okp cache) (fn-scr-owner-catalogp (fn-ocfg-owner oc) id fn-arena fn-cat) (fn-scol-okp fn-arena fn-cat)
                (fn-scar-view-indexedp (fn-ocfg-owner oc)))
           (equal (fn-scr-ocfg-read-span oc id i end cache fn-octets fn-arena fn-cat)
                  (fn-scar-ocfg-read-span oc id i end fn-octets fn-arena)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scr-ocfg-read-span fn-scar-ocfg-read-span
                                fn-scr-own-read-span-is-scar-own-read-span)
                              (theory 'minimal-theory)))))

; KEYSTONE.  The host's served read over the catalog is the reference read
; over the octet slice: fn-scar-ocfg-read-span-is-reference-under-ocl-relation
; (books/served-span.lisp) through the equation above.
(defthm fn-scr-ocfg-read-span-is-reference-under-ocl-relation
  (implies (and (fn-gacc-okp cache) (fn-ocl-relation oc)
                (fn-scar-view-indexedp (fn-ocfg-owner oc))
                (fn-scr-owner-catalogp (fn-ocfg-owner oc) id fn-arena fn-cat)
                (fn-scol-okp fn-arena fn-cat)
                (natp i) (natp end))
           (equal (fn-scr-ocfg-read-span oc id i end cache fn-octets fn-arena fn-cat)
                  (fn-ocfg-read-tls-prefix oc id (fn-oct-slice-list i end fn-octets) fn-arena)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scr-ocfg-read-span-is-scar-ocfg-read-span
                                fn-scar-ocfg-read-span-is-reference-under-ocl-relation)
                              (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; PKT-643: the host prepares the connection's restricted view before a read.
;
; host/owner-host.lisp fn-owner-chunk-span-at calls this with the cache it
; holds (nil at start) and the connection ID, before the read, and passes the
; result to the read (fn-oas-read-span ... CACHE ...).  For a connection whose
; session reads under a rule, at a pinned index, the rule's entry is kept,
; grown by the articles accepted since, or built (books/group-access-cache.lisp
; fn-gacc-prepare); for any other connection the cache is unchanged.
(defun fn-scr-prepare-access (cache o id)
  (declare (xargs :guard t))
  (let ((conn (fn-own-find-conn id (fn-own-conns o))))
    (if conn
        (let* ((sc (fn-own-tls-served-conn o conn))
               (read (fn-auth-access-read (fn-served-conn-session sc)
                                          (fn-served-conn-config sc)))
               (index (fn-served-conn-pinned-index sc)))
          (if (and read (fn-gidx-pinp index))
              (fn-gacc-prepare read (fn-served-conn-archive sc)
                               (fn-gidx-pin-control index) cache)
            cache))
      cache)))

;; KEYSTONE (the host's cache): preparing keeps fn-gacc-okp, the premise of
;; fn-scr-ocfg-read-span-is-reference-under-ocl-relation; the host starts
;; with nil (fn-gacc-okp-of-nil) and only prepares.
(defthm fn-scr-prepare-access-keeps-okp
  (implies (fn-gacc-okp cache)
           (fn-gacc-okp (fn-scr-prepare-access cache o id)))
  :hints (("Goal" :in-theory (e/d (fn-scr-prepare-access)
                                  (fn-gacc-prepare fn-own-tls-served-conn
                                   fn-auth-access-read fn-own-find-conn)))))

;; After preparing, a restricted command of that connection at its pin is
;; answered from the cache: the delegate builds nothing.
(defthm fn-scr-prepare-access-serves-the-pin
  (let* ((conn (fn-own-find-conn id (fn-own-conns o)))
         (sc (fn-own-tls-served-conn o conn))
         (as (fn-served-conn-session sc))
         (config (fn-served-conn-config sc))
         (index (fn-served-conn-pinned-index sc)))
    (implies (and (fn-gacc-okp cache)
                  conn
                  (fn-auth-access-read as config)
                  (fn-gidx-pinp index))
             (equal (fn-scr-cached-view as config (fn-served-conn-archive sc) index
                                        (fn-scr-prepare-access cache o id))
                    (fn-gac-view-entry (fn-auth-access-read as config)
                                       (fn-served-conn-archive sc)
                                       (fn-gidx-pin-control index)))))
  :hints (("Goal" :in-theory (e/d (fn-scr-prepare-access fn-scr-cached-view)
                                  (fn-gacc-prepare fn-own-tls-served-conn fn-gac-view-entry
                                   fn-auth-access-read fn-own-find-conn fn-gacc-view)))))

(in-theory (disable fn-scr-own-read-span fn-scr-ocfg-read-span))

;; Withdrawn from includers (lane rule-hygiene, tools/rule_cost.py).
;; Each is tried in includers' proofs and pays for its frames in
;; almost none (planning/evidence/rule-cost-*.json has the counts;
;; docs/proof-style.md section 8).  An includer that needs one
;; enables it where it is used.
(in-theory (disable (:definition fn-scr-catalogp)
                    (:definition fn-scr-conn-okp)
                    (:definition fn-scr-fields-catalogp)
                    (:rewrite fn-scr-feed-span-is-scar-feed-span)))
