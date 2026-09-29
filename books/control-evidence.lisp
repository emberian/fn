; fn: `control log' and `control evidence MESSAGE-ID', rendered by ACL2
; (PKT-209, PRF-185).
;
; A withdrawing article (a cancel, or an ordinary article with one
; Supersedes target) is decided once, when the refresh that first publishes
; it runs `fn-ctl-article-withdrawals' (books/control-visible.lisp) under
; the configuration at its own Store txid.  The owner carries the records
; it decided in its committed view (`fn-own-view-withdrawals',
; books/owner.lisp `fn-own-refresh'), and recovery rebuilds the same list
; (`fn-ctl-refresh-withdrawals-is-the-journal',
; `fn-ctl-articles-withdrawals-is-the-journal').  Until now an operator could
; not read that list, nor why a cancel withdrew nothing.
;
;   control log                 one line per withdrawal record the owner
;                               holds, in its order: target, cause,
;                               principal, the principal's cancel scope, and
;                               the configuration generation it was decided
;                               under;
;   control evidence MSGID      the decision context of MSGID: whether the
;                               owner holds the article, the txid of its
;                               acceptance record, its stored verdict, the
;                               decision the refresh made for it (the record,
;                               a decline and its reason, or none: it names
;                               no target), and every record naming MSGID as
;                               its target with that record's effect on it.
;
; The running owner renders both over the view it carries
; (`fn-cev-live-report'); with no owner the offline command renders them
; over the replayed Store, deciding the records as recovery does
; (`fn-cev-offline-report').  They travel as FNLS pages
; (books/native-live-status.lisp): a request carrying a report kind and an
; argument is FNLS frame kind 3 (`fn-cev-request-encode'); FNLS kinds 1 and
; 2 are unchanged, so an old client never meets it, and an old owner answers
; it with the plain refusal (it decodes as nothing it knows).  No FNCT kind
; is taken.
;
; KEYSTONE `fn-cev-evidence-decision-is-in-the-log': under the owner's
; maintained relation (the carried records are the journal of the carried
; archive), the decision `control evidence' prints for a stored article is
; a record of `control log' exactly when it is a withdrawal record; and
; `fn-cev-decision-line-is-a-log-line': the words of that decision are one
; of the log's lines, so the two verbs cannot disagree.
;
; Cost (pessimistic, per request, under the owner mutex): `control log' is
; one pass over the records |WS|; `control evidence' one walk of the carried
; archive N for the article, two walks of the Store's records R for its
; row and its target's row (`fn-ctl-row-event', one Message-ID compared per
; row) and one of the configuration journal, and one pass over WS.  The
; offline command decides every record as recovery does: N walks of R.  Paging bounds each reply (`fn-nls-page'), not the render.
;
; Prefix `fn-cev-' (docs/prefixes.md).
(in-package "ACL2")
(include-book "control-evidence-grammar")
(include-book "native-live-status")
(include-book "native-control-reason")
(include-book "control-visible")
; Row S3d (lane operability-5): `store inspect --group GROUP' rides the same
; frame (kind 3, code 11) as `moderation list GROUP'.
(include-book "owner-inspect-group")

; -----------------------------------------------------------------------------
; Words

(defun fn-cev-string (x)
  (declare (xargs :guard t))
  (if (and (stringp x) (not (equal x ""))) (fn-nls-text x) (fn-nls-text "-")))

; A principal's granted scope is operator data with no fixed cap (D27): the
; walk executes by a loop (lane depth-debt, PRF-919), the octets reversed
; onto ACC, equal by fn-cev-scope-words-loop-is-rev-onto.
(defun fn-cev-scope-words-loop (scope acc)
  (declare (xargs :guard t))
  (if (consp scope)
      (fn-cev-scope-words-loop
       (cdr scope)
       (let ((acc (fn-ag-rev-onto (fn-cev-string (car scope)) acc)))
         (if (consp (cdr scope)) (cons 44 acc) acc)))
    (fn-ag-rev-onto acc nil)))

(defun fn-cev-scope-words (scope)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (if (consp scope)
                  (append (fn-cev-string (car scope))
                          (if (consp (cdr scope))
                              (cons 44 (fn-cev-scope-words (cdr scope)))
                            nil))
                nil)
       :exec (fn-cev-scope-words-loop scope nil)))

(local
 (defthm fn-cev-rev-onto-of-rev-onto
   (equal (fn-ag-rev-onto (fn-ag-rev-onto x acc) y)
          (fn-ag-rev-onto acc (append x y)))))

(defthm fn-cev-scope-words-loop-is-rev-onto
  (equal (fn-cev-scope-words-loop scope acc)
         (fn-ag-rev-onto acc (fn-cev-scope-words scope)))
  :hints (("Goal" :induct (fn-cev-scope-words-loop scope acc)
                  :in-theory (union-theories
                              '(fn-cev-scope-words-loop fn-cev-scope-words
                                fn-ag-rev-onto fn-cev-rev-onto-of-rev-onto
                                car-cons cdr-cons)
                              (theory 'minimal-theory)))))

(verify-guards fn-cev-scope-words
  :hints (("Goal" :in-theory (union-theories
                              '(fn-cev-scope-words fn-ag-rev-onto
                                fn-cev-scope-words-loop-is-rev-onto)
                              (union-theories (theory 'minimal-theory)
                                              (executable-counterpart-theory :here))))))

(defun fn-cev-scope (scope)
  (declare (xargs :guard t))
  (if (consp scope) (fn-cev-scope-words scope) (fn-nls-text "-")))

(defun fn-cev-word (x)
  (declare (xargs :guard t))
  (fn-nctrl-reason-word x))

; The fields of withdrawal record W, after its first word.
(defun fn-cev-withdrawal-fields (w)
  (declare (xargs :guard t))
  (append (fn-nls-text " target=") (fn-cev-string (fn-ctl-w-target w))
          (fn-nls-text " cause=") (fn-cev-string (fn-ctl-w-cause w))
          (fn-nls-text " principal=")
          ;; A key record (SEC-006) names no principal: its basis is the
          ;; Cancel-Key its cause carries, which the cause's octets hold.
          (cond ((fn-ctl-key-principalp (fn-ctl-w-principal w))
                 (fn-nls-text "cancel-key"))
                ;; PKT-575: the node operator's withdrawal.
                ((eq (fn-ctl-w-principal w) :node) (fn-nls-text "node"))
                (t (fn-cev-string (fn-ctl-w-principal w))))
          (fn-nls-text " scope=") (fn-cev-scope (fn-ctl-w-scope w))
          (fn-nls-field "generation" (fn-ctl-w-generation w))))

; One line of `control log'.
(defun fn-cev-log-line (w)
  (declare (xargs :guard t))
  (append (fn-nls-text "withdrawal") (fn-cev-withdrawal-fields w) *fn-nls-lf*))

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-cev-log-lines-loop (ws acc)
  (declare (xargs :guard (true-listp acc) :verify-guards nil))
  (if (consp ws)
      (fn-cev-log-lines-loop (cdr ws) (cons (fn-cev-log-line (car ws)) acc))
    (revappend acc nil)))

(defun fn-cev-log-lines (ws)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp ws)
           (cons (fn-cev-log-line (car ws)) (fn-cev-log-lines (cdr ws)))
         nil)
       :exec (fn-cev-log-lines-loop ws nil)))

(local
 (defthm fn-cev-log-lines-loop-is-revappend
   (equal (fn-cev-log-lines-loop ws acc)
          (revappend acc (fn-cev-log-lines ws)))
   :hints (("Goal" :induct (fn-cev-log-lines-loop ws acc)
                   :in-theory (union-theories '(fn-cev-log-lines-loop fn-cev-log-lines revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-cev-log-lines-loop)

(verify-guards fn-cev-log-lines
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-cev-log-lines)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-cev-log-lines-loop-is-revappend (acc nil))))))


; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-cev-join-loop (lines acc)
  (declare (xargs :guard (true-listp acc) :verify-guards nil))
  (if (consp lines)
      (fn-cev-join-loop (cdr lines) (fn-ag-rev-onto (true-list-fix (car lines)) acc))
    (revappend acc nil)))

(defun fn-cev-join (lines)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp lines)
           (append (true-list-fix (car lines)) (fn-cev-join (cdr lines)))
         nil)
       :exec (fn-cev-join-loop lines nil)))

(local
 (defthm fn-cev-join-loop-rev-onto-append
   (equal (revappend (fn-ag-rev-onto x acc) y)
          (revappend acc (append x y)))))

(local
 (defthm fn-cev-join-loop-is-revappend
   (equal (fn-cev-join-loop lines acc)
          (revappend acc (fn-cev-join lines)))
   :hints (("Goal" :induct (fn-cev-join-loop lines acc)
                   :in-theory (union-theories '(fn-cev-join-loop fn-cev-join revappend car-cons cdr-cons fn-cev-join-loop-rev-onto-append)
                                              (theory 'minimal-theory))))))

(verify-guards fn-cev-join-loop)

(verify-guards fn-cev-join
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-cev-join)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-cev-join-loop-is-revappend (acc nil))))))


; `control log': the count, then one line per record in the owner's order.
(defun fn-cev-log-report (ws)
  (declare (xargs :guard t))
  (append (fn-nls-text "withdrawals=") (fn-nls-nat (len ws)) *fn-nls-lf*
          (fn-cev-join (fn-cev-log-lines ws))))

; -----------------------------------------------------------------------------
; The decision context of one Message-ID

(defun fn-cev-find-article (msgid arts)
  (declare (xargs :guard t))
  (if (consp arts)
      (if (and (consp (car arts)) (equal (fn-article-msgid (car arts)) msgid))
          (car arts)
        (fn-cev-find-article msgid (cdr arts)))
    nil))

; The decision the refresh made for stored article A: the plan
; `fn-ctl-article-withdrawals' computes (a withdrawal record, or
; (:decline REASON)), or nil when A names no target.  After the records
; flip the target and keys are the article's row's control fact, so this is
; the refresh's own decision, `fn-ctl-article-plan' (books/control-visible).
(defun fn-cev-plan (a verdicts records configs)
  (declare (xargs :guard t))
  (fn-ctl-article-plan a verdicts records configs))

(defun fn-cev-decision-line (plan)
  (declare (xargs :guard t))
  (cond ((fn-ctl-withdrawalp plan)
         (append (fn-nls-text "decision=") (fn-cev-log-line plan)))
        ((and (consp plan) (equal (car plan) :decline))
         (append (fn-nls-text "decision=declined reason=")
                 (fn-cev-word (fn-ctl-at 1 plan)) *fn-nls-lf*))
        (t (append (fn-nls-text "decision=none") *fn-nls-lf*))))

; The effect of W on the stored target A (nil when A is not stored).
(defun fn-cev-effect-words (w a verdicts)
  (declare (xargs :guard t))
  (if (consp a)
      (let ((effect (fn-ctl-withdrawal-effect
                     w (fn-article-groups a)
                     (fn-ctl-lookup-verdict (fn-article-msgid a) verdicts)
                     (fn-article-payload a))))
        (if (fn-ctl-effect-withdrawsp effect)
            (append (fn-nls-text " effect=") (fn-cev-word effect))
          (append (fn-nls-text " effect=declined reason=")
                  (fn-cev-word (fn-ctl-at 1 effect)))))
    (fn-nls-text " effect=target-absent")))

; Every record of WS whose target is MSGID, with its effect on A.
; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec folds the reversed list (fn-ag-rev-onto) from the left with the
; same step.
(defun fn-cev-targeting-lines-loop (msgid rev a verdicts acc)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp rev)
      (fn-cev-targeting-lines-loop msgid
                                   (cdr rev)
                                   a
                                   verdicts
                                   (if (and (fn-ctl-withdrawalp (car rev))
                                            (equal (fn-ctl-w-target (car rev)) msgid))
                                       (append (fn-nls-text "withdrawn-by")
                                               (fn-cev-withdrawal-fields (car rev))
                                               (fn-cev-effect-words (car rev)
                                                                    a
                                                                    verdicts)
                                               *fn-nls-lf*
                                               acc)
                                     acc))
    acc))

(defun fn-cev-targeting-lines (msgid ws a verdicts)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp ws)
           (if (and (fn-ctl-withdrawalp (car ws))
                    (equal (fn-ctl-w-target (car ws)) msgid))
               (append (fn-nls-text "withdrawn-by")
                       (fn-cev-withdrawal-fields (car ws))
                       (fn-cev-effect-words (car ws) a verdicts)
                       *fn-nls-lf*
                       (fn-cev-targeting-lines msgid (cdr ws) a verdicts))
             (fn-cev-targeting-lines msgid (cdr ws) a verdicts))
         nil)
       :exec (fn-cev-targeting-lines-loop msgid (fn-ag-rev-onto ws nil) a verdicts nil)))

(local
 (defthm fn-cev-targeting-lines-loop-of-rev-onto
   (equal (fn-cev-targeting-lines-loop msgid (fn-ag-rev-onto ws zs) a verdicts nil)
          (fn-cev-targeting-lines-loop msgid zs a verdicts (fn-cev-targeting-lines msgid ws a verdicts)))
   :hints (("Goal" :induct (fn-ag-rev-onto ws zs)
                   :in-theory (union-theories '(fn-cev-targeting-lines-loop fn-cev-targeting-lines fn-ag-rev-onto
                                                car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-cev-targeting-lines-loop)

(verify-guards fn-cev-targeting-lines
  :hints (("Goal" :in-theory (union-theories '(fn-cev-targeting-lines fn-cev-targeting-lines-loop)
                                                  (union-theories (theory 'minimal-theory)
                                                                  (executable-counterpart-theory :here)))
                  :use ((:instance fn-cev-targeting-lines-loop-of-rev-onto (zs nil))))))


(defun fn-cev-verdict-word (verdict)
  (declare (xargs :guard t))
  (if verdict (fn-cev-word (fn-stx-verdict-token verdict)) (fn-nls-text "unsigned")))

(defun fn-cev-txid-words (txid)
  (declare (xargs :guard t))
  (if (natp txid) (fn-nls-nat txid) (fn-nls-text "-")))

(defun fn-cev-evidence-report (msgid ws raw verdicts records configs)
  (declare (xargs :guard t))
  (let ((a (fn-cev-find-article msgid raw)))
    (append (fn-nls-text "evidence message-id=") (fn-cev-string msgid)
            (if (consp a)
                (append (fn-nls-text " stored=yes txid=")
                        (fn-cev-txid-words
                         (fn-store-event-txid (fn-ctl-row-event msgid records)))
                        (fn-nls-text " verdict=")
                        (fn-cev-verdict-word (fn-ctl-lookup-verdict msgid verdicts))
                        *fn-nls-lf*
                        (fn-cev-decision-line (fn-cev-plan a verdicts records configs)))
              (append (fn-nls-text " stored=no") *fn-nls-lf*))
            (fn-cev-targeting-lines msgid ws a verdicts))))

;; -----------------------------------------------------------------------------
;; PKT-657 (PRF-228): `moderation list GROUP'.  A held post is the envelope
;; books/moderation.lisp `fn-mod-forward' injected into GROUP's queue, whose
;; Message-ID is the post's with "fn-moderate." after the `<'.  Its state is
;; read, never kept: `rejected' when a withdrawal record of WS withdraws the
;; envelope, `approved' when the archive holds the post's own Message-ID (the
;; moderator's approved injection, RFC 5537 section 3.9 step 4), `held'
;; otherwise.  One walk of the archive N for the queue's envelopes, and per
;; envelope one walk of N and one pass over WS; the configuration is the
;; journal applied once (as `control evidence' applies it).

(defconst *fn-cev-envelope-prefix* "<fn-moderate.")

; What follows prefix P in O, or :no when O does not begin with P.
(defun fn-cev-after-prefix (p o)
  (declare (xargs :guard t))
  (if (consp p)
      (if (and (consp o) (equal (car p) (car o)))
          (fn-cev-after-prefix (cdr p) (cdr o))
        :no)
    o))

; The post's Message-ID an envelope Message-ID ID names, or nil.
(defun fn-cev-envelope-original (id)
  (declare (xargs :guard t))
  (let ((rest (fn-cev-after-prefix
               (fn-record-string-octets *fn-cev-envelope-prefix*)
               (fn-record-string-octets id))))
    (if (and (consp rest) (fn-cbor-octet-listp rest))
        (fn-record-octets-string (cons 60 rest))
      nil)))

; RECEIVED is the envelope's octets: a key record's effect (the :poster arm,
; RFC 8315 Cancel-Lock, SEC-006) reads the target's locks from them.
(fn-payload-kind fn-cev-withdrawn-by-some :handle "passes the payload to fn-ctl-withdrawal-effect, which ignores it")
(defun fn-cev-withdrawn-by-some (msgid ws groups verdict received)
  (declare (xargs :guard t))
  (if (consp ws)
      (or (and (fn-ctl-withdrawalp (car ws))
               (equal (fn-ctl-w-target (car ws)) msgid)
               (fn-ctl-effect-withdrawsp
                (fn-ctl-withdrawal-effect (car ws) groups verdict received)))
          (fn-cev-withdrawn-by-some msgid (cdr ws) groups verdict received))
    nil))

(defun fn-cev-envelope-state (a ws raw verdicts)
  (declare (xargs :guard t))
  (cond ((fn-cev-withdrawn-by-some
          (fn-article-msgid a) ws (fn-article-groups a)
          (fn-ctl-lookup-verdict (fn-article-msgid a) verdicts)
          (fn-article-payload a))
         "rejected")
        ((consp (fn-cev-find-article
                 (fn-cev-envelope-original (fn-article-msgid a)) raw))
         "approved")
        (t "held")))

; The queue Q's envelopes among ARTS, in archive order.
; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-cev-queue-envelopes-loop (q arts acc)
  (declare (xargs :guard (true-listp acc) :verify-guards nil))
  (if (consp arts)
      (if (and (consp (car arts))
               (member-equal q (true-list-fix (fn-article-groups (car arts))))
               (fn-cev-envelope-original (fn-article-msgid (car arts))))
          (fn-cev-queue-envelopes-loop q (cdr arts) (cons (car arts) acc))
        (fn-cev-queue-envelopes-loop q (cdr arts) acc))
    (revappend acc nil)))

(defun fn-cev-queue-envelopes (q arts)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp arts)
           (if (and (consp (car arts))
                    (member-equal q (true-list-fix (fn-article-groups (car arts))))
                    (fn-cev-envelope-original (fn-article-msgid (car arts))))
               (cons (car arts) (fn-cev-queue-envelopes q (cdr arts)))
             (fn-cev-queue-envelopes q (cdr arts)))
         nil)
       :exec (fn-cev-queue-envelopes-loop q arts nil)))

(local
 (defthm fn-cev-queue-envelopes-loop-is-revappend
   (equal (fn-cev-queue-envelopes-loop q arts acc)
          (revappend acc (fn-cev-queue-envelopes q arts)))
   :hints (("Goal" :induct (fn-cev-queue-envelopes-loop q arts acc)
                   :in-theory (union-theories '(fn-cev-queue-envelopes-loop fn-cev-queue-envelopes revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-cev-queue-envelopes-loop)

(verify-guards fn-cev-queue-envelopes
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-cev-queue-envelopes)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-cev-queue-envelopes-loop-is-revappend (acc nil))))))


; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec folds the reversed list (fn-ag-rev-onto) from the left with the
; same step.
(defun fn-cev-held-count-loop (rev ws raw verdicts acc)
  (declare (xargs :guard (rationalp acc) :verify-guards nil))
  (if (consp rev)
      (fn-cev-held-count-loop (cdr rev)
                              ws
                              raw
                              verdicts
                              (+ (if (equal (fn-cev-envelope-state (car rev)
                                                                   ws
                                                                   raw
                                                                   verdicts)
                                            "held")
                                     1
                                   0)
                                 acc))
    acc))

(defun fn-cev-held-count (envs ws raw verdicts)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp envs)
           (+ (if (equal (fn-cev-envelope-state (car envs) ws raw verdicts) "held") 1 0)
              (fn-cev-held-count (cdr envs) ws raw verdicts))
         0)
       :exec (fn-cev-held-count-loop (fn-ag-rev-onto envs nil) ws raw verdicts 0)))

(local
 (defthm fn-cev-held-count-loop-of-rev-onto
   (equal (fn-cev-held-count-loop (fn-ag-rev-onto envs zs) ws raw verdicts 0)
          (fn-cev-held-count-loop zs ws raw verdicts (fn-cev-held-count envs ws raw verdicts)))
   :hints (("Goal" :induct (fn-ag-rev-onto envs zs)
                   :in-theory (union-theories '(fn-cev-held-count-loop fn-cev-held-count fn-ag-rev-onto
                                                car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-cev-held-count-loop)

(verify-guards fn-cev-held-count
  :hints (("Goal" :in-theory (union-theories '(fn-cev-held-count fn-cev-held-count-loop)
                                                  (union-theories (theory 'minimal-theory)
                                                                  (executable-counterpart-theory :here)))
                  :use ((:instance fn-cev-held-count-loop-of-rev-onto (zs nil))))))


; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec folds the reversed list (fn-ag-rev-onto) from the left with the
; same step.
(defun fn-cev-envelope-lines-loop (rev ws raw verdicts acc)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp rev)
      (fn-cev-envelope-lines-loop (cdr rev)
                                  ws
                                  raw
                                  verdicts
                                  (append (fn-nls-text (fn-cev-envelope-state (car rev)
                                                                              ws
                                                                              raw
                                                                              verdicts))
                                          (fn-nls-text " envelope=")
                                          (fn-cev-string (fn-article-msgid (car rev)))
                                          (fn-nls-text " message-id=")
                                          (fn-cev-string (fn-cev-envelope-original (fn-article-msgid (car rev))))
                                          *fn-nls-lf*
                                          acc))
    acc))

(defun fn-cev-envelope-lines (envs ws raw verdicts)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp envs)
           (append (fn-nls-text (fn-cev-envelope-state (car envs) ws raw verdicts))
                   (fn-nls-text " envelope=") (fn-cev-string (fn-article-msgid (car envs)))
                   (fn-nls-text " message-id=")
                   (fn-cev-string (fn-cev-envelope-original (fn-article-msgid (car envs))))
                   *fn-nls-lf*
                   (fn-cev-envelope-lines (cdr envs) ws raw verdicts))
         nil)
       :exec (fn-cev-envelope-lines-loop (fn-ag-rev-onto envs nil) ws raw verdicts nil)))

(local
 (defthm fn-cev-envelope-lines-loop-of-rev-onto
   (equal (fn-cev-envelope-lines-loop (fn-ag-rev-onto envs zs) ws raw verdicts nil)
          (fn-cev-envelope-lines-loop zs ws raw verdicts (fn-cev-envelope-lines envs ws raw verdicts)))
   :hints (("Goal" :induct (fn-ag-rev-onto envs zs)
                   :in-theory (union-theories '(fn-cev-envelope-lines-loop fn-cev-envelope-lines fn-ag-rev-onto
                                                car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-cev-envelope-lines-loop)

(verify-guards fn-cev-envelope-lines
  :hints (("Goal" :in-theory (union-theories '(fn-cev-envelope-lines fn-cev-envelope-lines-loop)
                                                  (union-theories (theory 'minimal-theory)
                                                                  (executable-counterpart-theory :here)))
                  :use ((:instance fn-cev-envelope-lines-loop-of-rev-onto (zs nil))))))


(defun fn-cev-moderation-report (group ws raw verdicts configs)
  (declare (xargs :guard t))
  (let* ((cfg (fn-ctl-apply-records (fn-cfg-initial) configs))
         (m (fn-cfg-group-moderation (fn-cfg-value cfg) (fn-cfg-generation cfg)
                                     group)))
    (if (not (consp m))
        (append (fn-nls-text "moderation group=") (fn-cev-string group)
                (fn-nls-text " moderated=no") *fn-nls-lf*)
      (let ((envs (fn-cev-queue-envelopes (car m) raw)))
        (append (fn-nls-text "moderation group=") (fn-cev-string group)
                (fn-nls-text " queue=") (fn-cev-string (car m))
                (fn-nls-text " held=")
                (fn-nls-nat (fn-cev-held-count envs ws raw verdicts))
                *fn-nls-lf*
                (fn-cev-envelope-lines envs ws raw verdicts))))))

; The report of KIND (`fn-cevg-kindp') over the records WS, the archive RAW,
; the verdicts, the Store's records and its configuration journal.
(defun fn-cev-report (kind ws raw verdicts records configs)
  (declare (xargs :guard t))
  (cond ((and (consp kind) (equal (car kind) :moderation-list))
         (fn-cev-moderation-report (cdr kind) ws raw verdicts configs))
        ((consp kind)
         (fn-cev-evidence-report (cdr kind) ws raw verdicts records configs))
        (t (fn-cev-log-report ws))))

; What the running owner answers, over the view it carries.  Host:
; host/native-live-status-host.lisp `fn-native-live-status-host-answer'
; (host/native/control.lisp `fnn-control-live-status-answer').
(defun fn-cev-live-report (kind oc)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((o (fn-ocfg-owner oc))
         (v (fn-own-view o))
         (s (fn-own-store o)))
    (if (fn-oig-kindp kind)
        ; Row S3d: the group's memberships over the archive the served view
        ; carries (books/owner-inspect-group.lisp fn-oig-report; the same
        ; archive LISTGROUP renders from: books/owner.lisp
        ; fn-served-live-archive).
        (fn-oig-report (cdr kind) (fn-own-view-archive v))
      (fn-cev-report kind (fn-own-view-withdrawals v) (fn-own-view-raw v)
                     (fn-own-view-verdicts v)
                     (fn-sf-records (fn-sn-files s)) (fn-sn-config-history s)))))

; What the offline command prints over the Store it replayed: the records
; decided as recovery decides them (`fn-ctl-articles-withdrawals').  Host:
; `fn-native-live-status-host-offline' (host/native/io.lisp
; `fnn-command-live-report').
(defun fn-cev-offline-report (kind s)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((archive (fn-node-acceptance (fn-sn-node s)))
         (raw (fn-state-articles archive))
         (verdicts (fn-sn-verdicts s))
         (records (fn-sf-records (fn-sn-files s)))
         (configs (fn-sn-config-history s)))
    (if (fn-oig-kindp kind)
        ; Row S3d: the same report over the archive the open replayed
        ; (books/owner-inspect-group.lisp fn-oig-report).
        (fn-oig-report (cdr kind) archive)
      (fn-cev-report kind (fn-ctl-articles-withdrawals raw verdicts records configs)
                     raw verdicts records configs))))

; -----------------------------------------------------------------------------
; The request: FNLS frame kind 3, (uint CODE, uint OFFSET, bytes ARGUMENT).

(defconst *fn-cev-request-kind* 3)

; The kinds the frame carries: the evidence kinds and row S3d's
; (:inspect-group . GROUP) (books/owner-inspect-group.lisp fn-oig-kindp).
(defun fn-cev-report-kindp (kind)
  (declare (xargs :guard t))
  (or (fn-cevg-kindp kind) (fn-oig-kindp kind)))

(defun fn-cev-kind-code (kind)
  (declare (xargs :guard t))
  (cond ((equal kind :control-log) 8)
        ((and (consp kind) (equal (car kind) :control-evidence)) 9)
        ; PKT-657: `moderation list GROUP' (FNLS frame kind 3, code 10).
        ((and (consp kind) (equal (car kind) :moderation-list)) 10)
        ; Row S3d: `store inspect --group GROUP' (code 11).
        ((and (consp kind) (equal (car kind) :inspect-group)) 11)
        (t 0)))

(defun fn-cev-kind-argument (kind)
  (declare (xargs :guard t))
  (if (consp kind) (fn-record-string-octets (cdr kind)) nil))

(defun fn-cev-request-encode (kind offset)
  (declare (xargs :guard t))
  (if (not (and (fn-cev-report-kindp kind) (fn-record-uint32p offset)))
      :bad
    (fn-nls-seal *fn-cev-request-kind*
                 (append (fn-cbor-encode (cons :uint (fn-cev-kind-code kind)))
                         (fn-cbor-encode (cons :uint offset))
                         (fn-record-item-encode
                          (cons :bytes (fn-cev-kind-argument kind)))))))

(defun fn-cev-code-kind (code argument)
  (declare (xargs :guard t))
  (cond ((and (equal code 8) (null argument)) :control-log)
        ((and (equal code 9) (fn-cbor-octet-listp argument))
         (let ((kind (cons :control-evidence (fn-record-octets-string argument))))
           (if (fn-cevg-kindp kind) kind nil)))
        ((and (equal code 10) (fn-cbor-octet-listp argument))
         (let ((kind (cons :moderation-list (fn-record-octets-string argument))))
           (if (fn-cevg-kindp kind) kind nil)))
        ((and (equal code 11) (fn-cbor-octet-listp argument))
         (let ((kind (cons :inspect-group (fn-record-octets-string argument))))
           (if (fn-oig-kindp kind) kind nil)))
        (t nil)))

; The payload grammar over an opened frame; the decode below is the open
; (fn-nls-open) followed by it, and books/native-live-buffer.lisp opens the
; frame in place and calls the grammar.
(defun fn-cev-request-payload-decode (opened)
  "(:live-status KIND OFFSET), or (:refused REASON)."
  (declare (xargs :guard t :verify-guards nil))
    (if (not (fn-frame-result-okp opened))
        (list :refused :frame)
      (let* ((r1 (fn-record-read-uint (fn-frame-result-payload opened)))
             (r2 (fn-record-read-uint (fn-record-parse-rest r1)))
             (r3 (fn-record-read-bytes (fn-record-parse-rest r2))))
        (if (not (and (fn-record-parse-okp r1) (fn-record-parse-okp r2)
                      (fn-record-parse-okp r3)
                      (natp (fn-record-parse-value r2))
                      (null (fn-record-parse-rest r3))))
            (list :refused :fields)
          (let ((kind (fn-cev-code-kind (fn-record-parse-value r1)
                                        (fn-record-parse-value r3))))
            (if kind
                (list :live-status kind (fn-record-parse-value r2))
              (list :refused :kind)))))))

(defun fn-cev-request-decode (octets)
  "(:live-status KIND OFFSET), or (:refused REASON)."
  (declare (xargs :guard t :verify-guards nil))
  (fn-cev-request-payload-decode (fn-nls-open octets *fn-cev-request-kind*)))

; Either request the owner pages: a status report (frame kind 1) or a
; control report (frame kind 3).
(defun fn-cev-any-request-decode (octets)
  (declare (xargs :guard t :verify-guards nil))
  (let ((plain (fn-nls-request-decode octets)))
    (if (equal (car plain) :live-status)
        plain
      (fn-cev-request-decode octets))))

(defun fn-cev-any-request-encode (kind offset)
  (declare (xargs :guard t))
  (if (fn-cev-report-kindp kind)
      (fn-cev-request-encode kind offset)
    (fn-nls-request-encode kind offset)))

; -----------------------------------------------------------------------------
; The keystones

(defthm fn-cev-find-article-is-a-member
  (implies (fn-cev-find-article msgid arts)
           (member-equal (fn-cev-find-article msgid arts) arts)))

(defthm fn-cev-plan-is-the-article-withdrawal-by-definition
  (equal (fn-ctl-article-withdrawals a verdicts records configs)
         (if (fn-ctl-withdrawalp (fn-cev-plan a verdicts records configs))
             (list (fn-cev-plan a verdicts records configs))
           nil))
  :hints (("Goal" :in-theory (e/d (fn-ctl-article-withdrawals fn-cev-plan)
                                  (fn-ctl-withdrawal-plan fn-ctl-withdrawalp
                                   fn-ctl-article-plan)))))

(defthm fn-cev-journal-records-are-withdrawals
  (implies (member-equal w (fn-ctl-articles-withdrawals arts verdicts records configs))
           (fn-ctl-withdrawalp w))
  :hints (("Goal" :induct (fn-ctl-articles-withdrawals arts verdicts records configs)
           :in-theory (e/d (fn-ctl-articles-withdrawals)
                           (fn-ctl-withdrawalp fn-cev-plan fn-ctl-article-withdrawals
                            fn-ctl-articles-withdrawals-is-the-journal)))))

(defthm fn-cev-journal-holds-each-articles-record
  (implies (and (member-equal a arts)
                (fn-ctl-withdrawalp (fn-cev-plan a verdicts records configs)))
           (member-equal (fn-cev-plan a verdicts records configs)
                         (fn-ctl-articles-withdrawals arts verdicts records configs)))
  :hints (("Goal" :induct (len arts)
           :in-theory (e/d (fn-ctl-articles-withdrawals)
                           (fn-ctl-withdrawalp fn-cev-plan fn-ctl-article-withdrawals
                            fn-ctl-articles-withdrawals-is-the-journal)))))

(defthm fn-cev-plan-of-no-article
  (equal (fn-cev-plan nil verdicts records configs) nil)
  :hints (("Goal" :in-theory (enable fn-cev-plan fn-ctl-article-plan))))

(defthm fn-cev-journal-holds-no-nil
  (not (member-equal nil (fn-ctl-articles-withdrawals arts verdicts records configs)))
  :hints (("Goal" :in-theory (disable fn-ctl-articles-withdrawals fn-ctl-withdrawalp
                                      fn-ctl-articles-withdrawals-is-the-journal)
           :use ((:instance fn-cev-journal-records-are-withdrawals (w nil))))))

; KEYSTONE.  The subject is `fn-cev-evidence-report''s decision
; (`fn-cev-plan' of the stored article `fn-cev-find-article' names), which
; host/native-live-status-host.lisp `fn-native-live-status-host-answer'
; renders through `fn-cev-live-report'.  WS is the owner's carried records;
; the one hypothesis is the owner's maintained relation (established by
; `fn-own-start''s refresh, preserved by every `fn-own-refresh':
; `fn-ctl-refresh-withdrawals-is-the-journal' with
; `fn-ctl-articles-withdrawals-is-the-journal'; the offline report
; establishes it by construction).
(defthm fn-cev-evidence-decision-is-in-the-log
  (implies (equal ws (fn-ctl-articles-withdrawals raw verdicts records configs))
           (iff (member-equal (fn-cev-plan (fn-cev-find-article msgid raw)
                                           verdicts records configs)
                              ws)
                (fn-ctl-withdrawalp (fn-cev-plan (fn-cev-find-article msgid raw)
                                                 verdicts records configs))))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawalp fn-cev-plan
                                      fn-cev-find-article
                                      fn-ctl-articles-withdrawals
                                      fn-ctl-articles-withdrawals-is-the-journal)
           :cases ((fn-cev-find-article msgid raw)))
          ("Subgoal 1" :use ((:instance fn-cev-journal-holds-each-articles-record
                            (a (fn-cev-find-article msgid raw)) (arts raw))
                 (:instance fn-cev-journal-records-are-withdrawals
                            (w (fn-cev-plan (fn-cev-find-article msgid raw)
                                            verdicts records configs))
                            (arts raw))))))

(defthm fn-cev-log-lines-member
  (implies (member-equal w ws)
           (member-equal (fn-cev-log-line w) (fn-cev-log-lines ws)))
  :hints (("Goal" :in-theory (disable fn-cev-log-line))))

; The words of a withdrawing decision are "decision=" and one of the lines
; `control log' prints over the same records.
(defthm fn-cev-decision-line-is-a-log-line
  (implies (and (equal ws (fn-ctl-articles-withdrawals raw verdicts records configs))
                (fn-ctl-withdrawalp (fn-cev-plan (fn-cev-find-article msgid raw)
                                                 verdicts records configs)))
           (let ((plan (fn-cev-plan (fn-cev-find-article msgid raw)
                                    verdicts records configs)))
             (and (equal (fn-cev-decision-line plan)
                         (append (fn-nls-text "decision=") (fn-cev-log-line plan)))
                  (member-equal (fn-cev-log-line plan) (fn-cev-log-lines ws)))))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawalp fn-cev-plan
                                      fn-cev-find-article fn-cev-log-line
                                      fn-ctl-articles-withdrawals fn-cev-log-lines)
           :use ((:instance fn-cev-evidence-decision-is-in-the-log)
                 (:instance fn-cev-log-lines-member
                            (w (fn-cev-plan (fn-cev-find-article msgid raw)
                                            verdicts records configs)))))))

; `control log' prints one line per record.
(defthm fn-cev-log-lines-len
  (equal (len (fn-cev-log-lines ws)) (len ws))
  :hints (("Goal" :in-theory '(fn-cev-log-lines len car-cons cdr-cons))))

(in-theory (disable fn-cev-plan-is-the-article-withdrawal-by-definition
                    fn-cev-plan fn-cev-find-article fn-cev-report
                    fn-cev-evidence-report fn-cev-log-report))

; -----------------------------------------------------------------------------
; PKT-518 (PRF-187): the FNLS request frame kind 3 round trip.  The frame had
; executed witnesses only (tests/acl2/control-evidence-tests.lisp); these are
; the theorems.
(encapsulate ()
(local (defthm fn-cev-printable-octets
  (implies (fn-cevg-printable-charsp cs)
           (and (fn-cbor-octet-listp (fn-record-string-octets-aux cs))
                (equal (len (fn-record-string-octets-aux cs)) (len cs))
                (equal (fn-record-octets-chars (fn-record-string-octets-aux cs)) cs)))
  :hints (("Goal" :in-theory (enable fn-cbor-octetp)))))
(defthm fn-cev-msgid-octets
  (implies (fn-cevg-msgidp x)
           (and (fn-cbor-octet-listp (fn-record-string-octets x))
                (<= (len (fn-record-string-octets x)) *fn-cevg-max-msgid-octets*)
                (equal (fn-record-octets-string (fn-record-string-octets x)) x)))
  :hints (("Goal" :in-theory (enable fn-cevg-msgidp fn-record-string-octets fn-record-octets-string))))
; PKT-657: the group argument of `moderation list' likewise.
(defthm fn-cev-group-octets
  (implies (fn-cevg-groupp x)
           (and (fn-cbor-octet-listp (fn-record-string-octets x))
                (<= (len (fn-record-string-octets x)) *fn-cevg-max-msgid-octets*)
                (equal (fn-record-octets-string (fn-record-string-octets x)) x)))
  :hints (("Goal" :in-theory (enable fn-cevg-groupp fn-record-string-octets fn-record-octets-string)))))

(encapsulate ()
(local (defthm fn-cev-octets-of-append
  (implies (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp b))
           (fn-cbor-octet-listp (append a b)))))
(local (defthm fn-cev-len-append
  (equal (len (append a b)) (+ (len a) (len b)))))
(local (defthm fn-cev-argument-facts
  (implies (fn-cev-report-kindp kind)
           (and (fn-cbor-octet-listp (fn-cev-kind-argument kind))
                (<= (len (fn-cev-kind-argument kind)) *fn-cevg-max-msgid-octets*)))
  :hints (("Goal" :use ((:instance fn-cev-msgid-octets (x (cdr kind)))
                        (:instance fn-cev-group-octets (x (cdr kind))))
           :in-theory (e/d (fn-cev-report-kindp fn-oig-kindp fn-cevg-kindp fn-cev-kind-argument)
                           (fn-cev-msgid-octets fn-cev-group-octets fn-cevg-msgidp
                            fn-cevg-groupp fn-record-string-octets
                            fn-record-octets-string))))))
(defthm fn-cev-request-payload-fits
  (implies (fn-cev-report-kindp kind)
           (<= (len (fn-record-item-encode (cons :bytes (fn-cev-kind-argument kind))))
               (+ 5 *fn-cevg-max-msgid-octets*)))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-nls-bytes-item-length (xs (fn-cev-kind-argument kind)))
                        fn-cev-argument-facts)
           :in-theory (disable fn-nls-bytes-item-length fn-record-item-encode fn-cev-kind-argument
                               fn-cev-argument-facts fn-cevg-kindp fn-cev-report-kindp))))
(defthm fn-cev-open-of-request-encode
  (implies (and (fn-cev-report-kindp kind) (fn-record-uint32p offset))
           (equal (fn-nls-open (fn-cev-request-encode kind offset) 3)
                  (fn-frame-ok *fn-nls-magic* *fn-nls-version* 3
                               (append (fn-cbor-encode (cons :uint (fn-cev-kind-code kind)))
                                       (fn-cbor-encode (cons :uint offset))
                                       (fn-record-item-encode
                                        (cons :bytes (fn-cev-kind-argument kind)))))))
  :hints (("Goal" :use ((:instance fn-nls-open-of-seal
                                   (kind 3)
                                   (payload (append (fn-cbor-encode (cons :uint (fn-cev-kind-code kind)))
                                                    (fn-cbor-encode (cons :uint offset))
                                                    (fn-record-item-encode
                                                     (cons :bytes (fn-cev-kind-argument kind)))))))
           :in-theory (e/d (fn-cev-request-encode fn-record-cbor-encode-octets
                            fn-record-item-encode-octets fn-record-cbor-uint-encoding-bound)
                           (fn-nls-open-of-seal fn-nls-open fn-nls-seal fn-cev-kind-code
                            fn-cev-kind-argument fn-record-item-encode
                            fn-cbor-encode (:e fn-cbor-encode)))))))

(encapsulate ()
(local (defthm fn-cev-octets-of-append
  (implies (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp b))
           (fn-cbor-octet-listp (append a b)))))
(local (defthm fn-cev-octets-true-listp
  (implies (fn-cbor-octet-listp r) (true-listp r))))
(local (defthm fn-cev-read-bytes-alone
  (implies (and (fn-cbor-octet-listp xs) (<= (len xs) *fn-record-max-octets*))
           (equal (fn-record-read-bytes (fn-record-item-encode (cons :bytes xs)))
                  (fn-record-parse-ok xs nil)))
  :hints (("Goal" :use ((:instance fn-record-read-bytes-of-item-encoding (rest nil))
                        (:instance fn-record-item-encode-true-list (value (cons :bytes xs))))
           :in-theory (disable fn-record-read-bytes-of-item-encoding fn-record-item-encode-true-list
                               fn-record-read-bytes fn-record-item-encode)))))
(local (defthm fn-cev-code-kind-of-argument
  (implies (fn-cev-report-kindp kind)
           (equal (fn-cev-code-kind (fn-cev-kind-code kind) (fn-cev-kind-argument kind))
                  kind))
  :hints (("Goal" :use ((:instance fn-cev-msgid-octets (x (cdr kind)))
                        (:instance fn-cev-group-octets (x (cdr kind))))
           :in-theory (e/d (fn-cev-report-kindp fn-oig-kindp
                            fn-cevg-kindp fn-cev-kind-argument fn-cev-kind-code fn-cev-code-kind)
                           (fn-cev-msgid-octets fn-cevg-msgidp fn-record-string-octets
                            fn-record-octets-string))))))
(local (defthm fn-cev-argument-octets
  (implies (fn-cev-report-kindp kind)
           (and (fn-cbor-octet-listp (fn-cev-kind-argument kind))
                (<= (len (fn-cev-kind-argument kind)) *fn-record-max-octets*)))
  :hints (("Goal" :use ((:instance fn-cev-msgid-octets (x (cdr kind)))
                        (:instance fn-cev-group-octets (x (cdr kind))))
           :in-theory (e/d (fn-cev-report-kindp fn-oig-kindp fn-cevg-kindp fn-cev-kind-argument)
                           (fn-cev-msgid-octets fn-cev-group-octets fn-cevg-msgidp
                            fn-cevg-groupp fn-record-string-octets
                            fn-record-octets-string))))))
(local (defthm fn-cev-kind-code-uint
  (fn-record-uint32p (fn-cev-kind-code kind))
  :hints (("Goal" :in-theory (enable fn-cev-kind-code)))))
; PKT-518: the owner reads back the report kind and offset the client framed
; in FNLS request frame kind 3 (`control log', `control evidence MSGID').
(defthm fn-cev-request-decode-of-encode
  (implies (and (fn-cev-report-kindp kind) (fn-record-uint32p offset))
           (equal (fn-cev-request-decode (fn-cev-request-encode kind offset))
                  (list :live-status kind offset)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cev-request-decode
                            fn-record-read-uint-of-encoding fn-record-read-bytes-of-item-encoding
                            fn-record-cbor-encode-octets fn-record-item-encode-octets
                            fn-frame-result-okp fn-frame-ok fn-frame-result-payload)
                           (fn-cev-request-encode fn-nls-open fn-nls-seal fn-record-read-uint
                            fn-record-read-bytes fn-cev-code-kind fn-cev-kind-code
                            fn-cev-kind-argument fn-record-item-encode fn-cevg-kindp
                            fn-cev-report-kindp
                            fn-cbor-encode (:e fn-cbor-encode)))))))

(encapsulate ()
(local (defthm fn-cev-open-one-kind
  (implies (and (fn-frame-result-okp (fn-nls-open x j))
                (not (equal j k)))
           (not (fn-frame-result-okp (fn-nls-open x k))))
  :hints (("Goal" :in-theory (enable fn-nls-open)))))
(local (defthm fn-cev-plain-decode-refuses-kind-3
  (implies (and (fn-cev-report-kindp kind) (fn-record-uint32p offset))
           (equal (fn-nls-request-decode (fn-cev-request-encode kind offset))
                  (list :refused :frame)))
  :hints (("Goal" :use ((:instance fn-cev-open-one-kind
                                   (x (fn-cev-request-encode kind offset)) (j 3) (k 1)))
           :in-theory (e/d (fn-nls-request-decode fn-frame-result-okp fn-frame-ok)
                           (fn-cev-open-one-kind fn-cev-request-encode fn-nls-open fn-cevg-kindp
                            fn-cev-report-kindp))))))
; KEYSTONE (PKT-518).  The subject pair the host calls: the client frames
; with `fn-cev-any-request-encode' (host/native-live-status-host.lisp
; `fn-native-live-status-host-request-encode', host/native/control.lisp
; `fnn-control-live-status-page') and the owner reads with
; `fn-cev-any-request-decode' (`fn-native-live-status-host-answer', under
; the owner mutex in `fnn-control-live-status-answer').  For every status
; kind and every control report kind, and every uint32 offset, the owner
; reads back exactly the kind and offset the client framed: frame kind 1 for
; the status kinds, frame kind 3 for `control log' and `control evidence
; MSGID', whose Message-ID survives the octet round trip.
(defthm fn-cev-any-request-decode-of-encode
  (implies (and (or (member-equal kind *fn-nls-kinds*) (fn-cev-report-kindp kind))
                (fn-record-uint32p offset))
           (equal (fn-cev-any-request-decode (fn-cev-any-request-encode kind offset))
                  (list :live-status kind offset)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cev-any-request-decode fn-cev-any-request-encode
                            fn-cev-request-decode-of-encode fn-nls-request-decode-of-encode)
                           (fn-cev-request-encode fn-cev-request-decode fn-nls-request-encode
                            fn-nls-request-decode fn-cevg-kindp fn-cev-report-kindp))))))
