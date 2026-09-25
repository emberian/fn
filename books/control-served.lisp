; fn: what a reader is told about a withdrawal (packet C3, brief control-c3d
; step 1; wired by control-c3e).  The served answers: the pinned dispatcher
; `fn-nntp-archive-command-pinned' (books/nntp.lisp) reads the control pin
; below from its index argument, and books/nntp-control.lisp states its three
; arms over this kernel.
;
; A pinned view serves `fn-ctl-visible-articles' of its raw article list
; (books/control-visible.lisp).  What it withdrew is the rest of that list,
; `fn-ctl-withdrawn-articles'.  A reader told "no such article" for a
; withdrawn number or Message-ID is told the truth (RFC 3977 section
; 6.2.1.2 lets a removed number become invalid), but the design
; (planning/design-2026-09-25-control-messages.md section 2.5) says why:
; `423 withdrawn' by number, `430 withdrawn' by Message-ID, and the
; machine-readable `HDR :fn-control' item on the withdrawing article.  This
; book gives the three answers over the withdrawn list W the view carries:
;
;   `fn-ctl-refresh-withdrawn'  W at a refresh, from the old W: unchanged
;                               when the new article is ordinary and visible
;                               (the common case, O(1)); otherwise one merge
;                               walk of the raw list against the visible
;                               list (O(N), the same class as the executed
;                               cancel's pass in `fn-ctl-visible-add').
;   `fn-ctl-number-withdrawn'   the withdrawn article holding (GROUP . N).
;   `fn-ctl-msgid-withdrawn'    the withdrawn article with MSGID.
;   `fn-ctl-control-status'     the :fn-control status of a withdrawing
;                               article: executed (author or authority),
;                               owed (target not held), declined, or none.
;
; Prefix `fn-ctl-' (docs/prefixes.md).
(in-package "ACL2")
(include-book "control-authority")
(include-book "nntp-projection")
(include-book "msgid-index")

; -----------------------------------------------------------------------------
; The withdrawn list.

(defun fn-ctl-withdrawn-filter (xs ws arts verdicts)
  (declare (xargs :guard t))
  (if (consp xs)
      (if (fn-ctl-withdrawn-by-p (car xs) ws arts verdicts)
          (cons (car xs) (fn-ctl-withdrawn-filter (cdr xs) ws arts verdicts))
        (fn-ctl-withdrawn-filter (cdr xs) ws arts verdicts))
    nil))

(defun fn-ctl-withdrawn-articles (arts ws verdicts)
  (declare (xargs :guard t))
  (fn-ctl-withdrawn-filter arts ws arts verdicts))

(defthm fn-ctl-withdrawn-filter-member
  (iff (member-equal a (fn-ctl-withdrawn-filter xs ws arts verdicts))
       (and (member-equal a xs)
            (fn-ctl-withdrawn-by-p a ws arts verdicts)))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawn-by-p))))

; KEYSTONE.  Within a view's raw list, an article is in the withdrawn list
; exactly when the view does not serve it.
(defthm fn-ctl-withdrawn-is-the-complement
  (implies (member-equal x arts)
           (iff (member-equal x (fn-ctl-withdrawn-articles arts ws verdicts))
                (not (member-equal x (fn-ctl-visible-articles arts ws verdicts)))))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawn-by-p))))

(defthm fn-ctl-visible-filter-is-subset-of-arts
  (implies (member-equal a (fn-ctl-visible-articles arts ws verdicts))
           (member-equal a arts))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawn-by-p))))

(defthm fn-ctl-withdrawn-articles-is-subset-of-arts
  (implies (member-equal a (fn-ctl-withdrawn-articles arts ws verdicts))
           (member-equal a arts))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawn-by-p))))

; The merge: RAW with the subsequence VISIBLE removed, walking both once.
; Once VISIBLE is exhausted the rest of RAW is withdrawn; it is copied as a
; true list (at most the withdrawn list's length) so the result is exactly
; the withdrawn list for any RAW.
(defun fn-ctl-subseq-diff (raw visible)
  (declare (xargs :guard t))
  (cond ((not (consp raw)) nil)
        ((not (consp visible)) (true-list-fix raw))
        ((equal (car raw) (car visible))
         (fn-ctl-subseq-diff (cdr raw) (cdr visible)))
        (t (cons (car raw) (fn-ctl-subseq-diff (cdr raw) visible)))))

(defun fn-ctl-refresh-withdrawn (raw old-raw visible old-visible old-withdrawn)
  (declare (xargs :guard t))
  (cond ((and (equal raw old-raw) (equal visible old-visible)) old-withdrawn)
        ((and (consp raw) (equal (cdr raw) old-raw)
              (consp visible) (equal (cdr visible) old-visible)
              (equal (car visible) (car raw)))
         old-withdrawn)
        (t (fn-ctl-subseq-diff raw visible))))

(defthm fn-ctl-refresh-withdrawn-is-the-diff
  (implies (equal old-withdrawn (fn-ctl-subseq-diff old-raw old-visible))
           (equal (fn-ctl-refresh-withdrawn raw old-raw visible old-visible
                                            old-withdrawn)
                  (fn-ctl-subseq-diff raw visible))))

(defthm fn-ctl-visible-filter-nil-means-all-withdrawn
  (implies (not (consp (fn-ctl-visible-filter xs ws arts verdicts)))
           (equal (fn-ctl-withdrawn-filter xs ws arts verdicts) (true-list-fix xs)))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawn-by-p))))

(defthm fn-ctl-visible-filter-car-is-a-member
  (implies (consp (fn-ctl-visible-filter xs ws arts verdicts))
           (member-equal (car (fn-ctl-visible-filter xs ws arts verdicts)) xs))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawn-by-p))))

(defthm fn-ctl-visible-filter-car-is-not-withdrawn
  (implies (consp (fn-ctl-visible-filter xs ws arts verdicts))
           (not (fn-ctl-withdrawn-by-p (car (fn-ctl-visible-filter xs ws arts verdicts))
                                       ws arts verdicts)))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawn-by-p))))

; Identical articles have the same status, so the greedy merge never pairs
; a dropped article with a kept one: no distinctness is needed.
(defthm fn-ctl-subseq-diff-of-filter
  (equal (fn-ctl-subseq-diff xs (fn-ctl-visible-filter xs ws arts verdicts))
         (fn-ctl-withdrawn-filter xs ws arts verdicts))
  :hints (("Goal" :induct (fn-ctl-withdrawn-filter xs ws arts verdicts)
           :in-theory (disable fn-ctl-withdrawn-by-p))))

(defthm fn-ctl-subseq-diff-of-visible-articles
  (equal (fn-ctl-subseq-diff raw (fn-ctl-visible-articles raw ws verdicts))
         (fn-ctl-withdrawn-articles raw ws verdicts))
  :hints (("Goal" :in-theory (disable fn-ctl-subseq-diff fn-ctl-visible-filter
                                      fn-ctl-withdrawn-filter))))

; KEYSTONE (the carried withdrawn list).  When the carried W was the merge
; of the old raw and visible lists and the new visible list is the view's,
; the refresh's W is the withdrawn list of the new raw list (any RAW): exactly what
; the view does not serve (`fn-ctl-withdrawn-is-the-complement').
(defthm fn-ctl-refresh-withdrawn-is-withdrawn
  (implies (and (equal old-withdrawn (fn-ctl-subseq-diff old-raw old-visible))
                (equal visible (fn-ctl-visible-articles raw ws verdicts)))
           (equal (fn-ctl-refresh-withdrawn raw old-raw visible old-visible
                                            old-withdrawn)
                  (fn-ctl-withdrawn-articles raw ws verdicts)))
  :hints (("Goal" :in-theory (disable fn-ctl-refresh-withdrawn fn-ctl-subseq-diff
                                      fn-ctl-visible-filter fn-ctl-withdrawn-filter))))

; -----------------------------------------------------------------------------
; The reader's lookups in W.

(defun fn-ctl-number-withdrawn (group number withdrawn)
  (fn-nntp-find-group-number group number withdrawn))

(defun fn-ctl-msgid-withdrawn (msgid withdrawn)
  (declare (xargs :guard t))
  (if (consp withdrawn)
      (if (and (consp (car withdrawn))
               (equal (fn-article-msgid (car withdrawn)) msgid))
          (car withdrawn)
        (fn-ctl-msgid-withdrawn msgid (cdr withdrawn)))
    nil))

(defthm fn-ctl-find-group-number-is-a-member
  (implies (consp (fn-nntp-find-group-number group number xs))
           (member-equal (fn-nntp-find-group-number group number xs) xs))
  :hints (("Goal" :in-theory (enable fn-nntp-find-group-number))))

(defthm fn-ctl-find-group-number-holds-the-number
  (implies (consp (fn-nntp-find-group-number group number xs))
           (equal (fn-nntp-membership-number
                   group (fn-article-memberships
                          (fn-nntp-find-group-number group number xs)))
                  number))
  :hints (("Goal" :in-theory (enable fn-nntp-find-group-number))))

(defthm fn-ctl-membership-number-of-atom
  (implies (not (consp x))
           (equal (fn-nntp-membership-number group (fn-article-memberships x)) 0))
  :hints (("Goal" :in-theory (enable fn-article-memberships fn-nntp-membership-number))))

(defthm fn-ctl-find-group-number-finds-a-member
  (implies (and (member-equal x xs) (consp x) (posp number)
                (equal (fn-nntp-membership-number group (fn-article-memberships x))
                       number))
           (consp (fn-nntp-find-group-number group number xs)))
  :hints (("Goal" :in-theory (enable fn-nntp-find-group-number))))

(defthm fn-ctl-msgid-withdrawn-is-a-member
  (implies (fn-ctl-msgid-withdrawn msgid xs)
           (member-equal (fn-ctl-msgid-withdrawn msgid xs) xs)))

(defthm fn-ctl-msgid-withdrawn-has-the-msgid
  (implies (fn-ctl-msgid-withdrawn msgid xs)
           (equal (fn-article-msgid (fn-ctl-msgid-withdrawn msgid xs)) msgid)))

(defthm fn-ctl-msgid-withdrawn-finds-a-member
  (implies (and (member-equal x xs) (consp x)
                (equal (fn-article-msgid x) msgid))
           (fn-ctl-msgid-withdrawn msgid xs)))

; KEYSTONE (423 withdrawn).  Over the view's withdrawn list, the lookup by
; (GROUP . NUMBER) finds an article exactly when the view's raw list holds
; an article at that number that the view does not serve.
(defthm fn-ctl-number-withdrawn-is-a-withdrawn-holder
  (implies (consp (fn-ctl-number-withdrawn group number
                                           (fn-ctl-withdrawn-articles raw ws verdicts)))
           (let ((y (fn-ctl-number-withdrawn group number
                                             (fn-ctl-withdrawn-articles raw ws verdicts))))
             (and (member-equal y raw)
                  (not (member-equal y (fn-ctl-visible-articles raw ws verdicts)))
                  (equal (fn-nntp-membership-number group (fn-article-memberships y))
                         number))))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawn-articles fn-ctl-visible-articles
                                      fn-ctl-withdrawn-is-the-complement)
           :use ((:instance fn-ctl-withdrawn-is-the-complement
                            (x (fn-nntp-find-group-number
                                group number (fn-ctl-withdrawn-articles raw ws verdicts)))
                            (arts raw))
                 (:instance fn-ctl-withdrawn-articles-is-subset-of-arts
                            (a (fn-nntp-find-group-number
                                group number (fn-ctl-withdrawn-articles raw ws verdicts)))
                            (arts raw))
                 (:instance fn-ctl-find-group-number-is-a-member
                            (xs (fn-ctl-withdrawn-articles raw ws verdicts)))))))

(defthm fn-ctl-withdrawn-holder-is-found-by-number
  (implies (and (member-equal x raw) (consp x) (posp number)
                (not (member-equal x (fn-ctl-visible-articles raw ws verdicts)))
                (equal (fn-nntp-membership-number group (fn-article-memberships x))
                       number))
           (consp (fn-ctl-number-withdrawn group number
                                           (fn-ctl-withdrawn-articles raw ws verdicts))))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawn-articles fn-ctl-visible-articles
                                      fn-ctl-withdrawn-is-the-complement)
           :use ((:instance fn-ctl-withdrawn-is-the-complement (arts raw))))))

; KEYSTONE (430 withdrawn), the same by Message-ID.
(defthm fn-ctl-msgid-withdrawn-is-a-withdrawn-article
  (implies (fn-ctl-msgid-withdrawn msgid (fn-ctl-withdrawn-articles raw ws verdicts))
           (let ((y (fn-ctl-msgid-withdrawn msgid (fn-ctl-withdrawn-articles raw ws verdicts))))
             (and (member-equal y raw)
                  (not (member-equal y (fn-ctl-visible-articles raw ws verdicts)))
                  (equal (fn-article-msgid y) msgid))))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawn-articles fn-ctl-visible-articles
                                      fn-ctl-withdrawn-is-the-complement
                                      fn-ctl-msgid-withdrawn)
           :use ((:instance fn-ctl-withdrawn-is-the-complement
                            (x (fn-ctl-msgid-withdrawn
                                msgid (fn-ctl-withdrawn-articles raw ws verdicts)))
                            (arts raw))
                 (:instance fn-ctl-withdrawn-articles-is-subset-of-arts
                            (a (fn-ctl-msgid-withdrawn
                                msgid (fn-ctl-withdrawn-articles raw ws verdicts)))
                            (arts raw))
                 (:instance fn-ctl-msgid-withdrawn-is-a-member
                            (xs (fn-ctl-withdrawn-articles raw ws verdicts)))))))

(defthm fn-ctl-withdrawn-article-is-found-by-msgid
  (implies (and (member-equal x raw) (consp x)
                (not (member-equal x (fn-ctl-visible-articles raw ws verdicts)))
                (equal (fn-article-msgid x) msgid))
           (fn-ctl-msgid-withdrawn msgid (fn-ctl-withdrawn-articles raw ws verdicts)))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawn-articles fn-ctl-visible-articles
                                      fn-ctl-withdrawn-is-the-complement
                                      fn-ctl-msgid-withdrawn)
           :use ((:instance fn-ctl-withdrawn-is-the-complement (arts raw))))))

; -----------------------------------------------------------------------------
; HDR :fn-control.  The status of article C (a cancel or a superseding
; article) in a view serving VISIBLE and withdrawing WITHDRAWN under the
; records WS and verdicts:
;   (:none)                   C names no target;
;   (:declined REASON)        the decision declined (unverified, no target,
;                             self-target), or the record's effect on the
;                             held target declines (no grant, outside the
;                             namespace, ...);
;   (:owed)                   the record exists and the target is not held;
;   (:executed :author) / (:executed :authority).
; The decline of the plan does not depend on the configuration (only scope
; and generation do), so it is recomputed with none.

(defun fn-ctl-cause-record (ws cause target)
  (declare (xargs :guard t))
  (if (consp ws)
      (if (and (fn-ctl-withdrawalp (car ws))
               (equal (fn-ctl-w-cause (car ws)) cause)
               (equal (fn-ctl-w-target (car ws)) target))
          (car ws)
        (fn-ctl-cause-record (cdr ws) cause target))
    nil))

(defun fn-ctl-find-held (msgid visible withdrawn)
  (declare (xargs :guard t))
  (or (fn-ctl-msgid-withdrawn msgid withdrawn)
      (fn-ctl-msgid-withdrawn msgid visible)))

(defthm fn-ctl-has-msgid-p-of-member
  (implies (and (member-equal x arts) (consp x))
           (fn-ctl-has-msgid-p (fn-article-msgid x) arts)))

(defun fn-ctl-control-status (c visible withdrawn ws verdicts)
  (declare (xargs :guard t))
  (let* ((msgid (and (consp c) (fn-article-msgid c)))
         (target (and (consp c) (fn-ctl-target-octets (fn-article-payload c))))
         (plan (fn-ctl-withdrawal-plan msgid (fn-ctl-lookup-verdict msgid verdicts)
                                       target nil)))
    (cond ((not target) (list :none))
          ((not (fn-ctl-withdrawalp plan)) (list :declined (fn-ctl-at 1 plan)))
          (t (let ((rec (fn-ctl-cause-record ws msgid target)))
               (if (not rec)
                   (list :declined :no-record)
                 (let ((held (fn-ctl-find-held target visible withdrawn)))
                   (if (not held)
                       (list :owed)
                     (let ((effect (fn-ctl-withdrawal-effect
                                    rec (fn-article-groups held)
                                    (fn-ctl-lookup-verdict target verdicts))))
                       (if (fn-ctl-effect-withdrawsp effect)
                           (list :executed effect)
                         (list :declined (fn-ctl-at 1 effect))))))))))))

(defthm fn-ctl-cause-record-member
  (implies (fn-ctl-cause-record ws cause target)
           (member-equal (fn-ctl-cause-record ws cause target) ws)))
(defthm fn-ctl-cause-record-withdrawalp
  (implies (fn-ctl-cause-record ws cause target)
           (fn-ctl-withdrawalp (fn-ctl-cause-record ws cause target)))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawalp))))
(defthm fn-ctl-cause-record-cause
  (implies (fn-ctl-cause-record ws cause target)
           (equal (fn-ctl-w-cause (fn-ctl-cause-record ws cause target)) cause))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawalp fn-ctl-w-cause))))
(defthm fn-ctl-cause-record-target
  (implies (fn-ctl-cause-record ws cause target)
           (equal (fn-ctl-w-target (fn-ctl-cause-record ws cause target)) target))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawalp fn-ctl-w-target))))
(defthm fn-ctl-cause-record-is-a-member
  (implies (fn-ctl-cause-record ws cause target)
           (and (member-equal (fn-ctl-cause-record ws cause target) ws)
                (fn-ctl-withdrawalp (fn-ctl-cause-record ws cause target))
                (equal (fn-ctl-w-cause (fn-ctl-cause-record ws cause target)) cause)
                (equal (fn-ctl-w-target (fn-ctl-cause-record ws cause target))
                       target)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-ctl-cause-record fn-ctl-withdrawalp
                                      fn-ctl-w-cause fn-ctl-w-target))))

(defthm fn-ctl-find-held-is-held
  (implies (fn-ctl-find-held m visible withdrawn)
           (and (or (member-equal (fn-ctl-find-held m visible withdrawn) visible)
                    (member-equal (fn-ctl-find-held m visible withdrawn) withdrawn))
                (equal (fn-article-msgid (fn-ctl-find-held m visible withdrawn)) m)))
  :hints (("Goal" :in-theory (disable fn-ctl-msgid-withdrawn))))

; KEYSTONE (HDR :fn-control, executed).  In a view whose served list is the
; visible articles of RAW and whose W is RAW's withdrawn list, when C is in
; RAW and its status is executed, the target is held in RAW and the view does
; not serve it, and the record C caused withdraws it on the stated basis.
(defthm fn-ctl-executed-status-means-withdrawn
  (let ((st (fn-ctl-control-status c (fn-ctl-visible-articles raw ws verdicts)
                                   (fn-ctl-withdrawn-articles raw ws verdicts)
                                   ws verdicts))
        (target (fn-ctl-target-octets (fn-article-payload c))))
    (implies (and (equal (car st) :executed)
                  (member-equal c raw))
             (let ((held (fn-ctl-find-held target
                                           (fn-ctl-visible-articles raw ws verdicts)
                                           (fn-ctl-withdrawn-articles raw ws verdicts)))
                   (rec (fn-ctl-cause-record ws (fn-article-msgid c) target)))
               (and (member-equal held raw)
                    (not (member-equal held (fn-ctl-visible-articles raw ws verdicts)))
                    (equal (fn-article-msgid held) target)
                    (member-equal rec ws)
                    (equal (fn-ctl-w-cause rec) (fn-article-msgid c))
                    (equal (cadr st)
                           (fn-ctl-withdrawal-effect
                            rec (fn-article-groups held)
                            (fn-ctl-lookup-verdict target verdicts)))
                    (fn-ctl-effect-withdrawsp (cadr st))))))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawal-plan fn-ctl-withdrawalp
                                      fn-ctl-withdrawal-effect fn-ctl-effect-withdrawsp
                                      fn-ctl-find-held fn-ctl-cause-record
                                      fn-ctl-visible-articles fn-ctl-withdrawn-articles
                                      fn-ctl-target-octets fn-ctl-lookup-verdict
                                      fn-ctl-target-is-never-visible-beside-its-cancel
                                      fn-ctl-has-msgid-p fn-ctl-w-cause fn-ctl-w-target)
           :use ((:instance fn-ctl-find-held-is-held
                            (m (fn-ctl-target-octets (fn-article-payload c)))
                            (visible (fn-ctl-visible-articles raw ws verdicts))
                            (withdrawn (fn-ctl-withdrawn-articles raw ws verdicts)))
                 (:instance fn-ctl-cause-record-is-a-member
                            (cause (fn-article-msgid c))
                            (target (fn-ctl-target-octets (fn-article-payload c))))
                 (:instance fn-ctl-has-msgid-p-of-member (x c) (arts raw))
                 (:instance fn-ctl-target-is-never-visible-beside-its-cancel
                            (w (fn-ctl-cause-record ws (fn-article-msgid c)
                                                    (fn-ctl-target-octets
                                                     (fn-article-payload c))))
                            (article (fn-ctl-find-held
                                      (fn-ctl-target-octets (fn-article-payload c))
                                      (fn-ctl-visible-articles raw ws verdicts)
                                      (fn-ctl-withdrawn-articles raw ws verdicts)))
                            (articles raw))))))

; KEYSTONE (HDR :fn-control, owed).  Owed means RAW holds no article with
; the target's Message-ID.
(defthm fn-ctl-owed-status-means-not-held
  (implies (and (equal (car (fn-ctl-control-status
                             c (fn-ctl-visible-articles raw ws verdicts)
                             (fn-ctl-withdrawn-articles raw ws verdicts) ws verdicts))
                       :owed)
                (member-equal x raw))
           (not (equal (fn-article-msgid x)
                       (fn-ctl-target-octets (fn-article-payload c)))))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawal-plan fn-ctl-withdrawalp
                                      fn-ctl-withdrawal-effect fn-ctl-effect-withdrawsp
                                      fn-ctl-cause-record fn-ctl-msgid-withdrawn
                                      fn-ctl-visible-articles fn-ctl-withdrawn-articles
                                      fn-ctl-target-octets fn-ctl-lookup-verdict
                                      fn-ctl-withdrawn-is-the-complement)
           :cases ((member-equal x (fn-ctl-visible-articles raw ws verdicts)))
           :use ((:instance fn-ctl-withdrawn-is-the-complement (arts raw))
                 (:instance fn-ctl-msgid-withdrawn-finds-a-member
                            (xs (fn-ctl-visible-articles raw ws verdicts))
                            (msgid (fn-article-msgid x)))
                 (:instance fn-ctl-msgid-withdrawn-finds-a-member
                            (xs (fn-ctl-withdrawn-articles raw ws verdicts))
                            (msgid (fn-article-msgid x)))))))

; The HDR item text (design section 4): the status as the reader sees it.
(defun fn-ctl-control-item (status target)
  (declare (xargs :guard t))
  (let ((tag (and (consp status) (car status)))
        (arg (and (consp status) (consp (cdr status)) (cadr status))))
    (cond ((eq tag :executed)
           (concatenate 'string "executed withdrawal "
                        (if (stringp target) target "")
                        (if (eq arg :author) " author" " authority")))
          ((eq tag :owed) "owed")
          ((eq tag :declined)
           (concatenate 'string "declined "
                        (if (and (symbolp arg)
                                 (standard-char-listp (coerce (symbol-name arg) 'list)))
                            (string-downcase (symbol-name arg))
                          "unknown")))
          (t "none"))))

;; -----------------------------------------------------------------------------
;; The control pin a served connection carries (control-c3e): the view's
;; withdrawn list W and the withdrawal records WS it was decided under, pinned
;; at open or advance with the archive, so a reader never sees a later
;; decision.  The pinned dispatcher reads it from the fourth slot of the group
;; pin (`fn-gidx-pin-with-control', books/group-bucket-index.lisp).

(defun fn-ctl-pin (withdrawn ws)
  (declare (xargs :guard t))
  (list :fn-control withdrawn ws))

(defun fn-ctl-pin-withdrawn (x)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr x)))

(defun fn-ctl-pin-ws (x)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr x))))

(defthm fn-ctl-pin-withdrawn-of-pin
  (equal (fn-ctl-pin-withdrawn (fn-ctl-pin withdrawn ws)) withdrawn))
(defthm fn-ctl-pin-ws-of-pin
  (equal (fn-ctl-pin-ws (fn-ctl-pin withdrawn ws)) ws))
(defthm fn-ctl-pin-withdrawn-of-nil
  (equal (fn-ctl-pin-withdrawn nil) nil))

;; The served lookups, over the pinned Message-ID trie of the visible list
;; instead of a scan of it.  A target that is not a non-empty string (no
;; parsed Control or Supersedes names one) takes the scan, which the trie
;; cannot answer; the reader never reaches that case with a found target.

(defun fn-ctl-served-held (msgid trie visible withdrawn)
  (declare (xargs :guard t))
  (or (fn-ctl-msgid-withdrawn msgid withdrawn)
      (if (consp (fn-midx-key-chars msgid))
          (let ((hit (fn-midx-lookup msgid trie)))
            (if (consp hit) hit nil))
        (fn-ctl-msgid-withdrawn msgid visible))))

(defthm fn-ctl-find-article-is-msgid-withdrawn
  (implies (stringp msgid)
           (equal (if (consp (fn-find-article msgid xs))
                      (fn-find-article msgid xs)
                    nil)
                  (fn-ctl-msgid-withdrawn msgid xs)))
  :hints (("Goal" :in-theory (enable fn-find-article fn-ctl-msgid-withdrawn))))

; KEYSTONE (the served lookup is the kernel's).  Over the trie of the
; visible list, the served lookup finds what `fn-ctl-find-held' finds.
(defthm fn-ctl-served-held-is-find-held
  (implies (fn-midx-correspondencep trie visible)
           (equal (fn-ctl-served-held msgid trie visible withdrawn)
                  (fn-ctl-find-held msgid visible withdrawn)))
  :hints (("Goal" :in-theory (e/d (fn-ctl-find-held fn-midx-correspondencep
                                   fn-midx-key-chars)
                                  (fn-midx-lookup fn-midx-build
                                   fn-find-article fn-ctl-msgid-withdrawn
                                   fn-ctl-find-article-is-msgid-withdrawn))
           :use ((:instance fn-ctl-find-article-is-msgid-withdrawn
                            (xs visible))
                 (:instance fn-midx-lookup-of-build-is-find-article-for-nonempty
                            (articles visible))))))

; The served :fn-control status: `fn-ctl-control-status' with the held
; target found through the trie.
(defun fn-ctl-served-status (c trie visible withdrawn ws verdicts)
  (declare (xargs :guard t))
  (let* ((msgid (and (consp c) (fn-article-msgid c)))
         (target (and (consp c) (fn-ctl-target-octets (fn-article-payload c))))
         (plan (fn-ctl-withdrawal-plan msgid (fn-ctl-lookup-verdict msgid verdicts)
                                       target nil)))
    (cond ((not target) (list :none))
          ((not (fn-ctl-withdrawalp plan)) (list :declined (fn-ctl-at 1 plan)))
          (t (let ((rec (fn-ctl-cause-record ws msgid target)))
               (if (not rec)
                   (list :declined :no-record)
                 (let ((held (fn-ctl-served-held target trie visible withdrawn)))
                   (if (not held)
                       (list :owed)
                     (let ((effect (fn-ctl-withdrawal-effect
                                    rec (fn-article-groups held)
                                    (fn-ctl-lookup-verdict target verdicts))))
                       (if (fn-ctl-effect-withdrawsp effect)
                           (list :executed effect)
                         (list :declined (fn-ctl-at 1 effect))))))))))))

(defthm fn-ctl-served-status-is-control-status
  (implies (fn-midx-correspondencep trie visible)
           (equal (fn-ctl-served-status c trie visible withdrawn ws verdicts)
                  (fn-ctl-control-status c visible withdrawn ws verdicts)))
  :hints (("Goal" :in-theory (e/d (fn-ctl-control-status)
                                  (fn-ctl-served-held fn-ctl-find-held
                                   fn-midx-correspondencep
                                   fn-ctl-withdrawal-plan fn-ctl-withdrawalp
                                   fn-ctl-withdrawal-effect fn-ctl-effect-withdrawsp
                                   fn-ctl-cause-record fn-ctl-target-octets
                                   fn-ctl-lookup-verdict)))))

; The article the reader names in `HDR :fn-control <msgid>': served or
; withdrawn, found as the held target is.
(defthm fn-ctl-find-held-is-in-raw
  (implies (fn-ctl-find-held m (fn-ctl-visible-articles raw ws verdicts)
                             (fn-ctl-withdrawn-articles raw ws verdicts))
           (member-equal (fn-ctl-find-held m (fn-ctl-visible-articles raw ws verdicts)
                                           (fn-ctl-withdrawn-articles raw ws verdicts))
                         raw))
  :hints (("Goal" :in-theory (disable fn-ctl-find-held fn-ctl-visible-articles
                                      fn-ctl-withdrawn-articles)
           :use ((:instance fn-ctl-find-held-is-held
                            (visible (fn-ctl-visible-articles raw ws verdicts))
                            (withdrawn (fn-ctl-withdrawn-articles raw ws verdicts)))))))

(in-theory (disable (:d fn-ctl-withdrawn-filter) (:d fn-ctl-subseq-diff)
                    (:d fn-ctl-refresh-withdrawn) (:d fn-ctl-control-status)
                    (:d fn-ctl-cause-record) (:d fn-ctl-find-held)
                    (:d fn-ctl-msgid-withdrawn) (:d fn-ctl-served-held)
                    (:d fn-ctl-served-status)))
