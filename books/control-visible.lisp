; fn: the visible article list, maintained incrementally (packet C3, D27).
;
; `fn-ctl-visible-articles' (books/control-authority.lisp) is the article
; list a newly published reader view serves: every article but a target some
; withdrawal record, whose cause is in the same list, withdraws.  Computing
; it afresh walks every article against every record, per refresh; the
; served path may not do that ("no whole-state revalidation on a served
; path", AGENTS.md; D27).  This book is the incremental form the committed
; view's refresh is to carry: the visible list of (A . OLD) from the visible
; list of OLD, and a batch of new articles folded one at a time, with the
; correspondence theorem that makes the carried list equal the definition.
;
; Work per new article A (WS the records, N the visible list):
;   - one pass over WS for records whose cause is A (`fn-ctl-causes-p');
;   - one pass over WS for records whose target is A, each probing the
;     article list for its cause (`fn-ctl-withdrawn-by-p' on A only);
;   - a pass over N only when A is the cause of some record (A is a cancel
;     with a decided withdrawal), dropping what A's records withdraw.
; So an ordinary article costs O(|WS|) and no walk of the archive; a cancel
; costs O(N x |WS|) once.  The cause probe is a list walk here; the owner
; wiring answers it from the Message-ID trie (fn-midx-lookup-of-build-is-
; find-article).  Pessimistic figure: an archive of N articles and R
; records costs N x R per executed cancel and R per other article.
;
; Prefix `fn-ctl-' (docs/prefixes.md).
(in-package "ACL2")
(include-book "control-authority")

; Some record in WS whose cause is CAUSE withdraws X.
(defun fn-ctl-withdrawn-via-p (x ws cause verdicts)
  (declare (xargs :guard t))
  (if (consp ws)
      (let ((w (car ws)))
        (or (and (fn-ctl-withdrawalp w)
                 (consp x)
                 (equal (fn-ctl-w-target w) (fn-article-msgid x))
                 (equal (fn-ctl-w-cause w) cause)
                 (fn-ctl-effect-withdrawsp
                  (fn-ctl-withdrawal-effect
                   w (fn-article-groups x)
                   (fn-ctl-lookup-verdict (fn-article-msgid x) verdicts))))
            (fn-ctl-withdrawn-via-p x (cdr ws) cause verdicts)))
    nil))

; Does any record name CAUSE as its cause?
(defun fn-ctl-causes-p (ws cause)
  (declare (xargs :guard t))
  (if (consp ws)
      (or (and (fn-ctl-withdrawalp (car ws))
               (equal (fn-ctl-w-cause (car ws)) cause))
          (fn-ctl-causes-p (cdr ws) cause))
    nil))

; XS without what the records caused by CAUSE withdraw.
(defun fn-ctl-drop-via (xs ws cause verdicts)
  (declare (xargs :guard t))
  (if (consp xs)
      (if (fn-ctl-withdrawn-via-p (car xs) ws cause verdicts)
          (fn-ctl-drop-via (cdr xs) ws cause verdicts)
        (cons (car xs) (fn-ctl-drop-via (cdr xs) ws cause verdicts)))
    nil))

; One new article A over OLD, whose visible list is OLD-VISIBLE.
(defun fn-ctl-visible-add (a old-visible old ws verdicts)
  (declare (xargs :guard t))
  (if (consp a)
      (let ((kept (if (fn-ctl-causes-p ws (fn-article-msgid a))
                      (fn-ctl-drop-via old-visible ws (fn-article-msgid a)
                                       verdicts)
                    old-visible)))
        (if (fn-ctl-withdrawn-by-p a ws (cons a old) verdicts)
            kept
          (cons a kept)))
    (cons a old-visible)))

; `append' with guard t (the same logical definition).
(defun fn-ctl-prepend (xs ys)
  (declare (xargs :guard t))
  (if (consp xs) (cons (car xs) (fn-ctl-prepend (cdr xs) ys)) ys))

(defthm fn-ctl-prepend-is-append
  (equal (fn-ctl-prepend xs ys) (append xs ys)))

; A batch DELTA (newest first, as the acceptance archive conses) over OLD.
(defun fn-ctl-visible-extend (delta old-visible old ws verdicts)
  (declare (xargs :guard t))
  (if (consp delta)
      (fn-ctl-visible-add (car delta)
                          (fn-ctl-visible-extend (cdr delta) old-visible old
                                                 ws verdicts)
                          (fn-ctl-prepend (cdr delta) old) ws verdicts)
    old-visible))

; -----------------------------------------------------------------------------
; The correspondence.

(defthm fn-ctl-has-msgid-p-of-cons
  (equal (fn-ctl-has-msgid-p m (cons a arts))
         (or (and (consp a) (equal (fn-article-msgid a) m))
             (fn-ctl-has-msgid-p m arts))))

(defthm fn-ctl-withdrawn-by-p-of-cons-article
  (iff (fn-ctl-withdrawn-by-p x ws (cons a arts) verdicts)
       (or (fn-ctl-withdrawn-by-p x ws arts verdicts)
           (and (consp a)
                (fn-ctl-withdrawn-via-p x ws (fn-article-msgid a) verdicts))))
  :hints (("Goal" :induct (fn-ctl-withdrawn-by-p x ws arts verdicts)
           :in-theory (disable fn-ctl-withdrawal-effect
                               fn-ctl-effect-withdrawsp
                               fn-ctl-withdrawalp
                               fn-ctl-has-msgid-p))))

(defthm fn-ctl-drop-via-of-cons
  (equal (fn-ctl-drop-via (cons x xs) ws cause verdicts)
         (if (fn-ctl-withdrawn-via-p x ws cause verdicts)
             (fn-ctl-drop-via xs ws cause verdicts)
           (cons x (fn-ctl-drop-via xs ws cause verdicts)))))

(defthm fn-ctl-drop-via-of-atom
  (implies (not (consp xs))
           (equal (fn-ctl-drop-via xs ws cause verdicts) nil)))

(defthm fn-ctl-visible-filter-of-cons-article
  (implies (consp a)
           (equal (fn-ctl-visible-filter xs ws (cons a arts) verdicts)
                  (fn-ctl-drop-via (fn-ctl-visible-filter xs ws arts verdicts)
                                   ws (fn-article-msgid a) verdicts)))
  :hints (("Goal" :induct (fn-ctl-visible-filter xs ws arts verdicts)
           :in-theory (disable fn-ctl-withdrawn-by-p fn-ctl-withdrawn-via-p
                               fn-ctl-drop-via))))

(defthm fn-ctl-visible-filter-of-cons-atom
  (implies (not (consp a))
           (equal (fn-ctl-visible-filter xs ws (cons a arts) verdicts)
                  (fn-ctl-visible-filter xs ws arts verdicts)))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawn-by-p))))

(defthm fn-ctl-withdrawn-via-p-needs-a-cause
  (implies (not (fn-ctl-causes-p ws cause))
           (not (fn-ctl-withdrawn-via-p x ws cause verdicts)))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawal-effect
                                      fn-ctl-effect-withdrawsp))))

(defthm fn-ctl-drop-via-without-a-cause
  (implies (and (not (fn-ctl-causes-p ws cause))
                (true-listp xs))
           (equal (fn-ctl-drop-via xs ws cause verdicts) xs)))

(defthm fn-ctl-true-listp-of-visible-filter
  (true-listp (fn-ctl-visible-filter xs ws arts verdicts))
  :rule-classes (:rewrite :type-prescription))

(defthm fn-ctl-withdrawn-by-p-of-an-atom
  (implies (not (consp a))
           (not (fn-ctl-withdrawn-by-p a ws arts verdicts))))

; KEYSTONE (C3, D27).  The carried visible list after one new article is the
; definition's visible list of the grown archive, whenever the carried list
; before it was the definition's: the refresh never needs the whole-archive
; filter to stay correct.
(defthm fn-ctl-visible-add-is-visible
  (implies (equal old-visible (fn-ctl-visible-articles old ws verdicts))
           (equal (fn-ctl-visible-add a old-visible old ws verdicts)
                  (fn-ctl-visible-articles (cons a old) ws verdicts)))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawn-by-p
                                      fn-ctl-withdrawn-via-p
                                      fn-ctl-drop-via fn-ctl-causes-p))))

; KEYSTONE (C3, D27).  The same for a batch, the shape the owner's refresh
; sees between two idle phases: the new archive is DELTA consed onto OLD.
(defthm fn-ctl-visible-extend-is-visible
  (implies (equal old-visible (fn-ctl-visible-articles old ws verdicts))
           (equal (fn-ctl-visible-extend delta old-visible old ws verdicts)
                  (fn-ctl-visible-articles (append delta old) ws verdicts)))
  :hints (("Goal" :induct (fn-ctl-visible-extend delta old-visible old ws
                                                 verdicts)
           :in-theory (disable fn-ctl-visible-add fn-ctl-visible-articles))))

(in-theory (disable (:d fn-ctl-visible-add) (:d fn-ctl-visible-extend)
                    (:d fn-ctl-drop-via) (:d fn-ctl-causes-p)
                    (:d fn-ctl-withdrawn-via-p)))
