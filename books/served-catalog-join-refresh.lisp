; served-catalog-join-refresh.lisp -- the refresh's side of the join's step
; (lane sca-join, 2026-09-27; split from books/served-catalog-join-step.lisp
; to keep each book under 10 s): what one article's drop-via removes from the
; old visible list is exactly what T4 withdraws (fn-scj-drop-via-is-keep,
; fn-scj-visible-add-kept-is-keep), and the new article is visible exactly
; when the rebuilt index shows its Message-ID (fn-scj-visible-add-shows-a).

(in-package "ACL2")

(include-book "served-catalog-owner")

; The rules below never reason about a Message-ID's syntax.
(local (in-theory (disable fn-nntp-article-idp-is-consp fn-scat-article-idp-is-msgid-idp
                           fn-scat-msgid-idp fn-nntp-index-msgid-okp-stringp
                           fn-nntp-index-msgid-okp fn-cp-id-length-bound)))

; -----------------------------------------------------------------------------
; The refresh's side: what one article's drop-via removes.

(defun fn-scj-keep (arts targets index)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp arts)
      (if (and (member-equal (fn-article-msgid (car arts)) targets)
               (not (fn-midx-lookup (fn-article-msgid (car arts)) index)))
          (fn-scj-keep (cdr arts) targets index)
        (cons (car arts) (fn-scj-keep (cdr arts) targets index)))
    nil))


(defthm fn-scj-withdrawn-via-names-a-target
  (implies (fn-ctl-withdrawn-via-p x ws cause verdicts)
           (member-equal (fn-article-msgid x) (fn-sca-targets-of cause ws)))
  :hints (("Goal" :induct (fn-ctl-withdrawn-via-p x ws cause verdicts)
           :in-theory (e/d (fn-ctl-withdrawn-via-p)
                           (fn-ctl-withdrawal-effect fn-ctl-effect-withdrawsp fn-ctl-withdrawalp)))))

(defthm fn-scj-targets-when-no-cause
  (implies (not (fn-ctl-causes-p ws cause))
           (equal (fn-sca-targets-of cause ws) nil))
  :hints (("Goal" :induct (fn-sca-targets-of cause ws)
           :in-theory (e/d (fn-ctl-causes-p) (fn-ctl-withdrawalp)))))

(defthm fn-scj-causes-when-withdrawn-via
  (implies (fn-ctl-withdrawn-via-p x ws cause verdicts)
           (fn-ctl-causes-p ws cause))
  :hints (("Goal" :induct (fn-ctl-withdrawn-via-p x ws cause verdicts)
           :in-theory (e/d (fn-ctl-withdrawn-via-p fn-ctl-causes-p)
                           (fn-ctl-withdrawal-effect fn-ctl-effect-withdrawsp fn-ctl-withdrawalp)))))

(defthm fn-scj-keep-of-no-targets
  (implies (true-listp arts)
           (equal (fn-scj-keep arts nil index) arts)))


(defthm fn-scj-acceptedp-of-member
  (implies (member-equal x w)
           (fn-acceptedp (fn-article-msgid x) w))
  :hints (("Goal" :in-theory (enable fn-acceptedp))))

(defthm fn-scj-has-msgid-of-drop-via
  (implies (and (no-duplicatesp-equal (fn-article-msgids v))
                (member-equal x v)
                (consp x))
           (iff (fn-ctl-has-msgid-p (fn-article-msgid x) (fn-ctl-drop-via v ws cause verdicts))
                (not (fn-ctl-withdrawn-via-p x ws cause verdicts))))
  :hints (("Goal" :induct (fn-ctl-drop-via v ws cause verdicts)
           :in-theory (disable fn-ctl-withdrawn-via-p))))

(defthm fn-scj-has-msgid-of-member
  (implies (and (member-equal x w) (consp x))
           (fn-ctl-has-msgid-p (fn-article-msgid x) w)))

(defthm fn-scj-has-msgid-of-drop-via-subset
  (implies (not (fn-ctl-has-msgid-p m v))
           (not (fn-ctl-has-msgid-p m (fn-ctl-drop-via v ws cause verdicts))))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawn-via-p))))


; For an article X of the old visible list V: the refresh's drop-via withdraws
; X exactly when X's Message-ID is a target of A's records and the new visible
; list no longer carries it.
(defthm fn-scj-withdrawn-via-iff
  (implies (and (consp a)
                (no-duplicatesp-equal (fn-article-msgids (cons a v)))
                (member-equal x v)
                (consp x))
           (iff (fn-ctl-withdrawn-via-p x ws (fn-article-msgid a) verdicts)
                (and (member-equal (fn-article-msgid x)
                                   (fn-sca-targets-of (fn-article-msgid a) ws))
                     (not (fn-ctl-has-msgid-p (fn-article-msgid x)
                                              (fn-ctl-visible-add a v old ws verdicts))))))
  :hints (("Goal" :in-theory (e/d (fn-ctl-visible-add)
                                  (fn-ctl-withdrawn-via-p fn-ctl-drop-via fn-ctl-causes-p
                                   fn-ctl-withdrawn-by-p fn-sca-targets-of))
           :cases ((equal (fn-article-msgid x) (fn-article-msgid a))))))

(defthm fn-scj-find-article-iff-has-msgid
  (implies (fn-midx-string-article-listp v2)
           (iff (fn-find-article m v2) (fn-ctl-has-msgid-p m v2)))
  :hints (("Goal" :in-theory (enable fn-find-article fn-midx-string-article-listp))))

(defthm fn-scj-lookup-of-build-iff-has-msgid
  (implies (and (stringp m) (fn-midx-string-article-listp v2))
           (iff (fn-midx-lookup m (fn-midx-build v2)) (fn-ctl-has-msgid-p m v2)))
  :hints (("Goal" :in-theory (disable fn-midx-build fn-midx-lookup))))

(defthm fn-scj-string-msgid-of-member
  (implies (and (fn-midx-string-article-listp v) (member-equal x v))
           (and (stringp (fn-article-msgid x)) (consp x)))
  :hints (("Goal" :in-theory (enable fn-midx-string-article-listp))))


(defthm fn-scj-drop-via-is-keep
  (implies (and (consp a)
                (no-duplicatesp-equal (fn-article-msgids (cons a v)))
                (fn-midx-string-article-listp v)
                (fn-midx-string-article-listp (fn-ctl-visible-add a v old ws verdicts))
                (subsetp-equal w v))
           (equal (fn-ctl-drop-via w ws (fn-article-msgid a) verdicts)
                  (fn-scj-keep w (fn-sca-targets-of (fn-article-msgid a) ws)
                               (fn-midx-build (fn-ctl-visible-add a v old ws verdicts)))))
  :hints (("Goal" :induct (fn-scj-keep w (fn-sca-targets-of (fn-article-msgid a) ws)
                                       (fn-midx-build (fn-ctl-visible-add a v old ws verdicts)))
           :in-theory (disable fn-ctl-withdrawn-via-p fn-ctl-visible-add fn-midx-build fn-midx-lookup
                               fn-sca-targets-of fn-scj-withdrawn-via-iff fn-ctl-has-msgid-p
                               fn-midx-string-article-listp))
          ("Subgoal *1/2" :use ((:instance fn-scj-withdrawn-via-iff (x (car w)))))
          ("Subgoal *1/1" :use ((:instance fn-scj-withdrawn-via-iff (x (car w)))))))

(defthm fn-scj-subsetp-cons (implies (subsetp-equal x y) (subsetp-equal x (cons a y))))

(defthm fn-scj-subsetp-refl (subsetp-equal x x))

(defthm fn-scj-visible-add-kept-is-keep
  (implies (and (consp a)
                (true-listp v)
                (no-duplicatesp-equal (fn-article-msgids (cons a v)))
                (fn-midx-string-article-listp v)
                (fn-midx-string-article-listp (fn-ctl-visible-add a v old ws verdicts)))
           (equal (if (fn-ctl-causes-p ws (fn-article-msgid a))
                      (fn-ctl-drop-via v ws (fn-article-msgid a) verdicts)
                    v)
                  (fn-scj-keep v (fn-sca-targets-of (fn-article-msgid a) ws)
                               (fn-midx-build (fn-ctl-visible-add a v old ws verdicts)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-ctl-visible-add fn-midx-build fn-sca-targets-of fn-ctl-drop-via
                               fn-scj-drop-via-is-keep fn-ctl-causes-p)
           :use ((:instance fn-scj-drop-via-is-keep (w v))))))

(defthm fn-scj-kept-msgids-subset
  (implies (not (member-equal m (fn-article-msgids v)))
           (not (fn-ctl-has-msgid-p m (fn-ctl-drop-via v ws cause verdicts)))))

(defthm fn-scj-has-msgid-of-member-msgids
  (implies (not (member-equal m (fn-article-msgids v)))
           (not (fn-ctl-has-msgid-p m v))))

(defthm fn-scj-visible-add-shows-a
  (implies (and (consp a)
                (stringp (fn-article-msgid a))
                (no-duplicatesp-equal (fn-article-msgids (cons a v)))
                (fn-midx-string-article-listp (fn-ctl-visible-add a v old ws verdicts)))
           (iff (fn-midx-lookup (fn-article-msgid a) (fn-midx-build (fn-ctl-visible-add a v old ws verdicts)))
                (not (fn-ctl-withdrawn-by-p a ws (cons a old) verdicts))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-ctl-visible-add)
                           (fn-midx-build fn-midx-lookup fn-ctl-drop-via fn-ctl-withdrawn-by-p fn-ctl-causes-p)))))

(defthm fn-scj-with-withdrawn-fields
  (and (equal (fn-held-withdrawn (fn-held-with-withdrawn h w)) w)
       (equal (fn-record-msgid (fn-held-with-withdrawn h w)) (fn-record-msgid h))
       (equal (fn-record-payload (fn-held-with-withdrawn h w)) (fn-record-payload h))
       (equal (fn-record-groups (fn-held-with-withdrawn h w)) (fn-record-groups h))
       (equal (fn-record-stamp (fn-held-with-withdrawn h w)) (fn-record-stamp h))
       (equal (fn-record-sequence (fn-held-with-withdrawn h w)) (fn-record-sequence h))
       (equal (fn-held-sequence (fn-held-with-withdrawn h w)) (fn-held-sequence h))
       (equal (fn-held-numbers (fn-held-with-withdrawn h w)) (fn-held-numbers h)))
  :hints (("Goal" :in-theory (enable fn-held-with-withdrawn fn-record-internals fn-held-internals))))
