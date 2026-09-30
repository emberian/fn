; Exact existing selected line reader; no new locator.
(in-package "ACL2")
(include-book "served-selected-article")
(include-book "nov-overview-source")
(include-book "nov-render-line")

(defmacro fn-scat-guard ()
  '(and (natp v) (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)))

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-nov-lines-for-numbers-cat-loop (group numbers v fn-arena fn-cat acc)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (and (fn-scat-guard) (true-listp acc)) :verify-guards nil))
  (if (consp numbers)
      (let* ((number (car numbers))
             (article (fn-scat-available-article group number v fn-arena fn-cat))
             (over (if (and (consp article)
                            (not (fn-nntp-article-tombstonep article fn-arena)))
                       (fn-nov-overview article fn-arena)
                     (list :error))))
        (if (fn-nov-okp over)
            (fn-nov-lines-for-numbers-cat-loop group
                                               (cdr numbers)
                                               v
                                               fn-arena
                                               fn-cat
                                               (cons (fn-nov-line number over) acc))
          (fn-nov-lines-for-numbers-cat-loop group (cdr numbers) v fn-arena fn-cat acc)))
    (revappend acc nil)))

(defun fn-nov-lines-for-numbers-cat (group numbers v fn-arena fn-cat)
  (declare (xargs :verify-guards nil :stobjs (fn-arena fn-cat) :guard (fn-scat-guard)))
  (mbe :logic
       (if (consp numbers)
           (let* ((number (car numbers))
                  (article (fn-scat-available-article group number v fn-arena fn-cat))
                  (over (if (and (consp article)
                                 (not (fn-nntp-article-tombstonep article fn-arena)))
                            (fn-nov-overview article fn-arena)
                          (list :error))))
             (if (fn-nov-okp over)
                 (cons (fn-nov-line number over)
                       (fn-nov-lines-for-numbers-cat group (cdr numbers) v fn-arena fn-cat))
               (fn-nov-lines-for-numbers-cat group (cdr numbers) v fn-arena fn-cat)))
         nil)
       :exec (fn-nov-lines-for-numbers-cat-loop group numbers v fn-arena fn-cat nil)))

(local
 (defthm fn-nov-lines-for-numbers-cat-loop-is-revappend
   (equal (fn-nov-lines-for-numbers-cat-loop group numbers v fn-arena fn-cat acc)
          (revappend acc (fn-nov-lines-for-numbers-cat group numbers v fn-arena fn-cat)))
   :hints (("Goal" :induct (fn-nov-lines-for-numbers-cat-loop group numbers v fn-arena fn-cat acc)
                   :in-theory (union-theories '(fn-nov-lines-for-numbers-cat-loop fn-nov-lines-for-numbers-cat revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-nov-lines-for-numbers-cat-loop)

(verify-guards fn-nov-lines-for-numbers-cat
  :hints (("Goal" :in-theory (union-theories '(revappend fn-nov-lines-for-numbers-cat)
                                                  (union-theories (theory 'minimal-theory)
                                                                  (executable-counterpart-theory :here)))
                  :use ((:instance fn-nov-lines-for-numbers-cat-loop-is-revappend (acc nil))))))
