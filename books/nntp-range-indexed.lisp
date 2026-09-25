; Indexed range renderers used by the pinned NNTP dispatcher.  The bucket
; selects local numbers; its entries resolve through the pinned Message-ID
; trie.  Neither path traverses the retained article list per output line.
(in-package "ACL2")
(include-book "nntp-responses")
(include-book "group-bucket-article")

(defun fn-nov-lines-for-numbers-indexed (group numbers entries trie)
  (declare (xargs :guard t))
  (if (consp numbers)
      (let* ((number (car numbers))
             (article (fn-gidx-entry-number-article group number entries trie))
             ; D13: a reclaimed article is skipped before the parser.
             (over (if (and (consp article)
                            (not (fn-rcl-tombstonep (fn-article-payload article))))
                       (fn-nov-overview article)
                     (list :error))))
        (if (fn-nov-okp over)
            (cons (fn-nov-line number over)
                  (fn-nov-lines-for-numbers-indexed
                   group (cdr numbers) entries trie))
          (fn-nov-lines-for-numbers-indexed
           group (cdr numbers) entries trie)))
    nil))

(defun fn-nntp-over-range-indexed (session buckets trie token legacyp)
  (declare (xargs :guard t))
  (let ((group (fn-nntp-session-group session))
        (range (fn-nntp-parse-range token)))
    (if (null group)
        (fn-nntp-single session "412 no newsgroup selected")
      (let* ((entries (fn-gidx-bucket group buckets))
             (numbers (fn-nntp-index-group-range-numbers
                       entries group (fn-nntp-range-low range)
                       (fn-nntp-range-high range)))
             (lines (fn-nov-lines-for-numbers-indexed
                     group numbers entries trie)))
        (if (consp lines)
            (fn-nntp-multi session "224 overview information follows" lines)
          (fn-nntp-single
           session (if legacyp "420 no article(s) selected"
                     "423 no articles in that range")))))))

(defthm fn-nntp-over-range-indexed-preserves-session
  (equal (fn-nntp-result-session
          (fn-nntp-over-range-indexed session buckets trie token legacyp))
         session)
  :hints (("Goal" :in-theory (e/d (fn-nntp-over-range-indexed
                                  fn-nntp-single fn-nntp-multi
                                  fn-nntp-result-session fn-nntp-make-result)
                                  (fn-nov-lines-for-numbers-indexed
                                   fn-gidx-range-numbers)))))
