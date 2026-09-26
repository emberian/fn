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

; The served renderer (over-number-index, PRF-189): each row's article comes
; from the bucket's number index (`fn-gidx-nidx-number-article', at most 31
; trie steps) instead of a walk of the bucket per row.  It renders what
; `fn-nov-lines-for-numbers-indexed' renders
; (`fn-nov-lines-for-numbers-numbered-of-build' below).
(defun fn-nov-lines-for-numbers-numbered (numbers nidx trie)
  (declare (xargs :guard t))
  (if (consp numbers)
      (let* ((number (car numbers))
             (article (fn-gidx-nidx-number-article number nidx trie))
             ; D13: a reclaimed article is skipped before the parser.
             (over (if (and (consp article)
                            (not (fn-rcl-tombstonep (fn-article-payload article))))
                       (fn-nov-overview article)
                     (list :error))))
        (if (fn-nov-okp over)
            (cons (fn-nov-line number over)
                  (fn-nov-lines-for-numbers-numbered (cdr numbers) nidx trie))
          (fn-nov-lines-for-numbers-numbered (cdr numbers) nidx trie)))
    nil))

(defthm fn-nov-lines-for-numbers-numbered-of-build
  (equal (fn-nov-lines-for-numbers-numbered
          numbers (fn-gnix-build group entries) trie)
         (fn-nov-lines-for-numbers-indexed group numbers entries trie))
  :hints (("Goal" :induct (fn-nov-lines-for-numbers-indexed
                           group numbers entries trie)
           :in-theory (disable fn-gidx-nidx-number-article
                               fn-gidx-entry-number-article fn-gnix-build
                               fn-nov-overview fn-nov-okp fn-nov-line
                               fn-rcl-tombstonep))))

; OVER/XOVER of a range in the pinned dispatcher: the numbers from the
; bucket (`fn-nntp-index-group-range-numbers'), each row through the number
; index.  Under the group index's relation (`fn-gidx-numbers-okp') this is
; the bucket walk's answer (`fn-nntp-over-range-indexed-is-walk' below).
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
             (lines (fn-nov-lines-for-numbers-numbered
                     numbers (fn-gidx-bucket-numbers group buckets) trie)))
        (if (consp lines)
            (fn-nntp-multi session "224 overview information follows" lines)
          (fn-nntp-single
           session (if legacyp "420 no article(s) selected"
                     "423 no articles in that range")))))))

; The spec: the same renderer with each row found by the bucket walk.
(defun fn-nntp-over-range-walk (session buckets trie token legacyp)
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

(defthm fn-nntp-over-range-indexed-is-walk
  (implies (fn-gidx-numbers-okp buckets)
           (equal (fn-nntp-over-range-indexed session buckets trie token legacyp)
                  (fn-nntp-over-range-walk session buckets trie token legacyp)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-over-range-indexed
                                   fn-nntp-over-range-walk)
                                  (fn-nov-lines-for-numbers-numbered
                                   fn-nov-lines-for-numbers-indexed
                                   fn-gnix-build fn-gidx-bucket
                                   fn-gidx-bucket-numbers
                                   fn-gidx-numbers-okp
                                   fn-nntp-index-group-range-numbers
                                   fn-nntp-multi fn-nntp-single
                                   fn-nntp-parse-range)))))

(defthm fn-nntp-over-range-indexed-preserves-session
  (equal (fn-nntp-result-session
          (fn-nntp-over-range-indexed session buckets trie token legacyp))
         session)
  :hints (("Goal" :in-theory (e/d (fn-nntp-over-range-indexed
                                  fn-nntp-single fn-nntp-multi
                                  fn-nntp-result-session fn-nntp-make-result)
                                  (fn-nov-lines-for-numbers-indexed
                                   fn-gidx-range-numbers)))))
