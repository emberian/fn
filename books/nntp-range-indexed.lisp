; Indexed range renderers used by the pinned NNTP dispatcher.  The bucket
; selects local numbers; its entries resolve through the pinned Message-ID
; trie.  Neither path traverses the retained article list per output line.
(in-package "ACL2")
(include-book "nntp-responses")
(include-book "protocol-table") ; reply texts: (fn-proto-text ROW KEY)
(include-book "group-bucket-article")

(defun fn-nov-lines-for-numbers-indexed (group numbers entries trie fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (consp numbers)
      (let* ((number (car numbers))
             (article (fn-gidx-entry-number-article group number entries trie))
             ; D13: a reclaimed article is skipped before the parser.
             (over (if (and (consp article)
                            (not (fn-nntp-article-tombstonep article fn-arena)))
                       (fn-nov-overview article fn-arena)
                     (list :error))))
        (if (fn-nov-okp over)
            (cons (fn-nov-line number over)
                  (fn-nov-lines-for-numbers-indexed
                   group (cdr numbers) entries trie fn-arena))
          (fn-nov-lines-for-numbers-indexed
           group (cdr numbers) entries trie fn-arena)))
    nil))

; The served renderer (over-number-index, PRF-189): each row's article comes
; from the bucket's number index (`fn-gidx-nidx-number-article', at most 31
; trie steps) instead of a walk of the bucket per row.  It renders what
; `fn-nov-lines-for-numbers-indexed' renders
; (`fn-nov-lines-for-numbers-numbered-of-build' below).
; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-nov-lines-for-numbers-numbered-loop (numbers nidx trie fn-arena acc)
  (declare (xargs :stobjs fn-arena :guard (true-listp acc) :verify-guards nil))
  (if (consp numbers)
      (let* ((number (car numbers))
             (article (fn-gidx-nidx-number-article number nidx trie))
             (over (if (and (consp article)
                            (not (fn-nntp-article-tombstonep article fn-arena)))
                       (fn-nov-overview article fn-arena)
                     (list :error))))
        (if (fn-nov-okp over)
            (fn-nov-lines-for-numbers-numbered-loop (cdr numbers)
                                                    nidx
                                                    trie
                                                    fn-arena
                                                    (cons (fn-nov-line number over) acc))
          (fn-nov-lines-for-numbers-numbered-loop (cdr numbers) nidx trie fn-arena acc)))
    (revappend acc nil)))

(defun fn-nov-lines-for-numbers-numbered (numbers nidx trie fn-arena)
  (declare (xargs :verify-guards nil :stobjs fn-arena :guard t))
  (mbe :logic
       (if (consp numbers)
           (let* ((number (car numbers))
                  (article (fn-gidx-nidx-number-article number nidx trie))
                  ; D13: a reclaimed article is skipped before the parser.
                  (over (if (and (consp article)
                                 (not (fn-nntp-article-tombstonep article fn-arena)))
                            (fn-nov-overview article fn-arena)
                          (list :error))))
             (if (fn-nov-okp over)
                 (cons (fn-nov-line number over)
                       (fn-nov-lines-for-numbers-numbered (cdr numbers) nidx trie fn-arena))
               (fn-nov-lines-for-numbers-numbered (cdr numbers) nidx trie fn-arena)))
         nil)
       :exec (fn-nov-lines-for-numbers-numbered-loop numbers nidx trie fn-arena nil)))

(local
 (defthm fn-nov-lines-for-numbers-numbered-loop-is-revappend
   (equal (fn-nov-lines-for-numbers-numbered-loop numbers nidx trie fn-arena acc)
          (revappend acc (fn-nov-lines-for-numbers-numbered numbers nidx trie fn-arena)))
   :hints (("Goal" :induct (fn-nov-lines-for-numbers-numbered-loop numbers nidx trie fn-arena acc)
                   :in-theory (union-theories '(fn-nov-lines-for-numbers-numbered-loop fn-nov-lines-for-numbers-numbered revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-nov-lines-for-numbers-numbered-loop)

(verify-guards fn-nov-lines-for-numbers-numbered
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-nov-lines-for-numbers-numbered)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-nov-lines-for-numbers-numbered-loop-is-revappend (acc nil))))))


(defthm fn-nov-lines-for-numbers-numbered-of-build
  (equal (fn-nov-lines-for-numbers-numbered
          numbers (fn-gnix-build group entries) trie fn-arena)
         (fn-nov-lines-for-numbers-indexed group numbers entries trie fn-arena))
  :hints (("Goal" :induct (fn-nov-lines-for-numbers-indexed
                           group numbers entries trie fn-arena)
           :in-theory (disable fn-gidx-nidx-number-article
                               fn-gidx-entry-number-article fn-gnix-build
                               fn-nov-overview fn-nov-okp fn-nov-line
                               fn-rcl-tombstonep))))

; OVER/XOVER of a range in the pinned dispatcher: the numbers from the
; bucket (`fn-nntp-index-group-range-numbers'), each row through the number
; index.  Under the group index's relation (`fn-gidx-numbers-okp') this is
; the bucket walk's answer (`fn-nntp-over-range-indexed-is-walk' below).
(defun fn-nntp-over-range-indexed (session buckets trie token legacyp fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (let ((group (fn-nntp-session-group session))
        (range (fn-nntp-parse-range token)))
    (if (null group)
        (fn-nntp-single session (fn-proto-text * :no-group-selected))
      (let* ((entries (fn-gidx-bucket group buckets))
             (numbers (fn-nntp-index-group-range-numbers
                       entries group (fn-nntp-range-low range)
                       (fn-nntp-range-high range)))
             (lines (fn-nov-lines-for-numbers-numbered
                     numbers (fn-gidx-bucket-numbers group buckets) trie fn-arena)))
        (if (consp lines)
            (fn-nntp-multi session (fn-proto-text * :overview) lines)
          (fn-nntp-single
           session (if legacyp (fn-proto-text * :none-selected)
                     (fn-proto-text * :empty-range))))))))

; The spec: the same renderer with each row found by the bucket walk.
(defun fn-nntp-over-range-walk (session buckets trie token legacyp fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (let ((group (fn-nntp-session-group session))
        (range (fn-nntp-parse-range token)))
    (if (null group)
        (fn-nntp-single session (fn-proto-text * :no-group-selected))
      (let* ((entries (fn-gidx-bucket group buckets))
             (numbers (fn-nntp-index-group-range-numbers
                       entries group (fn-nntp-range-low range)
                       (fn-nntp-range-high range)))
             (lines (fn-nov-lines-for-numbers-indexed
                     group numbers entries trie fn-arena)))
        (if (consp lines)
            (fn-nntp-multi session (fn-proto-text * :overview) lines)
          (fn-nntp-single
           session (if legacyp (fn-proto-text * :none-selected)
                     (fn-proto-text * :empty-range))))))))

(defthm fn-nntp-over-range-indexed-is-walk
  (implies (fn-gidx-numbers-okp buckets)
           (equal (fn-nntp-over-range-indexed session buckets trie token legacyp fn-arena)
                  (fn-nntp-over-range-walk session buckets trie token legacyp fn-arena)))
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
          (fn-nntp-over-range-indexed session buckets trie token legacyp fn-arena))
         session)
  :hints (("Goal" :in-theory (e/d (fn-nntp-over-range-indexed
                                  fn-nntp-single fn-nntp-multi
                                  fn-nntp-result-session fn-nntp-make-result)
                                  (fn-nov-lines-for-numbers-indexed
                                   fn-gidx-range-numbers)))))
