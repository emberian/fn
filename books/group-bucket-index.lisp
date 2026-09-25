; Derived per-group buckets for served NNTP number/range reads.  The source
; entries and all validity decisions remain books/index and books/nntp-index.
(in-package "ACL2")
(include-book "nntp-index-runtime")
(include-book "msgid-index")

(defun fn-gidx-bucket (group buckets)
  (declare (xargs :guard t))
  (if (consp buckets)
      (if (equal group (fn-ag-car (fn-ag-car buckets)))
          (fn-ag-cdr (fn-ag-car buckets))
        (fn-gidx-bucket group (cdr buckets)))
    nil))

(defun fn-gidx-put (entry buckets)
  (declare (xargs :guard t))
  (let ((group (fn-index-entry-group entry)))
    (if (consp buckets)
        (if (equal group (fn-ag-car (fn-ag-car buckets)))
            (cons (cons group (cons entry (fn-ag-cdr (fn-ag-car buckets))))
                  (cdr buckets))
          (cons (car buckets) (fn-gidx-put entry (cdr buckets))))
      (list (cons group (list entry))))))

(defun fn-gidx-build-entries (entries)
  (declare (xargs :guard t))
  (if (consp entries)
      (fn-gidx-put (car entries) (fn-gidx-build-entries (cdr entries)))
    nil))

(defun fn-gidx-build (articles)
  (declare (xargs :guard t))
  (fn-gidx-build-entries (fn-index-build articles)))

(defun fn-gidx-select (group entries)
  (declare (xargs :guard t))
  (if (consp entries)
      (if (equal group (fn-index-entry-group (car entries)))
          (cons (car entries) (fn-gidx-select group (cdr entries)))
        (fn-gidx-select group (cdr entries)))
    nil))

(defthm fn-gidx-bucket-of-put
  (equal (fn-gidx-bucket group (fn-gidx-put entry buckets))
         (if (equal group (fn-index-entry-group entry))
             (cons entry (fn-gidx-bucket group buckets))
           (fn-gidx-bucket group buckets)))
  :hints (("Goal" :induct (fn-gidx-put entry buckets))))

(defthm fn-gidx-bucket-of-build-entries
  (equal (fn-gidx-bucket group (fn-gidx-build-entries entries))
         (fn-gidx-select group entries)))

; The selected bucket is the exact ordered membership projection of the
; authoritative archive.  Connection pins carry this fact from build time;
; served reads never revalidate against the entire archive.
(defthm fn-gidx-bucket-of-build
  (equal (fn-gidx-bucket group (fn-gidx-build articles))
         (fn-gidx-select group (fn-index-build articles)))
  :hints (("Goal" :in-theory (enable fn-gidx-build))))

(defun fn-gidx-range-numbers (buckets group low high)
  (declare (xargs :guard t))
  (fn-nntp-index-group-range-numbers
   (fn-gidx-bucket group buckets) group low high))

(defthm fn-gidx-select-listp
  (implies (fn-index-listp entries)
           (fn-index-listp (fn-gidx-select group entries))))

(defthm fn-gidx-built-bucket-listp
  (implies (fn-article-listp configured articles)
           (fn-index-listp
            (fn-gidx-bucket group (fn-gidx-build articles))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-index-build-listp)
                 (:instance fn-gidx-select-listp
                            (entries (fn-index-build articles))))
           :in-theory (disable fn-index-build-listp fn-gidx-select-listp))))

(defthm fn-gidx-raw-range-of-select
  (equal (fn-index-range-query-raw (fn-gidx-select group entries)
                                    group low high)
         (fn-index-range-query-raw entries group low high))
  :hints (("Goal" :induct (fn-gidx-select group entries)
           :in-theory (enable fn-index-range-query-raw
                              fn-index-entry-in-range-p))))

(defthm fn-gidx-query-range-of-select
  (implies (and (fn-index-listp entries)
                (stringp group) (natp low) (natp high))
           (equal (fn-index-query-range (fn-gidx-select group entries)
                                        group low high)
                  (fn-index-query-range entries group low high)))
  :hints (("Goal" :in-theory (enable fn-index-query-range))))

; Reuse the existing number projection and correctness theorem, rather than
; introducing another definition of NNTP local-number availability.
(defthm fn-gidx-range-of-build-is-flat-index-range
  (implies (and (fn-index-listp entries)
                (stringp group) (natp low) (natp high))
           (equal (fn-gidx-range-numbers (fn-gidx-build-entries entries)
                                         group low high)
                  (fn-nntp-index-group-range-numbers entries group low high)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-gidx-bucket-of-build-entries)
                 (:instance fn-gidx-query-range-of-select))
           :in-theory (e/d (fn-gidx-range-numbers
                            fn-nntp-index-group-range-numbers)
                           (fn-gidx-bucket-of-build-entries
                            fn-gidx-query-range-of-select)))))

; Exact number of bucket headers visited by one lookup.  The range evaluator
; then visits at most the selected bucket's entries, independent of unrelated
; memberships.  No archive recognizer or article projection runs per query.
(defun fn-gidx-lookup-work (group buckets)
  (declare (xargs :guard t))
  (if (consp buckets)
      (if (equal group (fn-ag-car (fn-ag-car buckets)))
          1
        (1+ (fn-gidx-lookup-work group (cdr buckets))))
    0))

(defun fn-gidx-range-work (buckets group)
  (declare (xargs :guard t))
  (+ (fn-gidx-lookup-work group buckets)
     (len (fn-gidx-bucket group buckets))))

(defthm fn-gidx-lookup-work-at-most-bucket-count
  (<= (fn-gidx-lookup-work group buckets) (len buckets))
  :rule-classes :linear)

; The pinned dispatcher receives this tagged pair through its existing index
; argument.  The middle POST/peer/auth layers make no index decision and keep
; one transition definition each.  The owner and served records still carry
; the trie and buckets as separate immutable fields.
;; The fourth slot is the control pin (control-c3e, books/control-served.lisp
;; `fn-ctl-pin'): the view's withdrawn list and its withdrawal records, which
;; the dispatcher reads for `423 withdrawn', `430 withdrawn' and
;; `HDR :fn-control'.  A pin without one carries nil.
(defun fn-gidx-pin-with-control (trie buckets control)
  (declare (xargs :guard t))
  (list :fn-group-pin trie buckets control))

(defun fn-gidx-pin (trie buckets)
  (declare (xargs :guard t))
  (fn-gidx-pin-with-control trie buckets nil))

(defun fn-gidx-pinp (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 4)
       (equal (fn-ag-car x) :fn-group-pin)))

(defun fn-gidx-pin-control (x)
  (declare (xargs :guard t))
  (if (fn-gidx-pinp x)
      (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))
    nil))

(defun fn-gidx-pin-trie (x)
  (declare (xargs :guard t))
  (if (fn-gidx-pinp x) (fn-ag-car (fn-ag-cdr x)) x))

(defun fn-gidx-pin-buckets (x)
  (declare (xargs :guard t))
  (if (fn-gidx-pinp x)
      (fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))
    nil))

(defthm fn-gidx-alistp-of-midx-branch-put
  (implies (alistp branches)
           (alistp (fn-midx-branch-put key value branches)))
  :hints (("Goal" :induct (fn-midx-branch-put key value branches)
           :in-theory (enable fn-midx-branch-put))))

(defthm fn-gidx-alistp-of-midx-put-chars
  (implies (alistp trie)
           (alistp (fn-midx-put-chars characters article trie)))
  :hints (("Goal" :induct (fn-midx-put-chars characters article trie)
           :in-theory (enable fn-midx-put-chars))))

(defthm fn-gidx-alistp-of-midx-build
  (alistp (fn-midx-build articles))
  :hints (("Goal" :induct (fn-midx-build articles)
           :in-theory (enable fn-midx-build fn-midx-extend))))

(defthm fn-gidx-alist-is-not-pin
  (implies (alistp x) (not (fn-gidx-pinp x)))
  :hints (("Goal" :in-theory (enable fn-gidx-pinp alistp))))

(defthm fn-gidx-midx-build-not-pin
  (not (fn-gidx-pinp (fn-midx-build articles)))
  :hints (("Goal" :use ((:instance fn-gidx-alist-is-not-pin
                                   (x (fn-midx-build articles))))
           :in-theory (disable fn-gidx-pinp fn-midx-build))))

(defthm fn-gidx-pinp-of-pin
  (fn-gidx-pinp (fn-gidx-pin trie buckets)))
(defthm fn-gidx-pin-trie-of-pin
  (equal (fn-gidx-pin-trie (fn-gidx-pin trie buckets)) trie))
(defthm fn-gidx-pin-buckets-of-pin
  (equal (fn-gidx-pin-buckets (fn-gidx-pin trie buckets)) buckets))
(defthm fn-gidx-pin-control-of-pin
  (equal (fn-gidx-pin-control (fn-gidx-pin trie buckets)) nil))
(defthm fn-gidx-pinp-of-pin-with-control
  (fn-gidx-pinp (fn-gidx-pin-with-control trie buckets control)))
(defthm fn-gidx-pin-trie-of-pin-with-control
  (equal (fn-gidx-pin-trie (fn-gidx-pin-with-control trie buckets control)) trie))
(defthm fn-gidx-pin-buckets-of-pin-with-control
  (equal (fn-gidx-pin-buckets (fn-gidx-pin-with-control trie buckets control))
         buckets))
(defthm fn-gidx-pin-control-of-pin-with-control
  (equal (fn-gidx-pin-control (fn-gidx-pin-with-control trie buckets control))
         control))
(defthm fn-gidx-pin-with-control-shape
  (and (consp (fn-gidx-pin-with-control trie buckets control))
       (true-listp (fn-gidx-pin-with-control trie buckets control))))
(in-theory (disable fn-gidx-pin-with-control))

; Proof-side cache relation.  Served transitions carry this relation; no
; dispatcher evaluates it while processing a command.
(defun fn-gidx-pin-correspondencep (index archive)
  (declare (xargs :guard t :verify-guards nil))
  (or (not (fn-gidx-pinp index))
      (equal (fn-gidx-pin-buckets index)
             (fn-gidx-build (fn-state-articles archive)))))

(defun fn-gidx-group-summary (archive buckets group)
  (declare (xargs :guard t))
  (let* ((entries (fn-gidx-bucket group buckets))
         (low (fn-nntp-index-group-low entries group)))
    (if (posp low)
        (list (fn-nntp-index-group-count entries group)
              low
              (fn-nntp-index-group-high entries group))
      (let ((watermark (fn-next-number group (fn-state-nexts archive))))
        (list 0 watermark (if (posp watermark) (- watermark 1) 0))))))

(defun fn-gidx-group-initial (archive buckets group)
  (declare (xargs :guard t))
  (let ((summary (fn-gidx-group-summary archive buckets group)))
    (fn-nntp-append-pieces
     (list (fn-nntp-string-octets "211 ")
           (fn-nntp-decimal-field (fn-nntp-summary-count summary)) '(32)
           (fn-nntp-decimal-field (fn-nntp-summary-low summary)) '(32)
           (fn-nntp-decimal-field (fn-nntp-summary-high summary)) '(32)
           (fn-nntp-string-octets group)))))

(defun fn-gidx-listgroup-result (session archive buckets group range)
  (declare (xargs :guard t))
  (if (mbe :logic (member-equal group (fn-state-groups archive))
           :exec (fn-ag-member group (fn-state-groups archive)))
      (let* ((low (fn-nntp-index-group-low (fn-gidx-bucket group buckets)
                                            group))
             (current (if (posp low) low nil))
             (next-session (fn-nntp-set-cursor session group current))
             (shown (fn-gidx-range-numbers buckets group
                                           (fn-nntp-range-low range)
                                           (fn-nntp-range-high range))))
        (fn-nntp-multi-octets next-session
                              (append (fn-gidx-group-initial archive buckets group)
                                      (fn-nntp-string-octets " list follows"))
                              (fn-nntp-number-lines shown)))
    (fn-nntp-single session "411 no such newsgroup")))

(defun fn-gidx-listgroup-command (session archive buckets args)
  (declare (xargs :guard t))
  (let ((all-range (list :ok 1 2147483647)))
    (if (null args)
        (let ((group (fn-nntp-session-group session)))
          (if (null group)
              (fn-nntp-single session "412 no newsgroup selected")
            (if (mbe :logic (member-equal group (fn-state-groups archive))
                     :exec (fn-ag-member group (fn-state-groups archive)))
                (fn-gidx-listgroup-result session archive buckets group all-range)
              (fn-nntp-single session "412 no newsgroup selected"))))
      (if (and (consp args) (null (cdr args))
               (fn-nntp-printable-tokenp (car args)))
          (fn-gidx-listgroup-result session archive buckets
                                    (fn-nntp-token-string (car args)) all-range)
        (if (and (consp args) (consp (cdr args)) (null (cdr (cdr args)))
                 (fn-nntp-printable-tokenp (car args)))
            (let ((range (fn-nntp-parse-range (car (cdr args)))))
              (if (fn-nntp-range-okp range)
                  (fn-gidx-listgroup-result
                   session archive buckets
                   (fn-nntp-token-string (car args)) range)
                (fn-nntp-single session "501 syntax error")))
          (fn-nntp-single session "501 syntax error"))))))
