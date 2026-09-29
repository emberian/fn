; Derived per-group buckets for served NNTP number/range reads.  The source
; entries and all validity decisions remain books/index and books/nntp-index.
(in-package "ACL2")
(include-book "nntp-index-runtime")
(include-book "protocol-table") ; reply texts: (fn-proto-text ROW KEY)
(include-book "msgid-index")
(include-book "group-number-index")

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-gnix-add)
                          (:definition fn-gnix-build)
                          (:definition fn-gnix-key)
                          (:definition fn-midx-put-chars)
                          (:definition fn-nntp-index-entry-available)
                          (:definition fn-nntp-index-msgid-okp))))

; A bucket is (group entries . numbers): the group's entries, newest first,
; and NUMBERS, the same entries keyed by available number
; (books/group-number-index.lisp; over-number-index, PRF-189).  `fn-gidx-put'
; keeps both; `fn-gidx-numbers-okp' below is the relation between them.
(defun fn-gidx-bucket (group buckets)
  (declare (xargs :guard t))
  (if (consp buckets)
      (if (equal group (fn-ag-car (fn-ag-car buckets)))
          (fn-ag-car (fn-ag-cdr (fn-ag-car buckets)))
        (fn-gidx-bucket group (cdr buckets)))
    nil))

(defun fn-gidx-bucket-numbers (group buckets)
  (declare (xargs :guard t))
  (if (consp buckets)
      (if (equal group (fn-ag-car (fn-ag-car buckets)))
          (fn-ag-cdr (fn-ag-cdr (fn-ag-car buckets)))
        (fn-gidx-bucket-numbers group (cdr buckets)))
    nil))

; Executes by a loop (lane depth-debt, PRF-919): it walks the buckets, one per configured newsgroup holding articles, operator
; data with no fixed cap (D27), and the recursion took one control-stack frame
; per element.  (mbe :logic <the recursion, unchanged> :exec <a loop>), equal
; by the lemma after it (books/rev-onto.lisp fn-ag-rev-onto).
(defun fn-gidx-put-loop (entry buckets acc)
  (declare (xargs :guard t))
  (let ((group (fn-index-entry-group entry)))
    (if (consp buckets)
        (if (equal group (fn-ag-car (fn-ag-car buckets)))
            (let ((bucket (fn-ag-cdr (fn-ag-car buckets))))
              (fn-ag-rev-onto
               acc
               (cons (cons group
                           (cons (cons entry (fn-ag-car bucket))
                                 (fn-gnix-add group entry (fn-ag-cdr bucket))))
                     (cdr buckets))))
          (fn-gidx-put-loop entry (cdr buckets) (cons (car buckets) acc)))
      (fn-ag-rev-onto
       acc (list (cons group (cons (list entry) (fn-gnix-add group entry nil))))))))

(defun fn-gidx-put (entry buckets)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (let ((group (fn-index-entry-group entry)))
         (if (consp buckets)
             (if (equal group (fn-ag-car (fn-ag-car buckets)))
                 (let ((bucket (fn-ag-cdr (fn-ag-car buckets))))
                   (cons (cons group
                               (cons (cons entry (fn-ag-car bucket))
                                     (fn-gnix-add group entry (fn-ag-cdr bucket))))
                         (cdr buckets)))
               (cons (car buckets) (fn-gidx-put entry (cdr buckets))))
           (list (cons group (cons (list entry) (fn-gnix-add group entry nil))))))
       :exec (fn-gidx-put-loop entry buckets nil)))

(defthm fn-gidx-put-loop-is-rev-onto
  (equal (fn-gidx-put-loop entry buckets acc)
         (fn-ag-rev-onto acc (fn-gidx-put entry buckets)))
  :hints (("Goal" :induct (fn-gidx-put-loop entry buckets acc)
                  :in-theory (union-theories
                              '(fn-gidx-put-loop fn-gidx-put fn-ag-rev-onto
                                car-cons cdr-cons)
                              (theory 'minimal-theory)))))

(verify-guards fn-gidx-put
  :hints (("Goal" :in-theory (union-theories
                              '(fn-gidx-put fn-ag-rev-onto fn-gidx-put-loop-is-rev-onto car-cons cdr-cons)
                              (union-theories (theory 'minimal-theory)
                                              (executable-counterpart-theory :here))))))

; Executes by a loop (PKT-876, lane open-depth): one control-stack frame per
; retained article on the owner's open.  The :logic is the recursion,
; unchanged; the :exec is a loop, equal by the guard proof.
(defun fn-gidx-build-entries-loop (rev acc)
  (declare (xargs :guard t))
  (if (consp rev)
      (fn-gidx-build-entries-loop (cdr rev) (fn-gidx-put (car rev) acc))
    acc))

(defun fn-gidx-build-entries (entries)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (consp entries)
           (fn-gidx-put (car entries) (fn-gidx-build-entries (cdr entries)))
         nil)
       :exec (fn-gidx-build-entries-loop (fn-ag-rev-onto entries nil) nil)))

(encapsulate ()
  (local
   (defthm fn-gidx-build-entries-loop-of-rev-onto
     (equal (fn-gidx-build-entries-loop (fn-ag-rev-onto xs zs) nil)
            (fn-gidx-build-entries-loop zs (fn-gidx-build-entries xs)))
     :hints (("Goal" :induct (fn-ag-rev-onto xs zs)
                     :in-theory (disable fn-gidx-put)))))
  (verify-guards fn-gidx-build-entries
    :hints (("Goal" :in-theory (disable fn-gidx-put fn-ag-rev-onto)
                    :use ((:instance fn-gidx-build-entries-loop-of-rev-onto (xs entries) (zs nil)))))))

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

; The relation the group index carries (PRF-189): every bucket's number index
; is its entries' (`fn-gnix-build').  Proof-side only: no served step
; evaluates it.  Established by every build and preserved by `fn-gidx-put'
; (and so by `fn-gidx-put-all' and `fn-gidx-refresh', books/owner.lisp).
(defun fn-gidx-numbers-okp (buckets)
  (declare (xargs :guard t))
  (if (consp buckets)
      (let ((bucket (fn-ag-car buckets)))
        (and (equal (fn-ag-cdr (fn-ag-cdr bucket))
                    (fn-gnix-build (fn-ag-car bucket)
                                   (fn-ag-car (fn-ag-cdr bucket))))
             (fn-gidx-numbers-okp (cdr buckets))))
    t))

(defthm fn-gidx-bucket-numbers-under-okp
  (implies (fn-gidx-numbers-okp buckets)
           (equal (fn-gidx-bucket-numbers group buckets)
                  (fn-gnix-build group (fn-gidx-bucket group buckets)))))

(defthm fn-gidx-numbers-okp-of-put
  (implies (fn-gidx-numbers-okp buckets)
           (fn-gidx-numbers-okp (fn-gidx-put entry buckets)))
  :hints (("Goal" :induct (fn-gidx-put entry buckets))))

(defthm fn-gidx-numbers-okp-of-build-entries
  (fn-gidx-numbers-okp (fn-gidx-build-entries entries)))

(defthm fn-gidx-numbers-okp-of-build
  (fn-gidx-numbers-okp (fn-gidx-build articles))
  :hints (("Goal" :in-theory (enable fn-gidx-build))))

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
    (fn-nntp-single session (fn-proto-text * :no-group))))

(defun fn-gidx-listgroup-command (session archive buckets args)
  (declare (xargs :guard t))
  (let ((all-range (list :ok 1 2147483647)))
    (if (null args)
        (let ((group (fn-nntp-session-group session)))
          (if (null group)
              (fn-nntp-single session (fn-proto-text * :no-group-selected))
            (if (mbe :logic (member-equal group (fn-state-groups archive))
                     :exec (fn-ag-member group (fn-state-groups archive)))
                (fn-gidx-listgroup-result session archive buckets group all-range)
              (fn-nntp-single session (fn-proto-text * :no-group-selected)))))
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
                (fn-nntp-single session (fn-proto-text * :syntax))))
          (fn-nntp-single session (fn-proto-text * :syntax)))))))

;; Withdrawn from includers (lane rule-hygiene, tools/rule_cost.py).
;; Each is tried in includers' proofs and pays for its frames in
;; almost none (planning/evidence/rule-cost-*.json has the counts;
;; docs/proof-style.md section 8).  An includer that needs one
;; enables it where it is used.
(in-theory (disable (:definition fn-gidx-numbers-okp)
                    (:definition fn-gidx-put)
                    (:rewrite fn-gidx-bucket-numbers-under-okp)))
