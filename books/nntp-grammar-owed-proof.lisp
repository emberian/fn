; Exact discharges for the NNTP parser, renderer, and transcript runner.
(in-package "ACL2")
(include-book "nntp-grammar")
(include-book "owed-discharge")

(defthm fn2-nntp-reply-typing-proved
  (fn2-nntp-reply-typing$owed cmd reply mask n0 n1 n2 sslot sgen soff slen
                              slot gen okind oslot ogen pool)
  :hints (("Goal" :in-theory (union-theories
                              (theory 'minimal-theory)
                              '(fn2-nntp-reply-typing$owed fn2-nntp-render-typed-p
                                fn2-nntp-render mv-nth))))
  :rule-classes nil)

(fn2-owed-discharge fn2-nntp-reply-typing fn2-nntp-reply-typing-proved)

(local
 (defthm fn2-nntp-args-result
   (let* ((result (fn2-nntp-args tag s end slot gen okind oslot ogen pool))
          (code (mv-nth 0 result))
          (count (mv-nth 1 result)))
     (and (or (equal code :ok) (equal code :syntax))
          (natp count)
          (<= count 4)))
   :rule-classes nil
   :hints (("Goal"
            :in-theory
            (union-theories
             (theory 'minimal-theory)
             (append '(fn2-nntp-args mv-nth nfix natp eql)
                     (set-difference-eq
                      (all-fnnames (getpropc 'fn2-nntp-args 'unnormalized-body nil world))
                      '(if cons eql))))))))

(local
 (defthm fn2-nntp-keyword-tag-range
   (let ((tag (fn2-nntp-keyword-tag ts tl slot gen okind oslot ogen pool)))
     (and (natp tag) (<= tag *fn2-nntp-command-none*)))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                             '(fn2-nntp-keyword-tag natp))))
   :rule-classes nil))

(local
 (defmacro fn2-nntp-line-tag ()
   '(fn2-nntp-keyword-tag
     s (nfix (- (fn2-gram-skip (nfix (- (nfix (- e 2)) s)) s (nfix (- e 2))
                               nil slot gen okind oslot ogen pool)
                s))
     slot gen okind oslot ogen pool)))

(local
 (defthm fn2-nntp-parse-line-0-shape
   (let ((r (fn2-nntp-parse-line-0 s e mask slot gen okind oslot ogen pool)))
     (fn2-gram-parse-shape-p (mv-nth 0 r) (mv-nth 1 r) (mv-nth 2 r)
                             *fn2-nntp-command-none*))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance fn2-nntp-args-result (tag (fn2-nntp-line-tag))
                             (end (nfix (- e 2))))
                  (:instance fn2-nntp-keyword-tag-range (ts s)
                             (tl (nfix (- (fn2-gram-skip
                                           (nfix (- (nfix (- e 2)) s)) s (nfix (- e 2))
                                           nil slot gen okind oslot ogen pool)
                                          s)))))
            :in-theory (union-theories
                        (theory 'minimal-theory)
                        '(fn2-nntp-parse-line-0 fn2-gram-parse-shape-p
                          fn2-gram-check-line mv-nth member-equal natp))))))

(local
 (defthm fn2-nntp-immediate-block-tag
   (implies (equal (fn2-nntp-block tag) :immediate)
            (and (natp tag) (< tag *fn2-nntp-command-none*)))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                             '(fn2-nntp-block natp eql))))
   :rule-classes nil))

(defthm fn2-nntp-parse-total-proved
  (fn2-nntp-parse-total$owed s e mask slot gen okind oslot ogen pool)
  :rule-classes nil
  :hints (("Goal"
           :use (fn2-nntp-parse-line-0-shape
                 (:instance fn2-nntp-immediate-block-tag (tag (fn2-nntp-line-tag))))
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(fn2-nntp-parse-total$owed fn2-nntp-parse-outcome-p
                         fn2-nntp-parse-line fn2-gram-parse-shape-p
                         mv-nth member-equal natp)))))

(fn2-owed-discharge fn2-nntp-parse-total fn2-nntp-parse-total-proved)

; A pool view holds a prefix of the same transcript at every chunk boundary.
; Command parsing reads only the portion visible through the end of its line.
; The TX array and its fill carry the replies emitted so far.
(local (include-book "std/lists/resize-list" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/append" :dir :system))
(local (include-book "std/lists/update-nth" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))

(local
 (defun-nx fn2-nntp-run-pool ()
   (let* ((initial (fn2-pool-init '((2 . 8192)) 1 1000 (create-fn2-pool)))
          (rx (fn2-pool-reserve 0 1 1 1 initial)))
     (mv-nth 3 (fn2-pool-reserve 0 1 1 1 (mv-nth 3 rx))))))

(local
 (defun fn2-nntp-rx-array (xs k)
   (resize-list (take k xs) 8192 0)))

(local
 (defun-nx fn2-nntp-pool-at (xs k tx used)
   (update-nth *fn2-pool-datai* (append (fn2-nntp-rx-array xs k) tx)
               (update-nth *fn2-pool-fill$ai* (list k used) (fn2-nntp-run-pool)))))

(local (in-theory (disable fn2-nntp-rx-array fn2-nntp-pool-at fn2-nntp-run-pool)))

(local
 (defthm fn2-nntp-rx-array-length
   (equal (len (fn2-nntp-rx-array xs k)) 8192)
   :hints (("Goal" :in-theory (enable fn2-nntp-rx-array)))))

(local
 (defthm fn2-nntp-rx-array-byte
   (implies (and (natp i) (< i 8192) (natp k))
            (equal (nth i (fn2-nntp-rx-array xs k))
                   (if (< i k) (nth i xs) 0)))
   :hints (("Goal" :in-theory (enable fn2-nntp-rx-array)))))

(local
 (defthm fn2-nntp-pool-at-observations
   (let ((p (fn2-nntp-pool-at xs k tx used)))
     (and (equal (fn2-gram-fill 0 p) (nfix k))
          (equal (fn2-gram-fill 1 p) (nfix used))
          (equal (fn2-pool-fill 0 p) k)
          (equal (fn2-pool-fill 1 p) used)
          (equal (fn2-pool-base 0 p) 0)
          (equal (fn2-pool-base 1 p) 8192)
          (equal (fn2-pool-cap 0 p) 8192)
          (equal (fn2-pool-cap 1 p) 8192)
          (equal (fn2-pool-workspace-code 0 1 1 1 1 p) :ok)
          (equal (fn2-pool-workspace-code 1 1 1 1 1 p) :ok)
          (equal (fn2-pool-readable-code 0 1 1 1 1 p) :ok)
          (equal (fn2-pool-readable-code 1 1 1 1 1 p) :ok)
          (equal (fn2-pool-data-length p) (+ 8192 (len tx)))))
   :hints (("Goal" :in-theory
            (e/d (fn2-nntp-pool-at fn2-nntp-run-pool create-fn2-pool
                  fn2-gram-fill fn2-pool-rows fn2-pool-base fn2-pool-cap fn2-pool-fill
                  fn2-pool-workspace-code fn2-pool-handle-code fn2-pool-state
                  fn2-pool-readable-code fn2-pool-data-length)
                 (fn2-pool-init fn2-pool-reserve update-nth nth))))))

(local
 (defthm fn2-nntp-rx-advance
   (implies (and (natp k) (< k 8192))
            (equal (update-nth k (nth k xs) (fn2-nntp-rx-array xs k))
                   (fn2-nntp-rx-array xs (+ 1 k))))
   :hints ((equal-by-nths-hint))))

(local
 (defthm fn2-nntp-pool-at-read-rx
   (implies (and (natp i) (natp k) (< i k) (<= k 8192))
            (equal (fn2-pool-datai i (fn2-nntp-pool-at xs k tx used)) (nth i xs)))
   :hints (("Goal" :in-theory (enable fn2-pool-datai fn2-nntp-pool-at)))))

(local
 (defthm fn2-nntp-pool-at-append-rx
   (implies (and (natp k) (< k 8192))
            (equal (fn2-pool-set-fill 0 (+ 1 k)
                     (update-fn2-pool-datai k (nth k xs) (fn2-nntp-pool-at xs k tx used)))
                   (fn2-nntp-pool-at xs (+ 1 k) tx used)))
   :hints (("Goal" :in-theory (enable fn2-nntp-pool-at fn2-pool-set-fill
                                      update-fn2-pool-fill$ai update-fn2-pool-datai)))))

(local
 (defthm fn2-nntp-pool-at-append-tx
   (implies (natp used)
            (equal (fn2-pool-set-fill 1 (+ 1 used)
                     (update-fn2-pool-datai (+ 8192 used) b (fn2-nntp-pool-at xs k tx used)))
                   (fn2-nntp-pool-at xs k (update-nth used b tx) (+ 1 used))))
   :hints (("Goal" :in-theory (enable fn2-nntp-pool-at fn2-pool-set-fill
                                      update-fn2-pool-fill$ai update-fn2-pool-datai)))))

(local
 (defthm fn2-nntp-read-visible
   (implies (and (natp i) (natp k) (< i k) (<= k 8192))
            (equal (fn2-gram-read 0 1 i 1 1 1 (fn2-nntp-pool-at xs k tx used))
                   (let ((b (nth i xs)))
                     (if (and (natp b) (< b 256)) (list t b) (list nil 0)))))
   :hints (("Goal" :in-theory (e/d (fn2-gram-read fn2-pool-read)
                                   (fn2-pool-readable-code fn2-pool-datai
                                    fn2-pool-base fn2-pool-data-length fn2-pool-fill))))))

(local
 (defthm fn2-nntp-feed-one-visible
   (implies (and (natp k) (< k 8192) (unsigned-byte-p 8 (nth k xs)))
            (equal (fn2-gram-put (nth k xs) 0 1 1 1 1 (fn2-nntp-pool-at xs k tx used))
                   (list :ok (fn2-nntp-pool-at xs (+ 1 k) tx used))))
   :hints (("Goal" :in-theory (e/d (fn2-gram-put fn2-pool-write)
                                   (fn2-pool-workspace-code fn2-pool-set-fill
                                    update-fn2-pool-datai fn2-pool-data-length
                                    fn2-pool-base fn2-pool-cap fn2-pool-fill))))))

(local
 (defthm fn2-nntp-emit-one
   (implies (and (natp used) (equal (len tx) 8192))
            (equal (fn2-gram-put b 1 1 1 1 1 (fn2-nntp-pool-at xs k tx used))
                   (if (and (unsigned-byte-p 8 b) (< used 8192))
                       (list :ok (fn2-nntp-pool-at xs k (update-nth used b tx) (+ 1 used)))
                     (list :bounds (fn2-nntp-pool-at xs k tx used)))))
   :hints (("Goal" :in-theory (e/d (fn2-gram-put fn2-pool-write)
                                   (fn2-pool-workspace-code fn2-pool-set-fill
                                    update-fn2-pool-datai fn2-pool-data-length
                                    fn2-pool-base fn2-pool-cap fn2-pool-fill))))))

(local
 (defun-nx fn2-nntp-source (xs)
   (fn2-nntp-pool-at xs 8192 nil 0)))

(local
 (defthm fn2-nntp-read-source
   (implies (and (natp i) (< i 8192))
            (equal (fn2-gram-read 0 1 i 1 1 1 (fn2-nntp-source xs))
                   (let ((b (nth i xs)))
                     (if (and (natp b) (< b 256)) (list t b) (list nil 0)))))
   :hints (("Goal" :in-theory (enable fn2-nntp-source)))))

(local (in-theory (disable fn2-nntp-source)))

(local
 (in-theory
  (disable
   fn2-gram-utf8-step fn2-gram-wspp fn2-gram-line-scan fn2-gram-check-line fn2-gram-skip
   fn2-gram-token fn2-gram-count fn2-gram-upcase fn2-gram-match-loop fn2-gram-match
   fn2-gram-digits fn2-gram-arg-digits fn2-gram-arg-number fn2-gram-find fn2-gram-arg-range
   fn2-gram-msgid-middle fn2-gram-arg-msgid fn2-gram-wildmat-loop fn2-gram-arg-wildmat
   fn2-gram-label-loop fn2-gram-arg-label fn2-gram-arg-date fn2-gram-arg-time fn2-gram-arg
   fn2-gram-block-scan fn2-gram-clean-scan fn2-gram-structural-p fn2-nntp-keyword-tag
   fn2-nntp-args fn2-nntp-parse-line-0 fn2-nntp-parse-line fn2-nntp-block
   fn2-nntp-command-states)))
(local
 (defmacro fn2-nntp-visible-reader (fn args bounds &key recursive)
   (let* ((tail '(0 1 1 1 1))
          (left (cons fn (append args tail '((fn2-nntp-pool-at xs visible tx used)))))
          (right (cons fn (append args tail '((fn2-nntp-source xs))))))
     `(defthm ,(fn2-gram-sym fn "-on-visible-prefix")
        (implies (and (natp visible) (<= visible 8192) ,@bounds)
                 (equal ,left ,right))
        :hints (("Goal" ,@(and recursive `(:induct ,left))
                 :in-theory (enable ,fn)))))))

(local
 (fn2-nntp-visible-reader fn2-gram-line-scan (left i need lo hi bad ctl)
   ((natp left) (natp i) (<= (+ i left) visible)) :recursive t))

(local
 (fn2-nntp-visible-reader fn2-gram-skip (left i end ws)
   ((natp i) (natp end) (<= end visible)) :recursive t))

(local
 (fn2-nntp-visible-reader fn2-gram-digits (left i acc)
   ((natp left) (natp i) (<= (+ i left) visible)) :recursive t))

(local
 (fn2-nntp-visible-reader fn2-gram-find (left i byte)
   ((natp left) (natp i) (<= (+ i left) visible)) :recursive t))

(local
 (fn2-nntp-visible-reader fn2-gram-msgid-middle (left i)
   ((natp left) (natp i) (<= (+ i left) visible)) :recursive t))

(local
 (fn2-nntp-visible-reader fn2-gram-wildmat-loop (left i first atstart alen)
   ((natp left) (natp i) (<= (+ i left) visible)) :recursive t))

(local
 (fn2-nntp-visible-reader fn2-gram-label-loop (left i)
   ((natp left) (natp i) (<= (+ i left) visible)) :recursive t))

(local
 (fn2-nntp-visible-reader fn2-gram-block-scan (left i)
   ((natp left) (natp i) (<= (+ i left) visible)) :recursive t))

(local
 (fn2-nntp-visible-reader fn2-gram-clean-scan (left i)
   ((natp left) (natp i) (<= (+ i left) visible)) :recursive t))

(local
 (fn2-nntp-visible-reader fn2-gram-match-loop (k ts kw)
   ((natp ts) (stringp kw) (<= (+ ts (length kw)) visible)) :recursive t))

(local
 (fn2-nntp-visible-reader fn2-gram-token (n i end)
   ((natp i) (natp end) (<= end visible)) :recursive t))

(local
 (fn2-nntp-visible-reader fn2-gram-count (left i end)
   ((natp i) (natp end) (<= end visible)) :recursive t))

(local
 (defthm fn2-gram-skip-upper-bound
   (implies (and (natp i) (natp end) (<= i end))
            (<= (fn2-gram-skip left i end ws slot gen okind oslot ogen pool) end))
   :rule-classes :linear
   :hints (("Goal" :induct (fn2-gram-skip left i end ws slot gen okind oslot ogen pool)
            :in-theory (enable fn2-gram-skip)))))

(local
 (defthm fn2-gram-token-end-bound
   (let ((r (fn2-gram-token n i end slot gen okind oslot ogen pool)))
     (implies (and (natp i) (natp end) (<= i end))
              (<= (+ (mv-nth 1 r) (mv-nth 2 r)) end)))
   :rule-classes :linear
   :hints (("Goal" :induct (fn2-gram-token n i end slot gen okind oslot ogen pool)
            :in-theory (enable fn2-gram-token)))))

(local
 (defthm fn2-gram-find-when-found
   (let ((r (fn2-gram-find left i byte slot gen okind oslot ogen pool)))
     (implies (and (natp i) (natp left) (mv-nth 0 r))
              (and (<= i (mv-nth 1 r)) (< (mv-nth 1 r) (+ i left)))))
   :rule-classes :linear
   :hints (("Goal" :induct (fn2-gram-find left i byte slot gen okind oslot ogen pool)
            :in-theory (enable fn2-gram-find)))))

(local
 (fn2-nntp-visible-reader fn2-gram-match (ts tl kw)
   ((natp ts) (natp tl) (<= (+ ts tl) visible) (stringp kw))))

(local
 (fn2-nntp-visible-reader fn2-gram-arg-digits (ts tl)
   ((natp ts) (natp tl) (<= (+ ts tl) visible))))

(local
 (fn2-nntp-visible-reader fn2-gram-arg-number (ts tl)
   ((natp ts) (natp tl) (<= (+ ts tl) visible))))

(local
 (fn2-nntp-visible-reader fn2-gram-arg-range (ts tl)
   ((natp ts) (natp tl) (<= (+ ts tl) visible))))

(local
 (fn2-nntp-visible-reader fn2-gram-arg-msgid (ts tl)
   ((natp ts) (natp tl) (<= (+ ts tl) visible))))

(local
 (fn2-nntp-visible-reader fn2-gram-arg-wildmat (ts tl)
   ((natp ts) (natp tl) (<= (+ ts tl) visible))))

(local
 (fn2-nntp-visible-reader fn2-gram-arg-label (ts tl)
   ((natp ts) (natp tl) (<= (+ ts tl) visible) (< ts visible))))

(local
 (fn2-nntp-visible-reader fn2-gram-arg-date (ts tl)
   ((natp ts) (natp tl) (<= (+ ts tl) visible))))

(local
 (fn2-nntp-visible-reader fn2-gram-arg-time (ts tl)
   ((natp ts) (natp tl) (<= (+ ts tl) visible))))

(local
 (fn2-nntp-visible-reader fn2-gram-arg (kind ts tl)
   ((natp ts) (natp tl) (<= (+ ts tl) visible) (< ts visible))))

(local
 (fn2-nntp-visible-reader fn2-gram-check-line (s e)
   ((natp s) (natp e) (<= e visible))))

(local
 (fn2-nntp-visible-reader fn2-gram-structural-p (s e)
   ((natp s) (natp e) (<= e visible))))

(local
 (defthm fn2-nntp-arg-of-visible-token
   (let* ((r (fn2-gram-token n s end 0 1 1 1 1 (fn2-nntp-source xs)))
          (ts (mv-nth 1 r)) (tl (mv-nth 2 r)))
     (implies (and (natp s) (natp end) (<= s end)
                   (natp visible) (< end visible) (<= visible 8192))
              (equal (fn2-gram-arg kind ts tl 0 1 1 1 1 (fn2-nntp-pool-at xs visible tx used))
                     (fn2-gram-arg kind ts tl 0 1 1 1 1 (fn2-nntp-source xs)))))
   :hints (("Goal" :use ((:instance fn2-gram-token-end-bound
                          (i s) (slot 0) (gen 1) (okind 1) (oslot 1) (ogen 1)
                          (pool (fn2-nntp-source xs))))))))

(local
 (defthm fn2-nntp-match-of-visible-token
   (let* ((r (fn2-gram-token n s end 0 1 1 1 1 (fn2-nntp-source xs)))
          (ts (mv-nth 1 r)) (tl (mv-nth 2 r)))
     (implies (and (stringp kw) (natp s) (natp end) (<= s end)
                   (natp visible) (< end visible) (<= visible 8192))
              (equal (fn2-gram-match ts tl kw 0 1 1 1 1 (fn2-nntp-pool-at xs visible tx used))
                     (fn2-gram-match ts tl kw 0 1 1 1 1 (fn2-nntp-source xs)))))
   :hints (("Goal" :use ((:instance fn2-gram-token-end-bound
                          (i s) (slot 0) (gen 1) (okind 1) (oslot 1) (ogen 1)
                          (pool (fn2-nntp-source xs))))))))

(local
 (defthm fn2-nntp-args-on-visible-prefix
   (implies (and (natp visible) (<= visible 8192)
                 (natp s) (natp end) (<= s end) (< end visible))
            (equal (fn2-nntp-args tag s end 0 1 1 1 1 (fn2-nntp-pool-at xs visible tx used))
                   (fn2-nntp-args tag s end 0 1 1 1 1 (fn2-nntp-source xs))))
   :hints (("Goal" :in-theory (enable fn2-nntp-args)))))

(local
 (defthm fn2-gram-skip-at-end
   (implies (<= end i)
            (equal (fn2-gram-skip left i end ws slot gen okind oslot ogen pool) (nfix i)))
   :hints (("Goal" :in-theory (enable fn2-gram-skip)))))

(local
 (defthm fn2-gram-check-line-too-short
   (implies (< (- e s) 3)
            (equal (fn2-gram-check-line s e slot gen okind oslot ogen pool) :malformed))
   :hints (("Goal" :in-theory (enable fn2-gram-check-line)))))

(local
 (fn2-nntp-visible-reader fn2-nntp-keyword-tag (ts tl)
   ((natp ts) (natp tl) (<= (+ ts tl) visible))))

(local
 (fn2-nntp-visible-reader fn2-nntp-parse-line-0 (s e mask)
   ((natp s) (natp e) (< s e) (<= e visible))))

(local
 (fn2-nntp-visible-reader fn2-nntp-parse-line (s e mask)
   ((natp s) (natp e) (< s e) (<= e visible))))

; Rendering a zero-length source span changes only the TX slot.
(local
 (defun fn2-nntp-tx-data (p)
   (nthcdr 8192 (nth *fn2-pool-datai* p))))

(local
 (defun-nx fn2-nntp-graft (xs visible p)
   (fn2-nntp-pool-at xs visible (fn2-nntp-tx-data p) (fn2-pool-fill 1 p))))

(local
 (defun-nx fn2-nntp-txp (p)
   (and (natp (fn2-pool-fill 1 p))
        (equal (len (fn2-nntp-tx-data p)) 8192)
        (equal p (fn2-nntp-graft nil 0 p)))))

(local (in-theory (disable fn2-nntp-tx-data fn2-nntp-graft fn2-nntp-txp)))

(local
 (defthm fn2-nntp-nthcdr-len-append
   (equal (nthcdr (len a) (append a b)) b)
   :hints (("Goal" :induct (len a) :in-theory (enable nthcdr)))))

(local
 (defthm fn2-nntp-tx-data-of-view
   (equal (fn2-nntp-tx-data (fn2-nntp-pool-at xs k tx used)) tx)
   :hints (("Goal" :use ((:instance fn2-nntp-nthcdr-len-append
                           (a (fn2-nntp-rx-array xs k)) (b tx)))
            :in-theory (enable fn2-nntp-tx-data fn2-nntp-pool-at)))))

(local
 (defthm fn2-nntp-txp-of-view
   (implies (and (natp used) (equal (len tx) 8192))
            (fn2-nntp-txp (fn2-nntp-pool-at nil 0 tx used)))
   :hints (("Goal" :in-theory (e/d (fn2-nntp-txp fn2-nntp-graft)
                                   (fn2-pool-fill))))))

(local
 (defthmd fn2-nntp-tx-put-rule
   (implies (fn2-nntp-txp p)
            (equal (fn2-gram-put b 1 1 1 1 1 p)
                   (let ((used (fn2-pool-fill 1 p)))
                     (if (and (unsigned-byte-p 8 b) (< used 8192))
                         (list :ok (fn2-nntp-pool-at nil 0
                                     (update-nth used b (fn2-nntp-tx-data p)) (+ 1 used)))
                       (list :bounds p)))))
   :hints (("Goal" :use ((:instance fn2-nntp-emit-one (xs nil) (k 0)
                          (tx (fn2-nntp-tx-data p)) (used (fn2-pool-fill 1 p))))
            :in-theory (e/d (fn2-nntp-txp fn2-nntp-graft)
                            (fn2-nntp-emit-one fn2-gram-put fn2-pool-fill))))))

(local
 (defthm fn2-nntp-tx-put-preserves
   (implies (fn2-nntp-txp p)
            (fn2-nntp-txp (mv-nth 1 (fn2-gram-put b 1 1 1 1 1 p))))
   :hints (("Goal" :use ((:instance fn2-nntp-txp-of-view
                             (tx (update-nth (fn2-pool-fill 1 p) b (fn2-nntp-tx-data p)))
                             (used (+ 1 (fn2-pool-fill 1 p)))) (:instance fn2-nntp-txp (p p)))
            :in-theory (e/d (fn2-nntp-tx-put-rule) (fn2-gram-put fn2-pool-fill))))))

(local
 (defthm fn2-nntp-put-graft
   (implies (fn2-nntp-txp p)
            (let ((out (fn2-gram-put b 1 1 1 1 1 p)))
              (equal (fn2-gram-put b 1 1 1 1 1 (fn2-nntp-graft xs k p))
                     (list (mv-nth 0 out) (fn2-nntp-graft xs k (mv-nth 1 out))))))
   :hints (("Goal" :use ((:instance fn2-nntp-txp (p p)))
            :in-theory (e/d (fn2-nntp-graft fn2-nntp-tx-put-rule) (fn2-gram-put fn2-pool-fill))))))

(local (in-theory (disable fn2-gram-put fn2-gram-put-digits fn2-gram-put-number
                           fn2-gram-put-digits14 fn2-gram-put-template fn2-gram-put-crlf
                           fn2-nntp-render fn2-nntp-reply-admitted fn2-nntp-reply-command
                           fn2-nntp-reply-template fn2-gram-pow10 fn2-gram-next-power
                           fn2-gram-digit-byte)))

(local
 (defmacro fn2-nntp-tx-operation (fn args &key recursive)
   (let* ((call (cons fn (append args '(1 1 1 1 1 old))))
          (on-prefix (cons fn (append args '(1 1 1 1 1 (fn2-nntp-graft xs visible old))))))
     `(progn
        (defthm ,(fn2-gram-sym fn "-preserves-run-tx")
          (implies (fn2-nntp-txp old) (fn2-nntp-txp (mv-nth 1 ,call)))
          :hints (("Goal" ,@(and recursive `(:induct ,call)) :in-theory (enable ,fn))))
        (defthm ,(fn2-gram-sym fn "-on-run-tx")
          (implies (fn2-nntp-txp old)
                   (equal ,on-prefix (list (mv-nth 0 ,call)
                                           (fn2-nntp-graft xs visible (mv-nth 1 ,call)))))
          :hints (("Goal" ,@(and recursive `(:induct ,call)) :in-theory (enable ,fn))))))))

(local
 (defthm fn2-gram-put-empty-span
   (equal (fn2-gram-put-span 0 soff sslot sgen slot gen okind oslot ogen pool)
          (list :ok pool))
   :hints (("Goal" :expand ((fn2-gram-put-span 0 soff sslot sgen slot gen okind oslot ogen pool))))))

(local (fn2-nntp-tx-operation fn2-gram-put-digits (left n power) :recursive t))

(local (fn2-nntp-tx-operation fn2-gram-put-number (n)))

(local (fn2-nntp-tx-operation fn2-gram-put-digits14 (n)))

(local (fn2-nntp-tx-operation fn2-gram-put-crlf ()))

(local (fn2-nntp-tx-operation fn2-gram-put-template (i tmpl nidx n0 n1 n2 0 1 soff 0) :recursive t))

(local (fn2-nntp-tx-operation fn2-nntp-render (cmd reply mask n0 n1 n2 0 1 soff 0)))

(local
 (defthm fn2-nntp-parse-on-graft
   (implies (and (natp s) (natp e) (< s e) (natp k) (<= e k) (<= k 8192))
            (equal (fn2-nntp-parse-line s e mask 0 1 1 1 1 (fn2-nntp-graft xs k old))
                   (fn2-nntp-parse-line s e mask 0 1 1 1 1 (fn2-nntp-source xs))))
   :hints (("Goal" :in-theory (enable fn2-nntp-graft)))))

(local
 (defthm fn2-nntp-graft-fill
   (equal (fn2-gram-fill 0 (fn2-nntp-graft xs k old)) (nfix k))
   :hints (("Goal" :in-theory (enable fn2-nntp-graft)))))

(local
 (defthm fn2-nntp-feed-graft-byte
   (implies (and (natp k) (< k 8192) (unsigned-byte-p 8 (nth k xs)))
            (equal (fn2-gram-put (nth k xs) 0 1 1 1 1 (fn2-nntp-graft xs k old))
                   (list :ok (fn2-nntp-graft xs (+ 1 k) old))))
   :hints (("Goal" :in-theory (enable fn2-nntp-graft)))))

(local
 (defthm fn2-nntp-transcript-byte
   (implies (and (fn2-gram-octetsp xs) (natp i) (< i (len xs)))
            (unsigned-byte-p 8 (nth i xs)))
   :hints (("Goal" :induct (nth i xs) :in-theory (enable nth)))))

(local
 (defthm fn2-nntp-octets-true-list
   (implies (fn2-gram-octetsp xs) (true-listp xs))
   :rule-classes :forward-chaining))

(local
 (defun fn2-nntp-feed-induct (k start)
   (if (zp k) start (fn2-nntp-feed-induct (1- k) (+ 1 start)))))

(local
 (defthm fn2-nntp-transcript-byte-natp
   (implies (and (fn2-gram-octetsp xs) (natp i) (< i (len xs)))
            (natp (nth i xs)))
   :rule-classes :type-prescription
   :hints (("Goal" :use fn2-nntp-transcript-byte))))

(local
 (defthm fn2-nntp-next-suffix
   (implies (natp i)
            (equal (cdr (nthcdr i xs)) (nthcdr (+ 1 i) xs)))
   :hints (("Goal" :expand ((nthcdr (+ 1 i) xs))))))

(local
 (defthm fn2-nntp-feed-visible-prefix
   (implies (and (fn2-gram-octetsp xs) (<= (len xs) 8192)
                 (natp start) (<= start (len xs)) (natp k))
            (equal (fn2-nntp-feed k (nthcdr start xs) 0 1 (fn2-nntp-graft xs start old))
                   (let ((end (min (len xs) (+ start k))))
                     (list (nthcdr end xs) (fn2-nntp-graft xs end old)))))
   :hints (("Goal" :induct (fn2-nntp-feed-induct k start)
            :expand ((:free (a b) (fn2-nntp-feed 0 a 0 1 b)) (fn2-nntp-feed k (nthcdr start xs) 0 1 (fn2-nntp-graft xs start old)))
            :in-theory (disable fn2-nntp-feed
                                unsigned-byte-p nth nthcdr nthcdr-of-cdr open-small-nthcdr)))))

; A schedule changes the visible limit, while the next LF stays fixed.
(local
 (defun fn2-nntp-next-lf (pos xs)
   (declare (xargs :measure (nfix (- (len xs) (nfix pos)))))
   (if (or (not (natp pos)) (>= pos (len xs))) (len xs)
     (if (equal (nth pos xs) 10) pos
       (fn2-nntp-next-lf (+ 1 pos) xs)))))

(local
 (defthm fn2-nntp-next-lf-bounds
   (implies (and (natp pos) (<= pos (len xs)))
            (and (<= pos (fn2-nntp-next-lf pos xs))
                 (<= (fn2-nntp-next-lf pos xs) (len xs))))
   :rule-classes :linear))

(local
 (defthm fn2-nntp-next-lf-resume
   (implies (and (natp pos) (natp n) (<= pos n) (<= n (fn2-nntp-next-lf pos xs)))
            (equal (fn2-nntp-next-lf n xs) (fn2-nntp-next-lf pos xs)))
   :rule-classes nil
   :hints (("Goal" :induct (fn2-nntp-next-lf pos xs)))))

(local (in-theory (disable fn2-nntp-next-lf fn2-nntp-next-suffix)))

(local
 (defthm fn2-nntp-pool-lf-scan
   (implies (and (natp a) (natp i) (natp n) (<= i n)
                 (natp k) (<= (+ a n) k) (<= k (len xs)) (<= k 8192))
            (equal (fn2-pool-scan-loop a i n 10 (fn2-nntp-pool-at xs k tx used))
                   (min n (- (fn2-nntp-next-lf (+ a i) xs) a))))
   :hints (("Goal" :induct (fn2-pool-scan-loop a i n 10 (fn2-nntp-pool-at xs k tx used))
            :expand ((fn2-nntp-next-lf (+ a i) xs))
            :in-theory (e/d (fn2-pool-scan-loop) (fn2-pool-datai nth))))))

(local
 (defthm fn2-nntp-scan-visible
   (implies (and (natp pos) (natp k) (<= pos k) (<= k (len xs)) (<= k 8192))
            (equal (fn2-pool-scan 0 1 pos (- k pos) 10 1 1 1 (fn2-nntp-graft xs k old))
                   (list :ok (- (min k (fn2-nntp-next-lf pos xs)) pos))))
   :hints (("Goal" :in-theory (e/d (fn2-pool-scan fn2-pool-range-in fn2-nntp-graft)
                                   (fn2-pool-readable-code fn2-pool-data-length
                                    fn2-pool-fill fn2-pool-base fn2-pool-scan-loop))))))

(local
 (defun fn2-nntp-pending-frame (xs start pos overflow cap)
   (let ((lf (fn2-nntp-next-lf pos xs))
         (limit (+ (nfix start) (nfix cap) -1)))
     (cond ((equal overflow 1) (list :long-line (+ 1 lf) (+ 1 lf) 1))
           ((<= (nfix cap) (- (nfix pos) (nfix start)))
            (if (equal lf pos) (list :long-line (+ 1 pos) (+ 1 pos) 1)
              (list :overflow (+ 1 pos) (+ 1 pos) 1)))
           ((<= lf limit) (list :line start (+ 1 lf) overflow))
           (t (list :overflow (+ 1 limit) (+ 1 limit) 1))))))

(local
 (defthm fn2-nntp-frame-at-limit
   (implies (and (natp start) (natp pos) (<= start pos)
                 (natp k) (<= pos k) (<= k (len xs)) (< (len xs) 4096))
            (equal (fn2-gram-frame 4096 start pos overflow cap 0 1 1 1 1
                                   (fn2-nntp-graft xs k old))
                   (let ((frame (fn2-nntp-pending-frame xs start pos overflow cap)))
                     (if (<= (nth 2 frame) k) frame
                       (list :need-more (if (and (equal overflow 1) (< pos k)) k start)
                             k overflow)))))
   :hints (("Goal" :in-theory (e/d (fn2-gram-frame) (fn2-pool-scan fn2-gram-fill))))))

; Extract one transition from the generated driver. Its recursive calls
; become returned states so both chunk schedules can use the same transition.
(local
 (defun fn2-nntp-action-term (term)
   (cond ((atom term) term)
         ((eq (car term) 'quote) term)
         ((member-eq (car term) '(fn2-gram-frame fn2-gram-block-step)) 'item)
         ((eq (car term) 'fn2-nntp-parse-line)
          (append (butlast term 1) '(input)))
         ((eq (car term) 'fn2-nntp-drive)
          (list 'list (nth 2 term) (nth 3 term) (nth 4 term) (nth 5 term)
                (nth 8 term) 'fn2-pool))
         (t (cons (fn2-nntp-action-term (car term))
                  (fn2-nntp-action-term (cdr term)))))))

(local
 (make-event
  (let* ((body (car (last (get-event 'fn2-nntp-drive (w state)))))
         (step (fn2-nntp-action-term (fourth body))))
    (value
     `(defun-nx fn2-nntp-action (mode item mask events input old)
        ,(sublis '((slot . 0) (gen . 1) (tslot . 1) (tgen . 1)
                   (fault . nil) (fn2-pool . old)) step))))))

(local
 (make-event
  (let ((body (car (last (get-event 'fn2-gram-block-step (w state))))))
    (value
     `(defun-nx fn2-nntp-classify (frame input)
        (mv-let ,(cadr body) frame
          ,(sublis '((slot . 0) (gen . 1) (okind . 1) (oslot . 1) (ogen . 1)
                     (fn2-pool . input)) (fourth body))))))))

(local
 (defun fn2-nntp-mode-cap (mode)
   (if (or (consp mode) (eq mode :block)) *fn2-nntp-block-line-cap*
     *fn2-nntp-line-cap*)))

(local
 (defun-nx fn2-nntp-item (mode frame xs)
   (if (or (consp mode) (eq mode :block))
       (fn2-nntp-classify frame (fn2-nntp-source xs))
     frame)))

(local
 (defthm fn2-nntp-read-under-limit
   (implies (and (natp i) (natp k) (< i k) (<= k 8192))
            (equal (fn2-gram-read 0 1 i 1 1 1 (fn2-nntp-graft xs k old))
                   (fn2-gram-read 0 1 i 1 1 1 (fn2-nntp-source xs))))
   :hints (("Goal" :in-theory (enable fn2-nntp-graft)))))

(local
 (defthm fn2-nntp-block-scan-under-limit
   (implies (and (natp left) (natp i) (natp k) (<= (+ i left) k) (<= k 8192))
            (equal (fn2-gram-block-scan left i 0 1 1 1 1 (fn2-nntp-graft xs k old))
                   (fn2-gram-block-scan left i 0 1 1 1 1 (fn2-nntp-source xs))))
   :hints (("Goal" :in-theory (enable fn2-nntp-graft)))))

(local
 (defthm fn2-nntp-classify-visible
   (implies (and (natp k) (<= k 8192)
                 (or (not (equal (mv-nth 0 frame) :line))
                     (and (natp (mv-nth 1 frame)) (natp (mv-nth 2 frame))
                          (< (mv-nth 1 frame) (mv-nth 2 frame))
                          (<= (mv-nth 2 frame) k))))
            (equal (fn2-nntp-classify frame (fn2-nntp-graft xs k old))
                   (fn2-nntp-classify frame (fn2-nntp-source xs))))
   :hints (("Goal" :in-theory (e/d (fn2-nntp-classify) (fn2-nntp-read-source fn2-nntp-read-visible))))))

(local
 (defthm fn2-nntp-block-step-classifies
   (equal (fn2-gram-block-step 4096 start pos overflow cap 0 1 1 1 1 input)
          (fn2-nntp-classify (fn2-gram-frame 4096 start pos overflow cap 0 1 1 1 1 input)
                             input))
   :hints (("Goal" :in-theory (e/d (fn2-gram-block-step fn2-nntp-classify)
                                   (fn2-gram-frame))))))

(local
 (defthm fn2-nntp-classify-nonline
   (implies (not (equal (car frame) :line))
            (equal (fn2-nntp-classify frame input)
                   (list (mv-nth 0 frame) (mv-nth 1 frame) (mv-nth 2 frame)
                         (mv-nth 3 frame) 0 0)))
   :hints (("Goal" :in-theory (enable fn2-nntp-classify)))))

(local (in-theory (disable fn2-nntp-action fn2-nntp-classify fn2-nntp-pending-frame
                           fn2-nntp-item fn2-nntp-respond fn2-nntp-hand-off fn2-nntp-block-refusal
                           fn2-nntp-drive fn2-gram-frame fn2-gram-block-step)))

(local
 (defthm fn2-nntp-drive-stopped
   (equal (fn2-nntp-drive fuel :stopped start pos overflow mask fault events slot gen ts tg pool)
          (list :stopped start pos overflow events pool))
   :hints (("Goal" :expand ((fn2-nntp-drive fuel :stopped start pos overflow mask fault
                                            events slot gen ts tg pool))))))

(local
 (defun-nx fn2-nntp-actual-item (mode start pos overflow pool)
   (if (or (consp mode) (eq mode :block))
       (fn2-gram-block-step 4096 start pos overflow *fn2-nntp-block-line-cap* 0 1 1 1 1 pool)
     (fn2-gram-frame 4096 start pos overflow *fn2-nntp-line-cap* 0 1 1 1 1 pool))))

(local
 (defthmd fn2-nntp-drive-one-action
   (implies (and (posp fuel) (not (equal mode :stopped)))
            (equal (fn2-nntp-drive fuel mode start pos overflow mask nil events 0 1 1 1 pool)
                   (let* ((item (fn2-nntp-actual-item mode start pos overflow pool))
                          (a (fn2-nntp-action mode item mask events pool pool)))
                     (if (equal (mv-nth 0 item) :need-more) a
                       (fn2-nntp-drive (- fuel 1) (mv-nth 0 a) (mv-nth 1 a)
                                       (mv-nth 2 a) (mv-nth 3 a) mask nil (mv-nth 4 a)
                                       0 1 1 1 (mv-nth 5 a))))))
   :hints (("Goal" :expand ((fn2-nntp-drive fuel mode start pos overflow mask nil events 0 1 1 1 pool))
            :in-theory (union-theories (theory 'minimal-theory)
                         '(fn2-nntp-action fn2-nntp-actual-item fn2-nntp-drive-stopped
                           posp zp mv-nth member-equal fn2-gram-fault-code fn2-gram-fault-reply))))))

(local
 (defun-nx fn2-nntp-graft-result (xs k r)
   (list (mv-nth 0 r) (mv-nth 1 r) (mv-nth 2 r) (mv-nth 3 r) (mv-nth 4 r)
         (fn2-nntp-graft xs k (mv-nth 5 r)))))

(local
 (defthm fn2-nntp-action-on-graft
   (implies (and (fn2-nntp-txp old) (natp k) (<= k 8192)
                 (or (not (eq (mv-nth 0 item) :line))
                     (and (natp (mv-nth 1 item)) (natp (mv-nth 2 item))
                          (< (mv-nth 1 item) (mv-nth 2 item)) (<= (mv-nth 2 item) k))))
            (equal (fn2-nntp-action mode item mask events (fn2-nntp-graft xs k old)
                                    (fn2-nntp-graft xs k old))
                   (fn2-nntp-graft-result xs k
                     (fn2-nntp-action mode item mask events (fn2-nntp-source xs) old))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(member-equal fn2-nntp-action fn2-nntp-parse-on-graft fn2-nntp-render-on-run-tx
               fn2-nntp-graft-result mv-nth natp fn2-gram-fault-reply fn2-gram-fault-code))))))

(local
 (defthm fn2-nntp-action-bounds
   (let ((a (fn2-nntp-action mode item mask events input old)))
     (and (equal (mv-nth 2 a) (mv-nth 2 item))
          (implies (and (natp (mv-nth 1 item)) (natp (mv-nth 2 item)))
                   (natp (mv-nth 1 a)))
          (implies (<= (mv-nth 1 item) (mv-nth 2 item))
                   (<= (mv-nth 1 a) (mv-nth 2 item)))
          (implies (fn2-nntp-txp old) (fn2-nntp-txp (mv-nth 5 a)))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn2-nntp-action mv-nth natp fn2-nntp-render-preserves-run-tx))))))

(local
 (defthm fn2-nntp-action-needs-more
   (implies (eq (mv-nth 0 item) :need-more)
            (equal (fn2-nntp-action mode item mask events input old)
                   (list mode (mv-nth 1 item) (mv-nth 2 item) (mv-nth 3 item) events old)))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                             '(member-equal fn2-nntp-action mv-nth))))))

(local
 (defthm fn2-nntp-pending-bounds
   (let ((f (fn2-nntp-pending-frame xs start pos overflow cap)))
     (implies (and (natp start) (natp pos) (<= start pos) (<= pos (len xs)))
              (and (natp (mv-nth 1 f)) (natp (mv-nth 2 f))
                   (< pos (mv-nth 2 f)) (<= (mv-nth 1 f) (mv-nth 2 f))
                   (implies (eq (mv-nth 0 f) :line) (< (mv-nth 1 f) (mv-nth 2 f)))
                   (not (equal (mv-nth 0 f) :need-more)))))
   :hints (("Goal" :in-theory (enable fn2-nntp-pending-frame)))))

(local
 (defthm fn2-nntp-pending-end-index
   (equal (nth 2 (fn2-nntp-pending-frame xs s p o cap))
          (mv-nth 2 (fn2-nntp-pending-frame xs s p o cap)))
   :hints (("Goal" :in-theory (enable fn2-nntp-pending-frame)))))

(local
 (defthm fn2-nntp-pending-after-pause
   (implies (and (natp start) (natp pos) (<= start pos)
                 (natp k) (<= pos k) (<= k (len xs))
                 (< k (mv-nth 2 (fn2-nntp-pending-frame xs start pos overflow cap))))
            (equal (fn2-nntp-pending-frame
                    xs (if (and (equal overflow 1) (< pos k)) k start) k overflow cap)
                   (fn2-nntp-pending-frame xs start pos overflow cap)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-nntp-next-lf-resume (n k)))
            :in-theory (enable fn2-nntp-pending-frame)))))

(local
 (defthm fn2-nntp-classify-fields
   (let ((item (fn2-nntp-classify frame input)))
     (and (equal (mv-nth 1 item) (mv-nth 1 frame))
          (equal (mv-nth 2 item) (mv-nth 2 frame))
          (equal (mv-nth 3 item) (mv-nth 3 frame))
          (equal (equal (mv-nth 0 item) :need-more) (equal (mv-nth 0 frame) :need-more))
          (not (equal (mv-nth 0 item) :line))))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                             '(fn2-nntp-classify mv-nth))))))

(local
 (defthm fn2-nntp-item-fields
   (let ((item (fn2-nntp-item mode frame xs)))
     (and (equal (mv-nth 1 item) (mv-nth 1 frame))
          (equal (mv-nth 2 item) (mv-nth 2 frame))
          (equal (mv-nth 3 item) (mv-nth 3 frame))
          (equal (equal (mv-nth 0 item) :need-more) (equal (mv-nth 0 frame) :need-more))
          (implies (not (eq (mv-nth 0 frame) :line)) (not (eq (mv-nth 0 item) :line)))))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn2-nntp-item fn2-nntp-classify-fields))))))

(local
 (defun fn2-nntp-frame-valid (f)
   (and (natp (mv-nth 1 f)) (natp (mv-nth 2 f))
        (<= (mv-nth 1 f) (mv-nth 2 f))
        (or (not (eq (mv-nth 0 f) :line)) (< (mv-nth 1 f) (mv-nth 2 f)))
        (not (eq (mv-nth 0 f) :need-more)))))

(local
 (defthm fn2-nntp-pending-valid
   (implies (and (natp start) (natp pos) (<= start pos) (<= pos (len xs)))
            (fn2-nntp-frame-valid (fn2-nntp-pending-frame xs start pos overflow cap)))
   :hints (("Goal" :use fn2-nntp-pending-bounds
            :in-theory (union-theories (theory 'minimal-theory) '(fn2-nntp-frame-valid))))))

(local
 (defthm fn2-nntp-frame-item-valid
   (implies (fn2-nntp-frame-valid frame)
            (fn2-nntp-frame-valid (fn2-nntp-item mode frame xs)))
   :hints (("Goal" :use fn2-nntp-item-fields :in-theory (union-theories (theory 'minimal-theory)
                                '(fn2-nntp-frame-valid fn2-nntp-item-fields))))))

(local
 (defun-nx fn2-nntp-advance (mode frame mask events xs old)
   (fn2-nntp-action mode (fn2-nntp-item mode frame xs) mask events (fn2-nntp-source xs) old)))

(local
 (defthm fn2-nntp-advance-bounds
   (let ((a (fn2-nntp-advance mode frame mask events xs old)))
     (implies (and (fn2-nntp-frame-valid frame) (fn2-nntp-txp old))
              (and (natp (mv-nth 1 a)) (equal (mv-nth 2 a) (mv-nth 2 frame))
                   (<= (mv-nth 1 a) (mv-nth 2 frame)) (fn2-nntp-txp (mv-nth 5 a)))))
   :hints (("Goal" :use ((:instance fn2-nntp-action-bounds
                           (item (fn2-nntp-item mode frame xs)) (input (fn2-nntp-source xs)))
                         fn2-nntp-frame-item-valid)
            :in-theory (union-theories (theory 'minimal-theory)
                      '(fn2-nntp-advance fn2-nntp-frame-valid fn2-nntp-item-fields))))))

(local (in-theory (disable fn2-nntp-advance fn2-nntp-frame-valid)))

(local
 (defun fn2-nntp-wait-frame (start pos overflow k)
   (list :need-more (if (and (equal overflow 1) (< pos k)) k start) k overflow)))

(local
 (defun fn2-nntp-window-ok (xs k start pos)
   (and (natp start) (natp pos) (<= start pos) (natp k) (<= pos k)
        (<= k (len xs)) (< (len xs) 4096))))

(local
 (defthm fn2-nntp-actual-item-visible
   (implies (fn2-nntp-window-ok xs k start pos)
            (equal (fn2-nntp-actual-item mode start pos overflow (fn2-nntp-graft xs k old))
                   (let ((f (fn2-nntp-pending-frame xs start pos overflow (fn2-nntp-mode-cap mode))))
                     (fn2-nntp-item mode (if (<= (mv-nth 2 f) k) f
                                           (fn2-nntp-wait-frame start pos overflow k)) xs))))
   :hints (("Goal" :in-theory
            (e/d (fn2-nntp-actual-item fn2-nntp-item fn2-nntp-mode-cap)
                 (fn2-gram-frame fn2-gram-block-step fn2-nntp-classify-nonline
                  (:definition mv-nth)))))))

(local
 (defthm fn2-nntp-item-advance-on-graft
   (implies (and (fn2-nntp-frame-valid frame) (natp k) (<= k 8192)
                 (<= (mv-nth 2 frame) k) (fn2-nntp-txp old))
            (let ((item (fn2-nntp-item mode frame xs)))
              (equal (fn2-nntp-action mode item mask events (fn2-nntp-graft xs k old)
                                      (fn2-nntp-graft xs k old))
                     (fn2-nntp-graft-result xs k (fn2-nntp-advance mode frame mask events xs old)))))
   :hints (("Goal" :use (fn2-nntp-frame-item-valid
                         (:instance fn2-nntp-action-on-graft (item (fn2-nntp-item mode frame xs))))
            :in-theory (union-theories (theory 'minimal-theory)
                        '(fn2-nntp-frame-valid fn2-nntp-item-fields fn2-nntp-advance))))))

(local
 (defthm fn2-nntp-item-wait
   (let* ((f (fn2-nntp-wait-frame start pos overflow k))
          (item (fn2-nntp-item mode f xs)))
     (and (equal (mv-nth 0 item) :need-more)
          (equal (fn2-nntp-action mode item mask events input old)
                 (list mode (mv-nth 1 f) k overflow events old))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn2-nntp-item fn2-nntp-classify fn2-nntp-action-needs-more
               fn2-nntp-wait-frame mv-nth))))))

(local
 (defmacro fn2-nntp-with-cursor (q &rest body)
   `(let ((mode (mv-nth 0 ,q)) (start (mv-nth 1 ,q)) (pos (mv-nth 2 ,q))
          (overflow (mv-nth 3 ,q)) (events (mv-nth 4 ,q)) (old (mv-nth 5 ,q)))
      (declare (ignorable mode start pos overflow events old))
      ,@body)))

(local
 (defmacro fn2-nntp-next-frame (xs q)
   `(fn2-nntp-with-cursor ,q
       (fn2-nntp-pending-frame ,xs start pos overflow (fn2-nntp-mode-cap mode)))))

(local
 (defmacro fn2-nntp-step-cursor (xs q frame mask)
   `(fn2-nntp-with-cursor ,q (fn2-nntp-advance mode ,frame ,mask events ,xs old))))

(local
 (defmacro fn2-nntp-paused-cursor (q k)
   `(fn2-nntp-with-cursor ,q
       (list mode (mv-nth 1 (fn2-nntp-wait-frame start pos overflow ,k))
             ,k overflow events old))))

(local
 (defmacro fn2-nntp-drive-cursor (fuel xs k q mask)
   `(fn2-nntp-with-cursor ,q
       (fn2-nntp-drive ,fuel mode start pos overflow ,mask nil events 0 1 1 1
                       (fn2-nntp-graft ,xs ,k old)))))

(local
 (defmacro fn2-nntp-cursor-ok (xs k q)
   `(fn2-nntp-with-cursor ,q (and (fn2-nntp-window-ok ,xs ,k start pos) (fn2-nntp-txp old)))))

(local
 (defun-nx fn2-nntp-drive-prefix (fuel xs k q mask)
   (declare (xargs :measure (nfix fuel)))
   (if (or (zp fuel) (eq (mv-nth 0 q) :stopped)) q
     (let ((f (fn2-nntp-next-frame xs q)))
       (if (< k (mv-nth 2 f)) (fn2-nntp-paused-cursor q k)
         (fn2-nntp-drive-prefix (- fuel 1) xs k (fn2-nntp-step-cursor xs q f mask) mask))))))

(local
 (defthm fn2-nntp-step-cursor-ok
   (let* ((f (fn2-nntp-next-frame xs q)) (a (fn2-nntp-step-cursor xs q f mask)))
     (implies (and (fn2-nntp-cursor-ok xs k q) (<= (mv-nth 2 f) k))
              (and (fn2-nntp-cursor-ok xs k a)
                   (< (mv-nth 2 q) (mv-nth 2 a)))))
   :hints (("Goal" :use ((:instance fn2-nntp-pending-bounds (start (mv-nth 1 q)) (pos (mv-nth 2 q))
                        (overflow (mv-nth 3 q)) (cap (fn2-nntp-mode-cap (mv-nth 0 q))))) :in-theory (disable fn2-nntp-mode-cap mv-nth)))))

(local
 (defthm fn2-nntp-project-cons
   (equal (mv-nth n (cons a b)) (if (zp n) a (mv-nth (1- n) b)))
   :hints (("Goal" :expand ((mv-nth n (cons a b)))))))

(local
 (defthm fn2-nntp-drive-no-fuel
   (implies (zp fuel)
            (equal (fn2-nntp-drive fuel mode start pos overflow mask fault events slot gen ts tg pool)
                   (list mode start pos overflow events pool)))
   :hints (("Goal" :expand ((fn2-nntp-drive fuel mode start pos overflow mask fault
                                            events slot gen ts tg pool))))))

(local
 (defthmd fn2-nntp-drive-window-unfolds
   (implies (fn2-nntp-cursor-ok xs k q)
            (equal (fn2-nntp-drive-cursor fuel xs k q mask)
                   (let ((f (fn2-nntp-next-frame xs q)))
                     (cond ((or (zp fuel) (eq (mv-nth 0 q) :stopped))
                            (fn2-nntp-graft-result xs k q))
                           ((< k (mv-nth 2 f))
                            (fn2-nntp-graft-result xs k (fn2-nntp-paused-cursor q k)))
                           (t (fn2-nntp-drive-cursor
                               (- fuel 1) xs k (fn2-nntp-step-cursor xs q f mask) mask))))))
   :hints (("Goal"
            :cases ((zp fuel) (equal (mv-nth 0 q) :stopped))
            :use ((:instance fn2-nntp-drive-one-action
              (mode (mv-nth 0 q)) (start (mv-nth 1 q)) (pos (mv-nth 2 q))
              (overflow (mv-nth 3 q)) (events (mv-nth 4 q))
              (pool (fn2-nntp-graft xs k (mv-nth 5 q)))))
            :in-theory (disable fn2-nntp-actual-item fn2-nntp-mode-cap fn2-nntp-item
                                fn2-nntp-wait-frame fn2-nntp-action fn2-nntp-advance
                                fn2-nntp-pending-frame fn2-nntp-drive mv-nth)))))

(local
 (defthm fn2-nntp-drive-prefix-refines
   (implies (fn2-nntp-cursor-ok xs k q)
            (equal (fn2-nntp-drive-cursor fuel xs k q mask)
                   (fn2-nntp-graft-result xs k (fn2-nntp-drive-prefix fuel xs k q mask))))
   :rule-classes nil
   :hints (("Goal" :induct (fn2-nntp-drive-prefix fuel xs k q mask)
            :in-theory (disable fn2-nntp-actual-item fn2-nntp-mode-cap fn2-nntp-wait-frame
                                fn2-nntp-graft-result fn2-nntp-window-ok mv-nth))
           ("Subgoal *1/3" :use (fn2-nntp-drive-window-unfolds fn2-nntp-step-cursor-ok))
           ("Subgoal *1/2" :use fn2-nntp-drive-window-unfolds)
           ("Subgoal *1/1" :use fn2-nntp-drive-window-unfolds))))

; Complete the pending frame against the full transcript. Each recursive
; call advances its end, including the overflow notification within a block.
(local
 (defun-nx fn2-nntp-finish-frame (xs mode frame mask events old)
   (declare (xargs :measure (nfix (- (+ 1 (len xs)) (nfix (mv-nth 2 frame))))))
   (let ((end (mv-nth 2 frame)))
     (if (or (eq mode :stopped) (not (natp end)) (< (len xs) end))
         (list mode events (fn2-nntp-graft xs (len xs) old))
       (let* ((a (fn2-nntp-advance mode frame mask events xs old))
              (next (fn2-nntp-next-frame xs a)))
         (if (and (natp (mv-nth 2 next)) (< end (mv-nth 2 next)))
             (fn2-nntp-finish-frame xs (mv-nth 0 a) next mask (mv-nth 4 a) (mv-nth 5 a))
           (list mode events (fn2-nntp-graft xs (len xs) old))))))))

(local
 (defmacro fn2-nntp-complete-cursor (xs q mask)
   `(fn2-nntp-with-cursor ,q
       (fn2-nntp-finish-frame ,xs mode (fn2-nntp-next-frame ,xs ,q) ,mask events old))))

(local
 (defthm fn2-nntp-finish-consumes
   (let ((f (fn2-nntp-next-frame xs q)))
     (implies (and (fn2-nntp-cursor-ok xs k q) (<= (mv-nth 2 f) k)
                   (not (equal (mv-nth 0 q) :stopped)))
              (equal (fn2-nntp-complete-cursor xs q mask)
                     (fn2-nntp-complete-cursor xs (fn2-nntp-step-cursor xs q f mask) mask))))
   :rule-classes nil
   :hints (("Goal" :use (fn2-nntp-step-cursor-ok (:instance fn2-nntp-pending-bounds (start (mv-nth 1 q)) (pos (mv-nth 2 q))
                        (overflow (mv-nth 3 q)) (cap (fn2-nntp-mode-cap (mv-nth 0 q))))
                     (:instance fn2-nntp-pending-bounds
                      (start (mv-nth 1 (fn2-nntp-step-cursor xs q (fn2-nntp-next-frame xs q) mask)))
                      (pos (mv-nth 2 (fn2-nntp-step-cursor xs q (fn2-nntp-next-frame xs q) mask)))
                      (overflow (mv-nth 3 (fn2-nntp-step-cursor xs q (fn2-nntp-next-frame xs q) mask)))
                      (cap (fn2-nntp-mode-cap
                            (mv-nth 0 (fn2-nntp-step-cursor xs q (fn2-nntp-next-frame xs q) mask))))))
            :expand ((:free (f) (fn2-nntp-finish-frame xs (mv-nth 0 q) f mask (mv-nth 4 q) (mv-nth 5 q))))
            :in-theory (disable fn2-nntp-finish-frame fn2-nntp-mode-cap mv-nth)))))

(local
 (defthm fn2-nntp-finish-pauses
   (implies (and (fn2-nntp-cursor-ok xs k q) (< k (mv-nth 2 (fn2-nntp-next-frame xs q))))
            (equal (fn2-nntp-complete-cursor xs (fn2-nntp-paused-cursor q k) mask)
                   (fn2-nntp-complete-cursor xs q mask)))
   :hints (("Goal" :use ((:instance fn2-nntp-pending-after-pause
                         (start (mv-nth 1 q)) (pos (mv-nth 2 q)) (overflow (mv-nth 3 q))
                         (cap (fn2-nntp-mode-cap (mv-nth 0 q)))))
            :in-theory (disable fn2-nntp-finish-frame fn2-nntp-mode-cap mv-nth)))))

(local
 (defthm fn2-nntp-remaining-fuel
   (implies (and (integerp pos) (integerp next) (< pos next)
                 (integerp fuel) (< (- k pos) fuel))
            (< (- k next) (+ -1 fuel)))
   :rule-classes nil
   :hints (("Goal" :cases ((<= (+ 1 pos) next))))))

(local
 (defthm fn2-nntp-prefix-keeps-completion
   (implies (fn2-nntp-cursor-ok xs k q)
            (equal (fn2-nntp-complete-cursor xs (fn2-nntp-drive-prefix fuel xs k q mask) mask)
                   (fn2-nntp-complete-cursor xs q mask)))
   :hints (("Goal" :induct (fn2-nntp-drive-prefix fuel xs k q mask)
            :in-theory (disable fn2-nntp-finish-frame fn2-nntp-mode-cap fn2-nntp-window-ok
                                fn2-nntp-wait-frame mv-nth))
           ("Subgoal *1/2" :use fn2-nntp-finish-pauses)
           ("Subgoal *1/3" :use (fn2-nntp-finish-consumes fn2-nntp-step-cursor-ok)))))

(local
 (defun fn2-nntp-enough-fuel (q k fuel)
   (or (equal (mv-nth 0 q) :stopped)
       (and (natp fuel) (< (- k (mv-nth 2 q)) fuel)))))

(local
 (defthm fn2-nntp-step-has-fuel
   (let* ((f (fn2-nntp-next-frame xs q)) (a (fn2-nntp-step-cursor xs q f mask)))
     (implies (and (fn2-nntp-cursor-ok xs k q) (<= (mv-nth 2 f) k)
                   (not (eq (mv-nth 0 q) :stopped)) (not (zp fuel))
                   (fn2-nntp-enough-fuel q k fuel))
              (fn2-nntp-enough-fuel a k (+ -1 fuel))))
   :hints (("Goal" :use ((:instance fn2-nntp-pending-bounds (start (mv-nth 1 q)) (pos (mv-nth 2 q))
                        (overflow (mv-nth 3 q)) (cap (fn2-nntp-mode-cap (mv-nth 0 q))))
                        (:instance fn2-nntp-remaining-fuel
                         (pos (mv-nth 2 q)) (next (mv-nth 2 (fn2-nntp-next-frame xs q)))))
            :in-theory (disable fn2-nntp-mode-cap mv-nth)))))

(local
 (defthm fn2-nntp-paused-is-drained
   (implies (fn2-nntp-cursor-ok xs k q)
            (and (fn2-nntp-cursor-ok xs k (fn2-nntp-paused-cursor q k))
                 (equal (mv-nth 2 (fn2-nntp-paused-cursor q k)) k)))
   :hints (("Goal" :in-theory (disable mv-nth)))))

(local
 (defthm fn2-nntp-drained-at-zero
   (implies (and (fn2-nntp-cursor-ok xs k q) (fn2-nntp-enough-fuel q k fuel)
                 (zp fuel))
            (equal (mv-nth 0 q) :stopped))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable mv-nth)))))

(local
 (defthm fn2-nntp-prefix-drains
   (let ((r (fn2-nntp-drive-prefix fuel xs k q mask)))
     (implies (and (fn2-nntp-cursor-ok xs k q) (fn2-nntp-enough-fuel q k fuel))
              (and (fn2-nntp-cursor-ok xs k r)
                   (or (eq (mv-nth 0 r) :stopped) (equal (mv-nth 2 r) k)))))
   :rule-classes nil
   :hints (("Goal" :induct (fn2-nntp-drive-prefix fuel xs k q mask)
            :in-theory (union-theories (theory 'minimal-theory)
                        '(fn2-nntp-drive-prefix (:induction fn2-nntp-drive-prefix))))
           ("Subgoal *1/3" :use (fn2-nntp-step-cursor-ok fn2-nntp-step-has-fuel))
           ("Subgoal *1/2" :use fn2-nntp-paused-is-drained)
           ("Subgoal *1/1" :use fn2-nntp-drained-at-zero))))

; At each nonterminal chunk boundary the cursor has reached the visible fill.
; The actual driver's fuel suffices because every completed frame advances it.
(local
 (defun fn2-nntp-ready-cursor (xs k q)
   (and (fn2-nntp-cursor-ok xs k q)
        (or (equal (mv-nth 0 q) :stopped) (equal (mv-nth 2 q) k)))))

(local
 (defun fn2-nntp-cut (sizes xs k)
   (if (and (consp sizes) (posp (car sizes))) (min (len xs) (+ k (car sizes))) (len xs))))

(local
 (defun fn2-nntp-budget (xs k) (+ 8 (* 4 (- (len xs) k)))))

(local
 (defmacro fn2-nntp-after-chunk (sizes xs k q mask)
   `(fn2-nntp-drive-prefix (fn2-nntp-budget ,xs ,k) ,xs (fn2-nntp-cut ,sizes ,xs ,k) ,q ,mask)))

(local
 (defmacro fn2-nntp-chunks-from (sizes xs k q mask)
   `(fn2-nntp-with-cursor ,q
       (fn2-nntp-chunks ,sizes (nthcdr ,k ,xs) mode start pos overflow ,mask nil events
                        0 1 1 1 (fn2-nntp-graft ,xs ,k old)))))

(local
 (defthm fn2-nntp-cut-progress
   (implies (and (natp k) (< k (len xs)))
            (and (natp (fn2-nntp-cut sizes xs k)) (< k (fn2-nntp-cut sizes xs k))
                 (<= (fn2-nntp-cut sizes xs k) (len xs))))
   :rule-classes nil))

(local
 (defun-nx fn2-nntp-schedule-induct (sizes xs k q mask)
   (declare (xargs :measure (nfix (- (len xs) (nfix k)))
                   :hints (("Goal" :use fn2-nntp-cut-progress))))
   (if (or (not (natp k)) (>= k (len xs))) q
     (fn2-nntp-schedule-induct (cdr sizes) xs (fn2-nntp-cut sizes xs k)
                                (fn2-nntp-after-chunk sizes xs k q mask) mask))))

(local
 (defthm fn2-nntp-cut-window
   (implies (and (fn2-nntp-ready-cursor xs k q) (< k (len xs)))
            (let ((cut (fn2-nntp-cut sizes xs k)))
              (and (fn2-nntp-cursor-ok xs cut q)
                   (fn2-nntp-enough-fuel q cut (fn2-nntp-budget xs k)))))
   :hints (("Goal" :use fn2-nntp-cut-progress :in-theory (disable fn2-nntp-cut mv-nth)))))

(local
 (defthm fn2-nntp-cut-ready
   (implies (and (fn2-nntp-ready-cursor xs k q) (< k (len xs)))
            (fn2-nntp-ready-cursor xs (fn2-nntp-cut sizes xs k)
                                   (fn2-nntp-after-chunk sizes xs k q mask)))
   :hints (("Goal" :use (fn2-nntp-cut-window
                         (:instance fn2-nntp-prefix-drains (k (fn2-nntp-cut sizes xs k))
                                    (fuel (fn2-nntp-budget xs k))))
            :in-theory (union-theories (theory 'minimal-theory) '(fn2-nntp-ready-cursor))))))

(local
 (defthm fn2-nntp-completion-at-end
   (implies (and (fn2-nntp-ready-cursor xs k q) (equal k (len xs)))
            (equal (fn2-nntp-complete-cursor xs q mask)
                   (list (mv-nth 0 q) (mv-nth 4 q) (fn2-nntp-graft xs k (mv-nth 5 q)))))
   :hints (("Goal" :use ((:instance fn2-nntp-pending-bounds (start (mv-nth 1 q)) (pos (mv-nth 2 q))
                        (overflow (mv-nth 3 q)) (cap (fn2-nntp-mode-cap (mv-nth 0 q)))))
            :expand ((:free (f m) (fn2-nntp-finish-frame xs m f mask
                                                       (mv-nth 4 q) (mv-nth 5 q))))
            :in-theory (disable fn2-nntp-finish-frame fn2-nntp-mode-cap mv-nth)))))

(local
 (defthm fn2-nntp-feed-for-cut
   (implies (and (fn2-gram-octetsp xs) (natp k) (< k (len xs)) (< (len xs) 4096))
            (equal (fn2-nntp-feed (if (and (consp sizes) (posp (car sizes)))
                                      (car sizes) (len (nthcdr k xs)))
                                  (nthcdr k xs) 0 1 (fn2-nntp-graft xs k old))
                   (let ((end (fn2-nntp-cut sizes xs k)))
                     (list (nthcdr end xs) (fn2-nntp-graft xs end old)))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-nntp-feed-visible-prefix
                           (start k) (k (if (and (consp sizes) (posp (car sizes)))
                                           (car sizes) (len (nthcdr k xs))))))
            :in-theory (disable fn2-nntp-feed fn2-nntp-feed-visible-prefix nthcdr)))))

(local
 (defthmd fn2-nntp-chunks-open
   (equal (fn2-nntp-chunks sizes bytes mode start pos overflow mask nil events 0 1 1 1 pool)
          (if (atom bytes) (list mode events pool)
            (let* ((feed (fn2-nntp-feed (if (and (consp sizes) (posp (car sizes)))
                                             (car sizes) (len bytes))
                                         bytes 0 1 pool))
                   (rest (mv-nth 0 feed))
                   (d (fn2-nntp-drive (+ 8 (* 4 (len bytes))) mode start pos overflow
                                      mask nil events 0 1 1 1 (mv-nth 1 feed))))
              (if (>= (len rest) (len bytes))
                  (list (mv-nth 0 d) (mv-nth 4 d) (mv-nth 5 d))
                (fn2-nntp-chunks (if (consp sizes) (cdr sizes) nil) rest
                                 (mv-nth 0 d) (mv-nth 1 d) (mv-nth 2 d) (mv-nth 3 d)
                                 mask nil (mv-nth 4 d) 0 1 1 1 (mv-nth 5 d))))))
   :hints (("Goal" :expand ((fn2-nntp-chunks sizes bytes mode start pos overflow mask nil
                                             events 0 1 1 1 pool))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm fn2-nntp-cut-suffix-facts
   (implies (and (fn2-nntp-ready-cursor xs k q) (< k (len xs)))
            (and (natp k) (< (len xs) 4096) (consp (nthcdr k xs))
                 (< (len (nthcdr (fn2-nntp-cut sizes xs k) xs)) (len (nthcdr k xs)))
                 (equal (+ 8 (* 4 (len (nthcdr k xs)))) (fn2-nntp-budget xs k))))
   :rule-classes nil
   :hints (("Goal" :use fn2-nntp-cut-progress
            :in-theory (disable fn2-nntp-cut fn2-nntp-next-lf-bounds mv-nth nthcdr)))))

(local
 (defthm fn2-nntp-sizes-tail
   (equal (if (consp sizes) (cdr sizes) nil) (cdr sizes))))

(local
 (defthm fn2-nntp-chunk-transition
   (implies (and (fn2-gram-octetsp xs) (fn2-nntp-ready-cursor xs k q) (< k (len xs)))
            (equal (fn2-nntp-chunks-from sizes xs k q mask)
                   (fn2-nntp-chunks-from (cdr sizes) xs (fn2-nntp-cut sizes xs k)
                                         (fn2-nntp-after-chunk sizes xs k q mask) mask)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-nntp-chunks-open
                           (bytes (nthcdr k xs)) (mode (mv-nth 0 q)) (start (mv-nth 1 q))
                           (pos (mv-nth 2 q)) (overflow (mv-nth 3 q)) (events (mv-nth 4 q))
                           (pool (fn2-nntp-graft xs k (mv-nth 5 q))))
                         fn2-nntp-cut-suffix-facts fn2-nntp-cut-window
                         (:instance fn2-nntp-feed-for-cut (old (mv-nth 5 q)))
                         (:instance fn2-nntp-drive-prefix-refines
                          (fuel (fn2-nntp-budget xs k)) (k (fn2-nntp-cut sizes xs k))))
            :in-theory (disable fn2-nntp-chunks fn2-nntp-feed fn2-nntp-drive-prefix
                                fn2-nntp-ready-cursor fn2-nntp-window-ok fn2-nntp-enough-fuel
                                fn2-nntp-drive-stopped fn2-nntp-next-lf-bounds
                                len-of-nthcdr consp-of-nthcdr fn2-nntp-budget posp nfix fn2-nntp-cut nthcdr mv-nth fn2-nntp-feed-visible-prefix)))))

(local
 (defthm fn2-nntp-empty-suffix
   (implies (and (true-listp xs) (natp k) (<= (len xs) k))
            (equal (nthcdr k xs) nil))
   :hints (("Goal" :cases ((consp (nthcdr k xs))) :in-theory (disable nthcdr fn2-nntp-next-lf-bounds)))))

(local
 (defthm fn2-nntp-chunks-empty
   (equal (fn2-nntp-chunks sizes nil mode start pos overflow mask nil events 0 1 1 1 pool)
          (list mode events pool))
   :hints (("Goal" :expand ((fn2-nntp-chunks sizes nil mode start pos overflow mask nil
                                            events 0 1 1 1 pool))))))

(local
 (defthm fn2-nntp-chunks-at-end
   (implies (and (fn2-gram-octetsp xs) (fn2-nntp-ready-cursor xs k q)
                 (or (not (natp k)) (<= (len xs) k)))
            (equal (fn2-nntp-chunks-from sizes xs k q mask) (fn2-nntp-complete-cursor xs q mask)))
   :rule-classes nil
   :hints (("Goal" :use fn2-nntp-completion-at-end
            :in-theory (disable fn2-nntp-finish-frame fn2-nntp-mode-cap mv-nth nthcdr
                                fn2-nntp-chunks)))))

(local
 (defthm fn2-nntp-cut-keeps-completion
   (implies (and (fn2-nntp-ready-cursor xs k q) (< k (len xs)))
            (equal (fn2-nntp-complete-cursor xs (fn2-nntp-after-chunk sizes xs k q mask) mask)
                   (fn2-nntp-complete-cursor xs q mask)))
   :hints (("Goal" :use (fn2-nntp-cut-window
                         (:instance fn2-nntp-prefix-keeps-completion
                          (fuel (fn2-nntp-budget xs k)) (k (fn2-nntp-cut sizes xs k))))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm fn2-nntp-chunks-complete
   (implies (and (fn2-gram-octetsp xs) (fn2-nntp-ready-cursor xs k q))
            (equal (fn2-nntp-chunks-from sizes xs k q mask) (fn2-nntp-complete-cursor xs q mask)))
   :rule-classes nil
   :hints (("Goal" :induct (fn2-nntp-schedule-induct sizes xs k q mask)
            :in-theory (union-theories (theory 'minimal-theory)
                                       '((:induction fn2-nntp-schedule-induct))))
           ("Subgoal *1/2" :use (fn2-nntp-chunk-transition fn2-nntp-cut-keeps-completion
                                 fn2-nntp-cut-ready))
           ("Subgoal *1/1" :use fn2-nntp-chunks-at-end))))

(local
 (defthm fn2-nntp-empty-rx-array
   (equal (fn2-nntp-rx-array xs 0) (fn2-nntp-rx-array nil 0))
   :hints (("Goal" :in-theory (enable fn2-nntp-rx-array)))))

(local
 (defthm fn2-nntp-empty-graft
   (equal (fn2-nntp-graft xs 0 p) (fn2-nntp-graft nil 0 p))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                    '(fn2-nntp-graft fn2-nntp-pool-at fn2-nntp-empty-rx-array (:e fn2-nntp-rx-array)))))))

(local
 (defthm fn2-nntp-pool-initial-tx
   (fn2-nntp-txp (fn2-nntp-run-pool))
   :hints (("Goal" :in-theory
            (union-theories
             (theory 'minimal-theory)
             '(fn2-nntp-txp fn2-nntp-graft fn2-nntp-pool-at fn2-nntp-run-pool
               fn2-nntp-tx-data create-fn2-pool (:e fn2-nntp-rx-array) (:e make-list-ac)
               (:e append) (:e nth) (:e nthcdr) (:e update-nth) (:e len) (:e natp)
               (:e fn2-pool-fill) (:e fn2-pool-init) (:e fn2-pool-reserve)
               (:e cons) (:e mv-nth)))))))

(local
 (defthm fn2-nntp-graft-initial-pool
   (equal (fn2-nntp-graft xs 0 (fn2-nntp-run-pool)) (fn2-nntp-run-pool))
   :hints (("Goal" :use ((:instance fn2-nntp-empty-graft (p (fn2-nntp-run-pool))) fn2-nntp-pool-initial-tx
                         (:instance fn2-nntp-txp (p (fn2-nntp-run-pool))))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm fn2-nntp-initial-chunks-agree
   (implies (and (fn2-gram-octetsp xs) (< (len xs) 4096))
            (equal (fn2-nntp-chunks sizes xs :command 0 0 0 mask nil nil 0 1 1 1 (fn2-nntp-run-pool))
                   (fn2-nntp-chunks nil xs :command 0 0 0 mask nil nil 0 1 1 1 (fn2-nntp-run-pool))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-nntp-chunks-complete (k 0)
                           (q (list :command 0 0 0 nil (fn2-nntp-run-pool))))
                         (:instance fn2-nntp-chunks-complete (k 0) (sizes nil)
                           (q (list :command 0 0 0 nil (fn2-nntp-run-pool)))))
            :in-theory (union-theories (theory 'minimal-theory)
                        '(fn2-nntp-ready-cursor fn2-nntp-window-ok fn2-nntp-project-cons
                          fn2-nntp-graft-initial-pool fn2-nntp-pool-initial-tx
                          nthcdr-when-zp (:e natp) (:e nfix) (:e zp) (:e <) (:e equal)
                          (:type-prescription len)))))))

(local
 (defmacro fn2-nntp-rx-reservation ()
   '(fn2-pool-reserve 0 1 1 1 (fn2-pool-init '((2 . 8192)) 1 1000 (create-fn2-pool)))))

(local
 (defmacro fn2-nntp-tx-reservation ()
   '(fn2-pool-reserve 0 1 1 1 (mv-nth 3 (fn2-nntp-rx-reservation)))))

(local
 (defthm fn2-nntp-run-reservations
   (and (equal (mv-nth 1 (fn2-nntp-rx-reservation)) 0)
        (equal (mv-nth 2 (fn2-nntp-rx-reservation)) 1)
        (equal (mv-nth 1 (fn2-nntp-tx-reservation)) 1)
        (equal (mv-nth 2 (fn2-nntp-tx-reservation)) 1)
        (equal (mv-nth 3 (fn2-nntp-tx-reservation)) (fn2-nntp-run-pool)))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                         '(fn2-nntp-run-pool create-fn2-pool (:e make-list-ac) (:e cons)
                           (:e fn2-pool-init) (:e fn2-pool-reserve) (:e mv-nth)))))))

(defthm fn2-nntp-fragmentation-proved
  (fn2-nntp-fragmentation$owed octets sizes mask)
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn2-nntp-initial-chunks-agree (xs octets)))
           :in-theory (union-theories (theory 'minimal-theory)
                       '(fn2-nntp-fragmentation$owed fn2-nntp-run fn2-nntp-run-fault
                         fn2-nntp-run-reservations fn2-nntp-project-cons)))))

(fn2-owed-discharge fn2-nntp-fragmentation fn2-nntp-fragmentation-proved)
