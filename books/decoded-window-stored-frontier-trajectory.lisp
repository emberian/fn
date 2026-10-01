; Repeated ACTUAL stored decoder calls and their returned global budget carry.
; Logical source observer only; actual returned state/ring/table/scratch retained.
(in-package "ACL2")
(include-book "decoded-window-interleaved-frontier-trajectory")

(local (include-book "arithmetic-5/top" :dir :system))

(local
 (defthm fn-pwsf-update-octet-retains-length
  (implies (and (natp i) (< i (len x)))
   (equal (len (fn-oct-update i o x)) (len x)))
  :hints (("Goal" :induct (fn-oct-update i o x) :in-theory (enable fn-oct-update)))))

(local
 (defthm fn-pwsf-table-length-word-write
  (implies (and (natp e) (< e *fn-zin-tab-entries*)
                (equal (len fn-zin-tab) *fn-zin-tab-octets*))
   (equal (len (fn-zin-tput e v fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :in-theory (e/d (fn-zin-tput) (fn-oct-update))))))

(local
 (defthm fn-pwsf-code-length-bounds-unconditional
  (and (natp (fn-zin-len-of e fn-zin-tab)) (<= (fn-zin-len-of e fn-zin-tab) 15))
  :rule-classes ((:rewrite) (:type-prescription :corollary (natp (fn-zin-len-of e fn-zin-tab))) (:linear :corollary (<= (fn-zin-len-of e fn-zin-tab) 15)))
  :hints (("Goal" :in-theory (enable fn-zin-len-of)))))

(local
 (defthm fn-pwsf-zero-counts-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-zero-counts k cb fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :induct (fn-zin-zero-counts k cb fn-zin-tab)
           :in-theory (e/d (fn-zin-zero-counts) (fn-zin-tput fn-oct-update fn-zin-len-of))))))

(local
 (defthm fn-pwsf-count-lens-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-count-lens s n lb cb fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :induct (fn-zin-count-lens s n lb cb fn-zin-tab)
           :in-theory (e/d (fn-zin-count-lens) (fn-zin-tput fn-oct-update fn-zin-len-of))))))

(local
 (defthm fn-pwsf-offsets-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-offsets len off cb fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :induct (fn-zin-offsets len off cb fn-zin-tab)
           :in-theory (e/d (fn-zin-offsets) (fn-zin-tput fn-oct-update fn-zin-len-of))))))

(local
 (defthm fn-pwsf-place-syms-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-place-syms s n lb sb smax fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :induct (fn-zin-place-syms s n lb sb smax fn-zin-tab)
           :in-theory (e/d (fn-zin-place-syms) (fn-zin-tput fn-oct-update fn-zin-len-of))))))

(local
 (defthm fn-pwsf-zero-range-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-zero-range e k fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :induct (fn-zin-zero-range e k fn-zin-tab)
           :in-theory (e/d (fn-zin-zero-range) (fn-zin-tput fn-oct-update fn-zin-len-of))))))

(local
 (defthm fn-pwsf-next-codes-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-next-codes len code cb fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :induct (fn-zin-next-codes len code cb fn-zin-tab)
           :in-theory (e/d (fn-zin-next-codes) (fn-zin-tput fn-oct-update fn-zin-len-of))))))

(local
 (defthm fn-pwsf-replicate-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-replicate e step k v fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :induct (fn-zin-replicate e step k v fn-zin-tab)
           :in-theory (e/d (fn-zin-replicate) (fn-zin-tput fn-oct-update fn-zin-len-of))))))

(local
 (defthm fn-pwsf-fill-lookup-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-fill-lookup s n lb base fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :induct (fn-zin-fill-lookup s n lb base fn-zin-tab)
           :in-theory (e/d (fn-zin-fill-lookup) (fn-zin-tput fn-oct-update fn-zin-len-of))))))

(local
 (defthm fn-pwsf-fill-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-fill e k v fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :induct (fn-zin-fill e k v fn-zin-tab)
           :in-theory (e/d (fn-zin-fill) (fn-zin-tput fn-oct-update fn-zin-len-of))))))

(local
 (defthm fn-pwsf-zero-cl-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-zero-cl i fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :induct (fn-zin-zero-cl i fn-zin-tab)
           :in-theory (e/d (fn-zin-zero-cl) (fn-zin-tput fn-oct-update fn-zin-len-of))))))

(local
 (defthm fn-pwsf-construct-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (mv-nth 1 (fn-zin-construct tb lb n fn-zin-tab))) *fn-zin-tab-octets*))
  :hints (("Goal" :in-theory (e/d (fn-zin-construct)
                           (fn-zin-tput fn-zin-zero-range fn-zin-zero-counts fn-zin-count-lens
                            fn-zin-offsets fn-zin-place-syms fn-zin-next-codes fn-zin-fill-lookup))))))

(local
 (defthm fn-pwsf-fixed-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-fixed-tables fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :in-theory (e/d (fn-zin-fixed-tables) (fn-zin-fill fn-zin-construct))))))

(local
 (defthm fn-pwsf-dynamic-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (mv-nth 1 (fn-zin-dynamic-tables hlit hdist fn-zin-tab))) *fn-zin-tab-octets*))
  :hints (("Goal" :in-theory (e/d (fn-zin-dynamic-tables) (fn-zin-construct))))))

(local
 (defthm fn-pwsf-emit-retains-history-length
  (implies (equal (len fn-zin-win) *fn-zin-win-octets*)
   (equal (len (mv-nth 2 (fn-zin-emit o fn-zin-st fn-zin-win fn-zin-out))) *fn-zin-win-octets*))
  :hints (("Goal" :in-theory (e/d (fn-zin-emit) (fn-oct-update fn-zin-emit-out))))))

(local
 (defthm fn-pwsf-actual-action-keeps-buffer-lengths
  (implies (and (equal (len fn-zin-win) *fn-zin-win-octets*)
                (equal (len fn-zin-tab) *fn-zin-tab-octets*))
   (let ((r (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
    (and (equal (len (mv-nth 2 r)) *fn-zin-win-octets*)
         (equal (len (mv-nth 3 r)) *fn-zin-tab-octets*))))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (fn-zin-act)
           (fn-zin-emit fn-zin-emit-out fn-zin-construct fn-zin-fixed-tables fn-zin-dynamic-tables fn-zin-fill fn-zin-zero-cl fn-zin-tput))))))

(local
 (defthm fn-pwsf-copy-retains-history-length
  (implies (equal (len fn-zin-win) *fn-zin-win-octets*)
   (equal (len (mv-nth 1 (fn-zin-copy k w d tout h fn-zin-win fn-zin-out))) *fn-zin-win-octets*))
  :hints (("Goal" :induct (fn-zin-copy k w d tout h fn-zin-win fn-zin-out)
           :in-theory (e/d (fn-zin-copy) (fn-oct-update))))))

(local
 (defthm fn-pwsf-match-retains-history-length
  (implies (equal (len fn-zin-win) *fn-zin-win-octets*)
   (equal (len (mv-nth 2 (fn-zin-match room fn-zin-st fn-zin-win fn-zin-out))) *fn-zin-win-octets*))
  :hints (("Goal" :in-theory (e/d (fn-zin-match) (fn-zin-copy))))))

(local
 (defthm fn-pwsf-literal-loop-retains-history-length
  (implies (equal (len fn-zin-win) *fn-zin-win-octets*)
   (equal (len (mv-nth 4 (fn-zin-lit-loop k bits nbits w tout limit fn-zin-tab fn-zin-win fn-zin-out))) *fn-zin-win-octets*))
  :hints (("Goal" :induct (fn-zin-lit-loop k bits nbits w tout limit fn-zin-tab fn-zin-win fn-zin-out)
           :in-theory (e/d (fn-zin-lit-loop) (fn-oct-update))))))

(local
 (defthm fn-pwsf-literals-retain-history-length
  (implies (equal (len fn-zin-win) *fn-zin-win-octets*)
   (equal (len (mv-nth 2 (fn-zin-lits room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))) *fn-zin-win-octets*))
  :hints (("Goal" :in-theory (e/d (fn-zin-lits) (fn-zin-lit-loop))))))

(local
 (defthm fn-pwsf-actual-step-keeps-buffer-lengths
  (implies (and (equal (len fn-zin-win) *fn-zin-win-octets*)
                (equal (len fn-zin-tab) *fn-zin-tab-octets*))
   (let ((r (fn-zin-step room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
    (and (equal (len (mv-nth 2 r)) *fn-zin-win-octets*)
         (equal (len (mv-nth 3 r)) *fn-zin-tab-octets*))))
  :hints (("Goal" :in-theory (e/d (fn-zin-step)
           (fn-zin-act fn-zin-match fn-zin-lits fn-zin-step-out-free))))))

(local
 (defthm fn-pwsf-actual-loop-keeps-buffer-lengths
  (implies (and (equal (len fn-zin-win) *fn-zin-win-octets*)
                (equal (len fn-zin-tab) *fn-zin-tab-octets*))
   (let ((r (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
    (and (equal (len (mv-nth 4 r)) *fn-zin-win-octets*)
         (equal (len (mv-nth 5 r)) *fn-zin-tab-octets*))))
  :hints (("Goal" :induct (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
           :in-theory (e/d (fn-zin-loop)
           (fn-zin-act fn-zin-step fn-zin-pull fn-zin-need fn-zin-step-out-free fn-zin-loop-counts))))))

(defun-nx fn-pwsf-actual-stored-frontier-turns
 (requests remaining ip end compressed expected fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out prefix)
 (declare (xargs :measure (len requests) :verify-guards nil))
 (let* ((requested (car requests))
        (b (fn-pzw-quantum requested remaining))
        (credited (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin fn-zin-st)) fn-zin-st))
        (frontier (+ (len prefix)
                     (fn-pzw-room (min (nfix expected) (fn-pzw-stored-allowance compressed))
                                  (fn-zin-tout credited))))
        (r (fn-pzw-stored-chunk requested remaining ip end compressed expected
                               fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
        (next-prefix (append prefix (mv-nth 6 r)))
        (observation (mv (car r) (mv-nth 1 r) (mv-nth 2 r)
                         (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin (mv-nth 3 r))) (mv-nth 3 r))
                         (mv-nth 4 r) (mv-nth 5 r) next-prefix)))
  (if (and (consp requests) (consp (cdr requests)) (member-equal (car r) '(:full :yield)))
   (mv-let (answer rows)
    (fn-pwsf-actual-stored-frontier-turns (cdr requests)
     (fn-pzw-budget-left requested remaining (mv-nth 1 r))
     (mv-nth 2 r) end compressed expected (mv-nth 3 r) fn-octets
     (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r) next-prefix)
    (mv answer (cons (list b frontier) rows)))
   (mv observation (list (list b frontier))))))

(local
 (defthm fn-pwsf-actual-stored-chunk-keeps-buffer-lengths
  (implies (and (equal (len fn-zin-win) *fn-zin-win-octets*)
                (equal (len fn-zin-tab) *fn-zin-tab-octets*))
   (let ((r (fn-pzw-stored-chunk requested remaining ip end compressed expected
                               fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
    (and (equal (len (mv-nth 4 r)) *fn-zin-win-octets*)
         (equal (len (mv-nth 5 r)) *fn-zin-tab-octets*))))
  :hints (("Goal" :use ((:instance fn-pwzc-actual-stored-chunk-recredited-full-tuple (start ip))
    (:instance fn-pwsf-actual-loop-keeps-buffer-lengths
     (b (fn-pzw-quantum requested remaining))
     (lim (fn-pzw-room (min (nfix expected) (fn-pzw-stored-allowance compressed)) (fn-zin-tout fn-zin-st)))
     (fn-zin-st (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin fn-zin-st)) fn-zin-st)) (fn-zin-out nil)))
   :in-theory (e/d (fn-pzw-stored-chunk fn-pzw-chunk fn-zin-feed fn-zin-window-ready-p fn-zin-tab-okp)
    (fn-zin-loop fn-pzw-room fn-pzw-quantum fn-pzw-stored-allowance min nfix))))))



(local
 (defthm fn-pwsf-quantum-natural
  (natp (fn-pzw-quantum requested remaining))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-pzw-quantum)))))
(local
 (defthm fn-pwsf-room-natural
  (natp (fn-pzw-room expected produced))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-pzw-room)))))
(local
 (defthm fn-pwsf-nfix-natural
  (implies (natp x) (equal (nfix x) x))
  :hints (("Goal" :in-theory (enable nfix)))))

(local
 (defthm fn-pwsf-generated-frontier-cons-unfolds
  (equal (fn-pwif-actual-frontier-turns (cons (list b frontier) rows) ip end
                    fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
   (let* ((r (fn-zin-loop (nfix b) ip end (nfix frontier) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
          (fuel (fn-pwz-actual-loop-semantic-fuel (nfix b) ip end (nfix frontier) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
    (if (and (consp rows) (member-equal (car r) '(:full :yield)))
     (mv-let (next rest final valid)
      (fn-pwif-actual-frontier-turns rows (mv-nth 2 r) end (mv-nth 3 r) fn-octets
                                   (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r))
      (mv next (+ (- fuel (mv-nth 1 r)) rest) final (and valid (<= (nfix frontier) final))))
     (mv r fuel (nfix frontier) t))))
  :hints (("Goal" :expand (fn-pwif-actual-frontier-turns (cons (list b frontier) rows) ip end
                    fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
   :in-theory (disable fn-pwif-actual-frontier-turns fn-zin-loop fn-pwz-actual-loop-semantic-fuel)))))


(local
 (defthm fn-pwsf-generated-rows-nonempty-by-definition
  (consp (mv-nth 1 (fn-pwsf-actual-stored-frontier-turns requests remaining ip end compressed expected
                   fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out prefix)))
  :hints (("Goal" :expand (fn-pwsf-actual-stored-frontier-turns requests remaining ip end compressed expected
                   fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out prefix)
   :in-theory (disable fn-pwsf-actual-stored-frontier-turns fn-pzw-stored-chunk fn-pzw-room
                       fn-pzw-quantum fn-pzw-budget-left fn-zin-set$inline fn-pzw-stored-allowance min nfix)))))

(defthm fn-pwsf-actual-stored-turns-generated-basic-loop-transcript
 (let* ((s (fn-pwsf-actual-stored-frontier-turns requests remaining ip end compressed expected
                      fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out prefix))
        (credited (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin fn-zin-st)) fn-zin-st)))
  (implies (and (true-listp prefix)
                (equal (len fn-zin-win) *fn-zin-win-octets*)
                (equal (len fn-zin-tab) *fn-zin-tab-octets*))
   (equal (mv-nth 0 s)
    (mv-nth 0 (fn-pwif-actual-frontier-turns (mv-nth 1 s) ip end credited fn-octets fn-zin-win fn-zin-tab prefix)))))
 :rule-classes nil
 :hints (("Goal" :induct (fn-pwsf-actual-stored-frontier-turns requests remaining ip end compressed expected
                         fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out prefix)
   :expand ((fn-pwsf-actual-stored-frontier-turns requests remaining ip end compressed expected fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out prefix)
    (fn-pwif-actual-frontier-turns (mv-nth 1 (fn-pwsf-actual-stored-frontier-turns requests remaining ip end compressed expected fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out prefix)) ip end (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin fn-zin-st)) fn-zin-st) fn-octets fn-zin-win fn-zin-tab prefix))
   :in-theory (disable (:definition fn-pwsf-actual-stored-frontier-turns) fn-pwif-actual-frontier-turns
    fn-pzw-stored-chunk fn-zin-loop fn-zin-feed fn-zin-set$inline fn-pzw-room fn-pzw-quantum fn-pzw-stored-allowance
     fn-pzw-budget-left fn-pwz-actual-loop-semantic-fuel min nfix))
  ("Subgoal *1/1" :use (:instance fn-pwy-actual-stored-cleared-chunk-complete-prefix-effects (requested (car requests)) (start ip)))
  ("Subgoal *1/2" :use (:instance fn-pwy-actual-stored-cleared-chunk-complete-prefix-effects (requested (car requests)) (start ip)))))

(local
 (defthm fn-pwsf-scalar-frontier-monotone
  (implies (and (natp p) (natp q) (<= p q))
   (<= (+ p (fn-pzw-room expected p)) (+ q (fn-pzw-room expected q))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pzw-room min nfix)))))

(local
 (defun fn-pwsf-frontier-rows-monotone (rows)
  (if (and (consp rows) (consp (cdr rows)))
   (and (<= (nfix (cadar rows)) (nfix (cadadr rows)))
        (fn-pwsf-frontier-rows-monotone (cdr rows)))
   t)))

(local
 (defthm fn-pwsf-monotone-frontier-rows-establish-condition
  (let ((s (fn-pwif-actual-frontier-turns rows ip end fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
   (implies (fn-pwsf-frontier-rows-monotone rows)
    (and (mv-nth 3 s)
         (implies (consp rows) (<= (nfix (cadar rows)) (mv-nth 2 s))))))
  :hints (("Goal" :induct (fn-pwif-actual-frontier-turns rows ip end fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
   :in-theory (e/d (fn-pwif-actual-frontier-turns fn-pwsf-frontier-rows-monotone)
    (fn-zin-loop fn-pwz-actual-loop-semantic-fuel))))))

(local
 (defthm fn-pwsf-credit-preserves-output-counter
  (equal (fn-zin-tout (fn-zin-set 7 credit fn-zin-st)) (fn-zin-tout fn-zin-st))
  :hints (("Goal" :in-theory (enable fn-zin-set$inline fn-zin-fld$inline)))))

(local
 (defthm fn-pwsf-generated-first-frontier-by-definition
  (equal (cadar (mv-nth 1 (fn-pwsf-actual-stored-frontier-turns requests remaining ip end compressed expected
                   fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out prefix)))
   (+ (len prefix) (fn-pzw-room (min (nfix expected) (fn-pzw-stored-allowance compressed)) (fn-zin-tout fn-zin-st))))
  :hints (("Goal" :expand (fn-pwsf-actual-stored-frontier-turns requests remaining ip end compressed expected
                   fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out prefix)
   :in-theory (disable fn-pwsf-actual-stored-frontier-turns fn-pzw-stored-chunk fn-pzw-room
                       fn-pzw-quantum fn-pzw-budget-left fn-zin-set$inline fn-pzw-stored-allowance min nfix)))))



(local
 (defthm fn-pwsf-prefix-append-length
  (equal (len (append p q)) (+ (len p) (len q)))
  :hints (("Goal" :induct (append p q) :in-theory (enable append len)))))
(local
 (defthm fn-pwsf-prefix-append-proper
  (implies (true-listp q) (true-listp (append p q)))
  :hints (("Goal" :induct (append p q) :in-theory (enable append true-listp)))))

(local
 (defthm fn-pwsf-actual-generated-frontiers-monotone
  (implies (and (true-listp prefix) (natp ip)
                (equal (len fn-zin-win) *fn-zin-win-octets*)
                (equal (len fn-zin-tab) *fn-zin-tab-octets*)
                (equal (fn-zin-tout fn-zin-st) (len prefix)))
   (fn-pwsf-frontier-rows-monotone (mv-nth 1 (fn-pwsf-actual-stored-frontier-turns requests remaining ip end compressed expected fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out prefix))))
  :hints (("Goal" :induct (fn-pwsf-actual-stored-frontier-turns requests remaining ip end compressed expected fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out prefix) :expand ((fn-pwsf-actual-stored-frontier-turns requests remaining ip end compressed expected fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out prefix)
    (fn-pwsf-actual-stored-frontier-turns requests remaining 0 end compressed expected fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out prefix))
   :in-theory (e/d (fn-pwsf-frontier-rows-monotone)
    ((:definition fn-pwsf-actual-stored-frontier-turns) fn-pzw-stored-chunk fn-pzw-room
     fn-pzw-quantum fn-pzw-budget-left fn-zin-set$inline fn-pzw-stored-allowance min nfix)))
   ("Subgoal *1/1" :use ((:instance fn-pzw-stored-chunk-counts-real-input (requested (car requests)) (start ip))
    (:instance fn-pwsf-scalar-frontier-monotone
     (p (len prefix)) (q (+ (len prefix) (len (mv-nth 6 (fn-pzw-stored-chunk (car requests) remaining ip end compressed expected fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))))
     (expected (min (nfix expected) (fn-pzw-stored-allowance compressed)))))))))



(local
 (defthm fn-pwsfc-canonical-initialize-tout-zero
  (equal (fn-zin-tout (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) 0)
  :hints (("Goal" :in-theory (enable fn-pzw-initialize fn-zin-reset fn-zin-reset-loop)))))

(local
 (defthm fn-pwsfc-logical-snoc-length
  (equal (len (fn-oct-snoc xs o)) (+ 1 (len xs)))
  :hints (("Goal" :induct (fn-oct-snoc xs o) :in-theory (enable fn-oct-snoc)))))

(local
 (defthm fn-pwsfc-logical-back-copy-length
   (implies (and (posp off) (<= off (len xs)))
            (equal (len (fn-oct-back-copy off n xs)) (+ (len xs) (nfix n))))
   :hints (("Goal" :induct (fn-oct-back-copy off n xs)))))

(local
 (defthm fn-pwsfc-logical-nthcdr-length
  (equal (len (nthcdr n x)) (nfix (- (len x) (nfix n))))
  :hints (("Goal" :induct (nthcdr n x) :in-theory (enable nthcdr nfix len)))))

(local
 (defthm fn-pwsfc-actual-payload-ready-buffer-lengths-unconditional
  (let ((r (fn-zin-payload-ready dict fn-zin-win fn-zin-tab)))
   (and (equal (len (mv-nth 1 r)) 65536) (equal (len (mv-nth 2 r)) 3494)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-zin-payload-ready)
                           (fn-oct-back-copy (:e fn-oct-back-copy)
                            (:e fn-zin-win-append-back) (:e fn-zin-tab-append-back)
                            (:e fn-octets$a-append-back)))))))

(local
 (defthm fn-pwsfc-actual-initialize-buffer-lengths-unconditional
  (let ((r (fn-pzw-initialize dict fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
   (and (equal (len (mv-nth 1 r)) 65536) (equal (len (mv-nth 2 r)) 3494)))
  :hints (("Goal" :in-theory (e/d (fn-pzw-initialize) (fn-zin-reset fn-zin-payload-ready))))))

(local
 (defthm fn-pwsf-actual-generated-frontier-condition
  (implies (and (true-listp prefix) (natp ip)
                (equal (len fn-zin-win) *fn-zin-win-octets*)
                (equal (len fn-zin-tab) *fn-zin-tab-octets*)
                (equal (fn-zin-tout fn-zin-st) (len prefix)))
   (mv-nth 3 (fn-pwif-actual-frontier-turns (mv-nth 1 (fn-pwsf-actual-stored-frontier-turns requests remaining ip end compressed expected fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out prefix)) ip end
    (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin fn-zin-st)) fn-zin-st)
    fn-octets fn-zin-win fn-zin-tab prefix)))
  :hints (("Goal" :use ((:instance fn-pwsf-actual-generated-frontiers-monotone)
    (:instance fn-pwsf-monotone-frontier-rows-establish-condition
     (rows (mv-nth 1 (fn-pwsf-actual-stored-frontier-turns requests remaining ip end compressed expected fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out prefix)))
     (fn-zin-st (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin fn-zin-st)) fn-zin-st))
     (fn-zin-out prefix)))
   :in-theory (disable fn-pwsf-actual-stored-frontier-turns fn-pwif-actual-frontier-turns
     fn-zin-set$inline fn-pwsf-frontier-rows-monotone)))))

(local
 (defthm fn-pwsfc-canonical-initialize-tin-zero
  (equal (fn-zin-tin (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) 0)
  :hints (("Goal" :in-theory (enable fn-pzw-initialize fn-zin-reset fn-zin-reset-loop)))))

(local
 (defthm fn-pwsfc-initialized-actual-generated-frontier-condition
  (mv-nth 3 (fn-pwif-actual-frontier-turns (mv-nth 1 (fn-pwsf-actual-stored-frontier-turns requests remaining 0 (len fn-octets) (len fn-octets) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) fn-octets (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil nil)) 0 (len fn-octets)
             (fn-zin-set 7 (len fn-octets) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) fn-octets (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil))
  :hints (("Goal" :use (:instance fn-pwsf-actual-generated-frontier-condition
   (ip 0) (end (len fn-octets)) (compressed (len fn-octets)) (expected n)
   (fn-zin-st (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-win (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-tab (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))
   (fn-zin-out nil) (prefix nil))
   :in-theory (disable fn-pwsf-actual-stored-frontier-turns fn-pwif-actual-frontier-turns
    fn-pzw-initialize create-fn-zin-st fn-zin-set$inline)))))
