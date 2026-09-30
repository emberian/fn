; Actual stored chunk credit and output-window composition. PRF1131 component.
; This book changes no runtime. Full remaining fuel is preserved at each actual
; wrapper boundary; completed-window confluence compares semantic effects only.
; Canonical initialization/dictionary/input-cut/yield/digest and native holder/
; complete selected runtime funding remain separate obligations.
(in-package "ACL2")

(include-book "decoded-window-output-trajectory")

(local (include-book "arithmetic-5/top" :dir :system))

(local
 (defun-nx fn-pwz-tin-coordinatep (fn-zin-st)
 (equal (fn-zin-set 7 (fn-zin-tin fn-zin-st) fn-zin-st) fn-zin-st)))

(local
 (defthm fn-pwzc-update-nth-same
  (equal (update-nth i x (update-nth i y z)) (update-nth i x z))
  :hints (("Goal" :induct (update-nth i x z) :in-theory (enable update-nth)))))

(local
 (defun fn-pwzc-index-pair-induction (i j z)
  (declare (xargs :measure (nfix i) :verify-guards nil))
  (if (and (posp i) (posp j)) (fn-pwzc-index-pair-induction (1- i) (1- j) (cdr z)) z)))

(local
 (defthm fn-pwzc-update-nth-commute
  (implies (and (natp i) (natp j) (not (equal i j)))
   (equal (update-nth i x (update-nth j y z)) (update-nth j y (update-nth i x z))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-pwzc-index-pair-induction i j z) :in-theory (enable update-nth)))))

(local
 (defthm fn-pwzc-state-set-same
  (equal (fn-zin-set i x (fn-zin-set i y fn-zin-st)) (fn-zin-set i x fn-zin-st))
  :hints (("Goal" :in-theory (enable fn-zin-set$inline)))))

(local
 (defthm fn-pwzc-state-set-commute
  (implies (not (equal i j))
   (equal (fn-zin-set i x (fn-zin-set j y fn-zin-st))
          (fn-zin-set j y (fn-zin-set i x fn-zin-st))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-zin-set$inline)
           :use ((:instance fn-pwzc-update-nth-commute (x (nfix x)) (y (nfix y)) (z (car fn-zin-st))))))))

(local
 (defthm fn-pwzc-tin-set-canonical
  (fn-pwz-tin-coordinatep (fn-zin-set 7 v fn-zin-st))
  :hints (("Goal" :in-theory (enable fn-pwz-tin-coordinatep fn-zin-set$inline fn-zin-fld$inline)))))

(local
 (defthm fn-pwzc-set-preserves-tin-coordinate
  (implies (fn-pwz-tin-coordinatep fn-zin-st)
   (fn-pwz-tin-coordinatep (fn-zin-set j v fn-zin-st)))
  :hints (("Goal" :cases ((equal j 7))
           :use ((:instance fn-pwzc-state-set-commute (i 7) (x (fn-zin-tin fn-zin-st)) (y v)))
           :in-theory (enable fn-pwz-tin-coordinatep)))))

(local
 (defthm fn-pwzc-take-preserves-tin-coordinate
  (implies (fn-pwz-tin-coordinatep fn-zin-st)
   (fn-pwz-tin-coordinatep (mv-nth 1 (fn-zin-take n fn-zin-st))))
  :hints (("Goal" :in-theory (enable fn-zin-take)))))

(local
 (defthm fn-pwzc-decode-preserves-tin-coordinate
  (implies (fn-pwz-tin-coordinatep fn-zin-st)
   (fn-pwz-tin-coordinatep (mv-nth 2 (fn-zin-decode-bit tb fn-zin-st fn-zin-tab))))
  :hints (("Goal" :in-theory (enable fn-zin-decode-bit)))))

(local
 (defthm fn-pwzc-emit-preserves-tin-coordinate
  (implies (fn-pwz-tin-coordinatep fn-zin-st)
   (fn-pwz-tin-coordinatep (mv-nth 1 (fn-zin-emit o fn-zin-st fn-zin-win fn-zin-out))))
  :hints (("Goal" :in-theory (e/d (fn-zin-emit) (fn-zin-emit-out))))))

(local
 (defthm fn-pwzc-act-preserves-tin-coordinate
  (implies (fn-pwz-tin-coordinatep fn-zin-st)
   (fn-pwz-tin-coordinatep (mv-nth 1 (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-zin-act) (fn-zin-act-counts fn-zin-emit-out))))))

(local
 (defthm fn-pwzc-step-preserves-tin-coordinate
  (implies (fn-pwz-tin-coordinatep fn-zin-st)
   (fn-pwz-tin-coordinatep (mv-nth 1 (fn-zin-step room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-zin-step fn-zin-match fn-zin-lits)
                           (fn-zin-act fn-zin-copy fn-zin-lit-loop fn-zin-step-counts
                            fn-zin-match-out-free fn-zin-lits-out-free fn-zin-step-out-free))))))

(local
 (defthm fn-pwzc-pull-tin-coordinate
  (fn-pwz-tin-coordinatep (fn-zin-pull ip fn-zin-st fn-octets))
  :hints (("Goal" :in-theory (enable fn-zin-pull)))))

(local
 (defthm fn-pwzc-actual-loop-preserves-tin-coordinate
 (implies (fn-pwz-tin-coordinatep fn-zin-st)
  (fn-pwz-tin-coordinatep
   (mv-nth 3 (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
 :rule-classes nil
 :hints (("Goal" :induct (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
          :in-theory (e/d (fn-zin-loop)
                          (fn-zin-step fn-zin-act fn-zin-pull fn-zin-need fn-zin-loop-counts
                           fn-zin-step-counts fn-zin-act-counts fn-zin-step-out-free))))))

(local
 (defthm fn-pwzc-pull-increases-tin
  (equal (fn-zin-tin (fn-zin-pull ip fn-zin-st fn-octets)) (+ 1 (fn-zin-tin fn-zin-st)))
  :hints (("Goal" :in-theory (enable fn-zin-pull)))))

(local
 (defthm fn-pwzc-actual-loop-tin-monotone
 (<= (fn-zin-tin fn-zin-st)
     (fn-zin-tin (mv-nth 3 (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
 :rule-classes nil
 :hints (("Goal" :induct (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
          :in-theory (e/d (fn-zin-loop)
                          (fn-zin-step fn-zin-act fn-zin-pull fn-zin-need fn-zin-loop-counts fn-zin-step-out-free))))))

(local
 (defthm fn-pwzc-exact-recredit-state
 (implies (and (fn-pwz-tin-coordinatep fn-zin-st)
               (<= (nfix compressed) (fn-zin-tin fn-zin-st)))
  (let ((real (fn-zin-set 7 (nfix (- (fn-zin-tin fn-zin-st) (nfix compressed))) fn-zin-st)))
   (equal (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin real)) real) fn-zin-st)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-pwz-tin-coordinatep nfix fn-zin-set$inline fn-zin-fld$inline)))))

(local
 (defthm fn-pwzc-nfix-natural
  (implies (natp x) (equal (nfix x) x))
  :hints (("Goal" :in-theory (enable nfix)))))

(local
 (defthm fn-pwzc-actual-credited-loop-recredit-exact
 (let* ((credited (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin fn-zin-st)) fn-zin-st))
        (r (fn-zin-loop b ip end lim credited fn-octets fn-zin-win fn-zin-tab fn-zin-out))
        (real (fn-zin-set 7 (nfix (- (fn-zin-tin (mv-nth 3 r)) (nfix compressed))) (mv-nth 3 r))))
  (equal (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin real)) real) (mv-nth 3 r)))
 :rule-classes nil
 :hints (("Goal"
          :use ((:instance fn-pwzc-actual-loop-preserves-tin-coordinate
                 (fn-zin-st (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin fn-zin-st)) fn-zin-st)))
                (:instance fn-pwzc-actual-loop-tin-monotone
                 (fn-zin-st (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin fn-zin-st)) fn-zin-st)))
                (:instance fn-pwzc-exact-recredit-state
                 (fn-zin-st (mv-nth 3 (fn-zin-loop b ip end lim
                          (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin fn-zin-st)) fn-zin-st)
                          fn-octets fn-zin-win fn-zin-tab fn-zin-out)))))
          :in-theory (disable fn-zin-loop fn-zin-step fn-zin-act fn-zin-pull fn-zin-need fn-pwz-tin-coordinatep fn-zin-loop-counts nfix)))))

(local
 (defthm fn-pwzc-actual-credited-feed-recredit-exact
 (let* ((credited (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin fn-zin-st)) fn-zin-st))
        (r (fn-zin-feed b credited start end lim fn-octets fn-zin-win fn-zin-tab fn-zin-out))
        (real (fn-zin-set 7 (nfix (- (fn-zin-tin (mv-nth 3 r)) (nfix compressed))) (mv-nth 3 r))))
  (equal (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin real)) real) (mv-nth 3 r)))
 :rule-classes nil
 :hints (("Goal"
          :use ((:instance fn-pwzc-actual-credited-loop-recredit-exact (ip start)))
          :in-theory (e/d (fn-zin-feed)
                          (fn-zin-loop fn-zin-step fn-zin-act fn-zin-pull fn-zin-need
                           fn-zin-loop-counts fn-pwz-tin-coordinatep nfix))))))

(local
 (defthm fn-pwzc-actual-loop-full-tuple
  (let ((r (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
   (equal (list (car r) (mv-nth 1 r) (mv-nth 2 r) (mv-nth 3 r)
                (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r)) r))
  :hints (("Goal" :induct (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
           :in-theory (e/d (fn-zin-loop)
                           (fn-zin-step fn-zin-act fn-zin-pull fn-zin-need fn-zin-loop-counts fn-zin-step-out-free))))))

(local
 (defthm fn-pwzc-actual-feed-full-tuple
  (let ((r (fn-zin-feed b fn-zin-st start end lim fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
   (equal (list (car r) (mv-nth 1 r) (mv-nth 2 r) (mv-nth 3 r)
                (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r)) r))
  :hints (("Goal" :in-theory (enable fn-zin-feed)))))

(defthm fn-pwzc-actual-stored-chunk-recredited-full-tuple
 (let* ((r (fn-pzw-stored-chunk requested remaining start end compressed expected
                               fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
        (credited (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin fn-zin-st)) fn-zin-st)))
  (equal (mv (car r) (mv-nth 1 r) (mv-nth 2 r)
             (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin (mv-nth 3 r))) (mv-nth 3 r))
             (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r))
         (fn-zin-feed (fn-pzw-quantum requested remaining) credited start end
                      (fn-pzw-room (min (nfix expected) (fn-pzw-stored-allowance compressed)) (fn-zin-tout credited))
                      fn-octets fn-zin-win fn-zin-tab nil)))
 :rule-classes nil
 :hints (("Goal"
          :use ((:instance fn-pwzc-actual-feed-full-tuple
                 (b (fn-pzw-quantum requested remaining))
                 (fn-zin-st (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin fn-zin-st)) fn-zin-st))
                 (lim (fn-pzw-room (min (nfix expected) (fn-pzw-stored-allowance compressed)) (fn-zin-tout fn-zin-st)))
                 (fn-zin-out nil))
                (:instance fn-pwzc-actual-credited-feed-recredit-exact
                 (b (fn-pzw-quantum requested remaining))
                 (lim (fn-pzw-room (min (nfix expected) (fn-pzw-stored-allowance compressed)) (fn-zin-tout fn-zin-st)))
                 (fn-zin-out nil)))
          :in-theory (e/d (fn-pzw-stored-chunk fn-pzw-chunk)
                          (fn-zin-feed fn-zin-loop fn-zin-step fn-zin-act fn-zin-pull fn-zin-need
                           fn-pzw-quantum fn-pzw-room fn-pzw-stored-allowance fn-zin-loop-counts fn-pwzc-actual-feed-full-tuple min nfix)))))

(defthm fn-pwzc-actual-two-stored-chunks-full-tuple
 (let* ((r1 (fn-pzw-stored-chunk requested1 remaining1 start end compressed expected
                                fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
        (r2 (fn-pzw-stored-chunk requested2 remaining2 (mv-nth 2 r1) end compressed expected
                                (mv-nth 3 r1) fn-octets (mv-nth 4 r1) (mv-nth 5 r1) (mv-nth 6 r1)))
        (credited (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin fn-zin-st)) fn-zin-st))
        (a1 (fn-zin-feed (fn-pzw-quantum requested1 remaining1) credited start end
                         (fn-pzw-room (min (nfix expected) (fn-pzw-stored-allowance compressed)) (fn-zin-tout credited))
                         fn-octets fn-zin-win fn-zin-tab nil))
        (a2 (fn-zin-feed (fn-pzw-quantum requested2 remaining2) (mv-nth 3 a1) (mv-nth 2 a1) end
                         (fn-pzw-room (min (nfix expected) (fn-pzw-stored-allowance compressed)) (fn-zin-tout (mv-nth 3 a1)))
                         fn-octets (mv-nth 4 a1) (mv-nth 5 a1) nil)))
  (equal (list (car r2) (mv-nth 1 r2) (mv-nth 2 r2)
               (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin (mv-nth 3 r2))) (mv-nth 3 r2))
               (mv-nth 4 r2) (mv-nth 5 r2) (mv-nth 6 r2)) a2))
 :rule-classes nil
 :hints (("Goal"
          :use ((:instance fn-pwzc-actual-stored-chunk-recredited-full-tuple (requested requested1) (remaining remaining1))
                (:instance fn-pwzc-actual-stored-chunk-recredited-full-tuple
                 (requested requested2) (remaining remaining2)
                 (start (mv-nth 2 (fn-pzw-stored-chunk requested1 remaining1 start end compressed expected fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-st (mv-nth 3 (fn-pzw-stored-chunk requested1 remaining1 start end compressed expected fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-win (mv-nth 4 (fn-pzw-stored-chunk requested1 remaining1 start end compressed expected fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-tab (mv-nth 5 (fn-pzw-stored-chunk requested1 remaining1 start end compressed expected fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-out (mv-nth 6 (fn-pzw-stored-chunk requested1 remaining1 start end compressed expected fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))))
          :in-theory (disable fn-pzw-stored-chunk fn-pzw-chunk fn-zin-feed fn-zin-loop
                              fn-pzw-room fn-pzw-quantum fn-pzw-stored-allowance nfix min
                              fn-pwzc-actual-feed-full-tuple fn-pwzc-actual-loop-full-tuple))))

(local
 (defthm fn-pwzc-update-octet-retains-length
  (implies (and (natp i) (< i (len x)))
   (equal (len (fn-oct-update i o x)) (len x)))
  :hints (("Goal" :induct (fn-oct-update i o x) :in-theory (enable fn-oct-update)))))

(local
 (defthm fn-pwzc-table-length-word-write
  (implies (and (natp e) (< e *fn-zin-tab-entries*)
                (equal (len fn-zin-tab) *fn-zin-tab-octets*))
   (equal (len (fn-zin-tput e v fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :in-theory (e/d (fn-zin-tput) (fn-oct-update))))))

(local
 (defthm fn-pwzc-code-length-bounds-unconditional
  (and (natp (fn-zin-len-of e fn-zin-tab)) (<= (fn-zin-len-of e fn-zin-tab) 15))
  :rule-classes ((:rewrite) (:type-prescription :corollary (natp (fn-zin-len-of e fn-zin-tab))) (:linear :corollary (<= (fn-zin-len-of e fn-zin-tab) 15)))
  :hints (("Goal" :in-theory (enable fn-zin-len-of)))))

(local
 (defthm fn-pwzc-zero-counts-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-zero-counts k cb fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :induct (fn-zin-zero-counts k cb fn-zin-tab)
           :in-theory (e/d (fn-zin-zero-counts) (fn-zin-tput fn-oct-update fn-zin-len-of))))))

(local
 (defthm fn-pwzc-count-lens-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-count-lens s n lb cb fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :induct (fn-zin-count-lens s n lb cb fn-zin-tab)
           :in-theory (e/d (fn-zin-count-lens) (fn-zin-tput fn-oct-update fn-zin-len-of))))))

(local
 (defthm fn-pwzc-offsets-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-offsets len off cb fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :induct (fn-zin-offsets len off cb fn-zin-tab)
           :in-theory (e/d (fn-zin-offsets) (fn-zin-tput fn-oct-update fn-zin-len-of))))))

(local
 (defthm fn-pwzc-place-syms-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-place-syms s n lb sb smax fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :induct (fn-zin-place-syms s n lb sb smax fn-zin-tab)
           :in-theory (e/d (fn-zin-place-syms) (fn-zin-tput fn-oct-update fn-zin-len-of))))))

(local
 (defthm fn-pwzc-zero-range-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-zero-range e k fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :induct (fn-zin-zero-range e k fn-zin-tab)
           :in-theory (e/d (fn-zin-zero-range) (fn-zin-tput fn-oct-update fn-zin-len-of))))))

(local
 (defthm fn-pwzc-next-codes-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-next-codes len code cb fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :induct (fn-zin-next-codes len code cb fn-zin-tab)
           :in-theory (e/d (fn-zin-next-codes) (fn-zin-tput fn-oct-update fn-zin-len-of))))))

(local
 (defthm fn-pwzc-replicate-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-replicate e step k v fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :induct (fn-zin-replicate e step k v fn-zin-tab)
           :in-theory (e/d (fn-zin-replicate) (fn-zin-tput fn-oct-update fn-zin-len-of))))))

(local
 (defthm fn-pwzc-fill-lookup-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-fill-lookup s n lb base fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :induct (fn-zin-fill-lookup s n lb base fn-zin-tab)
           :in-theory (e/d (fn-zin-fill-lookup) (fn-zin-tput fn-oct-update fn-zin-len-of))))))

(local
 (defthm fn-pwzc-fill-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-fill e k v fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :induct (fn-zin-fill e k v fn-zin-tab)
           :in-theory (e/d (fn-zin-fill) (fn-zin-tput fn-oct-update fn-zin-len-of))))))

(local
 (defthm fn-pwzc-zero-cl-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-zero-cl i fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :induct (fn-zin-zero-cl i fn-zin-tab)
           :in-theory (e/d (fn-zin-zero-cl) (fn-zin-tput fn-oct-update fn-zin-len-of))))))

(local
 (defthm fn-pwzc-construct-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (mv-nth 1 (fn-zin-construct tb lb n fn-zin-tab))) *fn-zin-tab-octets*))
  :hints (("Goal" :in-theory (e/d (fn-zin-construct)
                           (fn-zin-tput fn-zin-zero-range fn-zin-zero-counts fn-zin-count-lens
                            fn-zin-offsets fn-zin-place-syms fn-zin-next-codes fn-zin-fill-lookup))))))

(local
 (defthm fn-pwzc-fixed-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-fixed-tables fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :in-theory (e/d (fn-zin-fixed-tables) (fn-zin-fill fn-zin-construct))))))

(local
 (defthm fn-pwzc-dynamic-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (mv-nth 1 (fn-zin-dynamic-tables hlit hdist fn-zin-tab))) *fn-zin-tab-octets*))
  :hints (("Goal" :in-theory (e/d (fn-zin-dynamic-tables) (fn-zin-construct))))))

(local
 (defthm fn-pwzc-emit-retains-history-length
  (implies (equal (len fn-zin-win) *fn-zin-win-octets*)
   (equal (len (mv-nth 2 (fn-zin-emit o fn-zin-st fn-zin-win fn-zin-out))) *fn-zin-win-octets*))
  :hints (("Goal" :in-theory (e/d (fn-zin-emit) (fn-oct-update fn-zin-emit-out))))))

(local
 (defthm fn-pwzc-actual-action-keeps-buffer-lengths
  (implies (and (equal (len fn-zin-win) *fn-zin-win-octets*)
                (equal (len fn-zin-tab) *fn-zin-tab-octets*))
   (let ((r (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
    (and (equal (len (mv-nth 2 r)) *fn-zin-win-octets*)
         (equal (len (mv-nth 3 r)) *fn-zin-tab-octets*))))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (fn-zin-act)
           (fn-zin-emit fn-zin-emit-out fn-zin-construct fn-zin-fixed-tables fn-zin-dynamic-tables fn-zin-fill fn-zin-zero-cl fn-zin-tput))))))

(local
 (defthm fn-pwzc-copy-retains-history-length
  (implies (equal (len fn-zin-win) *fn-zin-win-octets*)
   (equal (len (mv-nth 1 (fn-zin-copy k w d tout h fn-zin-win fn-zin-out))) *fn-zin-win-octets*))
  :hints (("Goal" :induct (fn-zin-copy k w d tout h fn-zin-win fn-zin-out)
           :in-theory (e/d (fn-zin-copy) (fn-oct-update))))))

(local
 (defthm fn-pwzc-match-retains-history-length
  (implies (equal (len fn-zin-win) *fn-zin-win-octets*)
   (equal (len (mv-nth 2 (fn-zin-match room fn-zin-st fn-zin-win fn-zin-out))) *fn-zin-win-octets*))
  :hints (("Goal" :in-theory (e/d (fn-zin-match) (fn-zin-copy))))))

(local
 (defthm fn-pwzc-literal-loop-retains-history-length
  (implies (equal (len fn-zin-win) *fn-zin-win-octets*)
   (equal (len (mv-nth 4 (fn-zin-lit-loop k bits nbits w tout limit fn-zin-tab fn-zin-win fn-zin-out))) *fn-zin-win-octets*))
  :hints (("Goal" :induct (fn-zin-lit-loop k bits nbits w tout limit fn-zin-tab fn-zin-win fn-zin-out)
           :in-theory (e/d (fn-zin-lit-loop) (fn-oct-update))))))

(local
 (defthm fn-pwzc-literals-retain-history-length
  (implies (equal (len fn-zin-win) *fn-zin-win-octets*)
   (equal (len (mv-nth 2 (fn-zin-lits room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))) *fn-zin-win-octets*))
  :hints (("Goal" :in-theory (e/d (fn-zin-lits) (fn-zin-lit-loop))))))

(local
 (defthm fn-pwzc-actual-step-keeps-buffer-lengths
  (implies (and (equal (len fn-zin-win) *fn-zin-win-octets*)
                (equal (len fn-zin-tab) *fn-zin-tab-octets*))
   (let ((r (fn-zin-step room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
    (and (equal (len (mv-nth 2 r)) *fn-zin-win-octets*)
         (equal (len (mv-nth 3 r)) *fn-zin-tab-octets*))))
  :hints (("Goal" :in-theory (e/d (fn-zin-step)
           (fn-zin-act fn-zin-match fn-zin-lits fn-zin-step-out-free))))))

(local
 (defthm fn-pwzc-actual-loop-keeps-buffer-lengths
  (implies (and (equal (len fn-zin-win) *fn-zin-win-octets*)
                (equal (len fn-zin-tab) *fn-zin-tab-octets*))
   (let ((r (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
    (and (equal (len (mv-nth 4 r)) *fn-zin-win-octets*)
         (equal (len (mv-nth 5 r)) *fn-zin-tab-octets*))))
  :hints (("Goal" :induct (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
           :in-theory (e/d (fn-zin-loop)
           (fn-zin-act fn-zin-step fn-zin-pull fn-zin-need fn-zin-step-out-free fn-zin-loop-counts))))))

(local
 (defthm fn-pwzc-actual-feed-cleared-windows-without-buffer-premises
 (let* ((r1 (fn-zin-feed b1 fn-zin-st ip end m fn-octets fn-zin-win fn-zin-tab nil))
        (r2 (fn-zin-feed b2 (mv-nth 3 r1) (mv-nth 2 r1) end l fn-octets
                        (mv-nth 4 r1) (mv-nth 5 r1) nil))
        (whole (fn-zin-feed b0 fn-zin-st ip end (+ (len (mv-nth 6 r1)) (nfix l))
                           fn-octets fn-zin-win fn-zin-tab nil)))
  (implies (and (equal (car r1) :full) (not (equal (car r2) :yield))
                (not (equal (car whole) :yield)))
   (equal (fn-pwz-semantic-observation whole)
          (list (car r2) (mv-nth 2 r2) (mv-nth 3 r2) (mv-nth 4 r2) (mv-nth 5 r2)
                (append (mv-nth 6 r1) (mv-nth 6 r2))))))
 :rule-classes nil
 :hints (("Goal"
          :use ((:instance fn-pwz-actual-basic-loop-general-cleared-windows (fn-zin-out nil))
                (:instance fn-pwzc-actual-loop-keeps-buffer-lengths (b b1) (lim m) (fn-zin-out nil)))
          :in-theory (e/d (fn-zin-feed fn-zin-window-ready-p fn-zin-tab-okp)
                          (fn-zin-loop fn-pwz-semantic-observation fn-zin-loop-keeps fn-zin-feed-unfolds fn-pwzc-actual-loop-keeps-buffer-lengths
                           fn-pwzc-actual-feed-full-tuple fn-pwzc-actual-loop-full-tuple nfix))))))

(defthm fn-pwzc-actual-stored-two-windows-without-buffer-premises
 (let* ((r1 (fn-pzw-stored-chunk requested1 remaining1 start end compressed expected
                                fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
        (r2 (fn-pzw-stored-chunk requested2 remaining2 (mv-nth 2 r1) end compressed expected
                                (mv-nth 3 r1) fn-octets (mv-nth 4 r1) (mv-nth 5 r1) (mv-nth 6 r1)))
        (credited (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin fn-zin-st)) fn-zin-st))
        (bound (min (nfix expected) (fn-pzw-stored-allowance compressed)))
        (l (fn-pzw-room bound (fn-zin-tout (mv-nth 3 r1))))
        (whole (fn-zin-feed b0 credited start end (+ (len (mv-nth 6 r1)) (nfix l))
                           fn-octets fn-zin-win fn-zin-tab nil)))
  (implies (and (equal (car r1) :full) (not (equal (car r2) :yield))
                (not (equal (car whole) :yield)))
   (equal (fn-pwz-semantic-observation whole)
          (list (car r2) (mv-nth 2 r2)
                (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin (mv-nth 3 r2))) (mv-nth 3 r2))
                (mv-nth 4 r2) (mv-nth 5 r2)
                (append (mv-nth 6 r1) (mv-nth 6 r2))))))
 :rule-classes nil
 :hints (("Goal"
          :use ((:instance fn-pwzc-actual-stored-chunk-recredited-full-tuple (requested requested1) (remaining remaining1))
                (:instance fn-pwzc-actual-two-stored-chunks-full-tuple)
                (:instance fn-pwzc-actual-feed-cleared-windows-without-buffer-premises
                 (b1 (fn-pzw-quantum requested1 remaining1)) (b2 (fn-pzw-quantum requested2 remaining2))
                 (ip start) (fn-zin-st (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin fn-zin-st)) fn-zin-st))
                 (m (fn-pzw-room (min (nfix expected) (fn-pzw-stored-allowance compressed)) (fn-zin-tout fn-zin-st)))
                 (l (fn-pzw-room (min (nfix expected) (fn-pzw-stored-allowance compressed))
                       (fn-zin-tout (mv-nth 3 (fn-pzw-stored-chunk requested1 remaining1 start end compressed expected fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))))))
          :in-theory (e/d (fn-pwz-semantic-observation)
                          (fn-pzw-stored-chunk fn-pzw-chunk fn-zin-feed fn-zin-loop
                           fn-pzw-room fn-pzw-quantum fn-pzw-stored-allowance nfix min
                           fn-zin-feed-unfolds fn-zin-loop-counts fn-zin-loop-keeps
                           fn-pwzc-actual-feed-full-tuple fn-pwzc-actual-loop-full-tuple)))))
