; Bounds on the last qualifying entry of an ordered overview stream.
(in-package "ACL2")
(include-book "range")

(defconst *fn2-overview-range-key* '((group (:id group)) (number (:id group-number))))
; Above the first position past P, monotonicity excludes the rest of the stream.
(defthm fn2-range-seek-scan-after-position
 (implies (and (fn2-range-monotone-scan es prefix 3 last) (<= p last))
          (equal (fn2-range-seek-scan es prefix 2 p hi 3 acc) acc))
 :hints (("Goal" :induct (fn2-range-monotone-scan es prefix 3 last)
          :in-theory (disable fn2-range-prefixp nth))))

(local
 (defthm fn2-range-nfix-natural
 (implies (and (integerp x) (<= 0 x)) (equal (nfix x) x))))

; Once past the exclusive upper key, sortedness excludes the remaining rows.
(defthm fn2-range-seek-scan-above-hi
 (implies (and (natp group) (natp hi)
               (fn2-run-sorted-spec *fn2-overview-range-key* es)
               (consp es)
               (or (< group (nfix (caar es)))
                   (and (equal group (nfix (caar es))) (<= hi (nfix (cadar es))))))
          (equal (fn2-range-seek-scan es (list group) 2 p hi 3 acc) acc))
 :hints (("Goal" :induct (fn2-run-sorted-spec *fn2-overview-range-key* es)
          :expand ((:free (prefix) (fn2-range-seek-scan es prefix 2 p hi 3 acc)))
          :in-theory (disable nfix))))

(defthm fn2-range-seek-scan-preserves-floor
 (implies (and (natp group) (natp n) (< n acc)
               (fn2-run-sorted-spec *fn2-overview-range-key* es)
               (or (atom es) (< group (nfix (caar es)))
                   (and (equal group (nfix (caar es))) (<= n (nfix (cadar es))))))
          (< n (fn2-range-seek-scan es (list group) 2 p hi 3 acc)))
 :rule-classes nil
 :hints (("Goal" :induct (fn2-range-seek-scan es (list group) 2 p hi 3 acc)
          :expand ((:free (prefix) (fn2-range-seek-scan es prefix 2 p hi 3 acc)))
          :in-theory (disable nfix))))

(defthm fn2-range-seek-scan-natp
 (implies (natp acc) (natp (fn2-range-seek-scan es prefix nk p hi pidx acc)))
 :rule-classes :type-prescription
 :hints (("Goal" :induct (fn2-range-seek-scan es prefix nk p hi pidx acc)
          :in-theory (disable fn2-range-prefixp nth))))
