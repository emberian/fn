; Actual action observers: arithmetic site counts, not allocator adequacy.
; Borrowed setters, getters, ring/index/bit operations remain explicit residuals.
(in-package "ACL2")
(include-book "payload-action-source-trace")

(defthm fn-pat-emit-arithmetic-counts
 (let ((trace (cdr (fn-pat-zin-emit o fn-zin-st fn-zin-win fn-zin-out))))
  (and (equal (fn-pzt-count :multiply trace) 1)
       (equal (fn-pzt-count :negate trace) 0)
       (equal (fn-pzt-count :add trace)
              (if (< (fn-zin-bomb-limit fn-zin-st)
                     (1+ (fn-zin-tout fn-zin-st))) 2 4))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
   :in-theory (e/d (fn-pat-zin-emit fn-pzt-zin-bomb-limit fn-zin-bomb-limit)
     (fn-zin-set fn-zin-wrap fn-zin-out-append-octet fn-zin-win-put
      fn-zin-fld binary-append)))))

(defthm fn-pat-pull-arithmetic-counts
 (let ((trace (cdr (fn-pat-zin-pull ip fn-zin-st fn-octets))))
  (and (equal (fn-pzt-count :multiply trace) 0)
       (equal (fn-pzt-count :negate trace) 0)
       (equal (fn-pzt-count :add trace) 2)))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
   :in-theory (e/d (fn-pat-zin-pull)
     (fn-zin-set fn-zin-shift-in fn-octets-get fn-zin-fld binary-append)))))

(defun fn-pat-match-count (room fn-zin-st)
 (declare (xargs :stobjs fn-zin-st :guard t))
 (min (fn-zin-n fn-zin-st)
      (min (nfix room)
           (nfix (- (fn-zin-bomb-limit fn-zin-st)
                    (fn-zin-tout fn-zin-st))))))

(defthm fn-pat-match-arithmetic-counts
 (let* ((k (fn-pat-match-count room fn-zin-st))
        (trace (cdr (fn-pat-zin-match room fn-zin-st fn-zin-win fn-zin-out))))
  (and (equal (fn-pzt-count :multiply trace) 1)
       (equal (fn-pzt-count :negate trace)
              (if (zp k) 1 (+ 2 (nfix k))))
       (equal (fn-pzt-count :add trace)
              (if (zp k) 2 (+ 4 (* 2 (nfix k)))))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
   :use ((:instance fn-pzc-copy-counter-source-counts
           (k (fn-pat-match-count room fn-zin-st))
           (w (fn-zin-wpos fn-zin-st))
           (d (fn-zin-dist fn-zin-st))
           (tout (fn-zin-tout fn-zin-st))
           (h (fn-zin-preset fn-zin-st))))
   :in-theory (e/d (fn-pat-zin-match fn-pat-match-count fn-pzt-zin-bomb-limit fn-zin-bomb-limit)
     (fn-zin-set fn-zin-wrap fn-zin-out-append-octet fn-zin-win-put
      fn-zin-fld fn-pzc-copy fn-zin-copy binary-append)))))

(in-theory (disable fn-pat-match-count))
