(defthm fn-lgw-entry-len-of-window
  (implies (and (stringp s) (<= (fn-lgw-pos st) (length s)))
           (equal (fn-lgw-entry-len (subseq s (fn-lgw-pos st)
                                            (+ (fn-lgw-pos st) (fn-lgw-header-len st (length s))))
                                    st (length s))
                  (let* ((x (nthcdr (fn-lgw-pos st) (fn-lgd-octets s)))
                         (n (fn-lg-declared-len x)))
                    (and n (<= n (len x)) n))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-lg-declared-len fn-lgd-declared-len-of-header fn-lgd-octets
                               fn-lgd-header-at fn-lgd-declared-at subseq)
           :use ((:instance fn-lgd-declared-len-of-header
                            (x (nthcdr (fn-lgw-pos st) (fn-lgd-octets s))))))))
(defthm fn-lgw-slice-of-window
  (implies (and (stringp s) (natp pos) (natp end) (<= pos end) (<= end (length s)))
           (equal (fn-lgd-range (subseq s pos end) 0 (length (subseq s pos end)))
                  (fn-bs-take (- end pos) (nthcdr pos (fn-lgd-octets s)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-lgd-octets subseq fn-lgd-range)
           :use ((:instance fn-lgd-range-is-take (s (subseq s pos end)) (pos 0)
                            (n (length (subseq s pos end))))))))
(defthm fn-lgw-slice-is-take
  (implies (and (fn-lg-declared-len x) (<= (fn-lg-declared-len x) (len x)))
           (equal (fn-bs-take (fn-lg-declared-len x) x) (fn-lg-slice x)))
  :hints (("Goal" :in-theory (e/d (fn-lg-slice) (fn-lg-declared-len)))))
(defthm fn-lgw-nthcdr-nthcdr
  (implies (and (natp a) (natp b))
           (equal (nthcdr a (nthcdr b x)) (nthcdr (+ a b) x))))
(defthm fn-lgw-chain-broken-when-first-fails
  (implies (not (fn-lg-entry-okp (fn-lg-slice x) prev max))
           (equal (fn-lgs-chain-broken-p x prev unit max)
                  (fn-lgw-broken-slice-p (fn-lg-slice x) prev max)))
  :hints (("Goal" :expand ((fn-lg-scan x prev unit max) (fn-lg-scan-last x prev unit max))
           :in-theory (disable fn-lg-entry-okp fn-lg-slice fn-lgs-claimed-prev))))
(defthm fn-lgw-chain-broken-of-step
  (implies (fn-lg-entry-okp (fn-lg-slice x) prev max)
           (equal (fn-lgs-chain-broken-p x prev unit max)
                  (let* ((slice (fn-lg-slice x))
                         (step (+ (len slice) (fn-lg-pad-len (len slice) unit))))
                    (fn-lgs-chain-broken-p (nthcdr step x) (fn-lg-trailer slice) unit max))))
  :hints (("Goal" :expand ((fn-lg-scan x prev unit max) (fn-lg-scan-last x prev unit max))
           :in-theory (disable fn-lg-entry-okp fn-lg-slice fn-lgs-claimed-prev fn-lg-scan
                               fn-lg-scan-last fn-lg-trailer fn-lg-pad-len fn-lg-slice-record))))
(defthm fn-lgw-chain-broken-of-atom
  (implies (atom x) (not (fn-lgs-chain-broken-p x prev unit max)))
  :hints (("Goal" :in-theory (enable fn-lg-slice fn-lg-declared-len))))
(defun fn-lgw-next-fold (records next)
  (declare (xargs :guard t))
  (if (consp records)
      (fn-lgw-next-fold (cdr records) (fn-lgw-next-after-one (car records) next))
    (nfix next)))
(defthm fn-lgw-next-after-of-max
  (implies (natp b)
           (equal (fn-lgt-next-after records (max b (nfix a)))
                  (max b (fn-lgt-next-after records a)))))
(defthm fn-lgw-next-fold-is-next-after
  (equal (fn-lgw-next-fold records floor) (fn-lgt-next-after records floor))
  :hints (("Goal" :induct (fn-lgw-next-fold records floor))
          ("Subgoal *1/1" :use ((:instance fn-lgw-next-after-of-max
                                           (records (cdr records))
                                           (b (1+ (nfix (fn-lgt-txid (car records)))))
                                           (a floor))))))
(defthm fn-lgw-scan-of-atom
  (implies (atom x) (equal (fn-lg-scan x prev unit max) (cons nil 0)))
  :hints (("Goal" :expand ((fn-lg-scan x prev unit max))
           :in-theory (enable fn-lg-slice fn-lg-declared-len))))
(defthm fn-lgw-run-is-the-scan
  (implies (and (stringp s) (not (fn-lgw-stop st)) (<= (fn-lgw-pos st) (length s)))
           (let* ((x (nthcdr (fn-lgw-pos st) (fn-lgd-octets s)))
                  (scan (fn-lg-scan x (fn-lgw-prev st) unit max))
                  (run (fn-lgw-run s st unit max)))
             (and (equal (mv-nth 0 run) (car scan))
                  (equal (fn-lgw-pos (mv-nth 1 run)) (+ (fn-lgw-pos st) (cdr scan)))
                  (equal (fn-lgw-prev (mv-nth 1 run))
                         (fn-lg-scan-last x (fn-lgw-prev st) unit max))
                  (equal (fn-lgw-count (mv-nth 1 run)) (+ (fn-lgw-count st) (len (car scan))))
                  (equal (fn-lgw-next (mv-nth 1 run))
                         (fn-lgw-next-fold (car scan) (fn-lgw-next st)))
                  (equal (fn-lgw-broken (mv-nth 1 run))
                         (fn-lgs-chain-broken-p x (fn-lgw-prev st) unit max)))))
  :hints (("Goal" :induct (fn-lgw-run s st unit max)
           :expand ((fn-lgw-run s st unit max)
                    (fn-lg-scan (nthcdr (fn-lgw-pos st) (fn-lgd-octets s)) (fn-lgw-prev st) unit max)
                    (fn-lg-scan-last (nthcdr (fn-lgw-pos st) (fn-lgd-octets s)) (fn-lgw-prev st) unit max))
           :in-theory (disable fn-lg-entry-okp fn-lg-slice fn-lgs-claimed-prev fn-lg-scan
                               fn-lg-scan-last fn-lg-trailer fn-lg-pad-len fn-lg-slice-record
                               fn-lgd-octets subseq fn-lgd-range fn-lg-declared-len
                               fn-lgs-chain-broken-p fn-lgw-entry-len fn-lgw-header-len
                               fn-lgd-declared-at fn-lgw-broken-slice-p fn-lgt-txid))))
