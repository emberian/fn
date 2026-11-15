; Whole-row construction and reversal, using the actual bounded runner.
(in-package "ACL2")
(include-book "envelope-output-language")

(defthm fn2-eo-run-zero-unfolds
 (equal (fn2-envelope-output-run 0 fn2-envelope-output-state) fn2-envelope-output-state)
 :hints (("Goal" :in-theory (e/d (fn2-envelope-output-run) (fn2-envelope-output-step)))))
(defthm fn2-eo-run-one-unfolds
 (implies (not (equal (fn2-eo-phase fn2-envelope-output-state) 10))
  (equal (fn2-envelope-output-run 1 fn2-envelope-output-state)
         (fn2-envelope-output-step fn2-envelope-output-state)))
 :hints (("Goal" :in-theory (e/d (fn2-envelope-output-run) (fn2-envelope-output-step)))))

(defthm fn2-eo-phase9-step-unfolds
 (implies (equal (fn2-eo-phase fn2-envelope-output-state) 9)
  (equal (fn2-envelope-output-step fn2-envelope-output-state)
   (if (consp (fn2-eo-acc fn2-envelope-output-state))
    (update-fn2-eo-reversed
     (cons (car (fn2-eo-acc fn2-envelope-output-state))
           (fn2-eo-reversed fn2-envelope-output-state))
     (update-fn2-eo-acc (cdr (fn2-eo-acc fn2-envelope-output-state)) fn2-envelope-output-state))
    (update-fn2-eo-row (fn2-eo-reversed fn2-envelope-output-state)
     (update-fn2-eo-phase 7 fn2-envelope-output-state)))))
 :hints (("Goal" :in-theory (enable fn2-envelope-output-step))))

(defthm fn2-eo-phase9-finishes-row
 (implies
  (and (natp fuel)
       (equal (fn2-eo-phase fn2-envelope-output-state) 9)
       (equal fuel (+ 1 (len (fn2-eo-acc fn2-envelope-output-state)))))
  (let ((finished (fn2-envelope-output-run fuel fn2-envelope-output-state)))
   (and (equal (fn2-eo-phase finished) 7)
        (equal (fn2-eo-row finished)
               (revappend (fn2-eo-acc fn2-envelope-output-state)
                          (fn2-eo-reversed fn2-envelope-output-state))))))
 :rule-classes nil
 :hints (("Goal" :induct (fn2-envelope-output-run fuel fn2-envelope-output-state)
          :expand ((:free (fuel) (fn2-envelope-output-run fuel fn2-envelope-output-state)))
          :in-theory (e/d ((:induction fn2-envelope-output-run)) ((:definition fn2-envelope-output-run) fn2-envelope-output-step)))))
(defthm fn2-eo-phase8-step-unfolds
 (implies (equal (fn2-eo-phase fn2-envelope-output-state) 8)
  (equal (fn2-envelope-output-step fn2-envelope-output-state)
   (let ((scan (fn2-eo-scan fn2-envelope-output-state))
         (shifted (fn2-eo-shifted fn2-envelope-output-state))
         (suffix (fn2-eo-suffix-scan fn2-envelope-output-state))
         (prefix (fn2-eo-prefix fn2-envelope-output-state))
         (byte (fn2-eo-byte fn2-envelope-output-state))
         (acc (fn2-eo-acc fn2-envelope-output-state)))
    (if (consp scan)
     (update-fn2-eo-acc
      (cons (or (and prefix (car suffix)) (and (equal (car scan) byte) (car shifted))) acc)
      (update-fn2-eo-suffix-scan (cdr suffix)
       (update-fn2-eo-shifted (cdr shifted)
        (update-fn2-eo-scan (cdr scan) fn2-envelope-output-state))))
     (update-fn2-eo-reversed nil
      (update-fn2-eo-acc (cons (and prefix (car suffix)) acc)
       (update-fn2-eo-phase 9 fn2-envelope-output-state)))))))
 :hints (("Goal" :in-theory (enable fn2-envelope-output-step))))

; Alignment facts expose only projections; row membership remains opaque.
(local
 (defthm fn2-eo-aligned-row-head
  (implies (and (equal row (fn2-eo-language-row segments peer))
                (true-listp peer))
   (equal (car row) (fn2-envelope-output-language-p segments peer)))
  :hints (("Goal" :use ((:instance fn2-eo-language-row-head-unfolds))
           :in-theory (disable fn2-eo-language-row
                               fn2-eo-language-row-head-unfolds
                               fn2-envelope-output-language-p)))))

(local
 (defthm fn2-eo-revappend-row-cons-unfolds
  (implies (consp peer)
   (equal (revappend (fn2-eo-language-row segments peer) acc)
          (revappend (fn2-eo-language-row segments (cdr peer))
                     (cons (fn2-envelope-output-language-p segments peer) acc))))
  :hints (("Goal" :expand ((fn2-eo-language-row segments peer))
           :in-theory (e/d (revappend) (fn2-eo-language-row
                                        fn2-envelope-output-language-p))))))

(local
 (defthm fn2-eo-row-empty-unfolds
  (equal (fn2-eo-language-row segments nil)
         (list (fn2-envelope-output-language-p segments nil)))
  :hints (("Goal" :in-theory (e/d (fn2-eo-language-row)
                                 (fn2-envelope-output-language-p))))))

(local
 (defthm fn2-eo-language-byte-unfolds
  (implies (or (equal mode :exact) (equal mode :prefix))
   (equal (fn2-envelope-output-language-p
           (cons (cons mode (cons byte rest)) following) peer)
          (or (and (equal mode :prefix)
                   (fn2-envelope-output-language-p following peer))
              (and (consp peer) (equal byte (car peer))
                   (fn2-envelope-output-language-p
                    (cons (cons mode rest) following) (cdr peer))))))
  :hints (("Goal" :expand
           ((:free (mode byte rest following peer)
             (fn2-envelope-output-language-p
              (cons (cons mode (cons byte rest)) following) peer)))
           :in-theory (disable fn2-envelope-output-language-p)))))

; Keep row projections opaque throughout the complete scan induction.
(defthm fn2-eo-phase8-builds-whole-row
 (implies
  (and (natp fuel)
       (equal fuel (+ 1 (len (fn2-eo-scan fn2-envelope-output-state))))
       (equal (fn2-eo-phase fn2-envelope-output-state) 8)
       (fn2-eo-octets-p (fn2-eo-scan fn2-envelope-output-state))
       (unsigned-byte-p 8 (fn2-eo-byte fn2-envelope-output-state))
       (fn2-eo-octets-p rest) (fn2-eo-segments-p following)
       (equal (fn2-eo-suffix-scan fn2-envelope-output-state)
              (fn2-eo-language-row following (fn2-eo-scan fn2-envelope-output-state)))
       (equal (fn2-eo-shifted fn2-envelope-output-state)
        (cdr (fn2-eo-language-row
         (cons (cons (if (fn2-eo-prefix fn2-envelope-output-state) :prefix :exact) rest) following)
         (fn2-eo-scan fn2-envelope-output-state)))))
  (let ((finished (fn2-envelope-output-run fuel fn2-envelope-output-state)))
   (and (equal (fn2-eo-phase finished) 9)
        (equal (fn2-eo-reversed finished) nil)
        (equal (fn2-eo-acc finished)
         (revappend
          (fn2-eo-language-row
           (cons (cons (if (fn2-eo-prefix fn2-envelope-output-state) :prefix :exact)
                       (cons (fn2-eo-byte fn2-envelope-output-state) rest)) following)
           (fn2-eo-scan fn2-envelope-output-state))
          (fn2-eo-acc fn2-envelope-output-state))))))
 :rule-classes nil
 :hints (("Goal" :induct (fn2-envelope-output-run fuel fn2-envelope-output-state)
          :expand ((:free (fuel) (fn2-envelope-output-run fuel fn2-envelope-output-state)))
          :in-theory (e/d ((:induction fn2-envelope-output-run)) (fn2-eo-language-row fn2-envelope-output-language-p (:definition fn2-envelope-output-run) fn2-envelope-output-step)))))

(defthm fn2-eo-revappend-length
 (equal (len (revappend xs ys)) (+ (len xs) (len ys)))
 :hints (("Goal" :induct (revappend xs ys))))
(defthm fn2-eo-revappend-twice
 (implies (true-listp xs)
  (equal (revappend (revappend xs ys) zs)
         (revappend ys (append xs zs))))
 :hints (("Goal" :induct (revappend xs ys))))
(defthm fn2-eo-row-proper
 (true-listp (fn2-eo-language-row segments peer))
 :hints (("Goal" :induct (fn2-eo-language-row segments peer)
          :in-theory (e/d (fn2-eo-language-row) (fn2-envelope-output-language-p)))))
(defthm fn2-eo-row-length
 (equal (len (fn2-eo-language-row segments peer)) (+ 1 (len peer)))
 :hints (("Goal" :induct (fn2-eo-language-row segments peer)
          :in-theory (e/d (fn2-eo-language-row) (fn2-envelope-output-language-p)))))
(defthm fn2-eo-phase8-9-completes-semantic-row
 (implies
  (and (equal (fn2-eo-acc fn2-envelope-output-state) nil)
       (equal (fn2-eo-phase fn2-envelope-output-state) 8)
       (fn2-eo-octets-p (fn2-eo-scan fn2-envelope-output-state))
       (unsigned-byte-p 8 (fn2-eo-byte fn2-envelope-output-state))
       (fn2-eo-octets-p rest) (fn2-eo-segments-p following)
       (equal (fn2-eo-suffix-scan fn2-envelope-output-state)
              (fn2-eo-language-row following (fn2-eo-scan fn2-envelope-output-state)))
       (equal (fn2-eo-shifted fn2-envelope-output-state)
        (cdr (fn2-eo-language-row
         (cons (cons (if (fn2-eo-prefix fn2-envelope-output-state) :prefix :exact) rest) following)
         (fn2-eo-scan fn2-envelope-output-state)))))
  (let ((finished (fn2-envelope-output-run
                    (+ 3 (len (fn2-eo-scan fn2-envelope-output-state))
                         (len (fn2-eo-scan fn2-envelope-output-state)))
                    fn2-envelope-output-state)))
   (and (equal (fn2-eo-phase finished) 7)
        (equal (fn2-eo-row finished)
         (fn2-eo-language-row
          (cons (cons (if (fn2-eo-prefix fn2-envelope-output-state) :prefix :exact)
                      (cons (fn2-eo-byte fn2-envelope-output-state) rest)) following)
          (fn2-eo-scan fn2-envelope-output-state))))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn2-eo-phase8-builds-whole-row
         (fuel (+ 1 (len (fn2-eo-scan fn2-envelope-output-state)))))
        (:instance fn2-eo-phase9-finishes-row
         (fuel (+ 2 (len (fn2-eo-scan fn2-envelope-output-state))))
         (fn2-envelope-output-state
          (fn2-envelope-output-run (+ 1 (len (fn2-eo-scan fn2-envelope-output-state)))
                                   fn2-envelope-output-state)))
        (:instance fn2-envelope-output-run-resume
         (a (+ 1 (len (fn2-eo-scan fn2-envelope-output-state))))
         (b (+ 2 (len (fn2-eo-scan fn2-envelope-output-state))))))
  :in-theory (disable fn2-envelope-output-run fn2-envelope-output-step
                      fn2-eo-language-row fn2-envelope-output-language-p
                      fn2-eo-phase fn2-eo-row fn2-eo-scan fn2-eo-acc
                      fn2-eo-reversed fn2-eo-prefix fn2-eo-byte
                      fn2-eo-suffix-scan fn2-eo-shifted))))
