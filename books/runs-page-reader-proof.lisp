; Shared proof events for byte-consuming codecs used in run page searches.
(in-package "ACL2")
(include-book "layout")
(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

(defthmd fn2-run-layout-byte-naturals
  (let ((res (fn2-layout-byte k pos v high size payload byte)))
    (implies (and (natp pos) (natp v) (natp high) (natp size)
                  (natp payload) (unsigned-byte-p 8 byte))
             (and (natp (mv-nth 1 res)) (natp (mv-nth 2 res))
                  (natp (mv-nth 3 res)) (natp (mv-nth 4 res)))))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (e/d (fn2-layout-byte) (fn2-layout-kind-code mod)))))

(defthmd fn2-run-reader-octet
 (let ((byte (mv-nth 1 (fn2-pool-read slot gen next pk ps pg pool))))
   (implies (and (fn2-poolp pool) (fn2-pool-wfp pool))
            (and (unsigned-byte-p 8 byte) (equal (mod (nfix byte) 256) byte))))
 :hints (("Goal" :in-theory (enable fn2-pool-read))))

(defthmd fn2-run-reader-active-phase
  (implies (and (natp phase) (natp count) (<= phase count) (not (equal phase count)))
           (< phase count)))

(defthmd fn2-run-reader-nfix (implies (natp x) (equal (nfix x) x)))
(defthmd fn2-run-reader-successor-natural (implies (natp x) (natp (1+ x))))
(defthmd fn2-run-reader-offset-natural
  (implies (and (natp base) (natp phase)) (natp (+ base phase))))
(defthmd fn2-run-reader-next-in-layout
  (implies (and (natp phase) (natp count) (< phase count)) (<= (+ 1 phase) count)))
(defthmd fn2-run-reader-mv-selector
  (implies (natp i) (equal (mv-nth i (cons a b)) (if (zp i) a (mv-nth (1- i) b)))))
(defthmd fn2-run-reader-first-result (equal (mv-nth 0 x) (car x)))
(defthmd fn2-run-reader-byte-status
  (not (equal (car (fn2-layout-byte k pos v high size payload byte)) :ok))
  :hints (("Goal" :in-theory (e/d (fn2-layout-byte) (fn2-layout-kind-code ash mod)))))
(defthmd fn2-run-reader-next-base
  (equal (+ (+ base phase) 1) (+ base (+ 1 phase))))

(defthmd fn2-run-reader-start-coordinates
  (let ((after (fn2-codec-save base 0 0 0 0 0 0 0 0 f)))
    (implies (and (natp base) (< base (fn2-fields-rows f)))
             (and (equal (fn2-fields-decode-phase base after) 0)
                  (equal (fn2-fields-decode-pos base after) 0)
                  (equal (fn2-fields-decode-acc base after) 0)
                  (equal (fn2-fields-decode-high base after) 0)
                  (equal (fn2-fields-decode-size base after) 0)
                  (equal (fn2-fields-decode-ref base after) 0)
                  (equal (fn2-fields-decode-payload base after) 0)
                  (equal (fn2-fields-decode-next base after) 0))))
  :hints (("Goal" :in-theory
           (e/d (fn2-codec-save nth-update-nth
                 fn2-fields-decode-phase fn2-fields-set-decode-phase update-fn2-fields-decode-phase$ai
                 fn2-fields-decode-pos fn2-fields-set-decode-pos update-fn2-fields-decode-pos$ai
                 fn2-fields-decode-acc fn2-fields-set-decode-acc update-fn2-fields-decode-acc$ai
                 fn2-fields-decode-high fn2-fields-set-decode-high update-fn2-fields-decode-high$ai
                 fn2-fields-decode-size fn2-fields-set-decode-size update-fn2-fields-decode-size$ai
                 fn2-fields-decode-ref fn2-fields-set-decode-ref update-fn2-fields-decode-ref$ai
                 fn2-fields-decode-payload fn2-fields-set-decode-payload update-fn2-fields-decode-payload$ai
                 fn2-fields-decode-next fn2-fields-set-decode-next update-fn2-fields-decode-next$ai)
                (nth update-nth fn2-fields-rows)))))

(defmacro fn2-run-scan-agreement (actual model base done)
  `(and (equal (car ,actual) :ok)
        (equal (mv-nth 1 ,actual) (mv-nth 8 ,model))
        (equal (mv-nth 2 ,actual)
               (fn2-codec-save ,base ,done 0 0 0 0 0 0 (mv-nth 8 ,model)
                               (mv-nth 9 ,model)))))

(defun fn2-run-reader-phase-cases (n)
  (declare (xargs :guard (natp n)))
  (if (zp n) nil
    (cons (list 'equal 'phase (1- n)) (fn2-run-reader-phase-cases (1- n)))))

; Each scanner consumes one byte per transition. The phase equations also
; check that the selected codec has no zero-width fields.
(defmacro fn2-run-page-reader-events (name phases)
  (let* ((layout (fn2-codec-constant name ""))
         (done (fn2-codec-phase name 'done))
         (index (fn2-codec-symbol name "-FIELD-INDEX"))
         (empty (fn2-codec-symbol name "-EMPTY-P"))
         (next-phase (fn2-codec-symbol name "-NEXT-PHASE"))
         (byte-step (fn2-codec-symbol name "-BYTE"))
         (scan (fn2-codec-symbol name "-SCAN"))
         (start (fn2-codec-symbol name "-START"))
         (decode (fn2-codec-symbol name "-DECODE"))
         (decode-step (fn2-codec-symbol name "-DECODE-STEP"))
         (phase-law (fn2-codec-symbol name "-PHASE-LAYOUT"))
         (scan-law (fn2-codec-symbol name "-SCAN-REFINES-LAYOUT"))
         (decode-law (fn2-codec-symbol name "-DECODE-REFINES-LAYOUT"))
         (actual `(,scan fuel base phase pos v high size ref payload next slot gen end pk ps pg f pool))
         (model `(fn2-layout-scan (nthcdr phase ,layout) fuel (+ base phase)
                                  pos v high size ref payload next slot gen end pk ps pg f pool)))
    `(encapsulate ()
       (local
        (defthm ,phase-law
          (implies (and (natp phase) (< phase ,done))
                   (let ((tail (nthcdr phase ,layout)))
                     (and (consp tail) (equal (,empty phase) nil)
                          (not (equal (cadar tail) '(:zero 0)))
                          (equal (,index phase) phase)
                          (equal (,next-phase phase) (1+ phase))
                          (equal (cdr tail) (nthcdr (1+ phase) ,layout))
                          (equal (,byte-step phase pos v high size payload byte)
                                 (fn2-layout-byte (cadar tail) pos v high size payload byte)))))
          :hints (("Goal" :cases ,(fn2-run-reader-phase-cases phases)
                   :in-theory (e/d (,byte-step fn2-layout-byte ,empty ,index ,next-phase)
                                   (ash nthcdr mod fn2-layout-kind-code))))))
       (local
        (defthm ,scan-law
          (implies (and (fn2-poolp pool) (fn2-pool-wfp pool) (natp base) (natp phase)
                        (<= phase ,done) (natp pos) (natp v) (natp high) (natp size) (natp payload)
                        (eq (mv-nth 0 ,model) :ok))
                   (fn2-run-scan-agreement ,actual ,model base ,done))
          :rule-classes nil
          :hints (("Goal" :induct ,actual :do-not '(preprocess) :case-split-limitations (80 2)
                   :expand (,actual ,model)
                   :in-theory (set-difference-theories
                               (union-theories (theory 'minimal-theory)
                                 '(,phase-law (:induction ,scan) fn2-run-layout-byte-naturals
                                   fn2-run-reader-octet fn2-run-reader-active-phase
                                   fn2-run-reader-nfix fn2-run-reader-successor-natural
                                   fn2-run-reader-offset-natural fn2-run-reader-next-in-layout
                                   fn2-run-reader-byte-status fn2-run-reader-first-result
                                   fn2-run-reader-next-base fn2-run-reader-mv-selector
                                   atom eq eql not car-cons cdr-cons member-equal
                                   (:e mv-nth) (:e nthcdr) (:e equal) (:e not) (:e consp)
                                   (:e zp) (:e natp) (:e binary-+) (:e unary--) (:e <)
                                   (:e car) (:e cdr) (:e member-equal)))
                               '((:definition mv-nth))))
                  ("Subgoal *1/1"
                   :expand ((,scan fuel base ,done pos v high size ref payload next slot gen end pk ps pg f pool)
                            (fn2-layout-scan nil fuel (+ base ,done) pos v high size ref payload
                                             next slot gen end pk ps pg f pool))))))
       (defthm ,decode-law
         (let* ((initial (,start base f))
                (model (fn2-layout-scan ,layout *fn2-codec-decode-fuel* base
                                        0 0 0 0 0 0 off slot gen end pk ps pg initial pool))
                (read (,decode base slot gen off end pk ps pg f pool)))
           (implies (and (fn2-poolp pool) (fn2-pool-wfp pool) (natp base)
                         (< base (fn2-fields-rows f)) (unsigned-byte-p 32 off) (unsigned-byte-p 32 end)
                         (<= off end) (eq (fn2-layout-range-code slot gen off end nil pk ps pg pool) :ok)
                         (eq (car model) :ok))
                    (fn2-run-scan-agreement read model base ,done)))
         :rule-classes nil
         :hints (("Goal" :use ((:instance ,scan-law (fuel *fn2-codec-decode-fuel*) (phase 0)
                                          (pos 0) (v 0) (high 0) (size 0) (ref 0) (payload 0) (next off)
                                          (f (,start base f))))
                  :in-theory (e/d (,decode ,decode-step ,start fn2-run-reader-start-coordinates)
                                  (fn2-layout-scan fn2-codec-save fn2-layout-range-code ,scan
                                   fn2-poolp fn2-pool-wfp fn2-fields-rows unsigned-byte-p
                                   fn2-fields-decode-phase fn2-fields-decode-pos fn2-fields-decode-acc
                                   fn2-fields-decode-high fn2-fields-decode-size fn2-fields-decode-ref
                                   fn2-fields-decode-payload fn2-fields-decode-next))))))))

(defmacro fn2-run-prove-page-reader (name)
  `(make-event (value (list 'fn2-run-page-reader-events ',name (len ,(fn2-codec-constant name ""))))))

