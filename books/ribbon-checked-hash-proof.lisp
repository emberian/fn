; Two accepted pages with the same parent have the same physical BLAKE3 digest.
(in-package "ACL2")
(include-book "ribbon-parent-digest-proof")
(include-book "page-parent-octets")
(local (include-book "format-binds-seal-proof"))
(local (in-theory (current-theory 'fc-u32-reconstruct)))

(local
 (defthmd fn2-page-parent-byte-from-list
   (implies (and (equal (fn2-fc-context-hash 0 ctx) 136) (natp k) (< k 32))
            (equal (fn2-page-parent-byte k ctx ds)
                   (fn2-fc-word-byte (nth (floor k 4) (fn2-digest-list 136 ds)) (mod k 4))))
   :hints (("Goal" :in-theory (e/d (fn2-page-parent-byte fn2-fc-context-hash-word fn2-page-parent-word-from-list)
                                   (fn2-fc-word-byte fn2-fc-context-hash fn2-digest-word fn2-digest-list nth))))))

(local
 (defthm fn2-page-checked-octets-from-parent
   (let ((r (fn2-page-driver-call fn2-format-drive)))
     (implies (and (natp k) (natp n) (equal (+ k n) 32)
                   (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-idle*)
                   (equal (fn2-fc-context-hash 0 ctx) 136) (equal (car r) :ok))
              (equal (fc-result-octets k n (mv-nth 5 r))
                     (fn2-page-parent-octets k n (fn2-digest-list 136 ds)))))
   :rule-classes nil
   :hints (("Goal" :induct (fn2-page-parent-octets k n words)
            :expand ((:free (ds) (fc-result-octets k n ds)) (:free (words) (fn2-page-parent-octets k n words)))
            :in-theory (e/d ((:induction fn2-page-parent-octets))
                            (fn2-format-drive (:definition fn2-page-parent-octets) fc-result-octets fn2-fc-phase
                             fn2-fc-digest-byte fn2-fc-context-hash fn2-digest-list floor mod mv-nth)))
           ("Subgoal *1/1" :expand ((:free (ds) (fc-result-octets 32 0 ds)) (:free (ws) (fn2-page-parent-octets 32 0 ws))))
           ("Subgoal *1/2" :use fn2-page-drive-checks-every-parent-byte
            :in-theory (e/d (fn2-page-outside-digest fn2-page-parent-matchp fn2-page-parent-byte-from-list
                             fn2-page-drive-retains-parent)
                            (fn2-page-parent-progressp fn2-format-drive fn2-page-parent-octets fc-result-octets
                             fn2-page-parent-byte fn2-fc-digest-byte fn2-fc-phase fn2-fc-context-hash fn2-digest-list
                             fn2-fc-word-byte floor mod mv-nth))))))

(defthmd fn2-page-computed-answer-is-words
  (fn-b3-word-listp (fn2-page-hash-answer bytes))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                    '(fn2-page-hash-answer fn2-b3-output-words fn-b3-compress-shape)))))

(defthmd fn2-page-drive-returns-hash-words
  (let ((r (fn2-page-driver-call fn2-format-drive)))
    (implies (and (fn2-page-hash-statep bytes (fn2-page-hash-answer bytes) fc ds b3)
                  (fn2-hash-page-windowp pool) (fn-b3-octet-listp bytes)
                  (equal (len bytes) 65536) (fn2-b3-covers bytes 0 pool) (eq (car r) :ok))
             (equal (fn2-digest-list 125 (mv-nth 5 r)) (fn2-page-hash-answer bytes))))
  :hints (("Goal" :induct (fn2-page-driver-call fn2-format-drive)
           :expand (fn2-page-driver-call fn2-format-drive)
           :in-theory (e/d ((:induction fn2-format-drive) fc-format-keeps-pool fc-mv-zero fc-mv-cons)
                           (fn2-format-run fn2-page-hash-answer fn2-page-hash-statep
                            fn2-b3-covers fn2-hash-page-windowp mv-nth)))
          ("Subgoal *1/3" :use fn2-page-format-hashes-input)
          ("Subgoal *1/2" :use fn2-page-format-hashes-input)))

(defmacro fn2-page-checks-bytes (bytes fc ctx pool)
  `(and (equal (fn2-fc-phase 0 ,fc) *fn2-fc-phase-idle*)
        (equal (fn2-fc-context-hash 0 ,ctx) 136)
        (fn2-hash-page-windowp ,pool) (fn-b3-octet-listp ,bytes)
        (equal (len ,bytes) 65536) (fn2-b3-covers ,bytes 0 ,pool)))

(defmacro fn2-page-check-drive (fuel fc ctx b3 f pool ds)
  `(fn2-format-drive ,fuel 0 :page nil 0 1 0 65536 0 9 0 1 4096 ,fc ,ctx ,b3 ,f ,pool ,ds))

(local
 (defthm fn2-page-accepted-result-and-parent
   (let ((r (fn2-page-driver-call fn2-format-drive)))
     (implies (and (fn2-page-checks-bytes bytes fc ctx pool) (equal (car r) :ok))
              (and (equal (fc-result-octets 0 32 (mv-nth 5 r)) (fn2-page-parent-octets 0 32 (fn2-digest-list 136 ds)))
                   (fn-b3-word-listp (fn2-digest-list 125 (mv-nth 5 r)))
                   (equal (fn-b3-words-octets (fn2-digest-list 125 (mv-nth 5 r)))
                          (fn-blake3 (fn2-fc-covered :page bytes nil))))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-page-checked-octets-from-parent (k 0) (n 32))
                         fn2-page-drive-returns-hash-words fn2-page-computed-answer-is-words
                         fn2-page-drive-hashes-checked-input)
            :in-theory (union-theories (theory 'minimal-theory)
                         '(fn2-page-hash-statep (:e equal) (:e binary-+) (:e natp)))))))

(defthm fn2-page-accepted-pair-has-same-hash
  (let ((a (fn2-page-check-drive fuel fc ctx b3 f pool ds))
        (b (fn2-page-check-drive fuel other-fc other-ctx other-b3 other-f other-pool other-ds)))
    (implies (and (fn2-page-checks-bytes bytes fc ctx pool)
                  (fn2-page-checks-bytes other other-fc other-ctx other-pool)
                  (equal (fn2-digest-list 136 ds) (fn2-digest-list 136 other-ds))
                  (equal (car a) :ok) (equal (car b) :ok))
             (equal (fn-blake3 (fn2-fc-covered :page bytes nil)) (fn-blake3 (fn2-fc-covered :page other nil)))))
  :rule-classes nil
  :hints (("Goal" :use (fn2-page-accepted-result-and-parent
                        (:instance fn2-page-accepted-result-and-parent (bytes other) (fc other-fc) (ctx other-ctx)
                                   (b3 other-b3) (f other-f) (pool other-pool) (ds other-ds))
                        (:instance fc-result-octets-fix-words
                                   (da (mv-nth 5 (fn2-page-driver-call fn2-format-drive)))
                                   (db (mv-nth 5 (fn2-page-check-drive fuel other-fc other-ctx other-b3 other-f other-pool other-ds)))))
           :in-theory (theory 'minimal-theory))))
