(in-package "ACL2")
(include-book "../../books/history-page-buffers")

; Ground logical witnesses use the exact concrete constructor representation.
(defthm hpqt-each-region-positive
  (let* ((s (create-fn-hpb))
         (r0 (fn-hpq-put 0 17 s s s s s))
         (r1 (fn-hpq-put 1 18 s s s s s))
         (r2 (fn-hpq-put 2 19 s s s s s))
         (r3 (fn-hpq-put 3 20 s s s s s))
         (r4 (fn-hpq-put 4 21 s s s s s)))
    (and (natp 0) (< 0 5) (natp 1) (< 1 5)
         (natp 2) (< 2 5) (natp 3) (< 3 5) (natp 4) (< 4 5)
         (unsigned-byte-p 64 17) (unsigned-byte-p 64 21)
         (fn-hpbp (nth 1 r0)) (fn-hpbp (nth 5 r4))
         (equal (fn-hpb-epoch (nth 1 r0)) (fn-hpb-epoch s))
         (equal (fn-hpb-lease (nth 1 r0)) (fn-hpb-lease s))
         (not (equal 0 4)) (fn-hpbp s) (natp (fn-hpb-used s)) (< (fn-hpb-used s) 2048)
         (equal (car r0) :stored) (equal (car r1) :stored)
         (equal (car r2) :stored) (equal (car r3) :stored) (equal (car r4) :stored)
         (equal (fn-hpb-prefix (nth 1 r0)) '(17))
         (equal (fn-hpb-prefix (nth 2 r1)) '(18))
         (equal (fn-hpb-prefix (nth 3 r2)) '(19))
         (equal (fn-hpb-prefix (nth 4 r3)) '(20))
         (equal (fn-hpb-prefix (nth 5 r4)) '(21))
         (equal (nth 5 r0) s) (equal (nth 1 r4) s)))
 :rule-classes nil
 :hints (("Goal" :in-theory
          (e/d (fn-hpq-put fn-hpb-put fn-hpb-prefix fn-hpb-prefix-aux fn-hpb-used)
               ((:e fn-hpq-put) (:e fn-hpb-put) (:e fn-hpb-prefix))))))

; Corrupted state/domain witness; every retained hypothesis is explicit.
(defthm hpqt-remove-region-nat
 (let* ((region -1) (s (update-fn-hpb-used 0 (create-fn-hpb)))
        (r (fn-hpq-put region 42 s s s s s)))
  (and (not (natp region))
       (< region 5)
       (natp (fn-hpb-used s))
       (< (fn-hpb-used s) 2048)
       (not (and (equal (car r) :stored)
                 (equal (fn-hpb-prefix (mv-nth (+ 1 region) r))
                        (append (fn-hpb-prefix s) (list 42)))))))
 :rule-classes nil
 :hints (("Goal" :in-theory
          (e/d (fn-hpq-put fn-hpb-put fn-hpb-prefix fn-hpb-prefix-aux fn-hpb-used)
               ((:e fn-hpq-put) (:e fn-hpb-put) (:e fn-hpb-prefix))))))

; Corrupted state/domain witness; every retained hypothesis is explicit.
(defthm hpqt-remove-region-bound
 (let* ((region 5) (s (update-fn-hpb-used 0 (create-fn-hpb)))
        (r (fn-hpq-put region 42 s s s s s)))
  (and (natp region)
       (not (< region 5))
       (natp (fn-hpb-used s))
       (< (fn-hpb-used s) 2048)
       (not (and (equal (car r) :stored)
                 (equal (fn-hpb-prefix (mv-nth (+ 1 region) r))
                        (append (fn-hpb-prefix s) (list 42)))))))
 :rule-classes nil
 :hints (("Goal" :in-theory
          (e/d (fn-hpq-put fn-hpb-put fn-hpb-prefix fn-hpb-prefix-aux fn-hpb-used)
               ((:e fn-hpq-put) (:e fn-hpb-put) (:e fn-hpb-prefix))))))

; Corrupted state/domain witness; every retained hypothesis is explicit.
(defthm hpqt-remove-used-nat
 (let* ((region 0) (s (update-fn-hpb-used -1 (create-fn-hpb)))
        (r (fn-hpq-put region 42 s s s s s)))
  (and (natp region)
       (< region 5)
       (not (natp (fn-hpb-used s)))
       (< (fn-hpb-used s) 2048)
       (not (and (equal (car r) :stored)
                 (equal (fn-hpb-prefix (mv-nth (+ 1 region) r))
                        (append (fn-hpb-prefix s) (list 42)))))))
 :rule-classes nil
 :hints (("Goal" :in-theory
          (e/d (fn-hpq-put fn-hpb-put fn-hpb-prefix fn-hpb-prefix-aux fn-hpb-used)
               ((:e fn-hpq-put) (:e fn-hpb-put) (:e fn-hpb-prefix))))))

; Corrupted state/domain witness; every retained hypothesis is explicit.
(defthm hpqt-remove-capacity
 (let* ((region 0) (s (update-fn-hpb-used 2048 (create-fn-hpb)))
        (r (fn-hpq-put region 42 s s s s s)))
  (and (natp region)
       (< region 5)
       (natp (fn-hpb-used s))
       (not (< (fn-hpb-used s) 2048))
       (not (and (equal (car r) :stored)
                 (equal (fn-hpb-prefix (mv-nth (+ 1 region) r))
                        (append (fn-hpb-prefix s) (list 42)))))))
 :rule-classes nil
 :hints (("Goal" :in-theory
          (e/d (fn-hpq-put fn-hpb-put fn-hpb-prefix fn-hpb-prefix-aux fn-hpb-used)
               ((:e fn-hpq-put) (:e fn-hpb-put) (:e fn-hpb-prefix))))))
