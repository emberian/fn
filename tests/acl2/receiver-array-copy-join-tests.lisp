; Literal model teeth: not observations of native REPLACE.
(in-package "ACL2")
(include-book "../../books/receiver-array-copy-join")
(defconst *fn-rxaj-provider*
 (list '(9 8) (list '(:rx-capacity 1 0 4096) 0 4096)))
(defthm fn-rxaj-positive-model
 (let* ((source '(1 2 3)) (destination '(9 8 7 6))
        (observation (fn-rxac-model-observe 'source 'destination source destination
                                         2 3 t 'issued-context :copied)))
  (and (fn-rxac-domain-p 'source 'destination source destination 2 3 t)
       (equal (mv-nth 0 (fn-rxp-fill-range '(:rx-capacity 1 0 4096)
                         3 nil 16 *fn-rxaj-provider*)) :receive-copy)
       (fn-rxp-child-corr (list (nth 4 observation) (nth 5 observation))
          (mv-nth 2 (fn-rxp-fill-reference '(:rx-capacity 1 0 4096)
                         source nil 16 *fn-rxaj-provider*)))
       (equal (nth 4 observation) '(1 2 3 6))
       (equal (nth 5 observation) 3)))
 :rule-classes nil)
(defthm fn-rxaj-status-removal-model
 (let* ((source '(1 2 3)) (destination '(9 8 7 6))
        (observation (fn-rxac-model-observe 'source 'destination source destination
                                         2 3 t 'issued-context :copied)))
  (and (fn-rxac-domain-p 'source 'destination source destination 2 3 t)
       (not (equal (mv-nth 0 (fn-rxp-fill-range '(:rx-capacity 2 0 4096)
                         3 nil 16 *fn-rxaj-provider*)) :receive-copy))
       (not (fn-rxp-child-corr (list (nth 4 observation) (nth 5 observation))
          (mv-nth 2 (fn-rxp-fill-reference '(:rx-capacity 2 0 4096)
                         source nil 16 *fn-rxaj-provider*))))))
 :rule-classes nil)
(defthm fn-rxaj-domain-removal-model
 (let* ((source '(1 2 3)) (destination '(9 8))
        (observation (fn-rxac-model-observe 'source 'destination source destination
                                         2 3 t 'issued-context :copied)))
  (and (not (fn-rxac-domain-p 'source 'destination source destination 2 3 t))
       (equal (mv-nth 0 (fn-rxp-fill-range '(:rx-capacity 1 0 4096)
                         3 nil 16 *fn-rxaj-provider*)) :receive-copy)
       (not (fn-rxp-child-corr (list (nth 4 observation) (nth 5 observation))
          (mv-nth 2 (fn-rxp-fill-reference '(:rx-capacity 1 0 4096)
                         source nil 16 *fn-rxaj-provider*))))))
 :rule-classes nil)
; Literal named-assumption witness, distinct from the executable model teeth.
(defthm fn-rxaj-positive-conditional-assumption
 (let ((observation
         (fn-assume-rxac-observe 'source 'destination '(1 2 3) '(9 8 7 6)
                                 2 3 t 'issued-context :copied)))
  (and (fn-rxac-domain-p 'source 'destination '(1 2 3) '(9 8 7 6) 2 3 t)
       (equal (mv-nth 0 (fn-rxp-fill-range '(:rx-capacity 1 0 4096)
                       3 nil 16 *fn-rxaj-provider*)) :receive-copy)
       (fn-rxp-child-corr (list (nth 4 observation) (nth 5 observation))
         (mv-nth 2 (fn-rxp-fill-reference '(:rx-capacity 1 0 4096)
                    '(1 2 3) nil 16 *fn-rxaj-provider*)))))
 :hints (("Goal" :use ((:instance fn-rxp-assumed-array-copy-refines-reference
              (source-id 'source) (destination-id 'destination)
              (source '(1 2 3)) (destination '(9 8 7 6)) (old-fill 2)
              (association 'issued-context) (token '(:rx-capacity 1 0 4096))
              (limits nil) (fuel 16) (fn-rx-provider *fn-rxaj-provider*)))
          :in-theory (disable fn-rxp-child-corr fn-rxp-fill-reference)))
 :rule-classes nil)
