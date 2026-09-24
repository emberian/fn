; Teeth for books/store-budget: the carried transaction budget, its verdict at
; budget-1, budget and budget+1, and the count as the transaction namespace.
(in-package "ACL2")
(include-book "../../books/store-budget")
(include-book "std/testing/must-fail" :dir :system)

(defconst *sbudt-dev* (fn-bs-config-for-profile :development))
(defconst *sbudt-scale* (fn-bs-config-for-profile :scale))

; A Store-shaped value whose file kernel holds N committed records; the count
; reads nothing else.
(defun sbudt-store (n)
  (declare (xargs :guard (natp n)))
  (list nil nil
        (list :store-files :ready n nil (make-list n) nil nil nil 0)))

; The named profiles: 128 and 4096, for an article and for every smaller kind.
(assert-event (equal (fn-sbud-budget *sbudt-dev* :article) 128))
(assert-event (equal (fn-sbud-budget *sbudt-scale* :article) 4096))
(assert-event (equal (fn-sbud-budget *sbudt-dev* :consumer) 128))
; A value that is not a named profile has budget 0: nothing is admitted.
(assert-event (equal (fn-sbud-budget (list 1 2 3 4 1000 5) :article) 0))
(assert-event (equal (fn-sbud-budget nil :article) 0))

; budget-1, budget, budget+1 under the development profile.
(assert-event (equal (fn-sbud-used (sbudt-store 127)) 127))
(assert-event (equal (fn-sbud-verdict *sbudt-dev* :article (sbudt-store 127))
                     :admissible))
(assert-event (equal (fn-sbud-verdict *sbudt-dev* :article (sbudt-store 128))
                     :unaffordable))
(assert-event (equal (fn-sbud-verdict *sbudt-dev* :article (sbudt-store 129))
                     :unaffordable))
; The same 128th record is admissible under the scale profile, and its
; 4096th is not.
(assert-event (equal (fn-sbud-verdict *sbudt-scale* :article (sbudt-store 128))
                     :admissible))
(assert-event (equal (fn-sbud-verdict *sbudt-scale* :article (sbudt-store 4095))
                     :admissible))
(assert-event (equal (fn-sbud-verdict *sbudt-scale* :article (sbudt-store 4096))
                     :unaffordable))
; The verdict agrees with the host's former question at each point.
(assert-event (fn-bs-publication-admissiblep
               *sbudt-dev* 127 (fn-store-publication-ceiling :article)))
(assert-event (not (fn-bs-publication-admissiblep
                    *sbudt-dev* 128 (fn-store-publication-ceiling :article))))

; Headroom reads the same count.
(assert-event (equal (fn-sbud-headroom *sbudt-dev* (fn-sn-initial '("fn.letters") 10))
                     (list 0 128 0 10)))

; The namespace theorem: an initial kernel has no names, and its hypothesis
; is needed -- a record list numbered from 1 is not the namespace 0..n-1.
(assert-event (equal (fn-sbud-sequences
                      (fn-sf-records (fn-sn-files (fn-sn-initial '("fn.letters") 10))))
                     (fn-sbud-iota 0 0)))
(defconst *sbudt-misnumbered*
  (list nil nil
        (list :store-files :ready 1 nil
              (list (fn-record-make 1 0 0 "<a@example.invalid>" '(65)
                                    '("fn.letters") "p" "s" "r" 2 1))
              nil nil nil 0)))
(assert-event (not (equal (fn-sbud-sequences
                           (fn-sf-records (fn-sn-files *sbudt-misnumbered*)))
                          (fn-sbud-iota 0 (fn-sbud-used *sbudt-misnumbered*)))))
;; The namespace theorem without its fn-sf-statep hypothesis, at that store.
(must-fail
 (defthm sbudt-namespace-without-statep
   (equal (fn-sbud-sequences (fn-sf-records (fn-sn-files *sbudt-misnumbered*)))
          (fn-sbud-iota 0 (fn-sbud-used *sbudt-misnumbered*)))))
; The candidate theorem without fn-sf-candidatep: the misnumbered record,
; sequence 1, offered to an empty store, whose next sequence is 0.
(defconst *sbudt-sequence-one*
  (car (fn-sf-records (fn-sn-files *sbudt-misnumbered*))))
(assert-event (equal (fn-store-event-sequence *sbudt-sequence-one*) 1))
(assert-event (not (fn-sf-candidatep *sbudt-sequence-one* nil 1)))
(must-fail
 (defthm sbudt-any-record-takes-sequence-used
   (equal (fn-store-event-sequence *sbudt-sequence-one*)
          (fn-sbud-used (sbudt-store 0)))))
