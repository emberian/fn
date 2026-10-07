; article-stream-owner-bridge.lisp -- the catalog-started capture and the walk-started
; capture take the same READY step (lane article-index-2, 2026-10-07).
;
; books/article-stream-owner.lisp equates the selection start the owner's capture
; installs (the catalog's, fn-asto-selection-start-cat) with the archive walk at the
; selection's START.  The READY step runs the walk: fn-asto-selection-ready steps
; the selection state and reads only the outcome fields of the result (mode,
; group, number, phase, and the article when selected: fn-asx-outcome).  So two
; captures that differ in their selection only, and whose selections step to one
; outcome, take one READY step.
(in-package "ACL2")
(include-book "article-stream-owner")
(include-book "served-catalog-join-conns")
(defthm fn-asx-outcome-fields-agree
  (implies (equal (fn-asx-outcome a) (fn-asx-outcome b))
           (and (equal (fn-ast-at 1 a) (fn-ast-at 1 b))
                (equal (fn-ast-at 2 a) (fn-ast-at 2 b))
                (equal (fn-ast-at 3 a) (fn-ast-at 3 b))
                (equal (fn-ast-at 9 a) (fn-ast-at 9 b))
                (implies (eq (fn-ast-at 9 a) :selected)
                         (equal (fn-ast-at 5 a) (fn-ast-at 5 b)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-asx-outcome))))

(defthm fn-asto-selection-missing-of-mode-phase
  (implies (and (equal (fn-ast-at 1 a) (fn-ast-at 1 b))
                (equal (fn-ast-at 9 a) (fn-ast-at 9 b)))
           (equal (mv-list 3 (fn-asto-selection-missing
                              oc (fn-asto-capture-with-selection cap a sc)))
                  (mv-list 3 (fn-asto-selection-missing
                              oc (fn-asto-capture-with-selection cap b sc)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-asto-selection-missing fn-asto-capture-with-selection) ()))))

(defthm fn-asto-selection-ready-on-of-outcome
  (implies (and (equal (fn-asx-outcome n1) (fn-asx-outcome n2))
                (or (fn-ast-select-donep n1) (equal n1 n2)))
           (equal (mv-list 3 (fn-asto-selection-ready-on oc cap n1 fn-arena))
                  (mv-list 3 (fn-asto-selection-ready-on
                              oc (fn-asto-capture-with-selection cap s sc) n2 fn-arena))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-asto-selection-ready-on fn-ast-select-donep)
                           (fn-asx-outcome fn-asto-selection-missing
                            fn-asto-payload-preflight fn-ast-select-state))
           :use ((:instance fn-asx-outcome-fields-agree (a n1) (b n2))
                 (:instance fn-asto-selection-missing-of-mode-phase (a n1) (b n2) (sc nil))))))

(defthm fn-asto-ready-rest-of-selection-preflight
  (implies (equal (fn-ast-at 0 (fn-ast-at 2 cap)) :article-select)
           (equal (mv-list 3 (fn-asto-ready-rest oc id (cons (list :article-preflight cap) rest0)
                                                 f fn-arena))
                  (if (equal id (fn-own-conn-id (fn-ast-at 0 cap)))
                      (list (mv-nth 0 (fn-asto-selection-ready oc cap f fn-arena))
                            (mv-nth 1 (fn-asto-selection-ready oc cap f fn-arena))
                            (append (mv-nth 2 (fn-asto-selection-ready oc cap f fn-arena))
                                    rest0))
                    (list :stale oc (cons (list :article-preflight cap) rest0)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-asto-selection-ready fn-asto-capture-with-selection)
           :expand ((fn-asto-ready-rest oc id (cons (list :article-preflight cap) rest0) f fn-arena)))))

(defthm fn-asto-capture-with-selection-fields
  (and (equal (fn-ast-at 0 (fn-asto-capture-with-selection cap s sc)) (fn-ast-at 0 cap))
       (equal (fn-ast-at 2 (fn-asto-capture-with-selection cap s sc)) s))
  :hints (("Goal" :in-theory (enable fn-asto-capture-with-selection))))


(defthm fn-asto-ready-plan-step-of-selection-outcome
  (implies (and (equal (fn-splan-cur plan1) (fn-splan-cur plan2))
                (equal (fn-splan-rest plan1) (cons (list :article-preflight cap1) rest0))
                (equal (fn-splan-rest plan2) (cons (list :article-preflight cap2) rest0))
                (equal cap2 (fn-asto-capture-with-selection cap1 s2 (fn-ast-at 5 cap1)))
                (equal (fn-ast-at 0 (fn-ast-at 2 cap1)) :article-select)
                (equal (fn-ast-at 0 s2) :article-select)
                (equal id (fn-own-conn-id (fn-ast-at 0 cap1)))
                (equal n1 (fn-ast-select-step (fn-ast-at 2 cap1) (nfix f1)))
                (equal n2 (fn-ast-select-step s2 (nfix f2)))
                (equal (fn-asx-outcome n1) (fn-asx-outcome n2))
                (or (fn-ast-select-donep n1) (equal n1 n2)))
           (equal (mv-list 3 (fn-asto-ready-plan-step oc id plan1 f1 fn-arena))
                  (mv-list 3 (fn-asto-ready-plan-step oc id plan2 f2 fn-arena))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-asto-ready-plan-step fn-asto-selection-ready)
                           (fn-asx-outcome fn-ast-select-step fn-ast-select-donep
                            fn-asto-selection-ready-on fn-asto-capture-with-selection
                            fn-asto-ready-rest))
           :use ((:instance fn-asto-ready-rest-of-selection-preflight
                            (cap cap1) (id id) (f f1) (rest0 rest0))
                 (:instance fn-asto-ready-rest-of-selection-preflight
                            (cap cap2) (id id) (f f2) (rest0 rest0))
                 (:instance fn-asto-selection-ready-on-of-outcome
                            (cap cap1) (s s2) (sc (fn-ast-at 5 cap1)) (oc oc))))))
