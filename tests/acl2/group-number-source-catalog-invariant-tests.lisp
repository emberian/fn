(in-package "ACL2")
(include-book "../../books/group-number-source-catalog-invariant")
(include-book "group-number-source-pending-tests")
(defun fn-tgnl-stage-run (fuel c)
  (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
  (if (or (zp fuel) (not (fn-gns-stage-cursorp c))
          (member-eq (fn-gns-at 0 c) '(:done :refused))) c
    (fn-tgnl-stage-run (1- fuel) (fn-gns-stage-step c))))
(defconst *tgnl-oldstage*
  (fn-tgnl-stage-run 600 (fn-gns-stage-begin (fn-held-numbers *tgnp-old*) 0 nil)))
(defconst *tgnl-root* (fn-gns-at 1 (fn-gns-stage-result *tgnl-oldstage*)))
(defconst *tgnl-assigned* (fn-tgnp-run 200 (fn-gns-pending-begin *tgnp-pending* *tgnl-root* 0)))
(defconst *tgnl-newstage*
  (fn-tgnl-stage-run 600 (fn-gns-stage-begin (fn-gns-at 5 *tgnl-assigned*) 1 *tgnl-root*)))
; Positive completes both the modeled insertion and actual completed-stage
; theorem antecedents/conclusion; loader old row supplies the immutable root.
(assert-event
 (and (fn-gns-stage-cursorp *tgnl-newstage*) (eq (fn-gns-at 0 *tgnl-newstage*) :done)
      (equal (fn-gns-stage-denotation *tgnl-newstage*)
        (fn-gns-memberships-root (fn-gns-assigned-memberships (fn-record-groups *tgnp-held*) *tgnl-root*) 1 *tgnl-root*))
      (fn-gns-groups-high-matchp (fn-record-groups *tgnp-held*) *tgnl-root* *tgnp-catalog*)
      (equal (fn-gns-group-value-high (fn-gns-group-get "fn.test" 0 0 *tgnl-root*))
             (fn-cat-group-high "fn.test" *tgnp-catalog*))
      (equal (fn-gns-group-value-high
               (fn-gns-group-get "fn.test" 0 0 (fn-gns-at 1 (fn-gns-stage-result *tgnl-newstage*))))
             (fn-cat-group-high "fn.test" (append *tgnp-catalog* (list (fn-cat-assign *tgnp-held* *tgnp-catalog*)))))))
; Runtime-built retained old/new trees keep old ordinal0 and insert ordinal1.
(assert-event
 (and (equal (fn-gnix-get 7 (fn-gns-group-value-root (fn-gns-group-get "fn.test" 0 0 *tgnl-root*))) '(:ordinal 0))
      (not (fn-gnix-get 8 (fn-gns-group-value-root (fn-gns-group-get "fn.test" 0 0 *tgnl-root*))))
      (equal (fn-gnix-get 7 (fn-gns-group-value-root (fn-gns-group-get "fn.test" 0 0 (fn-gns-at 2 *tgnl-newstage*)))) '(:ordinal 0))
      (equal (fn-gnix-get 8 (fn-gns-group-value-root (fn-gns-group-get "fn.test" 0 0 (fn-gns-at 2 *tgnl-newstage*)))) '(:ordinal 1))))
; Initial empty high correspondence is proved, not an input flag.
(assert-event
 (and (fn-gns-string-groupsp '("fn.test" "fn.other"))
      (fn-gns-groups-high-matchp '("fn.test" "fn.other") nil nil)
      (equal (fn-gns-group-value-high (fn-gns-group-get "fn.test" 0 0 nil))
             (fn-cat-group-high "fn.test" nil))))
; Removal of queried-point high correspondence for insertion theorem:
; new row has no groups, so all its group hypotheses hold vacuously, but the
; retained root's queried high disagrees with the old catalog and stays wrong.
(assert-event
 (let ((h (fn-tgnp-held nil)))
   (and (fn-gns-groups-high-matchp (fn-record-groups h) nil *tgnp-catalog*)
        (not (equal (fn-gns-group-value-high (fn-gns-group-get "fn.test" 0 0 nil))
                     (fn-cat-group-high "fn.test" *tgnp-catalog*)))
        (not (equal (fn-gns-group-value-high
                      (fn-gns-group-get "fn.test" 0 0
                        (fn-gns-memberships-root (fn-gns-assigned-memberships (fn-record-groups h) nil) 1 nil)))
                     (fn-cat-group-high "fn.test" (append *tgnp-catalog* (list (fn-cat-assign h *tgnp-catalog*)))))))))
; Corrupted-row removal of per-membership high/domain correspondence.
; The retained queried-point hypothesis holds; malformed prefix stops the
; insertion fold, while actual logical assignment still reaches later group.
(assert-event
 (let ((h (fn-tgnp-held '(7 "fn.test"))))
   (and (not (fn-gns-groups-high-matchp (fn-record-groups h) *tgnl-root* *tgnp-catalog*))
        (equal (fn-gns-group-value-high (fn-gns-group-get "fn.test" 0 0 *tgnl-root*))
               (fn-cat-group-high "fn.test" *tgnp-catalog*))
        (not (equal (fn-gns-group-value-high
                      (fn-gns-group-get "fn.test" 0 0
                        (fn-gns-memberships-root (fn-gns-assigned-memberships (fn-record-groups h) *tgnl-root*) 1 *tgnl-root*)))
                     (fn-cat-group-high "fn.test" (append *tgnp-catalog* (list (fn-cat-assign h *tgnp-catalog*)))))))))
; Actual-terminal theorem removal: :done, every other retained hypothesis.
(assert-event
 (let ((c (fn-gns-stage-begin (fn-gns-assigned-memberships (fn-record-groups *tgnp-held*) *tgnl-root*) 1 *tgnl-root*)))
   (and (not (eq (fn-gns-at 0 c) :done))
        (equal (fn-gns-stage-denotation c) (fn-gns-memberships-root (fn-gns-assigned-memberships (fn-record-groups *tgnp-held*) *tgnl-root*) 1 *tgnl-root*))
        (fn-gns-groups-high-matchp (fn-record-groups *tgnp-held*) *tgnl-root* *tgnp-catalog*)
        (equal (fn-gns-group-value-high (fn-gns-group-get "fn.test" 0 0 *tgnl-root*)) (fn-cat-group-high "fn.test" *tgnp-catalog*))
        (not (equal (fn-gns-group-value-high (fn-gns-group-get "fn.test" 0 0 (fn-gns-at 1 (fn-gns-stage-result c))))
                    (fn-cat-group-high "fn.test" (append *tgnp-catalog* (list (fn-cat-assign *tgnp-held* *tgnp-catalog*)))))))))
; Corrupted-schedule removal: completed cursor belongs to the old row.
(assert-event
 (let ((c *tgnl-oldstage*))
   (and (eq (fn-gns-at 0 c) :done)
        (not (equal (fn-gns-stage-denotation c) (fn-gns-memberships-root (fn-gns-assigned-memberships (fn-record-groups *tgnp-held*) *tgnl-root*) 1 *tgnl-root*)))
        (fn-gns-groups-high-matchp (fn-record-groups *tgnp-held*) *tgnl-root* *tgnp-catalog*)
        (equal (fn-gns-group-value-high (fn-gns-group-get "fn.test" 0 0 *tgnl-root*)) (fn-cat-group-high "fn.test" *tgnp-catalog*))
        (not (equal (fn-gns-group-value-high (fn-gns-group-get "fn.test" 0 0 (fn-gns-at 1 (fn-gns-stage-result c))))
                    (fn-cat-group-high "fn.test" (append *tgnp-catalog* (list (fn-cat-assign *tgnp-held* *tgnp-catalog*)))))))))
; Corrupted-row removal: original memberships/domain correspondence.
(assert-event
 (let ((h (fn-tgnp-held '(7 "fn.test"))) (c *tgnl-oldstage*))
   (and (eq (fn-gns-at 0 c) :done)
        (equal (fn-gns-stage-denotation c) (fn-gns-memberships-root (fn-gns-assigned-memberships (fn-record-groups h) *tgnl-root*) 1 *tgnl-root*))
        (not (fn-gns-groups-high-matchp (fn-record-groups h) *tgnl-root* *tgnp-catalog*))
        (equal (fn-gns-group-value-high (fn-gns-group-get "fn.test" 0 0 *tgnl-root*)) (fn-cat-group-high "fn.test" *tgnp-catalog*))
        (not (equal (fn-gns-group-value-high (fn-gns-group-get "fn.test" 0 0 (fn-gns-at 1 (fn-gns-stage-result c))))
                    (fn-cat-group-high "fn.test" (append *tgnp-catalog* (list (fn-cat-assign h *tgnp-catalog*)))))))))
; Actual-terminal removal: retained queried-point high correspondence.
(assert-event
 (let ((h (fn-tgnp-held nil)) (c (fn-tgnl-stage-run 4 (fn-gns-stage-begin nil 1 nil))))
   (and (eq (fn-gns-at 0 c) :done)
        (equal (fn-gns-stage-denotation c) (fn-gns-memberships-root (fn-gns-assigned-memberships (fn-record-groups h) nil) 1 nil))
        (fn-gns-groups-high-matchp (fn-record-groups h) nil *tgnp-catalog*)
        (not (equal (fn-gns-group-value-high (fn-gns-group-get "fn.test" 0 0 nil)) (fn-cat-group-high "fn.test" *tgnp-catalog*)))
        (not (equal (fn-gns-group-value-high (fn-gns-group-get "fn.test" 0 0 (fn-gns-at 1 (fn-gns-stage-result c))))
                    (fn-cat-group-high "fn.test" (append *tgnp-catalog* (list (fn-cat-assign h *tgnp-catalog*)))))))))
; Removal of initial group typing: no other retained hypotheses.
(assert-event
 (and (not (fn-gns-string-groupsp '(7)))
      (not (fn-gns-groups-high-matchp '(7) nil nil))))
