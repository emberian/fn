; Witnesses and teeth for books/store-history-marker.
(in-package "ACL2")
(include-book "../../books/store-history-marker")
(include-book "std/testing/must-fail" :dir :system)

(defconst *hmt-max* 4294967295)

; The codec: the marker after sequence 4 reads back as the count 5, and an
; allocation-frontier frame (FNSM kind 2) holding the same number is not a
; marker.
(assert-event (equal (fn-hm-decode (fn-hm-after-commit 4)) 5))
(assert-event (equal (fn-hm-open-verdict (list :present (fn-bs-frontier-encode-impl 5)) 5)
                     '(:refused :marker-damaged)))
(assert-event (equal (fn-hm-open-verdict '(:absent) 3) '(:admitted :unmarked)))
(assert-event (equal (fn-hm-open-verdict (list :present (fn-hm-after-commit 4)) 5)
                     '(:admitted :marked 5)))
(assert-event (equal (fn-hm-open-verdict (list :present (fn-hm-after-commit 4)) 9)
                     '(:admitted :marked 5)))
(assert-event (equal (fn-hm-open-verdict (list :present (fn-hm-after-commit 4)) 4)
                     '(:refused :history-short-of-marker 5)))
(assert-event (equal (fn-hm-after-commit *hmt-max*) nil))
(assert-event (equal (fn-hm-open-verdict (list :present (fn-hm-after-commit 4)) -1)
                     '(:refused :observation)))

; A reachable, non-degenerate history from a fresh store (count 0, no
; marker): an acknowledged commit, a burned reservation, a commit crashed
; after its marker rename with the old marker surviving, an uncertain
; publication whose record survived, a second acknowledged commit, then a
; burn and an uncertain publication that did not survive.
(defconst *hmt-st0* '(0 :absent))
(defconst *hmt-ops*
  '((:commit :marker-durable nil) (:burn) (:commit :marker-replaced nil)
    (:uncertain t) (:commit :marker-durable t) (:burn) (:uncertain nil)))
(assert-event (equal (car (fn-hm-run *hmt-ops* *hmt-st0*)) 4))
(assert-event (equal (fn-hm-marker-value (fn-hm-run *hmt-ops* *hmt-st0*)) 4))
; Keystone 1 on it: admitted, and at every prefix.
(assert-event (fn-hm-admittedp (fn-hm-run *hmt-ops* *hmt-st0*)))
(assert-event (fn-hm-admittedp (fn-hm-run (take 3 *hmt-ops*) *hmt-st0*)))
(assert-event (equal (fn-hm-marker-value (fn-hm-run (take 4 *hmt-ops*) *hmt-st0*)) 1))
; Finding 3's contrast.  The newest record (sequence 3) lost: refused, with
; the reason.  The burns after it: admitted (the frontier moved, the
; marker did not).
(assert-event (equal (fn-hm-open-verdict (cdr (fn-hm-run *hmt-ops* *hmt-st0*)) 3)
                     '(:refused :history-short-of-marker 4)))
(assert-event (equal (fn-hm-run '((:burn) (:uncertain nil) (:burn))
                                (fn-hm-run *hmt-ops* *hmt-st0*))
                     (fn-hm-run *hmt-ops* *hmt-st0*)))
; An unacknowledged survivor above the marker is not covered: after the
; crashed commit and the surviving uncertain record (count 3, marker 1),
; losing both is admitted.  That is the marker's stated scope.
(assert-event (equal (car (fn-hm-open-verdict
                           (cdr (fn-hm-run (take 4 *hmt-ops*) *hmt-st0*)) 1))
                     :admitted))

; Teeth.  Each hypothesis of a keystone gets one instance where every other
; hypothesis holds and the conclusion, evaluated, is false: the must-fail is
; of the conclusion's assertion at that instance.

; Keystone 1 (fn-hm-run-keeps-every-open-admitted).
;   admission of the start state: a marker above the records it reads.
(must-fail (assert-event (fn-hm-admittedp (fn-hm-run nil (list 1 :present (fn-hm-after-commit 4))))))
;   the uint32 count domain: the start is admitted, a commit at the last
;   count has no marker to write.
(assert-event (fn-hm-admittedp (cons *hmt-max* '(:absent))))
(must-fail (assert-event (fn-hm-admittedp (fn-hm-run '((:commit :marker-durable nil))
                                                     (cons *hmt-max* '(:absent))))))

; Keystone 2 (fn-hm-open-refuses-a-lost-acknowledged-record): END and its
; claimed verdict, as the theorem states them.
(defun hmt-k2-end (post st)
  (fn-hm-run post (fn-hm-step '(:commit :marker-durable nil) st)))
(defun hmt-k2-holds (post st k)
  (equal (fn-hm-open-verdict (cdr (hmt-k2-end post st)) k)
         (list :refused :history-short-of-marker
               (fn-hm-marker-value (hmt-k2-end post st)))))
; Witness: sequence 2 acknowledged, then a burn and a commit crashed before
; its rename; the open that sees 2 records refuses with the marker's count.
(assert-event (hmt-k2-holds '((:burn) (:commit :marker-created nil)) '(2 :absent) 2))
(assert-event (equal (fn-hm-open-verdict
                      (cdr (hmt-k2-end '((:burn) (:commit :marker-created nil)) '(2 :absent))) 2)
                     '(:refused :history-short-of-marker 3)))
;   k <= the acknowledged sequence: k = 3 (record 2 present) is admitted.
(must-fail (assert-event (hmt-k2-holds nil '(2 :absent) 3)))
;   natp k: a malformed count is refused for another reason.
(must-fail (assert-event (hmt-k2-holds nil '(2 :absent) -1)))
;   natp of the acknowledged sequence: no marker can name it.
(must-fail (assert-event (hmt-k2-holds nil '(x :absent) 0)))
;   the count domain: a later commit past uint32 damages the marker.
(must-fail (assert-event (hmt-k2-holds '((:commit :marker-durable nil))
                                       (cons (1- *hmt-max*) '(:absent)) 0)))
