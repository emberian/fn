; Teeth for books/packed-submission.lisp (lane chunked-body-2, B6b, PRF-928).
; The keystones (the round trips) have no hypothesis: their witnesses cover
; every arm (an octet list, a field that is not one,
; joinable groups, groups that are not, a transit record, a short record).

(in-package "ACL2")
(include-book "../../books/packed-submission")

(defconst *pst-octets* (append (make-list 700 :initial-element 97) '(0 255 13 10 0 0)))
(defconst *pst-groups* (list '(102 110 46 116 101 115 116) '(102 110 46 120)))

; -----------------------------------------------------------------------------
; The divide and conquer the host runs is the logical packing (the lemma
; fn-psub-pack-dc-is-pack, on the lengths the host calls it with).
(assert-event (equal (fn-psub-pack-dc *pst-octets* (len *pst-octets*))
                     (fn-bch-pack *pst-octets*)))
(assert-event (equal (fn-psub-pack-dc *pst-octets* 9) (fn-bch-pack (fn-psub-first *pst-octets* 9))))

; -----------------------------------------------------------------------------
; The octets field: packed to (LEN . N), one octet a byte; trailing zeros kept.
(defconst *pst-p* (fn-psub-pack-octets *pst-octets*))
(assert-event (equal (car *pst-p*) 706))
(assert-event (natp (cdr *pst-p*)))
(assert-event (equal (fn-psub-unpack-octets *pst-p*) *pst-octets*))
(assert-event (equal (fn-psub-packed-octets-len *pst-p*) 706))
; Not an octet list: kept.
(assert-event (equal (fn-psub-pack-octets '(300 1)) '(:raw 300 1)))
(assert-event (equal (fn-psub-unpack-octets (fn-psub-pack-octets '(300 1))) '(300 1)))
(assert-event (equal (fn-psub-unpack-octets (fn-psub-pack-octets nil)) nil))

; -----------------------------------------------------------------------------
; The groups: joinable names packed as one natural; otherwise kept.
(assert-event (equal (car (fn-psub-pack-groups *pst-groups*)) :g))
(assert-event (equal (fn-psub-unpack-groups (fn-psub-pack-groups *pst-groups*)) *pst-groups*))
(assert-event (equal (fn-psub-pack-groups '((97 44 98))) '(:raw (97 44 98))))
(assert-event (equal (fn-psub-unpack-groups (fn-psub-pack-groups '((97 44 98)))) '((97 44 98))))
(assert-event (equal (fn-psub-unpack-groups (fn-psub-pack-groups '(nil (97)))) '(nil (97))))

; -----------------------------------------------------------------------------
; The decision and the submission.
(defconst *pst-inj* (list :injected nil '(60 109 62) *pst-groups* *pst-octets*))
(defconst *pst-transit* (list :transit "peer" :ihave '(60 116 62) *pst-octets*))
(defconst *pst-sub* (list 7 3 nil *pst-inj* "login" 11))
(assert-event (not (equal (fn-psub-pack-sub *pst-sub*) *pst-sub*)))
(assert-event (equal (fn-psub-unpack-sub (fn-psub-pack-sub *pst-sub*)) *pst-sub*))
(assert-event (equal (nth 3 (fn-psub-pack-decision *pst-transit*)) '(60 116 62)))
(assert-event (equal (fn-psub-unpack-decision (fn-psub-pack-decision *pst-transit*)) *pst-transit*))
(assert-event (equal (fn-psub-unpack-sub (fn-psub-pack-sub '(7 3))) '(7 3)))
(assert-event (equal (fn-psub-unpack-sub (fn-psub-pack-sub (list 1 2 3 :witness)))
                     (list 1 2 3 :witness)))
; What the queue's credit charges: the packed octets, not sixteen an octet.
(assert-event (< (fn-psub-sub-heap (fn-psub-pack-sub *pst-sub*)) (* 2 706)))
