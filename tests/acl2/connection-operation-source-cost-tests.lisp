(in-package "ACL2")
(include-book "../../books/connection-operation-source-cost")
(include-book "../../books/connection-ticket-source-cost")
(include-book "../../books/connection-operation-operand-domain")
(include-book "allocation-turn-source-cost-tests")

; Literal complete antecedent/result witnesses. These synthetic descriptors
; exercise evaluator source semantics and never authorize an installation.
(defun copct-install (base per-input per-level domain quantum)
 (declare (xargs :guard t))
 (list :connection-operation-installation 7 '(runtime pool 1 2 3 4)
       '(source-only-test) domain '(4 4 4 4 1) base per-input per-level quantum))
(defun copct-evaluate (installation kind family address peer depth expected operators)
 (declare (xargs :guard t :verify-guards nil))
 (mv-let (word demand fuel body quantum) (fn-cop-evaluate installation kind family address peer depth)
  (let ((seen (fn-copc-evaluate installation kind family address peer depth)))
   (and (equal (list word demand fuel body quantum) expected)
        (equal (fn-atsc-value seen) expected)
        (equal (len (fn-atsc-ops seen)) operators)))))
(assert-event (copct-evaluate (copct-install 10 2 3 1000 8) :reader nil nil nil 0
                             '(:derived (4 4 4 4 1) 8 13 8) 11))
(assert-event (copct-evaluate (copct-install 10 2 3 1000 8) :peer nil nil '(1 2 3) 1
                             '(:derived (4 4 4 4 1) 16 22 8) 15))
(assert-event (copct-evaluate (copct-install 10 2 3 1000 8) :exposure :inet '(127 0 0 1) '(7 8) 0
                             '(:derived (4 4 4 4 1) 8 25 8) 18))
(assert-event (copct-evaluate (copct-install 10 2 3 1000 2) :peer nil nil '(1 2 3) 0
                             '(:refused nil 0 0 2) 2))
(assert-event (copct-evaluate (copct-install 10 2 3 1000 8) :peer nil nil '(1 256) 0
                             '(:refused nil 0 0 8) 1))
(assert-event (copct-evaluate (copct-install 10 2 3 1000 8) :exposure :inet '(1 2 3) nil 0
                             '(:refused nil 0 0 8) 0))
(assert-event (copct-evaluate (copct-install 10 2 3 7 8) :reader nil nil nil 0
                             '(:unsupported-runtime nil 0 0 0) 0))
(assert-event (copct-evaluate (copct-install 10 2 3 7 7) :reader nil nil nil 0
                             '(:unsupported-runtime nil 0 0 7) 1))
(assert-event (copct-evaluate (copct-install 10 1000 3 1000 8) :peer nil nil '(1 2) 0
                             '(:unsupported-runtime nil 0 0 8) 6))
(assert-event (copct-evaluate (copct-install 999 2 3 1000 8) :peer nil nil '(1) 0
                             '(:unsupported-runtime nil 0 0 8) 9))
(assert-event (copct-evaluate (copct-install 999 0 3 1000 8) :reader nil nil nil 0
                             '(:unsupported-runtime nil 0 0 8) 9))

(assert-event
 (equal (fn-atsc-ops (fn-copc-evaluate (copct-install 10 2 3 1000 8) :peer nil nil '(1 2 3) 1))
  '((:subtract (8 1)) (:subtract (7 1)) (:subtract (6 1))
    (:add (1 1)) (:floor (1000 2)) (:subtract (8 5))
    (:floor (1000 3)) (:floor (1000 2))
    (:multiply (2 3)) (:multiply (3 2)) (:subtract (1000 6))
    (:add (10 6)) (:subtract (1000 6)) (:add (16 6)) (:multiply (8 2)))))
(assert-event
 (and (equal (fn-atsc-value (fn-copc-octets-match '(1 2) '(1 2) 2)) t)
      (equal (fn-atsc-ops (fn-copc-octets-match '(1 2) '(1 2) 2))
             '((:subtract (2 1)) (:subtract (1 1))))))
(assert-event
 (and (not (fn-atsc-value (fn-copc-octets-match '(1 2) '(1 3) 2)))
      (equal (fn-atsc-ops (fn-copc-octets-match '(1 2) '(1 3) 2)) '((:subtract (2 1))))))
(assert-event
 (and (not (fn-atsc-value (fn-copc-octets-match '(1 2) '(1 2) 1)))
      (equal (fn-atsc-ops (fn-copc-octets-match '(1 2) '(1 2) 1)) '((:subtract (1 1))))))
(assert-event
 (let ((ledger '((8 8 8 8 8) (1 1 1 1 1) 1 nil (2 2 2 2 2))))
  (and (fn-cop-issuer-domainp ledger '(1 1 1 1 1) 100)
       (fn-atsc-value (fn-copc-issuer-domain ledger '(1 1 1 1 1) 100))
       (equal (len (fn-atsc-ops (fn-copc-issuer-domain ledger '(1 1 1 1 1) 100))) 40))))
; Each coordinate is material. Corrupt one charged coordinate to make the
; actual checked intermediate sum fail BEFORE oversized ADD construction.
(assert-event
 (let ((ledger '((8 8 8 8 8) (1 1 100 1 1) 1 nil (2 2 2 2 2))))
  (and (not (fn-cop-issuer-domainp ledger '(1 1 1 1 1) 100))
       (not (fn-atsc-value (fn-copc-issuer-domain ledger '(1 1 1 1 1) 100)))
       (equal (len (fn-atsc-ops (fn-copc-issuer-domain ledger '(1 1 1 1 1) 100))) 29))))

(assert-event (and (equal (fn-atsc-cells (fn-coptc-update 1 :phase '(a b c))) 2)
                  (equal (fn-atsc-ops (fn-coptc-update 1 :phase '(a b c))) '((:subtract (1 1))))))
(assert-event (and (equal (fn-atsc-cells (fn-coptc-update 15 :token '(a b c))) 16)
                  (equal (len (fn-atsc-ops (fn-coptc-update 15 :token '(a b c)))) 15)))
; Complete literal ordered operator witnesses for checked arithmetic, including
; refusal BEFORE an oversized intermediate would have been constructed.
(assert-event
 (and (not (fn-aed-add-roomp 999 2 1000))
      (equal (fn-atsc-ops (fn-atsc-add-room 999 2 1000)) '((:subtract (1000 2))))
      (fn-copod-operationsp (fn-atsc-ops (fn-atsc-add-room 999 2 1000)) 1000)))
(assert-event
 (and (not (fn-cop-times-roomp 1000 2 1000))
      (equal (fn-atsc-ops (fn-copc-times-room 1000 2 1000)) '((:floor (1000 2))))
      (fn-copod-operationsp (fn-atsc-ops (fn-copc-times-room 1000 2 1000)) 1000)))
(assert-event
 (let ((i (copct-install 10 2 3 1000 8)))
  (and (copct-evaluate i :peer nil nil '(1 2 3) 1 '(:derived (4 4 4 4 1) 16 22 8) 15)
       (fn-copod-operationsp (fn-atsc-ops (fn-copc-evaluate i :peer nil nil '(1 2 3) 1))
                            (fn-omk-at 4 i)))))
(assert-event
 (let ((i (copct-install 999 2 3 1000 8)))
  (and (copct-evaluate i :peer nil nil '(1) 0 '(:unsupported-runtime nil 0 0 8) 9)
       (fn-copod-operationsp (fn-atsc-ops (fn-copc-evaluate i :peer nil nil '(1) 0))
                            (fn-omk-at 4 i)))))
(assert-event
 (and (natp 5) (natp 100) (<= 5 100)
      (fn-copod-operationsp
       (fn-atsc-ops (fn-copc-vector-room '(2 2 2 2 2) '(1 1 100 1 1) '(1 1 1 1 1) 100 5)) 100)))
; Hypothesis removal: retain both natural-number predicates, omit fuel<=domain.
; The actual positive-fuel decrement (5-1) then has operand5 outside domain4.
(assert-event
 (and (natp 5) (natp 4) (not (<= 5 4))
      (not (fn-copod-operationsp
       (fn-atsc-ops (fn-copc-vector-room '(0 0 0 0 0) '(0 0 0 0 0) '(0 0 0 0 0) 4 5)) 4))))
; Hypothesis removal: retain nat domain, omit installed domain>=5. The actual
; five-coordinate traversal has the same out-of-envelope fuel operand.
(assert-event
 (let ((ledger '((0 0 0 0 0) (0 0 0 0 0) 0 nil (0 0 0 0 0))))
  (and (natp 4) (not (<= 5 4))
       (not (fn-copod-operationsp
        (fn-atsc-ops (fn-copc-issuer-domain ledger '(0 0 0 0 1) 4)) 4)))))
