(in-package "ACL2")
(include-book "../../books/payload-table-runtime-workspace")

; Positive from actual reset/pull/header-produced table, full antecedent.
(defthm pawtw-actual-produced-table-complete-positive
 (let* ((initial (fn-zin-reset (create-fn-zin-st)))
        (st (fn-zin-pull 0 initial '(3)))
        (win (make-list 65536 :initial-element 0))
        (tab (make-list 3494 :initial-element 0))
        (r (fn-zin-act st win tab nil))
        (fn-zin-tab (mv-nth 3 r)) (e 1746))
  (and (fn-zin-window-ready-p win) (fn-zin-tab-okp tab)
       (equal (mv-nth 0 r) nil) (equal (fn-zin-mode (mv-nth 1 r)) 8)
       (natp e) (< e *fn-zin-tab-entries*)
       (fn-zin-tab-okp fn-zin-tab) (fn-cbor-octet-listp fn-zin-tab)
       (fn-cbor-octetp (fn-zin-tab-get (* 2 e) fn-zin-tab))
       (fn-cbor-octetp (fn-zin-tab-get (+ 1 (* 2 e)) fn-zin-tab))
       (natp (* 2 e)) (< (* 2 e) *fn-zin-tab-octets*)
       (natp (+ 1 (* 2 e))) (< (+ 1 (* 2 e)) *fn-zin-tab-octets*)
       (natp (* 256 (fn-zin-tab-get (+ 1 (* 2 e)) fn-zin-tab)))
       (<= (* 256 (fn-zin-tab-get (+ 1 (* 2 e)) fn-zin-tab)) 65280)
       (natp (fn-zin-tget e fn-zin-tab)) (< (fn-zin-tget e fn-zin-tab) 65536)
       (equal (fn-zin-tget e fn-zin-tab) 2591)
       (fn-srp-table-object-domain-p e (fn-zin-tab-get (* 2 e) fn-zin-tab)
          (fn-zin-tab-get (+ 1 (* 2 e)) fn-zin-tab) (fn-zin-tab-len fn-zin-tab))))
 :rule-classes nil)

; Corrupted logical representation: complete literal premise removal.
(defthm pawtw-remove-natural
 (let ((e -1) (fn-zin-tab (make-list 3494 :initial-element 0)))
  (and (not (natp e))
       (< e *fn-zin-tab-entries*)
       (fn-zin-tab-okp fn-zin-tab)
       (fn-cbor-octetp (fn-zin-tab-get (* 2 e) fn-zin-tab))
       (fn-cbor-octetp (fn-zin-tab-get (+ 1 (* 2 e)) fn-zin-tab))
       (not (fn-srp-table-object-domain-p
         e (fn-zin-tab-get (* 2 e) fn-zin-tab)
         (fn-zin-tab-get (+ 1 (* 2 e)) fn-zin-tab)
         (fn-zin-tab-len fn-zin-tab)))))
 :rule-classes nil)

; Corrupted logical representation: complete literal premise removal.
; Corrupted logical representation: complete literal premise removal.
(defthm pawtw-remove-table-shape
 (let ((e 0) (fn-zin-tab '(0 0)))
  (and (natp e)
       (< e *fn-zin-tab-entries*)
       (not (fn-zin-tab-okp fn-zin-tab))
       (fn-cbor-octetp (fn-zin-tab-get (* 2 e) fn-zin-tab))
       (fn-cbor-octetp (fn-zin-tab-get (+ 1 (* 2 e)) fn-zin-tab))
       (not (fn-srp-table-object-domain-p
         e (fn-zin-tab-get (* 2 e) fn-zin-tab)
         (fn-zin-tab-get (+ 1 (* 2 e)) fn-zin-tab)
         (fn-zin-tab-len fn-zin-tab)))))
 :rule-classes nil)

; Corrupted logical representation: complete literal premise removal.
(defthm pawtw-remove-low-octet
 (let ((e 0) (fn-zin-tab (cons 65536 (make-list 3493 :initial-element 0))))
  (and (natp e)
       (< e *fn-zin-tab-entries*)
       (fn-zin-tab-okp fn-zin-tab)
       (not (fn-cbor-octetp (fn-zin-tab-get (* 2 e) fn-zin-tab)))
       (fn-cbor-octetp (fn-zin-tab-get (+ 1 (* 2 e)) fn-zin-tab))
       (not (fn-srp-table-object-domain-p
         e (fn-zin-tab-get (* 2 e) fn-zin-tab)
         (fn-zin-tab-get (+ 1 (* 2 e)) fn-zin-tab)
         (fn-zin-tab-len fn-zin-tab)))))
 :rule-classes nil)

; Corrupted logical representation: complete literal premise removal.
(defthm pawtw-remove-high-octet
 (let ((e 0) (fn-zin-tab (cons 0 (cons 256 (make-list 3492 :initial-element 0)))))
  (and (natp e)
       (< e *fn-zin-tab-entries*)
       (fn-zin-tab-okp fn-zin-tab)
       (fn-cbor-octetp (fn-zin-tab-get (* 2 e) fn-zin-tab))
       (not (fn-cbor-octetp (fn-zin-tab-get (+ 1 (* 2 e)) fn-zin-tab)))
       (not (fn-srp-table-object-domain-p
         e (fn-zin-tab-get (* 2 e) fn-zin-tab)
         (fn-zin-tab-get (+ 1 (* 2 e)) fn-zin-tab)
         (fn-zin-tab-len fn-zin-tab)))))
 :rule-classes nil)

; Local assumption witness at the supported domain; no allocator observation.
(defthm pawtw-qualified-family-complete-positive
 (and (fn-srp-table-coordinate-p *fn-srp-selected-coordinate* *fn-srp-selected-table-body*)
      (fn-srp-table-object-domain-p 1746 255 255 3494)
      (equal (fn-assume-srp-table-object-octets
               1746 255 255 3494 *fn-srp-selected-coordinate* *fn-srp-selected-table-body*) 0))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-assume-srp-table-object-path-bound
              (entry 1746) (low 255) (high 255) (table-length 3494)
              (coordinate *fn-srp-selected-coordinate*) (body *fn-srp-selected-table-body*)))
          :in-theory (enable fn-srp-table-coordinate-p fn-srp-table-object-domain-p fn-srp-coordinate-p))))
