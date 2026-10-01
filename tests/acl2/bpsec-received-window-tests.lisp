(in-package "ACL2")
(include-book "../../books/bpsec-received-window")
(include-book "../../books/bpsec-asb")
; Explicitly unfunded internal local-stobj fixture. No source issuer/backing
; registry, original-held/block binding, physical I/O or crypto is claimed.
(defconst *fn-bpsrw-limits* (fn-bps-limits-make 4096 128 16 16 2048 2048))
(defconst *fn-bpsrw-wire*
 '(129 1 2 1 130 1 0 129 130 1 76 0 1 2 3 4 5 6 7 8 9 10 11 129 128))
(defconst *fn-bpsrw-asb*
 (fn-bps-asb-make 12 '(1) 2 1 '(:dtn-none)
  (list (list 1 (cons :bytes '(0 1 2 3 4 5 6 7 8 9 10 11)))) '(nil)))

(defun fn-bpsrw-fill (octets at fn-bprx-segment)
 (declare (xargs :stobjs fn-bprx-segment :measure (acl2-count octets)
  :guard (and (fn-cbor-octet-listp octets) (natp at) (<= (+ at (len octets)) 256))
  :guard-hints (("Goal" :in-theory (e/d (fn-cbor-octet-listp fn-cbor-octetp)
                                      (fn-bprx-segment-put))))))
 (if (consp octets)
  (mv-let (word fn-bprx-segment) (fn-bprx-segment-put 7 2 at (car octets) fn-bprx-segment)
   (if (eq word :source-byte) (fn-bpsrw-fill (cdr octets) (1+ at) fn-bprx-segment)
    (mv word fn-bprx-segment)))
  (mv :fixture-filled fn-bprx-segment)))

(defun fn-bpsrw-pump (cursor fuel fn-bprx-segment)
 (declare (xargs :stobjs fn-bprx-segment :guard t :measure (nfix fuel)
  :hints (("Goal" :in-theory (disable fn-bps-asb-step fn-bps-get fn-bps-field)))
  :guard-hints (("Goal" :in-theory (disable fn-bps-asb-step fn-bps-get fn-bps-field fn-bprx-segment-window)))))
 (if (zp (nfix fuel)) (list :test-fuel cursor)
  (let* ((at (nfix (fn-bps-get :offset cursor)))
         (count (min 64 (nfix (- (fn-bprx-used fn-bprx-segment) at)))))
   (mv-let (word bytes) (fn-bprx-segment-window 7 2 at count fn-bprx-segment)
    (if (not (eq word :source-window)) (list :not-fed word)
     (let* ((step (fn-bps-asb-step cursor (fn-bps-window-make :fixture at bytes) 1))
            (next (fn-bps-field 2 step)))
      (if (member-equal (fn-bps-field 0 step) '(:more :need-input))
       (fn-bpsrw-pump next (1- (nfix fuel)) fn-bprx-segment)
       (list (fn-bps-field 0 step) next))))))))

(defun fn-bpsrw-test ()
 (with-local-stobj fn-bprx-segment
  (mv-let (result fn-bprx-segment)
   (mv-let (unpublished absent) (fn-bprx-segment-window 0 0 0 0 fn-bprx-segment)
    (mv-let (begin fn-bprx-segment) (fn-bprx-segment-begin 7 2 fn-bprx-segment)
     (mv-let (filled fn-bprx-segment) (fn-bpsrw-fill *fn-bpsrw-wire* 0 fn-bprx-segment)
      (mv-let (freeze fn-bprx-segment) (fn-bprx-segment-freeze 7 2 25 fn-bprx-segment)
       (mv-let (word bytes) (fn-bprx-segment-window 7 2 3 12 fn-bprx-segment)
        (mv-let (stale wrong) (fn-bprx-segment-window 8 2 3 12 fn-bprx-segment)
         (mv-let (ordinal wrong-ordinal) (fn-bprx-segment-window 7 3 3 12 fn-bprx-segment)
          (mv-let (range beyond) (fn-bprx-segment-window 7 2 24 2 fn-bprx-segment)
           (mv-let (mutation fn-bprx-segment) (fn-bprx-segment-put 7 2 25 90 fn-bprx-segment)
            (let* ((alpha (fn-bps-received-segment-alpha fn-bprx-segment))
                   (run (fn-bpsrw-pump (fn-bps-asb-start 12 :fixture 0 25 *fn-bpsrw-limits*) 256 fn-bprx-segment))
                   (asb (fn-bps-asb-span-alpha (fn-bps-asb-span-result (fn-bps-field 1 run))
                           (list (cons :fixture alpha)))))
             (mv
              (and (eq unpublished :source-unpublished) (null absent)
                   (eq begin :source-filling) (eq filled :fixture-filled) (eq freeze :source-frozen)
                   (fn-bprx-segmentp fn-bprx-segment) (natp 3) (natp 12) (<= 12 64)
                   (equal 7 (fn-bprx-nonce fn-bprx-segment)) (equal 2 (fn-bprx-ordinal fn-bprx-segment))
                   (eq (fn-bprx-phase fn-bprx-segment) :frozen) (<= (+ 3 12) (fn-bprx-used fn-bprx-segment))
                   (eq word :source-window) (equal bytes (take 12 (nthcdr 3 alpha)))
                   (equal (len bytes) 12) (<= (len bytes) 64)
                   (fn-bps-windowp (fn-bps-window-make :fixture 3 bytes))
                   (equal alpha *fn-bpsrw-wire*)
                   (equal alpha (fn-bps-received-segment-alpha-from 0 25 fn-bprx-segment))
                   (eq stale :stale-source) (null wrong) (not (equal 8 (fn-bprx-nonce fn-bprx-segment)))
                   (eq ordinal :stale-source) (null wrong-ordinal) (not (equal 3 (fn-bprx-ordinal fn-bprx-segment)))
                   (eq range :source-range) (null beyond) (> (+ 24 2) (fn-bprx-used fn-bprx-segment))
                   (eq mutation :source-immutable) (eq (fn-bps-field 0 run) :parsed)
                   (equal asb *fn-bpsrw-asb*))
              fn-bprx-segment)))))))))))
   result)))
(assert-event
 (and (eq (symbol-class 'fn-bps-received-segment-alpha (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-bprx-segment-window (w state)) :common-lisp-compliant)))
(assert-event (fn-bpsrw-test))

; Ground logical omission teeth call the literal host subject on raw abstract
; stobj representations. They are proof-only corrupted-state/guard-omission
; witnesses, never executions permitted by the installed runtime guards.
(local
 (defthm fn-bpsrw-representation-omission-witness
  (let ((raw '( (65) 7 2 3/2 :frozen)))
   (and (natp 0) (natp 1) (<= 1 64) (equal 7 (fn-bprx-nonce raw)) (equal 2 (fn-bprx-ordinal raw)) (eq (fn-bprx-phase raw) :frozen) (<= (+ 0 1) (fn-bprx-used raw))
        (not (fn-bprx-segmentp raw)) (not (equal (mv-nth 1 (fn-bprx-segment-window 7 2 0 1 raw)) (take 1 (nthcdr 0 (fn-bps-received-segment-alpha raw)))))))
  :rule-classes nil))
(local
 (defthm fn-bpsrw-natural-offset-omission-witness
  (let ((raw (list (cons 65 (cons 66 (make-list 254 :initial-element 0))) 7 2 2 :frozen)))
   (and (fn-bprx-segmentp raw) (natp 2) (<= 2 64) (equal 7 (fn-bprx-nonce raw)) (equal 2 (fn-bprx-ordinal raw)) (eq (fn-bprx-phase raw) :frozen) (<= (+ -1 2) (fn-bprx-used raw))
        (not (natp -1)) (not (equal (mv-nth 1 (fn-bprx-segment-window 7 2 -1 2 raw)) (take 2 (nthcdr -1 (fn-bps-received-segment-alpha raw)))))))
  :rule-classes nil))
(local
 (defthm fn-bpsrw-natural-count-omission-witness
  (let ((raw (list (make-list 256 :initial-element 65) 7 2 2 :frozen)))
   (and (fn-bprx-segmentp raw) (natp 0) (<= 1/2 64) (equal 7 (fn-bprx-nonce raw)) (equal 2 (fn-bprx-ordinal raw)) (eq (fn-bprx-phase raw) :frozen) (<= (+ 0 1/2) (fn-bprx-used raw))
        (not (natp 1/2)) (not (equal (len (mv-nth 1 (fn-bprx-segment-window 7 2 0 1/2 raw))) 1/2))))
  :rule-classes nil))
(local
 (defthm fn-bpsrw-window-cap-omission-witness
  (let ((raw (list (make-list 256 :initial-element 65) 7 2 65 :frozen)))
   (and (fn-bprx-segmentp raw) (natp 0) (natp 65) (equal 7 (fn-bprx-nonce raw)) (equal 2 (fn-bprx-ordinal raw)) (eq (fn-bprx-phase raw) :frozen) (<= (+ 0 65) (fn-bprx-used raw))
        (not (<= 65 64)) (not (<= (len (mv-nth 1 (fn-bprx-segment-window 7 2 0 65 raw))) 64))))
  :rule-classes nil))
(local
 (defthm fn-bpsrw-nonce-omission-witness
  (let ((raw (list (make-list 256 :initial-element 65) 7 2 25 :frozen)))
   (and (fn-bprx-segmentp raw) (natp 3) (natp 12) (<= 12 64) (equal 2 (fn-bprx-ordinal raw)) (eq (fn-bprx-phase raw) :frozen) (<= (+ 3 12) (fn-bprx-used raw))
        (not (equal 8 (fn-bprx-nonce raw))) (not (equal (mv-nth 0 (fn-bprx-segment-window 8 2 3 12 raw)) :source-window))))
  :rule-classes nil))
(local
 (defthm fn-bpsrw-ordinal-omission-witness
  (let ((raw (list (make-list 256 :initial-element 65) 7 2 25 :frozen)))
   (and (fn-bprx-segmentp raw) (natp 3) (natp 12) (<= 12 64) (equal 7 (fn-bprx-nonce raw)) (eq (fn-bprx-phase raw) :frozen) (<= (+ 3 12) (fn-bprx-used raw))
        (not (equal 3 (fn-bprx-ordinal raw))) (not (equal (mv-nth 0 (fn-bprx-segment-window 7 3 3 12 raw)) :source-window))))
  :rule-classes nil))
(local
 (defthm fn-bpsrw-frozen-omission-witness
  (let ((raw (list (make-list 256 :initial-element 65) 7 2 25 :filling)))
   (and (fn-bprx-segmentp raw) (natp 3) (natp 12) (<= 12 64) (equal 7 (fn-bprx-nonce raw)) (equal 2 (fn-bprx-ordinal raw)) (<= (+ 3 12) (fn-bprx-used raw))
        (not (eq (fn-bprx-phase raw) :frozen)) (not (equal (mv-nth 0 (fn-bprx-segment-window 7 2 3 12 raw)) :source-window))))
  :rule-classes nil))
(local
 (defthm fn-bpsrw-range-omission-witness
  (let ((raw (list (make-list 256 :initial-element 65) 7 2 25 :frozen)))
   (and (fn-bprx-segmentp raw) (natp 24) (natp 2) (<= 2 64) (equal 7 (fn-bprx-nonce raw)) (equal 2 (fn-bprx-ordinal raw)) (eq (fn-bprx-phase raw) :frozen)
        (not (<= (+ 24 2) (fn-bprx-used raw))) (not (equal (mv-nth 0 (fn-bprx-segment-window 7 2 24 2 raw)) :source-window))))
  :rule-classes nil))
