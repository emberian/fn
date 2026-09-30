(in-package "ACL2")
(include-book "../../books/ninep-version")

(defun-nx ninep-version-wire (server bytes)
 (let* ((buf (fn-octets-from-list bytes (create-fn-octets)))
        (c0 (fn-9p-fields-start (fn-9p-header-at 0 (len bytes) 128 buf)))
        (c1 (mv-nth 1 (fn-9p-fields-step c0 buf)))
        (c2 (mv-nth 1 (fn-9p-fields-step c1 buf)))
        (c3 (mv-nth 1 (fn-9p-fields-step c2 buf)))
        (c4 (mv-nth 1 (fn-9p-fields-step c3 buf)))
        (c5 (mv-nth 1 (fn-9p-fields-step c4 buf)))
        (c6 (mv-nth 1 (fn-9p-fields-step c5 buf)))
        (c7 (mv-nth 1 (fn-9p-fields-step c6 buf)))
        (c8 (mv-nth 1 (fn-9p-fields-step c7 buf)))
        (c9 (mv-nth 1 (fn-9p-fields-step c8 buf)))
        (c10 (mv-nth 1 (fn-9p-fields-step c9 buf)))
        (c11 (mv-nth 1 (fn-9p-fields-step c10 buf)))
        (c12 (mv-nth 1 (fn-9p-fields-step c11 buf)))
        (c13 (mv-nth 1 (fn-9p-fields-step c12 buf)))
        (c14 (mv-nth 1 (fn-9p-fields-step c13 buf)))
        (c15 (mv-nth 1 (fn-9p-fields-step c14 buf)))
        (c16 (mv-nth 1 (fn-9p-fields-step c15 buf)))
        (c17 (mv-nth 1 (fn-9p-fields-step c16 buf)))
        (c18 (mv-nth 1 (fn-9p-fields-step c17 buf)))
        (c19 (mv-nth 1 (fn-9p-fields-step c18 buf)))
        (c20 (mv-nth 1 (fn-9p-fields-step c19 buf))))
  (and (fn-octets-p buf) (fn-9p-fields-ready-p c20)
       (list (nth 9 c20) (fn-9p-version-at server c20 buf)))))

(defthm ninep-version-base-complete-positive
 (equal (ninep-version-wire 64 '(19 0 0 0 100 255 255 64 0 0 0 6 0 57 80 50 48 48 48))
        '(:parsed (:version 64 :base (19 0 0 0 101 255 255 64 0 0 0 6 0 57 80 50 48 48 48))))
 :rule-classes nil)

(defthm ninep-version-extension-falls-back-base
 (equal (ninep-version-wire 64 '(21 0 0 0 100 255 255 64 0 0 0 8 0 57 80 50 48 48 48 46 117))
        '(:parsed (:version 64 :base (19 0 0 0 101 255 255 64 0 0 0 6 0 57 80 50 48 48 48))))
 :rule-classes nil)

(defthm ninep-version-unknown-complete-positive
 (equal (ninep-version-wire 64 '(18 0 0 0 100 255 255 64 0 0 0 5 0 111 116 104 101 114))
        '(:parsed (:version 64 :unknown (20 0 0 0 101 255 255 64 0 0 0 7 0 117 110 107 110 111 119 110))))
 :rule-classes nil)

(defthm ninep-version-too-small-refusal
 (equal (ninep-version-wire 64 '(19 0 0 0 100 255 255 18 0 0 0 6 0 57 80 50 48 48 48))
        '(:parsed (:close :msize-too-small)))
 :rule-classes nil)

(defthm ninep-version-notag-required
 (equal (ninep-version-wire 64 '(19 0 0 0 100 1 0 64 0 0 0 6 0 57 80 50 48 48 48))
        '(:parsed (:close :invalid-version-request)))
 :rule-classes nil)


(defthm ninep-version-bound-complete-positive
 (let ((answer (fn-9p-version-response 64 32 t)))
  (and (equal (car answer) :version)
       (equal (cadr answer) 32)
       (<= (cadr answer) 64) (<= (cadr answer) 32)
       (<= (len (nth 3 answer)) (cadr answer))
       (<= (len (nth 3 answer)) 20)))
 :rule-classes nil)

; Hypothesis removal: without a successful version result an invalid profile
; does not satisfy the numerical negotiated-size conclusion.
(defthm ninep-version-result-hypothesis-removal
 (let ((answer (fn-9p-version-response -1 64 t)))
  (and (not (equal (car answer) :version))
       (not (<= (cadr answer) -1))
       (equal answer '(:close :profile-unrepresentable))))
 :rule-classes nil)
