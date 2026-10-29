(in-package "ACL2")
(include-book "../books/core-children")
(include-book "std/testing/must-fail" :dir :system)
(fn2-book-layer :b)

; B-shaped per-layout enum emission uses the same generated artifact names.
(defmacro fn2-dm-layout (name tags)
  (fn2-declare (list :columns name) '(:role :layout-fixture) nil
    (fn2-columns-enum-events `((tag (:enum fn2-dm-layout-tag ,tags))))))
(fn2-dm-layout fn2-dm-layout-a (:plain :marked))
(fn2-dm-layout fn2-dm-layout-b (:plain :marked))
(assert-event (fn2-decl-get :reuse (fn2-decl-row '(:columns fn2-dm-layout-b) (w state))))
(must-fail (fn2-dm-layout fn2-dm-layout-c (:plain :different)) :expected :soft)

(defmachine fn2-dm-staged :states (:idle) :fields nil 
 :budget (:bytes 0 :steps 1 :descriptors 0) :continuations ((:idle fn2-dm-idle :cost (:steps 0) :writes () :next (:idle) :uses ()))
 :observes ((:read-result fn2-dm-idle :cost (:steps 0) :writes () :next () :uses ())))
(fn2-resolve :index)
(must-fail (fn2-resolve :callbacks) :expected :soft)
(assert-event (equal (fn2-decl-unresolved (fn2-decl-all-rows (w state)) :callbacks (w state))
                    '((:machine fn2-dm-staged) (:function fn2-dm-idle :at :callbacks))))
(defun fn2-dm-idle () t)
(fn2-resolve :callbacks)

; An absent operation-set owner is named at its resolving section.
(defun fn2-dm-owner-tooth () t)
(defthm-owed fn2-dm-orphan (x) (equal x x) :teeth (fn2-dm-owner-tooth)
 :from (:operation-set fn2-dm-operations))
(fn2-resolve :callbacks)
(must-fail (fn2-resolve :core) :expected :soft)
(assert-event (equal (fn2-decl-unresolved (fn2-decl-all-rows (w state)) :core (w state))
                    '((:square fn2-dm-orphan) (:owner (:operation-set fn2-dm-operations) :at :core))))
(make-event (value (fn2-declare '(:operation-set fn2-dm-operations) nil nil nil)))
(fn2-resolve :core)
(defwide-columns fn2-dm-wide)
(assert-event (and (fn2-operation-row 'fn2-dm-wide-compare (w state))
                   (equal (fn2-decl-get :returns (fn2-operation-row 'fn2-dm-wide-increment (w state)))
                          '(code fn2-dm-wide))))
; Identical operation replay succeeds, a changed body under its name fails.
(fn2-defoperation (:columns fn2-dm-wide) :declaration (order)
 (defun fn2-dm-wide-probe (fn2-dm-wide)
   (declare (xargs :stobjs fn2-dm-wide :guard t) (ignore fn2-dm-wide)) :same))
(fn2-defoperation (:columns fn2-dm-wide) :declaration (order)
 (defun fn2-dm-wide-probe (fn2-dm-wide)
   (declare (xargs :stobjs fn2-dm-wide :guard t) (ignore fn2-dm-wide)) :same))
(must-fail
 (fn2-defoperation (:columns fn2-dm-wide) :declaration (order)
  (defun fn2-dm-wide-probe (fn2-dm-wide)
    (declare (xargs :stobjs fn2-dm-wide :guard t) (ignore fn2-dm-wide)) :different))
 :expected :soft)
(value-triple (cw "DM0b STAGING: callback/owner resolution, B enum reuse/conflict, carrier operations PASS~%"))

(assert-event (member-equal '(:callback fn2-dm-wide-probe)
                 (fn2-decl-get :reuse (fn2-decl-row '(:columns fn2-dm-wide) (w state)))))
(must-fail
 (fn2-defoperation (:operation-set fn2-dm-absent) :core (value)
  (defun fn2-dm-no-owner (fn2-dm-wide)
    (declare (xargs :stobjs fn2-dm-wide :guard t) (ignore fn2-dm-wide)) :value))
 :expected :soft)
