; Teeth for books/catalog-dense-map.lisp (lane stage-4, 2026-10-01).
;
; POSITIVE, executed: a fn-dmap built by its exports (the concrete pages
; run) beside the logical alists built by the exports' :logic functions;
; every get of the concrete side equals the alist lookup, over cells on two
; pages of one group, a second group, the escape (a value past a cell, a
; key that is not a membership), a removal and a clear -- the content of
; the extensional correspondence fn-dm-agree on the built pair (a defun-sk,
; not executable).
;
; HYPOTHESIS REMOVAL, evaluated: fn-dmap-put{preserved} without
; (fn-dm-lanep lane): the retained (fn-dmap$ap a) holds, lane 3 is not a
; lane, and the conclusion fails (the logical put grows the list to four
; tables).  Likewise fn-dmap-rem{preserved}.

(in-package "ACL2")
(include-book "../../books/catalog-dense-map")

(defconst *cdt-ops*
  ;; (op lane key value)
  '((:put 0 ("fn.test" . 1) 0)
    (:put 1 ("fn.test" . 1) 0)
    (:put 2 ("fn.test" . 1) 0)
    (:put 0 ("fn.test" . 2) 1)
    (:put 0 ("fn.test" . 300) 299)        ; the group's second page
    (:put 0 ("fn.bench" . 1) 2)           ; a second group
    (:put 1 ("fn.test" . 2) 18446744073709551615) ; past a cell: escaped
    (:put 2 x 7)                           ; not a membership: escaped
    (:put 0 ("fn.test" . 2) 9)            ; rebinding
    (:rem 1 ("fn.test" . 1) nil)
    (:rem 0 ("fn.test" . 300) nil)))

(defconst *cdt-keys*
  '(("fn.test" . 1) ("fn.test" . 2) ("fn.test" . 3) ("fn.test" . 300)
    ("fn.bench" . 1) ("fn.bench" . 2) x ("fn.other" . 1) ("fn.test" . 0)))

(defun cdt-apply (ops fn-dmap a)
  (declare (xargs :mode :program :stobjs fn-dmap))
  (if (atom ops)
      (mv fn-dmap a)
    (let* ((o (car ops)) (lane (nth 1 o)) (k (nth 2 o)) (v (nth 3 o)))
      (if (eq (car o) :put)
          (let ((fn-dmap (fn-dmap-put lane k v fn-dmap)))
            (cdt-apply (cdr ops) fn-dmap (fn-dmap$a-put lane k v a)))
        (let ((fn-dmap (fn-dmap-rem lane k fn-dmap)))
          (cdt-apply (cdr ops) fn-dmap (fn-dmap$a-rem lane k a)))))))

(defun cdt-agree-keys (lane keys fn-dmap a)
  (declare (xargs :mode :program :stobjs fn-dmap))
  (if (atom keys)
      t
    (and (equal (fn-dmap-get lane (car keys) fn-dmap) (fn-dmap$a-get lane (car keys) a))
         (cdt-agree-keys lane (cdr keys) fn-dmap a))))

(defun cdt-agree (lanes keys fn-dmap a)
  (declare (xargs :mode :program :stobjs fn-dmap))
  (if (atom lanes)
      t
    (and (cdt-agree-keys (car lanes) keys fn-dmap a)
         (cdt-agree (cdr lanes) keys fn-dmap a))))

; (agree after the ops, three sample answers, agree after a clear)
(defun cdt-run (ops)
  (declare (xargs :mode :program))
  (with-local-stobj fn-dmap
    (mv-let (r fn-dmap)
      (mv-let (fn-dmap a)
        (cdt-apply ops fn-dmap (create-fn-dmap$a))
        (let* ((ok (cdt-agree '(0 1 2) *cdt-keys* fn-dmap a))
               (s (list (fn-dmap-get 0 '("fn.test" . 2) fn-dmap)
                        (fn-dmap-get 1 '("fn.test" . 2) fn-dmap)
                        (fn-dmap-get 0 '("fn.test" . 300) fn-dmap)))
               (fn-dmap (fn-dmap-clear fn-dmap))
               (a (fn-dmap$a-clear a)))
          (mv (list ok s (cdt-agree '(0 1 2) *cdt-keys* fn-dmap a)) fn-dmap)))
      r)))

(assert-event (equal (cdt-run *cdt-ops*)
                     '(t (9 18446744073709551615 nil) t)))

; fn-dmap-put{preserved} / fn-dmap-rem{preserved}: the omitted lane
; hypothesis fails, the retained one holds, the conclusion fails.
(defthm cdt-put-preserved-lane-removal
  (and (fn-dmap$ap '(nil nil nil))
       (not (fn-dm-lanep 3))
       (not (fn-dmap$ap (fn-dmap$a-put 3 '("fn.test" . 1) 0 '(nil nil nil)))))
  :rule-classes nil)

(defthm cdt-rem-preserved-lane-removal
  (and (fn-dmap$ap '(nil nil nil))
       (not (fn-dm-lanep 3))
       (not (fn-dmap$ap (fn-dmap$a-rem 3 '("fn.test" . 1) '(nil nil nil)))))
  :rule-classes nil)
