(in-package "ACL2")
(include-book "../../books/held-record-size")

(defun hszt-carries (xs)
  (if (consp xs) (cons (fn-scs-summary (car xs)) (hszt-carries (cdr xs))) nil))

(defconst *hszt-row*
  (fn-held-make 0 1 1 "<a@x>" 255 '("fn.test") "o" "s" "e" 1 5
                (fn-hf-make 100 20 2 nil)
                (fn-hc-make (fn-stx-make-verdict :unverified nil 0) nil 0)
                nil nil))
(defconst *hszt-carries* (hszt-carries *hszt-row*))

(defun hszt-make (cs)
  (fn-hsz-make 0 1 1 "<a@x>" 255 '("fn.test") "o" "s" "e" 1 5
               (fn-hf-make 100 20 2 nil)
               (fn-hc-make (fn-stx-make-verdict :unverified nil 0) nil 0)
               nil nil cs))

(assert-event
 (and (eq (symbol-class 'fn-hsz-make (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-hsz-remap (w state)) :common-lisp-compliant)))
; fn-hsz-make-preserves-canonical-size: literal hypothesis and conclusion.
(assert-event
 (and (fn-scs-correspondsp *hszt-carries* *hszt-row*)
      (equal (nth 1 (mv-list 2 (hszt-make *hszt-carries*)))
             (fn-scs-summary (nth 0 (mv-list 2 (hszt-make *hszt-carries*)))))))
; Drop the sole correspondence hypothesis.
(assert-event
 (let ((cs (update-nth 3 '(999 nil nil) *hszt-carries*)))
   (and (not (fn-scs-correspondsp cs *hszt-row*))
        (not (equal (nth 1 (mv-list 2 (hszt-make cs)))
                    (fn-scs-summary (nth 0 (mv-list 2 (hszt-make cs)))))))))

; fn-hsz-remap-preserves-canonical-size: actual held record and width crossing.
(assert-event
 (and (< 4 (len *hszt-row*))
      (fn-scs-correspondsp *hszt-carries* *hszt-row*) (atom 256)
      (equal (nth 2 (mv-list 3 (fn-hsz-remap *hszt-row* *hszt-carries* 256)))
             (fn-scs-summary (nth 0 (mv-list 3 (fn-hsz-remap *hszt-row* *hszt-carries* 256)))))
      (equal (car (nth 2 (mv-list 3 (fn-hsz-remap *hszt-row* *hszt-carries* 256))))
             (+ 1 (car (fn-scs-summary *hszt-row*))))))
; Drop correspondence, affirm retained length/atom hypotheses.
(assert-event
 (let ((cs (update-nth 3 '(999 nil nil) *hszt-carries*)))
   (and (< 4 (len *hszt-row*)) (atom 256)
        (not (fn-scs-correspondsp cs *hszt-row*))
        (not (equal (nth 2 (mv-list 3 (fn-hsz-remap *hszt-row* cs 256)))
                    (fn-scs-summary (nth 0 (mv-list 3 (fn-hsz-remap *hszt-row* cs 256)))))))))

; Logical hypothesis-removal witnesses outside the executable guard.

(assert-event (with-guard-checking :none
 (and (not (< 4 (len nil))) (fn-scs-correspondsp nil nil) (atom 256)
      (not (equal (nth 2 (mv-list 3 (fn-hsz-remap nil nil 256)))
                  (fn-scs-summary (nth 0 (mv-list 3 (fn-hsz-remap nil nil 256)))))))))
(assert-event (with-guard-checking :none
 (and (< 4 (len *hszt-row*)) (fn-scs-correspondsp *hszt-carries* *hszt-row*)
      (not (atom '(1 2)))
      (not (equal (nth 2 (mv-list 3 (fn-hsz-remap *hszt-row* *hszt-carries* '(1 2))))
                  (fn-scs-summary
                   (nth 0 (mv-list 3 (fn-hsz-remap *hszt-row* *hszt-carries* '(1 2))))))))))


; Root-only remap: exact old root and canonical width change, shared tail.
(assert-event
 (let ((h *hszt-row*) (handle 256) (encoded (car (fn-scs-summary *hszt-row*))))
   (and (not (fn-scc-octet-listp (nthcdr 5 h)))
        (atom (nth 4 h)) (atom handle)
        (equal encoded (car (fn-scs-summary h)))
        (equal (nth 1 (mv-list 2 (fn-hsz-remap-root h encoded handle)))
               (car (fn-scs-summary (nth 0 (mv-list 2 (fn-hsz-remap-root h encoded handle))))))
        (equal (nthcdr 5 (nth 0 (mv-list 2 (fn-hsz-remap-root h encoded handle))))
               (nthcdr 5 h)))))

; Remove the non-octet suffix premise: compact octets change opcode/shape.
(assert-event
 (let* ((h '(1 2 3 4 5 6)) (handle 256) (encoded (car (fn-scs-summary h))))
   (and (fn-scc-octet-listp (nthcdr 5 h)) (atom (nth 4 h)) (atom handle)
        (equal encoded (car (fn-scs-summary h)))
        (not (equal (nth 1 (mv-list 2 (fn-hsz-remap-root h encoded handle)))
                     (car (fn-scs-summary
                           (nth 0 (mv-list 2 (fn-hsz-remap-root h encoded handle))))))))))

; Logical malformed-payload case, outside the executable guard: old leaf not atom.
(assert-event (with-guard-checking :none
 (let* ((h (update-nth 4 '(1 2) *hszt-row*)) (handle 256)
        (encoded (car (fn-scs-summary h))))
   (and (not (fn-scc-octet-listp (nthcdr 5 h)))
        (not (atom (nth 4 h))) (atom handle)
        (equal encoded (car (fn-scs-summary h)))
        (not (equal (nth 1 (mv-list 2 (fn-hsz-remap-root h encoded handle)))
                     (car (fn-scs-summary
                           (nth 0 (mv-list 2 (fn-hsz-remap-root h encoded handle)))))))))))

; Logical malformed replacement, outside the executable guard: new leaf not atom.
(assert-event (with-guard-checking :none
 (let* ((h *hszt-row*) (handle '(1 2)) (encoded (car (fn-scs-summary h))))
   (and (not (fn-scc-octet-listp (nthcdr 5 h)))
        (atom (nth 4 h)) (not (atom handle))
        (equal encoded (car (fn-scs-summary h)))
        (not (equal (nth 1 (mv-list 2 (fn-hsz-remap-root h encoded handle)))
                     (car (fn-scs-summary
                           (nth 0 (mv-list 2 (fn-hsz-remap-root h encoded handle)))))))))))

; Corrupted root carry; all structural/leaf hypotheses retained.
(assert-event
 (let ((h *hszt-row*) (handle 256) (encoded 99999))
   (and (not (fn-scc-octet-listp (nthcdr 5 h)))
        (atom (nth 4 h)) (atom handle)
        (not (equal encoded (car (fn-scs-summary h))))
        (not (equal (nth 1 (mv-list 2 (fn-hsz-remap-root h encoded handle)))
                     (car (fn-scs-summary
                           (nth 0 (mv-list 2 (fn-hsz-remap-root h encoded handle))))))))))
