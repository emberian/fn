; Teeth for books/raw-dispatch-verdict.lisp (D40 verdicts judged in the
; world; lane extract, 2026-10-05).
;
;   1. A world with a raw-declared entry definterface accepts, a registered
;      creator, and a raw row written into fn-interfaces past definterface
;      that the world refutes (a row judged problematic).
;   2. The verdicts: one per raw-declared row, the refuted one carrying its
;      problem and no target, the creator its role.  The table takes exactly
;      the world's judgment; a forged clean verdict for the refuted row, a
;      verdict for an entry that is not raw-declared and a verdict with a
;      different digest are each refused by the table's guard, alone or in
;      a :clear.
;   3. Admission (fn-rdv-admit), as fnn-install-raw-dispatch asks it: the
;      clean row admitted with its judged target; the refuted row refused;
;      a row whose digest differs from the judged one refused; an unjudged
;      name refused.  The keystone's premise is inhabited (the clean row)
;      and each of its conclusions fails without the premise.

(in-package "ACL2")
(include-book "../../books/raw-dispatch-verdict")
(include-book "../../books/payload-kinds") ; *fn-entry-guard-kinds*
(include-book "must-fail-checked")

; ---------------------------------------------------------------------------
; 1. The world.

(defstobj fn-rdvt-st (fn-rdvt-fld :type integer :initially 1))

(defun fn-rdvt-positivep (fn-rdvt-st)
  (declare (xargs :stobjs fn-rdvt-st))
  (< 0 (fn-rdvt-fld fn-rdvt-st)))

(defun fn-rdvt-r (n fn-rdvt-st)
  (declare (xargs :stobjs fn-rdvt-st
                  :guard (and (natp n) (fn-rdvt-positivep fn-rdvt-st))))
  (update-fn-rdvt-fld (+ n (fn-rdvt-fld fn-rdvt-st)) fn-rdvt-st))

(defthm fn-rdvt-positive-is-positive
  (implies (fn-rdvt-positivep fn-rdvt-st)
           (fn-rdvt-positivep fn-rdvt-st)))

(defthm fn-rdvt-r-keeps-positive
  (implies (and (natp n) (fn-rdvt-positivep fn-rdvt-st))
           (fn-rdvt-positivep (fn-rdvt-r n fn-rdvt-st))))

(defthm fn-rdvt-unrelated
  (equal (len (list x)) 1))

(definterface fn-rdvt-r
  :class :common-lisp-compliant
  :kinds ((n natp))
  :raw-with (fn-rdvt-positive-is-positive fn-rdvt-r-keeps-positive))

(definterface create-fn-rdvt-st
  :class :common-lisp-compliant
  :raw-guarded (0 nil (fn-rdvt-st)))

; definterface refuses this row ...
(defun fn-rdvt-bad (n fn-rdvt-st)
  (declare (xargs :stobjs fn-rdvt-st
                  :guard (and (natp n) (fn-rdvt-positivep fn-rdvt-st))))
  (update-fn-rdvt-fld (+ n (fn-rdvt-fld fn-rdvt-st)) fn-rdvt-st))

(defconst *fn-rdvt-bad-kvs*
  '(:class :common-lisp-compliant :kinds ((n natp)) :raw-with (fn-rdvt-unrelated)))

(must-fail-checked
 (definterface fn-rdvt-bad :class :common-lisp-compliant :kinds ((n natp))
   :raw-with (fn-rdvt-unrelated))
 :unchecked "definterface refuses a :raw-with whose theorem concludes nothing")

; ... and here it is in the table anyway: what the install's re-check exists
; for (a row written past definterface, or one a later event made false).
(table fn-interfaces 'fn-rdvt-bad *fn-rdvt-bad-kvs*)

; a declared entry that is not raw-dispatched gets no verdict
(definterface fn-rdvt-positivep :class :common-lisp-compliant)

; ---------------------------------------------------------------------------
; 2. The verdicts.

(defconst *fn-rdvt-r-kvs*
  '(:class :common-lisp-compliant :kinds ((n natp))
    :raw-with (fn-rdvt-positive-is-positive fn-rdvt-r-keeps-positive)))

(assert-event
 (equal (strip-cars (fn-rdv-verdicts (table-alist 'fn-interfaces (w state)) (w state)))
        ; the table's newest first
        '(fn-rdvt-bad create-fn-rdvt-st fn-rdvt-r)))

(assert-event
 (let ((v (fn-rdv-judge 'fn-rdvt-r *fn-rdvt-r-kvs* (w state))))
   (and (equal (fn-rdv-verdict-digest v)
               (fn-rdv-row-digest 'fn-rdvt-r *fn-rdvt-r-kvs* (w state)))
        (equal (len (fn-rdv-verdict-digest v)) 32)
        (null (fn-rdv-verdict-problem v))
        (eq (fn-rdv-verdict-target v) 'fn-rdvt-r)
        (null (fn-rdv-verdict-creatorp v)))))

(assert-event
 (let ((v (fn-rdv-judge 'fn-rdvt-bad *fn-rdvt-bad-kvs* (w state))))
   (and (fn-rdv-verdict-problem v)
        (search "refused declaration" (car (fn-rdv-verdict-problem v)))
        (null (fn-rdv-verdict-target v))
        (null (fn-rdv-verdict-creatorp v)))))

(assert-event
 (let ((v (fn-rdv-judge 'create-fn-rdvt-st
                        (cdr (assoc-eq 'create-fn-rdvt-st (table-alist 'fn-interfaces (w state))))
                        (w state))))
   (and (null (fn-rdv-verdict-problem v))
        (eq (fn-rdv-verdict-target v) 'create-fn-rdvt-st)
        (eq (fn-rdv-verdict-creatorp v) t))))

; The digest is of the judged row: another declaration of the same entry is
; another digest.
(assert-event
 (not (equal (fn-rdv-row-digest 'fn-rdvt-r *fn-rdvt-r-kvs* (w state))
             (fn-rdv-row-digest 'fn-rdvt-r
                                '(:class :common-lisp-compliant :kinds ((n natp))
                                  :raw-with (fn-rdvt-r-keeps-positive))
                                (w state)))))

; The guard refuses a forged verdict: the refuted row judged clean ...
(must-fail-checked
 (make-event
  `(table fn-raw-dispatch-verdicts 'fn-rdvt-bad
          '(,(fn-rdv-row-digest 'fn-rdvt-bad *fn-rdvt-bad-kvs* (w state)) nil fn-rdvt-bad nil)))
 :unchecked "the table guard refuses a verdict the world does not give")
; ... a verdict for a declared entry that is not raw-dispatched ...
(must-fail-checked
 (make-event
  `(table fn-raw-dispatch-verdicts 'fn-rdvt-positivep
          '(,(fn-rdv-row-digest 'fn-rdvt-positivep '(:class :common-lisp-compliant) (w state))
            nil fn-rdvt-positivep nil)))
 :unchecked "the table guard refuses a verdict on an entry with no raw declaration")
; ... and the clean row's verdict over another digest.
(must-fail-checked
 (table fn-raw-dispatch-verdicts 'fn-rdvt-r '((1 2 3) nil fn-rdvt-r nil))
 :unchecked "the table guard refuses a verdict over a row it did not judge")

; ... and a whole table with any forged pair (the guard reads each pair of
; a :clear too).  A table that OMITS a raw row is the unjudged case of 3.
(must-fail-checked
 (table fn-raw-dispatch-verdicts nil '((fn-rdvt-r (1) nil fn-rdvt-r nil)) :clear)
 :unchecked "the table guard reads every pair of a :clear")

; The world's judgment is accepted whole (host/raw-dispatch-verdicts.lisp's
; event).
(make-event
 `(table fn-raw-dispatch-verdicts nil
         ',(fn-rdv-verdicts (table-alist 'fn-interfaces (w state)) (w state))
         :clear))

(assert-event
 (equal (fn-rdv-refused-names (table-alist 'fn-raw-dispatch-verdicts (w state)))
        '(fn-rdvt-bad)))

; ---------------------------------------------------------------------------
; 3. Admission.

(defun fn-rdvt-admit (name kvs state)
  (declare (xargs :mode :program :stobjs state))
  ; fnn-install-raw-dispatch's question, over this world
  (mv-let (problem target creatorp)
    (fn-rdv-admit name (fn-rdv-row-digest name kvs (w state))
                  (table-alist 'fn-raw-dispatch-verdicts (w state)))
    (list problem target creatorp)))

; the clean row: admitted, with its judged target
(assert-event (equal (fn-rdvt-admit 'fn-rdvt-r *fn-rdvt-r-kvs* state)
                     '(nil fn-rdvt-r nil)))
(assert-event (equal (fn-rdvt-admit 'create-fn-rdvt-st '(:class :common-lisp-compliant
                                                       :raw-guarded (0 nil (fn-rdvt-st)))
                                    state)
                     '(nil create-fn-rdvt-st t)))
; the row judged problematic: refused, by name, with the judged problem
(assert-event
 (let ((r (fn-rdvt-admit 'fn-rdvt-bad *fn-rdvt-bad-kvs* state)))
   (and (car r) (null (cadr r))
        (search "was judged refused" (car (car r))))))
; the clean entry under a row it was not judged on: refused
(assert-event
 (let ((r (fn-rdvt-admit 'fn-rdvt-r '(:class :common-lisp-compliant :kinds ((n natp))
                                      :raw-with (fn-rdvt-r-keeps-positive))
                         state)))
   (and (car r) (null (cadr r))
        (search "is not the row its verdict judged" (car (car r))))))
; a name never judged: refused
(assert-event
 (let ((r (fn-rdvt-admit 'fn-rdvt-positivep '(:class :common-lisp-compliant :raw-with (x))
                         state)))
   (and (car r) (search "no raw-dispatch verdict" (car (car r))))))
; no digest at all (a row the host could not read) admits nothing, even
; against a verdict whose digest is also absent
(assert-event (mv-let (p tg c) (fn-rdv-admit 'x nil '((x nil nil x nil)))
                (declare (ignore tg c))
                p))

; The keystone's premise is inhabited ...
(assert-event (mv-let (p tg c) (fn-rdv-admit 'x '(1) '((x (1) nil x nil)))
                (declare (ignore c))
                (and (null p) (eq tg 'x))))
; ... and each of its conclusions fails without it.
(must-fail-checked (thm (fn-rdv-lookup name verdicts)))
(must-fail-checked (thm (consp digest)))
(must-fail-checked
 (thm (equal (fn-rdv-verdict-digest (cdr (fn-rdv-lookup name verdicts))) digest)))
(must-fail-checked
 (thm (not (fn-rdv-verdict-problem (cdr (fn-rdv-lookup name verdicts))))))
