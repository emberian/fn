; Teeth for books/def-holder.lisp (lane def-holder).
;
;   1. The keyed generic: reachable positives with the complete antecedent
;      and conclusion of each keystone, one removal per hypothesis (the
;      conclusion fails), corrupted-state witnesses labelled.
;   2. A keyed instance (a toy file table threaded by two entries): every
;      generated name present with its regenerated statement (def-holder-check),
;      the row, the cuts, the teeth-owed rows, the def-carried trace, and
;      the generated statements evaluated on a run.
;   3. Refusals, each asserted exactly: malformed forms; a world refusal
;      (a theorem about another term proves no generated statement); a
;      :durable effect whose program does not name the cut; a redeclared
;      name; an undeclared caller of the step refused by def-holder-check.
;
; must-fail-checked (tests/acl2/must-fail-checked.lisp): a macro refusal is
; a translation-time refusal, so :unchecked names why.
(in-package "ACL2")
(include-book "../../books/def-holder")
(include-book "must-fail-checked")

; ---------------------------------------------------------------------------
; 1. The keyed generic.

; A macro, not a function: a FUNCTION that calls the step is what
; def-holder-check refuses (section 3), so the evaluated checks call it
; inline.
(defmacro hdt-step (table ev)
  `(mv-list 2 (fn-hd-keyed-step ,table ,ev)))

; A run: file 3 held twice, file 5 once, 3 dropped once, 5 dropped, 5 dropped
; again (late: refused), 3 dropped, 3 dropped again (late: refused).
(defconst *hdt-evs*
  '((:hold 3) (:hold 5) (:hold 3) (:drop 3) (:drop 5) (:drop 5) (:drop 3) (:drop 3)))

(assert-event (equal (fn-hd-run-answers (fn-hd-initial) *hdt-evs*)
                     '(:held :held :held :dropped :dropped :refused :dropped :refused)))
(assert-event (equal (fn-hd-run (fn-hd-initial) *hdt-evs*) nil))
(assert-event (equal (fn-hd-run (fn-hd-initial) (take 3 *hdt-evs*)) '((3 . 2) (5 . 1))))
(assert-event (equal (hdt-step '((3 . 2) (5 . 1)) '(:count 3)) '(((3 . 2) (5 . 1)) 2)))
(assert-event (equal (hdt-step '((3 . 2) (5 . 1)) '(:quiet 3)) '(((3 . 2) (5 . 1)) nil)))
(assert-event (equal (hdt-step '((3 . 2) (5 . 1)) '(:quiet 4)) '(((3 . 2) (5 . 1)) t)))
(assert-event (equal (hdt-step '((3 . 2)) '(:hold -1)) '(((3 . 2)) :refused)))
(assert-event (equal (hdt-step '((3 . 2)) '(:frob 3)) '(((3 . 2)) :refused)))

;;; KEYSTONE fn-hd-drop-of-unheld-is-refused.
; REACHABLE POSITIVE: the late drop of 5 after its only hold was dropped
; (the run's sixth event), complete antecedent and conclusion.
(assert-event
 (let ((table (fn-hd-run (fn-hd-initial) (take 5 *hdt-evs*))) (k 5))
   (and (not (and (natp k) (fn-arpn-held-p k table)))
        (equal (hdt-step table (list :drop k)) (list table :refused)))))
; also: a non-natural key, and the empty table
(assert-event (equal (hdt-step '((3 . 1)) '(:drop :three)) '(((3 . 1)) :refused)))
(assert-event (equal (hdt-step (fn-hd-initial) '(:drop 3)) '(nil :refused)))
; HYPOTHESIS-REMOVAL: 3 is held: the drop is not refused (the conclusion
; fails: the answer is :dropped and the table changes).
(assert-event
 (let ((table '((3 . 2) (5 . 1))) (k 3))
   (and (natp k) (fn-arpn-held-p k table)
        (not (equal (hdt-step table (list :drop k)) (list table :refused)))
        (equal (hdt-step table (list :drop k)) '(((3 . 1) (5 . 1)) :dropped)))))

;;; KEYSTONE fn-hd-run-count-is-holds-less-drops.
; REACHABLE POSITIVES: every key of the run, and a key never held, from the
; empty table and from a table that already holds.
(defun hdt-accounts-p (table k evs)
  (declare (xargs :guard (and (fn-arpn-pinsp table) (natp k) (true-listp evs))))
  (equal (fn-arpn-pins-of k (fn-hd-run table evs))
         (+ (fn-arpn-pins-of k table)
            (fn-hd-holds-of k evs)
            (- (fn-hd-drops-of k evs (fn-hd-run-answers table evs))))))
(assert-event (and (hdt-accounts-p (fn-hd-initial) 3 *hdt-evs*)
                   (hdt-accounts-p (fn-hd-initial) 5 *hdt-evs*)
                   (hdt-accounts-p (fn-hd-initial) 4 *hdt-evs*)
                   (hdt-accounts-p '((3 . 1)) 3 *hdt-evs*)
                   (hdt-accounts-p '((3 . 1)) 3 (take 4 *hdt-evs*))
                   (equal (fn-hd-holds-of 3 *hdt-evs*) 2)
                   (equal (fn-hd-drops-of 3 *hdt-evs* (fn-hd-run-answers (fn-hd-initial) *hdt-evs*)) 2)
                   (equal (fn-hd-drops-of 5 *hdt-evs* (fn-hd-run-answers (fn-hd-initial) *hdt-evs*)) 1)))
; HYPOTHESIS-REMOVAL (natp k): a non-natural key's holds are counted by
; fn-hd-holds-of but refused by the step: the conclusion fails.
(assert-event
 (let ((k :three) (evs '((:hold :three))))
   (and (not (natp k))
        (equal (fn-hd-holds-of k evs) 1)
        (equal (fn-arpn-pins-of k (fn-hd-run (fn-hd-initial) evs)) 0)
        (not (equal (fn-arpn-pins-of k (fn-hd-run (fn-hd-initial) evs))
                    (+ (fn-arpn-pins-of k (fn-hd-initial))
                       (fn-hd-holds-of k evs)
                       (- (fn-hd-drops-of k evs (fn-hd-run-answers (fn-hd-initial) evs)))))))))
; CORRUPTED-STATE (not a table): a descending, duplicated table miscounts
; the key it names twice: the conclusion fails (evaluated with guards off:
; the table violates every guard, which is the point).
(assert-event
 (with-guard-checking :none
   (let ((table '((5 . 1) (3 . 1) (3 . 1))) (k 3) (evs '((:hold 3))))
     (and (not (fn-arpn-pinsp table))
          (not (hdt-accounts-p table k evs))))))

;;; KEYSTONE fn-hd-quiet-from-empty-means-every-hold-was-dropped.
; REACHABLE POSITIVE: the run ends quiet at 3 and at 5; holds = drops.
(assert-event
 (let ((k 3) (evs *hdt-evs*))
   (and (natp k)
        (equal (fn-arpn-pins-of k (fn-hd-run (fn-hd-initial) evs)) 0)
        (equal (fn-hd-holds-of k evs)
               (fn-hd-drops-of k evs (fn-hd-run-answers (fn-hd-initial) evs))))))
; HYPOTHESIS-REMOVAL (quiet): after three events 3 is held twice: holds 2,
; drops 0; the conclusion fails.
(assert-event
 (let ((k 3) (evs (take 3 *hdt-evs*)))
   (and (not (equal (fn-arpn-pins-of k (fn-hd-run (fn-hd-initial) evs)) 0))
        (not (equal (fn-hd-holds-of k evs)
                    (fn-hd-drops-of k evs (fn-hd-run-answers (fn-hd-initial) evs)))))))

; ---------------------------------------------------------------------------
; 2. A keyed instance: a toy file table threaded by an open and a close.

(defun hdt-open (k table)
  (declare (xargs :guard (fn-arpn-pinsp table)))
  (if (natp k)
      (mv-let (table1 answer) (fn-hd-keyed-step table (list :hold k))
        (mv answer table1))
    (mv :refused table)))

(defun hdt-close (k table)
  (declare (xargs :guard (fn-arpn-pinsp table)))
  (if (natp k)
      (mv-let (table1 answer) (fn-hd-keyed-step table (list :drop k))
        (mv answer table1))
    (mv :refused table)))

(defthm hdt-open-holds
  (implies (fn-arpn-pinsp table)
           (equal (mv-nth 1 (hdt-open k table))
                  (if (equal (mv-nth 0 (hdt-open k table)) :held)
                      (mv-nth 0 (fn-hd-keyed-step table (list :hold k)))
                    table)))
  :hints (("Goal" :in-theory (disable fn-hd-keyed-step)
           :use ((:instance fn-hd-hold-counts-exactly-its-key (h k))))))

(defthm hdt-close-drops
  (implies (fn-arpn-pinsp table)
           (equal (mv-nth 1 (hdt-close k table))
                  (if (equal (mv-nth 0 (hdt-close k table)) :dropped)
                      (mv-nth 0 (fn-hd-keyed-step table (list :drop k)))
                    table)))
  :hints (("Goal" :in-theory (disable fn-hd-keyed-step)
           :use ((:instance fn-hd-drop-counts-exactly-its-key (h k))
                 (:instance fn-hd-drop-of-unheld-is-refused)))))

(defun hdt-program ()
  (declare (xargs :guard t))
  (list (list :cut "hdt-unlinked")))

(def-holder hdt-files
  :shape :keyed
  :key "a toy file incarnation"
  :holders ((reader :acquire (hdt-open hdt-open-holds :table 1 :result (mv-nth 1 _)
                              :key k :ok (equal (mv-nth 0 _) :held))
                    :release (hdt-close hdt-close-drops :table 1 :result (mv-nth 1 _)
                              :key k :ok (equal (mv-nth 0 _) :dropped))))
  :effect (:durable hdt-program "hdt-unlinked")
  :complete-by "a toy: hdt-open and hdt-close are its only entries")

; Every generated name is a theorem; the row, the cuts and the owed teeth.
(assert-event
 (and (getpropc 'hdt-files-reader-acquire-holds 'theorem nil (w state))
      (getpropc 'hdt-files-reader-release-drops 'theorem nil (w state))
      (getpropc 'hdt-files-reader-acquire-keeps 'theorem nil (w state))
      (getpropc 'hdt-files-reader-release-keeps 'theorem nil (w state))
      (getpropc 'hdt-files-initial-establishes 'theorem nil (w state))
      (getpropc 'hdt-files-table-hdt-open-carries 'theorem nil (w state))
      (getpropc 'hdt-files-table-hdt-close-carries 'theorem nil (w state))
      (getpropc 'hdt-files-table-run-carries 'theorem nil (w state))
      (equal *hdt-files-cuts* '(:hdt-files-decided :hdt-files-released))
      (equal (cdr (assoc-eq 'hdt-files (table-alist 'fn-holder-cuts (w state))))
             '(:effect (:durable hdt-program "hdt-unlinked")
               :cuts (:hdt-files-decided :hdt-files-released)))
      (assoc-eq 'hdt-files-reader-acquire-holds (table-alist 'fn-teeth-owed (w state)))
      (assoc-eq 'hdt-files-reader-release-drops (table-alist 'fn-teeth-owed (w state)))
      (assoc-eq 'hdt-files-reader-acquire-keeps (table-alist 'fn-teeth-owed (w state)))
      ; the owed row's claim is the statement in source shape, its subject the entry
      (equal (cdr (assoc-eq 'hdt-files-reader-release-drops (table-alist 'fn-teeth-owed (w state))))
             '(:by def-holder
               :claim (implies (and (fn-arpn-pinsp table))
                               (equal (mv-nth '1 (hdt-close k table))
                                      (if (equal (mv-nth '0 (hdt-close k table)) ':dropped)
                                          (mv-nth '0 (fn-hd-keyed-step table (cons ':drop (cons k 'nil))))
                                        table)))
               :subject hdt-close))
      (assoc-eq 'hdt-files-table (table-alist 'fn-carried (w state)))
      (equal (fn-hd-get :shape (cdr (assoc-eq 'hdt-files (table-alist 'fn-holder (w state)))))
             :keyed)))

; The generated statements, pinned literally (what the host-side reader of
; the row may rely on; a drift here is a drift of the generator).
(assert-event
 (equal (getpropc 'hdt-files-reader-acquire-holds 'theorem nil (w state))
        '(implies (fn-arpn-pinsp table)
                  (equal (mv-nth '1 (hdt-open k table))
                         (if (equal (mv-nth '0 (hdt-open k table)) ':held)
                             (mv-nth '0 (fn-hd-keyed-step table (cons ':hold (cons k 'nil))))
                           table)))))
(assert-event
 (equal (getpropc 'hdt-files-reader-release-keeps 'theorem nil (w state))
        '(implies (if (fn-arpn-pinsp table) (fn-arpn-pinsp table) 'nil)
                  (fn-arpn-pinsp (mv-nth '1 (hdt-close k table))))))

(def-holder-check hdt-files)

;;; The generated -holds/-drops theorems, evaluated on a run (owed teeth;
;;; converted to defteeth when GENERATORS lands it).
; REACHABLE POSITIVES: an open on the empty table and on a table that holds;
; a close of a held and of an unheld (late) key.
(defmacro hdt-open-as-generated-p (k table)
  `(equal (mv-nth 1 (mv-list 2 (hdt-open ,k ,table)))
          (if (equal (mv-nth 0 (mv-list 2 (hdt-open ,k ,table))) :held)
              (mv-nth 0 (mv-list 2 (fn-hd-keyed-step ,table (list :hold ,k))))
            ,table)))
(defmacro hdt-close-as-generated-p (k table)
  `(equal (mv-nth 1 (mv-list 2 (hdt-close ,k ,table)))
          (if (equal (mv-nth 0 (mv-list 2 (hdt-close ,k ,table))) :dropped)
              (mv-nth 0 (mv-list 2 (fn-hd-keyed-step ,table (list :drop ,k))))
            ,table)))
(assert-event
 (and (hdt-open-as-generated-p 7 nil)
      (equal (mv-list 2 (hdt-open 7 nil)) '(:held ((7 . 1))))
      (hdt-open-as-generated-p 7 '((7 . 1)))
      (hdt-open-as-generated-p :seven '((7 . 1)))
      (equal (mv-list 2 (hdt-open :seven '((7 . 1)))) '(:refused ((7 . 1))))
      (hdt-close-as-generated-p 7 '((7 . 1)))
      (equal (mv-list 2 (hdt-close 7 '((7 . 1)))) '(:dropped nil))
      (hdt-close-as-generated-p 7 nil)
      (equal (mv-list 2 (hdt-close 7 nil)) '(:refused nil))))
; The trace theorem (hdt-files-table-run-carries, over def-carried's
; defun-nx run) is asserted present above; its functions do not execute.

; ---------------------------------------------------------------------------
; 3. Refusals.

; Malformed forms.
(must-fail-checked (def-holder hdt-bad-shape :shape :counted :key "k" :holders ((r :host t :acquire a :release b :in (c))) :effect (:process-local "x"))
                   :unchecked "the shape is not one of the two")
(must-fail-checked (def-holder hdt-no-holders :shape :keyed :key "k" :holders () :effect (:process-local "x"))
                   :unchecked "a resource nobody holds")
(must-fail-checked (def-holder hdt-bad-effect :shape :keyed :key "k" :holders ((r :host t :acquire a :release b :in (c))) :effect (:later "x"))
                   :unchecked "the effect is neither process-local nor durable")
(must-fail-checked (def-holder hdt-no-key :shape :keyed :holders ((r :host t :acquire a :release b :in (c))) :effect (:process-local "x"))
                   :unchecked "no :key prose")
(must-fail-checked (def-holder hdt-when-without-keeps :shape :keyed :key "k"
                     :holders ((r :acquire (hdt-open hdt-open-holds :table 1 :result (mv-nth 1 _) :key k :ok t :when (natp k))
                                  :release (hdt-close hdt-close-drops :table 1 :result (mv-nth 1 _) :key k :ok t)))
                     :effect (:process-local "x") :complete-by "x")
                   :unchecked "an arm selector without the instance's own preservation theorem")
(must-fail-checked (def-holder hdt-unknown :shape :keyed :key "k" :holders ((r :host t :acquire a :release b :in (c))) :effect (:process-local "x") :lease x)
                   :unchecked "an unknown keyword")

; World refusals.
; A theorem about another term proves no generated statement: the declared
; THM is hdt-close-drops for the OPEN entry.
(must-fail-checked (def-holder hdt-wrong-theorem :shape :keyed :key "k"
                     :holders ((r :acquire (hdt-open hdt-close-drops :table 1 :result (mv-nth 1 _) :key k :ok (equal (mv-nth 0 _) :held))
                                  :release (hdt-close hdt-close-drops :table 1 :result (mv-nth 1 _) :key k :ok (equal (mv-nth 0 _) :dropped))))
                     :effect (:process-local "x") :complete-by "x")
                   :unchecked "the generated acquire-holds statement is not proved from a theorem about the close")
; A :durable effect whose program does not name the cut.
(must-fail-checked (def-holder hdt-wrong-cut :shape :keyed :key "k"
                     :holders ((r :acquire (hdt-open hdt-open-holds :table 1 :result (mv-nth 1 _) :key k :ok (equal (mv-nth 0 _) :held))
                                  :release (hdt-close hdt-close-drops :table 1 :result (mv-nth 1 _) :key k :ok (equal (mv-nth 0 _) :dropped))))
                     :effect (:durable hdt-program "hdt-renamed") :complete-by "x")
                   :unchecked "the program names no such cut")
; A :durable effect naming a program that is not a function.
(must-fail-checked (def-holder hdt-no-program :shape :keyed :key "k"
                     :holders ((r :acquire (hdt-open hdt-open-holds :table 1 :result (mv-nth 1 _) :key k :ok (equal (mv-nth 0 _) :held))
                                  :release (hdt-close hdt-close-drops :table 1 :result (mv-nth 1 _) :key k :ok (equal (mv-nth 0 _) :dropped))))
                     :effect (:durable hdt-no-such-program "hdt-unlinked") :complete-by "x")
                   :unchecked "the program is not a function of this world")
; A logic holder over a value table with no :complete-by.
(must-fail-checked (def-holder hdt-incomplete :shape :keyed :key "k"
                     :holders ((r :acquire (hdt-open hdt-open-holds :table 1 :result (mv-nth 1 _) :key k :ok (equal (mv-nth 0 _) :held))
                                  :release (hdt-close hdt-close-drops :table 1 :result (mv-nth 1 _) :key k :ok (equal (mv-nth 0 _) :dropped))))
                     :effect (:process-local "x"))
                   :unchecked "a value table's holder list must say why it is complete")
; A :table position that is not a formal; a :key over a non-formal.
(must-fail-checked (def-holder hdt-bad-table :shape :keyed :key "k"
                     :holders ((r :acquire (hdt-open hdt-open-holds :table 4 :result (mv-nth 1 _) :key k :ok (equal (mv-nth 0 _) :held))
                                  :release (hdt-close hdt-close-drops :table 1 :result (mv-nth 1 _) :key k :ok (equal (mv-nth 0 _) :dropped))))
                     :effect (:process-local "x") :complete-by "x")
                   :unchecked ":table 4 is no formal of a two-formal function")
(must-fail-checked (def-holder hdt-bad-key :shape :keyed :key "k"
                     :holders ((r :acquire (hdt-open hdt-open-holds :table 1 :result (mv-nth 1 _) :key other :ok (equal (mv-nth 0 _) :held))
                                  :release (hdt-close hdt-close-drops :table 1 :result (mv-nth 1 _) :key k :ok (equal (mv-nth 0 _) :dropped))))
                     :effect (:process-local "x") :complete-by "x")
                   :unchecked "the key mentions a variable that is not a formal")
; A redeclared name.
(must-fail-checked (def-holder hdt-files :shape :keyed :key "k" :holders ((r :host t :acquire a :release b :in (c))) :effect (:process-local "x"))
                   :unchecked "hdt-files is already declared")
; An undeclared caller of the step: a function that holds without being a
; declared entry of any row is refused by def-holder-check (the progn is
; atomic: the world keeps neither).
(must-fail-checked (progn (defun hdt-rogue (k table)
                            (declare (xargs :guard (fn-arpn-pinsp table)))
                            (mv-nth 0 (fn-hd-keyed-step table (list :hold k))))
                          (def-holder-check hdt-files))
                   :unchecked "hdt-rogue calls the step and is no declared entry")
; After the refusal the check still passes: nothing rogue stayed.
(def-holder-check hdt-files)
