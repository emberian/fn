; Teeth for the defadt prototype (lane proto-adt, 2026-09-27):
; books/proto/adt-lib.lisp, books/proto/adt.lisp,
; books/proto/adt-consumer-position.lisp.
;
; 1. Genericity: two unrelated record types declared with `defadt' and no
;    other event (a held-row-like type and a config-entry-like type).
; 2. Positive witnesses, executed: each instance's EXECUTABLE (typed columns,
;    pool, raw-Lisp live stobj via with-local-stobj) answers what its LOGICAL
;    side (list of records) answers, for append, set, count and every get.
; 3. The library keystones (adt-corr-append, adt-corr-set, adt-corr-get)
;    at ground instances: a reachable positive witness with every hypothesis
;    and the conclusion checked, and one hypothesis-removal witness per
;    hypothesis that checks the retained hypotheses, the failure of the
;    omitted one, and the failure of the conclusion.
; 4. The invasiveness probe's bridge (cpent-find-is-fn-cp-find) and the
;    carried theorem, at a concrete table.

(in-package "ACL2")
(include-book "../../books/proto/adt-consumer-position")
(include-book "std/testing/assert-bang" :dir :system)

; -----------------------------------------------------------------------------
; 1. Two instances.

(defadt held
  (id :u64) (msgid :octets) (size (:nat 1000000)) (flag :bool) (kind (:enum :a :b :c)))

(defadt cfgent
  (key :octets) (value :octets) (version :u32) (live :bool)
  (scope (:enum :global :group :peer)) (ttl (:nat 86400)) (weight :u8))

; -----------------------------------------------------------------------------
; 2. Executed witnesses: the live stobj's answers equal the logical answers.

(defconst *held-r0* '(7 (104 105) 42 t :b))
(defconst *held-r1* '(18446744073709551615 (1 2 3 4 5) 1000000 nil :c))

(defun held-run ()
  (declare (xargs :guard t))
  (with-local-stobj held
    (mv-let (out held)
      (let* ((held (held-append *held-r0* held))
             (held (held-append *held-r1* held))
             (held (held-set-msgid 0 '(200 201 202) held))
             (held (held-set-kind 1 :a held)))
        (mv (list (held-count held)
                  (held-get-id 0 held) (held-get-msgid 0 held) (held-get-size 0 held)
                  (held-get-flag 0 held) (held-get-kind 0 held)
                  (held-get-id 1 held) (held-get-msgid 1 held) (held-get-size 1 held)
                  (held-get-flag 1 held) (held-get-kind 1 held))
            held))
      out)))

; The same program over the logical value.
(defun held-logic ()
  (let* ((a (append (append nil (list *held-r0*)) (list *held-r1*)))
         (a (update-nth 0 (update-nth 1 '(200 201 202) (nth 0 a)) a))
         (a (update-nth 1 (update-nth 4 :a (nth 1 a)) a)))
    (cons (len a)
          (append (nth 0 a) (nth 1 a)))))

(assert-event (equal (held-run) (held-logic)))
(assert-event (equal (held-run)
                     '(2 7 (200 201 202) 42 t :b
                         18446744073709551615 (1 2 3 4 5) 1000000 nil :a)))

(defun cfgent-fill (n cfgent)
  (declare (xargs :stobjs cfgent :guard (natp n)))
  (if (zp n)
      cfgent
    (let* ((b (if (< n 256) n 0))
           (cfgent (cfgent-append (list (list b) (list 1 2 b) 5
                                        (evenp n) :group (if (<= n 86400) n 0) b)
                                  cfgent)))
      (cfgent-fill (1- n) cfgent))))

(defun cfgent-run (n)
  ; N appends of one entry (every column grows past its first doubling),
  ; then a set of an octets field in the middle row.
  (declare (xargs :guard (natp n)))
  (with-local-stobj cfgent
    (mv-let (out cfgent)
      (let* ((cfgent (cfgent-fill n cfgent))
             (cfgent (if (< 3 (cfgent-count cfgent))
                         (cfgent-set-value 3 '(9 9 9 9) cfgent)
                       cfgent)))
        (mv (list (cfgent-count cfgent)
                  (if (< 3 (cfgent-count cfgent)) (cfgent-get-value 3 cfgent) nil)
                  (if (< 4 (cfgent-count cfgent)) (cfgent-get-value 4 cfgent) nil)
                  (if (< 4 (cfgent-count cfgent)) (cfgent-get-version 4 cfgent) nil)
                  (if (< 4 (cfgent-count cfgent)) (cfgent-get-scope 4 cfgent) nil))
            cfgent))
      out)))

; 40 appends: row 3 was written by the 37th append (n = 37), row 4 by n = 36.
(assert-event (equal (cfgent-run 40)
                     (list 40 '(9 9 9 9) (list 1 2 36) 5 :group)))

; -----------------------------------------------------------------------------
; 3. The library keystones at ground instances (the functions the instance
;    bridges rewrite to, over the stobj's logical image).  Guard checking is
;    off in these forms: a hypothesis-removal witness calls the logical
;    operation outside its guard on purpose.

(defconst *s* *cfgent-schema*)
(defconst *c0* (adt-empty-c *s*))
(defconst *rec* '((1 2) (3) 5 t :peer 60 7))
(defconst *c1* (adt-append-c *s* *rec* *c0*))

; adt-corr-append: (adt-corr s c a) and (adt-rec-p s rec) imply
; (adt-corr s (adt-append-c s rec c) (append a (list rec))).
(assert-event (with-guard-checking :none (and (adt-corr *s* *c0* nil)
                   (adt-rec-p *s* *rec*)
                   (adt-corr *s* *c1* (append nil (list *rec*))))))
; without (adt-rec-p s rec): a u32 field at 2^32
(assert-event (with-guard-checking :none (let ((bad '((1 2) (3) 4294967296 t :peer 60 7)))
                (and (adt-corr *s* *c0* nil)
                     (not (adt-rec-p *s* bad))
                     (not (adt-corr *s* (adt-append-c *s* bad *c0*) (list bad)))))))
; without (adt-corr s c a): an empty store paired with a one-record list
(assert-event (with-guard-checking :none (and (adt-rec-p *s* *rec*)
                   (not (adt-corr *s* *c0* (list *rec*)))
                   (not (adt-corr *s* (adt-append-c *s* *rec* *c0*)
                                  (append (list *rec*) (list *rec*)))))))

; adt-corr-set: (adt-corr s c a), natp j, j < |s|, natp i, i < |a|,
; (adt-val-okp (nth j s) v) imply
; (adt-corr s (adt-set-c s j i v c) (adt-set-a j i v a)).
(assert-event (with-guard-checking :none (and (adt-corr *s* *c1* (list *rec*))
                   (< 1 (len *s*)) (< 0 (len (list *rec*)))
                   (adt-val-okp (nth 1 *s*) '(5 6))
                   (adt-corr *s* (adt-set-c *s* 1 0 '(5 6) *c1*)
                             (adt-set-a 1 0 '(5 6) (list *rec*)))
                   (equal (adt-set-a 1 0 '(5 6) (list *rec*))
                          '(((1 2) (5 6) 5 t :peer 60 7))))))
; without j < |s|: j = 7
(assert-event (with-guard-checking :none (and (adt-corr *s* *c1* (list *rec*))
                   (not (< 7 (len *s*)))
                   (not (adt-corr *s* (adt-set-c *s* 7 0 3 *c1*)
                                  (adt-set-a 7 0 3 (list *rec*)))))))
; without i < |a|: i = 1 on a one-record store
(assert-event (with-guard-checking :none (and (adt-corr *s* *c1* (list *rec*))
                   (adt-val-okp (nth 2 *s*) 9)
                   (not (< 1 (len (list *rec*))))
                   (not (adt-corr *s* (adt-set-c *s* 2 1 9 *c1*)
                                  (adt-set-a 2 1 9 (list *rec*)))))))
; without (adt-val-okp (nth j s) v): an enum value outside the sum
(assert-event (with-guard-checking :none (and (adt-corr *s* *c1* (list *rec*))
                   (not (adt-val-okp (nth 4 *s*) :nowhere))
                   (not (adt-corr *s* (adt-set-c *s* 4 0 :nowhere *c1*)
                                  (adt-set-a 4 0 :nowhere (list *rec*)))))))
; without (adt-corr s c a)
(assert-event (with-guard-checking :none (and (not (adt-corr *s* *c0* (list *rec*)))
                   (adt-val-okp (nth 2 *s*) 9)
                   (not (adt-corr *s* (adt-set-c *s* 2 0 9 *c0*)
                                  (adt-set-a 2 0 9 (list *rec*)))))))
; natp j and natp i are REDUNDANT in adt-corr-set: both sides fix a
; non-natural index to 0 (zp / nfix), so no witness can falsify the
; conclusion without also violating another hypothesis.  The weakened
; theorem is not proved here; this checks the redundancy at j = 1/2.
(assert-event (with-guard-checking :none (adt-corr *s* (adt-set-c *s* 1/2 0 '(8) *c1*)
                        (adt-set-a 1/2 0 '(8) (list *rec*)))))

; adt-corr-get: (adt-corr s c a), natp j, j < |s|, natp i, i < |a| imply
; (adt-get-c s j i c) = (nth j (nth i a)) and (adt-get-okp s j i c).
(assert-event (with-guard-checking :none (and (adt-corr *s* *c1* (list *rec*))
                   (equal (adt-get-c *s* 1 0 *c1*) '(3))
                   (equal (adt-get-c *s* 4 0 *c1*) :peer)
                   (adt-get-okp *s* 1 0 *c1*))))
; without i < |a|: row 1 exists in the columns (capacity 2) but not in the ADT
(assert-event (with-guard-checking :none (and (adt-corr *s* *c1* (list *rec*))
                   (< 1 (len (nth 2 *c1*)))
                   (not (equal (adt-get-c *s* 2 1 *c1*) (nth 2 (nth 1 (list *rec*))))))))
; without j < |s|: no field 7; the read is not permitted
(assert-event (with-guard-checking :none (and (adt-corr *s* *c1* (list *rec*))
                   (not (adt-get-okp *s* 7 0 *c1*)))))
; without (adt-corr s c a)
(assert-event (with-guard-checking :none (and (not (adt-corr *s* *c0* (list *rec*)))
                   (not (equal (adt-get-c *s* 2 0 *c0*) (nth 2 (nth 0 (list *rec*))))))))

; The canonical image: two histories with one logical value reach two
; different images (the set leaves (3) in the pool), both corresponding;
; the canonical image of the value is the append-only one.
(assert-event (with-guard-checking :none
 (let* ((r2 '((1 2) (5 6) 5 t :peer 60 7))
        (img-a (adt-set-c *s* 1 0 '(5 6) *c1*))
        (img-b (adt-append-c *s* r2 *c0*))
        (a (adt-set-a 1 0 '(5 6) (list *rec*))))
   (and (equal a (list r2))
        (adt-corr *s* img-a a)
        (adt-corr *s* img-b a)
        (not (equal img-a img-b))
        (equal (adt-canon *s* a) img-b)))))

;; -----------------------------------------------------------------------------
; 4. The invasiveness probe (now over `defadt-keyed', lane proto-adt-2): the
;    keyed stobj finds what `fn-cp-find' finds over the logical value, the
;    carried epoch bound holds, and the rebase step on the columns is the
;    model's.

(defconst *cp-e0* '(:entry (1 2) (3) (4 5) 1 1 3 0))
(defconst *cp-e1* '(:entry (9) (3) (4 5) 1 1 4 2))
(defconst *cp-e1b* '(:entry (9) (3) (6) 2 1 5 0))

(defun cpent-probe (c)
  ; the table (e0 e1): e1 inserted first, e0 consed in front of it
  (with-local-stobj cpent
    (mv-let (out cpent)
      (let* ((cpent (cpent-insert *cp-e1* cpent))
             (cpent (cpent-insert *cp-e0* cpent)))
        (mv (cpent-find c cpent) cpent))
      out)))

(defun cpent-rebase-probe ()
  (with-local-stobj cpent
    (mv-let (out cpent)
      (let* ((cpent (cpent-insert *cp-e1* cpent))
             (cpent (cpent-insert *cp-e0* cpent))
             (cpent (cpent-rebase '(9) *cp-e1b* cpent)))
        (mv (list (cpent-find '(9) cpent) (cpent-find '(1 2) cpent) (cpent-has '(7) cpent)) cpent))
      out)))

(assert-event (let ((tbl (list *cp-e0* *cp-e1*)))
                (and (fn-cp-entriesp tbl 5 6)
                     (cpentp tbl)
                     (equal (cpent-probe '(9)) *cp-e1*)
                     (equal (fn-cp-find '(9) tbl) *cp-e1*)
                     (< (nth 6 (cpent-probe '(9))) 6))))
; without (fn-cp-entriesp ...): an epoch at next-epoch is found and breaks the bound
(assert-event (let ((tbl (list *cp-e0* *cp-e1*)))
                (and (not (fn-cp-entriesp tbl 5 4))
                     (equal (cpent-probe '(9)) *cp-e1*)
                     (not (< (nth 6 (cpent-probe '(9))) 4)))))
; without the find: absent consumer, nothing found
(assert-event (and (equal (cpent-probe '(8)) nil)
                   (equal (fn-cp-find '(8) (list *cp-e0* *cp-e1*)) nil)))
; the rebase step on the columns is the model's (cons e (fn-cp-remove c es))
(assert-event (let ((model (cons *cp-e1b* (fn-cp-remove '(9) (list *cp-e0* *cp-e1*)))))
                (and (equal model (list *cp-e1b* *cp-e0*))
                     (equal (cpent-rebase-probe)
                            (list (fn-cp-find '(9) model) (fn-cp-find '(1 2) model) nil)))))
