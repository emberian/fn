;; fn: teeth for books/config-policy-delta.lisp (PKT-601 (6), lane
;; config-consumer-catalog-2): the resumable application of a committed delta
;; under any schedule of quanta is the one-shot application
;; (fn-cfgp-apply-in-quanta-is-apply-delta).  The executable side runs both
;; on a live two-row catalog over a live arena (catalog-delta-tests' fixture);
;; per hypothesis a witness on which the retained hypotheses hold, the
;; omitted one fails and the conclusion fails, then the theorem without it
;; with the keystone's hints does not prove.

(in-package "ACL2")
(include-book "../../books/config-policy-delta")
(include-book "std/testing/must-fail" :dir :system)

(defconst *cpdt-p0* (append (fn-record-string-octets "Subject: a") '(13 10 13 10 65 13 10)))
(defconst *cpdt-p1* (append (fn-record-string-octets "Subject: b") '(13 10 13 10 66 13 10 67 13 10)))

(defun cpdt-held (seq msgid handle bytes)
  (fn-held-make seq (+ 1 seq) 0 msgid handle '("fn.test") "o" "s" "e" 1 5
                (fn-held-facts-of bytes) (fn-held-context-of bytes nil 0) nil nil))

(defconst *cpdt-h0* (cpdt-held 0 "<a@x>" 0 *cpdt-p0*))
(defconst *cpdt-h1* (cpdt-held 1 "<b@x>" 1 *cpdt-p1*))

(defun cpdt-build (fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((fn-arena (fn-arena-clear fn-arena))
         (fn-cat (fn-cat-clear fn-cat))
         (fn-arena (fn-arena-seal-list *cpdt-p0* fn-arena))
         (fn-arena (fn-arena-seal-list *cpdt-p1* fn-arena))
         (fn-cat (fn-cat-commit *cpdt-h0* fn-cat))
         (fn-cat (fn-cat-commit *cpdt-h1* fn-cat)))
    (mv fn-arena fn-cat)))

; What a run leaves in the rows: each row's context and withdrawal.
(defun cpdt-rows (fn-cat)
  (declare (xargs :mode :program :stobjs fn-cat))
  (list (fn-held-context (fn-cat-at 0 fn-cat)) (fn-held-withdrawn (fn-cat-at 0 fn-cat))
        (fn-held-context (fn-cat-at 1 fn-cat)) (fn-held-withdrawn (fn-cat-at 1 fn-cat))))

; (BEFORE ONE-SHOT IN-QUANTA) for delta D, the run started at CURSOR.
(defun cpdt-run (d cursor quanta fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (mv-let (fn-arena fn-cat)
    (cpdt-build fn-arena fn-cat)
    (let* ((before (cpdt-rows fn-cat))
           (fn-cat (fn-cat-apply-delta d nil fn-arena fn-cat))
           (one-shot (cpdt-rows fn-cat)))
      (mv-let (fn-arena fn-cat)
        (cpdt-build fn-arena fn-cat)
        (let* ((fn-cat (fn-cat-apply-in-quanta d cursor quanta nil fn-arena fn-cat)))
          (mv (list before one-shot (cpdt-rows fn-cat)) fn-arena fn-cat))))))

(defun cpdt (d cursor quanta)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (with-local-stobj fn-cat
        (mv-let (result fn-arena fn-cat)
          (cpdt-run d cursor quanta fn-arena fn-cat)
          (mv result fn-arena)))
      result)))

(defmacro cpdt-agrees (d cursor quanta)
  `(let ((r (cpdt ,d ,cursor ,quanta)))
     (equal (nth 1 r) (nth 2 r))))
(defmacro cpdt-moves (d cursor quanta)
  `(let ((r (cpdt ,d ,cursor ,quanta)))
     (not (equal (nth 0 r) (nth 1 r)))))

; -----------------------------------------------------------------------------
; The antecedents and the conclusion, non-degenerate: a :policy delta over
; both rows re-decides them under generation 1 (the rows change), and the
; run from the range's start agrees under quanta (1), (2 1) and (5); a
; :withdraw delta (one step) agrees too.
(defconst *cpdt-policy* (list :policy 1 0 2))
(assert-event (and (fn-delta-p *cpdt-policy*) (natp 0) (<= 0 (nfix (nth 2 *cpdt-policy*)))))
(assert-event (cpdt-moves *cpdt-policy* 0 '(1)))
(assert-event (cpdt-agrees *cpdt-policy* 0 '(1)))
(assert-event (cpdt-agrees *cpdt-policy* 0 '(2 1)))
(assert-event (cpdt-agrees *cpdt-policy* 0 '(5)))
(assert-event (equal (nth 1 (cpdt *cpdt-policy* 0 '(1)))
                     (list (fn-held-context-of *cpdt-p0* nil 1) nil
                           (fn-held-context-of *cpdt-p1* nil 1) nil)))
(assert-event (and (fn-delta-p (list :withdraw 0 2))
                   (cpdt-moves (list :withdraw 0 2) 0 '(1))
                   (cpdt-agrees (list :withdraw 0 2) 0 '(1))))

; The hypothesis witnesses run on the logical side (the list arena and the
; list catalog, as catalog-delta-tests does): the executable exports guard
; the malformed inputs out.
(defconst *cpdt-a* (list *cpdt-p0* *cpdt-p1*))
(defconst *cpdt-c* (list (fn-cat-assign *cpdt-h0* nil)
                         (fn-cat-assign *cpdt-h1* (list (fn-cat-assign *cpdt-h0* nil)))))
(defthm cpdt-w-positive
  (and (fn-delta-p *cpdt-policy*) (natp 0) (<= 0 (nfix (nth 2 *cpdt-policy*)))
       (equal (fn-cat-apply-in-quanta *cpdt-policy* 0 '(1) nil *cpdt-a* *cpdt-c*)
              (fn-cat-apply-delta *cpdt-policy* nil *cpdt-a* *cpdt-c*))
       (not (equal (fn-cat-apply-delta *cpdt-policy* nil *cpdt-a* *cpdt-c*) *cpdt-c*)))
  :rule-classes nil)

; (1) fn-delta-p.  A :policy delta whose range starts at -1: the one-shot
; application refuses a non-natural start (the identity), the resumable run
; reads it as 0 and re-decides both rows.
(defconst *cpdt-bad* (list :policy 1 -1 2))
(defthm cpdt-w-without-delta-p
  (and (not (fn-delta-p *cpdt-bad*)) (natp 0) (<= 0 (nfix (nth 2 *cpdt-bad*)))
       (not (equal (fn-cat-apply-in-quanta *cpdt-bad* 0 '(1) nil *cpdt-a* *cpdt-c*)
                   (fn-cat-apply-delta *cpdt-bad* nil *cpdt-a* *cpdt-c*))))
  :rule-classes nil)
(must-fail
 (defthm fn-cpdt-without-delta-p
  (implies (and (natp cursor) (<= cursor (nfix (nth 2 d))))
           (equal (fn-cat-apply-in-quanta d cursor quanta keyring fn-arena fn-cat)
                  (fn-cat-apply-delta d keyring fn-arena fn-cat)))
  :hints (("Goal"
            :do-not-induct t
            :cases ((equal (car d) :policy))
            :in-theory (e/d (fn-delta-p)
                            (fn-cat-recontext-range fn-cat-count-is-len
                             fn-cat-at-is-nth fn-cat-p-is-rowsp
                             fn-cat-apply-delta-step fn-cat-withdraw
                             fn-cat-redecide fn-dart-p)))
           ("Subgoal 2" :expand ((fn-cat-apply-in-quanta d cursor quanta keyring
                                                         fn-arena fn-cat)))
           ("Subgoal 1" :in-theory (e/d (fn-delta-p fn-cat-apply-delta)
                                        (fn-cat-recontext-range fn-cat-count-is-len
                                         fn-cat-at-is-nth fn-cat-p-is-rowsp
                                         fn-cat-apply-in-quanta min max))))))

; (2) natp of the cursor.  From -1 the run takes one step (row 0) and stops.
(defthm cpdt-w-without-natp-cursor
  (and (fn-delta-p *cpdt-policy*) (not (natp -1))
       (<= -1 (nfix (nth 2 *cpdt-policy*)))
       (not (equal (fn-cat-apply-in-quanta *cpdt-policy* -1 '(1) nil *cpdt-a* *cpdt-c*)
                   (fn-cat-apply-delta *cpdt-policy* nil *cpdt-a* *cpdt-c*))))
  :rule-classes nil)
(must-fail
 (defthm fn-cpdt-without-natp-cursor
  (implies (and (fn-delta-p d) (<= cursor (nfix (nth 2 d))))
           (equal (fn-cat-apply-in-quanta d cursor quanta keyring fn-arena fn-cat)
                  (fn-cat-apply-delta d keyring fn-arena fn-cat)))
  :hints (("Goal"
            :do-not-induct t
            :cases ((equal (car d) :policy))
            :in-theory (e/d (fn-delta-p)
                            (fn-cat-recontext-range fn-cat-count-is-len
                             fn-cat-at-is-nth fn-cat-p-is-rowsp
                             fn-cat-apply-delta-step fn-cat-withdraw
                             fn-cat-redecide fn-dart-p)))
           ("Subgoal 2" :expand ((fn-cat-apply-in-quanta d cursor quanta keyring
                                                         fn-arena fn-cat)))
           ("Subgoal 1" :in-theory (e/d (fn-delta-p fn-cat-apply-delta)
                                        (fn-cat-recontext-range fn-cat-count-is-len
                                         fn-cat-at-is-nth fn-cat-p-is-rowsp
                                         fn-cat-apply-in-quanta min max))))))

; (3) the cursor at or before the range.  From 1 the run re-decides row 1
; only; the one-shot application both.
(defthm cpdt-w-without-cursor-bound
  (and (fn-delta-p *cpdt-policy*) (natp 1)
       (not (<= 1 (nfix (nth 2 *cpdt-policy*))))
       (not (equal (fn-cat-apply-in-quanta *cpdt-policy* 1 '(1) nil *cpdt-a* *cpdt-c*)
                   (fn-cat-apply-delta *cpdt-policy* nil *cpdt-a* *cpdt-c*))))
  :rule-classes nil)
(assert-event (not (cpdt-agrees *cpdt-policy* 1 '(1))))
(must-fail
 (defthm fn-cpdt-without-cursor-bound
  (implies (and (fn-delta-p d) (natp cursor))
           (equal (fn-cat-apply-in-quanta d cursor quanta keyring fn-arena fn-cat)
                  (fn-cat-apply-delta d keyring fn-arena fn-cat)))
  :hints (("Goal"
            :do-not-induct t
            :cases ((equal (car d) :policy))
            :in-theory (e/d (fn-delta-p)
                            (fn-cat-recontext-range fn-cat-count-is-len
                             fn-cat-at-is-nth fn-cat-p-is-rowsp
                             fn-cat-apply-delta-step fn-cat-withdraw
                             fn-cat-redecide fn-dart-p)))
           ("Subgoal 2" :expand ((fn-cat-apply-in-quanta d cursor quanta keyring
                                                         fn-arena fn-cat)))
           ("Subgoal 1" :in-theory (e/d (fn-delta-p fn-cat-apply-delta)
                                        (fn-cat-recontext-range fn-cat-count-is-len
                                         fn-cat-at-is-nth fn-cat-p-is-rowsp
                                         fn-cat-apply-in-quanta min max))))))
