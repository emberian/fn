; PRF-1362: successful configuration crossing, cursor preservation, costs,
; wrong-tail mutation, and the executed (rather than logical MBE) closure.
(in-package "ACL2")
(include-book "../../books/paged-checkpoint-cursor")
(include-book "store-finalize-incremental-tests")

; Test-only raw wrapper, matching the existing carried-trie teeth. The
; production entry is logic mode and guard verified. Logical MBE evaluation
; answers from the node, so only raw execution can expose a wrong carried IX.
(defun pckc-raw-resume (r rest events ix)
  (declare (xargs :mode :program))
  (fn-pck-cpr-resume-from r rest events ix))

(defun pckc-raw-steps (r rest events ix)
  (declare (xargs :mode :program))
  (fn-pck-cpr-resume-from-steps r rest events ix))
(defun pckc-raw-consumed (r rest ix deltas)
  (declare (xargs :mode :program))
  (fn-pck-publications-configs-consumed r rest ix deltas))

(defconst *pckc-base*
  (fn-sco-capture *sfi-t-configs* (list *sfi-t-undertake* *sfi-t-release*)))
(defconst *pckc-r* (fn-sco-cpr *pckc-base*))
(defconst *pckc-ix* (fn-sfi-carry *pckc-base*))
(defconst *pckc-rest* (nthcdr (fn-sco-at 2 *pckc-r*) *sfi-t-configs*))
(defconst *pckc-delta* (list *sfi-t-article*))
(defconst *pckc-out*
  (list (fn-sco-cpr *sfi-t-base*) (fn-sfi-carry *sfi-t-base*) nil))

(defthm pckc-open-producer-has-the-whole-cursor-invariant
  (fn-pck-cpr-cursorp *pckc-r* *pckc-ix* *pckc-rest* *sfi-t-configs*)
  :hints (("Goal" :use ((:instance fn-pck-cpr-cursor-at-open (c *pckc-base*)
                            (configs *sfi-t-configs*)))
           :in-theory (disable fn-pck-cpr-cursorp fn-pck-cpr-cursor-at-open))))

(assert-event
 (and (consp *pckc-delta*)
      (fn-sco-pausedp (car *pckc-out*))
      (equal (car *pckc-out*)
             (fn-sco-cpr-resume *pckc-r* *sfi-t-configs* *pckc-delta*))
      (equal (fn-pck-configs-consumed *pckc-r* (car *pckc-out*)) 2)
      (equal (pckc-raw-steps *pckc-r* *pckc-rest*
                                          *pckc-delta* *pckc-ix*) 3)
      (equal (pckc-raw-consumed
              *pckc-r* *pckc-rest* *pckc-ix*
              (list *pckc-delta* *sfi-t-q* nil)) 2)
      (<= (pckc-raw-consumed
           *pckc-r* *pckc-rest* *pckc-ix* (list *pckc-delta* *sfi-t-q* nil))
          (len *sfi-t-configs*))))

(assert-event
 (and (not (equal (cdr *pckc-rest*) *pckc-rest*))
      (not (equal (car (pckc-raw-resume
                       *pckc-r* (cdr *pckc-rest*) *pckc-delta* *pckc-ix*))
                  (fn-sco-cpr-resume *pckc-r* *sfi-t-configs* *pckc-delta*)))))
(must-fail-checked
 (defthm pckc-wrong-rest-still-resumes
   (equal (car (fn-pck-cpr-resume-from
                *pckc-r* (cdr *pckc-rest*) *pckc-delta* *pckc-ix*))
          (fn-sco-cpr-resume *pckc-r* *sfi-t-configs* *pckc-delta*))))

(assert-event
 (let ((calls (sfi-t-exec-closure '(fn-pck-cpr-resume-from) nil (w state))))
   (and (not (intersection-eq
              '(fn-cnode-statep fn-rii-ix-of fn-sco-drop fn-sco-nthcdr
                fn-sco-extend fn-rii-sco-extend fn-cei-build-aux)
              calls))
        (member-eq 'fn-sfi-cpr-prefix-carried calls)
        (member-eq 'fn-pck-config-tail calls))))

(assert-event
 (equal (pckc-raw-resume *pckc-r* *pckc-rest* *pckc-delta* *pckc-ix*)
        *pckc-out*))

(assert-event
 (let* ((r (fn-sco-cpr *sfi-t-base*))
        (rest (nthcdr (fn-sco-at 2 r) *sfi-t-configs*))
        (bad (pckc-raw-resume r rest *sfi-t-q-dup* *sfi-t-ix-wrong*))
        (good (pckc-raw-resume r rest *sfi-t-q-dup* *sfi-t-ix*)))
   (and (fn-sco-pausedp r)
        (not (equal (car *sfi-t-ix-wrong*) (car *sfi-t-ix*)))
        (fn-sco-pausedp (car bad))
        (equal (car good) (fn-sco-cpr-resume r *sfi-t-configs* *sfi-t-q-dup*))
        (equal (fn-replay-result-kind (car good)) :fault))))

(must-fail-checked
 (assert-event
  (let* ((r (fn-sco-cpr *sfi-t-base*))
         (rest (nthcdr (fn-sco-at 2 r) *sfi-t-configs*)))
    (equal (car (pckc-raw-resume r rest *sfi-t-q-dup* *sfi-t-ix-wrong*))
           (fn-sco-cpr-resume r *sfi-t-configs* *sfi-t-q-dup*)))))

(assert-event
 (let ((bad (fn-sco-make nil '(:fault) nil nil nil nil)))
   (and (not (fn-sfi-carry bad))
        (not (fn-pck-cpr-cursorp (fn-sco-cpr bad) nil nil nil)))))
(must-fail-checked
 (assert-event
  (let ((bad (fn-sco-make nil '(:fault) nil nil nil nil)))
    (fn-pck-cpr-cursorp (fn-sco-cpr bad) (fn-sfi-carry bad) nil nil))))
