; Actual command -> LIST cursor -> private render-buffer windows.
; Fuel belongs only to this finite fixture and explicitly reports :limit.
(in-package "ACL2")
(include-book "../../books/served-query-plan")
(include-book "../../books/list-available-reference")
(include-book "served-available-commands-tests")

(defun qpt-drain (plan w fuel fn-octets fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-octets fn-arena fn-cat)))
  (cond
   ((fn-qplan-donep plan) (mv :done nil plan fn-octets))
   ((zp fuel) (mv :limit nil plan fn-octets))
   ((fn-qplan-at-cursorp plan)
    (mv-let (status next) (fn-qplan-cursor-step plan w fn-arena fn-cat)
      (if (eq status :ok)
          (qpt-drain next w (1- fuel) fn-octets fn-arena fn-cat)
        (mv status nil plan fn-octets))))
   (t
    (mv-let (status next fn-octets) (fn-qplan-window plan w fn-octets)
      (let ((front (fn-octets-list fn-octets)))
        (if (or (eq status :ok) (eq status :cursor))
            (mv-let (done more final fn-octets)
              (qpt-drain next w (1- fuel) fn-octets fn-arena fn-cat)
              (mv done (append front more) final fn-octets))
          (mv status front next fn-octets)))))))

(defun qpt-command (line archive index env w fn-octets fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-octets fn-arena fn-cat)))
  (let* ((session (fn-nntp-make-session t "fn.available" 1 t))
         (tokens (fn-nntp-tokenize (fn-nntp-string-octets line)))
         (result (fn-scr-command-available session archive index nil env tokens 34 fn-arena fn-cat))
         (counts (and (consp (cdr tokens))
                      (fn-nntp-keywordp (cadr tokens) "COUNTS")))
         (expected (if counts
                       (fn-av-nntp-list-counts-command-cat session archive
                         (fn-nntp-env-closed env) (cddr tokens) 34 fn-cat)
                     (fn-av-nntp-list-active-cat session archive
                       (fn-nntp-env-closed env) (cdr tokens) 34 fn-cat))))
    (mv-let (status octets final fn-octets)
      (qpt-drain (fn-splan-of-effects (fn-nntp-result-effects result)) w 100000
                 fn-octets fn-arena fn-cat)
      (mv (and (equal (fn-nntp-result-session result) (fn-nntp-result-session expected))
               (eq status :done) (fn-qplan-donep final)
               (equal octets (fn-served-reply-octets (fn-nntp-result-effects expected))))
          fn-octets))))

; The carried summary against the numbered walk the LIST cursor used to run
; (fn-scat-available-summary-is-the-walk): they agree where the group's high is
; below the allocation watermark, and a stale watermark (below the high) is the
; wrong-answer witness for that premise.
(defun qpt-walk-agreep (archive groups v fn-cat)
  (declare (xargs :mode :program :stobjs fn-cat))
  (if (consp groups)
      (and (equal (fn-scat-available-summary archive (car groups) v fn-cat)
                  (fn-lst-probe-summary
                   (car groups) (fn-next-number (car groups) (fn-state-nexts archive)) v fn-cat))
           (qpt-walk-agreep archive (cdr groups) v fn-cat))
    t))

(defun qpt-run (survivors w fn-octets fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-octets fn-arena fn-cat)))
  (let ((fn-cat (fn-cat-clear fn-cat)))
    (mv-let (fn-arena fn-cat) (cav-av-fill 0 34 survivors fn-arena fn-cat)
      (let* ((groups '("fn.empty0" "fn.empty1" "fn.empty2" "fn.empty3" "fn.empty4"
                      "fn.empty5" "fn.empty6" "fn.empty7" "fn.empty8" "fn.empty9"
                      "fn.available" "fn.empty10"))
             (archive (fn-make-state groups '(("fn.available" . 35))
                                     (cav-av-articles 34 34 fn-cat) 0 nil nil))
             (index (fn-gidx-pin-with-control
                                              (fn-gidx-build (fn-state-articles archive)) nil))
             (closed (list (list :moderated (fn-nntp-string-octets "fn.available") nil)
                           (fn-nntp-string-octets "fn.empty10")))
             (env (fn-nntp-env-with-closed nil nil nil closed))
             (cur (fn-lst-start archive closed t nil nil nil 34)))
        (mv-let (bout bnext bcalls bstatus) (fn-lst-batch cur 256 256 fn-cat)
         (mv-let (one-out one-next one-calls one-status) (fn-lst-batch cur 1 256 fn-cat)
         (mv-let (empty next calls state) (fn-lst-step cur 1 1 fn-cat)
          (declare (ignore state))
          (mv-let (a fn-octets) (qpt-command "LIST ACTIVE" archive index env w fn-octets fn-arena fn-cat)
            (mv-let (b fn-octets) (qpt-command "LIST ACTIVE fn.available" archive index env w fn-octets fn-arena fn-cat)
              (mv-let (c fn-octets) (qpt-command "LIST COUNTS fn.*,!fn.empty*" archive index env w fn-octets fn-arena fn-cat)
                (mv-let (d fn-octets) (qpt-command "LIST ACTIVE no.match.*" archive index env w fn-octets fn-arena fn-cat)
                  ;; Teeth for fn-scat-available-summary-is-the-walk: its premise
                  ;; holds of this actual intern/commit fixture (carried summary =
                  ;; numbered walk), and a stale watermark falsifies the agreement;
                  ;; the cursor still answers the model on the stale archive.
                  (let* ((agree (qpt-walk-agreep archive groups 34 fn-cat))
                         (stale (fn-make-state groups '(("fn.available" . 2))
                                               (fn-state-articles archive) 0 nil nil))
                         (stale-agree (qpt-walk-agreep stale groups 34 fn-cat)))
                    (mv-let (stale-ok fn-octets)
                      (qpt-command "LIST ACTIVE fn.available" stale index env w fn-octets fn-arena fn-cat)
                      (mv (and a b c d (null empty) (equal calls 1) (fn-lst-livep next)
                               ;; The batch spends the grant until the first row (positive
                               ;; witness: more than one call, stopped at the call that emitted); the
                               ;; one-visit batch is the single step (wrong-answer witness
                               ;; for a batch that ignores its grant), and the two
                               ;; cursors differ.
                               (< 1 bcalls) (<= bcalls 256) (eq bstatus :candidate) (consp bout)
                               (equal one-calls 1) (equal one-next next) (null one-out)
                               (eq one-status :yield)
                               (not (equal bnext one-next))
                               (fn-lst-livep bnext)
                               (eq (fn-cur-at 1 (fn-cur-progress next)) :status)
                               (equal (fn-cur-at 2 (fn-cur-progress next)) (cdr groups))
                               agree
                               (or (null survivors) (not stale-agree))
                               stale-ok)
                          fn-octets fn-arena fn-cat))))))))))))))

(defun qpt-local (survivors w)
  (declare (xargs :mode :program))
  (with-local-stobj fn-octets
    (mv-let (answer fn-octets)
      (with-local-stobj fn-arena
        (mv-let (answer fn-octets fn-arena)
          (with-local-stobj fn-cat
            (mv-let (answer fn-octets fn-arena fn-cat)
              (qpt-run survivors w fn-octets fn-arena fn-cat)
              (mv answer fn-octets fn-arena)))
          (mv answer fn-octets)))
      answer)))

; Can run additively in an older initialized native world: only new factory/
; query-plan names and private stobjs are used. Empty metadata has the same
; raw/available reference; this does not qualify changed catalog columns.
(defun qpt-empty-command (line archive env w fn-octets fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-octets fn-arena fn-cat)))
  (let* ((session (fn-nntp-make-session t nil nil t))
         (tokens (fn-nntp-tokenize (fn-nntp-string-octets line)))
         (args (cdr tokens))
         (counts (and (consp args) (fn-nntp-keywordp (car args) "COUNTS")))
         (result (if counts
                     (fn-lst-counts-command session archive (fn-nntp-env-closed env)
                                           (cdr args) 0 fn-cat)
                   (fn-lst-active-command session archive (fn-nntp-env-closed env)
                                          args 0 fn-cat)))
         (expected (fn-nntp-list-command session archive env args)))
    (mv-let (status octets final fn-octets)
      (qpt-drain (fn-splan-of-effects (fn-nntp-result-effects result)) w 100000
                 fn-octets fn-arena fn-cat)
      (mv (and (eq status :done) (fn-qplan-donep final)
               (equal octets (fn-served-reply-octets (fn-nntp-result-effects expected))))
          fn-octets))))

(defun qpt-empty-local (w)
  (declare (xargs :mode :program))
  (with-local-stobj fn-octets
    (mv-let (answer fn-octets)
      (with-local-stobj fn-arena
        (mv-let (answer fn-octets fn-arena)
          (with-local-stobj fn-cat
            (mv-let (answer fn-octets fn-arena fn-cat)
              (let* ((archive (fn-make-state '("fn.first" "fn.middle" "fn.last") nil nil 0 nil nil))
                     (env (fn-nntp-env-with-closed nil nil nil
                             (list (list :moderated (fn-nntp-string-octets "fn.middle") nil)
                                   (fn-nntp-string-octets "fn.last")))))
                (mv-let (a fn-octets) (qpt-empty-command "LIST ACTIVE" archive env w fn-octets fn-arena fn-cat)
                  (mv-let (b fn-octets) (qpt-empty-command "LIST COUNTS" archive env w fn-octets fn-arena fn-cat)
                    (mv-let (c fn-octets) (qpt-empty-command "LIST ACTIVE fn.*,!fn.first" archive env w fn-octets fn-arena fn-cat)
                      (mv-let (d fn-octets) (qpt-empty-command "LIST ACTIVE no.*" archive env w fn-octets fn-arena fn-cat)
                        (mv (and a b c d) fn-octets fn-arena fn-cat))))))
              (mv answer fn-octets fn-arena)))
          (mv answer fn-octets)))
      answer)))

(assert-event (qpt-local '(1 34) 1))
(assert-event (qpt-local '(1 34) 256))
(assert-event (qpt-local nil 1))
(assert-event (qpt-local nil 256))
(assert-event (qpt-empty-local 1))
(assert-event (qpt-empty-local 256))

; The skipped prefix of non-cursor effects before the first cursor is carried
; by a tail-recursive worker (fn-qplan-rest-cursor-step-acc): the step over
; PREFIX ++ SUFFIX is PREFIX ++ the step over SUFFIX (the logical recursion),
; for a three-effect prefix, and a prefix far deeper than the control stack
; of a non-tail recursion (the 100,000-article OVER crash) completes.
(defun qpt-skip-run (n w fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((archive (fn-make-state '("fn.first") nil nil 0 nil nil))
         (cur (fn-lst-start archive nil t nil nil nil 0))
         (suffix (list (fn-lst-effect cur) (fn-nntp-reply-effect '(65))))
         (e1 (fn-nntp-reply-effect '(1 2 3)))
         (prefix (make-list n :initial-element e1)))
    (mv-let (status-s next-s) (fn-qplan-rest-cursor-step suffix w fn-arena fn-cat)
      (mv-let (status next) (fn-qplan-rest-cursor-step (append prefix suffix) w fn-arena fn-cat)
        (and (eq status-s :ok) (eq status :ok)
             (equal next (append prefix next-s))
             (equal (mv-list 2 (fn-qplan-rest-cursor-step-acc (append prefix suffix) w nil fn-arena fn-cat))
                    (list status next)))))))

(defun qpt-skip-local (n w)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (answer fn-arena)
      (with-local-stobj fn-cat
        (mv-let (answer fn-arena fn-cat)
          (mv (qpt-skip-run n w fn-arena fn-cat) fn-arena fn-cat)
          (mv answer fn-arena)))
      (declare (ignore fn-arena))
      answer)))

(assert-event (qpt-skip-local 3 8))
(assert-event (qpt-skip-local 1000000 8))
