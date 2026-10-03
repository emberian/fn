; Actual command -> LIST cursor -> private render-buffer windows.
; Fuel belongs only to this finite fixture and explicitly reports :limit.
(in-package "ACL2")
(include-book "../../books/served-query-plan")
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

(defun qpt-run (survivors w fn-octets fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-octets fn-arena fn-cat)))
  (let ((fn-cat (fn-cat-clear fn-cat)))
    (mv-let (fn-arena fn-cat) (cav-av-fill 0 34 survivors fn-arena fn-cat)
      (let* ((groups '("fn.empty0" "fn.empty1" "fn.empty2" "fn.empty3" "fn.empty4"
                      "fn.empty5" "fn.empty6" "fn.empty7" "fn.empty8" "fn.empty9"
                      "fn.available" "fn.empty10"))
             (archive (fn-make-state groups '(("fn.available" . 35))
                                     (cav-av-articles 34 34 fn-cat) 0 nil nil))
             (index (fn-gidx-pin-with-control (fn-midx-build (fn-state-articles archive))
                                              (fn-gidx-build (fn-state-articles archive)) nil))
             (closed (list (list :moderated (fn-nntp-string-octets "fn.available") nil)
                           (fn-nntp-string-octets "fn.empty10")))
             (env (fn-nntp-env-with-closed nil nil nil closed))
             (cur (fn-lst-start archive closed t nil nil nil 34)))
        (mv-let (empty next calls state) (fn-lst-step cur 1 1 fn-cat)
          (declare (ignore state))
          (mv-let (a fn-octets) (qpt-command "LIST ACTIVE" archive index env w fn-octets fn-arena fn-cat)
            (mv-let (b fn-octets) (qpt-command "LIST ACTIVE fn.available" archive index env w fn-octets fn-arena fn-cat)
              (mv-let (c fn-octets) (qpt-command "LIST COUNTS fn.*,!fn.empty*" archive index env w fn-octets fn-arena fn-cat)
                (mv-let (d fn-octets) (qpt-command "LIST ACTIVE no.match.*" archive index env w fn-octets fn-arena fn-cat)
                  (mv (and a b c d (null empty) (equal calls 1) (fn-lst-livep next)
                           (eq (fn-cur-at 1 (fn-cur-progress next)) :next)
                           (equal (fn-cur-at 2 (fn-cur-progress next)) (cdr groups)))
                      fn-octets fn-arena fn-cat))))))))))

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
