; LIST ACTIVE/COUNTS keeps captured group/next/config references and advances
; matcher, next-watermark lookup, number probes and status entries separately.
; Row construction is still a whole-row allocation: profile/string/integer and
; catalog lookup tariffs plus captured-column stability remain explicit debt.
(in-package "ACL2")
(include-book "group-summary-cursor")
(include-book "wildmat-cursor")
(include-book "def-cursor")
(include-book "protocol-table")

(local (in-theory (disable (tau-system))))

; Environment: archive closed statusp countsp parsed-patterns filteredp version.
; Progress: environment phase remaining-groups current-group detail summary calls.
(defun fn-lst-env (archive closed statusp countsp patterns filteredp v)
  (declare (xargs :guard t))
  (list archive closed statusp countsp patterns filteredp (nfix v)))

(defun fn-lst-progress (env phase groups group detail summary calls)
  (declare (xargs :guard t))
  (list env phase groups group detail summary (nfix calls)))

(defun fn-lst-start (archive closed statusp countsp patterns filteredp v)
  (declare (xargs :guard t))
  (let ((env (fn-lst-env archive closed statusp countsp patterns filteredp v)))
    (fn-cur-make env (fn-lst-progress env :group (fn-state-groups archive) nil nil nil 0) nil nil)))

(defun fn-lst-call-metric (progress)
  (declare (xargs :guard t))
  (- (nfix (fn-cur-at 6 progress))))

(defun fn-lst-line (group summary countsp status)
  (declare (xargs :guard t))
  (fn-nntp-append-pieces
   (append (list (fn-nntp-string-octets group) '(32)
                 (fn-nntp-decimal-field (fn-nntp-summary-high summary)) '(32)
                 (fn-nntp-decimal-field (fn-nntp-summary-low summary)))
           (if countsp (list '(32) (fn-nntp-decimal-field (fn-nntp-summary-count summary))) nil)
           (list '(32) (fn-nntp-string-octets status)))))

(defun fn-lst-one (progress fn-cat)
  (declare (xargs :stobjs fn-cat :guard t :verify-guards nil))
  (let* ((env (fn-cur-at 0 progress))
         (phase (fn-cur-at 1 progress))
         (groups (fn-cur-at 2 progress))
         (group (fn-cur-at 3 progress))
         (detail (fn-cur-at 4 progress))
         (summary (fn-cur-at 5 progress))
         (calls (+ 1 (nfix (fn-cur-at 6 progress))))
         (archive (fn-cur-at 0 env))
         (closed (fn-cur-at 1 env))
         (statusp (fn-cur-at 2 env))
         (countsp (fn-cur-at 3 env))
         (patterns (fn-cur-at 4 env))
         (filteredp (fn-cur-at 5 env))
         (v (nfix (fn-cur-at 6 env))))
    (cond
     ((eq phase :group)
      (if (consp groups)
          (mv nil (fn-lst-progress env (if filteredp :match :next) (cdr groups)
                        (car groups)
                        (if filteredp (fn-wmc-start patterns (car groups)) (fn-state-nexts archive))
                        nil calls))
        (mv '(46 13 10) nil)))
     ((eq phase :match)
      (if (fn-wmc-decidedp detail)
          (mv nil (fn-lst-progress env (if (fn-wmc-matchedp detail) :next :group)
                      groups group (fn-state-nexts archive) nil calls))
        (mv nil (fn-lst-progress env :match groups group
                    (fn-wmc-step detail 1 (fn-wmc-demand detail)) nil calls))))
     ((eq phase :next)
      (if (and (consp detail) (not (equal group (fn-ag-car (car detail)))))
          (mv nil (fn-lst-progress env :next groups group (cdr detail) nil calls))
        (let ((next (nfix (if (consp detail) (fn-ag-cdr (car detail)) 0))))
          (mv nil (fn-lst-progress env :summary groups group
                     (fn-gsc-start group (if (posp next) (- next 1) 0) next v) nil calls)))))
     ((eq phase :summary)
      (if (posp (fn-gsc-remaining detail))
          (mv nil (fn-lst-progress env :summary groups group (fn-gsc-one detail fn-cat) nil calls))
        (mv nil (fn-lst-progress env (if (or statusp countsp) :status :row) groups group
                       (if (or statusp countsp)
                           (list closed (fn-nntp-string-octets group) nil) "y")
                       (fn-gsc-summary detail) calls))))
     ((eq phase :status)
      (let ((tail (fn-cur-at 0 detail)) (octets (fn-cur-at 1 detail)) (moderated (fn-cur-at 2 detail)))
        (if (consp tail)
            (if (equal octets (car tail))
                (mv nil (fn-lst-progress env :row groups group "n" summary calls))
              (mv nil (fn-lst-progress env :status groups group
                          (list (cdr tail) octets
                                (or moderated (and (fn-nntp-moderated-entryp (car tail))
                                                   (equal (fn-cur-at 1 (car tail)) octets))))
                          summary calls)))
          (mv nil (fn-lst-progress env :row groups group (if moderated "m" "y") summary calls)))))
     ((eq phase :row)
      (mv (fn-nntp-stuff-lines (list (fn-lst-line group summary countsp detail)))
          (fn-lst-progress env :group groups nil nil nil calls)))
     (t (mv '(46 13 10) nil)))))

(local
 (defthm fn-lst-progress-calls
   (equal (fn-cur-at 6 (fn-lst-progress env phase groups group detail summary calls))
          (nfix calls))
   :hints (("Goal" :in-theory (enable fn-cur-at fn-lst-progress)))))

; This literal metric counts controller calls, not bytes or catalog internals.
(defthm fn-lst-one-control-at-most-one
  (<= (- (fn-lst-call-metric progress)
          (fn-lst-call-metric (mv-nth 1 (fn-lst-one progress fn-cat)))) 1)
  :hints (("Goal" :in-theory
           (e/d (fn-lst-one fn-lst-call-metric)
                (fn-lst-progress fn-cur-at fn-wmc-start fn-wmc-step fn-wmc-demand
                 fn-wmc-decidedp fn-wmc-matchedp fn-state-nexts fn-state-groups
                 fn-gsc-one fn-gsc-start fn-gsc-remaining fn-gsc-summary
                 fn-nntp-moderated-entryp fn-nntp-stuff-lines fn-lst-line)))))

(local (in-theory (disable fn-lst-one fn-lst-progress fn-lst-env fn-lst-call-metric)))

(def-cursor fn-lst (fn-cat) :stobjs (fn-cat)
  :call (fn-lst-one progress fn-cat)
  :visit-proof fn-lst-one-control-at-most-one
  :visit-metric (fn-lst-call-metric progress))

(verify-guards fn-lst-one)
(verify-guards fn-lst-step :hints (("Goal" :in-theory (disable fn-lst-one fn-cur-split))))

(defun fn-lst-effect (cur)
  (declare (xargs :guard t))
  (list :list-cursor cur))

(defun fn-lst-effectp (effect)
  (declare (xargs :guard t))
  (and (consp effect) (eq (car effect) :list-cursor) (consp (cdr effect))))

(defun fn-lst-livep (cur)
  (declare (xargs :guard t))
  (or (fn-cur-progress cur) (consp (fn-cur-pending cur)) (fn-cur-dependency cur)))

(defun fn-lst-result (session archive closed statusp countsp patterns filteredp v)
  (declare (xargs :guard t))
  (fn-nntp-make-result session
   (list (fn-nntp-reply-effect
           (fn-nntp-crlf (fn-nntp-string-octets (if countsp (fn-proto-text "LIST" :newsgroups) (fn-proto-text "LIST" :active)))))
         (fn-lst-effect (fn-lst-start archive closed statusp countsp patterns filteredp v)))))

(defun fn-lst-active-command (session archive closed args v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)) (ignore fn-cat))
  (let ((arguments (if (consp args) (cdr args) nil)))
    (if (null arguments)
        (fn-lst-result session archive closed (consp closed) nil nil nil v)
      (if (and (consp arguments) (null (cdr arguments)))
          (let ((parsed (fn-wildmat-parse (car arguments))))
            (if (fn-wildmat-result-okp parsed)
                (fn-lst-result session archive closed (consp closed) nil
                               (fn-wildmat-result-value parsed) t v)
              (fn-nntp-single session (fn-proto-text * :syntax))))
        (fn-nntp-single session (fn-proto-text * :syntax))))))

(defun fn-lst-counts-command (session archive closed args v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)) (ignore fn-cat))
  (if (null args)
      (fn-lst-result session archive closed t t nil nil v)
    (if (and (consp args) (null (cdr args)))
        (let ((parsed (fn-wildmat-parse (car args))))
          (if (fn-wildmat-result-okp parsed)
              (fn-lst-result session archive closed t t (fn-wildmat-result-value parsed) t v)
            (fn-nntp-single session (fn-proto-text * :syntax))))
      (fn-nntp-single session (fn-proto-text * :syntax)))))

(in-theory (disable fn-lst-env fn-lst-progress fn-lst-start fn-lst-one fn-lst-call-metric
                    fn-lst-line fn-lst-step fn-lst-livep fn-lst-effectp fn-lst-effect))
