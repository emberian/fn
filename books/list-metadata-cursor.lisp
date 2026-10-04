; LIST ACTIVE/COUNTS keeps captured group/next/config references and advances
; matcher, next-watermark lookup, number probes and status entries separately.
; Row strings and decimal digits advance through a retained renderer. Integer
; width, status comparisons, catalog tariffs and snapshot stability remain debt.
(in-package "ACL2")
(include-book "group-summary-cursor")
(include-book "wildmat-cursor")
(include-book "list-row-cursor")
(include-book "list-status-cursor")
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
     ((not progress) (mv nil nil))
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
                           (fn-lss-start group closed) "y")
                       (fn-gsc-summary detail) calls))))
     ((eq phase :status)
      (if (fn-lss-donep detail)
          (mv nil (fn-lst-progress env :row groups group (fn-lss-status detail) summary calls))
        (mv nil (fn-lst-progress env :status groups group (fn-lss-one detail) summary calls))))
     ((eq phase :row)
      (mv nil (fn-lst-progress env :render groups group
                              (fn-lsr-start group summary countsp detail) nil calls)))
     ((eq phase :render)
      (mv-let (octets next) (fn-lsr-one detail)
        (mv octets (if next
                       (fn-lst-progress env :render groups group next nil calls)
                     (fn-lst-progress env :group groups nil nil nil calls)))))
     (t (mv '(46 13 10) nil)))))

(local
 (defthm fn-lst-progress-calls
   (equal (fn-cur-at 6 (fn-lst-progress env phase groups group detail summary calls))
          (nfix calls))
   :hints (("Goal" :in-theory (enable fn-cur-at fn-lst-progress)))))

(local
 (defthm fn-lst-nfix-successor
   (equal (nfix (+ 1 (nfix calls))) (+ 1 (nfix calls)))
   :hints (("Goal" :in-theory '(nfix natp)))))

(local
 (defthm fn-lst-empty-call-metric
   (equal (fn-lst-call-metric nil) 0)
   :hints (("Goal" :in-theory '(fn-lst-call-metric fn-cur-at nfix)))))

(local
 (defthm fn-lst-empty-field
   (equal (fn-cur-at n nil) nil)
   :hints (("Goal" :in-theory '(fn-cur-at)))))

; This literal metric counts controller calls, not bytes or catalog internals.
(defthm fn-lst-one-control-at-most-one
  (<= (- (fn-lst-call-metric progress)
          (fn-lst-call-metric (mv-nth 1 (fn-lst-one progress fn-cat)))) 1)
  :hints (("Goal" :in-theory
           (union-theories
            '(fn-lst-one fn-lst-call-metric fn-lst-progress-calls
              fn-lst-nfix-successor fn-lst-empty-call-metric fn-lst-empty-field nfix natp)
            (theory 'minimal-theory)))))

(local (in-theory (disable fn-lst-one fn-lst-progress fn-lst-env fn-lst-call-metric)))

(local
 (defthm fn-lst-mv-first
   (equal (mv-nth 0 x) (car x))
   :hints (("Goal" :expand ((mv-nth 0 x))))))

(local
 (defthm fn-lst-mv-third
   (equal (mv-nth 2 (cons a (cons b tail))) (car tail))
   :hints (("Goal" :expand ((mv-nth 2 (cons a (cons b tail)))
                            (mv-nth 1 (cons b tail)) (mv-nth 0 tail))))))

(local (deftheory fn-lst-before-generated-bounds (current-theory :here)))

(local
 (in-theory
  (union-theories
   '(fn-cur-context fn-cur-progress fn-cur-pending fn-cur-dependency fn-cur-make
     fn-cur-at fn-cur-split-byte-bound fn-cur-split-keeps-true-listp
     fn-lst-mv-first fn-lst-mv-third car-cons cdr-cons nfix natp len mv-nth zp)
   (theory 'minimal-theory))))

(def-cursor fn-lst (fn-cat) :stobjs (fn-cat)
  :call (fn-lst-one progress fn-cat)
  :visit-proof fn-lst-one-control-at-most-one
  :visit-metric (fn-lst-call-metric progress))

(verify-guards fn-lst-one)
(verify-guards fn-lst-step :hints (("Goal" :in-theory (disable fn-lst-one fn-cur-split))))

(local (in-theory (theory 'fn-lst-before-generated-bounds)))

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

; -----------------------------------------------------------------------------
; Logical residual of the actual LIST controller (re-derived from the
; harvested codex/sol-served-20261003@232fa612a books/list-query-reference
; for the render/status phases dev's fn-lst-one carries). Never computed by
; the served path. The completion walk below is the reference reply.
(defun-nx fn-lst-row-status (env group)
  (if (or (fn-cur-at 2 env) (fn-cur-at 3 env))
      (fn-nntp-closed-status (fn-nntp-string-octets group) (fn-cur-at 1 env))
    "y"))

(defun-nx fn-lst-row-reference (env group summary status)
  (fn-nntp-stuff-lines (list (fn-lst-line group summary (fn-cur-at 3 env) status))))

(defun-nx fn-lst-next-summary (env group next fn-cat)
  (let ((next (nfix next)))
    (fn-gsc-reference (fn-gsc-start group (if (posp next) (- next 1) 0) next
                                    (nfix (fn-cur-at 6 env)))
                      fn-cat)))

(defun-nx fn-lst-group-reference (env group fn-cat)
  (fn-lst-row-reference
   env group
   (fn-lst-next-summary env group
                        (fn-next-number group (fn-state-nexts (fn-cur-at 0 env))) fn-cat)
   (fn-lst-row-status env group)))

(defun-nx fn-lst-groups-reference (env groups fn-cat)
  (if (consp groups)
      (append (if (or (not (fn-cur-at 5 env))
                      (fn-nntp-group-matches-parsed-wildmatp (fn-cur-at 4 env) (car groups)))
                  (fn-lst-group-reference env (car groups) fn-cat)
                nil)
              (fn-lst-groups-reference env (cdr groups) fn-cat))
    '(46 13 10)))

(defun-nx fn-lst-progress-reference (progress fn-cat)
  (let* ((env (fn-cur-at 0 progress))
         (phase (fn-cur-at 1 progress))
         (group (fn-cur-at 3 progress))
         (detail (fn-cur-at 4 progress))
         (summary (fn-cur-at 5 progress))
         (future (fn-lst-groups-reference env (fn-cur-at 2 progress) fn-cat)))
    (cond
     ((not progress) nil)
     ((eq phase :group) future)
     ((eq phase :match)
      (append (if (fn-wmc-value detail) (fn-lst-group-reference env group fn-cat) nil)
              future))
     ((eq phase :next)
      (append (fn-lst-row-reference env group
                (fn-lst-next-summary env group (fn-next-number group detail) fn-cat)
                (fn-lst-row-status env group))
              future))
     ((eq phase :summary)
      (append (fn-lst-row-reference env group (fn-gsc-reference detail fn-cat)
                                    (fn-lst-row-status env group))
              future))
     ((eq phase :status)
      (append (fn-lst-row-reference env group summary (fn-lss-reference detail)) future))
     ((eq phase :row)
      (append (fn-lst-row-reference env group summary detail) future))
     ((eq phase :render) (append (fn-lsr-reference detail) future))
     (t '(46 13 10)))))

(defun-nx fn-lst-remaining (cur fn-cat)
  (append (fn-cur-pending cur) (fn-lst-progress-reference (fn-cur-progress cur) fn-cat)))

(local
 (defthm fn-lst-progress-fields
   (and (equal (fn-cur-at 0 (fn-lst-progress env phase groups group detail summary calls)) env)
        (equal (fn-cur-at 1 (fn-lst-progress env phase groups group detail summary calls)) phase)
        (equal (fn-cur-at 2 (fn-lst-progress env phase groups group detail summary calls)) groups)
        (equal (fn-cur-at 3 (fn-lst-progress env phase groups group detail summary calls)) group)
        (equal (fn-cur-at 4 (fn-lst-progress env phase groups group detail summary calls)) detail)
        (equal (fn-cur-at 5 (fn-lst-progress env phase groups group detail summary calls)) summary)
        (fn-lst-progress env phase groups group detail summary calls))
   :hints (("Goal" :in-theory (enable fn-cur-at fn-lst-progress)))))

(local
 (defthm fn-lst-row-reference-is-render-start
   (equal (fn-lsr-reference (fn-lsr-start group summary countsp status))
          (fn-nntp-stuff-lines (list (fn-lst-line group summary countsp status))))
   :hints (("Goal" :in-theory (e/d (fn-lst-line) (fn-nntp-stuff-lines fn-lsr-start))))))

(local
 (defthm fn-lst-append-nil
   (implies (true-listp x) (equal (append x nil) x))))

(local
 (defthm fn-lst-render-done
   (implies (not (mv-nth 1 (fn-lsr-one cur)))
            (equal (mv-nth 0 (fn-lsr-one cur)) (fn-lsr-reference cur)))
   :hints (("Goal" :use (fn-lsr-one-keeps-reference fn-lsr-one-output-true-listp)
            :in-theory (e/d (fn-lsr-reference) (fn-lsr-one-keeps-reference fn-lsr-one-output-true-listp fn-lsr-one))))))

(local
 (defthm fn-lst-next-number-step
   (implies (and (consp detail) (not (equal group (car (car detail)))))
            (equal (fn-next-number group (cdr detail)) (fn-next-number group detail)))
   :hints (("Goal" :in-theory (enable fn-next-number)))))

(local
 (defthm fn-lst-next-number-here
   (equal (fn-next-number group detail)
          (if (consp detail)
              (if (equal group (car (car detail))) (cdr (car detail))
                (fn-next-number group (cdr detail)))
            0))
   :rule-classes ((:definition :controller-alist ((fn-next-number nil t))))
   :hints (("Goal" :in-theory (enable fn-next-number)))))

(local
 (defthm fn-lst-render-step
   (equal (append (car (fn-lsr-one c)) (fn-lsr-reference (cadr (fn-lsr-one c))) z)
          (append (fn-lsr-reference c) z))
   :hints (("Goal" :use ((:instance fn-lsr-one-keeps-reference (cur c)))
            :in-theory (e/d (mv-nth) (fn-lsr-one-keeps-reference fn-lsr-one))))))

(local
 (defthm fn-lst-render-last
   (implies (not (cadr (fn-lsr-one c)))
            (equal (append (car (fn-lsr-one c)) z)
                   (append (fn-lsr-reference c) z)))
   :hints (("Goal" :use ((:instance fn-lst-render-done (cur c)))
            :in-theory (e/d (mv-nth) (fn-lst-render-done fn-lsr-one))))))

(local
 (defthm fn-lst-groups-reference-unfold
   (equal (fn-lst-groups-reference env groups fn-cat)
          (if (consp groups)
              (append (if (or (not (fn-cur-at 5 env))
                              (fn-nntp-group-matches-parsed-wildmatp (fn-cur-at 4 env) (car groups)))
                          (fn-lst-group-reference env (car groups) fn-cat)
                        nil)
                      (fn-lst-groups-reference env (cdr groups) fn-cat))
            '(46 13 10)))
   :rule-classes ((:definition :controller-alist ((fn-lst-groups-reference nil t nil))))
   :hints (("Goal" :in-theory (enable fn-lst-groups-reference)))))

(defthm fn-lst-one-keeps-reference
  (equal (append (mv-nth 0 (fn-lst-one progress fn-cat))
                 (fn-lst-progress-reference (mv-nth 1 (fn-lst-one progress fn-cat)) fn-cat))
         (fn-lst-progress-reference progress fn-cat))
  :hints (("Goal" :in-theory
           (e/d (fn-lst-one fn-lst-progress-reference fn-lst-group-reference
                 fn-lst-next-summary fn-lst-row-status fn-lst-row-reference)
                (fn-lst-progress fn-cur-at fn-gsc-start fn-gsc-one
                 fn-lss-start fn-lss-one fn-lsr-start fn-lsr-one fn-wmc-start fn-wmc-step
                 fn-next-number nfix fn-nntp-closed-status fn-lst-line fn-nntp-stuff-lines)))))

(local (in-theory (disable fn-lst-row-status fn-lst-row-reference fn-lst-next-summary
                           fn-lst-group-reference fn-lst-groups-reference
                           fn-lst-progress-reference fn-lst-remaining)))

(local
 (defthm fn-lst-cur-make-fields
   (and (equal (fn-cur-progress (fn-cur-make c p r d)) p)
        (equal (fn-cur-pending (fn-cur-make c p r d)) r))
   :hints (("Goal" :in-theory (enable fn-cur-progress fn-cur-pending fn-cur-make fn-cur-at)))))

(local
 (defthm fn-lst-append-atom
   (implies (not (consp x)) (equal (append x y) y))))

(local
 (defthm fn-lst-split-assoc
   (equal (append (mv-nth 0 (fn-cur-split xs n)) (mv-nth 1 (fn-cur-split xs n)) z)
          (append xs z))
   :hints (("Goal" :use fn-cur-split-residual
            :in-theory (disable fn-cur-split-residual fn-cur-split)))))

(local
 (defthm fn-lst-one-keeps-reference-assoc
   (equal (append (car (fn-lst-one progress fn-cat))
                  (fn-lst-progress-reference (cadr (fn-lst-one progress fn-cat)) fn-cat))
          (fn-lst-progress-reference progress fn-cat))
   :hints (("Goal" :use fn-lst-one-keeps-reference
            :in-theory (e/d (mv-nth) (fn-lst-one-keeps-reference fn-lst-one))))))

(local
 (defthm fn-lst-split-assoc-cars
   (equal (append (car (fn-cur-split xs n)) (cadr (fn-cur-split xs n)) z)
          (append xs z))
   :hints (("Goal" :use fn-cur-split-residual
            :in-theory (e/d (mv-nth) (fn-cur-split-residual fn-cur-split))))))


; The host-called quantum: what one fn-lst-step emits followed by the residual
; of the cursor it returns is exactly the residual it was given.
(defthm fn-lst-step-keeps-remaining
  (equal (append (mv-nth 0 (fn-lst-step cur visits bytes fn-cat))
                 (fn-lst-remaining (mv-nth 1 (fn-lst-step cur visits bytes fn-cat)) fn-cat))
         (fn-lst-remaining cur fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-lst-step fn-lst-remaining)
                                  (fn-cur-split fn-lst-one fn-cur-make fn-cur-progress
                                   fn-cur-pending fn-lst-progress-reference)))))

; A started LIST cursor owes the reference reply body: every selected group's
; row, then the terminator.
(defthm fn-lst-start-remaining
  (equal (fn-lst-remaining (fn-lst-start archive closed statusp countsp patterns filteredp v) fn-cat)
         (fn-lst-groups-reference (fn-lst-env archive closed statusp countsp patterns filteredp v)
                                  (fn-state-groups archive) fn-cat))
  :hints (("Goal" :in-theory (enable fn-lst-remaining fn-lst-start fn-lst-progress-reference
                                     fn-lst-progress fn-cur-make fn-cur-pending fn-cur-progress
                                     fn-cur-at))))

(in-theory (disable fn-lst-row-status fn-lst-row-reference fn-lst-next-summary
                    fn-lst-group-reference fn-lst-groups-reference
                    fn-lst-progress-reference fn-lst-remaining))

; -----------------------------------------------------------------------------
; Finite potential of the whole LIST controller. Logical only: never
; computed by the served path. Each phase's cost bounds the calls left for
; the current group; F bounds every later group's from its :group phase.
(defun-nx fn-lst-row-cost (env group summary status)
  (+ 1 (fn-lsr-remaining-work (fn-lsr-start group summary (fn-cur-at 3 env) status))))

(defun-nx fn-lst-status-cost (env group summary)
  (if (or (fn-cur-at 2 env) (fn-cur-at 3 env))
      (+ 1 (fn-lss-remaining-work (fn-lss-start group (fn-cur-at 1 env)))
         (fn-lst-row-cost env group summary
                          (fn-nntp-closed-status (fn-nntp-string-octets group) (fn-cur-at 1 env))))
    (fn-lst-row-cost env group summary "y")))

(defun-nx fn-lst-summary-cost (env group next fn-cat)
  (let ((next (nfix next)))
    (+ 1 (fn-gsc-remaining (fn-gsc-start group (if (posp next) (- next 1) 0) next
                                         (nfix (fn-cur-at 6 env))))
       (fn-lst-status-cost env group (fn-lst-next-summary env group next fn-cat)))))

(defun-nx fn-lst-next-cost (env group detail fn-cat)
  (+ 1 (len detail) (fn-lst-summary-cost env group (fn-next-number group detail) fn-cat)))

(defun-nx fn-lst-group-cost (env group fn-cat)
  (let ((after (fn-lst-next-cost env group (fn-state-nexts (fn-cur-at 0 env)) fn-cat)))
    (if (fn-cur-at 5 env)
        (+ 2 (fn-wmc-remaining (fn-wmc-start (fn-cur-at 4 env) group)) after)
      (+ 1 after))))

(defun-nx fn-lst-groups-cost (env groups fn-cat)
  (if (consp groups)
      (+ (fn-lst-group-cost env (car groups) fn-cat)
         (fn-lst-groups-cost env (cdr groups) fn-cat))
    0))

(defun-nx fn-lst-phase-cost (progress fn-cat)
  (let* ((env (fn-cur-at 0 progress))
         (phase (fn-cur-at 1 progress))
         (group (fn-cur-at 3 progress))
         (detail (fn-cur-at 4 progress))
         (summary (fn-cur-at 5 progress)))
    (cond
     ((eq phase :match)
      (+ 1 (fn-wmc-remaining detail)
         (fn-lst-next-cost env group (fn-state-nexts (fn-cur-at 0 env)) fn-cat)))
     ((eq phase :next) (fn-lst-next-cost env group detail fn-cat))
     ((eq phase :summary)
      (+ 1 (fn-gsc-remaining detail)
         (fn-lst-status-cost env group (fn-gsc-reference detail fn-cat))))
     ((eq phase :status)
      (+ 1 (fn-lss-remaining-work detail)
         (fn-lst-row-cost env group summary (fn-lss-reference detail))))
     ((eq phase :row) (fn-lst-row-cost env group summary detail))
     ((eq phase :render) (fn-lsr-remaining-work detail))
     (t 0))))

(defun-nx fn-lst-potential (progress fn-cat)
  (if progress
      (+ 1 (fn-lst-phase-cost progress fn-cat)
         (fn-lst-groups-cost (fn-cur-at 0 progress) (fn-cur-at 2 progress) fn-cat))
    0))

; Carried shape: the wildmat state in :match and a live row state in :render.
(defun-nx fn-lst-progress-okp (progress)
  (let ((phase (fn-cur-at 1 progress)) (detail (fn-cur-at 4 progress)))
    (cond ((eq phase :match) (fn-wmc-shapedp detail))
          ((eq phase :render) (and detail (fn-lsr-statep detail)))
          (t t))))

(local
 (defthm fn-lst-wmc-remaining-natp
   (natp (fn-wmc-remaining s))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (e/d (fn-wmc-remaining) (fn-wmc-utf8-count fn-wildmat-decode-aux
                                                      fn-wmc-core-remaining))))))

(local
 (defthm fn-lst-wmc-step-is-one
   (implies (not (fn-wmc-decidedp d))
            (equal (fn-wmc-step d 1 (fn-wmc-demand d)) (fn-wmc-one d)))
   :hints (("Goal" :in-theory (enable fn-wmc-step fn-wmc-acceptedp)))))

(local
 (defthm fn-lst-lss-live-work
   (implies (not (fn-lss-donep c)) (< 0 (fn-lss-remaining-work c)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-lss-donep fn-lss-remaining-work)))))

(local
 (defthm fn-lst-gsc-remaining-natp
   (natp (fn-gsc-remaining c))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-gsc-remaining)))))

(local
 (defthm fn-lst-lsr-start-live
   (fn-lsr-start group summary countsp status)
   :hints (("Goal" :in-theory (enable fn-lsr-start fn-lsr-make)))))

(local
 (defthm fn-lst-groups-cost-unfold
   (equal (fn-lst-groups-cost env groups fn-cat)
          (if (consp groups)
              (+ (fn-lst-group-cost env (car groups) fn-cat)
                 (fn-lst-groups-cost env (cdr groups) fn-cat))
            0))
   :rule-classes ((:definition :controller-alist ((fn-lst-groups-cost nil t nil))))
   :hints (("Goal" :in-theory (enable fn-lst-groups-cost)))))

(local
 (defthm fn-lst-groups-cost-natp
   (natp (fn-lst-groups-cost env groups fn-cat))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-lst-groups-cost fn-lst-group-cost fn-lst-next-cost
                                      fn-lst-summary-cost fn-lst-status-cost fn-lst-row-cost)))))


(local
 (defthm fn-lst-lsr-cadr-forms
   (and (implies (fn-lsr-statep c) (fn-lsr-statep (cadr (fn-lsr-one c))))
        (implies (and c (fn-lsr-statep c))
                 (< (fn-lsr-remaining-work (cadr (fn-lsr-one c)))
                    (fn-lsr-remaining-work c))))
   :rule-classes ((:rewrite :corollary (implies (fn-lsr-statep c) (fn-lsr-statep (cadr (fn-lsr-one c)))))
                  (:linear :corollary (implies (and c (fn-lsr-statep c))
                                               (< (fn-lsr-remaining-work (cadr (fn-lsr-one c)))
                                                  (fn-lsr-remaining-work c)))))
   :hints (("Goal" :use ((:instance fn-lsr-one-keeps-statep (cur c))
                         (:instance fn-lsr-one-finite-progress (cur c)))
            :in-theory (e/d (mv-nth) (fn-lsr-one-keeps-statep fn-lsr-one-finite-progress fn-lsr-one
                                      fn-lsr-statep fn-lsr-remaining-work))))))

(defthm fn-lst-one-keeps-okp
  (implies (fn-lst-progress-okp progress)
           (fn-lst-progress-okp (mv-nth 1 (fn-lst-one progress fn-cat))))
  :hints (("Goal" :in-theory (e/d (fn-lst-one fn-lst-progress-okp)
                                  (fn-lst-progress fn-cur-at fn-wmc-start fn-wmc-step fn-wmc-shapedp
                                   fn-lsr-start fn-lsr-one fn-lsr-statep fn-wmc-one)))))


(local
 (defthm fn-lst-lss-live-progress
   (implies (not (fn-lss-donep c))
            (< (fn-lss-remaining-work (fn-lss-one c)) (fn-lss-remaining-work c)))
   :rule-classes :linear
   :hints (("Goal" :use ((:instance fn-lss-one-progress (cur c)))
            :in-theory (disable fn-lss-one-progress fn-lss-one fn-lss-remaining-work)))))

(local (defthm fn-lst-nfix-twice (equal (nfix (nfix x)) (nfix x))))
(local (defthm fn-lst-lsr-live-work
         (implies c (< 0 (fn-lsr-remaining-work c)))
         :rule-classes :linear
         :hints (("Goal" :in-theory (enable fn-lsr-remaining-work)))))
(defthm fn-lst-one-finite-progress
  (implies (and progress (fn-lst-progress-okp progress))
           (< (fn-lst-potential (mv-nth 1 (fn-lst-one progress fn-cat)) fn-cat)
              (fn-lst-potential progress fn-cat)))
  :hints (("Goal" :in-theory
           (e/d (fn-lst-one fn-lst-potential fn-lst-phase-cost fn-lst-progress-okp
                 fn-lst-group-cost fn-lst-next-cost fn-lst-summary-cost fn-lst-status-cost
                 fn-lst-next-summary fn-lst-row-cost)
                (fn-lst-progress fn-cur-at fn-gsc-start fn-gsc-one fn-lss-start fn-lss-one
                 fn-lsr-start fn-lsr-one fn-wmc-start fn-wmc-step fn-wmc-one fn-wmc-shapedp
                 fn-lsr-statep fn-next-number nfix fn-nntp-closed-status
                 fn-lst-groups-cost fn-wmc-remaining fn-lsr-remaining-work
                 fn-lss-remaining-work fn-gsc-remaining fn-gsc-reference)))))

(defthm fn-lst-potential-natp
  (natp (fn-lst-potential progress fn-cat))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (fn-lst-potential fn-lst-phase-cost fn-lst-next-cost
                                   fn-lst-summary-cost fn-lst-status-cost fn-lst-row-cost)
                                  (fn-lst-groups-cost fn-wmc-remaining fn-lsr-remaining-work
                                   fn-lss-remaining-work fn-gsc-remaining)))))

(defthm fn-lst-start-okp
  (fn-lst-progress-okp (fn-cur-progress (fn-lst-start archive closed statusp countsp patterns filteredp v)))
  :hints (("Goal" :in-theory (enable fn-lst-progress-okp fn-lst-start fn-lst-progress fn-cur-make
                                     fn-cur-progress fn-cur-at))))

(in-theory (disable fn-lst-row-cost fn-lst-status-cost fn-lst-summary-cost fn-lst-next-cost
                    fn-lst-group-cost fn-lst-groups-cost fn-lst-phase-cost fn-lst-potential
                    fn-lst-progress-okp))
