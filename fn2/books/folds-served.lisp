; Layer C4: the folds' summary contract through the real engine
; (fn2/docs/c-ordered-runs.md §4 "Folds", §9). A fold's materialized state is
; its rows (one per key, the latest) in overlays and runs. The image below is
; the summary side of TRANSPORT §9's two-representation contract: rows
; written through the real insert (sigma), events applied through the real
; step (each reads the key's row by a range read, newest source first, runs
; the schema's served step NAME-FOLD-APPLY over the decoded row and writes the
; result back through the overlay's replace), observations read back by the
; range read. The history side is the declaration's list fold. Keystones per
; fold: NAME-SUMMARY-ADEQUATE-KIND for each event kind (the homomorphism
; certificate: obs(sigma s) = obs s and sigma(delta s e) = delta_Sigma(sigma s, e)
; observed at every query), and NAME-SUMMARY-CUT (State = Fold(Summary_k,
; E_{k+1..n}) at every cut, the summary sealed into a run or held in the
; overlay).
(in-package "ACL2")
(include-book "range-served")
(fn2-book-layer :c)

; Logic-side dispatch over the fold schemas (never served).
(defun fn2-fold-rows (rows)
 (declare (xargs :verify-guards nil))
 (cond ((atom rows) nil)
       ((fn2-decl-get :fold (cdar rows)) (cons (car rows) (fn2-fold-rows (cdr rows))))
       (t (fn2-fold-rows (cdr rows)))))
(defun fn2-fold-dispatch-arms (rows suffix args)
 (declare (xargs :verify-guards nil))
 (if (atom rows) nil
  (cons `(,(fn2-decl-get :id (cdar rows)) (,(fn2-columns-sym (caar rows) suffix) ,@args))
        (fn2-fold-dispatch-arms (cdr rows) suffix args))))
(make-event
 (let ((rows (fn2-fold-rows (fn2-decl-rows :schema (w state)))))
  (value
   `(progn
     (defun fn2-fold-key-spec (sid e)
      (declare (xargs :verify-guards nil))
      (case sid ,@(fn2-fold-dispatch-arms rows "-FOLD-KEY" '(e)) (otherwise nil)))
     (defun fn2-fold-observe-vals (sid vals)
      (declare (xargs :verify-guards nil))
      (case sid ,@(fn2-fold-dispatch-arms rows "-FOLD-OBSERVE" '((list (cons :q vals)) :q)) (otherwise nil)))))))

; Field plan above the range adapter's (fn2-rga-setup): the row being
; written at 600, the event's args at 700; the overlay insert decodes at the
; adapter's reader rows.
(defconst *fn2-fia-wb* 600)
(defconst *fn2-fia-args* 700)
(defun fn2-fia-zeros (n) (declare (xargs :verify-guards nil)) (make-list n :initial-element 0))
(defun fn2-fia-load-args (args i fn2-fields)
 (declare (xargs :stobjs fn2-fields :verify-guards nil))
 (if (atom args) fn2-fields
  (let ((fn2-fields (fn2-fields-set-value (+ *fn2-fia-args* (nfix i)) (nfix (car args)) fn2-fields)))
   (fn2-fia-load-args (cdr args) (+ 1 (nfix i)) fn2-fields))))

;; The rows the range read delivers for key Q (at most one: the newest).
(fn2-rga-defun fn2-fia-read (sid layout q)
 (b* ((key-layout (take (fn2-run-layout-keys sid) layout))
      ((mv & qslot qgen fn2-pool) (fn2-pool-reserve 0 10 0 1 fn2-pool))
      ((mv & off fn2-fields fn2-pool) (fn2-run-load-values key-layout q *fn2-rga-lo* qslot qgen 0 10 0 1 fn2-fields fn2-pool))
      ((mv & & fn2-fields fn2-pool) (fn2-run-load-values key-layout q *fn2-rga-hi* qslot qgen off 10 0 1 fn2-fields fn2-pool))
      ((mv & fn2-pool) (fn2-pool-release qslot qgen 10 0 1 fn2-pool))
      ((mv code fn2-ranges fn2-range-sources)
       (fn2-range-start 0 sid *fn2-rga-lo* *fn2-rga-hi* 0 *fn2-rga-smax* 0 *fn2-rga-heads* *fn2-range-no-position* 0 10 0 1
                        fn2-ranges fn2-range-sources fn2-overlays fn2-run-installed))
      ((unless (eq code :ok)) (fn2-rga-mv (list (list :start code)))))
  (fn2-rga-call fn2-rga-drive 1000 sid layout 4096 nil 0)))
(defun fn2-fia-found (got nf)
 (declare (xargs :verify-guards nil))
 (and (consp got) (null (cdr got)) (true-listp (car got)) (equal (len (car got)) nf)))

;; Apply event E through the real step and write its row back; BUG (for
;; teeth only; nil in every statement) :plus1 corrupts the step's first
;; value field, :skip drops the write.
(fn2-rga-defun fn2-fia-event (sid layout nk e bug)
 (b* ((nf (fn2-run-layout-fields sid 0))
      (key (fn2-fold-key-spec sid e))
      ((mv got fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths
           fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
       (fn2-rga-call fn2-fia-read sid layout key))
      ((unless (or (null got) (fn2-fia-found got nf))) (fn2-rga-mv (list :read got)))
      (row (if got (car got) (append key (fn2-fia-zeros (- nf nk)))))
      ((mv & & fn2-fields fn2-pool) (fn2-run-load-values layout row *fn2-fia-wb* 0 0 0 9 0 1 fn2-fields fn2-pool))
      (fn2-fields (fn2-fia-load-args (cdr e) 0 fn2-fields))
      ((mv code fn2-fields) (fn2-fold-apply sid (car e) *fn2-fia-wb* *fn2-fia-args* fn2-fields))
      ((unless (eq code :ok)) (fn2-rga-mv code))
      (fn2-fields (if (eq bug :plus1)
                      (fn2-fields-set-value (+ *fn2-fia-wb* nk) (+ 1 (fn2-fields-value (+ *fn2-fia-wb* nk) fn2-fields)) fn2-fields)
                    fn2-fields))
      ((when (eq bug :skip)) (fn2-rga-mv :ok))
      ((mv code fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
       (fn2-ov-insert 0 *fn2-fia-wb* *fn2-run-adapter-reader* fn2-overlays fn2-overlay-index fn2-fields fn2-pool)))
  (fn2-rga-mv code)))
(fn2-rga-defun fn2-fia-events (sid layout nk events bug)
 (if (atom events) (fn2-rga-mv nil)
  (b* (((mv code fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths
            fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
        (fn2-rga-call fn2-fia-event sid layout nk (car events) bug))
       ((mv rest fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths
            fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
        (fn2-rga-call fn2-fia-events sid layout nk (cdr events) bug)))
   (fn2-rga-mv (cons code rest)))))
;; Each query's observation: of its row, or of zeros when it has none.
(fn2-rga-defun fn2-fia-observe (sid layout nk qs)
 (if (atom qs) (fn2-rga-mv nil)
  (b* ((nf (fn2-run-layout-fields sid 0))
       ((mv got fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths
            fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
        (fn2-rga-call fn2-fia-read sid layout (car qs)))
       (obs (cond ((null got) (fn2-fold-observe-vals sid (fn2-fia-zeros (- nf nk))))
                  ((fn2-fia-found got nf) (fn2-fold-observe-vals sid (nthcdr nk (car got))))
                  (t (list :read got))))
       ((mv rest fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths
            fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
        (fn2-rga-call fn2-fia-observe sid layout nk (cdr qs))))
   (fn2-rga-mv (cons obs rest)))))
(defun fn2-fia-entries (rows)
 (declare (xargs :verify-guards nil))
 (if (atom rows) nil (cons (append (caar rows) (cdar rows)) (fn2-fia-entries (cdr rows)))))
;; ROWS (an alist key -> value) materialized: sealed into run 1 when SEAL,
;; else inserted into the overlay; then EVENTS, then the observations of QS.
;; The answer is (observations codes) where CODES are the events' outcomes.
(fn2-rga-defun fn2-fia-run (sid layout key rows events seal qs bug)
 (b* (((mv & fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths
           fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
       (fn2-rga-call fn2-rga-setup))
      (nk (len key))
      (entries (fn2-ov-sort-spec key (fn2-fia-entries rows)))
      ((mv code fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths
           fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
       (if seal (fn2-rga-call fn2-rga-build sid layout entries 0) (fn2-rga-mv :ok)))
      ((unless (eq code :ok)) (fn2-rga-mv (list :seal code)))
      ((mv code fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths
           fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
       (fn2-rga-call fn2-rga-overlay sid layout (if seal nil entries)))
      ((unless (eq code :ok)) (fn2-rga-mv (list :overlay code)))
      ((mv codes fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths
           fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
       (fn2-rga-call fn2-fia-events sid layout nk events bug))
      ((mv obs fn2-ranges fn2-range-sources fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths
           fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
       (fn2-rga-call fn2-fia-observe sid layout nk qs)))
  (fn2-rga-mv (list obs codes))))
(defun fn2-fold-image-bug (sid layout key rows events seal qs bug)
 (declare (xargs :verify-guards nil))
 (fn2-rga-local fn2-fia-run sid layout key rows events seal qs bug))
(defun fn2-fold-image (sid layout key rows events seal qs)
 (declare (xargs :verify-guards nil))
 (car (fn2-fold-image-bug sid layout key rows events seal qs nil)))

; ---------------------------------------------------------------------------
; Keystones, generated per fold from its declaration. Premises: a state of at
; most 8 rows whose keys and values fit the schema (NAME-FOLD-STATEP), events
; the declaration admits, at most 8 queries that are keys.
(defun fn2-fold-kinds (evs) (declare (xargs :verify-guards nil)) (if (atom evs) nil (cons (caar evs) (fn2-fold-kinds (cdr evs)))))
(defun fn2-fold-adequate-events (name sid layout key kinds)
 (declare (xargs :verify-guards nil))
 (if (atom kinds) nil
  (let ((thm (fn2-columns-sym name (concatenate 'string "-SUMMARY-ADEQUATE-" (symbol-name (car kinds))))))
   (cons `(defthm-owed ,thm (rows e seal qs)
           (implies (and (,(fn2-columns-sym name "-FOLD-STATEP") rows) (<= (len rows) 8)
                         (,(fn2-columns-sym name "-FOLD-EVENTP") e) (eq (car e) ,(car kinds))
                         (,(fn2-columns-sym name "-FOLD-KEYSP") qs) (<= (len qs) 8) (booleanp seal))
                    (and (equal (fn2-fold-image ,sid ,layout ',key rows nil seal qs)
                                (,(fn2-columns-sym name "-FOLD-OBSERVE-ALL") rows qs))
                         (equal (fn2-fold-image ,sid ,layout ',key rows (list e) seal qs)
                                (,(fn2-columns-sym name "-FOLD-OBSERVE-ALL") (,(fn2-columns-sym name "-FOLD-APPLY-SPEC") rows e) qs))))
           :teeth (,(fn2-columns-sym thm "-POSITIVE") ,(fn2-columns-sym thm "-NEGATIVE"))
           :doc ,(concatenate 'string "The summary rule's certificate for " (symbol-name name) " and event kind "
                              (symbol-name (car kinds)) ": the rows read back through the real engine observe as the "
                              "fold's state, and after one such event applied by the real step they observe as the "
                              "fold's step of that state, whether the rows are sealed in a run or held in an overlay."))
         (fn2-fold-adequate-events name sid layout key (cdr kinds))))))
(defun fn2-fold-cut-event (name sid layout key)
 (declare (xargs :verify-guards nil))
 (let ((thm (fn2-columns-sym name "-SUMMARY-CUT")))
  `(defthm-owed ,thm (events k seal qs)
    (implies (and (,(fn2-columns-sym name "-FOLD-EVENTSP") events) (<= (len events) 8) (natp k) (<= k (len events))
                  (,(fn2-columns-sym name "-FOLD-KEYSP") qs) (<= (len qs) 8) (booleanp seal))
             (equal (fn2-fold-image ,sid ,layout ',key (,(fn2-columns-sym name "-FOLD-SPEC") (take k events)) (nthcdr k events) seal qs)
                    (,(fn2-columns-sym name "-FOLD-OBSERVE-ALL") (,(fn2-columns-sym name "-FOLD-SPEC") events) qs)))
    :teeth (,(fn2-columns-sym thm "-POSITIVE") ,(fn2-columns-sym thm "-NEGATIVE") ,(fn2-columns-sym thm "-WEAK"))
    :doc ,(concatenate 'string "State = Fold(Summary_k, Events_{k+1..n}) for " (symbol-name name)
                       ": the summary at any cut k, materialized as rows sealed into a run or held in an overlay, "
                       "with the rest of the events applied by the real step, observes as the whole fold."))))
(defun fn2-fold-keystone-events (rows)
 (declare (xargs :verify-guards nil))
 (if (atom rows) nil
  (let* ((name (caar rows)) (row (cdar rows)) (sid (fn2-decl-get :id row)) (key (fn2-decl-get :key row))
         (layout (fn2-codec-constant (car (fn2-decl-get :layouts row)) ""))
         (kinds (fn2-fold-kinds (cadr (member-eq :events (fn2-decl-get :fold row))))))
   (append (fn2-fold-adequate-events name sid layout key kinds)
           (list (fn2-fold-cut-event name sid layout key))
           (fn2-fold-keystone-events (cdr rows))))))
(make-event (value (cons 'progn (fn2-fold-keystone-events (fn2-fold-rows (fn2-decl-rows :schema (w state)))))))
