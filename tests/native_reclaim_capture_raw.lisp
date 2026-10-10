;;; S038 (admission before credit): a pass or a publication in flight refuses
;;; the capture by name, (:deferred WORD NIL), before any credit is reserved.
;;; S114: actual capture -> history sync -> carried census -> credit reserve,
;;; entered through actual native trailing-stobj/value dispatch. Array and
;;; Store accessors, row-byte costs and captured result are recording seams.
(load "tests/native_section_envelope_raw.lisp")
(in-package "ACL2")

;;; ---- derived stubs: BEGIN (python3 tools/harness_check.py --write-stubs; do not edit) ----
(define-condition harness-stub-reached (serious-condition)
  ((name :initarg :name :reader harness-stub-reached-name)
   (source :initarg :source :reader harness-stub-reached-source))
  (:report (lambda (c s)
             (format s "harness: host function ~(~a~) (~a) was reached; this harness neither stubs nor extracts it"
                     (harness-stub-reached-name c) (harness-stub-reached-source c)))))
(defun harness-stub-reached (name source)
  (format *error-output* "harness: host function ~(~a~) (~a) was reached; this harness neither stubs nor extracts it~%"
          name source)
  (finish-output *error-output*)
  (error 'harness-stub-reached :name name :source source))
(defun fnn-live-ast-ws ()
  (harness-stub-reached 'fnn-live-ast-ws "host/native/io.lisp"))
(defun fnn-live-owner-st ()
  (harness-stub-reached 'fnn-live-owner-st "host/native/io.lisp"))
;;; ---- derived stubs: END ----
(defun natp (x) (and (integerp x) (<= 0 x)))
(defun nfix (x) (if (natp x) x 0))
(defun zp (x) (not (and (integerp x) (> x 0))))
(defun true-list-fix (x) (if (listp x) x nil))
(defun hons-assoc-equal (x xs) (assoc x xs :test #'equal))
(defmacro mbe (&key logic exec) (declare (ignore logic)) exec)
(defmacro mv (&rest xs) `(values ,@xs))
(defmacro mv-let (vars value &body body) `(multiple-value-bind ,vars ,value ,@body))
(defmacro value (x) `(values nil ,x state))
(load-deployed-forms "books/reclaim-tombstone.lisp" '((defconst *fn-rcl-tombstone-fixed*)))
(load-deployed-forms "books/heap-store-figure.lisp"
 '((defconst *fn-heap-list-octets-per-octet*) (defconst *fn-heap-handle-octets*)
   (defconst *fn-heap-record-fixed-octets*) (defconst *fn-heap-record-msgid-index-octets*)
   (defconst *fn-heap-record-octets*) (defconst *fn-heap-charge-heap-octets*)
   (defconst *fn-heap-open-record-octets*) (defconst *fn-heap-reclaim-chunk-rows*)
   (defconst *fn-heap-reclaim-record-octets*) (defconst *fn-heap-reclaim-tombstone-octets*)
   (defconst *fn-heap-reclaim-agent-octets-per-charge*) (defun fn-heap-reclaim-demand-octets)))
(load-deployed-forms "books/memory-credits.lisp"
 '((defun fn-mcr-op-owned) (defun fn-mcr-op-reserved) (defun fn-mcr-ops-credit-onto)
   (defun fn-mcr-ops-credit) (defun fn-mcr-make) (defun fn-mcr-budget)
   (defun fn-mcr-base) (defun fn-mcr-cache) (defun fn-mcr-completion)
   (defun fn-mcr-runtime) (defun fn-mcr-drawn) (defun fn-mcr-ops)
   (defun fn-mcr-hroot) (defun fn-mcr-hroots)
   (defun fn-mcr-total) (defun fn-mcr-with) (defun fn-mcr-drop-loop)
   (defun fn-mcr-drop) (defun fn-mcr-put) (defun fn-mcr-credit-of)
   (defun fn-mcr-set) (defun fn-mcr-resize) (defun fn-mcr-borrow)))
(load-deployed-forms "books/owner-credits.lisp" '((defconst *fn-mca-reclaim*)))
(load-deployed-forms "books/owner-reclaim-pass.lisp"
 '((defconst *fn-orcp-credit-key*) (defun fn-orcp-reserve)))
(load-deployed-forms "books/history-columns-relation.lisp"
 '((defun fn-hist-sync-aux) (defun fn-hist-sync)))
(load-deployed-forms "books/history-columns-store.lisp"
 '((defun fn-hist-octets-advance) (defun fn-hist-bytes-carried)))
(load-deployed-forms "books/owner-reclaim.lisp" '((defun fn-orc-capture-word)))
(load-deployed-forms "books/owner-admission-state.lisp"
 '((defun fn-oadm-initial) (defun fn-oadm-configure-reclaim) (defun fn-oadm-reclaim-live)
   (defun fn-ost-admission) (defun fn-ost-install-admission)))
(load-deployed-forms "books/owner-publication-state.lisp"
 '((defun fn-opub-initial) (defun fn-opub-index) (defun fn-opub-get)
   (defun fn-ost-publication) (defun fn-ost-install-publication)))
(load-deployed-forms "host/owner-host.lisp"
 '((defun fn-owner-record-octets) (defun fn-owner-sco-count) (defun fn-owner-orc-pass)
   (defun fn-owner-reclaim-live-p) (defun fn-owner-orcp-capture)))
(load-deployed-forms "host/native/io.lisp"
 '((defun fnn-trailing-kind) (defun fnn-live-stobj) (defun fnn-arena-then-state)
   (defun fnn-core-state)))
(load-deployed-forms "host/native/owner.lisp" '((defun fnn-owner-core)))
(defvar *the-live-state* nil)
(defvar *hist* nil)
(defvar *fnn-trailing-stobjs* (make-hash-table))
(defvar *capture-count* 0)
(defvar *rows-read* nil)
(defun w (state) (declare (ignore state)) nil)
(defun stobjs-in (name world)
 (declare (ignore world))
 ;; Read the actual entry formals: a signature change cannot be hidden by
 ;; the fixture supplying the history argument directly.
 (with-open-file (s "host/owner-host.lisp")
  (loop for f = (read s nil :eof) until (eq f :eof)
   when (and (consp f) (eq (car f) 'defun) (eq (cadr f) name))
   return (mapcar (lambda (arg) (and (member arg '(fn-hist state)) arg)) (caddr f)))))
(defun fnn-live-hist () *hist*)
(defun fnn-live-arena () (error "unexpected arena"))
(defun fnn-live-cat () (error "unexpected catalog"))
(defun fnn-call (name &rest args) (multiple-value-list (apply name args)))
(defun boundp-global (key state) (nth-value 1 (gethash key state)))
(defun f-get-global (key state) (gethash key state))
(defun f-boundp-global (key state) (nth-value 1 (gethash key state)))
(defun f-put-global (key val state) (setf (gethash key state) val) state)
(defun fn-owner-store (state) (gethash :records state))
(defun fn-own-store (owner) (declare (ignore owner)) (gethash :records *the-live-state*))
(defun fn-sn-files (store) store)
(defun fn-sf-records-count (files) (length files))
(defun fn-sf-records-nth (k files) (nth k files))
(defun fn-hist-count (hist) (length (aref hist 0)))
(defun fn-hist-at (k hist) (push k *rows-read*) (nth k (aref hist 0)))
(defun fn-hist-append (row hist)
 (setf (aref hist 0) (append (aref hist 0) (list row))) hist)
(defun fn-sbud-row-octets (row) row)
(defun fn-sbud-bytes-used (store) (reduce #'+ store :initial-value 0))
(defun fn-owner-credits (state) (gethash :credits state))
(defun fn-owner-put-credits (credits state) (setf (gethash :credits state) credits) state)
(defun fn-owner-core (state) (declare (ignore state)) :owner)
(defun fn-own-max-conns (owner) (declare (ignore owner)) 10)
(defun fn-owner-orc-capture (mode clock override free revision state)
 (declare (ignore mode clock override free revision))
 (incf *capture-count*) (values nil :actual-capture state))
(defun census-check (ok label)
 (unless ok (format t "RECLAIM_CENSUS_ASSERTION:~a~%" label) (error "~a" label)))
;; The pass borrows its demand over the 2 committed records charging 300
;; octets (fn-heap-reclaim-demand-octets 2 300 = 54,544) from the completion
;; reserve (lane reclaim-funding): 10,000 of reserve refuses, 60,000 admits.
(dolist (case '((10000 :stale) (60000 :stale) (60000 :missing) (60000 :ahead)))
 (let* ((reserve (first case)) (cache-mode (second case)) (*the-live-state* (make-hash-table)) (*hist* (vector '(100)))
        (*capture-count* 0) (*rows-read* nil)
        (credits (fn-mcr-make (+ reserve 20) 0 0 reserve 0 0 '((:other . (0 . 10))) 0 nil)))
  (setf (gethash :records *the-live-state*) '(100 200)
        (gethash :credits *the-live-state*) credits
        ;; the operator's opt-in (D53), installed by the connection budget
        (gethash 'fn-owner-admission *the-live-state*) (fn-oadm-configure-reclaim t))
  (unless (eq cache-mode :missing)
   (setf (gethash 'fn-owner-record-octets *the-live-state*)
         (if (eq cache-mode :ahead) '(9 . 900) '(1 . 100))))
  (let ((answer (fnn-owner-core 'fn-owner-orcp-capture :recorded :clock nil 99999 :revision)))
   (if (= reserve 10000)
    (progn
     (census-check (equal answer (list :deferred :credit (fn-heap-reclaim-demand-octets 2 300)))
                   "stale census must not admit unfunded reclaim")
     (census-check (and (zerop *capture-count*) (equal credits (fn-owner-credits *the-live-state*)))
                   "refusal must not capture or mutate credits"))
    (progn
     (census-check (equal answer '(:captured :actual-capture 10)) "funded capture remains admitted")
     (census-check (= (fn-mcr-credit-of :reclaim (fn-mcr-ops (fn-owner-credits *the-live-state*)))
                     (fn-heap-reclaim-demand-octets 2 300)) "reservation pays current committed history")
     (census-check (= (fn-mcr-total (fn-owner-credits *the-live-state*)) (fn-mcr-total credits))
                   "the borrow leaves the articles' room")
     (census-check (= *capture-count* 1) "capture once")))
   (census-check (equal (gethash 'fn-owner-record-octets *the-live-state*) '(2 . 300))
                 "cache count and sum advance together")
   (census-check (and (= (fn-hist-count *hist*) 2) (equal *rows-read* (if (eq cache-mode :stale) '(1) nil)))
                 "sync and census visit only new committed row")
   (census-check (= (fn-mcr-credit-of :other (fn-mcr-ops (fn-owner-credits *the-live-state*))) 10)
                 "unrelated reservation retained"))))

;; S038: the slot's admission precedes the reservation.  A pass in flight, or a
;; publication in flight against a writing pass, is refused by name and the
;; credits, the census cache and the capture are exactly as they were.
(dolist (case '((:recorded nil :in-flight) (:dry-run nil :in-flight) (nil 7 :queued)))
 (destructuring-bind (pass inflight word) case
  (let* ((*the-live-state* (make-hash-table)) (*hist* (vector '(100)))
         (*capture-count* 0) (*rows-read* nil)
         (credits (fn-mcr-make 99999 0 0 0 0 0 '((:other . (0 . 10))) 0 nil)))
   (setf (gethash :records *the-live-state*) '(100 200)
         (gethash :credits *the-live-state*) credits
         (gethash 'fn-owner-publication *the-live-state*)
         (list nil nil nil nil nil inflight nil nil nil pass))
   (let ((answer (fnn-owner-core 'fn-owner-orcp-capture :recorded :clock nil 99999 :revision)))
    (census-check (equal answer (list :deferred word nil))
                  "a held slot is refused by name, third element nil")
    (census-check (and (zerop *capture-count*) (equal credits (fn-owner-credits *the-live-state*)))
                  "a held slot reserves no credit and captures nothing")
    (census-check (and (null *rows-read*) (= (fn-hist-count *hist*) 1)
                       (not (nth-value 1 (gethash 'fn-owner-record-octets *the-live-state*))))
                  "a held slot touches neither the history nor the census cache")))))
;; D53: without the opt-in (the budget installed NIL, or never ran) the
;; capture's own check refuses by name, whatever the reserve: :offline-only,
;; nothing captured, credits unchanged.
(dolist (installed '(:nil :unbound))
 (let* ((*the-live-state* (make-hash-table)) (*hist* (vector '(100)))
        (*capture-count* 0) (*rows-read* nil)
        (credits (fn-mcr-make 99999 0 0 60000 0 0 '((:other . (0 . 10))) 0 nil)))
  (setf (gethash :records *the-live-state*) '(100 200)
        (gethash :credits *the-live-state*) credits)
  (when (eq installed :nil) (fn-ost-install-admission (fn-oadm-configure-reclaim nil) *the-live-state*))
  (let ((answer (fnn-owner-core 'fn-owner-orcp-capture :recorded :clock nil 99999 :revision)))
   (census-check (equal answer '(:deferred :offline-only nil))
                 "without the opt-in the capture is refused by name")
   (census-check (and (zerop *capture-count*) (equal credits (fn-owner-credits *the-live-state*)))
                 "an off capture reserves no credit and captures nothing"))))
(format t "RECLAIM_CENSUS_PASS refused, admitted, missing and out-of-range cache through actual trailing-stobj dispatch~%")
