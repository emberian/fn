(in-package "ACL2")
(include-book "../../books/peer-catchup-spool")

(defun csp-test-state (limit)
  (let* ((cursor (fn-cu-fresh-cursor (fn-record-string-octets "remote")))
         (round (fn-cu-begin cursor (fn-record-string-octets "fn.test")))
         (session (fn-cu-session (fn-fc-make-state (fn-fwi-initial-state) nil :ready 0 :clear)
                                round nil :clear)))
    (list :status session nil nil nil 0 0 nil *fn-cu-zero-chain* nil nil 0 limit 0 nil nil nil)))

(defun csp-test-wire (body lines claim)
  (append (fn-cu-initial-line 1 1 claim) '(13 10)
            (fn-cu-record-header "<a@x>" lines) '(13 10) body '(46 13 10)))

(defun csp-test-drive (s effects wire disk local journals fuel)
  ; Test-only materialized witness. Actual consumer never retains these lists.
  (declare (xargs :mode :program))
  (cond
   ((zp fuel) (list :exhausted s local journals disk))
   ((consp effects)
    (let* ((effect (car effects)) (kind (car effect))
           (disk (if (eq kind :spool-write)
                     (append (take (cadr effect) disk) (caddr effect)) disk))
           (local (if (eq kind :local) (append local (cdr effect)) local))
           (journals (if (eq kind :journal) (cons (cdr effect) journals) journals))
           (event
            (case kind
              (:spool-write (list :spool-written :ok (len (caddr effect))))
              (:spool-hash (list :digest (fn-blake3-stobj (take (caddr effect) (nthcdr (cadr effect) disk)))))
              (:spool-read (list :spool-read :ok (caddr effect) (take (caddr effect) (nthcdr (cadr effect) disk))))
              (:open-local (cons :local '(50 48 48 32 111 107 13 10)))
              (:local (case (fn-csp-mode s)
                        (:offer (cons :local '(51 51 53 32 111 107 13 10)))
                        (:local-write '(:local-window))
                        (:verdict (cons :local '(50 51 53 32 111 107 13 10)))
                        (otherwise '(:lost))))
              (otherwise nil))))
      (if event
          (let ((pair (fn-csp-step s event)))
            (csp-test-drive (car pair) (append (cdr effects) (cadr pair)) wire disk local journals (1- fuel)))
        (csp-test-drive s (cdr effects) wire disk local journals (1- fuel)))))
   ((member-eq (fn-csp-mode s) '(:done :failed))
    (list (fn-csp-mode s) s local journals disk))
   ((fn-csp-tick-p s)
    (let ((pair (fn-csp-step s '(:tick))))
      (csp-test-drive (car pair) (cadr pair) wire disk local journals (1- fuel))))
   ((consp wire)
    (let* ((n (min 512 (len wire)))
           (pair (fn-csp-step s (cons :remote (take n wire)))))
      (csp-test-drive (car pair) (cadr pair) (nthcdr n wire) disk local journals (1- fuel))))
   (t (list :stuck s local journals disk))))

(defconst *csp-test-article* '(46 120 13 10 13 10))
(defconst *csp-test-chain*
  (fn-cu-chain-step *fn-cu-zero-chain* (fn-record-string-octets "<a@x>") *csp-test-article*))
(defconst *csp-test-result*
  (csp-test-drive (csp-test-state 4096) nil
                 (csp-test-wire '(46 46 120 13 10 13 10) 2 *csp-test-chain*) nil nil nil 200))
(assert-event (eq (car *csp-test-result*) :done))
(assert-event
 (equal (nth 2 *csp-test-result*)
        (append (fn-pull-command (list (fn-record-string-octets "IHAVE") (fn-record-string-octets "<a@x>")))
                '(46 46 120 13 10 13 10 46 13 10))))
(assert-event (equal (len (nth 3 *csp-test-result*)) 1))
(assert-event
 (equal (fn-cu-cursor-position (car (nth 3 *csp-test-result*))) 1))
(assert-event
 (equal (fn-cu-cursor-chain (car (nth 3 *csp-test-result*))) *csp-test-chain*))
(assert-event
 (let ((r (csp-test-drive (csp-test-state 4096) nil
                         (csp-test-wire '(120 120 13 10 13 10) 2 *csp-test-chain*) nil nil nil 200)))
   (and (eq (car r) :failed) (not (nth 2 r)) (not (nth 3 r))
        (equal (fn-cu-r-refusal (fn-cu-s-round (fn-csp-session (cadr r)))) :digest-mismatch))))
(assert-event
 (let ((r (csp-test-drive (csp-test-state 1) nil
                         (csp-test-wire '(46 46 120 13 10 13 10) 2 *csp-test-chain*) nil nil nil 200)))
   (and (eq (car r) :failed) (not (nth 2 r)) (not (nth 3 r))
        (equal (fn-cu-r-refusal (fn-cu-s-round (fn-csp-session (cadr r)))) :spool-quota))))
(assert-event
 (let* ((article (append (make-list 1025 :initial-element 120) '(13 10)))
        (claim (fn-cu-chain-step *fn-cu-zero-chain* (fn-record-string-octets "<a@x>") article))
        (r (csp-test-drive (csp-test-state 4096) nil (csp-test-wire article 1 claim) nil nil nil 200)))
   (and (eq (car r) :done) (equal (len (nth 3 r)) 1)
        (equal (nth 2 r)
               (append (fn-pull-command (list (fn-record-string-octets "IHAVE") (fn-record-string-octets "<a@x>")))
                       article '(46 13 10))))))

; Teeth: fn-csp-step-keeps-window. Positive: a full 512-octet peer window is
; admitted into a windowed state and the result is windowed with that window.
(assert-event
 (let* ((s (csp-test-state 4096))
        (bytes (make-list 512 :initial-element 120))
        (s2 (car (fn-csp-step s (cons :remote bytes)))))
   (and (fn-csp-windowp s) (fn-csp-windowp s2)
        (equal (fn-csp-pending s2) bytes))))
; A 513-octet window is not retained: the round fails by name.
(assert-event
 (let* ((s2 (car (fn-csp-step (csp-test-state 4096)
                              (cons :remote (make-list 513 :initial-element 120))))))
   (and (fn-csp-windowp s2) (eq (fn-csp-mode s2) :failed)
        (equal (fn-cu-r-refusal (fn-cu-s-round (fn-csp-session s2))) :malformed))))
; Hypothesis removal: from a state already holding 600 pending octets, a step
; can leave it unwindowed, so the hypothesis is not redundant.
(assert-event
 (let* ((s (fn-csp-with (csp-test-state 4096) :mode :write :count 0
                       :resume :body :pending (make-list 600 :initial-element 120)))
        (s2 (car (fn-csp-step s '(:spool-written :ok 0)))))
   (and (not (fn-csp-windowp s)) (not (fn-csp-windowp s2)))))
; Teeth: fn-csp-write-spools-whole-or-fails-by-name, the whole-write disjunct.
(assert-event
 (let* ((s (csp-test-state 4096))
        (r (fn-csp-write s '(1 2 3) :body)))
   (and (equal (cadr r) '((:spool-write 0 (1 2 3))))
        (equal (fn-csp-offset (car r)) 3) (equal (fn-csp-count (car r)) 3)
        (eq (fn-csp-mode (car r)) :write) (eq (fn-csp-resume (car r)) :body))))
; ... and the named-refusal disjunct: one octet over the funded limit.
(assert-event
 (let* ((s (fn-csp-with (csp-test-state 4) :offset 2))
        (r (fn-csp-write s '(1 2 3) :body)))
   (and (eq (fn-csp-mode (car r)) :failed) (equal (cadr r) '((:close)))
        (equal (fn-cu-r-refusal (fn-cu-s-round (fn-csp-session (car r)))) :spool-quota))))
