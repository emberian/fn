; Actual proper-reader live-buffer fixtures; no copied decoder definitions.
; Codec permitted tables are not an installed owner recovery seed.
(in-package "ACL2")
(include-book "../../books/store-checkpoint-arena-size-load")

(defun fn-scsr-fixture-frame (program a)
 (declare (xargs :mode :program))
 (let ((header (fn-scc-header 0 1 (len program) 1)))
  (list header a (+ a (len program))
        (fn-scc-seal *fn-scc-genesis* header program))))

(defun fn-scsr-fixture-plan (fn-octets)
 (declare (xargs :stobjs fn-octets :mode :program))
 (let* ((ctx '(:ok 9 ((:key "abc" (4 5))) ((1 2 3 "<a@b>" :carried (7 8) 4 (9))) nil :none))
        (f (fn-scc-program '(3 1 1 "rev" nil 2)))
        (p (fn-scc-program '(7 8))) (e (fn-scc-program '(7 8)))
        (r (append (fn-scc-program nil) (fn-scc-program ctx)
                   (fn-scc-program nil) (fn-scc-program nil)))
        (fb (len f)) (pb (+ fb (len p))) (eb (+ pb (len e)))
        (plan (list (fn-scsr-fixture-frame f 0) (fn-scsr-fixture-frame p fb)
                    (fn-scsr-fixture-frame e pb) (fn-scsr-fixture-frame r eb)))
        (fn-octets (fn-octets-clear fn-octets))
        (fn-octets (fn-octets-append-list (append f p e r) fn-octets)))
  (mv plan fn-octets)))

(defun fn-scsr-live-full-load (fn-octets)
 (declare (xargs :stobjs fn-octets :mode :program))
 (mv-let (plan fn-octets) (fn-scsr-fixture-plan fn-octets)
  (mv-let (decoded info region) (fn-sctsr-load plan fn-octets)
   (mv-let (status root fields) (fn-sctsr-original-context-carries info)
    (mv (and (equal decoded (fn-sct-load plan fn-octets))
             (eq (car decoded) :ok)
             (equal region (list :summary-region (nth 1 (nth 3 plan)) (nth 2 (nth 3 plan)) :R 1)) (eq status :ready)
             (equal root (fn-scs-summary (cadr (nth 3 (cadr decoded)))))
             (fn-scs-correspondsp fields (cadr (nth 3 (cadr decoded))))) fn-octets)))))

(defun fn-scsr-live-full-load-local ()
 (declare (xargs :mode :program))
 (with-local-stobj fn-octets
   (mv-let (ok fn-octets) (fn-scsr-live-full-load fn-octets) ok)))

(make-event (value (list 'assert-event (fn-scsr-live-full-load-local))))

(defun fn-scsr-live-projected-ref (raw fn-octets)
 (declare (xargs :stobjs fn-octets :mode :program))
 (let* ((p (fn-scc-program raw))
        (ref (cons *fn-sct-op-ref* (fn-scc-nat-octets 0)))
        (boundary (len p)) (end (+ boundary (len ref)))
        (fn-octets (fn-octets-clear fn-octets))
        (fn-octets (fn-octets-append-list (append p ref) fn-octets)))
  (mv-let (rows infos) (fn-sctsr-decode-rows 0 boundary nil nil fn-octets)
   (let ((table (fn-cei-build (cadr rows))) (info-table (fn-scsr-info-index infos)))
    (mv-let (step next-infos)
     (fn-sctsr-step boundary end nil nil table info-table fn-octets)
     (mv (and (eq (car rows) :ok) (equal (cadr rows) (list raw))
              (equal step (fn-sctr-step boundary end nil table fn-octets))
              (equal (car (car step)) '(7 8))
              (equal (fn-scsr-info-root (car next-infos)) (fn-scs-octets 2))
              (fn-scsr-info-provenancep (car next-infos) '(7 8))
              (not (equal (fn-scsr-info-root (car infos))
                          (fn-scsr-info-root (car next-infos))))) fn-octets))))))

(defun fn-scsr-live-projected-ref-local (raw)
 (declare (xargs :mode :program))
 (with-local-stobj fn-octets
  (mv-let (ok fn-octets) (fn-scsr-live-projected-ref raw fn-octets) ok)))

(make-event (value (list 'assert-event
 (fn-scsr-live-projected-ref-local '(1 2 3 "<m@b>" (7 8))))))

(make-event (value (list 'assert-event
 (fn-scsr-live-projected-ref-local '(1 2 3 nil nil nil (7 8))))))

; Same one-call finish API used by the actual host producer. These are
; summary-only fixtures, not a complete arena/restart qualification.
(defun fn-scsr-live-paired-finish (fn-octets)
 (declare (xargs :stobjs fn-octets :mode :program))
 (mv-let (plan fn-octets) (fn-scsr-fixture-plan fn-octets)
  (mv-let (loaded info region) (fn-sckas-finish plan 1 0 0 fn-octets)
   (mv-let (closed closed-info closed-region) (fn-sckas-finish plan 2 0 0 fn-octets)
    (mv-let (arena arena-info arena-region) (fn-sckas-finish plan 1 0 1 fn-octets)
     (mv-let (absent absent-info absent-region) (fn-sckas-finish nil 1 0 0 fn-octets)
      (mv (and (equal loaded (fn-sshr-share (fn-sct-load plan fn-octets)))
               (eq (car loaded) :ok) info
               (equal region (list :summary-region (nth 1 (nth 3 plan))
                                                   (nth 2 (nth 3 plan)) :R 1))
               (equal closed '(:refused :close)) (not closed-info) (not closed-region)
               (equal arena '(:refused :arena)) (not arena-info) (not arena-region)
               (eq (car absent) :refused) (not absent-info) (not absent-region)) fn-octets)))))))
(defun fn-scsr-live-paired-finish-local ()
 (declare (xargs :mode :program))
 (with-local-stobj fn-octets
  (mv-let (ok fn-octets) (fn-scsr-live-paired-finish fn-octets) ok)))
(make-event (value (list 'assert-event (fn-scsr-live-paired-finish-local))))
