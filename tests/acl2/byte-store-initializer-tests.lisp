; Reached fresh initializer witnesses and fault cuts.
(in-package "ACL2")
(include-book "../../books/byte-store-initializer")
(include-book "../../books/byte-store-frame")
(include-book "std/testing/must-fail" :dir :system)

(defun fn-bsi-test-config () (fn-bs-initial-config-octets))
(defun fn-bsi-test-frontier () (fn-bs-initial-frontier-octets))
(defun fn-bsi-test-record () '(1 2 3 4))
(defconst *fn-bsi-test-config-stage* ".init-config-test")
(defconst *fn-bsi-test-record-stage* ".init-record-test")
(defconst *fn-bsi-test-frontier-stage* ".init-frontier-test")

(defun fn-bsi-test-program ()
  (fn-bsi-current-init-program (fn-bsi-test-config) (fn-bsi-test-record)
                               (fn-bsi-test-frontier)
                               *fn-bsi-test-config-stage*
                               *fn-bsi-test-record-stage*
                               *fn-bsi-test-frontier-stage*))

(defun fn-bsi-test-run (outcomes)
  (fn-bs-run *fn-bs-empty-store* (fn-sf-initial-state)
             (fn-bsi-test-program) outcomes nil nil))

(defun fn-bsi-test-outcome-at (n outcome)
  (declare (xargs :guard t))
  (if (zp n) (list outcome)
    (cons :ok (fn-bsi-test-outcome-at (1- n) outcome))))

(assert-event
 (fn-bsi-fresh-inputp (fn-bsi-test-config) (fn-bsi-test-record)
                      (fn-bsi-test-frontier)
                      *fn-bsi-test-config-stage* *fn-bsi-test-record-stage*
                      *fn-bsi-test-frontier-stage*))
(assert-event (fn-bs-initial-inputp (fn-bsi-test-config) (fn-bsi-test-frontier)))

; The host's omitted state is now present: lock, config directory and the
; generation-1 configuration record.  The final staging cleanup is unfenced.
(assert-event
 (let* ((run (fn-bsi-test-run nil)) (bs (car (car (last run)))))
   (and (equal (len run) (len (fn-bsi-test-program)))
        (fn-bs-store-relation bs (fn-sf-initial-state))
        (equal (fn-bs-durable-entry bs :root *fn-bsi-lock-name*) 0)
        (equal (fn-bs-durable-entry bs :root "config") :config)
        (equal (fn-bs-durable-entry bs :config *fn-bsi-config-record-name*) 2)
        (equal (fn-bs-durable-content bs 2) (fn-bsi-test-record))
        (not (fn-bs-dir-quietp bs :staging))
        (fn-bs-dir-quietp bs :config))))

; Pin durable calls and their post-call cuts.  These cuts are model crash
; points even where current Python faults.at uses the repeated init-barrier
; label rather than a distinct injected name.
(assert-event
 (let ((p (fn-bsi-test-program)))
   (and (member-equal '(:fsync-dir :parent) p)
        (member-equal '(:cut "init-root-parent-fenced") p)
        (member-equal '(:fsync-dir :config) p)
        (member-equal '(:cut "init-config-history-fenced") p)
        (member-equal '(:cut "init-config-record-file-fenced") p)
        (member-equal '(:cut "init-parent-fenced") p))))

; Error after the root parent fence: the lock and all later publications have
; not run.  This reaches a real initializer failure boundary, not a synthetic
; postcondition mutation.
(assert-event
 (let* ((run (fn-bsi-test-run (fn-bsi-test-outcome-at 4 '(:eio :drop))))
        (bs (car (car (last run)))))
   (and (equal (len run) 5)
        (equal (fn-bs-durable-entry bs :parent "store") :root)
        (not (fn-bs-lookup bs :root *fn-bsi-lock-name*))
        (equal (fn-bs-durable-entry bs :root *fn-bs-config-name*) nil))))

; Error after the config-history link can leave either legal directory image.
; The runner stops there; the explicit config-directory barrier never runs.
(assert-event
 (let* ((drop (fn-bsi-test-run (fn-bsi-test-outcome-at 42 '(:eio :drop))))
        (keep (fn-bsi-test-run (fn-bsi-test-outcome-at 42 '(:eio :apply))))
        (old (car (car (last drop)))) (new (car (car (last keep)))))
   (and (equal (len drop) 43) (equal (len keep) 43)
        (equal (fn-bs-durable-entry old :config *fn-bsi-config-record-name*) nil)
        (equal (fn-bs-durable-entry new :config *fn-bsi-config-record-name*) 2)
        (not (equal old new)))))

; The physical input boundary and the metadata-to-kernel binding are separate
; theorem hypotheses, each with a reachable counterexample.
(must-fail
 (assert-event
  (fn-bs-store-relation
   (car (car (last (fn-bs-run *fn-bs-empty-store* (fn-sf-initial-state)
                              (fn-bsi-current-init-program nil (fn-bsi-test-record)
                                                           (fn-bsi-test-frontier)
                                                           *fn-bsi-test-config-stage*
                                                           *fn-bsi-test-record-stage*
                                                           *fn-bsi-test-frontier-stage*)
                              nil nil nil))))
   (fn-sf-initial-state))))
(must-fail
 (assert-event
  (fn-bs-store-relation
   (car (car (last (fn-bs-run *fn-bs-empty-store* (fn-sf-initial-state)
                              (fn-bsi-current-init-program (fn-bsi-test-config)
                                                           (fn-bsi-test-record)
                                                           (fn-bs-frontier-encode-impl 1)
                                                           *fn-bsi-test-config-stage*
                                                           *fn-bsi-test-record-stage*
                                                           *fn-bsi-test-frontier-stage*)
                              nil nil nil))))
   (fn-sf-initial-state))))
