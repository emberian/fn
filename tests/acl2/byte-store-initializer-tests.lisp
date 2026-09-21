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
  (declare (xargs :guard t :verify-guards nil))
  (if (zp n) (list outcome)
    (cons :ok (fn-bsi-test-outcome-at (1- n) outcome))))

(defun fn-bsi-test-cut-names (program)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp program)
      (if (equal (car (car program)) :cut)
          (cons (nth 1 (car program)) (fn-bsi-test-cut-names (cdr program)))
        (fn-bsi-test-cut-names (cdr program)))
    nil))

(defun fn-bsi-test-through-cut (label program)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp program)
      (cons (car program)
            (if (and (equal (car (car program)) :cut)
                     (equal (nth 1 (car program)) label))
                nil
              (fn-bsi-test-through-cut label (cdr program))))
    nil))

(defun fn-bsi-test-no-duplicatesp (xs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp xs)
      (and (not (member-equal (car xs) (cdr xs)))
           (fn-bsi-test-no-duplicatesp (cdr xs)))
    t))

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

; Pin durable calls and their post-call cuts.  The three publication instances
; have distinct labels; current Python still exposes only the older repeated
; init-barrier injection label, a source-correspondence limit recorded in the
; handoff rather than evidence that every model cut is host-killable.
(assert-event
 (let ((p (fn-bsi-test-program)))
   (and (member-equal '(:fsync-dir :parent) p)
        (member-equal '(:cut "init-root-parent-fenced") p)
        (member-equal '(:fsync-dir :config) p)
        (member-equal '(:cut "init-config-history-fenced") p)
        (member-equal '(:cut "init-final-config-record-file-fenced") p)
        (member-equal '(:cut "init-parent-fenced") p)
        (member-equal '(:cut "init-config-linked") p)
        (member-equal '(:cut "init-history-linked") p)
        (member-equal '(:cut "init-frontier-linked") p)
        (fn-bsi-test-no-duplicatesp (fn-bsi-test-cut-names p)))))

; The lock creation errors after the root parent fence: all metadata
; publications have not run.  This reaches a real initializer failure
; boundary, not a synthetic postcondition mutation.
(assert-event
 (let* ((run (fn-bsi-test-run (fn-bsi-test-outcome-at 4 '(:eio :drop))))
        (bs (car (car (last run)))))
   (and (equal (len run) 5)
        (equal (fn-bs-durable-entry bs :parent "store") :root)
        (not (fn-bs-lookup bs :root *fn-bsi-lock-name*))
        (equal (fn-bs-durable-entry bs :root *fn-bs-config-name*) nil))))

; A config-directory fsync error after the history link can leave either legal
; directory image.  The barrier runs and reports EIO; the runner stops at that
; failed barrier, so no later fence runs.
(assert-event
 (let* ((drop (fn-bsi-test-run (fn-bsi-test-outcome-at 42 '(:eio :drop))))
        (keep (fn-bsi-test-run (fn-bsi-test-outcome-at 42 '(:eio :apply))))
        (old (car (car (last drop)))) (new (car (car (last keep)))))
   (and (equal (len drop) 43) (equal (len keep) 43)
        (equal (fn-bs-durable-entry old :config *fn-bsi-config-record-name*) nil)
        (equal (fn-bs-durable-entry new :config *fn-bsi-config-record-name*) 2)
        (not (equal old new)))))

; The metadata-binding witness violates fn-bs-initial-inputp.  The physical
; witness below keeps that binding true and violates only the string-name
; portion of fn-bsi-fresh-inputp.
(assert-event
 (and (fn-bs-initial-inputp (fn-bsi-test-config) (fn-bsi-test-frontier))
      (not (fn-bsi-fresh-inputp (fn-bsi-test-config) (fn-bsi-test-record)
                                (fn-bsi-test-frontier) 7
                                *fn-bsi-test-record-stage*
                                *fn-bsi-test-frontier-stage*))))
(must-fail
 (assert-event
  (fn-bs-store-relation
   (car (car (last (fn-bs-run *fn-bs-empty-store* (fn-sf-initial-state)
                              (fn-bsi-current-init-program (fn-bsi-test-config)
                                                           (fn-bsi-test-record)
                                                           (fn-bsi-test-frontier)
                                                           7
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

; Equal fresh stage names are a positive witness: the prior pending
; create/unlink pair has no name in the running view, so the next O_EXCL
; create succeeds.  This does not cover an entry that was already present.
(assert-event
 (let* ((stage ".one-fresh-stage")
        (run (fn-bs-run *fn-bs-empty-store* (fn-sf-initial-state)
                        (fn-bsi-current-init-program (fn-bsi-test-config)
                                                     (fn-bsi-test-record)
                                                     (fn-bsi-test-frontier)
                                                     stage stage stage)
                        nil nil nil))
        (bs (car (car (last run)))))
   (and (fn-bsi-fresh-inputp (fn-bsi-test-config) (fn-bsi-test-record)
                             (fn-bsi-test-frontier) stage stage stage)
        (equal bs (fn-bsi-current-initial-image (fn-bsi-test-config)
                                                 (fn-bsi-test-record)
                                                 (fn-bsi-test-frontier)
                                                 stage stage stage))
        (fn-bs-store-relation bs (fn-sf-initial-state)))))

; Removing only the history-directory fence leaves the old relation true,
; because it does not observe :config, while the complete-image keystone is
; false.  This is the separating witness for the image theorem's real scope.
(assert-event
 (let* ((program (remove-equal '(:fsync-dir :config) (fn-bsi-test-program)))
        (run (fn-bs-run *fn-bs-empty-store* (fn-sf-initial-state) program nil nil nil))
        (bs (car (car (last run)))))
   (and (fn-bs-store-relation bs (fn-sf-initial-state))
        (equal (fn-bs-durable-entry bs :config *fn-bsi-config-record-name*) nil)
        (not (equal bs (fn-bsi-current-initial-image
                        (fn-bsi-test-config) (fn-bsi-test-record)
                        (fn-bsi-test-frontier) *fn-bsi-test-config-stage*
                        *fn-bsi-test-record-stage*
                        *fn-bsi-test-frontier-stage*))))))

; The expected-EEXIST step is live only when the immutable destination is
; already present.  A normal link error remains a stopping run; it is not
; silently reclassified as a retry.
(assert-event
 (let* ((program (fn-bsi-existing-init-program
                  (fn-bsi-test-config) (fn-bsi-test-frontier)
                  ".retry-config" ".retry-frontier"))
        (run (fn-bs-run (fn-bsi-current-initial-image
                         (fn-bsi-test-config) (fn-bsi-test-record)
                         (fn-bsi-test-frontier)
                         *fn-bsi-test-config-stage*
                         *fn-bsi-test-record-stage*
                         *fn-bsi-test-frontier-stage*)
                        (fn-sf-initial-state) program nil nil nil))
        (bs (car (car (last run)))))
   (and (fn-bs-step-listp program)
        (equal (len run) (len program))
        (member-equal '(:link-eexist :staging ".retry-config" :root "config.json")
                      program)
        (member-equal '(:link-eexist :staging ".retry-frontier" :root
                        "allocation-frontier.json") program)
        (equal (fn-bs-durable-content bs
                                      (fn-bs-durable-entry bs :root "config.json"))
               (fn-bsi-test-config))
        (equal (fn-bs-durable-content bs
                                      (fn-bs-durable-entry bs :root
                                                           "allocation-frontier.json"))
               (fn-bsi-test-frontier))
        (equal (fn-bs-durable-content bs
                                      (fn-bs-durable-entry bs :config "00000001.cfg"))
               (fn-bsi-test-record)))))

(assert-event
 (let* ((prefix (fn-bsi-test-through-cut "init-config-history-fenced"
                                         (fn-bsi-test-program)))
        (partial-run (fn-bs-run *fn-bs-empty-store* (fn-sf-initial-state)
                                prefix nil nil nil))
        (partial (car (car (last partial-run))))
        (retry (fn-bsi-history-retry-program
                (fn-bsi-test-config) (fn-bsi-test-frontier)
                ".history-retry-config" ".history-retry-frontier"))
        (run (fn-bs-run partial (fn-sf-initial-state) retry nil nil nil))
        (bs (car (car (last run)))))
   (and (equal (len partial-run) (len prefix))
        (equal (len run) (len retry))
        (fn-bs-step-listp retry)
        (equal (fn-bs-durable-entry partial :root "allocation-frontier.json") nil)
        (equal (fn-bs-durable-content
                bs (fn-bs-durable-entry bs :root "allocation-frontier.json"))
               (fn-bsi-test-frontier)))))

; EEXIST is the only link result that continues the retry program.  A link
; error with an issued namespace operation remains a stopped/uncertain model
; observation, rather than a known-abort retry.
(assert-event
 (let* ((program (fn-bsi-publish-existing-steps
                  "issued-link-" ".issued-config" :transactions "issued.txn"
                  (fn-bsi-test-config)))
        (run (fn-bs-run (fn-bsi-current-initial-image
                         (fn-bsi-test-config) (fn-bsi-test-record)
                         (fn-bsi-test-frontier)
                         *fn-bsi-test-config-stage*
                         *fn-bsi-test-record-stage*
                         *fn-bsi-test-frontier-stage*)
                        (fn-sf-initial-state) program
                        (fn-bsi-test-outcome-at 6 '(:eio . :issued)) nil nil)))
   (and (equal (len run) 7)
        (< (len run) (len program)))))

(must-fail
 (assert-event
  (let* ((program (fn-bsi-existing-init-program
                   (fn-bsi-test-config) (fn-bsi-test-frontier)
                   ".absent-config" ".absent-frontier"))
         (run (fn-bs-run *fn-bs-empty-store* (fn-sf-initial-state)
                         program nil nil nil)))
    (equal (len run) (len program)))))
