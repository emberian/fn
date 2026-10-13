;;; Rebuilt developer image only. Real compiled BP entries and sync seam;
;;; no socket, durable Store I/O, or full owner quantum claim.
;;; Save/hook/restore symbol-function as in native_bp_prefix_probe_source.lisp.
(in-package "ACL2")
(cl:unless (cl:fboundp 'acl2::fnn-save-world-flavor)
  (cl:error "fn: this probe runs only inside a built fn-host image"))

(defun d14-pin-fixtures ()
  ;; Trusted repository fixture expressions, never external wire input.
  (let ((wanted '(*rl-groups* *rl-payload* *rl-node-empty* *rl-node-prepared*
                  *rl-node-committed* *rl-config* *rl-empty* *rl-enqueued*
                  *rl-work* *rl-undertaken* *rl-delivered* *rl-receipt*
                  *rl-receipt-pending* *rl-receipted*
                  *rl-config-record* *rl-enqueue-record*)))
    (with-open-file (in "tests/acl2/bp-release-tests.lisp")
      (loop for form = (read in nil :eof) until (eq form :eof)
            when (and (consp form) (eq (car form) 'defconst)
                      (member (second form) wanted))
            do (eval `(defparameter ,(second form) ,(third form)))
               (setf wanted (remove (second form) wanted))))
    (assert (null wanted))))
(d14-pin-fixtures)

(defun d14-second-node (node)
  (let* ((prepared (fn-node-prepare node 10 "<rl2@example.invalid>" 1
                                   *rl-groups* "archive-rl2" "subject-rl2"
                                   "operator-release" 4 841000000))
         (next (fn-node-complete prepared 1 10 :durable)))
    (assert (consp (fn-node-stage prepared)))
    (assert (null (fn-node-stage next)))
    (assert (fn-node-find-binding "<rl2@example.invalid>" (fn-node-bindings next)))
    (assert (fn-node-statep next))
    next))

(defun d14-store-at-node (node)
  (let ((sn (fn-sn-initial *rl-groups* 16)))
    (fn-sn-update sn (fn-sn-files sn) node)))

(defun d14-owner-at-node (node)
  ;; A configured owner with a real Store/node projection, not a sentinel.
  ;; Its disk journal is outside this in-process projection fixture's scope.
  (f-put-global 'fn-owner
                (fn-ocfg-make (fn-own-start (d14-store-at-node node) 1)
                              '(0 nil) nil nil)
                *the-live-state*))

(defun d14-owner-store-refresh ()
  ;; The Store-side read/refresh/write seam used by owner POST. Only O.
  (fn-owner-retain-carry-put
   (fn-prc-refresh (fn-owner-retain-carry *the-live-state*)
                  (fn-node-retention (fn-sn-node (fn-owner-store *the-live-state*))))
   *the-live-state*))

(defun d14-two-receipted-works ()
  ;; Both pins are admitted by real transitions, then both receipts commit.
  (let* ((s (fn-bprl-with-node *rl-receipted*
                              (d14-second-node (fn-bp-state-node *rl-receipted*))))
         (s (fn-bp-result-state
             (fn-bp-complete
              (fn-bp-prepare-enqueue s 20 0 "work-2" "<rl2@example.invalid>"
                                     "forward-2" "policy-1" "terms-2") 20 0 :durable)))
         (s (fn-bprl-undertake s "work-2" 3))
         (s (fn-bp-observe-transport
             (fn-bp-result-state
              (fn-bp-complete (fn-bp-prepare-attempt s 21 0 "work-2" "attempt-2")
                              21 0 :durable)) "work-2" "attempt-2" 0 :delivered))
         (receipt (fn-bp-make-receipt "receipt-2" "work-2" "subject-rl2"
                                     "receipt-authority" "dtn://peer/fn" "policy-1"
                                     "home-incarnation-1" "authorization-context-1" "terms-2"))
         (s (fn-bp-result-state
             (fn-bp-complete (fn-bp-prepare-receipt s 22 0 receipt t) 22 0 :durable))))
    (assert (fn-bp-statep s))
    (assert (= (length (fn-bp-state-receipts s)) 2))
    s))

(let* ((workflow *rl-undertaken*)
       (node0 (fn-bp-state-node workflow))
       (node1 (d14-second-node node0))
       (ledger0 (fn-node-retention node0))
       (ledger1 (fn-node-retention node1))
       (actual-scan (symbol-function 'fn-prc-find-scan))
       (actual-build (symbol-function 'fn-prc-build))
       (actual-find (symbol-function 'fn-prc-find-pin))
       (scans 0) (builds 0) (queries 0)
       (expected-ledger nil) (check-seam nil))
  ;; Arena setup precedes the measured native calls. BP and owner later
  ;; share L0; the standalone Store installs its distinct L1 cache cold.
  (assert (not (equal ledger0 ledger1)))
  (fn-arena-clear (fnn-live-stobj 'fn-arena))
  (fn-arn-seal-many '((72 105 13 10) (72 105 13 10)) (fnn-live-stobj 'fn-arena))
  (f-put-global 'fn-store-sn (d14-store-at-node node1) *the-live-state*)
  ;; A fresh process must exercise install from the lazy reader's nil default.
  ;; Do not manually prewarm the standalone Store carry in this fixture.
  (assert (not (boundp-global 'fn-workflow-store-pin-carry *the-live-state*)))
  (unwind-protect
      (progn
        (setf (symbol-function 'fn-prc-find-scan)
              (lambda (id pins) (incf scans) (funcall actual-scan id pins))
              (symbol-function 'fn-prc-build)
              (lambda (ledger) (incf builds) (funcall actual-build ledger))
              (symbol-function 'fn-prc-find-pin)
              (lambda (id ledger pin-carry)
                (incf queries)
                (when check-seam
                  (assert (eq ledger expected-ledger))
                  (assert (eq (car pin-carry) ledger))
                  (assert (fn-prc-carry-findsp pin-carry)))
                (funcall actual-find id ledger pin-carry)))
        ;; Cold controls prove both hooks observe the real fallback/rebuild.
        (fn-prc-refresh nil ledger0)
        (fn-bprl-work-pin workflow *rl-work* nil)
        (assert (plusp scans)) (assert (plusp builds))
        (format t "PIN-COUNTS cold scans=~d builds=~d queries=~d~%" scans builds queries)
        ;; Cold install must pay the initial S rebuild, then the FIRST served
        ;; gate must find a marked, correctly anchored cache without rebuilding.
        (setf scans 0 builds 0 queries 0)
        (assert (eq (fnn-core-state 'fn-workflow-install-replay
                                   (list *rl-config-record* *rl-enqueue-record*
                                         '(:outcome 10 0 :ordinary :durable))) :ready))
        (assert (plusp builds))
        (assert (eq (car (fn-workflow-store-pin-carry-of *the-live-state*)) ledger1))
        (setf scans 0 builds 0 queries 0 check-seam t expected-ledger ledger1)
        (let ((plan (fnn-core-state 'fn-workflow-ion-attempt-plan
                                   30 0 "work-1" "first-after-install")))
          (assert (consp plan))
          (assert (not (eq (car plan) :refused))))
        (assert (plusp queries)) (assert (zerop scans)) (assert (zerop builds))
        (format t "PIN-COUNTS first-ion-after-install scans=~d builds=~d queries=~d~%"
                scans builds queries)
        ;; Warm the owner/BP fixture outside its measured interval. S remains
        ;; the value installed by the actual cold entry, with no fixture put.
        (setf check-seam nil)
        (d14-owner-at-node node0)
        (f-put-global 'fn-workflow-state workflow *the-live-state*)
        (f-put-global 'fn-workflow-ion-state (fn-bpiw-initial) *the-live-state*)
        (fn-workflow-pin-carry-put
         (fn-prc-refresh (fn-workflow-pin-carry-of *the-live-state*) ledger0) *the-live-state*)
        (d14-owner-store-refresh)
        (setf scans 0 builds 0 queries 0 check-seam t)
        (flet ((bp-projection ()
                 (setf expected-ledger
                       (fn-node-retention (fn-bp-state-node (fnn-global 'fn-workflow-state))))
                 (let ((before queries)
                       (owner-carry (fn-owner-retain-carry *the-live-state*)))
                   (assert (eq (fnn-core-state 'fn-owner-workflow-forward-pinnedp "work-1") t))
                   (fnn-core-state 'fn-workflow-carry-report "work-1")
                   (assert (> queries before))
                   (assert (eq owner-carry (fn-owner-retain-carry *the-live-state*)))))
               (canonical-request ()
                 (setf expected-ledger
                       (fn-node-retention (fn-sn-node (fn-owner-store *the-live-state*))))
                 (let ((before queries)
                       (bp-carry (fn-workflow-pin-carry-of *the-live-state*)))
                   (assert (eq (car (fnn-core-state 'fn-owner-workflow-request-plan
                                                   "work-1" "next-attempt")) :request))
                   (assert (> queries before))
                   (assert (eq bp-carry (fn-workflow-pin-carry-of *the-live-state*))))))
          (dotimes (i 3)
            (declare (ignore i))
            (bp-projection) (canonical-request) (d14-owner-store-refresh))
          ;; Store moves forward while B still lags; repeated alternation must
          ;; never pull OC back to B or the BP carry forward to O prematurely.
          (d14-owner-at-node node1)
          (d14-owner-store-refresh)
          (assert (eq (car (fn-owner-retain-carry *the-live-state*)) ledger1))
          (dotimes (i 3)
            (declare (ignore i))
            (bp-projection) (canonical-request) (d14-owner-store-refresh))
          (assert (eq (car (fn-workflow-pin-carry-of *the-live-state*)) ledger0))
          (assert (zerop scans)) (assert (zerop builds))
          (format t "PIN-COUNTS owner-alternating scans=~d builds=~d queries=~d~%" scans builds queries)
          ;; Standalone ION gate reads S's own cache and leaves BP's alone.
          (setf scans 0 builds 0 queries 0 expected-ledger ledger1)
          (dotimes (i 3)
            (declare (ignore i))
            (setf expected-ledger ledger1)
            (let ((bp-carry (fn-workflow-pin-carry-of *the-live-state*))
                  (before queries))
              (let ((plan (fnn-core-state 'fn-workflow-ion-attempt-plan
                                         30 0 "work-1" "ion-attempt")))
                (assert (consp plan))
                (assert (not (eq (car plan) :refused))))
              (assert (> queries before))
              (assert (eq bp-carry (fn-workflow-pin-carry-of *the-live-state*))))
            (bp-projection))
          (assert (zerop scans)) (assert (zerop builds))
          (format t "PIN-COUNTS standalone-gate scans=~d builds=~d queries=~d~%" scans builds queries)
          ;; The real exported sync entry calls fn-bprl-with-node. The next BP
          ;; query must advance its cache through the forward delta, no build.
          (setf scans 0 builds 0 queries 0)
          (assert (eq (fnn-core-state 'fn-owner-workflow-sync-store-node) :ready))
          (assert (eq (fn-bp-state-node (fnn-global 'fn-workflow-state)) node1))
          (bp-projection) (canonical-request)
          (assert (eq (car (fn-workflow-pin-carry-of *the-live-state*)) ledger1))
          (assert (plusp queries)) (assert (zerop scans)) (assert (zerop builds))
          (format t "PIN-COUNTS sync-forward scans=~d builds=~d queries=~d~%" scans builds queries))
        ;; Cold replay: first release uses L0's warmed trie; the second DISTINCT
        ;; work reaches lookup on changed L1 with the unchanged replay carry.
        (setf check-seam nil)
        (let* ((s (d14-two-receipted-works))
               (carry (fn-prc-refresh nil (fn-node-retention (fn-bp-state-node s))))
               (r1 (fn-bprl-release-record s "receipt-1" carry))
               (r2 (fn-bprl-release-record s "receipt-2" carry)))
          (assert (and r1 r2 (not (equal (third r1) (third r2)))))
          (setf scans 0 builds 0 queries 0)
          (let ((first (fn-bpiw-replay-records s (fn-bpiw-initial) (list r1) nil
                                             carry (fnn-live-stobj 'fn-arena))))
            (assert (car first)) (assert (zerop scans)))
          (let ((answer (fn-bpiw-replay-records s (fn-bpiw-initial) (list r1 r2) nil
                                              carry (fnn-live-stobj 'fn-arena))))
            (assert (car answer))
            (assert (member '(:released "work-1") (nth 2 answer) :test #'equal))
            (assert (member '(:released "work-2") (nth 2 answer) :test #'equal))
            (assert (null (fn-retain-find-id "forward-1" (fn-bprl-pins (nth 1 answer)))))
            (assert (null (fn-retain-find-id "forward-2" (fn-bprl-pins (nth 1 answer))))))
          (assert (plusp scans))
          (format t "PIN-COUNTS replay-distinct-release scans=~d builds=~d queries=~d~%" scans builds queries)))
    (setf (symbol-function 'fn-prc-find-scan) actual-scan
          (symbol-function 'fn-prc-build) actual-build
          (symbol-function 'fn-prc-find-pin) actual-find)))
(format t "PASS BP pin carry lineage, forward sync, rebuild and scan controls~%")
