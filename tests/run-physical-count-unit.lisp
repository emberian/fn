; Operation fixture for the actual counted installed-run transitions. The
; intentionally corrupted scalar controls below are not reachable invariants.
; Source fixture only until this book is run by an ACL2 lane.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "../books/runs")

(defun fn2-rpc-operations (fn2-run-installed)
 (declare (xargs :stobjs fn2-run-installed :verify-guards nil))
 (b* ((fn2-run-installed (fn2-run-installed-init 3 fn2-run-installed))
      (initial (and (= (fn2-run-installed-physical-count fn2-run-installed) 0)
                    (fn2-run-physical-count-consistent-p fn2-run-installed)))
      ((mv first fn2-run-installed)
       ; Query priority 11 and persisted wire rank 9 are independent.
       (fn2-run-install-physical 0 7 11 9 0 2 *fn2-storage-extent-units* 3 5 17
        1 2 3 4 5 6 7 8 fn2-run-installed))
      (one (and (eq first :ok) (= (fn2-run-installed-physical-count fn2-run-installed) 1)
                (fn2-run-physical-count-consistent-p fn2-run-installed)
                (= (fn2-run-installed-physical 0 fn2-run-installed) 1)
                (= (fn2-run-installed-run 0 fn2-run-installed) 11)
                (= (fn2-run-installed-wire-run 0 fn2-run-installed) 9)))
      ((mv second fn2-run-installed)
       (fn2-run-install-physical 1 7 12 12 0 3 (* 2 *fn2-storage-extent-units*) 4 6 18
        11 12 13 14 15 16 17 18 fn2-run-installed))
      (two (and (eq second :ok) (= (fn2-run-installed-physical-count fn2-run-installed) 2)
                (fn2-run-physical-count-consistent-p fn2-run-installed)
                (= (fn2-run-physical-rows-from 3 0 fn2-run-installed) 2)))
      ((mv duplicate fn2-run-installed)
       (fn2-run-install-physical 0 7 13 13 0 4 *fn2-storage-extent-units* 5 7 19
        21 22 23 24 25 26 27 28 fn2-run-installed))
      (duplicate-unchanged
       (and (eq duplicate :state) (= (fn2-run-installed-physical-count fn2-run-installed) 2)
            (= (fn2-run-installed-run 0 fn2-run-installed) 11)
            (= (fn2-run-installed-wire-run 0 fn2-run-installed) 9)
            (fn2-run-physical-count-consistent-p fn2-run-installed)))
      ((mv retired-first fn2-run-installed) (fn2-run-retire 0 fn2-run-installed))
      (retired-retained
       (and (eq retired-first :ok)
            (= (fn2-run-installed-state 0 fn2-run-installed) *fn2-run-installed-state-retired*)
            (= (fn2-run-installed-physical-count fn2-run-installed) 2)
            (fn2-run-physical-count-consistent-p fn2-run-installed)))
      ((mv next-physical fn2-run-installed) (fn2-run-retired-next 0 fn2-run-installed))
      (next-refused
       (and (eq next-physical :physical)
            (= (fn2-run-installed-state 0 fn2-run-installed) *fn2-run-installed-state-retired*)
            (= (fn2-run-installed-physical-count fn2-run-installed) 2)
            (fn2-run-physical-count-consistent-p fn2-run-installed)))
      ((mv freed-first fn2-run-installed) (fn2-run-free-physical 0 fn2-run-installed))
      (freed-once
       (and (eq freed-first :ok) (= (fn2-run-installed-physical-count fn2-run-installed) 1)
            (= (fn2-run-installed-state 0 fn2-run-installed) *fn2-run-installed-state-free*)
            (= (fn2-run-installed-physical 0 fn2-run-installed) 0)
            (fn2-run-physical-count-consistent-p fn2-run-installed)))
      ((mv duplicate-free fn2-run-installed) (fn2-run-free-physical 0 fn2-run-installed))
      (no-double-free
       (and (eq duplicate-free :state) (= (fn2-run-installed-physical-count fn2-run-installed) 1)
            (fn2-run-physical-count-consistent-p fn2-run-installed)))
      ((mv retired-second fn2-run-installed) (fn2-run-retire 1 fn2-run-installed))
      ((mv freed-second fn2-run-installed) (fn2-run-free-physical 1 fn2-run-installed))
      (last-free
       (and (eq retired-second :ok) (eq freed-second :ok)
            (= (fn2-run-installed-physical-count fn2-run-installed) 0)
            (fn2-run-physical-count-consistent-p fn2-run-installed)))
      ((mv resident fn2-run-installed)
       (fn2-run-install 2 7 20 0 0 0 9 2 1 0 0 0 fn2-run-installed))
      (resident-installed
       (and (eq resident :ok) (= (fn2-run-installed-physical 2 fn2-run-installed) 0)
            (= (fn2-run-installed-run 2 fn2-run-installed) 20)
            (= (fn2-run-installed-wire-run 2 fn2-run-installed) 20)
            (= (fn2-run-installed-physical-count fn2-run-installed) 0)
            (fn2-run-physical-count-consistent-p fn2-run-installed)))
      ((mv resident-retired fn2-run-installed) (fn2-run-retire 2 fn2-run-installed))
      (resident-retained
       (and (eq resident-retired :ok)
            (= (fn2-run-installed-physical-count fn2-run-installed) 0)
            (fn2-run-physical-count-consistent-p fn2-run-installed))))
  (mv (and initial one two duplicate-unchanged retired-retained next-refused
           freed-once no-double-free last-free resident-installed resident-retained)
      fn2-run-installed)))

(defun fn2-rpc-overflow-control (fn2-run-installed)
 (declare (xargs :stobjs fn2-run-installed :verify-guards nil))
 (b* ((fn2-run-installed (fn2-run-installed-init 1 fn2-run-installed))
      ; Explicitly corrupt the scalar while all rows remain FREE.
      (fn2-run-installed (update-fn2-run-installed-physical-count #xffffffff fn2-run-installed))
      (seeded (not (fn2-run-physical-count-consistent-p fn2-run-installed)))
      ((mv code fn2-run-installed)
       (fn2-run-install-physical 0 7 11 11 0 2 *fn2-storage-extent-units* 3 5 17
        1 2 3 4 5 6 7 8 fn2-run-installed)))
  (mv (and seeded (eq code :exhausted)
           (= (fn2-run-installed-physical-count fn2-run-installed) #xffffffff)
           (= (fn2-run-installed-state 0 fn2-run-installed) *fn2-run-installed-state-free*)
           (= (fn2-run-installed-physical 0 fn2-run-installed) 0))
      fn2-run-installed)))

(defun fn2-rpc-underflow-control (fn2-run-installed)
 (declare (xargs :stobjs fn2-run-installed :verify-guards nil))
 (b* ((fn2-run-installed (fn2-run-installed-init 1 fn2-run-installed))
      ((mv installed fn2-run-installed)
       (fn2-run-install-physical 0 7 11 11 0 2 *fn2-storage-extent-units* 3 5 17
        1 2 3 4 5 6 7 8 fn2-run-installed))
      (valid-before (fn2-run-physical-count-consistent-p fn2-run-installed))
      ((mv retired fn2-run-installed) (fn2-run-retire 0 fn2-run-installed))
      ; Explicitly corrupt a counted RETIRED row to zero before free.
      (fn2-run-installed (update-fn2-run-installed-physical-count 0 fn2-run-installed))
      (seeded (not (fn2-run-physical-count-consistent-p fn2-run-installed)))
      ((mv code fn2-run-installed) (fn2-run-free-physical 0 fn2-run-installed)))
  (mv (and (eq installed :ok) valid-before (eq retired :ok) seeded
           (eq code :coverage) (= (fn2-run-installed-physical-count fn2-run-installed) 0)
           (= (fn2-run-installed-state 0 fn2-run-installed) *fn2-run-installed-state-retired*)
           (= (fn2-run-installed-physical 0 fn2-run-installed) 1))
      fn2-run-installed)))

(defun fn2-rpc-test ()
 (declare (xargs :verify-guards nil))
 (fn2-run-with-local (fn2-run-installed)
  (b* (((mv operations fn2-run-installed) (fn2-rpc-operations fn2-run-installed))
       ((mv overflow fn2-run-installed) (fn2-rpc-overflow-control fn2-run-installed))
       ((mv underflow fn2-run-installed) (fn2-rpc-underflow-control fn2-run-installed)))
   (mv (and operations overflow underflow) fn2-run-installed))))
(assert-event (fn2-rpc-test))
