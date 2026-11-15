; Actual HELD-cut working-lease admission, independent of source construction.
(in-package "ACL2")
(include-book "c-snapshot-state")
(include-book "checkpoint-working-geometry")
(fn2-book-layer :c)

; Dedicated physical-source reader windows follow the original nineteen.
; They cannot alias semantic/payload windows across iterator yields.







(defcolumns fn2-checkpoint-windows ((live :bool) (slot :u32) (generation :u60)))

(defcolumns fn2-checkpoint-root1
 ((phase (:enum fn2-checkpoint-root1-phase (:idle :reserved :select :source :retention :semantic :payload :format :page :manifest :finish :scan :complete :uncertain)))
  (owner-kind :u8) (owner-slot :u32) (owner-gen :u60) (token :u60)
  (reserved :u8) (build :u32) (level :u8) (read-kind :u8) (resume-phase :u8)))



(defun fn2-checkpoint-window-roomp (i fn2-pool)
 (declare (xargs :stobjs fn2-pool :guard (and (natp i) (<= i *fn2-checkpoint-window-count*))
                 :measure (nfix (- *fn2-checkpoint-window-count* i))))
 (if (>= i *fn2-checkpoint-window-count*) t
  (let ((class (fn2-pool-class-for (fn2-checkpoint-window-length i) fn2-pool)))
   (and (natp class) (< class (fn2-pool-nclasses fn2-pool))
        (<= (fn2-checkpoint-window-class-demand 0 class fn2-pool) (fn2-pool-free-count class fn2-pool))
        (fn2-checkpoint-window-roomp (+ i 1) fn2-pool)))))

(defun fn2-checkpoint-windows-reserve-loop (i kind owner generation fn2-checkpoint-root1 fn2-checkpoint-windows fn2-pool)
 (declare (xargs :stobjs (fn2-checkpoint-root1 fn2-checkpoint-windows fn2-pool)
  :guard (and (fn2-checkpoint-root1-wfp fn2-checkpoint-root1) (< 0 (fn2-checkpoint-root1-rows fn2-checkpoint-root1))
              (fn2-checkpoint-windows-wfp fn2-checkpoint-windows) (<= *fn2-checkpoint-window-count* (fn2-checkpoint-windows-rows fn2-checkpoint-windows))
              (fn2-pool-wfp fn2-pool) (natp i) (<= i *fn2-checkpoint-window-count*))
  :measure (nfix (- *fn2-checkpoint-window-count* i))))
 (if (>= i *fn2-checkpoint-window-count*)
  (let ((fn2-checkpoint-root1 (fn2-checkpoint-root1-set-phase 0 *fn2-checkpoint-root1-phase-reserved* fn2-checkpoint-root1)))
   (mv :ok fn2-checkpoint-root1 fn2-checkpoint-windows fn2-pool))
  (b* ((class (fn2-pool-class-for (fn2-checkpoint-window-length i) fn2-pool))
       ((mv code slot gen fn2-pool) (fn2-pool-reserve class kind owner generation fn2-pool))
       ((unless (eq code :ok))
        (let ((fn2-checkpoint-root1 (fn2-checkpoint-root1-set-phase 0 *fn2-checkpoint-root1-phase-uncertain* fn2-checkpoint-root1)))
         (mv code fn2-checkpoint-root1 fn2-checkpoint-windows fn2-pool)))
       (fn2-checkpoint-windows (fn2-checkpoint-windows-put i (live 1) (slot slot) (generation gen)))
       (fn2-checkpoint-root1 (fn2-checkpoint-root1-set-reserved 0 (+ i 1) fn2-checkpoint-root1)))
   (fn2-checkpoint-windows-reserve-loop (+ i 1) kind owner generation fn2-checkpoint-root1 fn2-checkpoint-windows fn2-pool))))



(defun fn2-checkpoint-root1-reserve (c token kind owner generation fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-future fn2-checkpoint-future-windows fn2-csnapshot fn2-pool)
 (declare (xargs :stobjs (fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-future fn2-checkpoint-future-windows fn2-csnapshot fn2-pool)
  :guard (and (fn2-checkpoint-root1-wfp fn2-checkpoint-root1) (fn2-checkpoint-windows-wfp fn2-checkpoint-windows)
              (fn2-checkpoint-future-wfp fn2-checkpoint-future) (fn2-checkpoint-future-windows-wfp fn2-checkpoint-future-windows)
              (fn2-csnapshot-wfp fn2-csnapshot) (fn2-pool-wfp fn2-pool))))
 (b* (((unless (and (unsigned-byte-p 32 c) (< 0 (fn2-checkpoint-root1-rows fn2-checkpoint-root1))
                    (<= *fn2-checkpoint-window-count* (fn2-checkpoint-windows-rows fn2-checkpoint-windows))
                    (< 0 (fn2-csnapshot-rows fn2-csnapshot))
                    (equal (fn2-csnapshot-phase 0 fn2-csnapshot) *fn2-csnapshot-phase-held*)
                    (posp token)
                    (fn2-csnapshot-ownerp token kind owner generation fn2-csnapshot)
                    (equal (fn2-checkpoint-root1-phase 0 fn2-checkpoint-root1) *fn2-checkpoint-root1-phase-idle*)
                    (equal (fn2-checkpoint-root1-reserved 0 fn2-checkpoint-root1) 0)
                    (< 0 (fn2-checkpoint-future-rows fn2-checkpoint-future))
                    (<= 8 (fn2-checkpoint-future-windows-rows fn2-checkpoint-future-windows))
                    (equal (fn2-checkpoint-future-phase 0 fn2-checkpoint-future) *fn2-checkpoint-future-phase-idle*)
                    (equal (fn2-checkpoint-future-reserved 0 fn2-checkpoint-future) 0)
                    (fn2-pool-mrefp kind owner generation)))
       (mv :owner fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-future fn2-checkpoint-future-windows fn2-pool))
      ((unless (fn2-checkpoint-admission-roomp 0 fn2-pool))
       (mv :exhausted fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-future fn2-checkpoint-future-windows fn2-pool))
      ((mv code fn2-checkpoint-future fn2-checkpoint-future-windows fn2-pool)
       (fn2-checkpoint-future-reserve c kind owner generation fn2-checkpoint-future fn2-checkpoint-future-windows fn2-pool))
      ((unless (eq code :ok))
       (mv :partial fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-future fn2-checkpoint-future-windows fn2-pool))
      (fn2-checkpoint-root1 (fn2-checkpoint-root1-put 0 (owner-kind kind) (owner-slot owner) (owner-gen generation)))
      ((mv code fn2-checkpoint-root1 fn2-checkpoint-windows fn2-pool)
       (fn2-checkpoint-windows-reserve-loop 0 kind owner generation fn2-checkpoint-root1 fn2-checkpoint-windows fn2-pool)))
  (mv (if (eq code :ok) :ok :partial) fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-future fn2-checkpoint-future-windows fn2-pool)))

(defun fn2-checkpoint-root1-workspaces (kind owner generation fn2-checkpoint-root1 fn2-checkpoint-windows fn2-pool)
 (declare (xargs :stobjs (fn2-checkpoint-root1 fn2-checkpoint-windows fn2-pool)
  :guard (and (fn2-checkpoint-root1-wfp fn2-checkpoint-root1) (fn2-checkpoint-windows-wfp fn2-checkpoint-windows)
              (fn2-pool-wfp fn2-pool))))
 (b* (((unless (and (< 0 (fn2-checkpoint-root1-rows fn2-checkpoint-root1))
                    (<= *fn2-checkpoint-window-count* (fn2-checkpoint-windows-rows fn2-checkpoint-windows))
                    (equal (fn2-checkpoint-root1-reserved 0 fn2-checkpoint-root1) *fn2-checkpoint-window-count*)
                    (not (equal (fn2-checkpoint-root1-phase 0 fn2-checkpoint-root1) *fn2-checkpoint-root1-phase-idle*))
                    (equal kind (fn2-checkpoint-root1-owner-kind 0 fn2-checkpoint-root1))
                    (equal owner (fn2-checkpoint-root1-owner-slot 0 fn2-checkpoint-root1))
                    (equal generation (fn2-checkpoint-root1-owner-gen 0 fn2-checkpoint-root1))))
       (mv :owner 0 0 0 0 0 0))
      (page (fn2-checkpoint-windows-slot 16 fn2-checkpoint-windows))
      (pgen (fn2-checkpoint-windows-generation 16 fn2-checkpoint-windows))
      (scratch (fn2-checkpoint-windows-slot 14 fn2-checkpoint-windows))
      (sgen (fn2-checkpoint-windows-generation 14 fn2-checkpoint-windows))
      (read (fn2-checkpoint-windows-slot 18 fn2-checkpoint-windows))
      (rgen (fn2-checkpoint-windows-generation 18 fn2-checkpoint-windows))
      ((unless (and (equal (fn2-checkpoint-windows-live 16 fn2-checkpoint-windows) 1)
                    (equal (fn2-checkpoint-windows-live 14 fn2-checkpoint-windows) 1)
                    (equal (fn2-checkpoint-windows-live 18 fn2-checkpoint-windows) 1)
                    (eq (fn2-pool-workspace-code page pgen kind owner generation fn2-pool) :ok)
                    (eq (fn2-pool-workspace-code scratch sgen kind owner generation fn2-pool) :ok)
                    (eq (fn2-pool-workspace-code read rgen kind owner generation fn2-pool) :ok)))
       (mv :busy 0 0 0 0 0 0)))
  (mv :ok page pgen scratch sgen read rgen)))

(fn2-checkpoint-root1-preserves fn2-checkpoint-root1-reserve
 (c token kind owner generation fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-future fn2-checkpoint-future-windows fn2-csnapshot fn2-pool)
 :hyps ((fn2-checkpoint-root1p fn2-checkpoint-root1) (fn2-checkpoint-root1-wfp fn2-checkpoint-root1) (fn2-checkpoint-windowsp fn2-checkpoint-windows) (fn2-checkpoint-windows-wfp fn2-checkpoint-windows) (fn2-checkpoint-futurep fn2-checkpoint-future) (fn2-checkpoint-future-wfp fn2-checkpoint-future) (fn2-checkpoint-future-windowsp fn2-checkpoint-future-windows) (fn2-checkpoint-future-windows-wfp fn2-checkpoint-future-windows) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool) (fn2-csnapshotp fn2-csnapshot) (fn2-csnapshot-wfp fn2-csnapshot))
 :specs (
  ("-CHECKPOINT-ROOT1-TYPE" fn2-checkpoint-root1p 1) ("-CHECKPOINT-ROOT1-WFP" fn2-checkpoint-root1-wfp 1) ("-CHECKPOINT-ROOT1-ROWS" fn2-checkpoint-root1-rows 1 :frame fn2-checkpoint-root1)
  ("-CHECKPOINT-WINDOWS-TYPE" fn2-checkpoint-windowsp 2) ("-CHECKPOINT-WINDOWS-WFP" fn2-checkpoint-windows-wfp 2) ("-CHECKPOINT-WINDOWS-ROWS" fn2-checkpoint-windows-rows 2 :frame fn2-checkpoint-windows)
  ("-CHECKPOINT-FUTURE-TYPE" fn2-checkpoint-futurep 3) ("-CHECKPOINT-FUTURE-WFP" fn2-checkpoint-future-wfp 3) ("-CHECKPOINT-FUTURE-ROWS" fn2-checkpoint-future-rows 3 :frame fn2-checkpoint-future)
  ("-CHECKPOINT-FUTURE-WINDOWS-TYPE" fn2-checkpoint-future-windowsp 4) ("-CHECKPOINT-FUTURE-WINDOWS-WFP" fn2-checkpoint-future-windows-wfp 4) ("-CHECKPOINT-FUTURE-WINDOWS-ROWS" fn2-checkpoint-future-windows-rows 4 :frame fn2-checkpoint-future-windows)
  ("-POOL-TYPE" fn2-poolp 5) ("-POOL-WFP" fn2-pool-wfp 5) ("-POOL-ROWS" fn2-pool-rows 5 :frame fn2-pool)
  ("-POOL-DATA" fn2-pool-data-length 5 :frame fn2-pool)))
