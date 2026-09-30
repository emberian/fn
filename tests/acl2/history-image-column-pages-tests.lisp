; Constructed supported full-page column phases, with actual funded writer
; issuance and ACK/reset. This is not a full native image trajectory.
; The partial-page fixture is corrupted pending state, labelled separately.
(in-package "ACL2")
(include-book "../../books/history-image-column-pages")
(include-book "../../books/history-image-effect-boundary")

(local (defun hpicp-test-buffer-copy (fn-hpb)
 (declare (xargs :stobjs fn-hpb :verify-guards nil))
 (list (fn-hpb-prefix-aux 0 2048 fn-hpb) (fn-hpb-used fn-hpb)
       (fn-hpb-epoch fn-hpb) (fn-hpb-lease fn-hpb))))
(local (defun hpicp-test-digest-frames (n pgs-digest-state)
 (declare (xargs :stobjs pgs-digest-state :verify-guards nil :measure (nfix n)))
 (if (zp n) nil (cons (pgs-dc-framesi (1- n) pgs-digest-state)
                     (hpicp-test-digest-frames (1- n) pgs-digest-state)))))
(local (defun hpicp-test-digest-copy (pgs-digest-state)
 (declare (xargs :stobjs pgs-digest-state :verify-guards nil))
 (list (pgs-dc-mode pgs-digest-state) (pgs-dc-sel pgs-digest-state)
       (pgs-dc-base pgs-digest-state) (pgs-dc-total pgs-digest-state)
       (pgs-dc-start pgs-digest-state) (pgs-dc-end pgs-digest-state)
       (pgs-dc-pos pgs-digest-state) (pgs-dc-counter pgs-digest-state)
       (pgs-dc-power pgs-digest-state) (pgs-dc-depth pgs-digest-state)
       (pgs-dc-cv pgs-digest-state) (pgs-dc-output pgs-digest-state)
       (pgs-dc-capture pgs-digest-state) (pgs-dc-lease pgs-digest-state)
       (pgs-dc-answer pgs-digest-state) (hpicp-test-digest-frames 64 pgs-digest-state))))


(local (defun hpicp-test-history (n)
 (declare (xargs :measure (nfix n)))
 (if (zp n) nil (cons "ABC" (hpicp-test-history (1- n))))))
(local (defun hpicp-test-fill (words fn-hpb)
 (declare (xargs :stobjs fn-hpb :verify-guards nil :measure (len words)))
 (if (atom words) fn-hpb
  (mv-let (status fn-hpb) (fn-hpb-put (car words) fn-hpb)
   (declare (ignore status)) (hpicp-test-fill (cdr words) fn-hpb)))))
(local (defun hpicp-test-region-fill (region h body pages source maintenance fn-hpb)
 (declare (xargs :stobjs fn-hpb :verify-guards nil))
 (let ((fn-hpb (fn-hpb-begin source maintenance fn-hpb)))
  (hpicp-test-fill
   (nthcdr (* 2048 (nfix (nth region pages)))
    (fn-hpicol-history-model region (fn-hpicol-carried-history region h "ABC" body) 17)) fn-hpb))))
(local (defun hpicp-test-case (region mode fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
 (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) :verify-guards nil))
 (mv-let (admitted maintenance ledger)
  (fn-pmn-admit (fn-prl-make '(10000000 10000000 4 1 10)) 7 1 '(1000000 16384 3 1 1))
  (let ((initial (fn-hpi-begin 2049 16392 2 2 '(7 (9 2049) 0 0) maintenance (fn-omk-at 1 maintenance) 10000000 "node" 17 "trail")))
   (mv-let (funded request c ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
    (fn-hpi-tick initial nil ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
    (declare (ignore request))
    (let* ((n (if (eq mode :partial) 2047 2048)) (h (hpicp-test-history n))
           (body (fn-hpcx-with :columns n (* 8 n) nil (list 7 '(9 2049) 1 n) (fn-hp-mkey "ABC" 17) (len (fn-scc-encode "ABC")) region (fn-omk-at 14 c)))
           (pages (list (if (and (= n 2048) (< 0 region)) 1 0)
                        (if (and (= n 2048) (< 1 region)) 1 0)
                        (if (and (= n 2048) (< 2 region)) 1 0)
                        0 1))
           (source (fn-omk-at 1 c))
           (c (fn-hpi-set 0 :body (fn-hpi-set 15 pages (fn-hpi-set 14 body c))))
           (fn-hpq0 (hpicp-test-region-fill 0 h body pages source maintenance fn-hpq0))
           (fn-hpq1 (hpicp-test-region-fill 1 h body pages source maintenance fn-hpq1))
           (fn-hpq2 (hpicp-test-region-fill 2 h body pages source maintenance fn-hpq2))
           (fn-hpq3 (hpicp-test-region-fill 3 h body pages source maintenance fn-hpq3))
           (baseline (and (eq admitted :admitted) (eq funded :funded)
                         (fn-hpicol-writer-ready-p h "ABC" 17 c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3)
                         (fn-hpi-grant-matchesp c ledger)))
           (before0 (hpicp-test-buffer-copy fn-hpq0)) (before1 (hpicp-test-buffer-copy fn-hpq1))
           (before2 (hpicp-test-buffer-copy fn-hpq2)) (before3 (hpicp-test-buffer-copy fn-hpq3))
           (before4 (hpicp-test-buffer-copy fn-hpb)) (before-digest (hpicp-test-digest-copy pgs-digest-state)))
     (mv-let (issued effect c next-ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
      (if (eq mode :partial)
       ; Deliberately corrupted pending issuance: an internal reference call
       ; requests a page whose supported canonical suffix is not full.
       (mv-let (status effect c) (fn-hpi-await-region region :body c)
        (mv status effect c ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))
       (fn-hpi-tick c nil ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))
      (let* ((issuance-frame (and (eq issued :write) (equal next-ledger ledger)
                 (equal (fn-omk-at 14 c) body)
                 (equal before0 (hpicp-test-buffer-copy fn-hpq0)) (equal before1 (hpicp-test-buffer-copy fn-hpq1))
                 (equal before2 (hpicp-test-buffer-copy fn-hpq2)) (equal before3 (hpicp-test-buffer-copy fn-hpq3))
                 (equal before4 (hpicp-test-buffer-copy fn-hpb)) (equal before-digest (hpicp-test-digest-copy pgs-digest-state))))
             ; Corrupted resume or other-column backing, after valid baseline.
             (c (if (eq mode :context) (fn-hpi-set 17 (list region :pad) c) c))
             (other (mod (+ 1 region) 4))
             (fn-hpq0 (if (and (eq mode :canonical) (= other 0)) (update-fn-hpb-wi 0 (logxor 1 (fn-hpb-wi 0 fn-hpq0)) fn-hpq0) fn-hpq0))
             (fn-hpq1 (if (and (eq mode :canonical) (= other 1)) (update-fn-hpb-wi 0 (logxor 1 (fn-hpb-wi 0 fn-hpq1)) fn-hpq1) fn-hpq1))
             (fn-hpq2 (if (and (eq mode :canonical) (= other 2)) (update-fn-hpb-wi 0 (logxor 1 (fn-hpb-wi 0 fn-hpq2)) fn-hpq2) fn-hpq2))
             (fn-hpq3 (if (and (eq mode :canonical) (= other 3)) (update-fn-hpb-wi 0 (logxor 1 (fn-hpb-wi 0 fn-hpq3)) fn-hpq3) fn-hpq3))
             (context (fn-hpicp-ack-contextp c))
             (canonical (fn-hpicol-four-invariantp h "ABC" 17 (fn-omk-at 14 c) (fn-omk-at 15 c) fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3))
             (full (equal (fn-hpi-region-used region fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) 2048))
             (old0 (hpicp-test-buffer-copy fn-hpq0)) (old1 (hpicp-test-buffer-copy fn-hpq1))
             (old2 (hpicp-test-buffer-copy fn-hpq2)) (old3 (hpicp-test-buffer-copy fn-hpq3))
             (observation (fn-hie-observation c effect (fn-omk-at 3 c) ledger (if (eq mode :status) -1 16384) (if (eq mode :status) :error :ok) nil)))
       (mv-let (status out next next-ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
        (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
        (let* ((written (eq status :written))
               (conclusion (and (fn-hpicol-four-invariantp h "ABC" 17 (fn-omk-at 14 next) (fn-omk-at 15 next) fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3)
                 (eq (fn-omk-at 0 next) :body) (equal (fn-omk-at 12 next) (fn-omk-at 12 c))
                 (equal (fn-omk-at 14 next) (fn-omk-at 14 c))
                 (equal before4 (hpicp-test-buffer-copy fn-hpb)) (equal out nil) (equal next-ledger ledger)
                 (equal before-digest (hpicp-test-digest-copy pgs-digest-state))))
               (old-buffers (list old0 old1 old2 old3))
               (new-buffers (list (hpicp-test-buffer-copy fn-hpq0) (hpicp-test-buffer-copy fn-hpq1)
                                  (hpicp-test-buffer-copy fn-hpq2) (hpicp-test-buffer-copy fn-hpq3)))
               (selected (nth region old-buffers))
               (expected (update-nth region (list (car selected) 0 source maintenance) old-buffers))
               (structural (and (eq (fn-hpi-written-status (fn-omk-at 5 c) observation) :written)
                    (eq (fn-omk-at 0 next) :body) (equal (fn-omk-at 14 next) (fn-omk-at 14 c))
                    (equal (fn-omk-at 15 next) (fn-hpi-set region (+ 1 (nfix (fn-omk-at region (fn-omk-at 15 c)))) (fn-omk-at 15 c)))
                    (equal (fn-omk-at 16 next) (fn-hpi-set region (+ 1 (nfix (fn-omk-at region (fn-omk-at 16 c)))) (fn-omk-at 16 c)))
                    (equal (fn-omk-at 5 next) nil) (equal (fn-omk-at 17 next) nil)
                    (equal new-buffers expected) (equal before4 (hpicp-test-buffer-copy fn-hpb))
                    (equal out nil) (equal next-ledger ledger) (equal before-digest (hpicp-test-digest-copy pgs-digest-state)))))
         (mv (list baseline issuance-frame context canonical full written conclusion structural)
             fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))))))))))
)
(local (defun hpicp-test-local (column mode)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-hpq0 (mv-let (result fn-hpq0) (with-local-stobj fn-hpq1 (mv-let (result fn-hpq0 fn-hpq1) (with-local-stobj fn-hpq2 (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2) (with-local-stobj fn-hpq3 (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3) (with-local-stobj fn-hpb (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) (with-local-stobj pgs-digest-state (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) (hpicp-test-case column mode fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) (mv result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))) (mv result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3))) (mv result fn-hpq0 fn-hpq1 fn-hpq2))) (mv result fn-hpq0 fn-hpq1))) (mv result fn-hpq0))) result))))
; Constructed supported phase positive; complete literal premises and conclusions.
(assert-event (equal (hpicp-test-local 0 :positive) '(t t t t t t t t)))
; Labelled mutation/removal: context; complete literal premises and conclusions.
(assert-event (equal (hpicp-test-local 0 :context) '(t t nil t t t nil nil)))
; Labelled mutation/removal: canonical; complete literal premises and conclusions.
(assert-event (equal (hpicp-test-local 0 :canonical) '(t t t nil t t nil t)))
; Labelled mutation/removal: partial; complete literal premises and conclusions.
(assert-event (equal (hpicp-test-local 0 :partial) '(t t t t nil t nil t)))
; Labelled mutation/removal: status; complete literal premises and conclusions.
(assert-event (equal (hpicp-test-local 0 :status) '(t t t t t nil nil nil)))
; Constructed supported phase positive; complete literal premises and conclusions.
(assert-event (equal (hpicp-test-local 1 :positive) '(t t t t t t t t)))
; Labelled mutation/removal: context; complete literal premises and conclusions.
(assert-event (equal (hpicp-test-local 1 :context) '(t t nil t t t nil nil)))
; Labelled mutation/removal: canonical; complete literal premises and conclusions.
(assert-event (equal (hpicp-test-local 1 :canonical) '(t t t nil t t nil t)))
; Labelled mutation/removal: partial; complete literal premises and conclusions.
(assert-event (equal (hpicp-test-local 1 :partial) '(t t t t nil t nil t)))
; Labelled mutation/removal: status; complete literal premises and conclusions.
(assert-event (equal (hpicp-test-local 1 :status) '(t t t t t nil nil nil)))
; Constructed supported phase positive; complete literal premises and conclusions.
(assert-event (equal (hpicp-test-local 2 :positive) '(t t t t t t t t)))
; Labelled mutation/removal: context; complete literal premises and conclusions.
(assert-event (equal (hpicp-test-local 2 :context) '(t t nil t t t nil nil)))
; Labelled mutation/removal: canonical; complete literal premises and conclusions.
(assert-event (equal (hpicp-test-local 2 :canonical) '(t t t nil t t nil t)))
; Labelled mutation/removal: partial; complete literal premises and conclusions.
(assert-event (equal (hpicp-test-local 2 :partial) '(t t t t nil t nil t)))
; Labelled mutation/removal: status; complete literal premises and conclusions.
(assert-event (equal (hpicp-test-local 2 :status) '(t t t t t nil nil nil)))
; Constructed supported phase positive; complete literal premises and conclusions.
(assert-event (equal (hpicp-test-local 3 :positive) '(t t t t t t t t)))
; Labelled mutation/removal: context; complete literal premises and conclusions.
(assert-event (equal (hpicp-test-local 3 :context) '(t t nil t t t nil nil)))
; Labelled mutation/removal: canonical; complete literal premises and conclusions.
(assert-event (equal (hpicp-test-local 3 :canonical) '(t t t nil t t nil t)))
; Labelled mutation/removal: partial; complete literal premises and conclusions.
(assert-event (equal (hpicp-test-local 3 :partial) '(t t t t nil t nil t)))
; Labelled mutation/removal: status; complete literal premises and conclusions.
(assert-event (equal (hpicp-test-local 3 :status) '(t t t t t nil nil nil)))
