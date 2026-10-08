; Critical host acknowledgement evidence, from the failed-barrier/restart
; trajectory and the actual copy program, not a spliced post-open state.
(in-package "ACL2")
(include-book "store-log-recover-copy-tests")
(include-book "teeth-ground-lemma")
(defconst-eval *lgct-before* (lgrct-restarted))
(defconst-eval *lgct-copied* (lgrct-a2-recovered))
(defconst-eval *lgct-bs* (fn-bsc-bs *lgct-copied*))
(defconst-eval *lgct-str*
  (fn-record-octets-string (fn-bsc-content *lgct-before* (fn-bsc-lookup *lgct-before* :journal "K"))))
(defconst-eval *lgct-genesis* (lgrct-genesis))
(defconst *lgct-ops* '((:take (4 5 7) 1 0 0 64 1048576 4)
                      (:seal :ok :ok :ok) (:fence :ok)))
(defconst-eval *lgct-ks*
  (fn-lgt-recover (fn-lgd-octets *lgct-str*) *lgct-genesis* 4 4096 0))
(defconst-eval *lgct-final*
  (fn-lgu-host-final *lgct-bs* *lgct-ks* (append *lgct-ops* (fn-lgu-finishes 1)) 1 4096))
(defconst-eval *lgct-image* (fn-bs-crash (car *lgct-final*) nil))
(assert-event (equal (fn-lgk-acked (cdr *lgct-final*)) 4))
(assert-event (fn-bs-crash-choicesp nil (fn-bs-pending (car *lgct-final*)) 4))

; Bound claims use ground lemmas only for the nonexecutable crash-image predicate.
(set-ignore-ok t)
(defthm lgct-related
 (fn-lgk-relp *lgct-bs*
   (fn-lgt-recover (fn-lgd-octets *lgct-str*) *lgct-genesis* 4 4096 0)
   1 *lgct-genesis* 4096)
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :in-theory (e/d (fn-lgk-relp fn-lgk-content-okp fn-lgt-recover fn-lgk-recover
                           fn-lgk-make fn-lgk-committed fn-lgk-last fn-lgk-frontier
                           fn-lgk-inflight fn-lgk-batch fn-lgk-acked fn-lgk-phase)
                          (fn-lgt-next-after (:definition fn-lg-scan)
                           (:definition fn-lg-scan-last))))))

(defconst-eval *lgct-uncopied-bs* (fn-bsc-bs *lgct-before*))
(defconst-eval *lgct-uncopied-image* (fn-bs-crash *lgct-uncopied-bs* nil))
(defconst-eval *lgct-open-image* (fn-bs-crash *lgct-bs* nil))
; Wrong implementation: recovery selects the pre-copy inode, not the new one.
(defun lgct-open-stale-inode (image genesis unit max next-txid)
 (declare (xargs :verify-guards nil))
 (fn-lgk-recover (fn-bs-durable-content image 0) genesis unit max next-txid))

(defconst *lgct-kernel-claim* '(let* ((ks0 (fn-lgt-recover (fn-lgd-octets s) genesis (fn-bs-unit bs) max floor))
         (final (fn-lgu-host-final bs ks0 ops ino max))
         (host (fn-lgc-host-run (mv-nth 1 (fn-lgc-open s genesis (fn-bs-unit bs) max floor))
                                (fn-lgu-host-kops bs ks0 ops ino max))))
    (((related (fn-lgk-relp bs ks0 ino genesis max)))
(and (equal (fn-lgc-acked host) (fn-lgk-acked (cdr final)))
                  (implies (fn-bs-crash-imagep (car final) image)
                           (let ((a (fn-lgc-acked host))
                                 (recovered (fn-lgk-committed
                                             (fn-lgk-recover (fn-bs-durable-content image ino)
                                                             genesis (fn-bs-unit (car final)) max
                                                             next-txid))))
                             (and (<= a (len recovered))
                                  (equal (take a recovered)
                                         (take a (fn-lgk-committed (cdr final)))))))))))
(teeth-ground-lemma lgct-kernel-witness *lgct-kernel-claim*
 ((s *lgct-str*) (genesis *lgct-genesis*) (max 4096) (floor 0) (next-txid 0) (bs *lgct-bs*) (ino 1) (ops (append *lgct-ops* (fn-lgu-finishes 1))) (image *lgct-image*))
 :hints (("Goal" :in-theory (union-theories '(fn-bs-unit) (theory 'minimal-theory))
            :use (lgct-related (:instance fn-lgu-host-kernel-acknowledges-only-recoverable-records (s *lgct-str*) (genesis *lgct-genesis*) (max 4096) (floor 0) (next-txid 0) (bs *lgct-bs*) (ino 1) (ops (append *lgct-ops* (fn-lgu-finishes 1))) (image *lgct-image*))))))
(teeth-ground-lemma lgct-kernel-without-relation *lgct-kernel-claim*
 ((s *lgct-str*) (genesis *lgct-genesis*) (max 4096) (floor 0) (next-txid 0) (bs *lgct-uncopied-bs*) (ino 0) (ops nil) (image *lgct-uncopied-image*))
 :without related
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-bs-crash-imagep-suff (s *lgct-uncopied-bs*) (image *lgct-uncopied-image*) (choices nil)))
 :in-theory (e/d (fn-lgu-host-final fn-lgu-host-kops fn-lgu-host-run fn-lgu-finishes fn-lgu-acknowledge
                  fn-lgc-host-run fn-lgc-open fn-lgc-acked fn-lgc-of fn-lgc-make fn-lgk-committed fn-lgk-acked
                  fn-lgk-make fn-lgt-recover fn-lgk-recover fn-lgk-relp fn-lgk-content-okp lgct-open-stale-inode)
                 (fn-lgt-next-after fn-bs-crash-imagep (:definition fn-lg-scan) (:definition fn-lg-scan-last))))))
(teeth-ground-lemma lgct-kernel-stale-inode *lgct-kernel-claim*
 ((s *lgct-str*) (genesis *lgct-genesis*) (max 4096) (floor 0) (next-txid 0) (bs *lgct-bs*) (ino 1) (ops nil) (image *lgct-open-image*))
 :mutation (:conclusion (let ((a (fn-lgc-acked host))
                    (recovered (fn-lgk-committed (lgct-open-stale-inode image genesis (fn-bs-unit bs) max next-txid))))
               (and (<= a (len recovered))
                    (equal (take a recovered) (take a (fn-lgk-committed (cdr final)))))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-bs-crash-imagep-suff (s *lgct-bs*) (image *lgct-open-image*) (choices nil)))
 :in-theory (e/d (fn-lgu-host-final fn-lgu-host-kops fn-lgu-host-run fn-lgu-finishes fn-lgu-acknowledge
                  fn-lgc-host-run fn-lgc-open fn-lgc-acked fn-lgc-of fn-lgc-make fn-lgk-committed fn-lgk-acked
                  fn-lgk-make fn-lgt-recover fn-lgk-recover fn-lgk-relp fn-lgk-content-okp lgct-open-stale-inode)
                 (fn-lgt-next-after fn-bs-crash-imagep (:definition fn-lg-scan) (:definition fn-lg-scan-last))))))
; Host fnn-log-ack / fnn-recover-log, exercised by
; tests/campaign/test_native_operator_campaign.py::test_served_owner_cuts_stop_and_production_refusals.
(defteeth fn-lgu-host-kernel-acknowledges-only-recoverable-records
 :claim (let* ((ks0 (fn-lgt-recover (fn-lgd-octets s) genesis (fn-bs-unit bs) max floor))
         (final (fn-lgu-host-final bs ks0 ops ino max))
         (host (fn-lgc-host-run (mv-nth 1 (fn-lgc-open s genesis (fn-bs-unit bs) max floor))
                                (fn-lgu-host-kops bs ks0 ops ino max))))
    (((related (fn-lgk-relp bs ks0 ino genesis max)))
(and (equal (fn-lgc-acked host) (fn-lgk-acked (cdr final)))
                  (implies (fn-bs-crash-imagep (car final) image)
                           (let ((a (fn-lgc-acked host))
                                 (recovered (fn-lgk-committed
                                             (fn-lgk-recover (fn-bs-durable-content image ino)
                                                             genesis (fn-bs-unit (car final)) max
                                                             next-txid))))
                             (and (<= a (len recovered))
                                  (equal (take a recovered)
                                         (take a (fn-lgk-committed (cdr final))))))))))
 :subject fn-lgc-host-run
 :witness ((s *lgct-str*) (genesis *lgct-genesis*) (max 4096) (floor 0) (next-txid 0) (bs *lgct-bs*) (ino 1) (ops (append *lgct-ops* (fn-lgu-finishes 1))) (image *lgct-image*))
 :witness-lemma lgct-kernel-witness
 :breaks ((related ((s *lgct-str*) (genesis *lgct-genesis*) (max 4096) (floor 0) (next-txid 0) (bs *lgct-uncopied-bs*) (ino 0) (ops nil) (image *lgct-uncopied-image*)) :lemma lgct-kernel-without-relation))
 :mutations ((stale-inode (:conclusion (let ((a (fn-lgc-acked host))
                    (recovered (fn-lgk-committed (lgct-open-stale-inode image genesis (fn-bs-unit bs) max next-txid))))
               (and (<= a (len recovered))
                    (equal (take a recovered) (take a (fn-lgk-committed (cdr final)))))))
 ((s *lgct-str*) (genesis *lgct-genesis*) (max 4096) (floor 0) (next-txid 0) (bs *lgct-bs*) (ino 1) (ops nil) (image *lgct-open-image*))
 :fault "recovery selects the pre-copy inode after the new inode was published" :lemma lgct-kernel-stale-inode)))

(defconst *lgct-ack-claim* '(let* ((ks0 (fn-lgt-recover (fn-lgd-octets s) genesis (fn-bs-unit bs) max floor))
         (run (fn-lgu-host-run bs ks0 (append ops (fn-lgu-finishes n)) ino max))
         (final (fn-lgu-host-final bs ks0 (append ops (fn-lgu-finishes n)) ino max))
         (host (fn-lgu-acknowledge
                (fn-lgc-host-run (mv-nth 1 (fn-lgc-open s genesis (fn-bs-unit bs) max floor))
                                 (fn-lgu-host-kops bs ks0 ops ino max))
                n)))
    (((related (fn-lgk-relp bs ks0 ino genesis max)))
(and
              ;; the count the host holds after acknowledging is the run's
              (equal (fn-lgc-acked host) (fn-lgk-acked (cdr final)))
              ;; ... and every crash image of the store it leaves recovers it
              (implies (fn-bs-crash-imagep (car final) image)
                       (let ((a (fn-lgc-acked host))
                             (recovered (fn-lgk-committed
                                         (fn-lgk-recover (fn-bs-durable-content image ino)
                                                         genesis (fn-bs-unit (car final)) max next-txid))))
                         (and (<= a (len recovered))
                              (equal (take a recovered) (take a (fn-lgk-committed (cdr final)))))))
              ;; at EVERY cut of the run, its acknowledged records are recovered
              ;; from every crash image of the cut
              (implies (and (member-equal pair run)
                            (fn-bs-crash-imagep (car pair) image))
                       (let ((a (fn-lgk-acked (cdr pair)))
                             (recovered (fn-lgk-committed
                                         (fn-lgk-recover (fn-bs-durable-content image ino)
                                                         genesis (fn-bs-unit (car pair)) max next-txid))))
                         (and (<= a (len recovered))
                              (equal (take a recovered) (take a (fn-lgk-committed (cdr pair)))))))))))
(teeth-ground-lemma lgct-ack-witness *lgct-ack-claim*
 ((s *lgct-str*) (genesis *lgct-genesis*) (max 4096) (floor 0) (next-txid 0) (bs *lgct-bs*) (ino 1) (ops *lgct-ops*) (image *lgct-image*) (n 1) (pair *lgct-final*))
 :hints (("Goal" :in-theory (union-theories '(fn-bs-unit) (theory 'minimal-theory))
            :use (lgct-related (:instance fn-lgu-acknowledge-acknowledges-only-recoverable-records (s *lgct-str*) (genesis *lgct-genesis*) (max 4096) (floor 0) (next-txid 0) (bs *lgct-bs*) (ino 1) (ops *lgct-ops*) (image *lgct-image*) (n 1) (pair *lgct-final*))))))
(teeth-ground-lemma lgct-ack-without-relation *lgct-ack-claim*
 ((s *lgct-str*) (genesis *lgct-genesis*) (max 4096) (floor 0) (next-txid 0) (bs *lgct-uncopied-bs*) (ino 0) (ops nil) (image *lgct-uncopied-image*) (n 0) (pair nil))
 :without related
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-bs-crash-imagep-suff (s *lgct-uncopied-bs*) (image *lgct-uncopied-image*) (choices nil)))
 :in-theory (e/d (fn-lgu-host-final fn-lgu-host-kops fn-lgu-host-run fn-lgu-finishes fn-lgu-acknowledge
                  fn-lgc-host-run fn-lgc-open fn-lgc-acked fn-lgc-of fn-lgc-make fn-lgk-committed fn-lgk-acked
                  fn-lgk-make fn-lgt-recover fn-lgk-recover fn-lgk-relp fn-lgk-content-okp lgct-open-stale-inode)
                 (fn-lgt-next-after fn-bs-crash-imagep (:definition fn-lg-scan) (:definition fn-lg-scan-last))))))
(teeth-ground-lemma lgct-ack-stale-inode *lgct-ack-claim*
 ((s *lgct-str*) (genesis *lgct-genesis*) (max 4096) (floor 0) (next-txid 0) (bs *lgct-bs*) (ino 1) (ops nil) (image *lgct-open-image*) (n 0) (pair nil))
 :mutation (:conclusion (let ((a (fn-lgc-acked host))
                    (recovered (fn-lgk-committed (lgct-open-stale-inode image genesis (fn-bs-unit bs) max next-txid))))
               (and (<= a (len recovered))
                    (equal (take a recovered) (take a (fn-lgk-committed (cdr final)))))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-bs-crash-imagep-suff (s *lgct-bs*) (image *lgct-open-image*) (choices nil)))
 :in-theory (e/d (fn-lgu-host-final fn-lgu-host-kops fn-lgu-host-run fn-lgu-finishes fn-lgu-acknowledge
                  fn-lgc-host-run fn-lgc-open fn-lgc-acked fn-lgc-of fn-lgc-make fn-lgk-committed fn-lgk-acked
                  fn-lgk-make fn-lgt-recover fn-lgk-recover fn-lgk-relp fn-lgk-content-okp lgct-open-stale-inode)
                 (fn-lgt-next-after fn-bs-crash-imagep (:definition fn-lg-scan) (:definition fn-lg-scan-last))))))
; Host fnn-log-ack / fnn-recover-log, exercised by
; tests/campaign/test_native_operator_campaign.py::test_served_owner_cuts_stop_and_production_refusals.
(defteeth fn-lgu-acknowledge-acknowledges-only-recoverable-records
 :claim (let* ((ks0 (fn-lgt-recover (fn-lgd-octets s) genesis (fn-bs-unit bs) max floor))
         (run (fn-lgu-host-run bs ks0 (append ops (fn-lgu-finishes n)) ino max))
         (final (fn-lgu-host-final bs ks0 (append ops (fn-lgu-finishes n)) ino max))
         (host (fn-lgu-acknowledge
                (fn-lgc-host-run (mv-nth 1 (fn-lgc-open s genesis (fn-bs-unit bs) max floor))
                                 (fn-lgu-host-kops bs ks0 ops ino max))
                n)))
    (((related (fn-lgk-relp bs ks0 ino genesis max)))
(and
              ;; the count the host holds after acknowledging is the run's
              (equal (fn-lgc-acked host) (fn-lgk-acked (cdr final)))
              ;; ... and every crash image of the store it leaves recovers it
              (implies (fn-bs-crash-imagep (car final) image)
                       (let ((a (fn-lgc-acked host))
                             (recovered (fn-lgk-committed
                                         (fn-lgk-recover (fn-bs-durable-content image ino)
                                                         genesis (fn-bs-unit (car final)) max next-txid))))
                         (and (<= a (len recovered))
                              (equal (take a recovered) (take a (fn-lgk-committed (cdr final)))))))
              ;; at EVERY cut of the run, its acknowledged records are recovered
              ;; from every crash image of the cut
              (implies (and (member-equal pair run)
                            (fn-bs-crash-imagep (car pair) image))
                       (let ((a (fn-lgk-acked (cdr pair)))
                             (recovered (fn-lgk-committed
                                         (fn-lgk-recover (fn-bs-durable-content image ino)
                                                         genesis (fn-bs-unit (car pair)) max next-txid))))
                         (and (<= a (len recovered))
                              (equal (take a recovered) (take a (fn-lgk-committed (cdr pair))))))))))
 :subject fn-lgu-acknowledge
 :witness ((s *lgct-str*) (genesis *lgct-genesis*) (max 4096) (floor 0) (next-txid 0) (bs *lgct-bs*) (ino 1) (ops *lgct-ops*) (image *lgct-image*) (n 1) (pair *lgct-final*))
 :witness-lemma lgct-ack-witness
 :breaks ((related ((s *lgct-str*) (genesis *lgct-genesis*) (max 4096) (floor 0) (next-txid 0) (bs *lgct-uncopied-bs*) (ino 0) (ops nil) (image *lgct-uncopied-image*) (n 0) (pair nil)) :lemma lgct-ack-without-relation))
 :mutations ((stale-inode (:conclusion (let ((a (fn-lgc-acked host))
                    (recovered (fn-lgk-committed (lgct-open-stale-inode image genesis (fn-bs-unit bs) max next-txid))))
               (and (<= a (len recovered))
                    (equal (take a recovered) (take a (fn-lgk-committed (cdr final)))))))
 ((s *lgct-str*) (genesis *lgct-genesis*) (max 4096) (floor 0) (next-txid 0) (bs *lgct-bs*) (ino 1) (ops nil) (image *lgct-open-image*) (n 0) (pair nil))
 :fault "recovery selects the pre-copy inode after the new inode was published" :lemma lgct-ack-stale-inode)))
