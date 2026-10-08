; The real copy followed by the host's acknowledgement entry.  All three
; premises have independent counterexamples; the positive trajectory is the
; failed barrier, cache-preserving restart, fresh copy, append, fence, finish.
(in-package "ACL2")
(include-book "store-log-copy-teeth-tests")
(set-ignore-ok t)
(defun lgca-copy-bs (s genesis)
 (declare (xargs :verify-guards nil))
 (fn-bsc-bs (fn-lgrc-final (fn-lgrc-attempt s :journal "K" :staging "stage" genesis 4096 0 nil) s)))
(defconst-eval *lgca-occupied*
 (lgrct-steps *lgct-before* '((:create :staging "stage" :ok) (:fsync-dir :staging :ok))))
(defconst-eval *lgca-occupied-bs* (lgca-copy-bs *lgca-occupied* *lgct-genesis*))
(defconst-eval *lgca-occupied-image* (fn-bs-crash *lgca-occupied-bs* nil))
(defconst-eval *lgca-short-bs* (lgca-copy-bs (lgrct-s0) *lgct-genesis*))
(defconst-eval *lgca-short-image* (fn-bs-crash *lgca-short-bs* nil))
(defconst-eval *lgca-invalid-bs* (lgca-copy-bs *lgct-before* nil))
(defconst-eval *lgca-invalid-ks* (fn-lgt-recover (fn-lgd-octets *lgct-str*) nil 4 4096 0))
(defconst *lgca-invalid-ops* '((:take (4 5 7) 0 0 0 64 1048576 4) (:seal :ok :ok :ok) (:fence :ok)))
(defconst-eval *lgca-invalid-final*
 (fn-lgu-host-final *lgca-invalid-bs* *lgca-invalid-ks* (append *lgca-invalid-ops* (fn-lgu-finishes 1)) 1 4096))
(defconst-eval *lgca-invalid-image* (fn-bs-crash (car *lgca-invalid-final*) nil))
(assert-event (equal (fn-lgk-acked (cdr *lgca-invalid-final*)) 1))
(assert-event (equal (car (fn-lg-scan (fn-bs-durable-content *lgca-invalid-image* 1) nil 4 4096)) nil))
(defconst-eval *lgca-mutant-bs* (lgcp-skip-file-barrier *lgct-before* :journal "K" :staging "stage" *lgct-genesis* 4096 0))
(defconst-eval *lgca-mutant-image* (fn-bs-crash *lgca-mutant-bs* nil))
(assert-event (equal (fn-bs-durable-content *lgca-mutant-image* 1) nil))
(defthm lgca-positive-premises
 (and (not (fn-bsc-lookup *lgct-before* :staging "stage"))
      (fn-frame-digestp *lgct-genesis*)
      (equal (fn-bsc-content *lgct-before* (fn-bsc-lookup *lgct-before* :journal "K"))
             (fn-lgd-octets *lgct-str*)))
 :rule-classes nil)
(defthm lgca-quiet-image-is-the-durable-store
 (implies (and (not (fn-bs-pending bs)) (fn-bs-crash-imagep bs image))
          (equal image (fn-bs-crash bs nil)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-bs-crash-imagep fn-bs-crash fn-bs-crash-select))))

(defconst *lgca-claim* '(let* ((bs0 (fn-bsc-bs s))
         (unit (fn-bs-unit bs0))
         (o (fn-bsc-content s (fn-bsc-lookup s j k)))
         (ino (fn-bs-next-ino bs0))
         (bs (fn-bsc-bs (fn-lgrc-final (fn-lgrc-attempt s j k stg stage genesis max floor nil) s)))
         (ks0 (fn-lgt-recover (fn-lgd-octets str) genesis unit max floor))
         (run (fn-lgu-host-run bs ks0 (append ops (fn-lgu-finishes n)) ino max))
         (final (fn-lgu-host-final bs ks0 (append ops (fn-lgu-finishes n)) ino max))
         (host (fn-lgu-acknowledge
                (fn-lgc-host-run (mv-nth 1 (fn-lgc-open str genesis unit max floor))
                                 (fn-lgu-host-kops bs ks0 ops ino max))
                n)))
    (((fresh (not (fn-bsc-lookup s stg stage)))
(genesis (fn-frame-digestp genesis))
(read (equal o (fn-lgd-octets str))))
(and (equal (fn-lgc-acked host) (fn-lgk-acked (cdr final)))
                  (implies (fn-bs-crash-imagep (car final) image)
                           (let ((a (fn-lgc-acked host))
                                 (recovered (fn-lgk-committed
                                             (fn-lgk-recover (fn-bs-durable-content image ino)
                                                             genesis (fn-bs-unit (car final)) max
                                                             next-txid))))
                             (and (<= a (len recovered))
                                  (equal (take a recovered) (take a (fn-lgk-committed (cdr final)))))))
                  (implies (and (member-equal pair run)
                                (fn-bs-crash-imagep (car pair) image))
                           (let ((a (fn-lgk-acked (cdr pair)))
                                 (recovered (fn-lgk-committed
                                             (fn-lgk-recover (fn-bs-durable-content image ino)
                                                             genesis (fn-bs-unit (car pair)) max
                                                             next-txid))))
                             (and (<= a (len recovered))
                                  (equal (take a recovered) (take a (fn-lgk-committed (cdr pair)))))))))))
(teeth-ground-lemma lgca-positive *lgca-claim*
 ((s *lgct-before*) (j :journal) (k "K") (stg :staging) (stage "stage") (genesis *lgct-genesis*) (max 4096) (floor 0) (str *lgct-str*) (ops *lgct-ops*) (n 1) (image *lgct-image*) (pair *lgct-final*) (next-txid 0))
 :hints (("Goal" :in-theory (theory 'minimal-theory)
 :use (lgca-positive-premises (:instance fn-lgrc-acknowledge-from-the-copy (s *lgct-before*) (j :journal) (k "K") (stg :staging) (stage "stage") (genesis *lgct-genesis*) (max 4096) (floor 0) (str *lgct-str*) (ops *lgct-ops*) (n 1) (image *lgct-image*) (pair *lgct-final*) (next-txid 0))))))
(teeth-ground-lemma lgca-without-fresh *lgca-claim*
 ((s *lgca-occupied*) (j :journal) (k "K") (stg :staging) (stage "stage") (genesis *lgct-genesis*) (max 4096) (floor 0) (str *lgct-str*) (ops nil) (n 0) (image *lgca-occupied-image*) (pair nil) (next-txid 0))
 :without fresh
 :hints (("Goal" :do-not-induct t
 :use ( (:instance fn-bs-crash-imagep-suff (s *lgca-occupied-bs*) (image *lgca-occupied-image*) (choices nil)))
 :in-theory (e/d (fn-lgrc-attempt fn-lgrc-attempt-ops fn-lgrc-out fn-lgrc-final fn-bsc-run fn-bsc-step fn-bsc-bs fn-bsc-content fn-bsc-lookup
 fn-lgu-host-final fn-lgu-host-run fn-lgu-host-kops fn-lgu-finishes fn-lgu-acknowledge fn-lgc-host-run fn-lgc-open fn-lgc-acked fn-lgc-of fn-lgc-make
 fn-lgk-committed fn-lgk-acked fn-lgk-frontier fn-lgk-make fn-lgt-recover fn-lgk-recover lgcp-skip-file-barrier )
 (fn-lgt-next-after fn-bs-crash-imagep (:definition fn-lg-scan) (:definition fn-lg-scan-last))))))
(teeth-ground-lemma lgca-without-read *lgca-claim*
 ((s (lgrct-s0)) (j :journal) (k "K") (stg :staging) (stage "stage") (genesis *lgct-genesis*) (max 4096) (floor 0) (str *lgct-str*) (ops nil) (n 0) (image *lgca-short-image*) (pair nil) (next-txid 0))
 :without read
 :hints (("Goal" :do-not-induct t
 :use ( (:instance fn-bs-crash-imagep-suff (s *lgca-short-bs*) (image *lgca-short-image*) (choices nil)))
 :in-theory (e/d (fn-lgrc-attempt fn-lgrc-attempt-ops fn-lgrc-out fn-lgrc-final fn-bsc-run fn-bsc-step fn-bsc-bs fn-bsc-content fn-bsc-lookup
 fn-lgu-host-final fn-lgu-host-run fn-lgu-host-kops fn-lgu-finishes fn-lgu-acknowledge fn-lgc-host-run fn-lgc-open fn-lgc-acked fn-lgc-of fn-lgc-make
 fn-lgk-committed fn-lgk-acked fn-lgk-frontier fn-lgk-make fn-lgt-recover fn-lgk-recover lgcp-skip-file-barrier )
 (fn-lgt-next-after fn-bs-crash-imagep (:definition fn-lg-scan) (:definition fn-lg-scan-last))))))
(teeth-ground-lemma lgca-without-genesis *lgca-claim*
 ((s *lgct-before*) (j :journal) (k "K") (stg :staging) (stage "stage") (genesis nil) (max 4096) (floor 0) (str *lgct-str*) (ops *lgca-invalid-ops*) (n 1) (image *lgca-invalid-image*) (pair *lgca-invalid-final*) (next-txid 0))
 :without genesis
 :hints (("Goal" :do-not-induct t
 :use ( (:instance fn-bs-crash-imagep-suff (s (car *lgca-invalid-final*)) (image *lgca-invalid-image*) (choices nil)))
 :in-theory (e/d (fn-lgrc-attempt fn-lgrc-attempt-ops fn-lgrc-out fn-lgrc-final fn-bsc-run fn-bsc-step fn-bsc-bs fn-bsc-content fn-bsc-lookup
 fn-lgu-host-final fn-lgu-host-run fn-lgu-host-kops fn-lgu-finishes fn-lgu-acknowledge fn-lgc-host-run fn-lgc-open fn-lgc-acked fn-lgc-of fn-lgc-make
 fn-lgk-committed fn-lgk-acked fn-lgk-frontier fn-lgk-make fn-lgt-recover fn-lgk-recover lgcp-skip-file-barrier fn-lgt-next-after)
 (fn-bs-crash-imagep (:definition fn-lg-scan) (:definition fn-lg-scan-last))))))
(teeth-ground-lemma lgca-skipped-fence *lgca-claim*
 ((s *lgct-before*) (j :journal) (k "K") (stg :staging) (stage "stage") (genesis *lgct-genesis*) (max 4096) (floor 0) (str *lgct-str*) (ops nil) (n 0) (image *lgca-mutant-image*) (pair nil) (next-txid 0))
 :mutation (:conclusion (let* ((bs (lgcp-skip-file-barrier s j k stg stage genesis max floor))
(run (fn-lgu-host-run bs ks0 (append ops (fn-lgu-finishes n)) ino max))
(final (fn-lgu-host-final bs ks0 (append ops (fn-lgu-finishes n)) ino max))
(host (fn-lgu-acknowledge
                (fn-lgc-host-run (mv-nth 1 (fn-lgc-open str genesis unit max floor))
                                 (fn-lgu-host-kops bs ks0 ops ino max))
                n)))
(and (equal (fn-lgc-acked host) (fn-lgk-acked (cdr final)))
                  (implies (fn-bs-crash-imagep (car final) image)
                           (let ((a (fn-lgc-acked host))
                                 (recovered (fn-lgk-committed
                                             (fn-lgk-recover (fn-bs-durable-content image ino)
                                                             genesis (fn-bs-unit (car final)) max
                                                             next-txid))))
                             (and (<= a (len recovered))
                                  (equal (take a recovered) (take a (fn-lgk-committed (cdr final)))))))
                  (implies (and (member-equal pair run)
                                (fn-bs-crash-imagep (car pair) image))
                           (let ((a (fn-lgk-acked (cdr pair)))
                                 (recovered (fn-lgk-committed
                                             (fn-lgk-recover (fn-bs-durable-content image ino)
                                                             genesis (fn-bs-unit (car pair)) max
                                                             next-txid))))
                             (and (<= a (len recovered))
                                  (equal (take a recovered) (take a (fn-lgk-committed (cdr pair))))))))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance lgca-quiet-image-is-the-durable-store (bs *lgct-bs*) (image *lgca-mutant-image*)) (:instance fn-bs-crash-imagep-suff (s *lgca-mutant-bs*) (image *lgca-mutant-image*) (choices nil)))
 :in-theory (e/d (fn-lgrc-attempt fn-lgrc-attempt-ops fn-lgrc-out fn-lgrc-final fn-bsc-run fn-bsc-step fn-bsc-bs fn-bsc-content fn-bsc-lookup
 fn-lgu-host-final fn-lgu-host-run fn-lgu-host-kops fn-lgu-finishes fn-lgu-acknowledge fn-lgc-host-run fn-lgc-open fn-lgc-acked fn-lgc-of fn-lgc-make
 fn-lgk-committed fn-lgk-acked fn-lgk-frontier fn-lgk-make fn-lgt-recover fn-lgk-recover lgcp-skip-file-barrier )
 (fn-lgt-next-after fn-bs-crash-imagep (:definition fn-lg-scan) (:definition fn-lg-scan-last))))))
; Host fnn-recover-log and fnn-log-ack: tests/test_native_log.py::
; test_every_log_cut_recovers_to_a_prefix and tests/campaign/
; test_native_operator_campaign.py::test_served_owner_cuts_stop_and_production_refusals.
; The retained-clean-cache fault case is specified in TEETH-CRITICAL-HOST-TESTS.
(defteeth fn-lgrc-acknowledge-from-the-copy
 :claim (let* ((bs0 (fn-bsc-bs s))
         (unit (fn-bs-unit bs0))
         (o (fn-bsc-content s (fn-bsc-lookup s j k)))
         (ino (fn-bs-next-ino bs0))
         (bs (fn-bsc-bs (fn-lgrc-final (fn-lgrc-attempt s j k stg stage genesis max floor nil) s)))
         (ks0 (fn-lgt-recover (fn-lgd-octets str) genesis unit max floor))
         (run (fn-lgu-host-run bs ks0 (append ops (fn-lgu-finishes n)) ino max))
         (final (fn-lgu-host-final bs ks0 (append ops (fn-lgu-finishes n)) ino max))
         (host (fn-lgu-acknowledge
                (fn-lgc-host-run (mv-nth 1 (fn-lgc-open str genesis unit max floor))
                                 (fn-lgu-host-kops bs ks0 ops ino max))
                n)))
    (((fresh (not (fn-bsc-lookup s stg stage)))
(genesis (fn-frame-digestp genesis))
(read (equal o (fn-lgd-octets str))))
(and (equal (fn-lgc-acked host) (fn-lgk-acked (cdr final)))
                  (implies (fn-bs-crash-imagep (car final) image)
                           (let ((a (fn-lgc-acked host))
                                 (recovered (fn-lgk-committed
                                             (fn-lgk-recover (fn-bs-durable-content image ino)
                                                             genesis (fn-bs-unit (car final)) max
                                                             next-txid))))
                             (and (<= a (len recovered))
                                  (equal (take a recovered) (take a (fn-lgk-committed (cdr final)))))))
                  (implies (and (member-equal pair run)
                                (fn-bs-crash-imagep (car pair) image))
                           (let ((a (fn-lgk-acked (cdr pair)))
                                 (recovered (fn-lgk-committed
                                             (fn-lgk-recover (fn-bs-durable-content image ino)
                                                             genesis (fn-bs-unit (car pair)) max
                                                             next-txid))))
                             (and (<= a (len recovered))
                                  (equal (take a recovered) (take a (fn-lgk-committed (cdr pair))))))))))
 :subject fn-lgu-acknowledge
 :witness ((s *lgct-before*) (j :journal) (k "K") (stg :staging) (stage "stage") (genesis *lgct-genesis*) (max 4096) (floor 0) (str *lgct-str*) (ops *lgct-ops*) (n 1) (image *lgct-image*) (pair *lgct-final*) (next-txid 0))
 :witness-lemma lgca-positive
 :breaks ((fresh ((s *lgca-occupied*) (j :journal) (k "K") (stg :staging) (stage "stage") (genesis *lgct-genesis*) (max 4096) (floor 0) (str *lgct-str*) (ops nil) (n 0) (image *lgca-occupied-image*) (pair nil) (next-txid 0)) :lemma lgca-without-fresh)
 (genesis ((s *lgct-before*) (j :journal) (k "K") (stg :staging) (stage "stage") (genesis nil) (max 4096) (floor 0) (str *lgct-str*) (ops *lgca-invalid-ops*) (n 1) (image *lgca-invalid-image*) (pair *lgca-invalid-final*) (next-txid 0)) :lemma lgca-without-genesis)
 (read ((s (lgrct-s0)) (j :journal) (k "K") (stg :staging) (stage "stage") (genesis *lgct-genesis*) (max 4096) (floor 0) (str *lgct-str*) (ops nil) (n 0) (image *lgca-short-image*) (pair nil) (next-txid 0)) :lemma lgca-without-read))
 :mutations ((skipped-file-fence (:conclusion (let* ((bs (lgcp-skip-file-barrier s j k stg stage genesis max floor))
(run (fn-lgu-host-run bs ks0 (append ops (fn-lgu-finishes n)) ino max))
(final (fn-lgu-host-final bs ks0 (append ops (fn-lgu-finishes n)) ino max))
(host (fn-lgu-acknowledge
                (fn-lgc-host-run (mv-nth 1 (fn-lgc-open str genesis unit max floor))
                                 (fn-lgu-host-kops bs ks0 ops ino max))
                n)))
(and (equal (fn-lgc-acked host) (fn-lgk-acked (cdr final)))
                  (implies (fn-bs-crash-imagep (car final) image)
                           (let ((a (fn-lgc-acked host))
                                 (recovered (fn-lgk-committed
                                             (fn-lgk-recover (fn-bs-durable-content image ino)
                                                             genesis (fn-bs-unit (car final)) max
                                                             next-txid))))
                             (and (<= a (len recovered))
                                  (equal (take a recovered) (take a (fn-lgk-committed (cdr final)))))))
                  (implies (and (member-equal pair run)
                                (fn-bs-crash-imagep (car pair) image))
                           (let ((a (fn-lgk-acked (cdr pair)))
                                 (recovered (fn-lgk-committed
                                             (fn-lgk-recover (fn-bs-durable-content image ino)
                                                             genesis (fn-bs-unit (car pair)) max
                                                             next-txid))))
                             (and (<= a (len recovered))
                                  (equal (take a recovered) (take a (fn-lgk-committed (cdr pair))))))))))
 ((s *lgct-before*) (j :journal) (k "K") (stg :staging) (stage "stage") (genesis *lgct-genesis*) (max 4096) (floor 0) (str *lgct-str*) (ops nil) (n 0) (image *lgca-mutant-image*) (pair nil) (next-txid 0))
 :fault "publish the copied inode after skipping its file barrier" :lemma lgca-skipped-fence)))
