; Additional teeth for physical persistence and the concrete dispatcher projection.
(in-package "ACL2")
(include-book "gc-pipeline-durable-tests")
(include-book "gc-pipeline-tests")
(include-book "../../books/defkeystone")
(defconst *gcpt-last* (fn-lg-last-trailer '((90)) *gcp-genesis*))
(defconst *gcpt-ks* (fn-lgk-make '((90)) *gcpt-last* 512 4 '((66)) '((65)) 1 :appended))
(defconst *gcpt-p* (fn-lgk-pipe-make *gcpt-ks* nil))
(defconst *gcpt-base*
 (fn-bs-make 512 (list (cons 0 (append (fn-lg-log '((90)) *gcp-genesis* 512)
                                     (make-list 2048 :initial-element 0)))) nil
  (list (list :write 0 512 (fn-lg-log '((65)) *gcpt-last* 512))) 1))
(defconst *gcpt-written*
 (mv-let (word after) (fn-lgk-pipe-physical-append *gcpt-base* *gcpt-p* 0 2560 :ok)
  (declare (ignore word)) after))
(defconst *gcpt-tail* (nthcdr 1 (fn-bs-pending *gcpt-written*)))
(defconst *gcpt-fenced*
 (mv-let (word after) (fn-bs-pipe-fsync-prefix *gcpt-written* 0 1 :ok)
  (declare (ignore word)) after))
(defconst *gcpt-image* (fn-bs-crash *gcpt-fenced* nil))
(defconst *gcpt-empty* (fn-bs-make 512 (list (cons 0 nil)) nil nil 1))
(defconst *gcpt-bad-written* (fn-bs-pipe-with-pending *gcpt-empty* (fn-bs-pending *gcpt-written*)))
(assert-event (and (equal (fn-lgk-acked *gcpt-ks*) 1)
 (fn-lgk-pipe-store-linkp *gcpt-written* *gcpt-base* *gcpt-ks* *gcpt-tail* 0 *gcp-genesis* 100)))

(defteeth fn-lgk-pipe-physical-append-establishes-link
 :claim (((:relation (and (fn-bs-shapep bs) (true-listp (fn-bs-pending bs)) (fn-lgk-pipe-okp p h) (fn-lgk-relp bs (fn-lgk-pipe-ks p) ino genesis max) (equal (fn-lgk-phase (fn-lgk-pipe-ks p)) :appended) (fn-lgk-behind-admitsp p (fn-bs-unit bs) extent)))) (fn-lgk-pipe-store-linkp (mv-nth 1 (fn-lgk-pipe-physical-append bs p ino extent outcome)) bs (fn-lgk-pipe-ks p) (nthcdr (len (fn-bs-pending bs)) (fn-bs-pending (mv-nth 1 (fn-lgk-pipe-physical-append bs p ino extent outcome)))) ino genesis max)) :subject fn-lgk-pipe-physical-append
 :witness ((bs *gcpt-base*) (p *gcpt-p*) (h '((90) (65) (66))) (ino 0) (extent 2560) (outcome :ok) (genesis *gcp-genesis*) (max 100)) :breaks ((:relation ((bs *gcpt-empty*) (p *gcpt-p*) (h '((90) (65) (66))) (ino 0) (extent 2560) (outcome :ok) (genesis *gcp-genesis*) (max 100))))
 :mutations (:not-applicable "The relation removal exercises loss of the durable prefix; explicit early-ACK and prefix-cut must-fails are in gc-pipeline-durable-tests."))

(defteeth fn-lgk-pipe-prefix-fence-safe
 :claim (((:relation (fn-lgk-pipe-store-linkp bs base ks tail ino genesis max))) (fn-lgu-safep (mv-nth 1 (fn-bs-pipe-fsync-prefix bs ino (len (fn-bs-pending base)) :ok)) (fn-lgk-fence ks (fn-bs-unit base)) ino genesis max)) :subject fn-bs-pipe-fsync-prefix
 :witness ((bs *gcpt-written*) (base *gcpt-base*) (ks *gcpt-ks*) (tail *gcpt-tail*) (ino 0) (genesis *gcp-genesis*) (max 100)) :breaks ((:relation ((bs *gcpt-bad-written*) (base *gcpt-base*) (ks *gcpt-ks*) (tail *gcpt-tail*) (ino 0) (genesis *gcp-genesis*) (max 100))))
 :mutations (:not-applicable "The relation removal exercises loss of the durable prefix; explicit early-ACK and prefix-cut must-fails are in gc-pipeline-durable-tests."))

(defteeth fn-lgk-pipe-prefix-failure-keeps-durable-prefix
 :claim (((:relation (fn-lgk-pipe-store-linkp bs base ks tail ino genesis max))) (fn-lgu-safep (mv-nth 1 (fn-bs-pipe-fsync-prefix bs ino (len (fn-bs-pending base)) outcome)) ks ino genesis max)) :subject fn-bs-pipe-fsync-prefix
 :witness ((bs *gcpt-written*) (base *gcpt-base*) (ks *gcpt-ks*) (tail *gcpt-tail*) (ino 0) (genesis *gcp-genesis*) (max 100) (outcome '(:eio))) :breaks ((:relation ((bs *gcpt-bad-written*) (base *gcpt-base*) (ks *gcpt-ks*) (tail *gcpt-tail*) (ino 0) (genesis *gcp-genesis*) (max 100) (outcome '(:eio)))))
 :mutations (:not-applicable "The relation removal exercises loss of the durable prefix; explicit early-ACK and prefix-cut must-fails are in gc-pipeline-durable-tests."))

(defteeth fn-lgk-pipe-ack-keeps-store-safe
 :claim (((:relation (and (fn-lgk-pipe-okp p h) (fn-lgu-safep bs (fn-lgk-pipe-ks p) ino genesis max)))) (fn-lgu-safep bs (fn-lgk-pipe-ks (fn-lgk-pipe-ack p n)) ino genesis max)) :subject fn-lgk-pipe-ack
 :witness ((bs *gcp-fenced*) (p (fn-lgk-pipe-make *gcp-kf* t)) (h '((65) (66))) (n 1) (ino 0) (genesis *gcp-genesis*) (max 100)) :breaks ((:relation ((bs *gcp-base*) (p *gcp-acked*) (h '((65) (66))) (n 1) (ino 0) (genesis *gcp-genesis*) (max 100))))
 :mutations (:not-applicable "The relation removal exercises loss of the durable prefix; explicit early-ACK and prefix-cut must-fails are in gc-pipeline-durable-tests."))

(defteeth fn-lgk-pipe-promotion-restores-relation
 :claim (((:relation (and (fn-bs-shapep bs) (true-listp (fn-bs-pending bs)) (fn-lgk-pipe-okp p h) (fn-lgk-relp bs (fn-lgk-pipe-ks p) ino genesis max) (equal (fn-lgk-phase (fn-lgk-pipe-ks p)) :appended) (fn-lgk-behind-admitsp p (fn-bs-unit bs) extent) (fn-lgk-fitsp (fn-lgk-fence (fn-lgk-pipe-ks p) (fn-bs-unit bs)) (fn-bs-unit bs) (len (fn-bs-durable-content (mv-nth 1 (fn-bs-fsync-file bs ino :ok)) ino)))))) (fn-lgk-relp (mv-nth 1 (fn-bs-pipe-fsync-prefix (mv-nth 1 (fn-lgk-pipe-physical-append bs p ino extent :ok)) ino (len (fn-bs-pending bs)) :ok)) (fn-lgk-append (fn-lgk-fence (fn-lgk-pipe-ks p) (fn-bs-unit bs)) (fn-bs-unit bs) (len (fn-bs-durable-content (mv-nth 1 (fn-bs-fsync-file bs ino :ok)) ino))) ino genesis max)) :subject fn-lgk-pipe-physical-append
 :witness ((bs *gcpt-base*) (p *gcpt-p*) (h '((90) (65) (66))) (ino 0) (extent 2560) (genesis *gcp-genesis*) (max 100)) :breaks ((:relation ((bs *gcpt-empty*) (p *gcpt-p*) (h '((90) (65) (66))) (ino 0) (extent 2560) (genesis *gcp-genesis*) (max 100))))
 :mutations (:not-applicable "The relation removal exercises loss of the durable prefix; explicit early-ACK and prefix-cut must-fails are in gc-pipeline-durable-tests."))

(defthm gcpt-crash-positive-flat
 (and (and (fn-lgk-pipe-store-linkp *gcpt-written* *gcpt-base* *gcpt-ks* *gcpt-tail* 0 *gcp-genesis* 100) (fn-bs-crash-imagep (mv-nth 1 (fn-bs-pipe-fsync-prefix *gcpt-written* 0 (len (fn-bs-pending *gcpt-base*)) :ok)) *gcpt-image*)) (and (<= (fn-lgk-acked (fn-lgk-fence *gcpt-ks* (fn-bs-unit *gcpt-base*))) (len (fn-lgk-committed (fn-lgk-recover (fn-bs-durable-content *gcpt-image* 0) *gcp-genesis* (fn-bs-unit (mv-nth 1 (fn-bs-pipe-fsync-prefix *gcpt-written* 0 (len (fn-bs-pending *gcpt-base*)) :ok))) 100 4)))) (equal (take (fn-lgk-acked (fn-lgk-fence *gcpt-ks* (fn-bs-unit *gcpt-base*))) (fn-lgk-committed (fn-lgk-recover (fn-bs-durable-content *gcpt-image* 0) *gcp-genesis* (fn-bs-unit (mv-nth 1 (fn-bs-pipe-fsync-prefix *gcpt-written* 0 (len (fn-bs-pending *gcpt-base*)) :ok))) 100 4))) (take (fn-lgk-acked (fn-lgk-fence *gcpt-ks* (fn-bs-unit *gcpt-base*))) (fn-lgk-committed (fn-lgk-fence *gcpt-ks* (fn-bs-unit *gcpt-base*)))))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-bs-crash-imagep-suff (s *gcpt-fenced*) (image *gcpt-image*) (choices nil)))
          :in-theory (disable fn-bs-crash-imagep))))
(defthm gcpt-crash-removal-flat
 (and (not (and (fn-lgk-pipe-store-linkp *gcpt-written* *gcpt-base* *gcpt-ks* *gcpt-tail* 0 *gcp-genesis* 100) (fn-bs-crash-imagep (mv-nth 1 (fn-bs-pipe-fsync-prefix *gcpt-written* 0 (len (fn-bs-pending *gcpt-base*)) :ok)) *gcpt-empty*))) (not (and (<= (fn-lgk-acked (fn-lgk-fence *gcpt-ks* (fn-bs-unit *gcpt-base*))) (len (fn-lgk-committed (fn-lgk-recover (fn-bs-durable-content *gcpt-empty* 0) *gcp-genesis* (fn-bs-unit (mv-nth 1 (fn-bs-pipe-fsync-prefix *gcpt-written* 0 (len (fn-bs-pending *gcpt-base*)) :ok))) 100 4)))) (equal (take (fn-lgk-acked (fn-lgk-fence *gcpt-ks* (fn-bs-unit *gcpt-base*))) (fn-lgk-committed (fn-lgk-recover (fn-bs-durable-content *gcpt-empty* 0) *gcp-genesis* (fn-bs-unit (mv-nth 1 (fn-bs-pipe-fsync-prefix *gcpt-written* 0 (len (fn-bs-pending *gcpt-base*)) :ok))) 100 4))) (take (fn-lgk-acked (fn-lgk-fence *gcpt-ks* (fn-bs-unit *gcpt-base*))) (fn-lgk-committed (fn-lgk-fence *gcpt-ks* (fn-bs-unit *gcpt-base*))))))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-lgk-pipe-prefix-fence-crash-recovers-acknowledged
   (bs *gcpt-written*) (base *gcpt-base*) (ks *gcpt-ks*) (tail *gcpt-tail*)
   (ino 0) (genesis *gcp-genesis*) (max 100) (image *gcpt-empty*) (next-txid 4)))
   :in-theory (disable fn-bs-crash-imagep))))
(defteeth fn-lgk-pipe-prefix-fence-crash-recovers-acknowledged
 :claim (((:relation-and-image (and (fn-lgk-pipe-store-linkp bs base ks tail ino genesis max) (fn-bs-crash-imagep (mv-nth 1 (fn-bs-pipe-fsync-prefix bs ino (len (fn-bs-pending base)) :ok)) image)))) (and (<= (fn-lgk-acked (fn-lgk-fence ks (fn-bs-unit base))) (len (fn-lgk-committed (fn-lgk-recover (fn-bs-durable-content image ino) genesis (fn-bs-unit (mv-nth 1 (fn-bs-pipe-fsync-prefix bs ino (len (fn-bs-pending base)) :ok))) max next-txid)))) (equal (take (fn-lgk-acked (fn-lgk-fence ks (fn-bs-unit base))) (fn-lgk-committed (fn-lgk-recover (fn-bs-durable-content image ino) genesis (fn-bs-unit (mv-nth 1 (fn-bs-pipe-fsync-prefix bs ino (len (fn-bs-pending base)) :ok))) max next-txid))) (take (fn-lgk-acked (fn-lgk-fence ks (fn-bs-unit base))) (fn-lgk-committed (fn-lgk-fence ks (fn-bs-unit base))))))) :subject fn-bs-pipe-fsync-prefix
 :witness ((bs *gcpt-written*) (base *gcpt-base*) (ks *gcpt-ks*) (tail *gcpt-tail*) (ino 0) (genesis *gcp-genesis*) (max 100) (image *gcpt-image*) (next-txid 4)) :witness-lemma gcpt-crash-positive-flat
 :breaks ((:relation-and-image ((bs *gcpt-written*) (base *gcpt-base*) (ks *gcpt-ks*) (tail *gcpt-tail*) (ino 0) (genesis *gcp-genesis*) (max 100) (image *gcpt-empty*) (next-txid 4)) :lemma gcpt-crash-removal-flat))
 :mutations (:not-applicable "The image removal loses an actually acknowledged record; the positive ACK is one, not zero."))

(defteeth fn-ocp-gc-host-step-commutes-with-projection
 :claim (() (equal (fn-ocp-gc-project (fn-ocp-gc-host-step x event)) (fn-ocp-gc-host-step (fn-ocp-gc-project x) event))) :subject fn-ocp-gc-host-step
 :witness ((x *gc-pipelined*) (event '(:reader))) :breaks nil
 :mutations ((:drop-reader-effect
  (:conclusion (equal (fn-ocp-gc-project (fn-ocp-gc-host-step x event))
   (update-nth 8 nil (fn-ocp-gc-host-step (fn-ocp-gc-project x) event))))
  ((x *gc-pipelined*) (event '(:reader)))
  :fault "A concrete dispatcher that drops the reader cut differs in its effects.")))
(value-triple :physical-and-projection-teeth-passed)
