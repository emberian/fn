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
