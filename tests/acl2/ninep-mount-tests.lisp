(in-package "ACL2")
(include-book "../../books/ninep-mount")

; Synthetic INTERNAL registered-provider fixture. No installed family,
; durable acceptance, native constructor, or deployed listener is claimed.
(defun-nx n9m-publication ()
 (fn-ipub-make 1 nil nil 0 17 3 nil 0 1 nil 0 1 nil 1 nil nil 1 0))
(defun-nx n9m-mio ()
 (let* ((token '(:index-generation 1 1 0))
        (segment (update-fn-ibp-gs-id 1 (create-fn-ibp-generation-segment)))
        (segment (update-fn-ibp-gs-active 1 segment))
        (segment (update-fn-ibp-gs-rowsi 0
                   (list :generation token (n9m-publication) 1 0 0 0 :live :internal-grant 1 0) segment))
        (node (fn-ibp-node-children-put 'fn-ibp-generation-segment segment (create-fn-ibp-node)))
        (backing (update-fn-ibp-registry node (create-fn-index-backing)))
        (backing (update-fn-ibp-pool-capacity 1 backing))
        (backing (update-fn-ibp-current (list :installed-publication token (n9m-publication)) backing)))
  (update-fn-mio$c-provider backing (create-fn-mio$c))))
(defun-nx n9m-pool ()
 (fn-owner-page-read-keep-ledger
  (fn-prl-build '(100 100 100 100 10) '(0 0 0 0 0) 0 nil '(0 0 0 0 0))
  (create-fn-page-read-pool)))
(defun-nx n9m-session ()
 (update-fn-9ps-phase :base (update-fn-9ps-msize 64 (create-fn-ninep-session))))

(defthm n9m-reserve-actual-identity-complete-positive
 (let* ((mio (n9m-mio)) (pool (n9m-pool)) (session (n9m-session))
        (result (fn-9p-mount-reserve-internal '(2 1 0 0 1) 100 session mio pool))
        (next-session (nth 3 result)) (next-pool (nth 5 result)))
  (and (fn-mio$cp mio) (fn-page-read-poolp pool) (fn-ninep-sessionp session)
       (equal (nth 0 result) :reserved) (equal (nth 1 result) '(:ninep-mount 0))
       (equal (nth 2 result) 99) (equal (nth 4 result) mio)
       (equal next-session
        (update-fn-9ps-mount-phase :reserved
         (update-fn-9ps-mount-token '(:ninep-mount 0)
          (update-fn-9ps-mount-intent
           (list :ninep-mount-intent '(:ninep-mount 0) '(:index-generation 1 1 0)
                 '(2 1 0 0 1) :reserved (n9m-publication)) session))))
       (equal next-pool
        (fn-owner-page-read-keep-ledger
          (fn-prl-build '(100 100 100 100 10) '(2 1 0 0 1) 1 nil '(0 0 0 0 0)) pool))))
 :rule-classes nil)

(defun-nx n9m-held-result ()
 (let* ((reserved (fn-9p-mount-reserve-internal '(2 1 0 0 1) 100 (n9m-session) (n9m-mio) (n9m-pool)))
        (held (fn-9p-mount-pin-step 100 (nth 3 reserved) (nth 4 reserved))))
  (list held (nth 5 reserved))))

(defthm n9m-pin-replay-once-complete-positive
 (let* ((held (car (n9m-held-result))) (session (nth 3 held)) (mio (nth 4 held))
        (row (mv-nth 1 (fn-mio-generation-read '(:index-generation 1 1 0) 100 mio))))
  (and (equal (nth 0 held) :held) (equal (nth 1 held) '(:ninep-mount 0))
       (equal (nth 2 held) 99) (equal (fn-9ps-mount-source session) (n9m-publication))
       (equal (fn-omk-at 4 row) 1)
       (equal (fn-9p-mount-pin-step 100 session mio)
              (list :held '(:ninep-mount 0) 100 session mio))))
 :rule-classes nil)

(defun-nx n9m-return-result ()
 (let* ((held (car (n9m-held-result))) (pool (cadr (n9m-held-result)))
        (session (fn-9ps-drain-begin (nth 3 held)))
        (session (mv-nth 1 (fn-9ps-quiesce-step session)))
        (session (mv-nth 1 (fn-9ps-quiesce-step session)))
        (session (mv-nth 1 (fn-9ps-quiesce-step session)))
        (session (mv-nth 1 (fn-9ps-quiesce-step session))))
  (fn-9p-mount-return-current 100 session (nth 4 held) pool)))

(defthm n9m-real-quiesce-drop-refund-replay-complete-positive
 (let* ((result (n9m-return-result)) (session (nth 2 result))
        (mio (nth 3 result)) (pool (nth 4 result))
        (ledger (fn-owner-page-read-ledger pool))
        (row (mv-nth 1 (fn-mio-generation-read '(:index-generation 1 1 0) 100 mio))))
  (and (equal (nth 0 result) :returned) (equal (nth 1 result) 99)
       (equal (fn-9ps-mount-phase session) :returned)
       (equal (fn-9ps-mount-source session) nil) (equal (fn-9ps-mount-token session) nil)
       (equal (fn-prl-nth 1 ledger) '(0 0 0 0 1)) (equal (fn-prl-nth 2 ledger) 1)
       (equal (fn-omk-at 4 row) 0)
       (equal (fn-9p-mount-return-current 100 session mio pool)
              (list :already-returned 100 session mio pool))))
 :rule-classes nil)
