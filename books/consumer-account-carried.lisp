; Actual staged authority transitions with immutable canonical-size metadata.
; The logical fn-caa-step remains the model. This producer updates the trie
; once and shares the same bounded selection/fixed reconstruction helpers.
; Funding, carried-state establishment and atomic owner publication are owed.
(in-package "ACL2")
(include-book "consumer-account-adoption")
(include-book "consumer-account-index-carry")

(defun fn-caac-atom (x)
  (declare (xargs :guard t))
  (fn-scs-atom (if (or (integerp x) (characterp x)
                       (stringp x) (symbolp x)) x nil)))

(defthm fn-caac-normalized-carryp
  (fn-scs-carryp (fn-cait-size c))
  :hints (("Goal" :in-theory (enable fn-cait-size))))

(defun fn-caac-spine (cs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp cs)
      (fn-scs-cons (fn-cait-size (car cs)) (fn-caac-spine (cdr cs)))
    (fn-scs-atom nil)))

(defthm fn-caac-spine-carryp
  (fn-scs-carryp (fn-caac-spine cs))
  :hints (("Goal" :in-theory (enable fn-caac-spine))))

(verify-guards fn-caac-spine)

; Account list metadata is (whole-carry head-carry tail-metadata), so an old
; cursor advance borrows a maintained tail instead of measuring its list.
(defun fn-caac-list-carry (metadata)
  (declare (xargs :guard t))
  (fn-cait-size (fn-cp-nth 0 metadata)))

(defun fn-caac-list-cons (head-carry tail-metadata)
  (declare (xargs :guard t))
  (list (fn-scs-cons (fn-cait-size head-carry)
                     (fn-caac-list-carry tail-metadata))
        (fn-cait-size head-carry) tail-metadata))

; These lengths are of newly selected bounded credential fields only.
; No account-table or shared trie is traversed by a size constructor.
(defun fn-caac-row-carry (row)
  (declare (xargs :guard t))
  (fn-caac-spine
   (list (fn-caac-atom :account)
         (fn-scs-octets (len (fn-cp-nth 1 row)))
         (fn-scs-octets 48) (fn-caac-atom (fn-cp-nth 3 row))
         (if (fn-cp-nth 3 row) (fn-scs-octets 145) (fn-caac-atom nil)))))

(defun fn-caac-credential-carry (op)
  (declare (xargs :guard t))
  (fn-caac-spine
   (list (fn-caac-atom :fn-auth-cred)
         (fn-scs-octets (len (fn-cp-nth 3 op))) (fn-scs-octets 32)
         (fn-caac-spine
          (list (fn-caac-atom :fn-authsec-v2) (fn-scs-octets 16)
                (fn-scs-octets 32) (fn-scs-octets 32) (fn-scs-octets 32)))
         (fn-caac-atom (equal (fn-cp-nth 10 op) 1)))))

(defun fn-caac-root-carry (root prep-metadata)
  (declare (xargs :guard t))
  (fn-caac-spine
   (list (fn-caac-atom :account-root) (fn-caac-atom (fn-cp-nth 1 root))
         (fn-cait-carry (fn-cp-nth 4 prep-metadata))
         (fn-cait-size (fn-cp-nth 5 prep-metadata)))))

; Preparation metadata6: tag, old-list, reversed-list, forward-list,
; trie-annotations, credential-list carry. It accompanies the existing prep8.
(defun fn-caac-prep-carry (prep pm)
  (declare (xargs :guard t))
  (fn-caac-spine
   (list (fn-caac-atom :account-preparation) (fn-caac-atom (fn-cp-nth 1 prep))
         (fn-caac-list-carry (fn-cp-nth 1 pm))
         (fn-caac-list-carry (fn-cp-nth 2 pm))
         (fn-caac-list-carry (fn-cp-nth 3 pm))
         (fn-caac-root-carry (fn-cp-nth 5 prep) pm)
         (fn-scs-octets 40) (fn-caac-atom (fn-cp-nth 7 prep)))))

(defun fn-caac-pending-carry (p pm)
  (declare (xargs :guard t))
  (if (null p) (fn-caac-atom nil)
    (fn-caac-spine
     (list (fn-caac-atom :adoption) (fn-scs-octets (len (fn-cp-nth 1 p)))
           (fn-caac-atom (fn-cp-nth 2 p)) (fn-caac-atom (fn-cp-nth 3 p))
           (fn-caac-atom (fn-cp-nth 4 p))
           (fn-caac-prep-carry (fn-cp-nth 5 p) pm)
           (fn-scs-octets (len (fn-cp-nth 6 p))) (fn-scs-octets 32)
           (fn-caac-atom (fn-cp-nth 8 p))))))

(defun fn-caac-authority-carry (a accounts-metadata prep-metadata)
  (declare (xargs :guard t))
  (fn-caac-spine
   (list (fn-caac-atom :authority) (fn-caac-atom (fn-cp-nth 1 a))
         (fn-caac-atom (fn-cp-nth 2 a))
         (if (fn-cp-nth 3 a) (fn-scs-octets 40) (fn-caac-atom nil))
         (fn-caac-list-carry accounts-metadata)
         (fn-caac-pending-carry (fn-cp-nth 5 a) prep-metadata))))

; Fixed4 sidecar (:account-carries CP-seven-child-carries accounts-meta prep-meta).
; The owner keeps root metadata from a fence alongside the published root4.
(defun fn-caac-metadata (s old-fields accounts-metadata prep-metadata)
  (declare (xargs :guard t))
  (let ((fields
         (list (fn-cait-size (fn-cp-nth 0 old-fields))
               (fn-cait-size (fn-cp-nth 1 old-fields))
               (fn-cait-size (fn-cp-nth 2 old-fields))
               (fn-caac-atom (fn-cp-nth 3 s))
               (fn-cait-size (fn-cp-nth 4 old-fields))
               (fn-cait-size (fn-cp-nth 5 old-fields))
               (fn-caac-authority-carry (fn-cp-nth 6 s)
                                        accounts-metadata prep-metadata))))
    (list :account-carries fields accounts-metadata prep-metadata)))

; Return actual decision + next metadata. No second fn-cai update is executed.
(defun fn-caac-stage-selected (s a event row credential old-rest old-advancedp metadata)
  (declare (xargs :guard t))
  (let* ((p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
         (root (fn-cp-nth 5 prep)) (pm (fn-cp-nth 3 metadata))
         (row-carry (fn-caac-row-carry row))
         (credential-carry
          (if credential (fn-caac-credential-carry (fn-cp-nth 4 event))
            (fn-caac-atom nil)))
         (binding-carry (fn-caac-spine
                         (list (fn-caac-atom :account-binding)
                               row-carry credential-carry))))
    (mv-let (index trie-metadata)
      (fn-cait-put-octets (fn-cp-nth 1 row) (list :account-binding row credential)
                          binding-carry (fn-cp-nth 2 root) (fn-cp-nth 4 pm))
      (let* ((one (fn-caa-stage-indexed s a event row index old-rest))
             (pm1 (list :prep-carries
                        (if old-advancedp
                            (fn-cp-nth 2 (fn-cp-nth 1 pm))
                          (fn-cp-nth 1 pm))
                        (fn-caac-list-cons row-carry (fn-cp-nth 2 pm))
                        nil trie-metadata (fn-cp-nth 5 pm)))
             (next-metadata
              (fn-caac-metadata (fn-cp-nth 1 one) (fn-cp-nth 1 metadata)
                                 (fn-cp-nth 2 metadata) pm1)))
        (mv one next-metadata)))))

(defthm fn-caac-stage-selected-is-logical-stage
  (equal (mv-nth 0 (fn-caac-stage-selected
                    s a event row credential old-rest old-advancedp metadata))
         (fn-caa-stage-selected s a event row credential old-rest))
  :hints (("Goal" :in-theory
           (e/d (fn-caac-stage-selected fn-caa-stage-selected)
                (fn-caa-stage-indexed fn-cait-put-octets fn-cai-put-octets
                 fn-caac-metadata fn-caac-row-carry fn-caac-credential-carry
                 fn-caac-spine fn-cp-nth)))))

(defun fn-caac-credential-value-carry (credential)
  (declare (xargs :guard t))
  (fn-caac-spine
   (list (fn-caac-atom :fn-auth-cred)
         (fn-scs-octets (len (fn-cp-nth 1 credential))) (fn-scs-octets 32)
         (fn-caac-spine
          (list (fn-caac-atom :fn-authsec-v2) (fn-scs-octets 16)
                (fn-scs-octets 32) (fn-scs-octets 32) (fn-scs-octets 32)))
         (fn-caac-atom (fn-cp-nth 4 credential)))))

; Given the one decision already made, carry fixed spines once. A refusal
; preserves old metadata. Only the fence exposes the completed root's carry.
(defun fn-caac-finish (one metadata accounts-metadata prep-metadata root-carry)
  (declare (xargs :guard t))
  (if (eq (fn-cp-nth 0 one) :ok)
      (mv one (fn-caac-metadata (fn-cp-nth 1 one) (fn-cp-nth 1 metadata)
                                accounts-metadata prep-metadata)
          root-carry)
    (mv one metadata nil)))

; This is the executable full authority producer, not a metadata scan after
; another producer ran. ROW/TOMBSTONE share the logical selection decision
; and invoke the carried trie update exactly once; all other logical steps
; are called once and their fixed/new-cell carries maintained here.
(defun fn-caac-step (s event metadata)
  (declare (xargs :guard t))
  (let* ((a (fn-cp-nth 6 s)) (p (fn-cp-nth 5 a))
         (prep (fn-cp-nth 5 p)) (op (fn-cp-nth 4 event))
         (kind (fn-cp-nth 0 op)) (am (fn-cp-nth 2 metadata))
         (pm (fn-cp-nth 3 metadata)))
    (cond
     ((or (null s) (not (fn-cac-eventp event))
          (not (equal (fn-cp-nth 1 event) (fn-cp-nth 3 s)))
          (not (fn-cp-uintp (fn-cp-nth 1 event)))
          (>= (nfix (fn-cp-nth 1 event)) *fn-cbor-max-uint*)
          (not (fn-cp-uintp (fn-cp-nth 2 event)))
          (not (posp (fn-cp-nth 2 event)))
          (>= (nfix (fn-cp-nth 2 event)) *fn-cbor-max-uint*))
      (mv (list :refused :authority-coordinate) metadata nil))
     ((eq kind :authority-begin)
      (fn-caac-finish (fn-caa-begin s a event op) metadata am
                      (list :prep-carries am nil nil nil (fn-caac-atom nil)) nil))
     ((not (fn-caa-matching-pendingp a op))
      (mv (list :refused :authority-base) metadata nil))
     ((or (eq kind :authority-row) (eq kind :authority-tombstone))
      (let ((plan (if (eq kind :authority-row)
                      (fn-caa-row-plan a event op)
                    (fn-caa-tombstone-plan a event op))))
        (if (eq (fn-cp-nth 0 plan) :stage)
            (mv-let (one next-metadata)
              (fn-caac-stage-selected
               s a event (fn-cp-nth 1 plan) (fn-cp-nth 2 plan)
               (fn-cp-nth 3 plan) (fn-cp-nth 4 plan) metadata)
              (mv one next-metadata nil))
          (mv plan metadata nil))))
     ((eq kind :authority-seal)
      (fn-caac-finish (fn-caa-seal s a event op) metadata am
                      (list :prep-carries nil (fn-cp-nth 2 pm) nil
                            (fn-cp-nth 4 pm) (fn-cp-nth 5 pm)) nil))
     ((eq kind :authority-prepare)
      (let* ((one (fn-caa-prepare s a event))
             (head (fn-cp-nth 0 (fn-cp-nth 3 prep)))
             (new-prep (fn-cp-nth 5 (fn-cp-nth 5
                                      (fn-cp-nth 6 (fn-cp-nth 1 one)))))
             (new-root (fn-cp-nth 5 new-prep))
             (credential (fn-cp-nth 0 (fn-cp-nth 3 new-root)))
             (credentials-carry
              (if (fn-cp-nth 3 head)
                  (fn-scs-cons (fn-caac-credential-value-carry credential)
                               (fn-cait-size (fn-cp-nth 5 pm)))
                (fn-cait-size (fn-cp-nth 5 pm))))
             (pm1 (list :prep-carries nil
                        (fn-cp-nth 2 (fn-cp-nth 2 pm))
                        (fn-caac-list-cons (fn-cp-nth 1 (fn-cp-nth 2 pm))
                                           (fn-cp-nth 3 pm))
                        (fn-cp-nth 4 pm) credentials-carry)))
        (fn-caac-finish one metadata am pm1 nil)))
     ((eq kind :authority-fence)
      (fn-caac-finish (fn-caa-fence s a event op) metadata
                      (fn-cp-nth 3 pm) nil
                      (fn-caac-root-carry (fn-cp-nth 5 prep) pm)))
     ((eq kind :authority-discard)
      (fn-caac-finish (fn-caa-success s (fn-caa-authority-pending a nil)
                                     event nil) metadata am nil nil))
     (t (mv (list :refused :authority-operation) metadata nil)))))

(defthm fn-caac-step-is-logical-authority-step
  (equal (mv-nth 0 (fn-caac-step s event metadata)) (fn-caa-step s event))
  :hints (("Goal" :in-theory
           (e/d (fn-caac-step fn-caac-finish fn-caa-step fn-caa-row
                  fn-caa-tombstone)
                (fn-caac-stage-selected fn-caa-stage-selected
                 fn-caac-metadata fn-caa-begin fn-caa-fence fn-caa-seal
                 fn-caa-prepare fn-caa-success fn-caa-authority-pending
                 fn-caa-matching-pendingp fn-caa-row-plan fn-caa-tombstone-plan
                 fn-cac-eventp fn-cp-uintp fn-cp-nth fn-caac-root-carry
                 fn-caac-list-cons fn-caac-credential-value-carry
                 fn-caac-atom fn-cait-size fn-scs-cons)))))

; Fixed-spine constructor boundary, not a scan used to establish a carry.
(defthm fn-caac-spine-keeps-canonical-size
  (implies (fn-scs-correspondsp cs xs)
           (equal (fn-caac-spine cs) (fn-scs-summary xs)))
  :hints (("Goal" :induct (fn-scs-correspondsp cs xs)
           :in-theory (e/d (fn-caac-spine fn-scs-correspondsp fn-cait-size)
                            (fn-scs-summary fn-scs-cons)))
          ("Subgoal *1/1" :use
           ((:instance fn-scs-cons-preserves-canonical-size
                       (x (car xs)) (y (cdr xs))
                       (a (car cs)) (d (fn-caac-spine (cdr cs))))))))

(defthm fn-caac-list-cons-keeps-canonical-size
  (implies (and (equal head-carry (fn-scs-summary head))
                (equal (fn-caac-list-carry tail-metadata)
                       (fn-scs-summary tail)))
           (equal (fn-caac-list-carry
                    (fn-caac-list-cons head-carry tail-metadata))
                  (fn-scs-summary (cons head tail))))
  :hints (("Goal"
           :use ((:instance fn-scs-cons-preserves-canonical-size
                            (x head) (y tail) (a head-carry)
                            (d (fn-caac-list-carry tail-metadata))))
           :in-theory
           (e/d (fn-caac-list-cons fn-caac-list-carry fn-cp-nth fn-cait-size)
                (fn-scs-summary fn-scs-cons)))))
