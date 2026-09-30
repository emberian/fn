; Shared actual typed-C final decision. E stages are never a publication.
; The live/recovery producer supplies the SAME staged C record, captured
; configuration base and persisted begin/current cuts. No synthetic E fence.
(in-package "ACL2")
(include-book "consumer-account-config-preparation")
(include-book "consumer-account-config-marker")

; Pack the actual once-produced account4 alongside borrowed entry metadata.
(defun fn-acj-metadata5 (account4 entries)
 (declare (xargs :guard t))
 (list :account-carries (fn-cp-nth 1 account4) (fn-cp-nth 2 account4)
       (fn-cp-nth 3 account4) entries))

(defun fn-acj-stage-advance (cp metadata event encoded)
 (declare (xargs :guard t))
 (let* ((a (fn-cp-nth 6 cp)) (p (fn-cp-nth 5 a))
        (p1 (fn-caa-pending (fn-cp-nth 1 p) (fn-cp-nth 2 p)
                            (fn-cp-nth 3 p) (fn-cp-nth 4 p) (fn-cp-nth 5 p)
                            (fn-cp-nth 6 p)
                            (fn-sha256 (ec-call (binary-append (fn-cp-nth 7 p) encoded)))
                            (fn-cp-nth 8 p)))
        (next (fn-cp-state-carry (fn-cp-nth 1 cp) (fn-cp-nth 2 cp)
                                (1+ (nfix (fn-cp-nth 1 event)))
                                (fn-cp-nth 4 cp) (fn-cp-nth 5 cp)
                                (fn-caa-authority-pending a p1)))
        (am (fn-caac-metadata next (fn-cp-nth 1 metadata)
                              (fn-cp-nth 2 metadata) (fn-cp-nth 3 metadata))))
  (list :ok next (fn-acj-metadata5 am (fn-cp-nth 4 metadata)))))

; Full7 stage result is old complete six-field publication result plus the
; nonauthorizing configuration preparation. It never returns a published root.
(defun fn-acj-stage (cp metadata preparation current-config event expected base-row-carry)
 (declare (xargs :guard t))
 (let* ((op (fn-cp-nth 4 event)) (kind (fn-cp-nth 0 op))
        (a (fn-cp-nth 6 cp)) (p (fn-cp-nth 5 a)) (ap (fn-cp-nth 5 p))
        (bindingp (fn-cab-eventp event)))
  (cond
   ((not (and (or bindingp (fn-cac-eventp event))
              (fn-cp-uintp expected) (< expected *fn-cbor-max-uint*)
              (equal (fn-cp-nth 1 event) expected) (equal (fn-cp-nth 3 cp) expected)
              (fn-cp-uintp (fn-cp-nth 2 event)) (posp (fn-cp-nth 2 event))
              (< (fn-cp-nth 2 event) *fn-cbor-max-uint*)
              (fn-cbor-at-mostp metadata 5) (true-listp metadata)
              (equal (len metadata) 5) (eq (fn-cp-nth 0 metadata) :account-carries)))
    '(:refused :account-stage-coordinate))
   ((eq kind :authority-fence) '(:refused :typed-config-commit-required))
   (bindingp
    (if (not (and (fn-caa-matching-pendingp a op) (eq (fn-cp-nth 1 ap) :merge)))
        '(:refused :binding-authority-base)
     (let ((b (fn-bcp-stage preparation event)))
      (if (not (eq (fn-cp-nth 0 b) :ok)) b
       (let ((one (fn-acj-stage-advance cp metadata event (fn-cab-encode event))))
        (list :ok (fn-cp-nth 1 one) nil nil (fn-cp-nth 2 one) nil (fn-cp-nth 1 b)))))))
   ((and (eq kind :authority-prepare) (eq (fn-cp-nth 1 ap) :ready))
    (if (not (and (fn-caa-matching-pendingp a op)
                  (member-eq (fn-cp-nth 4 preparation) '(:bindings-reverse :scan :restore))))
        '(:refused :configuration-preparation-phase)
     (let ((b (fn-bcp-tick preparation base-row-carry)))
      (if (not (member-eq (fn-cp-nth 0 b) '(:ready :yield))) b
       (let ((one (fn-acj-stage-advance cp metadata event (fn-cac-encode event))))
        (list :ok (fn-cp-nth 1 one) nil nil (fn-cp-nth 2 one) nil (fn-cp-nth 1 b)))))))
   ((and (member-eq kind '(:authority-row :authority-tombstone))
         (not (eq (fn-cp-nth 4 preparation) :collect)))
    '(:refused :binding-stage-missing))
   ((and (eq kind :authority-seal) (not (eq (fn-cp-nth 4 preparation) :collect)))
    '(:refused :binding-stage-missing))
   (t
    (mv-let (one am rootcarry)
     (fn-caac-step cp event (list :account-carries (fn-cp-nth 1 metadata)
                                 (fn-cp-nth 2 metadata) (fn-cp-nth 3 metadata)))
     (declare (ignore rootcarry))
     (if (not (eq (fn-cp-nth 0 one) :ok)) one
      (let ((b (case kind
                 (:authority-begin (list :ok (fn-bcp-begin (fn-cp-nth 1 op) current-config
                                                         (fn-cp-nth 1 a))))
                 ((:authority-row :authority-tombstone)
                  (fn-bcp-expect preparation (fn-cp-nth 3 op)
                                 (if (eq kind :authority-row) :row :tombstone)))
                 (:authority-seal (fn-bcp-seal preparation))
                 (:authority-discard (list :ok nil))
                 (otherwise (list :ok preparation)))))
       (if (not (eq (fn-cp-nth 0 b) :ok)) b
        (list :ok (fn-cp-nth 1 one) nil nil
                  (fn-acj-metadata5 am (fn-cp-nth 4 metadata)) nil (fn-cp-nth 1 b))))))))))

; Full8 retains CP/root/cut/metadata/rootcarry and prepared config/accounts
; metadata from ONE decision; an owner collector must preserve all outputs.
(defun fn-acj-commit (cp metadata preparation record begin-count event-count)
 (declare (xargs :guard t))
 (let* ((a (fn-cp-nth 6 cp)) (p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
        (m (fn-cfg-record-change record))
        (base (fn-cfg-generation (fn-cp-nth 2 preparation)))
        (generation (fn-cfg-record-generation record))
        (revision (fn-cp-nth 1 a)))
  (if (not (and (fn-cacm-recordp record)
                (fn-cbor-at-mostp metadata 5) (true-listp metadata)
                (equal (len metadata) 5) (eq (fn-cp-nth 0 metadata) :account-carries)
                (fn-cp-uintp base) (< base *fn-cbor-max-uint*)
                (equal generation (1+ base))
                (equal (fn-cfg-record-sequence record) generation)
                (fn-cp-uintp (fn-cfg-record-txid record))
                (posp (fn-cfg-record-txid record))
                (< (fn-cfg-record-txid record) *fn-cbor-max-uint*)
                (fn-cp-uintp revision) (< revision *fn-cbor-max-uint*)
                (equal (fn-cp-nth 1 m) (fn-cp-nth 1 p))
                (equal (fn-cp-nth 1 m) (fn-cp-nth 1 preparation))
                (equal (fn-cp-nth 2 m) base)
                (equal (fn-cp-nth 3 m) revision)
                (equal (fn-cp-nth 3 preparation) revision)
                (equal (fn-cp-nth 2 p) revision)
                (fn-cp-uintp begin-count) (fn-cp-uintp event-count)
                (< begin-count event-count)
                (equal (fn-cp-nth 4 m) begin-count)
                (equal (fn-cp-nth 5 m) event-count)
                (equal (fn-cp-nth 3 cp) event-count)
                (equal (fn-cp-nth 6 m) (fn-cp-nth 3 p))
                (equal (fn-cp-nth 7 m) (fn-cp-nth 7 p))
                (fn-cp-nth 8 p) (eq (fn-cp-nth 1 prep) :ready)
                (eq (fn-cp-nth 4 preparation) :ready)))
      '(:refused :account-config-commit)
   (let* ((root (fn-cp-nth 5 prep))
          (next (fn-cp-state-carry (fn-cp-nth 1 cp) (fn-cp-nth 2 cp)
                                  (fn-cp-nth 3 cp) (fn-cp-nth 4 cp) (fn-cp-nth 5 cp)
                                  (list :authority (1+ revision) (fn-cp-nth 4 p)
                                        (fn-cp-nth 6 prep) (fn-cp-nth 4 prep) nil)))
          (pm (fn-cp-nth 3 metadata)) (accounts-meta (fn-cp-nth 3 pm))
          (am (fn-caac-metadata next (fn-cp-nth 1 metadata) accounts-meta nil))
          (nextmetadata (list :account-carries (fn-cp-nth 1 am)
                              accounts-meta nil (fn-cp-nth 4 metadata)))
          (configured (fn-bcp-prepared preparation generation)))
    (list :ok next root event-count nextmetadata
          (fn-caac-root-carry root pm) (fn-cp-nth 1 configured) (fn-cp-nth 2 configured))))))

; This boundary is about the actual new final decision, not an E twin.
; Whole authority/config/carry association additionally requires the maintained
; jointly produced preparation invariant; shape/ready alone never establishes it.
(defthm fn-acj-success-preserves-actual-e-frontier
 (implies (equal (fn-cp-nth 0 (fn-acj-commit cp metadata preparation record begin-count event-count)) :ok)
          (equal (fn-cp-nth 3 (fn-cp-nth 1 (fn-acj-commit cp metadata preparation record begin-count event-count)))
                 (fn-cp-nth 3 cp)))
 :hints (("Goal" :in-theory (enable fn-acj-commit fn-cp-state-carry fn-cp-nth))))

(in-theory (disable fn-acj-metadata5 fn-acj-stage-advance fn-acj-stage fn-acj-commit))
