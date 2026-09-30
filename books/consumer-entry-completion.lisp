; Final selected local consumer-event producer. The owner must bind the
; selected old/removal to its captured CP and revalidate before the frontier.
; This source component is not an issuer, durable ACK, or remote endpoint.
(in-package "ACL2")
(include-book "consumer-entry-preparation")

; Exact LEN comparison with at most N+1 spine inspections, including an
; improper final atom (LEN's logical semantics). No request length scan.
(defun fn-cec-length-is (n x)
 (declare (xargs :guard (natp n) :measure (nfix n)))
 (if (zp n) (not (consp x))
   (and (consp x) (fn-cec-length-is (1- n) (cdr x)))))

(defthm fn-cec-length-is-exact
 (implies (natp n)
          (equal (fn-cec-length-is n x) (equal (len x) n)))
 :hints (("Goal" :induct (fn-cec-length-is n x)
          :in-theory (enable fn-cec-length-is len))))

; The original cursor recognizer is only reached behind this bounded spine
; gate; its ID recognizers already check their <=64 bound before octet scans.
(defun fn-cec-scope-matchp (cp cursor old)
 (declare (xargs :guard t))
 (and (fn-cec-length-is 10 cursor)
      (fn-cp-scope-matchp cp (fn-cp-nth 4 cursor) (fn-cp-nth 6 cursor)
                          (fn-cp-nth 7 cursor) cursor old)))

; Return (:changed nextCP entry-mode) or (:inert originalCP nil).
; Remote definition validation/carry must come from the actual resumable
; parsed producer; it is unavailable here, never supplied as a host Boolean.
; OLD and REMOVED are borrowed from the same CEP decision, not looked up again.
(defun fn-cec-selected-local (cp op old removed)
 (declare (xargs :guard t))
 (let* ((kind (fn-cp-nth 0 op)) (consumer (fn-cp-nth 1 op))
        (entries (fn-cp-nth 5 cp)))
  (cond
   ((and (eq kind :register) (fn-cec-length-is 7 op) (not old)
         (equal (fn-cp-nth 6 op) (fn-cp-nth 4 cp))
         (posp (fn-cp-nth 6 op)) (fn-cp-uintp (fn-cp-nth 6 op))
         (< (fn-cp-nth 6 op) *fn-cbor-max-uint*)
         (fn-cp-idp consumer) (fn-cp-idp (fn-cp-nth 2 op))
         (fn-cp-idp (fn-cp-nth 3 op))
         (fn-cp-uintp (fn-cp-nth 4 op)) (fn-cp-uintp (fn-cp-nth 5 op)))
    (list :changed
     (fn-cp-state-carry (fn-cp-nth 1 cp) (fn-cp-nth 2 cp) (fn-cp-nth 3 cp)
      (1+ (fn-cp-nth 4 cp)) (cons (fn-cp-event-entry op) entries)
      (fn-cp-nth 6 cp)) :new))
   ((and (eq kind :rebase) (fn-cec-length-is 7 op)
         old (equal (fn-cp-nth 2 op) (fn-cp-nth 2 old))
         (equal (fn-cp-nth 6 op) (fn-cp-nth 4 cp))
         (posp (fn-cp-nth 6 op)) (fn-cp-uintp (fn-cp-nth 6 op))
         (< (fn-cp-nth 6 op) *fn-cbor-max-uint*)
         (fn-cp-idp (fn-cp-nth 3 op))
         (fn-cp-uintp (fn-cp-nth 4 op)) (fn-cp-uintp (fn-cp-nth 5 op)))
    (list :changed
     (fn-cp-state-carry (fn-cp-nth 1 cp) (fn-cp-nth 2 cp) (fn-cp-nth 3 cp)
      (1+ (fn-cp-nth 4 cp)) (cons (fn-cp-event-entry op) removed)
      (fn-cp-nth 6 cp)) :new))
   ((and (eq kind :ack) (fn-cec-length-is 2 op)
         (or (fn-cec-length-is 8 old) (fn-cec-length-is 10 old))
         (fn-cec-scope-matchp cp (fn-cp-nth 1 op) old)
         (<= (fn-cp-nth 9 (fn-cp-nth 1 op)) (nfix (fn-cp-nth 3 cp)))
         (<= (nfix (fn-cp-nth 7 old)) (fn-cp-nth 9 (fn-cp-nth 1 op))))
    (list :changed
     (fn-cp-state-carry (fn-cp-nth 1 cp) (fn-cp-nth 2 cp) (fn-cp-nth 3 cp)
      (fn-cp-nth 4 cp)
      (cons (fn-cp-entry-with-ack old (fn-cp-nth 9 (fn-cp-nth 1 op))) removed)
      (fn-cp-nth 6 cp)) :ack))
   ((and (eq kind :unregister) (fn-cec-length-is 3 op)
         old (equal (fn-cp-nth 2 op) (fn-cp-nth 6 old)))
    (list :changed
     (fn-cp-state-carry (fn-cp-nth 1 cp) (fn-cp-nth 2 cp) (fn-cp-nth 3 cp)
      (fn-cp-nth 4 cp) removed (fn-cp-nth 6 cp)) :remove))
   (t (list :inert cp nil)))))

; Fixed local8 constructor carry. The three ID lengths are bounded newly
; parsed/selected fields; numeric tail collapse is maintained by SCS-spine.
(defun fn-cec-local-entry-carry (entry)
 (declare (xargs :guard t))
 (fn-caac-spine
  (list (fn-caac-atom :entry)
        (fn-scs-octets (len (fn-cp-nth 1 entry)))
        (fn-scs-octets (len (fn-cp-nth 2 entry)))
        (fn-scs-octets (len (fn-cp-nth 3 entry)))
        (fn-caac-atom (fn-cp-nth 4 entry)) (fn-caac-atom (fn-cp-nth 5 entry))
        (fn-caac-atom (fn-cp-nth 6 entry)) (fn-caac-atom (fn-cp-nth 7 entry)))))

; Remote10's nonempty group/account children prevent octet-list collapse of
; the scalar suffix. Its original root carry and shared groups stay literal.
; This delta is NOT used for local8, whose scalar suffix may collapse.
(defun fn-cec-remote-ack-carry (old oldcarry ack)
 (declare (xargs :guard t))
 (list (+ (nfix (- (nfix (fn-cp-nth 0 oldcarry))
                   (nfix (fn-cp-nth 0 (fn-caac-atom (fn-cp-nth 7 old))))))
          (nfix (fn-cp-nth 0 (fn-caac-atom ack)))) nil nil))

; A ready cursor remains nonauthorizing. Source/metadata/quantum/retirement
; validation belongs to the actual owner before its nonyielding allocation.
; Success contains the exact once-called selected decision and fixed5 metadata.
(defun fn-cec-finish-local (cp op metadata cursor)
 (declare (xargs :guard t))
 (cond ((not (fn-cpm-metadatap metadata)) '(:refused :consumer-metadata-unavailable))
       ((not (eq (fn-cp-nth 6 cursor) :ready)) '(:refused :consumer-preparation-incomplete))
       ((not (equal (fn-cp-nth 1 cursor) (fn-cep-operation-key op)))
        '(:refused :consumer-preparation-key))
       ((member-eq (fn-cp-nth 0 op) '(:remote-register :remote-rebase))
        '(:refused :remote-definition-unavailable))
       (t
        (let* ((removed (fn-cp-nth 7 cursor)) (rm (fn-cp-nth 8 cursor))
               (old (fn-cp-nth 9 cursor)) (oc (fn-cp-nth 10 cursor))
               (one (fn-cec-selected-local cp op old removed))
               (next (fn-cp-nth 1 one)) (mode (fn-cp-nth 2 one)))
         (if (not (eq (car one) :changed)) (list :ok next metadata)
          (let* ((head (fn-cp-nth 0 (fn-cp-nth 5 next)))
                 (em (cond ((eq mode :remove) rm)
                           ((eq mode :new)
                            (fn-caac-list-cons (fn-cec-local-entry-carry head)
                              (if (eq (fn-cp-nth 0 op) :register) (fn-cp-nth 4 metadata) rm)))
                           (t (fn-caac-list-cons
                               (if (fn-cec-length-is 10 old)
                                   (fn-cec-remote-ack-carry old oc (fn-cp-nth 7 head))
                                 (fn-cec-local-entry-carry head)) rm))))
                 (fields (fn-cp-nth 1 metadata))
                 (newfields (list (fn-cp-nth 0 fields) (fn-cp-nth 1 fields)
                                  (fn-cp-nth 2 fields) (fn-cp-nth 3 fields)
                                  (fn-caac-atom (fn-cp-nth 4 next))
                                  (fn-caac-list-carry em) (fn-cp-nth 6 fields))))
           (list :ok next (list :account-carries newfields
                                (fn-cp-nth 2 metadata) (fn-cp-nth 3 metadata) em))))))))

(in-theory (disable fn-cec-length-is fn-cec-scope-matchp fn-cec-selected-local
                    fn-cec-local-entry-carry fn-cec-remote-ack-carry fn-cec-finish-local))


; Selected proposal producers preserve the exact original decision and scope.
(defun fn-cec-register-selected (s caller consumer query qver view old)
  (declare (xargs :guard t))
  (let ((old old))
    (cond ((or (not (fn-cp-idp caller)) (not (fn-cp-idp consumer))
               (not (fn-cp-idp query)) (not (fn-cp-uintp qver))
               (not (fn-cp-uintp view))) (list :refused :input))
          (old (if (and (equal caller (fn-cp-nth 2 old))
                        (equal query (fn-cp-nth 3 old))
                        (equal qver (fn-cp-nth 4 old))
                        (equal view (fn-cp-nth 5 old)))
                   (list :no-op (fn-cp-scope-cursor s old))
                 (list :refused :rebase-required)))
          ((or (not (posp (fn-cp-nth 4 s)))
               (not (fn-cp-uintp (fn-cp-nth 4 s)))
               (equal (fn-cp-nth 4 s) *fn-cbor-max-uint*))
           (list :refused :epoch-exhausted))
          (t (list :write (list :register consumer caller query qver view
                                (fn-cp-nth 4 s)))))))


(defun fn-cec-ack-selected (s caller qver view cursor entry)
  (declare (xargs :guard t))
  (let ((entry entry))
    (cond ((or (not (fn-cec-length-is 10 cursor))
               (not (fn-cp-scope-matchp s caller qver view cursor entry)))
           (list :refused :scope))
          ((> (fn-cp-nth 9 cursor) (nfix (fn-cp-nth 3 s)))
           (list :refused :future))
          ((< (fn-cp-nth 9 cursor) (nfix (fn-cp-nth 7 entry)))
           (list :refused :backwards))
          ((equal (fn-cp-nth 9 cursor) (fn-cp-nth 7 entry))
           (list :no-op (fn-cp-scope-cursor s entry)))
          (t (list :write (list :ack cursor))))))


(defun fn-cec-rebase-selected (s caller consumer query qver view entry)
  (declare (xargs :guard t))
  (let ((entry entry))
    (cond ((or (not (fn-cp-idp caller)) (not (fn-cp-idp query))
               (not (fn-cp-uintp qver)) (not (fn-cp-uintp view)))
           (list :refused :input))
          ((or (not entry) (not (equal caller (fn-cp-nth 2 entry))))
           (list :refused :scope))
          ((and (equal query (fn-cp-nth 3 entry))
                (equal qver (fn-cp-nth 4 entry))
                (equal view (fn-cp-nth 5 entry)))
           (list :no-op (fn-cp-scope-cursor s entry)))
          ((or (not (posp (fn-cp-nth 4 s)))
               (not (fn-cp-uintp (fn-cp-nth 4 s)))
               (equal (fn-cp-nth 4 s) *fn-cbor-max-uint*))
           (list :refused :epoch-exhausted))
          (t (list :write (list :rebase consumer caller query qver view
                                (fn-cp-nth 4 s)))))))


(defun fn-cec-unregister-selected (s caller consumer entry)
  (declare (ignore s) (xargs :guard t))
  (let ((entry entry))
    (if (and entry (equal caller (fn-cp-nth 2 entry)))
        (list :write (list :unregister consumer (fn-cp-nth 6 entry)))
      (list :refused :scope))))

(defun fn-cec-proposal-local (cp op old)
 (declare (xargs :guard t))
 (case (fn-cp-nth 0 op)
  (:register (fn-cec-register-selected cp (fn-cp-nth 2 op) (fn-cp-nth 1 op)
              (fn-cp-nth 3 op) (fn-cp-nth 4 op) (fn-cp-nth 5 op) old))
  (:rebase (fn-cec-rebase-selected cp (fn-cp-nth 2 op) (fn-cp-nth 1 op)
            (fn-cp-nth 3 op) (fn-cp-nth 4 op) (fn-cp-nth 5 op) old))
  (:ack (let ((cursor (fn-cp-nth 1 op)))
          (fn-cec-ack-selected cp (fn-cp-nth 4 cursor) (fn-cp-nth 6 cursor)
                                  (fn-cp-nth 7 cursor) cursor old)))
  (:unregister (fn-cec-unregister-selected cp (fn-cp-nth 2 old) (fn-cp-nth 1 op) old))
  (otherwise '(:refused :operation))))

; This exact local preflight is consumed as a saved publication result. It
; performs no table lookup/removal and never declares a proposed row durable.
(defun fn-cec-local-preflight (cp op metadata cursor)
 (declare (xargs :guard t))
 (let ((proposal (fn-cec-proposal-local cp op (fn-cp-nth 9 cursor))))
  (if (equal proposal (list :write op))
      (fn-cec-finish-local cp op metadata cursor)
    (list :refused :operation))))

(in-theory (disable fn-cec-register-selected fn-cec-ack-selected
                    fn-cec-rebase-selected fn-cec-unregister-selected
                    fn-cec-proposal-local fn-cec-local-preflight))
