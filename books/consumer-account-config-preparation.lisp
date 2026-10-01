; Non-authorizing prepared configuration paired with an account candidate.
; The actual joint live/cfg-first producer establishes the captured C base.
; Pending checkpoint capture is deferred and its begin replay source retained.
; Every row/tombstone requires exactly one matching durable binding stage.
(in-package "ACL2")
(include-book "consumer-account-binding-codec")
(include-book "consumer-account-input")
(include-book "config")
(include-book "identity-hex")
(include-book "consumer-account-binding-lookup")

; Fixed16, immutable base config and borrowed preparation cursors. Size
; annotations follow each changed path/list cell; no final shared-tree scan.
(defun fn-bcp-state (candidate base baseauthority phase expected rowkind
                              intents im bindings bm cursor reversed rm final fm)
 (declare (xargs :guard t))
 (list :account-config-preparation candidate base baseauthority phase expected rowkind
       intents im bindings bm cursor reversed rm final fm))

(defun fn-bcp-begin (candidate base baseauthority)
 (declare (xargs :guard t))
 (fn-bcp-state candidate base baseauthority :collect nil nil nil nil nil nil nil nil nil nil nil))

(defun fn-bcp-with (s phase expected kind intents im bindings bm cursor reversed rm final fm)
 (declare (xargs :guard t))
 (fn-bcp-state (fn-cp-nth 1 s) (fn-cp-nth 2 s) (fn-cp-nth 3 s)
               phase expected kind intents im bindings bm cursor reversed rm final fm))

(defun fn-bcp-expect (s login rowkind)
 (declare (xargs :guard t))
 (if (not (and (eq (fn-cp-nth 4 s) :collect)
               (member-eq rowkind '(:row :tombstone)) (fn-cp-idp login)))
     '(:refused :binding-row-order)
  (list :ok (fn-bcp-with s :binding login rowkind
                          (fn-cp-nth 7 s) (fn-cp-nth 8 s)
                          (fn-cp-nth 9 s) (fn-cp-nth 10 s)
                          nil nil nil nil nil))))

(defun fn-bcp-binding-row (login principal)
 (declare (xargs :guard t))
 (if (and (fn-cbor-at-mostp principal 32) (fn-cbor-octet-listp principal)
          (equal (len principal) 32))
     (fn-cfg-row-make (fn-record-octets-string login)
                     (fn-record-octets-string (fn-id-hex-octets principal)) "" 2)
   nil))

(defun fn-bcp-binding-row-carry (login)
 (declare (xargs :guard t))
 (fn-caac-spine (list (fn-caac-atom (fn-record-octets-string login))
                      (fn-caac-atom "0000000000000000000000000000000000000000000000000000000000000000")
                      (fn-caac-atom "") (fn-caac-atom 2))))

(defun fn-bcp-stage (s event)
 (declare (xargs :guard t))
 (let* ((op (fn-cp-nth 4 event)) (origin (fn-cp-nth 4 op))
        (mode (fn-cp-nth 5 op)) (principal (fn-cp-nth 6 op))
        (name (fn-cp-nth 3 op)))
  (if (not (and (fn-cab-eventp event) (eq (fn-cp-nth 4 s) :binding)
                (equal (fn-cp-nth 1 op) (fn-cp-nth 1 s))
                (equal (fn-cp-nth 2 op) (fn-cp-nth 3 s))
                (equal name (fn-cp-nth 5 s))
                (if (eq (fn-cp-nth 6 s) :tombstone) (equal origin 2)
                  (member-equal origin '(0 1)))))
      '(:refused :binding-stage)
   (mv-let (index im)
    (fn-cait-put-octets name (fn-aic-intent origin mode principal)
                        (fn-aic-intent-carry origin mode)
                        (fn-cp-nth 7 s) (fn-cp-nth 8 s))
    (list :ok
     (fn-bcp-with s :collect nil nil index im
                  (if (equal mode 2)
                      (cons (fn-bcp-binding-row name principal) (fn-cp-nth 9 s))
                    (fn-cp-nth 9 s))
                  (if (equal mode 2)
                      (fn-caac-list-cons (fn-bcp-binding-row-carry name) (fn-cp-nth 10 s))
                    (fn-cp-nth 10 s))
                  nil nil nil nil nil))))))

; Called by the actual successful account seal. A missing/reordered binding
; cannot leave :binding and therefore cannot start configuration preparation.
(defun fn-bcp-seal (s)
 (declare (xargs :guard t))
 (if (not (eq (fn-cp-nth 4 s) :collect)) '(:refused :binding-stage-missing)
  (list :ok (fn-bcp-with s :bindings-reverse nil nil
                         (fn-cp-nth 7 s) (fn-cp-nth 8 s)
                         (fn-cp-nth 9 s) (fn-cp-nth 10 s)
                         nil nil nil nil nil))))

; BASE-ROW-CARRY is supplied by the SAME carried captured configuration list
; source. Its correspondence is an actual producer obligation; no recompute.
(defun fn-bcp-tick (s base-row-carry)
 (declare (xargs :guard t))
 (let ((phase (fn-cp-nth 4 s)) (bindings (fn-cp-nth 9 s))
       (bm (fn-cp-nth 10 s)) (cursor (fn-cp-nth 11 s))
       (reversed (fn-cp-nth 12 s)) (rm (fn-cp-nth 13 s))
       (final (fn-cp-nth 14 s)) (fm (fn-cp-nth 15 s)))
  (case phase
   (:bindings-reverse
    (if (consp bindings)
        (list :yield (fn-bcp-with s phase nil nil (fn-cp-nth 7 s) (fn-cp-nth 8 s)
                                  (cdr bindings) (fn-cp-nth 2 bm) nil nil nil
                                  (cons (car bindings) final)
                                  (fn-caac-list-cons (fn-cp-nth 1 bm) fm)))
      (list :yield (fn-bcp-with s :scan nil nil (fn-cp-nth 7 s) (fn-cp-nth 8 s)
                                nil nil (fn-cfg-accounts (fn-cfg-value (fn-cp-nth 2 s)))
                                nil nil final fm))))
   (:scan
    (if (consp cursor)
        (let* ((row (car cursor))
               ; Durable CFG names remain arbitrary stored strings. A name
               ; outside the established <=64-octet authority login domain
               ; cannot match a binding intent produced by fn-cab-eventp.
               ; Keep its row literally; do not coerce/traverse its contents.
               ; Exact reference agreement additionally needs the maintained
               ; intent-key domain, not merely the trie fanout invariant.
               (name (fn-cfg-row-a row))
               (intent (and (equal (fn-cfg-row-n row) 2)
                            (fn-bcp-intent-lookup name (fn-cp-nth 7 s))))
               (dropp (member-equal (fn-cp-nth 2 intent) '(1 2))))
         (list :yield (fn-bcp-with s phase nil nil (fn-cp-nth 7 s) (fn-cp-nth 8 s)
                                   nil nil (cdr cursor)
                                   (if dropp reversed (cons row reversed))
                                   (if dropp rm (fn-caac-list-cons base-row-carry rm)) final fm)))
      (list :yield (fn-bcp-with s :restore nil nil (fn-cp-nth 7 s) (fn-cp-nth 8 s)
                                nil nil nil reversed rm final fm))))
   (:restore
    (if (consp reversed)
        (list :yield (fn-bcp-with s phase nil nil (fn-cp-nth 7 s) (fn-cp-nth 8 s)
                                  nil nil nil (cdr reversed) (fn-cp-nth 2 rm)
                                  (cons (car reversed) final)
                                  (fn-caac-list-cons (fn-cp-nth 1 rm) fm)))
      (list :ready (fn-bcp-with s :ready nil nil (fn-cp-nth 7 s) (fn-cp-nth 8 s)
                                nil nil nil nil nil final fm))))
   (:ready (list :ready s))
   (otherwise '(:refused :configuration-preparation-phase)))))

(defun fn-bcp-prepared (s generation)
 (declare (xargs :guard t))
 (if (not (eq (fn-cp-nth 4 s) :ready)) '(:refused :configuration-not-prepared)
  (let ((v (fn-cfg-value (fn-cp-nth 2 s))))
   (list :ok
    (fn-cfg-make generation
     (fn-cfg-value-make-full (fn-cfg-groups v) (fn-cfg-capacity v) (fn-cfg-quotas v)
                            (fn-cfg-policies v) (fn-cfg-listeners v) (fn-cfg-peers v)
                            (fn-cfg-limits v) (fn-cfg-authorities v) (fn-cfg-invitations v)
                            (fn-cp-nth 14 s) (fn-cfg-descriptions v)))
    (fn-cp-nth 15 s)))))

(in-theory (disable fn-bcp-state fn-bcp-begin fn-bcp-with fn-bcp-expect
                    fn-bcp-binding-row fn-bcp-binding-row-carry fn-bcp-stage
                    fn-bcp-seal fn-bcp-tick fn-bcp-prepared))
