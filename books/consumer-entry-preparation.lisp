; One-cell retained consumer-entry preparation for the actual CP publisher.
; The opaque original CP/op/source binding is retained by the owner proposal.
; This cursor itself confers no publication, freshness or funding authority.
(in-package "ACL2")
(include-book "consumer-progress-carried")

; Fixed11: tag,key,remaining,remaining-meta,reversed,reversed-meta,phase,
; rebuilt,rebuilt-meta,selected-old-entry,selected-old-entry-carry.
(defun fn-cep-state (key remaining rm reversed vm phase rebuilt bm old oc)
 (declare (xargs :guard t))
 (list :consumer-entry-preparation key remaining rm reversed vm phase rebuilt bm old oc))

(defun fn-cep-operation-key (op)
 (declare (xargs :guard t))
 (if (eq (fn-cp-nth 0 op) :ack)
     (fn-cp-nth 3 (fn-cp-nth 1 op))
   (fn-cp-nth 1 op)))

(defun fn-cep-begin (cp op metadata)
 (declare (xargs :guard t))
 (if (not (fn-cpm-metadatap metadata))
     '(:refused :consumer-metadata-unavailable)
  (list :yield
   (fn-cep-state (fn-cep-operation-key op) (fn-cp-nth 5 cp) (fn-cp-nth 4 metadata)
                 nil nil :seek nil nil nil nil))))

; Exactly one inspected cell OR one prefix-rebuild cell per invocation.
; ID comparison is bounded only under the maintained <=64-octet ID domain.
; Row carries are borrowed from the established annotation, never resummarized.
(defun fn-cep-tick (cursor)
 (declare (xargs :guard t))
 (let* ((key (fn-cp-nth 1 cursor)) (remaining (fn-cp-nth 2 cursor))
        (rm (fn-cp-nth 3 cursor)) (reversed (fn-cp-nth 4 cursor))
        (vm (fn-cp-nth 5 cursor)) (phase (fn-cp-nth 6 cursor))
        (rebuilt (fn-cp-nth 7 cursor)) (bm (fn-cp-nth 8 cursor))
        (old (fn-cp-nth 9 cursor)) (oc (fn-cp-nth 10 cursor)))
  (cond
   ((eq phase :ready) (list :ready cursor))
   ((eq phase :seek)
    (if (not (consp remaining))
        (list :yield (fn-cep-state key nil nil reversed vm :reverse nil nil nil nil))
      (let ((head (car remaining)) (hc (fn-cp-nth 1 rm)) (tailm (fn-cp-nth 2 rm)))
       (if (equal key (fn-cp-nth 1 head))
           (list :yield (fn-cep-state key nil nil reversed vm :reverse
                                      (cdr remaining) tailm head hc))
         (list :yield (fn-cep-state key (cdr remaining) tailm
                                   (cons head reversed) (fn-caac-list-cons hc vm)
                                   :seek nil nil nil nil))))))
   ((eq phase :reverse)
    (if (not (consp reversed))
        (list :ready (fn-cep-state key nil nil nil nil :ready rebuilt bm old oc))
      (list :yield (fn-cep-state key nil nil (cdr reversed) (fn-cp-nth 2 vm)
                                :reverse (cons (car reversed) rebuilt)
                                (fn-caac-list-cons (fn-cp-nth 1 vm) bm) old oc))))
   (t '(:refused :consumer-preparation-phase)))))

; Bounded selectors only. READY does not authorize a mutation; the owner must
; revalidate the captured actual source and grant before a nonyielding frontier.
(defun fn-cep-ready-result (cursor)
 (declare (xargs :guard t))
 (if (eq (fn-cp-nth 6 cursor) :ready)
     (list :ready (fn-cp-nth 7 cursor) (fn-cp-nth 8 cursor)
                  (fn-cp-nth 9 cursor) (fn-cp-nth 10 cursor))
   '(:refused :consumer-preparation-incomplete)))

(in-theory (disable fn-cep-state fn-cep-operation-key fn-cep-begin
                    fn-cep-tick fn-cep-ready-result))
