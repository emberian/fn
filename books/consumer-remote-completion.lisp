; Selected remote registration decisions and canonical carries. The actual
; owner retains/revalidates CP, config, definition and CEP source custody;
; neither this cursor nor an equal semantic key supplies an allocation grant.
(in-package "ACL2")
(include-book "consumer-remote-scope")
(include-book "consumer-entry-completion")

; Fixed12: tag,key,ingress,CP,CEP,definition,newTail,oldTail,phase,same,
; visited-consumer-count,profile-max-consumers. All children remain literal.
(defun fn-crd-state (key ingress cp cep definition new old phase same count max)
 (declare (xargs :guard t))
 (list :remote-decision key ingress cp cep definition new old phase same count max))

(defun fn-crd-begin (key ingress cp cep definition max configured-generation)
 (declare (xargs :guard t))
 (let ((old (fn-cp-nth 9 cep)))
  (cond ((not (eq (fn-cp-nth 0 ingress) :authenticated)) '(:refused :authentication))
        ((or (not (eq (fn-cp-nth 6 cep) :ready))
              (not (equal (fn-cp-nth 1 cep) (fn-cp-nth 4 (fn-cp-nth 1 ingress)))))
         '(:refused :consumer-preparation-incomplete))
        ((not (eq (fn-cp-nth 3 definition) :ready)) '(:refused :scope-incomplete))
        ((not (equal (fn-cp-nth 1 definition) (fn-crs-key ingress configured-generation)))
         '(:refused :scope-changed))
        ((not (eq (fn-cp-nth 0 (fn-cre-selected-route ingress old)) :definition-request))
         '(:refused :scope))
        (t (list :yield (fn-crd-state key ingress cp cep definition
                         (fn-cp-nth 15 definition)
                         (if old (fn-cp-nth 8 old) (fn-cp-nth 5 cp))
                         (if old :compare :capacity) (and old t) 0 max))))))

; Compare one bounded stored/query name, or count one borrowed CP table cell.
; Counting is a funded resumable current-source producer, not a trusted host
; count or a whole-list LEN in the final registration decision.
(defun fn-crd-tick (s current-key)
 (declare (xargs :guard t))
 (let ((key (fn-cp-nth 1 s)) (ingress (fn-cp-nth 2 s)) (cp (fn-cp-nth 3 s))
       (cep (fn-cp-nth 4 s)) (definition (fn-cp-nth 5 s))
       (new (fn-cp-nth 6 s)) (old (fn-cp-nth 7 s)) (phase (fn-cp-nth 8 s))
       (same (fn-cp-nth 9 s)) (count (nfix (fn-cp-nth 10 s))) (max (nfix (fn-cp-nth 11 s))))
  (cond ((not (equal key current-key)) '(:refused :consumer-source-changed))
        ((eq phase :ready) (list :ready s))
        ((eq phase :compare)
         (if (and (consp new) (consp old) (equal (car new) (car old)))
             (list :yield (fn-crd-state key ingress cp cep definition (cdr new) (cdr old)
                                         :compare same count max))
           (list :ready (fn-crd-state key ingress cp cep definition nil nil :ready
                                      (and (null new) (null old) same) count max))))
        ((eq phase :capacity)
         (cond ((<= max count) '(:refused :max-consumers))
               ((not (consp old))
                (list :ready (fn-crd-state key ingress cp cep definition nil nil :ready nil count max)))
               (t (list :yield (fn-crd-state key ingress cp cep definition new (cdr old)
                                             :capacity nil (1+ count) max)))))
        (t '(:refused :consumer-decision-phase)))))

; Query ID is the opaque consumer ID. Query version is derived only from the
; maintained server CP next-registration epoch. An idempotent register retains
; the old query version after exact bounded definition/account comparison.
(defun fn-crd-proposal (s current-key)
 (declare (xargs :guard t))
 (let* ((cp (fn-cp-nth 3 s)) (ingress (fn-cp-nth 2 s))
        (request (fn-cp-nth 1 ingress)) (op (fn-cp-nth 1 request))
        (consumer (fn-cp-nth 4 request)) (principal (fn-cp-nth 2 ingress))
        (view (fn-cp-nth 5 ingress)) (creation (fn-cp-nth 3 ingress))
        (old (fn-cp-nth 9 (fn-cp-nth 4 s)))
        (same (fn-cp-nth 9 s)) (epoch (fn-cp-nth 4 cp)))
  (cond ((not (equal (fn-cp-nth 1 s) current-key)) '(:refused :consumer-source-changed))
        ((not (eq (fn-cp-nth 8 s) :ready)) '(:refused :consumer-decision-incomplete))
        ((not (member-eq op '(:register :rebase))) '(:refused :operation))
        ((and old same (equal (fn-cp-nth 5 old) view))
         (list :no-op (fn-cp-scope-cursor cp old)))
        ((and old (eq op :register)) '(:refused :rebase-required))
        ((and (eq op :rebase) (not old)) '(:refused :scope))
        ((or (not (posp epoch)) (not (fn-cp-uintp epoch))
              (equal epoch *fn-cbor-max-uint*)) '(:refused :epoch-exhausted))
        (t (list :write
           (list (if (eq op :register) :remote-register :remote-rebase)
                 consumer principal consumer epoch view epoch
                 (fn-cp-nth 15 (fn-cp-nth 5 s)) creation))))))

; The exact remote10 head's bounded fields and group carry are constructed
; without a query or account-tree summary walk. GROUPMETA is the produced
; literal annotation, established and preserved in the definition cursor.
(defun fn-crd-entry-carry (entry groupmeta)
 (declare (xargs :guard t))
 (fn-caac-spine
  (list (fn-caac-atom :entry)
        (fn-scs-octets (len (fn-cp-nth 1 entry)))
        (fn-scs-octets (len (fn-cp-nth 2 entry)))
        (fn-scs-octets (len (fn-cp-nth 3 entry)))
        (fn-caac-atom (fn-cp-nth 4 entry)) (fn-caac-atom (fn-cp-nth 5 entry))
        (fn-caac-atom (fn-cp-nth 6 entry)) (fn-caac-atom 0)
        (fn-caac-list-carry groupmeta) (fn-scs-octets (len (fn-cp-nth 9 entry))))))

; One saved proposal and one saved selected removal feed this completion.
; Metadata5 is retained from the same source; the operation is not decided
; twice and no fn-cp-find/remove/metadatap group recognizer runs here.
(defun fn-crd-finish (s current-key metadata)
 (declare (xargs :guard t))
 (let* ((proposal (fn-crd-proposal s current-key)) (cp (fn-cp-nth 3 s))
        (cep (fn-cp-nth 4 s)) (definition (fn-cp-nth 5 s)))
  (if (not (fn-cpm-metadatap metadata)) '(:refused :consumer-metadata-unavailable)
   (if (not (eq (fn-cp-nth 0 proposal) :write)) proposal
    (let* ((op (fn-cp-nth 1 proposal)) (entry (fn-cp-event-entry op))
           (registerp (eq (fn-cp-nth 0 op) :remote-register))
           (tail (if registerp (fn-cp-nth 5 cp) (fn-cp-nth 7 cep)))
           (tailmeta (if registerp (fn-cp-nth 4 metadata) (fn-cp-nth 8 cep)))
           (entrymeta (fn-caac-list-cons (fn-crd-entry-carry entry (fn-cp-nth 16 definition)) tailmeta))
           (next (fn-cp-state-carry (fn-cp-nth 1 cp) (fn-cp-nth 2 cp) (fn-cp-nth 3 cp)
                          (1+ (nfix (fn-cp-nth 4 cp))) (cons entry tail) (fn-cp-nth 6 cp)))
           (fields (fn-cp-nth 1 metadata))
           (nextfields (list (fn-cp-nth 0 fields) (fn-cp-nth 1 fields) (fn-cp-nth 2 fields)
                            (fn-cp-nth 3 fields) (fn-caac-atom (fn-cp-nth 4 next))
                            (fn-caac-list-carry entrymeta) (fn-cp-nth 6 fields))))
     (list :prepared proposal next
           (list :account-carries nextfields (fn-cp-nth 2 metadata) (fn-cp-nth 3 metadata) entrymeta)
           (fn-cp-nth 16 definition) (fn-cp-nth 12 definition)
           (fn-cp-nth 17 definition)))))))

(in-theory (disable fn-crd-state fn-crd-begin fn-crd-tick fn-crd-proposal fn-crd-entry-carry fn-crd-finish))
