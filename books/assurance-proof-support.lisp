(in-package "ACL2")

; ACL2 8.7 event-support projection, NOT an exact rune/dependency certificate.
; install-proof-supporters collapses rune identities to event names.  Missing
; entries conflate empty support with support discarded by INCLUDE-BOOK.
(defun fn2-proof-support-entries (name entries)
  (if (endp entries)
      nil
    (let ((key (caar entries)))
      (if (or (equal key name)
              (and (consp key) (member-eq name key)))
          (cons (car entries)
                (fn2-proof-support-entries name (cdr entries)))
        (fn2-proof-support-entries name (cdr entries))))))

(defun fn2-proof-support-names (entries)
  (if (endp entries)
      nil
    (union-eq (cdar entries) (fn2-proof-support-names (cdr entries)))))

; An origin token alone is advisory ACL2 metadata.  Bind it to BOTH the live
; theorem name and its exact translated formula before reporting this edge.
(defun fn2-proof-constraint-match (name formula terms origins)
  (if (or (endp terms) (endp origins))
      nil
    (or (and (equal formula (car terms))
             (equal (car origins) (list 'theorem name)))
        (fn2-proof-constraint-match name formula (cdr terms) (cdr origins)))))

(defun fn2-proof-assumption-contexts (name formula subjects world)
  (if (endp subjects)
      nil
    (let* ((subject (car subjects))
           (present (getpropc subject 'constraint-lst-etc nil world)))
      (cons
       (if (not present)
           (list :subject subject :status :no-live-encapsulate-constraint)
         (mv-let (representative terms origins) (constraint-info subject world)
           (list :subject subject :representative representative
                 :constraints terms :origins origins
                 :status (cond ((unknown-constraints-p terms) :unknown-constraints)
                               ((not (equal (len terms) (len origins)))
                                :unsupported-origins)
                               ((and formula
                                     (fn2-proof-constraint-match
                                      name formula terms origins))
                                :exact-live-constraint-theorem)
                               (t :not-this-constraint-theorem)))))
       (fn2-proof-assumption-contexts name formula (cdr subjects) world)))))

(defun fn2-proof-support-node (name subjects world)
  (let* ((formula (getpropc name 'theorem nil world))
         (body (getpropc name 'unnormalized-body nil world))
         (entries (fn2-proof-support-entries
                   name (global-val 'proof-supporters-alist world))))
    (list :name name :theorem formula :definition body
          :event-kind (cond (formula :theorem) (body :definition)
                            (t :unsupported-event))
          :support-state (if entries :recorded-event-support
                           :absent-or-empty-unknown)
          :support-entries entries
          :supporters (fn2-proof-support-names entries)
          :constraint-contexts
          (fn2-proof-assumption-contexts name formula subjects world))))

(defun fn2-proof-support-walk (todo seen fuel subjects world)
  (declare (xargs :measure (nfix fuel)))
  (cond ((endp todo) nil)
        ((zp fuel) (list (list :status :fuel-exhausted :pending todo)))
        ((member-eq (car todo) seen)
         (fn2-proof-support-walk (cdr todo) seen (1- fuel) subjects world))
        (t (let* ((node (fn2-proof-support-node (car todo) subjects world))
                  (next (cadr (assoc-keyword :supporters node))))
             (cons node
                   (fn2-proof-support-walk
                    (append next (cdr todo)) (cons (car todo) seen)
                    (1- fuel) subjects world))))))

(defun fn2-proof-support-report (roots subjects fuel world)
  (list :kind :live-event-proof-support-projection
        :roots roots :named-assumption-subjects subjects
        :complete nil
        :limitations '(:rune-identities-collapsed
                       :absent-support-is-unknown
                       :included-proof-support-not-recoverable
                       :constraint-origins-are-not-proof-certificates
                       :attachments-and-raw-runtime-unchecked)
        :nodes (fn2-proof-support-walk roots nil fuel subjects world)))

; Capture this DURING source admission, before final INCLUDE-BOOK discards
; proof-support entries.  The snapshot is diagnostic evidence, not a cert.
(defun fn2-proof-support-export (path roots subjects fuel state)
  (declare (xargs :stobjs state :verify-guards nil))
  (mv-let (channel state) (open-output-channel path :character state)
    (if (not channel)
        (prog2$ (er hard 'fn2-proof-support-export "Cannot write ~x0." path) state)
      (let ((state (prin1$ (fn2-proof-support-report roots subjects fuel (w state))
                           channel state)))
        (close-output-channel channel state)))))
