; The actual owner poll selects the same answer as the historical list suffix.
; The list formulation is proof-only and is not called on a served path.
(in-package "ACL2")
(include-book "consumer-owner-local")
(include-book "consumer-event-index-store-invariants")

(defun fn-col-poll-list-reference (o consumer)
  (let* ((store (fn-own-store o))
         (s (fn-sn-consumer store))
         (scoped (fn-col-scope-entry s consumer)))
    (if (not (eq (car scoped) :scope))
        scoped
      (let* ((entry (fn-cp-nth 1 scoped))
             (position (fn-cp-nth 7 entry))
             (frontier (fn-cp-nth 3 s))
             (scan (fn-col-poll-scan
                    (fn-col-poll-list-window
                     (fn-sf-records (fn-sn-files store))
                     position frontier *fn-col-poll-max-scan*)
                    (fn-cp-nth 3 entry) position frontier
                    *fn-col-poll-max-scan*)))
        (if (not (eq (car scan) :scan)) scan
          (let ((cursor (update-nth 9 (fn-cp-nth 1 scan)
                                    (fn-cp-scope-cursor s entry))))
            (list :poll (fn-cp-cursor-encode cursor)
                  (fn-cp-nth 2 scan))))))))

(defthm fn-col-poll-agrees-with-committed-list-under-index-relation
  (let* ((store (fn-own-store o))
         (records (fn-sf-records (fn-sn-files store)))
         (consumer-state (fn-sn-consumer store)))
    (implies (and (fn-ceis-relatedp store)
                  (not (member-eq (fn-sf-phase (fn-sn-files store))
                                  '(:replaying :fault)))
                  (true-listp records)
                  (<= (len records) (1+ *fn-cbor-max-uint*))
                  (natp (fn-cp-nth 3 consumer-state))
                  (<= (fn-cp-nth 3 consumer-state) (len records)))
             (equal (fn-col-poll o consumer)
                    (fn-col-poll-list-reference o consumer))))
  :hints (("Goal"
           :use ((:instance fn-col-poll-index-window-is-committed-prefix
                            (index (fn-sn-event-index (fn-own-store o)))
                            (events (fn-sf-records
                                     (fn-sn-files (fn-own-store o))))
                            (position (fn-cp-nth 7
                                       (fn-cp-nth 1
                                        (fn-col-scope-entry
                                         (fn-sn-consumer (fn-own-store o))
                                         consumer))))
                            (frontier (fn-cp-nth 3
                                       (fn-sn-consumer (fn-own-store o))))
                            (budget *fn-col-poll-max-scan*)))
           :in-theory (e/d (fn-col-poll fn-col-poll-list-reference
                            fn-ceis-relatedp)
                           (fn-col-poll-index-window-is-committed-prefix
                            fn-col-poll-index-window fn-col-poll-list-window
                            fn-col-poll-scan fn-cp-cursor-encode
                            fn-cei-correspondencep fn-cei-build)))))
