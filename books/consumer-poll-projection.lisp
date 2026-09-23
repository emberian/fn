; Bounded read-only projection of the exact E2 poll pair.  This function
; checks the composite's own bindings; only an authenticated local `consumer
; poll' response establishes that these octets came from this Store.
(in-package "ACL2")
(include-book "replay")
(include-book "consumer-position")

(defun fn-cpj-project (cursor-octets event-octets)
  ; consumer-position's public cursor decoder is admitted but its guard is
  ; not yet verified, so this joined projection makes no guard claim either.
  (declare (xargs :guard t :verify-guards nil))
  (if (or (not (fn-cp-at-mostp cursor-octets 346))
          (not (fn-cp-at-mostp event-octets *fn-stxa-max-octets*)))
      (list :refused :limit)
    (let* ((cursor-result (fn-cp-cursor-decode cursor-octets))
           (event-result (fn-stxa-decode-exact event-octets)))
      (if (or (not (eq (car cursor-result) :ok))
              (not (fn-stmt-okp event-result)))
          (list :refused :codec)
        (let* ((cursor (cadr cursor-result))
               (event (fn-stmt-value event-result))
               (record-result
                (fn-record-decode-exact (fn-stxa-article-record event)))
               (verdict-result
                (fn-stxe-decode-exact (fn-stxa-verdict-event event))))
          (if (or (not (equal (fn-stxa-schema event)
                              *fn-stxa-carried-version*))
                  (not (fn-stxa-bindsp event))
                  (not (fn-record-result-okp record-result))
                  (not (fn-stmt-okp verdict-result))
                  (not (equal (nth 9 cursor)
                              (1+ (fn-stxa-sequence event)))))
              (list :refused :binding)
            (let* ((record (fn-record-result-record record-result))
                   (received (fn-record-payload record))
                   (source (fn-stxa-authored-source event))
                   (source-id (fn-stxa-authored-id event))
                   (verdict (fn-stmt-value verdict-result)))
              (if (or (not (equal source-id
                                  (fn-hsig-authored-source-id source)))
                      (not (fn-hsig-carried-record-metadatap
                            source received record))
                      (not (eq (fn-stxe-token verdict) :verified)))
                  (list :refused :authored-binding)
                (list :ok
                      (list (nth 1 cursor) (nth 2 cursor)
                            (nth 3 cursor) (nth 4 cursor) (nth 5 cursor)
                            (nth 6 cursor) (nth 7 cursor)
                            (nth 8 cursor) (nth 9 cursor))
                      (fn-stxa-sequence event) (fn-stxa-txid event)
                      source-id (fn-record-string-octets
                                 (fn-record-msgid record))
                      source received (fn-stxe-detail verdict)
                      (fn-stxa-verdict-event event))))))))))

(in-theory (disable (:d fn-cpj-project)))
