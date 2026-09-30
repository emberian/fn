(in-package "ACL2")
(include-book "../../books/owner-retire-stream-reference")

; Test-only exact accessor graph. This is not an installed/durably accepted owner.
(defun fn-orr-fixture-oc (feeds pins reserved)
  (declare (xargs :guard t))
  (let* ((retention (list nil reserved pins))
         (node (list nil retention))
         (store (list nil nil nil node))
         (owner (list store nil nil nil nil nil nil nil nil nil nil nil feeds)))
    (list owner)))

; Complete boundary positive witness asserts every semantic domain component.
(assert-event
 (let* ((feed (list nil nil (list (list "a" '(:dropped :retry-bound))
                                  (list "b" '(:dropped :operator))) nil nil nil nil 2 1))
        (feeds (list (list "peer" nil feed)))
        (pins (list (list "forward-unrelated" "message" :forward nil 123)))
        (oc (fn-orr-fixture-oc feeds pins 456)))
   (and (equal (fn-own-feeds (fn-ocfg-owner oc)) feeds)
        (equal (fn-retain-pins (fn-nls-retention (fn-own-store (fn-ocfg-owner oc)))) pins)
        (fn-orr-feed-domainp feeds) (fn-orr-pins-domainp pins) (natp 456)
        (fn-orr-report-domainp oc) (fn-orr-invariant (fn-orr-start :deadline oc))
        (equal (fn-orr-run (fn-orr-start :deadline oc)) (fn-oret-report :deadline oc))
        (equal (fn-orr-run (fn-orr-start :deadline oc))
               (append (fn-nls-text "retire peer=peer undelivered=2 dropped=1
obligations=1 reserved=456
obligation id=forward-unrelated kind=forward charge=123 subject=message
retired state=deadline undelivered=2 obligations=1
") (fn-orf-nls-reference (fn-ord-release)))))))

; Corrupted-state removal of count relation: pin domain/reserved natural remain.
(assert-event
 (let* ((feed (list nil nil (list (list "a" :queued)) nil nil nil nil 0 0))
        (feeds (list (list "peer" nil feed)))
        (oc (fn-orr-fixture-oc feeds nil 0)))
   (and (not (fn-orr-feed-domainp feeds)) (fn-orr-pins-domainp nil) (natp 0)
        (not (fn-orr-report-domainp oc))
        (not (equal (fn-orr-run (fn-orr-start :deadline oc)) (fn-oret-report :deadline oc))))))

; Removal of pin field domain: actual word charge differs from numeric fallback.
(assert-event
 (let* ((pins (list (list "forward-unrelated" "message" :forward nil "opaque")))
        (oc (fn-orr-fixture-oc nil pins 0)))
   (and (fn-orr-feed-domainp nil) (not (fn-orr-pins-domainp pins)) (natp 0)
        (not (fn-orr-report-domainp oc))
        (not (equal (fn-orr-run (fn-orr-start :deadline oc)) (fn-oret-report :deadline oc))))))

; Removal of natural reserved: actual word remains visible, never silently zeroed.
(assert-event
 (let ((oc (fn-orr-fixture-oc nil nil "held")))
   (and (fn-orr-feed-domainp nil) (fn-orr-pins-domainp nil) (not (natp "held"))
        (not (fn-orr-report-domainp oc))
        (not (equal (fn-orr-run (fn-orr-start :deadline oc)) (fn-oret-report :deadline oc))))))
