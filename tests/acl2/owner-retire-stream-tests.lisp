(in-package "ACL2")
(include-book "../../books/owner-retire-stream")

; Pure composed cursor witness, not durable acceptance/native custody evidence.
(assert-event
 (let* ((feed (list nil nil (list (list "a" '(:dropped :retry-bound))
                                  (list "b" '(:dropped :operator))
                                  (list "c" :queued)) nil nil nil nil 3 1))
        (entry (list "peer" nil feed))
        (pin (list "forward-unrelated" "message" :forward nil 123))
        (cursor (fn-orr-cursor :count-pins (list entry) (list pin) (list pin)
                               0 0 456 :deadline nil nil)))
   (mv-let (next output done) (fn-orr-step cursor)
    (declare (ignore output done))
    (and (fn-feed-count-relationp feed) (fn-orr-pin-domainp pin)
        (fn-orr-invariant cursor)
        (fn-orr-invariant next)
        (o< (fn-orr-rank next) (fn-orr-rank cursor))
        (equal (fn-orr-run cursor)
               (append (fn-nls-text "retire peer=peer undelivered=3 dropped=1
obligations=1 reserved=456
obligation id=forward-unrelated kind=forward charge=123 subject=message
retired state=deadline undelivered=3 obligations=1
")
                       (fn-orf-nls-reference (fn-ord-release))))))))

(assert-event
 (let ((cursor (fn-orr-cursor :count-pins nil nil nil 0 0 0 :drained nil nil)))
   (and (fn-orr-invariant cursor)
        (equal (fn-orr-run cursor)
               (fn-nls-text "obligations=0 reserved=0
retired state=drained undelivered=0 obligations=0
")))))

; Corrupted-state hypothesis-removal tooth for the output-octet theorem:
; retained output-consp holds; omitted carried invariant fails; octet bound fails.
(assert-event
 (with-guard-checking :none
 (let* ((emitter (list :emit (list (list :nat 0)) nil 0 0 (list 999)))
        (cursor (fn-orr-cursor :emit nil nil nil 0 0 0 :drained emitter :done)))
   (mv-let (next output done) (ec-call (fn-orr-step cursor))
    (declare (ignore next done))
    (and (not (fn-orr-invariant cursor)) (consp output)
        (not (and (integerp (car output)) (<= 0 (car output)) (< (car output) 256))))))))
