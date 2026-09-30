; Authored actual Store category regressions; no source/normal/runtime credit
; until admitted in the matching modern Store/record12/held16 world.
(in-package "ACL2")
(include-book "../../books/store-events-carried")
(include-book "../../books/records-concrete")

(defconst *crst-event*
 '(:consumer 8 9 10 (:remote-register (99) (112) (99) 1 2 1 ((97) (98)) (65))))
;@mutation-witness remote-v4-is-consumer-not-authority-or-topic
(assert-event
 (and (fn-crev-eventp *crst-event*) (fn-store-event-p *crst-event*)
      (fn-wire-event-p *crst-event*)
      (eq (fn-evc-class-by-shape *crst-event*) :consumer)
      (not (eq (fn-evc-class-by-shape *crst-event*) :authority))
      (not (eq (fn-evc-class-by-shape *crst-event*) :topic))
      (equal (fn-store-event-decode-exact (fn-store-event-encode *crst-event*))
             (list :ok *crst-event*))
      (fn-rcon-wire-event-p *crst-event*)
      (equal (fn-rcon-wire-event-sequence *crst-event*) 8)
      (equal (fn-rcon-wire-event-txid *crst-event*) 9)
      (equal (fn-rcon-wire-event-generation *crst-event*) 10)))
;@mutation-witness old-generic-cp-never-silently-skips-remote-operation
(assert-event
 (let ((cp (fn-cp-initial (make-list 32 :initial-element 1)
                         (make-list 32 :initial-element 2) 8)))
  (and (equal (fn-cpe-projection-step cp *crst-event* 8)
              '(:refused :remote-consumer-interpreter-required))
       (equal (fn-ccar-cpe-projection-step cp *crst-event* 8)
              '(:refused :remote-consumer-interpreter-required)))))
