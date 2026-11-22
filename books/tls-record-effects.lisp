; Result facts for callers of the TLS record controller.
(in-package "ACL2")
(include-book "tls-stack")
(fn2-book-layer :d)

(defthm fn2-tls-record-start-ok-shape
 (implies (and (fn2-tls-recordp fn2-tls-record)
               (fn2-tls-record-wfp fn2-tls-record)
               (equal (mv-nth 0 (fn2-tls-record-start cap nonce op gen extent parent-serial writep fn2-tls-record)) :ok))
  (let ((next (mv-nth 1 (fn2-tls-record-start cap nonce op gen extent parent-serial writep fn2-tls-record))))
   (and (fn2-tls-recordp next)
        (fn2-tls-record-wfp next)
        (equal (fn2-tls-record-rows next) 1))))
 :hints (("Goal" :in-theory
  (set-difference-theories (current-theory :here)
   (union-theories '(fn2-tls-record-bind fn2-tls-record-bind-child)
                   (theory 'fn2-tls-record-readers))))))

(local
 (defthm fn2-tls-record-plan-offset-is-natural
  (natp (mv-nth 2 (fn2-tls-record-plan writep extent sp rp status seen progress copied fed il io ol oo room pending quantum)))
  :rule-classes :type-prescription
  :hints (("Goal" :use fn2-tls-record-plan-widths
           :in-theory (disable fn2-tls-record-plan fn2-tls-record-plan-widths)))))

(defthm fn2-tls-record-next-offset-is-natural
 (natp (mv-nth 2 (fn2-tls-record-next room pending fn2-tls-transport fn2-tls-record)))
 :rule-classes :type-prescription
 :hints (("Goal" :in-theory
  (set-difference-theories (current-theory :here)
   (union-theories '(fn2-tls-record-plan fn2-tls-record-finish fn2-tls-transport-select
                     fn2-tls-record-requestable-p fn2-tls-record-request)
    (union-theories (theory 'fn2-tls-record-readers) (theory 'fn2-tls-transport-readers)))))))

(local
 (defthm fn2-tls-record-request-preserves-row-count
  (implies (and (fn2-tls-recordp fn2-tls-record) (fn2-tls-record-wfp fn2-tls-record)
                (equal (fn2-tls-record-rows fn2-tls-record) 1))
   (equal (fn2-tls-record-rows (mv-nth 1 (fn2-tls-record-request serial action source-count sink-count fn2-tls-record))) 1))
  :hints (("Goal" :in-theory
   (set-difference-theories (current-theory :here)
    (union-theories '(fn2-tls-record-requestable-p) (theory 'fn2-tls-record-readers)))))))

(defthm fn2-tls-record-next-action-shape
 (implies (and (fn2-tls-transportp fn2-tls-transport) (fn2-tls-transport-wfp fn2-tls-transport)
               (equal (fn2-tls-transport-rows fn2-tls-transport) 1)
               (fn2-tls-recordp fn2-tls-record) (fn2-tls-record-wfp fn2-tls-record)
               (equal (fn2-tls-record-rows fn2-tls-record) 1)
               (equal (mv-nth 0 (fn2-tls-record-next room pending fn2-tls-transport fn2-tls-record)) :act))
  (let ((transport (mv-nth 5 (fn2-tls-record-next room pending fn2-tls-transport fn2-tls-record)))
        (record (mv-nth 6 (fn2-tls-record-next room pending fn2-tls-transport fn2-tls-record))))
   (and (fn2-tls-transportp transport) (fn2-tls-transport-wfp transport)
        (equal (fn2-tls-transport-rows transport) 1)
        (fn2-tls-recordp record) (fn2-tls-record-wfp record)
        (equal (fn2-tls-record-rows record) 1))))
 :hints (("Goal" :in-theory
  (set-difference-theories (current-theory :here)
   (union-theories '(fn2-tls-record-plan fn2-tls-record-finish fn2-tls-transport-select
                     fn2-tls-record-requestable-p fn2-tls-record-request)
    (union-theories (theory 'fn2-tls-record-readers) (theory 'fn2-tls-transport-readers)))))))

(defthm fn2-compress-tls-parent-channel
 (implies (equal (mv-nth 0 (fn2-compress-tls-parent cap nonce slot generation fn2-compress-transport)) :ok)
  (or (equal (mv-nth 1 (fn2-compress-tls-parent cap nonce slot generation fn2-compress-transport)) 2)
      (equal (mv-nth 1 (fn2-compress-tls-parent cap nonce slot generation fn2-compress-transport)) 3)))
 :rule-classes :forward-chaining
 :hints (("Goal" :in-theory (disable fn2-compress-transport-match-p
   fn2-compress-transport-rows
   fn2-compress-transport-serial fn2-compress-transport-pending fn2-compress-transport-alive
   fn2-compress-transport-terminal fn2-compress-transport-request-in-channel
   fn2-compress-transport-request-out-channel fn2-compress-transport-request-in-offset
   fn2-compress-transport-request-out-offset fn2-compress-transport-request-in-count
   fn2-compress-transport-request-out-count fn2-compress-transport-request-in-extent
   fn2-compress-transport-request-out-extent fn2-compress-transport-output-offset
   fn2-compress-transport-output-length fn2-compress-transport-output-quantum
   fn2-compress-transport-input-offset fn2-compress-transport-input-length
   fn2-compress-transport-input-quantum))))
