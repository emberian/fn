; Cleanup capacity remains available after all admitted handshake work is spent.
(in-package "ACL2")
(include-book "tls-transport")
(fn2-book-layer :d)
(local (in-theory
 (set-difference-theories (current-theory :here) (theory 'fn2-tls-transport-abstraction))))
(defun fn2-tls-transport-reservation (fn2-tls-transport)
 (declare (xargs :stobjs fn2-tls-transport
  :guard (and (fn2-tls-transport-wfp fn2-tls-transport) (= (fn2-tls-transport-rows fn2-tls-transport) 1))))
 (<= (+ (fn2-tls-transport-serial 0 fn2-tls-transport)
        (fn2-tls-transport-budget 0 fn2-tls-transport)
        (fn2-tls-transport-cleanup-credit 0 fn2-tls-transport)) #x100000000))
(defthm fn2-tls-transport-start-establishes-reservation
 (implies (and (fn2-tls-transportp fn2-tls-transport)
               (equal (mv-nth 0 (fn2-tls-transport-start cap nonce slot generation total capacity quantum budget window fn2-tls-transport)) :ok))
  (fn2-tls-transport-reservation
   (mv-nth 1 (fn2-tls-transport-start cap nonce slot generation total capacity quantum budget window fn2-tls-transport))))
 :hints (("Goal" :in-theory (e/d (fn2-tls-transport-reservation fn2-tls-transport-serial fn2-tls-transport-budget fn2-tls-transport-cleanup-credit) (nth update-nth fn2-tls-transport-init)))))

(defthm fn2-tls-transport-next-preserves-reservation
 (implies (and (fn2-tls-transportp fn2-tls-transport)
               (fn2-tls-transport-wfp fn2-tls-transport)
               (= (fn2-tls-transport-rows fn2-tls-transport) 1)
               (fn2-tls-transport-reservation fn2-tls-transport))
  (fn2-tls-transport-reservation (mv-nth 5 (fn2-tls-transport-next room pending fn2-tls-transport))))
 :hints (("Goal" :in-theory (e/d (fn2-tls-transport-reservation fn2-tls-transport-serial fn2-tls-transport-budget fn2-tls-transport-cleanup-credit fn2-tls-transport-rows) (nth update-nth)))))

(defthm fn2-tls-transport-observe-preserves-reservation
 (implies (and (fn2-tls-transportp fn2-tls-transport)
               (fn2-tls-transport-wfp fn2-tls-transport)
               (= (fn2-tls-transport-rows fn2-tls-transport) 1)
               (fn2-tls-transport-reservation fn2-tls-transport))
  (fn2-tls-transport-reservation (mv-nth 2 (fn2-tls-transport-observe cap nonce slot generation serial code count errno fn2-tls-transport))))
 :hints (("Goal" :in-theory (e/d (fn2-tls-transport-reservation fn2-tls-transport-serial fn2-tls-transport-budget fn2-tls-transport-cleanup-credit fn2-tls-transport-rows) (nth update-nth)))))

(defthm fn2-tls-transport-retire-preserves-reservation
 (implies (and (fn2-tls-transportp fn2-tls-transport)
               (fn2-tls-transport-wfp fn2-tls-transport)
               (= (fn2-tls-transport-rows fn2-tls-transport) 1)
               (fn2-tls-transport-reservation fn2-tls-transport))
  (fn2-tls-transport-reservation (mv-nth 1 (fn2-tls-transport-retire cap nonce fn2-tls-transport))))
 :hints (("Goal" :in-theory (e/d (fn2-tls-transport-reservation fn2-tls-transport-serial fn2-tls-transport-budget fn2-tls-transport-cleanup-credit fn2-tls-transport-rows) (nth update-nth)))))

(defthm fn2-tls-transport-handoff-preserves-reservation
 (implies (and (fn2-tls-transportp fn2-tls-transport)
               (fn2-tls-transport-wfp fn2-tls-transport)
               (= (fn2-tls-transport-rows fn2-tls-transport) 1)
               (fn2-tls-transport-reservation fn2-tls-transport))
  (fn2-tls-transport-reservation (mv-nth 7 (fn2-tls-transport-handoff cap nonce slot generation fn2-tls-transport))))
 :hints (("Goal" :in-theory (e/d (fn2-tls-transport-reservation fn2-tls-transport-serial fn2-tls-transport-budget fn2-tls-transport-cleanup-credit fn2-tls-transport-rows) (nth update-nth)))))

(defthm fn2-tls-transport-closing-selects-reserved-free
 (implies (and (fn2-tls-transportp fn2-tls-transport)
               (fn2-tls-transport-wfp fn2-tls-transport)
               (= (fn2-tls-transport-rows fn2-tls-transport) 1)
               (fn2-tls-transport-handle-invariant fn2-tls-transport)
               (fn2-tls-transport-reservation fn2-tls-transport)
               (= (fn2-tls-transport-pending 0 fn2-tls-transport) 0)
               (= (fn2-tls-transport-alive 0 fn2-tls-transport) 1)
               (member-equal (fn2-tls-transport-terminal 0 fn2-tls-transport) '(2 4)))
  (and (equal (mv-nth 0 (fn2-tls-transport-next room pending fn2-tls-transport)) :cleanup)
       (equal (mv-nth 1 (fn2-tls-transport-next room pending fn2-tls-transport)) 9)
       (equal (fn2-tls-transport-cleanup-credit 0
                (mv-nth 5 (fn2-tls-transport-next room pending fn2-tls-transport))) 0)
       (equal (fn2-tls-transport-budget 0
                (mv-nth 5 (fn2-tls-transport-next room pending fn2-tls-transport)))
              (fn2-tls-transport-budget 0 fn2-tls-transport))))
 :hints (("Goal" :in-theory (e/d (fn2-tls-transport-reservation fn2-tls-transport-handle-invariant fn2-tls-transport-serial fn2-tls-transport-budget fn2-tls-transport-cleanup-credit fn2-tls-transport-rows fn2-tls-transport-alive fn2-tls-transport-handle-id fn2-tls-transport-pending fn2-tls-transport-terminal) (nth update-nth)))))

(defthm-owed fn2-tls-transport-closing-selects-reserved-free (room pending fn2-tls-transport)
 (implies (and (fn2-tls-transportp fn2-tls-transport)
               (fn2-tls-transport-wfp fn2-tls-transport)
               (= (fn2-tls-transport-rows fn2-tls-transport) 1)
               (fn2-tls-transport-handle-invariant fn2-tls-transport)
               (fn2-tls-transport-reservation fn2-tls-transport)
               (= (fn2-tls-transport-pending 0 fn2-tls-transport) 0)
               (= (fn2-tls-transport-alive 0 fn2-tls-transport) 1)
               (member-equal (fn2-tls-transport-terminal 0 fn2-tls-transport) '(2 4)))
  (and (equal (mv-nth 0 (fn2-tls-transport-next room pending fn2-tls-transport)) :cleanup)
       (equal (mv-nth 1 (fn2-tls-transport-next room pending fn2-tls-transport)) 9)
       (equal (fn2-tls-transport-cleanup-credit 0
                (mv-nth 5 (fn2-tls-transport-next room pending fn2-tls-transport))) 0)
       (equal (fn2-tls-transport-budget 0
                (mv-nth 5 (fn2-tls-transport-next room pending fn2-tls-transport)))
              (fn2-tls-transport-budget 0 fn2-tls-transport))))
 :schema :invariant
 :teeth (fn2-tls-transport-reservation-positive fn2-tls-transport-reservation-negative)
 :doc "Closing a live TLS handle always selects its reserved free action, even after the handshake budget is zero. The reservation prevents serial exhaustion from stranding a handle; the library free effect remains a primitive contract.")
(fn2-owed-discharge fn2-tls-transport-closing-selects-reserved-free fn2-tls-transport-closing-selects-reserved-free)
