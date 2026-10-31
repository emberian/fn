; The consumer port's keystones (layer E3; fn2/docs/e-surface.md section 9),
; statement first over the reference model (consumer-model.lisp), each owed
; with teeth: the Mini and helm fixtures as the satisfiable runs, and a
; deliberately wrong node (a FAULT of the model) that falsifies it. The
; served machine's refinement of the model through crashes (K10) is stated
; when D5 2/n serves a durable POST.
(in-package "ACL2")
(include-book "consumer-model")
(fn2-book-layer :e)

(defun fn2-cns-limits-p (limits)
  (declare (xargs :guard t))
  (and (true-listp limits) (equal (len limits) 2) (posp (car limits)) (natp (cadr limits))))

(defthm-owed fn2-cns-outcomes-declared (ops)
  (fn2-cns-declared-p (fn2-cns-trace ops nil))
  :schema :invariant :from (:operation-set fn2-consumer)
  :teeth (fn2-cns-test-mini fn2-cns-test-helm fn2-cns-test-declared-negative)
  :doc "K0: every reply the model gives a verb is an outcome FN2-CONSUMER declares for it (accepted with one value per result field, refused with one of its words, uncertain only for a durable verb), and a parked wait answers with a declared wait outcome. Ties the meaning to the port: a verb cannot answer a word its carriers do not render.")

(defthm-owed fn2-cns-at-least-once (ops limits)
  (implies (fn2-cns-limits-p limits)
           (fn2-cns-k1-trace (fn2-cns-trace ops nil) limits nil))
  :schema :invariant :from (:operation-set fn2-consumer)
  :teeth (fn2-cns-test-helm fn2-cns-test-helm-negative)
  :doc "K1: at every reachable state, for every registration whose view is current, the items a chain of pages delivers from the acknowledged position through the frontier, at any page size, are exactly the events its edges select under the current grants after each edge's start, in position order: none skipped, none invented. Teeth: helm's pages of four; a page that drops its last item when it stops early (fault :skip).")

(defthm-owed fn2-cns-ack-monotone (ops)
  (fn2-cns-k2 (fn2-cns-trace ops nil))
  :schema :invariant :from (:operation-set fn2-consumer)
  :teeth (fn2-cns-test-mini fn2-cns-test-mini-negative)
  :doc "K2: no recorded position ever decreases, per (principal, consumer, registration epoch); a rebase is a new epoch, so a reset is a new scope, never a rewind. Teeth: Mini's stale duplicate ack (cut c7); an ack behind the recorded position that is recorded (fault :rewind).")

(defthm-owed fn2-cns-append-retry (ops)
  (fn2-cns-k3 (fn2-cns-trace ops nil))
  :schema :invariant :from (:operation-set fn2-consumer)
  :teeth (fn2-cns-test-mini fn2-cns-test-mini-negative)
  :doc "K3: an append retried with the same principal, operation id and request answers its first outcome and adds nothing to the log. Teeth: Mini's lost Q reply (cut c2); an append that ignores the retry table (fault :reappend). Owed beyond the model: the outcome's retention lifetime and its answer after it (operation-expired), the semantic result stored by reference, keys on the durable principal identity (e-surface.md 11).")

(defthm-owed fn2-cns-wait-is-read (ops)
  (and (fn2-cns-k4 (fn2-cns-trace ops nil)) (fn2-cns-k4b (fn2-cns-trace ops nil)))
  :schema :invariant :from (:operation-set fn2-consumer)
  :teeth (fn2-cns-test-mini fn2-cns-test-mini-negative)
  :doc "K4 (CNS-007, scenario 7): a parked wait answers exactly what a read gives at the moment it answers, and after every step no parked wait has a read that is due (a step that makes one due answers it: no lost wake). Teeth: Mini's wait (cut c0) and its crash under a parked wait (c6); a woken wait that answers the page it saw when it parked (:stale-wait); a step that does not answer a due wait (:lost-wake).")

(defthm-owed fn2-cns-nntp-parity (ops)
  (fn2-cns-k5 (fn2-cns-trace ops nil) nil)
  :schema :invariant :from (:operation-set fn2-consumer)
  :teeth (fn2-cns-test-mini fn2-cns-test-mini-negative)
  :doc "K5 (M2's second half): an accepted append's article is what the NNTP view's ARTICLE by its Message-ID serves, exact octets, at the group numbers the append answered, in the state the append produced (a later withdrawal or reclamation may change ARTICLE; that is the read contract, not a parity failure). Teeth: Mini's report and Q; a view that re-renders the article (:rerender).")

(defthm-owed fn2-cns-uncertain-settles (ops)
  (fn2-cns-k6 (fn2-cns-trace ops nil) nil)
  :schema :invariant :from (:operation-set fn2-consumer)
  :teeth (fn2-cns-test-mini fn2-cns-test-mini-negative)
  :doc "K6: whether or not an accepted ack's reply reached the client, POSITION answers the old or the proposed position and repeating the ack is accepted (no intervening mutation of that consumer, the client's fence). Teeth: Mini's lost ack reply (cut c3); an equal ack refused as behind (:equal-behind).")

(defthm-owed fn2-cns-authority-current (ops)
  (fn2-cns-k7 (fn2-cns-trace ops nil))
  :schema :invariant :from (:operation-set fn2-consumer)
  :teeth (fn2-cns-test-helm fn2-cns-test-helm-negative)
  :doc "K7 (CNS-011): every item a page or a woken wait delivers is readable by its principal through one of the article's own streams under the grants current when it is answered (an addr entry never authorizes its originating room). Teeth: helm's denied-room mention, the grant that adds r3 and the revocation of r4; a read that uses the grants of its registration (:pinned-grant).")

(defthm-owed fn2-cns-refusal-changes-nothing (ops)
  (fn2-cns-k8 (fn2-cns-trace ops nil))
  :schema :invariant :from (:operation-set fn2-consumer)
  :teeth (fn2-cns-test-helm fn2-cns-test-helm-negative)
  :doc "K8 (the admission order of section 6): a refused verb leaves the state, the meter included, as it was, but for the conflict evidence IDENTITY ruling 6 commits beside an article's refusal. Teeth: helm's post into a room the seat may not post to; a meter that charges before the grant check and keeps it (:meter-first).")
