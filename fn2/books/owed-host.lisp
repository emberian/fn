; A5r's keystones at the host boundary (layer doc 4.1.6). The first is the
; peer-address ABI: an Accept posted with a peer record reaches the listener
; row that observes it, exactly, and a refused record changes nothing but the
; stray count. Its subject is fn2-accept-peer-run, a logical view of the
; initialized core at its adapter boundary (fn2-turn, the outbox, the posts);
; lists exist only in the view.
(in-package "ACL2")
(include-book "executor")

(make-event (value (fn2-declare '(:operation-set fn2-host-accept) nil nil nil)))

; Turn until the outbox head is an Accept, acknowledging what is taken; the
; Accept's op, its generation and its owner's slot.
(defun fn2-ah-take-accept (fuel fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix fuel)))
  (if (zp fuel) (mv nil 0 0 0 fn2-core)
    (b* (((mv & & & & fn2-core) (fn2-turn fn2-core))
         ((mv code op opgen kind oslot fn2-core)
          (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
            (code op opgen kind oslot fn2-ops)
            (mv-let (code op opgen) (fn2-outbox-peek 0 fn2-ops)
              (if (not (eq code :ok)) (mv code 0 0 0 0 fn2-ops)
                (let ((kind (fn2-ops-kind op fn2-ops)) (oslot (fn2-ops-owner-slot op fn2-ops)))
                  (mv-let (ack fn2-ops) (fn2-outbox-ack 1 fn2-ops)
                    (mv ack op opgen kind oslot fn2-ops)))))
            (mv code op opgen kind oslot fn2-core))))
      (if (and (eq code :ok) (equal kind *fn2-action-accept*)) (mv t op opgen oslot fn2-core)
        (fn2-ah-take-accept (- fuel 1) fn2-core)))))

(defun fn2-ah-listener-view (id fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-listener (fn2-listener-table fn2-core)))
    (view)
    (list (fn2-listener-cap-index id fn2-listener) (fn2-listener-cap-nonce id fn2-listener)
          (fn2-listener-peer-family id fn2-listener) (fn2-listener-peer-port id fn2-listener)
          (fn2-listener-peer-w0 id fn2-listener) (fn2-listener-peer-w1 id fn2-listener)
          (fn2-listener-peer-w2 id fn2-listener) (fn2-listener-peer-w3 id fn2-listener))
    view))

; From the initialized core: the first Accept completes with capability
; (5, 9) and the given peer record, one turn harvests it. Result: (strays
; cap-index cap-nonce family port w0 w1 w2 w3), the strays the post added
; and the observing listener row's fields.
(defun fn2-accept-peer-run (family port w0 w1 w2 w3)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core)
      (b* ((fn2-core (fn2-init-executor *fn2-profile-tiny* :echo nil fn2-core))
           ((mv found op opgen oslot fn2-core) (fn2-ah-take-accept 8 fn2-core))
           ((unless found) (mv :no-accept fn2-core))
           (before (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (n) (fn2-ops-stray fn2-ops) n))
           (fn2-core (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (fn2-ops)
                       (fn2-post-accept-result op opgen *fn2-outcome-done* *fn2-reason-none* 5 9
                                               family port w0 w1 w2 w3 fn2-ops)
                       fn2-core))
           (after (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (n) (fn2-ops-stray fn2-ops) n))
           ((mv & & & & fn2-core) (fn2-turn fn2-core)))
        (mv (cons (- after before) (fn2-ah-listener-view oslot fn2-core)) fn2-core))
      result)))

(defthm-owed fn2-accept-peer-delivered (family port w0 w1 w2 w3)
  (implies (fn2-peer-recordp *fn2-outcome-done* family port w0 w1 w2 w3)
           (equal (fn2-accept-peer-run family port w0 w1 w2 w3)
                  (list 0 5 9 family port w0 w1 w2 w3)))
  :schema :invariant :from (:operation-set fn2-host-accept)
  :teeth (fn2-host-test-peer-delivered fn2-host-test-peer-delivered-negative)
  :doc "A5r's ABI: an Accept result posted with a valid peer record (any family) is harvested into the observing listener row exactly, beside its capability, with no stray; the peer address reaches the core only through the Accept's own cell.")
