; Completion delivery uses owner-tests' real open, POST, reservation and commit trace.
(in-package "ACL2")
(include-book "owner-tests")
(include-book "../../books/defkeystone")
;; Implementation mutation: completion delivery maps every storage word to
;; durable, losing the uncertain result after consumption.
(defun owct-outcome-all-durable (o id word)
 (declare (ignore word)) (fn-own-outcome o id :durable))
(defteeth fn-own-consumed-completion-is-240-or-uncertain
 :subject fn-own-outcome
 :claim (((connection (fn-own-find-conn id (fn-own-conns o))) (identity (equal (fn-own-sub-id (fn-own-inflight o)) id)) (natural-mark (natp (fn-own-sub-mark (fn-own-inflight o)))) (consumed (< (fn-own-sub-mark (fn-own-inflight o)) (len (fn-own-ledger o)))))
 (equal (car (fn-own-outcome o id word)) (let ((conn (fn-own-find-conn id (fn-own-conns o)))) (fn-served-result-effects (fn-served-post-outcome (fn-served-make-conn-group-indexed (fn-own-conn-wire conn) (fn-own-conn-session conn) (fn-own-conn-archive conn) (fn-own-conn-config conn) (fn-own-conn-observation conn) (fn-own-clock o) (fn-own-conn-verdicts conn) (fn-own-conn-group-index conn) (fn-own-conn-control conn)) (cond ((equal word :durable) :durable) ((equal word :durable-key-change-refused) word) (t :uncertain)))))))
 :witness ((o *own-p-done*) (id 4) (word :refused))
 :breaks ((connection ((o *own-w2-no-conn*)) :logical "corrupted owner: the completed connection is absent")
          (identity ((id 0)))
          (natural-mark ((o *own-w2-nil-mark*)) :logical "corrupted owner: nil completion mark")
          (consumed ((o *own-taken*))))
 :mutations ((all-durable (:conclusion (equal (car (owct-outcome-all-durable o id word)) (let ((conn (fn-own-find-conn id (fn-own-conns o)))) (fn-served-result-effects (fn-served-post-outcome (fn-served-make-conn-group-indexed (fn-own-conn-wire conn) (fn-own-conn-session conn) (fn-own-conn-archive conn) (fn-own-conn-config conn) (fn-own-conn-observation conn) (fn-own-clock o) (fn-own-conn-verdicts conn) (fn-own-conn-group-index conn) (fn-own-conn-control conn)) (cond ((equal word :durable) :durable) ((equal word :durable-key-change-refused) word) (t :uncertain))))))) ()
              :fault "completion delivery turns an ambiguous storage word into durable")))
(defteeth-check (fn-own-consumed-completion-is-240-or-uncertain))
