; fn: the POST machine's acceptance spans PRE, INS and SUFTAIL bounded by one
; term K of the sealed configuration (books/post-transaction.lisp
; fn-ptx-acc-end, lane/post, Builder P: |pre|, |ins|, |suftail| <= K).  The
; record's head and tail around the payload are bounded by the records seam
; (books/records-seam.lisp: head <= *fn-record-head-max-octets*, tail <=
; *fn-record-tail-max-octets*); the injected block the head span carries is
; bounded by C's O1 figure (books/filed-stored.lisp
; fn-o1-injected-block-octets, 2236 + 2 len(agent)) at the widest agent a
; configuration admits (books/injection.lisp fn-inj-configp:
; len(agent) <= *fn-inj-max-agent-octets*).  K is derived from those figures,
; never pinned.

(in-package "ACL2")
(include-book "filed-stored")
(include-book "records-seam")

; The injected block at the widest agent a configuration admits.
(defun fn-adm-injected-block-max ()
  (declare (xargs :guard t))
  (fn-o1-injected-block-octets
   (make-list *fn-inj-max-agent-octets* :initial-element 0)))

; KEYSTONE: an agent within the configuration's bound injects at most
; (fn-adm-injected-block-max) octets.
(defthm fn-adm-injected-block-within-its-max
  (implies (<= (len agent) *fn-inj-max-agent-octets*)
           (<= (fn-o1-injected-block-octets agent) (fn-adm-injected-block-max)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-o1-injected-block-octets))))

; Every configuration's own agent meets the hypothesis.
(defthm fn-adm-configured-injected-block-within-its-max
  (implies (fn-inj-configp config)
           (<= (fn-o1-injected-block-octets (fn-inj-config-agent config))
               (fn-adm-injected-block-max)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (fn-inj-configp) (fn-o1-injected-block-octets
                                                     fn-adm-injected-block-max))
                  :use ((:instance fn-adm-injected-block-within-its-max
                                   (agent (fn-inj-config-agent config)))))))

; K: the widest acceptance span, the record's head with the injected block,
; or its tail.
(defun fn-adm-acc-out-max ()
  (declare (xargs :guard t))
  (max (+ *fn-record-head-max-octets* (fn-adm-injected-block-max))
       *fn-record-tail-max-octets*))

(defthm fn-adm-acc-out-max-holds-the-head-and-the-block
  (<= (+ *fn-record-head-max-octets* (fn-adm-injected-block-max))
      (fn-adm-acc-out-max))
  :rule-classes nil)

(defthm fn-adm-acc-out-max-holds-the-tail
  (<= *fn-record-tail-max-octets* (fn-adm-acc-out-max))
  :rule-classes nil)
