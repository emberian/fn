; Teeth for books/provenance-inspect.lisp (packet C, the inspect verb).
(in-package "ACL2")
(include-book "owner-log-ocl-tests")
(include-book "../../books/provenance-inspect")

; REACHABLE: the configured owner after the article <ocmt@example> committed
; (owner-log-ocl-tests' *lgt-finished*): the live node binds it and holds its
; retention pin; the lookup is the pin's recorded evidence, described.
(defconst *provi-node* (fn-sn-node (lgt-store *lgt-finished*)))
(defconst *provi-pin* (fn-provi-pin-of-msgid *provi-node* "<ocmt@example>"))
(assert-event (equal (lgt-phase *lgt-finished*) :ready))
(assert-event (consp *provi-pin*))
(assert-event (equal (fn-retain-obligation-evidence *provi-pin*) "own-release:<ocmt@example>"))
(defconst *provi-out* (fn-provi-of-msgid *provi-node* "<ocmt@example>"))
(assert-event (consp *provi-out*))
(assert-event (equal *provi-out*
                     (fn-record-string-octets
                      (fn-provi-evidence-description "own-release:<ocmt@example>"))))
; No binding: an unknown Message-ID; a refused decode; the node before the
; article committed.
(assert-event (null (fn-provi-of-msgid *provi-node* "<absent@example>")))
(assert-event (null (fn-provi-of-msgid *provi-node* :bad)))
(assert-event (null (fn-provi-of-msgid (fn-sn-node (lgt-store *lgt-oc0*)) "<ocmt@example>")))
