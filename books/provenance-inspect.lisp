; fn: the inspect verb's provenance of a Message-ID is ACL2's (lane
; host-decisions-2, 2026-09-27; packet C of
; planning/evidence/host-decisions-2026-09-27.md).
;
; host/store-node-host.lisp fn-store-prov-for-msgid walked the live node's
; bindings and retention pins and chose between the wire and the legacy form
; of the recorded evidence in host code.  The lookup and the dispatch are
; here; the host passes the node and the Message-ID and relays the octets.
; Off the served path: the inspect verb (tools/run_store.py) only.
;
; This book has the prefix `fn-provi-' (docs/prefixes.md).
(in-package "ACL2")
(include-book "provenance-codec")
(include-book "node")
(include-book "retention")

; The recorded evidence, described: a string is the provenance wire (or the
; legacy rendering, which fn-prov-of-wire passes through); anything else is
; already a provenance value.
(defun fn-provi-evidence-description (ev)
  (declare (xargs :guard t :verify-guards nil))
  (fn-prov-describe (if (stringp ev) (fn-prov-of-wire ev) ev)))

; The retention pin of the article NODE binds to MSGID, or NIL.
(defun fn-provi-pin-of-msgid (node msgid)
  (declare (xargs :guard t :verify-guards nil))
  (let ((binding (and (not (equal msgid :bad))
                      (fn-node-find-binding msgid (fn-node-bindings node)))))
    (and binding
         (fn-retain-find-id (fn-node-binding-id binding)
                            (fn-retain-pins (fn-node-retention node))))))

; THE LOOKUP the host calls (host/store-node-host.lisp fn-store-prov-for-msgid):
; the octets of the pin's evidence, described; NIL when the node binds no
; such Message-ID or its pin was released.
(defun fn-provi-of-msgid (node msgid)
  (declare (xargs :guard t :verify-guards nil))
  (let ((pin (fn-provi-pin-of-msgid node msgid)))
    (if pin
        (fn-record-string-octets
         (fn-provi-evidence-description (fn-retain-obligation-evidence pin)))
      nil)))

; The lookup names nothing but the node's own binding and pin: NIL without a
; pin, the pin's evidence described otherwise.
(defthm fn-provi-of-msgid-unfolds
  (equal (fn-provi-of-msgid node msgid)
         (let ((pin (fn-provi-pin-of-msgid node msgid)))
           (and pin
                (fn-record-string-octets
                 (fn-provi-evidence-description
                  (fn-retain-obligation-evidence pin))))))
  :hints (("Goal" :in-theory '(fn-provi-of-msgid))))

; A malformed Message-ID (the host's octet decode refused it) has no pin.
(defthm fn-provi-bad-msgid-has-no-provenance
  (equal (fn-provi-of-msgid node :bad) nil)
  :hints (("Goal" :in-theory '(fn-provi-of-msgid fn-provi-pin-of-msgid
                               (:executable-counterpart equal)
                               (:executable-counterpart not)))))
