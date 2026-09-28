; fn: payload kinds --- a payload HANDLE is not a payload's OCTETS
; (lane entry-guards, 2026-09-27).
;
; Since the records flip (PKT-635) the retained article's payload
; (books/acceptance.lisp fn-article-payload) and the held row's
; (books/held-record.lisp fn-held-payload) are HANDLES: naturals naming a
; payload in the arena (books/payload-arena.lisp), whose octets are read
; through it (books/store-intern.lisp fn-handle-bytes).  A wire record's
; payload (books/records-shape.lisp fn-record-payloadp) is octets.  AGENTS.md:
; octets, parsed fields, content identities, Message-IDs and local article
; numbers are distinct types; so are handles and octets.  Six defects on
; 2026-09-27 handed a handle where octets were meant, each surfacing as a
; silent refusal downstream (planning/evidence/entry-guards-2026-09-27.md).
;
; This book names the two kinds by recognizer and proves them DISJOINT, so a
; guard that names one refuses the other: `fn-payload-handle-p' (a natural)
; and `fn-cbor-octet-listp' (a NIL-terminated list of bytes, books/cbor.lisp).
; `fn-payload-handle-p' is a compound recognizer for natp: a proof that knows
; a value is a handle knows it is a natural, and nothing else changes.
;
; *fn-entry-guard-kinds* is the list of KIND recognizers the host's entry
; guard evaluates (host/native/io.lisp fnn-entry-guard): each is guard-t and
; costs at most one pass over the argument it reads, which the entry consumes
; anyway.  A guard conjunct (R v) over a non-stobj formal v with R in this
; list is checked on the actual argument at every host->ACL2 call, before the
; entry runs, and refused by name; any other conjunct is ACL2's alone.

(in-package "ACL2")
(include-book "cbor")

(defun fn-payload-handle-p (x)
  (declare (xargs :guard t))
  (natp x))

(defthm fn-payload-handle-p-is-natp
  (equal (fn-payload-handle-p x) (natp x))
  :rule-classes :compound-recognizer)

(in-theory (disable fn-payload-handle-p))

; KEYSTONE: the kinds are disjoint.  A handle is never octets and octets are
; never a handle (NIL, the empty payload, is octets and not a handle).
(defthm fn-payload-handle-is-not-octets
  (implies (fn-payload-handle-p x)
           (not (fn-cbor-octet-listp x)))
  :hints (("Goal" :in-theory (enable fn-cbor-octet-listp))))

(defthm fn-payload-octets-are-not-a-handle
  (implies (fn-cbor-octet-listp x)
           (not (fn-payload-handle-p x)))
  :hints (("Goal" :in-theory (enable fn-cbor-octet-listp))))

; A list of octet lists (a batch of records, a configuration's records).
(defun fn-octet-list-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-cbor-octet-listp (car xs))
           (fn-octet-list-listp (cdr xs)))
    (null xs)))

; The kind recognizers the host entry guard evaluates, with the kind each
; names in a refusal.  Every one is guard-verified with guard T and at most
; linear in its argument.
(defconst *fn-entry-guard-kinds*
  '((fn-payload-handle-p . "a payload handle (a natural naming an arena payload; its octets are fn-handle-bytes)")
    (fn-cbor-octet-listp . "octets (a NIL-terminated list of bytes, not a payload handle)")
    (fn-octet-list-listp . "a list of octet lists")
    (natp . "a natural")
    (posp . "a positive integer")
    (integerp . "an integer")
    (stringp . "a string")
    (symbolp . "a symbol")
    (keywordp . "a keyword")
    (booleanp . "a boolean")
    (true-listp . "a NIL-terminated list")))

; -----------------------------------------------------------------------------
; Declaring which kind a function takes.  (fn-payload-kind F :handle "why")
; says F works in HANDLES: a retained payload handed to it, or read inside it,
; is a handle (it reads the arena at it, compares it with another handle,
; returns it, or ignores it).  (fn-payload-kind F :source "why") says F
; RETURNS a handle, so its callers are checked as a payload read is.
; (fn-payload-kind F :wire "why") says F's
; articles are the octet model's (alpha: store-intern.lisp
; fn-articles-wire-of), so the payload it reads IS octets.  The declaration is
; a table entry and changes no logic; tools/payload_kind_check.py refuses a
; definition that reads a retained payload into anything undeclared.
(defmacro fn-payload-kind (name kind reason)
  (declare (xargs :guard (and (symbolp name) (member-eq kind '(:handle :source :wire))
                              (stringp reason))))
  `(table fn-payload-kinds ',name '(,kind ,reason)))

; The handle readers and the constructors that carry a handle unchanged.
(fn-payload-kind fn-payload-handle-p :handle "the handle recognizer")
(fn-payload-kind natp :handle "a handle is a natural")
(fn-payload-kind < :handle "a handle compared with the arena's count")
(fn-payload-kind fn-handle-bytes :handle "store-intern.lisp: the octets at a handle")
(fn-payload-kind fn-arena-payload :handle "payload-arena.lisp: the payload at a handle")
(fn-payload-kind fn-arena-payload-len :handle "payload-arena.lisp: its length")
(fn-payload-kind fn-nntp-arena-prefixp :handle "nntp-responses.lisp: a prefix test in the arena")
(fn-payload-kind fn-nntp-payload-bytes :handle "nntp-session.lisp: a handle's octets (NIL-or-octets passes through)")
(fn-payload-kind fn-bs-handle-bytes :handle "byte-store-scan.lisp: the octets at a handle")
(fn-payload-kind fn-make-article :handle "acceptance.lisp: the handle field, carried unchanged")
(fn-payload-kind fn-held-make :handle "held-record.lisp: the handle field, carried unchanged")

;; Withdrawn from includers (lane rule-hygiene, tools/rule_cost.py).
;; Each is tried in includers' proofs and pays for its frames in
;; almost none (planning/evidence/rule-cost-*.json has the counts;
;; docs/proof-style.md section 8).  An includer that needs one
;; enables it where it is used.
(in-theory (disable (:rewrite fn-payload-handle-is-not-octets)))
