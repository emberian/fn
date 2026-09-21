; fn: the host-fault boundary of the owner (AGENTS.md, three outcomes).
;
; WHY THIS BOOK EXISTS.  tools/run_owner.py drives the owner machine from one
; selector loop.  Until this book, an exception raised anywhere inside that
; loop -- inside `Owner.drain' in particular -- unwound through `serve' and
; `run' and the PROCESS EXITED, so one peer's input ended the service for
; every other connection.  tools/v0_matrix.py measured it on persvati on
; 2026-09-20: node B died on the first IHAVE and 22 transit rows, 4 feed
; rows, 6 crash rows and 1 concurrency row of the 190-row matrix read
; `not-built' behind that one death.  A news server facing untrusted peers
; may not have that shape.
;
; The host must therefore be able to abandon ONE connection and keep serving.
; Abandoning a connection is a decision with a reply code, a scope and a
; durable consequence, so it is ACL2's, not Python's: this book is that
; transition.  The host's only decision at the boundary stays "do I still
; trust this socket"; every byte it then writes, and everything that happens
; to the owner's state, is `fn-own-fault' below.
;
; WHY IT IS A FOURTH OUTCOME.  Accepted, refused and uncertain are answers
; about the ARTICLE.  A host fault is not one of them: nothing is known about
; the article, and the thing that failed is the server.  books/nntp-post.lisp
; met the same question for a malformed posting session and answered it with
; RFC 3977 section 3.2.1's `403', stating in
; `fn-post-outcome-separates-a-malformed-session' that the fourth outcome
; differs from all three.  This book answers the owner-level question the
; same way and states the same separation
; (`fn-own-fault-reply-is-not-a-post-outcome'), so the two 403s are one
; vocabulary and neither can be read as a refusal.
;
; WHY IT IS ITS OWN BOOK AND NOT A FORM IN books/owner.lisp.  books/owner is
; 1,424 lines and is included by books/owner-invariants, books/owner-config
; and two test books.  The fault boundary is a seam of its own -- it is about
; the HOST's failure, not the service's -- and putting it here leaves those
; four certificates untouched.  The prefix stays `fn-own-': this is an owner
; transition and docs/prefixes.md records the book on that row.
;
; WHAT IS NOT HERE.  Nothing decides WHEN a fault happened; that is the
; host's observation, exactly as the store's `:durable'/`:refused'/
; `:uncertain' word is.  No new connection state exists: a faulted connection
; is a CLOSED connection (`fn-own-close', already proved to drop the
; connection, its pending transaction, its queued submissions and its
; submission in flight), which is why a fault cannot wedge the writer.

(in-package "ACL2")
(include-book "owner")

; LOCAL, deliberately.  books/owner-invariants owns the connection-list
; algebra this book reasons with (`fn-own-find-conn-of-remove-conn-other');
; citing it is right and restating it here would be a second copy.  But
; host/owner-host.lisp includes THIS book to reach `fn-own-fault', and a
; served node has no use for two thousand lines of proof rules in its world,
; so the dependency stops at the certificate.
(local (include-book "owner-invariants"))

; -----------------------------------------------------------------------------
; The reply
;
; RFC 3977 section 3.2.1: 403 is the generic "internal fault or problem
; prevented the command from completing".  The line is a constant of the
; model; the host may not compose one.  The close effect is in the same
; effect list because a connection the server stopped trusting is not served
; further: the host writes the reply and drops the socket, and
; `fn-served-closingp' is how it learns that from the effects it was handed,
; exactly as for every other close.

(defconst *fn-own-fault-line*
  "403 internal fault; this connection is closed and the server continues")

(defun fn-own-fault-effects ()
  (declare (xargs :guard t))
  (list (fn-nntp-reply-effect
         (fn-nntp-crlf (fn-nntp-string-octets *fn-own-fault-line*)))
        (fn-nntp-close-effect)))

; -----------------------------------------------------------------------------
; The transition
;
; (effects . owner), the shape `fn-own-outcome' and `fn-own-read' return, so
; the host installs it through the same `fn-owner-install-effects' and takes
; the same three projections of it.
;
; The CLOSE IS UNCONDITIONAL and only the reply is not.  The first draft did
; nothing at all for an id with no open connection, which would have left a
; submission in flight while its connection was gone -- and
; `fn-own-take-submission' moves a submission into the durable path only when
; NOTHING is in flight, so that state stops EVERY other connection from ever
; posting again.  In the composed machine that state is not reachable
; (`fn-own-close' clears a connection`s in-flight submission with the
; connection, so the two never come apart), but making the close
; unconditional is what lets K-FAULT-3 be stated with no hypothesis about the
; socket: what the owner forgets does not depend on what the host still
; holds.  The empty-effects branch is the same totality choice on the reply
; side and is UNREACHABLE-IN-COMPOSITION: `fn-owner-fault`
; (host/owner-host.lisp) is called with a connection id the host is serving,
; and a host fault with no connection to name -- an accept, a feed poll --
; never enters the model at all.

(defun fn-own-fault (o id)
  (declare (xargs :guard t))
  (cons (if (fn-own-find-conn id (fn-own-conns o))
            (fn-own-fault-effects)
          nil)
        (fn-own-close o id)))

(local (in-theory (enable fn-own-close
                          fn-own-find-conn-of-remove-conn-other)))

; The sibling of books/owner-invariants' `fn-own-find-conn-of-remove-conn-other',
; for the removed id itself.  LOCAL: the connection-list algebra has one home
; and it is books/owner-invariants; this is stated here only because that book
; did not need this half before, and it moves there the next time that book is
; opened rather than becoming a second exported copy.
(local
 (defthm fn-own-find-conn-of-remove-conn-same
   (not (fn-own-find-conn id (fn-own-remove-conn id conns)))
   :hints (("Goal" :induct (fn-own-remove-conn id conns)))))

; -----------------------------------------------------------------------------
; The keystones

; K-FAULT-1.  The faulted connection is gone.  This is what makes the host's
; drop safe: the owner does not hold a connection the host stopped serving.
(defthm fn-own-fault-closes-the-faulted-connection
  (not (fn-own-find-conn id (fn-own-conns (cdr (fn-own-fault o id))))))

; K-FAULT-2.  THE LANE'S THEOREM.  Every other connection is exactly what it
; was: same id, same version pin, same wire, same session, same pinned
; archive.  One peer's fault is one peer's fault.  Stated over
; `fn-own-find-conn' because that is the only way any later step reaches a
; connection (`fn-own-read', `fn-own-advance', `fn-own-outcome' and
; `fn-own-close' all begin with it), so equality here is equality of every
; later step's input.
(defthm fn-own-fault-keeps-every-other-connection
  (implies (not (equal other id))
           (equal (fn-own-find-conn other (fn-own-conns (cdr (fn-own-fault o id))))
                  (fn-own-find-conn other (fn-own-conns o)))))

; K-FAULT-3.  The writer is not wedged.  `fn-own-take-submission' moves a
; submission into the durable path only when NOTHING is in flight, so a
; fault that left the faulted connection's submission in flight would stop
; every OTHER connection from ever posting again -- a denial of service that
; survived the connection that caused it.  It does not: the in-flight slot
; and the pending transaction are cleared exactly when they were that
; connection's, and with no hypothesis about the connection still being open.
(defthm fn-own-fault-clears-the-faulted-submission
  (implies (and (fn-own-inflight o)
                (equal (fn-own-sub-id (fn-own-inflight o)) id))
           (not (fn-own-inflight (cdr (fn-own-fault o id))))))

(defthm fn-own-fault-keeps-another-connections-submission
  (implies (and (fn-own-inflight o)
                (not (equal (fn-own-sub-id (fn-own-inflight o)) id)))
           (equal (fn-own-inflight (cdr (fn-own-fault o id)))
                  (fn-own-inflight o))))

(defthm fn-own-fault-releases-the-faulted-transaction
  (implies (equal (fn-own-pending o) id)
           (not (fn-own-pending (cdr (fn-own-fault o id))))))

; K-FAULT-4.  A fault is not a store event.  The committed store, the
; committed view and the completion ledger are untouched, so no article is
; accepted, refused or released by the server giving up on a socket.  With
; K-FAULT-3 this is the whole durable content of a fault: it forgets one
; connection and nothing else.
(defthm fn-own-fault-is-not-a-store-event
  (and (equal (fn-own-store (cdr (fn-own-fault o id))) (fn-own-store o))
       (equal (fn-own-view (cdr (fn-own-fault o id))) (fn-own-view o))
       (equal (fn-own-ledger (cdr (fn-own-fault o id))) (fn-own-ledger o))))

; K-FAULT-5.  The fourth outcome, on the wire.  The octets a faulted
; connection receives are not the octets ANY posting outcome produces, for
; any session and any completion the store could have reported -- including
; the malformed-session 403 of books/nntp-post.lisp, which is a different
; line about a different subject.  So a client (and tools/v0_matrix.py's
; reply classifier) can never read a fault as an acceptance, as a refusal or
; as an uncertain post.
(defthm fn-own-fault-reply-is-not-a-post-outcome
  (not (equal (fn-served-reply-octets (fn-own-fault-effects))
              (fn-served-reply-octets
               (fn-post-result-effects (fn-nntp-post-outcome ps completion)))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-post-outcome fn-post-make-result
                                   fn-post-result-effects fn-post-single
                                   fn-nntp-single fn-nntp-make-result
                                   fn-nntp-result-effects fn-nntp-reply-effect
                                   fn-nntp-crlf fn-nntp-close-effect
                                   fn-nntp-string-octets
                                   fn-nntp-string-octets-aux
                                   fn-served-reply-octets
                                   fn-inj-nth fn-inj-car fn-inj-cdr)
                                  (fn-post-sessionp))))
  :rule-classes nil)

; K-FAULT-6.  The host is told to close.  `fn-served-closingp' is the only
; thing the host reads to decide that, and it is true here whatever else the
; effect list is projected for.
(defthm fn-own-fault-effects-close-the-connection
  (fn-served-closingp (fn-own-fault-effects)))

; The effect list is one the served path is allowed to emit: a reply and a
; close, both `fn-nntp-effectp'.  Nothing new enters the enumeration for a
; fault, so `fn-served-reply-octets', `fn-served-closingp',
; `fn-served-starttlsp' and `fn-served-submission' read it as they read any
; other, and the last two are false.
(defthm fn-own-fault-effects-are-typed
  (fn-served-effectsp (fn-own-fault-effects))
  :hints (("Goal" :in-theory (enable fn-served-effectsp fn-served-effectp
                                     fn-nntp-effectp))))

(defthm fn-own-fault-effects-ask-for-nothing-else
  (and (not (fn-served-starttlsp (fn-own-fault-effects)))
       (not (fn-served-submission (fn-own-fault-effects)))))

(verify-guards fn-own-fault-effects)
(verify-guards fn-own-fault)

; -----------------------------------------------------------------------------
; Export theory.  The two definitions are withdrawn; the keystones above and
; the typed-effects fact leave enabled.  A caller reasoning about a fault
; re-enables `fn-own-fault-vocabulary' in one line.

(deftheory fn-own-fault-vocabulary
  '(fn-own-fault-effects fn-own-fault))

(in-theory (disable fn-own-fault-vocabulary))
