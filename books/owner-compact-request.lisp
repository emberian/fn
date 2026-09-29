; fn: compaction on a running owner, as an operator's request (lane
; operations, PKT-868, 2026-09-28).
;
; `store compact' and `store checkpoint' opened the store under its
; exclusive lock, so a running owner refused them (`store is already
; locked') and compaction meant a stop.  The owner already compacts itself:
; its automatic publication (books/owner-checkpoint-open.lisp
; fn-ock-publication-next; host/native/owner.lisp fnn-owner-maybe-publish)
; captures under the owner mutex, writes the checkpoint in bounded batches
; off it (fnn-checkpoint-write-steps, which yield at a stop), installs it by
; the byte program's cuts and drops the covered log segments (T8).  An
; operator's request is one more reason for that same publication to be due:
; with a suffix since the newest durable checkpoint (any length, not the
; threshold K/2), nothing in flight and no deferral blocking, the request
; makes it :due.  Everything else is the automatic decision's, so:
;
;   fn-ock-requested-next-without-request   no request: the automatic word.
;   fn-ock-requested-one-in-flight          a request never starts a second
;       publication (the in-flight one's :coalesce/:inflight stand).
;   fn-ock-requested-never-past-a-deferral  a request never overrides a
;       deferral by the budget or the space (PKT-492's :blocked stands).
;   fn-ock-requested-next-is-due-with-a-suffix   (KEYSTONE) with a request,
;       nothing in flight and nothing blocking, the publication is due
;       exactly when there is a suffix to compact.
;
; The request's answer (fn-ock-request-word) is what the operator is told:
; :requested, :coalesced (it runs when the one in flight finishes, which
; decides again with the request still standing), :nothing-to-compact, or
; :blocked (refused by name; the deferral's own report says why).
(in-package "ACL2")
(include-book "owner-checkpoint-open")

; A suffix to compact: records committed past the newest durable checkpoint,
; and not the count the last attempt already took.
(defun fn-ock-request-duep (durable count attempted)
  (declare (xargs :guard t))
  (let ((s (if (natp durable) durable 0)))
    (and (natp count)
         (< s count)
         (not (equal count attempted)))))

(defun fn-ock-requested-next (durable count k attempted inflight blockedp requested)
  (declare (xargs :guard t))
  (let ((word (fn-ock-publication-next durable count k attempted inflight blockedp)))
    (if (and requested
             (equal word :idle)
             (fn-ock-request-duep durable count attempted))
        :due
      word)))

(defthm fn-ock-requested-next-without-request
  (equal (fn-ock-requested-next durable count k attempted inflight blockedp nil)
         (fn-ock-publication-next durable count k attempted inflight blockedp)))

(defthm fn-ock-requested-one-in-flight
  (implies (natp inflight)
           (equal (fn-ock-requested-next durable count k attempted inflight blockedp requested)
                  (fn-ock-publication-next durable count k attempted inflight blockedp)))
  :hints (("Goal" :in-theory (enable fn-ock-publication-next))))

(defthm fn-ock-requested-never-past-a-deferral
  (implies (and (not (natp inflight)) blockedp)
           (equal (fn-ock-requested-next durable count k attempted inflight blockedp requested)
                  :blocked))
  :hints (("Goal" :in-theory (enable fn-ock-publication-next))))

; KEYSTONE.  The subject is host/owner-host.lisp fn-owner-sco-due, called by
; host/native/owner.lisp fnn-owner-maybe-publish-quantum.
(defthm fn-ock-requested-next-is-due-with-a-suffix
  (implies (and requested (not (natp inflight)) (not blockedp))
           (iff (equal (fn-ock-requested-next durable count k attempted inflight blockedp
                                              requested)
                       :due)
                (or (fn-ock-publication-duep durable count k attempted)
                    (fn-ock-request-duep durable count attempted))))
  :hints (("Goal" :in-theory (enable fn-ock-publication-next fn-ock-publication-duep))))

; The operator's answer, from the same observations.  The subject is
; host/owner-host.lisp fn-owner-sco-request, called by host/native/admin.lisp
; fnn-owner-live-admin-serialized for the `compaction request' plan.
(defun fn-ock-request-word (durable count attempted inflight blockedp)
  (declare (xargs :guard t))
  (cond ((natp inflight) :coalesced)
        (blockedp :blocked)
        ((fn-ock-request-duep durable count attempted) :requested)
        (t :nothing-to-compact)))

; The control reply's status for the answer: a deferral is a refusal (the
; operator is told by name, `status' says which deferral); the rest accept.
(defun fn-ock-request-status (word)
  (declare (xargs :guard t))
  (if (equal word :blocked) :refused :accepted))

; A request answered :requested is the next decision's :due.
(defthm fn-ock-requested-word-is-the-next-due
  (implies (equal (fn-ock-request-word durable count attempted inflight blockedp) :requested)
           (equal (fn-ock-requested-next durable count k attempted inflight blockedp t)
                  :due))
  :hints (("Goal" :in-theory (enable fn-ock-publication-next fn-ock-publication-duep))))
