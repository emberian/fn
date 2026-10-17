; fn: the catalog may take a sealed POST payload (lane arena-forget,
; 2026-10-03; the leak family of a reclaim that seals before it decides).
;
; host/native/owner.lisp fnn-owner-attempt sealed the POST's buffer and
; THEN asked the catalog to prepare the row naming it
; (host/owner-host.lisp fn-owner-cat-prepare-sealed).  That prepare refuses
; :recovery-required when the index writer holds a ticket that is not
; finished, or a prepared catalog commit is pending -- conditions that held
; before the seal -- and the sealed payload stayed in the arena, named by no
; row, for the life of the process.  The host now asks this word, a pure
; function of the ticket and the pending commit, BEFORE the seal, under the
; same owner-mutex hold, and seals nothing when it answers nil.
;
; THE KEYSTONES (lane proofs, 2026-10-04).  The 2026-10-03 theorem
; fn-cat-may-seal-is-the-prepare-gate restated the definition as a Boolean
; formula and is gone; what the host's interface row cites is the relation
; to the prepare transition itself, T1 (books/served-catalog-owner.lisp
; fn-cat-prepare-sealed, the prepare after the host's one seal).
;
;   fn-cat-may-seal-is-the-prepare-transition-gate: the word is t exactly
;   when the index writer is idle AND T1 over the REAL pending commit does
;   not refuse :pending -- for every record, row, plan, reservation, arena
;   and catalog.  The idle conjunct is the index writer's own begin test
;   (host/index-writer-operation-host.lisp fn-owner-index-writer-prepare
;   refuses :recovery-required on a ticket that is not finished), which no
;   book models as a transition; its teeth here are the iff's right-to-left
;   direction (a gate that ignored the ticket would answer t where T1 does
;   not refuse).  The pending conjunct's teeth are both directions: a gate
;   that ignored PENDING would answer t where T1 answers (:pending); a T1
;   that stopped refusing a pending commit would make the gate refuse what
;   T1 admits.
;
;   fn-cat-may-seal-admits-the-prepare-after-the-seal: after the word
;   answers t and the host seals the buffer, T1 over the row at the count
;   and the sealed arena IS prepared: the pending commit holds the row,
;   whose handle is the count the seal made, and that handle holds the
;   buffer's octets.  T1's :not-sealed arm is unreachable over a seal at
;   count - 1 and its :pending arm is what the gate refused, so a seal the
;   gate admitted is never a payload no row names (the leak this book
;   closes).  Satisfiable: a nil ticket, no pending commit, any record.
;   Premise inhabitation: every POST the host accepts is such a record
;   (tests/acl2/served-catalog-owner-tests.lisp runs T1 over them).

(in-package "ACL2")
(include-book "index-writer-ticket")
(include-book "served-catalog-owner")

(defun fn-cat-may-seal (ticket pending)
  (declare (xargs :guard t))
  (and (fn-iwt-idlep ticket)
       (not pending)
       t))

; T1's prepared answer is never the :pending refusal (the record is a
; five-field list; the refusal a one-element one).
(local
 (defthm fn-cms-prepared-is-not-the-pending-refusal
   (not (equal (fn-pc-make token expected held plan reservation) (list :pending)))
   :hints (("Goal" :in-theory (enable fn-pc-internals)))))

(defthm fn-cat-may-seal-is-the-prepare-transition-gate
  (iff (fn-cat-may-seal ticket pending)
       (and (fn-iwt-idlep ticket)
            (not (equal (fn-cat-prepare-sealed w row plan reservation pending fn-arena fn-cat)
                        (list :pending)))))
  :hints (("Goal" :in-theory (e/d (fn-cat-prepare-sealed)
                                  (fn-iwt-idlep fn-pc-make fn-record-payload
                                   fn-arena-count fn-cat-count fn-record-txid)))))

(defthm fn-cat-may-seal-admits-the-prepare-after-the-seal
  (implies (and (fn-cat-may-seal ticket pending)
                (fn-record-p w) (natp generation))
           (let* ((row (fn-intern-row-at w keyring generation (fn-arena-count fn-arena)))
                  (arena2 (fn-arena-seal-buffer fn-octets fn-arena))
                  (pc (fn-cat-prepare-sealed w row plan reservation pending arena2 fn-cat)))
             (and (fn-pc-p pc)
                  (equal (fn-pc-expected pc) (fn-cat-count fn-cat))
                  (equal (fn-record-payload (fn-pc-held pc)) (fn-arena-count fn-arena))
                  (equal (fn-arena-count arena2) (+ 1 (fn-arena-count fn-arena)))
                  (equal (fn-arena-payload (fn-arena-count fn-arena) arena2)
                         (fn-octets-list fn-octets)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cat-prepare-sealed-names-the-sealed-handle))
           :in-theory (e/d (fn-cat-may-seal)
                           (fn-cat-prepare-sealed-names-the-sealed-handle
                            fn-cat-prepare-sealed fn-intern-row-at fn-arena-seal-buffer
                            fn-pc-p fn-pc-expected fn-pc-held fn-record-p fn-iwt-idlep
                            fn-arena-count fn-arena-payload fn-cat-count fn-octets-list
                            fn-record-payload)))))
