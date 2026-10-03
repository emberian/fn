; fn: who holds a payload handle, and what a released one is proved to be
; (lane def-holder, 2026-10-03: the payload-handle instance of
; books/def-holder.lisp; ARENA-FORGET's liveness precondition,
; books/arena-forget.lisp "GEN: def-holder fn-handle-holds"; consultation
; c05 shaped the relation).
;
; A payload handle H (books/payload-arena.lisp) may be forgotten only when
; NO REACHABLE ROOT NAMES IT, physical custody of its storage has ended, and
; the physical effect follows the durable replacement.  The roots, from the
; inventory (build/coordinator/lanedumps/def-holder.md sections 1 and 1b):
;
;   TOP      the served history's rows: a reclaim swap rewrites changed rows
;            at fresh handles; the old handles of the changed positions stop
;            being named (books/arena-forget.lisp fn-arf-changed-handles;
;            KEYSTONE fn-arf-changed-handles-are-unnamed);
;   CONNS    every connection's retained view (version, archive, index:
;            books/owner.lisp:126-163): the swap re-pins every live
;            connection to the rebuilt view in the same quantum
;            (books/owner-reclaim-pass.lisp fn-orcp-swapped-owner ->
;            fn-orcp-repin-conns), so after the swap CONNS names what TOP
;            names;
;   READERS  the off-mutex readers of the live arena (a checkpoint
;            publication, an export, a reclaim dry run, the reclaim pass) and
;            a connection's response plan in flight (an OVER cursor among
;            them), each pinned at a generation BEFORE it copied anything
;            (host/native/io.lisp fnn-arena-pin under the mutex;
;            books/response-plan-pins.lisp fn-rpin-step, keyed by cid);
;   LOG      the fenced and in-flight log members (H FILE PLACE OCTETS,
;            host/native/io.lisp:6316-6323): the swap word does not test
;            them; the release must refuse while one names a retired handle
;            (ARENA-FORGET's open clause 4(c));
;   CUSTODY  a cold read names a PLACE (file, eoff, elen, trailer), not H
;            (host/native/extent.lisp:830-843); the forget reuses no
;            storage, and the file closes only once fn-pio-file-clear-p;
;   OTHER    the BP workflow's own node (host/workflow-host.lisp:19-24,
;            serialized with its reads), the consumer remote-visible writer's
;            retained row and the NEWNEWS tail (both unwired), the
;            whole-arena leases (drivers not in the native image).
;
; Feeds and BP outbound hold a Message-ID and a rendered COPY, not a
; deferred handle.  The declaration below names every root with its host
; functions and status; tools/holder_check.py checks the host side.
;
; What this book PROVES (KEYSTONE
; fn-handle-holds-released-handles-are-unnamed-and-postdate-every-pin,
; parameterised over NAMED, the handles the roots still name): a
; retirement the pins step's :release answers, whose items are the handles
; a swap un-named (fn-arf-retire-event of fn-arf-changed-handles) and those
; are disjoint from NAMED, was pending, its stamp is below every reader
; still pinned (each pinned after the swap: READERS), its items are exactly
; those handles, and none is in NAMED.  The corollary
; ...-under-the-pairwise-root-fact discharges the disjointness from today's
; root fact (PRF-1235: the old rows' handles distinct, NEW a rewrite) with
; NAMED the rewritten history's rows (TOP, and CONNS by the repin); when
; ARENA-FORGET's per-handle name count over every root lands (c08 (a)), only
; that corollary's hypothesis and citation change.  What it does NOT prove: LOG, CUSTODY and OTHER -- those are the
; row's :excluded, :serialized and :unwired roots, each a clause the host
; establishes (the swap clause, the file pin, the wiring gate), not a
; theorem here.  The forget (fn-arf-apply-released, ARENA-FORGET) runs at
; the reclaim pass's :released cut, after :installed (the durable
; replacement): effect (:physical *fn-orcp-cuts* :cut :released :after
; :installed).
(in-package "ACL2")
(include-book "def-holder")
(include-book "arena-forget")       ; fn-arf-retire-event, -changed-handles, the root fact
(include-book "response-plan-pins") ; fn-rpin-step
(include-book "reclaim-cuts")       ; *fn-orcp-cuts* (a leaf of owner-reclaim-pass)

; ---------------------------------------------------------------------------
; The response plan's two arms, as the holder relation needs them: on
; :acquire the table it returns is the pin when it answers :acquired and
; the table it was handed otherwise; on :release the unpin of the owner's
; generation when it answers :released, else unchanged.

(defthm fn-hh-rpin-acquire-pins
  (implies (and (alistp owners) (fn-arpn-okp st) (equal (car event) :acquire))
           (equal (mv-nth 1 (fn-rpin-step owners st event))
                  (if (equal (mv-nth 2 (fn-rpin-step owners st event)) :acquired)
                      (mv-nth 0 (fn-arpn-step st '(:pin)))
                    st)))
  :hints (("Goal" :in-theory (e/d (fn-rpin-step) (fn-arpn-step fn-arpn-okp fn-rpin-owner))))
  :rule-classes nil)

(defthm fn-hh-rpin-release-unpins
  (implies (and (alistp owners) (fn-arpn-okp st) (equal (car event) :release))
           (equal (mv-nth 1 (fn-rpin-step owners st event))
                  (if (equal (mv-nth 2 (fn-rpin-step owners st event)) :released)
                      (mv-nth 0 (fn-arpn-step st (list :unpin (cdr (fn-rpin-owner (cadr event) owners)))))
                    st)))
  :hints (("Goal" :in-theory (e/d (fn-rpin-step) (fn-arpn-step fn-arpn-okp fn-rpin-owner))))
  :rule-classes nil)

; ---------------------------------------------------------------------------
; The declaration.

(def-holder fn-handle-holds
  :shape :stamped
  :key "an arena generation: a holder pins the generation current when it takes its handles (under the owner's mutex); the handles a reclaim swap stops naming are retired at the stamp of that moment (fn-arf-retire-event, in the swap's quantum) and released once no pin is at or below it"
  :holders ((publication :host t :acquire fnn-arena-pin :release fnn-arena-unpin
                         :in (fnn-owner-maybe-publish-quantum fnn-owner-publish-captured))
            (export :host t :acquire fnn-arena-pin :release fnn-arena-unpin
                    :in (fnn-owner-export-start fnn-owner-export-captured))
            (reclaim-dry-run :host t :acquire fnn-arena-pin :release fnn-arena-unpin
                             :in (fnn-owner-reclaim-dry-run))
            (reclaim-pass :host t :acquire fnn-arena-pin :release fnn-arena-unpin
                          :in (fnn-owner-reclaim-pass))
            (response-plan
             :acquire (fn-rpin-step fn-hh-rpin-acquire-pins
                       :table 1 :result (mv-nth 1 _)
                       :ok (equal (mv-nth 2 _) :acquired)
                       :when (equal (car event) :acquire)
                       :keeps fn-rpin-step-keeps-arena-invariant)
             :release (fn-rpin-step fn-hh-rpin-release-unpins
                       :table 1 :result (mv-nth 1 _)
                       :key (cdr (fn-rpin-owner (cadr event) owners))
                       :ok (equal (mv-nth 2 _) :released)
                       :when (equal (car event) :release)
                       :keeps fn-rpin-step-keeps-arena-invariant))
            ; the roots (section 1b of the inventory)
            (connection-view :root t :in (fnn-owner-reclaim-pass)
                             :status (:repinned "fn-orcp-swapped-owner re-pins every live connection to the rebuilt view in the swap quantum (fn-orcp-repin-conns): after the swap a connection's archive names what the rewritten history names"))
            (over-cursor :root t :in (fnn-owner-handle-chunk-read fnn-mux-after)
                         :status (:pinned "the response hold is acquired before the plan leaves the quantum (host/native/owner.lisp:4545-4549); every later cursor quantum reads under that generation"))
            (log-member :root t :in (fnn-log-members-in-flight fnn-log-reseat-fenced)
                        :status (:excluded "a fenced or in-flight member (H FILE PLACE OCTETS) is not tested by the swap word; the release is refused while one names a retired handle (ARENA-FORGET clause 4(c): the swap word, or fn-arx-commit-extent refusing a forgotten handle)"))
            (cold-read :root t :in (fnn-extent-issue-direct fnn-extent-direct-settle fnn-extent-close)
                       :status (:excluded "physical custody: a worker holds (file, place), not H; the forget reuses no storage, and the file closes only when fn-pio-file-clear-p (books/page-read-ownership.lisp)"))
            (bp-workflow-node :root t :in (fnn-bpo-call-with-owner-journal)
                              :status (:serialized "fn-workflow-state holds the open's node; the request thunk that resolves an article in it runs inside the same serialized region (host/native/bp-obligation.lisp:44-59); a longer-lived image must be refreshed per swap"))
            (remote-visible-writer :root t :in (fn-owner-remote-collection-step-internal)
                                   :status (:unwired "the writer retains a row and re-reads its handle (books/consumer-remote-visible-buffer.lisp:85-136); no issuer exists (host/consumer-remote-report-host.lisp:57-58)"))
            (newnews-tail :root t :in (fn-nnw-response)
                          :status (:unwired "books/newnews-cursor.lisp:42-46: called by nothing served yet"))
            (whole-arena-lease :root t :in (fnn-snapshot-payload-view-acquire fnn-snapshot-payload-view-release)
                               :status (:unwired "fn-pvl-livep / fn-rpv-livep hold every handle below the token's prefix; their drivers are not in host/native/build.lisp; a forget under a live one is refused by the host before the step is asked")))
  :effect (:physical *fn-orcp-cuts* :cut :released :after :installed)
  :complete-by "fn-rpin-step is the only function of the world that calls fn-arpn-step (def-holder-check's walk refuses another); the host's own calls are the four fnn-arena-pin sites named above and the roots' :in functions (tools/holder_check.py)")

; ---------------------------------------------------------------------------
; The composed release theorem.

(local
 (defthm fn-hh-row-handle-natp-or-nil
   (or (null (fn-arf-row-handle row)) (natp (fn-arf-row-handle row)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-arf-row-handle)))))

(local
 (defthm fn-hh-changed-handles-nat-listp
   (nat-listp (fn-arf-changed-handles old new))
   :hints (("Goal" :induct (fn-arf-changed-handles old new)
            :in-theory (disable fn-arf-row-handle))
           ("Subgoal *1/3" :use ((:instance fn-hh-row-handle-natp-or-nil (row (car old))))))))

(local
 (defthm fn-hh-disjointp-member
   (implies (and (fn-arf-disjointp xs ys) (member-equal h xs))
            (not (member-equal h ys)))))

; KEYSTONE (PRF-1240), PARAMETERISED over NAMED, the handles the declared
; roots still name after the swap (today: the rewritten history's rows,
; fn-arf-rows-handles NEW; ARENA-FORGET's c08 (a): the union of every root,
; carried as a per-handle name count).  A released retirement whose items
; are the handles a swap un-named (fn-arf-tag of the walk's answer), those
; handles disjoint from NAMED: it was pending; its stamp S is below every
; live pin G (every reader still running pinned after the swap:
; fn-arpn-release-postdates-every-live-pin); its items are exactly those
; handles; and no item is in NAMED.  The root fact -- that the walk's
; handles ARE disjoint from NAMED -- is the hypothesis, discharged by the
; corollary below for today's fact and by ARENA-FORGET's name-count theorem
; when it lands; this statement does not change.  Not here: LOG, CUSTODY,
; OTHER (the row's :excluded, :serialized and :unwired roots).  Host
; subject: the owner passes (fn-arf-retire-event (fn-arf-changed-handles old
; new)) to the pins step in the swap's quantum, under the gate, and hands
; the step's :release answer to fn-arf-apply-released at the :released cut
; (ARENA-FORGET, host/native/io.lisp fnn-arena-apply-due).
(defthm fn-handle-holds-released-handles-are-unnamed-and-postdate-every-pin
  (implies (and (fn-arpn-okp st)
                (member-equal e (mv-nth 1 (fn-arpn-step st '(:release))))
                (equal (cdr e) (fn-arf-tag (fn-arf-changed-handles old new)))
                (fn-arf-disjointp (fn-arf-changed-handles old new) named))
           (and (member-equal e (third st))
                (implies (< 0 (fn-arpn-pins-of g (second (mv-nth 0 (fn-arpn-step st '(:release))))))
                         (< (car e) g))
                (equal (fn-arf-items-handles (cdr e)) (fn-arf-changed-handles old new))
                (implies (member-equal h (fn-arf-items-handles (cdr e)))
                         (not (member-equal h named)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-arpn-release-postdates-every-live-pin (h g))
                 ; pending, with or without a live pin: the release is the split
                 (:instance fn-arpn-split-released-are-clear (pend (third st)) (pins (second st)))
                 (:instance fn-arf-items-handles-of-tag (hs (fn-arf-changed-handles old new)))
                 (:instance fn-hh-disjointp-member
                            (xs (fn-arf-changed-handles old new))
                            (ys named)))
           :in-theory (e/d (fn-arpn-step)
                           (fn-arpn-release-postdates-every-live-pin fn-arpn-split-released-are-clear
                            fn-arf-items-handles-of-tag
                            fn-hh-disjointp-member fn-arpn-okp fn-arpn-split fn-arpn-clear-through-p
                            fn-arf-changed-handles fn-arf-rows-handles fn-arf-tag
                            fn-arf-items-handles fn-arf-disjointp fn-arf-rewrite-of-p
                            fn-arf-pend-handles))))
  :rule-classes nil)

; The corollary under today's root fact (PRF-1235 fn-arf-changed-handles-
; are-unnamed): NAMED is the rewritten history's rows' handles, and the walk's
; handles are disjoint from them when the old rows' handles are pairwise
; distinct and NEW is a rewrite of OLD.  This is the citation that changes
; when the root fact becomes the per-handle name count.
(defthm fn-handle-holds-released-handles-are-unnamed-under-the-pairwise-root-fact
  (implies (and (fn-arpn-okp st)
                (member-equal e (mv-nth 1 (fn-arpn-step st '(:release))))
                (equal (cdr e) (fn-arf-tag (fn-arf-changed-handles old new)))
                (no-duplicatesp-equal (fn-arf-rows-handles old))
                (fn-arf-rewrite-of-p old new (fn-arf-rows-handles old)))
           (and (member-equal e (third st))
                (implies (< 0 (fn-arpn-pins-of g (second (mv-nth 0 (fn-arpn-step st '(:release))))))
                         (< (car e) g))
                (equal (fn-arf-items-handles (cdr e)) (fn-arf-changed-handles old new))
                (implies (member-equal h (fn-arf-items-handles (cdr e)))
                         (not (member-equal h (fn-arf-rows-handles new))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-handle-holds-released-handles-are-unnamed-and-postdate-every-pin
                            (named (fn-arf-rows-handles new)))
                 (:instance fn-arf-changed-handles-are-unnamed))
           :in-theory (disable fn-arf-changed-handles-are-unnamed fn-arpn-step fn-arpn-okp
                               fn-arf-changed-handles fn-arf-rows-handles fn-arf-tag
                               fn-arf-items-handles fn-arf-disjointp fn-arf-rewrite-of-p)))
  :rule-classes nil)

; The debts (GENERATORS' defteeth v1): each claim is the statement above, in
; its source shape; the subject is the host's step.
(table fn-teeth-owed 'fn-handle-holds-released-handles-are-unnamed-and-postdate-every-pin
       '(:by handle-holds
         :claim (implies (and (fn-arpn-okp st)
                              (member-equal e (mv-nth 1 (fn-arpn-step st '(:release))))
                              (equal (cdr e) (fn-arf-tag (fn-arf-changed-handles old new)))
                              (fn-arf-disjointp (fn-arf-changed-handles old new) named))
                         (and (member-equal e (third st))
                              (implies (< 0 (fn-arpn-pins-of g (second (mv-nth 0 (fn-arpn-step st '(:release))))))
                                       (< (car e) g))
                              (equal (fn-arf-items-handles (cdr e)) (fn-arf-changed-handles old new))
                              (implies (member-equal h (fn-arf-items-handles (cdr e)))
                                       (not (member-equal h named)))))
         :subject fn-arpn-step))

(table fn-teeth-owed 'fn-handle-holds-released-handles-are-unnamed-under-the-pairwise-root-fact
       '(:by handle-holds
         :claim (implies (and (fn-arpn-okp st)
                              (member-equal e (mv-nth 1 (fn-arpn-step st '(:release))))
                              (equal (cdr e) (fn-arf-tag (fn-arf-changed-handles old new)))
                              (no-duplicatesp-equal (fn-arf-rows-handles old))
                              (fn-arf-rewrite-of-p old new (fn-arf-rows-handles old)))
                         (and (member-equal e (third st))
                              (implies (< 0 (fn-arpn-pins-of g (second (mv-nth 0 (fn-arpn-step st '(:release))))))
                                       (< (car e) g))
                              (equal (fn-arf-items-handles (cdr e)) (fn-arf-changed-handles old new))
                              (implies (member-equal h (fn-arf-items-handles (cdr e)))
                                       (not (member-equal h (fn-arf-rows-handles new))))))
         :subject fn-arpn-step))
