; fn: who holds a payload handle, and when a released one is named by no row
; and held by no reader (lane def-holder, 2026-10-03: the payload-handle
; instance of books/def-holder.lisp; ARENA-FORGET's liveness precondition,
; books/arena-forget.lisp "GEN: def-holder fn-handle-holds").
;
; A payload handle (books/payload-arena.lisp) is held across a release of the
; owner's mutex by exactly these (the inventory from source,
; build/coordinator/lanedumps/def-holder.md section 1 R1; verified by
; ARENA-FORGET's own sweep):
;
;   - the served history's ROWS, each naming the handle it was interned at
;     (books/held-record.lisp); a reclaim swap rewrites changed rows at fresh
;     handles, and the old handles of the changed positions stop being named
;     (books/arena-forget.lisp fn-arf-changed-handles; KEYSTONE
;     fn-arf-changed-handles-are-unnamed);
;   - the off-mutex READERS of the live arena -- a checkpoint publication, an
;     export, a reclaim dry run, the reclaim pass -- each pinned at the
;     generation current when it started (host/native/io.lisp fnn-arena-pin
;     under the mutex; books/arena-reader-pins.lisp);
;   - a connection's RESPONSE PLAN in flight (one hold per connection id,
;     books/response-plan-pins.lisp fn-rpin-step, the same generation table).
;
; Feeds, consumers and BP jobs hold a Message-ID and resolve the handle per
; call under the mutex: they are not holders.  The two whole-arena leases
; (books/payload-view-lease.lisp fn-pvl-livep, books/recovery-payload-view.lisp
; fn-rpv-livep) hold every handle below the count at their acquire; their
; drivers are not in the native image (host/native/build.lisp), and a forget
; under a live one is refused by the host before the pins step is asked.
;
; So holding is the generation table, declared here as a def-holder of the
; :stamped shape: the four reader kinds are HOST holders (the raw host calls
; the step; tools/holder_check.py refuses an fnn-arena-pin outside their
; functions), the response plan is a LOGIC holder (fn-rpin-step threads the
; table; its two arms are declared with the theorems proved below).
;
; KEYSTONE fn-handle-holds-released-handles-are-unnamed-and-unheld: a
; retirement the pins step's :release answers, whose items are the handles a
; swap un-named (fn-arf-retire-event of fn-arf-changed-handles), was pending,
; its stamp is below every reader still pinned (each pinned after the swap,
; so from the rewritten history), and every one of its handles is named by
; no row of that history.  Nothing reaches such a handle: the forget
; (fn-arf-apply-released, ARENA-FORGET) may empty it.
(in-package "ACL2")
(include-book "def-holder")
(include-book "arena-forget")       ; fn-arf-retire-event, -changed-handles, the root fact
(include-book "response-plan-pins") ; fn-rpin-step

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
  :key "an arena generation: a holder pins the generation current when it takes its handles (under the owner's mutex); the handles a reclaim swap stops naming are retired at the stamp of that moment (fn-arf-retire-event) and released once no pin is at or below it"
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
                       :keeps fn-rpin-step-keeps-arena-invariant)))
  :effect (:process-local "the table is *fnn-arena-pins* (host/native/io.lisp), NIL before its first event; a death between :fn-handle-holds-decided (the pins step answered :release) and :fn-handle-holds-released (fn-arf-apply-released ran) loses the process and no durable state: the next open rebuilds the arena from the retained records, which name no retired handle (fn-arf-changed-handles-are-unnamed), with the table at fn-handle-holds-initial")
  :complete-by "fn-rpin-step is the only function of the world that calls fn-arpn-step (def-holder-check's walk refuses another); the host's own calls are the four fnn-arena-pin sites named above (tools/holder_check.py)")

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

; KEYSTONE.  A released retirement of the handles a swap un-named: it was
; pending; its stamp S is below every live pin G (every reader still running
; pinned after the swap: fn-arpn-release-postdates-every-live-pin); its items
; are exactly those handles; and each is named by no row of the rewritten
; history NEW (fn-arf-changed-handles-are-unnamed).  Host subject: the owner
; passes (fn-arf-retire-event (fn-arf-changed-handles old new)) to the pins
; step in the swap's quantum and hands the step's :release answer to
; fn-arf-apply-released (ARENA-FORGET, host/native/io.lisp fnn-arena-apply-due).
(defthm fn-handle-holds-released-handles-are-unnamed-and-unheld
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
           :use ((:instance fn-arpn-release-postdates-every-live-pin (h g))
                 ; pending, with or without a live pin: the release is the split
                 (:instance fn-arpn-split-released-are-clear (pend (third st)) (pins (second st)))
                 (:instance fn-arf-changed-handles-are-unnamed)
                 (:instance fn-arf-items-handles-of-tag (hs (fn-arf-changed-handles old new)))
                 (:instance fn-hh-disjointp-member
                            (xs (fn-arf-changed-handles old new))
                            (ys (fn-arf-rows-handles new))))
           :in-theory (e/d (fn-arpn-step)
                           (fn-arpn-release-postdates-every-live-pin fn-arpn-split-released-are-clear
                            fn-arf-changed-handles-are-unnamed fn-arf-items-handles-of-tag
                            fn-hh-disjointp-member fn-arpn-okp fn-arpn-split fn-arpn-clear-through-p
                            fn-arf-changed-handles fn-arf-rows-handles fn-arf-tag
                            fn-arf-items-handles fn-arf-disjointp fn-arf-rewrite-of-p
                            fn-arf-pend-handles))))
  :rule-classes nil)

; The debt (GENERATORS' defteeth v1): the claim is the statement above, in
; its source shape; the subject is the host's step.
(table fn-teeth-owed 'fn-handle-holds-released-handles-are-unnamed-and-unheld
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
