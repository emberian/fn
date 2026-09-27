; fn: THE IDENTITY PREPARE INTERNS ITS COMPOSITE (lane signed-post,
; 2026-09-27; PRF-292; D25, D27).
;
; Since the records flip the Store retains an accepted signed article as a
; ROW: the wire composite beside its article interned (books/held-record.lisp
; fn-hstxa-p), and the identity prepare's gate admits exactly the retained
; kinds (books/owner-commit-carried.lisp fn-ccar-sn-prepare-identity:
; fn-stxe-p, fn-stxk-p, fn-hstxa-p).  The composite the owner constructs
; (books/peer-authored-accept.lisp fn-pa-authorized-event, a wire
; fn-stxa-p) never passes that gate as it is, so every signed POST, signed
; NNTP transit and signed BP application was refused 441 from the flip on.
; The owner's identity entry therefore stages the row the intern WOULD make
; (fn-intern-event of the composite at the arena's count, under the Store's
; keyring and generation) and names the article's payload for the host to
; seal exactly when the Store took the row, as the POST entry does
; (books/store-intern.lisp fn-store-prepare-interned).  The signing input is
; untouched: the composite keeps the relayed octets (D25), and the row keeps
; the composite.
;
; Host path: host/native/owner.lisp fnn-owner-identity-commit calls
; host/owner-host.lisp fn-owner-prepare-identity, which installs
; fn-oii-ocfg-prepare-identity at the live arena's count and answers
; (:seal PAYLOAD) (fn-oii-identity-payload) when the Store changed and
; fn-oii-identity-sealsp holds; the host seals those octets with one
; fn-arena-seal-list call (host/native/io.lisp fnn-seal-octets).
;
; KEYSTONE fn-oii-ocfg-prepare-identity-is-intern-then-step: on every owner
; the maintained relation admits, the entry is the owner's
; (:prepare-identity ROW) step over the row fn-intern-event makes, and the
; sealed arena is the intern's (fn-oii-seal-is-the-intern-arena).
(in-package "ACL2")
(include-book "store-intern")
(include-book "owner-commit-carried")

; The row fn-intern-event makes of W at handle H, without sealing.
(defun fn-oii-identity-row (w keyring generation h)
  (declare (xargs :guard (and (fn-prin-keyringp keyring) (natp generation) (natp h))))
  (cond ((fn-record-p w) (fn-intern-row-at w keyring generation h))
        ((fn-stxa-p w)
         (let ((a (fn-replay-composite-record w)))
           (if (fn-record-p a)
               (fn-hstxa-make w (fn-intern-row-at a keyring generation h))
             :bad)))
        ((fn-wire-event-p w) w)
        (t :bad)))

; Whether the intern of W seals a payload, and which.
(defun fn-oii-identity-sealsp (w)
  (declare (xargs :guard t))
  (or (fn-record-p w)
      (and (fn-stxa-p w) (fn-record-p (fn-replay-composite-record w)))))

(defun fn-oii-identity-payload (w)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable fn-record-p fn-record-payloadp)))))
  (cond ((fn-record-p w) (fn-record-payload w))
        ((and (fn-stxa-p w) (fn-record-p (fn-replay-composite-record w)))
         (fn-record-payload (fn-replay-composite-record w)))
        (t nil)))

; The row at the arena's count is the intern's row.
(defthm fn-oii-identity-row-is-the-intern
  (equal (fn-oii-identity-row w keyring generation (fn-arena-count fn-arena))
         (mv-nth 0 (fn-intern-event w keyring generation fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-intern-event fn-oii-identity-row)
                                  (fn-intern-row-at fn-cat-intern-list fn-arena-count
                                   fn-cat-intern-list-is-row-at-count))
           :use ((:instance fn-cat-intern-list-is-row-at-count)
                 (:instance fn-cat-intern-list-is-row-at-count
                  (w (fn-replay-composite-record w)))))))

; The seal the host makes is the intern's arena.
(defthm fn-oii-seal-is-the-intern-arena
  (equal (mv-nth 1 (fn-intern-event w keyring generation fn-arena))
         (if (fn-oii-identity-sealsp w)
             (fn-arena-seal-list (fn-oii-identity-payload w) fn-arena)
           fn-arena))
  :hints (("Goal" :in-theory (e/d (fn-intern-event-arena) (fn-intern-event)))))

; A composite whose article decodes is sealed, and interns to a row the
; identity prepare's gate admits (a retained composite carrying W).
(defthm fn-oii-composite-row-is-held
  (implies (and (fn-stxa-p w) (fn-record-p (fn-replay-composite-record w))
                (natp generation))
           (let ((row (fn-oii-identity-row w keyring generation (fn-arena-count fn-arena))))
             (and (fn-oii-identity-sealsp w)
                  (fn-hstxa-p row)
                  (equal (fn-hstxa-stxa row) w))))
  :hints (("Goal" :in-theory (e/d (fn-oii-identity-row fn-oii-identity-sealsp
                                   fn-hstxa-p fn-hstxa-make fn-hstxa-stxa)
                                  (fn-intern-row-at fn-cat-intern-list fn-held-p fn-arena-count
                                   fn-stxa-p fn-record-p fn-replay-composite-record
                                   fn-cat-intern-list-is-row-at-count))
           :use ((:instance fn-held-p-of-intern-list
                  (w (fn-replay-composite-record w)))
                 (:instance fn-cat-intern-list-is-row-at-count
                  (w (fn-replay-composite-record w)))))))

; The groups the article a composite carries is filed in: the memberships
; the row the intern makes of W is charged (books/store-budget.lisp
; `fn-sbud-row-memberships' of an hstxa row), which the identity preflight
; charges at 320 each (books/store-capacity-vector.lisp
; `fn-cvec-statement-figure'; host/owner-host.lisp
; `fn-owner-identity-publication-verdict').  0 for any other event.
(defun fn-oii-publication-group-count (w)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (fn-stxa-p w) (fn-record-p (fn-replay-composite-record w)))
      (len (fn-record-groups (fn-replay-composite-record w)))
    0))

; The preflight's count is the interned row's: the held article inside the
; composite row is filed in exactly the groups the wire article names.
(defthm fn-oii-publication-group-count-is-the-rows
  (implies (and (fn-stxa-p w) (fn-record-p (fn-replay-composite-record w)))
           (equal (len (fn-record-groups
                        (fn-hstxa-held
                         (fn-oii-identity-row w keyring generation h))))
                  (fn-oii-publication-group-count w)))
  :hints (("Goal" :in-theory (e/d (fn-oii-identity-row fn-intern-row-at
                                   fn-oii-publication-group-count
                                   fn-hstxa-make fn-hstxa-held)
                                  (fn-stxa-p fn-record-p
                                   fn-replay-composite-record)))))

; THE ENTRY the host installs: the configured owner's identity prepare over
; the row at handle H under the owner's Store keyring and generation.
(defun fn-oii-ocfg-prepare-identity (oc w h)
  (declare (xargs :guard (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
                              (natp h))
                  :verify-guards nil))
  (let ((s (fn-own-store (fn-ocfg-owner oc))))
    (fn-ccar-ocfg-prepare-identity
     oc (fn-oii-identity-row w (fn-sn-keyring s) (fn-sn-keyring-generation s) h))))

; KEYSTONE (PRF-292): the entry at the arena's count is the owner's
; (:prepare-identity ROW) step over the interned row, on every owner the
; maintained relation admits.
(defthm fn-oii-ocfg-prepare-identity-is-intern-then-step
  (implies (fn-own-relation (fn-ocfg-owner oc))
           (let* ((s (fn-own-store (fn-ocfg-owner oc)))
                  (row (mv-nth 0 (fn-intern-event w (fn-sn-keyring s)
                                                  (fn-sn-keyring-generation s)
                                                  fn-arena))))
             (equal (fn-oii-ocfg-prepare-identity oc w (fn-arena-count fn-arena))
                    (fn-ocfg-step oc (list :store (list :prepare-identity row))
                                  fn-arena))))
  :hints (("Goal"
           :use ((:instance fn-ccar-ocfg-prepare-identity-is-ocfg-step-under-relation
                  (event (fn-oii-identity-row
                          w (fn-sn-keyring (fn-own-store (fn-ocfg-owner oc)))
                          (fn-sn-keyring-generation (fn-own-store (fn-ocfg-owner oc)))
                          (fn-arena-count fn-arena))))
                 (:instance fn-oii-identity-row-is-the-intern
                  (keyring (fn-sn-keyring (fn-own-store (fn-ocfg-owner oc))))
                  (generation (fn-sn-keyring-generation (fn-own-store (fn-ocfg-owner oc))))))
           :in-theory (union-theories '(fn-oii-ocfg-prepare-identity)
                                      (theory 'minimal-theory)))))
(in-theory (disable fn-oii-ocfg-prepare-identity fn-oii-identity-row))
