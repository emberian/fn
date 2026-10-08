; Evidence package for the checkpoint capture's intern (identity-binding
; critical claim, RULINGS "critical claims carry their evidence package"):
; books/store-checkpoint-fold.lisp, books/store-checkpoint-arena.lisp
; fn-scka-recover-from-checkpoint-is-full-recover and
; books/store-checkpoint-arena-writer.lisp fn-scka-next-checkpoint-is-capture.
;
; THE LOG: enroll (a keyring snapshot, generation 1), article A, rotate
; (a second snapshot, generation 2), article B.  A replay interns B under
; the rotated keyring; the checkpoint capture used to intern every row at
; keyring NIL and generation 0, so a checkpoint open and a replay open
; served different HDR :fn-verified generations for B.  Below:
;   - the premises are inhabited (positive witness, whole antecedent and
;     conclusion);
;   - the capture's rows are the host's worker's (fn-ssr-intern-step) and
;     differ from the old keyring-NIL/generation-0 rows on the articles;
;   - the wrong-answer witness: the old rows' checkpoint serves generation
;     0 where the replay serves 2 (must-fail teeth);
;   - hypothesis removal;
;   - the host-path model: the checkpoint FILE written from the live store
;     by the writer, loaded, and opened (no suffix and a suffix) serves the
;     replay open's verdicts.
(in-package "ACL2")
(include-book "must-fail-checked")
(include-book "store-checkpoint-arena-tests")
(include-book "../../books/owner-checkpoint-open")
(include-book "../../books/codec-attach")
(include-book "../../books/crypto-attach")
(include-book "../../books/defkeystone")
(include-book "../../books/reclaim-chunked-walk")

(defconst *scft-principal* (make-list 32 :initial-element 7))
(defconst *scft-keys1*
  (list (cons :ed25519 (make-list 32 :initial-element 11))
        (cons :ml-dsa-65 (make-list 1952 :initial-element 13))))
(defconst *scft-keys2*
  (list (cons :ed25519 (make-list 32 :initial-element 12))
        (cons :ml-dsa-65 (make-list 1952 :initial-element 14))))
(make-event `(defconst *scft-enroll*
               ',(fn-hl-enroll-event 0 0 0 1 *scft-principal* *scft-keys1* nil)))
(defconst *scft-a*
  (fn-record-make 1 1 1 "<before@example>" '(65 13 10) '("fn.test") "o1" "s1" "e1" 1 841000000))
(make-event `(defconst *scft-rotate*
               ',(fn-hl-enroll-event 2 2 2 2 *scft-principal* *scft-keys2* (list *scft-enroll*))))
(defconst *scft-b*
  (fn-record-make 3 3 3 "<after@example>" '(66 13 10) '("fn.test") "o2" "s2" "e2" 1 841000001))
(defconst *scft-ws* (list *scft-enroll* *scft-a*))
(defconst *scft-vs* (list *scft-rotate* *scft-b*))
(defconst *scft-log* (append *scft-ws* *scft-vs*))
(defconst *scft-id0* (fn-stxk-initial-context 0))
(defconst *scft-cfgs* (list *fn-cfg-default-record*))
(defconst *scft-frontier* 4)

; --- the two interns, run -----------------------------------------------------

; The host's worker over WS from the seed of ID, on an arena holding A0: the
; rows, and the arena's contents.
(defun scft-worker (ws id a0)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (out fn-arena)
      (let ((fn-arena (sckat-seal-all a0 fn-arena)))
        (mv-let (acc fn-arena)
          (fn-ssr-intern-step (fn-ssr-seed id) ws nil nil :resident nil fn-arena)
          (mv (list (fn-ssr-rows acc) (sckat-arena-list 0 fn-arena)) fn-arena)))
      out)))

; The OLD canonical rows: fn-intern-events at keyring NIL and generation 0,
; which is what fn-scka-canon-rows used to compute.
(defun scft-nil0-rows (ws)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (out fn-arena)
      (mv-let (rows fn-arena) (fn-intern-events ws nil 0 fn-arena) (mv rows fn-arena))
      out)))

; The verdicts the opened Store serves (what HDR :fn-verified answers from),
; the checkpoint open over ROWS and no suffix.
(defun scft-open-verdicts (rows)
  (declare (xargs :verify-guards nil))
  (fn-sn-verdicts
   (fn-sn-open-state
    (fn-sco-finalize (fn-sco-capture *scft-cfgs* rows) *scft-cfgs* *scft-frontier*))))
(defun scft-replay-verdicts (rows)
  (declare (xargs :verify-guards nil))
  (fn-sn-verdicts (fn-sn-open-state (fn-cpo-open-observed *scft-cfgs* *scft-frontier* rows))))

(make-event `(defconst *scft-replay* ',(car (scft-worker *scft-log* *scft-id0* nil))))
(make-event `(defconst *scft-canon* ',(fn-scka-intern-at *scft-log* *scft-id0* 0)))
(make-event `(defconst *scft-old* ',(scft-nil0-rows *scft-log*)))

; --- 1. positive witness: the antecedent of the keystone, whole -----------------

(assert-event
 (and (true-listp *scft-ws*)
      (not (equal (fn-scka-intern-at *scft-ws* *scft-id0* 0) :bad))
      (not (equal (fn-scka-intern-at (append *scft-ws* *scft-vs*) *scft-id0* 0) :bad))
      ;; the conclusion: the extension and the arena
      (let ((r (sckat-recover-pair *scft-ws* *scft-vs*)))
        (and (equal (car r) (caddr r))
             (equal (cadr r) (cadddr r))
             (not (eq (car r) :bad))
             (equal (car r) (fn-sco-capture *sckat-configs* *scft-canon*))))))

; --- 2. the capture's rows are the host worker's, and are not the old rows ------

(assert-event
 (and (equal *scft-canon* *scft-replay*)
      (not (equal *scft-canon* *scft-old*))
      ;; the keyring snapshots agree, the ARTICLES differ
      (equal (nth 0 *scft-canon*) (nth 0 *scft-old*))
      (equal (nth 2 *scft-canon*) (nth 2 *scft-old*))
      (not (equal (nth 1 *scft-canon*) (nth 1 *scft-old*)))
      (not (equal (nth 3 *scft-canon*) (nth 3 *scft-old*)))
      ;; the arena the worker builds is the payloads
      (equal (cadr (scft-worker *scft-log* *scft-id0* nil)) (fn-scka-payloads *scft-log*))))

; --- 3. what the opened Store serves: HDR :fn-verified --------------------------

(assert-event
 (let ((replay (scft-replay-verdicts *scft-replay*))
       (ckpt (scft-open-verdicts *scft-canon*)))
   (and (equal ckpt replay)
        (equal (cdr (assoc-equal "<after@example>" replay)) '(:unverified :malformed 2))
        (equal (cdr (assoc-equal "<before@example>" replay)) '(:unverified :malformed 1)))))

; The wrong-answer witness, on dev before this change: the checkpoint of the
; old keyring-NIL/generation-0 rows serves generation 0 for both articles
; where the replay serves 1 and 2.
(assert-event
 (let ((replay (scft-replay-verdicts *scft-replay*))
       (old (scft-open-verdicts *scft-old*)))
   (and (not (equal old replay))
        (equal (cdr (assoc-equal "<after@example>" old)) '(:unverified :malformed 0))
        (equal (cdr (assoc-equal "<before@example>" old)) '(:unverified :malformed 0)))))

; The must-fail teeth: the old claim "the canonical rows of the log are the
; keyring-NIL/generation-0 intern" is false.
(must-fail-checked
 (defthm scft-old-canonical-form
   (equal (fn-scka-intern-at *scft-log* *scft-id0* 0) (scft-nil0-rows *scft-log*))
   :rule-classes nil))

; ... and a checkpoint of the old rows does not open to the replay's store: the
; open keystone, with the capture of the old rows in place of the fold's.
(defun scft-old-pair (ws vs)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (out fn-arena)
      (let ((fn-arena (sckat-seal-all (fn-scka-payloads ws) fn-arena)))
        (mv-let (lhs fn-arena)
          (fn-scka-recover-rows (fn-sco-capture *sckat-configs* (scft-nil0-rows ws)) *sckat-configs* vs
                                fn-arena)
          (mv-let (full fn-arena) (sckat-full-in (append ws vs) fn-arena)
            (mv (list lhs (car full)) fn-arena))))
      out)))
(assert-event
 (let ((r (scft-old-pair *scft-ws* *scft-vs*)))
   (and (not (eq (cadr r) :bad))
        (not (equal (car r) (cadr r))))))

; --- 4. the identity seed is a premise of the suffix intern ---------------------

; The suffix interned from the seed of the PREFIX's identity (the host's
; fn-store-statement-replay-seed) is the replay's; from the initial context
; (a checkpoint's suffix seeded as a full replay) it is not.
(assert-event
 (let* ((rows (fn-scka-intern-at *scft-ws* *scft-id0* 0))
        (id (fn-replay-identity-loop rows *scft-id0*))
        (h (len (fn-scka-payloads *scft-ws*))))
   (and (equal (append rows (fn-scka-intern-at *scft-vs* id h)) *scft-canon*)
        (not (equal (fn-scka-intern-at *scft-vs* *scft-id0* h) (fn-scka-intern-at *scft-vs* id h))))))

; The state after a prefix is the seed of its identity (fn-scka-fold-at-seed).
(assert-event
 (let* ((r (fn-scka-fold-at (fn-ssr-seed *scft-id0*) *scft-ws* 0)))
   (and (not (eq r :bad))
        (equal (fn-scka-ctx r)
               (fn-ssr-seed (fn-replay-identity-loop (fn-ssr-rows r) *scft-id0*)))
        (not (equal (fn-scka-ctx r) (fn-ssr-seed *scft-id0*))))))

; --- 5. hypothesis removal ------------------------------------------------------

; The rows result has no hypothesis on the suffix: a refused event after the
; rotation refuses the open on both sides (the arenas agree here too: both hold
; the prefix's payload).
(assert-event
 (let* ((vs (list *scft-rotate* 'not-an-event))
        (r (sckat-recover-pair *scft-ws* vs)))
   (and (equal (fn-scka-intern-at (append *scft-ws* vs) *scft-id0* 0) :bad)
        (eq (car r) :bad) (eq (caddr r) :bad)
        (equal (cadr r) (cadddr r)))))

; Without "the prefix's own fold is not refused" there is no checkpoint: its
; canonical rows are :bad, the capture of them is the empty one, and the open
; from it extends where the full recover refuses.
(assert-event
 (let* ((ws (list 'not-an-event))
        (r (sckat-recover-pair ws (list *scft-enroll*))))
   (and (equal (fn-scka-intern-at ws *scft-id0* 0) :bad)
        (not (eq (car r) :bad))
        (eq (caddr r) :bad))))

; Without "WS is a true list" the append drops the dotted tail and the folds
; of WS and of WS ++ VS differ.
(assert-event
 (with-guard-checking :none
   (let ((ws (cons *scft-enroll* 7)))
     (and (not (true-listp ws))
          (equal (fn-scka-intern-at ws *scft-id0* 0) :bad)
          (not (equal (fn-scka-intern-at (append ws (list *scft-a*)) *scft-id0* 0) :bad))))))

; --- 6. the owner installed from the checkpoint is the owner the replay installs

(assert-event
 (let ((full (fn-ock-recover-full *scft-cfgs* *scft-frontier* *scft-replay* 4))
       (ck (fn-ock-recover-extended
            (fn-sco-extend (fn-sco-capture *scft-cfgs* (fn-scka-intern-at *scft-ws* *scft-id0* 0))
                           *scft-cfgs* (fn-scka-intern-at *scft-vs*
                                         (fn-replay-identity-loop
                                          (fn-scka-intern-at *scft-ws* *scft-id0* 0) *scft-id0*)
                                         (len (fn-scka-payloads *scft-ws*))))
            *scft-cfgs* *scft-frontier* 4)))
   (and (not (equal full :fault))
        (equal ck full))))

; --- 7. the host path, modelled: the file the writer wrote -----------------------

; The live store is the host worker's rows over the log (a replay), the
; writer writes the checkpoint file from them (the arena run, then the tables
; of the capture of the canonical rows), the load reads the file back through
; the host's plan shape and the open runs over a suffix.  (OPENED VERDICTS)
; of the opened Store, and the replay's.
(defun scft-file-open (ws-live vs-suffix)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (out fn-arena)
      (with-local-stobj fn-octets
        (mv-let (out fn-arena fn-octets)
          (mv-let (acc fn-arena)
            (fn-ssr-intern-step (fn-ssr-seed *scft-id0*) ws-live nil nil :resident nil fn-arena)
            (let ((rows (fn-ssr-rows acc)))
              (mv-let (written fn-octets)
                (sckat-write-in rows nil 1 fn-arena fn-octets)
                (let ((file (append (nth 3 written) (nth 5 written))))
                  (mv-let (lo fn-arena fn-octets)
                    (sckat-load-open-in file vs-suffix fn-arena fn-octets)
                    (mv (list (nth 0 lo) (nth 2 lo)) fn-arena fn-octets))))))
          (mv out fn-arena)))
      out)))

(make-event `(defconst *scft-file-all* ',(scft-file-open *scft-log* nil)))
(make-event `(defconst *scft-file-split* ',(scft-file-open *scft-ws* *scft-vs*)))

; The verdicts the opened Store serves are its rows' (fn-sn-update-replayed:
; fn-sn-row-verdicts of the records), so HDR :fn-verified follows the rows the
; file loads to.
(assert-event
 (let ((opened-all (cadr *scft-file-all*)))
   (and (eq (car (car *scft-file-all*)) :ok)
        (not (eq opened-all :bad))
        ;; the whole log checkpointed after the rotation, opened with no suffix
        (equal opened-all (fn-sco-capture *sckat-configs* *scft-canon*))
        (equal (fn-sn-row-verdicts (fn-sco-records opened-all))
               (scft-replay-verdicts *scft-replay*)))))

(assert-event
 (let ((opened-split (cadr *scft-file-split*)))
   (and (eq (car (car *scft-file-split*)) :ok)
        ;; checkpointed before the rotation, the rotation and article B replayed
        ;; over the loaded checkpoint
        (equal opened-split (fn-sco-capture *sckat-configs* *scft-canon*))
        (equal (cdr (assoc-equal "<after@example>"
                                 (fn-sn-row-verdicts (fn-sco-records opened-split))))
               '(:unverified :malformed 2)))))

; --- 8. the keystone's teeth (Ruling 22 evidence package) -------------------------

; Native rendering of the claim's conclusion on the live arena; defteeth
; proves the unconditional equality before it executes any witness or removal.
(defun scft-open-conclusion (configs ws vs fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (e fn-arena)
    (fn-scka-recover-rows
     (fn-sco-capture configs (fn-scka-intern-at ws (fn-stxk-initial-context 0) 0))
     configs vs fn-arena)
    (mv (equal e (car (fn-scka-full-recover configs (append ws vs)))) fn-arena)))

(defun scft-open-mutant (configs ws vs fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (e fn-arena)
    (fn-scka-recover-rows
     (fn-sco-capture configs (fn-scka-intern-at ws (fn-stxk-initial-context 0) 0))
     configs vs fn-arena)
    (mv (equal e (fn-sco-extend (fn-sco-capture configs nil) configs
                                (scft-nil0-rows (append ws vs))))
        fn-arena)))

(defteeth fn-scka-recover-from-checkpoint-is-full-recover
  :subject fn-scka-recover-rows
  :claim
  (((prefix-folds (not (equal (fn-scka-intern-at ws (fn-stxk-initial-context 0) 0) :bad)))
    (arena-count (equal (fn-arena-count fn-arena) (len (fn-scka-payloads ws)))))
   (equal (mv-nth 0 (fn-scka-recover-rows
                     (fn-sco-capture configs (fn-scka-intern-at ws (fn-stxk-initial-context 0) 0))
                     configs vs fn-arena))
          (car (fn-scka-full-recover configs (append ws vs)))))
  :witness ((configs *scft-cfgs*) (ws *scft-ws*) (vs *scft-vs*)
            (loaded (fn-scka-payloads *scft-ws*)))
  :stobjs ((fn-arena (sckat-seal-all loaded fn-arena)))
  :stobj-checks
  (((equal (mv-nth 0 (fn-scka-recover-rows
                      (fn-sco-capture configs (fn-scka-intern-at ws (fn-stxk-initial-context 0) 0))
                      configs vs fn-arena))
           (car (fn-scka-full-recover configs (append ws vs))))
    (scft-open-conclusion configs ws vs fn-arena)
    :hints (("Goal" :in-theory '(scft-open-conclusion))))
   ((equal (mv-nth 0 (fn-scka-recover-rows
                      (fn-sco-capture configs (fn-scka-intern-at ws (fn-stxk-initial-context 0) 0))
                      configs vs fn-arena))
           (fn-sco-extend (fn-sco-capture configs nil) configs (scft-nil0-rows (append ws vs))))
    (scft-open-mutant configs ws vs fn-arena)
    :hints (("Goal" :in-theory '(scft-open-mutant)))))
  :breaks
  ((prefix-folds ((ws (list 'not-an-event)) (loaded nil) (vs (list *scft-enroll*))))
   (arena-count ((loaded nil))))
  :mutations
  ((old-nil-zero-intern
    (:conclusion (equal (mv-nth 0 (fn-scka-recover-rows
                                   (fn-sco-capture configs (fn-scka-intern-at ws (fn-stxk-initial-context 0) 0))
                                   configs vs fn-arena))
                        (fn-sco-extend (fn-sco-capture configs nil) configs (scft-nil0-rows (append ws vs)))))
    () :fault "The capture interns every row at keyring NIL and generation 0, as before this change.")))

(defteeth-check (fn-scka-recover-from-checkpoint-is-full-recover))

; The live arena the writer and the chunked walk read: the host worker's
; interning of the log (handles are the rows' own).
(defun scft-live-arena (fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (acc fn-arena)
    (fn-ssr-intern-step (fn-ssr-seed (fn-stxk-initial-context 0)) *scft-log* nil nil :resident nil
                        fn-arena)
    (declare (ignore acc))
    fn-arena))

(defteeth fn-scka-next-checkpoint-is-capture
  :subject fn-scka-next-checkpoint
  :claim
  (((within (<= plen (len records)))
    (canon-ok (not (equal (fn-scka-canon-rows records fn-arena 0 (fn-stxk-initial-context 0))
                          :bad))))
   (equal (fn-scka-next-checkpoint
           (fn-sco-capture configs
                           (fn-scka-canon-rows (take plen records) fn-arena 0
                                               (fn-stxk-initial-context 0)))
           (len (fn-scka-canon-payloads (take plen records) fn-arena))
           configs records fn-arena)
          (fn-sco-capture configs
                          (fn-scka-canon-rows records fn-arena 0 (fn-stxk-initial-context 0)))))
  :witness ((configs *scft-cfgs*) (plen 2) (records *scft-replay*))
  :stobjs ((fn-arena (scft-live-arena fn-arena)))
  :breaks
  ((within ((plen 5)))
   (canon-ok ((plen 1) (records (list (car *scft-replay*) (nth 3 *scft-replay*))))))
  :mutations
  ((old-nil-zero-intern
    (:conclusion (equal (fn-scka-next-checkpoint
                         (fn-sco-capture configs
                                         (fn-scka-canon-rows (take plen records) fn-arena 0
                                                             (fn-stxk-initial-context 0)))
                         (len (fn-scka-canon-payloads (take plen records) fn-arena))
                         configs records fn-arena)
                        (fn-sco-capture configs (scft-nil0-rows (fn-rows-wire-of records fn-arena)))))
    () :fault "The capture interns every row at keyring NIL and generation 0, as before this change.")))

(defteeth fn-rcw-canon-acc-steps-is-the-checkpoint-capture
  :subject fn-rcw-canon-acc-step
  :claim
  (let ((r (fn-rcw-canon-acc-steps (fn-rcw-acc-init configs) configs chunks 0 fn-arena))
        (all (fn-scka-canon-rows (fn-rcw-concat chunks) fn-arena 0 (fn-stxk-initial-context 0))))
    (()
     (and (equal (eq r :bad) (eq all :bad))
          (implies (not (eq r :bad))
                   (equal (fn-rcw-acc-finish (car r)) (fn-sco-capture configs all))))))
  :witness ((configs *scft-cfgs*)
            (chunks (list (take 2 *scft-replay*) (nthcdr 2 *scft-replay*))))
  :stobjs ((fn-arena (scft-live-arena fn-arena)))
  :mutations
  ((old-nil-zero-intern
    (:conclusion
     (let ((r (fn-rcw-canon-acc-steps (fn-rcw-acc-init configs) configs chunks 0 fn-arena)))
       (equal (fn-rcw-acc-finish (car r))
              (fn-sco-capture configs (scft-nil0-rows (fn-rows-wire-of (fn-rcw-concat chunks)
                                                                       fn-arena))))))
    () :fault "The chunked capture interns every row at keyring NIL and generation 0, as before this change.")))

(defteeth-check (fn-scka-next-checkpoint-is-capture fn-rcw-canon-acc-steps-is-the-checkpoint-capture))
