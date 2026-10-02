; fn: THE BP RECEIPT AFTER A CRASH OF THE RECORD LOG (PKT-217 restated,
; coordinator decision 2026-10-01).  Prefix fn-brlc-.
;
; The receipt theorem fn-bpr-live-receipt-regenerated-after-restart
; (books/bp-receiver-evolving-store-invariants.lisp) and its host-open twin
; (books/store-open-node-bridge.lisp) take the crash from the per-file model:
; fn-sf-crash-imagep over (fn-sn-files final), the format-9 frontier and
; transaction files.  Format 10 stores the history as ONE record log; what a
; crash leaves is the log's crash model, the one the recovery refinement
; composes (books/recovery-refinement.lisp, PRF-1212):
;
;   - every crash point of the log's served programs is a related state
;     (fn-lgk-relp BS KS), and every admissible crash image of it recovers
;     COMMITTED followed by a PREFIX of the batch in flight, under
;     A-CRYPTO-TRAILER's premise on the tear
;     (fn-rr-log-crash-image-recovers-a-tree-sequence-member, over
;     books/store-log-kernel.lisp fn-lgk-crash-of-related-state-is-a-prefix);
;   - THE HOST'S FULL-REPLAY OPEN over what the recovery holds
;     (host/native/io.lisp fnn-recover-log, full replay: the records go to
;     fnn-recover-log-stream-take / -flush in chunks ACL2 closes):
;       begin   fnn-bridge-recover-begin: the replay seeded with
;               (fn-ssr-seed (fn-stxk-initial-context 0));
;       decode  per chunk fn-lgb-decode-next, whose first value is
;               fn-srs-decode (its :logic; fn-store-decode-records on the
;               pack path is fn-srs-decode too);
;       intern  per chunk fnn-bridge-recover-step: fn-ssr-intern-step
;               :resident, the statement keyring, generation and identity
;               cursor carried between records (or -extents / -lz, which
;               equal :resident under fn-arena-p and a faithful placement:
;               fn-ssr-extent-step-refines-resident,
;               fn-ssr-lz-step-refines-resident);
;       open    fnn-bridge-recover-end: fn-store-sn-recover-rows over
;               (fn-ssr-rows ACC), which calls fn-rii-sco-extend-open on the
;               empty capture, and installs (fn-sn-open-state (cadr
;               CLASSIFIED)) through fn-store-sn-open-classified.
;     This book models exactly that chain: fn-brlc-rows is the seeded
;     fn-ssr-intern-step over the decode (fn-brlc-chunks-are-one-step: any
;     chunking gives the same rows), fn-brlc-host-classified is the host's
;     fn-rii-sco-extend-open, and fn-brlc-host-open-is-the-observed-open
;     equates the opened value with fn-cpo-open-observed when it is a Store
;     (fn-rii-sco-extend-open-is-extend-then-open,
;     fn-rii-classified-open-is-classified-open, fn-rii-sco-extend-is-sco-extend,
;     fn-sco-store-open-of-extended-capture with PREFIX = NIL).  The
;     checkpoint opens (fnn-recover-log-from-state-checkpoint, -from-log-
;     checkpoint) are not covered here.
;
; THE PREMISE THAT REPLACES THE IMAGE PREDICATE.  The receiver acts only on
; acknowledged Store records: the live Store's history is a prefix of the
; rows the open makes of the log's ACKNOWLEDGED records (the first ACKED of
; COMMITTED, R's fourth conjunct).  A record still in flight may be lost by a
; crash and the log model says so; a receipt that depended on one could not
; be regenerated, and the MUTATION in the test book is exactly that.
;
; KEYSTONE fn-brlc-receipt-regenerated-after-log-crash: from a receiver whose
; state is the replay of its journal, run any live trace; crash the log at
; any related state to any admissible image; decode and intern what the
; log's recovery holds; open as the host opens; run the recovery barriers to
; :ready; then fn-bprj-install's replay of the journal is the live receiver
; state and the receipt ADU is byte-identical.
;
; NOT claimed here, named (OPEN):
;   - THE PREMISE'S PRODUCER.  Nothing yet proves, for a log the host wrote,
;     that the live Store history is a prefix of the rows of the acknowledged
;     records: that every row the Store holds came from a record the log
;     fenced and the owner acknowledged (fn-lgk-finish-one), in order.  It is
;     the join between the owner's commit path and the log kernel.
;   - the open's SUCCESS is a hypothesis (fn-sn-open-okp of the host open over
;     the recovered rows): under the per-file model it followed from the image
;     predicate; under the log it is the store instance's obligation
;     (books/recovery-refinement-store.lisp, PRF-1212/PRF-1213, written, not
;     admitted).  A refused open serves nothing.
;   - fn-sonb-configured-before-eventsp: a store reconfigured after an event
;     needs the receipt over fn-cst-relation (PKT-217's first follow-up; the
;     fn-snrt-run preservation stack at the configured relation).
;   - the arena: as in the per-file theorem, the replay reads payloads through
;     one FN-ARENA; the open's intern starts from ARENA0.
(in-package "ACL2")
(include-book "store-open-node-bridge")
(include-book "recovery-refinement")
(include-book "statement-recover-stream")
(include-book "replay-identity-index")
(include-book "owner-checkpoint-open")

; -----------------------------------------------------------------------------
; 1. The rows the host's open makes of a list of log records: the seeded
;    statement-context replay over their decode, oldest first.

(defun fn-brlc-seed ()
  (declare (xargs :verify-guards nil))
  (fn-ssr-seed (fn-stxk-initial-context 0)))

; Logical (defun-nx): the host runs fn-ssr-intern-step on the live arena
; stobj; these name its value from an arbitrary starting arena.
(defun-nx fn-brlc-intern (octet-records arena0)
  (fn-ssr-intern-step (fn-brlc-seed) (fn-srs-decode octet-records) nil nil :resident nil arena0))

(defun-nx fn-brlc-rows (octet-records arena0)
  (fn-ssr-rows (mv-nth 0 (fn-brlc-intern octet-records arena0))))

(defun-nx fn-brlc-decodedp (octet-records arena0)
  (not (eq (mv-nth 0 (fn-brlc-intern octet-records arena0)) :bad)))

; The host's chunks (fnn-recover-log-stream-flush per chunk): each chunk
; decoded, then interned from the accumulator so far.
(defun fn-brlc-chunks-intern (acc chunks fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (if (atom chunks)
      (mv acc fn-arena)
    (mv-let (acc fn-arena)
      (fn-ssr-intern-step acc (fn-srs-decode (car chunks)) nil nil :resident nil fn-arena)
      (fn-brlc-chunks-intern acc (cdr chunks) fn-arena))))

(defun fn-brlc-flatten (chunks)
  (declare (xargs :guard (true-list-listp chunks)))
  (if (atom chunks) nil (append (car chunks) (fn-brlc-flatten (cdr chunks)))))

(local
 (defthm fn-brlc-ssr-of-bad
   (equal (fn-ssr-intern-step :bad ws rs ps mode dicts arena) (mv :bad arena))
   :hints (("Goal" :in-theory (enable fn-ssr-intern-step)))))

(local
 (defthm fn-brlc-ssr-of-nil
   (equal (fn-ssr-intern-step acc nil rs ps mode dicts arena) (mv acc arena))
   :hints (("Goal" :in-theory (enable fn-ssr-intern-step)))))

(local
 (defthm fn-brlc-ssr-of-bad-ws
   (equal (fn-ssr-intern-step acc :bad rs ps mode dicts arena) (mv :bad arena))
   :hints (("Goal" :in-theory (enable fn-ssr-intern-step)))))

(local
 (defthm fn-brlc-srs-decode-atom
   (implies (and (not (equal (fn-srs-decode x) :bad))
                 (not (consp (fn-srs-decode x))))
            (equal (fn-srs-decode x) nil))
   :hints (("Goal" :use fn-srs-decode-true-listp :in-theory (disable fn-srs-decode)))))

; Any chunking of the records gives the rows of the one step over all of
; them (fn-srs-decode-of-append, fn-ssr-resident-step-of-append).
(defthm fn-brlc-chunks-are-one-step
  (implies (true-list-listp chunks)
           (equal (mv-nth 0 (fn-brlc-chunks-intern acc chunks arena))
                  (mv-nth 0 (fn-ssr-intern-step acc (fn-srs-decode (fn-brlc-flatten chunks))
                                                nil nil :resident nil arena))))
  :hints (("Goal" :induct (fn-brlc-chunks-intern acc chunks arena)
           :in-theory (e/d (fn-brlc-chunks-intern)
                           (fn-ssr-intern-step fn-srs-decode)))
          ("Subgoal *1/2" :use ((:instance fn-srs-decode-of-append
                                           (a (car chunks))
                                           (b (fn-brlc-flatten (cdr chunks))))
                                (:instance fn-ssr-resident-step-of-append
                                           (a (fn-srs-decode (car chunks)))
                                           (b (fn-srs-decode (fn-brlc-flatten (cdr chunks))))
                                           (dicts nil) (fn-arena arena))))))

; -----------------------------------------------------------------------------
; 2. The rows of a prefix are a prefix of the rows, when the whole decodes.

(defun fn-brlc-tailp (x y)
  (declare (xargs :guard t))
  (if (equal x y) t (and (consp y) (fn-brlc-tailp x (cdr y)))))

(local
 (defthm fn-brlc-tailp-of-cons
   (implies (fn-brlc-tailp (cons r x) y) (fn-brlc-tailp x y))))

(local
 (defthm fn-brlc-ssr-at-0-of-publish
   (equal (fn-ssr-at 0 (fn-ssr-publish acc row wire identity))
          (cons row (fn-ssr-at 0 acc)))
   :hints (("Goal" :in-theory (enable fn-ssr-publish fn-ssr-state fn-ssr-at)))))

; Each published row is consed onto the accumulator: what was there stays.
(defthm fn-brlc-ssr-rows-grow
  (implies (not (eq (mv-nth 0 (fn-ssr-intern-step acc ws nil nil :resident dicts arena)) :bad))
           (fn-brlc-tailp (fn-ssr-at 0 acc)
                          (fn-ssr-at 0 (mv-nth 0 (fn-ssr-intern-step acc ws nil nil :resident
                                                                     dicts arena)))))
  :hints (("Goal" :induct (fn-ssr-intern-step acc ws nil nil :resident dicts arena)
           :in-theory (e/d (fn-ssr-intern-step)
                           (fn-intern-event fn-arx-intern-event fn-lzr-intern-event
                            fn-replay-identity-step fn-ssr-publish fn-ssr-at
                            fn-stxk-context-kind)))))

(local
 (defthm fn-brlc-rev-onto-of-append-acc
   (equal (fn-ag-rev-onto y (append a acc)) (append (fn-ag-rev-onto y a) acc))))

(local
 (defthm fn-brlc-rev-onto-acc
   (implies (syntaxp (not (equal acc ''nil)))
            (equal (fn-ag-rev-onto y acc) (append (fn-ag-rev-onto y nil) acc)))
   :hints (("Goal" :use ((:instance fn-brlc-rev-onto-of-append-acc (a nil)))
            :in-theory (disable fn-brlc-rev-onto-of-append-acc)))))

(local
 (defthm fn-brlc-prefixp-of-append-right
   (implies (fn-sf-prefixp p q) (fn-sf-prefixp p (append q r)))
   :hints (("Goal" :in-theory (enable fn-sf-prefixp)))))

(defthm fn-brlc-tailp-reverses-to-prefixp
  (implies (fn-brlc-tailp x y)
           (fn-sf-prefixp (fn-ag-rev-onto x nil) (fn-ag-rev-onto y nil)))
  :hints (("Goal" :induct (fn-brlc-tailp x y))))

(defthm fn-brlc-rows-of-prefix-is-a-prefix
  (implies (and (true-listp a)
                (fn-brlc-decodedp (append a b) arena0))
           (and (fn-brlc-decodedp a arena0)
                (fn-sf-prefixp (fn-brlc-rows a arena0) (fn-brlc-rows (append a b) arena0))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-srs-decode-of-append)
                 (:instance fn-ssr-resident-step-of-append
                            (acc (fn-brlc-seed)) (a (fn-srs-decode a)) (b (fn-srs-decode b))
                            (dicts nil) (fn-arena arena0))
                 (:instance fn-brlc-ssr-rows-grow
                            (acc (mv-nth 0 (fn-ssr-intern-step (fn-brlc-seed) (fn-srs-decode a)
                                                               nil nil :resident nil arena0)))
                            (ws (fn-srs-decode b)) (dicts nil)
                            (arena (mv-nth 1 (fn-ssr-intern-step (fn-brlc-seed) (fn-srs-decode a)
                                                                 nil nil :resident nil arena0)))))
           :in-theory (e/d (fn-brlc-rows fn-brlc-decodedp fn-brlc-intern fn-ssr-rows)
                           (fn-ssr-intern-step fn-srs-decode fn-srs-decode-of-append
                            fn-ssr-resident-step-of-append fn-brlc-ssr-rows-grow
                            fn-brlc-seed fn-ssr-at)))))

; -----------------------------------------------------------------------------
; 2b. The host's open over the rows: fn-store-sn-recover-rows calls
;     fn-rii-sco-extend-open on the empty capture and installs the state of
;     the CLASSIFIED answer's second element.  When that element is a Store it
;     is the observed open.

(defun-nx fn-brlc-host-classified (configs frontier rows)
  (cadr (fn-rii-sco-extend-open (fn-sco-capture configs nil) configs rows frontier)))

(local
 (defthm fn-brlc-refusal-is-no-store
   (implies (fn-sopc-open-refusal e)
            (not (fn-sn-open-okp (cadr (fn-sopc-open-refusal e)))))
   :hints (("Goal" :in-theory (enable fn-sopc-open-refusal fn-sn-open-okp fn-sn-open-shapep)))))

(defthm fn-brlc-host-open-is-the-observed-open
  (implies (fn-sn-open-okp (cadr (fn-brlc-host-classified configs frontier rows)))
           (equal (cadr (fn-brlc-host-classified configs frontier rows))
                  (fn-cpo-open-observed configs frontier rows)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-sco-store-open-of-extended-capture
                            (prefix nil) (suffix rows)))
           :in-theory (e/d (fn-brlc-host-classified fn-rii-sco-extend-open-is-extend-then-open
                            fn-rii-classified-open-is-classified-open fn-rii-sco-extend-is-sco-extend
                            fn-sopc-classified-open)
                           (fn-rii-sco-extend-open fn-rii-classified-open fn-rii-sco-extend
                            fn-sco-store-open fn-sco-extend fn-sco-capture fn-cpo-open-observed
                            fn-sco-store-open-of-extended-capture)))))

; A Store opens only over rows that decoded: the rows of an undecodable
; list are :bad, and an :ok open's records are its events
; (fn-cpo-open-success-exact-image), a true list in any Store state.  So the
; decode is no hypothesis of the keystone (removed after this proof).
(defthm fn-brlc-open-ok-implies-decoded
  (implies (fn-sn-open-okp (cadr (fn-brlc-host-classified configs frontier
                                                          (fn-brlc-rows rec arena0))))
           (fn-brlc-decodedp rec arena0))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-brlc-host-open-is-the-observed-open
                            (rows (fn-brlc-rows rec arena0)))
                 (:instance fn-cpo-open-success-exact-image
                            (events (fn-brlc-rows rec arena0)))
                 (:instance fn-sf-state-records-are-true-list
                            (s (fn-sn-files (fn-sn-open-state
                                             (fn-cpo-open-observed configs frontier
                                                                   (fn-brlc-rows rec arena0)))))))
           :in-theory (e/d (fn-brlc-decodedp fn-brlc-rows fn-ssr-rows fn-sn-open-okp fn-sn-statep)
                           (fn-brlc-host-open-is-the-observed-open
                            fn-sf-state-records-are-true-list fn-brlc-host-classified
                            fn-cpo-open-observed fn-brlc-intern))))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; 3. The log's half: the acknowledged records are a prefix of what the
;    recovery holds, at every admissible crash image of a related state.

(local
 (defthm fn-brlc-relp-acked-facts
   (implies (fn-lgk-relp bs ks ino genesis max)
            (and (true-listp (fn-lgk-committed ks))
                 (natp (fn-lgk-acked ks))
                 (<= (fn-lgk-acked ks) (len (fn-lgk-committed ks)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-lgk-relp fn-lgk-content-okp)
                                   (fn-lg-scan fn-lg-scan-last fn-lg-log fn-lg-recordsp fn-bs-take
                                    fn-lg-zerosp fn-frame-digestp fn-bs-durable-content))))))

(local
 (defthm fn-brlc-take-append-nthcdr
   (implies (and (natp n) (<= n (len x)))
            (equal (append (take n x) (nthcdr n x)) x))
   :hints (("Goal" :induct (take n x)))))

(local
 (defthm fn-brlc-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(local
 (defthm fn-brlc-true-listp-take
   (true-listp (take n x))))

(local
 (defthm fn-brlc-split
   (implies (and (equal r (append c p)) (equal (append x y) c))
            (equal r (append x (append y p))))
   :rule-classes nil))

(defthm fn-brlc-recovered-is-the-acknowledged-prefix-and-more
  (let ((recovered (fn-rr-recovered-records image ino genesis (fn-bs-unit bs) max next-txid))
        (acked (take (fn-lgk-acked ks) (fn-lgk-committed ks))))
    (implies (and (fn-lgk-relp bs ks ino genesis max)
                  (fn-bs-crash-imagep bs image)
                  (fn-lg-platform-tears-p
                   (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content image ino))
                   (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs)))
             (and (true-listp acked)
                  (equal recovered
                         (append acked
                                 (append (nthcdr (fn-lgk-acked ks) (fn-lgk-committed ks))
                                         (nthcdr (len (fn-lgk-committed ks)) recovered)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-rr-log-crash-image-recovers-a-tree-sequence-member)
                 (:instance fn-brlc-relp-acked-facts)
                 (:instance fn-brlc-take-append-nthcdr
                            (n (fn-lgk-acked ks)) (x (fn-lgk-committed ks)))
                 (:instance fn-brlc-split
                            (r (fn-rr-recovered-records image ino genesis (fn-bs-unit bs)
                                                        max next-txid))
                            (c (fn-lgk-committed ks))
                            (p (nthcdr (len (fn-lgk-committed ks))
                                       (fn-rr-recovered-records image ino genesis (fn-bs-unit bs)
                                                                max next-txid)))
                            (x (take (fn-lgk-acked ks) (fn-lgk-committed ks)))
                            (y (nthcdr (fn-lgk-acked ks) (fn-lgk-committed ks)))))
           :in-theory (union-theories '(fn-rr-tree-sequence-memberp fn-brlc-true-listp-take)
                                      (theory 'minimal-theory)))))

(defthm fn-brlc-acknowledged-rows-are-a-prefix-of-the-recovered-rows
  (let ((recovered (fn-rr-recovered-records image ino genesis (fn-bs-unit bs) max next-txid)))
    (implies (and (fn-lgk-relp bs ks ino genesis max)
                  (fn-bs-crash-imagep bs image)
                  (fn-lg-platform-tears-p
                   (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content image ino))
                   (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs))
                  (fn-brlc-decodedp recovered arena0))
             (fn-sf-prefixp (fn-brlc-rows (take (fn-lgk-acked ks) (fn-lgk-committed ks)) arena0)
                            (fn-brlc-rows recovered arena0))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-brlc-recovered-is-the-acknowledged-prefix-and-more)
                 (:instance fn-brlc-rows-of-prefix-is-a-prefix
                            (a (take (fn-lgk-acked ks) (fn-lgk-committed ks)))
                            (b (append (nthcdr (fn-lgk-acked ks) (fn-lgk-committed ks))
                                       (nthcdr (len (fn-lgk-committed ks))
                                               (fn-rr-recovered-records image ino genesis
                                                                        (fn-bs-unit bs) max
                                                                        next-txid))))))
           :in-theory (union-theories '() (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; 4. THE KEYSTONE.

(defthm fn-brlc-receipt-regenerated-after-log-crash
  (let* ((final (fn-bpr-live-run live events fn-arena))
         (recovered (fn-rr-recovered-records image ino genesis (fn-bs-unit bs) max next-txid))
         (opened (cadr (fn-brlc-host-classified configs frontier
                                                (fn-brlc-rows recovered arena0))))
         (probe (fn-snrt-run (fn-sn-open-state opened) recovery-events))
         (installed (fn-bpr-live-install probe (caddr final) fn-arena)))
    (implies (and (fn-csi-full-relationp (car live))
                  (equal (fn-bprr-replay (car live) (caddr live) fn-arena) (list t (cadr live)))
                  (fn-lgk-relp bs ks ino genesis max)
                  (fn-bs-crash-imagep bs image)
                  (fn-lg-platform-tears-p
                   (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content image ino))
                   (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs))
                  (fn-sf-prefixp (fn-bprv-history (car final))
                                 (fn-brlc-rows (take (fn-lgk-acked ks) (fn-lgk-committed ks))
                                               arena0))
                  (fn-sonb-configured-before-eventsp configs)
                  (fn-sn-open-okp opened)
                  (equal (fn-bprv-phase probe) :ready))
             (and (equal (cadr installed) (cadr final))
                  (equal (fn-bpr-receipt-adu (cadr installed) request)
                         (fn-bpr-receipt-adu (cadr final) request)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-brlc-acknowledged-rows-are-a-prefix-of-the-recovered-rows)
                 (:instance fn-brlc-open-ok-implies-decoded
                            (rec (fn-rr-recovered-records image ino genesis (fn-bs-unit bs) max
                                                          next-txid)))
                 (:instance fn-brlc-host-open-is-the-observed-open
                            (rows (fn-brlc-rows (fn-rr-recovered-records
                                                 image ino genesis (fn-bs-unit bs) max next-txid)
                                                arena0)))
                 (:instance fn-sn-open-observed-success-has-live-history-relation-of-host-open
                            (events (fn-brlc-rows (fn-rr-recovered-records
                                                   image ino genesis (fn-bs-unit bs) max next-txid)
                                                  arena0)))
                 (:instance fn-cpo-open-success-exact-image
                            (events (fn-brlc-rows (fn-rr-recovered-records
                                                   image ino genesis (fn-bs-unit bs) max next-txid)
                                                  arena0)))
                 (:instance fn-sf-prefixp-transitive
                            (xs (fn-bprv-history (car (fn-bpr-live-run live events fn-arena))))
                            (ys (fn-brlc-rows (take (fn-lgk-acked ks) (fn-lgk-committed ks)) arena0))
                            (zs (fn-brlc-rows (fn-rr-recovered-records
                                               image ino genesis (fn-bs-unit bs) max next-txid)
                                              arena0)))
                 (:instance fn-sonb-live-receipt-regenerated-from-related-open
                            (o (fn-sn-open-state
                                (fn-cpo-open-observed
                                 configs frontier
                                 (fn-brlc-rows (fn-rr-recovered-records
                                                image ino genesis (fn-bs-unit bs) max next-txid)
                                               arena0))))))
           :in-theory (union-theories '(fn-bprv-extendsp fn-bprv-history)
                                      (theory 'minimal-theory)))))
