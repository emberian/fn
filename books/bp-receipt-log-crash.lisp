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
;   - the open then decodes the recovered record octets and interns them
;     (host/native/io.lisp fnn-bridge-recover: fn-store-decode-records =
;     fn-srs-decode, then fn-srs-intern-step; books/store-recover-stream.lisp
;     fn-srs-one-step-is-the-intern-of-the-decode), and opens over those rows
;     through fn-cpo-open-observed (host/store-node-host.lisp
;     fn-store-sn-recover).
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
; log's recovery holds; open; run the recovery barriers to :ready; then
; fn-bprj-install's replay of the journal is the live receiver state and the
; receipt ADU is byte-identical.
;
; NOT claimed here, named:
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
(include-book "store-recover-stream")

; -----------------------------------------------------------------------------
; 1. The rows the open makes of a list of log records: the host's one step
;    from no rows (fn-srs-step, the decode then the intern), oldest first.

; Logical (defun-nx): the host runs fn-srs-step on the live arena stobj; these
; name its value from an arbitrary starting arena.
(defun-nx fn-brlc-rows (octet-records arena0)
  (fn-srs-rows (mv-nth 0 (fn-srs-step nil octet-records arena0))))

(defun-nx fn-brlc-decodedp (octet-records arena0)
  (not (eq (mv-nth 0 (fn-srs-step nil octet-records arena0)) :bad)))

; -----------------------------------------------------------------------------
; 2. The rows of a prefix are a prefix of the rows, when the whole decodes.

(local
 (defthm fn-brlc-srs-step-of-nil-is-intern
   (equal (fn-srs-step nil octet-records arena0)
          (if (eq (fn-srs-decode octet-records) :bad)
              (mv :bad arena0)
            (mv-let (rows a) (fn-intern-events (fn-srs-decode octet-records) nil 0 arena0)
              (if (eq rows :bad) (mv :bad a) (mv (revappend rows nil) a)))))
   :hints (("Goal" :in-theory (e/d (fn-srs-step fn-srs-intern-step)
                                   (fn-intern-events fn-srs-decode))))))

(local
 (defthm fn-brlc-reverse-revappend
   (implies (true-listp x)
            (equal (reverse (true-list-fix (revappend x nil))) x))))

(defthm fn-brlc-rows-of-append
  (implies (and (true-listp a)
                (fn-brlc-decodedp (append a b) arena0))
           (and (fn-brlc-decodedp a arena0)
                (equal (fn-brlc-rows (append a b) arena0)
                       (append (fn-brlc-rows a arena0)
                               (mv-nth 0 (fn-intern-events
                                          (fn-srs-decode b) nil 0
                                          (mv-nth 1 (fn-intern-events (fn-srs-decode a)
                                                                      nil 0 arena0))))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-srs-intern-events-of-append
                            (a (fn-srs-decode a)) (b (fn-srs-decode b))
                            (keyring nil) (generation 0) (fn-arena arena0))
                 (:instance fn-srs-intern-events-true-listp
                            (ws (fn-srs-decode a)) (keyring nil) (generation 0)
                            (fn-arena arena0))
                 (:instance fn-srs-intern-events-true-listp
                            (ws (fn-srs-decode b)) (keyring nil) (generation 0)
                            (fn-arena (mv-nth 1 (fn-intern-events (fn-srs-decode a)
                                                                  nil 0 arena0)))))
           :in-theory (e/d (fn-brlc-rows fn-brlc-decodedp)
                           (fn-intern-events fn-srs-decode fn-srs-intern-events-of-append
                            fn-srs-intern-events-true-listp reverse)))))

(defthm fn-brlc-rows-of-prefix-is-a-prefix
  (implies (and (true-listp a)
                (fn-brlc-decodedp (append a b) arena0))
           (fn-sf-prefixp (fn-brlc-rows a arena0) (fn-brlc-rows (append a b) arena0)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-brlc-rows-of-append)
                 (:instance fn-bprv-prefixp-of-append
                            (h (fn-brlc-rows a arena0))
                            (more (mv-nth 0 (fn-intern-events
                                             (fn-srs-decode b) nil 0
                                             (mv-nth 1 (fn-intern-events (fn-srs-decode a)
                                                                         nil 0 arena0)))))))
           :in-theory (e/d (fn-brlc-rows)
                           (fn-brlc-rows-of-append fn-bprv-prefixp-of-append
                            fn-intern-events fn-srs-decode fn-srs-step)))))

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
         (opened (fn-cpo-open-observed configs frontier (fn-brlc-rows recovered arena0)))
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
                  (fn-brlc-decodedp recovered arena0)
                  (fn-sonb-configured-before-eventsp configs)
                  (fn-sn-open-okp opened)
                  (equal (fn-bprv-phase probe) :ready))
             (and (equal (cadr installed) (cadr final))
                  (equal (fn-bpr-receipt-adu (cadr installed) request)
                         (fn-bpr-receipt-adu (cadr final) request)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-brlc-acknowledged-rows-are-a-prefix-of-the-recovered-rows)
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
