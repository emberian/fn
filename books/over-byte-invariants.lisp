; Selected-row guard premises derived from carried catalog invariants.
; These are proofs only: the served cursor must never evaluate F or the
; complete handle relation on its request path. PRF-1066 remains dormant.
(in-package "ACL2")
(include-book "over-byte-cursor")
(include-book "nov-row-facts-model")
(include-book "catalog-handles")

(local
 (defthm fn-obc-boundary-selected-seq-in-bounds
   (implies (fn-cnx-view-seq group k v fn-cat)
            (and (natp (fn-cnx-view-seq group k v fn-cat))
                 (< (fn-cnx-view-seq group k v fn-cat) (fn-cat-count fn-cat))))
   :hints (("Goal" :in-theory
            (e/d (fn-cnx-view-seq)
                 (fn-cat-group-number fn-cat-visible-at fn-cat-count-is-len))))))

(defthm fn-obc-cached-ready-from-carried-columns
  (implies (fn-scol-okp fn-arena fn-cat)
           (fn-obc-cached-ready-p s fn-cat))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-nrf-facts-are-row-bytes-facts
                            (seq (fn-cnx-view-seq
                                  (fn-lpc-at 0 (fn-lpc-at 0 s))
                                  (nfix (fn-lpc-at 1 (fn-lpc-at 0 s)))
                                  (nfix (fn-lpc-at 3 (fn-lpc-at 0 s))) fn-cat)))
                 (:instance fn-hnov-p-of-hnov-of
                            (bytes (fn-nntp-payload-bytes
                                    (fn-record-payload
                                     (fn-cat-at
                                      (fn-cnx-view-seq
                                       (fn-lpc-at 0 (fn-lpc-at 0 s))
                                       (nfix (fn-lpc-at 1 (fn-lpc-at 0 s)))
                                       (nfix (fn-lpc-at 3 (fn-lpc-at 0 s))) fn-cat)
                                      fn-cat)) fn-arena))))
           :in-theory
           (e/d (fn-obc-cached-ready-p)
                (fn-scol-okp fn-nrf-facts fn-cnx-view-seq fn-lpc-at
                 fn-hnov-of fn-hnov-p fn-hf-nov fn-held-facts-of fn-nntp-payload-bytes
                 fn-nrf-facts-are-row-bytes-facts fn-hnov-p-of-hnov-of
                 fn-cat-at-is-nth fn-cat-count-is-len)))))

(defthm fn-obc-source-ready-from-carried-handles
  (implies (and (fn-cat-p fn-cat)
                (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
           (fn-obc-source-ready-p s fn-arena fn-cat))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cat-handles-inp-at
                            (n (fn-cat-count fn-cat)) (seq (fn-cnx-view-seq (fn-lpc-at 0 (fn-lpc-at 0 s))
                               (nfix (fn-lpc-at 1 (fn-lpc-at 0 s)))
                               (nfix (fn-lpc-at 3 (fn-lpc-at 0 s))) fn-cat)))
                 (:instance fn-cat-row-payload-natp (seq (fn-cnx-view-seq (fn-lpc-at 0 (fn-lpc-at 0 s))
                               (nfix (fn-lpc-at 1 (fn-lpc-at 0 s)))
                               (nfix (fn-lpc-at 3 (fn-lpc-at 0 s))) fn-cat))))
           :in-theory
           (e/d (fn-obc-source-ready-p)
                (fn-cat-p fn-cat-handles-inp fn-cnx-view-seq fn-lpc-at
                 fn-cat-handles-inp-at fn-cat-row-payload-natp
                 fn-cat-at-is-nth fn-cat-count-is-len)))))

; The owner carries these invariants between mutations. This theorem does
; not request their revalidation during a quantum.
(defthm fn-obc-one-keeps-shape-under-carried-catalog-by-definition
  (implies (and (fn-obc-statep s fn-arena)
                (fn-cat-p fn-cat)
                (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)
                (fn-scol-okp fn-arena fn-cat))
           (let ((next (mv-nth 1 (fn-obc-one s fn-arena fn-cat))))
             (or (not next) (fn-obc-statep next fn-arena))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-obc-one-preserves-state-shape
                 fn-obc-source-ready-from-carried-handles
                 fn-obc-cached-ready-from-carried-columns)
           :in-theory (disable fn-obc-one fn-obc-statep fn-cat-p
                               fn-cat-handles-inp fn-scol-okp
                               fn-obc-source-ready-p fn-obc-cached-ready-p))))
