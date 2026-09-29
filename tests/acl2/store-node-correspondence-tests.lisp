; fn: teeth for books/store-node-correspondence.lisp (W5b half (a), lanes
; stx-model-2 and stx-model-3).  Every state below is reached by the
; transitions of books/store-node from tests/acl2/store-node-index-tests'
; run, and every positive witness has a NON-EMPTY store: the correspondence
; fn-snc-correspondp is asserted after each transition that adds an article
; or changes the rows, the keystone fn-snc-node-lace-is-the-rows-lace is
; evaluated on a node of two articles with its hypothesis checked
; affirmatively, and one hypothesis-removal witness shows a well-formed
; state that does not correspond stays so through the finish.
(in-package "ACL2")
(include-book "store-node-index-tests")
(include-book "../../books/store-node-correspondence")

; The keys, spelled out once so the witnesses below are not equalities of
; two NILs: the run's first article, then both.  A key is (Message-ID .
; HANDLE): the rows and the node hold the arena handle the intern assigned
; (records-flip), 0 for the run's first payload and 1 for its second, not
; the wire record's octets.
(assert-event (equal (fn-snc-article-keys (fn-stx-store (fn-sn-node *sni-finished*)))
                     (list (cons (fn-record-msgid *sni-record*) 0))))
(assert-event (equal (fn-snc-row-keys-newest-first (fn-sn-indexed-rows *sni-finished*))
                     (list (cons (fn-record-msgid *sni-record*) 0))))
(assert-event (fn-snc-correspondp *sni-initial*))
(assert-event (fn-snc-correspondp *sni-keyed*))
(assert-event (fn-snc-correspondp *sni-completing*))
(assert-event (fn-snc-correspondp *sni-finished*))

; -----------------------------------------------------------------------------
; The second article, transition by transition, on a node that already holds
; one: the reservation (I/O), the prepare, the publication (I/O), the finish.

(make-event (list 'defconst '*snct-reserved-2*
                  (list 'quote (fn-sni-reserve *sni-finished*))))
(assert-event (equal (fn-sf-phase (fn-sn-files *snct-reserved-2*)) :reserved))
(assert-event (fn-sn-statep *snct-reserved-2*))
(assert-event (equal (len (fn-stx-store (fn-sn-node *snct-reserved-2*))) 1))
(assert-event (fn-snc-correspondp *snct-reserved-2*))

(make-event (list 'defconst '*snct-prepared-2*
                  (list 'quote (fn-sni-prepare *snct-reserved-2* (list *sni-record*) *sni-record-2*))))
(assert-event (not (equal *snct-prepared-2* *snct-reserved-2*)))
(assert-event (equal (fn-sf-phase (fn-sn-files *snct-prepared-2*)) :record-staged))
(assert-event (fn-sn-statep *snct-prepared-2*))
(assert-event (fn-snc-correspondp *snct-prepared-2*))

(make-event (list 'defconst '*snct-completing-2*
                  (list 'quote (fn-sni-publish *snct-prepared-2*))))
(assert-event (equal (fn-sf-phase (fn-sn-files *snct-completing-2*)) :completing))
(assert-event (fn-sn-statep *snct-completing-2*))
(assert-event (fn-sn-completion-is-last-p (fn-sn-files *snct-completing-2*)))
; In :completing the last row is durable but not indexed: one row, one article.
(assert-event (equal (len (fn-sf-records (fn-sn-files *snct-completing-2*))) 2))
(assert-event (equal (len (fn-sn-indexed-rows *snct-completing-2*)) 1))
(assert-event (fn-snc-correspondp *snct-completing-2*))

; The finish (fn-snc-finish-preserves-correspondp): the store grows by the
; second article and the rows by the second row, and the keys agree.
(assert-event (fn-sn-completion-enabledp *snct-completing-2*))
(assert-event (equal (fn-sn-finish *snct-completing-2*) *sni-forked*))
(assert-event (equal (len (fn-stx-store (fn-sn-node *sni-forked*))) 2))
(assert-event (equal (fn-snc-article-keys (fn-stx-store (fn-sn-node *sni-forked*)))
                     (list (cons (fn-record-msgid *sni-record-2*) 1)
                           (cons (fn-record-msgid *sni-record*) 0))))
(assert-event (fn-snc-correspondp *sni-forked*))

; -----------------------------------------------------------------------------
; The crash and the recovery of the two-article node
; (fn-snc-crash-preserves-correspondp-by-recomputation,
; fn-snc-recover-preserves-correspondp-by-recomputation).

(make-event (list 'defconst '*snct-crashed-2*
                  (list 'quote (fn-sn-crash *sni-forked* :new :present))))
(assert-event (equal (fn-stx-store (fn-sn-node *snct-crashed-2*)) nil))
(assert-event (equal (fn-sn-indexed-rows *snct-crashed-2*) nil))
(assert-event (fn-snc-correspondp *snct-crashed-2*))

(make-event (list 'defconst '*snct-recovered-2*
                  (list 'quote (fn-sn-recover *snct-crashed-2*))))
(assert-event (equal (fn-sf-phase (fn-sn-files *snct-recovered-2*)) :recovering))
(assert-event (equal (len (fn-stx-store (fn-sn-node *snct-recovered-2*))) 2))
(assert-event (equal (fn-snc-article-keys (fn-stx-store (fn-sn-node *snct-recovered-2*)))
                     (fn-snc-article-keys (fn-stx-store (fn-sn-node *sni-forked*)))))
(assert-event (fn-snc-correspondp *snct-recovered-2*))
(assert-event (fn-snc-correspondp *sni-recovered*))

; -----------------------------------------------------------------------------
; The keyring installation (fn-snc-set-keyring-preserves-correspondp): the
; rows are recontexted, their Message-IDs and handles stay.

(assert-event (equal (len (fn-stx-store (fn-sn-node *sni-rekeyed*))) 1))
(assert-event (fn-snc-correspondp *sni-rekeyed*))
(make-event (list 'defconst '*snct-rekeyed-2*
                  (list 'quote (fn-sni-set-keyring *sni-forked* *sni-keyring*
                                                   (list *sni-record* *sni-record-2*)))))
(assert-event (not (equal *snct-rekeyed-2* *sni-forked*)))
(assert-event (equal (fn-sn-keyring-generation *snct-rekeyed-2*) 2))
(assert-event (equal (len (fn-sn-indexed-rows *snct-rekeyed-2*)) 2))
(assert-event (fn-snc-correspondp *snct-rekeyed-2*))

; -----------------------------------------------------------------------------
; The two resolutions (fn-snc-refuse-reservation-preserves-correspondp,
; fn-snc-known-abort-preserves-correspondp) on the one-article node.

(make-event (list 'defconst '*snct-refused*
                  (list 'quote (fn-sn-refuse-reservation
                                *snct-reserved-2*
                                (1- (fn-sf-frontier (fn-sn-files *snct-reserved-2*)))))))
(assert-event (not (equal *snct-refused* *snct-reserved-2*)))
(assert-event (equal (fn-sf-phase (fn-sn-files *snct-refused*)) :ready))
(assert-event (equal (len (fn-stx-store (fn-sn-node *snct-refused*))) 1))
(assert-event (fn-snc-correspondp *snct-refused*))

(make-event (list 'defconst '*snct-aborted*
                  (list 'quote (fn-sn-known-abort *snct-prepared-2*))))
(assert-event (fn-sn-known-abort-enabledp *snct-prepared-2*))
(assert-event (not (equal *snct-aborted* *snct-prepared-2*)))
(assert-event (equal (len (fn-stx-store (fn-sn-node *snct-aborted*))) 1))
(assert-event (fn-snc-correspondp *snct-aborted*))

; The sweep returns the store as it was
; (fn-snc-sweep-staging-preserves-correspondp-by-definition).
(assert-event (equal (cdr (fn-sn-sweep-staging *sni-forked* nil nil)) *sni-forked*))
(assert-event (fn-snc-correspondp (cdr (fn-sn-sweep-staging *sni-forked* nil nil))))

; -----------------------------------------------------------------------------
; KEYSTONE (fn-snc-node-lace-is-the-rows-lace, PRF-1027) on the two-article
; node, through an arena holding both records' payloads: the hypothesis
; fn-rows-contexts-okp is checked affirmatively, the lace is non-empty, and
; the node lace read through the arena IS the rows' lace.

(defun fn-snct-node-side-in (s keyring prior fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (rows fn-arena)
    (fn-intern-events prior nil 0 fn-arena)
    (declare (ignore rows))
    (mv (list (fn-rows-contexts-okp (fn-sn-indexed-rows s) keyring
                                    (fn-sn-keyring-generation s) fn-arena)
              (fn-stx-lace (fn-sn-node s) keyring fn-arena))
        fn-arena)))

; (contexts-okp . node-lace) of S under KEYRING, read through the arena
; holding PRIOR's payloads.
(defun fn-snct-node-side (s keyring prior)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (answer fn-arena)
      (fn-snct-node-side-in s keyring prior fn-arena)
      answer)))

(make-event (list 'defconst '*snct-node-side*
                  (list 'quote (fn-snct-node-side *sni-forked* *sni-keyring*
                                                  (list *sni-record* *sni-record-2*)))))
(assert-event (equal (nth 0 *snct-node-side*) t))
(assert-event (equal (len (fn-sn-lace-of-rows (fn-sn-indexed-rows *sni-forked*))) 2))
(assert-event (equal (nth 1 *snct-node-side*)
                     (fn-sn-lace-of-rows (fn-sn-indexed-rows *sni-forked*))))

; -----------------------------------------------------------------------------
; HYPOTHESIS REMOVAL (fn-snc-finish-preserves-correspondp, the correspondence
; hypothesis): a state that is a state and whose completion is its last row
; but whose node holds an article the rows do not, before the finish and
; after it.  The finish is disabled on it (the node has no pending for the
; completion record), so it is the same state; a corrupted-state witness.

(make-event (list 'defconst '*snct-corrupt*
                  (list 'quote (fn-sn-update *snct-completing-2*
                                             (fn-sn-files *snct-completing-2*)
                                             (fn-sn-node *sni-forked*)))))
(assert-event (fn-sn-statep *snct-corrupt*))
(assert-event (fn-sn-completion-is-last-p (fn-sn-files *snct-corrupt*)))
(assert-event (equal (len (fn-stx-store (fn-sn-node *snct-corrupt*))) 2))
(assert-event (equal (len (fn-sn-indexed-rows *snct-corrupt*)) 1))
(assert-event (not (fn-snc-correspondp *snct-corrupt*)))
(assert-event (not (fn-sn-completion-enabledp *snct-corrupt*)))
(assert-event (not (fn-snc-correspondp (fn-sn-finish *snct-corrupt*))))
