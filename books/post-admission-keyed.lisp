; The served POST's admission with the keyed Message-ID index (lane
; paged-history-6, row P2 slice 3; prefix fn-pak-).
;
; THE HOST-CALLED SUBJECT is `fn-pak-post-admission', asked by
; host/owner-host.lisp `fn-owner-post-boundary' (host/native/owner.lisp
; `fnn-owner-attempt-post' and `fnn-owner-attempt-transit', through
; `fnn-validate-post-boundary') for every POST and every transit article,
; BEFORE the duplicate test and the prepare, so before anything is staged
; or made durable: the five bounds of the carried boundary
; (books/store-profile-carried.lisp fn-pvc-post-boundary-carried, PRF-284),
; and when they admit, the catalog's keyed page table's own answer whether
; one more row carrying this Message-ID can be placed (books/catalog.lisp
; fn-cat-msgid-saturatedp, THE SWITCH's served refusal, PRF-1037).  The
; sixth verdict word `:mpx-saturated' is a REFUSAL by name (its 441 text is
; books/store-budget-naming.lisp *fn-sbud-refusal-mpx-saturated*): refused,
; never uncertain, never accepted; the poster may retry after the operator
; acts.  The key is the node secret's current entry's
; (books/msgid-pages-exec.lisp fn-mpxt-key-of-entry), the one the open
; installed in the table (books/served-catalog-owner-keyed.lisp), read from
; the owner's ring by the host entry; the executable answers from the table
; only when the key is its own (fn-cat$c-msgid-saturatedp), which the
; composition guarantees.
;
; KEYSTONE fn-pak-post-admission-ok-is-indexed: an admitted POST is indexed --
; the fold of the catalog's rows and one more row carrying the POST's
; Message-ID places it (no unplaced row is added).  Teeth:
; tests/acl2/post-admission-keyed-tests.lisp.

(in-package "ACL2")

(include-book "store-profile-carried")
(include-book "store-budget-naming")
(include-book "catalog")
(include-book "owner-scheduler")

(defun fn-pak-post-admission (carry profile msgid-octets payload-length
                                    group-count charge key fn-cat)
  (declare (xargs :stobjs fn-cat
                  :guard (and (fn-mpxt-keyp key)
                              (equal (len key) *fn-mpxt-key-octets*))))
  (let ((verdict (fn-pvc-post-boundary-carried carry profile msgid-octets
                                               payload-length group-count
                                               charge)))
    (cond ((not (equal verdict :ok)) verdict)
          ((fn-cat-msgid-saturatedp key (fn-record-octets-string msgid-octets)
                                    fn-cat)
           :mpx-saturated)
          (t :ok))))

; A bound's refusal passes through unchanged: the index is asked only of an
; admitted boundary.
(defthm fn-pak-post-admission-refused-is-the-boundary-by-definition
  (implies (not (equal (fn-pvc-post-boundary-carried carry profile msgid-octets
                                                     payload-length group-count
                                                     charge)
                       :ok))
           (equal (fn-pak-post-admission carry profile msgid-octets
                                         payload-length group-count charge
                                         key fn-cat)
                  (fn-pvc-post-boundary-carried carry profile msgid-octets
                                                payload-length group-count
                                                charge))))

; The boundary never says the sixth word: `:mpx-saturated' is the index's
; alone.
(defthm fn-pak-boundary-never-says-mpx-saturated
  (not (equal (fn-pvc-post-boundary-carried carry profile msgid-octets
                                            payload-length group-count charge)
              :mpx-saturated))
  :hints (("Goal" :in-theory (enable fn-pvc-post-boundary-carried
                                     fn-pvc-post-boundary))))

; The range: one of the six named words of books/store-budget-naming.lisp,
; so the host's refusal text is never the unnamed one
; (fn-sbud-post-boundary-refusal).
(defthm fn-pak-post-admission-is-a-named-verdict
  (implies (fn-pvc-carryp carry)
           (fn-sbud-post-boundary-verdictp
            (fn-pak-post-admission carry profile msgid-octets payload-length
                                   group-count charge key fn-cat)))
  :hints (("Goal" :in-theory (e/d (fn-pak-post-admission)
                                  (fn-sbud-post-boundary-verdictp))
           :use ((:instance fn-sbud-post-boundary-verdicts-are-named
                            (msgid msgid-octets))))))

; KEYSTONE: an admitted POST is indexed.  Over the opened view (the abstract
; catalog is its rows), the fold under the table's key over the rows and one
; more row H carrying the POST's Message-ID leaves the unplaced count where
; it was (books/catalog.lisp fn-cat-msgid-saturatedp-is-the-outcome).
(defthm fn-pak-post-admission-ok-is-indexed
  (implies (and (equal (fn-pak-post-admission carry profile msgid-octets
                                              payload-length group-count
                                              charge key fn-cat)
                       :ok)
                (equal (fn-record-msgid h) (fn-record-octets-string msgid-octets)))
           (equal (fn-mlh-build-unplaced key (append fn-cat (list h)))
                  (fn-mlh-build-unplaced key fn-cat)))
  :hints (("Goal" :use ((:instance fn-cat-msgid-saturatedp-is-the-outcome
                                   (msgid (fn-record-octets-string msgid-octets)))))))

; The sixth word means the index said so (the boundary never says it).
(defthm fn-pak-post-admission-saturated-means-saturated-by-definition
  (implies (equal (fn-pak-post-admission carry profile msgid-octets
                                         payload-length group-count charge
                                         key fn-cat)
                  :mpx-saturated)
           (fn-cat-msgid-saturatedp key (fn-record-octets-string msgid-octets)
                                    fn-cat))
  :hints (("Goal" :in-theory (enable fn-pak-post-admission)
           :use ((:instance fn-pak-boundary-never-says-mpx-saturated)))))

; And the refusal is exact: the sixth word is said exactly when the fold
; could not place that row.
(defthm fn-pak-post-admission-saturated-is-not-indexed
  (implies (and (equal (fn-pak-post-admission carry profile msgid-octets
                                              payload-length group-count
                                              charge key fn-cat)
                       :mpx-saturated)
                (equal (fn-record-msgid h) (fn-record-octets-string msgid-octets)))
           (not (equal (fn-mlh-build-unplaced key (append fn-cat (list h)))
                       (fn-mlh-build-unplaced key fn-cat))))
  :hints (("Goal" :in-theory (disable fn-pak-post-admission)
           :use ((:instance fn-cat-msgid-saturatedp-is-the-outcome
                            (msgid (fn-record-octets-string msgid-octets)))
                 (:instance fn-pak-post-admission-saturated-means-saturated-by-definition)))))

(in-theory (disable fn-pak-post-admission))

; -----------------------------------------------------------------------------
; The `health' report's index line (host/native-live-status-host.lisp): the
; table's pages, entries, the rows the fold could not place and the stuck
; count, rendered from fn-cat-index-health's four-element answer
; (books/catalog.lisp fn-cat-index-health-is-the-build).  An operator reads
; `unplaced' > 0 as the index degraded to a scan (fn-cat$c-msgid-seqs) and
; `stuck' as the writer's own count; both are 0 on every store the natives
; build.

(defun fn-pak-index-health-line (health)
  (declare (xargs :guard t))
  (if (and (true-listp health) (equal (len health) 4))
      (append (fn-osch-text "msgid-index:")
              (fn-osch-kv "pages" (nth 0 health))
              (fn-osch-kv "entries" (nth 1 health))
              (fn-osch-kv "unplaced" (nth 2 health))
              (fn-osch-kv "stuck" (nth 3 health))
              (list 10))
    (append (fn-osch-text "msgid-index: unavailable") (list 10))))
