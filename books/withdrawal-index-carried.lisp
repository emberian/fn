;; fn: a POST's two withdrawal-record tests answered from a carried index
;; (audit-incremental-2026-10-02 I3).
;
; Two tests on a POST's path walked the view's withdrawal records, a list
; that grows with every control article the node ever accepted (W):
;
;   1. fn-pidx-targetedp (books/post-identity-index.lisp): does any record
;      name the posted Message-ID as its target?  Asked by
;      fn-pidx-find-article-cat (books/post-identity-catalog.lisp) under
;      fn-pidx-existing-action-cat, which host/owner-host.lisp
;      fn-owner-prepare-buffer and fn-owner-existing-action-buffer call once
;      per POST each.
;   2. fn-sca-targets-of (books/served-catalog-owner.lisp): the targets of
;      the records the completed article caused.  host/owner-host.lisp
;      fn-owner-finish-submission-synced and fn-owner-finish-identity call it
;      once per completion, on the refreshed view's records.
;
; Both are O(W) per call however few records concern the Message-ID; an
; ordinary article is the target and the cause of none.
;
; The carry is (WS TSET . CSET): WS a withdrawal list, TSET and CSET
; path-compressed id tries (fn-rit-*, books/post-retain-carried.lisp) of the
; string targets and the string causes of WS's records.  fn-wix-carryp says
; only that they are COMPLETE: every record's string target is in TSET and
; every record's string cause is in CSET.  Soundness is not needed: a reader
; trusts only a negative answer, and on a positive one (a control article's
; Message-ID, or a cancel's target) it runs the reference walk, so its value
; is the reference's for every list.  A reader uses the tries only when the
; list in hand is EQUAL to the carried one (one EQ test when the carry was
; refreshed from this view).
;
; fn-wix-refresh brings a carry to a withdrawal list: it walks the list
; until a tail EQUAL to the carried list, putting the walked records' ids
; into the carried tries (the refresh of the view prepends the new article's
; records, books/control-visible.lisp fn-ctl-refresh-withdrawals, so the
; walk is that delta); if no tail matches (the first call, a recomputed or
; tlock-resolved list, a reopen) it rebuilds from empty tries.  It keeps
; fn-wix-carryp for every carry that has it, and nil has it, so a host global
; written only with fn-wix-refresh of nil or of a value it read always has it
; (fn-wix-carryp-of-refresh, fn-wix-carryp-of-nil).
;
; KEYSTONES (the host calls the left-hand sides once wired; see
; build/coordinator/lanedumps/served-incremental-4.md NEXT):
;   fn-wix-targets-of-is-sca-targets-of
;   fn-wix-existing-action-cat-is-pidx-existing-action-cat
; and, for the lookup itself, fn-wix-targetedp-is-pidx-targetedp.
;
; Not here: books/control-visible.lisp fn-ctl-resolve-tlocks also walks the
; list once per new article (fn-ctl-targets-p) inside the owner's refresh;
; the same carry answers it but has to be threaded through the owner
; transition (an open item, PRF-1231's scope note).

(in-package "ACL2")
(include-book "post-identity-catalog")
(include-book "post-retain-carried")

; -----------------------------------------------------------------------------
; 1. The carry and its recognizer.

(defun fn-wix-ws (carry) (declare (xargs :guard t)) (fn-ag-car carry))
(defun fn-wix-tset (carry) (declare (xargs :guard t)) (fn-ag-car (fn-ag-cdr carry)))
(defun fn-wix-cset (carry) (declare (xargs :guard t)) (fn-ag-cdr (fn-ag-cdr carry)))

; Every record's string target is in TSET and string cause in CSET.
(defun fn-wix-completep (ws tset cset)
  (declare (xargs :guard t))
  (if (consp ws)
      (and (or (not (stringp (fn-ctl-w-target (car ws))))
               (fn-rit-hasp (fn-ctl-w-target (car ws)) 0 tset))
           (or (not (stringp (fn-ctl-w-cause (car ws))))
               (fn-rit-hasp (fn-ctl-w-cause (car ws)) 0 cset))
           (fn-wix-completep (cdr ws) tset cset))
    t))

(defun fn-wix-carryp (carry)
  (declare (xargs :guard t))
  (fn-wix-completep (fn-wix-ws carry) (fn-wix-tset carry) (fn-wix-cset carry)))

(defthm fn-wix-carryp-of-nil
  (fn-wix-carryp nil))

; -----------------------------------------------------------------------------
; 2. The lookups.

(defun fn-wix-targetedp (msgid ws carry)
  (declare (xargs :guard t))
  (if (and (stringp msgid)
           (equal ws (fn-wix-ws carry))
           (not (fn-rit-hasp msgid 0 (fn-wix-tset carry))))
      nil
    (fn-pidx-targetedp msgid ws)))

(defun fn-wix-targets-of (cause ws carry)
  (declare (xargs :guard t))
  (if (and (stringp cause)
           (equal ws (fn-wix-ws carry))
           (not (fn-rit-hasp cause 0 (fn-wix-cset carry))))
      nil
    (fn-sca-targets-of cause ws)))

(local
 (defthm fn-wix-absent-target-is-untargeted
   (implies (and (fn-wix-completep ws tset cset)
                 (stringp msgid)
                 (not (fn-rit-hasp msgid 0 tset)))
            (not (fn-pidx-targetedp msgid ws)))
   :hints (("Goal" :in-theory (disable fn-rit-hasp fn-ctl-w-target fn-ctl-w-cause)))))

(local
 (defthm fn-wix-absent-cause-has-no-targets
   (implies (and (fn-wix-completep ws tset cset)
                 (stringp cause)
                 (not (fn-rit-hasp cause 0 cset)))
            (equal (fn-sca-targets-of cause ws) nil))
   :hints (("Goal" :in-theory (disable fn-rit-hasp fn-ctl-w-target fn-ctl-w-cause
                                       fn-ctl-withdrawalp)))))

; KEYSTONE (the lookup).
(defthm fn-wix-targetedp-is-pidx-targetedp
  (implies (fn-wix-carryp carry)
           (equal (fn-wix-targetedp msgid ws carry)
                  (fn-pidx-targetedp msgid ws)))
  :hints (("Goal" :in-theory (disable fn-rit-hasp fn-pidx-targetedp fn-wix-completep))))

; KEYSTONE (the finish's targets).
(defthm fn-wix-targets-of-is-sca-targets-of
  (implies (fn-wix-carryp carry)
           (equal (fn-wix-targets-of cause ws carry)
                  (fn-sca-targets-of cause ws)))
  :hints (("Goal" :in-theory (disable fn-rit-hasp fn-sca-targets-of fn-wix-completep))))

; -----------------------------------------------------------------------------
; 3. The refresh.

(defun fn-wix-put (x set)
  (declare (xargs :guard t))
  (if (stringp x) (fn-rit-put x 0 set) set))

; Walk TAIL until it is EQUAL to OLD, putting each record's ids.  Returns
; (mv FOUND TSET CSET).
(defun fn-wix-extend (tail old tset cset)
  (declare (xargs :guard t))
  (cond ((equal tail old) (mv t tset cset))
        ((atom tail) (mv nil tset cset))
        (t (fn-wix-extend (cdr tail) old
                          (fn-wix-put (fn-ctl-w-target (car tail)) tset)
                          (fn-wix-put (fn-ctl-w-cause (car tail)) cset)))))

(defun fn-wix-refresh (carry ws)
  (declare (xargs :guard t))
  (if (equal ws (fn-wix-ws carry))
      carry
    (mv-let (found tset cset)
      (fn-wix-extend ws (fn-wix-ws carry) (fn-wix-tset carry) (fn-wix-cset carry))
      (if found
          (cons ws (cons tset cset))
        (mv-let (found2 tset cset)
          (fn-wix-extend ws nil nil nil)
          (declare (ignore found2))
          (cons ws (cons tset cset)))))))

(local
 (defthm fn-wix-hasp-of-put
   (implies (and (stringp x) (fn-rit-hasp x 0 set))
            (fn-rit-hasp x 0 (fn-wix-put y set)))
   :hints (("Goal" :in-theory (disable fn-rit-hasp fn-rit-put)))))

(local
 (defthm fn-wix-completep-of-put
   (implies (fn-wix-completep ws tset cset)
            (and (fn-wix-completep ws (fn-wix-put x tset) cset)
                 (fn-wix-completep ws tset (fn-wix-put x cset))))
   :hints (("Goal" :in-theory (disable fn-rit-hasp fn-wix-put fn-ctl-w-target
                                       fn-ctl-w-cause)))))

(local
 (defthm fn-wix-put-has-it
   (implies (stringp x) (fn-rit-hasp x 0 (fn-wix-put x set)))
   :hints (("Goal" :in-theory (disable fn-rit-hasp fn-rit-put)))))

(local
 (defthm fn-wix-hasp-of-extend
   (implies (and (stringp x)
                 (fn-rit-hasp x 0 tset))
            (fn-rit-hasp x 0 (mv-nth 1 (fn-wix-extend tail old tset cset))))
   :hints (("Goal" :in-theory (disable fn-rit-hasp fn-wix-put fn-ctl-w-target
                                       fn-ctl-w-cause)))))

(local
 (defthm fn-wix-hasp-of-extend-cset
   (implies (and (stringp x)
                 (fn-rit-hasp x 0 cset))
            (fn-rit-hasp x 0 (mv-nth 2 (fn-wix-extend tail old tset cset))))
   :hints (("Goal" :in-theory (disable fn-rit-hasp fn-wix-put fn-ctl-w-target
                                       fn-ctl-w-cause)))))

(local
 (defthm fn-wix-completep-of-extend-sets
   (implies (fn-wix-completep ws tset cset)
            (fn-wix-completep ws
                              (mv-nth 1 (fn-wix-extend tail old tset cset))
                              (mv-nth 2 (fn-wix-extend tail old tset cset))))
   :hints (("Goal" :induct (fn-wix-completep ws tset cset)
            :in-theory (disable fn-rit-hasp fn-wix-put fn-ctl-w-target
                                fn-ctl-w-cause fn-wix-extend)))))

; The walked tail is complete under the extended tries when it was found
; (OLD complete under the tries it started with) or ran to its end.
(local
 (defthm fn-wix-completep-of-extend
   (implies (or (fn-wix-completep old tset cset)
                (not (mv-nth 0 (fn-wix-extend tail old tset cset))))
            (fn-wix-completep tail
                              (mv-nth 1 (fn-wix-extend tail old tset cset))
                              (mv-nth 2 (fn-wix-extend tail old tset cset))))
   :hints (("Goal" :induct (fn-wix-extend tail old tset cset)
            :in-theory (disable fn-rit-hasp fn-wix-put fn-ctl-w-target
                                fn-ctl-w-cause)))))

; KEYSTONE (the writer keeps the recognizer).
(defthm fn-wix-carryp-of-refresh
  (implies (fn-wix-carryp carry)
           (fn-wix-carryp (fn-wix-refresh carry ws)))
  :hints (("Goal" :in-theory (disable fn-wix-extend fn-wix-completep)
           :use ((:instance fn-wix-completep-of-extend
                            (tail ws) (old (fn-wix-ws carry))
                            (tset (fn-wix-tset carry)) (cset (fn-wix-cset carry)))
                 (:instance fn-wix-completep-of-extend
                            (tail ws) (old nil) (tset nil) (cset nil))))))

(defthm fn-wix-ws-of-refresh
  (equal (fn-wix-ws (fn-wix-refresh carry ws)) ws)
  :hints (("Goal" :in-theory (disable fn-wix-extend))))

(in-theory (disable fn-wix-ws fn-wix-tset fn-wix-cset fn-wix-carryp
                    fn-wix-targetedp fn-wix-targets-of fn-wix-refresh))

; -----------------------------------------------------------------------------
; 4. The POST's duplicate test with the targeted test read from the carry.

; fn-pidx-find-article-cat with fn-wix-targetedp.
(defun fn-wix-find-article-cat (msgid arts view carry fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)))
  (if (and (stringp msgid)
           (< 0 (length msgid))
           (equal arts (fn-own-view-raw view))
           (not (fn-wix-targetedp msgid (fn-own-view-withdrawals view) carry)))
      (fn-scat-msgid-article msgid (fn-cat-count fn-cat) fn-arena fn-cat)
    (fn-find-article msgid arts)))

(defthm fn-wix-find-article-cat-is-pidx-find-article-cat
  (implies (fn-wix-carryp carry)
           (equal (fn-wix-find-article-cat msgid arts view carry fn-arena fn-cat)
                  (fn-pidx-find-article-cat msgid arts view fn-arena fn-cat)))
  :hints (("Goal" :in-theory (e/d (fn-pidx-find-article-cat)
                                  (fn-scat-msgid-article fn-find-article
                                   fn-pidx-targetedp)))))

(in-theory (disable fn-wix-find-article-cat))

; fn-pidx-existing-action-cat with the article found through
; fn-wix-find-article-cat.
(defun fn-wix-existing-action-cat (msgid fn-octets groups o carry fn-arena fn-cat)
  (declare (xargs :stobjs (fn-octets fn-arena fn-cat)
                  :guard (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)))
  (let ((article (fn-wix-find-article-cat
                  msgid
                  (fn-state-articles
                   (fn-node-acceptance (fn-sn-node (fn-own-store o))))
                  (fn-own-view o) carry fn-arena fn-cat)))
    (if article
        (if (and (fn-rclb-same-articlep (fn-record-string-octets msgid) fn-octets
                                        (fn-handle-bytes (fn-article-payload article)
                                                         fn-arena))
                 (equal groups (fn-article-groups article)))
            :duplicate
          :conflict)
      nil)))

; KEYSTONE.  Hence, by fn-pidx-existing-action-cat-is-store-existing-action,
; the host's call is the Store's duplicate entry.
(defthm fn-wix-existing-action-cat-is-pidx-existing-action-cat
  (implies (fn-wix-carryp carry)
           (equal (fn-wix-existing-action-cat msgid fn-octets groups o carry
                                              fn-arena fn-cat)
                  (fn-pidx-existing-action-cat msgid fn-octets groups o
                                               fn-arena fn-cat)))
  :hints (("Goal" :in-theory (e/d (fn-pidx-existing-action-cat)
                                  (fn-pidx-find-article-cat fn-rclb-same-articlep
                                   fn-handle-bytes fn-record-string-octets)))))

(in-theory (disable fn-wix-existing-action-cat))
