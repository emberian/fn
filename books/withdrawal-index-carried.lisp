;; fn: a POST's two withdrawal-record tests answered from a carried index
;; (audit-incremental-2026-10-02 I3), DECLARED (books/def-carried-view.lisp,
;; lane generators-2: the first def-carried-view pilot; the hand book of
;; served-incremental-4 is in history at 4aa332295).
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
; The carry is (WS TSET CSET): WS a withdrawal list, TSET and CSET
; path-compressed id tries (fn-rit-*, books/post-retain-carried.lisp) of the
; string targets and the string causes of WS's records, each a :set index
; of the view: COMPLETE (every record's string target is in TSET, every
; string cause in CSET; fn-wix-tset-okp, fn-wix-cset-okp), never sound: a
; reader trusts only a negative answer and on a positive one runs the
; reference walk (a NEGATIVE FILTER, def-carried-reader).  fn-wix-refresh
; walks the new list to the tail EQUAL to the carried one, folds the walked
; records' ids onto the carried tries, else rebuilds; it keeps fn-wix-carryp
; (fn-wix-carryp-of-refresh), nil has it (fn-wix-carryp-of-nil), and the
; walk steps exactly the prepended delta (fn-wix-refresh-walks-the-delta;
; the equal at each step is the host's, books/def-carried-view.lisp).
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
(include-book "def-carried-view")

; -----------------------------------------------------------------------------
; 1. The index: a string id put in a trie, a non-string ignored; the two
; facts a :set index owes.

(defun fn-wix-key (x)
  (declare (xargs :guard t))
  (if (stringp x) x nil))

(defun fn-wix-add (x set)
  (declare (xargs :guard t))
  (if (stringp x) (fn-rit-put x 0 set) set))

(defthm fn-wix-hasp-of-put
  (implies (and (stringp x) (fn-rit-hasp x 0 set))
           (fn-rit-hasp x 0 (fn-wix-add y set)))
  :hints (("Goal" :in-theory (disable fn-rit-hasp fn-rit-put))))

(defthm fn-wix-put-has-it
  (implies (stringp x) (fn-rit-hasp x 0 (fn-wix-add x set)))
  :hints (("Goal" :in-theory (disable fn-rit-hasp fn-rit-put))))

(in-theory (disable fn-wix-key fn-wix-add))

(def-carried-view fn-wix
  :key ws
  :indexes ((tset :kind :set
                  :key-fn (lambda (e) (fn-wix-key (fn-ctl-w-target e)))
                  :put (lambda (e idx) (fn-wix-add (fn-ctl-w-target e) idx))
                  :hasp (lambda (k idx) (fn-rit-hasp k 0 idx))
                  :empty nil
                  :lemmas (fn-wix-hasp-of-put fn-wix-put-has-it fn-wix-key))
            (cset :kind :set
                  :key-fn (lambda (e) (fn-wix-key (fn-ctl-w-cause e)))
                  :put (lambda (e idx) (fn-wix-add (fn-ctl-w-cause e) idx))
                  :hasp (lambda (k idx) (fn-rit-hasp k 0 idx))
                  :empty nil
                  :lemmas (fn-wix-hasp-of-put fn-wix-put-has-it fn-wix-key))))

; -----------------------------------------------------------------------------
; 2. The lookups: negative filters over the two indexes.  Each owes one
; lemma: a key absent from a complete index is absent from the list.

(local
 (defthm fn-wix-absent-target-is-untargeted
   (implies (and (fn-wix-tset-okp ws idxs)
                 (stringp msgid)
                 (not (fn-rit-hasp msgid 0 (fn-wix-tset-of idxs))))
            (equal (fn-pidx-targetedp msgid ws) nil))
   :hints (("Goal" :in-theory (e/d (fn-wix-tset-okp fn-wix-key)
                                   (fn-rit-hasp fn-ctl-w-target fn-ctl-w-cause))))))

(local
 (defthm fn-wix-absent-cause-has-no-targets
   (implies (and (fn-wix-cset-okp ws idxs)
                 (stringp cause)
                 (not (fn-rit-hasp cause 0 (fn-wix-cset-of idxs))))
            (equal (fn-sca-targets-of cause ws) nil))
   :hints (("Goal" :in-theory (e/d (fn-wix-cset-okp fn-wix-key)
                                   (fn-rit-hasp fn-ctl-w-target fn-ctl-w-cause
                                    fn-ctl-withdrawalp))))))

; KEYSTONE (the lookup).
(def-carried-reader fn-wix-targetedp (msgid ws carry)
  :of fn-wix :carry carry :list ws
  :when (stringp msgid)
  :probe (tset msgid)
  :fast nil
  :reference (fn-pidx-targetedp msgid ws)
  :by fn-wix-absent-target-is-untargeted
  :name fn-wix-targetedp-is-pidx-targetedp)

; KEYSTONE (the finish's targets).
(def-carried-reader fn-wix-targets-of (cause ws carry)
  :of fn-wix :carry carry :list ws
  :when (stringp cause)
  :probe (cset cause)
  :fast nil
  :reference (fn-sca-targets-of cause ws)
  :by fn-wix-absent-cause-has-no-targets
  :name fn-wix-targets-of-is-sca-targets-of)

; -----------------------------------------------------------------------------
; 3. The POST's duplicate test with the targeted test read from the carry.

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
