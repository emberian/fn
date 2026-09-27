;; fn: a POST's retention admission answered from a carried obligation-id trie.
;
; After PRF-191 (books/post-identity-index.lisp) one test in the owner's
; prepare still walked a list that grows with the history: the retention
; admission, fn-retain-admissiblep -> fn-retain-known-id-scanp, which asks
; whether the submission's obligation id is already known to the ledger by
; walking every pin (EQUAL + STRING= per pin) and every release.  At
; N = 10,000 it was 205 of 1,741 sb-sprof :cpu samples of an owner POST run
; (11.8 percent, every one under fn-pidx-node-prepare; lane post-alloc's
; hbox profile work/after-cpu10k); PRF-191's own header left it open as
; test (3) (PKT-549).
;
; PRF-274 carried the open fold's character trie (books/replay-identity-
; index.lisp fn-rii-kbuild) across POSTs.  PRF-279 replaces it: that trie
; cost ~2 KB of live heap per pin (1,246,448 conses for 10,000 random 64-hex
; ids) and was rebuilt whole (24 MB allocated) after every release.
;
; The set is a path-compressed id trie (section 1, fn-rit-*): a leaf is the
; ledger's own id string, so an id is only as deep as the prefix it shares
; with another (about four levels for random hex ids) and the trie holds no
; copy of any id.  fn-rit-hasp-of-put holds for every node.
;
; The carry is (LEDGER . TRIE).  fn-prc-carryp says the trie answers exactly
; LEDGER's known ids: every pin and release id is in it (complete) and every
; string stored in it is a known id (sound) (fn-prc-set-okp,
; fn-prc-carryp-is-knownp).  It is executable (a test or a guard can ask it;
; the host never does).  It mentions neither the owner nor the Store, so NO
; owner transition can falsify it: whatever the owner did between two POSTs,
; the carry still describes the ledger it names.  A reader uses the trie
; only when the ledger in hand is EQUAL to the carried one (one EQ test when
; the carry was refreshed from this node), and the reference scan otherwise.
;
; fn-prc-refresh brings the carry to the node's current ledger, preserving
; fn-prc-carryp (fn-prc-carryp-of-refresh): the same ledger keeps the carry;
; a ledger reached from the carried one by retention steps -- releases consed
; on the carried releases (fn-retain-release), pins that are new pins over
; the carried ones less released ones (a durable commit's cons,
; fn-node-complete; a release's fn-retain-remove-id) -- applies that delta
; (fn-prc-delta: new ids put, nothing rebuilt; a commit costs O(1), a release
; O(position of the released pin), k steps between POSTs one walk); anything
; else (the first POST, a recovery, a reopen) rebuilds (fn-prc-build).
;
; The writers are host/owner-host.lisp: fn-owner-install-extended builds the
; carry for the ledger the owner opens with (so the first POST pays nothing),
; and fn-owner-prepare-buffer refreshes it from the owner's Store node and
; passes the result to fn-prc-sbud-prepare.  Every value either writes is
; fn-prc-refresh of nil or of a value it read, and nil satisfies the
; recognizer, so the global always satisfies it (fn-prc-carryp-of-refresh,
; fn-prc-carryp-when-atom).
;
; KEYSTONE (the host calls the left-hand side):
;   fn-prc-sbud-prepare-is-pidx-sbud-prepare
;     (fn-prc-sbud-prepare oc record budget carry)
;       = (fn-pidx-sbud-prepare oc record budget)     under fn-prc-carryp carry
; hence, by fn-pidx-sbud-prepare-is-pcar-sbud-prepare and
; fn-pcar-sbud-prepare-is-sbud-prepare, every theorem about fn-sbud-prepare
; is about the host's call (fn-prc-sbud-prepare-of-refresh-is-pcar-sbud-prepare
; states the composition with the writer).

(in-package "ACL2")
(include-book "post-identity-index")
(include-book "replay-identity-index")

; -----------------------------------------------------------------------------
; 1. The id trie: path-compressed, leaves are the ledger's own id strings.
;
; A node at depth I is nil (empty), a string (a leaf: that one id, the
; ledger's own string object, never copied), or a branch: an alist
; (fn-midx-branch-get / -put) from the character at position I to the node
; one deeper, and :end to the bucket (a list) of the ids of length I.  A put
; that meets a leaf holding another id lifts the leaf one level
; (fn-rit-lift) and puts again, so an id is only as deep as the prefix it
; shares with another; for 10,000 random 64-hex ids that is about four
; levels, where the character trie of books/replay-identity-index.lisp is
; 64.  fn-rit-hasp-of-put holds for every node, well-formed or not: a lookup
; compares the whole id at a leaf, so a misplaced leaf is merely unreachable.

(defun fn-rit-hasp (id i node)
  (declare (xargs :guard (and (stringp id) (natp i))
                  :measure (nfix (- (length id) (nfix i)))))
  (cond ((stringp node) (equal node id))
        ((atom node) nil)
        ((and (mbt (and (stringp id) (natp i))) (< i (length id)))
         (fn-rit-hasp id (1+ i) (fn-midx-branch-get (char id i) node)))
        (t (if (fn-ag-member id (fn-midx-branch-get :end node)) t nil))))

(defun fn-rit-lift (old i)
  (declare (xargs :guard (and (stringp old) (natp i))))
  (if (and (mbt (and (stringp old) (natp i))) (< i (length old)))
      (list (cons (char old i) old))
    (list (cons :end (list old)))))

(defun fn-rit-put (new i node)
  (declare (xargs :guard (and (stringp new) (natp i))
                  :measure (+ (* 2 (nfix (- (length new) (nfix i))))
                              (if (stringp node) 1 0))))
  (cond ((stringp node)
         (if (equal node new)
             node
           (fn-rit-put new i (fn-rit-lift node i))))
        ((atom node) new)
        ((and (mbt (and (stringp new) (natp i))) (< i (length new)))
         (let ((key (char new i)))
           (fn-midx-branch-put
            key (fn-rit-put new (1+ i) (fn-midx-branch-get key node)) node)))
        (t (let ((bucket (fn-midx-branch-get :end node)))
             (if (fn-ag-member new bucket)
                 node
               (fn-midx-branch-put :end (cons new bucket) node))))))

; Every string stored anywhere in a node (the ids it can answer, and
; possibly unreachable ones): what the recognizer's soundness half reads.
(defun fn-rit-strings (x)
  (declare (xargs :guard t))
  (cond ((stringp x) (list x))
        ((atom x) nil)
        (t (append (fn-rit-strings (car x)) (fn-rit-strings (cdr x))))))

; A lookup at a leaf, a branch and an empty node.
(defthm fn-rit-hasp-of-leaf
  (implies (stringp node)
           (equal (fn-rit-hasp x i node) (equal node x)))
  :hints (("Goal" :expand ((fn-rit-hasp x i node)))))

(defthm fn-rit-hasp-of-branch
  (implies (consp node)
           (equal (fn-rit-hasp x i node)
                  (if (and (stringp x) (natp i) (< i (length x)))
                      (fn-rit-hasp x (+ 1 i)
                                   (fn-midx-branch-get (char x i) node))
                    (if (fn-ag-member x (fn-midx-branch-get :end node)) t nil))))
  :hints (("Goal" :expand ((fn-rit-hasp x i node)))))

(defthm fn-rit-hasp-of-atom
  (implies (and (atom node) (not (stringp node)))
           (not (fn-rit-hasp x i node)))
  :hints (("Goal" :expand ((fn-rit-hasp x i node)))))

; A character key is never the bucket key, and holds no string.
(local
 (defthm fn-rit-nth-char-list
   (implies (character-listp l)
            (or (characterp (nth i l)) (equal (nth i l) nil)))
   :rule-classes nil))

(defthm fn-rit-char-type
  (or (characterp (char x i)) (equal (char x i) nil))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable char)
           :use ((:instance fn-rit-nth-char-list (l (coerce x 'list)))))))

(defthm fn-rit-char-not-end
  (not (equal (char x i) :end)))

(local
 (defthm fn-rit-hasp-of-lift
   (implies (and (stringp x) (stringp old) (natp i))
            (equal (fn-rit-hasp x i (fn-rit-lift old i))
                   (equal x old)))
   :hints (("Goal" :in-theory (disable fn-rit-hasp)
            :cases ((< i (length x)))))))

(defthm fn-rit-hasp-of-put
  (implies (and (stringp x) (stringp new) (natp i))
           (iff (fn-rit-hasp x i (fn-rit-put new i node))
                (or (equal x new) (fn-rit-hasp x i node))))
  :hints (("Goal" :induct (fn-rit-put new i node)
           :in-theory (disable fn-rit-lift fn-rit-hasp char length))))

(local
 (defthm fn-rit-member-of-append
   (iff (member-equal y (append a b))
        (or (member-equal y a) (member-equal y b)))))

(local
 (defthm fn-rit-strings-of-branch-get
   (implies (not (member-equal y (fn-rit-strings a)))
           (not (member-equal y (fn-rit-strings (fn-midx-branch-get k a)))))))

(local
 (defthm fn-rit-strings-of-branch-put
   (implies (and (not (member-equal y (fn-rit-strings k)))
                 (not (member-equal y (fn-rit-strings v)))
                 (not (member-equal y (fn-rit-strings a))))
           (not (member-equal y (fn-rit-strings (fn-midx-branch-put k v a)))))))

(local
 (defthm fn-rit-strings-when-member
   (implies (and (stringp y) (member-equal y l))
            (member-equal y (fn-rit-strings l)))))

(local
 (defthm fn-rit-strings-of-char
   (equal (fn-rit-strings (char x i)) nil)
   :hints (("Goal" :in-theory (disable char)))))

(local
 (defthm fn-rit-strings-of-lift
   (implies (and (stringp old) (not (equal y old)))
            (not (member-equal y (fn-rit-strings (fn-rit-lift old i)))))
   :hints (("Goal" :in-theory (disable char)))))

(defthm fn-rit-strings-of-put
  (implies (and (stringp new)
                (not (equal y new))
                (not (member-equal y (fn-rit-strings node))))
           (not (member-equal y (fn-rit-strings (fn-rit-put new i node)))))
  :hints (("Goal" :induct (fn-rit-put new i node)
           :in-theory (disable fn-rit-lift char))))

(defthm fn-rit-hasp-is-stored
  (implies (and (fn-rit-hasp x i node) (stringp x))
           (member-equal x (fn-rit-strings node))))

(in-theory (disable fn-rit-hasp fn-rit-put fn-rit-lift))

; The set operations the carry uses: an id is a string at depth 0.
(defun fn-prc-has (id trie)
  (declare (xargs :guard t))
  (and (stringp id) (fn-rit-hasp id 0 trie)))

(defun fn-prc-add (id trie)
  (declare (xargs :guard t))
  (if (and (stringp id) (not (fn-rit-hasp id 0 trie)))
      (fn-rit-put id 0 trie)
    trie))

(defthm fn-prc-has-of-add
  (implies (stringp x)
           (iff (fn-prc-has x (fn-prc-add id trie))
                (or (equal x id) (fn-prc-has x trie)))))

(defthm fn-prc-strings-of-add
  (implies (and (not (equal y id)) (not (member-equal y (fn-rit-strings trie))))
           (not (member-equal y (fn-rit-strings (fn-prc-add id trie))))))

(defthm fn-prc-has-is-stored
  (implies (fn-prc-has x trie)
           (and (stringp x) (member-equal x (fn-rit-strings trie)))))

(in-theory (disable fn-prc-has fn-prc-add))

; -----------------------------------------------------------------------------
; 2. The trie of a ledger (the rebuild), and the carry's recognizer.

(defun fn-prc-add-pins (pins trie)
  (declare (xargs :guard t))
  (if (consp pins)
      (fn-prc-add-pins (cdr pins)
                       (fn-prc-add (fn-retain-obligation-id (car pins)) trie))
    trie))

(defun fn-prc-add-releases (releases trie)
  (declare (xargs :guard t))
  (if (consp releases)
      (fn-prc-add-releases (cdr releases)
                           (fn-prc-add (fn-retain-release-id (car releases))
                                       trie))
    trie))

(defthm fn-prc-has-of-add-pins
  (implies (stringp x)
           (iff (fn-prc-has x (fn-prc-add-pins pins trie))
                (or (member-equal x (fn-retain-obligation-ids pins))
                    (fn-prc-has x trie)))))

(defthm fn-prc-strings-of-add-pins
  (implies (and (not (member-equal y (fn-retain-obligation-ids pins)))
                (not (member-equal y (fn-rit-strings trie))))
           (not (member-equal y (fn-rit-strings (fn-prc-add-pins pins trie))))))

(defthm fn-prc-has-of-add-releases
  (implies (stringp x)
           (iff (fn-prc-has x (fn-prc-add-releases releases trie))
                (or (member-equal x (fn-retain-release-ids releases))
                    (fn-prc-has x trie)))))

(defthm fn-prc-strings-of-add-releases
  (implies (and (not (member-equal y (fn-retain-release-ids releases)))
                (not (member-equal y (fn-rit-strings trie))))
           (not (member-equal y (fn-rit-strings (fn-prc-add-releases releases trie))))))

(defun fn-prc-build (ledger)
  (declare (xargs :guard t))
  (fn-prc-add-pins (fn-retain-pins ledger)
                   (fn-prc-add-releases (fn-retain-releases ledger) nil)))

; The recognizer's halves.  Complete: every (string) id the ledger knows is
; in the trie.  Sound: every string stored in the trie is an id the ledger
; knows.  Each is a scan that returns its first counterexample (a witness
; the proofs instantiate), nil when there is none.
(defun fn-prc-pins-miss (pins trie)
  (declare (xargs :guard t))
  (if (consp pins)
      (let ((id (fn-retain-obligation-id (car pins))))
        (if (and (stringp id) (not (fn-prc-has id trie)))
            (list id)
          (fn-prc-pins-miss (cdr pins) trie)))
    nil))

(defun fn-prc-releases-miss (releases trie)
  (declare (xargs :guard t))
  (if (consp releases)
      (let ((id (fn-retain-release-id (car releases))))
        (if (and (stringp id) (not (fn-prc-has id trie)))
            (list id)
          (fn-prc-releases-miss (cdr releases) trie)))
    nil))

(defun fn-prc-unknown (strings ledger)
  (declare (xargs :guard t))
  (if (consp strings)
      (if (fn-rii-knownp (car strings) ledger)
          (fn-prc-unknown (cdr strings) ledger)
        (list (car strings)))
    nil))

(defun fn-prc-set-okp (ledger trie)
  (declare (xargs :guard t))
  (and (not (fn-prc-pins-miss (fn-retain-pins ledger) trie))
       (not (fn-prc-releases-miss (fn-retain-releases ledger) trie))
       (not (fn-prc-unknown (fn-rit-strings trie) ledger))))

(local
 (defthm fn-prc-pins-miss-when-member
   (implies (and (not (fn-prc-pins-miss pins trie))
                 (stringp x)
                 (member-equal x (fn-retain-obligation-ids pins)))
            (fn-prc-has x trie))))

(local
 (defthm fn-prc-pins-miss-witness
   (implies (fn-prc-pins-miss pins trie)
            (and (stringp (car (fn-prc-pins-miss pins trie)))
                 (member-equal (car (fn-prc-pins-miss pins trie))
                               (fn-retain-obligation-ids pins))
                 (not (fn-prc-has (car (fn-prc-pins-miss pins trie)) trie))))))

(local
 (defthm fn-prc-releases-miss-when-member
   (implies (and (not (fn-prc-releases-miss releases trie))
                 (stringp x)
                 (member-equal x (fn-retain-release-ids releases)))
            (fn-prc-has x trie))))

(local
 (defthm fn-prc-releases-miss-witness
   (implies (fn-prc-releases-miss releases trie)
            (and (stringp (car (fn-prc-releases-miss releases trie)))
                 (member-equal (car (fn-prc-releases-miss releases trie))
                               (fn-retain-release-ids releases))
                 (not (fn-prc-has (car (fn-prc-releases-miss releases trie))
                                  trie))))))

(local
 (defthm fn-prc-unknown-when-member
   (implies (and (not (fn-prc-unknown strings ledger))
                 (member-equal y strings))
            (fn-rii-knownp y ledger))
   :hints (("Goal" :in-theory (disable fn-rii-knownp-is-known-idp)))))

(local
 (defthm fn-prc-unknown-witness-member
   (implies (fn-prc-unknown strings ledger)
            (member-equal (car (fn-prc-unknown strings ledger)) strings))
   :hints (("Goal" :in-theory (disable fn-rii-knownp-is-known-idp)))))

(local
 (defthm fn-prc-unknown-witness-unknown
   (implies (fn-prc-unknown strings ledger)
            (not (fn-rii-knownp (car (fn-prc-unknown strings ledger))
                                ledger)))
   :hints (("Goal" :in-theory (disable fn-rii-knownp-is-known-idp)))))

(local
 (defthm fn-prc-unknown-witness
   (implies (fn-prc-unknown strings ledger)
            (and (member-equal (car (fn-prc-unknown strings ledger)) strings)
                 (not (fn-rii-knownp (car (fn-prc-unknown strings ledger))
                                     ledger))))
   :hints (("Goal" :in-theory (disable fn-rii-knownp-is-known-idp)))))

(local
 (defthm fn-prc-knownp-unfolds
   (iff (fn-rii-knownp id ledger)
        (or (member-equal id (fn-retain-obligation-ids (fn-retain-pins ledger)))
            (member-equal id (fn-retain-release-ids (fn-retain-releases ledger)))))
   :hints (("Goal" :in-theory (enable fn-retain-known-idp)
            :use fn-rii-knownp-is-known-idp))))

; What a reader uses: under the recognizer the trie answers, for every
; string, exactly whether the ledger knows it.
(defthm fn-prc-set-okp-is-knownp
  (implies (and (fn-prc-set-okp ledger trie) (stringp x))
           (iff (fn-prc-has x trie)
                (fn-rii-knownp x ledger)))
  :hints (("Goal" :in-theory (disable fn-prc-has-is-stored)
           :use ((:instance fn-prc-has-is-stored)
                 (:instance fn-prc-unknown-when-member
                            (y x) (strings (fn-rit-strings trie)))))))

(local
 (defthm fn-prc-strings-are-strings
   (implies (member-equal y (fn-rit-strings x)) (stringp y))))

(local
 (defthm fn-prc-build-is-known
   (implies (not (fn-rii-knownp y ledger))
            (not (member-equal y (fn-rit-strings (fn-prc-build ledger)))))))

(local
 (defthm fn-prc-build-has-known
   (implies (and (stringp x)
                 (or (member-equal x (fn-retain-obligation-ids
                                      (fn-retain-pins ledger)))
                     (member-equal x (fn-retain-release-ids
                                      (fn-retain-releases ledger)))))
            (fn-prc-has x (fn-prc-build ledger)))))

(defthm fn-prc-set-okp-of-build
  (fn-prc-set-okp ledger (fn-prc-build ledger))
  :hints (("Goal"
           :in-theory (disable fn-prc-pins-miss-witness fn-prc-releases-miss-witness
                               fn-prc-unknown-witness fn-prc-build
                               fn-prc-knownp-unfolds)
           :use ((:instance fn-prc-pins-miss-witness
                            (pins (fn-retain-pins ledger))
                            (trie (fn-prc-build ledger)))
                 (:instance fn-prc-releases-miss-witness
                            (releases (fn-retain-releases ledger))
                            (trie (fn-prc-build ledger)))
                 (:instance fn-prc-unknown-witness
                            (strings (fn-rit-strings (fn-prc-build ledger))))))))

(in-theory (disable fn-prc-set-okp))

(defun fn-prc-carryp (carry)
  (declare (xargs :guard t))
  (or (atom carry)
      (fn-prc-set-okp (car carry) (cdr carry))))

(defthm fn-prc-carryp-when-atom
  (implies (atom carry) (fn-prc-carryp carry)))

(defthm fn-prc-carryp-is-knownp
  (implies (and (fn-prc-carryp carry) (consp carry) (stringp x))
           (iff (fn-prc-has x (cdr carry))
                (fn-rii-knownp x (car carry))))
  :hints (("Goal" :use ((:instance fn-prc-set-okp-is-knownp
                                   (ledger (car carry)) (trie (cdr carry)))))))

; -----------------------------------------------------------------------------
; 3. The refresh: the same ledger keeps the carry; a ledger reached from the
; carried one by retention steps (releases consed on the carried releases;
; pins = new pins and the carried pins less released ones) applies that
; delta; anything else (the first POST, a recovery) rebuilds.

; RELEASES1 is RELEASES0 under a prefix of new releases.
(defun fn-prc-releases-tailp (r1 r0)
  (declare (xargs :guard t))
  (cond ((equal r1 r0) t)
        ((atom r1) nil)
        (t (fn-prc-releases-tailp (cdr r1) r0))))

; The ids of that prefix put into TRIE.
(defun fn-prc-add-new-releases (r1 r0 trie)
  (declare (xargs :guard t))
  (cond ((equal r1 r0) trie)
        ((atom r1) trie)
        (t (fn-prc-add-new-releases
            (cdr r1) r0 (fn-prc-add (fn-retain-release-id (car r1)) trie)))))

(defun fn-prc-new-release-idp (x r1 r0)
  (declare (xargs :guard t))
  (cond ((equal r1 r0) nil)
        ((atom r1) nil)
        (t (or (equal x (fn-retain-release-id (car r1)))
               (fn-prc-new-release-idp x (cdr r1) r0)))))

(defthm fn-prc-has-of-add-new-releases
  (implies (stringp x)
           (iff (fn-prc-has x (fn-prc-add-new-releases r1 r0 trie))
                (or (fn-prc-new-release-idp x r1 r0)
                    (fn-prc-has x trie))))
  :hints (("Goal" :induct (fn-prc-add-new-releases r1 r0 trie))))

(defthm fn-prc-strings-of-add-new-releases
  (implies (and (not (fn-prc-new-release-idp y r1 r0))
                (not (member-equal y (fn-rit-strings trie))))
           (not (member-equal y (fn-rit-strings (fn-prc-add-new-releases r1 r0 trie)))))
  :hints (("Goal" :induct (fn-prc-add-new-releases r1 r0 trie))))

(local
 (defthm fn-prc-new-release-idp-is-member
   (implies (fn-prc-new-release-idp x r1 r0)
            (member-equal x (fn-retain-release-ids r1)))))

(local
 (defthm fn-prc-releases-tailp-members
   (implies (fn-prc-releases-tailp r1 r0)
            (and (implies (member-equal x (fn-retain-release-ids r0))
                          (member-equal x (fn-retain-release-ids r1)))
                 (implies (member-equal x (fn-retain-release-ids r1))
                          (or (fn-prc-new-release-idp x r1 r0)
                              (member-equal x (fn-retain-release-ids r0))))))))

; Every carried pin's id is released (in RTRIE, the new releases' ids).
(defun fn-prc-all-released (p0 rtrie)
  (declare (xargs :guard t))
  (if (consp p0)
      (and (fn-prc-has (fn-retain-obligation-id (car p0)) rtrie)
           (fn-prc-all-released (cdr p0) rtrie))
    t))

; The pins walk: P1 against the carried P0.  A pin EQUAL to the carried
; head is carried; a carried head whose id was released is skipped; any
; other pin of P1 is new and its id is put.  After a skip or a put the rest
; is tried whole (EQUAL; one EQ test when P1's tail is P0's, which is how a
; commit's cons and a release's fn-retain-remove-id leave them), so a
; commit costs O(1) and a release O(position of the released pin), with no
; allocation but the put ids.  Returns (mv OK TRIE); not OK means the delta
; is not of this shape and the caller rebuilds.
(defun fn-prc-pins-walk (p1 p0 rtrie trie check)
  (declare (xargs :guard t :measure (+ (len p1) (len p0))))
  (cond ((and check (equal p1 p0)) (mv t trie))
        ((atom p1) (mv (fn-prc-all-released p0 rtrie) trie))
        ((and (consp p0) (equal (car p1) (car p0)))
         (fn-prc-pins-walk (cdr p1) (cdr p0) rtrie trie nil))
        ((and (consp p0)
              (fn-prc-has (fn-retain-obligation-id (car p0)) rtrie))
         (fn-prc-pins-walk p1 (cdr p0) rtrie trie t))
        (t (fn-prc-pins-walk (cdr p1) p0 rtrie
                             (fn-prc-add (fn-retain-obligation-id (car p1))
                                         trie)
                             t))))

(local
 (defthm fn-prc-all-released-member
   (implies (and (fn-prc-all-released p0 rtrie)
                 (member-equal x (fn-retain-obligation-ids p0)))
            (fn-prc-has x rtrie))))

(defthm fn-prc-pins-walk-monotone
  (implies (fn-prc-has x trie)
           (fn-prc-has x (mv-nth 1 (fn-prc-pins-walk p1 p0 rtrie trie check)))))

(defthm fn-prc-pins-walk-strings
  (implies (and (not (member-equal y (fn-rit-strings trie)))
                (not (member-equal y (fn-retain-obligation-ids p1))))
           (not (member-equal y (fn-rit-strings
                            (mv-nth 1 (fn-prc-pins-walk p1 p0 rtrie trie check)))))))

(defthm fn-prc-pins-walk-covers-new
  (implies (and (mv-nth 0 (fn-prc-pins-walk p1 p0 rtrie trie check))
                (stringp x)
                (member-equal x (fn-retain-obligation-ids p1)))
           (or (member-equal x (fn-retain-obligation-ids p0))
               (fn-prc-has x (mv-nth 1 (fn-prc-pins-walk p1 p0 rtrie trie check))))))

(defthm fn-prc-pins-walk-keeps-or-releases
  (implies (and (mv-nth 0 (fn-prc-pins-walk p1 p0 rtrie trie check))
                (member-equal x (fn-retain-obligation-ids p0)))
           (or (member-equal x (fn-retain-obligation-ids p1))
               (fn-prc-has x rtrie))))

(defun fn-prc-delta (carry ledger)
  (declare (xargs :guard (consp carry)))
  (let* ((l0 (car carry))
         (r0 (fn-retain-releases l0))
         (r1 (fn-retain-releases ledger)))
    (if (fn-prc-releases-tailp r1 r0)
        (mv-let (ok trie)
          (fn-prc-pins-walk (fn-retain-pins ledger) (fn-retain-pins l0)
                            (fn-prc-add-new-releases r1 r0 nil)
                            (cdr carry) t)
          (if ok (mv t (fn-prc-add-new-releases r1 r0 trie)) (mv nil nil)))
      (mv nil nil))))

(defun fn-prc-refresh (carry ledger)
  (declare (xargs :guard t))
  (if (and (consp carry) (equal (car carry) ledger))
      carry
    (mv-let (ok trie)
      (if (consp carry) (fn-prc-delta carry ledger) (mv nil nil))
      (if ok
          (cons ledger trie)
        (cons ledger (fn-prc-build ledger))))))

;; The delta's trie, in the carried ledger L0's and the new ledger L1's
;; terms, and what the three halves of the recognizer need of it.
(defmacro fn-prc-delta-trie (l1 l0 trie)
  `(fn-prc-add-new-releases
    (fn-retain-releases ,l1) (fn-retain-releases ,l0)
    (mv-nth 1 (fn-prc-pins-walk (fn-retain-pins ,l1) (fn-retain-pins ,l0)
                                (fn-prc-add-new-releases
                                 (fn-retain-releases ,l1)
                                 (fn-retain-releases ,l0) nil)
                                ,trie t))))

(defmacro fn-prc-delta-okp (l1 l0 trie)
  `(and (fn-prc-releases-tailp (fn-retain-releases ,l1) (fn-retain-releases ,l0))
        (mv-nth 0 (fn-prc-pins-walk (fn-retain-pins ,l1) (fn-retain-pins ,l0)
                                    (fn-prc-add-new-releases
                                     (fn-retain-releases ,l1)
                                     (fn-retain-releases ,l0) nil)
                                    ,trie t))))

(local
 (defthm fn-prc-has-of-nil
   (not (fn-prc-has x nil))
   :hints (("Goal" :in-theory (enable fn-prc-has)))))

(local
 (defthm fn-prc-delta-sound
   (implies (and (fn-prc-delta-okp l1 l0 trie)
                 (not (fn-prc-unknown (fn-rit-strings trie) l0))
                 (member-equal y (fn-rit-strings (fn-prc-delta-trie l1 l0 trie))))
            (fn-rii-knownp y l1))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (theory 'minimal-theory)
            :use ((:instance fn-prc-strings-of-add-new-releases
                             (r1 (fn-retain-releases l1)) (r0 (fn-retain-releases l0))
                             (trie (mv-nth 1 (fn-prc-pins-walk
                                              (fn-retain-pins l1) (fn-retain-pins l0)
                                              (fn-prc-add-new-releases
                                               (fn-retain-releases l1)
                                               (fn-retain-releases l0) nil)
                                              trie t))))
                  (:instance fn-prc-new-release-idp-is-member
                             (x y) (r1 (fn-retain-releases l1))
                             (r0 (fn-retain-releases l0)))
                  (:instance fn-prc-pins-walk-strings
                             (p1 (fn-retain-pins l1)) (p0 (fn-retain-pins l0))
                             (rtrie (fn-prc-add-new-releases
                                     (fn-retain-releases l1)
                                     (fn-retain-releases l0) nil))
                             (check t))
                  (:instance fn-prc-unknown-when-member
                             (strings (fn-rit-strings trie)) (ledger l0))
                  (:instance fn-prc-knownp-unfolds (id y) (ledger l0))
                  (:instance fn-prc-knownp-unfolds (id y) (ledger l1))
                  (:instance fn-prc-pins-walk-keeps-or-releases
                             (x y)
                             (p1 (fn-retain-pins l1)) (p0 (fn-retain-pins l0))
                             (rtrie (fn-prc-add-new-releases
                                     (fn-retain-releases l1)
                                     (fn-retain-releases l0) nil))
                             (check t))
                  (:instance fn-prc-has-of-add-new-releases
                             (x y) (r1 (fn-retain-releases l1))
                             (r0 (fn-retain-releases l0)) (trie nil))
                  (:instance fn-prc-has-of-nil (x y))
                  (:instance fn-prc-releases-tailp-members
                             (x y) (r1 (fn-retain-releases l1))
                             (r0 (fn-retain-releases l0)))
                  (:instance fn-prc-strings-are-strings
                             (x (fn-prc-delta-trie l1 l0 trie))))))))

(local
 (defthm fn-prc-delta-complete
   (implies (and (fn-prc-delta-okp l1 l0 trie)
                 (not (fn-prc-pins-miss (fn-retain-pins l0) trie))
                 (not (fn-prc-releases-miss (fn-retain-releases l0) trie))
                 (stringp x)
                 (or (member-equal x (fn-retain-obligation-ids (fn-retain-pins l1)))
                     (member-equal x (fn-retain-release-ids (fn-retain-releases l1)))))
            (fn-prc-has x (fn-prc-delta-trie l1 l0 trie)))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (theory 'minimal-theory)
            :use ((:instance fn-prc-pins-walk-covers-new
                             (p1 (fn-retain-pins l1)) (p0 (fn-retain-pins l0))
                             (rtrie (fn-prc-add-new-releases
                                     (fn-retain-releases l1)
                                     (fn-retain-releases l0) nil))
                             (check t))
                  (:instance fn-prc-pins-miss-when-member
                             (pins (fn-retain-pins l0)))
                  (:instance fn-prc-releases-miss-when-member
                             (releases (fn-retain-releases l0)))
                  (:instance fn-prc-pins-walk-monotone
                             (p1 (fn-retain-pins l1)) (p0 (fn-retain-pins l0))
                             (rtrie (fn-prc-add-new-releases
                                     (fn-retain-releases l1)
                                     (fn-retain-releases l0) nil))
                             (check t))
                  (:instance fn-prc-has-of-add-new-releases
                             (r1 (fn-retain-releases l1)) (r0 (fn-retain-releases l0))
                             (trie (mv-nth 1 (fn-prc-pins-walk
                                              (fn-retain-pins l1) (fn-retain-pins l0)
                                              (fn-prc-add-new-releases
                                               (fn-retain-releases l1)
                                               (fn-retain-releases l0) nil)
                                              trie t))))
                  (:instance fn-prc-releases-tailp-members
                             (r1 (fn-retain-releases l1))
                             (r0 (fn-retain-releases l0))))))))

; The delta keeps the recognizer: its trie is the carried one with the new
; pins' and new releases' ids put, and every carried id is still known
; (carried, or released).
(defthm fn-prc-set-okp-of-delta
  (implies (and (consp carry)
                (fn-prc-set-okp (car carry) (cdr carry))
                (mv-nth 0 (fn-prc-delta carry ledger)))
           (fn-prc-set-okp ledger (mv-nth 1 (fn-prc-delta carry ledger))))
  :hints (("Goal"
           :in-theory (e/d (fn-prc-set-okp)
                           (fn-prc-pins-miss-witness fn-prc-releases-miss-witness
                            fn-prc-unknown-witness fn-prc-pins-walk
                            fn-prc-add-new-releases fn-prc-releases-tailp
                            fn-prc-pins-miss fn-prc-releases-miss
                            fn-prc-unknown))
           :use ((:instance fn-prc-pins-miss-witness
                            (pins (fn-retain-pins ledger))
                            (trie (fn-prc-delta-trie ledger (car carry) (cdr carry))))
                 (:instance fn-prc-releases-miss-witness
                            (releases (fn-retain-releases ledger))
                            (trie (fn-prc-delta-trie ledger (car carry) (cdr carry))))
                 (:instance fn-prc-unknown-witness
                            (strings (fn-rit-strings
                                      (fn-prc-delta-trie ledger (car carry)
                                                         (cdr carry))))
                            (ledger ledger))
                 (:instance fn-prc-delta-complete
                            (l1 ledger) (l0 (car carry)) (trie (cdr carry))
                            (x (car (fn-prc-pins-miss
                                     (fn-retain-pins ledger)
                                     (fn-prc-delta-trie ledger (car carry)
                                                        (cdr carry))))))
                 (:instance fn-prc-delta-complete
                            (l1 ledger) (l0 (car carry)) (trie (cdr carry))
                            (x (car (fn-prc-releases-miss
                                     (fn-retain-releases ledger)
                                     (fn-prc-delta-trie ledger (car carry)
                                                        (cdr carry))))))
                 (:instance fn-prc-delta-sound
                            (l1 ledger) (l0 (car carry)) (trie (cdr carry))
                            (y (car (fn-prc-unknown
                                     (fn-rit-strings
                                      (fn-prc-delta-trie ledger (car carry)
                                                         (cdr carry)))
                                     ledger))))))))

(defthm fn-prc-carryp-of-refresh
  (implies (fn-prc-carryp carry)
           (fn-prc-carryp (fn-prc-refresh carry ledger)))
  :hints (("Goal" :in-theory (disable fn-prc-delta fn-prc-set-okp fn-prc-build))))

(defthm fn-prc-refresh-names-the-ledger
  (and (consp (fn-prc-refresh carry ledger))
       (equal (car (fn-prc-refresh carry ledger)) ledger)))

(in-theory (disable fn-prc-carryp fn-prc-refresh fn-prc-delta fn-prc-set-okp
                    fn-prc-build))

; -----------------------------------------------------------------------------
; 4. The admission through the carry.

; fn-retain-admissiblep, with the known-id test answered by the carried trie
; when the carry names this ledger.
(defun fn-prc-set-admissiblep (s id subject kind evidence charge trie)
  (declare (xargs :guard (fn-retain-statep s)
                  :guard-hints (("Goal" :in-theory (enable fn-retain-statep)))))
  (and (mbe :logic (fn-retain-statep s) :exec t)
       (stringp id)
       (stringp subject)
       (fn-retain-kindp kind)
       (fn-provp evidence)
       (posp charge)
       (not (fn-rit-hasp id 0 trie))
       (<= (+ (fn-retain-reserved s) charge)
           (fn-retain-capacity s))))

(defun fn-prc-admissiblep (s id subject kind evidence charge carry)
  (declare (xargs :guard (fn-retain-statep s)))
  (if (and (consp carry) (equal (car carry) s))
      (fn-prc-set-admissiblep s id subject kind evidence charge (cdr carry))
    (fn-retain-admissiblep s id subject kind evidence charge)))

(defthm fn-prc-admissiblep-is-admissiblep
  (implies (fn-prc-carryp carry)
           (equal (fn-prc-admissiblep s id subject kind evidence charge carry)
                  (fn-retain-admissiblep s id subject kind evidence charge)))
  :hints (("Goal" :in-theory (e/d (fn-retain-admissiblep fn-prc-has)
                                  (fn-retain-statep fn-prc-carryp-is-knownp))
           :use ((:instance fn-prc-carryp-is-knownp (x id))
                 (:instance fn-rii-knownp-is-known-idp (retention s))))))

; Where the carried test holds, so do the reference's conjuncts the admitted
; ledger's construction reads.
(defthm fn-prc-admissiblep-facts
  (implies (fn-prc-admissiblep s id subject kind evidence charge carry)
           (and (fn-retain-statep s) (stringp id) (stringp subject)
                (fn-retain-kindp kind) (fn-provp evidence) (posp charge)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-retain-admissiblep))))

(in-theory (disable fn-prc-admissiblep fn-prc-set-admissiblep))

; -----------------------------------------------------------------------------
; 5. The prepare chain: fn-pidx-* (books/post-identity-index.lisp) with the
; admission through the carry.

(defun fn-prc-node-prepare (s generation msgid payload groups
                              obligation-id subject evidence charge stamp
                              view carry)
  (declare (xargs :guard (fn-node-statep s) :verify-guards nil))
  (if (mbe :logic (not (fn-node-statep s)) :exec nil)
      s
    (let ((retention (fn-node-retention s)))
      (if (not (fn-prc-admissiblep retention obligation-id subject :archive
                                   evidence charge carry))
          s
        (let ((next-acceptance
               (fn-pidx-accept-prepare (fn-node-acceptance s)
                                       generation msgid payload groups stamp
                                       view)))
          (if (equal next-acceptance (fn-node-acceptance s))
              s
            (fn-node-make-state
             next-acceptance
             retention
             (fn-node-make-stage
              msgid generation obligation-id subject evidence charge
              (fn-retain-make-state
               (fn-retain-capacity retention)
               (+ (fn-retain-reserved retention) charge)
               (cons (fn-retain-make-obligation obligation-id subject :archive
                                                evidence charge)
                     (fn-retain-pins retention))
               (fn-retain-releases retention)))
             (fn-node-bindings s))))))))

(defthm fn-prc-node-prepare-is-pidx-node-prepare
  (implies (fn-prc-carryp carry)
           (equal (fn-prc-node-prepare s generation msgid payload groups
                                       obligation-id subject evidence charge
                                       stamp view carry)
                  (fn-pidx-node-prepare s generation msgid payload groups
                                        obligation-id subject evidence charge
                                        stamp view)))
  :hints (("Goal" :in-theory (e/d (fn-prc-node-prepare fn-pidx-node-prepare)
                                  (fn-node-statep fn-retain-admissiblep
                                   fn-pidx-accept-prepare fn-retain-make-state
                                   fn-retain-make-obligation
                                   fn-node-make-state fn-node-make-stage)))))

(verify-guards fn-prc-node-prepare
  :hints (("Goal" :in-theory (enable fn-node-statep))))

(in-theory (disable fn-prc-node-prepare))

(defun fn-prc-sn-prepare-node (node record view carry)
  (declare (xargs :guard (and (fn-node-statep node) (true-listp record))
                  :verify-guards nil))
  (fn-prc-node-prepare (fn-replay-advance-txid node (fn-record-txid record))
                       (fn-record-generation record) (fn-record-msgid record)
                       (fn-record-payload record) (fn-record-groups record)
                       (fn-record-obligation-id record)
                       (fn-record-content-subject record)
                       (fn-record-release-evidence record)
                       (fn-record-charge record)
                       (fn-record-stamp record)
                       view carry))

(verify-guards fn-prc-sn-prepare-node)

(defthm fn-prc-sn-prepare-node-is-pidx-sn-prepare-node
  (implies (fn-prc-carryp carry)
           (equal (fn-prc-sn-prepare-node node record view carry)
                  (fn-pidx-sn-prepare-node node record view)))
  :hints (("Goal" :in-theory (e/d (fn-prc-sn-prepare-node fn-pidx-sn-prepare-node)
                                  (fn-pidx-node-prepare fn-replay-advance-txid)))))

(in-theory (disable fn-prc-sn-prepare-node))

(defun fn-prc-spc-prepare (s record view carry)
  (declare (xargs :guard (and (fn-sn-statep s) (fn-pidx-view-okp view)
                              (fn-prc-carryp carry))
                  :verify-guards nil))
  (if (and (mbe :logic (fn-sn-statep s) :exec t)
           (equal (fn-sf-phase (fn-sn-files s)) :reserved)
           (null (fn-node-stage (fn-sn-node s)))
           (fn-held-p record)
           (not (equal (fn-record-stamp record) :legacy))
           (equal (fn-hc-generation (fn-held-context record))
                  (fn-sn-keyring-generation s))
           (eq (car (fn-rcon-cpe-projection-step
                     (fn-sn-consumer s) record (fn-sn-identity-next s))) :ok))
      (let* ((node (fn-prc-sn-prepare-node (fn-sn-node s) record view carry))
             (files (fn-pcar-stage-record (fn-sn-files s) record)))
        (if (and (fn-rcon-sn-record-bindsp node record)
                 (equal (fn-sf-phase files) :record-staged))
            (fn-sn-update s files node)
          s))
    s))

(defthm fn-prc-spc-prepare-is-pidx-spc-prepare
  (implies (fn-prc-carryp carry)
           (equal (fn-prc-spc-prepare s record view carry)
                  (fn-pidx-spc-prepare s record view)))
  :hints (("Goal" :in-theory (e/d (fn-prc-spc-prepare fn-pidx-spc-prepare)
                                  (fn-sn-statep fn-pcar-stage-record
                                   fn-pidx-sn-prepare-node fn-rcon-sn-record-bindsp
                                   fn-held-p fn-rcon-cpe-projection-step
                                   fn-sn-update)))))

(verify-guards fn-prc-spc-prepare
  :hints (("Goal" :use ((:instance fn-prc-spc-prepare-is-pidx-spc-prepare)
                        (:instance fn-pidx-spc-prepare-is-pcar-spc-prepare)
                        (:instance fn-pcar-spc-prepare-is-spc-prepare))
           :in-theory (e/d (fn-sn-statep)
                           (fn-sf-statep fn-node-statep fn-node-pending-matchesp
                            fn-sn-pending-record fn-sn-prepare-node
                            fn-pidx-view-okp fn-prc-carryp)))))

(in-theory (disable fn-prc-spc-prepare))

(defun fn-prc-opc-owner-prepare (o record carry)
  (declare (xargs :guard (and (fn-sn-statep (fn-own-store o))
                              (fn-pidx-view-okp (fn-own-view o))
                              (fn-prc-carryp carry))))
  (fn-own-refresh
   (fn-own-make (fn-prc-spc-prepare (fn-own-store o) record (fn-own-view o) carry)
                (fn-own-view o) (fn-own-conns o)
                (fn-own-next-id o) (fn-own-max-conns o)
                (fn-own-pending o) (fn-own-ledger o)
                (fn-own-clock o) (fn-own-facts o)
                (fn-own-config o) (fn-own-queue o)
                (fn-own-inflight o) (fn-own-feeds o) (fn-own-node-secret o) (fn-own-refused o))))

(defthm fn-prc-opc-owner-prepare-is-pidx-opc-owner-prepare
  (implies (fn-prc-carryp carry)
           (equal (fn-prc-opc-owner-prepare o record carry)
                  (fn-pidx-opc-owner-prepare o record)))
  :hints (("Goal" :in-theory (e/d (fn-prc-opc-owner-prepare
                                   fn-pidx-opc-owner-prepare)
                                  (fn-own-refresh fn-pidx-spc-prepare)))))

(in-theory (disable fn-prc-opc-owner-prepare))

(defun fn-prc-opc-prepare (oc record carry)
  (declare (xargs :guard (and (fn-sn-statep
                               (fn-own-store (fn-ocfg-owner oc)))
                              (fn-pidx-view-okp
                               (fn-own-view (fn-ocfg-owner oc)))
                              (fn-prc-carryp carry))))
  (fn-ocfg-with-owner
   oc (fn-prc-opc-owner-prepare (fn-ocfg-owner oc) record carry)))

(defthm fn-prc-opc-prepare-is-pidx-opc-prepare
  (implies (fn-prc-carryp carry)
           (equal (fn-prc-opc-prepare oc record carry)
                  (fn-pidx-opc-prepare oc record)))
  :hints (("Goal" :in-theory (e/d (fn-prc-opc-prepare fn-pidx-opc-prepare)
                                  (fn-pidx-opc-owner-prepare)))))

(in-theory (disable fn-prc-opc-prepare))

; The function host/owner-host.lisp fn-owner-prepare-buffer installs, with
; CARRY = (fn-prc-refresh <the global fn-owner-retain-carry> <the ledger of
; the owner's Store node>).
(defun fn-prc-sbud-prepare (oc record budget carry)
  (declare (xargs :guard (and (fn-sn-statep (fn-sbud-oc-store oc))
                              (fn-pidx-view-okp
                               (fn-own-view (fn-ocfg-owner oc)))
                              (fn-prc-carryp carry))))
  (if (fn-sbud-admitp budget (fn-sbud-count (fn-sbud-oc-store oc)))
      (fn-prc-opc-prepare oc record carry)
    oc))

; KEYSTONE.  Under the carry's recognizer (which no owner step can falsify),
; the host's prepare is PRF-191's, for every owner, record and budget.
(defthm fn-prc-sbud-prepare-is-pidx-sbud-prepare
  (implies (fn-prc-carryp carry)
           (equal (fn-prc-sbud-prepare oc record budget carry)
                  (fn-pidx-sbud-prepare oc record budget)))
  :hints (("Goal" :in-theory (e/d (fn-prc-sbud-prepare fn-pidx-sbud-prepare)
                                  (fn-pidx-opc-prepare fn-sbud-admitp
                                   fn-sbud-count fn-sbud-oc-store)))))

; The composition with the host's writer: the carry the host passes is the
; refresh of a value that has the recognizer; so the host's call is the
; carried prepare fn-pcar-sbud-prepare under PRF-191's three hypotheses.
(defthm fn-prc-sbud-prepare-of-refresh-is-pcar-sbud-prepare
  (implies (and (fn-prc-carryp carry)
                (fn-ocl-view-visiblep (fn-own-view (fn-ocfg-owner oc)))
                (fn-scar-view-indexedp (fn-ocfg-owner oc))
                (fn-ceis-indexedp (fn-sbud-oc-store oc)))
           (equal (fn-prc-sbud-prepare oc record budget
                                       (fn-prc-refresh carry ledger))
                  (fn-pcar-sbud-prepare oc record budget)))
  :hints (("Goal" :in-theory (disable fn-prc-sbud-prepare fn-pidx-sbud-prepare
                                      fn-pcar-sbud-prepare))))

(in-theory (disable fn-prc-sbud-prepare))
