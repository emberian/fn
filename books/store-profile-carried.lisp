; fn: the Store profile's admission, decided once per open (PRF-284).
;
; The served POST asked `fn-bs-profile-admittedp' of the owner's profile
; many times per article: every profile accessor (`fn-bs-profile-field')
; reads the profile through `fn-bs-profile-of', which validates the whole
; value (`fn-bs-profile-validp': the frame layout, each text field through
; the RFC 3629 decoder, every relation) before it reads one natural.  The
; article budget (`fn-cvec-article-budget-for') and the POST boundary
; (`fn-sbud-post-boundary') together ran that validation about a dozen
; times per POST (post-alloc-2's allocation profile: ~64 KB per POST).
;
; The profile is fixed for the life of an open: `fn-owner-install-profile'
; (host/owner-host.lisp) installs it once, recovery resets it to NIL, and no
; owner step writes it (books/store-budget.lisp says why it is fixed at
; init).  So its admission is decided once, where it is installed, and
; carried: CARRY = (PROFILE . ADMITTEDP), built by `fn-pvc-make'.  The
; recognizer `fn-pvc-carryp' says the verdict is the profile's; it names no
; owner state, so no owner transition can falsify it (the carry's only
; writer is `fn-pvc-make', `fn-pvc-carryp-of-make'; the reset value NIL
; satisfies it, `fn-pvc-carryp-when-atom').  A reader uses the carried
; verdict only when the carry names the profile in hand (`fn-pvc-admittedp':
; the host passes the same object, so the EQUAL is its EQ test) and decides
; afresh otherwise, so a stale carry costs time, never a wrong answer.
;
; Given the verdict V, every field read is `fn-pvc-pf': the raw field when V,
; else 0 (`fn-bs-profile-field-is-pvc-pf').  The twins below are the budget
; chain over V; each is equal to its original at V = the profile's own
; verdict, and the host-called functions are equal to the originals under
; `fn-pvc-carryp' (the three KEYSTONES at the end).
;
; Host calls: host/owner-host.lisp `fn-owner-prepare' and
; `fn-owner-prepare-buffer' call `fn-pvc-article-budget-carried' (for
; `fn-cvec-article-budget-for'), `fn-owner-post-boundary' calls
; `fn-pvc-post-boundary-carried' (for `fn-sbud-post-boundary'),
; `fn-owner-publication-verdict' calls `fn-pvc-verdict-carried' (for
; `fn-cvec-verdict-at'); `fn-owner-install-profile' writes `fn-pvc-make'.
(in-package "ACL2")
(include-book "store-capacity-vector")
(include-book "store-budget-naming")

; The verdict is opened only where a field is read through it
; (`fn-bs-profile-field-is-pvc-pf'); everywhere else it is an atom.
(local (in-theory (disable fn-bs-profile-admittedp fn-bs-profile-validp)))

; -----------------------------------------------------------------------------
; The carry

(defun fn-pvc-make (profile)
  "The carry of PROFILE: the profile and its admission verdict."
  (declare (xargs :guard t))
  (cons profile (fn-bs-profile-admittedp profile)))

(defun fn-pvc-carryp (carry)
  "CARRY's verdict is its profile's (or CARRY names no profile)."
  (declare (xargs :guard t))
  (or (atom carry)
      (equal (cdr carry) (fn-bs-profile-admittedp (car carry)))))

(defun fn-pvc-admittedp (carry profile)
  "PROFILE's admission: the carried verdict when CARRY names PROFILE."
  (declare (xargs :guard t))
  (if (and (consp carry) (equal (car carry) profile))
      (cdr carry)
    (fn-bs-profile-admittedp profile)))

(defthm fn-pvc-carryp-of-make
  (fn-pvc-carryp (fn-pvc-make profile)))

(defthm fn-pvc-carryp-when-atom
  (implies (atom carry) (fn-pvc-carryp carry)))

(defthm fn-pvc-admittedp-is-the-verdict
  (implies (fn-pvc-carryp carry)
           (equal (fn-pvc-admittedp carry profile)
                  (fn-bs-profile-admittedp profile))))

(in-theory (disable fn-pvc-make fn-pvc-carryp fn-pvc-admittedp))

; -----------------------------------------------------------------------------
; A field under a decided verdict

(defun fn-pvc-pf (v i profile)
  (declare (xargs :guard (natp i)))
  (if v (fn-bs-pf i profile) 0))

(local
 (defthm fn-pvc-meta-nth-of-nil
   (equal (fn-bs-meta-nth i nil) nil)
   :hints (("Goal" :in-theory (enable fn-bs-meta-nth)))))

(local
 (defthm fn-pvc-nil-is-no-profile
   (not (fn-bs-profile-validp nil))))

(defthm fn-bs-profile-field-is-pvc-pf
  (equal (fn-bs-profile-field i profile)
         (fn-pvc-pf (fn-bs-profile-admittedp profile) i profile))
  :hints (("Goal" :in-theory (e/d (fn-bs-profile-field fn-bs-profile-of
                                   fn-bs-profile-admittedp fn-bs-pf)
                                  (fn-bs-profile-validp)))))

(in-theory (disable fn-pvc-pf))

; -----------------------------------------------------------------------------
; The budget chain over the verdict V (twins of books/store-budget.lisp,
; store-budget-article, store-maintenance-reserve, store-capacity-vector)

(defun fn-pvc-budget (v profile kind)
  (declare (xargs :guard t))
  (if (and v (<= (fn-store-publication-ceiling kind) (fn-pvc-pf v *fn-bs-pf-max-record-octets* profile)))
      (fn-pvc-pf v *fn-bs-pf-max-transactions* profile)
    0))

(defun fn-pvc-history-admissiblep (v profile committed-octets prospective-octets)
  (declare (xargs :guard t))
  (and v
       (natp committed-octets) (natp prospective-octets)
       (<= (+ committed-octets prospective-octets) (fn-pvc-pf v *fn-bs-pf-max-history-octets* profile))))

(defun fn-pvc-sbud-verdict-at (v profile kind used bytes-used)
  (declare (xargs :guard t))
  (if (and (fn-sbud-admitp (fn-pvc-budget v profile kind) used)
           (fn-pvc-history-admissiblep v profile bytes-used
                                       (fn-store-publication-ceiling kind)))
      :admissible
    :unaffordable))

(defun fn-pvc-roomp (v profile used bytes-used debt)
  (declare (xargs :guard t))
  (and (natp used) (natp bytes-used)
       (equal (fn-pvc-sbud-verdict-at
               v profile :release (+ used (nfix debt))
               (+ bytes-used (* (nfix debt) (fn-smr-reserve-octets))))
              :admissible)))

(defun fn-pvc-verdict-at (v profile kind used bytes-used debt)
  (declare (xargs :guard t))
  (if (equal kind :release)
      (fn-pvc-sbud-verdict-at v profile kind used bytes-used)
    (if (and (equal (fn-pvc-sbud-verdict-at v profile kind used bytes-used)
                    :admissible)
             (fn-pvc-roomp v profile (+ 1 (nfix used))
                           (+ (nfix bytes-used)
                              (fn-store-publication-ceiling kind))
                           (fn-cvec-debt-step kind debt)))
        :admissible
      :unaffordable)))

(defun fn-pvc-statement-verdict-at (v profile used bytes-used group-count debt)
  (declare (xargs :guard t))
  (if (and (fn-sbud-admitp (fn-pvc-budget v profile :accepted-statement) used)
           (fn-pvc-history-admissiblep v profile bytes-used
                                       (fn-cvec-statement-figure group-count))
           (fn-pvc-roomp v profile (+ 1 (nfix used))
                         (+ (nfix bytes-used)
                            (fn-cvec-statement-figure group-count))
                         debt))
      :admissible
    :unaffordable))

(defun fn-pvc-article-budget (v profile used bytes-used payload-length
                                group-count debt)
  (declare (xargs :guard t))
  (let ((figure (fn-sbud-article-gate-figure payload-length group-count)))
    (if (and (fn-pvc-roomp v profile (+ 1 (nfix used))
                           (+ (nfix bytes-used) figure) debt)
             (fn-pvc-history-admissiblep v profile bytes-used figure))
        (fn-pvc-budget v profile :article)
      0)))

(defun fn-pvc-article-budget-for (v profile used bytes-used record debt)
  (declare (xargs :guard t))
  (fn-pvc-article-budget v profile used bytes-used
                         (len (fn-record-payload record))
                         (len (fn-record-groups record)) debt))

(defun fn-pvc-post-boundary (v profile msgid payload-length group-count charge)
  (declare (xargs :guard t))
  (cond ((not (fn-af-message-idp msgid)) :bad-message-id)
        ((or (not (natp payload-length))
             (< (fn-pvc-pf v *fn-bs-pf-max-article-octets* profile) payload-length))
         :payload-bound)
        ((or (not (posp group-count))
             (< (fn-pvc-pf v *fn-bs-pf-max-groups-per-article* profile) group-count))
         :group-bound)
        ((or (not (posp charge)) (< *fn-cbor-max-uint* charge))
         :charge-bound)
        (t :ok)))

; -----------------------------------------------------------------------------
; Each twin at the profile's own verdict is the original

(local (in-theory (disable fn-bs-profile-admittedp fn-bs-profile-field
                           fn-sbud-article-figure fn-sbud-article-gate-figure fn-store-publication-ceiling
                           fn-smr-reserve-octets fn-af-message-idp)))

(defthm fn-pvc-budget-is-sbud-budget
  (implies (equal v (fn-bs-profile-admittedp profile))
    (equal (fn-pvc-budget v profile kind)
           (fn-sbud-budget profile kind)))
  :hints (("Goal" :in-theory (enable fn-sbud-budget
                                     fn-bs-profile-record-ceiling
                                     fn-bs-profile-max-record-octets
                                     fn-bs-profile-max-transactions
                                     fn-pvc-pf))))

(defthm fn-pvc-history-admissiblep-is-bs-history-admissiblep
  (implies (equal v (fn-bs-profile-admittedp profile))
    (equal (fn-pvc-history-admissiblep v profile
                                       committed prospective)
           (fn-bs-history-admissiblep profile committed prospective)))
  :hints (("Goal" :in-theory (enable fn-bs-history-admissiblep
                                     fn-bs-profile-max-history-octets
                                     fn-pvc-pf))))

(in-theory (disable fn-pvc-budget fn-pvc-history-admissiblep))

(defthm fn-pvc-sbud-verdict-at-is-sbud-verdict-at
  (implies (equal v (fn-bs-profile-admittedp profile))
    (equal (fn-pvc-sbud-verdict-at v profile
                                   kind used bytes-used)
           (fn-sbud-verdict-at profile kind used bytes-used)))
  :hints (("Goal" :in-theory (e/d (fn-sbud-verdict-at)
                                  (fn-sbud-admitp fn-sbud-budget
                                   fn-bs-history-admissiblep)))))

(in-theory (disable fn-pvc-sbud-verdict-at))

(defthm fn-pvc-roomp-is-cvec-roomp
  (implies (equal v (fn-bs-profile-admittedp profile))
    (equal (fn-pvc-roomp v profile
                         used bytes-used debt)
           (fn-cvec-roomp profile used bytes-used debt)))
  :hints (("Goal" :in-theory (e/d (fn-cvec-roomp fn-smr-roomp)
                                  (fn-sbud-verdict-at)))))

(in-theory (disable fn-pvc-roomp))

(defthm fn-pvc-verdict-at-is-cvec-verdict-at
  (implies (equal v (fn-bs-profile-admittedp profile))
    (equal (fn-pvc-verdict-at v profile
                              kind used bytes-used debt)
           (fn-cvec-verdict-at profile kind used bytes-used debt)))
  :hints (("Goal" :in-theory (e/d (fn-cvec-verdict-at)
                                  (fn-sbud-verdict-at fn-cvec-roomp
                                   fn-cvec-debt-step)))))

(defthm fn-pvc-statement-verdict-at-is-cvec-statement-verdict-at
  (implies (equal v (fn-bs-profile-admittedp profile))
    (equal (fn-pvc-statement-verdict-at v profile used bytes-used group-count
                                        debt)
           (fn-cvec-statement-verdict-at profile used bytes-used group-count
                                         debt)))
  :hints (("Goal" :in-theory (e/d (fn-cvec-statement-verdict-at)
                                  (fn-sbud-admitp fn-sbud-budget
                                   fn-bs-history-admissiblep fn-cvec-roomp
                                   fn-cvec-statement-figure)))))

(defthm fn-pvc-article-budget-is-cvec-article-budget
  (implies (equal v (fn-bs-profile-admittedp profile))
    (equal (fn-pvc-article-budget v profile
                                  used bytes-used payload-length group-count debt)
           (fn-cvec-article-budget profile used bytes-used payload-length
                                   group-count debt)))
  :hints (("Goal" :in-theory (e/d (fn-cvec-article-budget
                                   fn-sbud-article-budget)
                                  (fn-cvec-roomp fn-sbud-budget
                                   fn-bs-history-admissiblep)))))

(defthm fn-pvc-post-boundary-is-sbud-post-boundary
  (implies (equal v (fn-bs-profile-admittedp profile))
    (equal (fn-pvc-post-boundary v profile
                                 msgid payload-length group-count charge)
           (fn-sbud-post-boundary profile msgid payload-length group-count
                                  charge)))
  :hints (("Goal" :in-theory (enable fn-sbud-post-boundary
                                     fn-sbud-payload-bound
                                     fn-sbud-group-bound
                                     fn-bs-profile-max-article-octets
                                     fn-bs-profile-max-groups-per-article))))

(in-theory (disable fn-pvc-verdict-at fn-pvc-article-budget
                    fn-pvc-statement-verdict-at fn-pvc-post-boundary))

; -----------------------------------------------------------------------------
; The host-called functions

(defun fn-pvc-article-budget-carried (carry profile used bytes-used record debt)
  "The served POST's transaction budget under the carried verdict."
  (declare (xargs :guard t))
  (fn-pvc-article-budget-for (fn-pvc-admittedp carry profile) profile
                             used bytes-used record debt))

(defun fn-pvc-verdict-carried (carry profile kind used bytes-used debt)
  "The publication verdict for one more record of KIND under the carried verdict."
  (declare (xargs :guard t))
  (fn-pvc-verdict-at (fn-pvc-admittedp carry profile) profile
                     kind used bytes-used debt))

(defun fn-pvc-statement-verdict-carried (carry profile used bytes-used
                                                group-count debt)
  "The publication verdict for one accepted-statement composite in
GROUP-COUNT groups under the carried verdict."
  (declare (xargs :guard t))
  (fn-pvc-statement-verdict-at (fn-pvc-admittedp carry profile) profile
                               used bytes-used group-count debt))

(defun fn-pvc-post-boundary-carried (carry profile msgid payload-length
                                           group-count charge)
  "The POST admission boundary under the carried verdict."
  (declare (xargs :guard t))
  (fn-pvc-post-boundary (fn-pvc-admittedp carry profile) profile
                        msgid payload-length group-count charge))

; KEYSTONE (the served POST's budget).  Under a carry whose verdict is its
; profile's, the budget the host hands the prepare is
; `fn-cvec-article-budget-for' of the profile in hand, whatever profile the
; carry names.
(defthm fn-pvc-article-budget-carried-is-cvec-article-budget-for
  (implies (fn-pvc-carryp carry)
           (equal (fn-pvc-article-budget-carried carry profile used bytes-used
                                                 record debt)
                  (fn-cvec-article-budget-for profile used bytes-used
                                              record debt)))
  :hints (("Goal" :in-theory (enable fn-cvec-article-budget-for))))

; KEYSTONE (the owner's publication verdict).
(defthm fn-pvc-verdict-carried-is-cvec-verdict-at
  (implies (fn-pvc-carryp carry)
           (equal (fn-pvc-verdict-carried carry profile kind used bytes-used
                                          debt)
                  (fn-cvec-verdict-at profile kind used bytes-used debt))))

; KEYSTONE (the identity preflight's composite verdict; lane
; bp-retention-leftovers).  Host line: host/owner-host.lisp
; `fn-owner-identity-publication-verdict', asked by host/native/owner.lisp
; `fnn-owner-identity-commit' for an accepted-statement composite.
(defthm fn-pvc-statement-verdict-carried-is-cvec-statement-verdict-at
  (implies (fn-pvc-carryp carry)
           (equal (fn-pvc-statement-verdict-carried carry profile used
                                                    bytes-used group-count debt)
                  (fn-cvec-statement-verdict-at profile used bytes-used
                                                group-count debt))))

; KEYSTONE (the POST admission boundary).
(defthm fn-pvc-post-boundary-carried-is-sbud-post-boundary
  (implies (fn-pvc-carryp carry)
           (equal (fn-pvc-post-boundary-carried carry profile msgid
                                                payload-length group-count
                                                charge)
                  (fn-sbud-post-boundary profile msgid payload-length
                                         group-count charge))))

(in-theory (disable fn-pvc-article-budget-carried fn-pvc-verdict-carried
                    fn-pvc-statement-verdict-carried
                    fn-pvc-post-boundary-carried))
