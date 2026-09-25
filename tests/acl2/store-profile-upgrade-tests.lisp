; Teeth for books/store-profile-upgrade and books/byte-store-profile-program:
; the upgrade relation over the named profiles, the operator verdict, one
; must-fail per keystone hypothesis at constants, and reachable witnesses of
; the byte program's crash keystone at its rename cut.
(in-package "ACL2")
(include-book "../../books/store-profile-upgrade")
(include-book "../../books/byte-store-profile-program")
(include-book "std/testing/must-fail" :dir :system)

(defconst *sput-dev* *fn-bs-profile-development*)
(defconst *sput-scale* *fn-bs-profile-scale*)
(defconst *sput-7dev* *fn-bs-meta-format-7-development-values*)
(defconst *sput-7scale* *fn-bs-meta-format-7-scale-values*)
; A free-field profile no preset equals: T = 1000, K = 1000, the default's
; 1 TiB history, 64 MiB records and 16 MiB articles, and G at the codec
; ceiling 65 535, as development's is (the defaults' 4096 is below it), so
; that it upgrades from development.
(defconst *sput-free*
  (fn-bs-profile-set-fields *fn-bs-profile-defaults*
                            '((2 . 1000) (8 . 1000) (6 . 65535))))

; -----------------------------------------------------------------------------
; The relation: valid NEW, admitted OLD, different, no field smaller.

(assert-event (fn-bs-profile-validp *sput-free*))
(assert-event (fn-profile-upgradep *sput-dev* *sput-scale*))
(assert-event (not (fn-profile-upgradep *sput-7dev* *sput-7scale*)))  ; NEW is format 8
(assert-event (fn-profile-upgradep *sput-7dev* *sput-scale*))
(assert-event (not (fn-profile-upgradep *sput-dev* *sput-dev*)))       ; no-op
(assert-event (not (fn-profile-upgradep *sput-scale* *sput-dev*)))     ; downgrade
(assert-event (not (fn-profile-upgradep '(1 2 3 4 5 6) *sput-scale*)))  ; not a profile
; The free profile upgrades from development (every field at least), and
; refuses a shrink: back to development, or its own T lowered.
(assert-event (fn-profile-upgradep *sput-dev* *sput-free*))
(assert-event (fn-profile-upgradep *sput-7dev* *sput-free*))
(assert-event (not (fn-profile-upgradep *sput-free* *sput-dev*)))
(assert-event (not (fn-profile-upgradep
                    *sput-free*
                    (fn-bs-profile-set-fields *sput-free* '((2 . 999) (8 . 999))))))
(assert-event (equal (fn-profile-shrunk-field *sput-free* *sput-dev*
                                              *fn-bs-profile-field-names*)
                     "max-transactions"))
; Not an upgrade to scale: the free profile's T is below scale's 4096.
(assert-event (not (fn-profile-upgradep *sput-scale* *sput-free*)))

; The verdict the verb acts on.
(assert-event (equal (fn-profile-upgrade-verdict *sput-dev* :development)
                     '(:refused :same-profile)))
(assert-event (equal (fn-profile-upgrade-verdict *sput-scale* :scale)
                     '(:refused :same-profile)))
(assert-event (equal (fn-profile-upgrade-verdict *sput-scale* :development)
                     '(:refused :not-an-upgrade "max-transactions")))
(assert-event (equal (fn-profile-upgrade-verdict *sput-dev* :huge)
                     '(:refused :unknown-profile)))
(assert-event (equal (fn-profile-upgrade-verdict nil :scale)
                     '(:refused :invalid-current-profile)))
(assert-event (equal (car (fn-profile-upgrade-verdict *sput-dev* :scale)) :upgrade))
(assert-event (equal (cddr (fn-profile-upgrade-verdict *sput-dev* :scale))
                     '(128 4096)))
; The octets it writes are the scale frame `init --profile scale' writes.
(assert-event (equal (cadr (fn-profile-upgrade-verdict *sput-dev* :scale))
                     (fn-bs-config-frame-for-profile :scale)))
(assert-event (equal (fn-bs-config-decode
                      (cadr (fn-profile-upgrade-verdict *sput-dev* :scale)))
                     *sput-scale*))
; The operator's request, over the store's current profile: raise T and H.
(assert-event (equal (cddr (fn-profile-upgrade-verdict
                            *sput-dev* '(:current ((2 . 1000) (3 . 1099511627776)))))
                     '(128 1000)))
(assert-event (equal (fn-bs-config-decode
                      (cadr (fn-profile-upgrade-verdict
                             *sput-dev* '(:current ((2 . 1000) (3 . 1099511627776))))))
                     (fn-bs-profile-set-fields *sput-dev*
                                               '((2 . 1000) (3 . 1099511627776)))))
; Lowering A below development's is a shrink, refused by its name.
(assert-event (equal (fn-profile-upgrade-verdict *sput-dev* '(:current ((5 . 20000))))
                     '(:refused :not-an-upgrade "max-article-octets")))
; A request that shrinks a field is refused by the field's name; one that
; breaks a relation by the relation's name; nothing is written for either.
(assert-event (equal (fn-profile-upgrade-verdict *sput-scale* '(:current ((2 . 1000))))
                     '(:refused :not-an-upgrade "max-transactions")))
(assert-event (equal (fn-profile-upgrade-verdict *sput-dev* '(:current ((3 . 1000))))
                     '(:refused :max-history-octets-below-max-record-octets)))
(assert-event (equal (fn-profile-upgrade-verdict *sput-dev* '(:current ((99 . 1))))
                     '(:refused :unknown-profile)))

; The format 7 to 8 step (fn-profile-upgrade-format-7-to-8): a format-7 store
; with no field named writes its translation, budgets unchanged; with a raise
; it writes the raised format-8 profile.  A format-8 store asked for the same
; is the same profile.
(assert-event (equal (car (fn-profile-upgrade-verdict *sput-7scale* '(:current nil)))
                     :upgrade))
(assert-event (equal (fn-bs-config-decode
                      (cadr (fn-profile-upgrade-verdict *sput-7scale* '(:current nil))))
                     *sput-scale*))
(assert-event (equal (cddr (fn-profile-upgrade-verdict *sput-7scale* '(:current nil)))
                     '(4096 4096)))
(assert-event (equal (cddr (fn-profile-upgrade-verdict *sput-7scale*
                                                       '(:current ((2 . 100000)))))
                     '(4096 100000)))
(assert-event (equal (fn-profile-upgrade-verdict *sput-scale* '(:current nil))
                     '(:refused :same-profile)))
; A 7-to-8 translation that shrinks is refused: format-7 scale to the
; development preset lowers max_transactions.
(assert-event (equal (fn-profile-upgrade-verdict *sput-7scale* :development)
                     '(:refused :not-an-upgrade "max-transactions")))
; Tooth for fn-profile-upgrade-format-7-to-8: its hypothesis is the format-7
; tuple; a format-8 profile is not upgraded to itself.
(must-fail
 (defthm sput-7-to-8-without-format-7
   (fn-profile-upgradep *sput-scale* (fn-bs-profile-from-format-7 *sput-scale*))))

; -----------------------------------------------------------------------------
; fn-profile-upgrade-keeps-txn-observation

(defun sput-names (i n)
  (declare (xargs :measure (nfix (- n i))))
  (if (and (natp i) (natp n) (< i n))
      (cons (fn-bs-txn-name-impl i) (sput-names (1+ i) n))
    nil))
(defconst *sput-129* (sput-names 0 129))
(defconst *sput-200* (sput-names 0 200))
; Witness: 129 committed names are one past the development bound and
; well inside scale's; 127 are inside both, with the same observation.
(assert-event (equal (fn-profile-txn-observation *sput-129* 128 0) :invalid))
(assert-event (not (equal (fn-profile-txn-observation *sput-129* 4096 0) :invalid)))
(assert-event (equal (fn-profile-txn-observation (sput-names 0 127) 4096 0)
                     (fn-profile-txn-observation (sput-names 0 127) 128 0)))
(assert-event (equal (len (caddr (fn-profile-txn-observation (sput-names 0 127) 128 0)))
                     127))
; Without the upgrade (scale to development) the 129-name observation is lost.
(must-fail
 (defthm sput-txn-without-upgradep
   (equal (fn-profile-txn-observation *sput-129* (fn-bs-profile-max-transactions *sput-dev*) 0)
          (fn-profile-txn-observation *sput-129* (fn-bs-profile-max-transactions *sput-scale*) 0))))
; Without the old observation being valid: 200 names are invalid under
; development and valid under scale, so the two differ.
(must-fail
 (defthm sput-txn-without-valid-old
   (equal (fn-profile-txn-observation *sput-200* (fn-bs-profile-max-transactions *sput-scale*) 0)
          (fn-profile-txn-observation *sput-200* (fn-bs-profile-max-transactions *sput-dev*) 0))))

; -----------------------------------------------------------------------------
; fn-profile-upgrade-keeps-replay-bound: 24 MiB under development, 768 MiB
; under scale.

(assert-event (fn-profile-replay-within-boundp *sput-dev* 25165824))
(assert-event (not (fn-profile-replay-within-boundp *sput-dev* 25165825)))
(assert-event (fn-profile-replay-within-boundp *sput-scale* 25165825))
(must-fail
 (defthm sput-replay-without-upgradep
   (implies (fn-profile-replay-within-boundp *sput-scale* 30000000)
            (fn-profile-replay-within-boundp *sput-dev* 30000000))))
(must-fail
 (defthm sput-replay-without-bound
   (fn-profile-replay-within-boundp *sput-scale* 900000000)))

; -----------------------------------------------------------------------------
; fn-profile-upgrade-keeps-publication-admissibility and -keeps-verdict

(defun sput-store (n)
  (declare (xargs :guard (natp n)))
  (list nil nil
        (list :store-files :ready n nil (make-list n) nil nil nil 0)))
(defconst *sput-ceiling* (fn-store-publication-ceiling :article))
(assert-event (fn-bs-publication-admissiblep *sput-dev* 127 *sput-ceiling*))
(assert-event (fn-bs-publication-admissiblep *sput-scale* 127 *sput-ceiling*))
(assert-event (not (fn-bs-publication-admissiblep *sput-dev* 200 *sput-ceiling*)))
(must-fail
 (defthm sput-admissible-without-upgradep
   (implies (fn-bs-publication-admissiblep *sput-scale* 200 *sput-ceiling*)
            (fn-bs-publication-admissiblep *sput-dev* 200 *sput-ceiling*))))
(must-fail
 (defthm sput-admissible-without-old-admissible
   (fn-bs-publication-admissiblep *sput-scale* 5000 *sput-ceiling*)))

; The deployed shape: 128 used under development is refused, and the same
; store after the upgrade is admitted.
(assert-event (equal (fn-sbud-verdict *sput-dev* :article (sput-store 128)) :unaffordable))
(assert-event (equal (fn-sbud-verdict *sput-scale* :article (sput-store 128)) :admissible))
(assert-event (equal (fn-sbud-verdict *sput-dev* :article (sput-store 3)) :admissible))
(assert-event (equal (fn-sbud-verdict *sput-scale* :article (sput-store 3)) :admissible))
(must-fail
 (defthm sput-verdict-without-upgradep
   (implies (equal (fn-sbud-verdict *sput-scale* :article (sput-store 200)) :admissible)
            (equal (fn-sbud-verdict *sput-dev* :article (sput-store 200)) :admissible))))
(must-fail
 (defthm sput-verdict-without-old-admissible
   (equal (fn-sbud-verdict *sput-scale* :article (sput-store 4096)) :admissible)))

; fn-profile-upgrade-verdict-writes-only-upgrades: its hypothesis is the
; :upgrade tag; a :refused verdict's second element is a reason, which does
; not decode to the named profile.
(must-fail
 (defthm sput-writes-without-upgrade-tag
   (equal (fn-bs-config-decode (cadr (fn-profile-upgrade-verdict *sput-dev* :development)))
          (fn-bs-config-for-profile :development))))

; -----------------------------------------------------------------------------
; fn-bs-profile-program-crash-is-old-or-new: a reachable run.  A quiet store
; whose config.json is inode 3 (holding '(7 7)), next inode 5, empty staging.

(defconst *sput-bs*
  (fn-bs-make 4 (list (cons 3 '(7 7)))
              (list (cons :root (list (cons "config.json" 3)))
                    (cons :staging nil))
              nil 5))
(defconst *sput-run*
  (fn-bs-run *sput-bs* nil (fn-bs-profile-program ".stage-profile-1" '(1 2 3))
             nil nil 0))
(assert-event (fn-bs-profile-inputp *sput-bs* ".stage-profile-1" 3))
(assert-event (equal (len *sput-run*) 10))
; At the rename cut (the eighth pair) both images are reachable: the
; replacement dropped keeps inode 3 and '(7 7); applied, inode 5 and the
; staged octets.  Neither is torn and neither is empty.
(defconst *sput-renamed* (car (nth 7 *sput-run*)))
(assert-event (equal (fn-bs-durable-entry (fn-bs-crash *sput-renamed* '(:drop :drop :drop))
                                          :root "config.json")
                     3))
(assert-event (equal (fn-bs-durable-entry (fn-bs-crash *sput-renamed* '(:drop :apply :drop))
                                          :root "config.json")
                     5))
(assert-event (fn-bs-profile-old-or-newp
               (fn-bs-crash *sput-renamed* '(:drop :drop :drop)) *sput-bs* 3 '(1 2 3)))
(assert-event (fn-bs-profile-old-or-newp
               (fn-bs-crash *sput-renamed* '(:drop :apply :drop)) *sput-bs* 3 '(1 2 3)))
; At the write cut the new inode is torn in a crash (a zeroed unit), but
; config.json still names inode 3: the torn bytes are never named.
(defconst *sput-written* (car (nth 2 *sput-run*)))
(assert-event (fn-bs-profile-old-or-newp
               (fn-bs-crash *sput-written* '(:apply (:zero))) *sput-bs* 3 '(1 2 3)))
; The same program from a store with a pending write to config.json's inode
; (the quiet hypothesis dropped) has a crash image holding a third content.
(defconst *sput-busy*
  (fn-bs-make 4 (list (cons 3 '(7 7)))
              (list (cons :root (list (cons "config.json" 3)))
                    (cons :staging nil))
              (list (list :write 3 0 '(9 9)))
              5))
(defconst *sput-busy-run*
  (fn-bs-run *sput-busy* nil (fn-bs-profile-program ".stage-profile-1" '(1 2 3))
             nil nil 0))
(must-fail
 (defthm sput-crash-without-quiet-store
   (fn-bs-profile-old-or-newp (fn-bs-crash (car (nth 0 *sput-busy-run*)) '((:new) :drop))
                              *sput-busy* 3 '(1 2 3))))
; Without the program run (a step list that renames an unfenced stage), the
; name reaches a torn inode: the program's order is what the keystone spends.
(defconst *sput-unfenced*
  (fn-bs-run *sput-bs* nil
             (list (list :create :staging ".stage-profile-1")
                   (list :write-all :staging ".stage-profile-1" '(1 2 3))
                   (list :rename :staging ".stage-profile-1" :root "config.json"))
             nil nil 0))
(must-fail
 (defthm sput-crash-without-the-program
   (fn-bs-profile-old-or-newp (fn-bs-crash (car (nth 2 *sput-unfenced*))
                                           '(:apply (:zero) :apply :drop))
                              *sput-bs* 3 '(1 2 3))))

; -----------------------------------------------------------------------------
; `store needs-upgrade' and the rollback check (PKT-099):
; fn-profile-needs-upgrade-verdict and fn-profile-rollback-verdict, which
; host/native/io.lisp fnn-command-needs-upgrade and fnn-command-rollback-check
; call.

(assert-event (equal (fn-profile-needs-upgrade-verdict *sput-7scale*) :needs-upgrade))
(assert-event (equal (fn-profile-needs-upgrade-verdict *sput-7dev*) :needs-upgrade))
(assert-event (equal (fn-profile-needs-upgrade-verdict *sput-scale*) :current))
(assert-event (equal (fn-profile-needs-upgrade-verdict *sput-dev*) :current))
(assert-event (equal (fn-profile-needs-upgrade-verdict nil) :invalid-current-profile))
; Teeth: without admission the statement fails (nil is no format-7 tuple, but
; a format-7-shaped tuple whose translation is invalid is not admitted).
; Teeth for fn-profile-format-7-store-needs-upgrade.  Without the format-7
; hypothesis it fails: the admitted scale preset answers :current (above).
; Without admission it fails: a value that is not a profile answers
; :invalid-current-profile (above).  Each must-fail keeps the prover to the
; evaluated counterexample's facts.
(must-fail
 (defthm sput-format-7-needs-upgrade-without-format-7
   (implies (fn-bs-profile-admittedp current)
            (equal (fn-profile-needs-upgrade-verdict current) :needs-upgrade))
   :hints (("Goal" :in-theory (disable fn-profile-needs-upgrade-verdict
                                       fn-bs-profile-admittedp)))))
(must-fail
 (defthm sput-needs-upgrade-without-admission
   (equal (fn-profile-needs-upgrade-verdict current) :needs-upgrade)
   :hints (("Goal" :in-theory (disable fn-profile-needs-upgrade-verdict)))))

; Rollback: the format-7 scale tuple's image read records up to H / T =
; 196,608 octets; the format-8 scale preset's R is its own.
(assert-event (equal (fn-profile-rollback-record-bound *sput-7scale*) 196608))
(assert-event (equal (fn-profile-rollback-verdict *sput-7scale* '(900 196608)) '(:sound)))
(assert-event
 (equal (fn-profile-rollback-verdict *sput-7scale* '(900 196609 12))
        '(:refused :record-exceeds-rollback-profile 1 196609 196608)))
(assert-event
 (equal (fn-profile-rollback-verdict nil '(1)) '(:refused :invalid-rollback-profile)))
(assert-event
 (equal (fn-profile-rollback-verdict *sput-scale* nil) '(:sound)))
; Teeth: soundness does not follow from admission alone, nor from the
; lengths alone.
(must-fail
 (defthm sput-rollback-sound-by-admission
   (implies (fn-bs-profile-admittedp old)
            (equal (car (fn-profile-rollback-verdict old lengths)) :sound))))
(must-fail
 (defthm sput-rollback-sound-by-lengths
   (implies (fn-profile-all-within lengths (fn-profile-rollback-record-bound old))
            (equal (car (fn-profile-rollback-verdict old lengths)) :sound))))
