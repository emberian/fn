; Teeth for books/store-profile-upgrade and books/byte-store-profile-program:
; the upgrade relation over the named profiles, the operator verdict, one
; must-fail per keystone hypothesis at constants, and reachable witnesses of
; the byte program's crash keystone at its rename cut.
(in-package "ACL2")
(include-book "../../books/store-profile-upgrade")
(include-book "../../books/byte-store-profile-program")
(include-book "std/testing/must-fail" :dir :system)

(defconst *sput-dev* *fn-bs-meta-development-values*)
(defconst *sput-scale* *fn-bs-meta-scale-values*)
(defconst *sput-ldev* *fn-bs-meta-legacy-development-values*)
(defconst *sput-lscale* *fn-bs-meta-legacy-scale-values*)

; -----------------------------------------------------------------------------
; The relation over the four named profiles: exactly two pairs.

(assert-event (fn-profile-upgradep *sput-dev* *sput-scale*))
(assert-event (fn-profile-upgradep *sput-ldev* *sput-lscale*))
(assert-event (not (fn-profile-upgradep *sput-dev* *sput-dev*)))       ; no-op
(assert-event (not (fn-profile-upgradep *sput-scale* *sput-dev*)))     ; downgrade
(assert-event (not (fn-profile-upgradep *sput-ldev* *sput-scale*)))    ; format
(assert-event (not (fn-profile-upgradep *sput-dev* *sput-lscale*)))    ; format
(assert-event (not (fn-profile-upgradep *sput-lscale* *sput-ldev*)))
(assert-event (not (fn-profile-upgradep '(1 2 3 4 5 6) *sput-scale*)))  ; not a profile

; The verdict the verb acts on.
(assert-event (equal (fn-profile-upgrade-verdict *sput-dev* :development)
                     '(:refused :same-profile)))
(assert-event (equal (fn-profile-upgrade-verdict *sput-scale* :scale)
                     '(:refused :same-profile)))
(assert-event (equal (fn-profile-upgrade-verdict *sput-scale* :development)
                     '(:refused :not-an-upgrade)))
(assert-event (equal (fn-profile-upgrade-verdict *sput-ldev* :scale)
                     '(:refused :not-an-upgrade)))
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
   (equal (fn-profile-txn-observation *sput-129* (fn-bs-meta-nth 4 *sput-dev*) 0)
          (fn-profile-txn-observation *sput-129* (fn-bs-meta-nth 4 *sput-scale*) 0))))
; Without the old observation being valid: 200 names are invalid under
; development and valid under scale, so the two differ.
(must-fail
 (defthm sput-txn-without-valid-old
   (equal (fn-profile-txn-observation *sput-200* (fn-bs-meta-nth 4 *sput-scale*) 0)
          (fn-profile-txn-observation *sput-200* (fn-bs-meta-nth 4 *sput-dev*) 0))))

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
