; W9: maintained total active obligations and per-immutable-subject count/charge.
; Build is initialization/off-mutex reconstruction only. Reads never refresh.
(in-package "ACL2")
(include-book "retention-invariants")
(include-book "view-delta-concrete")
(local (include-book "arithmetic/top" :dir :system))

(defun fn-rov-contrib (pin)
  (declare (xargs :guard t))
  (cons (fn-retain-obligation-subject pin) (fn-retain-obligation-charge pin)))

(defun fn-rov-contribs (pins)
  (declare (xargs :guard t))
  (if (consp pins)
      (cons (fn-rov-contrib (car pins)) (fn-rov-contribs (cdr pins)))
    nil))

(defthm fn-rov-contribs-typed
  (implies (fn-retain-obligation-listp pins)
           (fn-vdc-contribsp (fn-rov-contribs pins)))
  :hints (("Goal" :in-theory (enable fn-vdc-contribsp fn-retain-obligationp))))

; VIEW = (total . subject-trie). Its correspondence is proof-only.
(defun fn-rov-count (view)
  (declare (xargs :guard t))
  (if (consp view) (nfix (car view)) 0))
(defun fn-rov-subject (subject view)
  (declare (xargs :guard t))
  (fn-vdc-get subject (if (consp view) (cdr view) nil)))
(defun fn-rov-correspondp (view pins)
  (declare (xargs :guard t :verify-guards nil))
  (and (consp view) (natp (car view))
       (equal (car view) (len pins))
       (fn-midx-unique-branchesp (cdr view))
       (fn-vdc-correspondp (cdr view) (fn-rov-contribs pins))))

(defun fn-rov-build-loop (pins count trie)
  (declare (xargs :guard (and (fn-retain-obligation-listp pins) (natp count))))
  (if (consp pins)
      (fn-rov-build-loop (cdr pins) (+ 1 count)
                         (fn-vdc-bump (fn-retain-obligation-subject (car pins))
                                      (fn-retain-obligation-charge (car pins)) trie))
    (cons count trie)))

(defun fn-rov-build (pins)
  (declare (xargs :guard (fn-retain-obligation-listp pins)))
  (fn-rov-build-loop pins 0 nil))

(defthm fn-rov-build-loop-count
  (implies (natp count)
           (equal (car (fn-rov-build-loop pins count trie)) (+ count (len pins)))))
(defthm fn-rov-build-loop-trie
  (equal (cdr (fn-rov-build-loop pins count trie))
         (fn-vdc-build-loop (fn-rov-contribs pins) trie))
  :hints (("Goal" :induct (fn-rov-build-loop pins count trie)
           :in-theory (enable fn-vdc-build-loop))))

(defthm fn-rov-build-corresponds
  (implies (fn-retain-obligation-listp pins)
           (fn-rov-correspondp (fn-rov-build pins) pins))
  :hints (("Goal" :in-theory (e/d (fn-vdc-build)
                                   (fn-vdc-build-corresponds fn-rov-contribs fn-rov-contrib))
           :use ((:instance fn-vdc-build-corresponds (cs (fn-rov-contribs pins)))))))

(defun fn-rov-arrive (pin view)
  (declare (xargs :guard t))
  (cons (+ 1 (fn-rov-count view))
        (fn-vdc-bump (fn-retain-obligation-subject pin)
                     (fn-retain-obligation-charge pin)
                     (if (consp view) (cdr view) nil))))

(defun fn-rov-retract (pin view)
  (declare (xargs :guard t))
  (cons (nfix (- (fn-rov-count view) 1))
        (fn-vdc-unbump (fn-retain-obligation-subject pin)
                       (fn-retain-obligation-charge pin)
                       (if (consp view) (cdr view) nil))))

(defthm fn-rov-arrive-delta
  (implies (and (fn-retain-obligationp pin) (fn-rov-correspondp view pins))
           (fn-rov-correspondp (fn-rov-arrive pin view) (cons pin pins)))
  :hints (("Goal" :in-theory (e/d (fn-retain-obligationp)
                                 (fn-vdc-correspondp-of-bump))
           :use ((:instance fn-vdc-correspondp-of-bump
                    (c (fn-rov-contrib pin)) (trie (cdr view))
                    (cs (fn-rov-contribs pins)))))))

(defthm fn-rov-find-contrib-member
  (implies (consp (fn-retain-find-id id pins))
           (member-equal (fn-rov-contrib (fn-retain-find-id id pins))
                         (fn-rov-contribs pins)))
  :hints (("Goal" :induct (fn-retain-find-id id pins))))

(defthm fn-rov-remove-id-count
  (implies (consp (fn-retain-find-id id pins))
           (equal (len (fn-retain-remove-id id pins)) (- (len pins) 1)))
  :hints (("Goal" :induct (fn-retain-remove-id id pins))))

(defthm fn-rov-remove-id-oracle-delta
 (implies (consp (fn-retain-find-id id pins))
  (equal (fn-vd-oracle-at key (fn-rov-contribs (fn-retain-remove-id id pins)))
   (if (equal (fn-retain-obligation-subject (fn-retain-find-id id pins)) key)
    (cons (- (car (fn-vd-oracle-at key (fn-rov-contribs pins))) 1)
          (- (cdr (fn-vd-oracle-at key (fn-rov-contribs pins)))
             (nfix (fn-retain-obligation-charge (fn-retain-find-id id pins)))))
    (fn-vd-oracle-at key (fn-rov-contribs pins)))))
 :hints (("Goal" :induct (fn-retain-remove-id id pins)
          :in-theory (enable fn-vd-oracle-at))))

(defthm fn-rov-remove-id-oracle
 (implies (consp (fn-retain-find-id id pins))
  (equal (fn-vd-oracle-at key (fn-rov-contribs (fn-retain-remove-id id pins)))
   (fn-vd-oracle-at key (remove1-equal (fn-rov-contrib (fn-retain-find-id id pins))
                                      (fn-rov-contribs pins)))))
 :hints (("Goal" :in-theory (e/d (fn-rov-contrib)
   (fn-vd-oracle-at-of-remove1 fn-rov-remove-id-oracle-delta fn-rov-find-contrib-member
    fn-rov-contribs fn-retain-find-id fn-retain-remove-id))
 :use ((:instance fn-rov-find-contrib-member)
       (:instance fn-vd-oracle-at-of-remove1 (k key)
        (c (fn-rov-contrib (fn-retain-find-id id pins))) (cs (fn-rov-contribs pins)))
       (:instance fn-rov-remove-id-oracle-delta)))))

(defthm fn-rov-find-id-positive-length
 (implies (consp (fn-retain-find-id id pins)) (< 0 (len pins)))
 :rule-classes :linear)

(defthm fn-rov-trie-retract-corresponds
 (implies (and (fn-retain-obligation-listp pins)
               (consp (fn-retain-find-id id pins))
               (fn-vdc-correspondp trie (fn-rov-contribs pins)))
  (fn-vdc-correspondp
   (fn-vdc-unbump (fn-retain-obligation-subject (fn-retain-find-id id pins))
                  (fn-retain-obligation-charge (fn-retain-find-id id pins)) trie)
   (fn-rov-contribs (fn-retain-remove-id id pins))))
 :hints (("Goal"
 :in-theory (e/d (fn-retain-obligationp fn-rov-contrib fn-vdc-correspondp)
                 (fn-vdc-correspondp-necc fn-vdc-get-of-unbump-is-oracle
                  fn-rov-contribs fn-retain-find-id fn-retain-remove-id
                  fn-rov-find-contrib-member))
 :expand ((fn-vdc-correspondp
   (fn-vdc-unbump (fn-retain-obligation-subject (fn-retain-find-id id pins))
                  (fn-retain-obligation-charge (fn-retain-find-id id pins)) trie)
   (fn-rov-contribs (fn-retain-remove-id id pins))))
 :use ((:instance fn-rov-find-contrib-member)
       (:instance fn-retain-release-find-is-obligation)
       (:instance fn-vdc-get-of-unbump-is-oracle
        (key (fn-vdc-correspondp-witness
              (fn-vdc-unbump (fn-retain-obligation-subject (fn-retain-find-id id pins))
                             (fn-retain-obligation-charge (fn-retain-find-id id pins)) trie)
              (fn-rov-contribs (fn-retain-remove-id id pins))))
        (c (fn-rov-contrib (fn-retain-find-id id pins)))
        (cs (fn-rov-contribs pins)))
       (:instance fn-vdc-correspondp-necc
        (key (fn-vdc-correspondp-witness
              (fn-vdc-unbump (fn-retain-obligation-subject (fn-retain-find-id id pins))
                             (fn-retain-obligation-charge (fn-retain-find-id id pins)) trie)
              (fn-rov-contribs (fn-retain-remove-id id pins))))
        (cs (fn-rov-contribs pins)))
       (:instance fn-vdc-correspondp-necc
        (key (fn-retain-obligation-subject (fn-retain-find-id id pins)))
        (cs (fn-rov-contribs pins)))))))

; A retraction is by obligation identity, not subject. The removed obligation
; contributes exactly once; another same-subject obligation remains required.
(defthm fn-rov-retract-delta
  (implies (and (fn-retain-obligation-listp pins)
                (consp (fn-retain-find-id id pins)) (fn-rov-correspondp view pins))
           (fn-rov-correspondp (fn-rov-retract (fn-retain-find-id id pins) view)
                               (fn-retain-remove-id id pins)))
  :hints (("Goal" :in-theory (enable fn-retain-obligationp))))

(defthm fn-rov-count-is-pin-count
  (implies (fn-rov-correspondp view pins)
           (equal (fn-rov-count view) (len pins))))
(defthm fn-rov-subject-is-oracle
  (implies (and (fn-rov-correspondp view pins) (stringp subject))
           (equal (fn-rov-subject subject view)
                  (fn-vd-oracle-at subject (fn-rov-contribs pins))))
  :hints (("Goal" :use ((:instance fn-vdc-correspondp-necc
                         (trie (cdr view)) (cs (fn-rov-contribs pins)) (key subject))))))

(in-theory (disable fn-rov-count fn-rov-subject fn-rov-arrive fn-rov-retract
                    fn-rov-build fn-rov-build-loop fn-rov-correspondp fn-rov-contribs fn-rov-contrib))

; Executable update word. No reconstruction fallback. Arrival is the exact
; one-cons shape; release is the ledger's append-only release history. The
; charge removed is 1 + old reservation - new reservation (the one retained
; history unit is not part of the active subject's contribution).
(defun fn-rov-update-arm (old new)
  (declare (xargs :guard t))
  ; Release first: never compare the removed-pin prefix. The new release's
  ; shared tail names the preceding history. Arrival next: the new pin's
  ; shared tail names the preceding pins. The same arm compares unchanged
  ; shared objects; initialization/reclaim use build at their own boundary.
  (cond ((and (consp (fn-retain-releases new))
              (equal (cdr (fn-retain-releases new)) (fn-retain-releases old))) :release)
        ((and (consp (fn-retain-pins new))
              (equal (cdr (fn-retain-pins new)) (fn-retain-pins old))
              (equal (fn-retain-releases old) (fn-retain-releases new))) :arrival)
        ((and (equal (fn-retain-pins old) (fn-retain-pins new))
              (equal (fn-retain-releases old) (fn-retain-releases new))) :same)
        (t :invalid)))

(defun fn-rov-update (old new view)
  (declare (xargs :guard t))
  (let ((arm (fn-rov-update-arm old new)))
    (cond ((equal arm :same) view)
          ((equal arm :arrival) (fn-rov-arrive (car (fn-retain-pins new)) view))
          ((equal arm :release)
           (let ((subject (fn-retain-release-subject (car (fn-retain-releases new))))
                 (charge (nfix (+ 1 (- (nfix (fn-retain-reserved old))
                                       (nfix (fn-retain-reserved new)))))))
             (cons (nfix (- (fn-rov-count view) 1))
                   (fn-vdc-unbump subject charge (if (consp view) (cdr view) nil)))))
          (t nil))))

(local
 (defthm fn-rov-not-self-tail
  (implies (consp x) (not (equal (cdr x) x)))
  :hints (("Goal" :induct (len x)))))

(defthm fn-rov-update-unchanged
  (equal (fn-rov-update ledger ledger view) view)
  :hints (("Goal" :in-theory (enable fn-rov-update fn-rov-update-arm))))

(defthm fn-rov-update-of-admit
  (implies (and (fn-retain-statep ledger)
                (fn-retain-admissiblep ledger id subject kind evidence charge))
           (equal (fn-rov-update ledger
                    (fn-retain-admit ledger id subject kind evidence charge) view)
                  (fn-rov-arrive (fn-retain-make-obligation id subject kind evidence charge) view)))
  :hints (("Goal" :in-theory (enable fn-retain-admit fn-rov-update fn-rov-update-arm))))

(defthm fn-rov-update-of-release
  (implies (and (fn-retain-statep ledger)
                (fn-retain-matching-releasep
                 (fn-retain-find-id id (fn-retain-pins ledger)) id subject kind evidence))
           (equal (fn-rov-update ledger
                    (fn-retain-release ledger id subject kind evidence) view)
                  (fn-rov-retract (fn-retain-find-id id (fn-retain-pins ledger)) view)))
  :hints (("Goal"
           :use ((:instance fn-retain-release-find-is-obligation (pins (fn-retain-pins ledger)))
                 (:instance fn-retain-release-charge-bounded-by-sum (pins (fn-retain-pins ledger))))
           :in-theory (enable fn-retain-release fn-retain-matching-releasep
                              fn-retain-statep fn-retain-obligationp
                              fn-rov-update fn-rov-update-arm fn-rov-retract))))

(defthm fn-rov-update-admit-preserves-correspondence
  (implies (and (fn-retain-statep ledger)
                (fn-rov-correspondp view (fn-retain-pins ledger)))
           (fn-rov-correspondp
            (fn-rov-update ledger (fn-retain-admit ledger id subject kind evidence charge) view)
            (fn-retain-pins (fn-retain-admit ledger id subject kind evidence charge))))
  :hints (("Goal" :in-theory (enable fn-retain-admit fn-retain-admissiblep fn-retain-obligationp))))

(defthm fn-rov-update-release-preserves-correspondence
  (implies (and (fn-retain-statep ledger)
                (fn-rov-correspondp view (fn-retain-pins ledger)))
           (fn-rov-correspondp
            (fn-rov-update ledger (fn-retain-release ledger id subject kind evidence) view)
            (fn-retain-pins (fn-retain-release ledger id subject kind evidence))))
  :hints (("Goal"
           :cases ((fn-retain-matching-releasep (fn-retain-find-id id (fn-retain-pins ledger))
                                               id subject kind evidence))
           :in-theory (e/d (fn-retain-release fn-retain-statep)
                           (fn-rov-update fn-rov-update-of-release))
           :use ((:instance fn-rov-update-of-release)))))

(in-theory (disable fn-rov-update fn-rov-update-arm))

(defthm fn-rov-admit-takes-arrival-arm
 (implies (and (fn-retain-statep ledger)
               (fn-retain-admissiblep ledger id subject kind evidence charge))
          (equal (fn-rov-update-arm ledger
                   (fn-retain-admit ledger id subject kind evidence charge)) :arrival))
 :hints (("Goal" :in-theory (enable fn-rov-update-arm fn-retain-admit))))
(defthm fn-rov-release-takes-release-arm
 (implies (and (fn-retain-statep ledger)
               (fn-retain-matching-releasep (fn-retain-find-id id (fn-retain-pins ledger))
                                            id subject kind evidence))
          (equal (fn-rov-update-arm ledger
                   (fn-retain-release ledger id subject kind evidence)) :release))
 :hints (("Goal" :in-theory (enable fn-rov-update-arm fn-retain-release))))
