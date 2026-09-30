; Logical observation of the actual bounded FNCR scope cursor. None of the
; scans below is called by the native endpoint or a served tick.
(in-package "ACL2")
(include-book "consumer-remote-scope")

(defun fn-crsm-pattern (access login)
 (declare (xargs :guard t))
 (fn-gac-pattern access login 1))

(defun fn-crsm-groups (groups read served closed login prev n g rev)
 (declare (xargs :guard t :verify-guards nil))
 (if (not (consp groups))
     (if (and (null groups) (posp n)) (list :definition (revappend rev nil))
       '(:refused :query))
  (let ((name (car groups)))
   (cond ((or (<= (nfix g) (nfix n)) (not (fn-crs-namep name))
              (and prev (or (not (lexorder prev name)) (equal prev name))))
          '(:refused :query))
         ((or (and read (not (fn-gac-readablep read
                                (coerce (fn-nntp-octets-chars name) 'string))))
              (not (member-equal name served))
              (fn-mod-queue-hiddenp name closed login)) '(:refused :read-scope))
         (t (fn-crsm-groups (cdr groups) read served closed login name
                              (1+ (nfix n)) g (cons name rev)))))))

(defun fn-crsm-after-current (s g)
 (declare (xargs :guard t :verify-guards nil))
 (let ((groups (fn-cp-nth 6 s)))
  (fn-crsm-groups (fn-inj-cdr groups) (fn-cp-nth 5 s) (fn-cp-nth 7 s)
     (fn-cp-nth 8 s) (fn-cp-nth 2 s) (fn-cp-nth 0 groups)
     (1+ (nfix (fn-cp-nth 12 s))) g
     (cons (fn-cp-nth 0 groups) (fn-cp-nth 13 s)))))

(defun fn-crsm-observe (s g)
 (declare (xargs :guard t :verify-guards nil))
 (let ((name (fn-cp-nth 0 (fn-cp-nth 6 s))) (login (fn-cp-nth 2 s))
       (phase (fn-cp-nth 3 s)) (scan (fn-cp-nth 9 s)))
  (case phase
   ((:access :groups)
    (fn-crsm-groups (fn-cp-nth 6 s)
     (if (eq phase :access) (fn-crsm-pattern (fn-cp-nth 4 s) login) (fn-cp-nth 5 s))
     (fn-cp-nth 7 s) (fn-cp-nth 8 s) login (fn-cp-nth 11 s)
     (nfix (fn-cp-nth 12 s)) g (fn-cp-nth 13 s)))
   (:served
    (if (and (member-equal name scan) (not (fn-mod-queue-hiddenp name (fn-cp-nth 8 s) login)))
        (fn-crsm-after-current s g) '(:refused :read-scope)))
   (:closed
    (if (fn-mod-queue-hiddenp name scan login) '(:refused :read-scope)
      (fn-crsm-after-current s g)))
   (:moderators
    (if (or (not (member-equal login (true-list-fix (fn-cp-nth 10 s))))
            (fn-mod-queue-hiddenp name scan login)) '(:refused :read-scope)
      (fn-crsm-after-current s g)))
   (:accept (fn-crsm-after-current s g))
   ((:reverse :ready)
    (list :definition (revappend (fn-cp-nth 13 s) (fn-cp-nth 15 s))))
   (otherwise '(:refused :scope-phase)))))

; The actual caller maintains this domain; it is not a runtime whole-cursor
; validator. In particular login is admitted, borrowed table spines proper,
; and every group copied into the retained reverse list is an octet group.
(defun fn-crsm-domainp (s)
 (declare (xargs :guard t :verify-guards nil))
 (and (true-listp (fn-cp-nth 2 s)) (consp (fn-cp-nth 2 s))
      (true-listp (fn-cp-nth 7 s)) (true-listp (fn-cp-nth 8 s))
      (true-listp (fn-cp-nth 9 s)) (true-listp (fn-cp-nth 10 s))
      (true-listp (fn-cp-nth 13 s)) (true-listp (fn-cp-nth 15 s))
      (or (not (member-eq (fn-cp-nth 3 s) '(:served :closed :moderators :accept)))
          (consp (fn-cp-nth 6 s)))))

(defun fn-crsm-answer (answer g)
 (declare (xargs :guard t :verify-guards nil))
 (if (member-eq (fn-cp-nth 0 answer) '(:yield :ready))
     (fn-crsm-observe (fn-cp-nth 1 answer) g) answer))

(local
 (defthm fn-crsm-groups-unfolds
  (equal (fn-crsm-groups groups read served closed login prev n g rev)
   (if (not (consp groups))
       (if (and (null groups) (posp n)) (list :definition (revappend rev nil)) '(:refused :query))
    (let ((name (car groups)))
     (cond ((or (<= (nfix g) (nfix n)) (not (fn-crs-namep name))
                (and prev (or (not (lexorder prev name)) (equal prev name)))) '(:refused :query))
           ((or (and read (not (fn-gac-readablep read
                                   (coerce (fn-nntp-octets-chars name) 'string))))
                (not (member-equal name served))
                (fn-mod-queue-hiddenp name closed login)) '(:refused :read-scope))
           (t (fn-crsm-groups (cdr groups) read served closed login name
                              (1+ (nfix n)) g (cons name rev)))))))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-crsm-groups groups read served closed login prev n g rev))
           :in-theory (disable fn-crsm-groups)))))

(local
 (defthm fn-crsm-reverse-one-cell
  (implies (consp xs)
   (equal (revappend xs ys) (revappend (cdr xs) (cons (car xs) ys))))
  :hints (("Goal" :expand ((revappend xs ys))
           :in-theory (disable revappend revappend-removal)))))

(local
 (defthm fn-crsm-groups-of-atom
  (implies (not (consp groups))
   (equal (fn-crsm-groups groups read served closed login prev n g rev)
          (if (and (null groups) (posp n)) (list :definition (revappend rev nil)) '(:refused :query))))
  :hints (("Goal" :expand ((fn-crsm-groups groups read served closed login prev n g rev))
           :in-theory (disable fn-crsm-groups revappend-removal)))))

(local
 (defthm fn-crsm-first-rule-unfolds
  (equal (fn-gac-rule table login)
   (if (consp table)
    (let ((row (car table)))
     (if (and (consp row) (consp (cdr row)) (consp (cddr row)) (consp (cdddr row))
              (equal (car (cdddr row)) 3)
              (equal (fn-gac-text-octets (car row)) (true-list-fix login))) row
       (fn-gac-rule (cdr table) login))) nil))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-gac-rule table login)) :in-theory (disable fn-gac-rule)))))

(local
 (defthm fn-crsm-state-fields
  (and
   (equal (fn-cp-nth 0 (fn-crs-state key login phase access read groups served closed scan mods prev n rev rm built bm wire)) :remote-scope)
   (equal (fn-cp-nth 1 (fn-crs-state key login phase access read groups served closed scan mods prev n rev rm built bm wire)) key)
   (equal (fn-cp-nth 2 (fn-crs-state key login phase access read groups served closed scan mods prev n rev rm built bm wire)) login)
   (equal (fn-cp-nth 3 (fn-crs-state key login phase access read groups served closed scan mods prev n rev rm built bm wire)) phase)
   (equal (fn-cp-nth 4 (fn-crs-state key login phase access read groups served closed scan mods prev n rev rm built bm wire)) access)
   (equal (fn-cp-nth 5 (fn-crs-state key login phase access read groups served closed scan mods prev n rev rm built bm wire)) read)
   (equal (fn-cp-nth 6 (fn-crs-state key login phase access read groups served closed scan mods prev n rev rm built bm wire)) groups)
   (equal (fn-cp-nth 7 (fn-crs-state key login phase access read groups served closed scan mods prev n rev rm built bm wire)) served)
   (equal (fn-cp-nth 8 (fn-crs-state key login phase access read groups served closed scan mods prev n rev rm built bm wire)) closed)
   (equal (fn-cp-nth 9 (fn-crs-state key login phase access read groups served closed scan mods prev n rev rm built bm wire)) scan)
   (equal (fn-cp-nth 10 (fn-crs-state key login phase access read groups served closed scan mods prev n rev rm built bm wire)) mods)
   (equal (fn-cp-nth 11 (fn-crs-state key login phase access read groups served closed scan mods prev n rev rm built bm wire)) prev)
   (equal (fn-cp-nth 12 (fn-crs-state key login phase access read groups served closed scan mods prev n rev rm built bm wire)) n)
   (equal (fn-cp-nth 13 (fn-crs-state key login phase access read groups served closed scan mods prev n rev rm built bm wire)) rev)
   (equal (fn-cp-nth 14 (fn-crs-state key login phase access read groups served closed scan mods prev n rev rm built bm wire)) rm)
   (equal (fn-cp-nth 15 (fn-crs-state key login phase access read groups served closed scan mods prev n rev rm built bm wire)) built)
   (equal (fn-cp-nth 16 (fn-crs-state key login phase access read groups served closed scan mods prev n rev rm built bm wire)) bm)
)
  :hints (("Goal" :in-theory (enable fn-cp-nth fn-crs-state)))))

(local
 (defthm fn-crsm-member-first
  (equal (member-equal x xs)
         (if (consp xs) (if (equal x (car xs)) xs (member-equal x (cdr xs))) nil))
  :rule-classes nil
  :hints (("Goal" :expand ((member-equal x xs)) :in-theory (disable member-equal)))))

(local
 (defthm fn-crsm-hidden-first
  (equal (fn-mod-queue-hiddenp name closed login)
   (if (consp closed)
    (or (and (fn-nntp-moderated-entryp (car closed))
             (equal (car (car closed)) :moderated)
             (equal (fn-mod-entry-queue (car closed)) name)
             (not (and login (member-equal login (true-list-fix (fn-mod-entry-moderators (car closed)))))) t)
        (fn-mod-queue-hiddenp name (cdr closed) login)) nil))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-mod-queue-hiddenp name closed login))
          :in-theory (disable fn-mod-queue-hiddenp)))))

(local
 (defthm fn-crsm-nth-zero
  (equal (fn-cp-nth 0 xs) (if (consp xs) (car xs) nil))
  :hints (("Goal" :in-theory (enable fn-cp-nth)))))

(local
 (defthm fn-crsm-nth-cons
  (equal (fn-cp-nth n (cons a xs))
         (if (zp n) a (fn-cp-nth (1- n) xs)))
  :hints (("Goal" :expand ((fn-cp-nth n (cons a xs)))
          :in-theory (disable fn-cp-nth)))))

(local
 (defthm fn-crsm-valid-row-spine
  (implies (equal (fn-cp-nth 3 row) 3) (consp (cdddr row)))
  :hints (("Goal" :in-theory (enable fn-cp-nth)))))

(local
 (defthm fn-crsm-access-row-fields
  (and (equal (fn-cp-nth 3 (car rows)) (if (consp (cdddr (car rows))) (cadddr (car rows)) nil))
       (equal (fn-cp-nth 1 (car rows)) (if (consp (cdr (car rows))) (cadr (car rows)) nil)))
  :hints (("Goal" :in-theory (enable fn-cp-nth)))))

(local
 (defthm fn-crsm-tick-access
  (implies (and (fn-crsm-domainp s) (equal key (fn-cp-nth 1 s)) (equal (fn-cp-nth 3 s) :access))
   (equal (fn-crsm-answer (fn-crs-tick s key g) g) (fn-crsm-observe s g)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
   :use ((:instance fn-crsm-first-rule-unfolds (table (fn-cp-nth 4 s)) (login (fn-cp-nth 2 s))))
   :in-theory (e/d (fn-crs-tick fn-crsm-answer fn-crsm-domainp fn-crsm-observe fn-crsm-after-current fn-crsm-pattern fn-gac-pattern fn-crsm-groups-of-atom fn-inj-cdr fn-inj-car fn-crsm-reverse-one-cell) (fn-cp-nth fn-crs-state fn-mod-queue-hiddenp member-equal fn-gac-rule revappend revappend-removal fn-crsm-groups fn-gac-text-octets fn-gac-readablep fn-crs-namep fn-nntp-octets-chars fn-caac-list-cons fn-scs-octets))))))

(local
 (defthm fn-crsm-tick-groups
  (implies (and (fn-crsm-domainp s) (equal key (fn-cp-nth 1 s)) (equal (fn-cp-nth 3 s) :groups))
   (equal (fn-crsm-answer (fn-crs-tick s key g) g) (fn-crsm-observe s g)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
   :use ((:instance fn-crsm-groups-unfolds (groups (fn-cp-nth 6 s)) (read (fn-cp-nth 5 s)) (served (fn-cp-nth 7 s)) (closed (fn-cp-nth 8 s)) (login (fn-cp-nth 2 s)) (prev (fn-cp-nth 11 s)) (n (nfix (fn-cp-nth 12 s))) (rev (fn-cp-nth 13 s))))
   :in-theory (e/d (fn-crs-tick fn-crsm-answer fn-crsm-domainp fn-crsm-observe fn-crsm-after-current fn-crsm-pattern fn-gac-pattern fn-crsm-groups-of-atom fn-inj-cdr fn-inj-car fn-crsm-reverse-one-cell) (fn-cp-nth fn-crs-state fn-mod-queue-hiddenp member-equal fn-gac-rule revappend revappend-removal fn-crsm-groups fn-gac-text-octets fn-gac-readablep fn-crs-namep fn-nntp-octets-chars fn-caac-list-cons fn-scs-octets))))))

(local
 (defthm fn-crsm-tick-served
  (implies (and (fn-crsm-domainp s) (equal key (fn-cp-nth 1 s)) (equal (fn-cp-nth 3 s) :served))
   (equal (fn-crsm-answer (fn-crs-tick s key g) g) (fn-crsm-observe s g)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
   :use ((:instance fn-crsm-member-first (x (fn-cp-nth 0 (fn-cp-nth 6 s))) (xs (fn-cp-nth 9 s))))
   :in-theory (e/d (fn-crs-tick fn-crsm-answer fn-crsm-domainp fn-crsm-observe fn-crsm-after-current fn-crsm-pattern fn-gac-pattern fn-crsm-groups-of-atom fn-inj-cdr fn-inj-car fn-crsm-reverse-one-cell) (fn-cp-nth fn-crs-state fn-mod-queue-hiddenp member-equal fn-gac-rule revappend revappend-removal fn-crsm-groups fn-gac-text-octets fn-gac-readablep fn-crs-namep fn-nntp-octets-chars fn-caac-list-cons fn-scs-octets))))))

(local
 (defthm fn-crsm-tick-closed
  (implies (and (fn-crsm-domainp s) (equal key (fn-cp-nth 1 s)) (equal (fn-cp-nth 3 s) :closed))
   (equal (fn-crsm-answer (fn-crs-tick s key g) g) (fn-crsm-observe s g)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
   :use ((:instance fn-crsm-hidden-first (name (fn-cp-nth 0 (fn-cp-nth 6 s))) (closed (fn-cp-nth 9 s)) (login (fn-cp-nth 2 s))))
   :in-theory (e/d (fn-crs-tick fn-crsm-answer fn-crsm-domainp fn-crsm-observe fn-crsm-after-current fn-crsm-pattern fn-gac-pattern fn-crsm-groups-of-atom fn-inj-cdr fn-inj-car fn-crsm-reverse-one-cell fn-nntp-moderated-entryp fn-mod-entry-moderators fn-mod-entry-queue) (fn-cp-nth fn-crs-state fn-mod-queue-hiddenp member-equal fn-gac-rule revappend revappend-removal fn-crsm-groups fn-gac-text-octets fn-gac-readablep fn-crs-namep fn-nntp-octets-chars fn-caac-list-cons fn-scs-octets))))))

(local
 (defthm fn-crsm-tick-moderators
  (implies (and (fn-crsm-domainp s) (equal key (fn-cp-nth 1 s)) (equal (fn-cp-nth 3 s) :moderators))
   (equal (fn-crsm-answer (fn-crs-tick s key g) g) (fn-crsm-observe s g)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
   :use ((:instance fn-crsm-member-first (x (fn-cp-nth 2 s)) (xs (fn-cp-nth 10 s))))
   :in-theory (e/d (fn-crs-tick fn-crsm-answer fn-crsm-domainp fn-crsm-observe fn-crsm-after-current fn-crsm-pattern fn-gac-pattern fn-crsm-groups-of-atom fn-inj-cdr fn-inj-car fn-crsm-reverse-one-cell) (fn-cp-nth fn-crs-state fn-mod-queue-hiddenp member-equal fn-gac-rule revappend revappend-removal fn-crsm-groups fn-gac-text-octets fn-gac-readablep fn-crs-namep fn-nntp-octets-chars fn-caac-list-cons fn-scs-octets))))))

(local
 (defthm fn-crsm-tick-accept
  (implies (and (fn-crsm-domainp s) (equal key (fn-cp-nth 1 s)) (equal (fn-cp-nth 3 s) :accept))
   (equal (fn-crsm-answer (fn-crs-tick s key g) g) (fn-crsm-observe s g)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
   :in-theory (e/d (fn-crs-tick fn-crsm-answer fn-crsm-domainp fn-crsm-observe fn-crsm-after-current fn-crsm-pattern fn-gac-pattern fn-crsm-groups-of-atom fn-inj-cdr fn-inj-car fn-crsm-reverse-one-cell) (fn-cp-nth fn-crs-state fn-mod-queue-hiddenp member-equal fn-gac-rule revappend revappend-removal fn-crsm-groups fn-gac-text-octets fn-gac-readablep fn-crs-namep fn-nntp-octets-chars fn-caac-list-cons fn-scs-octets))))))

(local
 (defthm fn-crsm-tick-reverse
  (implies (and (fn-crsm-domainp s) (equal key (fn-cp-nth 1 s)) (equal (fn-cp-nth 3 s) :reverse))
   (equal (fn-crsm-answer (fn-crs-tick s key g) g) (fn-crsm-observe s g)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
   :in-theory (e/d (fn-crs-tick fn-crsm-answer fn-crsm-domainp fn-crsm-observe fn-crsm-after-current fn-crsm-pattern fn-gac-pattern fn-crsm-groups-of-atom fn-inj-cdr fn-inj-car fn-crsm-reverse-one-cell) (fn-cp-nth fn-crs-state fn-mod-queue-hiddenp member-equal fn-gac-rule revappend revappend-removal fn-crsm-groups fn-gac-text-octets fn-gac-readablep fn-crs-namep fn-nntp-octets-chars fn-caac-list-cons fn-scs-octets))))))

(local
 (defthm fn-crsm-tick-ready
  (implies (and (fn-crsm-domainp s) (equal key (fn-cp-nth 1 s)) (equal (fn-cp-nth 3 s) :ready))
   (equal (fn-crsm-answer (fn-crs-tick s key g) g) (fn-crsm-observe s g)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
   :in-theory (e/d (fn-crs-tick fn-crsm-answer fn-crsm-domainp fn-crsm-observe fn-crsm-after-current fn-crsm-pattern fn-gac-pattern fn-crsm-groups-of-atom fn-inj-cdr fn-inj-car fn-crsm-reverse-one-cell) (fn-cp-nth fn-crs-state fn-mod-queue-hiddenp member-equal fn-gac-rule revappend revappend-removal fn-crsm-groups fn-gac-text-octets fn-gac-readablep fn-crs-namep fn-nntp-octets-chars fn-caac-list-cons fn-scs-octets))))))

(local
 (defthm fn-crsm-tick-other
  (implies (and (fn-crsm-domainp s) (equal key (fn-cp-nth 1 s)) (not (member-eq (fn-cp-nth 3 s) '(:access :groups :served :closed :moderators :accept :reverse :ready))))
   (equal (fn-crsm-answer (fn-crs-tick s key g) g) (fn-crsm-observe s g)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
   :in-theory (e/d (fn-crs-tick fn-crsm-answer fn-crsm-domainp fn-crsm-observe fn-crsm-after-current fn-crsm-pattern fn-gac-pattern fn-crsm-groups-of-atom fn-inj-cdr fn-inj-car fn-crsm-reverse-one-cell member-equal) (fn-cp-nth fn-crs-state fn-mod-queue-hiddenp fn-gac-rule revappend revappend-removal fn-crsm-groups fn-gac-text-octets fn-gac-readablep fn-crs-namep fn-nntp-octets-chars fn-caac-list-cons fn-scs-octets))))))

(defthm fn-crs-tick-is-current-read-and-moderation-projection
 (implies (and (fn-crsm-domainp s) (equal key (fn-cp-nth 1 s)))
          (equal (fn-crsm-answer (fn-crs-tick s key g) g) (fn-crsm-observe s g)))
 :rule-classes nil
 :hints (("Goal" :use (fn-crsm-tick-access fn-crsm-tick-groups fn-crsm-tick-served fn-crsm-tick-closed fn-crsm-tick-moderators fn-crsm-tick-accept fn-crsm-tick-reverse fn-crsm-tick-ready fn-crsm-tick-other)
          :in-theory (e/d (member-equal) (fn-cp-nth fn-crs-tick fn-crsm-answer fn-crsm-observe fn-crsm-domainp fn-crsm-groups fn-crsm-after-current fn-crsm-pattern fn-gac-pattern fn-crsm-access-row-fields fn-crsm-nth-cons fn-crsm-nth-zero)))))

(in-theory (disable fn-crsm-pattern fn-crsm-groups fn-crsm-after-current fn-crsm-observe fn-crsm-domainp fn-crsm-answer))
