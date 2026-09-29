; books/owner-inspect-group.lisp -- `store inspect --group GROUP' (row S3d,
; lane operability-5; HST-038, SCN-213, PRF-1004).
;
; A group's memberships, article numbers to Message-IDs, for the operator
; and for the resilience checker's offline observation: offline over the
; archive the open replayed from the checkpoint and its suffix, and on the
; running owner over the archive its served view carries, rendered by ONE
; function on both sides (fn-oig-report; the host reaches it through
; books/control-evidence.lisp fn-cev-offline-report and fn-cev-live-report,
; from host/native-live-status-host.lisp fn-native-live-status-host-offline
; and fn-native-live-status-host-answer).
;
; The numbers are LISTGROUP's: fn-oig-rows keeps exactly the articles
; fn-nntp-group-range-numbers keeps, by its tests, and inserts them in number
; order as it does (books/nntp-projection.lisp, the logical model the served
; catalog is proven to equal: books/served-catalog.lisp
; fn-scat-range-numbers-is-group-range-numbers).  KEYSTONE
; fn-oig-rows-number-the-listgroup-numbers.
;
; The report travels as a control report kind, (:inspect-group . GROUP), FNLS
; frame kind 3 code 11 (books/control-evidence.lisp fn-cev-kind-code): the
; `moderation list GROUP' exchange, the client paging the rendered buffer by
; offset.  Work: one report renders the group's rows in one quantum under the
; owner mutex, as the status report's reclaim line walks every article today;
; a per-number cursor over the paged report (books/native-live-pages.lisp) is
; the named next step -- measure at convergence.
(in-package "ACL2")
(include-book "nntp-projection")
(include-book "control-evidence-grammar")

(defun fn-oig-kindp (kind)
  (declare (xargs :guard t))
  (and (consp kind)
       (equal (car kind) :inspect-group)
       (fn-cevg-groupp (cdr kind))))

; -----------------------------------------------------------------------------
; Rows: (NUMBER . MSGID), in number order

(defun fn-oig-rowsp (rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (and (consp (car rows))
           (natp (car (car rows)))
           (stringp (cdr (car rows)))
           (fn-oig-rowsp (cdr rows)))
    (null rows)))

(defthm fn-oig-rowsp-true-listp
  (implies (fn-oig-rowsp rows) (true-listp rows))
  :rule-classes :forward-chaining)

; Insertion by number, as fn-nntp-insert-number inserts a number: the loop
; is the executable (PKT-693: no recursion on the served depth).
(defun fn-oig-insert-loop (row rows prefix)
  (declare (xargs :guard (and (consp row) (natp (car row))
                              (fn-oig-rowsp rows) (true-listp prefix))))
  (if (consp rows)
      (if (< (car row) (car (car rows)))
          (revappend prefix (cons row rows))
        (fn-oig-insert-loop row (cdr rows) (cons (car rows) prefix)))
    (revappend prefix (list row))))

(defun fn-oig-insert (row rows)
  (declare (xargs :guard (and (consp row) (natp (car row)) (fn-oig-rowsp rows))
                  :verify-guards nil))
  (mbe :logic
       (if (consp rows)
           (if (< (car row) (car (car rows)))
               (cons row rows)
             (cons (car rows) (fn-oig-insert row (cdr rows))))
         (list row))
       :exec (fn-oig-insert-loop row rows nil)))

(local
 (defthm fn-oig-insert-loop-is-revappend
   (equal (fn-oig-insert-loop row rows prefix)
          (revappend prefix (fn-oig-insert row rows)))))

(verify-guards fn-oig-insert)

(defthm fn-oig-rowsp-of-insert
  (implies (and (consp row) (natp (car row)) (stringp (cdr row))
                (fn-oig-rowsp rows))
           (fn-oig-rowsp (fn-oig-insert row rows))))

; The article's Message-ID as a string ("" for a malformed article, which
; fn-nntp-article-number gives no number anyway).
(defun fn-oig-msgid (article)
  (declare (xargs :guard t))
  (let ((m (fn-article-msgid article)))
    (if (stringp m) m "")))

; The rows of GROUP whose numbers lie in LOW..HIGH: the articles
; fn-nntp-group-range-numbers keeps, by its tests, inserted in number order.
(defun fn-oig-rows-loop (group low high rev acc)
  (declare (xargs :guard (fn-oig-rowsp acc) :verify-guards nil))
  (if (consp rev)
      (fn-oig-rows-loop
       group low high (cdr rev)
       (let ((number (fn-nntp-article-number group (car rev))))
         (if (and (posp number)
                  (fn-ng-less-equal low number)
                  (fn-ng-less-equal number high))
             (fn-oig-insert (cons number (fn-oig-msgid (car rev))) acc)
           acc)))
    acc))

(defun fn-oig-rows (group low high articles)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (consp articles)
           (let ((number (fn-nntp-article-number group (car articles))))
             (if (and (posp number)
                      (fn-ng-less-equal low number)
                      (fn-ng-less-equal number high))
                 (fn-oig-insert (cons number (fn-oig-msgid (car articles)))
                                (fn-oig-rows group low high (cdr articles)))
               (fn-oig-rows group low high (cdr articles))))
         nil)
       :exec (fn-oig-rows-loop group low high (fn-ag-rev-onto articles nil) nil)))

(local
 (defthm fn-oig-rows-loop-of-rev-onto
   (equal (fn-oig-rows-loop group low high (fn-ag-rev-onto xs zs) nil)
          (fn-oig-rows-loop group low high zs (fn-oig-rows group low high xs)))
   :hints (("Goal" :induct (fn-ag-rev-onto xs zs)
            :in-theory (disable fn-nntp-article-number fn-ng-less-equal
                                fn-oig-insert)))))

(defthm fn-oig-rowsp-of-rows
  (fn-oig-rowsp (fn-oig-rows group low high articles))
  :hints (("Goal" :in-theory (disable fn-nntp-article-number fn-ng-less-equal
                                      fn-oig-insert))))

(verify-guards fn-oig-rows-loop)
(verify-guards fn-oig-rows)

; KEYSTONE.  The report's numbers are LISTGROUP's: the cars of the rows are
; fn-nntp-group-range-numbers of the same group, range and archive, the
; logical model the served catalog's fn-scat-range-numbers is proven equal
; to (books/served-catalog.lisp fn-scat-range-numbers-is-group-range-numbers).
; No hypothesis.  The subject is fn-oig-report below, which the host calls
; through fn-cev-offline-report (the stopped store) and fn-cev-live-report
; (the running owner), both over 1 .. *fn-nntp-max-article-number*.
(local
 (defthm fn-oig-strip-cars-of-insert
   (equal (strip-cars (fn-oig-insert row rows))
          (fn-nntp-insert-number (car row) (strip-cars rows)))
   :hints (("Goal" :in-theory (enable fn-nntp-insert-number)))))

(defthm fn-oig-rows-number-the-listgroup-numbers
  (equal (strip-cars (fn-oig-rows group low high articles))
         (fn-nntp-group-range-numbers group low high articles))
  :hints (("Goal" :in-theory (e/d (fn-oig-rows fn-nntp-group-range-numbers)
                                  (fn-nntp-article-number fn-ng-less-equal
                                   fn-nntp-insert-number fn-oig-insert)))))

; -----------------------------------------------------------------------------
; The lines

(defconst *fn-oig-lf* (list 10))

(defun fn-oig-text (text)
  (declare (xargs :guard (stringp text)))
  (fn-record-string-octets text))

; Every natural in decimal (fn-nntp-decimal-field answers 0 past ten digits;
; a count is not so bounded).
(encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defun fn-oig-digits (n acc)
    (declare (xargs :guard (and (natp n) (true-listp acc))
                    :measure (nfix n)
                    :hints (("Goal" :in-theory (disable floor mod)))))
    (if (zp n)
        acc
      (fn-oig-digits (floor n 10) (cons (+ 48 (mod n 10)) acc)))))

(defthm fn-oig-digits-true-listp
  (implies (true-listp acc) (true-listp (fn-oig-digits n acc))))

(defun fn-oig-nat (n)
  (declare (xargs :guard (natp n)))
  (if (posp n) (fn-oig-digits n nil) (list 48)))

(defthm fn-oig-nat-true-listp
  (true-listp (fn-oig-nat n)))

(defthm fn-oig-text-true-listp
  (true-listp (fn-oig-text text)))

(in-theory (disable fn-oig-digits fn-oig-nat fn-oig-text))

; `NUMBER MSGID' and a line feed.
(defun fn-oig-line (row)
  (declare (xargs :guard (and (consp row) (natp (car row)) (stringp (cdr row)))))
  (append (fn-oig-nat (car row))
          (list 32)
          (fn-oig-text (cdr row))
          *fn-oig-lf*))

(defun fn-oig-lines-loop (rows acc)
  (declare (xargs :guard (and (fn-oig-rowsp rows) (true-listp acc))))
  (if (consp rows)
      (fn-oig-lines-loop (cdr rows) (revappend (fn-oig-line (car rows)) acc))
    (revappend acc nil)))

(defun fn-oig-lines (rows)
  (declare (xargs :guard (fn-oig-rowsp rows) :verify-guards nil))
  (mbe :logic
       (if (consp rows)
           (append (fn-oig-line (car rows)) (fn-oig-lines (cdr rows)))
         nil)
       :exec (fn-oig-lines-loop rows nil)))

(local
 (defthm fn-oig-revappend-revappend
   (equal (revappend (revappend a b) c)
          (revappend b (append a c)))))

(local
 (defthm fn-oig-lines-loop-is-revappend
   (equal (fn-oig-lines-loop rows acc)
          (revappend acc (fn-oig-lines rows)))
   :hints (("Goal" :in-theory (disable fn-oig-line)))))

(verify-guards fn-oig-lines
  :hints (("Goal" :in-theory (disable fn-oig-line))))

; -----------------------------------------------------------------------------
; The report

; `inspect group=GROUP members=N'
(defun fn-oig-members-line (group count)
  (declare (xargs :guard (and (stringp group) (natp count))))
  (append (fn-oig-text "inspect group=")
          (fn-oig-text group)
          (fn-oig-text " members=")
          (fn-oig-nat count)
          *fn-oig-lf*))

; Refused by name, with what it would take.
(defun fn-oig-refused-line (group)
  (declare (xargs :guard (stringp group)))
  (append (fn-oig-text "refused unknown-group group=")
          (fn-oig-text group)
          (fn-oig-text " this node carries no such group; what it would take: a group this node's configuration names (fn operator CONFIG group create GROUP)")
          *fn-oig-lf*))

(defun fn-oig-memberp (x l)
  (declare (xargs :guard t))
  (if (consp l)
      (or (equal x (car l)) (fn-oig-memberp x (cdr l)))
    nil))

; The subject: the report of GROUP over ARCHIVE (the acceptance state: its
; groups and its articles).  A group the archive does not carry is refused by
; name; every other answers the members line and one line per row.
(defun fn-oig-report (group archive)
  (declare (xargs :guard (stringp group) :verify-guards nil))
  (if (fn-oig-memberp group (fn-state-groups archive))
      (let ((rows (fn-oig-rows group 1 *fn-nntp-max-article-number*
                               (fn-state-articles archive))))
        (append (fn-oig-members-line group (len rows))
                (fn-oig-lines rows)))
    (fn-oig-refused-line group)))

(verify-guards fn-oig-report
  :hints (("Goal" :in-theory (disable fn-oig-rows fn-oig-lines))))

; The exit code the client reads back from the octets it printed: 0 for a
; report, 1 for the refusal (ACL2 decides it; the host prints and exits).
(defun fn-oig-prefixp (p o)
  (declare (xargs :guard t))
  (if (consp p)
      (and (consp o) (equal (car p) (car o)) (fn-oig-prefixp (cdr p) (cdr o)))
    t))

(defun fn-oig-report-exit (octets)
  (declare (xargs :guard t))
  (if (fn-oig-prefixp (fn-oig-text "inspect group=") octets) 0 1))

(local
 (defthm fn-oig-prefixp-of-append
   (fn-oig-prefixp p (append p x))))

; The exit is the archive's membership word: 0 exactly when the archive
; carries the group.
(defthm fn-oig-report-exit-is-the-membership
  (equal (fn-oig-report-exit (fn-oig-report group archive))
         (if (fn-oig-memberp group (fn-state-groups archive)) 0 1))
  :hints (("Goal" :in-theory (e/d (fn-oig-report fn-oig-report-exit
                                   fn-oig-members-line fn-oig-refused-line)
                                  (fn-oig-rows fn-oig-lines fn-oig-nat)))))

(in-theory (disable fn-oig-kindp fn-oig-insert fn-oig-rows fn-oig-line
                    fn-oig-lines fn-oig-members-line fn-oig-refused-line
                    fn-oig-report fn-oig-report-exit))
