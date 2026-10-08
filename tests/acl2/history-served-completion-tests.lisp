; A reachable completing owner, and a resident history corrupted after sync.
(in-package "ACL2")
(include-book "owner-served-invariants-tests")
(include-book "../../books/history-served-finish")
(include-book "../../books/defkeystone")

(defconst *hsvt-store* (fn-own-store *osi-completing*))
(defconst *hsvt-history* (fn-sf-records (fn-sn-files *hsvt-store*)))

(defthm fn-hsvt-reader-positive
  (and (fn-sn-statep *hsvt-store*)
       (fn-hist-of-storep *hsvt-history* *hsvt-store*)
       (equal (fn-hist-completion-record *hsvt-store* *hsvt-history*)
              (fn-ccar-completion-record *hsvt-store*))))

(defthm fn-hsvt-reader-missing-history
  (and (fn-sn-statep *hsvt-store*)
       (not (fn-hist-of-storep nil *hsvt-store*))
       (not (equal (fn-hist-completion-record *hsvt-store* nil)
                   (fn-ccar-completion-record *hsvt-store*))))
  :hints (("Goal" :in-theory (enable fn-hist-completion-record))))

(defconst *hsvt-bad-store*
 (fn-sn-make-v2 nil 0
  (fn-sf-make :completing 1 nil '(bad) nil '(nil) nil nil)
  nil nil nil 0 nil nil 0))

(defthm fn-hsvt-reader-missing-store-invariant
 (and (not (fn-sn-statep *hsvt-bad-store*))
      (fn-hist-of-storep '(bad) *hsvt-bad-store*)
      (not (equal (fn-hist-completion-record *hsvt-bad-store* '(bad))
                  (fn-ccar-completion-record *hsvt-bad-store*))))
 :hints (("Goal" :in-theory (enable fn-hist-completion-record
 fn-ccar-completion-record fn-ccar-seek-at fn-evc-carried-definitions))))

(defthm fn-hsvt-reader-lost-completion
 (and (fn-sn-statep *hsvt-store*)
      (fn-hist-of-storep *hsvt-history* *hsvt-store*)
      (not (equal nil (fn-ccar-completion-record *hsvt-store*)))))

(defthm fn-hsvt-store-break
 (and (fn-hist-of-storep '(bad) *hsvt-bad-store*)
      (not (fn-sn-statep *hsvt-bad-store*))
      (not (equal (fn-hist-completion-record *hsvt-bad-store* '(bad))
                  (fn-ccar-completion-record *hsvt-bad-store*)))))

(defthm fn-hsvt-completion-mutation
 (and (fn-sn-statep *hsvt-store*)
      (fn-hist-of-storep *hsvt-history* *hsvt-store*)
      (equal (fn-hist-completion-record *hsvt-store* *hsvt-history*)
             (fn-ccar-completion-record *hsvt-store*))
      (not (equal nil (fn-ccar-completion-record *hsvt-store*)))))

(defteeth fn-hist-completion-record-is-reference
  :claim (((store (fn-sn-statep s)) (history (fn-hist-of-storep hist s)))
          (equal (fn-hist-completion-record s hist) (fn-ccar-completion-record s)))
  :subject fn-owner-finish-synced
  :witness ((s *hsvt-store*) (hist *hsvt-history*))
  :witness-lemma fn-hsvt-reader-positive
  :breaks ((store ((s *hsvt-bad-store*) (hist '(bad))) :lemma fn-hsvt-store-break)
           (history ((s *hsvt-store*) (hist nil)) :lemma fn-hsvt-reader-missing-history))
  :mutations ((lost-completion
               (:conclusion (equal nil (fn-ccar-completion-record s)))
               ((s *hsvt-store*) (hist *hsvt-history*))
               :fault "a served reader returning nil loses an enabled durable completion"
               :lemma fn-hsvt-completion-mutation)))
