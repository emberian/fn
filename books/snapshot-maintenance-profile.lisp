; PRF-1142 / SCN-1048. Selected Linux x86-64 signed-long backing profile.
; The native writer uses signed sb-alien:long offsets. This check precedes
; actual ledger growth; it is not whole-operation runtime adequacy.
(in-package "ACL2")
(include-book "snapshot-maintenance-demand")

(defun fn-osj-native-offset-max ()
 (declare (xargs :guard t))
 (- (expt 2 63) 1))

(defun fn-osj-native-backingp (request)
 (declare (xargs :guard t))
 (and (natp (fn-omk-at 7 request))
      (<= (fn-omk-at 7 request) (fn-osj-native-offset-max))
      (natp (fn-omk-at 8 request))
      (<= (fn-omk-at 8 request) (fn-osj-native-offset-max))
      (natp (fn-omk-at 9 request))
      (<= (fn-omk-at 9 request) (fn-osj-native-offset-max))))

(defun fn-osj-native-grow (ledger maintenance source stage request)
 (declare (xargs :guard t))
 (if (not (fn-osj-native-backingp request))
     (mv '(:refused :checkpoint-offset-profile) ledger)
   (fn-osj-grow ledger maintenance source stage request)))

(defun fn-osj-native-grant-livep (grant ledger)
 (declare (xargs :guard t))
 (and (fn-osj-native-backingp grant) (fn-osj-grant-livep grant ledger)))

(defthm fn-osj-native-grown-authority-is-live
 (implies (equal (car (mv-nth 0
                       (fn-osj-native-grow ledger maintenance source stage request)))
                 :checkpoint-funded)
          (fn-osj-native-grant-livep
           (mv-nth 0 (fn-osj-native-grow ledger maintenance source stage request))
           (mv-nth 1 (fn-osj-native-grow ledger maintenance source stage request))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-osj-native-grow fn-osj-native-grant-livep
                                    fn-osj-native-backingp fn-omk-at)
          :use ((:instance fn-osj-grown-authority-is-live)
                (:instance fn-osj-grown-authority-matches-exact-request)))))

(defthm fn-osj-native-grown-authority-preserves-pool-funding
 (implies (equal (car (mv-nth 0
                       (fn-osj-native-grow ledger maintenance source stage request)))
                 :checkpoint-funded)
          (fn-prs-fundedp
           (fn-prl-nth 0 ledger) (fn-prl-baseline ledger) '(0 0 0 0 0)
           (fn-prl-nth 1 (mv-nth 1
                          (fn-osj-native-grow ledger maintenance source stage request)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-osj-native-grow)
          :use ((:instance fn-osj-grown-authority-preserves-pool-funding)))))

(defthm fn-osj-native-profile-refusal-retains-ledger
 (implies (not (fn-osj-native-backingp request))
          (equal (fn-osj-native-grow ledger maintenance source stage request)
                 (list '(:refused :checkpoint-offset-profile) ledger)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-osj-native-grow))))

; The actual writer must also carry each effect's interval within its exact
; captured stage/spool extent. This is the scalar composition boundary,
; not a theorem that its current controller already carries that fact.
(defun fn-osj-native-slicep (extent offset count)
 (declare (xargs :guard t))
 (and (natp extent) (natp offset) (natp count)
      (<= extent (fn-osj-native-offset-max))
      (<= (+ offset count) extent)))

(defthm fn-osj-native-slice-representable
 (implies (fn-osj-native-slicep extent offset count)
          (and (natp offset) (natp count) (natp (+ offset count))
               (<= offset (fn-osj-native-offset-max))
               (<= count (fn-osj-native-offset-max))
               (<= (+ offset count) (fn-osj-native-offset-max))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-osj-native-slicep))))

(in-theory (disable fn-osj-native-offset-max fn-osj-native-backingp
                    fn-osj-native-grow fn-osj-native-grant-livep
                    fn-osj-native-slicep))
