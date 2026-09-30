(in-package "ACL2")
(include-book "../../host/history-image-producer-host")

; Complete logical frame for the actual controller's profile refusal.
; This is an unfolding fact, not a registry completion keystone.
(defthm fn-hpi-native-profile-refusal-by-definition
  (implies (and (fn-omk-widthp c 25)
                (equal (fn-omk-at 0 c) :need-growth)
                (not (fn-osj-native-backingp (fn-hpi-growth-request c))))
           (equal (fn-hpi-tick c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
                  (list '(:refused :checkpoint-offset-profile) nil c ledger
                        fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-hpi-tick fn-osj-native-grow)
                                   (fn-hpi-growth-request fn-osj-native-backingp
                                    fn-hpi-buffer-step fn-hpi-stream-step fn-hpi-reset-buffer)))))

; Explicit corrupted-layout mutation: the ordinary constructor's small
; admitted layout is altered to exceed the selected signed offset profile.
; It is not a claim that a legitimate huge current-format census gets here.
(defun hpi-profile-mutation-attempt (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
  (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) :verify-guards nil))
  (let* ((initial (fn-hpi-begin 1 8 1 1 '(7 (9 1) 0 0) '(:maintenance 19 7 1) 19
                              163840 "node" 17 "trail"))
         (layout (update-nth 2 (expt 2 63) (fn-omk-at 6 initial)))
         (c (fn-hpi-set 6 layout initial))
         (fn-hpq0 (fn-hpb-begin :old-source :old-lease fn-hpq0))
         (fn-hpq1 (fn-hpb-begin :old-source :old-lease fn-hpq1))
         (fn-hpq2 (fn-hpb-begin :old-source :old-lease fn-hpq2))
         (fn-hpq3 (fn-hpb-begin :old-source :old-lease fn-hpq3))
         (fn-hpb (fn-hpb-begin :old-source :old-lease fn-hpb)))
    (mv-let (stored fn-hpb) (fn-hpb-put 42 fn-hpb)
      (mv-let (v effect next ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
        (fn-hpi-tick c nil '(:unchanged-ledger) fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
        (mv (and (eq stored :stored) (fn-omk-widthp c 25)
                 (equal (fn-omk-at 0 initial) :need-growth)
                 (fn-osj-native-backingp (fn-hpi-growth-request initial))
                 (not (fn-osj-native-backingp (fn-hpi-growth-request c)))
                 (equal v '(:refused :checkpoint-offset-profile)) (null effect)
                 (equal next c) (equal ledger '(:unchanged-ledger))
                 (equal (fn-hpb-prefix fn-hpb) '(42))
                 (equal (fn-hpb-epoch fn-hpb) :old-source)
                 (equal (fn-hpb-lease fn-hpb) :old-lease)
                 (equal (fn-hpb-epoch fn-hpq0) :old-source)
                 (equal (fn-hpb-epoch fn-hpq1) :old-source)
                 (equal (fn-hpb-epoch fn-hpq2) :old-source)
                 (equal (fn-hpb-epoch fn-hpq3) :old-source)
                 (equal (fn-hpb-used fn-hpq0) 0) (equal (fn-hpb-used fn-hpq1) 0)
                 (equal (fn-hpb-used fn-hpq2) 0) (equal (fn-hpb-used fn-hpq3) 0))
            fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))))

(defun hpi-profile-local-mutation ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-hpq0 (mv-let (result fn-hpq0) (with-local-stobj fn-hpq1 (mv-let (result fn-hpq0 fn-hpq1) (with-local-stobj fn-hpq2 (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2) (with-local-stobj fn-hpq3 (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3) (with-local-stobj fn-hpb (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) (with-local-stobj pgs-digest-state (mv-let (result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) (hpi-profile-mutation-attempt fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) (mv result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))) (mv result fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3))) (mv result fn-hpq0 fn-hpq1 fn-hpq2))) (mv result fn-hpq0 fn-hpq1))) (mv result fn-hpq0))) result)))
(assert-event (hpi-profile-local-mutation))
