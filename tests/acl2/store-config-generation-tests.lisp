(in-package "ACL2")
(include-book "must-fail-checked")
(include-book "../../books/store-config-generation")
(include-book "store-capacity-config-tests")

(defconst *cvcg-configs* (list *fn-cfg-default-record* *cvc-other*))
(defconst *cvcg-replayed* (fn-cnode-config-replay *cvcg-configs*))
; fn-cvcg-config-replay-generation-counts-records: successful nonempty
; configured-node replay, with the complete hypothesis and conclusion.
(assert-event
 (and (equal (fn-replay-result-kind *cvcg-replayed*) :ok)
      (equal (len *cvcg-configs*) 2)
      (equal (fn-cfg-generation
              (fn-cnode-config (fn-replay-result-node *cvcg-replayed*)))
             (len *cvcg-configs*))))

; Remove successful replay: the repeated record has a valid record shape,
; but a stale sequence. The replay faults after one record, short of len 2.
(defconst *cvcg-stale-configs*
  (list *fn-cfg-default-record* *fn-cfg-default-record*))
(defconst *cvcg-stale-replayed* (fn-cnode-config-replay *cvcg-stale-configs*))
(assert-event
 (and (not (equal (fn-replay-result-kind *cvcg-stale-replayed*) :ok))
      (not (equal (fn-cfg-generation
                   (fn-cnode-config (fn-replay-result-node *cvcg-stale-replayed*)))
                  (len *cvcg-stale-configs*)))))
(must-fail-checked
 (assert-event
  (equal (fn-cfg-generation
          (fn-cnode-config (fn-replay-result-node *cvcg-stale-replayed*)))
         (len *cvcg-stale-configs*))))

(defconst *cvcg-profile* (fn-bs-profile-set-fields *fn-bs-profile-defaults* '((10 . 3))))
(defconst *cvcg-existing-configs* (list *fn-cfg-default-record*))
(defconst *cvcg-authorized*
  (fn-cvec-native-admin-authorize
   nil 0 *cvcg-existing-configs* *cvc-other* t nil *cvcg-profile*))
; fn-cvcg-accepted-publication-count-fits-profile: complete accepted writer
; antecedent and both conclusion clauses, authorizing a second record.
(assert-event
 (and (equal (fn-native-admin-publication-status *cvcg-authorized*) :accepted)
      (equal (fn-native-admin-publication-generation *cvcg-authorized*)
             (+ 1 (len *cvcg-existing-configs*)))
      (<= (+ 1 (len *cvcg-existing-configs*))
          (nfix (fn-bs-profile-max-config-generations *cvcg-profile*)))))

; Remove acceptance: the profile cannot fit that next namespace entry;
; the actual profile-aware writer refuses it before any publication.
(defconst *cvcg-short-profile*
  (fn-bs-profile-set-fields *fn-bs-profile-defaults* '((10 . 1))))
(defconst *cvcg-refused*
  (fn-cvec-native-admin-authorize
   nil 0 *cvcg-existing-configs* *cvc-other* t nil *cvcg-short-profile*))
(assert-event
 (and (not (equal (fn-native-admin-publication-status *cvcg-refused*) :accepted))
      (not (and
            (equal (fn-native-admin-publication-generation *cvcg-refused*)
                   (+ 1 (len *cvcg-existing-configs*)))
            (<= (+ 1 (len *cvcg-existing-configs*))
                (nfix (fn-bs-profile-max-config-generations *cvcg-short-profile*)))))))
(must-fail-checked
 (assert-event
  (and (equal (fn-native-admin-publication-generation *cvcg-refused*)
              (+ 1 (len *cvcg-existing-configs*)))
       (<= (+ 1 (len *cvcg-existing-configs*))
           (nfix (fn-bs-profile-max-config-generations *cvcg-short-profile*))))))
