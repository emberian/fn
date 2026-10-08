; A reserved candidate, and a mid-run frontier reused after a committed event.
(in-package "ACL2")
(include-book "../../books/owner-prepare-fresh-frontier")
(include-book "../../books/defkeystone")

(defconst *hpft-record*
 (fn-store-retention-event-make :undertake 0 0 0 "one" "subject" "evidence" 1))
(defconst *hpft-repeated*
 (fn-store-retention-event-make :undertake 1 0 0 "two" "subject" "evidence" 1))
(defconst *hpft-files*
 (fn-sf-frontier-dir-result
  (fn-sf-frontier-replace-result
   (fn-sf-frontier-file-result (fn-sf-start-frontier (fn-sf-initial-state)) :ok) :ok) :ok))
(defconst *hpft-reused-frontier*
 (fn-sf-make :reserved 1 nil (list *hpft-record*) nil nil nil 0))

(defthm fn-hpft-candidate-positive
 (and (fn-sf-statep *hpft-files*) (fn-store-event-p *hpft-record*)
      (<= (fn-sf-next-lower (fn-sf-records *hpft-files*) 0)
          (+ -1 (fn-sf-frontier *hpft-files*)))
      (fn-hpf-files-candidatep *hpft-record* *hpft-files*)
      (equal (fn-hpf-files-candidatep *hpft-record* *hpft-files*)
             (fn-pcar-files-candidatep *hpft-record* *hpft-files*))))

(defthm fn-hpft-frontier-reuse-breaks-equality
 (and (not (<= (fn-sf-next-lower (fn-sf-records *hpft-reused-frontier*) 0)
                (+ -1 (fn-sf-frontier *hpft-reused-frontier*))))
      (not (equal (fn-hpf-files-candidatep *hpft-repeated* *hpft-reused-frontier*)
                  (fn-pcar-files-candidatep *hpft-repeated* *hpft-reused-frontier*)))))

(defthm fn-hpft-sequence-check-mutation
 (and (<= (fn-sf-next-lower (fn-sf-records *hpft-files*) 0)
          (+ -1 (fn-sf-frontier *hpft-files*)))
      (equal (fn-hpf-files-candidatep *hpft-repeated* *hpft-files*)
             (fn-pcar-files-candidatep *hpft-repeated* *hpft-files*))
      (not (equal t (fn-pcar-files-candidatep *hpft-repeated* *hpft-files*)))))

(defthm fn-hpft-candidate-witness
 (and (<= (fn-sf-next-lower (fn-sf-records *hpft-files*) 0)
          (+ -1 (fn-sf-frontier *hpft-files*)))
      (equal (fn-hpf-files-candidatep *hpft-record* *hpft-files*)
             (fn-pcar-files-candidatep *hpft-record* *hpft-files*))))

(defteeth fn-hpf-files-candidatep-is-reference
 :claim (((fresh (<= (fn-sf-next-lower (fn-sf-records files) 0)
                    (+ -1 (fn-sf-frontier files)))))
         (equal (fn-hpf-files-candidatep record files)
                (fn-pcar-files-candidatep record files)))
 :subject fn-owner-prepare-retention-served
 :witness ((files *hpft-files*) (record *hpft-record*))
 :witness-lemma fn-hpft-candidate-witness
 :breaks ((fresh ((files *hpft-reused-frontier*) (record *hpft-repeated*))
                  :lemma fn-hpft-frontier-reuse-breaks-equality))
 :mutations ((omit-sequence-check
   (:conclusion (equal t (fn-pcar-files-candidatep record files)))
   ((files *hpft-files*) (record *hpft-repeated*))
   :fault "accepting the successor sequence in an empty history corrupts prepare"
   :lemma fn-hpft-sequence-check-mutation)))
