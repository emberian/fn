; Exact unchanged carried source-resume lineage packet.
(in-package "ACL2")
(include-book "post-identity-source-cursor-invariants")

; Carried source continuation lineage: both inverses retain the incoming span.

(defun fn-psc-source-resumep (c)
 (declare (xargs :guard t :verify-guards nil))
 (and (member-eq (fn-psc-get mode c) '(:source-incoming :source-held))
      (or (equal (fn-psc-get phase c) :done)
          (and (member-eq (fn-psc-get resume c)
           '(:start :skip-lock :after-lock :skip-key :after-key
             :source-path-field :source-path-agent :source-path-tail
             :source-stamp :source-stamp-tail :source-info-simple :source-info-v1
             :source-v1-msgid :source-v1-date :source-optional-msgid :source-optional-date :source-found
             :msgid-field :msgid-content :msgid-tail :date-field :date-content :date-tail
             :info-field :info-agent :info-tail :unsplice-field :unsplice-agent :unsplice-tail))
           (implies (equal (fn-psc-get phase c) :info-choice)
                    (equal (fn-psc-get resume c) :info-agent))
           (implies (member-eq (fn-psc-get phase c) '(:path-scan :path-cr))
                    (member-eq (fn-psc-get resume c) '(:source-found :unsplice-field)))
           (implies (member-eq (fn-psc-get resume c)
              '(:msgid-field :msgid-content :msgid-tail :date-field :date-content :date-tail
                :info-field :info-agent :info-tail))
            (member-eq (fn-psc-get aux c)
              '(:source-info-simple :source-info-v1 :source-v1-msgid :source-v1-date
                :source-optional-msgid :source-optional-date)))))))

(defthm fn-psc-begin-establishes-source-resumes
 (implies (member-eq mode '(:source-incoming :source-held))
  (fn-psc-source-resumep (fn-psc-begin mode n msgid agent-span incoming-n)))
 :hints (("Goal" :in-theory (e/d (fn-psc-source-resumep fn-psc-begin fn-psc-finish)
                               (nth update-nth len nfix)))))

(defthm fn-psc-source-step-preserves-incoming-agent
 (implies (fn-psc-source-resumep c)
  (and (equal (fn-psc-get agent-start (fn-psc-step c byte)) (fn-psc-get agent-start c))
       (equal (fn-psc-get agent-end (fn-psc-step c byte)) (fn-psc-get agent-end c))))
 :hints (("Goal" :in-theory
  (e/d (fn-psc-source-resumep fn-psc-step fn-psc-control fn-psc-finish fn-psc-return
        fn-psc-compare fn-psc-literal fn-psc-agent-compare fn-psc-msgid-compare
        fn-psc-date-compare fn-psc-info-compare)
       (nth update-nth len nfix fn-psc-expected)))))

(local (defthm fn-psc-control-preserves-source-resumes
 (implies (and (fn-psc-source-resumep c) (equal (fn-psc-get phase c) :control))
  (fn-psc-source-resumep (fn-psc-control c)))
 :hints (("Goal" :in-theory
  (e/d (fn-psc-source-resumep fn-psc-control fn-psc-finish fn-psc-return
        fn-psc-compare fn-psc-literal fn-psc-agent-compare fn-psc-msgid-compare
        fn-psc-date-compare fn-psc-info-compare)
       (nth update-nth len nfix fn-psc-expected))))))

(local (defthm fn-psc-source-resumes-scalar-update
 (implies (and (natp slot) (not (member-equal slot '(0 1 14 20))))
  (equal (fn-psc-source-resumep (update-nth slot value c)) (fn-psc-source-resumep c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-source-resumep nfix) (nth update-nth len))))))

(local (defthm fn-psc-source-return-live
 (implies (and (fn-psc-source-resumep c) (not (equal (fn-psc-get phase c) :done)))
  (fn-psc-source-resumep (fn-psc-return ok c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-source-resumep fn-psc-return) (nth update-nth len nfix))))))

(local (defthm fn-psc-source-finish
 (implies (fn-psc-source-resumep c) (fn-psc-source-resumep (fn-psc-finish result c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-source-resumep fn-psc-finish) (nth update-nth len nfix))))))

(local (defthm fn-psc-source-compare-control-base
 (equal (fn-psc-source-resumep (fn-psc-compare p ref start count resume c))
        (fn-psc-source-resumep (fn-psc-return nil (fn-psc-set resume resume c))))
 :hints (("Goal" :in-theory (e/d (fn-psc-source-resumep fn-psc-compare fn-psc-return)
                               (nth update-nth len nfix))))))

(local (defthm fn-psc-info-choice-preserves-source-resumes
 (implies (and (fn-psc-source-resumep c) (equal (fn-psc-get phase c) :info-choice))
  (fn-psc-source-resumep (fn-psc-step c byte)))
 :hints (("Goal" :in-theory
  (e/d (fn-psc-source-resumep fn-psc-step fn-psc-finish fn-psc-return fn-psc-literal fn-psc-compare)
       (fn-psc-control nth update-nth len nfix fn-psc-expected))))))

(local (defthm fn-psc-path-scan-preserves-source-resumes
 (implies (and (fn-psc-source-resumep c)
               (member-eq (fn-psc-get phase c) '(:path-scan :path-cr)))
  (fn-psc-source-resumep (fn-psc-step c byte)))
 :hints (("Goal" :in-theory
  (e/d (fn-psc-source-resumep fn-psc-step fn-psc-finish fn-psc-return fn-psc-literal fn-psc-compare)
       (fn-psc-control nth update-nth len nfix fn-psc-expected))))))

(local (defthm fn-psc-source-ordinary-phase-update
 (implies (and (fn-psc-source-resumep c) (not (equal (fn-psc-get phase c) :done))
               (not (member-eq phase '(:info-choice :path-scan :path-cr))))
  (fn-psc-source-resumep (fn-psc-set phase phase c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-source-resumep) (nth update-nth len nfix))))))

(local (defthm fn-psc-ordinary-byte-preserves-source-resumes
 (implies (and (fn-psc-source-resumep c)
               (not (member-eq (fn-psc-get phase c) '(:control :info-choice :path-scan :path-cr))))
  (fn-psc-source-resumep (fn-psc-step c byte)))
 :hints (("Goal" :in-theory
  (e/d (fn-psc-step)
       (fn-psc-source-resumep fn-psc-control fn-psc-finish fn-psc-return
        nth update-nth len nfix fn-psc-expected))))))

(defthm fn-psc-step-preserves-source-resumes
 (implies (fn-psc-source-resumep c)
  (fn-psc-source-resumep (fn-psc-step c byte)))
 :hints (("Goal"
  :use ((:instance fn-psc-control-preserves-source-resumes)
        (:instance fn-psc-info-choice-preserves-source-resumes)
        (:instance fn-psc-path-scan-preserves-source-resumes)
        (:instance fn-psc-ordinary-byte-preserves-source-resumes))
  :cases ((equal (fn-psc-get phase c) :control))
  :in-theory (e/d (fn-psc-step)
   (fn-psc-source-resumep fn-psc-control fn-psc-finish fn-psc-return fn-psc-compare fn-psc-literal
    fn-psc-control-preserves-source-resumes fn-psc-info-choice-preserves-source-resumes
    fn-psc-path-scan-preserves-source-resumes fn-psc-ordinary-byte-preserves-source-resumes
    nth update-nth len nfix fn-psc-expected)))))

(in-theory (disable fn-psc-source-resumep))
