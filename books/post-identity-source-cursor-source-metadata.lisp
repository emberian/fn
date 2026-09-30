(in-package "ACL2")

(include-book "post-identity-source-cursor-source-after-path")

(local (defun fn-psc-source-recipe-resumep (c)
 (declare (xargs :guard t :verify-guards nil))
 (and (fn-psc-source-resumep c)
      (not (member-eq (fn-psc-get resume c)
       '(:start :skip-lock :after-lock :skip-key :after-key
         :source-path-field :source-path-agent :source-path-tail))))))

(local (defthm fn-psc-source-control-step-unfolds
 (implies (equal (fn-psc-get phase c) :control)
  (equal (fn-psc-step c byte) (fn-psc-control c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-step) (fn-psc-control nth len nfix))))))

(local (defthm fn-psc-source-ordinary-step-keeps-recipe-resume
 (implies (and (not (member-eq (fn-psc-get phase c) '(:control :info-choice)))
               (not (member-eq (fn-psc-get resume c)
                '(:start :skip-lock :after-lock :skip-key :after-key
                  :source-path-field :source-path-agent :source-path-tail))))
  (not (member-eq (fn-psc-get resume (fn-psc-step c byte))
                '(:start :skip-lock :after-lock :skip-key :after-key
                  :source-path-field :source-path-agent :source-path-tail))))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-return fn-psc-finish fn-psc-literal fn-psc-compare)
   (fn-psc-control fn-psc-expected nth len update-nth nfix))))))

(local (defthm fn-psc-source-ordinary-step-keeps-generated-path-flag
 (implies (not (equal (fn-psc-get phase c) :control))
  (equal (fn-psc-get has-path (fn-psc-step c byte)) (fn-psc-get has-path c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-return fn-psc-finish fn-psc-literal fn-psc-compare)
   (fn-psc-control fn-psc-expected nth len update-nth nfix))))))

(local (defthm fn-psc-source-control-keeps-recipe-resume
 (implies (and (fn-psc-source-recipe-resumep c) (equal (fn-psc-get phase c) :control))
  (not (member-eq (fn-psc-get resume (fn-psc-control c))
       '(:start :skip-lock :after-lock :skip-key :after-key
         :source-path-field :source-path-agent :source-path-tail))))
 :hints (("Goal" :in-theory (e/d (fn-psc-source-recipe-resumep fn-psc-source-resumep
    fn-psc-control fn-psc-compare fn-psc-literal fn-psc-agent-compare
    fn-psc-msgid-compare fn-psc-date-compare fn-psc-info-compare fn-psc-return fn-psc-finish)
   (fn-psc-step fn-psc-expected nth len update-nth nfix))))))

(local (defthm fn-psc-source-control-keeps-generated-path-flag
 (implies (not (member-eq (fn-psc-get resume c)
                '(:source-path-field :source-path-agent :source-path-tail)))
  (equal (fn-psc-get has-path (fn-psc-control c)) (fn-psc-get has-path c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-control fn-psc-compare fn-psc-literal fn-psc-agent-compare
    fn-psc-msgid-compare fn-psc-date-compare fn-psc-info-compare fn-psc-return fn-psc-finish)
   (fn-psc-step nth len update-nth nfix))))))

(local (defthm fn-psc-source-info-choice-keeps-recipe-resume
 (implies (and (fn-psc-source-recipe-resumep c) (equal (fn-psc-get phase c) :info-choice))
  (not (member-eq (fn-psc-get resume (fn-psc-step c byte))
       '(:start :skip-lock :after-lock :skip-key :after-key
         :source-path-field :source-path-agent :source-path-tail))))
 :hints (("Goal" :in-theory (e/d (fn-psc-source-recipe-resumep fn-psc-source-resumep
    fn-psc-step fn-psc-compare fn-psc-literal fn-psc-return fn-psc-finish)
   (fn-psc-control fn-psc-expected nth len update-nth nfix))))))

(local (defthm fn-psc-source-step-preserves-recipe-resumes
 (implies (fn-psc-source-recipe-resumep c)
  (fn-psc-source-recipe-resumep (fn-psc-step c byte)))
 :hints (("Goal" :cases ((equal (fn-psc-get phase c) :control)
                        (equal (fn-psc-get phase c) :info-choice))
  :use (fn-psc-step-preserves-source-resumes fn-psc-source-control-keeps-recipe-resume
        fn-psc-source-info-choice-keeps-recipe-resume fn-psc-source-ordinary-step-keeps-recipe-resume)
  :in-theory (e/d (fn-psc-source-recipe-resumep)
   (fn-psc-step fn-psc-control fn-psc-source-resumep fn-psc-step-preserves-source-resumes
    fn-psc-source-control-keeps-recipe-resume fn-psc-source-info-choice-keeps-recipe-resume
    fn-psc-source-ordinary-step-keeps-recipe-resume nth len nfix))))))

(local (defthm fn-psc-source-recipe-step-preserves-generated-path-flag
 (implies (fn-psc-source-recipe-resumep c)
  (equal (fn-psc-get has-path (fn-psc-step c byte)) (fn-psc-get has-path c)))
 :hints (("Goal" :cases ((equal (fn-psc-get phase c) :control))
  :use (fn-psc-source-control-keeps-generated-path-flag fn-psc-source-ordinary-step-keeps-generated-path-flag)
  :in-theory (e/d (fn-psc-source-recipe-resumep)
   (fn-psc-step fn-psc-control fn-psc-source-resumep fn-psc-source-control-keeps-generated-path-flag
    fn-psc-source-ordinary-step-keeps-generated-path-flag nth len nfix))))))

(local (defthm fn-psc-source-recipe-paid-run-preserves-generated-path-flag
 (implies (fn-psc-source-recipe-resumep c)
  (equal (fn-psc-get has-path (fn-psc-model-byte-run fuel c incoming held)) (fn-psc-get has-path c)))
 :hints (("Goal" :induct (fn-psc-model-byte-run fuel c incoming held)
  :in-theory (e/d (fn-psc-model-byte-run)
   (fn-psc-step fn-psc-source-recipe-resumep nth len nfix))))))

(local (defthm fn-psc-source-stamp-initializer-establishes-recipe-resumes
 (implies (fn-psc-source-contextp c incoming held)
  (fn-psc-source-recipe-resumep (fn-psc-literal pos *fn-inj-injection-date-field* :source-stamp c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-source-contextp fn-psc-source-recipe-resumep fn-psc-source-resumep
                    fn-psc-literal fn-psc-compare)
   (fn-psc-model-source nth len update-nth nfix))))))

(local (defthm fn-psc-source-literal-keeps-generated-path-flag
 (equal (fn-psc-get has-path (fn-psc-literal pos bytes resume c)) (fn-psc-get has-path c))
 :hints (("Goal" :in-theory (e/d (fn-psc-literal fn-psc-compare) (nth len update-nth nfix))))))

(defthm fn-psc-source-after-path-complete-preserves-generated-path-flag
 (implies (and (fn-psc-source-contextp c incoming held) (natp pos)
               (<= pos (len (fn-psc-model-source c incoming held))))
  (equal (fn-psc-get has-path (fn-psc-model-source-after-path-complete pos c incoming held))
         (fn-psc-get has-path c)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-source-stamp-initializer-establishes-recipe-resumes)
        (:instance fn-psc-source-recipe-paid-run-preserves-generated-path-flag
          (fuel (fn-psc-model-source-after-path-cost pos c incoming held))
          (c (fn-psc-literal pos *fn-inj-injection-date-field* :source-stamp c))))
  :in-theory (disable fn-psc-source-contextp fn-psc-source-recipe-resumep fn-psc-model-source
    fn-psc-model-source-after-path-complete fn-psc-model-source-after-path-cost fn-psc-model-byte-run fn-psc-literal
    fn-psc-source-stamp-initializer-establishes-recipe-resumes
    fn-psc-source-recipe-paid-run-preserves-generated-path-flag nth len nfix))))

(local (in-theory (disable fn-psc-source-control-step-unfolds)))
