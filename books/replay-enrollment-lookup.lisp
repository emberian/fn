; One retained evidence row or one borrowed enrollment octet per step.
; Entries are produced with the same snapshot decision, not supplied grants.
(in-package "ACL2")
(include-book "replay-enrollment-span-equality")

; Evidence row4 = literal snapshot, :enrolled/:none, borrowed spans3, source.
(defun fn-rse-evidence (snapshot kind spans source)
 (declare (xargs :guard t))
 (list snapshot kind spans source))
(defun fn-rse-evidence-shapep (entry)
 (declare (xargs :guard t))
 (and (fn-rsc-widthp 4 entry)
      (if (eq (fn-rsc-at 1 entry) :none) (null (fn-rsc-at 2 entry))
       (and (eq (fn-rsc-at 1 entry) :enrolled)
            (fn-rsc-widthp 3 (fn-rsc-at 2 entry))
            (fn-rse-span-shapep (fn-rsc-at 0 (fn-rsc-at 2 entry)))
            (fn-rse-span-shapep (fn-rsc-at 1 (fn-rsc-at 2 entry)))
            (fn-rse-span-shapep (fn-rsc-at 2 (fn-rsc-at 2 entry)))))))
; Fixed7: phase, query principal, query keys, remaining borrowed evidence,
; current equality continuation, captured operation source, selected entry.
(defun fn-rse-lookup-state (phase principal keys remaining comparison source answer)
 (declare (xargs :guard t))
 (list phase principal keys remaining comparison source answer))
(defun fn-rse-lookup-begin (principal keys evidence source)
 (declare (xargs :guard t))
 (if (fn-rse-keys-shapep keys)
  (fn-rse-lookup-state :seek principal keys evidence nil source nil)
  (fn-rse-lookup-state :done principal keys nil nil source nil)))
(defun fn-rse-lookup-step (s)
 (declare (xargs :guard t))
 (if (not (fn-rsc-widthp 7 s)) (mv :refused s)
  (let ((phase (fn-rsc-at 0 s)) (principal (fn-rsc-at 1 s))
        (keys (fn-rsc-at 2 s)) (remaining (fn-rsc-at 3 s))
        (comparison (fn-rsc-at 4 s)) (source (fn-rsc-at 5 s)))
   (cond
    ((member-eq phase '(:found :done)) (mv :done s))
    ((eq phase :seek)
     (cond
      ((not (consp remaining))
       (if (null remaining)
        (mv :done (fn-rse-lookup-state :done principal keys nil nil source nil))
        (mv :refused s)))
      ((not (fn-rse-evidence-shapep (car remaining))) (mv :refused s))
      ((eq (fn-rsc-at 1 (car remaining)) :none)
       (mv :working (fn-rse-lookup-state :seek principal keys (cdr remaining)
                                         nil source nil)))
      (t (mv :working (fn-rse-lookup-state :compare principal keys remaining
        (fn-rse-equality-begin principal keys (fn-rsc-at 2 (car remaining)) source)
        source nil)))))
    ((eq phase :compare)
     (if (not (consp remaining)) (mv :refused s)
      (mv-let (word next) (fn-rse-equality-step comparison)
       (cond
        ((eq word :refused) (mv :refused s))
        ((not (eq word :done))
         (mv :working (fn-rse-lookup-state :compare principal keys remaining
                                           next source nil)))
        ((fn-rsc-at 7 next)
         (mv :done (fn-rse-lookup-state :found principal keys remaining
                                        next source (car remaining))))
        (t (mv :working (fn-rse-lookup-state :seek principal keys (cdr remaining)
                                             nil source nil)))))))
    (t (mv :refused s))))))

; Proof-only model. This is not an executable retained-state validator.
(defun fn-rse-evidence-value (entry)
 (declare (xargs :guard t))
 (if (eq (fn-rsc-at 1 entry) :enrolled)
  (fn-rse-enrollment-model (fn-rsc-at 2 entry)) nil))
(defun fn-rse-evidence-ledgerp (entries)
 (declare (xargs :guard t))
 (if (consp entries)
  (and (fn-rse-evidence-shapep (car entries))
       (or (eq (fn-rsc-at 1 (car entries)) :none)
        (fn-rse-spans-provenance-shapep (fn-rsc-at 2 (car entries))))
       (fn-rse-evidence-ledgerp (cdr entries)))
  (null entries)))
(defun fn-rse-enrolled-model (principal keys entries)
 (declare (xargs :guard t))
 (if (consp entries)
  (or (equal (list principal keys) (fn-rse-evidence-value (car entries)))
      (fn-rse-enrolled-model principal keys (cdr entries)))
  nil))
(defun fn-rse-lookup-outcome (s)
 (declare (xargs :guard t))
 (cond ((eq (fn-rsc-at 0 s) :found) t)
       ((eq (fn-rsc-at 0 s) :done) nil)
       (t (fn-rse-enrolled-model (fn-rsc-at 1 s) (fn-rsc-at 2 s)
                                (fn-rsc-at 3 s)))))
(defun fn-rse-lookup-invariantp (s)
 (declare (xargs :guard t))
 (and (fn-rsc-widthp 7 s) (fn-rse-keys-shapep (fn-rsc-at 2 s))
      (fn-rse-evidence-ledgerp (fn-rsc-at 3 s))
      (member-eq (fn-rsc-at 0 s) '(:seek :compare :found :done))
      (if (eq (fn-rsc-at 0 s) :compare)
       (and (consp (fn-rsc-at 3 s))
            (fn-rse-equality-invariantp (fn-rsc-at 4 s))
            (equal (fn-rse-equality-outcome (fn-rsc-at 4 s))
             (equal (list (fn-rsc-at 1 s) (fn-rsc-at 2 s))
                    (fn-rse-evidence-value (car (fn-rsc-at 3 s))))))
       (if (eq (fn-rsc-at 0 s) :found)
        (and (consp (fn-rsc-at 3 s))
             (equal (fn-rsc-at 6 s) (car (fn-rsc-at 3 s)))
             (equal (list (fn-rsc-at 1 s) (fn-rsc-at 2 s))
                    (fn-rse-evidence-value (car (fn-rsc-at 3 s)))))
        (if (eq (fn-rsc-at 0 s) :done)
         (and (null (fn-rsc-at 3 s)) (null (fn-rsc-at 6 s))) t)))))

(local (defthm fn-rse-ledger-head-and-tail
 (implies (and (fn-rse-evidence-ledgerp entries) (consp entries))
  (and (fn-rse-evidence-shapep (car entries))
       (fn-rse-evidence-ledgerp (cdr entries))
       (or (eq (fn-rsc-at 1 (car entries)) :none)
        (fn-rse-spans-provenance-shapep (fn-rsc-at 2 (car entries))))))
 :hints (("Goal" :expand ((fn-rse-evidence-ledgerp entries))
          :in-theory (disable fn-rse-evidence-ledgerp fn-rse-evidence-shapep
                              fn-rse-spans-provenance-shapep)))))
(local (defthm fn-rse-enrolled-model-head-unfolds
 (equal (fn-rse-enrolled-model principal keys entries)
  (if (consp entries)
   (or (equal (list principal keys) (fn-rse-evidence-value (car entries)))
       (fn-rse-enrolled-model principal keys (cdr entries))) nil))
 :rule-classes nil
 :hints (("Goal" :expand ((fn-rse-enrolled-model principal keys entries))
          :in-theory (disable fn-rse-enrolled-model fn-rse-evidence-value)))))
(defthm fn-rse-lookup-begin-refines-retained-enrollment-model
 (implies (and (fn-rse-keys-shapep keys) (fn-rse-evidence-ledgerp evidence))
  (and (fn-rse-lookup-invariantp (fn-rse-lookup-begin principal keys evidence source))
       (equal (fn-rse-lookup-outcome
                (fn-rse-lookup-begin principal keys evidence source))
              (fn-rse-enrolled-model principal keys evidence))))
 :rule-classes nil
 :hints (("Goal" :in-theory
  (e/d (fn-rse-lookup-begin fn-rse-lookup-state fn-rse-lookup-invariantp
        fn-rse-lookup-outcome fn-rsc-at fn-rsc-widthp)
       (fn-rse-keys-shapep fn-rse-evidence-ledgerp fn-rse-enrolled-model)))))
(defthm fn-rse-lookup-step-preserves-complete-enrollment-and-source
 (implies (fn-rse-lookup-invariantp s)
  (and (fn-rse-lookup-invariantp (mv-nth 1 (fn-rse-lookup-step s)))
       (equal (fn-rse-lookup-outcome (mv-nth 1 (fn-rse-lookup-step s)))
              (fn-rse-lookup-outcome s))
       (equal (fn-rsc-at 5 (mv-nth 1 (fn-rse-lookup-step s))) (fn-rsc-at 5 s))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-rse-equality-begin-has-exact-public-value-comparison
         (principal (fn-rsc-at 1 s)) (keys (fn-rsc-at 2 s))
         (spans (fn-rsc-at 2 (car (fn-rsc-at 3 s)))) (source (fn-rsc-at 5 s)))
        (:instance fn-rse-equality-step-preserves-complete-comparison
         (s (fn-rsc-at 4 s)))
        (:instance fn-rse-completed-step-exposes-exact-comparison
         (s (fn-rsc-at 4 s)))
        (:instance fn-rse-ledger-head-and-tail (entries (fn-rsc-at 3 s)))
        (:instance fn-rse-enrolled-model-head-unfolds
         (principal (fn-rsc-at 1 s)) (keys (fn-rsc-at 2 s))
         (entries (fn-rsc-at 3 s))))
  :in-theory
   (e/d (fn-rse-lookup-step fn-rse-lookup-state fn-rse-lookup-invariantp
         fn-rse-lookup-outcome fn-rse-evidence-value fn-rse-evidence-shapep fn-rsc-at fn-rsc-widthp)
        (fn-rse-equality-step fn-rse-equality-begin fn-rse-equality-invariantp
         fn-rse-equality-outcome fn-rse-evidence-ledgerp
         fn-rse-enrollment-model fn-rse-enrolled-model
         fn-rse-spans-provenance-shapep fn-rse-keys-shapep)))))
