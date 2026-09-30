; Ghost cursor denotation for the actual scheduling tick. No model traversal
; runs during mapping, publication, checkpoint loading or authentication.
(in-package "ACL2")
(include-book "consumer-checkpoint-carry-map")
(include-book "consumer-account-metadata")

(defun fn-ccmm-target (kind value info)
 (declare (xargs :guard t :verify-guards nil :measure (acl2-count value)))
 (if (not (consp value)) nil
  (if (eq kind :list)
      (list (fn-cp-nth 0 info) (fn-cp-nth 0 (fn-cp-nth 1 info))
            (fn-ccmm-target :list (cdr value) (fn-ccm-info-tail info)))
    (let* ((entry (car value)) (ei (fn-cp-nth 1 info))
           (vi (fn-ccm-info-tail ei)))
     (list (fn-cp-nth 0 info) (fn-cp-nth 0 vi)
           (and (characterp (fn-cp-nth 0 entry))
                (fn-ccmm-target :trie (ec-call (cdr entry)) vi))
           (fn-ccmm-target :trie (cdr value) (fn-ccm-info-tail info)))))))

(defun fn-ccmm-stack-target (frames child)
 (declare (xargs :guard t :verify-guards nil :measure (len frames)))
 (if (not (consp frames)) child
  (let* ((frame (car frames)) (tag (fn-cp-nth 0 frame)))
   (fn-ccmm-stack-target
    (cdr frames)
    (case tag
     (:list (list (fn-cp-nth 1 frame) (fn-cp-nth 2 frame) child))
     (:trie-child (list (fn-cp-nth 1 frame) (fn-cp-nth 2 frame) child
                        (fn-ccmm-target :trie (fn-cp-nth 3 frame) (fn-cp-nth 4 frame))))
     (:trie-tail (list (fn-cp-nth 1 frame) (fn-cp-nth 2 frame)
                       (fn-cp-nth 3 frame) child))
     (otherwise nil))))))

(defun fn-ccmm-denotation (cursor)
 (declare (xargs :guard t :verify-guards nil))
 (fn-ccmm-stack-target
  (fn-cp-nth 4 cursor)
  (if (eq (fn-cp-nth 5 cursor) :visit)
      (fn-ccmm-target (fn-cp-nth 1 cursor) (fn-cp-nth 2 cursor) (fn-cp-nth 3 cursor))
    (fn-cp-nth 6 cursor))))

(defthm fn-ccmm-actual-tick-preserves-complete-annotation-target
 (implies (eq (fn-cp-nth 0 (fn-ccm-tick cursor)) :yield)
  (equal (fn-ccmm-denotation (fn-cp-nth 1 (fn-ccm-tick cursor)))
         (fn-ccmm-denotation cursor)))
 :rule-classes nil
 :hints (("Goal" :in-theory
  (e/d (fn-ccm-tick fn-ccm-cursor fn-ccmm-denotation fn-ccmm-stack-target
        fn-ccmm-target fn-cp-nth)
       (fn-ccm-pair-infop fn-ccm-info-tail)))))

(defthm fn-ccmm-actual-finish-is-complete-annotation-target
 (implies (eq (fn-cp-nth 0 (fn-ccm-tick cursor)) :ok)
  (equal (fn-cp-nth 1 (fn-ccm-tick cursor)) (fn-ccmm-denotation cursor)))
 :rule-classes nil
 :hints (("Goal" :in-theory
  (e/d (fn-ccm-tick fn-ccm-cursor fn-ccmm-denotation fn-ccmm-stack-target fn-cp-nth)
       (fn-ccmm-target fn-ccm-pair-infop fn-ccm-info-tail)))))

(defun fn-ccmm-task-targets (tasks)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp tasks)
     (cons (fn-ccmm-target (fn-cp-nth 0 (car tasks))
                           (fn-cp-nth 1 (car tasks)) (fn-cp-nth 2 (car tasks)))
           (fn-ccmm-task-targets (cdr tasks)))
   nil))

(defun fn-ccmm-context-results (context)
 (declare (xargs :guard t :verify-guards nil))
 (revappend (fn-ccmm-task-targets (fn-cp-nth 4 context))
            (if (fn-cp-nth 6 context)
                (cons (fn-ccmm-denotation (fn-cp-nth 6 context))
                      (fn-cp-nth 5 context))
              (fn-cp-nth 5 context))))

(defun fn-ccmm-context-denotation (context)
 (declare (xargs :guard t :verify-guards nil))
 (let ((results (fn-ccmm-context-results context))
       (pending (fn-cp-nth 2 context)))
  (list :account-carries (fn-cp-nth 1 context)
    (if pending (fn-cp-nth 5 results) (fn-cp-nth 1 results))
    (and pending (list :prep-carries (fn-cp-nth 3 results) (fn-cp-nth 2 results)
                                    (fn-cp-nth 1 results) (fn-cp-nth 0 results)
                                    (fn-cp-nth 3 context)))
    (if pending (fn-cp-nth 4 results) (fn-cp-nth 0 results)))))

(local (defthm fn-ccmm-yield-has-retained-cursor
 (implies (eq (fn-cp-nth 0 (fn-ccm-tick cursor)) :yield)
          (consp (fn-cp-nth 1 (fn-ccm-tick cursor))))
 :hints (("Goal" :in-theory (enable fn-ccm-tick fn-ccm-cursor fn-cp-nth)))))

(local (defthm fn-ccmm-begin-denotation
 (equal (fn-ccmm-denotation (fn-ccm-cursor kind value info nil :visit nil))
        (fn-ccmm-target kind value info))
 :hints (("Goal" :in-theory
   (e/d (fn-ccm-cursor fn-cp-nth fn-ccmm-denotation
         fn-ccmm-stack-target) (fn-ccmm-target))))))

(defthm fn-ccmm-actual-context-tick-preserves-complete-target
 (implies (eq (fn-cp-nth 0 (fn-ccm-context-tick context)) :yield)
   (equal (fn-ccmm-context-denotation
            (fn-cp-nth 1 (fn-ccm-context-tick context)))
          (fn-ccmm-context-denotation context)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-ccmm-yield-has-retained-cursor
                   (cursor (fn-cp-nth 6 context)))
        (:instance fn-ccmm-actual-tick-preserves-complete-annotation-target
                   (cursor (fn-cp-nth 6 context)))
        (:instance fn-ccmm-actual-finish-is-complete-annotation-target
                   (cursor (fn-cp-nth 6 context))))
  :in-theory (e/d (fn-ccm-context-tick fn-ccm-context fn-ccm-begin
                    fn-ccmm-context-denotation fn-ccmm-context-results
                    fn-ccmm-task-targets
                    fn-cp-nth revappend)
                   (fn-ccm-tick fn-ccmm-target fn-ccmm-denotation fn-ccmm-stack-target fn-ccm-cursor
                    revappend-removal)))))

(defthm fn-ccmm-actual-context-finish-is-complete-target
 (implies (eq (fn-cp-nth 0 (fn-ccm-context-tick context)) :ok)
  (equal (fn-cp-nth 1 (fn-ccm-context-tick context))
         (fn-ccmm-context-denotation context)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-ccm-context-tick fn-ccmm-context-denotation
                    fn-ccmm-context-results fn-ccmm-task-targets fn-cp-nth revappend)
                   (fn-ccm-tick fn-ccmm-target fn-ccmm-denotation fn-ccmm-stack-target fn-ccm-cursor
                    revappend-removal)))))

(in-theory (disable fn-ccmm-target fn-ccmm-stack-target fn-ccmm-denotation))
