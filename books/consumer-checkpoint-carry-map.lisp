; Bounded mapping of SAME-PARSE generic infos to consumer annotations.
; Each tick visits one list/trie cell or returns one completed child. No size
; summary, credential reconstruction, authority validation or serving readiness
; is inferred here. The decoder's attributed info/value relation is required.
(in-package "ACL2")
(include-book "consumer-progress-carried")

; Generic parser info ABI: (rootcarry car-info . cdr-info), or (rootcarry)
; for a scalar/collapsed octet leaf. A missing pair is never expanded into
; invented per-child annotations.
(defun fn-ccm-info-tail (info)
 (declare (xargs :guard t))
 (ec-call (nthcdr 2 info)))

(defun fn-ccm-info-field (n info)
 (declare (xargs :guard (natp n) :measure (nfix n)))
 (if (and (fn-scs-carryp (fn-cp-nth 0 info))
          (consp (ec-call (cdr info))))
     (if (zp n) (fn-cp-nth 1 info)
       (fn-ccm-info-field (1- n) (fn-ccm-info-tail info)))
   nil))

(defun fn-ccm-pair-infop (info)
 (declare (xargs :guard t))
 (and (consp (ec-call (cdr info)))
      (fn-scs-carryp (fn-cp-nth 0 info))
      (fn-scs-carryp (fn-cp-nth 0 (fn-cp-nth 1 info)))
      (fn-scs-carryp (fn-cp-nth 0 (fn-ccm-info-tail info)))))

; Fixed7 cursor: tag, kind, remaining value, same-parse info, frames, phase,
; completed child. Frames borrow only selected carries/unvisited aliases.
(defun fn-ccm-cursor (kind value info frames phase child)
 (declare (xargs :guard t))
 (list :consumer-checkpoint-carry kind value info frames phase child))

(defun fn-ccm-begin (kind value info)
 (declare (xargs :guard t))
 (if (member-eq kind '(:list :trie))
     (list :yield (fn-ccm-cursor kind value info nil :visit nil))
   '(:refused :checkpoint-carry-kind)))

; LIST result is the existing list3 annotation; TRIE result is the existing
; trie4 annotation. Traversal uses a retained stack; no recursive graph walk
; or unbounded reversal occurs inside a scheduling tick.
(defun fn-ccm-tick (cursor)
 (declare (xargs :guard t))
 (let* ((kind (fn-cp-nth 1 cursor)) (value (fn-cp-nth 2 cursor))
        (info (fn-cp-nth 3 cursor)) (frames (fn-cp-nth 4 cursor))
        (phase (fn-cp-nth 5 cursor)) (child (fn-cp-nth 6 cursor)))
  (cond
   ((eq phase :visit)
    (cond
     ((not (consp value))
      (if (and (null value) (fn-scs-carryp (fn-cp-nth 0 info)))
          (list :yield (fn-ccm-cursor kind nil nil frames :return nil))
        '(:refused :checkpoint-carry-leaf)))
     ((not (fn-ccm-pair-infop info)) '(:refused :checkpoint-carry-pair))
     ((eq kind :list)
      (list :yield
       (fn-ccm-cursor :list (cdr value) (fn-ccm-info-tail info)
        (cons (list :list (fn-cp-nth 0 info)
                         (fn-cp-nth 0 (fn-cp-nth 1 info))) frames) :visit nil)))
     ((eq kind :trie)
      (let* ((entry (car value)) (entry-info (fn-cp-nth 1 info))
             (tail (cdr value)) (tail-info (fn-ccm-info-tail info)))
       (if (or (not (consp entry)) (not (fn-ccm-pair-infop entry-info)))
           '(:refused :checkpoint-carry-entry)
         (let ((rootcarry (fn-cp-nth 0 info))
               (valuecarry (fn-cp-nth 0 (fn-ccm-info-tail entry-info))))
          (if (characterp (car entry))
              (list :yield
               (fn-ccm-cursor :trie (cdr entry) (fn-ccm-info-tail entry-info)
                (cons (list :trie-child rootcarry valuecarry tail tail-info) frames)
                :visit nil))
            (list :yield
             (fn-ccm-cursor :trie tail tail-info
              (cons (list :trie-tail rootcarry valuecarry nil) frames) :visit nil)))))))
     (t '(:refused :checkpoint-carry-kind))))
   ((eq phase :return)
    (if (not (consp frames)) (list :ok child)
      (let* ((frame (car frames)) (outer (cdr frames)) (tag (fn-cp-nth 0 frame)))
       (cond
        ((eq tag :list)
         (list :yield
          (fn-ccm-cursor :list nil nil outer :return
           (list (fn-cp-nth 1 frame) (fn-cp-nth 2 frame) child))))
        ((eq tag :trie-child)
         (list :yield
          (fn-ccm-cursor :trie (fn-cp-nth 3 frame) (fn-cp-nth 4 frame)
           (cons (list :trie-tail (fn-cp-nth 1 frame) (fn-cp-nth 2 frame) child) outer)
           :visit nil)))
        ((eq tag :trie-tail)
         (list :yield
          (fn-ccm-cursor :trie nil nil outer :return
           (list (fn-cp-nth 1 frame) (fn-cp-nth 2 frame) (fn-cp-nth 3 frame) child))))
        (t '(:refused :checkpoint-carry-frame))))))
   (t '(:refused :checkpoint-carry-phase)))))

; Fixed7 consumer-context cursor: tag, seven carries, pending flag, credential
; root carry, at most six fixed tasks, completed task results, current job.
; Task and result spines are bounded by the FORMAT, not account/entry count.
(defun fn-ccm-context (fields pending credentialcarry tasks results job)
 (declare (xargs :guard t))
 (list :consumer-checkpoint-context fields pending credentialcarry tasks results job))

; CP and CPINFO are selected from the SAME consumer-wrapper parse. Root and
; fence-count remain separately retained by its publication collector. This
; constructor establishes no semantic/account/index or parser attribution.
(defun fn-ccm-context-begin (cp cpinfo)
 (declare (xargs :guard t))
 (if (null cp) '(:ok nil)
  (if (or (not (eq (fn-cp-nth 0 cp) :consumer-state))
          (not (consp (ec-call (nthcdr 6 cp))))
          (ec-call (nthcdr 7 cp)))
      '(:refused :checkpoint-consumer-schema)
    (let* ((ai (fn-ccm-info-field 6 cpinfo)) (a (fn-cp-nth 6 cp))
           (p (fn-cp-nth 5 a)) (pending-info (fn-ccm-info-field 5 ai))
           (prep (fn-cp-nth 5 p)) (prepi (fn-ccm-info-field 5 pending-info))
           (root (fn-cp-nth 5 prep)) (ri (fn-ccm-info-field 5 prepi))
           (fields (list (fn-cp-nth 0 (fn-ccm-info-field 0 cpinfo))
                         (fn-cp-nth 0 (fn-ccm-info-field 1 cpinfo))
                         (fn-cp-nth 0 (fn-ccm-info-field 2 cpinfo))
                         (fn-cp-nth 0 (fn-ccm-info-field 3 cpinfo))
                         (fn-cp-nth 0 (fn-ccm-info-field 4 cpinfo))
                         (fn-cp-nth 0 (fn-ccm-info-field 5 cpinfo))
                         (fn-cp-nth 0 ai)))
           (accounts (list :list (fn-cp-nth 4 a) (fn-ccm-info-field 4 ai)))
           (entries (list :list (fn-cp-nth 5 cp) (fn-ccm-info-field 5 cpinfo)))
           (credentialcarry (and p (fn-cp-nth 0 (fn-ccm-info-field 3 ri))))
           (tasks (if p
                    (list accounts entries
                     (list :list (fn-cp-nth 2 prep) (fn-ccm-info-field 2 prepi))
                     (list :list (fn-cp-nth 3 prep) (fn-ccm-info-field 3 prepi))
                     (list :list (fn-cp-nth 4 prep) (fn-ccm-info-field 4 prepi))
                     (list :trie (fn-cp-nth 2 root) (fn-ccm-info-field 2 ri)))
                   (list accounts entries))))
      (if (or (not (fn-scs-carry-listp fields))
              (and p (not (fn-scs-carryp credentialcarry))))
          '(:refused :checkpoint-consumer-infos)
        (list :yield (fn-ccm-context fields p credentialcarry tasks nil nil)))))))

(defun fn-ccm-context-tick (context)
 (declare (xargs :guard t))
 (let* ((fields (fn-cp-nth 1 context)) (pending (fn-cp-nth 2 context))
        (credentialcarry (fn-cp-nth 3 context)) (tasks (fn-cp-nth 4 context))
        (results (fn-cp-nth 5 context)) (job (fn-cp-nth 6 context)))
  (cond
   (job
    (let ((one (fn-ccm-tick job)))
     (case (fn-cp-nth 0 one)
      (:yield (list :yield (fn-ccm-context fields pending credentialcarry tasks results
                                           (fn-cp-nth 1 one))))
      (:ok (list :yield (fn-ccm-context fields pending credentialcarry tasks
                                        (cons (fn-cp-nth 1 one) results) nil)))
      (otherwise one))))
   ((consp tasks)
    (let* ((task (car tasks))
           (one (fn-ccm-begin (fn-cp-nth 0 task) (fn-cp-nth 1 task) (fn-cp-nth 2 task))))
     (if (eq (fn-cp-nth 0 one) :yield)
         (list :yield (fn-ccm-context fields pending credentialcarry (cdr tasks) results
                                     (fn-cp-nth 1 one)))
       one)))
   (t
    (list :ok
     (list :account-carries fields
      (if pending (fn-cp-nth 5 results) (fn-cp-nth 1 results))
      (and pending (list :prep-carries (fn-cp-nth 3 results) (fn-cp-nth 2 results)
                                      (fn-cp-nth 1 results) (fn-cp-nth 0 results)
                                      credentialcarry))
      (if pending (fn-cp-nth 4 results) (fn-cp-nth 0 results))))))))

(in-theory (disable fn-ccm-info-tail fn-ccm-info-field fn-ccm-pair-infop
                    fn-ccm-cursor fn-ccm-begin fn-ccm-tick
                    fn-ccm-context fn-ccm-context-begin fn-ccm-context-tick))
