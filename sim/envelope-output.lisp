; Peer delivery is observed independently of consumed application bytes.
; Exact successful segments use a linear path; ambiguous failure/cancellation
; prefixes use resumable polynomial row evaluation, never search backtracking.
(in-package "ACL2")
(defun fn2-eo-first (x) (declare (xargs :guard t)) (if (consp x) (car x) nil))
(defun fn2-eo-rest (x) (declare (xargs :guard t)) (if (consp x) (cdr x) nil))
(defthm fn2-eo-first-by-definition (equal (fn2-eo-first x) (car x)))
(defthm fn2-eo-rest-by-definition (equal (fn2-eo-rest x) (cdr x)))
(defstobj fn2-envelope-output-state
          (fn2-eo-phase :initially 0)
          (fn2-eo-segments :initially nil)
          (fn2-eo-ordered :initially nil)
          (fn2-eo-peer :initially nil)
          (fn2-eo-scan :initially nil)
          (fn2-eo-row :initially nil)
          (fn2-eo-suffix :initially nil)
          (fn2-eo-shifted :initially nil)
          (fn2-eo-suffix-scan :initially nil)
          (fn2-eo-bytes :initially nil)
          (fn2-eo-reversed :initially nil)
          (fn2-eo-acc :initially nil)
          (fn2-eo-byte :initially nil)
          (fn2-eo-prefix :initially nil)
          (fn2-eo-result :initially nil))

(defun fn2-envelope-output-init (segments-reversed peer fn2-envelope-output-state)
  (declare (xargs :stobjs fn2-envelope-output-state :guard t ))
  (let* ((fn2-envelope-output-state (update-fn2-eo-phase 0
                                                         fn2-envelope-output-state))
         (fn2-envelope-output-state (update-fn2-eo-segments segments-reversed
                                                            fn2-envelope-output-state))
         (fn2-envelope-output-state (update-fn2-eo-ordered nil
                                                           fn2-envelope-output-state))
         (fn2-envelope-output-state (update-fn2-eo-peer peer
                                                        fn2-envelope-output-state))
         (fn2-envelope-output-state (update-fn2-eo-result nil
                                                          fn2-envelope-output-state)))
    fn2-envelope-output-state))
(defun fn2-envelope-output-step (fn2-envelope-output-state)
  (declare (xargs :stobjs fn2-envelope-output-state :guard t ))
  (let* ((phase (fn2-eo-phase fn2-envelope-output-state))
         (segments (fn2-eo-segments fn2-envelope-output-state))
         (ordered (fn2-eo-ordered fn2-envelope-output-state))
         (peer (fn2-eo-peer fn2-envelope-output-state))
         (scan (fn2-eo-scan fn2-envelope-output-state))
         (row (fn2-eo-row fn2-envelope-output-state))
         (suffix (fn2-eo-suffix fn2-envelope-output-state))
         (shifted (fn2-eo-shifted fn2-envelope-output-state))
         (suffix-scan (fn2-eo-suffix-scan fn2-envelope-output-state))
         (bytes (fn2-eo-bytes fn2-envelope-output-state))
         (reversed (fn2-eo-reversed fn2-envelope-output-state))
         (acc (fn2-eo-acc fn2-envelope-output-state))
         (byte (fn2-eo-byte fn2-envelope-output-state))
         (prefix (fn2-eo-prefix fn2-envelope-output-state)))
    (case phase
          (0 (cond
 ((consp segments)
  (if (and (consp (fn2-eo-first segments)) (member-eq (fn2-eo-first (fn2-eo-first segments)) '(:exact :prefix)))
      (let* ((fn2-envelope-output-state (update-fn2-eo-phase 11 fn2-envelope-output-state)) (fn2-envelope-output-state (update-fn2-eo-segments (fn2-eo-rest segments) fn2-envelope-output-state)) (fn2-envelope-output-state (update-fn2-eo-ordered (cons (fn2-eo-first segments) ordered) fn2-envelope-output-state)) (fn2-envelope-output-state (update-fn2-eo-bytes (fn2-eo-rest (fn2-eo-first segments)) fn2-envelope-output-state))) fn2-envelope-output-state)
    (let* ((fn2-envelope-output-state (update-fn2-eo-phase 10 fn2-envelope-output-state)) (fn2-envelope-output-state (update-fn2-eo-result nil fn2-envelope-output-state))) fn2-envelope-output-state)))
 ((equal segments nil) (let* ((fn2-envelope-output-state (update-fn2-eo-phase 12 fn2-envelope-output-state)) (fn2-envelope-output-state (update-fn2-eo-segments ordered fn2-envelope-output-state)) (fn2-envelope-output-state (update-fn2-eo-scan peer fn2-envelope-output-state))) fn2-envelope-output-state))
 (t (let* ((fn2-envelope-output-state (update-fn2-eo-phase 10 fn2-envelope-output-state)) (fn2-envelope-output-state (update-fn2-eo-result nil fn2-envelope-output-state))) fn2-envelope-output-state))))
          (1 (cond ((atom segments)
                    (let* ((fn2-envelope-output-state (update-fn2-eo-phase 10
                                                                           fn2-envelope-output-state))
                           (fn2-envelope-output-state (update-fn2-eo-result (equal peer
                                                                                   nil)
                                                                            fn2-envelope-output-state)))
                      fn2-envelope-output-state))
                   ((eq (fn2-eo-first (fn2-eo-first segments)) :exact)
                    (cond ((atom (fn2-eo-rest (fn2-eo-first segments)))
                           (let* ((fn2-envelope-output-state (update-fn2-eo-segments (fn2-eo-rest segments)
                                                                                     fn2-envelope-output-state)))
                             fn2-envelope-output-state))
                          ((and (consp peer) (equal (fn2-eo-first peer) (fn2-eo-first (fn2-eo-rest (fn2-eo-first segments)))))
                           (let* ((fn2-envelope-output-state (update-fn2-eo-peer (fn2-eo-rest peer)
                                                                                 fn2-envelope-output-state))
                                  (fn2-envelope-output-state (update-fn2-eo-segments (cons (cons :exact (fn2-eo-rest (fn2-eo-rest (fn2-eo-first segments))))
                                                                                           (fn2-eo-rest segments))
                                                                                     fn2-envelope-output-state)))
                             fn2-envelope-output-state))
                          (t (let* ((fn2-envelope-output-state (update-fn2-eo-phase 10
                                                                                    fn2-envelope-output-state))
                                    (fn2-envelope-output-state (update-fn2-eo-result nil
                                                                                     fn2-envelope-output-state)))
                               fn2-envelope-output-state))))
                   ((eq (fn2-eo-first (fn2-eo-first segments)) :prefix)
                    (if (atom (fn2-eo-rest segments))
                        (let* ((fn2-envelope-output-state (update-fn2-eo-phase 2
                                                                               fn2-envelope-output-state))
                               (fn2-envelope-output-state (update-fn2-eo-bytes (fn2-eo-rest (fn2-eo-first segments))
                                                                               fn2-envelope-output-state)))
                          fn2-envelope-output-state)
                      (let* ((fn2-envelope-output-state (update-fn2-eo-phase 3
                                                                             fn2-envelope-output-state))
                             (fn2-envelope-output-state (update-fn2-eo-ordered nil
                                                                               fn2-envelope-output-state)))
                        fn2-envelope-output-state)))
                   (t (let* ((fn2-envelope-output-state (update-fn2-eo-phase 10
                                                                             fn2-envelope-output-state))
                             (fn2-envelope-output-state (update-fn2-eo-result nil
                                                                              fn2-envelope-output-state)))
                        fn2-envelope-output-state))))
          (2 (cond ((atom peer)
                    (let* ((fn2-envelope-output-state (update-fn2-eo-phase 10
                                                                           fn2-envelope-output-state))
                           (fn2-envelope-output-state (update-fn2-eo-result (equal peer
                                                                                   nil)
                                                                            fn2-envelope-output-state)))
                      fn2-envelope-output-state))
                   ((and (consp bytes) (equal (fn2-eo-first peer) (fn2-eo-first bytes)))
                    (let* ((fn2-envelope-output-state (update-fn2-eo-peer (fn2-eo-rest peer)
                                                                          fn2-envelope-output-state))
                           (fn2-envelope-output-state (update-fn2-eo-bytes (fn2-eo-rest bytes)
                                                                           fn2-envelope-output-state)))
                      fn2-envelope-output-state))
                   (t (let* ((fn2-envelope-output-state (update-fn2-eo-phase 10
                                                                             fn2-envelope-output-state))
                             (fn2-envelope-output-state (update-fn2-eo-result nil
                                                                              fn2-envelope-output-state)))
                        fn2-envelope-output-state))))
          (3 (if (consp segments)
                 (let* ((fn2-envelope-output-state (update-fn2-eo-segments (fn2-eo-rest segments)
                                                                           fn2-envelope-output-state))
                        (fn2-envelope-output-state (update-fn2-eo-ordered (cons (fn2-eo-first segments)
                                                                                ordered)
                                                                          fn2-envelope-output-state)))
                   fn2-envelope-output-state)
               (let* ((fn2-envelope-output-state (update-fn2-eo-phase 4
                                                                      fn2-envelope-output-state))
                      (fn2-envelope-output-state (update-fn2-eo-segments ordered
                                                                         fn2-envelope-output-state))
                      (fn2-envelope-output-state (update-fn2-eo-scan peer
                                                                     fn2-envelope-output-state))
                      (fn2-envelope-output-state (update-fn2-eo-row '(t)
                                                                    fn2-envelope-output-state)))
                 fn2-envelope-output-state)))
          (4 (if (consp scan)
                 (let* ((fn2-envelope-output-state (update-fn2-eo-scan (fn2-eo-rest scan)
                                                                       fn2-envelope-output-state))
                        (fn2-envelope-output-state (update-fn2-eo-row (cons nil row)
                                                                      fn2-envelope-output-state)))
                   fn2-envelope-output-state)
               (let* ((fn2-envelope-output-state (update-fn2-eo-phase 5
                                                                      fn2-envelope-output-state)))
                 fn2-envelope-output-state)))
          (5 (cond ((atom segments)
                    (let* ((fn2-envelope-output-state (update-fn2-eo-phase 10
                                                                           fn2-envelope-output-state))
                           (fn2-envelope-output-state (update-fn2-eo-result (and (fn2-eo-first row)
                                                                                 t)
                                                                            fn2-envelope-output-state)))
                      fn2-envelope-output-state))
                   ((member-eq (fn2-eo-first (fn2-eo-first segments)) '(:exact :prefix))
                    (let* ((fn2-envelope-output-state (update-fn2-eo-phase 6
                                                                           fn2-envelope-output-state))
                           (fn2-envelope-output-state (update-fn2-eo-segments (fn2-eo-rest segments)
                                                                              fn2-envelope-output-state))
                           (fn2-envelope-output-state (update-fn2-eo-bytes (fn2-eo-rest (fn2-eo-first segments))
                                                                           fn2-envelope-output-state))
                           (fn2-envelope-output-state (update-fn2-eo-reversed nil
                                                                              fn2-envelope-output-state))
                           (fn2-envelope-output-state (update-fn2-eo-suffix row
                                                                            fn2-envelope-output-state))
                           (fn2-envelope-output-state (update-fn2-eo-prefix (eq (fn2-eo-first (fn2-eo-first segments))
                                                                                :prefix)
                                                                            fn2-envelope-output-state)))
                      fn2-envelope-output-state))
                   (t (let* ((fn2-envelope-output-state (update-fn2-eo-phase 10
                                                                             fn2-envelope-output-state))
                             (fn2-envelope-output-state (update-fn2-eo-result nil
                                                                              fn2-envelope-output-state)))
                        fn2-envelope-output-state))))
          (6 (if (consp bytes)
                 (let* ((fn2-envelope-output-state (update-fn2-eo-bytes (fn2-eo-rest bytes)
                                                                        fn2-envelope-output-state))
                        (fn2-envelope-output-state (update-fn2-eo-reversed (cons (fn2-eo-first bytes)
                                                                                 reversed)
                                                                           fn2-envelope-output-state)))
                   fn2-envelope-output-state)
               (let* ((fn2-envelope-output-state (update-fn2-eo-phase 7
                                                                      fn2-envelope-output-state))
                      (fn2-envelope-output-state (update-fn2-eo-bytes reversed
                                                                      fn2-envelope-output-state)))
                 fn2-envelope-output-state)))
          (7 (if (atom bytes)
                 (let* ((fn2-envelope-output-state (update-fn2-eo-phase 5
                                                                        fn2-envelope-output-state)))
                   fn2-envelope-output-state)
               (let* ((fn2-envelope-output-state (update-fn2-eo-phase 8
                                                                      fn2-envelope-output-state))
                      (fn2-envelope-output-state (update-fn2-eo-byte (fn2-eo-first bytes)
                                                                     fn2-envelope-output-state))
                      (fn2-envelope-output-state (update-fn2-eo-bytes (fn2-eo-rest bytes)
                                                                      fn2-envelope-output-state))
                      (fn2-envelope-output-state (update-fn2-eo-scan peer
                                                                     fn2-envelope-output-state))
                      (fn2-envelope-output-state (update-fn2-eo-shifted (fn2-eo-rest row)
                                                                        fn2-envelope-output-state))
                      (fn2-envelope-output-state (update-fn2-eo-suffix-scan suffix
                                                                            fn2-envelope-output-state))
                      (fn2-envelope-output-state (update-fn2-eo-acc nil
                                                                    fn2-envelope-output-state)))
                 fn2-envelope-output-state)))
          (8 (if (consp scan)
                 (let* ((fn2-envelope-output-state (update-fn2-eo-scan (fn2-eo-rest scan)
                                                                       fn2-envelope-output-state))
                        (fn2-envelope-output-state (update-fn2-eo-shifted (fn2-eo-rest shifted)
                                                                          fn2-envelope-output-state))
                        (fn2-envelope-output-state (update-fn2-eo-suffix-scan (fn2-eo-rest suffix-scan)
                                                                              fn2-envelope-output-state))
                        (fn2-envelope-output-state (update-fn2-eo-acc (cons (or (and prefix
                                                                                     (fn2-eo-first suffix-scan))
                                                                                (and (equal (fn2-eo-first scan)
                                                                                            byte)
                                                                                     (fn2-eo-first shifted)))
                                                                            acc)
                                                                      fn2-envelope-output-state)))
                   fn2-envelope-output-state)
               (let* ((fn2-envelope-output-state (update-fn2-eo-phase 9
                                                                      fn2-envelope-output-state))
                      (fn2-envelope-output-state (update-fn2-eo-acc (cons (and prefix
                                                                               (fn2-eo-first suffix-scan))
                                                                          acc)
                                                                    fn2-envelope-output-state))
                      (fn2-envelope-output-state (update-fn2-eo-reversed nil
                                                                         fn2-envelope-output-state)))
                 fn2-envelope-output-state)))
          (9 (if (consp acc)
                 (let* ((fn2-envelope-output-state (update-fn2-eo-acc (fn2-eo-rest acc)
                                                                      fn2-envelope-output-state))
                        (fn2-envelope-output-state (update-fn2-eo-reversed (cons (fn2-eo-first acc)
                                                                                 reversed)
                                                                           fn2-envelope-output-state)))
                   fn2-envelope-output-state)
               (let* ((fn2-envelope-output-state (update-fn2-eo-phase 7
                                                                      fn2-envelope-output-state))
                      (fn2-envelope-output-state (update-fn2-eo-row reversed
                                                                    fn2-envelope-output-state)))
                 fn2-envelope-output-state)))
          (11 (cond ((consp bytes)
 (if (unsigned-byte-p 8 (fn2-eo-first bytes)) (let* ((fn2-envelope-output-state (update-fn2-eo-bytes (fn2-eo-rest bytes) fn2-envelope-output-state))) fn2-envelope-output-state) (let* ((fn2-envelope-output-state (update-fn2-eo-phase 10 fn2-envelope-output-state)) (fn2-envelope-output-state (update-fn2-eo-result nil fn2-envelope-output-state))) fn2-envelope-output-state)))
 ((equal bytes nil) (let* ((fn2-envelope-output-state (update-fn2-eo-phase 0 fn2-envelope-output-state))) fn2-envelope-output-state)) (t (let* ((fn2-envelope-output-state (update-fn2-eo-phase 10 fn2-envelope-output-state)) (fn2-envelope-output-state (update-fn2-eo-result nil fn2-envelope-output-state))) fn2-envelope-output-state))))
(12 (cond ((consp scan)
 (if (unsigned-byte-p 8 (fn2-eo-first scan)) (let* ((fn2-envelope-output-state (update-fn2-eo-scan (fn2-eo-rest scan) fn2-envelope-output-state))) fn2-envelope-output-state) (let* ((fn2-envelope-output-state (update-fn2-eo-phase 10 fn2-envelope-output-state)) (fn2-envelope-output-state (update-fn2-eo-result nil fn2-envelope-output-state))) fn2-envelope-output-state)))
 ((equal scan nil) (let* ((fn2-envelope-output-state (update-fn2-eo-phase 1 fn2-envelope-output-state))) fn2-envelope-output-state)) (t (let* ((fn2-envelope-output-state (update-fn2-eo-phase 10 fn2-envelope-output-state)) (fn2-envelope-output-state (update-fn2-eo-result nil fn2-envelope-output-state))) fn2-envelope-output-state))))
(otherwise fn2-envelope-output-state))))
(defun fn2-envelope-output-run (fuel fn2-envelope-output-state)
  (declare (xargs :stobjs fn2-envelope-output-state
                  :guard (natp fuel)
                  ))
  (if (or (zp fuel) (equal (fn2-eo-phase fn2-envelope-output-state) 10))
      fn2-envelope-output-state
    (let ((fn2-envelope-output-state (fn2-envelope-output-step fn2-envelope-output-state)))
      (fn2-envelope-output-run (1- fuel) fn2-envelope-output-state))))
; One linear size pass supplies a conservative drain budget; no data ceiling.
(defun fn2-envelope-output-source-size (segments)
  (declare (xargs :guard t ))
  (if (atom segments)
      0
    (+ (if (consp (car segments)) (len (cdar segments)) 0)
       (fn2-envelope-output-source-size (cdr segments)))))
(defun fn2-envelope-output-budget (segments peer)
  (declare (xargs :guard t ))
  (+ 32
     (* 8 (len segments))
     (* 6 (len peer))
     (* (+ 20 (* 2 (len peer))) (fn2-envelope-output-source-size segments))))
(defun fn2-envelope-output-matches-p (segments-reversed peer)
  (declare (xargs :guard t ))
  (with-local-stobj fn2-envelope-output-state
                    (mv-let (matched fn2-envelope-output-state) (let* ((fn2-envelope-output-state (fn2-envelope-output-init segments-reversed
                                                                                                                            peer
                                                                                                                            fn2-envelope-output-state))
                                                                       (fn2-envelope-output-state (fn2-envelope-output-run (fn2-envelope-output-budget segments-reversed
                                                                                                                                                       peer)
                                                                                                                           fn2-envelope-output-state)))
                                                                  (mv (and (equal (fn2-eo-phase fn2-envelope-output-state)
                                                                                  10)
                                                                           (fn2-eo-result fn2-envelope-output-state))
                                                                      fn2-envelope-output-state))
                      matched)))

; Independent nondeterministic prefix-language specification. This definition
; is for statements/controls only; the runtime checker uses the row machine.
(defun fn2-envelope-output-language-p (segments peer)
 (declare (xargs :measure (acl2-count segments) :verify-guards nil))
 (cond ((atom segments) (and (equal segments nil) (equal peer nil)))
       ((not (consp (car segments))) nil)
       ((eq (caar segments) :exact)
        (if (atom (cdar segments))
            (and (equal (cdar segments) nil) (fn2-envelope-output-language-p (cdr segments) peer))
          (and (consp peer) (equal (cadar segments) (car peer))
               (fn2-envelope-output-language-p
                (cons (cons :exact (cddar segments)) (cdr segments)) (cdr peer)))))
       ((eq (caar segments) :prefix)
        (or (fn2-envelope-output-language-p (cdr segments) peer)
            (and (consp (cdar segments)) (consp peer) (equal (cadar segments) (car peer))
                 (fn2-envelope-output-language-p
                  (cons (cons :prefix (cddar segments)) (cdr segments)) (cdr peer)))))
       (t nil)))

(defthm fn2-envelope-output-run-resume
 (implies (and (natp a) (natp b))
  (equal (fn2-envelope-output-run (+ a b) fn2-envelope-output-state)
         (fn2-envelope-output-run b
          (fn2-envelope-output-run a fn2-envelope-output-state))))
 :rule-classes nil
 :hints (("Goal" :induct (fn2-envelope-output-run a fn2-envelope-output-state)
 :in-theory (disable fn2-envelope-output-step fn2-eo-phase))))
