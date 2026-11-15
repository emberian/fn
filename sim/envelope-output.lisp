; Peer delivery is observed independently of consumed application bytes.
; Exact successful segments use a linear path; ambiguous failure/cancellation
; prefixes use resumable polynomial row evaluation, never search backtracking.
(in-package "ACL2")
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
  (declare (xargs :stobjs fn2-envelope-output-state :guard t :verify-guards nil))
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
  (declare (xargs :stobjs fn2-envelope-output-state :guard t :verify-guards nil))
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
          (0 (if (consp segments)
                 (let* ((fn2-envelope-output-state (update-fn2-eo-segments (cdr segments)
                                                                           fn2-envelope-output-state))
                        (fn2-envelope-output-state (update-fn2-eo-ordered (cons (car segments)
                                                                                ordered)
                                                                          fn2-envelope-output-state)))
                   fn2-envelope-output-state)
               (let* ((fn2-envelope-output-state (update-fn2-eo-phase 1
                                                                      fn2-envelope-output-state))
                      (fn2-envelope-output-state (update-fn2-eo-segments ordered
                                                                         fn2-envelope-output-state)))
                 fn2-envelope-output-state)))
          (1 (cond ((atom segments)
                    (let* ((fn2-envelope-output-state (update-fn2-eo-phase 10
                                                                           fn2-envelope-output-state))
                           (fn2-envelope-output-state (update-fn2-eo-result (equal peer
                                                                                   nil)
                                                                            fn2-envelope-output-state)))
                      fn2-envelope-output-state))
                   ((eq (caar segments) :exact)
                    (cond ((atom (cdar segments))
                           (let* ((fn2-envelope-output-state (update-fn2-eo-segments (cdr segments)
                                                                                     fn2-envelope-output-state)))
                             fn2-envelope-output-state))
                          ((and (consp peer) (equal (car peer) (cadar segments)))
                           (let* ((fn2-envelope-output-state (update-fn2-eo-peer (cdr peer)
                                                                                 fn2-envelope-output-state))
                                  (fn2-envelope-output-state (update-fn2-eo-segments (cons (cons :exact (cddar segments))
                                                                                           (cdr segments))
                                                                                     fn2-envelope-output-state)))
                             fn2-envelope-output-state))
                          (t (let* ((fn2-envelope-output-state (update-fn2-eo-phase 10
                                                                                    fn2-envelope-output-state))
                                    (fn2-envelope-output-state (update-fn2-eo-result nil
                                                                                     fn2-envelope-output-state)))
                               fn2-envelope-output-state))))
                   ((eq (caar segments) :prefix)
                    (if (atom (cdr segments))
                        (let* ((fn2-envelope-output-state (update-fn2-eo-phase 2
                                                                               fn2-envelope-output-state))
                               (fn2-envelope-output-state (update-fn2-eo-bytes (cdar segments)
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
                   ((and (consp bytes) (equal (car peer) (car bytes)))
                    (let* ((fn2-envelope-output-state (update-fn2-eo-peer (cdr peer)
                                                                          fn2-envelope-output-state))
                           (fn2-envelope-output-state (update-fn2-eo-bytes (cdr bytes)
                                                                           fn2-envelope-output-state)))
                      fn2-envelope-output-state))
                   (t (let* ((fn2-envelope-output-state (update-fn2-eo-phase 10
                                                                             fn2-envelope-output-state))
                             (fn2-envelope-output-state (update-fn2-eo-result nil
                                                                              fn2-envelope-output-state)))
                        fn2-envelope-output-state))))
          (3 (if (consp segments)
                 (let* ((fn2-envelope-output-state (update-fn2-eo-segments (cdr segments)
                                                                           fn2-envelope-output-state))
                        (fn2-envelope-output-state (update-fn2-eo-ordered (cons (car segments)
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
                 (let* ((fn2-envelope-output-state (update-fn2-eo-scan (cdr scan)
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
                           (fn2-envelope-output-state (update-fn2-eo-result (and (car row)
                                                                                 t)
                                                                            fn2-envelope-output-state)))
                      fn2-envelope-output-state))
                   ((member-eq (caar segments) '(:exact :prefix))
                    (let* ((fn2-envelope-output-state (update-fn2-eo-phase 6
                                                                           fn2-envelope-output-state))
                           (fn2-envelope-output-state (update-fn2-eo-segments (cdr segments)
                                                                              fn2-envelope-output-state))
                           (fn2-envelope-output-state (update-fn2-eo-bytes (cdar segments)
                                                                           fn2-envelope-output-state))
                           (fn2-envelope-output-state (update-fn2-eo-reversed nil
                                                                              fn2-envelope-output-state))
                           (fn2-envelope-output-state (update-fn2-eo-suffix row
                                                                            fn2-envelope-output-state))
                           (fn2-envelope-output-state (update-fn2-eo-prefix (eq (caar segments)
                                                                                :prefix)
                                                                            fn2-envelope-output-state)))
                      fn2-envelope-output-state))
                   (t (let* ((fn2-envelope-output-state (update-fn2-eo-phase 10
                                                                             fn2-envelope-output-state))
                             (fn2-envelope-output-state (update-fn2-eo-result nil
                                                                              fn2-envelope-output-state)))
                        fn2-envelope-output-state))))
          (6 (if (consp bytes)
                 (let* ((fn2-envelope-output-state (update-fn2-eo-bytes (cdr bytes)
                                                                        fn2-envelope-output-state))
                        (fn2-envelope-output-state (update-fn2-eo-reversed (cons (car bytes)
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
                      (fn2-envelope-output-state (update-fn2-eo-byte (car bytes)
                                                                     fn2-envelope-output-state))
                      (fn2-envelope-output-state (update-fn2-eo-bytes (cdr bytes)
                                                                      fn2-envelope-output-state))
                      (fn2-envelope-output-state (update-fn2-eo-scan peer
                                                                     fn2-envelope-output-state))
                      (fn2-envelope-output-state (update-fn2-eo-shifted (cdr row)
                                                                        fn2-envelope-output-state))
                      (fn2-envelope-output-state (update-fn2-eo-suffix-scan suffix
                                                                            fn2-envelope-output-state))
                      (fn2-envelope-output-state (update-fn2-eo-acc nil
                                                                    fn2-envelope-output-state)))
                 fn2-envelope-output-state)))
          (8 (if (consp scan)
                 (let* ((fn2-envelope-output-state (update-fn2-eo-scan (cdr scan)
                                                                       fn2-envelope-output-state))
                        (fn2-envelope-output-state (update-fn2-eo-shifted (cdr shifted)
                                                                          fn2-envelope-output-state))
                        (fn2-envelope-output-state (update-fn2-eo-suffix-scan (cdr suffix-scan)
                                                                              fn2-envelope-output-state))
                        (fn2-envelope-output-state (update-fn2-eo-acc (cons (or (and prefix
                                                                                     (car suffix-scan))
                                                                                (and (equal (car scan)
                                                                                            byte)
                                                                                     (car shifted)))
                                                                            acc)
                                                                      fn2-envelope-output-state)))
                   fn2-envelope-output-state)
               (let* ((fn2-envelope-output-state (update-fn2-eo-phase 9
                                                                      fn2-envelope-output-state))
                      (fn2-envelope-output-state (update-fn2-eo-acc (cons (and prefix
                                                                               (car suffix-scan))
                                                                          acc)
                                                                    fn2-envelope-output-state))
                      (fn2-envelope-output-state (update-fn2-eo-reversed nil
                                                                         fn2-envelope-output-state)))
                 fn2-envelope-output-state)))
          (9 (if (consp acc)
                 (let* ((fn2-envelope-output-state (update-fn2-eo-acc (cdr acc)
                                                                      fn2-envelope-output-state))
                        (fn2-envelope-output-state (update-fn2-eo-reversed (cons (car acc)
                                                                                 reversed)
                                                                           fn2-envelope-output-state)))
                   fn2-envelope-output-state)
               (let* ((fn2-envelope-output-state (update-fn2-eo-phase 7
                                                                      fn2-envelope-output-state))
                      (fn2-envelope-output-state (update-fn2-eo-row reversed
                                                                    fn2-envelope-output-state)))
                 fn2-envelope-output-state)))
          (otherwise fn2-envelope-output-state))))
(defun fn2-envelope-output-run (fuel fn2-envelope-output-state)
  (declare (xargs :stobjs fn2-envelope-output-state
                  :guard (natp fuel)
                  :verify-guards nil))
  (if (or (zp fuel) (equal (fn2-eo-phase fn2-envelope-output-state) 10))
      fn2-envelope-output-state
    (let ((fn2-envelope-output-state (fn2-envelope-output-step fn2-envelope-output-state)))
      (fn2-envelope-output-run (1- fuel) fn2-envelope-output-state))))
; One linear size pass supplies a conservative drain budget; no data ceiling.
(defun fn2-envelope-output-source-size (segments)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom segments)
      0
    (+ (len (cdar segments)) (fn2-envelope-output-source-size (cdr segments)))))
(defun fn2-envelope-output-budget (segments peer)
  (declare (xargs :guard t :verify-guards nil))
  (+ 32
     (* 8 (len segments))
     (* 4 (len peer))
     (* (+ 12 (* 2 (len peer))) (fn2-envelope-output-source-size segments))))
(defun fn2-envelope-output-matches-p (segments-reversed peer)
  (declare (xargs :guard t :verify-guards nil))
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
