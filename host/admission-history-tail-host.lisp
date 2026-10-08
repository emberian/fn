; Actual current append-leaf selection before durability. No supplied leaf,
; source, reservation, count or constructor authority enters this callback.
(in-package "ACL2")
(include-book "admission-semantic-node-host")
(include-book "../books/history-preparation-page-ready")
(include-book "../books/history-page-construction")

(defun fn-hpr-builder-with-cursor (builder cursor)
 (declare (xargs :guard t))
 (list (fn-hed-at 0 builder) (fn-hed-at 1 builder)
       (fn-hed-at 2 builder) (fn-hed-at 3 builder)
       (fn-hed-at 4 builder) (fn-hed-at 5 builder)
       (fn-hed-at 6 builder) (fn-hed-at 7 builder)
       cursor (fn-hed-at 9 builder)))


; This internal continuation is reached only after TAIL's current token/source
; gate. Creator intent is durable in the retained builder before raw effects.
(defun fn-owner-admission-new-page-step (fuel fn-history-backing state)
 (declare (xargs :stobjs (fn-history-backing state) :mode :program :guard (natp fuel)))
 (let* ((builder (fn-hep-builder fn-history-backing))
        (token (fn-hed-at 6 builder)) (old (fn-hed-at 7 builder))
        (cursor (fn-hed-at 8 builder)) (count (fn-hed-at 7 old))
        (pages (fn-hed-at 6 old)) (depth (integer-length (nfix (fn-prl-nth 1 token)))))
  (cond
   ((or (not (natp count)) (not (natp pages))
         (not (equal (mod count 256) 0)) (not (equal pages (floor count 256))))
    (mv :recovery-required fuel fn-history-backing state))
   ((not cursor)
    (let* ((leaf (list :history-leaf (fn-prl-nth 1 token) (1+ (fn-prl-nth 1 token)) 0 (fn-hed-at 2 old) count))
           (next (list :history-page-build token leaf :construct nil depth))
           (fn-history-backing (update-fn-hep-builder
             (fn-hpr-builder-with-cursor builder next) fn-history-backing)))
     (mv :yield (1- fuel) fn-history-backing state)))
   ((not (and (fn-hed-fixedp cursor 6) (eq (fn-hed-at 0 cursor) :history-page-build)
               (fn-apr-tokenp (fn-hed-at 1 cursor)) (equal token (fn-hed-at 1 cursor))
               (fn-hed-leafp (fn-hed-at 2 cursor)) (equal depth (fn-hed-at 5 cursor))))
    (mv :recovery-required fuel fn-history-backing state))
   ((eq (fn-hed-at 3 cursor) :construct-intent)
    (mv :recovery-required fuel fn-history-backing state))
   ((eq (fn-hed-at 3 cursor) :construct)
    (let* ((leaf (fn-hed-at 2 cursor))
           (fn-history-backing (update-fn-hep-builder
             (fn-hpr-builder-with-cursor builder
               (list :history-page-build token leaf :construct-intent nil depth)) fn-history-backing)))
     (stobj-let ((fn-hep-node (fn-hep-provider fn-history-backing)))
      (word left fn-hep-node)
      (fn-hpc-node-one (fn-prl-nth 1 token) depth (fn-hed-at 2 old) (1+ (fn-prl-nth 1 token)) 0 count fuel fn-hep-node)
      (let* ((grow (and (eq word :page-ready)
                        (fn-hed-grow-begin (fn-hed-at 4 old) pages (fn-hed-at 5 old) leaf)))
             (phase (cond ((eq word :page-ready) :forest)
                          ((member-eq word '(:yield :constructed)) :construct)
                          (t :fenced)))
             (fn-history-backing (update-fn-hep-builder
               (fn-hpr-builder-with-cursor builder
                 (list :history-page-build token leaf phase grow depth)) fn-history-backing)))
       (mv word left fn-history-backing state)))))
   ((eq (fn-hed-at 3 cursor) :forest)
    (let* ((grow (fn-hed-grow-step (fn-hed-at 4 cursor)))
           (word (fn-hed-at 1 grow))
           (next (if (eq word :done)
                     (list :history-tail-ready token (fn-hed-at 2 cursor) 0
                           (fn-hed-at 6 grow) (fn-hed-at 4 grow) (fn-hed-at 5 grow))
                   (list :history-page-build token (fn-hed-at 2 cursor)
                         (if (eq word :carry) :forest :fenced) grow depth)))
           (fn-history-backing (update-fn-hep-builder
             (fn-hpr-builder-with-cursor builder next) fn-history-backing)))
     (mv (cond ((eq word :done) :append-ready) ((eq word :carry) :yield)
               (t :recovery-required)) (1- fuel) fn-history-backing state)))
   (t (mv :recovery-required fuel fn-history-backing state)))))

(defun fn-owner-admission-tail-step (fuel fn-history-backing state)
 (declare (xargs :stobjs (fn-history-backing state) :mode :program
                 :guard (natp fuel)))
 (let* ((current (fn-apr-owner-current state))
        (token (fn-prl-nth 0 current))
        (builder (fn-hep-builder fn-history-backing))
        (old (fn-hed-at 7 builder))
        (cursor (fn-hed-at 8 builder))
        (count (fn-hed-at 7 old)))
  (cond
   ((not (and (fn-apr-tokenp token) (fn-apr-livep token current)
              (eq (fn-owner-history-writer-gate token state) :writer-current)
              (eq (fn-hep-producer-phase fn-history-backing) :offered)
              (fn-hed-fixedp builder 10)
              (eq (fn-hed-at 0 builder) :history-builder)
              (fn-apr-tokenp (fn-hed-at 6 builder))
              (equal token (fn-hed-at 6 builder))
              (fn-apr-tokenp (fn-hep-producer-token fn-history-backing))
              (equal token (fn-hep-producer-token fn-history-backing))
              (fn-hep-sourcep old) (fn-hep-epoch-livep old fn-history-backing)
              (fn-hep-source-stamps-equal old (fn-hep-current fn-history-backing))
              (equal count (fn-prl-nth 3 token))))
    (mv :writer-stale fuel fn-history-backing state))
   ((and (or (fn-hed-fixedp cursor 4) (fn-hed-fixedp cursor 7)) (eq (fn-hed-at 0 cursor) :history-tail-ready)
          (fn-apr-tokenp (fn-hed-at 1 cursor))
          (equal token (fn-hed-at 1 cursor)))
    (mv :append-ready fuel fn-history-backing state))
   ((zp fuel) (mv :yield fuel fn-history-backing state))
   ; New pages and directory growth are private until durable publication.
   ((or (zp count) (equal (mod count 256) 0))
    (fn-owner-admission-new-page-step fuel fn-history-backing state))
   ((not cursor)
    (let* ((next (fn-hed-read-begin (fn-hed-at 4 old) (fn-hed-at 6 old) (1- count)))
           (fn-history-backing
            (update-fn-hep-builder (fn-hpr-builder-with-cursor builder next)
                                   fn-history-backing)))
     (mv :yield (1- fuel) fn-history-backing state)))
   (t
    (mv-let (word next leaf) (fn-hed-read-step cursor)
     (let* ((left (1- fuel))
            (fn-history-backing
             (update-fn-hep-builder (fn-hpr-builder-with-cursor builder next)
                                    fn-history-backing)))
      (cond
       ((eq word :yield) (mv :yield left fn-history-backing state))
       ((not (and (eq word :leaf) (fn-hed-leafp leaf)
                   (equal (fn-hed-at 4 leaf) (fn-hed-at 2 old))
                   (<= (fn-hed-at 5 leaf) count)
                   (< (- count (fn-hed-at 5 leaf)) 256)))
        (mv :recovery-required left fn-history-backing state))
       ((<= left (integer-length (nfix (fn-hed-at 1 leaf))))
        (mv :yield left fn-history-backing state))
       (t
        (let ((expected (- count (fn-hed-at 5 leaf))))
         (stobj-let ((fn-hep-node (fn-hep-provider fn-history-backing)))
          (ready remaining)
          (fn-hpr-node-ready (fn-hed-at 1 leaf) (integer-length (nfix (fn-hed-at 1 leaf)))
                             (fn-hed-at 4 leaf) (fn-hed-at 2 leaf) (fn-hed-at 3 leaf)
                             (fn-hed-at 5 leaf) expected left fn-hep-node)
          (if (eq ready :append-ready)
              (let ((fn-history-backing
                     (update-fn-hep-builder
                      (fn-hpr-builder-with-cursor builder
                       (list :history-tail-ready token leaf expected)) fn-history-backing)))
               (mv :append-ready remaining fn-history-backing state))
            (mv ready remaining fn-history-backing state))))))))))))
