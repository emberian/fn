; Actual current append-leaf selection before durability. No supplied leaf,
; source, reservation, count or constructor authority enters this callback.
(in-package "ACL2")
(include-book "admission-semantic-node-host")
(include-book "../books/history-preparation-page-ready")

(defun fn-hpr-builder-with-cursor (builder cursor)
 (declare (xargs :guard t))
 (list (fn-hed-at 0 builder) (fn-hed-at 1 builder)
       (fn-hed-at 2 builder) (fn-hed-at 3 builder)
       (fn-hed-at 4 builder) (fn-hed-at 5 builder)
       (fn-hed-at 6 builder) (fn-hed-at 7 builder)
       cursor (fn-hed-at 9 builder)))

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
   ((and (fn-hed-fixedp cursor 4) (eq (fn-hed-at 0 cursor) :history-tail-ready)
          (fn-apr-tokenp (fn-hed-at 1 cursor))
          (equal token (fn-hed-at 1 cursor)))
    (mv :append-ready fuel fn-history-backing state))
   ((zp fuel) (mv :yield fuel fn-history-backing state))
   ; A new/full page requires a genuine separately issued constructor. This
   ; existing-page path neither defaults a child nor invents a page identity.
   ((or (zp count) (equal (mod count 256) 0))
    (mv :constructor-required fuel fn-history-backing state))
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
       ((<= left (fn-hep-provider-depth fn-history-backing))
        (mv :yield left fn-history-backing state))
       (t
        (let ((expected (- count (fn-hed-at 5 leaf))))
         (stobj-let ((fn-hep-node (fn-hep-provider fn-history-backing)))
          (ready remaining)
          (fn-hpr-node-ready (fn-hed-at 1 leaf) (fn-hep-provider-depth fn-history-backing)
                             (fn-hed-at 4 leaf) (fn-hed-at 2 leaf) (fn-hed-at 3 leaf)
                             (fn-hed-at 5 leaf) expected left fn-hep-node)
          (if (eq ready :append-ready)
              (let ((fn-history-backing
                     (update-fn-hep-builder
                      (fn-hpr-builder-with-cursor builder
                       (list :history-tail-ready token leaf expected)) fn-history-backing)))
               (mv :append-ready remaining fn-history-backing state))
            (mv ready remaining fn-history-backing state))))))))))))
