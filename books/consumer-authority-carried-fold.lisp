; Paired complete Store callback draft. Its low account/config producer is
; separate for exact source reuse; this high callback requires the matching
; actual Store/schema/view/metadata source world before qualification. No
; native activation or whole replay/funding claim follows from the low leaf.
(in-package "ACL2")

(include-book "consumer-store-projection")
(include-book "consumer-authority-carried-result")

(include-book "consumer-entry-completion")
(include-book "control-visible-effect")

(defun fn-carfc-frontier-metadata (next metadata)
 (declare (xargs :guard t))
 (let* ((fields (fn-cp-nth 1 metadata))
        (nf (list (fn-cp-nth 0 fields) (fn-cp-nth 1 fields)
                  (fn-cp-nth 2 fields) (fn-caac-atom next)
                  (fn-cp-nth 4 fields) (fn-cp-nth 5 fields) (fn-cp-nth 6 fields))))
  (list :account-carries nf (fn-cp-nth 2 metadata)
                            (fn-cp-nth 3 metadata) (fn-cp-nth 4 metadata))))

(defun fn-carfc-advance (cp next metadata)
 (declare (xargs :guard t))
 (if (null cp) (list :ok nil nil)
  (if (not (fn-cpm-metadatap metadata)) '(:refused :consumer-metadata-unavailable)
    (list :ok (fn-cpe-projection-advance cp next)
              (fn-carfc-frontier-metadata next metadata)))))

(defun fn-carfc-event-effect (event visibility-effect)
 (declare (xargs :guard t))
 (cond ((fn-cpe-eventp event)
        (if (eq (fn-cp-nth 0 (fn-cpe-operation event)) :rollover)
            :changed :preserved))
       ((or (fn-stxk-p event) (fn-th-topic-eventp event)
            (fn-store-retention-event-p event)) :changed)
       (t visibility-effect)))

(defun fn-carfc-rollover (cp incarnation expected metadata)
 (declare (xargs :guard t))
 (if (not (fn-cpm-metadatap metadata)) '(:refused :consumer-metadata-unavailable)
  (if (equal incarnation (fn-cp-nth 2 cp)) '(:refused :same-incarnation)
   (let* ((next (fn-cp-state-carry (fn-cp-nth 1 cp) incarnation (1+ (nfix expected))
                                   (fn-cp-nth 4 cp) nil (fn-cp-nth 6 cp)))
          (fields (fn-cp-nth 1 metadata))
          (nf (list (fn-cp-nth 0 fields) (fn-cp-nth 1 fields)
                    (fn-scs-octets (len incarnation)) (fn-caac-atom (1+ (nfix expected)))
                    (fn-cp-nth 4 fields) (fn-caac-atom nil) (fn-cp-nth 6 fields)))
          (nm (list :account-carries nf (fn-cp-nth 2 metadata) (fn-cp-nth 3 metadata) nil)))
    (fn-carfc-finish-effect (list :ok next nm) :changed)))))

(defun fn-carfc-event-step (cp event expected visibility-effect metadata cursor)
 (declare (xargs :guard t))
 (if (or (not (fn-cp-uintp expected))
         (>= (nfix expected) *fn-cbor-max-uint*)
         (not (equal (fn-store-event-sequence event) expected)))
     '(:refused :sequence)
  (cond
   ; Account2/binding3 require the jointly captured C preparation and typed
   ; C publication. In particular this generic branch must never activate
   ; the inherited E fence or silently lose its signing/config preparation.
   ((fn-cae-eventp event) '(:refused :account-config-interpreter-required))
   ((fn-cpe-eventp event)
    (let* ((op (fn-cpe-operation event)) (kind (fn-cp-nth 0 op)))
     (cond
      ((eq kind :bootstrap)
       (if cp '(:refused :duplicate-bootstrap)
        (mv-let (seed seedmetadata)
          (fn-cpm-initial (fn-cp-nth 1 op) (fn-cp-nth 2 op) (1+ expected)
                          (len (fn-cp-nth 1 op)) (len (fn-cp-nth 2 op)))
         (fn-carfc-result seed nil nil seedmetadata nil))))
      ((null cp) '(:refused :unbootstrapped))
      ((not (equal (fn-cp-nth 3 cp) expected)) '(:refused :frontier))
      ((eq kind :rollover) (fn-carfc-rollover cp (fn-cp-nth 1 op) expected metadata))
      (t (let ((one (fn-cec-local-preflight cp op metadata cursor)))
           (if (not (eq (fn-cp-nth 0 one) :ok)) one
             (fn-carfc-finish-effect
               (fn-carfc-advance (fn-cp-nth 1 one) (1+ expected) (fn-cp-nth 2 one))
               :preserved)))))))
   (t (let ((one (fn-cpe-projection-step cp event expected)))
       (if (not (eq (fn-cp-nth 0 one) :ok)) one
         (let ((approved-cp (fn-cp-nth 1 one)))
          (if (and approved-cp (not (fn-cpm-metadatap metadata)))
              '(:refused :consumer-metadata-unavailable)
            (fn-carfc-finish-effect
             (list :ok approved-cp
                       (and approved-cp (fn-carfc-frontier-metadata (1+ expected) metadata)))
             (fn-carfc-event-effect event visibility-effect))))))))))

; The actual refresh produces the effect alongside the exact withdrawals and
; visible list installed by the caller. Neither native code nor an EFFECTS
; list supplies it. The caller retains physical/identity replay once and feeds
; their same-prefix raw/verdict values to this single paired consumer decision.
(defun fn-carfc-event-refresh-step
    (cp event expected new old ws old-visible old-verdicts verdicts
        files fn-hist configs metadata cursor)
 (declare (xargs :stobjs fn-hist :guard t))
 (mv-let (withdrawals withdrawal-effect)
   (fn-ctl-refresh-withdrawals-effect-fx new old ws verdicts files fn-hist configs)
   (mv-let (visible effect)
     (fn-ctl-refresh-visible-effect
      new old old-visible withdrawals old-verdicts verdicts withdrawal-effect)
     (mv (fn-carfc-event-step cp event expected effect metadata cursor)
         withdrawals visible))))

(in-theory (disable fn-carfc-frontier-metadata fn-carfc-advance fn-carfc-event-effect
                    fn-carfc-rollover fn-carfc-event-step
                    fn-carfc-event-refresh-step))
