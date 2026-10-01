; Actual control-input continuation over a pinned dense event source.
; SOURCE-ASSEMBLY: reader/custody/funding integration and guards remain open.
; No whole-history lookup occurs here. ROW is supplied only by the actual
; completed registered candidate reader, never by a remote client/native flag.
(in-package "ACL2")
(include-book "control-visible")
(include-book "store-events-carried")
(include-book "control-config-projection")

; Fixed15: tag,phase,msgid,target,ordinal,F,Eupper,chain,source,verdict-tail,
; original-event,original-control,selected-verdict,target-locks,config-cursor.
; Captured F includes the privately installed current E row. It is not a C
; ordinal or an allocator txid. Source/custody is established by the caller.
(defun fn-ctcd-cursorp (x)
 (declare (xargs :guard t))
 (and (fn-cbor-at-mostp x 15) (true-listp x) (equal (len x) 15)
      (eq (fn-cp-nth 0 x) :control-input-cursor)
      (member-eq (fn-cp-nth 1 x) '(:event :verdict :target :config))
      (natp (fn-cp-nth 4 x)) (natp (fn-cp-nth 5 x))
      (<= (fn-cp-nth 4 x) (fn-cp-nth 5 x))
      (natp (fn-cp-nth 6 x))))

(defun fn-ctcd-begin (article verdicts chain captured-source event-count event-upper-txid)
 (declare (xargs :guard t :verify-guards nil))
 (cond ((not (consp article)) '(:plan nil nil nil))
       ((not (and (natp event-count) (natp event-upper-txid)))
        '(:unavailable :control-event-source-bound))
       (t (list :yield (list :control-input-cursor :event
                             (fn-article-msgid article) nil 0 event-count
                             event-upper-txid chain captured-source verdicts
                             nil nil nil nil nil)))))

; Transition after one exact verdict is selected (or saved list exhausted).
; Target lookup starts at ordinal0: preserve oldest row selection even when
; an inactive/expired older row shares the arriving candidate's Message-ID.
(defun fn-ctcd-target-begin (cursor verdict)
 (declare (xargs :guard t :verify-guards nil))
 (list :yield
  (ec-call (update-nth 1 :target
   (ec-call (update-nth 4 0
    (ec-call (update-nth 9 nil
     (ec-call (update-nth 12 verdict cursor))))))))))

(defun fn-ctcd-config-begin (cursor locks)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((event (fn-cp-nth 10 cursor))
        (query (fn-evc-txid event)))
  (if (not (and (natp query) (<= query (fn-cp-nth 6 cursor))))
      '(:unavailable :control-event-source-bound)
   (let ((one (fn-ccpx-begin (fn-cp-nth 7 cursor) query (fn-cp-nth 8 cursor))))
    (if (not (eq (fn-cp-nth 0 one) :yield)) one
     (list :yield
      (ec-call (update-nth 1 :config
       (ec-call (update-nth 13 locks
        (ec-call (update-nth 14 (fn-cp-nth 1 one) cursor))))))))))))

; No read is requested at F. Absence is established only by completing all
; ordinals in this SAME captured prefix, never by a NIL/unavailable read.
; Verdict lookup consumes precisely one original borrowed pair per tick.
(defun fn-ctcd-step (cursor)
 (declare (xargs :guard t :verify-guards nil))
 (if (not (fn-ctcd-cursorp cursor)) '(:refused :control-input-cursor)
  (let ((phase (fn-cp-nth 1 cursor))
        (ordinal (fn-cp-nth 4 cursor)) (f (fn-cp-nth 5 cursor)))
   (cond
    ((eq phase :event)
     (if (< ordinal f)
         (list :read cursor ordinal (fn-cp-nth 8 cursor))
       '(:plan nil nil nil)))
    ((eq phase :verdict)
     (let ((tail (fn-cp-nth 9 cursor)))
      (if (not (consp tail)) (fn-ctcd-target-begin cursor nil)
       (if (and (consp (car tail))
                (equal (car (car tail)) (fn-cp-nth 2 cursor)))
           (fn-ctcd-target-begin cursor (cdr (car tail)))
         (list :yield (ec-call (update-nth 9 (cdr tail) cursor)))))))
    ((eq phase :target)
     (if (< ordinal f)
         (list :read cursor ordinal (fn-cp-nth 8 cursor))
       (fn-ctcd-config-begin cursor nil)))
    (t
     (let ((one (fn-ccpx-tick (fn-cp-nth 14 cursor))))
      (cond ((eq (fn-cp-nth 0 one) :yield)
             (list :yield (ec-call (update-nth 14 (fn-cp-nth 1 one) cursor))))
            ((not (eq (fn-cp-nth 0 one) :configuration)) one)
            (t
             (list :plan
              (fn-ctl-w-with-tlocks
               (fn-ctl-withdrawal-plan
                (fn-cp-nth 2 cursor) (fn-cp-nth 12 cursor)
                (fn-cp-nth 3 cursor)
                (fn-ctl-control-keys (fn-cp-nth 11 cursor))
                (fn-cp-nth 1 one))
               (fn-cp-nth 13 cursor))
              one (fn-ctl-control-locks (fn-cp-nth 11 cursor)))))))))))

; Called only after the registered dense candidate reader completes :row.
; Scalar sequence/txid checks reject a mismatched reply before cursor change;
; they do not establish the source/root/epoch association by themselves.
; The actual registered decoder/reader must establish valid Store-event
; input; the executable body uses carried fixed-shape coordinate selectors,
; never a complete remote group recognizer. The unverified guard blocks any
; representation completion claim until this actual caller relation exists.
(defun fn-ctcd-row (cursor row)
 (declare (xargs :guard (and (fn-ctcd-cursorp cursor) (fn-store-event-p row))
                 :verify-guards nil))
 (if (not (and (fn-ctcd-cursorp cursor)
               (member-eq (fn-cp-nth 1 cursor) '(:event :target))
               (< (fn-cp-nth 4 cursor) (fn-cp-nth 5 cursor))))
     '(:refused :control-input-row-phase)
  (if (not (and (mbe :logic (fn-store-event-p row) :exec t)
                (equal (fn-evc-sequence row) (fn-cp-nth 4 cursor))
                (natp (fn-evc-txid row))
                (<= (fn-evc-txid row) (fn-cp-nth 6 cursor))))
      '(:unavailable :control-event-source-row)
   (let* ((held (fn-ctl-event-row row))
          (wanted (if (eq (fn-cp-nth 1 cursor) :event)
                      (fn-cp-nth 2 cursor) (fn-cp-nth 3 cursor)))
          (matched (and wanted held (equal (fn-record-msgid held) wanted))))
    (if (not matched)
        (list :yield (ec-call (update-nth 4 (1+ (fn-cp-nth 4 cursor)) cursor)))
     (let ((control (fn-hf-control (fn-held-facts held))))
      (if (eq (fn-cp-nth 1 cursor) :target)
          (fn-ctcd-config-begin cursor (fn-ctl-control-locks control))
       (let ((target (fn-ctl-control-target control)))
        (if (not target) (list :plan nil nil (fn-ctl-control-locks control))
         (list :yield
          (ec-call (update-nth 1 :verdict
           (ec-call (update-nth 3 target
            (ec-call (update-nth 10 row
             (ec-call (update-nth 11 control cursor))))))))))))))))))

(in-theory (disable fn-ctcd-cursorp fn-ctcd-begin fn-ctcd-target-begin
                    fn-ctcd-config-begin fn-ctcd-step fn-ctcd-row))
