; Internal retained-row actions for the registered range provider.
; HELD is supplied only by the SAME sealed captured row child; this book
; does not authorize an externally supplied row or activate a host entry.
(in-package "ACL2")
(include-book "index-range-number-controller")
(include-book "over-selected-source-carry")

; Caller/guard vocabulary; never a semantic scan in the selected body.
(defun fn-ibr-held-install-ready-p (control held fn-arena)
 (declare (xargs :stobjs fn-arena :guard t))
 (let* ((work (fn-spp-at 8 control))
        (range (fn-spp-at 1 work)) (publication (fn-spp-at 2 work))
        (result (fn-gns-number-result (fn-spp-at 7 control))))
  (and (true-listp control) (true-listp work) (true-listp range)
       (equal (fn-spp-at 3 control) :row)
       (equal (fn-spp-at 0 result) :ordinal)
       (natp (fn-spp-at 1 result))
       (natp (fn-ipub-count publication))
       (< (fn-spp-at 1 result) (fn-ipub-count publication))
       (natp (fn-ipub-view publication))
       (fn-held-withdrawnp (fn-held-withdrawn held))
       (natp (fn-record-payload held))
       (< (fn-record-payload held) (fn-arena-count fn-arena))
       (or (not (fn-hf-nov (fn-held-facts held)))
           (fn-hnov-p (fn-hf-nov (fn-held-facts held)))))))

; SAME captured C and V remain distinct. Reference/catalog correspondence
; is a separate boundary obligation; this literal scalar test is not a
; claim that a later catalog at the same numeric V denotes this source.
(defun fn-ibr-held-visible-p (ordinal count view held)
 (declare (xargs :guard (and (natp ordinal) (natp count) (natp view)
                             (fn-held-withdrawnp (fn-held-withdrawn held)))
                 :guard-hints (("Goal" :in-theory (enable fn-held-withdrawnp)))))
 (and (< ordinal count) (< ordinal view)
      (let ((withdrawn (fn-held-withdrawn held)))
       (or (null withdrawn) (<= view (car withdrawn))))))

(defun fn-ibr-selected-held-row-install (control held fn-arena)
 (declare (xargs :stobjs fn-arena
                 :guard (fn-ibr-held-install-ready-p control held fn-arena)
                 :verify-guards nil) (ignore fn-arena))
 (let* ((work (fn-spp-at 8 control))
        (range (fn-spp-at 1 work)) (publication (fn-spp-at 2 work))
        (ordinal (fn-spp-at 1 (fn-gns-number-result (fn-spp-at 7 control))))
        (group (fn-spp-at 6 control)) (number (fn-spp-at 7 control)))
  (if (fn-ibr-held-visible-p ordinal (fn-ipub-count publication)
                              (fn-ipub-view publication) held)
      (mv :held
       (fn-ibr-restate control :held group number
        (fn-ibr-work range publication (fn-spp-at 3 work)
          (fn-osh-begin range (fn-spp-origin (fn-spp-at 4 control)) held))))
    (let ((next (fn-obc-next-range range (fn-spp-at 5 range))))
     (mv :number
      (fn-ibr-restate control :number group
       (fn-gns-number-begin (fn-spp-at 1 next)
         (fn-spp-at 1 (fn-gns-group-selected-result group))
         (fn-ipub-count publication))
       (fn-ibr-work next publication nil nil)))))))

(verify-guards fn-ibr-selected-held-row-install
 :hints (("Goal" :in-theory
  (e/d (fn-ibr-held-install-ready-p)
       (fn-ibr-held-visible-p fn-gns-number-result fn-gns-number-begin
        fn-osh-begin fn-obc-next-range fn-ibr-restate fn-ibr-work
        fn-spp-origin fn-ipub-count fn-ipub-view fn-held-withdrawnp)))))

(defthm fn-ibr-selected-held-install-establishes-cell-carry
 (implies (fn-ibr-held-install-ready-p control held fn-arena)
  (let* ((result (fn-ibr-selected-held-row-install control held fn-arena))
         (next (mv-nth 1 result))
         (cell (fn-spp-at 4 (fn-spp-at 8 next))))
   (implies (eq (mv-nth 0 result) :held)
    (and (fn-osh-ready-p cell fn-arena)
         (fn-osh-selected-source-p cell)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-osh-begin-establishes-held-row-carry
          (range (fn-spp-at 1 (fn-spp-at 8 control)))
          (origin (fn-spp-origin (fn-spp-at 4 control))) (row held)))
  :in-theory
   (e/d (fn-ibr-held-install-ready-p fn-ibr-selected-held-row-install
         fn-ibr-restate fn-ibr-make fn-ibr-work fn-spp-at fn-ag-car fn-ag-cdr
         fn-osh-selected-source-p fn-osh-begin fn-osh-make fn-hmid-at)
        (fn-osh-ready-p fn-hmid-begin fn-spp-origin fn-ibr-held-visible-p
         fn-held-facts fn-hf-nov fn-hnov-p fn-record-payload
         fn-gns-number-result fn-gns-number-begin fn-obc-next-range
         fn-ipub-count fn-ipub-view fn-held-withdrawnp
         fn-arena-count fn-arena-payload-len)))))

(defun fn-ibr-held-current-ready-p (control fn-arena)
 (declare (xargs :stobjs fn-arena :guard t))
 (let* ((work (fn-spp-at 8 control)) (range (fn-spp-at 1 work))
        (cell (fn-spp-at 4 work)))
  (and (true-listp control) (true-listp work) (true-listp range) (consp range)
       (equal (fn-spp-at 3 control) :held)
       (equal (fn-hmid-at 1 cell) range)
       (fn-osh-ready-p cell fn-arena) (fn-osh-selected-source-p cell))))

; ONE changes the SAME installed cell, retaining original plan/publication.
; Its actual returned seek range already contains the correct owed state:
; after a row it is NIL, after invalid MsgID it is the old reply obligation.
(defun fn-ibr-held-one (control fn-arena)
 (declare (xargs :stobjs fn-arena
                 :guard (fn-ibr-held-current-ready-p control fn-arena)
                 :verify-guards nil))
 (let* ((work (fn-spp-at 8 control))
        (publication (fn-spp-at 2 work)) (cell (fn-spp-at 4 work))
        (group (fn-spp-at 6 control)) (number (fn-spp-at 7 control)))
  (mv-let (out next-cell) (fn-osh-one cell fn-arena)
   (if (not next-cell)
       (mv out :recovery-required control)
    (if (or (equal (fn-hmid-at 4 next-cell) :skip)
            (and (equal (fn-hmid-at 4 next-cell) :row)
                 (equal (fn-hmid-at 2 (fn-hmid-at 5 next-cell)) :seek)))
        (let ((next-range (fn-hmid-at 0 (fn-hmid-at 5 next-cell))))
         (mv out :number
          (fn-ibr-restate control :number group
           (fn-gns-number-begin (fn-spp-at 1 next-range)
             (fn-spp-at 1 (fn-gns-group-selected-result group))
             (fn-ipub-count publication))
           (fn-ibr-work next-range publication nil nil))))
      (mv out :held
       (fn-ibr-restate control :held group number
        (fn-ibr-work (fn-spp-at 1 work) publication
                     (fn-spp-at 3 work) next-cell))))))))

(verify-guards fn-ibr-held-one
 :hints (("Goal" :in-theory
  (e/d (fn-ibr-held-current-ready-p)
       (fn-osh-one fn-osh-ready-p fn-osh-selected-source-p
        fn-gns-number-begin fn-gns-group-selected-result fn-ibr-restate fn-ibr-work
        fn-ipub-count)))))

(local
 (defthm fn-ibr-cell-at-one-is-nth
  (equal (fn-hmid-at i x) (nth (nfix i) x))
  :hints (("Goal" :in-theory (enable fn-hmid-at fn-ag-car fn-ag-cdr nth)))))

(defthm fn-ibr-held-one-preserves-current-cell-carry
 (implies (fn-ibr-held-current-ready-p control fn-arena)
  (let ((result (fn-ibr-held-one control fn-arena)))
   (implies (eq (mv-nth 1 result) :held)
            (fn-ibr-held-current-ready-p (mv-nth 2 result) fn-arena))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-osh-one-preserves-held-row-carry
          (cell (fn-spp-at 4 (fn-spp-at 8 control))))
        (:instance fn-osh-one-preserves-selected-source
          (cell (fn-spp-at 4 (fn-spp-at 8 control))))
        (:instance fn-osh-one-retains-original-row-source-and-range-unfolds
          (cell (fn-spp-at 4 (fn-spp-at 8 control)))))
  :in-theory
   (e/d (fn-ibr-held-current-ready-p fn-ibr-held-one
         fn-ibr-restate fn-ibr-make fn-ibr-work fn-spp-at fn-hmid-at
         fn-ag-car fn-ag-cdr)
        (nth mv-nth fn-osh-one fn-osh-ready-p fn-osh-selected-source-p
         fn-gns-number-begin fn-gns-group-selected-result fn-ipub-count)))))

; Full range termination becomes the current paid reply, with every later
; effect still in the SAME SPP. OWED is taken from the actual advanced range.
(defun fn-ibr-terminal-prepare (control)
 (declare (xargs :guard t))
 (let* ((plan (fn-spp-at 4 control)) (work (fn-spp-at 8 control))
        (range (fn-spp-at 1 work)))
  (if (not (and (equal (fn-spp-at 3 control) :terminal)
                (eq (fn-spp-status plan) :cursor)))
      (mv :unavailable control)
    (let* ((reply (if (fn-spp-at 5 range)
                     (fn-ovw-status (fn-ovw-empty-text (fn-spp-at 4 range)))
                   '(46 13 10)))
           (next-plan
             (fn-spp-save-active plan
               (cons reply (fn-ag-cdr (fn-spp-rest plan))))))
     (mv :position
      (fn-ibr-make (fn-spp-at 1 control) (fn-spp-at 2 control) :position
                   next-plan (fn-spp-at 5 control)
                   (fn-spp-at 6 control) (fn-spp-at 7 control) work))))))

(defun fn-ibr-terminal-head-window (w fn-octets control)
 (declare (xargs :stobjs fn-octets :guard (natp w)))
 (if (not (natp w)) (mv :unavailable control fn-octets)
  (mv-let (word positioned) (fn-ibr-terminal-prepare control)
   (if (not (and (eq word :position)
                 (eq (fn-spp-status (fn-spp-at 4 positioned)) :reply)))
       (mv (if (eq word :position) :recovery-required word) control fn-octets)
     (mv-let (status plan fn-octets)
       (fn-spp-head-window (fn-spp-at 4 positioned) w fn-octets)
      (mv status
       (fn-ibr-make (fn-spp-at 1 positioned) (fn-spp-at 2 positioned) :position
                    plan (fn-spp-at 5 positioned) (fn-spp-at 6 positioned)
                    (fn-spp-at 7 positioned) (fn-spp-at 8 positioned))
       fn-octets))))))

(local
 (defthm fn-ibr-terminal-prepares-fixed-reply
  (implies (and (equal (fn-spp-at 3 control) :terminal)
                (eq (fn-spp-status (fn-spp-at 4 control)) :cursor))
   (let ((plan (fn-spp-at 4 (mv-nth 1 (fn-ibr-terminal-prepare control)))))
    (and (eq (mv-nth 0 (fn-ibr-terminal-prepare control)) :position)
         (eq (fn-spp-status plan) :reply) (consp (fn-spp-cur plan))
         (true-listp (fn-spp-cur plan)))))
  :hints (("Goal" :do-not-induct t :in-theory
    (e/d (fn-ibr-terminal-prepare fn-ibr-make fn-spp-save-active fn-spp-make
          fn-spp-status fn-spp-holderp fn-spp-cur fn-spp-rest fn-spp-prefix
          fn-spp-origin fn-spp-resource fn-spp-at fn-ag-car fn-ag-cdr
          fn-splan-cur fn-splan-rest fn-ovw-empty-text)
         (fn-ovw-status fn-splan-cursor-effectp fn-srb-effect-octets))))))

(defthm fn-ibr-terminal-window-refines-original-buffer-window
 (let* ((positioned (mv-nth 1 (fn-ibr-terminal-prepare control)))
        (prepared (fn-spp-at 4 positioned))
        (actual (fn-ibr-terminal-head-window w fn-octets control))
        (old (fn-splan-window (fn-spp-active-plan prepared)
                              (min w (len (fn-spp-cur prepared))) fn-octets))
        (next (fn-spp-at 4 (mv-nth 1 actual))))
  (implies (and (natp w)
                (equal (fn-spp-at 3 control) :terminal)
                (eq (fn-spp-status (fn-spp-at 4 control)) :cursor))
   (and (equal (mv-nth 0 actual) (mv-nth 0 old))
        (equal (mv-nth 2 actual) (mv-nth 2 old))
        (equal (fn-spp-active-plan next) (mv-nth 1 old))
        (equal (fn-spp-prefix next) (fn-spp-prefix (fn-spp-at 4 control)))
        (equal (fn-spp-origin next) (fn-spp-origin (fn-spp-at 4 control)))
        (equal (fn-spp-resource next) (fn-spp-resource (fn-spp-at 4 control))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-ibr-terminal-prepares-fixed-reply)
        (:instance fn-spp-head-window-refines-actual-old-buffer-window
          (p (fn-spp-at 4 (mv-nth 1 (fn-ibr-terminal-prepare control))))))
  :in-theory
   (e/d (fn-ibr-terminal-head-window fn-ibr-terminal-prepare fn-ibr-make
         fn-spp-save-active fn-spp-make fn-spp-at fn-ag-car fn-ag-cdr
         fn-spp-prefix fn-spp-origin fn-spp-resource)
        (fn-spp-head-window fn-splan-window fn-spp-active-plan fn-spp-cur
         fn-spp-rest
         fn-spp-status fn-ovw-status fn-ovw-empty-text len min)))))
