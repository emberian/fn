; Actual private checkpoint writer controller. The remaining stream joins
; live in this book; this preflight/handshake does not activate a host path.
(in-package "ACL2")
(include-book "history-pool-columns")
(include-book "history-image-header")
(include-book "history-page-layout")
(include-book "history-page-metadata")
(include-book "snapshot-maintenance-demand")
(include-book "pagestore-digest-byte-cursor")

; Fixed controller/meta fields only, never a stored-data traversal. This
; guarded updater preserves the model update on every actual slot0..24.
(defun fn-hpi-set (index value c)
  (declare (xargs :guard t :measure (nfix index)))
  (cond ((not (and (natp index) (< index 25))) c)
        ((zp index) (cons value (if (consp c) (cdr c) nil)))
        (t (cons (if (consp c) (car c) nil)
                 (fn-hpi-set (1- index) value (if (consp c) (cdr c) nil))))))

(defthm fn-hpi-set-is-update-by-definition
  (implies (and (natp index) (< index 25))
           (equal (fn-hpi-set index value c) (update-nth index value c)))
  :hints (("Goal" :induct (fn-hpi-set index value c)
           :in-theory (enable update-nth))))

(in-theory (disable fn-hpi-set))

(defun fn-hpi-cap-validp (used cap)
  (declare (xargs :guard t))
  ; Check the completed doubling cursor's exact current-format capacity.
  ; Width comes from the persisted image domain, not an implementation cap.
  (and (unsigned-byte-p 64 used) (unsigned-byte-p 51 cap)
       (if (equal used 0) (equal cap 0)
         (and (< 0 cap) (equal (logcount cap) 1)
              (<= (ceiling used 16384) cap)
              (< (floor cap 2) (ceiling used 16384))))))

(defun fn-hpi-layout (count pool column-cap pool-cap extent-limit)
  (declare (xargs :guard t))
  ; The FNSI wrapper owns the first 16KiB. Physical page0 then contains
  ; zeros; logical header page0 is a data page at the fresh layout's base.
  ; EXTENT-LIMIT is the admitted profile/platform file extent, not u64.
  (if (not (and (unsigned-byte-p 61 count) (unsigned-byte-p 64 pool)
                (equal (mod pool 8) 0) (or (< 0 count) (equal pool 0))
                (fn-hpi-cap-validp (* 8 count) column-cap)
                (fn-hpi-cap-validp pool pool-cap) (natp extent-limit)))
      '(:refused :census-domain)
    (let ((admit (fn-hcl-admit count pool column-cap pool-cap)))
      (if (not (eq (car admit) :prepared)) admit
        (let* ((layout (fn-hpl-layout (fn-omk-at 1 admit)))
               (n (fn-omk-at 1 layout)) (nt (fn-omk-at 2 layout))
               (stage-end (+ 16384 (* 16384 (nfix (fn-omk-at 6 layout)))))
               (data-spool (* 32 (nfix n))) (table-spool (* 32 (nfix nt))))
          (if (not (and (eq (car layout) :layout)
                        (<= stage-end extent-limit)
                        (<= data-spool extent-limit) (<= table-spool extent-limit)))
              '(:refused :file-extent)
            (list :prepared layout stage-end data-spool table-spool)))))))

; Fixed control: phase,source4,resource-ticket,stage-ticket,serial,pending,
; layout-answer,count,pool,column-cap,pool-cap,node,salt,trail,body,
; region-pages,buffer-generations,resume,pad-region,metadata,digest,cached,
; funded-grant,io-kind,terminal.
; Resource admission must install the actual growth grant before any buffer
; initialization or write. Merely carrying RESOURCE-TICKET does not fund it.
(defun fn-hpi-begin (count pool column-cap pool-cap source4 resource-ticket
                          stage-ticket extent-limit node salt trail)
  (declare (xargs :guard t))
  (let ((layout (fn-hpi-layout count pool column-cap pool-cap extent-limit)))
    (if (not (and (eq (car layout) :prepared) (fn-omk-tokenp source4)
                  (equal (fn-omk-at 2 source4) 0) (natp stage-ticket)
                  (fn-omk-widthp resource-ticket 4)
                  (eq (fn-omk-at 0 resource-ticket) :maintenance)
                  (equal stage-ticket (fn-omk-at 1 resource-ticket))
                  (equal (fn-omk-at 0 source4) (fn-omk-at 2 resource-ticket))
                  (natp (fn-omk-at 3 resource-ticket))
                  (equal (fn-omk-at 3 source4) 0)
                  (equal (fn-omk-at 1 (fn-omk-at 1 source4)) count)))
        (list :refused source4 resource-ticket stage-ticket 0 nil layout
              count pool column-cap pool-cap node salt trail nil
              '(0 0 0 0 0) '(0 0 0 0 0) nil 0 nil nil nil nil nil nil)
      (list :need-growth source4 resource-ticket stage-ticket 0 nil layout
            count pool column-cap pool-cap node salt trail
            ; The producer's actual fn-osrc-restart changes drained census
            ; pass0 into emission pass1. The job/grant source4 stays pass0.
            (fn-hpcx-begin count pool
                          (list (fn-omk-at 0 source4) (fn-omk-at 1 source4)
                                (+ 1 (fn-omk-at 2 source4)) 0)
                          (fn-omk-at 1 source4) resource-ticket)
            '(0 0 0 0 0) '(0 0 0 0 0) nil 0 nil nil nil nil nil nil))))

(defun fn-hpi-growth-request (c)
  (declare (xargs :guard t))
  (let* ((answer (fn-omk-at 6 c)) (layout (fn-omk-at 1 answer)))
    ; Retained unchanged after growth, so the actual ledger grant can be
    ; rechecked throughout the writer. Only the grow entry may issue credit.
    (if (not (eq (fn-omk-at 0 answer) :prepared)) nil
      (list :checkpoint-growth (fn-omk-at 1 c) (fn-omk-at 3 c)
            (fn-omk-at 2 c) (fn-omk-at 1 layout) (fn-omk-at 2 layout)
            (fn-omk-at 3 layout) (fn-omk-at 2 answer)
            (fn-omk-at 3 answer) (fn-omk-at 4 answer)))))

(defun fn-hpi-write-effect (source4 stage-ticket serial region logical-page
                                  physical-page buffer-generation)
  (declare (xargs :guard (and (natp serial) (natp physical-page))))
  ; Host executes these exact scalars. It computes no address or decision.
  (list :write-page source4 stage-ticket serial region logical-page physical-page
        (+ 16384 (* 16384 physical-page)) 16384 buffer-generation))

(defun fn-hpi-written-matchp (effect observation)
  (declare (xargs :guard t))
  (and (fn-omk-widthp effect 10) (eq (fn-omk-at 0 effect) :write-page)
       (fn-omk-widthp observation 6) (eq (fn-omk-at 0 observation) :written)
       (fn-omk-token-matchp (fn-omk-at 1 effect) (fn-omk-at 1 observation))
       (equal (fn-omk-at 2 effect) (fn-omk-at 2 observation))
       (equal (fn-omk-at 3 effect) (fn-omk-at 3 observation))
       (equal (fn-omk-at 9 effect) (fn-omk-at 4 observation))
       (member-eq (fn-omk-at 5 observation) '(:ok :uncertain))))

(defun fn-hpi-written-status (effect observation)
  (declare (xargs :guard t))
  (if (not (fn-hpi-written-matchp effect observation)) :stale
    (if (eq (fn-omk-at 5 observation) :ok) :written :recovery-required)))

(defun fn-hpi-region-cap (region c)
  (declare (xargs :guard t))
  (if (equal region 4) (nfix (fn-omk-at 10 c))
    (nfix (fn-omk-at 9 c))))

(defun fn-hpi-region-start (region c)
  (declare (xargs :guard (and (natp region) (< region 5))))
  (+ 1 (* region (nfix (fn-omk-at 9 c)))))

(defun fn-hpi-await-page (region logical physical buffer resume c)
  (declare (xargs :guard (and (natp physical) (natp buffer) (< buffer 5))))
  (let* ((serial (nfix (fn-omk-at 4 c)))
         (generation (nfix (fn-omk-at buffer (fn-omk-at 16 c))))
         (effect (fn-hpi-write-effect (fn-omk-at 1 c) (fn-omk-at 3 c)
                   serial region logical physical generation))
         (c (fn-hpi-set 0 :wait-write c))
         (c (fn-hpi-set 4 (+ 1 serial) c))
         (c (fn-hpi-set 5 effect c))
         (c (fn-hpi-set 17 (list buffer resume) c)))
    (mv :write effect c)))

(defun fn-hpi-await-region (region resume c)
  (declare (xargs :guard (and (natp region) (< region 5))))
  (let* ((page (nfix (fn-omk-at region (fn-omk-at 15 c))))
         (logical (+ (fn-hpi-region-start region c) page))
         (layout (fn-omk-at 1 (fn-omk-at 6 c)))
         (physical (+ (nfix (fn-omk-at 4 layout)) logical)))
    (if (<= (fn-hpi-region-cap region c) page)
        (mv '(:refused :region-extent) nil (fn-hpi-set 0 :recovery-required c))
      (fn-hpi-await-page region logical physical region resume c))))

(defun fn-hpi-offer (c ordinal source token key)
  (declare (xargs :guard t))
  ; Producer authenticates the actual offered row and MKEY. The existing
  ; child enforces its epoch/capture/pass/ordinal before touching any buffer.
  (if (not (eq (fn-omk-at 0 c) :body)) (mv :stale c)
    (mv-let (word body) (fn-hpcx-offer (fn-omk-at 14 c) ordinal source token key)
      (mv word (fn-hpi-set 14 body c)))))

(defun fn-hpi-reset-buffer (region epoch lease fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
  (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
  (case region
    (0 (let ((fn-hpq0 (fn-hpb-begin epoch lease fn-hpq0)))
         (mv fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
    (1 (let ((fn-hpq1 (fn-hpb-begin epoch lease fn-hpq1)))
         (mv fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
    (2 (let ((fn-hpq2 (fn-hpb-begin epoch lease fn-hpq2)))
         (mv fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
    (3 (let ((fn-hpq3 (fn-hpb-begin epoch lease fn-hpq3)))
         (mv fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
    (otherwise (let ((fn-hpb (fn-hpb-begin epoch lease fn-hpb)))
                 (mv fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))))

(defun fn-hpi-written (c observation fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
  (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
  (let* ((effect (fn-omk-at 5 c))
         (word (fn-hpi-written-status effect observation))
         (buffer (fn-omk-at 0 (fn-omk-at 17 c)))
         (resume (fn-omk-at 1 (fn-omk-at 17 c)))
         (region (fn-omk-at 4 effect)))
    (cond
     ((not (eq (fn-omk-at 0 c) :wait-write))
      (mv :stale c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
     ((not (and (natp buffer) (< buffer 5)))
      (mv :recovery-required (fn-hpi-set 0 :recovery-required c)
          fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
     ((eq word :stale) (mv word c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
     ((eq word :recovery-required)
      (mv word (fn-hpi-set 0 :recovery-required c)
          fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
     (t
      (mv-let (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
        (fn-hpi-reset-buffer buffer (fn-omk-at 1 c) (fn-omk-at 2 c)
                             fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
        (let* ((generations (fn-omk-at 16 c))
               (c (fn-hpi-set 16 (fn-hpi-set buffer
                       (+ 1 (nfix (fn-omk-at buffer generations))) generations) c))
               (pages (fn-omk-at 15 c))
               (c (if (and (natp region) (< region 5))
                      (fn-hpi-set 15 (fn-hpi-set region
                          (+ 1 (nfix (fn-omk-at region pages))) pages) c) c))
               (c (fn-hpi-set 0 resume (fn-hpi-set 5 nil (fn-hpi-set 17 nil c)))))
          (mv :written c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))))))

(defun fn-hpi-region-used (region fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
  (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
  (case region (0 (fn-hpb-used fn-hpq0)) (1 (fn-hpb-used fn-hpq1))
               (2 (fn-hpb-used fn-hpq2)) (3 (fn-hpb-used fn-hpq3))
               (otherwise (fn-hpb-used fn-hpb))))

(defun fn-hpi-buffer-step (c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
  ; Internal dispatcher. The actual outer entry must check its live growth
  ; grant before calling this; it is not a host export or an admission bypass.
  (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
  (let* ((phase (fn-omk-at 0 c))
         (layout (fn-omk-at 1 (fn-omk-at 6 c))))
    (cond
     ((eq phase :zero)
      (mv-let (v fn-hpb) (fn-hpb-put 0 fn-hpb)
        (if (eq v :stored)
            (mv :continue nil c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
          (mv-let (word effect next) (fn-hpi-await-page :zero nil 0 4 :header c)
            (mv word effect next fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))))
     ((eq phase :header)
      (if (not (and (unsigned-byte-p 61 (fn-omk-at 7 c))
                    (unsigned-byte-p 64 (fn-omk-at 8 c))
                    (unsigned-byte-p 51 (fn-omk-at 9 c))
                    (unsigned-byte-p 51 (fn-omk-at 10 c))))
          (mv '(:refused :header-domain) nil (fn-hpi-set 0 :refused c)
              fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
        (mv-let (v fn-hpb)
          (fn-hch-tick (fn-omk-at 7 c) (fn-omk-at 8 c)
                       (fn-omk-at 9 c) (fn-omk-at 10 c) fn-hpb)
          (if (eq v :stored)
              (mv :continue nil c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
            (mv-let (word effect next)
              (fn-hpi-await-page :header 0 (nfix (fn-omk-at 4 layout)) 4 :body c)
              (mv word effect next fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))))))
     ((eq phase :body)
      (mv-let (v summary body fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
        (fn-hpcx-tick (fn-omk-at 14 c) fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
        (let ((c (fn-hpi-set 14 body c)))
          (cond
           ((fn-hsrcb-demandp v)
            (mv :need-byte v c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
           ((eq v :need-row)
            (let* ((token (fn-omk-at 6 body))
                   (expected (list (fn-omk-at 0 token) (fn-omk-at 1 token)
                                   (fn-omk-at 2 token) (fn-omk-at 2 body))))
              (mv :need-row (list :source-row expected) c
                  fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
           ((eq v :prepared)
            (mv :continue nil (fn-hpi-set 0 :pad (fn-hpi-set 18 0 c))
                fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
           ((eq v :page-full)
            (let ((region (if (null summary) 4 summary)))
              (if (not (and (natp region) (< region 5)))
                  (mv '(:refused :buffer-selector) nil (fn-hpi-set 0 :refused c)
                      fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
                (mv-let (word effect next) (fn-hpi-await-region region :body c)
                  (mv word effect next fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))))
           ((eq v :row-done)
            ; All four column effects, including column3, are installed.
            ; The provider may consume this exact row only at this ACK.
            (mv :row-done (list :row-emitted (fn-omk-at 6 body) summary) c
                fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
           ((member-eq v '(:continue :columns :column-stored))
            (mv :continue nil c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
           (t (mv v nil (fn-hpi-set 0 :refused c)
                  fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))))))
     ((eq phase :pad)
      (let ((region (fn-omk-at 18 c)))
        (cond
         ((not (and (natp region) (<= region 5)))
          (mv '(:refused :padding-region) nil (fn-hpi-set 0 :refused c)
              fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
         ((equal region 5)
          (mv :continue nil (fn-hpi-set 0 :data-digest-start c)
              fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
         (t
          (let ((page (nfix (fn-omk-at region (fn-omk-at 15 c))))
                (cap (fn-hpi-region-cap region c)))
            (cond
             ((< cap page)
              (mv '(:refused :region-overrun) nil (fn-hpi-set 0 :refused c)
                  fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
             ((equal page cap)
              (if (equal (fn-hpi-region-used region fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb) 0)
                  (mv :continue nil (fn-hpi-set 18 (+ 1 region) c)
                      fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
                (mv '(:refused :unwritten-region-tail) nil (fn-hpi-set 0 :refused c)
                    fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))
             (t
              (mv-let (v fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
                (fn-hpq-put region 0 fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
                (if (eq v :stored)
                    (mv :continue nil c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
                  (mv-let (word effect next) (fn-hpi-await-region region :pad c)
                    (mv word effect next fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))))))))))
     (t (mv :await-phase nil c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)))))

; The immutable receipt is compared with this controller's exact retained
; request, then checked against the actual ledger receipt on EVERY step.
(defun fn-hpi-grant-matchesp (c ledger)
  (declare (xargs :guard t))
  (let ((request (fn-hpi-growth-request c)) (grant (fn-omk-at 22 c)))
    (and (consp request)
         (equal grant (cons :checkpoint-funded (cdr request)))
         (fn-osj-grant-livep grant ledger))))

(defun fn-hpi-supply (c position byte fn-hpb)
  (declare (xargs :stobjs fn-hpb))
  (if (not (eq (fn-omk-at 0 c) :body))
      (mv '(:refused :not-awaiting-source-byte) c fn-hpb)
    (mv-let (word body fn-hpb)
      (fn-hpcx-supply (fn-omk-at 14 c) position byte fn-hpb)
      (mv word (if (eq word :continue) (fn-hpi-set 14 body c) c) fn-hpb))))

; Fixed-width response validation; even a malformed list costs at most64 cells.
(defun fn-hpi-octets-p (n bytes)
  (declare (xargs :guard t :measure (nfix n)))
  (cond ((not (and (natp n) (<= n 64))) nil)
        ((zp n) (null bytes))
        ((not (consp bytes)) nil)
        (t (and (fn-scc-octetp (car bytes))
                (fn-hpi-octets-p (1- n) (cdr bytes))))))

(defthm fn-hpi-octets-p-shape
  (implies (fn-hpi-octets-p n bytes)
           (and (true-listp bytes) (equal (len bytes) n)))
  :hints (("Goal" :induct (fn-hpi-octets-p n bytes)
           :in-theory (enable fn-hpi-octets-p))))

(defun fn-hpi-issue-io (tag kind ordinal offset length bytes wait c)
  (declare (xargs :guard t))
  (let* ((serial (nfix (fn-omk-at 4 c)))
         (generation (nfix (fn-omk-at 4 (fn-omk-at 16 c))))
         (effect (list tag (fn-omk-at 1 c) (fn-omk-at 3 c) serial kind ordinal
                       offset length generation bytes))
         (c (fn-hpi-set 0 wait (fn-hpi-set 4 (+ 1 serial)
                     (fn-hpi-set 5 effect c)))))
    (mv :io effect c)))

(defun fn-hpi-io-matchp (c observation tag width)
  (declare (xargs :guard t))
  (let ((effect (fn-omk-at 5 c)))
    (and (natp width) (fn-omk-widthp effect 10) (fn-omk-widthp observation width)
         (equal (fn-omk-at 0 observation) tag)
         (fn-omk-token-matchp (fn-omk-at 1 effect) (fn-omk-at 1 observation))
         (equal (fn-omk-at 2 effect) (fn-omk-at 2 observation))
         (equal (fn-omk-at 3 effect) (fn-omk-at 3 observation))
         (equal (fn-omk-at 4 effect) (fn-omk-at 4 observation))
         (equal (fn-omk-at 5 effect) (fn-omk-at 5 observation))
         (equal (fn-omk-at 8 effect) (fn-omk-at 6 observation))
         (member-eq (fn-omk-at 7 observation) '(:ok :uncertain :refused)))))

(defun fn-hpi-digest-validp (total c pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :guard t))
  (and (natp total)
       (equal (pgs-dc-total pgs-digest-state) (ceiling total 8))
       (<= (pgs-dc-start pgs-digest-state) (pgs-dc-pos pgs-digest-state))
       (<= (pgs-dc-pos pgs-digest-state) (pgs-dc-end pgs-digest-state))
       (<= (pgs-dc-end pgs-digest-state) (pgs-dc-total pgs-digest-state))
       (<= (* 8 (pgs-dc-pos pgs-digest-state)) total)
       (equal (pgs-dc-capture pgs-digest-state) (fn-omk-at 1 c))
       (equal (pgs-dc-lease pgs-digest-state) (fn-omk-at 2 c))))

; Digest exact bytes previously acknowledged in this private stage. Directory
; hashing spans ALL M pages; its root record names N data pages, not M.
(defun fn-hpi-digest-begin (kind index c pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :guard t))
  (let* ((layout (fn-omk-at 1 (fn-omk-at 6 c)))
         (physical (cond ((eq kind :data) (+ (nfix (fn-omk-at 4 layout)) (nfix index)))
                         ((eq kind :table) (+ (nfix (fn-omk-at 5 layout)) (nfix index)))
                         (t 1)))
         (total (if (eq kind :directory) (* 16384 (nfix (fn-omk-at 3 layout))) 16384))
         (base (+ 16384 (* 16384 physical))))
    (if (not (and (natp index)
                  (case kind (:data (< index (nfix (fn-omk-at 1 layout))))
                             (:table (< index (nfix (fn-omk-at 2 layout))))
                             (:directory (and (equal index 0) (< 0 total)))
                             (otherwise nil))))
        (mv '(:refused :digest-coordinate) (fn-hpi-set 0 :refused c) pgs-digest-state)
      (let* ((pgs-digest-state (pgs-dcb-begin 0 base total (fn-omk-at 1 c)
                                             (fn-omk-at 2 c) pgs-digest-state))
             (c (fn-hpi-set 20 (list kind index total base) (fn-hpi-set 0 :digest c))))
        (mv :continue c pgs-digest-state)))))

; Metadata state: kind, global ordinal, component, remaining words, entry
; limit, physical single base, page index. Each table stops at341 entries;
; its two trailing words are zero even if another table follows.
(defun fn-hpi-meta-begin (kind page c)
  (declare (xargs :guard t))
  (let* ((layout (fn-omk-at 1 (fn-omk-at 6 c)))
         (n (nfix (fn-omk-at 1 layout))) (nt (nfix (fn-omk-at 2 layout)))
         (m (nfix (fn-omk-at 3 layout)))
         (metadata (if (eq kind :table)
                       (list :table (* 341 (nfix page)) 0 2048
                             (min n (* 341 (+ 1 (nfix page))))
                             (nfix (fn-omk-at 4 layout)) (nfix page))
                     (list :directory 0 0 (* 2048 m) nt
                           (nfix (fn-omk-at 5 layout)) 0))))
    (fn-hpi-set 19 metadata (fn-hpi-set 21 nil (fn-hpi-set 0 :metadata c)))))

(defun fn-hpi-after-spool (c pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :guard t))
  (let* ((d (fn-omk-at 20 c)) (kind (fn-omk-at 0 d)) (index (nfix (fn-omk-at 1 d)))
         (layout (fn-omk-at 1 (fn-omk-at 6 c))))
    (cond
     ((eq kind :data)
      (if (< (+ 1 index) (nfix (fn-omk-at 1 layout)))
          (fn-hpi-digest-begin :data (+ 1 index) c pgs-digest-state)
        (mv :continue (fn-hpi-meta-begin :table 0 c) pgs-digest-state)))
     ((eq kind :table)
      (mv :continue (fn-hpi-meta-begin
                      (if (< (+ 1 index) (nfix (fn-omk-at 2 layout))) :table :directory)
                      (+ 1 index) c) pgs-digest-state))
     (t (mv '(:refused :spool-coordinate) (fn-hpi-set 0 :refused c) pgs-digest-state)))))

(defun fn-hpi-metadata-step (c fn-hpb)
  (declare (xargs :stobjs fn-hpb :verify-guards nil))
  (let* ((meta (fn-omk-at 19 c)) (kind (fn-omk-at 0 meta))
         (ordinal (fn-omk-at 1 meta)) (component (fn-omk-at 2 meta))
         (remaining (fn-omk-at 3 meta)) (entries (fn-omk-at 4 meta))
         (base (fn-omk-at 5 meta)) (page (fn-omk-at 6 meta))
         (cache (fn-omk-at 21 c))
         (cached (and (fn-omk-widthp cache 3) (eq (fn-omk-at 0 cache) :digest)
                      (equal ordinal (fn-omk-at 1 cache))
                      (unsigned-byte-p 256 (fn-omk-at 2 cache))))
         (layout (fn-omk-at 1 (fn-omk-at 6 c))))
    (cond
     ((not (and (member-eq kind '(:table :directory))
                (unsigned-byte-p 64 ordinal) (natp component) (< component 6)
                (unsigned-byte-p 64 remaining) (unsigned-byte-p 64 entries)
                (unsigned-byte-p 64 base) (natp page)
                (< page (nfix (fn-omk-at (if (eq kind :table) 2 3) layout)))))
      (mv '(:refused :metadata-coordinate) nil (fn-hpi-set 0 :refused c) fn-hpb))
     ((fn-hpb-ready fn-hpb)
      (let* ((physical (if (eq kind :table) (+ (nfix (fn-omk-at 5 layout)) page) (+ 1 page)))
             (resume (if (eq kind :table) :table-digest-start
                       (if (zp remaining) :directory-digest-start :metadata)))
             (c (if (eq kind :directory)
                    (fn-hpi-set 19 (fn-hpi-set 6 (+ 1 page) meta) c) c)))
        (mv-let (v effect next) (fn-hpi-await-page kind page physical 4 resume c)
          (mv v effect next fn-hpb))))
     ((zp remaining)
      (mv '(:refused :partial-metadata-page) nil (fn-hpi-set 0 :refused c) fn-hpb))
     ((and (< ordinal entries) (not cached))
      (mv-let (word effect next)
        (fn-hpi-issue-io :read-spool (if (eq kind :table) :data :table)
                         ordinal (* 32 ordinal) 32 nil :wait-spool-read c)
        (mv word effect next fn-hpb)))
     (t
      (mv-let (v ordinal2 component2 remaining2 fn-hpb)
        (fn-hpm-tick ordinal component remaining entries base
                    (if cached (fn-omk-at 2 cache) 0) fn-hpb)
        (if (eq v :stored)
            (mv :continue nil
                (fn-hpi-set 19 (list kind ordinal2 component2 remaining2 entries base page) c)
                fn-hpb)
          (mv (list :refused v) nil (fn-hpi-set 0 :refused c) fn-hpb)))))))

(verify-guards fn-hpi-metadata-step)

(defun fn-hpi-stream-step (c observation fn-hpb pgs-digest-state)
  (declare (xargs :stobjs (fn-hpb pgs-digest-state) :verify-guards nil))
  (let* ((phase (fn-omk-at 0 c)) (d (fn-omk-at 20 c))
         (kind (fn-omk-at 0 d)) (index (nfix (fn-omk-at 1 d)))
         (total (nfix (fn-omk-at 2 d))) (base (nfix (fn-omk-at 3 d))))
    (cond
     ((member-eq phase '(:data-digest-start :table-digest-start :directory-digest-start))
      (mv-let (v next pgs-digest-state)
        (fn-hpi-digest-begin
          (case phase (:data-digest-start :data) (:table-digest-start :table)
                      (otherwise :directory))
          (if (eq phase :table-digest-start) (nfix (fn-omk-at 6 (fn-omk-at 19 c))) 0)
          c pgs-digest-state)
        (mv v nil next fn-hpb pgs-digest-state)))
     ((eq phase :metadata)
      (mv-let (v effect next fn-hpb) (fn-hpi-metadata-step c fn-hpb)
        (mv v effect next fn-hpb pgs-digest-state)))
     ((eq phase :wait-spool-read)
      (let ((effect (fn-omk-at 5 c)))
        (cond
         ((not (fn-hpi-io-matchp c observation :spool-read 9))
          (mv :stale nil c fn-hpb pgs-digest-state))
         ((not (eq (fn-omk-at 7 observation) :ok))
          (mv (fn-omk-at 7 observation) nil
              (fn-hpi-set 0 (if (eq (fn-omk-at 7 observation) :uncertain)
                                :recovery-required :refused) c) fn-hpb pgs-digest-state))
         ((not (and (equal (fn-omk-at 7 effect) 32)
                    (fn-hpi-octets-p 32 (fn-omk-at 8 observation))))
          (mv '(:refused :spool-response) nil (fn-hpi-set 0 :refused c) fn-hpb pgs-digest-state))
         (t (mv :continue nil
                (fn-hpi-set 0 :metadata (fn-hpi-set 5 nil
                  (fn-hpi-set 21 (list :digest (fn-omk-at 5 effect)
                                      (pgs-octets-be-nat (fn-omk-at 8 observation))) c)))
                fn-hpb pgs-digest-state)))))
     ((eq phase :wait-spool-write)
      (cond
       ((not (fn-hpi-io-matchp c observation :spool-written 8))
        (mv :stale nil c fn-hpb pgs-digest-state))
       ((not (eq (fn-omk-at 7 observation) :ok))
        (mv (fn-omk-at 7 observation) nil
            (fn-hpi-set 0 (if (eq (fn-omk-at 7 observation) :uncertain)
                              :recovery-required :refused) c) fn-hpb pgs-digest-state))
       (t (mv-let (v next pgs-digest-state)
            (fn-hpi-after-spool (fn-hpi-set 5 nil c) pgs-digest-state)
            (mv v nil next fn-hpb pgs-digest-state)))))
     ((eq phase :wait-stage-read)
      (let ((effect (fn-omk-at 5 c)))
        (cond
         ((not (fn-hpi-io-matchp c observation :image-read 9))
          (mv :stale nil c fn-hpb pgs-digest-state))
         ((not (eq (fn-omk-at 7 observation) :ok))
          (mv (fn-omk-at 7 observation) nil
              (fn-hpi-set 0 (if (eq (fn-omk-at 7 observation) :uncertain)
                                :recovery-required :refused) c) fn-hpb pgs-digest-state))
         ((not (and (fn-hpi-octets-p (fn-omk-at 7 effect) (fn-omk-at 8 observation))
                    (fn-hpi-digest-validp total c pgs-digest-state)))
          (mv '(:refused :stage-response) nil (fn-hpi-set 0 :refused c) fn-hpb pgs-digest-state))
         (t
          (let ((block (fn-b3-words 16 (append (fn-omk-at 8 observation)
                                    (adt-zeros (nfix (- 64 (nfix (fn-omk-at 7 effect)))))))))
            (mv-let (v pgs-digest-state) (pgs-dcb-step total block pgs-digest-state)
              (mv (if (member-eq v '(:continue :done)) :continue (list :refused v)) nil
                  (fn-hpi-set 0 (if (member-eq v '(:continue :done)) :digest :refused)
                              (fn-hpi-set 5 nil c)) fn-hpb pgs-digest-state)))))))
     ((eq phase :digest)
      (cond
       ((not (fn-hpi-digest-validp total c pgs-digest-state))
        (mv '(:refused :digest-state) nil (fn-hpi-set 0 :refused c) fn-hpb pgs-digest-state))
       ((eq (pgs-dc-mode pgs-digest-state) :done)
        (let ((bytes (pgs-dcb-result-octets pgs-digest-state)))
          (if (eq kind :directory)
              (let* ((layout (fn-omk-at 1 (fn-omk-at 6 c)))
                     (root (pgs-make-rec 1 1 (fn-omk-at 1 layout) (pgs-octets-be-nat bytes)))
                     (terminal (list :image-complete (fn-omk-at 1 c) (fn-omk-at 3 c)
                                     (fn-omk-at 11 c) (fn-omk-at 12 c) (fn-omk-at 7 c)
                                     (fn-omk-at 13 c) root (fn-omk-at 2 (fn-omk-at 6 c)))))
                (mv :prepared terminal (fn-hpi-set 24 terminal (fn-hpi-set 0 :prepared c))
                    fn-hpb pgs-digest-state))
            (mv-let (v effect next)
              (fn-hpi-issue-io :write-spool kind index (* 32 index) 32 bytes :wait-spool-write c)
              (mv v effect next fn-hpb pgs-digest-state)))))
       ((< 0 (pgs-dcb-read-demand total pgs-digest-state))
        (mv-let (v effect next)
          (fn-hpi-issue-io :read-stage kind index
                           (+ base (pgs-dcb-next-byte-offset pgs-digest-state))
                           (pgs-dcb-read-demand total pgs-digest-state) nil :wait-stage-read c)
          (mv v effect next fn-hpb pgs-digest-state)))
       (t (mv-let (v pgs-digest-state) (pgs-dcb-step total nil pgs-digest-state)
            (mv (if (member-eq v '(:continue :done)) :continue (list :refused v)) nil
                (if (member-eq v '(:continue :done)) c (fn-hpi-set 0 :refused c))
                fn-hpb pgs-digest-state)))))
     ((eq phase :prepared) (mv :prepared (fn-omk-at 24 c) c fn-hpb pgs-digest-state))
     (t (mv '(:refused :writer-phase) nil (fn-hpi-set 0 :refused c) fn-hpb pgs-digest-state)))))

(verify-guards fn-hpi-stream-step
  :hints (("Goal" :in-theory (enable pgs-dcb-word-count))))

(defun fn-hpi-tick (c observation ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
  (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state) :verify-guards nil))
  (let ((phase (fn-omk-at 0 c)))
    (cond
     ((not (fn-omk-widthp c 25))
      (mv '(:refused :image-cursor) nil c ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))
     ((eq phase :need-growth)
      (mv-let (grant ledger)
        (fn-osj-grow ledger (fn-omk-at 2 c) (fn-omk-at 1 c) (fn-omk-at 3 c)
                     (fn-hpi-growth-request c))
        (if (not (eq (fn-omk-at 0 grant) :checkpoint-funded))
            (mv grant nil c ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)
          (let* ((c (fn-hpi-set 22 grant c))
                 (source (fn-omk-at 1 c)) (maintenance (fn-omk-at 2 c)))
            (mv-let (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
              (fn-hpi-reset-buffer 0 source maintenance fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
              (mv-let (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
                (fn-hpi-reset-buffer 1 source maintenance fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
                (mv-let (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
                  (fn-hpi-reset-buffer 2 source maintenance fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
                  (mv-let (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
                    (fn-hpi-reset-buffer 3 source maintenance fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
                    (mv-let (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
                      (fn-hpi-reset-buffer 4 source maintenance fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
                      (mv :funded (fn-hpi-growth-request c) (fn-hpi-set 0 :zero c) ledger
                          fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))))))))))
     ((member-eq phase '(:refused :recovery-required))
      (mv phase nil c ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))
     ((not (fn-hpi-grant-matchesp c ledger))
      (mv '(:refused :image-growth-receipt) nil c ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))
     ((eq phase :wait-write)
      (mv-let (word next fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
        (fn-hpi-written c observation fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
        (mv word nil next ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
     ((and (eq phase :body) (fn-omk-widthp observation 3)
           (eq (fn-omk-at 0 observation) :supply))
      (mv-let (word next fn-hpb)
        (fn-hpi-supply c (fn-omk-at 1 observation) (fn-omk-at 2 observation) fn-hpb)
        (mv word nil next ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
     ((member-eq phase '(:zero :header :body :pad))
      (mv-let (word effect next fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
        (fn-hpi-buffer-step c fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb)
        (mv word effect next ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state)))
     (t
      (mv-let (word effect next fn-hpb pgs-digest-state)
        (fn-hpi-stream-step c observation fn-hpb pgs-digest-state)
        (mv word effect next ledger fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb pgs-digest-state))))))

(verify-guards fn-hpi-tick)
