; Actual SAME registered controller/RH step. Missing source/constructor/runtime
; remains unavailable. Original plan stays in immutable custody root8.
(in-package "ACL2")
(include-book "index-range-render-output")
; Exact readonly custody predicate is owned by the reader packet.
(include-book "index-reader-render-ready")

; Fixed registered scalar fence, shared by all phase actions below. This is
; not the captured-row semantic authority or installed runtime allowance.
(defun fn-ibr-joint-segment-source-fence-p
 (token fn-ibp-query-segment fn-query-payload-grants)
 (declare (xargs :stobjs (fn-ibp-query-segment fn-query-payload-grants)
                 :guard (fn-ibp-query-tokenp token)))
 (and (fn-ibp-query-slot-livep token fn-ibp-query-segment)
  (let* ((slot (nth 3 token))
         (control (fn-ibp-qs-controlsi slot fn-ibp-query-segment))
         (capture (fn-ibp-qs-capturesi slot fn-ibp-query-segment))
         (context (fn-ibp-qs-inputsi slot fn-ibp-query-segment))
         (payload (fn-omk-at 5 context))
         (admission (fn-ibp-qs-admissionsi slot fn-ibp-query-segment))
         (claim (fn-omk-at 0 admission))
         (pin (fn-spp-at 5 control))
         (publication (fn-spp-at 2 pin)))
   (and (and (eq (fn-spp-at 0 control) :fn-ibr)
                 (equal (fn-spp-at 1 control) (nth 1 token))
                 (equal (fn-spp-at 2 control) (nth 4 token))
                 (eq (fn-spp-at 0 pin) :publication-pin)
                 (equal (fn-ipub-generation publication) (nth 4 token))
                 (equal (fn-ipub-table-id publication) (fn-ibp-capture-table-root-id capture))
                 (equal (fn-ipub-row-id publication) (fn-ibp-capture-row-root-id capture))
                 (equal (fn-ipub-count publication) (fn-ibp-capture-count capture))
                 (equal (fn-ipub-frontier publication) (fn-ibp-capture-frontier capture))
                 (eq (fn-omk-at 2 admission) :active)
                 (fn-omk-widthp claim 12)
                 (eq (fn-omk-at 0 claim) :query-grant)
                 (equal (fn-omk-at 1 claim) (nth 1 token))
                 (equal (fn-omk-at 2 claim) (nth 2 token))
                 (equal (fn-omk-at 3 claim) slot)
                 (equal (fn-omk-at 4 claim) (nth 4 token))
                 (equal (fn-omk-at 5 claim) (fn-ibp-capture-table-root-id capture))
                 (equal (fn-omk-at 6 claim) (fn-ibp-capture-row-root-id capture))
                 (equal (fn-omk-at 7 claim) (fn-ibp-capture-count capture))
                 (equal (fn-omk-at 8 claim) (fn-ibp-capture-frontier capture))
                 (equal (fn-omk-at 9 claim) (nth 4 token))
                 (fn-qpg-livep payload fn-query-payload-grants)
                 (equal (fn-omk-at 1 payload) (nth 1 token))
                 (equal (fn-omk-at 2 payload) slot)
                 (equal (fn-omk-at 3 payload) (nth 4 token))
                 (equal (fn-omk-at 6 payload) (nth 2 token))
                 (equal (fn-omk-at 10 claim) (fn-omk-at 4 payload))
                 (equal (fn-omk-at 11 claim) (fn-omk-at 5 payload)))
    (let ((payload-row (fn-qpg-rowsi (fn-qpg-slot payload) fn-query-payload-grants)))
      (and (eq (fn-omk-at 2 payload-row) :active)
           (equal (fn-omk-at 1 payload-row) claim)))))))

; Current plan only; the immutable initial actor root remains in QSinputs.
(defun fn-ibr-with-current-plan (control plan)
 (declare (xargs :guard t))
 (fn-ibr-make (fn-spp-at 1 control) (fn-spp-at 2 control)
              (fn-spp-at 3 control) plan (fn-spp-at 5 control)
              (fn-spp-at 6 control) (fn-spp-at 7 control) (fn-spp-at 8 control)))

; Proof/caller carry only: the runtime never computes this whole relation.
(defun fn-ibr-dispatch-domain-p (fn-render-holder fn-ibp-query-segment fn-arena)
 (declare (xargs :stobjs (fn-render-holder fn-ibp-query-segment fn-arena) :guard t))
 (implies (fn-rh-live fn-render-holder)
  (let ((token (fn-rh-query fn-render-holder)))
   (and (fn-ibp-query-tokenp token)
    (implies (fn-ibp-query-slot-livep token fn-ibp-query-segment)
     (let ((control (fn-ibp-qs-controlsi (nth 3 token) fn-ibp-query-segment)))
      (and (equal (fn-rh-plan fn-render-holder) (fn-spp-at 4 control))
       (case (fn-spp-at 3 control)
        (:group (fn-gns-group-cursorp (fn-spp-at 6 control)))
        (:number (and (fn-gns-number-cursorp (fn-spp-at 7 control))
                      (true-listp (fn-spp-at 1 (fn-spp-at 8 control)))))
        (:held (fn-ibr-held-current-ready-p control fn-arena))
        (otherwise t)))))))))

; Exactly one literal reply octet, represented by a scalar MV (not a new
; whole reply). Invalid current octet retains all source and plan aliases.
(defun fn-ibr-literal-reply-one (plan)
 (declare (xargs :guard t))
 (let* ((current (fn-spp-cur plan)) (currentp (consp current))
        (cur (if currentp current (fn-srb-effect-octets (fn-ag-car (fn-spp-rest plan)))))
        (tail (if currentp (fn-spp-rest plan) (fn-ag-cdr (fn-spp-rest plan)))))
  (if (not (and (eq (fn-spp-status plan) :reply)
                (consp cur) (fn-cbor-octetp (fn-ag-car cur))))
      (mv :invalid-reply nil plan)
    (mv :reply-byte (fn-ag-car cur)
        (fn-spp-save-active plan (cons (fn-ag-cdr cur) tail))))))

; Internal SAME-child dispatch. Public host route must borrow both actual
; registered children from MIO and derive its token from RH, never supply a
; control/plan/source tuple. Missing row issuer or runtime/factory stays open.
(defun fn-ibr-joint-segment-render-one
 (capacity fn-render-holder fn-ibp-query-segment fn-query-payload-grants fn-arena fn-octets)
 (declare (xargs :stobjs (fn-render-holder fn-ibp-query-segment fn-query-payload-grants fn-arena fn-octets)
  :guard (and (natp capacity)
               (fn-ibr-dispatch-domain-p fn-render-holder fn-ibp-query-segment fn-arena))
  :verify-guards nil))
 (if (not (fn-rh-live fn-render-holder))
     (mv :unavailable fn-render-holder fn-ibp-query-segment fn-octets)
  (let ((token (fn-rh-query fn-render-holder)))
   (if (not (and (fn-irc-slot-render-ready-p token fn-ibp-query-segment fn-render-holder)
                 (fn-ibr-joint-segment-source-fence-p token fn-ibp-query-segment fn-query-payload-grants)))
       (mv :unavailable-render-custody fn-render-holder fn-ibp-query-segment fn-octets)
    (let* ((slot (nth 3 token))
           (control (fn-ibp-qs-controlsi slot fn-ibp-query-segment))
           (plan (fn-spp-at 4 control)) (phase (fn-spp-at 3 control)))
     (cond
      ((eq phase :held)
       (if (<= capacity (fn-octets-len fn-octets))
           (mv :output-full fn-render-holder fn-ibp-query-segment fn-octets)
        ; The outer joint fence already selected this exact QS/QPG source.
        ; Do not repeat that fence or allocate a second demand tuple here.
        (mv-let (out word next) (fn-ibr-held-one control fn-arena)
         (let* ((fn-octets (fn-octets-append-list out fn-octets))
                (fn-ibp-query-segment
                  (if (eq word :recovery-required) fn-ibp-query-segment
                   (update-fn-ibp-qs-controlsi slot next fn-ibp-query-segment))))
          (mv word fn-render-holder fn-ibp-query-segment fn-octets)))))
      ((and (eq phase :position) (eq (fn-spp-status plan) :reply))
       (if (<= capacity (fn-octets-len fn-octets))
           (mv :output-full fn-render-holder fn-ibp-query-segment fn-octets)
        (mv-let (word byte next-plan) (fn-ibr-literal-reply-one plan)
         (if (not (eq word :reply-byte))
             (mv word fn-render-holder fn-ibp-query-segment fn-octets)
          (let* ((fn-octets (fn-octets-append-octet byte fn-octets))
                 (fn-render-holder (update-fn-rh-plan next-plan fn-render-holder))
                 (fn-ibp-query-segment (update-fn-ibp-qs-controlsi slot
                    (fn-ibr-with-current-plan control next-plan) fn-ibp-query-segment)))
           (mv :reply-byte fn-render-holder fn-ibp-query-segment fn-octets))))))
      (t
       (mv-let (word next)
        (cond
         ((eq phase :group) (mv :group (fn-ibr-group-one control)))
         ((eq phase :number) (mv :number (fn-ibr-number-one control)))
         ((eq phase :terminal) (fn-ibr-terminal-prepare control))
         ((and (eq phase :position) (eq (fn-spp-status plan) :cursor))
          (fn-ibr-number-source-begin control))
         ((and (eq phase :position) (eq (fn-spp-status plan) :position))
          (mv :position (fn-ibr-with-current-plan control (fn-spp-one plan))))
         ((and (eq phase :position) (eq (fn-spp-status plan) :done))
          (mv :done control))
         ((eq phase :row) (mv :row-read-required control))
         (t (mv :unavailable-phase control)))
        (let* ((fn-render-holder (update-fn-rh-plan (fn-spp-at 4 next) fn-render-holder))
               (fn-ibp-query-segment (update-fn-ibp-qs-controlsi slot next fn-ibp-query-segment)))
         (mv word fn-render-holder fn-ibp-query-segment fn-octets))))))))))

(defthm fn-ibr-literal-reply-one-scalar-octet
 (implies (eq (mv-nth 0 (fn-ibr-literal-reply-one plan)) :reply-byte)
          (fn-cbor-octetp (mv-nth 1 (fn-ibr-literal-reply-one plan))))
 :rule-classes nil
 :hints (("Goal" :in-theory
  (e/d (fn-ibr-literal-reply-one) (fn-spp-status fn-spp-save-active fn-cbor-octetp)))))

(local
 (defthm fn-ibr-joint-source-fence-live-by-definition
  (implies (fn-ibr-joint-segment-source-fence-p token fn-ibp-query-segment fn-query-payload-grants)
           (fn-ibp-query-slot-livep token fn-ibp-query-segment))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
   :in-theory (e/d (fn-ibr-joint-segment-source-fence-p)
                    (fn-ibp-query-slot-livep fn-qpg-livep fn-qpg-rowsi
                     fn-ipub-generation fn-ipub-count fn-ipub-frontier
                     fn-ibp-capture-table-root-id fn-ibp-capture-row-root-id))))))

(verify-guards fn-ibr-joint-segment-render-one
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-ibr-joint-source-fence-live-by-definition
          (token (fn-rh-query fn-render-holder)))
        (:instance fn-ibr-held-one-output-octets
           (control (fn-ibp-qs-controlsi (nth 3 (fn-rh-query fn-render-holder)) fn-ibp-query-segment)))
        (:instance fn-ibr-literal-reply-one-scalar-octet
          (plan (fn-spp-at 4 (fn-ibp-qs-controlsi
                   (nth 3 (fn-rh-query fn-render-holder)) fn-ibp-query-segment)))))
  :in-theory (e/d (fn-ibr-dispatch-domain-p fn-ibp-query-tokenp)
   (fn-irc-slot-render-ready-p fn-ibr-joint-segment-source-fence-p fn-ibr-held-one
    fn-ibr-joint-segment-held-output-one fn-ibr-literal-reply-one
    fn-ibr-group-one fn-ibr-number-one fn-ibr-number-source-begin
    fn-ibr-terminal-prepare fn-ibr-with-current-plan
    fn-ibr-held-current-ready-p fn-gns-group-cursorp fn-gns-number-cursorp
    fn-spp-status fn-spp-one fn-spp-at fn-rh-plan fn-rh-query fn-rh-live)))))


(local
 (defthm fn-ibr-held-one-plan-frame-by-definition
  (equal (fn-spp-at 4 (mv-nth 2 (fn-ibr-held-one control fn-arena)))
         (fn-spp-at 4 control))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
   :in-theory (e/d (fn-ibr-held-one fn-ibr-restate fn-ibr-make fn-spp-at fn-ag-car fn-ag-cdr)
    (fn-osh-one fn-gns-number-begin fn-gns-group-selected-result fn-ibr-work fn-ipub-count))))))

(defthm fn-ibr-render-one-retains-custody-and-owner-identities
 (let* ((answer (fn-ibr-joint-segment-render-one capacity fn-render-holder fn-ibp-query-segment
                 fn-query-payload-grants fn-arena fn-octets))
        (rh (mv-nth 1 answer)) (qs (mv-nth 2 answer)))
  (and (equal (fn-rh-live rh) (fn-rh-live fn-render-holder))
       (equal (fn-rh-pin rh) (fn-rh-pin fn-render-holder))
       (equal (fn-rh-query rh) (fn-rh-query fn-render-holder))
       (equal (fn-rh-resource rh) (fn-rh-resource fn-render-holder))
       (equal (fn-rh-origin rh) (fn-rh-origin fn-render-holder))
       (equal (fn-ibp-qs-inputsi index qs) (fn-ibp-qs-inputsi index fn-ibp-query-segment))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-ibr-joint-segment-render-one update-fn-rh-plan
                   fn-rh-live fn-rh-pin fn-rh-query fn-rh-resource fn-rh-origin
                   update-fn-ibp-qs-controlsi fn-ibp-qs-inputsi)
   (fn-irc-slot-render-ready-p fn-ibr-joint-segment-source-fence-p
    fn-ibr-held-one fn-ibr-literal-reply-one fn-ibr-with-current-plan
    fn-ibr-group-one fn-ibr-number-one fn-ibr-number-source-begin
    fn-ibr-terminal-prepare fn-spp-status fn-spp-one fn-octets-append-list
    fn-octets-append-octet fn-octets-len)))))

(defthm fn-ibr-render-one-preserves-paired-current-plan
 (implies (and (fn-rh-live fn-render-holder)
               (fn-ibp-query-slot-livep (fn-rh-query fn-render-holder) fn-ibp-query-segment)
               (fn-ibr-dispatch-domain-p fn-render-holder fn-ibp-query-segment fn-arena))
  (let* ((answer (fn-ibr-joint-segment-render-one capacity fn-render-holder fn-ibp-query-segment
                 fn-query-payload-grants fn-arena fn-octets))
         (rh (mv-nth 1 answer)) (qs (mv-nth 2 answer)))
   (equal (fn-rh-plan rh)
          (fn-spp-at 4 (fn-ibp-qs-controlsi (nth 3 (fn-rh-query rh)) qs)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-ibr-held-one-plan-frame-by-definition
          (control (fn-ibp-qs-controlsi (nth 3 (fn-rh-query fn-render-holder)) fn-ibp-query-segment))))
  :in-theory (e/d (fn-ibr-joint-segment-render-one fn-ibr-dispatch-domain-p
                   update-fn-rh-plan fn-rh-plan fn-rh-query fn-rh-live
                   update-fn-ibp-qs-controlsi fn-ibp-qs-controlsi fn-ibr-with-current-plan
                   fn-ibr-make fn-spp-at fn-ag-car fn-ag-cdr)
    (fn-irc-slot-render-ready-p fn-ibr-joint-segment-source-fence-p
     fn-ibr-held-one fn-ibr-literal-reply-one fn-ibr-group-one fn-ibr-number-one
     fn-ibr-number-source-begin fn-ibr-terminal-prepare fn-spp-status fn-spp-one
     fn-octets-append-list fn-octets-append-octet fn-octets-len fn-ibp-query-slot-livep
     fn-ibp-query-tokenp fn-gns-group-cursorp fn-gns-number-cursorp
     fn-ibr-held-current-ready-p)))))
