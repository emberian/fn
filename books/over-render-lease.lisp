; OVER's executor model over the runtime-contract pool lease.
; Model of sending pool windows and reclaiming the lease on completion.
(in-package "ACL2")
(include-book "over-render-quantum")
(include-book "over-render-bound")
(include-book "over-render-capl")
(include-book "runtime-contract-host-lease")
(include-book "runtime-contract-host-lease-run")

(defun fn-ovr-lease-quantum (cur w h id inc fn-rtc-st fn-arena fn-cat)
  (declare (xargs :stobjs (fn-rtc-st fn-arena fn-cat) :verify-guards nil))
  (let ((cfg (fn-rtc-st-config fn-rtc-st)))
    (if (and (natp h) (< h (fn-rtc-nbufs cfg))
             (equal (fn-rtc-st-owner h fn-rtc-st) (list :workspace id inc))
             (fn-rtc-x-live-p id inc fn-rtc-st)
             (not (fn-rtc-kind-out-p :send id inc (fn-rtc-st-uses fn-rtc-st))))
        (let ((g (fn-rtc-st-gen h fn-rtc-st))
              (op (fn-rtc-st-next-op fn-rtc-st)))
          (mv-let (n next j fn-rtc-st)
            (fn-ovr-quantum cur w h 0 (fn-rtc-buf-cap h cfg) fn-rtc-st fn-arena fn-cat)
            (if (and (posp n) (< 0 j))
                (mv-let (fn-rtc-st acts refused cost)
                  (fn-rtc-x-request (list :submit :send (list h g 0 j) nil) id inc fn-rtc-st)
                  (declare (ignore acts cost))
                  (mv n next j (if refused nil op) fn-rtc-st))
              (mv n next j nil fn-rtc-st))))
      (mv 0 cur 0 nil fn-rtc-st))))

(defun fn-ovr-st-view (h i j fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :verify-guards nil :measure (nfix (- (nfix j) (nfix i)))))
  (if (and (natp i) (< i (nfix j)))
      (cons (fn-rtc-st-byte h i fn-rtc-st) (fn-ovr-st-view h (+ 1 i) j fn-rtc-st))
    nil))

(local (in-theory (fn-dss-measure-theory)))

(defun fn-ovr-lease-run (cur w k h id inc fn-rtc-st fn-arena fn-cat)
  (declare (xargs :stobjs (fn-rtc-st fn-arena fn-cat) :verify-guards nil :measure (nfix k)))
  (if (not (consp cur))
      (mv t nil fn-rtc-st)
    (if (zp k)
        (mv nil nil fn-rtc-st)
      (mv-let (n next j op fn-rtc-st) (fn-ovr-lease-quantum cur w h id inc fn-rtc-st fn-arena fn-cat)
        (if (not (posp n))
            (mv nil nil fn-rtc-st)
          (let ((sent (if op (fn-ovr-st-view h 0 j fn-rtc-st) nil)))
            (mv-let (fn-rtc-st left)
              (if op (fn-hld-sent id inc op (list :done j) fn-rtc-st) (mv fn-rtc-st nil))
              (declare (ignore left))
              (if (null next)
                  (mv t sent fn-rtc-st)
                (mv-let (okp rest fn-rtc-st) (fn-ovr-lease-run next w (- k 1) h id inc fn-rtc-st fn-arena fn-cat)
                  (mv okp (append sent rest) fn-rtc-st))))))))))

(defun fn-ovr-lease-run-quanta (cur w k h id inc fn-rtc-st fn-arena fn-cat)
  (declare (xargs :stobjs (fn-rtc-st fn-arena fn-cat) :verify-guards nil :measure (nfix k)))
  (if (or (not (consp cur)) (zp k))
      (mv 0 fn-rtc-st)
    (mv-let (n next j op fn-rtc-st) (fn-ovr-lease-quantum cur w h id inc fn-rtc-st fn-arena fn-cat)
      (if (not (posp n))
          (mv 1 fn-rtc-st)
        (mv-let (fn-rtc-st left)
          (if op (fn-hld-sent id inc op (list :done j) fn-rtc-st) (mv fn-rtc-st nil))
          (declare (ignore left))
          (if (null next)
              (mv 1 fn-rtc-st)
            (mv-let (m fn-rtc-st)
              (fn-ovr-lease-run-quanta next w (- k 1) h id inc fn-rtc-st fn-arena fn-cat)
              (mv (+ 1 m) fn-rtc-st))))))))

(defthm fn-ovr-leased-quantum-sends-the-step
  (implies (and (fn-ovw-cursorp cur)
                (fn-hl-render-ready-p h id inc s) (fn-rtc-live-p id inc s)
                (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses s))))
           (mv-let (n next j s2) (fn-ovr-quantum cur w h 0 limit s fn-arena fn-cat)
             (declare (ignore next s2))
             (let ((out (mv-nth 0 (fn-ovw-step cur n fn-arena fn-cat))))
               (implies (and (posp n) (< 0 j)
                             (fn-rtc-st$corr c (fn-hl-quantum-state h out id inc s)))
                        (and (member-equal (list :send id inc (fn-rtc-next-op s)
                                                 (list h (fn-rtc-get 0 (fn-rtc-buffer h s)) 0 j))
                                           (fn-rtc-uses (fn-hl-quantum-state h out id inc s)))
                             (equal (fn-rtc-c-octets (fn-rtc-buf-base h (fn-rtc-config s)) j
                                                     (nth *fn-rtc-c-bytesi* c))
                                    out)))))))

; Invariant and metadata proofs follow the window/write composition.
(local (defthm fn-ovrlp-splice-mstates
 (equal (fn-rtc-mstates (fn-rtc-st$a-splice h j data s)) (fn-rtc-mstates s))
 :hints (("Goal" :in-theory (union-theories '(fn-rtc-st$a-splice fn-rtc-with-accessors)
   (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-splice-keeps-hll
 (implies (fn-hll-invp s) (fn-hll-invp (fn-rtc-st$a-splice h j data s)))
 :hints (("Goal" :use ((:instance fn-rtc-splice-keeps-invp (st s) (off j)))
  :in-theory (union-theories '(fn-hld-hll-invp-is fn-rtc-st-splice fn-ovrlp-splice-mstates)
  (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-put-keeps-hll
 (implies (fn-hll-invp s) (fn-hll-invp (fn-rtc-st-put h j data s)))
 :hints (("Goal" :in-theory (union-theories '(fn-rtc-st-put fn-rtc-st$a-put fn-ovrlp-splice-keeps-hll)
   (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-append-loop-keeps-hll
 (implies (fn-hll-invp fn-rtc-st)
   (fn-hll-invp (fn-dsw-append-loop h j octets fn-rtc-st)))
 :hints (("Goal" :induct (fn-dsw-append-loop h j octets fn-rtc-st)
 :in-theory (union-theories '(fn-dsw-append-loop fn-ovrlp-put-keeps-hll)
 (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-append-keeps-hll
 (implies (fn-hll-invp s) (fn-hll-invp (mv-nth 2 (fn-dsw-append h j octets s))))
 :hints (("Goal" :in-theory (union-theories '(fn-dsw-append fn-ovrlp-append-loop-keeps-hll
  mv-nth zp car-cons cdr-cons) (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-dsw-decimal-keeps-hll
 (implies (fn-hll-invp fn-rtc-st) (fn-hll-invp (mv-nth 2 (fn-dsw-decimal h j n fn-rtc-st))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories '(fn-dsw-decimal fn-ovrlp-append-keeps-hll mv-nth zp car-cons cdr-cons (:type-prescription fn-dsw-decimal) (:type-prescription fn-ovr-wcopy-string) (:type-prescription fn-ovr-put-octets) (:type-prescription fn-ovr-put-string) (:type-prescription fn-ovr-put-decimal-field) (:type-prescription fn-ovr-put-decimal) (:type-prescription fn-ovr-put-xref) (:type-prescription fn-ovr-put-decimal-field-tab) (:type-prescription fn-ovr-put-decimal-tab) (:type-prescription fn-ovr-put-fields) (:type-prescription fn-ovr-put-served-xref) (:type-prescription fn-ovr-put-column-line) (:type-prescription fn-ovr-put-number) (:type-prescription fn-ovr-put-probe) (:type-prescription fn-ovr-fill) (:type-prescription fn-ovr-quantum)) (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-ovr-wcopy-string-keeps-hll
 (implies (fn-hll-invp fn-rtc-st) (fn-hll-invp (mv-nth 2 (fn-ovr-wcopy-string h i end j dss-str fn-rtc-st))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories '(fn-ovr-wcopy-string fn-ovrlp-append-keeps-hll fn-ovrlp-dsw-decimal-keeps-hll mv-nth zp car-cons cdr-cons (:type-prescription fn-dsw-decimal) (:type-prescription fn-ovr-wcopy-string) (:type-prescription fn-ovr-put-octets) (:type-prescription fn-ovr-put-string) (:type-prescription fn-ovr-put-decimal-field) (:type-prescription fn-ovr-put-decimal) (:type-prescription fn-ovr-put-xref) (:type-prescription fn-ovr-put-decimal-field-tab) (:type-prescription fn-ovr-put-decimal-tab) (:type-prescription fn-ovr-put-fields) (:type-prescription fn-ovr-put-served-xref) (:type-prescription fn-ovr-put-column-line) (:type-prescription fn-ovr-put-number) (:type-prescription fn-ovr-put-probe) (:type-prescription fn-ovr-fill) (:type-prescription fn-ovr-quantum)) (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-ovr-put-octets-keeps-hll
 (implies (fn-hll-invp fn-rtc-st) (fn-hll-invp (mv-nth 2 (fn-ovr-put-octets octets h j limit fn-rtc-st))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories '(fn-ovr-put-octets fn-ovrlp-append-keeps-hll fn-ovrlp-dsw-decimal-keeps-hll fn-ovrlp-ovr-wcopy-string-keeps-hll mv-nth zp car-cons cdr-cons (:type-prescription fn-dsw-decimal) (:type-prescription fn-ovr-wcopy-string) (:type-prescription fn-ovr-put-octets) (:type-prescription fn-ovr-put-string) (:type-prescription fn-ovr-put-decimal-field) (:type-prescription fn-ovr-put-decimal) (:type-prescription fn-ovr-put-xref) (:type-prescription fn-ovr-put-decimal-field-tab) (:type-prescription fn-ovr-put-decimal-tab) (:type-prescription fn-ovr-put-fields) (:type-prescription fn-ovr-put-served-xref) (:type-prescription fn-ovr-put-column-line) (:type-prescription fn-ovr-put-number) (:type-prescription fn-ovr-put-probe) (:type-prescription fn-ovr-fill) (:type-prescription fn-ovr-quantum)) (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-ovr-put-string-keeps-hll
 (implies (fn-hll-invp fn-rtc-st) (fn-hll-invp (mv-nth 2 (fn-ovr-put-string s h j limit fn-rtc-st))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories '(fn-ovr-put-string fn-ovrlp-append-keeps-hll fn-ovrlp-dsw-decimal-keeps-hll fn-ovrlp-ovr-wcopy-string-keeps-hll fn-ovrlp-ovr-put-octets-keeps-hll mv-nth zp car-cons cdr-cons (:type-prescription fn-dsw-decimal) (:type-prescription fn-ovr-wcopy-string) (:type-prescription fn-ovr-put-octets) (:type-prescription fn-ovr-put-string) (:type-prescription fn-ovr-put-decimal-field) (:type-prescription fn-ovr-put-decimal) (:type-prescription fn-ovr-put-xref) (:type-prescription fn-ovr-put-decimal-field-tab) (:type-prescription fn-ovr-put-decimal-tab) (:type-prescription fn-ovr-put-fields) (:type-prescription fn-ovr-put-served-xref) (:type-prescription fn-ovr-put-column-line) (:type-prescription fn-ovr-put-number) (:type-prescription fn-ovr-put-probe) (:type-prescription fn-ovr-fill) (:type-prescription fn-ovr-quantum)) (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-ovr-put-decimal-field-keeps-hll
 (implies (fn-hll-invp fn-rtc-st) (fn-hll-invp (mv-nth 2 (fn-ovr-put-decimal-field n h j limit fn-rtc-st))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories '(fn-ovr-put-decimal-field fn-ovrlp-append-keeps-hll fn-ovrlp-dsw-decimal-keeps-hll fn-ovrlp-ovr-wcopy-string-keeps-hll fn-ovrlp-ovr-put-octets-keeps-hll fn-ovrlp-ovr-put-string-keeps-hll mv-nth zp car-cons cdr-cons (:type-prescription fn-dsw-decimal) (:type-prescription fn-ovr-wcopy-string) (:type-prescription fn-ovr-put-octets) (:type-prescription fn-ovr-put-string) (:type-prescription fn-ovr-put-decimal-field) (:type-prescription fn-ovr-put-decimal) (:type-prescription fn-ovr-put-xref) (:type-prescription fn-ovr-put-decimal-field-tab) (:type-prescription fn-ovr-put-decimal-tab) (:type-prescription fn-ovr-put-fields) (:type-prescription fn-ovr-put-served-xref) (:type-prescription fn-ovr-put-column-line) (:type-prescription fn-ovr-put-number) (:type-prescription fn-ovr-put-probe) (:type-prescription fn-ovr-fill) (:type-prescription fn-ovr-quantum)) (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-ovr-put-decimal-keeps-hll
 (implies (fn-hll-invp fn-rtc-st) (fn-hll-invp (mv-nth 2 (fn-ovr-put-decimal n h j limit fn-rtc-st))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories '(fn-ovr-put-decimal fn-ovrlp-append-keeps-hll fn-ovrlp-dsw-decimal-keeps-hll fn-ovrlp-ovr-wcopy-string-keeps-hll fn-ovrlp-ovr-put-octets-keeps-hll fn-ovrlp-ovr-put-string-keeps-hll fn-ovrlp-ovr-put-decimal-field-keeps-hll mv-nth zp car-cons cdr-cons (:type-prescription fn-dsw-decimal) (:type-prescription fn-ovr-wcopy-string) (:type-prescription fn-ovr-put-octets) (:type-prescription fn-ovr-put-string) (:type-prescription fn-ovr-put-decimal-field) (:type-prescription fn-ovr-put-decimal) (:type-prescription fn-ovr-put-xref) (:type-prescription fn-ovr-put-decimal-field-tab) (:type-prescription fn-ovr-put-decimal-tab) (:type-prescription fn-ovr-put-fields) (:type-prescription fn-ovr-put-served-xref) (:type-prescription fn-ovr-put-column-line) (:type-prescription fn-ovr-put-number) (:type-prescription fn-ovr-put-probe) (:type-prescription fn-ovr-fill) (:type-prescription fn-ovr-quantum)) (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-ovr-put-xref-keeps-hll
 (implies (fn-hll-invp fn-rtc-st) (fn-hll-invp (mv-nth 2 (fn-ovr-put-xref ms all idp h j limit fn-rtc-st))))
 :hints (("Goal" :induct (fn-ovr-put-xref ms all idp h j limit fn-rtc-st) :in-theory (union-theories '(fn-ovr-put-xref fn-ovrlp-append-keeps-hll fn-ovrlp-dsw-decimal-keeps-hll fn-ovrlp-ovr-wcopy-string-keeps-hll fn-ovrlp-ovr-put-octets-keeps-hll fn-ovrlp-ovr-put-string-keeps-hll fn-ovrlp-ovr-put-decimal-field-keeps-hll fn-ovrlp-ovr-put-decimal-keeps-hll mv-nth zp car-cons cdr-cons (:type-prescription fn-dsw-decimal) (:type-prescription fn-ovr-wcopy-string) (:type-prescription fn-ovr-put-octets) (:type-prescription fn-ovr-put-string) (:type-prescription fn-ovr-put-decimal-field) (:type-prescription fn-ovr-put-decimal) (:type-prescription fn-ovr-put-xref) (:type-prescription fn-ovr-put-decimal-field-tab) (:type-prescription fn-ovr-put-decimal-tab) (:type-prescription fn-ovr-put-fields) (:type-prescription fn-ovr-put-served-xref) (:type-prescription fn-ovr-put-column-line) (:type-prescription fn-ovr-put-number) (:type-prescription fn-ovr-put-probe) (:type-prescription fn-ovr-fill) (:type-prescription fn-ovr-quantum)) (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-ovr-put-decimal-field-tab-keeps-hll
 (implies (fn-hll-invp fn-rtc-st) (fn-hll-invp (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories '(fn-ovr-put-decimal-field-tab fn-ovrlp-append-keeps-hll fn-ovrlp-dsw-decimal-keeps-hll fn-ovrlp-ovr-wcopy-string-keeps-hll fn-ovrlp-ovr-put-octets-keeps-hll fn-ovrlp-ovr-put-string-keeps-hll fn-ovrlp-ovr-put-decimal-field-keeps-hll fn-ovrlp-ovr-put-decimal-keeps-hll fn-ovrlp-ovr-put-xref-keeps-hll mv-nth zp car-cons cdr-cons (:type-prescription fn-dsw-decimal) (:type-prescription fn-ovr-wcopy-string) (:type-prescription fn-ovr-put-octets) (:type-prescription fn-ovr-put-string) (:type-prescription fn-ovr-put-decimal-field) (:type-prescription fn-ovr-put-decimal) (:type-prescription fn-ovr-put-xref) (:type-prescription fn-ovr-put-decimal-field-tab) (:type-prescription fn-ovr-put-decimal-tab) (:type-prescription fn-ovr-put-fields) (:type-prescription fn-ovr-put-served-xref) (:type-prescription fn-ovr-put-column-line) (:type-prescription fn-ovr-put-number) (:type-prescription fn-ovr-put-probe) (:type-prescription fn-ovr-fill) (:type-prescription fn-ovr-quantum)) (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-ovr-put-decimal-tab-keeps-hll
 (implies (fn-hll-invp fn-rtc-st) (fn-hll-invp (mv-nth 2 (fn-ovr-put-decimal-tab n h j limit fn-rtc-st))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories '(fn-ovr-put-decimal-tab fn-ovrlp-append-keeps-hll fn-ovrlp-dsw-decimal-keeps-hll fn-ovrlp-ovr-wcopy-string-keeps-hll fn-ovrlp-ovr-put-octets-keeps-hll fn-ovrlp-ovr-put-string-keeps-hll fn-ovrlp-ovr-put-decimal-field-keeps-hll fn-ovrlp-ovr-put-decimal-keeps-hll fn-ovrlp-ovr-put-xref-keeps-hll fn-ovrlp-ovr-put-decimal-field-tab-keeps-hll mv-nth zp car-cons cdr-cons (:type-prescription fn-dsw-decimal) (:type-prescription fn-ovr-wcopy-string) (:type-prescription fn-ovr-put-octets) (:type-prescription fn-ovr-put-string) (:type-prescription fn-ovr-put-decimal-field) (:type-prescription fn-ovr-put-decimal) (:type-prescription fn-ovr-put-xref) (:type-prescription fn-ovr-put-decimal-field-tab) (:type-prescription fn-ovr-put-decimal-tab) (:type-prescription fn-ovr-put-fields) (:type-prescription fn-ovr-put-served-xref) (:type-prescription fn-ovr-put-column-line) (:type-prescription fn-ovr-put-number) (:type-prescription fn-ovr-put-probe) (:type-prescription fn-ovr-fill) (:type-prescription fn-ovr-quantum)) (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-ovr-put-fields-keeps-hll
 (implies (fn-hll-invp fn-rtc-st) (fn-hll-invp (mv-nth 2 (fn-ovr-put-fields fields h j limit fn-rtc-st))))
 :hints (("Goal" :induct (fn-ovr-put-fields fields h j limit fn-rtc-st) :in-theory (union-theories '(fn-ovr-put-fields fn-ovrlp-append-keeps-hll fn-ovrlp-dsw-decimal-keeps-hll fn-ovrlp-ovr-wcopy-string-keeps-hll fn-ovrlp-ovr-put-octets-keeps-hll fn-ovrlp-ovr-put-string-keeps-hll fn-ovrlp-ovr-put-decimal-field-keeps-hll fn-ovrlp-ovr-put-decimal-keeps-hll fn-ovrlp-ovr-put-xref-keeps-hll fn-ovrlp-ovr-put-decimal-field-tab-keeps-hll fn-ovrlp-ovr-put-decimal-tab-keeps-hll mv-nth zp car-cons cdr-cons (:type-prescription fn-dsw-decimal) (:type-prescription fn-ovr-wcopy-string) (:type-prescription fn-ovr-put-octets) (:type-prescription fn-ovr-put-string) (:type-prescription fn-ovr-put-decimal-field) (:type-prescription fn-ovr-put-decimal) (:type-prescription fn-ovr-put-xref) (:type-prescription fn-ovr-put-decimal-field-tab) (:type-prescription fn-ovr-put-decimal-tab) (:type-prescription fn-ovr-put-fields) (:type-prescription fn-ovr-put-served-xref) (:type-prescription fn-ovr-put-column-line) (:type-prescription fn-ovr-put-number) (:type-prescription fn-ovr-put-probe) (:type-prescription fn-ovr-fill) (:type-prescription fn-ovr-quantum)) (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-ovr-put-served-xref-keeps-hll
 (implies (fn-hll-invp fn-rtc-st) (fn-hll-invp (mv-nth 2 (fn-ovr-put-served-xref server ms idp h j limit fn-rtc-st))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories '(fn-ovr-put-served-xref fn-ovrlp-append-keeps-hll fn-ovrlp-dsw-decimal-keeps-hll fn-ovrlp-ovr-wcopy-string-keeps-hll fn-ovrlp-ovr-put-octets-keeps-hll fn-ovrlp-ovr-put-string-keeps-hll fn-ovrlp-ovr-put-decimal-field-keeps-hll fn-ovrlp-ovr-put-decimal-keeps-hll fn-ovrlp-ovr-put-xref-keeps-hll fn-ovrlp-ovr-put-decimal-field-tab-keeps-hll fn-ovrlp-ovr-put-decimal-tab-keeps-hll fn-ovrlp-ovr-put-fields-keeps-hll mv-nth zp car-cons cdr-cons (:type-prescription fn-dsw-decimal) (:type-prescription fn-ovr-wcopy-string) (:type-prescription fn-ovr-put-octets) (:type-prescription fn-ovr-put-string) (:type-prescription fn-ovr-put-decimal-field) (:type-prescription fn-ovr-put-decimal) (:type-prescription fn-ovr-put-xref) (:type-prescription fn-ovr-put-decimal-field-tab) (:type-prescription fn-ovr-put-decimal-tab) (:type-prescription fn-ovr-put-fields) (:type-prescription fn-ovr-put-served-xref) (:type-prescription fn-ovr-put-column-line) (:type-prescription fn-ovr-put-number) (:type-prescription fn-ovr-put-probe) (:type-prescription fn-ovr-fill) (:type-prescription fn-ovr-quantum)) (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-ovr-put-column-line-keeps-hll
 (implies (fn-hll-invp fn-rtc-st) (fn-hll-invp (mv-nth 2 (fn-ovr-put-column-line n nov octets body server ms idp h j limit fn-rtc-st))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories '(fn-ovr-put-column-line fn-ovrlp-append-keeps-hll fn-ovrlp-dsw-decimal-keeps-hll fn-ovrlp-ovr-wcopy-string-keeps-hll fn-ovrlp-ovr-put-octets-keeps-hll fn-ovrlp-ovr-put-string-keeps-hll fn-ovrlp-ovr-put-decimal-field-keeps-hll fn-ovrlp-ovr-put-decimal-keeps-hll fn-ovrlp-ovr-put-xref-keeps-hll fn-ovrlp-ovr-put-decimal-field-tab-keeps-hll fn-ovrlp-ovr-put-decimal-tab-keeps-hll fn-ovrlp-ovr-put-fields-keeps-hll fn-ovrlp-ovr-put-served-xref-keeps-hll mv-nth zp car-cons cdr-cons (:type-prescription fn-dsw-decimal) (:type-prescription fn-ovr-wcopy-string) (:type-prescription fn-ovr-put-octets) (:type-prescription fn-ovr-put-string) (:type-prescription fn-ovr-put-decimal-field) (:type-prescription fn-ovr-put-decimal) (:type-prescription fn-ovr-put-xref) (:type-prescription fn-ovr-put-decimal-field-tab) (:type-prescription fn-ovr-put-decimal-tab) (:type-prescription fn-ovr-put-fields) (:type-prescription fn-ovr-put-served-xref) (:type-prescription fn-ovr-put-column-line) (:type-prescription fn-ovr-put-number) (:type-prescription fn-ovr-put-probe) (:type-prescription fn-ovr-fill) (:type-prescription fn-ovr-quantum)) (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-ovr-put-number-keeps-hll
 (implies (fn-hll-invp fn-rtc-st) (fn-hll-invp (mv-nth 2 (fn-ovr-put-number group n server v h j limit fn-rtc-st fn-arena fn-cat))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories '(fn-ovr-put-number fn-ovrlp-append-keeps-hll fn-ovrlp-dsw-decimal-keeps-hll fn-ovrlp-ovr-wcopy-string-keeps-hll fn-ovrlp-ovr-put-octets-keeps-hll fn-ovrlp-ovr-put-string-keeps-hll fn-ovrlp-ovr-put-decimal-field-keeps-hll fn-ovrlp-ovr-put-decimal-keeps-hll fn-ovrlp-ovr-put-xref-keeps-hll fn-ovrlp-ovr-put-decimal-field-tab-keeps-hll fn-ovrlp-ovr-put-decimal-tab-keeps-hll fn-ovrlp-ovr-put-fields-keeps-hll fn-ovrlp-ovr-put-served-xref-keeps-hll fn-ovrlp-ovr-put-column-line-keeps-hll mv-nth zp car-cons cdr-cons (:type-prescription fn-dsw-decimal) (:type-prescription fn-ovr-wcopy-string) (:type-prescription fn-ovr-put-octets) (:type-prescription fn-ovr-put-string) (:type-prescription fn-ovr-put-decimal-field) (:type-prescription fn-ovr-put-decimal) (:type-prescription fn-ovr-put-xref) (:type-prescription fn-ovr-put-decimal-field-tab) (:type-prescription fn-ovr-put-decimal-tab) (:type-prescription fn-ovr-put-fields) (:type-prescription fn-ovr-put-served-xref) (:type-prescription fn-ovr-put-column-line) (:type-prescription fn-ovr-put-number) (:type-prescription fn-ovr-put-probe) (:type-prescription fn-ovr-fill) (:type-prescription fn-ovr-quantum)) (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-ovr-put-probe-keeps-hll
 (implies (fn-hll-invp fn-rtc-st) (fn-hll-invp (mv-nth 2 (fn-ovr-put-probe group number server v h j limit fn-rtc-st fn-arena fn-cat))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories '(fn-ovr-put-probe fn-ovrlp-append-keeps-hll fn-ovrlp-dsw-decimal-keeps-hll fn-ovrlp-ovr-wcopy-string-keeps-hll fn-ovrlp-ovr-put-octets-keeps-hll fn-ovrlp-ovr-put-string-keeps-hll fn-ovrlp-ovr-put-decimal-field-keeps-hll fn-ovrlp-ovr-put-decimal-keeps-hll fn-ovrlp-ovr-put-xref-keeps-hll fn-ovrlp-ovr-put-decimal-field-tab-keeps-hll fn-ovrlp-ovr-put-decimal-tab-keeps-hll fn-ovrlp-ovr-put-fields-keeps-hll fn-ovrlp-ovr-put-served-xref-keeps-hll fn-ovrlp-ovr-put-column-line-keeps-hll fn-ovrlp-ovr-put-number-keeps-hll mv-nth zp car-cons cdr-cons (:type-prescription fn-dsw-decimal) (:type-prescription fn-ovr-wcopy-string) (:type-prescription fn-ovr-put-octets) (:type-prescription fn-ovr-put-string) (:type-prescription fn-ovr-put-decimal-field) (:type-prescription fn-ovr-put-decimal) (:type-prescription fn-ovr-put-xref) (:type-prescription fn-ovr-put-decimal-field-tab) (:type-prescription fn-ovr-put-decimal-tab) (:type-prescription fn-ovr-put-fields) (:type-prescription fn-ovr-put-served-xref) (:type-prescription fn-ovr-put-column-line) (:type-prescription fn-ovr-put-number) (:type-prescription fn-ovr-put-probe) (:type-prescription fn-ovr-fill) (:type-prescription fn-ovr-quantum)) (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-ovr-fill-keeps-hll
 (implies (fn-hll-invp fn-rtc-st) (fn-hll-invp (mv-nth 3 (fn-ovr-fill group number last top owedp legacyp room server v h j fn-rtc-st fn-arena fn-cat))))
 :hints (("Goal" :induct (fn-ovr-fill group number last top owedp legacyp room server v h j fn-rtc-st fn-arena fn-cat) :in-theory (union-theories '(fn-ovr-fill fn-ovrlp-append-keeps-hll fn-ovrlp-dsw-decimal-keeps-hll fn-ovrlp-ovr-wcopy-string-keeps-hll fn-ovrlp-ovr-put-octets-keeps-hll fn-ovrlp-ovr-put-string-keeps-hll fn-ovrlp-ovr-put-decimal-field-keeps-hll fn-ovrlp-ovr-put-decimal-keeps-hll fn-ovrlp-ovr-put-xref-keeps-hll fn-ovrlp-ovr-put-decimal-field-tab-keeps-hll fn-ovrlp-ovr-put-decimal-tab-keeps-hll fn-ovrlp-ovr-put-fields-keeps-hll fn-ovrlp-ovr-put-served-xref-keeps-hll fn-ovrlp-ovr-put-column-line-keeps-hll fn-ovrlp-ovr-put-number-keeps-hll fn-ovrlp-ovr-put-probe-keeps-hll mv-nth zp car-cons cdr-cons (:type-prescription fn-dsw-decimal) (:type-prescription fn-ovr-wcopy-string) (:type-prescription fn-ovr-put-octets) (:type-prescription fn-ovr-put-string) (:type-prescription fn-ovr-put-decimal-field) (:type-prescription fn-ovr-put-decimal) (:type-prescription fn-ovr-put-xref) (:type-prescription fn-ovr-put-decimal-field-tab) (:type-prescription fn-ovr-put-decimal-tab) (:type-prescription fn-ovr-put-fields) (:type-prescription fn-ovr-put-served-xref) (:type-prescription fn-ovr-put-column-line) (:type-prescription fn-ovr-put-number) (:type-prescription fn-ovr-put-probe) (:type-prescription fn-ovr-fill) (:type-prescription fn-ovr-quantum)) (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-ovr-quantum-keeps-hll
 (implies (fn-hll-invp fn-rtc-st) (fn-hll-invp (mv-nth 3 (fn-ovr-quantum cur w h base limit fn-rtc-st fn-arena fn-cat))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories '((:type-prescription fn-dsw-append) fn-ovr-quantum fn-ovrlp-append-keeps-hll fn-ovrlp-dsw-decimal-keeps-hll fn-ovrlp-ovr-wcopy-string-keeps-hll fn-ovrlp-ovr-put-octets-keeps-hll fn-ovrlp-ovr-put-string-keeps-hll fn-ovrlp-ovr-put-decimal-field-keeps-hll fn-ovrlp-ovr-put-decimal-keeps-hll fn-ovrlp-ovr-put-xref-keeps-hll fn-ovrlp-ovr-put-decimal-field-tab-keeps-hll fn-ovrlp-ovr-put-decimal-tab-keeps-hll fn-ovrlp-ovr-put-fields-keeps-hll fn-ovrlp-ovr-put-served-xref-keeps-hll fn-ovrlp-ovr-put-column-line-keeps-hll fn-ovrlp-ovr-put-number-keeps-hll fn-ovrlp-ovr-put-probe-keeps-hll fn-ovrlp-ovr-fill-keeps-hll mv-nth zp car-cons cdr-cons (:type-prescription fn-dsw-decimal) (:type-prescription fn-ovr-wcopy-string) (:type-prescription fn-ovr-put-octets) (:type-prescription fn-ovr-put-string) (:type-prescription fn-ovr-put-decimal-field) (:type-prescription fn-ovr-put-decimal) (:type-prescription fn-ovr-put-xref) (:type-prescription fn-ovr-put-decimal-field-tab) (:type-prescription fn-ovr-put-decimal-tab) (:type-prescription fn-ovr-put-fields) (:type-prescription fn-ovr-put-served-xref) (:type-prescription fn-ovr-put-column-line) (:type-prescription fn-ovr-put-number) (:type-prescription fn-ovr-put-probe) (:type-prescription fn-ovr-fill) (:type-prescription fn-ovr-quantum)) (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-put-frame (implies (natp h) (and (equal (fn-rtc-config (fn-rtc-st-put h j data s)) (fn-rtc-config s))
(equal (fn-rtc-slots (fn-rtc-st-put h j data s)) (fn-rtc-slots s))
(equal (fn-rtc-uses (fn-rtc-st-put h j data s)) (fn-rtc-uses s))
(equal (fn-rtc-next-op (fn-rtc-st-put h j data s)) (fn-rtc-next-op s))
(equal (len (fn-rtc-pool (fn-rtc-st-put h j data s))) (len (fn-rtc-pool s)))
(equal (fn-rtc-b-owner (fn-rtc-buffer k (fn-rtc-st-put h j data s))) (fn-rtc-b-owner (fn-rtc-buffer k s)))
(equal (fn-rtc-b-gen (fn-rtc-buffer k (fn-rtc-st-put h j data s))) (fn-rtc-b-gen (fn-rtc-buffer k s)))))
 :hints (("Goal" :in-theory (union-theories '(fn-rtc-st-put fn-hlr-put-frame2 fn-hlr-put-pool-len)
 (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-append-loop-frame (implies (natp h) (and (equal (fn-rtc-config (fn-dsw-append-loop h j octets fn-rtc-st)) (fn-rtc-config fn-rtc-st))
(equal (fn-rtc-slots (fn-dsw-append-loop h j octets fn-rtc-st)) (fn-rtc-slots fn-rtc-st))
(equal (fn-rtc-uses (fn-dsw-append-loop h j octets fn-rtc-st)) (fn-rtc-uses fn-rtc-st))
(equal (fn-rtc-next-op (fn-dsw-append-loop h j octets fn-rtc-st)) (fn-rtc-next-op fn-rtc-st))
(equal (len (fn-rtc-pool (fn-dsw-append-loop h j octets fn-rtc-st))) (len (fn-rtc-pool fn-rtc-st)))
(equal (fn-rtc-b-owner (fn-rtc-buffer k (fn-dsw-append-loop h j octets fn-rtc-st))) (fn-rtc-b-owner (fn-rtc-buffer k fn-rtc-st)))
(equal (fn-rtc-b-gen (fn-rtc-buffer k (fn-dsw-append-loop h j octets fn-rtc-st))) (fn-rtc-b-gen (fn-rtc-buffer k fn-rtc-st)))))
 :hints (("Goal" :induct (fn-dsw-append-loop h j octets fn-rtc-st) :in-theory (union-theories '(fn-dsw-append-loop fn-ovrlp-put-frame)
 (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-dsw-append-frame (implies (natp h) (and (equal (fn-rtc-config (mv-nth 2 (fn-dsw-append h j octets fn-rtc-st))) (fn-rtc-config fn-rtc-st))
(equal (fn-rtc-slots (mv-nth 2 (fn-dsw-append h j octets fn-rtc-st))) (fn-rtc-slots fn-rtc-st))
(equal (fn-rtc-uses (mv-nth 2 (fn-dsw-append h j octets fn-rtc-st))) (fn-rtc-uses fn-rtc-st))
(equal (fn-rtc-next-op (mv-nth 2 (fn-dsw-append h j octets fn-rtc-st))) (fn-rtc-next-op fn-rtc-st))
(equal (len (fn-rtc-pool (mv-nth 2 (fn-dsw-append h j octets fn-rtc-st)))) (len (fn-rtc-pool fn-rtc-st)))
(equal (fn-rtc-b-owner (fn-rtc-buffer k (mv-nth 2 (fn-dsw-append h j octets fn-rtc-st)))) (fn-rtc-b-owner (fn-rtc-buffer k fn-rtc-st)))
(equal (fn-rtc-b-gen (fn-rtc-buffer k (mv-nth 2 (fn-dsw-append h j octets fn-rtc-st)))) (fn-rtc-b-gen (fn-rtc-buffer k fn-rtc-st)))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories '(fn-dsw-append fn-ovrlp-append-loop-frame mv-nth zp car-cons cdr-cons (:type-prescription fn-dsw-append) (:type-prescription fn-ovr-fill)) (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-dsw-decimal-frame (implies (natp h) (and (equal (fn-rtc-config (mv-nth 2 (fn-dsw-decimal h j n fn-rtc-st))) (fn-rtc-config fn-rtc-st))
(equal (fn-rtc-slots (mv-nth 2 (fn-dsw-decimal h j n fn-rtc-st))) (fn-rtc-slots fn-rtc-st))
(equal (fn-rtc-uses (mv-nth 2 (fn-dsw-decimal h j n fn-rtc-st))) (fn-rtc-uses fn-rtc-st))
(equal (fn-rtc-next-op (mv-nth 2 (fn-dsw-decimal h j n fn-rtc-st))) (fn-rtc-next-op fn-rtc-st))
(equal (len (fn-rtc-pool (mv-nth 2 (fn-dsw-decimal h j n fn-rtc-st)))) (len (fn-rtc-pool fn-rtc-st)))
(equal (fn-rtc-b-owner (fn-rtc-buffer k (mv-nth 2 (fn-dsw-decimal h j n fn-rtc-st)))) (fn-rtc-b-owner (fn-rtc-buffer k fn-rtc-st)))
(equal (fn-rtc-b-gen (fn-rtc-buffer k (mv-nth 2 (fn-dsw-decimal h j n fn-rtc-st)))) (fn-rtc-b-gen (fn-rtc-buffer k fn-rtc-st)))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories '(fn-dsw-decimal fn-ovrlp-append-loop-frame fn-ovrlp-dsw-append-frame mv-nth zp car-cons cdr-cons (:type-prescription fn-dsw-append) (:type-prescription fn-ovr-fill)) (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-ovr-wcopy-string-frame (implies (natp h) (and (equal (fn-rtc-config (mv-nth 2 (fn-ovr-wcopy-string h i end j dss-str fn-rtc-st))) (fn-rtc-config fn-rtc-st))
(equal (fn-rtc-slots (mv-nth 2 (fn-ovr-wcopy-string h i end j dss-str fn-rtc-st))) (fn-rtc-slots fn-rtc-st))
(equal (fn-rtc-uses (mv-nth 2 (fn-ovr-wcopy-string h i end j dss-str fn-rtc-st))) (fn-rtc-uses fn-rtc-st))
(equal (fn-rtc-next-op (mv-nth 2 (fn-ovr-wcopy-string h i end j dss-str fn-rtc-st))) (fn-rtc-next-op fn-rtc-st))
(equal (len (fn-rtc-pool (mv-nth 2 (fn-ovr-wcopy-string h i end j dss-str fn-rtc-st)))) (len (fn-rtc-pool fn-rtc-st)))
(equal (fn-rtc-b-owner (fn-rtc-buffer k (mv-nth 2 (fn-ovr-wcopy-string h i end j dss-str fn-rtc-st)))) (fn-rtc-b-owner (fn-rtc-buffer k fn-rtc-st)))
(equal (fn-rtc-b-gen (fn-rtc-buffer k (mv-nth 2 (fn-ovr-wcopy-string h i end j dss-str fn-rtc-st)))) (fn-rtc-b-gen (fn-rtc-buffer k fn-rtc-st)))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories '(fn-ovr-wcopy-string fn-ovrlp-append-loop-frame fn-ovrlp-dsw-append-frame fn-ovrlp-dsw-decimal-frame mv-nth zp car-cons cdr-cons (:type-prescription fn-dsw-append) (:type-prescription fn-ovr-fill)) (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-ovr-put-octets-frame (implies (natp h) (and (equal (fn-rtc-config (mv-nth 2 (fn-ovr-put-octets octets h j limit fn-rtc-st))) (fn-rtc-config fn-rtc-st))
(equal (fn-rtc-slots (mv-nth 2 (fn-ovr-put-octets octets h j limit fn-rtc-st))) (fn-rtc-slots fn-rtc-st))
(equal (fn-rtc-uses (mv-nth 2 (fn-ovr-put-octets octets h j limit fn-rtc-st))) (fn-rtc-uses fn-rtc-st))
(equal (fn-rtc-next-op (mv-nth 2 (fn-ovr-put-octets octets h j limit fn-rtc-st))) (fn-rtc-next-op fn-rtc-st))
(equal (len (fn-rtc-pool (mv-nth 2 (fn-ovr-put-octets octets h j limit fn-rtc-st)))) (len (fn-rtc-pool fn-rtc-st)))
(equal (fn-rtc-b-owner (fn-rtc-buffer k (mv-nth 2 (fn-ovr-put-octets octets h j limit fn-rtc-st)))) (fn-rtc-b-owner (fn-rtc-buffer k fn-rtc-st)))
(equal (fn-rtc-b-gen (fn-rtc-buffer k (mv-nth 2 (fn-ovr-put-octets octets h j limit fn-rtc-st)))) (fn-rtc-b-gen (fn-rtc-buffer k fn-rtc-st)))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories '(fn-ovr-put-octets fn-ovrlp-append-loop-frame fn-ovrlp-dsw-append-frame fn-ovrlp-dsw-decimal-frame fn-ovrlp-ovr-wcopy-string-frame mv-nth zp car-cons cdr-cons (:type-prescription fn-dsw-append) (:type-prescription fn-ovr-fill)) (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-ovr-put-string-frame (implies (natp h) (and (equal (fn-rtc-config (mv-nth 2 (fn-ovr-put-string s h j limit fn-rtc-st))) (fn-rtc-config fn-rtc-st))
(equal (fn-rtc-slots (mv-nth 2 (fn-ovr-put-string s h j limit fn-rtc-st))) (fn-rtc-slots fn-rtc-st))
(equal (fn-rtc-uses (mv-nth 2 (fn-ovr-put-string s h j limit fn-rtc-st))) (fn-rtc-uses fn-rtc-st))
(equal (fn-rtc-next-op (mv-nth 2 (fn-ovr-put-string s h j limit fn-rtc-st))) (fn-rtc-next-op fn-rtc-st))
(equal (len (fn-rtc-pool (mv-nth 2 (fn-ovr-put-string s h j limit fn-rtc-st)))) (len (fn-rtc-pool fn-rtc-st)))
(equal (fn-rtc-b-owner (fn-rtc-buffer k (mv-nth 2 (fn-ovr-put-string s h j limit fn-rtc-st)))) (fn-rtc-b-owner (fn-rtc-buffer k fn-rtc-st)))
(equal (fn-rtc-b-gen (fn-rtc-buffer k (mv-nth 2 (fn-ovr-put-string s h j limit fn-rtc-st)))) (fn-rtc-b-gen (fn-rtc-buffer k fn-rtc-st)))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories '(fn-ovr-put-string fn-ovrlp-append-loop-frame fn-ovrlp-dsw-append-frame fn-ovrlp-dsw-decimal-frame fn-ovrlp-ovr-wcopy-string-frame fn-ovrlp-ovr-put-octets-frame mv-nth zp car-cons cdr-cons (:type-prescription fn-dsw-append) (:type-prescription fn-ovr-fill)) (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-ovr-put-decimal-field-frame (implies (natp h) (and (equal (fn-rtc-config (mv-nth 2 (fn-ovr-put-decimal-field n h j limit fn-rtc-st))) (fn-rtc-config fn-rtc-st))
(equal (fn-rtc-slots (mv-nth 2 (fn-ovr-put-decimal-field n h j limit fn-rtc-st))) (fn-rtc-slots fn-rtc-st))
(equal (fn-rtc-uses (mv-nth 2 (fn-ovr-put-decimal-field n h j limit fn-rtc-st))) (fn-rtc-uses fn-rtc-st))
(equal (fn-rtc-next-op (mv-nth 2 (fn-ovr-put-decimal-field n h j limit fn-rtc-st))) (fn-rtc-next-op fn-rtc-st))
(equal (len (fn-rtc-pool (mv-nth 2 (fn-ovr-put-decimal-field n h j limit fn-rtc-st)))) (len (fn-rtc-pool fn-rtc-st)))
(equal (fn-rtc-b-owner (fn-rtc-buffer k (mv-nth 2 (fn-ovr-put-decimal-field n h j limit fn-rtc-st)))) (fn-rtc-b-owner (fn-rtc-buffer k fn-rtc-st)))
(equal (fn-rtc-b-gen (fn-rtc-buffer k (mv-nth 2 (fn-ovr-put-decimal-field n h j limit fn-rtc-st)))) (fn-rtc-b-gen (fn-rtc-buffer k fn-rtc-st)))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories '(fn-ovr-put-decimal-field fn-ovrlp-append-loop-frame fn-ovrlp-dsw-append-frame fn-ovrlp-dsw-decimal-frame fn-ovrlp-ovr-wcopy-string-frame fn-ovrlp-ovr-put-octets-frame fn-ovrlp-ovr-put-string-frame mv-nth zp car-cons cdr-cons (:type-prescription fn-dsw-append) (:type-prescription fn-ovr-fill)) (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-ovr-put-decimal-frame (implies (natp h) (and (equal (fn-rtc-config (mv-nth 2 (fn-ovr-put-decimal n h j limit fn-rtc-st))) (fn-rtc-config fn-rtc-st))
(equal (fn-rtc-slots (mv-nth 2 (fn-ovr-put-decimal n h j limit fn-rtc-st))) (fn-rtc-slots fn-rtc-st))
(equal (fn-rtc-uses (mv-nth 2 (fn-ovr-put-decimal n h j limit fn-rtc-st))) (fn-rtc-uses fn-rtc-st))
(equal (fn-rtc-next-op (mv-nth 2 (fn-ovr-put-decimal n h j limit fn-rtc-st))) (fn-rtc-next-op fn-rtc-st))
(equal (len (fn-rtc-pool (mv-nth 2 (fn-ovr-put-decimal n h j limit fn-rtc-st)))) (len (fn-rtc-pool fn-rtc-st)))
(equal (fn-rtc-b-owner (fn-rtc-buffer k (mv-nth 2 (fn-ovr-put-decimal n h j limit fn-rtc-st)))) (fn-rtc-b-owner (fn-rtc-buffer k fn-rtc-st)))
(equal (fn-rtc-b-gen (fn-rtc-buffer k (mv-nth 2 (fn-ovr-put-decimal n h j limit fn-rtc-st)))) (fn-rtc-b-gen (fn-rtc-buffer k fn-rtc-st)))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories '(fn-ovr-put-decimal fn-ovrlp-append-loop-frame fn-ovrlp-dsw-append-frame fn-ovrlp-dsw-decimal-frame fn-ovrlp-ovr-wcopy-string-frame fn-ovrlp-ovr-put-octets-frame fn-ovrlp-ovr-put-string-frame fn-ovrlp-ovr-put-decimal-field-frame mv-nth zp car-cons cdr-cons (:type-prescription fn-dsw-append) (:type-prescription fn-ovr-fill)) (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-ovr-put-xref-frame (implies (natp h) (and (equal (fn-rtc-config (mv-nth 2 (fn-ovr-put-xref ms all idp h j limit fn-rtc-st))) (fn-rtc-config fn-rtc-st))
(equal (fn-rtc-slots (mv-nth 2 (fn-ovr-put-xref ms all idp h j limit fn-rtc-st))) (fn-rtc-slots fn-rtc-st))
(equal (fn-rtc-uses (mv-nth 2 (fn-ovr-put-xref ms all idp h j limit fn-rtc-st))) (fn-rtc-uses fn-rtc-st))
(equal (fn-rtc-next-op (mv-nth 2 (fn-ovr-put-xref ms all idp h j limit fn-rtc-st))) (fn-rtc-next-op fn-rtc-st))
(equal (len (fn-rtc-pool (mv-nth 2 (fn-ovr-put-xref ms all idp h j limit fn-rtc-st)))) (len (fn-rtc-pool fn-rtc-st)))
(equal (fn-rtc-b-owner (fn-rtc-buffer k (mv-nth 2 (fn-ovr-put-xref ms all idp h j limit fn-rtc-st)))) (fn-rtc-b-owner (fn-rtc-buffer k fn-rtc-st)))
(equal (fn-rtc-b-gen (fn-rtc-buffer k (mv-nth 2 (fn-ovr-put-xref ms all idp h j limit fn-rtc-st)))) (fn-rtc-b-gen (fn-rtc-buffer k fn-rtc-st)))))
 :hints (("Goal" :induct (fn-ovr-put-xref ms all idp h j limit fn-rtc-st) :in-theory (union-theories '(fn-ovr-put-xref fn-ovrlp-append-loop-frame fn-ovrlp-dsw-append-frame fn-ovrlp-dsw-decimal-frame fn-ovrlp-ovr-wcopy-string-frame fn-ovrlp-ovr-put-octets-frame fn-ovrlp-ovr-put-string-frame fn-ovrlp-ovr-put-decimal-field-frame fn-ovrlp-ovr-put-decimal-frame mv-nth zp car-cons cdr-cons (:type-prescription fn-dsw-append) (:type-prescription fn-ovr-fill)) (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-ovr-put-decimal-field-tab-frame (implies (natp h) (and (equal (fn-rtc-config (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st))) (fn-rtc-config fn-rtc-st))
(equal (fn-rtc-slots (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st))) (fn-rtc-slots fn-rtc-st))
(equal (fn-rtc-uses (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st))) (fn-rtc-uses fn-rtc-st))
(equal (fn-rtc-next-op (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st))) (fn-rtc-next-op fn-rtc-st))
(equal (len (fn-rtc-pool (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)))) (len (fn-rtc-pool fn-rtc-st)))
(equal (fn-rtc-b-owner (fn-rtc-buffer k (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)))) (fn-rtc-b-owner (fn-rtc-buffer k fn-rtc-st)))
(equal (fn-rtc-b-gen (fn-rtc-buffer k (mv-nth 2 (fn-ovr-put-decimal-field-tab n h j limit fn-rtc-st)))) (fn-rtc-b-gen (fn-rtc-buffer k fn-rtc-st)))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories '(fn-ovr-put-decimal-field-tab fn-ovrlp-append-loop-frame fn-ovrlp-dsw-append-frame fn-ovrlp-dsw-decimal-frame fn-ovrlp-ovr-wcopy-string-frame fn-ovrlp-ovr-put-octets-frame fn-ovrlp-ovr-put-string-frame fn-ovrlp-ovr-put-decimal-field-frame fn-ovrlp-ovr-put-decimal-frame fn-ovrlp-ovr-put-xref-frame mv-nth zp car-cons cdr-cons (:type-prescription fn-dsw-append) (:type-prescription fn-ovr-fill)) (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-ovr-put-decimal-tab-frame (implies (natp h) (and (equal (fn-rtc-config (mv-nth 2 (fn-ovr-put-decimal-tab n h j limit fn-rtc-st))) (fn-rtc-config fn-rtc-st))
(equal (fn-rtc-slots (mv-nth 2 (fn-ovr-put-decimal-tab n h j limit fn-rtc-st))) (fn-rtc-slots fn-rtc-st))
(equal (fn-rtc-uses (mv-nth 2 (fn-ovr-put-decimal-tab n h j limit fn-rtc-st))) (fn-rtc-uses fn-rtc-st))
(equal (fn-rtc-next-op (mv-nth 2 (fn-ovr-put-decimal-tab n h j limit fn-rtc-st))) (fn-rtc-next-op fn-rtc-st))
(equal (len (fn-rtc-pool (mv-nth 2 (fn-ovr-put-decimal-tab n h j limit fn-rtc-st)))) (len (fn-rtc-pool fn-rtc-st)))
(equal (fn-rtc-b-owner (fn-rtc-buffer k (mv-nth 2 (fn-ovr-put-decimal-tab n h j limit fn-rtc-st)))) (fn-rtc-b-owner (fn-rtc-buffer k fn-rtc-st)))
(equal (fn-rtc-b-gen (fn-rtc-buffer k (mv-nth 2 (fn-ovr-put-decimal-tab n h j limit fn-rtc-st)))) (fn-rtc-b-gen (fn-rtc-buffer k fn-rtc-st)))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories '(fn-ovr-put-decimal-tab fn-ovrlp-append-loop-frame fn-ovrlp-dsw-append-frame fn-ovrlp-dsw-decimal-frame fn-ovrlp-ovr-wcopy-string-frame fn-ovrlp-ovr-put-octets-frame fn-ovrlp-ovr-put-string-frame fn-ovrlp-ovr-put-decimal-field-frame fn-ovrlp-ovr-put-decimal-frame fn-ovrlp-ovr-put-xref-frame fn-ovrlp-ovr-put-decimal-field-tab-frame mv-nth zp car-cons cdr-cons (:type-prescription fn-dsw-append) (:type-prescription fn-ovr-fill)) (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-ovr-put-fields-frame (implies (natp h) (and (equal (fn-rtc-config (mv-nth 2 (fn-ovr-put-fields fields h j limit fn-rtc-st))) (fn-rtc-config fn-rtc-st))
(equal (fn-rtc-slots (mv-nth 2 (fn-ovr-put-fields fields h j limit fn-rtc-st))) (fn-rtc-slots fn-rtc-st))
(equal (fn-rtc-uses (mv-nth 2 (fn-ovr-put-fields fields h j limit fn-rtc-st))) (fn-rtc-uses fn-rtc-st))
(equal (fn-rtc-next-op (mv-nth 2 (fn-ovr-put-fields fields h j limit fn-rtc-st))) (fn-rtc-next-op fn-rtc-st))
(equal (len (fn-rtc-pool (mv-nth 2 (fn-ovr-put-fields fields h j limit fn-rtc-st)))) (len (fn-rtc-pool fn-rtc-st)))
(equal (fn-rtc-b-owner (fn-rtc-buffer k (mv-nth 2 (fn-ovr-put-fields fields h j limit fn-rtc-st)))) (fn-rtc-b-owner (fn-rtc-buffer k fn-rtc-st)))
(equal (fn-rtc-b-gen (fn-rtc-buffer k (mv-nth 2 (fn-ovr-put-fields fields h j limit fn-rtc-st)))) (fn-rtc-b-gen (fn-rtc-buffer k fn-rtc-st)))))
 :hints (("Goal" :induct (fn-ovr-put-fields fields h j limit fn-rtc-st) :in-theory (union-theories '(fn-ovr-put-fields fn-ovrlp-append-loop-frame fn-ovrlp-dsw-append-frame fn-ovrlp-dsw-decimal-frame fn-ovrlp-ovr-wcopy-string-frame fn-ovrlp-ovr-put-octets-frame fn-ovrlp-ovr-put-string-frame fn-ovrlp-ovr-put-decimal-field-frame fn-ovrlp-ovr-put-decimal-frame fn-ovrlp-ovr-put-xref-frame fn-ovrlp-ovr-put-decimal-field-tab-frame fn-ovrlp-ovr-put-decimal-tab-frame mv-nth zp car-cons cdr-cons (:type-prescription fn-dsw-append) (:type-prescription fn-ovr-fill)) (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-ovr-put-served-xref-frame (implies (natp h) (and (equal (fn-rtc-config (mv-nth 2 (fn-ovr-put-served-xref server ms idp h j limit fn-rtc-st))) (fn-rtc-config fn-rtc-st))
(equal (fn-rtc-slots (mv-nth 2 (fn-ovr-put-served-xref server ms idp h j limit fn-rtc-st))) (fn-rtc-slots fn-rtc-st))
(equal (fn-rtc-uses (mv-nth 2 (fn-ovr-put-served-xref server ms idp h j limit fn-rtc-st))) (fn-rtc-uses fn-rtc-st))
(equal (fn-rtc-next-op (mv-nth 2 (fn-ovr-put-served-xref server ms idp h j limit fn-rtc-st))) (fn-rtc-next-op fn-rtc-st))
(equal (len (fn-rtc-pool (mv-nth 2 (fn-ovr-put-served-xref server ms idp h j limit fn-rtc-st)))) (len (fn-rtc-pool fn-rtc-st)))
(equal (fn-rtc-b-owner (fn-rtc-buffer k (mv-nth 2 (fn-ovr-put-served-xref server ms idp h j limit fn-rtc-st)))) (fn-rtc-b-owner (fn-rtc-buffer k fn-rtc-st)))
(equal (fn-rtc-b-gen (fn-rtc-buffer k (mv-nth 2 (fn-ovr-put-served-xref server ms idp h j limit fn-rtc-st)))) (fn-rtc-b-gen (fn-rtc-buffer k fn-rtc-st)))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories '(fn-ovr-put-served-xref fn-ovrlp-append-loop-frame fn-ovrlp-dsw-append-frame fn-ovrlp-dsw-decimal-frame fn-ovrlp-ovr-wcopy-string-frame fn-ovrlp-ovr-put-octets-frame fn-ovrlp-ovr-put-string-frame fn-ovrlp-ovr-put-decimal-field-frame fn-ovrlp-ovr-put-decimal-frame fn-ovrlp-ovr-put-xref-frame fn-ovrlp-ovr-put-decimal-field-tab-frame fn-ovrlp-ovr-put-decimal-tab-frame fn-ovrlp-ovr-put-fields-frame mv-nth zp car-cons cdr-cons (:type-prescription fn-dsw-append) (:type-prescription fn-ovr-fill)) (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-ovr-put-column-line-frame (implies (natp h) (and (equal (fn-rtc-config (mv-nth 2 (fn-ovr-put-column-line n nov octets body server ms idp h j limit fn-rtc-st))) (fn-rtc-config fn-rtc-st))
(equal (fn-rtc-slots (mv-nth 2 (fn-ovr-put-column-line n nov octets body server ms idp h j limit fn-rtc-st))) (fn-rtc-slots fn-rtc-st))
(equal (fn-rtc-uses (mv-nth 2 (fn-ovr-put-column-line n nov octets body server ms idp h j limit fn-rtc-st))) (fn-rtc-uses fn-rtc-st))
(equal (fn-rtc-next-op (mv-nth 2 (fn-ovr-put-column-line n nov octets body server ms idp h j limit fn-rtc-st))) (fn-rtc-next-op fn-rtc-st))
(equal (len (fn-rtc-pool (mv-nth 2 (fn-ovr-put-column-line n nov octets body server ms idp h j limit fn-rtc-st)))) (len (fn-rtc-pool fn-rtc-st)))
(equal (fn-rtc-b-owner (fn-rtc-buffer k (mv-nth 2 (fn-ovr-put-column-line n nov octets body server ms idp h j limit fn-rtc-st)))) (fn-rtc-b-owner (fn-rtc-buffer k fn-rtc-st)))
(equal (fn-rtc-b-gen (fn-rtc-buffer k (mv-nth 2 (fn-ovr-put-column-line n nov octets body server ms idp h j limit fn-rtc-st)))) (fn-rtc-b-gen (fn-rtc-buffer k fn-rtc-st)))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories '(fn-ovr-put-column-line fn-ovrlp-append-loop-frame fn-ovrlp-dsw-append-frame fn-ovrlp-dsw-decimal-frame fn-ovrlp-ovr-wcopy-string-frame fn-ovrlp-ovr-put-octets-frame fn-ovrlp-ovr-put-string-frame fn-ovrlp-ovr-put-decimal-field-frame fn-ovrlp-ovr-put-decimal-frame fn-ovrlp-ovr-put-xref-frame fn-ovrlp-ovr-put-decimal-field-tab-frame fn-ovrlp-ovr-put-decimal-tab-frame fn-ovrlp-ovr-put-fields-frame fn-ovrlp-ovr-put-served-xref-frame mv-nth zp car-cons cdr-cons (:type-prescription fn-dsw-append) (:type-prescription fn-ovr-fill)) (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-ovr-put-number-frame (implies (natp h) (and (equal (fn-rtc-config (mv-nth 2 (fn-ovr-put-number group n server v h j limit fn-rtc-st fn-arena fn-cat))) (fn-rtc-config fn-rtc-st))
(equal (fn-rtc-slots (mv-nth 2 (fn-ovr-put-number group n server v h j limit fn-rtc-st fn-arena fn-cat))) (fn-rtc-slots fn-rtc-st))
(equal (fn-rtc-uses (mv-nth 2 (fn-ovr-put-number group n server v h j limit fn-rtc-st fn-arena fn-cat))) (fn-rtc-uses fn-rtc-st))
(equal (fn-rtc-next-op (mv-nth 2 (fn-ovr-put-number group n server v h j limit fn-rtc-st fn-arena fn-cat))) (fn-rtc-next-op fn-rtc-st))
(equal (len (fn-rtc-pool (mv-nth 2 (fn-ovr-put-number group n server v h j limit fn-rtc-st fn-arena fn-cat)))) (len (fn-rtc-pool fn-rtc-st)))
(equal (fn-rtc-b-owner (fn-rtc-buffer k (mv-nth 2 (fn-ovr-put-number group n server v h j limit fn-rtc-st fn-arena fn-cat)))) (fn-rtc-b-owner (fn-rtc-buffer k fn-rtc-st)))
(equal (fn-rtc-b-gen (fn-rtc-buffer k (mv-nth 2 (fn-ovr-put-number group n server v h j limit fn-rtc-st fn-arena fn-cat)))) (fn-rtc-b-gen (fn-rtc-buffer k fn-rtc-st)))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories '(fn-ovr-put-number fn-ovrlp-append-loop-frame fn-ovrlp-dsw-append-frame fn-ovrlp-dsw-decimal-frame fn-ovrlp-ovr-wcopy-string-frame fn-ovrlp-ovr-put-octets-frame fn-ovrlp-ovr-put-string-frame fn-ovrlp-ovr-put-decimal-field-frame fn-ovrlp-ovr-put-decimal-frame fn-ovrlp-ovr-put-xref-frame fn-ovrlp-ovr-put-decimal-field-tab-frame fn-ovrlp-ovr-put-decimal-tab-frame fn-ovrlp-ovr-put-fields-frame fn-ovrlp-ovr-put-served-xref-frame fn-ovrlp-ovr-put-column-line-frame mv-nth zp car-cons cdr-cons (:type-prescription fn-dsw-append) (:type-prescription fn-ovr-fill)) (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-ovr-put-probe-frame (implies (natp h) (and (equal (fn-rtc-config (mv-nth 2 (fn-ovr-put-probe group number server v h j limit fn-rtc-st fn-arena fn-cat))) (fn-rtc-config fn-rtc-st))
(equal (fn-rtc-slots (mv-nth 2 (fn-ovr-put-probe group number server v h j limit fn-rtc-st fn-arena fn-cat))) (fn-rtc-slots fn-rtc-st))
(equal (fn-rtc-uses (mv-nth 2 (fn-ovr-put-probe group number server v h j limit fn-rtc-st fn-arena fn-cat))) (fn-rtc-uses fn-rtc-st))
(equal (fn-rtc-next-op (mv-nth 2 (fn-ovr-put-probe group number server v h j limit fn-rtc-st fn-arena fn-cat))) (fn-rtc-next-op fn-rtc-st))
(equal (len (fn-rtc-pool (mv-nth 2 (fn-ovr-put-probe group number server v h j limit fn-rtc-st fn-arena fn-cat)))) (len (fn-rtc-pool fn-rtc-st)))
(equal (fn-rtc-b-owner (fn-rtc-buffer k (mv-nth 2 (fn-ovr-put-probe group number server v h j limit fn-rtc-st fn-arena fn-cat)))) (fn-rtc-b-owner (fn-rtc-buffer k fn-rtc-st)))
(equal (fn-rtc-b-gen (fn-rtc-buffer k (mv-nth 2 (fn-ovr-put-probe group number server v h j limit fn-rtc-st fn-arena fn-cat)))) (fn-rtc-b-gen (fn-rtc-buffer k fn-rtc-st)))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories '(fn-ovr-put-probe fn-ovrlp-append-loop-frame fn-ovrlp-dsw-append-frame fn-ovrlp-dsw-decimal-frame fn-ovrlp-ovr-wcopy-string-frame fn-ovrlp-ovr-put-octets-frame fn-ovrlp-ovr-put-string-frame fn-ovrlp-ovr-put-decimal-field-frame fn-ovrlp-ovr-put-decimal-frame fn-ovrlp-ovr-put-xref-frame fn-ovrlp-ovr-put-decimal-field-tab-frame fn-ovrlp-ovr-put-decimal-tab-frame fn-ovrlp-ovr-put-fields-frame fn-ovrlp-ovr-put-served-xref-frame fn-ovrlp-ovr-put-column-line-frame fn-ovrlp-ovr-put-number-frame mv-nth zp car-cons cdr-cons (:type-prescription fn-dsw-append) (:type-prescription fn-ovr-fill)) (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-ovr-fill-frame (implies (natp h) (and (equal (fn-rtc-config (mv-nth 3 (fn-ovr-fill group number last top owedp legacyp room server v h j fn-rtc-st fn-arena fn-cat))) (fn-rtc-config fn-rtc-st))
(equal (fn-rtc-slots (mv-nth 3 (fn-ovr-fill group number last top owedp legacyp room server v h j fn-rtc-st fn-arena fn-cat))) (fn-rtc-slots fn-rtc-st))
(equal (fn-rtc-uses (mv-nth 3 (fn-ovr-fill group number last top owedp legacyp room server v h j fn-rtc-st fn-arena fn-cat))) (fn-rtc-uses fn-rtc-st))
(equal (fn-rtc-next-op (mv-nth 3 (fn-ovr-fill group number last top owedp legacyp room server v h j fn-rtc-st fn-arena fn-cat))) (fn-rtc-next-op fn-rtc-st))
(equal (len (fn-rtc-pool (mv-nth 3 (fn-ovr-fill group number last top owedp legacyp room server v h j fn-rtc-st fn-arena fn-cat)))) (len (fn-rtc-pool fn-rtc-st)))
(equal (fn-rtc-b-owner (fn-rtc-buffer k (mv-nth 3 (fn-ovr-fill group number last top owedp legacyp room server v h j fn-rtc-st fn-arena fn-cat)))) (fn-rtc-b-owner (fn-rtc-buffer k fn-rtc-st)))
(equal (fn-rtc-b-gen (fn-rtc-buffer k (mv-nth 3 (fn-ovr-fill group number last top owedp legacyp room server v h j fn-rtc-st fn-arena fn-cat)))) (fn-rtc-b-gen (fn-rtc-buffer k fn-rtc-st)))))
 :hints (("Goal" :induct (fn-ovr-fill group number last top owedp legacyp room server v h j fn-rtc-st fn-arena fn-cat) :in-theory (union-theories '(fn-ovr-fill fn-ovrlp-append-loop-frame fn-ovrlp-dsw-append-frame fn-ovrlp-dsw-decimal-frame fn-ovrlp-ovr-wcopy-string-frame fn-ovrlp-ovr-put-octets-frame fn-ovrlp-ovr-put-string-frame fn-ovrlp-ovr-put-decimal-field-frame fn-ovrlp-ovr-put-decimal-frame fn-ovrlp-ovr-put-xref-frame fn-ovrlp-ovr-put-decimal-field-tab-frame fn-ovrlp-ovr-put-decimal-tab-frame fn-ovrlp-ovr-put-fields-frame fn-ovrlp-ovr-put-served-xref-frame fn-ovrlp-ovr-put-column-line-frame fn-ovrlp-ovr-put-number-frame fn-ovrlp-ovr-put-probe-frame mv-nth zp car-cons cdr-cons (:type-prescription fn-dsw-append) (:type-prescription fn-ovr-fill)) (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-ovr-quantum-frame (implies (natp h) (and (equal (fn-rtc-config (mv-nth 3 (fn-ovr-quantum cur w h base limit fn-rtc-st fn-arena fn-cat))) (fn-rtc-config fn-rtc-st))
(equal (fn-rtc-slots (mv-nth 3 (fn-ovr-quantum cur w h base limit fn-rtc-st fn-arena fn-cat))) (fn-rtc-slots fn-rtc-st))
(equal (fn-rtc-uses (mv-nth 3 (fn-ovr-quantum cur w h base limit fn-rtc-st fn-arena fn-cat))) (fn-rtc-uses fn-rtc-st))
(equal (fn-rtc-next-op (mv-nth 3 (fn-ovr-quantum cur w h base limit fn-rtc-st fn-arena fn-cat))) (fn-rtc-next-op fn-rtc-st))
(equal (len (fn-rtc-pool (mv-nth 3 (fn-ovr-quantum cur w h base limit fn-rtc-st fn-arena fn-cat)))) (len (fn-rtc-pool fn-rtc-st)))
(equal (fn-rtc-b-owner (fn-rtc-buffer k (mv-nth 3 (fn-ovr-quantum cur w h base limit fn-rtc-st fn-arena fn-cat)))) (fn-rtc-b-owner (fn-rtc-buffer k fn-rtc-st)))
(equal (fn-rtc-b-gen (fn-rtc-buffer k (mv-nth 3 (fn-ovr-quantum cur w h base limit fn-rtc-st fn-arena fn-cat)))) (fn-rtc-b-gen (fn-rtc-buffer k fn-rtc-st)))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories '(fn-ovr-quantum fn-ovrlp-append-loop-frame fn-ovrlp-dsw-append-frame fn-ovrlp-dsw-decimal-frame fn-ovrlp-ovr-wcopy-string-frame fn-ovrlp-ovr-put-octets-frame fn-ovrlp-ovr-put-string-frame fn-ovrlp-ovr-put-decimal-field-frame fn-ovrlp-ovr-put-decimal-frame fn-ovrlp-ovr-put-xref-frame fn-ovrlp-ovr-put-decimal-field-tab-frame fn-ovrlp-ovr-put-decimal-tab-frame fn-ovrlp-ovr-put-fields-frame fn-ovrlp-ovr-put-served-xref-frame fn-ovrlp-ovr-put-column-line-frame fn-ovrlp-ovr-put-number-frame fn-ovrlp-ovr-put-probe-frame fn-ovrlp-ovr-fill-frame mv-nth zp car-cons cdr-cons (:type-prescription fn-dsw-append) (:type-prescription fn-ovr-fill)) (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-submit-keeps-hll
 (implies (and (fn-hll-invp s) (fn-hl-render-ready-p h id inc s))
  (fn-hll-invp (mv-nth 0 (fn-rtc-x-request (list :submit :send handle nil) id inc s))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-hld-workspace-owner-is-active)
        (:instance fn-hld-request-keeps-invp (r (list :submit :send handle nil))))
  :in-theory (union-theories '(fn-hld-hll-invp-is fn-hld-hll-invp-is-generic-invp
   fn-hld-hll-invp-st-p fn-rtc-x-request-is fn-hl-render-ready-p
   fn-rtc-invp-is-core-and-admission fn-rtc-get-of-cons
   (:executable-counterpart fn-rtc-get) (:executable-counterpart nfix)
   car-cons cdr-cons mv-nth zp)
   (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-kl12
  (implies (fn-hll-invp st)
           (fn-hll-invp (mv-nth 4 (fn-ovr-lease-quantum cur w h id inc st fn-arena fn-cat))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-ovrlp-submit-keeps-hll (s (mv-nth 3 (fn-ovr-quantum cur w h 0 (fn-rtc-buf-cap h (fn-rtc-config st)) st fn-arena fn-cat)))
   (handle (list h (fn-rtc-st-gen h st) 0 (mv-nth 2 (fn-ovr-quantum cur w h 0 (fn-rtc-buf-cap h (fn-rtc-config st)) st fn-arena fn-cat))))))
 :in-theory (union-theories '(fn-ovr-lease-quantum fn-hld-readers
  fn-ovrlp-ovr-quantum-keeps-hll fn-ovrlp-ovr-quantum-frame fn-hl-render-ready-p
  fn-rtc-x-live-p-is fn-rtc-st-config fn-rtc-st$a-config
  mv-nth zp posp car-cons cdr-cons
  (:type-prescription fn-ovr-quantum) (:type-prescription fn-rtc-x-request))
 (theory 'minimal-theory))))))

(local (set-default-hints '((quote (:use fn-ovrlp-kl12 :in-theory (theory 'minimal-theory))))))
(defthm fn-ovr-lease-quantum-keeps-invp
  (implies (fn-hll-invp st)
           (fn-hll-invp (mv-nth 4 (fn-ovr-lease-quantum cur w h id inc st fn-arena fn-cat)))))
(local (set-default-hints nil))

; The in-place executor agrees with the proved leased send driver.
(local (defthm fn-ovrlp-hll-is-ap
 (implies (fn-hll-invp s) (fn-rtc-st$ap s))
 :hints (("Goal" :use fn-hld-hll-invp-st-p :in-theory (union-theories '(fn-hld-hll-invp-st-p fn-dsw-st-p-is-abstract-recognizer)
 (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-cap-natural (natp (fn-rtc-buf-cap h cfg))
 :rule-classes :type-prescription
 :hints (("Goal" :in-theory (union-theories '(fn-rtc-buf-cap fn-rtc-capf fn-rtc-capl nfix natp) (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-quantum-step-facts
 (implies (and (fn-hll-invp s) (fn-ovw-cursorp cur)
 (posp (mv-nth 0 (fn-ovr-quantum cur w h 0 (fn-rtc-buf-cap h (fn-rtc-config s)) s fn-arena fn-cat))))
 (let* ((q (fn-ovr-quantum cur w h 0 (fn-rtc-buf-cap h (fn-rtc-config s)) s fn-arena fn-cat))
        (out (mv-nth 0 (fn-ovw-step cur (mv-nth 0 q) fn-arena fn-cat))))
  (and (fn-cbor-octet-listp out)
       (equal (mv-nth 2 q) (len out))
       (<= (len out) (fn-rtc-buf-cap h (fn-rtc-config s)))
       (equal (mv-nth 1 q) (mv-nth 1 (fn-ovw-step cur (mv-nth 0 q) fn-arena fn-cat)))
       (equal (mv-nth 3 q) (fn-rtc-st$a-puts h 0 out s)))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-ovr-quantum-is-the-step (base 0) (limit (fn-rtc-buf-cap h (fn-rtc-config s))))
       (:instance fn-ovr-quantum-taken-is-splice-okp (base 0) (limit (fn-rtc-buf-cap h (fn-rtc-config s))))
       (:instance fn-ovr-quantum-within-the-lease (base 0) (limit (fn-rtc-buf-cap h (fn-rtc-config s)))))
 :in-theory (union-theories '(fn-ovrlp-hll-is-ap fn-ovrlp-cap-natural
 fn-rtc-splice-okp fn-dsw-splice-is-puts fn-ovrqp-nfix-natural
 natp-compound-recognizer mv-nth zp posp car-cons cdr-cons len unicity-of-0 fn-hlr-fix-len
 (:type-prescription len) (:type-prescription fn-ovr-quantum) (:type-prescription fn-ovw-step)
 (:executable-counterpart nfix)) (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-executor-taken
 (implies (and (fn-hll-invp s) (fn-ovw-cursorp cur)
  (fn-hl-render-ready-p h id inc s) (fn-rtc-live-p id inc s)
  (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses s)))
  (posp (mv-nth 0 (fn-ovr-quantum cur w h 0 (fn-rtc-buf-cap h (fn-rtc-config s)) s fn-arena fn-cat)))
  (< 0 (mv-nth 2 (fn-ovr-quantum cur w h 0 (fn-rtc-buf-cap h (fn-rtc-config s)) s fn-arena fn-cat))))
 (let* ((q (fn-ovr-quantum cur w h 0 (fn-rtc-buf-cap h (fn-rtc-config s)) s fn-arena fn-cat))
        (n (mv-nth 0 q)) (next (mv-nth 1 q)) (j (mv-nth 2 q))
        (out (mv-nth 0 (fn-ovw-step cur n fn-arena fn-cat)))
        (hq (fn-hld-quantum h id inc out s)))
  (equal (fn-ovr-lease-quantum cur w h id inc s fn-arena fn-cat)
         (list n next j (mv-nth 1 hq) (mv-nth 0 hq)))))
 :hints (("Goal" :do-not-induct t :use (fn-ovrlp-quantum-step-facts
 (:instance fn-hld-copy-is-puts (i 0) (st s)
  (out (mv-nth 0 (fn-ovw-step cur (mv-nth 0 (fn-ovr-quantum cur w h 0
  (fn-rtc-buf-cap h (fn-rtc-config s)) s fn-arena fn-cat)) fn-arena fn-cat)))))
 :in-theory (union-theories '(fn-ovr-lease-quantum fn-hld-quantum fn-hld-readers
   fn-hl-render-ready-p fn-rtc-x-live-p-is fn-dss-out-len-is-len
   fn-hld-copy-is-puts fn-hld-nthcdr-0 fn-ovrlp-cap-natural
   fn-rtc-st-config fn-rtc-st$a-config fn-ovrqp-nfix-natural
   (:executable-counterpart natp) (:executable-counterpart binary-+) mv-nth zp posp car-cons cdr-cons len
   (:executable-counterpart nfix) (:executable-counterpart len)
   (:type-prescription len) (:type-prescription fn-ovr-quantum)
   (:type-prescription fn-rtc-x-request))
 (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-state-view
 (implies (and (fn-rtc-st$ap s) (natp i) (natp j) (<= i j)
 (<= j (len (fn-rtc-b-bytes (fn-rtc-buffer h s)))))
 (equal (fn-ovr-st-view h i j s)
        (take (- j i) (nthcdr i (fn-rtc-b-bytes (fn-rtc-buffer h s))))))
 :hints (("Goal" :induct (fn-ovr-st-view h i j s)
 :expand ((:free (a d n) (take n (cons a d))))
 :in-theory (union-theories '(fn-ovr-st-view fn-rtc-st-byte fn-rtc-st$a-byte fn-rtc-bytes
 fn-ovrqp-buffer-shape fn-cbor-octet-listp-implies-true-listp fn-ovrqp-nfix-natural
 natp-compound-recognizer fn-rtc-c-nthcdr-is-cons take (:type-prescription len)
 nth (:type-prescription nthcdr) true-listp nthcdr mv-nth zp car-cons cdr-cons
 (:executable-counterpart natp) (:executable-counterpart binary-+)
 associativity-of-+ commutativity-of-+ commutativity-2-of-+ inverse-of-+ distributivity-of-minus-over-+ fn-ovrqp-fold-sums)
 (set-difference-theories (fn-dss-measure-theory) '()))))))

; Send submission preserves the byte slice read before completion.
(local (defthm fn-ovrlp-ready-generation
 (implies (and (fn-rtc-invp s) (fn-hl-render-ready-p h id inc s))
  (natp (fn-rtc-get 0 (fn-rtc-buffer h s))))
 :hints (("Goal" :use (fn-rtc-invp-implies-core-invp fn-rtc-core-invp-buffer)
  :in-theory (union-theories '(fn-hl-render-ready-p fn-rtc-buffer-okp fn-rtc-bufferp)
    (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-puts-bytes
 (implies (and (fn-rtc-st$ap s) (fn-hl-render-ready-p h id inc s)
 (fn-cbor-octet-listp out) (<= (len out) (fn-rtc-buf-cap h (fn-rtc-config s))))
 (equal (fn-rtc-b-bytes (fn-rtc-buffer h (fn-rtc-st$a-puts h 0 out s)))
        (fn-rtc-splice (fn-rtc-b-bytes (fn-rtc-buffer h s)) 0 out)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-dsw-splice-is-puts (j 0) (data out))
       (:instance fn-ovrqp-splice-frames (j 0) (data out)))
 :in-theory (union-theories '(fn-hl-render-ready-p fn-rtc-splice-okp fn-rtc-splice-target-p
 fn-rtc-get-of-cons natp zp nfix len fn-hlr-fix-len unicity-of-0
 (:type-prescription len) (:executable-counterpart fn-rtc-get)
 (:executable-counterpart binary-+) (:executable-counterpart natp)
 (:executable-counterpart fn-cbor-octet-listp) car-cons cdr-cons)
 (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-take-prefix
 (implies (true-listp out)
  (and (equal (take (len out) (append out rest)) out)
       (<= (len out) (len (append out rest)))))
 :hints (("Goal" :induct (len out) :expand ((:free (n a d) (take n (cons a d)))) :in-theory
 (union-theories '(take binary-append len true-listp zp car-cons cdr-cons
 (:type-prescription len) unicity-of-0 car-cdr-elim fn-ovrqp-fold-sums fn-hlr-fix-len fn-ovrqp-len-append)
 (fn-dss-measure-theory))))))

(local (defthm fn-ovrlp-take-splice-0
 (implies (true-listp out)
  (and (equal (take (len out) (fn-rtc-splice bytes 0 out)) out)
       (<= (len out) (len (fn-rtc-splice bytes 0 out)))))
 :hints (("Goal" :in-theory (union-theories '(min fn-rtc-true-list-fix-identity fn-hlr-fix-len fn-rtc-splice fn-ovrlp-take-prefix
 take nthcdr binary-append fn-ovrqp-len-append len zp nfix natp car-cons cdr-cons
 (:executable-counterpart binary-+) (:type-prescription len)) (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-hlq-bytes
 (implies (and (fn-hll-invp s) (fn-hl-render-ready-p h id inc s)
 (fn-rtc-live-p id inc s) (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses s)))
 (consp out) (fn-cbor-octet-listp out) (<= (len out) (fn-rtc-buf-cap h (fn-rtc-config s))))
 (equal (fn-rtc-b-bytes (fn-rtc-buffer h (fn-hl-quantum-state h out id inc s)))
        (fn-rtc-splice (fn-rtc-b-bytes (fn-rtc-buffer h s)) 0 out)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-hlr-submit-send (p (fn-rtc-st$a-puts h 0 out s))
 (g (fn-rtc-b-gen (fn-rtc-buffer h s))) (n (len out)))
 (:instance fn-ovrlp-ready-generation)
 (:instance fn-ovrlp-take-splice-0 (bytes (fn-rtc-b-bytes (fn-rtc-buffer h s))))
 (:instance fn-hlr-puts-frame (off 0) (w out) (k h))
 (:instance fn-ovrlp-puts-bytes)
 (:instance fn-hlr-buffer-facts)
 (:instance fn-hlr-pool-len-facts))
 :in-theory (union-theories '(fn-hl-quantum-state fn-hl-render-ready-p
 fn-hld-hll-invp-is-generic-invp fn-ovrlp-hll-is-ap fn-ovrlp-cap-natural
 fn-hlr-puts-frame fn-hlr-puts-len2 fn-hlr-live-of-puts
 fn-rtc-b-gen fn-ovrqp-nfix-natural fn-ovrqp-puts-compose fn-ovrlp-puts-bytes
 fn-rtc-issue-frame fn-rtc-buffer-of-with fn-ovrqp-get-of-set fn-ovrqp-buffer-shape
 fn-rtc-b-bytes fn-rtc-b-owner fn-rtc-get-of-cons fn-rtc-get nfix natp zp
 fn-cbor-octet-listp-implies-true-listp fn-hlr-fix-len fn-rtc-with-accessors fn-rtc-request-config-frame
 mv-nth car-cons cdr-cons len unicity-of-0
 (:executable-counterpart fn-rtc-get) (:executable-counterpart nfix)
 (:executable-counterpart natp) (:executable-counterpart binary-+)
 (:type-prescription len) (:type-prescription fn-rtc-req-submit))
 (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-driver-view
 (implies (and (fn-hll-invp s) (fn-hl-render-ready-p h id inc s)
 (fn-rtc-live-p id inc s) (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses s)))
 (consp out) (fn-cbor-octet-listp out) (<= (len out) (fn-rtc-buf-cap h (fn-rtc-config s))))
 (equal (fn-ovr-st-view h 0 (len out) (mv-nth 0 (fn-hld-quantum h id inc out s))) out))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-hlr-quantum-succeeds (st s))
 (:instance fn-hld-quantum-keeps-invp (st s))
 (:instance fn-ovrlp-hll-is-ap (s (mv-nth 0 (fn-hld-quantum h id inc out s))))
 (:instance fn-hlr-next-op-true)
 (:instance fn-hld-quantum-is-the-quantum-state (st s))
 (:instance fn-ovrlp-hlq-bytes)
 (:instance fn-ovrlp-take-splice-0 (bytes (fn-rtc-b-bytes (fn-rtc-buffer h s))))
 (:instance fn-ovrlp-state-view (s (mv-nth 0 (fn-hld-quantum h id inc out s))) (i 0) (j (len out))))
 :in-theory (union-theories '(fn-hld-hll-invp-is-generic-invp fn-hld-hll-invp-st-p
 fn-dss-out-p-is-octet-listp fn-ovrlp-hll-is-ap fn-hld-quantum-keeps-invp
 fn-hld-nthcdr-0 fn-cbor-octet-listp-implies-true-listp
 natp-compound-recognizer natp mv-nth zp car-cons cdr-cons
 (:type-prescription len) (:executable-counterpart natp)
 (:type-prescription fn-hld-quantum) (:executable-counterpart unary--)
 commutativity-of-+ unicity-of-0 fn-hlr-fix-len)
 (theory 'minimal-theory))))))

; Adaptive windows compose into the full reply; sends restore the lease.
(local (defthm fn-ovrlp-step-listp
 (implies (not (nth 7 cur)) (true-listp (mv-nth 0 (fn-ovw-step cur n fn-arena fn-cat))))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories '(fn-ovw-step fn-nntp-crlf true-listp-append
 (:type-prescription fn-nntp-stuff-lines) fn-ovw-status fn-ovw-empty-text
 (:type-prescription fn-nntp-string-octets) mv-nth zp car-cons cdr-cons
 (:type-prescription fn-ovw-step) (:type-prescription binary-append)
 (:executable-counterpart true-listp)) (theory 'minimal-theory))))))

(local (defun fn-ovrp-canon (cur)
   (declare (xargs :verify-guards nil))
   (fn-ovw-cursor (nth 0 cur) (nfix (nth 1 cur)) (nfix (nth 2 cur)) (nth 3 cur) (nth 4 cur)
                  (nth 5 cur) (nth 6 cur))))

(local (defthm fn-ovrp-canon-step
   (implies (and (consp cur) (not (nth 7 cur)))
            (equal (fn-ovw-step (fn-ovrp-canon cur) w fn-arena fn-cat)
                   (fn-ovw-step cur w fn-arena fn-cat)))
   :hints (("Goal" :in-theory (e/d (fn-ovw-step fn-ovrp-canon fn-ovw-cursor nth zp nfix (:executable-counterpart nth) (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart unary--) car-cons cdr-cons) (fn-ovw-hdr-step fn-ovw-lines fn-nntp-stuff-lines fn-ovw-status))))))

(local (defthm fn-ovrlp-canon-consp
 (consp (fn-ovrp-canon cur))
 :hints (("Goal" :in-theory (union-theories '(fn-ovrp-canon fn-ovw-cursor) (theory 'minimal-theory))))))

(local (defthm fn-ovrp-canon-run
   (implies (and (consp cur) (not (nth 7 cur)))
            (equal (fn-ovw-run (fn-ovrp-canon cur) w fn-arena fn-cat)
                   (fn-ovw-run cur w fn-arena fn-cat)))
   :hints (("Goal" :in-theory (e/d ((:type-prescription fn-ovrp-canon)) (fn-ovw-step (:definition fn-ovrp-canon)))
            :use fn-ovrlp-canon-consp
            :expand ((fn-ovw-run (fn-ovrp-canon cur) w fn-arena fn-cat)
                     (fn-ovw-run cur w fn-arena fn-cat))))))

(local (defthm fn-ovrp-run-indep
   (implies (and (consp cur) (not (nth 7 cur)) (natp (nth 3 cur)))
            (equal (fn-ovw-run cur w fn-arena fn-cat)
                   (fn-ovw-run cur w2 fn-arena fn-cat)))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable fn-ovw-run fn-ovrp-canon-run)
            :use (fn-ovrp-canon-run
                  (:instance fn-ovrp-canon-run (w w2))
                  (:instance fn-ovw-run-is-reply (k (nfix (nth 1 cur))) (top (nfix (nth 2 cur)))
                             (group (nth 0 cur)) (v (nth 3 cur)) (legacyp (nth 4 cur))
                             (owedp (nth 5 cur)) (server (nth 6 cur)))
                  (:instance fn-ovw-run-is-reply (k (nfix (nth 1 cur))) (top (nfix (nth 2 cur)))
                             (group (nth 0 cur)) (v (nth 3 cur)) (legacyp (nth 4 cur))
                             (owedp (nth 5 cur)) (server (nth 6 cur)) (w w2)))))))

(local (defthm fn-ovrp-step-next-live
   (implies (and (not (nth 7 cur)) (mv-nth 1 (fn-ovw-step cur n fn-arena fn-cat)))
            (not (nth 7 (mv-nth 1 (fn-ovw-step cur n fn-arena fn-cat)))))
   :hints (("Goal" :in-theory (e/d (fn-ovw-step fn-ovw-cursor nth zp nfix car-cons cdr-cons (:executable-counterpart nth) (:executable-counterpart zp) (:executable-counterpart nfix) (:executable-counterpart binary-+) (:executable-counterpart unary--))
                                   (fn-ovw-hdr-step fn-ovw-lines fn-nntp-stuff-lines fn-ovw-status))))))

(local (defthm fn-ovrp-run-split
   (implies (and (fn-ovw-cursorp cur) (consp cur) (not (nth 7 cur)))
            (equal (fn-ovw-run cur w fn-arena fn-cat)
                   (append (mv-nth 0 (fn-ovw-step cur n fn-arena fn-cat))
                           (if (mv-nth 1 (fn-ovw-step cur n fn-arena fn-cat))
                               (fn-ovw-run (mv-nth 1 (fn-ovw-step cur n fn-arena fn-cat)) w fn-arena fn-cat)
                             nil))))
   :hints (("Goal" :in-theory (e/d (append-to-nil fn-ovw-cursorp natp natp-compound-recognizer) (fn-ovw-step fn-ovw-run fn-ovrp-canon fn-ovrp-step-next-live fn-ovw-step-keeps-cursorp))
            :use (fn-ovrlp-step-listp (:instance fn-ovrp-run-indep (w w) (w2 n))
                  (:instance fn-ovrp-run-indep (w n) (w2 w) (cur (mv-nth 1 (fn-ovw-step cur n fn-arena fn-cat))))
                  (:instance fn-ovrp-step-next-live)
                  (:instance fn-ovw-step-progresses (w n))
                  (:instance fn-ovw-step-keeps-cursorp (w n)))
            :expand ((fn-ovw-run cur n fn-arena fn-cat))))))

(local (defthm fn-ovrp-run-fold-more
   (implies (and (fn-ovw-cursorp cur) (consp cur) (not (nth 7 cur))
                 (mv-nth 1 (fn-ovw-step cur n fn-arena fn-cat)))
            (equal (append (mv-nth 0 (fn-ovw-step cur n fn-arena fn-cat))
                           (fn-ovw-run (mv-nth 1 (fn-ovw-step cur n fn-arena fn-cat)) w fn-arena fn-cat))
                   (fn-ovw-run cur w fn-arena fn-cat)))
   :hints (("Goal" :use (fn-ovrp-run-split fn-ovrlp-step-listp) :in-theory (e/d (append-to-nil) (fn-ovrp-run-split fn-ovw-step fn-ovw-run))))))

(local (defthm fn-ovrp-run-fold-last
   (implies (and (fn-ovw-cursorp cur) (consp cur) (not (nth 7 cur))
                 (not (mv-nth 1 (fn-ovw-step cur n fn-arena fn-cat))))
            (equal (mv-nth 0 (fn-ovw-step cur n fn-arena fn-cat))
                   (fn-ovw-run cur w fn-arena fn-cat)))
   :hints (("Goal" :use (fn-ovrp-run-split fn-ovrlp-step-listp) :in-theory (e/d (append-to-nil) (fn-ovrp-run-split fn-ovw-step fn-ovw-run))))))

(local (defthm fn-ovrlp-run-fold-more-car
   (implies (and (fn-ovw-cursorp cur) (consp cur) (not (nth 7 cur))
                 (mv-nth 1 (fn-ovw-step cur n fn-arena fn-cat)))
            (equal (append (car (fn-ovw-step cur n fn-arena fn-cat))
                           (fn-ovw-run (mv-nth 1 (fn-ovw-step cur n fn-arena fn-cat)) w fn-arena fn-cat))
                   (fn-ovw-run cur w fn-arena fn-cat)))
   :hints (("Goal" :use fn-ovrp-run-fold-more
 :in-theory (union-theories '(mv-nth zp (:type-prescription fn-ovw-step))
 (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-executor-positions
 (implies (and (fn-hl-render-ready-p h id inc s) (fn-rtc-live-p id inc s)
 (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses s))))
 (let ((q (fn-ovr-quantum cur w h 0 (fn-rtc-buf-cap h (fn-rtc-config s)) s fn-arena fn-cat))
       (e (fn-ovr-lease-quantum cur w h id inc s fn-arena fn-cat)))
 (and (equal (mv-nth 0 e) (mv-nth 0 q))
      (equal (mv-nth 1 e) (mv-nth 1 q))
      (equal (mv-nth 2 e) (mv-nth 2 q)))))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories '(fn-ovr-lease-quantum fn-hld-readers fn-hl-render-ready-p
 fn-rtc-x-live-p-is mv-nth zp posp car-cons cdr-cons
 (:type-prescription fn-ovr-quantum) (:type-prescription fn-rtc-x-request))
 (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-executor-finished
 (implies (and (fn-hll-invp s) (fn-ovw-cursorp cur)
 (fn-hl-render-ready-p h id inc s) (fn-rtc-live-p id inc s)
 (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses s)))
 (posp (mv-nth 0 (fn-ovr-lease-quantum cur w h id inc s fn-arena fn-cat)))
 (< 0 (mv-nth 2 (fn-ovr-lease-quantum cur w h id inc s fn-arena fn-cat))))
 (let* ((e (fn-ovr-lease-quantum cur w h id inc s fn-arena fn-cat))
        (n (mv-nth 0 e)) (j (mv-nth 2 e)) (op (mv-nth 3 e)) (q (mv-nth 4 e))
        (out (mv-nth 0 (fn-ovw-step cur n fn-arena fn-cat)))
        (s2 (mv-nth 0 (fn-hld-sent id inc op (list :done j) q))))
 (and op (equal op (fn-rtc-next-op s))
      (equal (fn-ovr-st-view h 0 j q) out)
      (fn-hll-invp s2) (fn-hl-render-ready-p h id inc s2) (fn-rtc-live-p id inc s2)
      (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses s2)))
      (equal (fn-rtc-config s2) (fn-rtc-config s)))))
 :hints (("Goal" :do-not-induct t
 :use (fn-ovrlp-executor-taken fn-ovrlp-quantum-step-facts
 (:instance fn-hlr-window (st s)
  (out (mv-nth 0 (fn-ovw-step cur (mv-nth 0 (fn-ovr-lease-quantum cur w h id inc s fn-arena fn-cat)) fn-arena fn-cat))))
 (:instance fn-ovrlp-driver-view
  (out (mv-nth 0 (fn-ovw-step cur (mv-nth 0 (fn-ovr-lease-quantum cur w h id inc s fn-arena fn-cat)) fn-arena fn-cat))))
 (:instance fn-hlr-octets-atom2
  (out (mv-nth 0 (fn-ovw-step cur (mv-nth 0 (fn-ovr-lease-quantum cur w h id inc s fn-arena fn-cat)) fn-arena fn-cat)))))
 :in-theory (union-theories '(fn-ovrlp-executor-positions fn-dss-out-p-is-octet-listp
 fn-ovrlp-hll-is-ap fn-hld-hll-invp-is-generic-invp
 mv-nth zp posp car-cons cdr-cons len (:type-prescription len)
 (:type-prescription fn-ovr-lease-quantum) (:type-prescription fn-ovr-quantum)
 (:type-prescription fn-hld-quantum) (:type-prescription fn-ovw-step)
 (:executable-counterpart len) (:executable-counterpart <))
 (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-executor-empty
 (implies (and (fn-hll-invp s) (fn-ovw-cursorp cur)
 (fn-hl-render-ready-p h id inc s) (fn-rtc-live-p id inc s)
 (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses s)))
 (posp (mv-nth 0 (fn-ovr-lease-quantum cur w h id inc s fn-arena fn-cat)))
 (equal (mv-nth 2 (fn-ovr-lease-quantum cur w h id inc s fn-arena fn-cat)) 0))
 (let ((e (fn-ovr-lease-quantum cur w h id inc s fn-arena fn-cat)))
 (and (not (mv-nth 3 e)) (equal (mv-nth 4 e) s)
 (equal (mv-nth 0 (fn-ovw-step cur (mv-nth 0 e) fn-arena fn-cat)) nil))))
 :hints (("Goal" :do-not-induct t
 :use (fn-ovrlp-quantum-step-facts fn-ovrlp-executor-positions
 (:instance fn-hlr-octets-atom2
 (out (mv-nth 0 (fn-ovw-step cur (mv-nth 0 (fn-ovr-lease-quantum cur w h id inc s fn-arena fn-cat)) fn-arena fn-cat)))))
 :in-theory (union-theories '(fn-ovr-lease-quantum fn-hld-readers fn-hl-render-ready-p
 fn-rtc-x-live-p-is fn-rtc-st$a-puts fn-dss-out-p-is-octet-listp fn-hlr-len-pos
 mv-nth zp posp car-cons cdr-cons len
 (:type-prescription len) (:type-prescription fn-ovr-quantum)
 (:type-prescription fn-ovr-lease-quantum) (:type-prescription fn-rtc-x-request)
 (:type-prescription fn-ovw-step) (:executable-counterpart <)
 (:executable-counterpart len) (:executable-counterpart nfix))
 (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-positive-cursor
 (implies (posp (mv-nth 0 (fn-ovr-quantum cur w h base limit s fn-arena fn-cat)))
 (and (consp cur) (not (nth 7 cur))))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories '(fn-ovr-quantum mv-nth zp posp car-cons cdr-cons
 (:type-prescription fn-ovr-fill) (:type-prescription fn-dsw-append)
 (:executable-counterpart integerp) (:executable-counterpart <))
 (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-executor-window
 (implies (and (fn-hll-invp s) (fn-ovw-cursorp cur)
 (fn-hl-render-ready-p h id inc s) (fn-rtc-live-p id inc s)
 (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses s)))
 (posp (mv-nth 0 (fn-ovr-lease-quantum cur w h id inc s fn-arena fn-cat))))
 (let* ((e (fn-ovr-lease-quantum cur w h id inc s fn-arena fn-cat))
        (n (mv-nth 0 e)) (next (mv-nth 1 e)) (j (mv-nth 2 e))
        (op (mv-nth 3 e)) (q (mv-nth 4 e))
        (sent (if op (fn-ovr-st-view h 0 j q) nil))
        (s2 (if op (mv-nth 0 (fn-hld-sent id inc op (list :done j) q)) q)))
  (and (consp cur) (not (nth 7 cur))
       (equal sent (mv-nth 0 (fn-ovw-step cur n fn-arena fn-cat)))
       (equal next (mv-nth 1 (fn-ovw-step cur n fn-arena fn-cat)))
       (fn-hll-invp s2) (fn-hl-render-ready-p h id inc s2) (fn-rtc-live-p id inc s2)
       (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses s2)))
       (equal (fn-rtc-config s2) (fn-rtc-config s)))))
 :hints (("Goal" :do-not-induct t
 :cases ((< 0 (mv-nth 2 (fn-ovr-lease-quantum cur w h id inc s fn-arena fn-cat))))
 :use (fn-ovrlp-executor-finished fn-ovrlp-executor-empty
 fn-ovrlp-executor-positions fn-ovrlp-quantum-step-facts
 (:instance fn-ovrlp-positive-cursor (base 0) (limit (fn-rtc-buf-cap h (fn-rtc-config s)))))
 :in-theory (union-theories '(fn-ovrlp-executor-positions natp-compound-recognizer
 mv-nth zp posp car-cons cdr-cons len (:type-prescription len)
 (:type-prescription fn-ovr-quantum) (:type-prescription fn-ovr-lease-quantum)
 (:type-prescription fn-ovw-step) (:executable-counterpart len))
 (fn-dss-measure-theory))))))

(local (defthm fn-ovrlp-run-atom
 (implies (not (consp cur)) (equal (fn-ovw-run cur w fn-arena fn-cat) nil))
 :hints (("Goal" :in-theory (union-theories '(fn-ovw-run) (theory 'minimal-theory))))))

(local (defthm fn-ovrlp-kl5
  (implies (and (fn-hll-invp st)
                (fn-hl-render-ready-p h id inc st)
                (fn-rtc-live-p id inc st)
                (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses st)))
                (fn-ovw-cursorp cur)
                (mv-nth 0 (fn-ovr-lease-run cur w k h id inc st fn-arena fn-cat)))
           (equal (mv-nth 1 (fn-ovr-lease-run cur w k h id inc st fn-arena fn-cat))
                  (fn-ovw-run cur w fn-arena fn-cat)))
 :hints (("Goal" :induct (fn-ovr-lease-run cur w k h id inc st fn-arena fn-cat)
 :in-theory (union-theories '(fn-ovr-lease-run (:induction fn-ovr-lease-run)
 fn-ovrlp-executor-window fn-ovrlp-run-atom
 fn-ovw-step-keeps-cursorp fn-ovrlp-run-fold-more-car fn-ovrp-run-fold-last
 fn-ovrp-step-next-live fn-ovrlp-step-listp append-to-nil binary-append
 mv-nth zp posp car-cons cdr-cons
 (:type-prescription fn-ovr-lease-quantum) (:type-prescription fn-ovr-quantum)
 (:type-prescription fn-ovw-step) (:type-prescription fn-hld-sent)
 (:executable-counterpart len) (:type-prescription len))
 (fn-dss-measure-theory)))
 ("Subgoal *1/5" :use ((:instance fn-ovrlp-executor-window (s st))
 (:instance fn-ovrp-run-split
  (n (mv-nth 0 (fn-ovr-lease-quantum cur w h id inc st fn-arena fn-cat))))))
 ("Subgoal *1/4" :use (:instance fn-ovrlp-executor-window (s st))))))

(local (set-default-hints '((quote (:use fn-ovrlp-kl5 :in-theory (theory 'minimal-theory))))))
(defthm fn-ovr-lease-run-is-the-windowed-reply
  (implies (and (fn-hll-invp st)
                (fn-hl-render-ready-p h id inc st)
                (fn-rtc-live-p id inc st)
                (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses st)))
                (fn-ovw-cursorp cur)
                (mv-nth 0 (fn-ovr-lease-run cur w k h id inc st fn-arena fn-cat)))
           (equal (mv-nth 1 (fn-ovr-lease-run cur w k h id inc st fn-arena fn-cat))
                  (fn-ovw-run cur w fn-arena fn-cat))))
(local (set-default-hints nil))

; Progress follows the preserved probe budget and decreasing cursor measure.
(local (defthm fn-ovrlp-fuel-positive
 (implies (and (natp r) (< r (nfix k))) (posp k))
 :hints (("Goal" :in-theory (union-theories '(nfix natp posp) (fn-dss-measure-theory))))))

(local (defthm fn-ovrlp-fuel-next
 (implies (and (natp r) (natp r2) (< r2 r) (< r (nfix k)))
 (< r2 (nfix (- k 1))))
 :hints (("Goal" :in-theory (union-theories '(nfix natp posp) (fn-dss-measure-theory))))))

(local (defthm fn-ovrlp-remaining-natural
 (natp (fn-ovw-remaining cur)) :rule-classes :type-prescription
 :hints (("Goal" :in-theory (union-theories '(fn-ovw-remaining nfix natp)
 (fn-dss-measure-theory))))))

(local (defthm fn-ovrlp-kl6
  (implies (and (fn-hll-invp st)
                (fn-hl-render-ready-p h id inc st)
                (fn-rtc-live-p id inc st)
                (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses st)))
                (fn-ovw-cursorp cur) (not (nth 7 cur)) (fn-cbor-octet-listp (nth 6 cur))
                (unsigned-byte-p 59 (fn-rtc-buf-cap h (fn-rtc-config st)))
                (fn-ovr-probes-within (nth 0 cur) (nfix (nth 1 cur)) (nfix (nth 2 cur)) (nth 6 cur)
                                      (nfix (nth 3 cur)) l fn-arena fn-cat)
                (<= (+ (nfix l) (fn-ovr-frame-max)) (fn-rtc-buf-cap h (fn-rtc-config st)))
                (< (fn-ovw-remaining cur) (nfix k)))
           (mv-nth 0 (fn-ovr-lease-run cur w k h id inc st fn-arena fn-cat)))
 :hints (("Goal" :induct (fn-ovr-lease-run cur w k h id inc st fn-arena fn-cat)
 :in-theory (union-theories '(fn-ovr-lease-run (:induction fn-ovr-lease-run)
 fn-ovrlp-hll-is-ap fn-ovrlp-executor-window fn-ovw-step-keeps-cursorp
 fn-ovrlp-fuel-positive fn-ovrlp-fuel-next fn-ovrlp-remaining-natural
 fn-ovrqp-nfix-natural fn-ovrqp-natural-nfix natp-compound-recognizer
 mv-nth zp posp car-cons cdr-cons
 (:type-prescription fn-ovw-remaining) (:type-prescription fn-ovr-lease-quantum)
 (:type-prescription fn-ovw-step) (:type-prescription fn-hld-sent)
 (:executable-counterpart nfix) (:executable-counterpart natp)) (set-difference-theories (fn-dss-measure-theory) '(natp nfix))))
 ("Subgoal *1/5" :use ((:instance fn-ovr-quantum-progress-under-probes (s st))
 (:instance fn-ovrlp-executor-positions (s st)) (:instance fn-ovrlp-executor-window (s st))
 (:instance fn-ovr-step-keeps-probe-bound (n (mv-nth 0 (fn-ovr-lease-quantum cur w h id inc st fn-arena fn-cat))))
 (:instance fn-ovw-step-progresses (w (mv-nth 0 (fn-ovr-lease-quantum cur w h id inc st fn-arena fn-cat))))))
 ("Subgoal *1/4" :use ((:instance fn-ovr-quantum-progress-under-probes (s st))
 (:instance fn-ovrlp-executor-positions (s st)) (:instance fn-ovrlp-executor-window (s st))
 (:instance fn-ovr-step-keeps-probe-bound (n (mv-nth 0 (fn-ovr-lease-quantum cur w h id inc st fn-arena fn-cat))))
 (:instance fn-ovw-step-progresses (w (mv-nth 0 (fn-ovr-lease-quantum cur w h id inc st fn-arena fn-cat))))))
 ("Subgoal *1/2" :use (:instance fn-ovrlp-fuel-positive (r (fn-ovw-remaining cur))))
 ("Subgoal *1/3" :use ((:instance fn-ovr-quantum-progress-under-probes (s st))
 (:instance fn-ovrlp-executor-positions (s st)) (:instance fn-ovrlp-executor-window (s st))
 (:instance fn-ovr-step-keeps-probe-bound (n (mv-nth 0 (fn-ovr-lease-quantum cur w h id inc st fn-arena fn-cat))))
 (:instance fn-ovw-step-progresses (w (mv-nth 0 (fn-ovr-lease-quantum cur w h id inc st fn-arena fn-cat)))))))))

(local (set-default-hints '((quote (:use fn-ovrlp-kl6 :in-theory (theory 'minimal-theory))))))
(defthm fn-ovr-lease-run-progresses
  (implies (and (fn-hll-invp st)
                (fn-hl-render-ready-p h id inc st)
                (fn-rtc-live-p id inc st)
                (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses st)))
                (fn-ovw-cursorp cur) (not (nth 7 cur)) (fn-cbor-octet-listp (nth 6 cur))
                (unsigned-byte-p 59 (fn-rtc-buf-cap h (fn-rtc-config st)))
                (fn-ovr-probes-within (nth 0 cur) (nfix (nth 1 cur)) (nfix (nth 2 cur)) (nth 6 cur)
                                      (nfix (nth 3 cur)) l fn-arena fn-cat)
                (<= (+ (nfix l) (fn-ovr-frame-max)) (fn-rtc-buf-cap h (fn-rtc-config st)))
                (< (fn-ovw-remaining cur) (nfix k)))
           (mv-nth 0 (fn-ovr-lease-run cur w k h id inc st fn-arena fn-cat))))
(local (set-default-hints nil))

(defthm fn-ovr-over-capl-progresses
  (implies (and (fn-hll-invp st)
                (fn-hl-render-ready-p h id inc st)
                (fn-rtc-live-p id inc st)
                (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses st)))
                (fn-ovw-cursorp cur) (not (nth 7 cur)) (fn-cbor-octet-listp (nth 6 cur))
                (fn-scol-okp fn-arena fn-cat)
                (fn-ovr-rows-within-header a limits fn-arena fn-cat)
                (<= (nfix (fn-article-limit-octets limits)) (nfix hdr))
                (unsigned-byte-p 59 (fn-rtc-buf-cap h (fn-rtc-config st)))
                (<= (fn-ovr-over-capl hdr a (len (nth 6 cur))) (fn-rtc-buf-cap h (fn-rtc-config st)))
                (< (fn-ovw-remaining cur) (nfix k)))
           (mv-nth 0 (fn-ovr-lease-run cur w k h id inc st fn-arena fn-cat))))

(defthm fn-ovr-lease-run-quanta-within-the-line-count
  (implies (and (fn-hll-invp st)
                (fn-hl-render-ready-p h id inc st)
                (fn-rtc-live-p id inc st)
                (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses st)))
                (fn-ovw-cursorp cur) (consp cur) (not (nth 7 cur)) (fn-cbor-octet-listp (nth 6 cur))
                (unsigned-byte-p 59 (fn-rtc-buf-cap h (fn-rtc-config st)))
                (posp l)
                (fn-ovr-probes-within (nth 0 cur) (nfix (nth 1 cur)) (nfix (nth 2 cur)) (nth 6 cur)
                                      (nfix (nth 3 cur)) l fn-arena fn-cat)
                (<= (+ l (fn-ovr-frame-max)) (fn-rtc-buf-cap h (fn-rtc-config st)))
                (<= (nfix (nth 1 cur)) (nfix (nth 2 cur)))
                (< (fn-ovw-remaining cur) (nfix k)))
           (<= (mv-nth 0 (fn-ovr-lease-run-quanta cur w k h id inc st fn-arena fn-cat))
               (ceiling (+ 1 (- (nfix (nth 2 cur)) (nfix (nth 1 cur))))
                        (min (if (posp w) w 1)
                             (floor (- (fn-rtc-buf-cap h (fn-rtc-config st)) (fn-ovr-frame-max)) l))))))
