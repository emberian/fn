;; OVER's quantum rendered in place into the runtime-contract pool.
;; In-place pool windows and their refinement to the OVER step.
(in-package "ACL2")
(include-book "over-render")
(include-book "over-render-capl")
(include-book "over-render-pool")
(include-book "runtime-contract-landing")

(defun fn-ovr-probes-within (group k top server v l fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil
                  :measure (nfix (- (+ 1 (nfix top)) (nfix k)))))
  (if (and (natp k) (<= k (nfix top)))
      (and (<= (fn-ovr-probe-len group k server v fn-arena fn-cat) (nfix l))
           (fn-ovr-probes-within group (+ 1 k) top server v l fn-arena fn-cat))
    t))

; One pass over NUMBER..LAST. Fit is measured against the absolute limit.
; The quantum has already admitted the target with its first empty append.
(defun fn-ovr-fill (group number last top owedp legacyp room server v h j fn-rtc-st fn-arena fn-cat)
  (declare (xargs :stobjs (fn-rtc-st fn-arena fn-cat) :verify-guards nil
                  :guard (and (natp j) (unsigned-byte-p 59 room) (<= j room))
                  :measure (nfix (- (+ 1 (nfix last)) (nfix number)))
                  :hints (("Goal" :in-theory (fn-dss-measure-theory)))))
  (let ((v (nfix v)))
    (if (and (natp number) (<= number (nfix last)))
      (let* ((p (fn-ovr-probe-len group number server v fn-arena fn-cat))
             (s (if (and owedp (posp p)) (len (fn-ovr-status-octets)) 0))
             (owed2 (and owedp (zp p)))
             (close (if (<= (nfix top) number) (len (fn-ovr-close-octets owed2 legacyp)) 0)))
        (if (<= (+ (nfix j) s p close) (nfix room))
            (mv-let (sig j fn-rtc-st)
              (if (posp s) (fn-ovr-put-octets (fn-ovr-status-octets) h j room fn-rtc-st)
                (mv :done j fn-rtc-st))
              (declare (ignore sig))
              (mv-let (sig j fn-rtc-st)
                (fn-ovr-put-probe group number server v h j room fn-rtc-st fn-arena fn-cat)
                (declare (ignore sig))
                (fn-ovr-fill group (+ 1 number) last top owed2 legacyp room server v h j fn-rtc-st fn-arena fn-cat)))
          (mv (- number 1) owedp j fn-rtc-st)))
    (mv (- (nfix number) 1) owedp j fn-rtc-st))))

; Guards use pool shape and the writers' position contracts.
(local (defthm fn-ovrwp-fill-open
 (implies (syntaxp (or (symbolp number) (quotep number)))
   (equal (fn-ovr-fill group number last top owedp legacyp room server v h j st fn-arena fn-cat) (let ((v (nfix v)))
    (if (and (natp number) (<= number (nfix last)))
      (let* ((p (fn-ovr-probe-len group number server v fn-arena fn-cat))
             (s (if (and owedp (posp p)) (len (fn-ovr-status-octets)) 0))
             (owed2 (and owedp (zp p)))
             (close (if (<= (nfix top) number) (len (fn-ovr-close-octets owed2 legacyp)) 0)))
        (if (<= (+ (nfix j) s p close) (nfix room))
            (mv-let (sig j st)
              (if (posp s) (fn-ovr-put-octets (fn-ovr-status-octets) h j room st)
                (mv :done j st))
              (declare (ignore sig))
              (mv-let (sig j st)
                (fn-ovr-put-probe group number server v h j room st fn-arena fn-cat)
                (declare (ignore sig))
                (fn-ovr-fill group (+ 1 number) last top owed2 legacyp room server v h j st fn-arena fn-cat)))
          (mv (- number 1) owedp j st)))
    (mv (- (nfix number) 1) owedp j st)))))
 :hints (("Goal" :use ((:instance (:definition fn-ovr-fill) (fn-rtc-st st)))
                :in-theory (theory 'minimal-theory)))))
(local (defthm fn-ovrqp-octets-keeps-ap
 (implies (fn-rtc-st$ap st) (fn-rtc-st$ap (mv-nth 2 (fn-ovr-put-octets data h j limit st))))
 :hints (("Goal" :in-theory (union-theories '(fn-ovr-put-octets fn-dsw-append-is-splice
          fn-ovrqp-splice-preserves-ap mv-nth zp car-cons cdr-cons)
         (theory 'minimal-theory))))))
(local (defthm fn-ovr-fill-keeps-ap
 (implies (fn-rtc-st$ap st)
   (fn-rtc-st$ap (mv-nth 3 (fn-ovr-fill group number last top owedp legacyp room server v h j st fn-arena fn-cat))))
 :hints (("Goal" :induct (fn-ovr-fill group number last top owedp legacyp room server v h j st fn-arena fn-cat)
  :in-theory (union-theories '(fn-ovrwp-fill-open (:induction fn-ovr-fill)
        fn-ovrqp-octets-keeps-ap fn-ovrwp-probe-preserves-ap
        fn-ovrqp-splice-preserves-ap mv-nth zp posp car-cons cdr-cons)
      (set-difference-theories (fn-dss-measure-theory) '(nfix natp)))))))
(verify-guards fn-ovr-fill
 :hints (("Goal" :do-not '(preprocess)
    :use ((:instance fn-ovrwp-octets-guard-output (octets (fn-ovr-status-octets)) (limit room) (s fn-rtc-st))
          (:instance fn-ovrwp-probe-guard-output (s (mv-nth 2 (if (posp (if (and owedp (posp (fn-ovr-probe-len group number server (nfix v) fn-arena fn-cat))) (len (fn-ovr-status-octets)) 0)) (fn-ovr-put-octets (fn-ovr-status-octets) h j room fn-rtc-st) (list :done j fn-rtc-st)))) (j (mv-nth 1 (if (posp (if (and owedp (posp (fn-ovr-probe-len group number server (nfix v) fn-arena fn-cat))) (len (fn-ovr-status-octets)) 0)) (fn-ovr-put-octets (fn-ovr-status-octets) h j room fn-rtc-st) (list :done j fn-rtc-st))))
                     (limit room) (v (nfix v))))
    :in-theory (union-theories '(fn-dsw-st-p-is-abstract-recognizer
      unsigned-byte-p integer-range-p natp nfix zp posp
      (:executable-counterpart fn-ovr-status-octets) (:executable-counterpart len)
      (:type-prescription fn-ovr-probe-len) (:type-prescription len))
      (theory 'minimal-theory)))))

; N numbers taken, with N = 1 for an empty range whose close fits.
; N = 0 leaves the cursor and state unchanged and returns (nfix BASE).
; Every window is preflighted against min(LIMIT, physical buffer capacity).
(defun fn-ovr-quantum (cur w h base limit fn-rtc-st fn-arena fn-cat)
  (declare (xargs :stobjs (fn-rtc-st fn-arena fn-cat) :verify-guards nil
                  :guard (and (fn-ovw-cursorp cur) (natp base)
                              (unsigned-byte-p 59 limit) (<= base limit))))
  (if (or (not (consp cur)) (nth 7 cur) (not (fn-cbor-octet-listp (nth 6 cur)))
          (not (natp base)) (not (unsigned-byte-p 59 limit)) (< limit base))
      (mv 0 cur (nfix base) fn-rtc-st)
    (let* ((cap (min limit (fn-rtc-buf-cap h (fn-rtc-st-config fn-rtc-st))))
           (group (nth 0 cur)) (k (nfix (nth 1 cur))) (top (nfix (nth 2 cur)))
           (v (nfix (nth 3 cur))) (legacyp (nth 4 cur)) (owedp (nth 5 cur)) (server (nth 6 cur)))
      (if (< cap base)
          (mv 0 cur base fn-rtc-st)
        (mv-let (sig j fn-rtc-st) (fn-dsw-append h base nil fn-rtc-st)
          (if (eq sig :refused)
              (mv 0 cur base fn-rtc-st)
            (mv-let (hi owed2 j fn-rtc-st)
              (fn-ovr-fill group k (fn-ovw-hi k top w) top owedp legacyp cap server v h j fn-rtc-st fn-arena fn-cat)
              (if (or (and (< hi k) (<= k top))
                      ; An empty range takes N = 1 and writes only the close, when it fits.
                      (and (< top k) (< cap (+ j (len (fn-ovr-close-octets owed2 legacyp))))))
                  (mv 0 cur base fn-rtc-st)
                (let ((donep (<= top hi)))
                  (mv-let (sig j fn-rtc-st)
                    (if donep (fn-dsw-append h j (fn-ovr-close-octets owed2 legacyp) fn-rtc-st)
                      (mv :done j fn-rtc-st))
                    (declare (ignore sig))
                    (mv (max 1 (+ 1 (- hi k)))
                        (if donep nil (fn-ovw-cursor group (+ 1 hi) top v legacyp owed2 server))
                        j fn-rtc-st)))))))))))

; Pool quantum refinements.
(local (defthm fn-ovrqp-octets-position
 (implies (and (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-octets octets h j limit st))))
     (and (natp j2) (<= j j2) (<= j2 (nfix limit)))))
 :hints (("Goal" :in-theory (union-theories '(fn-ovr-put-octets fn-dsw-append nfix natp len car-cons cdr-cons)
                   (fn-dss-measure-theory))))))
(local (defthm fn-ovrqp-octets-position-linear
 (implies (and (natp j) (<= j (nfix limit)))
   (let ((j2 (mv-nth 1 (fn-ovr-put-octets octets h j limit st))))
     (and (<= j j2) (<= j2 (nfix limit)))))
 :rule-classes :linear
 :hints (("Goal" :use fn-ovrqp-octets-position :in-theory (theory 'minimal-theory)))))
(local (defthm fn-ovrqp-fill-position
 (implies (and (fn-rtc-st$ap st) (natp j) (<= j (nfix room)))
   (let ((j2 (mv-nth 2 (fn-ovr-fill group number last top owedp legacyp room server v h j st fn-arena fn-cat))))
     (and (natp j2) (<= j j2) (<= j2 (nfix room)))))
 :hints (("Goal" :induct (fn-ovr-fill group number last top owedp legacyp room server v h j st fn-arena fn-cat)
    :in-theory (union-theories '(fn-ovrwp-fill-open (:induction fn-ovr-fill)
        fn-ovrqp-octets-position fn-ovrwp-probe-position fn-ovrwp-probe-position-linear fn-ovrqp-octets-position-linear fn-ovrqp-octets-keeps-ap fn-ovrwp-probe-preserves-ap
        fn-ovrqp-nfix-natural fn-ovrqp-natural-nfix natp-compound-recognizer mv-nth zp posp car-cons cdr-cons)
        (set-difference-theories (fn-dss-measure-theory) '(nfix natp)))))))
(local (defthm fn-ovrqp-append-keeps-ap
 (implies (fn-rtc-st$ap st) (fn-rtc-st$ap (mv-nth 2 (fn-dsw-append h j data st))))
 :hints (("Goal" :in-theory (union-theories '(fn-dsw-append-is-splice fn-ovrqp-splice-preserves-ap
                                            mv-nth car-cons cdr-cons) (theory 'minimal-theory))))))
(local (defthm fn-ovrqp-append-guard-output
 (implies (and (fn-rtc-st$ap st) (natp j) (natp limit) (<= (+ j (len data)) limit))
   (let ((j2 (mv-nth 1 (fn-dsw-append h j data st))))
     (and (natp j2) (<= j2 limit) (fn-rtc-st$ap (mv-nth 2 (fn-dsw-append h j data st))))))
 :rule-classes ((:forward-chaining :trigger-terms ((fn-dsw-append h j data st))))
 :hints (("Goal" :in-theory (union-theories '(fn-dsw-append-is-splice fn-ovrqp-splice-preserves-ap
           mv-nth zp car-cons cdr-cons natp (:type-prescription len)) (theory 'minimal-theory))))))
(local (defthm fn-ovrqp-buf-cap-natural (natp (fn-rtc-buf-cap h cfg))
 :rule-classes :type-prescription
 :hints (("Goal" :in-theory (union-theories '(fn-rtc-buf-cap fn-rtc-capf fn-rtc-capl nfix natp) (theory 'minimal-theory))))))
(local (defthm fn-ovrqp-fill-guard-output
 (implies (and (fn-rtc-st$ap st) (natp j) (unsigned-byte-p 59 room) (<= j room))
   (let ((j2 (mv-nth 2 (fn-ovr-fill group number last top owedp legacyp room server v h j st fn-arena fn-cat))))
     (and (natp j2) (integerp j2) (rationalp j2) (acl2-numberp j2) (<= j2 room)
          (fn-rtc-st$ap (mv-nth 3 (fn-ovr-fill group number last top owedp legacyp room server v h j st fn-arena fn-cat))))))
 :rule-classes ((:forward-chaining :trigger-terms ((fn-ovr-fill group number last top owedp legacyp room server v h j st fn-arena fn-cat))))
 :hints (("Goal" :use (fn-ovrqp-fill-position fn-ovr-fill-keeps-ap)
    :in-theory (union-theories '(natp nfix unsigned-byte-p integer-range-p) (theory 'minimal-theory))))))



; Count bounds do not require a writable target or a valid abstract state.

(local (defthm fn-ovrwp-fill-hi-bounds
 (implies (natp number)
   (let ((hi (mv-nth 0 (fn-ovr-fill group number last top owedp legacyp room server v h j s fn-arena fn-cat))))
     (and (integerp hi) (<= (- number 1) hi) (<= hi (max (- number 1) (nfix last))))))
 :hints (("Goal" :induct (fn-ovr-fill group number last top owedp legacyp room server v h j s fn-arena fn-cat)
    :in-theory (union-theories '(fn-ovrwp-fill-open (:induction fn-ovr-fill) max mv-nth car-cons cdr-cons posp fn-ovrqp-nfix-natural fn-ovrqp-natural-nfix natp-compound-recognizer) (set-difference-theories (fn-dss-measure-theory) '(nfix natp)))))))

(local (defthm fn-ovrwp-quantum-count-bound
 (<= (mv-nth 0 (fn-ovr-quantum cur w h base limit s fn-arena fn-cat)) (if (posp w) w 1))
 :hints (("Goal" :do-not-induct t
    :use ((:instance fn-ovrwp-fill-hi-bounds
       (group (nth 0 cur)) (number (nfix (nth 1 cur)))
       (last (fn-ovw-hi (nfix (nth 1 cur)) (nfix (nth 2 cur)) w))
       (top (nfix (nth 2 cur))) (owedp (nth 5 cur)) (legacyp (nth 4 cur))
       (room (min limit (fn-rtc-buf-cap h (fn-rtc-st-config s))))
       (server (nth 6 cur)) (v (nfix (nth 3 cur)))
       (j (mv-nth 1 (fn-dsw-append h base nil s)))
       (s (mv-nth 2 (fn-dsw-append h base nil s)))))
    :in-theory (union-theories '(fn-ovr-quantum fn-ovw-hi max min posp mv-nth
                                unsigned-byte-p integer-range-p car-cons cdr-cons)
                               (fn-dss-measure-theory))))))
(local (set-default-hints '((and stable-under-simplificationp
                         '(:use fn-ovrwp-quantum-count-bound :in-theory (theory 'minimal-theory))))))
(defthm fn-ovr-quantum-window-at-most-w
  (<= (mv-nth 0 (fn-ovr-quantum cur w h base limit s fn-arena fn-cat)) (if (posp w) w 1)))
(local (set-default-hints nil))

(verify-guards fn-ovr-quantum
 :hints (("Goal" :do-not '(preprocess)
 :use ((:instance fn-ovrqp-fill-guard-output (group (nth 0 cur)) (number (nfix (nth 1 cur))) (last (fn-ovw-hi (nfix (nth 1 cur)) (nfix (nth 2 cur)) w)) (top (nfix (nth 2 cur))) (owedp (nth 5 cur)) (legacyp (nth 4 cur)) (room (min limit (fn-rtc-buf-cap h (fn-rtc-st-config fn-rtc-st)))) (server (nth 6 cur)) (v (nfix (nth 3 cur))) (j base) (st fn-rtc-st))
 (:instance fn-ovrwp-fill-hi-bounds (group (nth 0 cur)) (number (nfix (nth 1 cur))) (last (fn-ovw-hi (nfix (nth 1 cur)) (nfix (nth 2 cur)) w)) (top (nfix (nth 2 cur))) (owedp (nth 5 cur)) (legacyp (nth 4 cur)) (room (min limit (fn-rtc-buf-cap h (fn-rtc-st-config fn-rtc-st)))) (server (nth 6 cur)) (v (nfix (nth 3 cur))) (j base) (s fn-rtc-st)))
    :in-theory (union-theories '(fn-dsw-st-p-is-abstract-recognizer fn-ovrqp-empty-append-keeps-state
       fn-ovrqp-empty-append-position fn-ovrqp-fill-guard-output fn-ovrwp-fill-hi-bounds fn-ovw-cursorp fn-ovrqp-append-keeps-ap fn-ovrqp-buf-cap-natural
       fn-ovrqp-nfix-natural fn-ovrqp-natural-nfix
       min max natp nfix unsigned-byte-p integer-range-p posp zp car-cons cdr-cons mv-nth
       (:type-prescription len) (:type-prescription fn-ovr-fill) (:type-prescription fn-dsw-append)) (theory 'minimal-theory)))))


; The logical range body supplies the splice refinement, without a second fill loop.
(local (in-theory (disable fn-ovr-probe-len fn-ovr-put-probe fn-ovr-probe-octets fn-ovw-lines-split)))
(local (defthm fn-ovrp-hi-type
   (implies (natp top) (natp (fn-ovw-hi k top w)))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-ovw-hi)))))
(local (defthm fn-ovrp-hi-linear
   (implies (and (natp k) (natp top) (<= k top))
            (and (<= k (fn-ovw-hi k top w))
                 (<= (fn-ovw-hi k top w) top)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-ovw-hi)))))
(local (defthm fn-ovrp-hi-at-top
   (implies (and (natp k) (natp top) (<= top (fn-ovw-hi k top w)))
            (equal (fn-ovw-hi k top w) top))
   :hints (("Goal" :in-theory (enable fn-ovw-hi)))))
(local (defthm fn-ovrp-stuff-consp
   (equal (consp (fn-nntp-stuff-lines x)) (consp x))
   :hints (("Goal" :in-theory (enable fn-nntp-stuff-lines fn-nntp-crlf)))))
(local (defthm fn-ovrp-lines-empty-above
   (implies (and (natp k) (natp hi) (< hi k))
            (equal (fn-ovw-lines group k hi server v fn-arena fn-cat) nil))
   :hints (("Goal" :in-theory (enable fn-ovw-lines)))))
(local (defthm fn-ovrp-len-pos
   (and (equal (posp (len x)) (consp x))
        (equal (zp (len x)) (not (consp x))))
   :hints (("Goal" :in-theory (enable posp)))))
(local (defthm fn-ovrp-consp-append
   (equal (consp (append a b)) (if (consp a) t (consp b)))))
(local (defthm fn-ovrp-append-iff
   (iff (append a b) (if (consp a) t b))))
(local (defun fn-ovrp-win (group j hi server v fn-arena fn-cat)
   (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
   (if (<= j hi) (fn-ovw-lines group j hi server v fn-arena fn-cat) nil)))
(local (in-theory (disable (:definition fn-ovrp-win))))
(local (defthm fn-ovrp-win-empty
   (implies (< hi j)
            (equal (fn-ovrp-win group j hi server v fn-arena fn-cat) nil))
   :hints (("Goal" :in-theory (enable fn-ovrp-win)))))
(local (defthm fn-ovrp-win-extend
   (implies (and (natp j) (integerp hi) (<= (- j 1) hi))
            (equal (fn-ovrp-win group j (+ 1 hi) server v fn-arena fn-cat)
                   (append (fn-ovrp-win group j hi server v fn-arena fn-cat)
                           (fn-ovrp-win group (+ 1 hi) (+ 1 hi) server v fn-arena fn-cat))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-ovrp-win) (fn-ovw-lines-split))
            :cases ((<= j hi))
            :use ((:instance fn-ovw-lines-split (k j) (top (+ 1 hi)) (hi hi)))))))
(local (defthm fn-ovrp-win-cons
   (implies (and (natp j) (integerp hi) (< j hi))
            (equal (fn-ovrp-win group j hi server v fn-arena fn-cat)
                   (append (fn-ovrp-win group j j server v fn-arena fn-cat)
                           (fn-ovrp-win group (+ 1 j) hi server v fn-arena fn-cat))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-ovrp-win) (fn-ovw-lines-split))
            :use ((:instance fn-ovw-lines-split (k j) (top hi) (hi j)))))))
(local (defthm fn-ovrp-probe-is-win
   (implies (natp j)
            (equal (fn-ovr-probe-octets group j server v fn-arena fn-cat)
                   (fn-nntp-stuff-lines (fn-ovrp-win group j j server v fn-arena fn-cat))))
   :hints (("Goal" :in-theory (enable fn-ovr-probe-octets fn-ovrp-win)))))
(local (defun fn-ovrp-body (group j hi owedp server v fn-arena fn-cat)
   (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil
                   :measure (nfix (- (+ 1 (ifix hi)) (nfix j)))))
   (if (and (natp j) (integerp hi) (<= j hi))
       (let ((pl (fn-ovr-probe-octets group j server v fn-arena fn-cat)))
         (append (if (and owedp (consp pl)) (fn-ovr-status-octets) nil)
                 pl
                 (fn-ovrp-body group (+ 1 j) hi (and owedp (not (consp pl))) server v fn-arena fn-cat)))
     nil)))
(local (defthm fn-ovrp-body-empty
   (implies (< hi j)
            (equal (fn-ovrp-body group j hi owedp server v fn-arena fn-cat) nil))))
(local (defun fn-ovrp-owed (group j hi owedp server v fn-arena fn-cat)
   (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil
                   :measure (nfix (- (+ 1 (ifix hi)) (nfix j)))))
   (if (and (natp j) (integerp hi) (<= j hi))
       (let ((pl (fn-ovr-probe-octets group j server v fn-arena fn-cat)))
         (fn-ovrp-owed group (+ 1 j) hi (and owedp (not (consp pl))) server v fn-arena fn-cat))
     owedp)))
(local (defthm fn-ovrp-owed-empty
   (implies (< hi j)
            (equal (fn-ovrp-owed group j hi owedp server v fn-arena fn-cat) owedp))))
(local (defthm fn-ovrp-body-is-window
   (implies (and (natp j) (integerp hi))
            (equal (fn-ovrp-body group j hi owedp server v fn-arena fn-cat)
                   (append (if (and owedp (consp (fn-ovrp-win group j hi server v fn-arena fn-cat)))
                               (fn-ovr-status-octets) nil)
                           (fn-nntp-stuff-lines (fn-ovrp-win group j hi server v fn-arena fn-cat)))))
   :rule-classes nil
   :hints (("Goal" :induct (fn-ovrp-body group j hi owedp server v fn-arena fn-cat))
           ("Subgoal *1/1'" :use fn-ovrp-win-cons))))
(local (defthm fn-ovrp-owed-is-window
   (implies (and (natp j) (integerp hi))
            (equal (fn-ovrp-owed group j hi owedp server v fn-arena fn-cat)
                   (if (<= j hi)
                       (and owedp (not (consp (fn-ovrp-win group j hi server v fn-arena fn-cat))))
                     owedp)))
   :rule-classes nil
   :hints (("Goal" :induct (fn-ovrp-owed group j hi owedp server v fn-arena fn-cat))
           ("Subgoal *1/1'" :use fn-ovrp-win-cons))))
(local (defthm fn-ovrp-body-snoc
   (implies (and (natp j) (integerp hi) (<= (- j 1) hi))
            (equal (fn-ovrp-body group j (+ 1 hi) owedp server v fn-arena fn-cat)
                   (append (fn-ovrp-body group j hi owedp server v fn-arena fn-cat)
                           (if (and (fn-ovrp-owed group j hi owedp server v fn-arena fn-cat)
                                    (consp (fn-ovr-probe-octets group (+ 1 hi) server v fn-arena fn-cat)))
                               (fn-ovr-status-octets) nil)
                           (fn-ovr-probe-octets group (+ 1 hi) server v fn-arena fn-cat))))
   :hints (("Goal" :in-theory (disable fn-ovrp-body fn-ovrp-owed)
            :use (fn-ovrp-win-extend
                  (:instance fn-ovrp-body-is-window (hi (+ 1 hi)))
                  (:instance fn-ovrp-body-is-window)
                  (:instance fn-ovrp-owed-is-window)
                  (:instance fn-ovrp-probe-is-win (j (+ 1 hi))))))))
(local (in-theory (disable fn-ovrp-body fn-ovrp-owed)))
(local (defthm fn-ovrp-body-step
   (implies (and (natp j) (integerp hi) (<= j hi)
                 (syntaxp (or (symbolp j) (quotep j))))
            (equal (fn-ovrp-body group j hi owedp server v fn-arena fn-cat)
                   (let ((pl (fn-ovr-probe-octets group j server v fn-arena fn-cat)))
                     (append (if (and owedp (consp pl)) (fn-ovr-status-octets) nil)
                             pl
                             (fn-ovrp-body group (+ 1 j) hi (and owedp (not (consp pl)))
                                           server v fn-arena fn-cat)))))
   :hints (("Goal" :expand ((fn-ovrp-body group j hi owedp server v fn-arena fn-cat))))))
(local (defthm fn-ovrp-owed-step
   (implies (and (natp j) (integerp hi) (<= j hi)
                 (syntaxp (or (symbolp j) (quotep j))))
            (equal (fn-ovrp-owed group j hi owedp server v fn-arena fn-cat)
                   (let ((pl (fn-ovr-probe-octets group j server v fn-arena fn-cat)))
                     (fn-ovrp-owed group (+ 1 j) hi (and owedp (not (consp pl)))
                                   server v fn-arena fn-cat))))
   :hints (("Goal" :expand ((fn-ovrp-owed group j hi owedp server v fn-arena fn-cat))))))
(local (defthm fn-ovrup-fill-position
 (implies (and (natp j) (<= j (nfix room)))
   (let ((j2 (mv-nth 2 (fn-ovr-fill group number last top owedp legacyp room server v h j st fn-arena fn-cat))))
     (and (natp j2) (<= j j2) (<= j2 (nfix room)))))
 :hints (("Goal" :induct (fn-ovr-fill group number last top owedp legacyp room server v h j st fn-arena fn-cat)
    :in-theory (union-theories '(fn-ovrwp-fill-open (:induction fn-ovr-fill)
        fn-ovrqp-octets-position fn-ovrup-probe-position fn-ovrup-probe-position-linear fn-ovrqp-octets-position-linear fn-ovrqp-octets-keeps-ap fn-ovrwp-probe-preserves-ap
        fn-ovrqp-nfix-natural fn-ovrqp-natural-nfix natp-compound-recognizer mv-nth zp posp car-cons cdr-cons)
        (set-difference-theories (fn-dss-measure-theory) '(nfix natp)))))))
(local (defthm fn-ovrqp-fill-hi-integer
 (implies (natp number)
   (integerp (mv-nth 0 (fn-ovr-fill group number last top owedp legacyp room server v h j st fn-arena fn-cat))))
 :rule-classes (:type-prescription :rewrite)
 :hints (("Goal" :use ((:instance fn-ovrwp-fill-hi-bounds (s st))) :in-theory (theory 'minimal-theory)))))
(local (defthm fn-ovrqp-body-octets
 (implies (and (natp v) (fn-cbor-octet-listp server))
  (fn-cbor-octet-listp (fn-ovrp-body group number hi owedp server v fn-arena fn-cat)))
 :hints (("Goal" :induct (fn-ovrp-body group number hi owedp server v fn-arena fn-cat)
   :in-theory (e/d (fn-ovrp-body) (fn-ovrp-probe-is-win fn-ovr-probe-octets fn-rtc-st$ap fn-rtc-shapep))))))
(local (defthm fn-ovrqp-fill-hi-lower
 (implies (natp number)
  (<= (- number 1) (mv-nth 0 (fn-ovr-fill group number last top owedp legacyp room server v h j st fn-arena fn-cat))))
 :rule-classes :linear
 :hints (("Goal" :use ((:instance fn-ovrwp-fill-hi-bounds (s st))) :in-theory (theory 'minimal-theory)))))
(local (defthm fn-ovrqp-fill-hi-car-type
 (implies (natp number)
   (integerp (car (fn-ovr-fill group number last top owedp legacyp room server v h j st fn-arena fn-cat))))
 :rule-classes (:type-prescription :rewrite)
 :hints (("Goal" :use fn-ovrqp-fill-hi-integer
  :in-theory (union-theories '(mv-nth zp) (theory 'minimal-theory))))))
(local (defthm fn-ovrqp-fill-hi-car-lower
 (implies (natp number)
  (<= (- number 1) (car (fn-ovr-fill group number last top owedp legacyp room server v h j st fn-arena fn-cat))))
 :rule-classes :linear
 :hints (("Goal" :use fn-ovrqp-fill-hi-lower
  :in-theory (union-theories '(mv-nth zp (:type-prescription fn-ovr-fill)) (theory 'minimal-theory))))))
(local (defthm fn-ovrqp-fill-owed
 (implies (and (natp number) (natp v))
  (equal (mv-nth 1 (fn-ovr-fill group number last top owedp legacyp room server v h j st fn-arena fn-cat))
   (fn-ovrp-owed group number
    (mv-nth 0 (fn-ovr-fill group number last top owedp legacyp room server v h j st fn-arena fn-cat))
    owedp server v fn-arena fn-cat)))
 :hints (("Goal" :induct (fn-ovr-fill group number last top owedp legacyp room server v h j st fn-arena fn-cat)
   :in-theory (e/d (fn-ovrwp-fill-open fn-ovr-probe-len-is-the-length fn-ovrp-owed-step fn-ovrp-owed-empty)
    (fn-ovrp-probe-is-win (:definition fn-ovr-fill) fn-ovr-put-probe fn-ovr-put-octets fn-ovr-probe-octets fn-ovr-probe-len fn-ovrp-owed
      fn-rtc-st$ap fn-rtc-shapep fn-rtc-st$a-splice fn-ovrqp-roomp))))))
(local (defthm fn-ovrqp-fill-is-body-splice
 (implies (and (fn-ovrqp-roomp h j room st) (natp number) (natp v) (fn-cbor-octet-listp server))
  (mv-let (hi owed2 j2 st2) (fn-ovr-fill group number last top owedp legacyp room server v h j st fn-arena fn-cat)
   (declare (ignore owed2))
   (let ((body (fn-ovrp-body group number hi owedp server v fn-arena fn-cat)))
    (and (natp j2) (<= j2 room) (equal j2 (+ j (len body))) (equal st2 (fn-rtc-st$a-splice h j body st))))))
 :hints (("Goal" :induct (fn-ovr-fill group number last top owedp legacyp room server v h j st fn-arena fn-cat)
  :in-theory (e/d (fn-ovrwp-fill-open fn-ovr-probe-len-is-the-length fn-ovrp-body-step fn-ovrp-body-empty)
   (fn-ovrp-probe-is-win (:definition fn-ovr-fill) fn-ovr-put-probe fn-ovr-put-octets fn-ovr-probe-octets fn-ovr-probe-len fn-ovrp-body
     fn-rtc-st$ap fn-rtc-shapep fn-rtc-st$a-splice fn-rtc-splice-okp fn-ovrqp-roomp))))))


(local (defthm fn-ovrqp-fill-hi-car-upper
 (implies (and (natp number) (<= number (nfix last)))
  (<= (car (fn-ovr-fill group number last top owedp legacyp room server v h j st fn-arena fn-cat)) (nfix last)))
 :rule-classes :linear
 :hints (("Goal" :use ((:instance fn-ovrwp-fill-hi-bounds (s st)))
  :in-theory (union-theories '(mv-nth zp max (:type-prescription fn-ovr-fill) natp nfix) (theory 'minimal-theory))))))
(local (defthm fn-ovrqp-fill-fit
 (implies (and (fn-ovrqp-roomp h j room st) (natp number) (natp last) (natp top) (natp v) (fn-cbor-octet-listp server)
  (<= last top)
  (equal hi (car (fn-ovr-fill group number last top owedp legacyp room server v h j st fn-arena fn-cat)))
  (<= number hi))
  (<= (+ j (len (fn-ovrp-body group number hi owedp server v fn-arena fn-cat))
   (if (<= (nfix top) hi)
    (len (fn-ovr-close-octets (fn-ovrp-owed group number hi owedp server v fn-arena fn-cat) legacyp)) 0)) room))
 :hints (("Goal" :induct (fn-ovr-fill group number last top owedp legacyp room server v h j st fn-arena fn-cat)
  :in-theory (union-theories
 '(fn-ovrwp-fill-open (:induction fn-ovr-fill) fn-ovr-probe-len-is-the-length
   fn-ovrp-body-step fn-ovrp-body-empty fn-ovrp-owed-step fn-ovrp-owed-empty fn-ovrp-len-pos
   fn-ovrqp-fill-is-body-splice fn-ovrqp-fill-owed fn-ovrqp-fill-hi-car-type
   fn-ovrqp-fill-hi-car-lower fn-ovrqp-fill-hi-car-upper
   fn-ovrqp-octets-is-splice fn-ovrqp-probe-is-splice fn-ovrqp-probe-octets fn-ovrqp-body-octets
   fn-ovrqp-octets-append fn-ovrqp-octets-cons fn-ovrqp-room-properties fn-ovrqp-room-bounds fn-ovrqp-room-at-splice-position
   fn-ovrqp-compose-at-splice-position fn-ovrqp-empty-splice
   fn-ovrqp-nfix-natural fn-ovrqp-natural-nfix fn-ovrqp-len-append
   fn-ovrqp-fold-sums associativity-of-+ commutativity-of-+ commutativity-2-of-+
   fix unicity-of-0 default-+-1 default-+-2 natp-compound-recognizer
   mv-nth zp posp car-cons cdr-cons len (:type-prescription len)
   (:type-prescription fn-ovr-fill) (:type-prescription fn-ovr-probe-octets)
   (:executable-counterpart fn-ovr-status-octets)
   (:executable-counterpart fn-cbor-octet-listp))
 (set-difference-theories (fn-dss-measure-theory) '(nfix natp)))))))


; Quantum cases: refused targets, nonempty windows, and an empty range.
(local (defthm fn-ovrp-win-is-lines
   (implies (and (natp j) (natp hi))
            (equal (fn-ovrp-win group j hi server v fn-arena fn-cat)
                   (fn-ovw-lines group j hi server v fn-arena fn-cat)))
   :hints (("Goal" :in-theory (enable fn-ovrp-win)))))
(local (defthm fn-ovrp-hi-natp
   (implies (natp top) (natp (fn-ovw-hi k top w)))
   :hints (("Goal" :in-theory (enable fn-ovw-hi)))))
(local (defthm fn-ovrp-hi-bounds
   (implies (and (natp k) (natp top) (<= k top))
            (and (<= k (fn-ovw-hi k top w))
                 (<= (fn-ovw-hi k top w) top)))
   :hints (("Goal" :in-theory (enable fn-ovw-hi)))))
(local (defthm fn-ovrp-step-octets
   (implies (and (consp cur) (not (nth 7 cur)) (natp (nth 3 cur)))
            (equal (mv-nth 0 (fn-ovw-step cur n fn-arena fn-cat))
                   (let* ((k (nfix (nth 1 cur))) (top (nfix (nth 2 cur)))
                          (hi (fn-ovw-hi k top n)))
                     (append (fn-ovrp-body (nth 0 cur) k hi (nth 5 cur) (nth 6 cur) (nth 3 cur)
                                           fn-arena fn-cat)
                             (if (<= top hi)
                                 (fn-ovr-close-octets
                                  (fn-ovrp-owed (nth 0 cur) k hi (nth 5 cur) (nth 6 cur) (nth 3 cur)
                                                fn-arena fn-cat)
                                  (nth 4 cur))
                               nil)))))
   :hints (("Goal" :in-theory (e/d (fn-ovw-step fn-ovr-close-octets) (fn-ovw-hi fn-ovrp-body-step fn-ovrp-owed-step))
            :use ((:instance fn-ovrp-body-is-window (j (nfix (nth 1 cur)))
                             (hi (fn-ovw-hi (nfix (nth 1 cur)) (nfix (nth 2 cur)) n))
                             (group (nth 0 cur)) (owedp (nth 5 cur)) (server (nth 6 cur)) (v (nth 3 cur)))
                  (:instance fn-ovrp-owed-is-window (j (nfix (nth 1 cur)))
                             (hi (fn-ovw-hi (nfix (nth 1 cur)) (nfix (nth 2 cur)) n))
                             (group (nth 0 cur)) (owedp (nth 5 cur)) (server (nth 6 cur)) (v (nth 3 cur)))
                  (:instance fn-ovrp-win-is-lines (j (nfix (nth 1 cur)))
                             (hi (fn-ovw-hi (nfix (nth 1 cur)) (nfix (nth 2 cur)) n))
                             (group (nth 0 cur)) (server (nth 6 cur)) (v (nth 3 cur)))
                  (:instance fn-ovrp-hi-natp (k (nfix (nth 1 cur))) (top (nfix (nth 2 cur))) (w n)))))))
(local (defthm fn-ovrp-step-next
   (implies (and (consp cur) (not (nth 7 cur)) (natp (nth 3 cur))
                 (<= (nfix (nth 1 cur)) (nfix (nth 2 cur))))
            (equal (mv-nth 1 (fn-ovw-step cur n fn-arena fn-cat))
                   (let* ((k (nfix (nth 1 cur))) (top (nfix (nth 2 cur)))
                          (hi (fn-ovw-hi k top n)))
                     (if (<= top hi)
                         nil
                       (fn-ovw-cursor (nth 0 cur) (+ 1 hi) top (nth 3 cur) (nth 4 cur)
                                      (fn-ovrp-owed (nth 0 cur) k hi (nth 5 cur) (nth 6 cur) (nth 3 cur)
                                                    fn-arena fn-cat)
                                      (nth 6 cur))))))
   :hints (("Goal" :in-theory (e/d (fn-ovw-step) (fn-ovw-hi fn-ovrp-body-step fn-ovrp-owed-step))
            :use ((:instance fn-ovrp-owed-is-window (j (nfix (nth 1 cur)))
                             (hi (fn-ovw-hi (nfix (nth 1 cur)) (nfix (nth 2 cur)) n))
                             (group (nth 0 cur)) (owedp (nth 5 cur)) (server (nth 6 cur)) (v (nth 3 cur)))
                  (:instance fn-ovrp-win-is-lines (j (nfix (nth 1 cur)))
                             (hi (fn-ovw-hi (nfix (nth 1 cur)) (nfix (nth 2 cur)) n))
                             (group (nth 0 cur)) (server (nth 6 cur)) (v (nth 3 cur)))
                  (:instance fn-ovrp-hi-natp (k (nfix (nth 1 cur))) (top (nfix (nth 2 cur))) (w n))
                  (:instance fn-ovrp-hi-bounds (k (nfix (nth 1 cur))) (top (nfix (nth 2 cur))) (w n)))))))
(local (defthm fn-ovrp-hi-top-lt
   (implies (and (natp k) (natp top) (< top k))
            (equal (fn-ovw-hi k top w) top))
   :hints (("Goal" :in-theory (enable fn-ovw-hi)))))
(local (defthm fn-ovrp-ub59
   (implies (unsigned-byte-p 59 cap)
            (and (natp cap) (equal (nfix cap) cap)))))
(local (defthm fn-ovrp-hi-le-top
   (<= (nfix (fn-ovw-hi k top w)) (nfix top))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-ovw-hi)))))
(local (defthm fn-ovrp-step-octets-fast (implies (and (consp cur) (not (nth 7 cur)) (natp (nth 3 cur)))
            (equal (mv-nth 0 (fn-ovw-step cur n fn-arena fn-cat))
                   (let* ((k (nfix (nth 1 cur))) (top (nfix (nth 2 cur)))
                          (hi (fn-ovw-hi k top n)))
                     (append (fn-ovrp-body (nth 0 cur) k hi (nth 5 cur) (nth 6 cur) (nth 3 cur)
                                           fn-arena fn-cat)
                             (if (<= top hi)
                                 (fn-ovr-close-octets
                                  (fn-ovrp-owed (nth 0 cur) k hi (nth 5 cur) (nth 6 cur) (nth 3 cur)
                                                fn-arena fn-cat)
                                  (nth 4 cur))
                               nil)))))
 :hints (("Goal" :use fn-ovrp-step-octets :in-theory (theory 'minimal-theory)))))
(local (defthm fn-ovrp-step-next-fast (implies (and (consp cur) (not (nth 7 cur)) (natp (nth 3 cur))
                 (<= (nfix (nth 1 cur)) (nfix (nth 2 cur))))
            (equal (mv-nth 1 (fn-ovw-step cur n fn-arena fn-cat))
                   (let* ((k (nfix (nth 1 cur))) (top (nfix (nth 2 cur)))
                          (hi (fn-ovw-hi k top n)))
                     (if (<= top hi)
                         nil
                       (fn-ovw-cursor (nth 0 cur) (+ 1 hi) top (nth 3 cur) (nth 4 cur)
                                      (fn-ovrp-owed (nth 0 cur) k hi (nth 5 cur) (nth 6 cur) (nth 3 cur)
                                                    fn-arena fn-cat)
                                      (nth 6 cur))))))
 :hints (("Goal" :use fn-ovrp-step-next :in-theory (theory 'minimal-theory)))))
(local (defthm fn-ovrp-hi-n
   (implies (and (natp k) (natp top) (integerp hi) (<= k hi)
                 (<= hi (fn-ovw-hi k top w)))
            (equal (fn-ovw-hi k top (+ 1 (- hi k))) hi))
   :hints (("Goal" :in-theory (enable fn-ovw-hi)))))
(local (defthm fn-ovrp-hi-le-w
   (implies (and (natp k) (natp top) (integerp hi)
                 (<= hi (fn-ovw-hi k top w)))
            (<= (+ 1 (- hi k)) (if (posp w) w 1)))
   :hints (("Goal" :in-theory (enable fn-ovw-hi)))))
(local (defthm fn-ovrqp-initial-room
 (implies (and (fn-rtc-st$ap s) (natp base) (natp limit)
               (<= base (min limit (fn-rtc-buf-cap h (fn-rtc-st-config s))))
               (equal (car (fn-dsw-append h base nil s)) :done))
  (fn-ovrqp-roomp h base (min limit (fn-rtc-buf-cap h (fn-rtc-st-config s))) s))
 :hints (("Goal" :in-theory (union-theories '(fn-dsw-append-is-splice fn-ovrqp-roomp
       fn-rtc-st-config fn-rtc-st$a-config min natp fn-ovrqp-buf-cap-natural
       mv-nth zp car-cons cdr-cons (:type-prescription fn-dsw-append)) (theory 'minimal-theory))))))
(local (defun fn-ovrqp-live (cur h base limit s)
 (declare (xargs :verify-guards nil))
 (and (consp cur) (not (nth 7 cur)) (fn-cbor-octet-listp (nth 6 cur))
      (natp base) (unsigned-byte-p 59 limit)
      (<= base (min limit (fn-rtc-buf-cap h (fn-rtc-config s))))
      (fn-rtc-splice-okp h base nil s))))
(local (defmacro fn-ovrqp-fq (cur w h base limit s)
 `(fn-ovr-fill (nth 0 ,cur) (nfix (nth 1 ,cur))
  (fn-ovw-hi (nfix (nth 1 ,cur)) (nfix (nth 2 ,cur)) ,w)
  (nfix (nth 2 ,cur)) (nth 5 ,cur) (nth 4 ,cur)
  (min ,limit (fn-rtc-buf-cap ,h (fn-rtc-config ,s)))
  (nth 6 ,cur) (nfix (nth 3 ,cur)) ,h ,base ,s fn-arena fn-cat)))
(local (defthm fn-ovrqp-quantum-closed
 (implies (and (fn-rtc-st$ap s) (not (fn-ovrqp-live cur h base limit s)))
  (equal (fn-ovr-quantum cur w h base limit s fn-arena fn-cat) (mv 0 cur (nfix base) s)))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories '(fn-ovr-quantum fn-ovrqp-live fn-rtc-st-config fn-rtc-st$a-config
   fn-dsw-append-is-splice fn-ovrqp-empty-append-keeps-state fn-ovrqp-empty-append-position
   fn-ovrqp-nfix-natural fn-ovrqp-natural-nfix fn-ovrqp-buf-cap-natural
   min natp nfix unsigned-byte-p integer-range-p mv-nth zp car-cons cdr-cons
   (:type-prescription fn-dsw-append)) (theory 'minimal-theory))))))
(local (defthm fn-ovrqp-live-room
 (implies (and (fn-rtc-st$ap s) (fn-ovrqp-live cur h base limit s))
  (fn-ovrqp-roomp h base (min limit (fn-rtc-buf-cap h (fn-rtc-config s))) s))
 :hints (("Goal" :in-theory (union-theories '(fn-ovrqp-live fn-ovrqp-roomp
   min unsigned-byte-p integer-range-p natp fn-ovrqp-buf-cap-natural)
  (theory 'minimal-theory))))))
(local (defthm fn-ovrqp-close-octets
 (fn-cbor-octet-listp (fn-ovr-close-octets owed legacyp))
 :hints (("Goal" :in-theory (union-theories '(fn-ovr-close-octets fn-ovw-empty-text
        (:executable-counterpart fn-ovw-status) (:executable-counterpart fn-cbor-octet-listp))
    (theory 'minimal-theory))))))
(local (defthm fn-ovrqp-adjacent-splice-okp
 (implies (and (fn-ovrqp-roomp h j limit s) (fn-cbor-octet-listp a) (fn-cbor-octet-listp b)
              (<= (+ j (len a) (len b)) limit))
  (fn-rtc-splice-okp h (+ j (len a)) b (fn-rtc-st$a-splice h j a s)))
 :hints (("Goal" :use ((:instance fn-ovrqp-room-after-splice (data a))
     (:instance fn-ovrqp-room-after-splice (data b) (j (+ j (len a)))
         (s (fn-rtc-st$a-splice h j a s))))
   :in-theory (union-theories '(fn-ovrqp-room-properties (:type-prescription len)
             associativity-of-+ natp-compound-recognizer) (theory 'minimal-theory))))))
(local (defthm fn-ovrqp-append-nil
 (implies (true-listp x) (equal (append x nil) x))
 :hints (("Goal" :induct (append x nil)
  :in-theory (union-theories '(binary-append true-listp car-cons cdr-cons) (theory 'minimal-theory))))))
(local (defthm fn-ovrp-step-empty
 (implies (and (consp cur) (not (nth 7 cur)) (natp (nth 3 cur))
               (< (nfix (nth 2 cur)) (nfix (nth 1 cur))))
  (equal (fn-ovw-step cur n fn-arena fn-cat)
         (mv (fn-ovr-close-octets (nth 5 cur) (nth 4 cur)) nil)))
 :hints (("Goal" :in-theory (e/d (fn-ovw-step fn-ovr-close-octets)
       (fn-ovw-hi fn-ovrp-body-step fn-ovrp-owed-step fn-ovr-probe-octets fn-ovr-probe-len))))))
(local (defthm fn-ovrqp-fill-done
 (implies (and (natp number) (< (nfix last) number))
  (equal (fn-ovr-fill group number last top owedp legacyp room server v h j st fn-arena fn-cat)
         (mv (- number 1) owedp j st)))
 :hints (("Goal" :in-theory (union-theories '(fn-ovr-fill fn-ovrqp-nfix-natural car-cons cdr-cons)
      (fn-dss-measure-theory))))))
(local (defthm fn-ovrqp-quantum-empty
 (implies (and (fn-rtc-st$ap s) (fn-ovrqp-live cur h base limit s)
               (< (nfix (nth 2 cur)) (nfix (nth 1 cur))))
  (let ((cap (min limit (fn-rtc-buf-cap h (fn-rtc-config s))))
        (out (fn-ovr-close-octets (nth 5 cur) (nth 4 cur))))
   (equal (fn-ovr-quantum cur w h base limit s fn-arena fn-cat)
    (if (< cap (+ base (len out))) (mv 0 cur base s)
     (mv 1 nil (+ base (len out)) (fn-rtc-st$a-splice h base out s))))))
 :hints (("Goal" :do-not-induct t
   :use (fn-ovrqp-live-room)
   :in-theory (union-theories '(fn-ovr-quantum fn-ovrqp-live fn-rtc-st-config fn-rtc-st$a-config
      fn-ovrqp-fill-done fn-ovrp-hi-top-lt fn-ovrp-hi-type
      fn-dsw-append-is-splice fn-ovrqp-empty-append-keeps-state fn-ovrqp-empty-append-position
      fn-ovrqp-room-properties fn-ovrqp-room-bounds fn-ovrqp-room-after-splice
      fn-ovrqp-close-octets fn-ovrqp-empty-splice fn-ovrqp-buf-cap-natural
      fn-ovrqp-nfix-natural fn-ovrqp-natural-nfix
      min max natp-compound-recognizer unsigned-byte-p integer-range-p fix cons-equal
      associativity-of-+ commutativity-of-+ commutativity-2-of-+ unicity-of-0 default-+-1 default-+-2
      car-cons cdr-cons len mv-nth zp (:type-prescription len) (:type-prescription fn-dsw-append))
     (set-difference-theories (fn-dss-measure-theory) '(nfix natp)))))))
(local (defthm fn-ovrqp-quantum-open
 (implies (and (fn-rtc-st$ap s) (fn-ovrqp-live cur h base limit s)
               (<= (nfix (nth 1 cur)) (nfix (nth 2 cur))))
  (let* ((k (nfix (nth 1 cur))) (top (nfix (nth 2 cur)))
         (hi (car (fn-ovrqp-fq cur w h base limit s)))
         (ow (fn-ovrp-owed (nth 0 cur) k hi (nth 5 cur) (nth 6 cur) (nfix (nth 3 cur)) fn-arena fn-cat))
         (body (fn-ovrp-body (nth 0 cur) k hi (nth 5 cur) (nth 6 cur) (nfix (nth 3 cur)) fn-arena fn-cat))
         (out (append body (if (<= top hi) (fn-ovr-close-octets ow (nth 4 cur)) nil))))
   (equal (fn-ovr-quantum cur w h base limit s fn-arena fn-cat)
    (if (< hi k) (mv 0 cur base s)
     (mv (+ 1 (- hi k))
       (if (<= top hi) nil (fn-ovw-cursor (nth 0 cur) (+ 1 hi) top (nfix (nth 3 cur)) (nth 4 cur) ow (nth 6 cur)))
       (+ base (len out)) (fn-rtc-st$a-splice h base out s))))))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories
 '(fn-ovr-quantum fn-ovrqp-live fn-rtc-st-config fn-rtc-st$a-config
   fn-dsw-append-is-splice fn-ovrqp-empty-append-keeps-state fn-ovrqp-empty-append-position
   fn-ovrqp-fill-owed fn-ovrqp-fill-hi-car-type fn-ovrqp-fill-hi-car-lower fn-ovrqp-fill-hi-car-upper
   fn-ovrp-hi-type fn-ovrp-hi-linear fn-ovrp-hi-natp fn-ovrp-hi-bounds
   fn-ovrqp-buf-cap-natural fn-ovrqp-natural-nfix fn-ovrqp-nfix-natural
   fn-ovrp-body-empty fn-ovrp-owed-empty fn-ovrqp-body-octets fn-ovrqp-close-octets
   fn-ovrqp-room-properties fn-ovrqp-room-bounds fn-ovrqp-room-after-splice fn-ovrqp-room-at-splice-position
   fn-ovrqp-compose-at-splice-position fn-ovrqp-splice-preserves-ap fn-ovrqp-empty-splice
   fn-ovrqp-octets-append fn-ovrqp-octets-cons fn-cbor-octet-listp-implies-true-listp
   fn-ovrqp-append-nil cons-equal fn-ovrqp-len-append fn-ovrqp-append-associates fn-ovrqp-fold-sums
   min max unsigned-byte-p integer-range-p natp-compound-recognizer fix
   associativity-of-+ commutativity-of-+ commutativity-2-of-+ unicity-of-0 default-+-1 default-+-2
   mv-nth zp posp car-cons cdr-cons len
   (:type-prescription len) (:type-prescription fn-ovr-fill) (:type-prescription fn-dsw-append))
 (set-difference-theories (fn-dss-measure-theory) '(nfix natp)))
  :use ((:instance fn-ovrqp-live-room)
 (:instance fn-ovrqp-adjacent-splice-okp (j base)
 (limit (min limit (fn-rtc-buf-cap h (fn-rtc-config s))))
 (a (fn-ovrp-body (nth 0 cur) (nfix (nth 1 cur)) (car (fn-ovrqp-fq cur w h base limit s))
       (nth 5 cur) (nth 6 cur) (nfix (nth 3 cur)) fn-arena fn-cat))
 (b (fn-ovr-close-octets
  (fn-ovrp-owed (nth 0 cur) (nfix (nth 1 cur)) (car (fn-ovrqp-fq cur w h base limit s))
       (nth 5 cur) (nth 6 cur) (nfix (nth 3 cur)) fn-arena fn-cat) (nth 4 cur))))
        (:instance fn-ovrqp-fill-is-body-splice
          (group (nth 0 cur)) (number (nfix (nth 1 cur)))
          (last (fn-ovw-hi (nfix (nth 1 cur)) (nfix (nth 2 cur)) w))
          (top (nfix (nth 2 cur))) (owedp (nth 5 cur)) (legacyp (nth 4 cur))
          (room (min limit (fn-rtc-buf-cap h (fn-rtc-config s))))
          (server (nth 6 cur)) (v (nfix (nth 3 cur))) (j base) (st s))
        (:instance fn-ovrqp-fill-fit
          (group (nth 0 cur)) (number (nfix (nth 1 cur)))
          (last (fn-ovw-hi (nfix (nth 1 cur)) (nfix (nth 2 cur)) w))
          (top (nfix (nth 2 cur))) (owedp (nth 5 cur)) (legacyp (nth 4 cur))
          (room (min limit (fn-rtc-buf-cap h (fn-rtc-config s))))
          (server (nth 6 cur)) (v (nfix (nth 3 cur))) (j base) (st s)
          (hi (car (fn-ovrqp-fq cur w h base limit s)))))))))
(local (defthm fn-ovrqp-tuple-parts
 (implies (equal q (if test (list a b c d) (list e f g hh)))
  (and (equal (car q) (if test a e))
       (equal (mv-nth 1 q) (if test b f))
       (equal (mv-nth 2 q) (if test c g))
       (equal (mv-nth 3 q) (if test d hh))))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories '(mv-nth zp car-cons cdr-cons) (theory 'minimal-theory))))))
(local (defthm fn-ovrqp-quantum-parts (implies (and (fn-rtc-st$ap s) (fn-ovrqp-live cur h base limit s)
               (<= (nfix (nth 1 cur)) (nfix (nth 2 cur)))) (let* ((k (nfix (nth 1 cur))) (top (nfix (nth 2 cur)))
         (hi (car (fn-ovrqp-fq cur w h base limit s)))
         (ow (fn-ovrp-owed (nth 0 cur) k hi (nth 5 cur) (nth 6 cur) (nfix (nth 3 cur)) fn-arena fn-cat))
         (body (fn-ovrp-body (nth 0 cur) k hi (nth 5 cur) (nth 6 cur) (nfix (nth 3 cur)) fn-arena fn-cat))
         (out (append body (if (<= top hi) (fn-ovr-close-octets ow (nth 4 cur)) nil)))) (and (equal (car (fn-ovr-quantum cur w h base limit s fn-arena fn-cat)) (if (< hi k) 0 (+ 1 (- hi k)))) (equal (mv-nth 1 (fn-ovr-quantum cur w h base limit s fn-arena fn-cat)) (if (< hi k) cur (if (<= top hi) nil (fn-ovw-cursor (nth 0 cur) (+ 1 hi) top (nfix (nth 3 cur)) (nth 4 cur) ow (nth 6 cur))))) (equal (mv-nth 2 (fn-ovr-quantum cur w h base limit s fn-arena fn-cat)) (if (< hi k) base (+ base (len out)))) (equal (mv-nth 3 (fn-ovr-quantum cur w h base limit s fn-arena fn-cat)) (if (< hi k) s (fn-rtc-st$a-splice h base out s))))))
 :hints (("Goal" :do-not-induct t :use (fn-ovrqp-quantum-open (:instance fn-ovrqp-tuple-parts (q (fn-ovr-quantum cur w h base limit s fn-arena fn-cat)) (test (< (car (fn-ovrqp-fq cur w h base limit s)) (nfix (nth 1 cur))))
 (a 0) (b cur) (c base) (d s)
 (e (+ 1 (- (car (fn-ovrqp-fq cur w h base limit s)) (nfix (nth 1 cur))))) (f (if (<= (nfix (nth 2 cur)) (car (fn-ovrqp-fq cur w h base limit s))) nil (fn-ovw-cursor (nth 0 cur) (+ 1 (car (fn-ovrqp-fq cur w h base limit s))) (nfix (nth 2 cur)) (nfix (nth 3 cur)) (nth 4 cur) (fn-ovrp-owed (nth 0 cur) (nfix (nth 1 cur)) (car (fn-ovrqp-fq cur w h base limit s)) (nth 5 cur) (nth 6 cur) (nfix (nth 3 cur)) fn-arena fn-cat) (nth 6 cur)))) (g (+ base (len (append (fn-ovrp-body (nth 0 cur) (nfix (nth 1 cur)) (car (fn-ovrqp-fq cur w h base limit s)) (nth 5 cur) (nth 6 cur) (nfix (nth 3 cur)) fn-arena fn-cat) (if (<= (nfix (nth 2 cur)) (car (fn-ovrqp-fq cur w h base limit s))) (fn-ovr-close-octets (fn-ovrp-owed (nth 0 cur) (nfix (nth 1 cur)) (car (fn-ovrqp-fq cur w h base limit s)) (nth 5 cur) (nth 6 cur) (nfix (nth 3 cur)) fn-arena fn-cat) (nth 4 cur)) nil))))) (hh (fn-rtc-st$a-splice h base (append (fn-ovrp-body (nth 0 cur) (nfix (nth 1 cur)) (car (fn-ovrqp-fq cur w h base limit s)) (nth 5 cur) (nth 6 cur) (nfix (nth 3 cur)) fn-arena fn-cat) (if (<= (nfix (nth 2 cur)) (car (fn-ovrqp-fq cur w h base limit s))) (fn-ovr-close-octets (fn-ovrp-owed (nth 0 cur) (nfix (nth 1 cur)) (car (fn-ovrqp-fq cur w h base limit s)) (nth 5 cur) (nth 6 cur) (nfix (nth 3 cur)) fn-arena fn-cat) (nth 4 cur)) nil)) s))))
 :in-theory (union-theories '(car-cons cdr-cons mv-nth zp) (theory 'minimal-theory))))))

(local (defthm fn-ovrqp-live-properties
 (implies (fn-ovrqp-live cur h base limit s)
  (and (consp cur) (not (nth 7 cur)) (fn-cbor-octet-listp (nth 6 cur))
       (natp base) (unsigned-byte-p 59 limit)
       (<= base (min limit (fn-rtc-buf-cap h (fn-rtc-config s))))
       (fn-rtc-splice-okp h base nil s)))
 :rule-classes (:rewrite (:forward-chaining :trigger-terms ((fn-ovrqp-live cur h base limit s))))
 :hints (("Goal" :in-theory (union-theories '(fn-ovrqp-live) (theory 'minimal-theory))))))
(local (defthm fn-ovrp-step-octets-car (implies (and (consp cur) (not (nth 7 cur)) (natp (nth 3 cur)))
            (equal (car (fn-ovw-step cur n fn-arena fn-cat))
                   (let* ((k (nfix (nth 1 cur))) (top (nfix (nth 2 cur)))
                          (hi (fn-ovw-hi k top n)))
                     (append (fn-ovrp-body (nth 0 cur) k hi (nth 5 cur) (nth 6 cur) (nth 3 cur)
                                           fn-arena fn-cat)
                             (if (<= top hi)
                                 (fn-ovr-close-octets
                                  (fn-ovrp-owed (nth 0 cur) k hi (nth 5 cur) (nth 6 cur) (nth 3 cur)
                                                fn-arena fn-cat)
                                  (nth 4 cur))
                               nil)))))
 :hints (("Goal" :use fn-ovrp-step-octets-fast
  :in-theory (union-theories '(mv-nth zp (:type-prescription fn-ovw-step)) (theory 'minimal-theory))))))
(local (defthm fn-ovrqp-quantum-empty-parts (implies (and (fn-rtc-st$ap s) (fn-ovrqp-live cur h base limit s)
               (< (nfix (nth 2 cur)) (nfix (nth 1 cur)))) (let* ((cap (min limit (fn-rtc-buf-cap h (fn-rtc-config s))))
        (out (fn-ovr-close-octets (nth 5 cur) (nth 4 cur)))) (and (equal (car (fn-ovr-quantum cur w h base limit s fn-arena fn-cat)) (if (< cap (+ base (len out))) 0 1)) (equal (mv-nth 1 (fn-ovr-quantum cur w h base limit s fn-arena fn-cat)) (if (< cap (+ base (len out))) cur nil)) (equal (mv-nth 2 (fn-ovr-quantum cur w h base limit s fn-arena fn-cat)) (if (< cap (+ base (len out))) base (+ base (len out)))) (equal (mv-nth 3 (fn-ovr-quantum cur w h base limit s fn-arena fn-cat)) (if (< cap (+ base (len out))) s (fn-rtc-st$a-splice h base out s))))))
 :hints (("Goal" :do-not-induct t :use (fn-ovrqp-quantum-empty (:instance fn-ovrqp-tuple-parts (q (fn-ovr-quantum cur w h base limit s fn-arena fn-cat)) (test (< (min limit (fn-rtc-buf-cap h (fn-rtc-config s))) (+ base (len (fn-ovr-close-octets (nth 5 cur) (nth 4 cur)))))) (a 0) (b cur) (c base) (d s) (e 1) (f nil) (g (+ base (len (fn-ovr-close-octets (nth 5 cur) (nth 4 cur))))) (hh (fn-rtc-st$a-splice h base (fn-ovr-close-octets (nth 5 cur) (nth 4 cur)) s))))
 :in-theory (union-theories '(car-cons cdr-cons mv-nth zp) (theory 'minimal-theory))))))
(local (defthm fn-ovrqp-KL1
  (implies (and (fn-ovw-cursorp cur) (fn-rtc-st$ap s))
           (mv-let (n next j s2) (fn-ovr-quantum cur w h base limit s fn-arena fn-cat)
             (let ((step (fn-ovw-step cur n fn-arena fn-cat)))
               (if (posp n)
                   (and (equal s2 (fn-rtc-st$a-splice h base (mv-nth 0 step) s))
                        (equal j (+ (nfix base) (len (mv-nth 0 step))))
                        (equal next (mv-nth 1 step)))
                 (and (equal s2 s) (equal j (nfix base)) (equal next cur))))))
 :hints (("Goal" :do-not-induct t :do-not '(preprocess)
  :cases ((not (fn-ovrqp-live cur h base limit s))
          (and (fn-ovrqp-live cur h base limit s) (<= (nfix (nth 1 cur)) (nfix (nth 2 cur))))
          (and (fn-ovrqp-live cur h base limit s) (< (nfix (nth 2 cur)) (nfix (nth 1 cur)))))
  :use (fn-ovrqp-quantum-empty-parts fn-ovrqp-quantum-parts fn-ovrqp-quantum-open fn-ovrqp-quantum-empty fn-ovrqp-quantum-closed
 (:instance fn-ovrp-hi-n
       (k (nfix (nth 1 cur))) (top (nfix (nth 2 cur)))
       (hi (car (fn-ovrqp-fq cur w h base limit s)))))
  :in-theory (union-theories
   '(fn-ovrqp-quantum-empty-parts fn-ovrqp-quantum-parts fn-ovrqp-quantum-closed fn-ovrqp-quantum-open fn-ovrqp-quantum-empty fn-ovrqp-live-properties
     fn-ovw-cursorp fn-ovrp-step-empty fn-ovrp-step-octets-car fn-ovrp-step-octets-fast fn-ovrp-step-next-fast fn-ovrp-hi-top-lt
     fn-ovrp-body-empty fn-ovrp-owed-empty fn-ovrp-hi-type fn-ovrp-hi-linear fn-ovrp-hi-bounds
     fn-ovrqp-fill-hi-car-type fn-ovrqp-fill-hi-car-lower fn-ovrqp-fill-hi-car-upper
     fn-ovrqp-body-octets fn-ovrqp-close-octets fn-ovrqp-nfix-natural fn-ovrqp-natural-nfix
     fn-ovrqp-append-nil fn-cbor-octet-listp-implies-true-listp
     mv-nth car-cons cdr-cons cons-equal posp zp natp-compound-recognizer
     associativity-of-+ commutativity-of-+ commutativity-2-of-+ unicity-of-0 default-+-1 default-+-2 fix
     (:type-prescription fn-ovw-step) (:type-prescription fn-ovr-quantum) (:type-prescription len) (:type-prescription fn-ovr-fill))
    (set-difference-theories (fn-dss-measure-theory) '(nfix natp)))))))
(local (set-default-hints '((quote (:use fn-ovrqp-KL1 :in-theory (theory 'minimal-theory))))))
(defthm fn-ovr-quantum-is-the-step
  (implies (and (fn-ovw-cursorp cur) (fn-rtc-st$ap s))
           (mv-let (n next j s2) (fn-ovr-quantum cur w h base limit s fn-arena fn-cat)
             (let ((step (fn-ovw-step cur n fn-arena fn-cat)))
               (if (posp n)
                   (and (equal s2 (fn-rtc-st$a-splice h base (mv-nth 0 step) s))
                        (equal j (+ (nfix base) (len (mv-nth 0 step))))
                        (equal next (mv-nth 1 step)))
                 (and (equal s2 s) (equal j (nfix base)) (equal next cur)))))))
(local (set-default-hints nil))

(local (defthm fn-ovrqp-quantum-open-okp
 (implies (and (fn-rtc-st$ap s) (fn-ovrqp-live cur h base limit s)
              (<= (nfix (nth 1 cur)) (nfix (nth 2 cur)))
              (<= (nfix (nth 1 cur)) (car (fn-ovrqp-fq cur w h base limit s))))
  (let* ((hi (car (fn-ovrqp-fq cur w h base limit s)))
    (body (fn-ovrp-body (nth 0 cur) (nfix (nth 1 cur)) hi (nth 5 cur) (nth 6 cur) (nfix (nth 3 cur)) fn-arena fn-cat))
    (ow (fn-ovrp-owed (nth 0 cur) (nfix (nth 1 cur)) hi (nth 5 cur) (nth 6 cur) (nfix (nth 3 cur)) fn-arena fn-cat))
    (out (append body (if (<= (nfix (nth 2 cur)) hi) (fn-ovr-close-octets ow (nth 4 cur)) nil))))
   (and (fn-rtc-splice-okp h base out s)
        (<= (+ base (len out)) (min limit (fn-rtc-buf-cap h (fn-rtc-config s)))))))
 :hints (("Goal" :do-not-induct t
  :use (fn-ovrqp-live-room
   (:instance fn-ovrqp-fill-fit
    (group (nth 0 cur)) (number (nfix (nth 1 cur)))
    (last (fn-ovw-hi (nfix (nth 1 cur)) (nfix (nth 2 cur)) w))
    (top (nfix (nth 2 cur))) (owedp (nth 5 cur)) (legacyp (nth 4 cur))
    (room (min limit (fn-rtc-buf-cap h (fn-rtc-config s))))
    (server (nth 6 cur)) (v (nfix (nth 3 cur))) (j base) (st s)
    (hi (car (fn-ovrqp-fq cur w h base limit s)))))
  :in-theory (union-theories '(fn-ovrqp-live-properties fn-ovrqp-room-properties fn-ovrqp-room-bounds
    fn-ovrqp-room-after-splice fn-ovrqp-body-octets fn-ovrqp-close-octets fn-ovrqp-octets-append
    fn-ovrqp-natural-nfix fn-ovrqp-nfix-natural fn-ovrqp-len-append
    fn-ovrp-hi-type fn-ovrp-hi-linear fn-ovrp-hi-bounds
    min len natp-compound-recognizer car-cons cdr-cons (:type-prescription len)
    (:executable-counterpart fn-cbor-octet-listp)) (fn-dss-measure-theory))))))
(local (defthm fn-ovrqp-KL1o
  (implies (and (fn-ovw-cursorp cur) (fn-rtc-st$ap s))
           (let ((n (mv-nth 0 (fn-ovr-quantum cur w h base limit s fn-arena fn-cat))))
             (implies (posp n)
                      (fn-rtc-splice-okp h base (mv-nth 0 (fn-ovw-step cur n fn-arena fn-cat)) s))))
 :hints (("Goal" :do-not-induct t :do-not '(preprocess)
  :cases ((not (fn-ovrqp-live cur h base limit s))
          (and (fn-ovrqp-live cur h base limit s) (<= (nfix (nth 1 cur)) (nfix (nth 2 cur))))
          (and (fn-ovrqp-live cur h base limit s) (< (nfix (nth 2 cur)) (nfix (nth 1 cur)))))
  :use (fn-ovrqp-quantum-open-okp fn-ovrqp-live-room
 (:instance fn-ovrqp-room-after-splice (j base)
 (limit (min limit (fn-rtc-buf-cap h (fn-rtc-config s))))
 (data (fn-ovr-close-octets (nth 5 cur) (nth 4 cur))))
 fn-ovrqp-quantum-empty-parts fn-ovrqp-quantum-parts fn-ovrqp-quantum-open fn-ovrqp-quantum-empty fn-ovrqp-quantum-closed
 (:instance fn-ovrp-hi-n
       (k (nfix (nth 1 cur))) (top (nfix (nth 2 cur)))
       (hi (car (fn-ovrqp-fq cur w h base limit s)))))
  :in-theory (union-theories
   '(fn-ovrqp-room-after-splice fn-ovrqp-room-properties fn-ovrqp-live-room fn-ovrqp-close-octets
 fn-ovrqp-quantum-open-okp fn-ovrqp-quantum-empty-parts fn-ovrqp-quantum-parts fn-ovrqp-quantum-closed fn-ovrqp-quantum-open fn-ovrqp-quantum-empty fn-ovrqp-live-properties
     fn-ovw-cursorp fn-ovrp-step-empty fn-ovrp-step-octets-car fn-ovrp-step-octets-fast fn-ovrp-step-next-fast fn-ovrp-hi-top-lt
     fn-ovrp-body-empty fn-ovrp-owed-empty fn-ovrp-hi-type fn-ovrp-hi-linear fn-ovrp-hi-bounds
     fn-ovrqp-fill-hi-car-type fn-ovrqp-fill-hi-car-lower fn-ovrqp-fill-hi-car-upper
     fn-ovrqp-body-octets fn-ovrqp-close-octets fn-ovrqp-nfix-natural fn-ovrqp-natural-nfix
     fn-ovrqp-append-nil fn-cbor-octet-listp-implies-true-listp
     mv-nth car-cons cdr-cons cons-equal posp zp natp-compound-recognizer
     associativity-of-+ commutativity-of-+ commutativity-2-of-+ unicity-of-0 default-+-1 default-+-2 fix
     (:type-prescription fn-ovw-step) (:type-prescription fn-ovr-quantum) (:type-prescription len) (:type-prescription fn-ovr-fill))
    (set-difference-theories (fn-dss-measure-theory) '(nfix natp)))))))
(local (set-default-hints '((quote (:use fn-ovrqp-KL1o :in-theory (theory 'minimal-theory))))))
(defthm fn-ovr-quantum-taken-is-splice-okp
  (implies (and (fn-ovw-cursorp cur) (fn-rtc-st$ap s))
           (let ((n (mv-nth 0 (fn-ovr-quantum cur w h base limit s fn-arena fn-cat))))
             (implies (posp n)
                      (fn-rtc-splice-okp h base (mv-nth 0 (fn-ovw-step cur n fn-arena fn-cat)) s)))))
(local (set-default-hints nil))

(local (defthm fn-ovrqp-invp-is-ap
 (implies (fn-rtc-invp s) (fn-rtc-st$ap s))
 :hints (("Goal" :use fn-rtc-invp-implies-st-p
   :in-theory (union-theories '(fn-dsw-st-p-is-abstract-recognizer) (theory 'minimal-theory))))))
(local (defthm fn-ovrqp-splice-keeps-invp
 (implies (fn-rtc-invp s) (fn-rtc-invp (fn-rtc-st$a-splice h base data s)))
 :hints (("Goal" :use ((:instance fn-rtc-splice-keeps-invp (st s) (off base)))
   :in-theory (union-theories '(fn-rtc-st-splice) (theory 'minimal-theory))))))
(local (defthm fn-ovrqp-ready-generation
 (implies (and (fn-rtc-invp s) (fn-hl-render-ready-p h id inc s))
  (natp (fn-rtc-get 0 (fn-rtc-buffer h s))))
 :hints (("Goal" :use (fn-rtc-invp-implies-core-invp fn-rtc-core-invp-buffer)
  :in-theory (union-theories '(fn-hl-render-ready-p fn-rtc-buffer-okp fn-rtc-bufferp)
    (theory 'minimal-theory))))))
(local (defthm fn-ovrqp-view-at-base
 (implies (and (fn-rtc-st$ap s) (natp base) (fn-rtc-splice-okp h base data s))
  (equal (fn-dsw-view h base (+ base (len data)) (fn-rtc-st$a-splice h base data s)) data))
 :hints (("Goal" :use ((:instance fn-dsw-view-appends-within-fill (j base)))
    :in-theory (union-theories '(fn-dsw-view binary-append natp take zp associativity-of-+ commutativity-of-+ commutativity-2-of-+ inverse-of-+ car-cons cdr-cons default-+-1 default-+-2
      (:executable-counterpart take)) (theory 'minimal-theory))))))
(local (defthm fn-ovrqp-splice-is-the-write-request
 (implies (and (fn-rtc-invp s) (fn-hl-render-ready-p h id inc s)
              (fn-rtc-splice-okp h base data s) (consp data))
  (equal (fn-rtc-st$a-splice h base data s)
   (mv-nth 0 (fn-rtc-req-write (list :write h (fn-rtc-get 0 (fn-rtc-buffer h s)) base data) id inc s))))
 :hints (("Goal" :use (fn-ovrqp-ready-generation (:instance fn-dsw-splice-is-puts (j base))
   (:instance fn-rtc-puts-is-the-write-request (w data) (off base) (g (fn-rtc-get 0 (fn-rtc-buffer h s)))))
   :in-theory (union-theories '(fn-ovrqp-invp-is-ap fn-ovrqp-ready-generation fn-hl-render-ready-p
      fn-rtc-splice-okp) (theory 'minimal-theory))))))
(local (defthm fn-ovrqp-positive-is-live
 (implies (and (fn-rtc-st$ap s)
              (posp (mv-nth 0 (fn-ovr-quantum cur w h base limit s fn-arena fn-cat))))
  (fn-ovrqp-live cur h base limit s))
 :hints (("Goal" :do-not-induct t :cases ((fn-ovrqp-live cur h base limit s))
   :in-theory (union-theories '(fn-ovrqp-quantum-closed posp mv-nth zp car-cons cdr-cons)
     (theory 'minimal-theory))))))
(local (defthm fn-ovrqp-KL1v
  (implies (and (fn-ovw-cursorp cur) (fn-rtc-invp s) (fn-hl-render-ready-p h id inc s))
           (mv-let (n next j s2) (fn-ovr-quantum cur w h base limit s fn-arena fn-cat)
             (declare (ignore next))
             (implies (posp n)
                      (and (equal (fn-dsw-view h base j s2) (mv-nth 0 (fn-ovw-step cur n fn-arena fn-cat)))
                           (implies (< base j)
                                    (equal s2 (mv-nth 0 (fn-rtc-req-write
                                                         (list :write h (fn-rtc-get 0 (fn-rtc-buffer h s)) base
                                                               (fn-dsw-view h base j s2))
                                                         id inc s))))
                           (fn-rtc-invp s2)))))
 :hints (("Goal" :do-not-induct t :do-not '(preprocess)
  :use (fn-ovr-quantum-is-the-step fn-ovr-quantum-taken-is-splice-okp fn-ovrqp-invp-is-ap
    fn-ovrqp-positive-is-live
    (:instance fn-ovrqp-view-at-base (data (mv-nth 0 (fn-ovw-step cur (mv-nth 0 (fn-ovr-quantum cur w h base limit s fn-arena fn-cat)) fn-arena fn-cat))))
    (:instance fn-ovrqp-splice-keeps-invp (data (mv-nth 0 (fn-ovw-step cur (mv-nth 0 (fn-ovr-quantum cur w h base limit s fn-arena fn-cat)) fn-arena fn-cat))))
    (:instance fn-ovrqp-splice-is-the-write-request (data (mv-nth 0 (fn-ovw-step cur (mv-nth 0 (fn-ovr-quantum cur w h base limit s fn-arena fn-cat)) fn-arena fn-cat)))))
  :in-theory (union-theories '(fn-ovrqp-invp-is-ap fn-ovrqp-live-properties
    fn-ovrqp-nfix-natural fn-ovrqp-natural-nfix fn-ovrp-len-pos
    fn-ovrqp-view-at-base fn-ovrqp-splice-keeps-invp fn-ovrqp-splice-is-the-write-request
    car-cons cdr-cons mv-nth zp posp len natp-compound-recognizer
    (:type-prescription fn-ovr-quantum) (:type-prescription fn-ovw-step) (:type-prescription len)
    associativity-of-+ commutativity-of-+ commutativity-2-of-+ inverse-of-+ unicity-of-0 default-+-1 default-+-2 fix)
    (set-difference-theories (fn-dss-measure-theory) '(nfix natp)))))))
(local (set-default-hints '((quote (:use fn-ovrqp-KL1v :in-theory (theory 'minimal-theory))))))
(defthm fn-ovr-quantum-view-is-the-step
  (implies (and (fn-ovw-cursorp cur) (fn-rtc-invp s) (fn-hl-render-ready-p h id inc s))
           (mv-let (n next j s2) (fn-ovr-quantum cur w h base limit s fn-arena fn-cat)
             (declare (ignore next))
             (implies (posp n)
                      (and (equal (fn-dsw-view h base j s2) (mv-nth 0 (fn-ovw-step cur n fn-arena fn-cat)))
                           (implies (< base j)
                                    (equal s2 (mv-nth 0 (fn-rtc-req-write
                                                         (list :write h (fn-rtc-get 0 (fn-rtc-buffer h s)) base
                                                               (fn-dsw-view h base j s2))
                                                         id inc s))))
                           (fn-rtc-invp s2))))))
(local (set-default-hints nil))

(local (defthm fn-ovrup-fill-reserves-close
 (implies (and (natp j) (<= j (nfix room)) (natp number) (natp last) (natp top) (<= last top)
              (fn-cbor-octet-listp server)
              (implies (< top number) (<= (+ j (len (fn-ovr-close-octets owedp legacyp))) (nfix room))))
  (mv-let (hi ow j2 st2) (fn-ovr-fill group number last top owedp legacyp room server v h j st fn-arena fn-cat)
   (declare (ignore st2))
   (implies (<= top hi) (<= (+ j2 (len (fn-ovr-close-octets ow legacyp))) (nfix room)))))
 :hints (("Goal" :induct (fn-ovr-fill group number last top owedp legacyp room server v h j st fn-arena fn-cat)
  :in-theory (union-theories '(fn-ovrwp-fill-open (:induction fn-ovr-fill)
    fn-ovrup-probe-advance fn-ovrup-octets-advance fn-ovrqp-octets-position fn-ovrqp-octets-position-linear
    fn-ovrup-probe-position fn-ovrup-probe-position-linear
    fn-ovrqp-nfix-natural fn-ovrqp-natural-nfix fn-ovrqp-fill-hi-car-type fn-ovrqp-fill-hi-car-lower
    fn-ovrqp-fill-hi-car-upper fn-ovrqp-fill-done
    fn-ovr-close-octets fn-ovrqp-fold-sums associativity-of-+ commutativity-of-+ commutativity-2-of-+
    fix unicity-of-0 default-+-1 default-+-2 car-cons cdr-cons mv-nth zp posp natp-compound-recognizer
    (:type-prescription len) (:type-prescription fn-ovr-probe-len) (:type-prescription fn-ovr-fill)
    (:executable-counterpart fn-ovr-status-octets) (:executable-counterpart fn-ovw-status))
    (set-difference-theories (fn-dss-measure-theory) '(natp nfix)))))))

(local (defthm fn-ovrup-append-position
 (implies (and (natp j) (<= (+ j (len data)) (nfix limit)))
  (<= (mv-nth 1 (fn-dsw-append h j data s)) (nfix limit)))
 :hints (("Goal" :in-theory (union-theories '(fn-dsw-append natp nfix car-cons cdr-cons len
   (:type-prescription len)) (fn-dss-measure-theory))))))
(local (defthm fn-ovrqp-KL2
 (implies (<= (nfix base) (nfix limit))
  (<= (mv-nth 2 (fn-ovr-quantum cur w h base limit s fn-arena fn-cat)) (nfix limit)))
 :hints (("Goal" :do-not-induct t :do-not '(preprocess)
  :use ((:instance fn-ovrp-hi-natp (k (nfix (nth 1 cur))) (top (nfix (nth 2 cur))) (w w))
 (:instance fn-ovrp-hi-le-top (k (nfix (nth 1 cur))) (top (nfix (nth 2 cur))) (w w))
 (:instance fn-ovrup-append-position
 (j (mv-nth 2 (fn-ovrqp-fq cur w h base limit s)))
 (data (fn-ovr-close-octets (mv-nth 1 (fn-ovrqp-fq cur w h base limit s)) (nth 4 cur)))
 (s (mv-nth 3 (fn-ovrqp-fq cur w h base limit s))) (limit (min limit (fn-rtc-buf-cap h (fn-rtc-config s)))))
 (:instance fn-ovrup-fill-position
    (group (nth 0 cur)) (number (nfix (nth 1 cur)))
    (last (fn-ovw-hi (nfix (nth 1 cur)) (nfix (nth 2 cur)) w))
    (top (nfix (nth 2 cur))) (owedp (nth 5 cur)) (legacyp (nth 4 cur))
    (room (min limit (fn-rtc-buf-cap h (fn-rtc-config s))))
    (server (nth 6 cur)) (v (nfix (nth 3 cur))) (j base) (st s))
   (:instance fn-ovrup-fill-reserves-close
    (group (nth 0 cur)) (number (nfix (nth 1 cur)))
    (last (fn-ovw-hi (nfix (nth 1 cur)) (nfix (nth 2 cur)) w))
    (top (nfix (nth 2 cur))) (owedp (nth 5 cur)) (legacyp (nth 4 cur))
    (room (min limit (fn-rtc-buf-cap h (fn-rtc-config s))))
    (server (nth 6 cur)) (v (nfix (nth 3 cur))) (j base) (st s)))
  :in-theory (union-theories '(fn-ovr-quantum fn-rtc-st-config fn-rtc-st$a-config
   fn-ovrqp-empty-append-keeps-state fn-ovrqp-empty-append-position fn-ovrup-append-position
   fn-ovrqp-buf-cap-natural fn-ovrqp-nfix-natural fn-ovrqp-natural-nfix
   fn-ovrp-hi-type fn-ovrp-hi-bounds fn-ovrp-hi-linear fn-ovrp-hi-top-lt
   fn-ovrqp-fill-done fn-ovrqp-fill-hi-car-type
   min natp nfix unsigned-byte-p integer-range-p mv-nth zp posp car-cons cdr-cons
   (:type-prescription len) (:type-prescription fn-ovr-fill) (:type-prescription fn-dsw-append))
   (fn-dss-measure-theory))))))
(local (set-default-hints '((quote (:use fn-ovrqp-KL2 :in-theory (theory 'minimal-theory))))))
(defthm fn-ovr-quantum-within-the-lease
  (implies (<= (nfix base) (nfix limit))
           (<= (mv-nth 2 (fn-ovr-quantum cur w h base limit s fn-arena fn-cat)) (nfix limit))))
(local (set-default-hints nil))



; Greedy stop and one-article extension. All supporting models are local.
(local (defun fn-ovrp-ext (group j top ow legacyp server v fn-arena fn-cat)
   (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
   (let ((pl (fn-ovr-probe-octets group j server v fn-arena fn-cat)))
     (+ (len pl)
        (if (and ow (consp pl)) (len (fn-ovr-status-octets)) 0)
        (if (<= (nfix top) j)
            (len (fn-ovr-close-octets (and ow (not (consp pl))) legacyp))
          0)))))

(local (defthm fn-ovrqp-fill-max
 (implies (and (fn-ovrqp-roomp h j room st) (natp number) (natp last) (natp top) (natp v)
              (fn-cbor-octet-listp server) (<= number last) (<= last top)
              (equal hi (car (fn-ovr-fill group number last top owedp legacyp room server v h j st fn-arena fn-cat)))
              (< hi last))
  (< room (+ j (len (fn-ovrp-body group number hi owedp server v fn-arena fn-cat))
      (fn-ovrp-ext group (+ 1 hi) top (fn-ovrp-owed group number hi owedp server v fn-arena fn-cat)
                  legacyp server v fn-arena fn-cat))))
 :hints (("Goal" :induct (fn-ovr-fill group number last top owedp legacyp room server v h j st fn-arena fn-cat)
  :in-theory (union-theories '(fn-ovrwp-fill-open (:induction fn-ovr-fill) fn-ovrp-ext
   fn-ovr-probe-len-is-the-length fn-ovrp-body-step fn-ovrp-body-empty fn-ovrp-owed-step fn-ovrp-owed-empty
   fn-ovrp-len-pos fn-ovrqp-fill-is-body-splice fn-ovrqp-fill-owed fn-ovrqp-fill-hi-car-type
   fn-ovrqp-fill-hi-car-lower fn-ovrqp-fill-hi-car-upper
   fn-ovrqp-octets-is-splice fn-ovrqp-probe-is-splice fn-ovrqp-probe-octets fn-ovrqp-body-octets
   fn-ovrqp-room-properties fn-ovrqp-room-bounds fn-ovrqp-room-at-splice-position
   fn-ovrqp-compose-at-splice-position fn-ovrqp-empty-splice fn-ovrqp-octets-append fn-ovrqp-octets-cons
   fn-ovrqp-nfix-natural fn-ovrqp-natural-nfix fn-ovrqp-len-append fn-ovrqp-fold-sums
   associativity-of-+ commutativity-of-+ commutativity-2-of-+ fix unicity-of-0 default-+-1 default-+-2
   natp-compound-recognizer mv-nth zp posp car-cons cdr-cons len (:type-prescription len)
   (:type-prescription fn-ovr-fill) (:type-prescription fn-ovr-probe-octets)
   (:executable-counterpart fn-ovr-status-octets) (:executable-counterpart fn-cbor-octet-listp))
   (set-difference-theories (fn-dss-measure-theory) '(natp nfix)))))))

(local (defthm fn-ovrp-step-at
   (implies (and (consp cur) (not (nth 7 cur)) (natp (nth 3 cur))
                 (integerp hi) (<= (nfix (nth 1 cur)) hi)
                 (<= hi (fn-ovw-hi (nfix (nth 1 cur)) (nfix (nth 2 cur)) w)))
            (let ((k (nfix (nth 1 cur))) (top (nfix (nth 2 cur))))
              (and (equal (mv-nth 0 (fn-ovw-step cur (+ 1 (- hi k)) fn-arena fn-cat))
                          (append (fn-ovrp-body (nth 0 cur) k hi (nth 5 cur) (nth 6 cur) (nth 3 cur)
                                                fn-arena fn-cat)
                                  (if (<= top hi)
                                      (fn-ovr-close-octets
                                       (fn-ovrp-owed (nth 0 cur) k hi (nth 5 cur) (nth 6 cur) (nth 3 cur)
                                                     fn-arena fn-cat)
                                       (nth 4 cur))
                                    nil)))
                   (equal (mv-nth 1 (fn-ovw-step cur (+ 1 (- hi k)) fn-arena fn-cat))
                          (if (<= top hi)
                              nil
                            (fn-ovw-cursor (nth 0 cur) (+ 1 hi) top (nth 3 cur) (nth 4 cur)
                                           (fn-ovrp-owed (nth 0 cur) k hi (nth 5 cur) (nth 6 cur)
                                                         (nth 3 cur) fn-arena fn-cat)
                                           (nth 6 cur)))))))
   :hints (("Goal" :in-theory (disable fn-ovrp-step-octets fn-ovrp-step-next fn-ovrp-hi-n fn-ovw-step fn-ovw-hi)
            :use ((:instance fn-ovrp-step-octets (n (+ 1 (- hi (nfix (nth 1 cur)))))) 
                  (:instance fn-ovrp-step-next (n (+ 1 (- hi (nfix (nth 1 cur)))))) 
                  (:instance fn-ovrp-hi-n (k (nfix (nth 1 cur))) (top (nfix (nth 2 cur)))))))))

(local (defthm fn-ovrp-owed-snoc
   (implies (and (natp j) (integerp hi) (<= (- j 1) hi))
            (equal (fn-ovrp-owed group j (+ 1 hi) owedp server v fn-arena fn-cat)
                   (and (fn-ovrp-owed group j hi owedp server v fn-arena fn-cat)
                        (not (consp (fn-ovr-probe-octets group (+ 1 hi) server v fn-arena fn-cat))))))
   :hints (("Goal" :in-theory (disable fn-ovrp-owed-step fn-ovrp-body-step)
            :use (fn-ovrp-win-extend
                  (:instance fn-ovrp-owed-is-window (hi (+ 1 hi)))
                  (:instance fn-ovrp-owed-is-window)
                  (:instance fn-ovrp-probe-is-win (j (+ 1 hi))))))))

(local (defthm fn-ovrp-top-eq
   (implies (and (natp top) (integerp hh) (<= top (+ 1 hh)) (<= (+ 1 hh) (fn-ovw-hi k top w)))
            (equal top (+ 1 hh)))
   :rule-classes nil
   :hints (("Goal" :use (fn-ovrp-hi-le-top fn-ovrp-hi-natp)))))

(local (defthm fn-ovrp-ext-step
   (implies (and (consp cur) (not (nth 7 cur)) (natp (nth 3 cur)) (integerp hh)
                 (<= (- (nfix (nth 1 cur)) 1) hh)
                 (<= (+ 1 hh) (fn-ovw-hi (nfix (nth 1 cur)) (nfix (nth 2 cur)) w)))
            (equal (len (mv-nth 0 (fn-ovw-step cur (+ 1 (- (+ 1 hh) (nfix (nth 1 cur)))) fn-arena fn-cat)))
                   (+ (len (fn-ovrp-body (nth 0 cur) (nfix (nth 1 cur)) hh (nth 5 cur) (nth 6 cur)
                                         (nth 3 cur) fn-arena fn-cat))
                      (fn-ovrp-ext (nth 0 cur) (+ 1 hh) (nfix (nth 2 cur))
                                   (fn-ovrp-owed (nth 0 cur) (nfix (nth 1 cur)) hh (nth 5 cur) (nth 6 cur)
                                                 (nth 3 cur) fn-arena fn-cat)
                                   (nth 4 cur) (nth 6 cur) (nth 3 cur) fn-arena fn-cat))))
   :hints (("Goal" :in-theory (union-theories '(fn-ovrp-ext fn-ovrqp-len-append fn-ovrp-len-pos
 fn-ovrqp-natural-nfix fn-ovrqp-nfix-natural fn-ovrqp-fold-sums
 len (:type-prescription len) (:type-prescription fn-ovr-probe-octets) (:type-prescription fn-ovw-step)
 car-cons cdr-cons mv-nth zp posp natp-compound-recognizer fix inverse-of-+
 associativity-of-+ commutativity-of-+ commutativity-2-of-+ unicity-of-0)
 (set-difference-theories (fn-dss-measure-theory) '(natp nfix)))
            :use ((:instance fn-ovrp-step-at (hi (+ 1 hh)))
                  (:instance fn-ovrp-hi-le-top (k (nfix (nth 1 cur))) (top (nfix (nth 2 cur))))
                  (:instance fn-ovrp-top-eq (k (nfix (nth 1 cur))) (top (nfix (nth 2 cur))))
                  (:instance fn-ovrp-body-snoc (j (nfix (nth 1 cur))) (hi hh) (group (nth 0 cur))
                             (owedp (nth 5 cur)) (server (nth 6 cur)) (v (nth 3 cur)))
                  (:instance fn-ovrp-owed-snoc (j (nfix (nth 1 cur))) (hi hh) (group (nth 0 cur))
                             (owedp (nth 5 cur)) (server (nth 6 cur)) (v (nth 3 cur))))))))

(local (defthm fn-ovrp-hi-int
   (integerp (fn-ovw-hi k (nfix top) w))
   :rule-classes nil
   :hints (("Goal" :use (:instance fn-ovrp-hi-natp (top (nfix top)))))))

(local (defthm fn-ovrp-hi-ge-k
   (implies (and (natp k) (natp top) (<= k top))
            (<= k (fn-ovw-hi k top w)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-ovw-hi)))))

(local (defthm fn-ovrqp-ready-empty-okp
 (implies (and (fn-hl-render-ready-p h id inc s) (natp base)
               (<= base (len (fn-rtc-b-bytes (fn-rtc-buffer h s))))
               (<= base (fn-rtc-buf-cap h (fn-rtc-config s))))
  (fn-rtc-splice-okp h base nil s))
 :hints (("Goal" :in-theory (union-theories '(fn-hl-render-ready-p fn-rtc-splice-okp
 fn-rtc-splice-target-p fn-rtc-get-of-cons fn-rtc-get nfix len natp zp car-cons cdr-cons
 (:executable-counterpart fn-cbor-octet-listp)) (theory 'minimal-theory))))))

(local (defthm fn-ovrqp-kl4-ready-live
 (implies (and (consp cur) (not (nth 7 cur)) (fn-cbor-octet-listp (nth 6 cur))
 (natp base) (unsigned-byte-p 59 limit) (<= base limit)
 (fn-hl-render-ready-p h id inc s)
 (<= base (len (fn-rtc-b-bytes (fn-rtc-buffer h s))))
 (<= limit (fn-rtc-buf-cap h (fn-rtc-config s))))
 (fn-ovrqp-live cur h base limit s))
 :hints (("Goal" :use fn-ovrqp-ready-empty-okp
 :in-theory (union-theories '(fn-ovrqp-live min) (theory 'minimal-theory))))))

(local (defthm fn-ovrqp-kl4
  (implies (and (fn-ovw-cursorp cur) (consp cur) (not (nth 7 cur)) (fn-cbor-octet-listp (nth 6 cur))
                (natp base) (unsigned-byte-p 59 limit)
                (fn-rtc-st$ap s) (fn-hl-render-ready-p h id inc s)
                (<= base (len (fn-rtc-b-bytes (fn-rtc-buffer h s))))
                (<= (nfix limit) (fn-rtc-buf-cap h (fn-rtc-config s))))
           (let* ((n (mv-nth 0 (fn-ovr-quantum cur w h base limit s fn-arena fn-cat)))
                  (room (- (nfix limit) base))
                  (wmax (+ 1 (- (fn-ovw-hi (nfix (nth 1 cur)) (nfix (nth 2 cur)) w) (nfix (nth 1 cur))))))
             (and (implies (and (<= base (nfix limit))
                                (<= (nfix (nth 1 cur)) (nfix (nth 2 cur)))
                                (<= (len (mv-nth 0 (fn-ovw-step cur 1 fn-arena fn-cat))) room))
                           (posp n))
                  (implies (and (posp n) (< n wmax))
                           (< room (len (mv-nth 0 (fn-ovw-step cur (+ 1 n) fn-arena fn-cat))))))))
 :hints (("Goal" :do-not-induct t
 :cases ((< limit base)
         (and (<= base limit) (< (nfix (nth 2 cur)) (nfix (nth 1 cur))))
         (and (<= base limit) (<= (nfix (nth 1 cur)) (nfix (nth 2 cur)))))
 :use (fn-ovrqp-kl4-ready-live fn-ovrqp-live-room
  (:instance fn-ovrp-hi-ge-k (k (nfix (nth 1 cur))) (top (nfix (nth 2 cur))))
  (:instance fn-ovrp-hi-le-top (k (nfix (nth 1 cur))) (top (nfix (nth 2 cur))))
  (:instance fn-ovrp-hi-int (k (nfix (nth 1 cur))) (top (nth 2 cur)))
  (:instance fn-ovrp-ext-step (hh (car (fn-ovrqp-fq cur w h base limit s))))
  (:instance fn-ovrp-ext-step (hh (+ -1 (nfix (nth 1 cur)))))
  (:instance fn-ovrqp-fill-max (group (nth 0 cur)) (number (nfix (nth 1 cur)))
   (last (fn-ovw-hi (nfix (nth 1 cur)) (nfix (nth 2 cur)) w)) (top (nfix (nth 2 cur)))
   (owedp (nth 5 cur)) (legacyp (nth 4 cur)) (room (min limit (fn-rtc-buf-cap h (fn-rtc-config s))))
   (server (nth 6 cur)) (v (nfix (nth 3 cur))) (j base) (st s)
   (hi (car (fn-ovrqp-fq cur w h base limit s)))))
 :in-theory (union-theories
 '(fn-ovrqp-live-properties fn-ovrqp-quantum-closed fn-ovrqp-quantum-parts fn-ovrqp-quantum-empty-parts
 fn-ovrqp-fill-hi-car-type fn-ovrqp-fill-hi-car-lower fn-ovrqp-fill-hi-car-upper
 fn-ovrp-hi-type fn-ovrp-hi-linear fn-ovrp-hi-natp fn-ovrp-hi-bounds fn-ovrp-hi-top-lt
 fn-ovw-cursorp fn-ovrp-body-empty fn-ovrp-owed-empty
 fn-ovrqp-nfix-natural fn-ovrqp-natural-nfix fn-ovrqp-buf-cap-natural
 min unsigned-byte-p integer-range-p natp-compound-recognizer fix
 fn-ovrqp-fold-sums inverse-of-+ associativity-of-+ commutativity-of-+ commutativity-2-of-+
 unicity-of-0 default-+-1 default-+-2

 mv-nth zp posp car-cons cdr-cons len (:type-prescription len)
 (:type-prescription fn-ovr-quantum) (:type-prescription fn-ovr-fill) (:type-prescription fn-ovw-step))
 (set-difference-theories (fn-dss-measure-theory) '(natp nfix)))))))

(local (set-default-hints '((quote (:use fn-ovrqp-kl4 :in-theory (theory 'minimal-theory))))))
(defthm fn-ovr-quantum-is-the-largest-that-fits
  (implies (and (fn-ovw-cursorp cur) (consp cur) (not (nth 7 cur)) (fn-cbor-octet-listp (nth 6 cur))
                (natp base) (unsigned-byte-p 59 limit)
                (fn-rtc-st$ap s) (fn-hl-render-ready-p h id inc s)
                (<= base (len (fn-rtc-b-bytes (fn-rtc-buffer h s))))
                (<= (nfix limit) (fn-rtc-buf-cap h (fn-rtc-config s))))
           (let* ((n (mv-nth 0 (fn-ovr-quantum cur w h base limit s fn-arena fn-cat)))
                  (room (- (nfix limit) base))
                  (wmax (+ 1 (- (fn-ovw-hi (nfix (nth 1 cur)) (nfix (nth 2 cur)) w) (nfix (nth 1 cur))))))
             (and (implies (and (<= base (nfix limit))
                                (<= (nfix (nth 1 cur)) (nfix (nth 2 cur)))
                                (<= (len (mv-nth 0 (fn-ovw-step cur 1 fn-arena fn-cat))) room))
                           (posp n))
                  (implies (and (posp n) (< n wmax))
                           (< room (len (mv-nth 0 (fn-ovw-step cur (+ 1 n) fn-arena fn-cat)))))))))
(local (set-default-hints nil))

; A taken window satisfies the contract's splice admission premise.


; The same probe budget guarantees a taken window and survives its cursor.
(local
 (defthm fn-ovrp-pw-first
   (implies (and (natp k) (<= k (nfix top))
                 (fn-ovr-probes-within group k top server v l fn-arena fn-cat))
            (<= (fn-ovr-probe-len group k server v fn-arena fn-cat) (nfix l)))
   :rule-classes nil
   :hints (("Goal" :expand ((fn-ovr-probes-within group k top server v l fn-arena fn-cat))))))

(local
 (defthm fn-ovrp-close-bound
   (<= (len (fn-ovr-close-octets ow lp))
       (max (len (fn-ovr-close-octets t t)) (max (len (fn-ovr-close-octets t nil)) 3)))
   :hints (("Goal" :in-theory (enable fn-ovr-close-octets fn-ovw-empty-text)
            :cases (ow lp)))))

(local
 (defthm fn-ovrp-ext-bound
   (<= (fn-ovrp-ext group j top ow lp server v fn-arena fn-cat)
       (+ (len (fn-ovr-probe-octets group j server v fn-arena fn-cat))
          (fn-ovr-frame-max)))
   :hints (("Goal" :in-theory (e/d (fn-ovrp-ext fn-ovr-frame-max) (fn-ovr-close-octets))
            :use (:instance fn-ovrp-close-bound (ow (and ow (not (consp (fn-ovr-probe-octets group j server v fn-arena fn-cat))))))))))

(local
 (defthm fn-ovrp-step1-len
   (implies (and (consp cur) (not (nth 7 cur)) (natp (nth 3 cur))
                 (<= (nfix (nth 1 cur)) (nfix (nth 2 cur))))
            (<= (len (mv-nth 0 (fn-ovw-step cur 1 fn-arena fn-cat)))
                (+ (len (fn-ovr-probe-octets (nth 0 cur) (nfix (nth 1 cur)) (nth 6 cur) (nth 3 cur)
                                             fn-arena fn-cat))
                   (fn-ovr-frame-max))))
   :hints (("Goal" :in-theory (disable fn-ovrp-ext-step fn-ovrp-ext-bound fn-ovw-step fn-ovw-hi
                                       fn-ovrp-ext fn-ovr-frame-max)
            :use ((:instance fn-ovrp-ext-step (hh (+ -1 (nfix (nth 1 cur)))) (w 1))
                  (:instance fn-ovrp-ext-bound (group (nth 0 cur)) (j (nfix (nth 1 cur)))
                             (top (nfix (nth 2 cur)))
                             (ow (fn-ovrp-owed (nth 0 cur) (nfix (nth 1 cur)) (+ -1 (nfix (nth 1 cur)))
                                               (nth 5 cur) (nth 6 cur) (nth 3 cur) fn-arena fn-cat))
                             (lp (nth 4 cur)) (server (nth 6 cur)) (v (nth 3 cur)))
                  (:instance fn-ovrp-body-empty (j (nfix (nth 1 cur))) (hi (+ -1 (nfix (nth 1 cur))))
                             (group (nth 0 cur)) (owedp (nth 5 cur)) (server (nth 6 cur)) (v (nth 3 cur)))
                  (:instance fn-ovrp-hi-ge-k (k (nfix (nth 1 cur))) (top (nfix (nth 2 cur))) (w 1))
                  (:instance fn-ovrp-hi-le-top (k (nfix (nth 1 cur))) (top (nfix (nth 2 cur))) (w 1)))
            :expand ((fn-ovw-hi (nfix (nth 1 cur)) (nfix (nth 2 cur)) 1))))))

(local
 (defthm fn-ovrp-probe-len-le
   (implies (and (natp (nth 3 cur)) (natp k) (<= k (nfix top))
                 (fn-ovr-probes-within g k top s (nth 3 cur) l fn-arena fn-cat))
            (<= (len (fn-ovr-probe-octets g k s (nth 3 cur) fn-arena fn-cat)) (nfix l)))
   :hints (("Goal" :use (fn-ovrp-pw-first
                         (:instance fn-ovr-probe-len-is-the-length (group g) (j k) (server s) (v (nth 3 cur))))
            :in-theory (disable fn-ovr-probe-len-is-the-length)))))

(local (defthm fn-ovrp-pw-mono
   (implies (and (natp k) (natp k2) (<= k k2)
                 (fn-ovr-probes-within group k top server v l fn-arena fn-cat))
            (fn-ovr-probes-within group k2 top server v l fn-arena fn-cat))
   :hints (("Goal" :induct (fn-ovr-probes-within group k top server v l fn-arena fn-cat)
            :in-theory (disable fn-ovr-probe-len-is-the-length))
           ("Subgoal *1/2" :expand ((fn-ovr-probes-within group k top server v l fn-arena fn-cat)))
           ("Subgoal *1/1" :expand ((fn-ovr-probes-within group k2 top server v l fn-arena fn-cat))))))

(local (defthm fn-ovrp-step-b
   (implies (and (consp cur) (not (nth 7 cur)) (natp (nth 3 cur))
                 (< (nfix (nth 2 cur)) (nfix (nth 1 cur))))
            (and (equal (mv-nth 0 (fn-ovw-step cur n fn-arena fn-cat))
                        (fn-ovr-close-octets (nth 5 cur) (nth 4 cur)))
                 (equal (mv-nth 1 (fn-ovw-step cur n fn-arena fn-cat)) nil)))
   :hints (("Goal" :in-theory (e/d (fn-ovw-step fn-ovr-close-octets fn-ovw-hi)
                                   (fn-ovw-hdr-step fn-ovw-lines fn-nntp-stuff-lines fn-ovw-status))
            :use ((:instance fn-ovrp-lines-empty-above (group (nth 0 cur)) (k (nfix (nth 1 cur)))
                             (hi (nfix (nth 2 cur))) (server (nth 6 cur)) (v (nth 3 cur))))))))

(local (defthm fn-ovrp-step-next-live
   (implies (and (not (nth 7 cur)) (mv-nth 1 (fn-ovw-step cur n fn-arena fn-cat)))
            (not (nth 7 (mv-nth 1 (fn-ovw-step cur n fn-arena fn-cat)))))
   :hints (("Goal" :in-theory (e/d (fn-ovw-step fn-ovw-cursor)
                                   (fn-ovw-hdr-step fn-ovw-lines fn-nntp-stuff-lines fn-ovw-status))))))

(local (defthm fn-ovrp-nx
   (implies (and (fn-ovw-cursorp cur) (consp cur) (not (nth 7 cur))
                 (<= (nfix (nth 1 cur)) (nfix (nth 2 cur)))
                 (mv-nth 1 (fn-ovw-step cur n fn-arena fn-cat)))
            (let ((nx (mv-nth 1 (fn-ovw-step cur n fn-arena fn-cat))))
              (and (fn-ovw-cursorp nx) (not (nth 7 nx))
                   (equal (nth 6 nx) (nth 6 cur))
                   (equal (nth 0 nx) (nth 0 cur))
                   (equal (nfix (nth 3 nx)) (nfix (nth 3 cur)))
                   (equal (nfix (nth 2 nx)) (nfix (nth 2 cur)))
                   (<= (nfix (nth 1 cur)) (nfix (nth 1 nx))))))
   :hints (("Goal" :in-theory (union-theories '(fn-ovw-cursor fn-ovw-cursorp natp nfix nth zp car-cons cdr-cons
 fn-ovrqp-nfix-natural fn-ovrqp-natural-nfix fn-ovrp-hi-type fn-ovrp-hi-linear
 fn-ovrp-hi-natp fn-ovrp-hi-bounds fn-ovrqp-fold-sums
 mv-nth (:type-prescription fn-ovw-step) (:executable-counterpart nfix)
 (:executable-counterpart natp) (:executable-counterpart nth) (:executable-counterpart zp)
 (:executable-counterpart binary-+) (:executable-counterpart unary--))
 (fn-dss-measure-theory))
            :use (fn-ovrp-step-next fn-ovw-step-keeps-cursorp fn-ovrp-step-next-live
                  (:instance fn-ovrp-hi-ge-k (k (nfix (nth 1 cur))) (top (nfix (nth 2 cur))) (w n))
                  (:instance fn-ovrp-hi-int (k (nfix (nth 1 cur))) (top (nth 2 cur)) (w n)))))))

(defthm fn-ovr-quantum-progress-under-probes
 (implies (and (fn-rtc-st$ap s) (fn-hl-render-ready-p h id inc s)
 (fn-ovw-cursorp cur) (consp cur) (not (nth 7 cur)) (fn-cbor-octet-listp (nth 6 cur))
 (unsigned-byte-p 59 (fn-rtc-buf-cap h (fn-rtc-config s)))
 (fn-ovr-probes-within (nth 0 cur) (nfix (nth 1 cur)) (nfix (nth 2 cur)) (nth 6 cur)
  (nfix (nth 3 cur)) l fn-arena fn-cat)
 (<= (+ (nfix l) (fn-ovr-frame-max)) (fn-rtc-buf-cap h (fn-rtc-config s))))
 (posp (mv-nth 0 (fn-ovr-quantum cur w h 0 (fn-rtc-buf-cap h (fn-rtc-config s)) s fn-arena fn-cat))))
 :hints (("Goal" :do-not-induct t
 :cases ((<= (nfix (nth 1 cur)) (nfix (nth 2 cur))))
 :use ((:instance fn-ovr-quantum-is-the-largest-that-fits (base 0) (limit (fn-rtc-buf-cap h (fn-rtc-config s))))
 (:instance fn-ovrqp-kl4-ready-live (base 0) (limit (fn-rtc-buf-cap h (fn-rtc-config s))))
 (:instance fn-ovrqp-quantum-empty-parts (base 0) (limit (fn-rtc-buf-cap h (fn-rtc-config s))))
 fn-ovrp-step1-len
 (:instance fn-ovrp-probe-len-le (g (nth 0 cur)) (k (nfix (nth 1 cur)))
  (top (nfix (nth 2 cur))) (s (nth 6 cur)))
 (:instance fn-ovrp-close-bound (ow (nth 5 cur)) (lp (nth 4 cur))))
 :in-theory (union-theories '(fn-ovw-cursorp fn-ovrqp-nfix-natural fn-ovrqp-natural-nfix
 fn-ovrqp-buf-cap-natural fn-ovrqp-live-properties fn-ovr-frame-max
 natp-compound-recognizer min max posp mv-nth zp car-cons cdr-cons
 fix unicity-of-0 associativity-of-+ commutativity-of-+ commutativity-2-of-+ inverse-of-+
 fn-ovrqp-fold-sums default-+-1 default-+-2
 (:type-prescription len) (:type-prescription fn-ovr-quantum)
 (:executable-counterpart natp) (:executable-counterpart nfix)
 (:executable-counterpart fn-ovr-close-octets) (:executable-counterpart fn-ovr-status-octets))
 (set-difference-theories (fn-dss-measure-theory) '(natp nfix))))))

(defthm fn-ovr-step-keeps-probe-bound
   (implies (and (fn-ovw-cursorp cur) (consp cur) (not (nth 7 cur))
                 (fn-cbor-octet-listp (nth 6 cur))
                 (fn-ovr-probes-within (nth 0 cur) (nfix (nth 1 cur)) (nfix (nth 2 cur)) (nth 6 cur)
                                       (nfix (nth 3 cur)) l fn-arena fn-cat)
                 (mv-nth 1 (fn-ovw-step cur n fn-arena fn-cat)))
            (let ((nx (mv-nth 1 (fn-ovw-step cur n fn-arena fn-cat))))
              (and (fn-ovw-cursorp nx) (not (nth 7 nx))
                   (fn-cbor-octet-listp (nth 6 nx))
                   (fn-ovr-probes-within (nth 0 nx) (nfix (nth 1 nx)) (nfix (nth 2 nx)) (nth 6 nx)
                                         (nfix (nth 3 nx)) l fn-arena fn-cat))))
   :hints (("Goal" :cases ((<= (nfix (nth 1 cur)) (nfix (nth 2 cur))))
            :in-theory (union-theories '(fn-ovrqp-nfix-natural fn-ovrqp-natural-nfix fn-ovw-cursorp
 natp-compound-recognizer mv-nth zp car-cons cdr-cons
 (:type-prescription fn-ovw-step)) (set-difference-theories (fn-dss-measure-theory) '(natp nfix))))
           ("Subgoal 2" :use (:instance fn-ovrp-step-b))
           ("Subgoal 1" :use (fn-ovrp-nx
                              (:instance fn-ovrp-pw-mono (group (nth 0 cur)) (k (nfix (nth 1 cur)))
                                         (k2 (nfix (nth 1 (mv-nth 1 (fn-ovw-step cur n fn-arena fn-cat)))))
                                         (top (nfix (nth 2 cur))) (server (nth 6 cur)) (v (nfix (nth 3 cur))))))))
