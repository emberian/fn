;; over-render-quantum.lisp -- OVER's quantum and run over the lease renderer (Builder O, row O1,
;; landing 1, 2026-10-10).  The definitions are books/over-render.lisp's statement draft 6;
;; KO2-KO7 are proved here, in a world without arithmetic-5 (the renderer book includes it
;; locally), helpers local with prefix fn-ovrp-.
;;
;;   KO2  fn-ovr-quantum-is-the-step               a quantum is fn-ovw-step's window of N
;;   KO3  fn-ovr-quantum-within-the-lease          never more than CAP
;;   KO4  fn-ovr-quantum-window-at-most-w          never more than W numbers
;;   KO5  fn-ovr-quantum-is-the-largest-that-fits  N is the largest window that fits
;;   KO6  fn-ovr-run-is-the-windowed-reply         the quanta are the windowed reply
;;   KO7  fn-ovr-run-progresses                    every probe within L, CAP >= L + framing

(in-package "ACL2")
(include-book "over-render")

; The two framing texts of a window.
(defun fn-ovr-status-octets ()
  (declare (xargs :guard t))
  (fn-ovw-status (fn-proto-text * :overview)))
(defun fn-ovr-close-octets (owed2 legacyp)
  (declare (xargs :guard t))
  (if owed2 (fn-ovw-status (fn-ovw-empty-text legacyp)) '(46 13 10)))

;; One pass over the probes J..LAST: each probe's length is read, and the probe is
;; written (after the status, while owed) only when the window through it, closed if
;; J is the range's last number, fits ROOM.  (mv HI OWED LEASE'): HI the last number
;; written (J-1 when none), OWED the status still owed.
(defun fn-ovr-fill (group j last top owedp legacyp room server v fn-ovr-lease fn-arena fn-cat)
  (declare (xargs :stobjs (fn-ovr-lease fn-arena fn-cat) :verify-guards nil
                  :measure (nfix (- (+ 1 (nfix last)) (nfix j)))))
  (if (and (natp j) (<= j (nfix last)))
      (let* ((p (fn-ovr-probe-len group j server v fn-arena fn-cat))
             (s (if (and owedp (posp p)) (len (fn-ovr-status-octets)) 0))
             (owed2 (and owedp (zp p)))
             (close (if (<= (nfix top) j) (len (fn-ovr-close-octets owed2 legacyp)) 0)))
        (if (<= (+ (fn-ovr-lease-len fn-ovr-lease) s p close) (nfix room))
            (let* ((fn-ovr-lease (if (posp s)
                                     (fn-ovr-lease-append-list (fn-ovr-status-octets) fn-ovr-lease)
                                   fn-ovr-lease))
                   (fn-ovr-lease (fn-ovr-put-probe group j server v fn-ovr-lease fn-arena fn-cat)))
              (fn-ovr-fill group (+ 1 j) last top owed2 legacyp room server v fn-ovr-lease fn-arena fn-cat))
          (mv (- j 1) owedp fn-ovr-lease)))
    (mv (- (nfix j) 1) owedp fn-ovr-lease)))

; ONE QUANTUM.  (mv N NEXT LEASE'): N numbers taken (0: not even one number's window
; fits the lease's remaining room under CAP; nothing written, the cursor unchanged),
; NEXT the cursor after them (nil when the range is exhausted), LEASE' the lease with
; the window's octets appended.  A header cursor (nth 7) is not this landing's: N = 0.
; A server name that is not an octet list cannot be written into an octet lease: N = 0
; (the served arm's server is fn-xref-serverp or nil, fn-nntp-xref-server-is-a-server).
(defun fn-ovr-quantum (cur w cap fn-ovr-lease fn-arena fn-cat)
  (declare (xargs :stobjs (fn-ovr-lease fn-arena fn-cat) :verify-guards nil))
  (if (or (not (consp cur)) (nth 7 cur) (not (fn-cbor-octet-listp (nth 6 cur)))
          (not (unsigned-byte-p 59 cap)) (< cap (fn-ovr-lease-len fn-ovr-lease)))
      (mv 0 cur fn-ovr-lease)
    (let* ((group (nth 0 cur)) (k (nfix (nth 1 cur))) (top (nfix (nth 2 cur)))
           (v (nfix (nth 3 cur))) (legacyp (nth 4 cur)) (owedp (nth 5 cur)) (server (nth 6 cur)))
      (mv-let (hi owed2 fn-ovr-lease)
        (fn-ovr-fill group k (fn-ovw-hi k top w) top owedp legacyp cap server v fn-ovr-lease fn-arena fn-cat)
        (if (or (and (< hi k) (<= k top))
                ;; an empty range (K past TOP: OVER 5-3, or a low bound past the group's last
                ;; article) is one window of no number that writes only the close, when it fits
                (and (< top k)
                     (< cap (+ (fn-ovr-lease-len fn-ovr-lease)
                               (len (fn-ovr-close-octets owed2 legacyp))))))
            (mv 0 cur fn-ovr-lease)
          (let* ((donep (<= top hi))
                 (fn-ovr-lease (if donep
                                   (fn-ovr-lease-append-list (fn-ovr-close-octets owed2 legacyp)
                                                             fn-ovr-lease)
                                 fn-ovr-lease)))
            (mv (max 1 (+ 1 (- hi k)))
                (if donep nil (fn-ovw-cursor group (+ 1 hi) top v legacyp owed2 server))
                fn-ovr-lease)))))))

; The run: quanta into the lease, cleared before each, until the cursor is nil;
; OKP nil when a quantum takes no number.
(defun fn-ovr-run (cur w cap fn-ovr-lease fn-arena fn-cat)
  (declare (xargs :stobjs (fn-ovr-lease fn-arena fn-cat) :verify-guards nil
                  :measure (fn-ovw-remaining cur)
                  :hints (("Goal" :in-theory (disable fn-ovr-quantum)))))
  (if (consp cur)
      (let ((fn-ovr-lease (fn-ovr-lease-clear fn-ovr-lease)))
        (mv-let (n next fn-ovr-lease) (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat)
          (cond ((not (posp n)) (mv nil nil fn-ovr-lease))
                ((null next) (mv t (fn-ovr-lease-list fn-ovr-lease) fn-ovr-lease))
                ((< (fn-ovw-remaining next) (fn-ovw-remaining cur))
                 (let ((octets (fn-ovr-lease-list fn-ovr-lease)))
                   (mv-let (okp rest fn-ovr-lease) (fn-ovr-run next w cap fn-ovr-lease fn-arena fn-cat)
                     (mv okp (append octets rest) fn-ovr-lease))))
                (t (mv nil nil fn-ovr-lease)))))
    (mv t nil fn-ovr-lease)))

; Every probe of K..TOP renders within L octets.
(defun fn-ovr-probes-within (group k top server v l fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil
                  :measure (nfix (- (+ 1 (nfix top)) (nfix k)))))
  (if (and (natp k) (<= k (nfix top)))
      (and (<= (fn-ovr-probe-len group k server v fn-arena fn-cat) (nfix l))
           (fn-ovr-probes-within group (+ 1 k) top server v l fn-arena fn-cat))
    t))

; The framing a window may add beyond its lines: the status and the longer close.
(defun fn-ovr-frame-max ()
  (declare (xargs :guard t))
  (+ (len (fn-ovr-status-octets))
     (max (len (fn-ovr-close-octets t t)) (max (len (fn-ovr-close-octets t nil)) 3))))


;; ===========================================================================
;; KO2-KO7 (the quantum and the run).  Helpers local, prefix fn-ovrp-.
;; KO2-KO7 proofs over statements.lisp draft 6; load after the definitions and KO1/KO1b.

;;; ---- p1
(in-theory (disable fn-ovr-probe-len fn-ovr-put-probe fn-ovr-probe-octets))

; The world KO2-KO7 were proved in: over-window's own forms loaded at the top level, so its
; LOCAL facts about fn-ovw-hi (books/over-window.lisp:289-313: the type, the bounds as :linear,
; hi at top, and fn-ovw-hi disabled) were live.  Included as a book those are dropped, fn-ovw-hi
; opens inside fn-ovw-step, and fn-ovw-lines-split (free variable HI) loops in the case split.
; The same facts, local here.
(local
 (defthm fn-ovrp-hi-type
   (implies (natp top) (natp (fn-ovw-hi k top w)))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-ovw-hi)))))

(local
 (defthm fn-ovrp-hi-linear
   (implies (and (natp k) (natp top) (<= k top))
            (and (<= k (fn-ovw-hi k top w))
                 (<= (fn-ovw-hi k top w) top)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-ovw-hi)))))

(local
 (defthm fn-ovrp-hi-at-top
   (implies (and (natp k) (natp top) (<= top (fn-ovw-hi k top w)))
            (equal (fn-ovw-hi k top w) top))
   :hints (("Goal" :in-theory (enable fn-ovw-hi)))))

(local (in-theory (disable fn-ovw-hi)))

(local
 (defthm fn-ovrp-stuff-consp
   (equal (consp (fn-nntp-stuff-lines x)) (consp x))
   :hints (("Goal" :in-theory (enable fn-nntp-stuff-lines fn-nntp-crlf)))))

(local
 (defthm fn-ovrp-lines-empty-above
   (implies (and (natp k) (natp hi) (< hi k))
            (equal (fn-ovw-lines group k hi server v fn-arena fn-cat) nil))
   :hints (("Goal" :in-theory (enable fn-ovw-lines)))))

(local
 (defthm fn-ovrp-append-list
   (equal (fn-ovr-lease-append-list xs l) (append l xs))))

(local
 (defthm fn-ovrp-len-pos
   (and (equal (posp (len x)) (consp x))
        (equal (zp (len x)) (not (consp x))))
   :hints (("Goal" :in-theory (enable posp)))))

(local
 (defthm fn-ovrp-consp-append
   (equal (consp (append a b)) (if (consp a) t (consp b)))))

(local
 (defthm fn-ovrp-append-iff
   (iff (append a b) (if (consp a) t b))))

; The lines of J..HI, nil when the range is empty (HI may be J-1, even -1).
(local
 (defun fn-ovrp-win (group j hi server v fn-arena fn-cat)
   (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
   (if (<= j hi) (fn-ovw-lines group j hi server v fn-arena fn-cat) nil)))

(local (in-theory (disable (:definition fn-ovrp-win))))

(local
 (defthm fn-ovrp-win-empty
   (implies (< hi j)
            (equal (fn-ovrp-win group j hi server v fn-arena fn-cat) nil))
   :hints (("Goal" :in-theory (enable fn-ovrp-win)))))

(local
 (defthm fn-ovrp-win-extend
   (implies (and (natp j) (integerp hi) (<= (- j 1) hi))
            (equal (fn-ovrp-win group j (+ 1 hi) server v fn-arena fn-cat)
                   (append (fn-ovrp-win group j hi server v fn-arena fn-cat)
                           (fn-ovrp-win group (+ 1 hi) (+ 1 hi) server v fn-arena fn-cat))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-ovrp-win) (fn-ovw-lines-split))
            :cases ((<= j hi))
            :use ((:instance fn-ovw-lines-split (k j) (top (+ 1 hi)) (hi hi)))))))

(local
 (defthm fn-ovrp-win-cons
   (implies (and (natp j) (integerp hi) (< j hi))
            (equal (fn-ovrp-win group j hi server v fn-arena fn-cat)
                   (append (fn-ovrp-win group j j server v fn-arena fn-cat)
                           (fn-ovrp-win group (+ 1 j) hi server v fn-arena fn-cat))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-ovrp-win) (fn-ovw-lines-split))
            :use ((:instance fn-ovw-lines-split (k j) (top hi) (hi j)))))))

(local
 (defthm fn-ovrp-probe-is-win
   (implies (natp j)
            (equal (fn-ovr-probe-octets group j server v fn-arena fn-cat)
                   (fn-nntp-stuff-lines (fn-ovrp-win group j j server v fn-arena fn-cat))))
   :hints (("Goal" :in-theory (enable fn-ovr-probe-octets fn-ovrp-win)))))

(local
 (defun fn-ovrp-body (group j hi owedp server v fn-arena fn-cat)
   (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil
                   :measure (nfix (- (+ 1 (ifix hi)) (nfix j)))))
   (if (and (natp j) (integerp hi) (<= j hi))
       (let ((pl (fn-ovr-probe-octets group j server v fn-arena fn-cat)))
         (append (if (and owedp (consp pl)) (fn-ovr-status-octets) nil)
                 pl
                 (fn-ovrp-body group (+ 1 j) hi (and owedp (not (consp pl))) server v fn-arena fn-cat)))
     nil)))

(local
 (defthm fn-ovrp-body-empty
   (implies (< hi j)
            (equal (fn-ovrp-body group j hi owedp server v fn-arena fn-cat) nil))))

(local
 (defun fn-ovrp-owed (group j hi owedp server v fn-arena fn-cat)
   (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil
                   :measure (nfix (- (+ 1 (ifix hi)) (nfix j)))))
   (if (and (natp j) (integerp hi) (<= j hi))
       (let ((pl (fn-ovr-probe-octets group j server v fn-arena fn-cat)))
         (fn-ovrp-owed group (+ 1 j) hi (and owedp (not (consp pl))) server v fn-arena fn-cat))
     owedp)))

(local
 (defthm fn-ovrp-owed-empty
   (implies (< hi j)
            (equal (fn-ovrp-owed group j hi owedp server v fn-arena fn-cat) owedp))))

; the body is the window: the status when owed and some line, the stuffed lines.
(local
 (defthm fn-ovrp-body-is-window
   (implies (and (natp j) (integerp hi))
            (equal (fn-ovrp-body group j hi owedp server v fn-arena fn-cat)
                   (append (if (and owedp (consp (fn-ovrp-win group j hi server v fn-arena fn-cat)))
                               (fn-ovr-status-octets) nil)
                           (fn-nntp-stuff-lines (fn-ovrp-win group j hi server v fn-arena fn-cat)))))
   :rule-classes nil
   :hints (("Goal" :induct (fn-ovrp-body group j hi owedp server v fn-arena fn-cat))
           ("Subgoal *1/1'" :use fn-ovrp-win-cons))))

(local
 (defthm fn-ovrp-owed-is-window
   (implies (and (natp j) (integerp hi))
            (equal (fn-ovrp-owed group j hi owedp server v fn-arena fn-cat)
                   (if (<= j hi)
                       (and owedp (not (consp (fn-ovrp-win group j hi server v fn-arena fn-cat))))
                     owedp)))
   :rule-classes nil
   :hints (("Goal" :induct (fn-ovrp-owed group j hi owedp server v fn-arena fn-cat))
           ("Subgoal *1/1'" :use fn-ovrp-win-cons))))

(local
 (defthm fn-ovrp-body-snoc
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

;;; ---- p2
(local
 (defthm fn-ovrp-fill-open
   (implies (and (natp j) (<= j (nfix last)) (syntaxp (or (symbolp j) (quotep j))))
            (equal (fn-ovr-fill group j last top owedp legacyp room server v fn-ovr-lease fn-arena fn-cat)
                   (let* ((p (fn-ovr-probe-len group j server v fn-arena fn-cat))
                          (s (if (and owedp (posp p)) (len (fn-ovr-status-octets)) 0))
                          (owed2 (and owedp (zp p)))
                          (close (if (<= (nfix top) j) (len (fn-ovr-close-octets owed2 legacyp)) 0)))
                     (if (<= (+ (fn-ovr-lease-len fn-ovr-lease) s p close) (nfix room))
                         (let* ((fn-ovr-lease (if (posp s)
                                                  (fn-ovr-lease-append-list (fn-ovr-status-octets) fn-ovr-lease)
                                                fn-ovr-lease))
                                (fn-ovr-lease (fn-ovr-put-probe group j server v fn-ovr-lease fn-arena fn-cat)))
                           (fn-ovr-fill group (+ 1 j) last top owed2 legacyp room server v fn-ovr-lease fn-arena fn-cat))
                       (mv (- j 1) owedp fn-ovr-lease)))))
   :hints (("Goal" :do-not-induct t :use ((:definition fn-ovr-fill))
            :in-theory (disable fn-ovr-fill fn-ovr-probe-len-is-the-length
                                fn-ovr-put-probe-is-the-served-octets)))))

(local
 (defthm fn-ovrp-fill-done
   (implies (not (and (natp j) (<= j (nfix last))))
            (equal (fn-ovr-fill group j last top owedp legacyp room server v fn-ovr-lease fn-arena fn-cat)
                   (list (- (nfix j) 1) owedp fn-ovr-lease)))
   :hints (("Goal" :do-not-induct t :use ((:definition fn-ovr-fill))
            :in-theory (disable fn-ovr-fill fn-ovrp-fill-open)))))

(local (in-theory (disable (:definition fn-ovr-fill))))

(local
 (defthm fn-ovrp-fill-hi
   (implies (natp j)
            (let ((hi (car (fn-ovr-fill group j last top owedp legacyp room server v
                                             fn-ovr-lease fn-arena fn-cat))))
              (and (integerp hi)
                   (<= (- j 1) hi)
                   (implies (<= j (nfix last)) (<= hi (nfix last)))
                   (implies (< (nfix last) j) (equal hi (- j 1))))))
   :rule-classes nil
   :hints (("Goal" :induct (fn-ovr-fill group j last top owedp legacyp room server v
                                         fn-ovr-lease fn-arena fn-cat)))))

(local
 (defthm fn-ovrp-fill-consp
   (and (consp (fn-ovr-fill group j last top owedp legacyp room server v fn-ovr-lease fn-arena fn-cat))
        (consp (cdr (fn-ovr-fill group j last top owedp legacyp room server v fn-ovr-lease fn-arena fn-cat)))
        (consp (cdr (cdr (fn-ovr-fill group j last top owedp legacyp room server v fn-ovr-lease fn-arena fn-cat)))))
   :hints (("Goal" :induct (fn-ovr-fill group j last top owedp legacyp room server v
                                        fn-ovr-lease fn-arena fn-cat)))))

(local
 (defthm fn-ovrp-fill-hi-lower
   (implies (natp j)
            (<= (- j 1) (car (fn-ovr-fill group j last top owedp legacyp room server v
                                               fn-ovr-lease fn-arena fn-cat))))
   :rule-classes :linear
   :hints (("Goal" :use fn-ovrp-fill-hi))))

(local
 (defthm fn-ovrp-fill-hi-integerp
   (implies (natp j)
            (integerp (car (fn-ovr-fill group j last top owedp legacyp room server v
                                             fn-ovr-lease fn-arena fn-cat))))
   :hints (("Goal" :use fn-ovrp-fill-hi))))

(local
 (defthm fn-ovrp-fill-hi-upper
   (implies (and (natp j) (<= j (nfix last)))
            (<= (car (fn-ovr-fill group j last top owedp legacyp room server v
                                       fn-ovr-lease fn-arena fn-cat))
                (nfix last)))
   :rule-classes :linear
   :hints (("Goal" :use fn-ovrp-fill-hi))))

(local
 (defthm fn-ovrp-fill-lease
   (implies (and (natp j) (natp v) (true-listp fn-ovr-lease))
            (equal (car (cdr (cdr (fn-ovr-fill group j last top owedp legacyp room server v
                                               fn-ovr-lease fn-arena fn-cat))))
                   (append fn-ovr-lease
                           (fn-ovrp-body group j
                                         (car (fn-ovr-fill group j last top owedp legacyp room server v
                                                           fn-ovr-lease fn-arena fn-cat))
                                         owedp server v fn-arena fn-cat))))
   :hints (("Goal" :induct (fn-ovr-fill group j last top owedp legacyp room server v
                                        fn-ovr-lease fn-arena fn-cat)))))

;;; ---- p3
(local
 (defthm fn-ovrp-len-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthm fn-ovrp-fill-owed
   (implies (and (natp j) (natp v))
            (equal (car (cdr (fn-ovr-fill group j last top owedp legacyp room server v
                                          fn-ovr-lease fn-arena fn-cat)))
                   (fn-ovrp-owed group j
                                 (car (fn-ovr-fill group j last top owedp legacyp room server v
                                                   fn-ovr-lease fn-arena fn-cat))
                                 owedp server v fn-arena fn-cat)))
   :hints (("Goal" :induct (fn-ovr-fill group j last top owedp legacyp room server v
                                        fn-ovr-lease fn-arena fn-cat)))))

(local (in-theory (disable fn-ovrp-body fn-ovrp-owed)))

(local
 (defthm fn-ovrp-body-step
   (implies (and (natp j) (integerp hi) (<= j hi)
                 (syntaxp (or (symbolp j) (quotep j))))
            (equal (fn-ovrp-body group j hi owedp server v fn-arena fn-cat)
                   (let ((pl (fn-ovr-probe-octets group j server v fn-arena fn-cat)))
                     (append (if (and owedp (consp pl)) (fn-ovr-status-octets) nil)
                             pl
                             (fn-ovrp-body group (+ 1 j) hi (and owedp (not (consp pl)))
                                           server v fn-arena fn-cat)))))
   :hints (("Goal" :expand ((fn-ovrp-body group j hi owedp server v fn-arena fn-cat))))))

(local
 (defthm fn-ovrp-owed-step
   (implies (and (natp j) (integerp hi) (<= j hi)
                 (syntaxp (or (symbolp j) (quotep j))))
            (equal (fn-ovrp-owed group j hi owedp server v fn-arena fn-cat)
                   (let ((pl (fn-ovr-probe-octets group j server v fn-arena fn-cat)))
                     (fn-ovrp-owed group (+ 1 j) hi (and owedp (not (consp pl)))
                                   server v fn-arena fn-cat))))
   :hints (("Goal" :expand ((fn-ovrp-owed group j hi owedp server v fn-arena fn-cat))))))


; what the probe J adds to the window: the status (while owed), its octets, and the close
; when J is the range's end.
(local
 (defun fn-ovrp-ext (group j top ow legacyp server v fn-arena fn-cat)
   (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
   (let ((pl (fn-ovr-probe-octets group j server v fn-arena fn-cat)))
     (+ (len pl)
        (if (and ow (consp pl)) (len (fn-ovr-status-octets)) 0)
        (if (<= (nfix top) j)
            (len (fn-ovr-close-octets (and ow (not (consp pl))) legacyp))
          0)))))

(local (in-theory (disable (:definition fn-ovrp-ext))))

; the window J..HI and the close (when HI is the end) fit.
(local
 (defthm fn-ovrp-fill-fit
   (implies (and (natp j) (natp v) (true-listp fn-ovr-lease)
                 (<= (nfix last) (nfix top))
                 (equal hi (car (fn-ovr-fill group j last top owedp legacyp room server v
                                             fn-ovr-lease fn-arena fn-cat)))
                 (<= j hi))
            (<= (+ (len fn-ovr-lease)
                   (len (fn-ovrp-body group j hi owedp server v fn-arena fn-cat))
                   (if (<= (nfix top) hi)
                       (len (fn-ovr-close-octets
                             (fn-ovrp-owed group j hi owedp server v fn-arena fn-cat)
                             legacyp))
                     0))
                (nfix room)))
   :hints (("Goal" :induct (fn-ovr-fill group j last top owedp legacyp room server v
                                        fn-ovr-lease fn-arena fn-cat))
)))

;;; ---- p4
; the stop: the window J..HI and the next probe's octets do not fit.
(local
 (defthm fn-ovrp-fill-max
   (implies (and (natp j) (natp v) (true-listp fn-ovr-lease)
                 (<= j (nfix last))
                 (<= (nfix last) (nfix top))
                 (equal hi (car (fn-ovr-fill group j last top owedp legacyp room server v
                                             fn-ovr-lease fn-arena fn-cat)))
                 (< hi (nfix last)))
            (< (nfix room)
               (+ (len fn-ovr-lease)
                  (len (fn-ovrp-body group j hi owedp server v fn-arena fn-cat))
                  (fn-ovrp-ext group (+ 1 hi) top
                               (fn-ovrp-owed group j hi owedp server v fn-arena fn-cat)
                               legacyp server v fn-arena fn-cat))))
   :hints (("Goal" :induct (fn-ovr-fill group j last top owedp legacyp room server v
                                        fn-ovr-lease fn-arena fn-cat))
           ("Subgoal *1/2" :in-theory (enable fn-ovrp-ext)))))

;;; ---- p5
(local
 (defthm fn-ovrp-win-is-lines
   (implies (and (natp j) (natp hi))
            (equal (fn-ovrp-win group j hi server v fn-arena fn-cat)
                   (fn-ovw-lines group j hi server v fn-arena fn-cat)))
   :hints (("Goal" :in-theory (enable fn-ovrp-win)))))

(local
 (defthm fn-ovrp-hi-natp
   (implies (natp top) (natp (fn-ovw-hi k top w)))
   :hints (("Goal" :in-theory (enable fn-ovw-hi)))))

(local
 (defthm fn-ovrp-hi-bounds
   (implies (and (natp k) (natp top) (<= k top))
            (and (<= k (fn-ovw-hi k top w))
                 (<= (fn-ovw-hi k top w) top)))
   :hints (("Goal" :in-theory (enable fn-ovw-hi)))))

; fn-ovw-step on a live (non-header) cursor: the body of the window and the close.
(local
 (defthm fn-ovrp-step-octets
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
   :hints (("Goal" :in-theory (e/d (fn-ovw-step fn-ovr-close-octets) (fn-ovrp-body-step fn-ovrp-owed-step))
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

(local
 (defthm fn-ovrp-step-next
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
   :hints (("Goal" :in-theory (e/d (fn-ovw-step) (fn-ovrp-body-step fn-ovrp-owed-step))
            :use ((:instance fn-ovrp-owed-is-window (j (nfix (nth 1 cur)))
                             (hi (fn-ovw-hi (nfix (nth 1 cur)) (nfix (nth 2 cur)) n))
                             (group (nth 0 cur)) (owedp (nth 5 cur)) (server (nth 6 cur)) (v (nth 3 cur)))
                  (:instance fn-ovrp-win-is-lines (j (nfix (nth 1 cur)))
                             (hi (fn-ovw-hi (nfix (nth 1 cur)) (nfix (nth 2 cur)) n))
                             (group (nth 0 cur)) (server (nth 6 cur)) (v (nth 3 cur)))
                  (:instance fn-ovrp-hi-natp (k (nfix (nth 1 cur))) (top (nfix (nth 2 cur))) (w n))
                  (:instance fn-ovrp-hi-bounds (k (nfix (nth 1 cur))) (top (nfix (nth 2 cur))) (w n)))))))

;;; ---- p6
(local (in-theory (disable fn-ovrp-fill-open fn-ovrp-fill-done)))

(local
 (defthm fn-ovrp-hi-top-lt
   (implies (and (natp k) (natp top) (< top k))
            (equal (fn-ovw-hi k top w) top))
   :hints (("Goal" :in-theory (enable fn-ovw-hi)))))

(local
 (defun fn-ovrp-live (cur cap n)
   (declare (xargs :verify-guards nil))
   (and (consp cur) (not (nth 7 cur)) (fn-cbor-octet-listp (nth 6 cur))
        (unsigned-byte-p 59 cap) (<= n cap))))

(local
 (defthm fn-ovrp-ub59
   (implies (unsigned-byte-p 59 cap)
            (and (natp cap) (equal (nfix cap) cap)))))

(local
 (defthm fn-ovrp-live-facts
   (implies (fn-ovrp-live cur cap n)
            (and (consp cur) (not (nth 7 cur)) (fn-cbor-octet-listp (nth 6 cur))
                 (unsigned-byte-p 59 cap) (<= n cap)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-ovrp-live)))))

(local (in-theory (disable (:definition fn-ovrp-live))))

(local (defthm fn-ovrp-nfix-natp (natp (nfix x))))

(local
 (defmacro fn-ovrp-fq (cur w cap l)
   `(fn-ovr-fill (nth 0 ,cur) (nfix (nth 1 ,cur))
                 (fn-ovw-hi (nfix (nth 1 ,cur)) (nfix (nth 2 ,cur)) ,w)
                 (nfix (nth 2 ,cur)) (nth 5 ,cur) (nth 4 ,cur) ,cap (nth 6 ,cur) (nfix (nth 3 ,cur))
                 ,l fn-arena fn-cat)))

(local
 (defthm fn-ovrp-quantum-open
   (implies (and (fn-ovrp-live cur cap (len fn-ovr-lease))
                 (<= (nfix (nth 1 cur)) (nfix (nth 2 cur))))
            (let ((hi (car (fn-ovrp-fq cur w cap fn-ovr-lease)))
                  (owed2 (car (cdr (fn-ovrp-fq cur w cap fn-ovr-lease))))
                  (l2 (car (cdr (cdr (fn-ovrp-fq cur w cap fn-ovr-lease)))))
                  (k (nfix (nth 1 cur))) (top (nfix (nth 2 cur))))
              (and (equal (mv-nth 0 (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat))
                          (if (< hi k) 0 (+ 1 (- hi k))))
                   (equal (mv-nth 1 (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat))
                          (if (< hi k)
                              cur
                            (if (<= top hi)
                                nil
                              (fn-ovw-cursor (nth 0 cur) (+ 1 hi) top (nfix (nth 3 cur)) (nth 4 cur)
                                             owed2 (nth 6 cur)))))
                   (equal (mv-nth 2 (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat))
                          (if (and (<= k hi) (<= top hi))
                              (append l2 (fn-ovr-close-octets owed2 (nth 4 cur)))
                            l2)))))
   :hints (("Goal" :in-theory (e/d (fn-ovr-quantum fn-ovrp-live) (fn-ovr-close-octets fn-ovrp-fill-owed fn-ovrp-fill-lease))))))

(local
 (defthm fn-ovrp-quantum-open-b
   (implies (and (fn-ovrp-live cur cap (len fn-ovr-lease))
                 (< (nfix (nth 2 cur)) (nfix (nth 1 cur))))
            (let ((zero (< cap (+ (len fn-ovr-lease) (len (fn-ovr-close-octets (nth 5 cur) (nth 4 cur)))))))
              (and (equal (mv-nth 0 (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat))
                          (if zero 0 1))
                   (equal (mv-nth 1 (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat))
                          (if zero cur nil))
                   (equal (mv-nth 2 (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat))
                          (if zero fn-ovr-lease
                            (append fn-ovr-lease (fn-ovr-close-octets (nth 5 cur) (nth 4 cur))))))))
   :hints (("Goal" :in-theory (e/d (fn-ovr-quantum fn-ovrp-live)
                                   (fn-ovr-close-octets fn-ovrp-fill-owed fn-ovrp-fill-lease))
            :use ((:instance fn-ovrp-fill-done (j (nfix (nth 1 cur))) (group (nth 0 cur))
                             (last (fn-ovw-hi (nfix (nth 1 cur)) (nfix (nth 2 cur)) w))
                             (top (nfix (nth 2 cur))) (owedp (nth 5 cur)) (legacyp (nth 4 cur))
                             (room cap) (server (nth 6 cur)) (v (nfix (nth 3 cur))))
                  (:instance fn-ovrp-hi-top-lt (k (nfix (nth 1 cur))) (top (nfix (nth 2 cur)))))))))

;;; ---- p7
(local
 (defthm fn-ovrp-quantum-closed
   (implies (not (fn-ovrp-live cur cap (len fn-ovr-lease)))
            (and (equal (mv-nth 0 (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat)) 0)
                 (equal (mv-nth 1 (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat)) cur)
                 (equal (mv-nth 2 (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat)) fn-ovr-lease)))
   :hints (("Goal" :in-theory (enable fn-ovr-quantum fn-ovrp-live)))))

; a window of N numbers from K is the host window through HI.
(local
 (defthm fn-ovrp-hi-n
   (implies (and (natp k) (natp top) (integerp hi) (<= k hi)
                 (<= hi (fn-ovw-hi k top w)))
            (equal (fn-ovw-hi k top (+ 1 (- hi k))) hi))
   :hints (("Goal" :in-theory (enable fn-ovw-hi)))))

(local
 (defthm fn-ovrp-hi-le-w
   (implies (and (natp k) (natp top) (integerp hi)
                 (<= hi (fn-ovw-hi k top w)))
            (<= (+ 1 (- hi k)) (if (posp w) w 1)))
   :hints (("Goal" :in-theory (enable fn-ovw-hi)))))

;;; ---- p8
(local
 (defthm fn-ovrp-fq-hi
   (let ((hi (car (fn-ovrp-fq cur w cap fn-ovr-lease)))
         (k (nfix (nth 1 cur))))
     (and (integerp hi)
          (<= (- k 1) hi)
          (<= (+ 1 (- hi k)) (if (posp w) w 1))))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable fn-ovrp-fill-open fn-ovrp-fill-done fn-ovrp-fill-lease fn-ovrp-fill-owed
                                       fn-ovrp-fill-hi-lower fn-ovrp-fill-hi-upper fn-ovrp-fill-hi-integerp
                                       fn-ovw-hi)
            :use ((:instance fn-ovrp-fill-hi (j (nfix (nth 1 cur)))
                             (group (nth 0 cur))
                             (last (fn-ovw-hi (nfix (nth 1 cur)) (nfix (nth 2 cur)) w))
                             (top (nfix (nth 2 cur))) (owedp (nth 5 cur)) (legacyp (nth 4 cur))
                             (room cap) (server (nth 6 cur)) (v (nfix (nth 3 cur))))
                  (:instance fn-ovrp-hi-le-w (k (nfix (nth 1 cur))) (top (nfix (nth 2 cur)))
                             (hi (car (fn-ovrp-fq cur w cap fn-ovr-lease))))
                  (:instance fn-ovrp-hi-natp (k (nfix (nth 1 cur))) (top (nfix (nth 2 cur)))))))))

(local
 (defthm fn-ovrp-ko4-live
   (implies (fn-ovrp-live cur cap (len fn-ovr-lease))
            (<= (mv-nth 0 (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat))
                (if (posp w) w 1)))
   :hints (("Goal" :cases ((<= (nfix (nth 1 cur)) (nfix (nth 2 cur))))
            :in-theory (disable fn-ovrp-fill-open fn-ovrp-fill-done fn-ovrp-fill-lease fn-ovrp-fill-owed
                                fn-ovrp-fill-hi-lower fn-ovrp-fill-hi-upper fn-ovrp-quantum-open
                                fn-ovrp-quantum-open-b fn-ovrp-quantum-closed fn-ovr-quantum))
           ("Subgoal 2" :use (fn-ovrp-quantum-open-b))
           ("Subgoal 1" :use (fn-ovrp-quantum-open fn-ovrp-fq-hi)))))

(defthm fn-ovr-quantum-window-at-most-w
  (<= (mv-nth 0 (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat))
      (if (posp w) w 1))
  :hints (("Goal" :cases ((fn-ovrp-live cur cap (len fn-ovr-lease)))
           :in-theory (disable fn-ovr-quantum fn-ovrp-live fn-ovrp-ko4-live))
          ("Subgoal 2" :use fn-ovrp-quantum-closed)
          ("Subgoal 1" :use fn-ovrp-ko4-live)))

;;; ---- p9
; the facts about the quantum's fill, as one statement the keystones use.
(local
 (defthm fn-ovrp-fq-facts
   (implies (and (fn-ovrp-live cur cap (len fn-ovr-lease)) (true-listp fn-ovr-lease))
            (let ((hi (car (fn-ovrp-fq cur w cap fn-ovr-lease)))
                  (k (nfix (nth 1 cur))) (top (nfix (nth 2 cur))))
              (and (equal (car (cdr (cdr (fn-ovrp-fq cur w cap fn-ovr-lease))))
                          (append fn-ovr-lease
                                  (fn-ovrp-body (nth 0 cur) k hi (nth 5 cur) (nth 6 cur)
                                                (nfix (nth 3 cur)) fn-arena fn-cat)))
                   (equal (car (cdr (fn-ovrp-fq cur w cap fn-ovr-lease)))
                          (fn-ovrp-owed (nth 0 cur) k hi (nth 5 cur) (nth 6 cur)
                                        (nfix (nth 3 cur)) fn-arena fn-cat))
                   (implies (<= k hi) (and (<= hi (fn-ovw-hi k top w)) (<= k top)))
                   (implies (< hi k) (equal (fn-ovrp-body (nth 0 cur) k hi (nth 5 cur) (nth 6 cur)
                                                          (nfix (nth 3 cur)) fn-arena fn-cat)
                                            nil)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-ovrp-live) (fn-ovrp-fill-hi-lower fn-ovrp-fill-hi-upper))
            :use ((:instance fn-ovrp-fill-lease (j (nfix (nth 1 cur)))
                             (group (nth 0 cur))
                             (last (fn-ovw-hi (nfix (nth 1 cur)) (nfix (nth 2 cur)) w))
                             (top (nfix (nth 2 cur))) (owedp (nth 5 cur)) (legacyp (nth 4 cur))
                             (room cap) (server (nth 6 cur)) (v (nfix (nth 3 cur))))
                  (:instance fn-ovrp-fill-owed (j (nfix (nth 1 cur)))
                             (group (nth 0 cur))
                             (last (fn-ovw-hi (nfix (nth 1 cur)) (nfix (nth 2 cur)) w))
                             (top (nfix (nth 2 cur))) (owedp (nth 5 cur)) (legacyp (nth 4 cur))
                             (room cap) (server (nth 6 cur)) (v (nfix (nth 3 cur))))
                  (:instance fn-ovrp-fill-hi (j (nfix (nth 1 cur)))
                             (group (nth 0 cur))
                             (last (fn-ovw-hi (nfix (nth 1 cur)) (nfix (nth 2 cur)) w))
                             (top (nfix (nth 2 cur))) (owedp (nth 5 cur)) (legacyp (nth 4 cur))
                             (room cap) (server (nth 6 cur)) (v (nfix (nth 3 cur))))
                  (:instance fn-ovrp-hi-natp (k (nfix (nth 1 cur))) (top (nfix (nth 2 cur))))
                  (:instance fn-ovrp-hi-bounds (k (nfix (nth 1 cur))) (top (nfix (nth 2 cur))))
                  (:instance fn-ovrp-body-empty (j (nfix (nth 1 cur)))
                             (hi (car (fn-ovrp-fq cur w cap fn-ovr-lease)))
                             (group (nth 0 cur)) (owedp (nth 5 cur)) (server (nth 6 cur))
                             (v (nfix (nth 3 cur)))))))))

;;; ---- p10
(local
 (defthm fn-ovrp-ko2-small
   (implies (and (fn-ovrp-live cur cap (len fn-ovr-lease)) (true-listp fn-ovr-lease)
                 (<= (nfix (nth 1 cur)) (nfix (nth 2 cur)))
                 (< (car (fn-ovrp-fq cur w cap fn-ovr-lease)) (nfix (nth 1 cur))))
            (and (equal (mv-nth 0 (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat)) 0)
                 (equal (mv-nth 1 (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat)) cur)
                 (equal (mv-nth 2 (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat)) fn-ovr-lease)))
   :hints (("Goal" :in-theory (disable fn-ovrp-quantum-open fn-ovrp-quantum-closed
                                       fn-ovrp-step-octets fn-ovrp-step-next fn-ovrp-hi-n fn-ovw-step fn-ovr-quantum fn-ovw-hi fn-ovrp-live)
            :use (fn-ovrp-quantum-open fn-ovrp-fq-facts)))))

(local
 (defthm fn-ovrp-stuff-true-listp
   (true-listp (fn-nntp-stuff-lines x))
   :hints (("Goal" :in-theory (enable fn-nntp-stuff-lines fn-nntp-crlf)))))

(local
 (defthm fn-ovrp-status-true-listp
   (true-listp (fn-ovr-status-octets))
   :hints (("Goal" :in-theory (enable fn-ovr-status-octets fn-ovw-status fn-nntp-crlf)))))

(local
 (defthm fn-ovrp-probe-true-listp
   (implies (natp j) (true-listp (fn-ovr-probe-octets group j server v fn-arena fn-cat)))
   :hints (("Goal" :use fn-ovrp-probe-is-win))))

(local
 (defthm fn-ovrp-body-true-listp
   (true-listp (fn-ovrp-body group j hi owedp server v fn-arena fn-cat))
   :hints (("Goal" :induct (fn-ovrp-body group j hi owedp server v fn-arena fn-cat)
            :in-theory (e/d (fn-ovrp-body) ())))))

(local
 (defthm fn-ovrp-step-at
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

(local
 (defthm fn-ovrp-ko2-n
   (implies (and (fn-ovrp-live cur cap (len fn-ovr-lease))
                 (<= (nfix (nth 1 cur)) (nfix (nth 2 cur)))
                 (equal (car (fn-ovrp-fq cur w cap fn-ovr-lease)) hi) (integerp hi)
                 (<= (nfix (nth 1 cur)) hi))
            (equal (mv-nth 0 (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat))
                   (+ 1 (- hi (nfix (nth 1 cur))))))
   :hints (("Goal" :in-theory (disable fn-ovrp-quantum-open fn-ovr-quantum fn-ovrp-live fn-ovrp-fill-open
                                       fn-ovrp-fill-done fn-ovrp-fill-lease fn-ovrp-fill-owed)
            :do-not-induct t
            :use (fn-ovrp-quantum-open (:instance fn-ovrp-fq-hi))))))

(local
 (defthm fn-ovrp-posp-n
   (implies (and (integerp hi) (<= (nfix k) hi) (equal n (+ 1 (- hi (nfix k)))))
            (posp n))))

(local
 (defthm fn-ovrp-ko2-big
   (implies (and (fn-ovrp-live cur cap (len fn-ovr-lease)) (true-listp fn-ovr-lease)
                 (<= (nfix (nth 1 cur)) (nfix (nth 2 cur)))
                 (consp cur) (not (nth 7 cur)) (natp (nth 3 cur))
                 (equal (car (fn-ovrp-fq cur w cap fn-ovr-lease)) hi) (integerp hi)
                 (<= (nfix (nth 1 cur)) hi))
            (let ((n (mv-nth 0 (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat))))
              (and (posp n)
                   (equal (mv-nth 2 (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat))
                          (append fn-ovr-lease (mv-nth 0 (fn-ovw-step cur n fn-arena fn-cat))))
                   (equal (mv-nth 1 (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat))
                          (mv-nth 1 (fn-ovw-step cur n fn-arena fn-cat))))))
   :hints (("Goal" :in-theory (union-theories '(mv-nth fn-cp-append-assoc natp nfix fn-ovrp-body-true-listp append-to-nil) (theory 'minimal-theory))
            :do-not-induct t
            :use (fn-ovrp-quantum-open fn-ovrp-fq-facts
                  (:instance fn-ovrp-ko2-n)
                  (:instance fn-ovrp-posp-n (k (nth 1 cur))
                             (n (mv-nth 0 (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat))))
                  (:instance fn-ovrp-step-at (hi hi)))))))

;;; ---- p11
(local
 (defthm fn-ovrp-step-b
   (implies (and (consp cur) (not (nth 7 cur)) (natp (nth 3 cur))
                 (< (nfix (nth 2 cur)) (nfix (nth 1 cur))))
            (and (equal (mv-nth 0 (fn-ovw-step cur n fn-arena fn-cat))
                        (fn-ovr-close-octets (nth 5 cur) (nth 4 cur)))
                 (equal (mv-nth 1 (fn-ovw-step cur n fn-arena fn-cat)) nil)))
   :hints (("Goal" :in-theory (e/d (fn-ovw-step fn-ovr-close-octets fn-ovw-hi)
                                   (fn-ovw-hdr-step fn-ovw-lines fn-nntp-stuff-lines fn-ovw-status))
            :use ((:instance fn-ovrp-lines-empty-above (group (nth 0 cur)) (k (nfix (nth 1 cur)))
                             (hi (nfix (nth 2 cur))) (server (nth 6 cur)) (v (nth 3 cur))))))))

(local
 (defthm fn-ovrp-ko2-live-b
   (implies (and (fn-ovrp-live cur cap (len fn-ovr-lease)) (fn-ovw-cursorp cur)
                 (true-listp fn-ovr-lease) (< (nfix (nth 2 cur)) (nfix (nth 1 cur))))
            (mv-let (n next lease2) (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat)
              (if (posp n)
                  (and (equal lease2 (append fn-ovr-lease (mv-nth 0 (fn-ovw-step cur n fn-arena fn-cat))))
                       (equal next (mv-nth 1 (fn-ovw-step cur n fn-arena fn-cat))))
                (and (equal lease2 fn-ovr-lease) (equal next cur)))))
   :hints (("Goal" :do-not-induct t
            :cases ((< cap (+ (len fn-ovr-lease) (len (fn-ovr-close-octets (nth 5 cur) (nth 4 cur))))))
            :in-theory (disable fn-ovrp-quantum-open fn-ovrp-quantum-open-b fn-ovrp-ko2-small fn-ovrp-ko2-big
                                fn-ovw-step fn-ovr-quantum fn-ovrp-live fn-ovr-close-octets fn-ovrp-step-b)
            :use (fn-ovrp-quantum-open-b
                  (:instance fn-ovrp-step-b (n 1)))))))

(local
 (defthm fn-ovrp-ko2-live-a
   (implies (and (fn-ovrp-live cur cap (len fn-ovr-lease)) (fn-ovw-cursorp cur)
                 (true-listp fn-ovr-lease) (<= (nfix (nth 1 cur)) (nfix (nth 2 cur))))
            (mv-let (n next lease2) (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat)
              (if (posp n)
                  (and (equal lease2 (append fn-ovr-lease (mv-nth 0 (fn-ovw-step cur n fn-arena fn-cat))))
                       (equal next (mv-nth 1 (fn-ovw-step cur n fn-arena fn-cat))))
                (and (equal lease2 fn-ovr-lease) (equal next cur)))))
   :hints (("Goal" :cases ((< (car (fn-ovrp-fq cur w cap fn-ovr-lease)) (nfix (nth 1 cur))))
            :in-theory (disable fn-ovrp-quantum-open fn-ovrp-quantum-open-b fn-ovrp-ko2-small fn-ovrp-ko2-big
                                fn-ovw-step fn-ovr-quantum fn-ovrp-live))
           ("Subgoal 2" :use ((:instance fn-ovrp-ko2-big (hi (car (fn-ovrp-fq cur w cap fn-ovr-lease))))
                              fn-ovrp-fq-hi))
           ("Subgoal 1" :use fn-ovrp-ko2-small))))

(local
 (defthm fn-ovrp-ko2-live
   (implies (and (fn-ovrp-live cur cap (len fn-ovr-lease)) (fn-ovw-cursorp cur)
                 (true-listp fn-ovr-lease))
            (mv-let (n next lease2) (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat)
              (if (posp n)
                  (and (equal lease2 (append fn-ovr-lease (mv-nth 0 (fn-ovw-step cur n fn-arena fn-cat))))
                       (equal next (mv-nth 1 (fn-ovw-step cur n fn-arena fn-cat))))
                (and (equal lease2 fn-ovr-lease) (equal next cur)))))
   :hints (("Goal" :cases ((<= (nfix (nth 1 cur)) (nfix (nth 2 cur))))
            :in-theory (disable fn-ovrp-ko2-live-a fn-ovrp-ko2-live-b fn-ovr-quantum fn-ovrp-live fn-ovw-step))
           ("Subgoal 2" :use fn-ovrp-ko2-live-b)
           ("Subgoal 1" :use fn-ovrp-ko2-live-a))))

(defthm fn-ovr-quantum-is-the-step
  (implies (and (fn-ovw-cursorp cur) (true-listp fn-ovr-lease))
           (mv-let (n next lease2) (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat)
             (if (posp n)
                 (and (equal lease2 (append fn-ovr-lease (mv-nth 0 (fn-ovw-step cur n fn-arena fn-cat))))
                      (equal next (mv-nth 1 (fn-ovw-step cur n fn-arena fn-cat))))
               (and (equal lease2 fn-ovr-lease) (equal next cur)))))
  :hints (("Goal" :cases ((fn-ovrp-live cur cap (len fn-ovr-lease)))
           :in-theory (disable fn-ovrp-quantum-closed fn-ovr-quantum fn-ovrp-live))
          ("Subgoal 2" :use fn-ovrp-quantum-closed)
          ("Subgoal 1" :use fn-ovrp-ko2-live)))

;;; ---- p12
(local
 (defthm fn-ovrp-ko3-arith
   (implies (and (true-listp l) (true-listp b)
                 (<= (+ (len l) (len b) (if donep (len c) 0)) m))
            (<= (len (if donep (append (append l b) c) (append l b))) m))))

(local
 (defthm fn-ovrp-hi-le-top
   (<= (nfix (fn-ovw-hi k top w)) (nfix top))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-ovw-hi)))))

(local
 (defthm fn-ovrp-ko3-fit
   (implies (and (fn-ovrp-live cur cap (len fn-ovr-lease)) (true-listp fn-ovr-lease)
                 (equal (car (fn-ovrp-fq cur w cap fn-ovr-lease)) hi) (integerp hi)
                 (<= (nfix (nth 1 cur)) hi))
            (<= (+ (len fn-ovr-lease)
                   (len (fn-ovrp-body (nth 0 cur) (nfix (nth 1 cur)) hi (nth 5 cur) (nth 6 cur)
                                      (nfix (nth 3 cur)) fn-arena fn-cat))
                   (if (<= (nfix (nth 2 cur)) hi)
                       (len (fn-ovr-close-octets
                             (fn-ovrp-owed (nth 0 cur) (nfix (nth 1 cur)) hi (nth 5 cur) (nth 6 cur)
                                           (nfix (nth 3 cur)) fn-arena fn-cat)
                             (nth 4 cur)))
                     0))
                (nfix cap)))
   :rule-classes nil
   :hints (("Goal" :in-theory (union-theories '(natp nfix fn-ovrp-nfix-natp) (theory 'minimal-theory))
            :do-not-induct t
            :use ((:instance fn-ovrp-fill-fit (j (nfix (nth 1 cur)))
                             (group (nth 0 cur))
                             (last (fn-ovw-hi (nfix (nth 1 cur)) (nfix (nth 2 cur)) w))
                             (top (nfix (nth 2 cur))) (owedp (nth 5 cur)) (legacyp (nth 4 cur))
                             (room cap) (server (nth 6 cur)) (v (nfix (nth 3 cur)))
                             (hi hi))
                  (:instance fn-ovrp-hi-le-top (k (nfix (nth 1 cur))) (top (nfix (nth 2 cur))) (w w)))))))

(local
 (defthm fn-ovrp-ko3-live
   (implies (and (fn-ovrp-live cur cap (len fn-ovr-lease)) (true-listp fn-ovr-lease)
                 (equal (car (fn-ovrp-fq cur w cap fn-ovr-lease)) hi) (integerp hi)
                 (<= (nfix (nth 1 cur)) (nfix (nth 2 cur)))
                 (<= (nfix (nth 1 cur)) hi))
            (<= (len (mv-nth 2 (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat)))
                (nfix cap)))
   :hints (("Goal" :in-theory (union-theories '(mv-nth natp nfix fn-ovrp-body-true-listp) (theory 'minimal-theory))
            :do-not-induct t
            :use (fn-ovrp-quantum-open fn-ovrp-fq-facts fn-ovrp-ko3-fit
                  (:instance fn-ovrp-ko3-arith (l fn-ovr-lease)
                             (b (fn-ovrp-body (nth 0 cur) (nfix (nth 1 cur)) hi (nth 5 cur) (nth 6 cur)
                                              (nfix (nth 3 cur)) fn-arena fn-cat))
                             (c (fn-ovr-close-octets
                                 (fn-ovrp-owed (nth 0 cur) (nfix (nth 1 cur)) hi (nth 5 cur) (nth 6 cur)
                                               (nfix (nth 3 cur)) fn-arena fn-cat)
                                 (nth 4 cur)))
                             (donep (<= (nfix (nth 2 cur)) hi))
                             (m (nfix cap))))))))

(local
 (defthm fn-ovrp-ko3-live2
   (implies (and (fn-ovrp-live cur cap (len fn-ovr-lease)) (true-listp fn-ovr-lease)
                 (<= (nfix (nth 1 cur)) (nfix (nth 2 cur))))
            (<= (len (mv-nth 2 (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat)))
                (nfix cap)))
   :hints (("Goal" :cases ((< (car (fn-ovrp-fq cur w cap fn-ovr-lease)) (nfix (nth 1 cur))))
            :in-theory (disable fn-ovrp-ko3-live fn-ovrp-ko2-small fn-ovr-quantum fn-ovrp-live))
           ("Subgoal 2" :use ((:instance fn-ovrp-ko3-live (hi (car (fn-ovrp-fq cur w cap fn-ovr-lease))))
                              fn-ovrp-fq-hi))
           ("Subgoal 1" :use fn-ovrp-ko2-small))))

(local
 (defthm fn-ovrp-ko3-live3
   (implies (and (fn-ovrp-live cur cap (len fn-ovr-lease)) (true-listp fn-ovr-lease))
            (<= (len (mv-nth 2 (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat)))
                (nfix cap)))
   :hints (("Goal" :cases ((<= (nfix (nth 1 cur)) (nfix (nth 2 cur))))
            :in-theory (disable fn-ovrp-ko3-live2 fn-ovrp-quantum-open-b fn-ovr-quantum fn-ovrp-live fn-ovr-close-octets))
           ("Subgoal 2" :use fn-ovrp-quantum-open-b)
           ("Subgoal 1" :use fn-ovrp-ko3-live2))))

(defthm fn-ovr-quantum-within-the-lease
  (implies (and (true-listp fn-ovr-lease) (<= (len fn-ovr-lease) (nfix cap)))
           (<= (len (mv-nth 2 (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat)))
               (nfix cap)))
  :hints (("Goal" :cases ((fn-ovrp-live cur cap (len fn-ovr-lease)))
           :in-theory (disable fn-ovr-quantum fn-ovrp-live))
          ("Subgoal 2" :use fn-ovrp-quantum-closed)
          ("Subgoal 1" :use fn-ovrp-ko3-live3)))

;;; ---- p13
(local
 (defthm fn-ovrp-owed-snoc
   (implies (and (natp j) (integerp hi) (<= (- j 1) hi))
            (equal (fn-ovrp-owed group j (+ 1 hi) owedp server v fn-arena fn-cat)
                   (and (fn-ovrp-owed group j hi owedp server v fn-arena fn-cat)
                        (not (consp (fn-ovr-probe-octets group (+ 1 hi) server v fn-arena fn-cat))))))
   :hints (("Goal" :in-theory (disable fn-ovrp-owed-step fn-ovrp-body-step)
            :use (fn-ovrp-win-extend
                  (:instance fn-ovrp-owed-is-window (hi (+ 1 hi)))
                  (:instance fn-ovrp-owed-is-window)
                  (:instance fn-ovrp-probe-is-win (j (+ 1 hi))))))))

(local
 (defthm fn-ovrp-top-eq
   (implies (and (natp top) (integerp hh) (<= top (+ 1 hh)) (<= (+ 1 hh) (fn-ovw-hi k top w)))
            (equal top (+ 1 hh)))
   :rule-classes nil
   :hints (("Goal" :use (fn-ovrp-hi-le-top fn-ovrp-hi-natp)))))

(local
 (defthm fn-ovrp-ext-step
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
   :hints (("Goal" :in-theory (e/d (fn-ovrp-ext) (fn-ovrp-step-at fn-ovrp-body-snoc fn-ovrp-owed-snoc fn-ovrp-body-step fn-ovrp-owed-step fn-ovw-step
                                                  fn-ovw-hi fn-ovr-close-octets))
            :use ((:instance fn-ovrp-step-at (hi (+ 1 hh)))
                  (:instance fn-ovrp-hi-le-top (k (nfix (nth 1 cur))) (top (nfix (nth 2 cur))))
                  (:instance fn-ovrp-top-eq (k (nfix (nth 1 cur))) (top (nfix (nth 2 cur))))
                  (:instance fn-ovrp-body-snoc (j (nfix (nth 1 cur))) (hi hh) (group (nth 0 cur))
                             (owedp (nth 5 cur)) (server (nth 6 cur)) (v (nth 3 cur)))
                  (:instance fn-ovrp-owed-snoc (j (nfix (nth 1 cur))) (hi hh) (group (nth 0 cur))
                             (owedp (nth 5 cur)) (server (nth 6 cur)) (v (nth 3 cur))))))))

;;; ---- p14
(local
 (defthm fn-ovrp-hi-int
   (integerp (fn-ovw-hi k (nfix top) w))
   :rule-classes nil
   :hints (("Goal" :use (:instance fn-ovrp-hi-natp (top (nfix top)))))))

(local
 (defthm fn-ovrp-hi-ge-k
   (implies (and (natp k) (natp top) (<= k top))
            (<= k (fn-ovw-hi k top w)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-ovw-hi)))))

(local
 (defthm fn-ovrp-ko5b
   (implies (and (fn-ovrp-live cur cap (len fn-ovr-lease)) (true-listp fn-ovr-lease)
                 (natp (nth 3 cur))
                 (equal (car (fn-ovrp-fq cur w cap fn-ovr-lease)) hi) (integerp hi)
                 (<= (nfix (nth 1 cur)) hi)
                 (<= (+ 1 hi) (fn-ovw-hi (nfix (nth 1 cur)) (nfix (nth 2 cur)) w)))
            (< (- (nfix cap) (len fn-ovr-lease))
               (len (mv-nth 0 (fn-ovw-step cur
                                           (+ 1 (mv-nth 0 (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat)))
                                           fn-arena fn-cat)))))
   :hints (("Goal" :in-theory (disable fn-ovrp-quantum-open fn-ovr-quantum fn-ovrp-live fn-ovrp-fill-max
                                       fn-ovrp-ext-step fn-ovrp-step-octets fn-ovrp-step-next fn-ovrp-step-at fn-ovw-step fn-ovw-hi fn-ovrp-ext fn-ovrp-fill-open
                                       fn-ovrp-fill-done fn-ovrp-fill-lease fn-ovrp-fill-owed)
            :do-not-induct t
            :use ((:instance fn-ovrp-ko2-n)
                  (:instance fn-ovrp-ext-step (hh hi))
                  (:instance fn-ovrp-fill-max (j (nfix (nth 1 cur)))
                             (group (nth 0 cur))
                             (last (fn-ovw-hi (nfix (nth 1 cur)) (nfix (nth 2 cur)) w))
                             (top (nfix (nth 2 cur))) (owedp (nth 5 cur)) (legacyp (nth 4 cur))
                             (room cap) (server (nth 6 cur)) (v (nfix (nth 3 cur)))
                             (hi hi))
                  (:instance fn-ovrp-hi-int (k (nfix (nth 1 cur))) (top (nth 2 cur)))
                  (:instance fn-ovrp-hi-le-top (k (nfix (nth 1 cur))) (top (nfix (nth 2 cur))) (w w)))))))

(local
 (defthm fn-ovrp-ko5a
   (implies (and (fn-ovrp-live cur cap (len fn-ovr-lease)) (true-listp fn-ovr-lease)
                 (natp (nth 3 cur))
                 (equal (+ -1 (nfix (nth 1 cur))) (car (fn-ovrp-fq cur w cap fn-ovr-lease)))
                 (<= (nfix (nth 1 cur)) (nfix (nth 2 cur)))
                 (<= (len (mv-nth 0 (fn-ovw-step cur 1 fn-arena fn-cat)))
                     (- (nfix cap) (len fn-ovr-lease))))
            nil)
   :rule-classes nil
   :hints (("Goal" :in-theory (disable fn-ovrp-quantum-open fn-ovr-quantum fn-ovrp-live fn-ovrp-fill-max
                                       fn-ovrp-ext-step fn-ovrp-step-octets fn-ovrp-step-next fn-ovrp-step-at
                                       fn-ovw-step fn-ovw-hi fn-ovrp-ext fn-ovrp-fill-open
                                       fn-ovrp-fill-done fn-ovrp-fill-lease fn-ovrp-fill-owed)
            :do-not-induct t
            :use ((:instance fn-ovrp-ext-step (hh (+ -1 (nfix (nth 1 cur)))))
                  (:instance fn-ovrp-body-empty (j (nfix (nth 1 cur))) (hi (+ -1 (nfix (nth 1 cur))))
                             (group (nth 0 cur)) (owedp (nth 5 cur)) (server (nth 6 cur)) (v (nfix (nth 3 cur))))
                  (:instance fn-ovrp-fill-max (j (nfix (nth 1 cur)))
                             (group (nth 0 cur))
                             (last (fn-ovw-hi (nfix (nth 1 cur)) (nfix (nth 2 cur)) w))
                             (top (nfix (nth 2 cur))) (owedp (nth 5 cur)) (legacyp (nth 4 cur))
                             (room cap) (server (nth 6 cur)) (v (nfix (nth 3 cur)))
                             (hi (+ -1 (nfix (nth 1 cur)))))
                  (:instance fn-ovrp-hi-ge-k (k (nfix (nth 1 cur))) (top (nfix (nth 2 cur))) (w w))
                  (:instance fn-ovrp-hi-int (k (nfix (nth 1 cur))) (top (nth 2 cur)))
                  (:instance fn-ovrp-hi-le-top (k (nfix (nth 1 cur))) (top (nfix (nth 2 cur))) (w w)))))))

;;; ---- p15
(local
 (defthm fn-ovrp-fq-int
   (integerp (car (fn-ovrp-fq cur w cap fn-ovr-lease)))
   :hints (("Goal" :use fn-ovrp-fq-hi))))

(local
 (defthm fn-ovrp-ko5a-hi
   (implies (and (fn-ovrp-live cur cap (len fn-ovr-lease)) (true-listp fn-ovr-lease)
                 (natp (nth 3 cur))
                 (equal (car (fn-ovrp-fq cur w cap fn-ovr-lease)) hi) (integerp hi)
                 (<= (+ -1 (nfix (nth 1 cur))) hi)
                 (<= (nfix (nth 1 cur)) (nfix (nth 2 cur)))
                 (<= (len (mv-nth 0 (fn-ovw-step cur 1 fn-arena fn-cat)))
                     (- (nfix cap) (len fn-ovr-lease))))
            (posp (mv-nth 0 (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat))))
   :hints (("Goal" :cases ((< hi (nfix (nth 1 cur))))
            :in-theory (disable fn-ovrp-ko2-small fn-ovrp-ko2-n fn-ovr-quantum fn-ovrp-live
                                fn-ovw-step fn-ovrp-step-octets fn-ovrp-step-next fn-ovrp-step-at fn-ovrp-ext-step))
           ("Subgoal 2" :use ((:instance fn-ovrp-ko2-n)
                              (:instance fn-ovrp-posp-n (k (nth 1 cur))
                                         (n (mv-nth 0 (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat))))))
           ("Subgoal 1" :use (fn-ovrp-ko2-small fn-ovrp-ko5a)))))

(local
 (defthm fn-ovrp-ko5a-live
   (implies (and (fn-ovrp-live cur cap (len fn-ovr-lease)) (true-listp fn-ovr-lease)
                 (natp (nth 3 cur))
                 (<= (nfix (nth 1 cur)) (nfix (nth 2 cur)))
                 (<= (len (mv-nth 0 (fn-ovw-step cur 1 fn-arena fn-cat)))
                     (- (nfix cap) (len fn-ovr-lease))))
            (posp (mv-nth 0 (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat))))
   :hints (("Goal" :in-theory (disable fn-ovrp-ko5a-hi fn-ovr-quantum fn-ovrp-live fn-ovw-step)
            :use ((:instance fn-ovrp-ko5a-hi (hi (car (fn-ovrp-fq cur w cap fn-ovr-lease))))
                  fn-ovrp-fq-hi)))))

(local
 (defthm fn-ovrp-ko5b-live
   (implies (and (fn-ovrp-live cur cap (len fn-ovr-lease)) (true-listp fn-ovr-lease)
                 (natp (nth 3 cur))
                 (posp (mv-nth 0 (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat)))
                 (< (mv-nth 0 (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat))
                    (+ 1 (- (fn-ovw-hi (nfix (nth 1 cur)) (nfix (nth 2 cur)) w) (nfix (nth 1 cur))))))
            (< (- (nfix cap) (len fn-ovr-lease))
               (len (mv-nth 0 (fn-ovw-step cur
                                           (+ 1 (mv-nth 0 (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat)))
                                           fn-arena fn-cat)))))
   :hints (("Goal" :cases ((< (car (fn-ovrp-fq cur w cap fn-ovr-lease)) (nfix (nth 1 cur))))
            :in-theory (disable fn-ovrp-ko2-small fn-ovrp-ko5b fn-ovrp-ko2-n fn-ovr-quantum fn-ovrp-live
                                fn-ovw-step fn-ovrp-step-octets fn-ovrp-step-next fn-ovrp-step-at fn-ovrp-ext-step))
           ("Subgoal 2" :use ((:instance fn-ovrp-ko5b (hi (car (fn-ovrp-fq cur w cap fn-ovr-lease))))
                              (:instance fn-ovrp-ko2-n (hi (car (fn-ovrp-fq cur w cap fn-ovr-lease))))
                              fn-ovrp-fq-hi))
           ("Subgoal 1" :use (fn-ovrp-ko2-small)))))

(local
 (defthm fn-ovrp-ko5-live
   (implies (and (fn-ovw-cursorp cur) (fn-ovrp-live cur cap (len fn-ovr-lease)) (true-listp fn-ovr-lease))
            (and (implies (and (<= (len fn-ovr-lease) (nfix cap))
                               (<= (nfix (nth 1 cur)) (nfix (nth 2 cur)))
                               (<= (len (mv-nth 0 (fn-ovw-step cur 1 fn-arena fn-cat)))
                                   (- (nfix cap) (len fn-ovr-lease))))
                          (posp (mv-nth 0 (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat))))
                 (implies (and (posp (mv-nth 0 (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat)))
                               (< (mv-nth 0 (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat))
                                  (+ 1 (- (fn-ovw-hi (nfix (nth 1 cur)) (nfix (nth 2 cur)) w)
                                          (nfix (nth 1 cur))))))
                          (< (- (nfix cap) (len fn-ovr-lease))
                             (len (mv-nth 0 (fn-ovw-step cur
                                                         (+ 1 (mv-nth 0 (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat)))
                                                         fn-arena fn-cat)))))))
   :hints (("Goal" :cases ((<= (nfix (nth 1 cur)) (nfix (nth 2 cur))))
            :in-theory (disable fn-ovr-quantum fn-ovrp-live fn-ovw-step fn-ovrp-ko5a-live fn-ovrp-ko5b-live
                                fn-ovrp-quantum-open-b fn-ovr-close-octets))
           ("Subgoal 2" :use (fn-ovrp-quantum-open-b
                              (:instance fn-ovrp-hi-top-lt (k (nfix (nth 1 cur))) (top (nfix (nth 2 cur))))))
           ("Subgoal 1" :use (fn-ovrp-ko5a-live fn-ovrp-ko5b-live)))))

(defthm fn-ovr-quantum-is-the-largest-that-fits
  (implies (and (fn-ovw-cursorp cur) (consp cur) (not (nth 7 cur)) (fn-cbor-octet-listp (nth 6 cur))
                (true-listp fn-ovr-lease) (unsigned-byte-p 59 cap))
           (let* ((n (mv-nth 0 (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat)))
                  (room (- (nfix cap) (len fn-ovr-lease)))
                  (wmax (+ 1 (- (fn-ovw-hi (nfix (nth 1 cur)) (nfix (nth 2 cur)) w)
                                (nfix (nth 1 cur))))))
             (and (implies (and (<= (len fn-ovr-lease) (nfix cap))
                                (<= (nfix (nth 1 cur)) (nfix (nth 2 cur)))
                                (<= (len (mv-nth 0 (fn-ovw-step cur 1 fn-arena fn-cat))) room))
                           (posp n))
                  (implies (and (posp n) (< n wmax))
                           (< room (len (mv-nth 0 (fn-ovw-step cur (+ 1 n) fn-arena fn-cat))))))))
  :hints (("Goal" :cases ((fn-ovrp-live cur cap (len fn-ovr-lease)))
           :in-theory (disable fn-ovr-quantum fn-ovrp-live fn-ovrp-ko5-live fn-ovw-step fn-ovrp-quantum-open fn-ovrp-quantum-open-b fn-ovrp-step-octets fn-ovrp-step-next fn-ovrp-step-at fn-ovrp-ext-step fn-ovrp-body-step fn-ovrp-owed-step fn-ovrp-quantum-closed))
          ("Subgoal 2" :use fn-ovrp-quantum-closed :in-theory (e/d (fn-ovrp-live) (fn-ovr-quantum fn-ovw-step fn-ovrp-ko5-live fn-ovrp-quantum-open fn-ovrp-quantum-open-b)))
          ("Subgoal 1" :use fn-ovrp-ko5-live :in-theory (disable fn-ovr-quantum fn-ovrp-live fn-ovrp-ko5-live fn-ovw-step fn-ovrp-quantum-open fn-ovrp-quantum-open-b fn-ovrp-step-octets fn-ovrp-step-next fn-ovrp-step-at fn-ovrp-ext-step fn-ovrp-body-step fn-ovrp-owed-step))))

;;; ---- p16
(local
 (defun fn-ovrp-canon (cur)
   (declare (xargs :verify-guards nil))
   (fn-ovw-cursor (nth 0 cur) (nfix (nth 1 cur)) (nfix (nth 2 cur)) (nth 3 cur) (nth 4 cur)
                  (nth 5 cur) (nth 6 cur))))

(local
 (defthm fn-ovrp-canon-step
   (implies (and (consp cur) (not (nth 7 cur)))
            (equal (fn-ovw-step (fn-ovrp-canon cur) w fn-arena fn-cat)
                   (fn-ovw-step cur w fn-arena fn-cat)))
   :hints (("Goal" :in-theory (e/d (fn-ovw-step fn-ovrp-canon fn-ovw-cursor) (fn-ovw-hdr-step))))))

(local
 (defthm fn-ovrp-canon-run
   (implies (and (consp cur) (not (nth 7 cur)))
            (equal (fn-ovw-run (fn-ovrp-canon cur) w fn-arena fn-cat)
                   (fn-ovw-run cur w fn-arena fn-cat)))
   :hints (("Goal" :in-theory (disable fn-ovw-step fn-ovrp-canon)
            :expand ((fn-ovw-run (fn-ovrp-canon cur) w fn-arena fn-cat)
                     (fn-ovw-run cur w fn-arena fn-cat))))))

(local
 (defthm fn-ovrp-run-indep
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

(local
 (defthm fn-ovrp-quantum-posp-live
   (implies (posp (mv-nth 0 (fn-ovr-quantum cur w cap fn-ovr-lease fn-arena fn-cat)))
            (and (consp cur) (not (nth 7 cur))))
   :rule-classes nil
   :hints (("Goal" :cases ((fn-ovrp-live cur cap (len fn-ovr-lease)))
            :in-theory (disable fn-ovr-quantum fn-ovrp-live)
            :use fn-ovrp-quantum-closed)
           ("Subgoal 1" :in-theory (enable fn-ovrp-live)))))

(local
 (defthm fn-ovrp-step-next-live
   (implies (and (not (nth 7 cur)) (mv-nth 1 (fn-ovw-step cur n fn-arena fn-cat)))
            (not (nth 7 (mv-nth 1 (fn-ovw-step cur n fn-arena fn-cat)))))
   :hints (("Goal" :in-theory (e/d (fn-ovw-step fn-ovw-cursor)
                                   (fn-ovw-hdr-step fn-ovw-lines fn-nntp-stuff-lines fn-ovw-status))))))

(local
 (defthm fn-ovrp-run-split
   (implies (and (fn-ovw-cursorp cur) (consp cur) (not (nth 7 cur)))
            (equal (fn-ovw-run cur w fn-arena fn-cat)
                   (append (mv-nth 0 (fn-ovw-step cur n fn-arena fn-cat))
                           (if (mv-nth 1 (fn-ovw-step cur n fn-arena fn-cat))
                               (fn-ovw-run (mv-nth 1 (fn-ovw-step cur n fn-arena fn-cat)) w fn-arena fn-cat)
                             nil))))
   :hints (("Goal" :in-theory (disable fn-ovw-step fn-ovw-run fn-ovrp-canon fn-ovrp-step-next-live fn-ovw-step-keeps-cursorp)
            :use ((:instance fn-ovrp-run-indep (w w) (w2 n))
                  (:instance fn-ovrp-run-indep (w n) (w2 w) (cur (mv-nth 1 (fn-ovw-step cur n fn-arena fn-cat))))
                  (:instance fn-ovrp-step-next-live)
                  (:instance fn-ovw-step-progresses (w n))
                  (:instance fn-ovw-step-keeps-cursorp (w n)))
            :expand ((fn-ovw-run cur n fn-arena fn-cat))))))

(local
 (defthm fn-ovrp-run-fold-more
   (implies (and (fn-ovw-cursorp cur) (consp cur) (not (nth 7 cur))
                 (mv-nth 1 (fn-ovw-step cur n fn-arena fn-cat)))
            (equal (append (mv-nth 0 (fn-ovw-step cur n fn-arena fn-cat))
                           (fn-ovw-run (mv-nth 1 (fn-ovw-step cur n fn-arena fn-cat)) w fn-arena fn-cat))
                   (fn-ovw-run cur w fn-arena fn-cat)))
   :hints (("Goal" :use fn-ovrp-run-split :in-theory (disable fn-ovrp-run-split fn-ovw-step fn-ovw-run)))))

(local
 (defthm fn-ovrp-run-fold-last
   (implies (and (fn-ovw-cursorp cur) (consp cur) (not (nth 7 cur))
                 (not (mv-nth 1 (fn-ovw-step cur n fn-arena fn-cat))))
            (equal (mv-nth 0 (fn-ovw-step cur n fn-arena fn-cat))
                   (fn-ovw-run cur w fn-arena fn-cat)))
   :hints (("Goal" :use fn-ovrp-run-split :in-theory (disable fn-ovrp-run-split fn-ovw-step fn-ovw-run)))))

(local
 (defthm fn-ovrp-q-oct
   (implies (and (fn-ovw-cursorp cur) (true-listp l)
                 (posp (mv-nth 0 (fn-ovr-quantum cur w cap l fn-arena fn-cat))))
            (equal (mv-nth 2 (fn-ovr-quantum cur w cap l fn-arena fn-cat))
                   (append l (mv-nth 0 (fn-ovw-step cur (mv-nth 0 (fn-ovr-quantum cur w cap l fn-arena fn-cat))
                                                    fn-arena fn-cat)))))
   :hints (("Goal" :use (:instance fn-ovr-quantum-is-the-step (fn-ovr-lease l))
            :in-theory (disable fn-ovr-quantum-is-the-step fn-ovr-quantum fn-ovw-step)))))

(local
 (defthm fn-ovrp-q-next
   (implies (and (fn-ovw-cursorp cur) (true-listp l)
                 (posp (mv-nth 0 (fn-ovr-quantum cur w cap l fn-arena fn-cat))))
            (equal (mv-nth 1 (fn-ovr-quantum cur w cap l fn-arena fn-cat))
                   (mv-nth 1 (fn-ovw-step cur (mv-nth 0 (fn-ovr-quantum cur w cap l fn-arena fn-cat))
                                          fn-arena fn-cat))))
   :hints (("Goal" :use (:instance fn-ovr-quantum-is-the-step (fn-ovr-lease l))
            :in-theory (disable fn-ovr-quantum-is-the-step fn-ovr-quantum fn-ovw-step)))))

(local
 (defthm fn-ovrp-q-live
   (implies (posp (mv-nth 0 (fn-ovr-quantum cur w cap l fn-arena fn-cat)))
            (and (consp cur) (not (nth 7 cur))))
   :hints (("Goal" :use (:instance fn-ovrp-quantum-posp-live (fn-ovr-lease l))
            :in-theory (disable fn-ovr-quantum)))))

(local
 (defthm fn-ovrp-q-live-consp
   (implies (posp (car (fn-ovr-quantum cur w cap l fn-arena fn-cat)))
            (consp cur))
   :hints (("Goal" :use fn-ovrp-q-live :in-theory (disable fn-ovr-quantum fn-ovrp-q-live)))))

(local
 (defthm fn-ovrp-q-live-nth7
   (implies (posp (car (fn-ovr-quantum cur w cap l fn-arena fn-cat)))
            (not (nth 7 cur)))
   :hints (("Goal" :use fn-ovrp-q-live :in-theory (disable fn-ovr-quantum fn-ovrp-q-live)))))

(local
 (defthm fn-ovrp-run-ko6
   (implies (and (fn-ovw-cursorp cur)
                 (mv-nth 0 (fn-ovr-run cur w cap fn-ovr-lease fn-arena fn-cat)))
            (equal (mv-nth 1 (fn-ovr-run cur w cap fn-ovr-lease fn-arena fn-cat))
                   (fn-ovw-run cur w fn-arena fn-cat)))
   :hints (("Goal" :induct (fn-ovr-run cur w cap fn-ovr-lease fn-arena fn-cat)
            :in-theory (disable fn-ovr-quantum fn-ovw-step fn-ovw-run fn-ovrp-canon fn-ovr-quantum-is-the-step
                                fn-ovrp-run-split fn-ovrp-step-octets fn-ovrp-step-next fn-ovrp-step-at fn-ovrp-ext-step fn-ovrp-ko2-big fn-ovrp-ko2-small fn-ovrp-ko2-n)
            :expand ((fn-ovr-run cur w cap fn-ovr-lease fn-arena fn-cat)))
           (and stable-under-simplificationp
                '(:use ((:instance fn-ovrp-q-live (l nil))
                        (:instance fn-ovrp-run-fold-more (n (mv-nth 0 (fn-ovr-quantum cur w cap nil fn-arena fn-cat))))
                        (:instance fn-ovrp-run-fold-last (n (mv-nth 0 (fn-ovr-quantum cur w cap nil fn-arena fn-cat))))))))))

(local (in-theory (disable fn-ovrp-run-fold-more fn-ovrp-run-fold-last fn-ovrp-q-oct fn-ovrp-q-next
                           fn-ovrp-q-live-consp fn-ovrp-q-live-nth7)))

;;; ---- p17
(defthm fn-ovr-run-is-the-windowed-reply
  (implies (and (fn-ovw-cursorp cur)
                (mv-nth 0 (fn-ovr-run cur w cap fn-ovr-lease fn-arena fn-cat)))
           (equal (mv-nth 1 (fn-ovr-run cur w cap fn-ovr-lease fn-arena fn-cat))
                  (fn-ovw-run cur w fn-arena fn-cat)))
  :hints (("Goal" :use fn-ovrp-run-ko6 :in-theory (disable fn-ovrp-run-ko6))))

; --- KO7 support (under the nonempty-range hypothesis)
(local
 (defthm fn-ovrp-pw-mono
   (implies (and (natp k) (natp k2) (<= k k2)
                 (fn-ovr-probes-within group k top server v l fn-arena fn-cat))
            (fn-ovr-probes-within group k2 top server v l fn-arena fn-cat))
   :hints (("Goal" :induct (fn-ovr-probes-within group k top server v l fn-arena fn-cat)
            :in-theory (disable fn-ovr-probe-len-is-the-length))
           ("Subgoal *1/2" :expand ((fn-ovr-probes-within group k top server v l fn-arena fn-cat)))
           ("Subgoal *1/1" :expand ((fn-ovr-probes-within group k2 top server v l fn-arena fn-cat))))))

(local
 (defthm fn-ovrp-pw-first
   (implies (and (natp k) (<= k (nfix top))
                 (fn-ovr-probes-within group k top server v l fn-arena fn-cat))
            (<= (fn-ovr-probe-len group k server v fn-arena fn-cat) (nfix l)))
   :rule-classes nil
   :hints (("Goal" :expand ((fn-ovr-probes-within group k top server v l fn-arena fn-cat))))))

;;; ---- p18
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

;;; ---- p19
(local
 (defthm fn-ovrp-live-intro
   (implies (and (consp cur) (not (nth 7 cur)) (fn-cbor-octet-listp (nth 6 cur)) (unsigned-byte-p 59 cap)
                 (<= (len fn-ovr-lease) cap))
            (fn-ovrp-live cur cap (len fn-ovr-lease)))
   :hints (("Goal" :in-theory (enable fn-ovrp-live)))))

(local
 (defthm fn-ovrp-probe-len-le
   (implies (and (natp (nth 3 cur)) (natp k) (<= k (nfix top))
                 (fn-ovr-probes-within g k top s (nth 3 cur) l fn-arena fn-cat))
            (<= (len (fn-ovr-probe-octets g k s (nth 3 cur) fn-arena fn-cat)) (nfix l)))
   :hints (("Goal" :use (fn-ovrp-pw-first
                         (:instance fn-ovr-probe-len-is-the-length (group g) (j k) (server s) (v (nth 3 cur))))
            :in-theory (disable fn-ovr-probe-len-is-the-length)))))

(local
 (defthm fn-ovrp-ko7-pos-a
   (implies (and (fn-ovw-cursorp cur) (consp cur) (not (nth 7 cur))
                 (fn-cbor-octet-listp (nth 6 cur)) (unsigned-byte-p 59 cap)
                 (fn-ovr-probes-within (nth 0 cur) (nfix (nth 1 cur)) (nfix (nth 2 cur)) (nth 6 cur)
                                       (nfix (nth 3 cur)) l fn-arena fn-cat)
                 (<= (+ (nfix l) (fn-ovr-frame-max)) (nfix cap))
                 (<= (nfix (nth 1 cur)) (nfix (nth 2 cur))))
            (posp (mv-nth 0 (fn-ovr-quantum cur w cap nil fn-arena fn-cat))))
   :hints (("Goal" :in-theory (disable fn-ovr-quantum fn-ovrp-live fn-ovrp-ko5a-live fn-ovrp-quantum-open
                                fn-ovrp-quantum-open-b fn-ovr-frame-max fn-ovw-step fn-ovr-probes-within
                                fn-ovr-close-octets fn-ovrp-step1-len fn-ovrp-close-bound fn-ovrp-probe-len-le)
            :use ((:instance fn-ovrp-ko5a-live (fn-ovr-lease nil))
                              fn-ovrp-step1-len
                              (:instance fn-ovrp-probe-len-le (g (nth 0 cur)) (k (nfix (nth 1 cur)))
                                         (top (nfix (nth 2 cur))) (s (nth 6 cur)) (l l))
                              (:instance fn-ovrp-live-intro (fn-ovr-lease nil)))))))


(local
 (defthm fn-ovrp-ko7-pos-b
   (implies (and (fn-ovw-cursorp cur) (consp cur) (not (nth 7 cur))
                 (fn-cbor-octet-listp (nth 6 cur)) (unsigned-byte-p 59 cap)
                 (<= (+ (nfix l) (fn-ovr-frame-max)) (nfix cap))
                 (< (nfix (nth 2 cur)) (nfix (nth 1 cur))))
            (posp (mv-nth 0 (fn-ovr-quantum cur w cap nil fn-arena fn-cat))))
   :hints (("Goal" :use ((:instance fn-ovrp-close-bound (ow (nth 5 cur)) (lp (nth 4 cur)))
                         (:instance fn-ovrp-quantum-open-b (fn-ovr-lease nil))
                         (:instance fn-ovrp-live-intro (fn-ovr-lease nil)))
            :in-theory (e/d (fn-ovr-frame-max)
                            (fn-ovr-quantum fn-ovrp-live fn-ovrp-quantum-open fn-ovrp-quantum-open-b
                             fn-ovr-close-octets fn-ovrp-close-bound fn-ovrp-live-intro))))))

(local
 (defthm fn-ovrp-ko7-pos
   (implies (and (fn-ovw-cursorp cur) (consp cur) (not (nth 7 cur))
                 (fn-cbor-octet-listp (nth 6 cur)) (unsigned-byte-p 59 cap)
                 (fn-ovr-probes-within (nth 0 cur) (nfix (nth 1 cur)) (nfix (nth 2 cur)) (nth 6 cur)
                                       (nfix (nth 3 cur)) l fn-arena fn-cat)
                 (<= (+ (nfix l) (fn-ovr-frame-max)) (nfix cap)))
            (posp (mv-nth 0 (fn-ovr-quantum cur w cap nil fn-arena fn-cat))))
   :hints (("Goal" :cases ((<= (nfix (nth 1 cur)) (nfix (nth 2 cur))))
            :in-theory (disable fn-ovrp-ko7-pos-a fn-ovrp-ko7-pos-b fn-ovr-quantum fn-ovr-probes-within
                                fn-ovr-frame-max))
           ("Subgoal 2" :use fn-ovrp-ko7-pos-b)
           ("Subgoal 1" :use fn-ovrp-ko7-pos-a))))

;;; ---- p20
(local
 (defthm fn-ovrp-nx
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
   :hints (("Goal" :in-theory (e/d (fn-ovw-cursor) (fn-ovw-step fn-ovrp-ext-step fn-ovrp-step-at fn-ovrp-step-octets
                                                   fn-ovw-step-keeps-cursorp))
            :use (fn-ovrp-step-next fn-ovw-step-keeps-cursorp fn-ovrp-step-next-live
                  (:instance fn-ovrp-hi-ge-k (k (nfix (nth 1 cur))) (top (nfix (nth 2 cur))) (w n))
                  (:instance fn-ovrp-hi-int (k (nfix (nth 1 cur))) (top (nth 2 cur)) (w n)))))))

(local
 (defthm fn-ovrp-nx-all
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
            :in-theory (disable fn-ovrp-nx fn-ovrp-step-b fn-ovw-step fn-ovr-probes-within fn-ovrp-pw-mono))
           ("Subgoal 2" :use (:instance fn-ovrp-step-b))
           ("Subgoal 1" :use (fn-ovrp-nx
                              (:instance fn-ovrp-pw-mono (group (nth 0 cur)) (k (nfix (nth 1 cur)))
                                         (k2 (nfix (nth 1 (mv-nth 1 (fn-ovw-step cur n fn-arena fn-cat)))))
                                         (top (nfix (nth 2 cur))) (server (nth 6 cur)) (v (nfix (nth 3 cur)))))))))

(local
 (defun fn-ovrp-a (cur l cap fn-arena fn-cat)
   (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
   (and (fn-ovw-cursorp cur) (not (nth 7 cur))
        (fn-cbor-octet-listp (nth 6 cur)) (unsigned-byte-p 59 cap)
        (fn-ovr-probes-within (nth 0 cur) (nfix (nth 1 cur)) (nfix (nth 2 cur)) (nth 6 cur)
                              (nfix (nth 3 cur)) l fn-arena fn-cat)
        (<= (+ (nfix l) (fn-ovr-frame-max)) (nfix cap)))))

(local (in-theory (disable (:definition fn-ovrp-a))))

(local
 (defthm fn-ovrp-a-next
   (implies (and (fn-ovrp-a cur l cap fn-arena fn-cat) (consp cur)
                 (mv-nth 1 (fn-ovw-step cur n fn-arena fn-cat)))
            (fn-ovrp-a (mv-nth 1 (fn-ovw-step cur n fn-arena fn-cat)) l cap fn-arena fn-cat))
   :hints (("Goal" :in-theory (disable fn-ovrp-nx-all fn-ovrp-nx fn-ovrp-step-next fn-ovrp-step-octets fn-ovrp-step-at fn-ovrp-ext-step fn-ovw-step fn-ovr-frame-max fn-ovr-probes-within)
            :use (fn-ovrp-nx-all) :expand ((fn-ovrp-a cur l cap fn-arena fn-cat)
                                           (fn-ovrp-a (mv-nth 1 (fn-ovw-step cur n fn-arena fn-cat)) l cap fn-arena fn-cat))))))

(local
 (defthm fn-ovrp-a-pos
   (implies (and (fn-ovrp-a cur l cap fn-arena fn-cat) (consp cur))
            (posp (mv-nth 0 (fn-ovr-quantum cur w cap nil fn-arena fn-cat))))
   :hints (("Goal" :in-theory (disable fn-ovrp-ko7-pos fn-ovr-quantum fn-ovr-frame-max fn-ovr-probes-within)
            :use fn-ovrp-ko7-pos :expand ((fn-ovrp-a cur l cap fn-arena fn-cat))))))

(local
 (defthm fn-ovrp-a-cursorp
   (implies (fn-ovrp-a cur l cap fn-arena fn-cat) (fn-ovw-cursorp cur))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-ovrp-a)))))

(local
 (defthm fn-ovrp-run-ko7
   (implies (fn-ovrp-a cur l cap fn-arena fn-cat)
            (mv-nth 0 (fn-ovr-run cur w cap fn-ovr-lease fn-arena fn-cat)))
   :hints (("Goal" :induct (fn-ovr-run cur w cap fn-ovr-lease fn-arena fn-cat)
            :in-theory (e/d (fn-ovrp-q-next)
                            (fn-ovr-quantum fn-ovw-step fn-ovw-run fn-ovrp-canon fn-ovrp-a
                             fn-ovrp-step-octets fn-ovrp-step-next fn-ovrp-step-at fn-ovrp-ext-step
                             fn-ovrp-ko2-big fn-ovrp-ko2-small fn-ovrp-ko2-n))
            :expand ((fn-ovr-run cur w cap fn-ovr-lease fn-arena fn-cat)))
           (and stable-under-simplificationp
                '(:use ((:instance fn-ovrp-a-pos (l l))
                        (:instance fn-ovw-step-progresses (w (mv-nth 0 (fn-ovr-quantum cur w cap nil fn-arena fn-cat))))
                        (:instance fn-ovrp-q-live-consp (l nil))))))))

;;; ---- p21
(defthm fn-ovr-run-progresses
  (implies (and (fn-ovw-cursorp cur) (not (nth 7 cur)) (fn-cbor-octet-listp (nth 6 cur))
                (unsigned-byte-p 59 cap)
                (fn-ovr-probes-within (nth 0 cur) (nfix (nth 1 cur)) (nfix (nth 2 cur)) (nth 6 cur)
                                      (nfix (nth 3 cur)) l fn-arena fn-cat)
                (<= (+ (nfix l) (fn-ovr-frame-max)) (nfix cap)))
           (mv-nth 0 (fn-ovr-run cur w cap fn-ovr-lease fn-arena fn-cat)))
  :hints (("Goal" :use fn-ovrp-run-ko7 :in-theory (e/d (fn-ovrp-a) (fn-ovrp-run-ko7 fn-ovr-run fn-ovr-frame-max fn-ovr-probes-within)))))

