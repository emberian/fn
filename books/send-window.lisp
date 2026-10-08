; Observed send-window admission, item LOAD-F5-SLOW-READER-ISOLATION.
; Statement: with one writer, exact NOTSENT observations before each render,
; and render quanta <= Q, NOTSENT + PENDING < W + Q at every legal prefix.
; A reader with no transmissions therefore causes < W + Q total rendering.
;
; TCP_NOTSENT_LOWAT controls writable notification, NOT acceptance of eager
; nonblocking writes. Train 51 on hbox refuted the former book's premise.
; The host now reads SIOCOUTQNSD, and fn-send-window-render-p admits rendering
; only below W. No decision about the queue size is made by host Lisp.
; :render requires empty PENDING and admission; :write moves any prefix of
; PENDING into NOTSENT; :transmit removes a prefix of NOTSENT. Between the
; observation and rendering the sole socket writer cannot increase NOTSENT.
; Q must include transport expansion (TLS/compression) for a wire-byte claim;
; this arithmetic model does not prove those facilities or the ioctl ABI.
; GATEP nil exhibits the old eager writer: no finite render-ahead bound.

(in-package "ACL2")
(include-book "profile-limits")
(include-book "defkeystone")

(defconst *fn-sw-window* (fn-profile-limit :send-window-octets))

; The profile value also supplies the POLLOUT wakeup threshold.
(defun fn-send-window-octets ()
  (declare (xargs :guard t))
  *fn-sw-window*)

(defun fn-sw-render-p (notsent w)
  (declare (xargs :guard (and (natp notsent) (natp w))))
  (< notsent w))

; The host supplies SIOCOUTQNSD immediately before rendering a quantum.
(defun fn-send-window-render-p (notsent)
  (declare (xargs :guard (natp notsent)))
  (fn-sw-render-p notsent (fn-send-window-octets)))

(defthm fn-send-window-render-p-by-definition
  (equal (fn-send-window-render-p notsent)
         (fn-sw-render-p notsent (fn-send-window-octets))))

; State: (NOTSENT PENDING RENDERED TRANSMITTED).
(defun fn-sw-statep (st)
  (declare (xargs :guard t))
  (and (true-listp st) (equal (len st) 4)
       (natp (nth 0 st)) (natp (nth 1 st)) (natp (nth 2 st)) (natp (nth 3 st))))

(defconst *fn-sw-start* '(0 0 0 0))

(defun fn-sw-step (st ev w q gatep)
  (declare (xargs :guard (and (fn-sw-statep st) (natp w) (natp q))))
  (let ((notsent (nth 0 st)) (pending (nth 1 st))
        (rendered (nth 2 st)) (transmitted (nth 3 st))
        (kind (and (consp ev) (car ev)))
        (n (and (consp ev) (consp (cdr ev)) (cadr ev))))
    (cond ((not (posp n)) nil)
          ((eq kind :render)
           (and (equal pending 0) (<= n q)
                (or (not gatep) (fn-sw-render-p notsent w))
                (list notsent n (+ rendered n) transmitted)))
          ((eq kind :write)
           (and (<= n pending)
                (list (+ notsent n) (- pending n) rendered transmitted)))
          ((eq kind :transmit)
           (and (<= n notsent)
                (list (- notsent n) pending rendered (+ transmitted n))))
          (t nil))))

; The state after EVS, or NIL when an event is not legal where it stands.
(defun fn-sw-run (st evs w q gatep)
  (declare (xargs :guard (and (fn-sw-statep st) (natp w) (natp q))
                  :measure (acl2-count evs)))
  (if (atom evs)
      st
    (let ((next (fn-sw-step st (car evs) w q gatep)))
      (and next (fn-sw-run next (cdr evs) w q gatep)))))

(defun fn-sw-no-transmit-p (evs)
  (declare (xargs :guard t))
  (if (atom evs)
      t
    (and (not (and (consp (car evs)) (eq (car (car evs)) :transmit)))
         (fn-sw-no-transmit-p (cdr evs)))))

; What a reachable state satisfies: the pending window is one window at most,
; NOTSENT + PENDING is below W + Q. Render admission tests the observation;
; writes merely move octets between the two, and transmission decreases it.
(defun fn-sw-inv (st w q)
  (declare (xargs :guard t))
  (and (fn-sw-statep st) (natp w) (posp q)
       (<= (nth 1 st) q)
       (< (+ (nth 0 st) (nth 1 st)) (+ w q))
       (equal (nth 2 st) (+ (nth 0 st) (nth 1 st) (nth 3 st)))))

(defthm fn-sw-step-keeps-inv
  (implies (and (fn-sw-inv st w q) (fn-sw-step st ev w q t))
           (fn-sw-inv (fn-sw-step st ev w q t) w q))
  :hints (("Goal" :in-theory (enable fn-sw-step fn-sw-inv fn-sw-statep))))

(defthm fn-sw-run-keeps-inv
  (implies (and (fn-sw-inv st w q) (fn-sw-run st evs w q t))
           (fn-sw-inv (fn-sw-run st evs w q t) w q))
  :hints (("Goal" :in-theory (disable fn-sw-inv fn-sw-step)
                  :induct (fn-sw-run st evs w q t))))

(defthm fn-sw-start-inv
  (implies (and (natp w) (posp q)) (fn-sw-inv *fn-sw-start* w q))
  :hints (("Goal" :in-theory (enable fn-sw-inv fn-sw-statep))))

; Trace lemma.  Rendered and not transmitted stays under W + Q, at the end of
; every legal trace and so at every prefix of one.
(defthm fn-sw-buffered-bounded
  (implies (and (natp w) (posp q)
                (fn-sw-run *fn-sw-start* evs w q t))
           (let ((st (fn-sw-run *fn-sw-start* evs w q t)))
             (< (+ (nth 0 st) (nth 1 st)) (+ w q))))
  :hints (("Goal" :use ((:instance fn-sw-run-keeps-inv (st *fn-sw-start*))
                        (:instance fn-sw-start-inv))
           :in-theory (e/d (fn-sw-inv) (fn-sw-run-keeps-inv fn-sw-start-inv))))
  :rule-classes nil)

(defthm fn-sw-no-transmit-no-transmitted
  (implies (and (fn-sw-no-transmit-p evs) (fn-sw-run st evs w q gatep)
                (equal (nth 3 st) 0))
           (equal (nth 3 (fn-sw-run st evs w q gatep)) 0))
  :hints (("Goal" :in-theory (enable fn-sw-step)
                  :induct (fn-sw-run st evs w q gatep))))

; Trace lemma.  A reader that transmits nothing: the owner renders under W + Q
; octets in all, however long the reply.
(defthm fn-sw-stalled-reader-bounded
  (implies (and (natp w) (posp q)
                (fn-sw-no-transmit-p evs)
                (fn-sw-run *fn-sw-start* evs w q t))
           (< (nth 2 (fn-sw-run *fn-sw-start* evs w q t)) (+ w q)))
  :hints (("Goal" :use ((:instance fn-sw-run-keeps-inv (st *fn-sw-start*))
                        (:instance fn-sw-start-inv)
                        (:instance fn-sw-no-transmit-no-transmitted (st *fn-sw-start*) (gatep t)))
           :in-theory (e/d (fn-sw-inv) (fn-sw-run-keeps-inv fn-sw-no-transmit-no-transmitted
                                        fn-sw-start-inv fn-sw-run))))
  :rule-classes nil)

 ; The deployed admission decision bounds the next rendered quantum.
(defthm fn-send-window-render-p-bounds-the-quantum
  (implies (and (and (natp notsent) (natp n) (natp q) (<= n q))
                (fn-send-window-render-p notsent))
           (< (+ notsent n) (+ (fn-send-window-octets) q)))
  :rule-classes nil)

(defteeth fn-send-window-render-p-bounds-the-quantum
  :claim (((quantum (and (natp notsent) (natp n) (natp q) (<= n q)))
           (admitted (fn-send-window-render-p notsent)))
          (< (+ notsent n) (+ (fn-send-window-octets) q)))
  :subject fn-send-window-render-p
  :witness ((notsent 65535) (n 16384) (q 16384))
  :breaks ((quantum ((notsent 65535) (n 2) (q 0)))
           (admitted ((notsent 65536) (n 16384) (q 16384))))
  :mutations ((ignore-quantum (:conclusion (< (+ notsent n) (fn-send-window-octets)))
               ((notsent 65535) (n 16384) (q 16384))
               :fault "An admitted render quantum may cross the notification threshold.")))

; ---- teeth: the full legal trace and a removed admission gate ----
(defun fn-sw-ten-windows ()
  (declare (xargs :guard t))
  '((:render 4) (:write 4) (:render 4) (:write 4) (:render 4) (:write 4)
    (:render 4) (:write 4) (:render 4) (:write 4) (:render 4) (:write 4)
    (:render 4) (:write 4) (:render 4) (:write 4) (:render 4) (:write 4)
    (:render 4) (:write 4)))

(defthm fn-sw-observed-render-admission-bounds
  (implies (and (and (natp w) (posp q)
                     (fn-sw-run *fn-sw-start* evs w q gatep))
                (equal gatep t))
           (< (+ (nth 0 (fn-sw-run *fn-sw-start* evs w q gatep))
                 (nth 1 (fn-sw-run *fn-sw-start* evs w q gatep)))
              (+ w q)))
  :hints (("Goal" :use fn-sw-buffered-bounded
           :in-theory (disable fn-sw-run)))
  :rule-classes nil)

(defteeth fn-sw-observed-render-admission-bounds
  :claim (((legal (and (natp w) (posp q)
                       (fn-sw-run *fn-sw-start* evs w q gatep)))
           (admission (equal gatep t)))
          (< (+ (nth 0 (fn-sw-run *fn-sw-start* evs w q gatep))
                (nth 1 (fn-sw-run *fn-sw-start* evs w q gatep))) (+ w q)))
  :subject fn-send-window-render-p
  :witness ((w 6) (q 4) (gatep t)
            (evs '((:render 4) (:write 4) (:render 4))))
  :breaks ((legal ((w 0) (q 0) (gatep t) (evs nil)))
           (admission ((w 6) (q 4) (gatep nil) (evs (fn-sw-ten-windows)))))
  :mutations ((no-overshoot (:conclusion
                            (<= (+ (nth 0 (fn-sw-run *fn-sw-start* evs w q gatep))
                                   (nth 1 (fn-sw-run *fn-sw-start* evs w q gatep))) w))
               ((w 6) (q 4) (gatep t) (evs '((:render 4) (:write 4) (:render 4))))
               :fault "Dropping the last admitted quantum understates retained bytes.")))

(defthm fn-sw-observed-stalled-reader-bounded
  (implies (and (and (natp w) (posp q)
                     (fn-sw-run *fn-sw-start* evs w q gatep))
                (equal gatep t)
                (fn-sw-no-transmit-p evs))
           (< (nth 2 (fn-sw-run *fn-sw-start* evs w q gatep)) (+ w q)))
  :hints (("Goal" :use fn-sw-stalled-reader-bounded
           :in-theory (disable fn-sw-run fn-sw-no-transmit-p)))
  :rule-classes nil)

(defteeth fn-sw-observed-stalled-reader-bounded
  :claim (((legal (and (natp w) (posp q)
                       (fn-sw-run *fn-sw-start* evs w q gatep)))
           (admission (equal gatep t))
           (stopped (fn-sw-no-transmit-p evs)))
          (< (nth 2 (fn-sw-run *fn-sw-start* evs w q gatep)) (+ w q)))
  :subject fn-send-window-render-p
  :witness ((w 6) (q 4) (gatep t) (evs '((:render 4) (:write 4) (:render 4))))
  :breaks ((legal ((w 0) (q 0) (gatep t) (evs nil)))
           (admission ((w 6) (q 4) (gatep nil) (evs (fn-sw-ten-windows))))
           (stopped ((w 6) (q 4) (gatep t)
                     (evs '((:render 4) (:write 4) (:transmit 4)
                            (:render 4) (:write 4) (:transmit 4) (:render 4))))))
  :mutations ((omit-last-render (:conclusion
                                (<= (nth 2 (fn-sw-run *fn-sw-start* evs w q gatep)) w))
               ((w 6) (q 4) (gatep t) (evs '((:render 4) (:write 4) (:render 4))))
               :fault "The last admitted quantum remains rendered with a stopped reader.")))

(defthm fn-sw-admission-refuses-render-at-window
  (and (not (fn-send-window-render-p (fn-send-window-octets)))
       (not (fn-sw-run *fn-sw-start*
                       '((:render 4) (:write 4) (:render 4) (:write 4) (:render 4)) 6 4 t))
       (equal (fn-sw-run *fn-sw-start* (fn-sw-ten-windows) 6 4 nil) '(40 0 40 0)))
  :rule-classes nil)

(defteeth-check)
