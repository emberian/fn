; fn: the log walk decodes each record once (lane snapshot-open-3,
; 2026-09-27).  Prefix `fn-lgb-', as books/store-log-buffer.lisp (and the stream's
; `fn-lgw-' names it adds:
; fn-lgw-set-next, fn-lgw-step-nf, fn-lgw-step-buf-nf, fn-lgw-run-nf).
;
; books/store-log-buffer.lisp walks the log over an octet buffer; its step
; still folds each record's txid into the stream's NEXT (fn-lgw-next-fold:
; fn-lgt-txid decodes the whole record), and the full replay then decodes
; every record again (fn-srs-decode): at 100k x 2 KiB the fold was 4.4 s of
; a 31.9 s open (planning/evidence/snapshot-open-3-2026-09-27.md section 3).
; Here the full replay walks with a step that keeps NEXT and takes the fold
; from its one decode of each record.

(in-package "ACL2")
(include-book "store-log-buffer")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; The walk without its txid fold, and the fold from the replay's decode.
;
; The step folds each record's txid into the stream's NEXT
; (fn-lgw-next-fold: fn-lgt-txid decodes the whole record), and the full
; replay decodes every record again (fn-srs-decode).  Here the host's full
; replay walks with fn-lgw-step-buf-nf, which keeps NEXT, and takes the fold
; from its one decode of each record (fn-lgb-decode-next: the replay's
; events and the fold, EQUAL to fn-srs-decode and fn-lgw-next-fold, one
; fn-record-decode-exact per article record); at the segment's end it sets
; the stream's NEXT to the fold (fn-lgw-set-next).  KEYSTONE
; fn-lgw-run-nf-then-fold-is-run: the run without the fold, its NEXT then set
; to the fold of the records it emitted, IS fn-lgw-run (so PRF-297's
; fn-lgw-run-is-the-open holds of the host's composition), and the fold of
; the records over any chunking is the fold of their concatenation
; (fn-lgw-next-fold-of-append).  Host: host/native/io.lisp
; fnn-log-stream-segment under *fnn-log-stream-finish* (the full replay).

(defun fn-lgw-set-next (st next)
  (declare (xargs :guard (true-listp st)))
  (fn-lgw-make (fn-lgw-pos st) (fn-lgw-prev st) (fn-lgw-count st) (nfix next)
               (fn-lgw-stop st) (fn-lgw-broken st)))

; The list step with NEXT kept: the logic of the host's step.
(defun fn-lgw-step-nf (e st unit max extent)
  (declare (xargs :guard (true-listp st) :verify-guards nil))
  (mv-let (took records st2) (fn-lgw-step e st unit max extent)
    (mv took records (fn-lgw-set-next st2 (fn-lgw-next st)))))

(defun fn-lgw-step-buf-nf (st unit max extent fn-octets)
  (declare (xargs :stobjs fn-octets :guard (true-listp st)))
  (let ((pos (fn-lgw-pos st)) (prev (fn-lgw-prev st))
        (count (fn-lgw-count st)) (next (fn-lgw-next st)))
    (cond ((fn-lgw-stop st) (mv nil nil (fn-lgw-set-next st next)))
          (t (mv-let (ok records) (fn-lgb-decide prev max fn-octets)
               (if (not ok)
                   (mv nil nil (fn-lgw-make pos prev count next t
                                            (fn-lgw-broken-slice-p (fn-octets-list fn-octets)
                                                                   prev max)))
                 (let* ((n (fn-octets-len fn-octets))
                        (step (+ n (fn-lg-pad-len n unit)))
                        (last (fn-lgb-trailer fn-octets)))
                   (mv t records
                       (fn-lgw-make (+ pos step) last (+ count (len records)) next
                                    (not (< (+ pos step) (nfix extent))) nil)))))))))

; The host's step is the list step with NEXT kept, no hypothesis.
(defthm fn-lgw-step-buf-nf-is-step-nf
  (equal (fn-lgw-step-buf-nf st unit max extent fn-octets)
         (fn-lgw-step-nf fn-octets st unit max extent))
  :hints (("Goal" :in-theory (e/d (fn-lgw-step fn-lgw-set-next)
                                  (fn-lgw-decide fn-lg-trailer fn-lgw-broken-slice-p
                                   fn-lgw-next-fold fn-lg-pad-len
                                   fn-lgw-decide-is-okp-and-records fn-lg-entry-okp
                                   fn-lg-open-bound true-listp)))))

(defun fn-lgw-run-nf (c st unit max)
  (declare (xargs :measure (nfix (- (len c) (fn-lgw-pos st)))
                  :verify-guards nil
                  :hints (("Goal" :in-theory (e/d (fn-lgw-step-nf fn-lgw-set-next)
                                                  (fn-lgw-step fn-lgw-window))))))
  (mv-let (took records st2) (fn-lgw-step-nf (fn-lgw-window c st) st unit max (len c))
    (if (and took (not (fn-lgw-stop st2)) (< (fn-lgw-pos st2) (len c)))
        (mv-let (rest st3) (fn-lgw-run-nf c st2 unit max)
          (mv (append records rest) st3))
      (mv (if took records nil) st2))))

(local
 (defthm fn-lgb-set-next-fields
   (and (equal (fn-lgw-pos (fn-lgw-set-next st n)) (fn-lgw-pos st))
        (equal (fn-lgw-prev (fn-lgw-set-next st n)) (fn-lgw-prev st))
        (equal (fn-lgw-count (fn-lgw-set-next st n)) (fn-lgw-count st))
        (equal (fn-lgw-next (fn-lgw-set-next st n)) (nfix n))
        (equal (fn-lgw-stop (fn-lgw-set-next st n)) (fn-lgw-stop st))
        (equal (fn-lgw-broken (fn-lgw-set-next st n)) (fn-lgw-broken st)))
   :hints (("Goal" :in-theory (enable fn-lgw-set-next)))))

; The step's NEXT is the fold of the records it took over the NEXT it was
; given, and the rest of its state does not read NEXT.
(local
 (defthm fn-lgb-step-of-set-next
   (equal (fn-lgw-step e (fn-lgw-set-next st n) unit max extent)
          (mv-let (took records st2) (fn-lgw-step e st unit max extent)
            (mv took records
                (if took
                    (fn-lgw-set-next st2 (fn-lgw-next-fold records (nfix n)))
                  (fn-lgw-set-next st2 (nfix n))))))
   :hints (("Goal" :in-theory (e/d (fn-lgw-step fn-lgw-set-next)
                                   (fn-lgw-decide fn-lg-trailer fn-lgw-broken-slice-p
                                    fn-lgw-next-fold fn-lg-pad-len
                                    fn-lgw-decide-is-okp-and-records fn-lg-entry-okp
                                    fn-lg-open-bound true-listp))))))

(in-theory (disable fn-lgw-set-next))

(local
 (defthm fn-lgb-header-len-of-set-next
   (equal (fn-lgw-header-len (fn-lgw-set-next st m) extent) (fn-lgw-header-len st extent))
   :hints (("Goal" :in-theory (enable fn-lgw-header-len)))))

(local
 (defthm fn-lgb-entry-len-of-set-next
   (equal (fn-lgw-entry-len h (fn-lgw-set-next st m) extent) (fn-lgw-entry-len h st extent))
   :hints (("Goal" :in-theory (e/d (fn-lgw-entry-len) (fn-lg-declared-len))))))

(local
 (defthm fn-lgb-window-of-set-next
   (equal (fn-lgw-window c (fn-lgw-set-next st m)) (fn-lgw-window c st))
   :hints (("Goal" :in-theory (e/d (fn-lgw-window)
                                   (fn-lgw-header-len fn-lgw-entry-len fn-bs-take nthcdr len))))))

(local
 (defthm fn-lgb-set-next-set-next
   (equal (fn-lgw-set-next (fn-lgw-set-next st a) b) (fn-lgw-set-next st b))
   :hints (("Goal" :in-theory (enable fn-lgw-set-next)))))

(local
 (defthm fn-lgb-set-next-of-nfix
   (equal (fn-lgw-set-next st (nfix n)) (fn-lgw-set-next st n))
   :hints (("Goal" :in-theory (enable fn-lgw-set-next)))))

(local
 (defthm fn-lgb-next-fold-of-non-natural
   (implies (not (natp n))
            (equal (fn-lgw-next-fold records n) (fn-lgw-next-fold records 0)))
   :hints (("Goal" :in-theory (disable fn-lgw-next-fold-of-nfix)
            :use ((:instance fn-lgw-next-fold-of-nfix))))))

(local
 (defun fn-lgb-run-ind (c st m unit max)
   (declare (xargs :measure (nfix (- (len c) (fn-lgw-pos st)))
                   :verify-guards nil
                   :hints (("Goal" :in-theory (e/d (fn-lgw-step-nf fn-lgw-set-next)
                                                   (fn-lgw-step fn-lgw-window))))))
   (mv-let (took records st2) (fn-lgw-step-nf (fn-lgw-window c st) st unit max (len c))
     (if (and took (not (fn-lgw-stop st2)) (< (fn-lgw-pos st2) (len c)))
         (fn-lgb-run-ind c st2 (fn-lgw-next-fold records m) unit max)
       (list c st m unit max)))))

; The run from a state whose NEXT is M is the run without the fold, its
; NEXT set to the fold of the records it emitted over M.
(defthm fn-lgw-run-of-set-next-is-run-nf
  (equal (fn-lgw-run c (fn-lgw-set-next st m) unit max)
         (mv-let (records st2) (fn-lgw-run-nf c st unit max)
           (mv records (fn-lgw-set-next st2 (fn-lgw-next-fold records m)))))
  :hints (("Goal" :induct (fn-lgb-run-ind c st m unit max)
           :in-theory (e/d (fn-lgw-step-nf)
                           (fn-lgw-step fn-lgw-window fn-lgw-next-fold
                            fn-lgw-next-fold-is-next-after nfix fn-lgw-window-is-the-slice
                            fn-lgw-slice-when-not-declared fn-lg-declared-len true-listp
                            fn-lgc-take-all
                            fn-cbor-octet-listp))
           :expand ((fn-lgw-run c (fn-lgw-set-next st m) unit max)
                    (fn-lgw-run-nf c st unit max)))))

; KEYSTONE: from the stream's start, the run without the fold, its NEXT then
; set to the fold of the records it emitted over the start's NEXT, IS
; fn-lgw-run -- so fn-lgw-run-is-the-open (PRF-297) is the host's
; composition's.
(defthm fn-lgw-run-nf-then-fold-is-run
  (equal (fn-lgw-run c (fn-lgw-start genesis floor) unit max)
         (mv-let (records st2) (fn-lgw-run-nf c (fn-lgw-start genesis floor) unit max)
           (mv records (fn-lgw-set-next st2 (fn-lgw-next-fold records floor)))))
  :hints (("Goal" :use ((:instance fn-lgw-run-of-set-next-is-run-nf
                                   (st (fn-lgw-start genesis floor)) (m floor)))
           :in-theory (e/d (fn-lgw-set-next fn-lgw-start)
                           (fn-lgw-run-of-set-next-is-run-nf fn-lgw-run fn-lgw-run-nf)))))

; The replay's decode and the walk's fold in one pass: each record decoded
; once by the codec (fn-record-decode-exact), its txid read from that
; decode (fn-lgt-txid's reading), its event the article record when the
; codec accepts it (fn-store-event-decode-exact's first answer) and
; fn-store-event-decode-exact's otherwise.
(defun fn-lgb-decode-one (r)
  (declare (xargs :guard t))
  (let* ((legacy (fn-record-decode-exact r))
         (txid (if (fn-record-parse-okp legacy)
                   (ec-call (fn-record-txid (fn-record-parse-value legacy)))
                 nil))
         (decoded (if (fn-record-result-okp legacy) legacy
                    (ec-call (fn-store-event-decode-exact r)))))
    ;; An accepted article record is a record (the seam's
    ;; fn-record-decode-exact-yields-a-record), so a wire event: its
    ;; recognizer is not run again on it.
    (mv (if (fn-record-result-okp legacy)
            (fn-record-result-record legacy)
          (if (and (consp decoded) (equal (car decoded) :ok) (consp (cdr decoded))
                   (fn-rcon-wire-event-p (car (cdr decoded))))
              (car (cdr decoded))
            :bad))
        txid)))

(local
 (defthm fn-lgb-event-decode-of-legacy
   (implies (fn-record-result-okp (fn-record-decode-exact r))
            (equal (fn-store-event-decode-exact r) (fn-record-decode-exact r)))
   :hints (("Goal" :expand ((fn-store-event-decode-exact r))
            :in-theory (disable fn-record-result-okp)))))

(local
 (defthm fn-lgb-legacy-is-a-wire-event
   (implies (fn-record-result-okp (fn-record-decode-exact r))
            (and (consp (fn-record-decode-exact r))
                 (equal (car (fn-record-decode-exact r)) :ok)
                 (consp (cdr (fn-record-decode-exact r)))
                 (fn-rcon-wire-event-p (car (cdr (fn-record-decode-exact r))))
                 (fn-wire-event-p (car (cdr (fn-record-decode-exact r))))
                 (equal (fn-record-result-record (fn-record-decode-exact r))
                        (car (cdr (fn-record-decode-exact r))))))
   :hints (("Goal" :in-theory (e/d (fn-rcon-wire-event-p-is-wire-event-p fn-wire-event-p
                                    fn-record-result-record fn-record-result-okp fn-cbor-ag-car)
                                   (fn-rcon-wire-event-p fn-record-p
                                    fn-record-decode-exact-yields-a-record))
            :use ((:instance fn-record-decode-exact-yields-a-record (octets r)))))))

(local
 (defthm fn-lgb-decode-one-is-decode-and-txid
   (equal (fn-lgb-decode-one r)
          (let ((decoded (fn-store-event-decode-exact r)))
            (mv (if (and (consp decoded) (equal (car decoded) :ok) (consp (cdr decoded))
                         (fn-rcon-wire-event-p (car (cdr decoded))))
                    (car (cdr decoded))
                  :bad)
                (fn-lgt-txid r))))
   :hints (("Goal" :cases ((fn-record-result-okp (fn-record-decode-exact r)))
            :in-theory (e/d (fn-lgt-txid)
                            (fn-rcon-wire-event-p fn-record-txid fn-store-event-decode-exact
                             fn-record-result-okp fn-record-result-record))))))

(in-theory (disable fn-lgb-decode-one))

; Executes by a loop (lane depth-debt, PRF-919): the recursion took one
; control-stack frame per element of data with no fixed cap.  The :logic is
; the recursion, unchanged; the :exec is the loop, equal by the lemma below.
; BADP says an event so far was :bad; the txid fold runs to the end as the
; recursion's did.
(defun fn-lgb-decode-next-exec-loop (rs next acc badp)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp rs)
      (mv-let (event txid) (fn-lgb-decode-one (car rs))
        (fn-lgb-decode-next-exec-loop (cdr rs) (max (1+ (nfix txid)) (nfix next))
                                      (cons event acc) (or badp (eq event :bad))))
    (mv (if (or badp (not (null rs))) :bad (fn-ag-rev-onto acc nil)) (nfix next))))

(defun fn-lgb-decode-next-exec (rs next)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
  (if (consp rs)
      (mv-let (event txid) (fn-lgb-decode-one (car rs))
        (mv-let (rest n2)
          (fn-lgb-decode-next-exec (cdr rs) (max (1+ (nfix txid)) (nfix next)))
          (mv (if (or (eq event :bad) (equal rest :bad)) :bad (cons event rest)) n2)))
    (mv (if (null rs) nil :bad) (nfix next)))
  :exec (mv-let (r n) (fn-lgb-decode-next-exec-loop rs next nil nil) (mv r n))))

; Its two answers are the replay's decode and the walk's fold.
(defthm fn-lgb-decode-next-exec-fold
  (equal (mv-nth 1 (fn-lgb-decode-next-exec rs next)) (fn-lgw-next-fold rs next))
  :hints (("Goal" :induct (fn-lgb-decode-next-exec rs next)
           :in-theory (e/d (fn-lgw-next-after-one)
                           (fn-store-event-decode-exact fn-rcon-wire-event-p fn-lgt-txid
                            fn-lgw-next-fold-is-next-after)))))

(defthm fn-lgb-decode-next-exec-decode
  (equal (mv-nth 0 (fn-lgb-decode-next-exec rs next)) (fn-srs-decode rs))
  :hints (("Goal" :induct (fn-lgb-decode-next-exec rs next)
           :in-theory (disable fn-store-event-decode-exact fn-rcon-wire-event-p fn-lgt-txid))))

(defthm fn-lgb-decode-next-exec-loop-next
  (equal (mv-nth 1 (fn-lgb-decode-next-exec-loop rs next acc badp))
         (mv-nth 1 (fn-lgb-decode-next-exec rs next)))
  :hints (("Goal" :induct (fn-lgb-decode-next-exec-loop rs next acc badp)
                  :in-theory (union-theories '(fn-lgb-decode-next-exec-loop fn-lgb-decode-next-exec mv-nth
                                                car-cons cdr-cons)
                                              (union-theories (theory 'minimal-theory)
                                                              (executable-counterpart-theory :here))))))

(defthm fn-lgb-decode-next-exec-loop-is-rev-onto
  (equal (mv-nth 0 (fn-lgb-decode-next-exec-loop rs next acc badp))
         (let ((r (mv-nth 0 (fn-lgb-decode-next-exec rs next))))
           (if (or badp (equal r :bad)) :bad (fn-ag-rev-onto acc r))))
  :hints (("Goal" :induct (fn-lgb-decode-next-exec-loop rs next acc badp)
                  :in-theory (union-theories '(fn-lgb-decode-next-exec-loop fn-lgb-decode-next-exec mv-nth
                                                car-cons cdr-cons fn-ag-rev-onto)
                                              (union-theories (theory 'minimal-theory)
                                                              (executable-counterpart-theory :here))))))

(verify-guards fn-lgb-decode-next-exec-loop)
(verify-guards fn-lgb-decode-next-exec
  :hints (("Goal" :expand ((fn-lgb-decode-next-exec rs next))
                  :in-theory (union-theories
                              '(mv-nth car-cons cdr-cons fn-ag-rev-onto
                                fn-lgb-decode-next-exec-loop-next
                                fn-lgb-decode-next-exec-loop-is-rev-onto)
                              (union-theories (theory 'minimal-theory)
                                              (executable-counterpart-theory :here))))))

; The host's call (host/native/io.lisp fnn-recover-log-stream-flush): the
; chunk's events (fn-srs-decode) and the fold of its records' txids over
; NEXT (fn-lgw-next-fold), from one decode of each record.
(defun fn-lgb-decode-next (rs next)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (union-theories
                                                    '(fn-lgb-decode-next-exec-fold
                                                      fn-lgb-decode-next-exec-decode
                                                      car-cons cdr-cons mv-nth zp)
                                                    (theory 'minimal-theory))))))
  (mbe :logic (mv (fn-srs-decode rs) (fn-lgw-next-fold rs next))
       :exec (mv-let (events n2) (fn-lgb-decode-next-exec rs next)
               (mv events n2))))
