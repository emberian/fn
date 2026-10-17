; Actual query render facade. Existing OVER/NEWNEWS theorems retain their
; fn-splan subject; LIST adds a distinct residual/availability boundary here:
; fn-qplan-cw-drain-is-a-prefix (windows and quanta write a prefix of what
; the plan owes, LIST cursors read as fn-lst-remaining).
; Plan representation and cold/output custody remain identical.
(in-package "ACL2")
(include-book "served-plan-cursor")
(include-book "list-metadata-cursor")

(local (in-theory (disable (tau-system))))

(defun fn-qplan-cursor-effectp (effect)
  (declare (xargs :guard t))
  (or (fn-splan-cursor-effectp effect) (fn-lst-effectp effect)))

(defun fn-qplan-rest-donep (rest)
  (declare (xargs :guard t))
  (if (consp rest)
      (and (not (fn-qplan-cursor-effectp (car rest)))
           (atom (fn-srb-effect-octets (car rest)))
           (fn-qplan-rest-donep (cdr rest)))
    t))

(defun fn-qplan-donep (plan)
  (declare (xargs :guard t))
  (and (atom (fn-splan-cur plan)) (fn-qplan-rest-donep (fn-splan-rest plan))))

(defun fn-qplan-rest-at-cursorp (rest)
  (declare (xargs :guard t))
  (if (consp rest)
      (cond ((fn-qplan-cursor-effectp (car rest)) t)
            ((consp (fn-srb-effect-octets (car rest))) nil)
            (t (fn-qplan-rest-at-cursorp (cdr rest))))
    nil))

(defun fn-qplan-at-cursorp (plan)
  (declare (xargs :guard t))
  (and (atom (fn-splan-cur plan))
       (fn-qplan-rest-at-cursorp (fn-splan-rest plan))))

(defun fn-qplan-rest-head-len (rest)
  (declare (xargs :guard t))
  (if (consp rest)
      (cond ((fn-qplan-cursor-effectp (car rest)) 0)
            ((consp (fn-srb-effect-octets (car rest)))
             (len (fn-srb-effect-octets (car rest))))
            (t (fn-qplan-rest-head-len (cdr rest))))
    0))

(defun fn-qplan-window-size (plan)
  (declare (xargs :guard t))
  (if (consp (fn-splan-cur plan)) (len (fn-splan-cur plan))
    (fn-qplan-rest-head-len (fn-splan-rest plan))))

(defun fn-qplan-window (plan w fn-octets)
  (declare (xargs :stobjs fn-octets :guard (natp w)))
  (if (fn-qplan-at-cursorp plan)
      (let ((fn-octets (fn-octets-clear fn-octets)))
        (mv :cursor plan fn-octets))
    ; Stop within the current materialized effect. This prevents the legacy
    ; fill loop from passing a new LIST tag and shares its actual buffer code.
    (fn-splan-window plan (min w (fn-qplan-window-size plan)) fn-octets)))

; Exactly one accepted LIST controller call per activation. Empty progress
; retains the cursor and response capture; no warmth-based completion.
(defun fn-qplan-rest-cursor-step (rest w fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (natp w)))
  (if (consp rest)
      (cond
       ((fn-lst-effectp (car rest))
        (mv-let (octets next calls state)
          (fn-lst-step (fn-cur-at 1 (car rest)) w w fn-cat)
          (declare (ignore calls state))
          (mv :ok (cons (fn-nntp-reply-effect octets)
                        (if (fn-lst-livep next)
                            (cons (fn-lst-effect next) (cdr rest))
                          (cdr rest))))))
       ((fn-splan-cursor-effectp (car rest))
        (fn-splan-rest-cursor-step rest w fn-arena fn-cat))
       (t (mv-let (status next)
            (fn-qplan-rest-cursor-step (cdr rest) w fn-arena fn-cat)
            (mv status (cons (car rest) next)))))
    (mv :ok rest)))

(defun fn-qplan-cursor-step (plan w fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (natp w)))
  (mv-let (status next)
    (fn-qplan-rest-cursor-step (fn-splan-rest plan) w fn-arena fn-cat)
    (mv status (cons (fn-splan-cur plan) next))))

(in-theory (disable fn-qplan-cursor-effectp fn-qplan-rest-donep fn-qplan-donep
                    fn-qplan-rest-at-cursorp fn-qplan-at-cursorp fn-qplan-rest-head-len
                    fn-qplan-window-size fn-qplan-window
                    fn-qplan-rest-cursor-step fn-qplan-cursor-step))

; -----------------------------------------------------------------------------
; What a query plan owes with every cursor read as its completion: LIST
; cursors by fn-lst-remaining, OVER/NEWNEWS cursors exactly as the existing
; served-plan list model reads them. Logical only.
(defun-nx fn-qplan-cw-octets (rest wl fn-arena fn-cat)
  (if (consp rest)
      (append (cond ((fn-lst-effectp (car rest))
                     (fn-lst-remaining (fn-cur-at 1 (car rest)) fn-cat))
                    ((fn-splan-cursor-effectp (car rest))
                     (if (fn-nnw-meta-effectp (car rest))
                         (fn-nnw-stream-remaining (car (cdr (car rest))) fn-arena fn-cat)
                       (fn-ovw-run (car (cdr (car rest))) wl fn-arena fn-cat)))
                    (t (fn-srb-effect-octets (car rest))))
              (fn-qplan-cw-octets (cdr rest) wl fn-arena fn-cat))
    nil))

(defun-nx fn-qplan-cw-remaining (p wl fn-arena fn-cat)
  (append (fn-splan-cur p) (fn-qplan-cw-octets (fn-splan-rest p) wl fn-arena fn-cat)))

(local
 (defthm fn-qplan-append-assoc
   (equal (append (append x y) z) (append x (append y z)))))

(local
 (defthm fn-qplan-reply-effect-shape
   (and (equal (fn-srb-effect-octets (fn-nntp-reply-effect octets)) octets)
        (not (fn-lst-effectp (fn-nntp-reply-effect octets)))
        (not (fn-splan-cursor-effectp (fn-nntp-reply-effect octets))))
   :hints (("Goal" :in-theory (enable fn-nntp-reply-effect fn-lst-effectp)))))

(local
 (defthm fn-qplan-lst-effect-shape
   (and (fn-lst-effectp (fn-lst-effect cur))
        (equal (fn-cur-at 1 (fn-lst-effect cur)) cur))
   :hints (("Goal" :in-theory (enable fn-lst-effect fn-lst-effectp fn-cur-at)))))

(local
 (defthm fn-qplan-ovw-effect-not-list
   (not (fn-lst-effectp (fn-ovw-cursor-effect cur)))
   :hints (("Goal" :in-theory (enable fn-ovw-cursor-effect fn-lst-effectp)))))

(local
 (defthm fn-qplan-nnw-effect-not-list
   (not (fn-lst-effectp (fn-nnw-meta-effect cur)))
   :hints (("Goal" :in-theory (enable fn-nnw-meta-effect fn-lst-effectp)))))

(local
 (defthm fn-qplan-not-live-owes-nothing
   (implies (not (fn-lst-livep cur))
            (equal (fn-lst-remaining cur fn-cat) nil))
   :hints (("Goal" :in-theory (enable fn-lst-livep fn-lst-remaining
                                      fn-lst-progress-reference)))))

(local
 (defthm fn-qplan-lst-step-assoc
   (equal (append (car (fn-lst-step cur visits bytes fn-cat))
                  (fn-lst-remaining (cadr (fn-lst-step cur visits bytes fn-cat)) fn-cat)
                  z)
          (append (fn-lst-remaining cur fn-cat) z))
   :hints (("Goal" :use fn-lst-step-keeps-remaining
            :in-theory (e/d (mv-nth) (fn-lst-step-keeps-remaining fn-lst-step))))))

(local
 (defthm fn-qplan-lst-step-last
   (implies (not (fn-lst-livep (cadr (fn-lst-step cur visits bytes fn-cat))))
            (equal (append (car (fn-lst-step cur visits bytes fn-cat)) z)
                   (append (fn-lst-remaining cur fn-cat) z)))
   :hints (("Goal" :use (fn-qplan-lst-step-assoc
                         (:instance fn-qplan-not-live-owes-nothing
                                    (cur (cadr (fn-lst-step cur visits bytes fn-cat)))))
            :in-theory (disable fn-qplan-lst-step-assoc fn-qplan-not-live-owes-nothing
                                fn-lst-step)))))


(local
 (defthm fn-qplan-cursor-effect-shapes
   (and (fn-splan-cursor-effectp (fn-ovw-cursor-effect cur))
        (not (fn-nnw-meta-effectp (fn-ovw-cursor-effect cur)))
        (equal (car (cdr (fn-ovw-cursor-effect cur))) cur)
        (fn-splan-cursor-effectp (fn-nnw-meta-effect cur))
        (fn-nnw-meta-effectp (fn-nnw-meta-effect cur))
        (equal (car (cdr (fn-nnw-meta-effect cur))) cur))
   :hints (("Goal" :in-theory (enable fn-ovw-cursor-effect fn-splan-cursor-effectp
                                      fn-nnw-meta-effectp fn-nnw-meta-effect)))))

(local (defthm fn-qplan-mv-first
         (equal (mv-nth 0 x) (car x))
         :hints (("Goal" :expand ((mv-nth 0 x))))))

; A quantum keeps what the plan owes.
(local
 (defthm fn-qplan-lst-step-assoc-mv
   (equal (append (car (fn-lst-step cur visits bytes fn-cat))
                  (fn-lst-remaining (mv-nth 1 (fn-lst-step cur visits bytes fn-cat)) fn-cat)
                  z)
          (append (fn-lst-remaining cur fn-cat) z))
   :hints (("Goal" :use fn-qplan-lst-step-assoc
            :in-theory (e/d (mv-nth) (fn-qplan-lst-step-assoc fn-lst-step))))))
(local
 (defthm fn-qplan-lst-step-last-mv
   (implies (not (fn-lst-livep (mv-nth 1 (fn-lst-step cur visits bytes fn-cat))))
            (equal (append (car (fn-lst-step cur visits bytes fn-cat)) z)
                   (append (fn-lst-remaining cur fn-cat) z)))
   :hints (("Goal" :use fn-qplan-lst-step-last
            :in-theory (e/d (mv-nth) (fn-qplan-lst-step-last fn-lst-step fn-lst-livep))))))
(defthm fn-qplan-rest-cursor-step-keeps-cw-octets
  (implies (equal (mv-nth 0 (fn-qplan-rest-cursor-step rest wl fn-arena fn-cat)) :ok)
           (equal (fn-qplan-cw-octets (mv-nth 1 (fn-qplan-rest-cursor-step rest wl fn-arena fn-cat))
                                      wl fn-arena fn-cat)
                  (fn-qplan-cw-octets rest wl fn-arena fn-cat)))
  :hints (("Goal" :induct (fn-qplan-rest-cursor-step rest wl fn-arena fn-cat)
           :in-theory (e/d (fn-qplan-rest-cursor-step fn-splan-rest-cursor-step)
                           (fn-ovw-step fn-ovw-cursorp fn-ovw-run fn-nnw-meta-livep
                            fn-nnw-stream-batch fn-lst-step fn-lst-remaining fn-lst-livep
                            fn-nntp-reply-effect fn-lst-effect mv-nth fn-splan-cursor-effectp
                            fn-nnw-meta-effectp fn-ovw-cursor-effect fn-nnw-meta-effect))
           :expand ((fn-ovw-run (car (cdr (car rest))) wl fn-arena fn-cat)))))


(defthm fn-qplan-cursor-step-keeps-cw-remaining
  (implies (equal (mv-nth 0 (fn-qplan-cursor-step p wl fn-arena fn-cat)) :ok)
           (equal (fn-qplan-cw-remaining (mv-nth 1 (fn-qplan-cursor-step p wl fn-arena fn-cat))
                                         wl fn-arena fn-cat)
                  (fn-qplan-cw-remaining p wl fn-arena fn-cat)))
  :hints (("Goal" :use ((:instance fn-qplan-rest-cursor-step-keeps-cw-octets
                                   (rest (fn-splan-rest p))))
           :in-theory (e/d (fn-qplan-cursor-step fn-qplan-cw-remaining)
                           (fn-qplan-rest-cursor-step fn-qplan-cw-octets
                            fn-qplan-rest-cursor-step-keeps-cw-octets fn-splan-rest fn-splan-cur)))))

(defun-nx fn-qplan-take-budget (cur rest)
  (if (consp cur) (len cur) (fn-qplan-rest-head-len rest)))

; A take no larger than the first materialized effect never passes a LIST
; tag: its octets followed by what the continuation owes is what was owed.
(defthm fn-qplan-take-keeps-cw-octets
  (implies (<= (nfix k) (fn-qplan-take-budget cur rest))
           (equal (append (mv-nth 1 (fn-splan-take cur rest k))
                          (fn-splan-cur (mv-nth 2 (fn-splan-take cur rest k)))
                          (fn-qplan-cw-octets (fn-splan-rest (mv-nth 2 (fn-splan-take cur rest k)))
                                              wl fn-arena fn-cat))
                  (append cur (fn-qplan-cw-octets rest wl fn-arena fn-cat))))
  :hints (("Goal" :induct (fn-splan-take cur rest k)
           :in-theory (e/d (fn-splan-take fn-qplan-rest-head-len fn-qplan-cursor-effectp)
                           (fn-ovw-run fn-lst-remaining fn-nnw-stream-remaining fn-cbor-octetp)))))

; A window followed by what its continuation owes is what the plan owed.
(local (defthm fn-qplan-take-of-len
         (implies (true-listp x) (equal (take (len x) x) x))))
(local (defthm fn-qplan-take-octets-true-listp
         (true-listp (cadr (fn-splan-take cur rest k)))
         :hints (("Goal" :use fn-splan-take-octets-are-octets
                  :in-theory (e/d (mv-nth) (fn-splan-take-octets-are-octets fn-splan-take))))))
(defthm fn-qplan-window-keeps-cw-remaining
  (let* ((r (fn-qplan-window p w fn-octets))
         (p2 (mv-nth 1 r))
         (buf (mv-nth 2 r)))
    (equal (append (fn-oct-slice-list 0 (fn-octets-len buf) buf)
                   (fn-qplan-cw-remaining p2 wl fn-arena fn-cat))
           (fn-qplan-cw-remaining p wl fn-arena fn-cat)))
  :hints (("Goal" :in-theory (e/d (fn-qplan-window fn-qplan-window-size fn-splan-window
                                   fn-qplan-cw-remaining fn-oct-len-is-len
                                   fn-oct-slice-list-is-take-nthcdr)
                                  (fn-splan-take fn-splan-fill fn-qplan-cw-octets
                                   fn-splan-cur fn-splan-rest fn-qplan-take-keeps-cw-octets))
           :use ((:instance fn-qplan-take-keeps-cw-octets
                            (cur (fn-splan-cur p)) (rest (fn-splan-rest p))
                            (k (min w (fn-qplan-window-size p))))))))

; N rounds of the host's loop over the list model of fn-qplan-window: a
; quantum at a cursor, else one window of at most W octets bounded by the
; current materialized effect. :malformed stops it, as the host faults.
(defun-nx fn-qplan-cw-drain (p w wl n fn-arena fn-cat)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (mv :ok nil p)
    (if (fn-qplan-at-cursorp p)
        (mv-let (status p2)
          (fn-qplan-cursor-step p wl fn-arena fn-cat)
          (if (equal status :ok)
              (fn-qplan-cw-drain p2 w wl (- n 1) fn-arena fn-cat)
            (mv status nil p)))
      (mv-let (status octets p2)
        (fn-splan-take (fn-splan-cur p) (fn-splan-rest p) (min (nfix w) (fn-qplan-window-size p)))
        (if (or (equal status :ok) (equal status :cursor))
            (mv-let (status2 more p3)
              (fn-qplan-cw-drain p2 w wl (- n 1) fn-arena fn-cat)
              (mv status2 (append octets more) p3))
          (mv status octets p2))))))


(local
 (defthm fn-qplan-budget-is-window-size
   (equal (fn-qplan-take-budget (fn-splan-cur p) (fn-splan-rest p))
          (fn-qplan-window-size p))
   :hints (("Goal" :in-theory (enable fn-qplan-window-size fn-qplan-take-budget)))))

(defthm fn-qplan-cw-drain-is-a-prefix
  (equal (append (mv-nth 1 (fn-qplan-cw-drain p w wl n fn-arena fn-cat))
                 (fn-qplan-cw-remaining (mv-nth 2 (fn-qplan-cw-drain p w wl n fn-arena fn-cat))
                                        wl fn-arena fn-cat))
         (fn-qplan-cw-remaining p wl fn-arena fn-cat))
  :hints (("Goal" :induct (fn-qplan-cw-drain p w wl n fn-arena fn-cat)
           :in-theory (e/d (fn-qplan-cw-remaining)
                           (fn-splan-take fn-qplan-cursor-step fn-splan-cur fn-splan-rest
                            fn-qplan-at-cursorp fn-qplan-cw-octets fn-qplan-window-size
                            fn-qplan-take-budget mv-nth)))))

(local
 (defthm fn-qplan-rest-donep-owes-nothing
   (implies (fn-qplan-rest-donep rest)
            (equal (fn-qplan-cw-octets rest wl fn-arena fn-cat) nil))
   :hints (("Goal" :induct (fn-qplan-cw-octets rest wl fn-arena fn-cat)
            :in-theory (e/d (fn-qplan-rest-donep fn-qplan-cursor-effectp)
                            (fn-ovw-run fn-lst-remaining fn-nnw-stream-remaining))))))

(defthm fn-qplan-donep-implies-cw-nothing-remains
  (implies (fn-qplan-donep p)
           (equal (fn-qplan-cw-remaining p wl fn-arena fn-cat) nil))
  :hints (("Goal" :in-theory (e/d (fn-qplan-donep fn-qplan-cw-remaining) (fn-qplan-cw-octets)))))

(defthm fn-qplan-of-effects-cw-remaining
  (equal (fn-qplan-cw-remaining (fn-splan-of-effects effects) wl fn-arena fn-cat)
         (fn-qplan-cw-octets effects wl fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-qplan-cw-remaining fn-splan-of-effects fn-splan-cur fn-splan-rest)
                                  (fn-qplan-cw-octets)))))

; What the LIST command's effects owe: its initial line, then the reference
; body of the cursor it starts.
(defthm fn-lst-result-cw-octets
  (equal (fn-qplan-cw-octets
          (fn-nntp-result-effects (fn-lst-result session archive closed statusp countsp patterns filteredp v))
          wl fn-arena fn-cat)
         (append (fn-nntp-crlf (fn-nntp-string-octets
                                (if countsp (fn-proto-text "LIST" :newsgroups)
                                  (fn-proto-text "LIST" :active))))
                 (fn-lst-groups-reference (fn-lst-env archive closed statusp countsp patterns filteredp v)
                                          (fn-state-groups archive) fn-cat)))
  :hints (("Goal" :in-theory (e/d (fn-lst-result fn-nntp-make-result fn-nntp-result-effects)
                                  (fn-lst-start fn-lst-remaining fn-lst-groups-reference
                                   fn-nntp-crlf fn-nntp-string-octets fn-lst-env)))))

(in-theory (disable fn-qplan-cw-octets fn-qplan-cw-remaining fn-qplan-take-budget
                    fn-qplan-cw-drain))
