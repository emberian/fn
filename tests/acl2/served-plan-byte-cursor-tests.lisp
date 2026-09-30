(in-package "ACL2")
(include-book "../../books/served-plan-byte-cursor")
(include-book "../../books/served-plan")
(include-book "over-byte-cursor-tests")

(defconst *spbct-tail* (list '(:audit retained) (fn-nntp-reply-effect '(97 102 116 101 114))))

(defun spbct-atoms (p n fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :measure (nfix n) :verify-guards nil))
  (if (or (zp n) (not (eq (fn-spbc-status p) :continue)))
      (mv p t)
    (let* ((q (fn-spbc-quantum p)) (next (fn-spbc-one p fn-arena fn-cat)))
      (mv-let (final good) (spbct-atoms next (1- n) fn-arena fn-cat)
        (mv final
            (and good (equal (fn-spbc-status p) :continue)
                 (fn-spbc-ready-p p fn-arena fn-cat)
                 (equal (fn-spbc-quantum next) (fn-obc-quantum-one q fn-arena fn-cat))
                 (equal (fn-spbc-tail next) *spbct-tail*)
                 (equal (fn-splan-cur next) (fn-splan-cur p))))))))

(defun spbct-drain (p quantum rounds fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :measure (nfix rounds) :verify-guards nil))
  (if (or (zp rounds) (fn-splan-donep p)) (mv nil p t)
    (mv-let (status started) (fn-spbc-begin p (obct-token) quantum)
      (mv-let (saved good) (spbct-atoms started quantum fn-arena fn-cat)
        (let* ((finished (fn-spbc-finish saved))
               (q (fn-spbc-quantum saved))
               (rest (fn-splan-rest finished)))
          (mv-let (out next) (fn-obc-quantum-finish q)
          (mv-let (render-status prefix continued)
            (fn-splan-take (fn-splan-cur finished) rest 1000)
            (mv-let (suffix final good2)
              (spbct-drain continued quantum (1- rounds) fn-arena fn-cat)
              (mv (append prefix suffix) final
                  (and good good2 (eq status :ok)
                       (member-eq render-status '(:ok :cursor))
                       (equal (car rest) (fn-nntp-reply-effect out))
                       (equal (cdr rest)
                              (if next (cons (fn-spbc-effect :byte next) *spbct-tail*)
                                *spbct-tail*))
                       (equal (fn-splan-cur finished) (fn-splan-cur saved))))))))))))

(defun spbct-case (legacy quantum fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (let* ((fn-arena (fn-arena-clear fn-arena)) (fn-cat (fn-cat-clear fn-cat))
         (wire (fn-record-make 0 1 0 "<e@x>" *obct-source* '("fn.test") "o" "s" "e" 1 5)))
    (mv-let (row fn-arena) (fn-cat-intern-list wire nil 0 fn-arena)
      (let* ((row (if legacy (fn-held-plain wire (fn-record-payload row)) row))
             (fn-cat (fn-cat-commit row fn-cat))
             (p (cons nil (cons (list :over-cursor (fn-ovw-cursor "fn.test" 1 1 1 nil t))
                                     *spbct-tail*))))
        (mv-let (bytes final good) (spbct-drain p quantum 1000 fn-arena fn-cat)
          (mv (and good (fn-splan-donep final)
                   (equal bytes (append *obct-expected* '(97 102 116 101 114))))
              fn-arena fn-cat))))))

; Positive full atomic-plan witnesses include a nonempty retained effect
; tail, real cached/legacy rows and the complete final response plus tail.
(assert-event (mv-let (good fn-arena fn-cat) (spbct-case nil 7 fn-arena fn-cat)
                (mv good fn-arena fn-cat)) :stobjs-out '(nil fn-arena fn-cat))
(assert-event (mv-let (good fn-arena fn-cat) (spbct-case t 7 fn-arena fn-cat)
                (mv good fn-arena fn-cat)) :stobjs-out '(nil fn-arena fn-cat))
(assert-event (mv-let (good fn-arena fn-cat) (spbct-case t 64 fn-arena fn-cat)
                (mv good fn-arena fn-cat)) :stobjs-out '(nil fn-arena fn-cat))

; A response's old captured generation is rejected even if V is unchanged.
(assert-event
 (let* ((s (fn-obc-begin (fn-ovw-cursor "fn.test" 1 1 1 nil t) (obct-token)))
        (p (cons nil (cons (fn-spbc-effect :byte s) *spbct-tail*))))
   (and (equal (nth 0 (mv-list 2 (fn-spbc-begin p '(:response 7 32) 7))) :stale-pin)
        (equal (nth 1 (mv-list 2 (fn-spbc-begin p '(:response 7 32) 7))) p))))

; Starting in unread materialized output or before a noncursor effect is
; explicit malformed, never an uncharged prefix scan or lost output.
(assert-event
 (let ((p (cons '(65) (list (list :over-cursor (fn-ovw-cursor "fn.test" 1 1 1 nil t))))))
   (and (equal (nth 0 (mv-list 2 (fn-spbc-begin p (obct-token) 7))) :malformed)
        (equal (nth 1 (mv-list 2 (fn-spbc-begin p (obct-token) 7))) p))))
(assert-event
 (let ((p (cons nil (cons '(:audit retained)
                         (list (list :over-cursor (fn-ovw-cursor "fn.test" 1 1 1 nil t)))))))
   (and (equal (nth 0 (mv-list 2 (fn-spbc-begin p (obct-token) 7))) :malformed)
        (equal (nth 1 (mv-list 2 (fn-spbc-begin p (obct-token) 7))) p))))

(defun spbct-empty-case (legacy k top fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (let* ((fn-arena (fn-arena-clear fn-arena)) (fn-cat (fn-cat-clear fn-cat))
         (p (cons nil (cons (list :over-cursor (fn-ovw-cursor "fn.test" k top 0 legacy t))
                                *spbct-tail*))))
    (mv-let (bytes final good) (spbct-drain p 7 1000 fn-arena fn-cat)
      (mv (and good (fn-splan-donep final)
               (equal bytes (append (fn-ovw-status (fn-ovw-empty-text legacy))
                                    '(97 102 116 101 114)))) fn-arena fn-cat))))

; Actual empty catalog sparse seek crosses several empty quanta before 423;
; empty XOVER uses its distinct 420 response, retaining the complete tail.
(assert-event (mv-let (good fn-arena fn-cat) (spbct-empty-case nil 1 31 fn-arena fn-cat)
                (mv good fn-arena fn-cat)) :stobjs-out '(nil fn-arena fn-cat))
(assert-event (mv-let (good fn-arena fn-cat) (spbct-empty-case t 1 0 fn-arena fn-cat)
                (mv good fn-arena fn-cat)) :stobjs-out '(nil fn-arena fn-cat))
