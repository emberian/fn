; fn: the leased pool's size (Builder A, the host lease, HL4; agreed with Builder M, 10-11).
;
; A run's contract configuration for the leased reader: the pool has P buffers, P the
; memory equation's large-payload holders (fn-mm-cfg-holders), each of the ARTICLE lease's
; capacity CAPL.  CAPL is one render window's worst rendering, two octets for every payload
; octet of the quantum Q the host renders per window (dot-stuffing and line ends) plus the
; status line, and never more than the whole reply's, 2A plus the status line, that the
; connection budget charges (books/connection-budget.lisp).  The render's output limit is
; the buffer's capacity (books/article-stream.lisp fn-ast-render-window-byte-bound), so a
; window never overruns its lease whatever Q is.
;
; HL4 (fn-hl-leased-pool-within-the-large-term): the pool's octets, npool x capl, are within
; the memory equation's LARGE term, fn-mm-large-pool (P x fn-mm-large-reply).  It is stated
; as <= while some large reply path is not leased (fn-mm-large-reply still charges the
; unleased 2A + status and OVER's list window); the landing that leases the last such path
; restates fn-mm-large-reply as the lease capacity and this as an equality (M's book).  OVER
; joins the lease (O's landing 2) by taking CAPL as the max of this and its own window term.
(in-package "ACL2")
(include-book "memory-model")
(include-book "runtime-contract")
(include-book "defkeystone")
(local (include-book "arithmetic-5/top" :dir :system))

(defconst *fn-pth-nstatic* 1)
(defconst *fn-pth-qs* 3)
(defconst *fn-pbatch-max* 65634)
(defconst *fn-pth-cs* (max 5606 (+ 29 *fn-pbatch-max*)))

(defun fn-hl-article-capl (profile q)
  (declare (xargs :guard t))
  (+ (min (* 2 (nfix q)) (* 2 (nfix (fn-bs-profile-max-article-octets profile))))
     *fn-cbud-reply-status-octets*))

; The run's contract configuration: listener, NSTATIC static instances (the owner is 1), one
; slot per connection; QS static home buffers of CS octets, QFIXED connection
; home buffers of CAPF octets per connection slot; the pool.
(defun fn-hl-rtc-config (profile cfg q nstatic qfixed capf qs cs)
  (declare (xargs :guard t))
  (let* ((nstatic (nfix nstatic))
         (qfixed (nfix qfixed)) (capf (nfix capf))
         (qs (nfix qs)) (cs (nfix cs))
         (nconnections (fn-mm-cfg-connections cfg))
         (nslots (+ 1 nstatic nconnections))
         (npool (fn-mm-cfg-holders cfg)))
    (list nslots (+ (* nstatic qs) (* (- (- nslots 1) nstatic) qfixed) npool)
          capf nstatic qfixed npool (fn-hl-article-capl profile q) qs cs)))

(defthm fn-hl-article-capl-is-a-lease
  (and (posp (fn-hl-article-capl profile q))
       (<= (fn-hl-article-capl profile q)
           (+ (* 2 (nfix (fn-bs-profile-max-article-octets profile))) *fn-cbud-reply-status-octets*)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hl-article-capl nfix natp posp min)
                                             (theory 'minimal-theory)))))

(local (defthm fn-hl-configp-of-a-list
  (implies (and (natp ns) (<= 2 ns) (natp cf) (natp st) (< st ns) (natp qf) (natp np) (natp cl)
                (natp qs) (natp cs))
           (fn-rtc-configp
            (list ns (+ (* st qs) (* (- (- ns 1) st) qf) np) cf st qf np cl qs cs)))
  :hints (("Goal" :in-theory (enable fn-rtc-configp fn-rtc-get) :nonlinearp t))))

(defthm fn-hl-rtc-config-is-a-config
  (implies (posp nstatic)
           (fn-rtc-configp (fn-hl-rtc-config profile cfg q nstatic qfixed capf qs cs)))
  :hints (("Goal" :in-theory (union-theories '(fn-hl-rtc-config posp natp nfix) (theory 'minimal-theory))
           :use (fn-hl-article-capl-is-a-lease (:instance fn-mm-terms-natp (img nil) (tot nil))
                 (:instance fn-hl-configp-of-a-list
                            (ns (+ 1 (nfix nstatic) (fn-mm-cfg-connections cfg))) (cf (nfix capf))
                            (st (nfix nstatic)) (qf (nfix qfixed)) (np (fn-mm-cfg-holders cfg))
                            (cl (fn-hl-article-capl profile q)) (qs (nfix qs)) (cs (nfix cs)))))))

(local (defthm fn-hl-times-monotone
  (implies (and (natp a) (natp b) (natp c) (<= a b)) (<= (* c a) (* c b)))
  :hints (("Goal" :nonlinearp t))))

(local (defthm fn-hl-rtc-config-pool-fields
  (and (equal (fn-rtc-npool (fn-hl-rtc-config profile cfg q nstatic qfixed capf qs cs)) (fn-mm-cfg-holders cfg))
       (equal (fn-rtc-capl (fn-hl-rtc-config profile cfg q nstatic qfixed capf qs cs)) (fn-hl-article-capl profile q)))
  :hints (("Goal" :in-theory (e/d (fn-hl-rtc-config fn-rtc-npool fn-rtc-capl fn-rtc-get)
                                  (fn-hl-article-capl fn-mm-cfg-holders fn-mm-cfg-connections))))))

(local (defthm fn-hl-large-reply-holds-the-article
  (<= (+ (* 2 (nfix (fn-bs-profile-max-article-octets profile))) *fn-cbud-reply-status-octets*)
      (fn-mm-large-reply profile cfg))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-mm-large-reply max) (theory 'minimal-theory))))))

(defthm fn-hl-leased-pool-within-the-large-term
  (let ((c (fn-hl-rtc-config profile cfg q nstatic qfixed capf qs cs)))
    (<= (* (fn-rtc-npool c) (fn-rtc-capl c)) (fn-mm-large-pool profile cfg)))
  :hints (("Goal" :in-theory (union-theories '(fn-hl-rtc-config-pool-fields fn-mm-large-pool posp natp)
                                             (theory 'minimal-theory))
           :use (fn-hl-article-capl-is-a-lease fn-hl-large-reply-holds-the-article
                 (:instance fn-mm-terms-natp (img nil) (tot nil))
                 (:instance fn-hl-times-monotone (c (fn-mm-cfg-holders cfg))
                            (a (fn-hl-article-capl profile q)) (b (fn-mm-large-reply profile cfg)))))))

; A cfg of 200,000 connections of which 10 may hold a large reply at once (LARGE is 562,556,544
; octets at the development profile, OVER's list window; one ARTICLE lease is 33,792).
(defconst *fn-hl-teeth-cfg* '(200000 nil 0 0 nil 0 0 0 nil 0 10))

(defteeth fn-hl-leased-pool-within-the-large-term
  :claim (() (let ((c (fn-hl-rtc-config profile cfg q nstatic qfixed capf qs cs)))
               (<= (* (fn-rtc-npool c) (fn-rtc-capl c)) (fn-mm-large-pool profile cfg))))
  :subject fn-hl-rtc-config
  :witness ((profile *fn-bs-profile-development*) (cfg *fn-hl-teeth-cfg*) (q 16384) (nstatic 1)
            (qfixed 1) (capf 4096) (qs 0) (cs 0))
  :breaks ()
  :mutations ((a-buffer-per-connection
               (:conclusion (let ((c (fn-hl-rtc-config profile cfg q nstatic qfixed capf qs cs)))
                              (<= (* (fn-mm-cfg-connections cfg) (fn-rtc-capl c)) (fn-mm-large-pool profile cfg))))
               ((profile *fn-bs-profile-development*) (cfg *fn-hl-teeth-cfg*) (q 16384) (nstatic 1)
                (qfixed 1) (capf 4096) (qs 0) (cs 0))
               :fault "A pool of one lease per connection, not per holder, is past the memory equation's LARGE term.")))
