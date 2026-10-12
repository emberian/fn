; fn: the leased pool's size (Builder A, the host lease, HL4; agreed with Builder M, 10-11).
;
; A run has P large pool buffers, where P is fn-mm-cfg-holders. Each
; buffer holds an ARTICLE render window or one header-bounded OVER line
; plus framing. The maximum is within the configured LARGE term (HL4).
(in-package "ACL2")
(include-book "memory-model")
(include-book "runtime-contract")
(include-book "defkeystone")

(defun fn-hl-article-capl (profile q)
  (declare (xargs :guard t))
  (+ (min (* 2 (nfix q)) (* 2 (nfix (fn-bs-profile-max-article-octets profile))))
     *fn-cbud-reply-status-octets*))

; The run's contract configuration: listener, NSTATIC static instances (the owner is 1), one
; slot per connection; QFIXED home buffers of CAPF octets per instance slot; the pool.
(defun fn-hl-rtc-config (profile cfg q nstatic qfixed capf)
  (declare (xargs :guard t))
  (let* ((nslots (+ 1 (nfix nstatic) (fn-mm-cfg-connections cfg)))
         (npool (fn-mm-cfg-holders cfg)))
    (list nslots (+ (* (- nslots 1) (nfix qfixed)) npool) (nfix capf) (nfix nstatic) (nfix qfixed)
          npool (max (fn-hl-article-capl profile q) (fn-ovr-over-capl-of profile cfg)))))

(defthm fn-hl-article-capl-is-a-lease
  (and (posp (fn-hl-article-capl profile q))
       (<= (fn-hl-article-capl profile q)
           (+ (* 2 (nfix (fn-bs-profile-max-article-octets profile))) *fn-cbud-reply-status-octets*)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hl-article-capl nfix natp posp min)
                                             (theory 'minimal-theory)))))

(local (defthm fn-hl-configp-of-a-list
  (implies (and (natp ns) (<= 2 ns) (natp cf) (natp st) (< st ns) (natp qf) (natp np) (natp cl))
           (fn-rtc-configp (list ns (+ (* (- ns 1) qf) np) cf st qf np cl)))
  :hints (("Goal" :in-theory (enable fn-rtc-configp fn-rtc-get) :nonlinearp t))))

(defthm fn-hl-rtc-config-is-a-config
  (implies (posp nstatic)
           (fn-rtc-configp (fn-hl-rtc-config profile cfg q nstatic qfixed capf)))
  :hints (("Goal" :in-theory (union-theories '(fn-hl-rtc-config posp natp nfix max (:type-prescription fn-ovr-over-capl-of)) (theory 'minimal-theory))
           :use (fn-hl-article-capl-is-a-lease (:instance fn-mm-terms-natp (img nil) (tot nil))
                 (:instance fn-hl-configp-of-a-list
                            (ns (+ 1 (nfix nstatic) (fn-mm-cfg-connections cfg))) (cf (nfix capf))
                            (st (nfix nstatic)) (qf (nfix qfixed)) (np (fn-mm-cfg-holders cfg))
                            (cl (max (fn-hl-article-capl profile q) (fn-ovr-over-capl-of profile cfg))))))))

(local (defthm fn-hl-times-monotone
  (implies (and (natp a) (natp b) (natp c) (<= a b)) (<= (* c a) (* c b)))
  :hints (("Goal" :nonlinearp t))))

(local (defthm fn-hl-rtc-config-pool-fields
  (and (equal (fn-rtc-npool (fn-hl-rtc-config profile cfg q nstatic qfixed capf)) (fn-mm-cfg-holders cfg))
       (equal (fn-rtc-capl (fn-hl-rtc-config profile cfg q nstatic qfixed capf)) (max (fn-hl-article-capl profile q) (fn-ovr-over-capl-of profile cfg))))
  :hints (("Goal" :in-theory (e/d (fn-hl-rtc-config fn-rtc-npool fn-rtc-capl fn-rtc-get)
                                  (fn-hl-article-capl fn-ovr-over-capl-of fn-mm-cfg-holders fn-mm-cfg-connections))))))

(local (defthm fn-hl-large-reply-holds-the-article
  (<= (+ (* 2 (nfix (fn-bs-profile-max-article-octets profile))) *fn-cbud-reply-status-octets*)
      (fn-mm-large-reply profile cfg))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-mm-large-reply max) (theory 'minimal-theory))))))

(defthm fn-hl-leased-pool-within-the-large-term
  (let ((c (fn-hl-rtc-config profile cfg q nstatic qfixed capf)))
    (<= (* (fn-rtc-npool c) (fn-rtc-capl c)) (fn-mm-large-pool profile cfg)))
  :hints (("Goal" :in-theory (union-theories '(fn-hl-rtc-config-pool-fields fn-mm-large-pool posp natp max (:type-prescription fn-ovr-over-capl-of))
                                             (theory 'minimal-theory))
           :use (fn-hl-article-capl-is-a-lease fn-hl-large-reply-holds-the-article fn-ovr-over-capl-within-the-large-reply
                 (:instance fn-mm-terms-natp (img nil) (tot nil))
                 (:instance fn-hl-times-monotone (c (fn-mm-cfg-holders cfg))
                            (a (max (fn-hl-article-capl profile q) (fn-ovr-over-capl-of profile cfg)))
                            (b (fn-mm-large-reply profile cfg)))))))

; A cfg of 200,000 connections of which 10 may hold a large reply.
(defconst *fn-hl-teeth-cfg* '(200000 nil 0 0 nil 0 0 0 nil 0 10))

(defteeth fn-hl-leased-pool-within-the-large-term
  :claim (() (let ((c (fn-hl-rtc-config profile cfg q nstatic qfixed capf)))
               (<= (* (fn-rtc-npool c) (fn-rtc-capl c)) (fn-mm-large-pool profile cfg))))
  :subject fn-hl-rtc-config
  :witness ((profile *fn-bs-profile-development*) (cfg *fn-hl-teeth-cfg*) (q 16384) (nstatic 1)
            (qfixed 1) (capf 4096))
  :breaks ()
  :mutations ((a-buffer-per-connection
               (:conclusion (let ((c (fn-hl-rtc-config profile cfg q nstatic qfixed capf)))
                              (<= (* (fn-mm-cfg-connections cfg) (fn-rtc-capl c)) (fn-mm-large-pool profile cfg))))
               ((profile *fn-bs-profile-development*) (cfg *fn-hl-teeth-cfg*) (q 16384) (nstatic 1)
                (qfixed 1) (capf 4096))
               :fault "A pool of one lease per connection, not per holder, is past the memory equation's LARGE term.")))

; KL7: any pool buffer holds the configured OVER line and framing.
(defthm fn-ovr-configured-capl-holds-a-line
  (implies (<= (fn-rtc-nhome (fn-hl-rtc-config profile cfg q nstatic qfixed capf)) (nfix h))
           (<= (fn-ovr-over-capl-of profile cfg)
               (fn-rtc-buf-cap h (fn-hl-rtc-config profile cfg q nstatic qfixed capf))))
  :hints (("Goal" :in-theory (e/d (fn-hl-rtc-config fn-rtc-nhome fn-rtc-nslots fn-rtc-qfixed
                                    fn-rtc-get fn-rtc-buf-cap fn-rtc-capl max)
                                  (fn-hl-article-capl fn-ovr-over-capl-of fn-mm-cfg-connections fn-mm-cfg-holders)))))
