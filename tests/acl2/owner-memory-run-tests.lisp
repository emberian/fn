(in-package "ACL2")
(include-book "../../books/owner-memory-run")
(include-book "../../books/defkeystone")
(defconst *omrt-profile* *fn-heap-small-profile*)
(defconst *omrt-img* '(104857600 24117248 1090519))
(defconst *omrt-cfg* '(32 t 8388608 8388608 nil 0 8388608 16 nil 64))
(defconst *omrt-tot* '(0 0 0 0 0 0 0 0 :resident))
(defconst *omrt-limit* (* 4096 *fn-heap-mib*))
(assert-event
 (let* ((bank (fn-adm-lease-startup-bank-cfg *omrt-profile* *omrt-img* *omrt-cfg* *omrt-limit* *omrt-tot*))
        (charge (fn-adm-installed-lease-allocation *omrt-profile* bank 1048576))
        (cfg (fn-adm-lease-startup-cfg *omrt-profile* *omrt-img* *omrt-cfg* *omrt-limit* *omrt-tot* 1048576))
        (cap (fn-adm-installed-capacity *omrt-profile* *omrt-img* cfg *omrt-limit* *omrt-tot*))
        (lowered (fn-adm-priced-cfg cfg 0 1)))
  (and (posp charge) (posp cap)
       (fn-mm-gate-p *omrt-profile* *omrt-img* (fn-adm-public-readers-cfg cfg cap) *omrt-limit* *omrt-tot*)
       (equal (fn-mm-cfg-cold lowered) (fn-mm-cfg-cold *omrt-cfg*))
       (equal (fn-mm-cfg-bank-floor lowered) charge)
       (<= charge (fn-mm-connections *omrt-profile* lowered))
       (equal (fn-mm-cfg-cold (fn-adm-lease-startup-cfg *omrt-profile* *omrt-img* *omrt-cfg* *omrt-limit* *omrt-tot* nil))
              (fn-mm-cfg-cold *omrt-cfg*)))))

; Whole positive A-K1 witness: a funded bank and all 64 configured readers.
(defconst *omrt-floor-cfg* (fn-adm-cfg-at *omrt-cfg* 64))
(defconst *omrt-floor-limit*
 (max (fn-mm-sum *omrt-profile* *omrt-img* (fn-adm-public-readers-cfg *omrt-floor-cfg* 64) *omrt-tot*)
      (fn-mm-reopen-need *omrt-profile* *omrt-img* *omrt-floor-cfg* *omrt-tot*)))
(with-guard-checking-event :none
 (assert-event
  (let* ((k (fn-adm-installed-capacity *omrt-profile* *omrt-img* *omrt-floor-cfg* *omrt-floor-limit* *omrt-tot*))
         (installed (fn-adm-lease-startup-cfg *omrt-profile* *omrt-img* *omrt-floor-cfg* *omrt-floor-limit* *omrt-tot* 1048576)))
   (and (natp 1048576) (equal k 64) (<= 1 k)
        (posp (fn-mm-cfg-bank-floor installed))
        (equal (fn-mm-cfg-cold installed) (fn-mm-cfg-cold *omrt-floor-cfg*))
        (equal (fn-adm-installed-capacity *omrt-profile* *omrt-img* installed *omrt-floor-limit* *omrt-tot*) k)))))

(defun omrt-old-cold-add-cfg (cfg lease-octets)
  (declare (xargs :guard t))
  (update-nth 6 (+ (fn-mm-cfg-cold cfg) (nfix lease-octets)) (true-list-fix cfg)))

; Removal/mutation tooth: the actual retired cold-add definition, evaluated
; against the same funded configuration; its second search loses readers.
(with-guard-checking-event :none
 (assert-event
  (let* ((k (fn-adm-installed-capacity *omrt-profile* *omrt-img* *omrt-floor-cfg* *omrt-floor-limit* *omrt-tot*))
         (old (omrt-old-cold-add-cfg *omrt-floor-cfg*
                (fn-adm-installed-lease-allocation *omrt-profile*
                 (fn-adm-lease-startup-bank-cfg *omrt-profile* *omrt-img* *omrt-floor-cfg* *omrt-floor-limit* *omrt-tot*) 1048576))))
   (and (natp 1048576) (<= 1 k)
        (not (<= k (fn-adm-installed-capacity *omrt-profile* *omrt-img* old *omrt-floor-limit* *omrt-tot*)))))))

; A-K2 positive witness and old-reader-only mutation: retained bank exceeds
; zero priced readers; the old connections equation would charge zero.
(assert-event
 (let* ((cfg (update-nth 14 1000000 nil))
        (priced (fn-adm-priced-cfg cfg 0 0)))
  (and (equal (fn-mm-cfg-bank-floor priced) (fn-mm-cfg-bank-floor cfg))
       (<= (fn-mm-cfg-bank-floor cfg) (fn-mm-connections *omrt-profile* priced))
       (not (<= (fn-mm-cfg-bank-floor cfg)
                (+ (* (fn-mm-cfg-connections priced) (fn-mm-connection-fixed *omrt-profile* priced))
                   (fn-mm-large-pool *omrt-profile* priced)))))))

(defkeystone m26-priced-cfg-keeps-the-installed-bank
(and (equal (fn-mm-cfg-bank-floor (fn-adm-priced-cfg cfg held capacity)) (fn-mm-cfg-bank-floor cfg))
       (<= (fn-mm-cfg-bank-floor cfg) (fn-mm-connections profile (fn-adm-priced-cfg cfg held capacity))))
 :id "PRF-100001"
 :restates fn-adm-priced-cfg-keeps-the-installed-bank
 :subject fn-adm-priced-cfg
 :rule-classes nil
 :witness ((profile *omrt-profile*) (cfg (update-nth 14 1000000 nil)) (held 0) (capacity 0))
 :mutations ((old-reader-only-charge
  (:conclusion
   (let ((priced (fn-adm-priced-cfg cfg held capacity)))
    (<= (fn-mm-cfg-bank-floor cfg)
        (+ (* (fn-mm-cfg-connections priced) (fn-mm-connection-fixed profile priced))
           (fn-mm-large-pool profile priced)))))
  ((profile *omrt-profile*) (cfg (update-nth 14 1000000 nil)) (held 0) (capacity 0))
  :fault "the old reader-only charge erases the retained bank at zero live readers"))
 :hints (("Goal" :by fn-adm-priced-cfg-keeps-the-installed-bank)))

(defkeystone m26-lease-startup-keeps-its-bank-readers
(<= (fn-adm-installed-capacity profile img cfg limit tot)
      (fn-adm-installed-capacity profile img
                                 (fn-adm-lease-startup-cfg profile img cfg limit tot quantum)
                                 limit tot))
 :id "PRF-100000"
 :restates fn-adm-lease-startup-keeps-its-bank-readers
 :subject fn-adm-lease-startup-cfg
 :rule-classes nil
 :witness ((profile *omrt-profile*) (img *omrt-img*) (cfg *omrt-floor-cfg*)
           (limit *omrt-floor-limit*) (tot *omrt-tot*) (quantum 1048576))
 :mutations ((old-cold-add
  (:conclusion
   (<= (fn-adm-installed-capacity profile img cfg limit tot)
       (fn-adm-installed-capacity profile img
        (omrt-old-cold-add-cfg cfg
         (fn-adm-installed-lease-allocation profile
          (fn-adm-lease-startup-bank-cfg profile img cfg limit tot) quantum))
        limit tot)))
  ((profile *omrt-profile*) (img *omrt-img*) (cfg *omrt-floor-cfg*)
   (limit *omrt-floor-limit*) (tot *omrt-tot*) (quantum 1048576))
  :fault "the retired cold-add equation charges the installed bank twice and loses funded readers"))
 :hints (("Goal" :by fn-adm-lease-startup-keeps-its-bank-readers)))

; Retaining the 64-reader bank while ten public places are free still
; charges the installed bank and funds the current run's operator slot.
(with-guard-checking-event :none
 (assert-event
  (let* ((installed (fn-adm-lease-startup-cfg *omrt-profile* *omrt-img*
                     *omrt-floor-cfg* *omrt-floor-limit* *omrt-tot* 1048576))
         (lowered (fn-adm-cfg-at installed 10))
         (held (fn-adm-run-gate-held 0 10 10 nil))
         (priced (fn-adm-priced-cfg lowered held 10)))
   (and (equal (fn-adm-installed-capacity *omrt-profile* *omrt-img* installed
                 *omrt-floor-limit* *omrt-tot*) 64)
        (equal (fn-adm-reader-count 10 10) 10)
        (equal held 11)
        (equal (fn-mm-cfg-connections priced) 11)
        (posp (fn-mm-cfg-bank-floor installed))
        (equal (fn-mm-cfg-bank-floor priced) (fn-mm-cfg-bank-floor installed))
        (<= (fn-mm-cfg-bank-floor installed) (fn-mm-connections *omrt-profile* priced))
        (fn-mm-gate-p *omrt-profile* *omrt-img* priced *omrt-floor-limit* *omrt-tot*)
        (equal (fn-adm-installed-capacity *omrt-profile* *omrt-img* lowered
                 *omrt-floor-limit* *omrt-tot*) 10)))))
