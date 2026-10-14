; Pure pin-charge witnesses over logical open/install/close transitions.
(in-package "ACL2")
(include-book "../../books/owner-memory-run-cfg")
(include-book "pinned-charge-tests")

(defconst *pin-injection-64*
 (fn-inj-make-config t '(112 105 110) '((102 110 46 116 101 115 116)) 65536))
(defconst *pin-owner-64*
 (nth 1 (mv-list 2 (fn-osb-install
  (fn-own-configure (fn-own-start (fn-sn-initial '("fn.test") 4) 4) *pin-injection-64*)
  *pin-profile-64*))))
(defconst *pin-open-64* (cdr (fn-own-open *pin-owner-64* nil)))
(defconst *pin-connection-64* (car (fn-own-conns *pin-open-64*)))
(defconst *pin-shrunk* (nth 1 (mv-list 2 (fn-osb-install *pin-open-64* *pin-profile-10*))))
(defconst *pin-closed* (fn-own-close *pin-shrunk* (fn-own-conn-id *pin-connection-64*)))
(defconst *pin-open-10* (cdr (fn-own-open *pin-closed* nil)))
(defconst *pin-huge-connection*
 (car (fn-own-conns (cdr (fn-own-open
  (fn-own-configure *pin-owner-64*
    (fn-inj-make-config t '(112 105 110) '((102 110 46 116 101 115 116)) 131072)) nil)))))
(defconst *pin-profile-1* (update-nth *fn-bs-pf-max-article-octets* 1 *pin-profile-10*))

(assert-event
 (and (consp (fn-own-conns *pin-open-64*))
      (equal (fn-inj-config-max-octets (fn-own-conn-config *pin-connection-64*)) 65536)
      (equal (fn-own-conns *pin-shrunk*) (fn-own-conns *pin-open-64*))
      (equal (fn-own-conns *pin-closed*) nil)
      (equal (fn-inj-config-max-octets
        (fn-own-conn-config (car (fn-own-conns *pin-open-10*)))) 10240)
      (fn-bs-profile-admittedp *pin-profile-1*)
      (equal (nfix (fn-bs-profile-max-article-octets *pin-profile-1*)) 1))
 :msg "PIN-OPEN-SHRINK-CLOSE-TRACE-WHOLE")

; Test-only mutants of the one actual pure builder, ground arguments only.
(defun pin-profile-only-builder (r v cfg conns most lease flight)
 (declare (xargs :guard t))
 (update-nth 15 0 (fn-owner-memory-run-cfg-of r v cfg conns most lease flight)))
(defun pin-monotone-builder (r v cfg conns most lease flight)
 (declare (xargs :guard t))
 (fn-owner-memory-run-cfg-of r v cfg conns (max 65536 (nfix most)) lease flight))

(defkeystone fn-owner-memory-run-cfg-of-charges-every-pinned-connection
 (implies (member-equal c conns)
           (<= (+ (* 2 (nfix (fn-inj-config-max-octets (fn-own-conn-config c))))
                  *fn-cbud-reply-status-octets*)
               (fn-mm-large-reply profile
                 (fn-adm-priced-cfg (fn-owner-memory-run-cfg-of r v cfg conns most lease flight)
                                    held cap))))
 :id "PRF-100008"
 :subject fn-owner-memory-run-cfg-of :hyps (member-premises)
 :witness ((c *pin-connection-64*) (conns (fn-own-conns *pin-shrunk*))
           (profile *pin-profile-10*) (r nil) (v nil) (cfg nil) (most 0)
           (lease 0) (flight 0) (held 0) (cap 1))
 :breaks ((member-premises ((c *pin-huge-connection*))))
 :mutations ((profile-only (:conclusion
   (<= (+ (* 2 (nfix (fn-inj-config-max-octets (fn-own-conn-config c)))) *fn-cbud-reply-status-octets*)
       (fn-mm-large-reply profile
        (fn-adm-priced-cfg (pin-profile-only-builder r v cfg conns most lease flight) held cap))))
   () :fault "The profile-only gate loses the retained 65536 pin after shrink"))
 :hints (("Goal" :by fn-owner-memory-run-cfg-of-charges-every-pinned-connection)))

(defkeystone fn-osb-install-keeps-every-pin-charged
 (implies (member-equal c (fn-own-conns o))
           (<= (+ (* 2 (nfix (fn-inj-config-max-octets (fn-own-conn-config c))))
                  *fn-cbud-reply-status-octets*)
               (fn-mm-large-reply values
                 (fn-adm-priced-cfg
                  (fn-owner-memory-run-cfg-of r v cfg (fn-own-conns (mv-nth 1 (fn-osb-install o values)))
                                              most lease flight)
                  held cap))))
 :id "PRF-100010"
 :subject fn-osb-install :hyps (member-premises)
 :witness ((c *pin-connection-64*) (o *pin-open-64*) (values *pin-profile-10*)
           (r nil) (v nil) (cfg nil) (most 0) (lease 0) (flight 0) (held 0) (cap 1))
 :breaks ((member-premises ((c *pin-huge-connection*))))
 :mutations ((profile-only-after-install (:conclusion
   (<= (+ (* 2 (nfix (fn-inj-config-max-octets (fn-own-conn-config c)))) *fn-cbud-reply-status-octets*)
       (fn-mm-large-reply values
        (fn-adm-priced-cfg
         (pin-profile-only-builder r v cfg (fn-own-conns (mv-nth 1 (fn-osb-install o values)))
                                   most lease flight) held cap))))
   () :fault "The actual logical install retains a 65536 pin the old builder loses"))
 :hints (("Goal" :by fn-osb-install-keeps-every-pin-charged)))

(defkeystone fn-owner-memory-run-cfg-of-charge-falls-to-the-current-profile
 (implies (and (<= (fn-adm-pin-octets conns) (nfix (fn-bs-profile-max-article-octets profile)))
                (<= (nfix most) (nfix (fn-bs-profile-max-article-octets profile))))
           (equal (fn-mm-served-article-octets profile
                    (fn-adm-priced-cfg (fn-owner-memory-run-cfg-of r v cfg conns most lease flight)
                                       held cap))
                  (nfix (fn-bs-profile-max-article-octets profile))))
 :id "PRF-100011"
 :subject fn-owner-memory-run-cfg-of :hyps (pin-limit stored-limit)
 :witness ((conns nil) (most 10240) (profile *pin-profile-10*)
           (r nil) (v nil) (cfg nil) (lease 0) (flight 0) (held 0) (cap 1))
 :breaks ((pin-limit ((conns (fn-own-conns *pin-open-64*))))
          (stored-limit ((most 65536))))
 :mutations ((monotone-high-water (:conclusion
   (equal (fn-mm-served-article-octets profile
           (fn-adm-priced-cfg (pin-monotone-builder r v cfg conns most lease flight) held cap))
          (nfix (fn-bs-profile-max-article-octets profile))))
   () :fault "The monotone old 65536 bound cannot fall after close"))
 :hints (("Goal" :by fn-owner-memory-run-cfg-of-charge-falls-to-the-current-profile)))

(assert-event
 (let* ((conns (fn-own-conns *pin-shrunk*)) (c *pin-connection-64*)
        (required (+ (* 2 (nfix (fn-inj-config-max-octets (fn-own-conn-config c))))
                     *fn-cbud-reply-status-octets*))
        (current (fn-owner-memory-run-cfg-of nil nil nil conns 0 0 0))
        (old (pin-profile-only-builder nil nil nil conns 0 0 0)))
  (and (member-equal c conns)
       (equal (fn-adm-pin-octets conns) 65536)
       (equal (nfix (fn-bs-profile-max-article-octets *pin-profile-10*)) 10240)
       (equal required 132096)
       (<= required (fn-mm-large-reply *pin-profile-10* (fn-adm-priced-cfg current 0 1)))
       (< (fn-mm-large-reply *pin-profile-10* (fn-adm-priced-cfg old 0 1)) required)))
 :msg "PIN-64-10-PIN-GAP")
(assert-event
 (let* ((o *pin-open-64*) (c *pin-connection-64*)
        (installed (mv-list 2 (fn-osb-install o *pin-profile-10*)))
        (conns (fn-own-conns (mv-nth 1 installed)))
        (current (fn-owner-memory-run-cfg-of nil nil nil conns 0 0 0))
        (old (pin-profile-only-builder nil nil nil conns 0 0 0)))
  (and (member-equal c (fn-own-conns o))
       (equal (mv-nth 0 installed) :installed)
       (equal conns (fn-own-conns o))
       (equal (fn-adm-pin-octets conns) 65536)
       (equal (nfix (fn-bs-profile-max-article-octets *pin-profile-10*)) 10240)
       (<= 132096 (fn-mm-large-reply *pin-profile-10* (fn-adm-priced-cfg current 0 1)))
       (< (fn-mm-large-reply *pin-profile-10* (fn-adm-priced-cfg old 0 1)) 132096)))
 :msg "PIN-64-10-LIVE-GAP")
(assert-event
 (let* ((conns (fn-own-conns *pin-closed*)) (most 10240)
        (profile *pin-profile-10*)
        (current (fn-owner-memory-run-cfg-of nil nil nil conns most 0 0))
        (old (pin-monotone-builder nil nil nil conns most 0 0)))
  (and (equal conns nil)
       (<= (fn-adm-pin-octets conns) (nfix (fn-bs-profile-max-article-octets profile)))
       (<= (nfix most) (nfix (fn-bs-profile-max-article-octets profile)))
       (equal (fn-mm-served-article-octets profile (fn-adm-priced-cfg current 0 1)) 10240)
       (equal (fn-mm-served-article-octets profile (fn-adm-priced-cfg old 0 1)) 65536)
       (< 10240 65536)))
 :msg "PIN-FALLS-MONOTONE-GAP")
(defteeth-check (fn-owner-memory-run-cfg-of-charges-every-pinned-connection fn-osb-install-keeps-every-pin-charged fn-owner-memory-run-cfg-of-charge-falls-to-the-current-profile))
