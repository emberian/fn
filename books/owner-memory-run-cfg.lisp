; Pure owner memory gate configuration and its pin-charge keystones.
(in-package "ACL2")
(include-book "public-exposure")
(include-book "cold-read-reservation")
(include-book "config")
(include-book "owner-agent")
(include-book "public-exposure-selectors")
(include-book "admission-memory")
(include-book "owner-memory-holding")
(include-book "owner-served-bound")

(defun fn-owner-memory-cfg (v tlsp trigger pub-trigger live cold profile window server config)
  (declare (xargs :guard t))
  (list (fn-exp-connections-capacity v) tlsp trigger pub-trigger live 0
        (if cold (car (fn-crv-pool-budget cold profile)) 0)
        (fn-cfg-limit v "tls-handshakes-in-flight")
        window (len server) nil nil (nfix config)))

(defun fn-owner-memory-run-cfg-of (r v cfg conns most lease flight)
  (declare (xargs :guard t))
  (let ((full (fn-owner-memory-cfg v (fn-exp-at 5 r) (fn-exp-at 2 r) (fn-exp-at 3 r) (fn-exp-at 6 r)
                                   (fn-exp-at 7 r) (fn-exp-at 4 r) (fn-exp-at 8 r) (fn-oag-agent cfg)
                                   (fn-exp-at 9 r))))
    (update-nth 15 (max (fn-adm-pin-octets conns) (nfix most))
      (update-nth 14 lease (fn-adm-cfg-holding-handshakes full flight)))))

(local
 (defthm pin-pure-builder-article-high
  (equal (fn-mm-cfg-article-high
           (fn-owner-memory-run-cfg-of r v cfg conns most lease flight))
         (max (fn-adm-pin-octets conns) (nfix most)))
  :hints (("Goal" :in-theory (union-theories
    '(fn-owner-memory-run-cfg-of fn-mm-cfg-article-high fn-mm-nat
      fn-clq-true-list-fix-id nth-update-nth true-listp-update-nth
      (:type-prescription fn-adm-cfg-holding-handshakes)
      (:type-prescription fn-adm-pin-octets-is-natural)
      nfix natp max (:type-prescription nfix))
    (theory 'minimal-theory))))))
(local (set-default-hints
 '((quote (:use fn-adm-pin-octets-covers-member
           :in-theory (union-theories
            '(fn-mm-large-reply fn-mm-served-article-octets
              fn-adm-priced-cfg-keeps-the-article-high pin-pure-builder-article-high
              max nfix natp (:type-prescription fn-adm-pin-octets-is-natural)
              (:type-prescription nfix))
            (theory 'minimal-theory)))))))
(defthm fn-owner-memory-run-cfg-of-charges-every-pinned-connection
  (implies (member-equal c conns)
           (<= (+ (* 2 (nfix (fn-inj-config-max-octets (fn-own-conn-config c))))
                  *fn-cbud-reply-status-octets*)
               (fn-mm-large-reply profile
                 (fn-adm-priced-cfg (fn-owner-memory-run-cfg-of r v cfg conns most lease flight)
                                    held cap)))))
(local (set-default-hints
 '((quote (:use ((:instance fn-owner-memory-run-cfg-of-charges-every-pinned-connection
                 (conns (fn-own-conns (mv-nth 1 (fn-osb-install o values))))
                 (profile values))
                (:instance fn-osb-install-keeps-the-connections (profile values)))
          :in-theory (theory 'minimal-theory))))))
(defthm fn-osb-install-keeps-every-pin-charged
  (implies (member-equal c (fn-own-conns o))
           (<= (+ (* 2 (nfix (fn-inj-config-max-octets (fn-own-conn-config c))))
                  *fn-cbud-reply-status-octets*)
               (fn-mm-large-reply values
                 (fn-adm-priced-cfg
                  (fn-owner-memory-run-cfg-of r v cfg (fn-own-conns (mv-nth 1 (fn-osb-install o values)))
                                              most lease flight)
                  held cap)))))
(local (set-default-hints
 '((quote (:in-theory (union-theories
            '(fn-mm-served-article-octets fn-adm-priced-cfg-keeps-the-article-high
              pin-pure-builder-article-high max nfix natp
              (:type-prescription fn-adm-pin-octets-is-natural)
              (:type-prescription nfix))
            (theory 'minimal-theory)))))))
(defthm fn-owner-memory-run-cfg-of-charge-falls-to-the-current-profile
  (implies (and (<= (fn-adm-pin-octets conns) (nfix (fn-bs-profile-max-article-octets profile)))
                (<= (nfix most) (nfix (fn-bs-profile-max-article-octets profile))))
           (equal (fn-mm-served-article-octets profile
                    (fn-adm-priced-cfg (fn-owner-memory-run-cfg-of r v cfg conns most lease flight)
                                       held cap))
                  (nfix (fn-bs-profile-max-article-octets profile)))))
(local (set-default-hints nil))

