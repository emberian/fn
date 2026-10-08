; Round 5 contracts over the host-facing installs and initialization.
(in-package "ACL2")
(include-book "extent-cache-storage")

(defthm fn-xc-decoded-count-natp
  (natp (fn-pwz-token-window-length token))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-pwz-token-window-length))))
(defthm fn-xcw-store-counted-stores-pair
  (let ((new (fn-xcw-store-counted row plan count wins buf)))
    (implies (and (natp row) (< row (fn-xcw-plans-length wins)) (natp count))
             (and (equal (fn-xcw-plan row new) plan)
                  (implies (and (natp j) (< j count))
                           (equal (nth j (nth 0 (fn-xcw-window row new))) (nth j (nth 0 buf)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-xcw-store-counted fn-xcw-plan fn-xcw-window)
                                (fn-xcw-copy fn-xcw-copy-exact-output-and-effects))
           :use (:instance fn-xcw-copy-exact-output-and-effects (src 0) (dst 0)
                  (fn-ew-buffer buf) (fn-xcw-win (fn-xcw-window row wins))))))

(defthm fn-xc-install-result-by-definition
  (equal (len (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer slots cells)) 5)
  :hints (("Goal" :in-theory (enable fn-xc-install))))
(defthm fn-xc-install-entry-result-by-definition
  (equal (len (fn-xc-install-entry file eoff elen trailer token slots cells)) 5))
(defthm fn-xc-install-window-result-by-definition
  (equal (len (fn-xc-install-window token slots cells)) 5))
(defthm fn-xc-install-result-listp-by-definition
  (true-listp (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer slots cells))
  :hints (("Goal" :in-theory (enable fn-xc-install))))
(defthm fn-xc-install-entry-result-listp-by-definition
  (true-listp (fn-xc-install-entry file eoff elen trailer token slots cells)))
(defthm fn-xc-install-window-result-listp-by-definition
  (true-listp (fn-xc-install-window token slots cells)))
(defthm fn-xc-take-len
  (implies (true-listp x) (equal (take (len x) x) x))
  :hints (("Goal" :induct (len x))))
(defthm fn-xc-list-five
  (implies (and (true-listp x) (equal (len x) 5))
           (equal (list (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x) (nth 4 x)) x))
  :hints (("Goal" :do-not-induct t :use fn-xc-take-len
           :in-theory (e/d (take nth) (fn-xc-take-len))
           :expand ((take 5 x) (take 4 (cdr x)) (take 3 (cddr x))
                    (take 2 (cdddr x)) (take 1 (cddddr x))))))

(defthm fn-xc-install-decoded-bytes-installs-the-table-decision
  (implies (and (fn-xc-readyp slots cells)
                (<= (fn-xc-nw cells) (fn-xcw-plans-length wins)) (fn-xc-decoded-planp z token))
           (equal (take 5 (fn-xc-install-decoded-bytes token z slots cells wins buf))
                  (fn-xc-install-window token slots cells)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (mv-nth) (fn-xc-install-window fn-xc-install-entry fn-xcw-copy fn-xce-adopt fn-xc-decoded-planp)) :use (:instance fn-xc-list-five (x (fn-xc-install-window token slots cells))))))

(defthm fn-xc-install-entry-bytes-installs-the-table-decision
  (implies (and (fn-xc-readyp slots cells)
                (<= (fn-xc-ne cells) (fn-xce-keys-length entries)) (natp elen)
                (equal (len stage) (+ elen *fn-frame-trailer-octets*)))
           (equal (take 5 (fn-xc-install-entry-bytes file eoff elen trailer token slots cells entries stage))
                  (fn-xc-install-entry file eoff elen trailer token slots cells)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (mv-nth) (fn-xc-install-window fn-xc-install-entry fn-xcw-copy fn-xce-adopt fn-xc-decoded-planp)) :use (:instance fn-xc-list-five (x (fn-xc-install-entry file eoff elen trailer token slots cells))))))

(defthm fn-xc-success-is-admissible
  (implies (member-equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer slots cells)) '(:installed :replaced))
           (fn-xc-install-okp kind tokp tid tcid file eoff elen a b c d start trailer slots cells))
  :hints (("Goal" :in-theory (e/d (fn-xc-install fn-xc-install-okp) (fn-xc-token fn-xc-slot-token)))))
(defthm fn-xc-success-placement
  (let ((r (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer slots cells)))
    (implies (and (fn-xcsp slots) (fn-xccp cells) (member-equal (mv-nth 0 r) '(:installed :replaced)))
             (and (natp (mv-nth 1 r)) (<= (fn-xc-lo kind cells) (mv-nth 1 r))
                  (< (mv-nth 1 r) (fn-xc-hi kind cells))
                  (fn-xcsp (mv-nth 3 r)) (fn-xccp (mv-nth 4 r))
                  (fn-xc-readyp (mv-nth 3 r) (mv-nth 4 r))
                  (equal (fn-xc-ne (mv-nth 4 r)) (fn-xc-ne cells))
                  (equal (fn-xc-nw (mv-nth 4 r)) (fn-xc-nw cells)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-xc-install fn-xc-install-okp fn-xc-install-placement)
           :use ((:instance fn-xc-install-placement (fn-xcs slots) (fn-xcc cells))))))
(defthm fn-xc-window-success-placement
  (let ((r (fn-xc-install-window token slots cells)))
    (implies (and (fn-xcsp slots) (fn-xccp cells) (member-equal (mv-nth 0 r) '(:installed :replaced)))
             (and (natp (mv-nth 1 r)) (<= (fn-xc-ne cells) (mv-nth 1 r))
                  (< (mv-nth 1 r) (+ (fn-xc-ne cells) (fn-xc-nw cells)))
                  (fn-xcsp (mv-nth 3 r)) (fn-xccp (mv-nth 4 r))
                  (fn-xc-readyp (mv-nth 3 r) (mv-nth 4 r))
                  (equal (fn-xc-ne (mv-nth 4 r)) (fn-xc-ne cells))
                  (equal (fn-xc-nw (mv-nth 4 r)) (fn-xc-nw cells)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-xc-install-window fn-xc-lo fn-xc-hi) (fn-xc-install fn-xc-install-okp))
           :use ((:instance fn-xc-success-placement (kind 2) (tokp t) (tid (nth 1 token)) (tcid 0)
                 (file (nth 2 token)) (eoff (nth 3 token)) (elen (nth 4 token))
                 (a (nth 5 token)) (b (nth 6 token)) (c 0) (d 0) (start (nth 7 token)) (trailer (nth 8 token)))
                 (:instance fn-xc-success-placement (kind 3) (tokp t) (tid (nth 1 token)) (tcid 0)
                 (file (nth 2 token)) (eoff (nth 3 token)) (elen (nth 4 token))
                 (a (nth 5 token)) (b (nth 6 token)) (c (nth 9 token)) (d (nth 10 token))
                 (start (nth 7 token)) (trailer (nth 8 token)))))))
(defthm fn-xc-entry-success-placement
  (let ((r (fn-xc-install-entry file eoff elen trailer token slots cells)))
    (implies (and (fn-xcsp slots) (fn-xccp cells) (member-equal (mv-nth 0 r) '(:installed :replaced)))
             (and (natp (mv-nth 1 r)) (< (mv-nth 1 r) (fn-xc-ne cells))
                  (fn-xcsp (mv-nth 3 r)) (fn-xccp (mv-nth 4 r))
                  (fn-xc-readyp (mv-nth 3 r) (mv-nth 4 r))
                  (equal (fn-xc-ne (mv-nth 4 r)) (fn-xc-ne cells))
                  (equal (fn-xc-nw (mv-nth 4 r)) (fn-xc-nw cells)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-xc-install-entry fn-xc-lo fn-xc-hi) (fn-xc-install fn-xc-install-okp))
           :use ((:instance fn-xc-success-placement (kind 1) (tokp nil) (tid 0) (tcid 0) (a 0) (b 0) (c 0) (d 0) (start 0))
                 (:instance fn-xc-success-placement (kind 1) (tokp t) (tid (nth 0 token)) (tcid (nth 1 token)) (a 0) (b 0) (c 0) (d 0) (start 0))))))

(defthm fn-xc-install-decoded-bytes-stores-the-pair
  (let* ((r (fn-xc-install-decoded-bytes token z slots cells wins buf))
         (row (fn-xc-row (mv-nth 1 r) (mv-nth 4 r))) (new (mv-nth 5 r)))
    (implies (and (and (fn-xcsp slots) (fn-xccp cells) (member-equal (mv-nth 0 r) '(:installed :replaced))))
             (and (equal (fn-xcw-plan row new) z)
                  (implies (and (natp j) (< j (fn-pwz-token-window-length token)))
                           (equal (nth j (nth 0 (fn-xcw-window row new))) (nth j (nth 0 buf)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-xc-row) (fn-xc-install-window fn-xc-install-entry fn-xcw-store-counted fn-xc-decoded-planp fn-xcw-plan fn-xcw-window))
           :use (fn-xc-window-success-placement
                 (:instance fn-xcw-store-counted-stores-pair
                  (row (fn-xc-row (mv-nth 1 (fn-xc-install-window token slots cells)) cells))
                  (plan z) (count (fn-pwz-token-window-length token)))))))

(defthm fn-xc-install-entry-bytes-stores-the-pair
  (let* ((r (fn-xc-install-entry-bytes file eoff elen trailer token slots cells entries stage))
         (s (mv-nth 1 r)) (new (mv-nth 5 r)))
    (implies (and (and (fn-xcsp slots) (fn-xccp cells) (member-equal (mv-nth 0 r) '(:installed :replaced))))
             (and (equal (nth s (nth 0 new)) (fn-xc-entry-key file eoff elen trailer token))
                  (equal (nth s (nth 1 new)) stage)
                  (equal (mv-nth 6 r) (nth s (nth 1 entries))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-xcw-plan fn-xcw-window fn-xc-row fn-pwz-token-window-length) (fn-xc-install-window fn-xc-install-entry fn-xcw-copy fn-xc-decoded-planp)) :use fn-xc-entry-success-placement)))

(defthm fn-xc-init-all-refuses-more-entries-than-rows
  (implies (and (natp ne) (< (fn-profile-limit :extent-cache-entries) ne))
           (equal (fn-xc-init-all ne nw slots cells) (list :refused-entry-rows slots cells)))
  :rule-classes nil)

(defthm fn-xc-init-all-refuses-more-windows-than-rows
  (implies (and (not (and (natp ne) (< (fn-profile-limit :extent-cache-entries) ne)))
                (natp nw) (< (fn-profile-limit :extent-cache-windows) nw))
           (equal (fn-xc-init-all ne nw slots cells) (list :refused-window-rows slots cells)))
  :rule-classes nil)

(defthm fn-xc-init-all-readies-all-rows
  (let ((r (fn-xc-init-all ne nw slots cells)))
    (implies (and (and (fn-xcsp slots) (fn-xccp cells) (equal (fn-xcs-count slots) 0) (equal (fn-xcc-count cells) 0))
                  (natp ne) (natp nw) (<= ne (fn-profile-limit :extent-cache-entries))
                  (<= nw (fn-profile-limit :extent-cache-windows)))
             (and (equal (mv-nth 0 r) :initialized)
                  (fn-xcsp (mv-nth 1 r)) (fn-xccp (mv-nth 2 r))
                  (fn-xc-readyp (mv-nth 1 r) (mv-nth 2 r))
                  (equal (fn-xc-ne (mv-nth 2 r)) ne) (equal (fn-xc-nw (mv-nth 2 r)) nw)
                  (<= ne (fn-xce-keys-length entries)) (<= nw (fn-xcw-plans-length wins)))) )
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-xc-init-all) (fn-xc-init)) :use (:instance fn-xc-init-initializes (fn-xcs slots) (fn-xcc cells)))))

(defthm fn-xc-install-decoded-bytes-installs-the-table-decision-round5a
  (implies (and (fn-xcsp slots) (fn-xccp cells) (fn-xc-readyp slots cells)
                (<= (fn-xc-nw cells) (fn-xcw-plans-length wins)) (fn-xc-decoded-planp z token))
           (equal (take 5 (fn-xc-install-decoded-bytes token z slots cells wins buf))
                  (fn-xc-install-window token slots cells)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-xc-install-entry-bytes fn-xc-install-decoded-bytes fn-xc-install-entry fn-xc-install-window fn-xcw-plan fn-xcw-window) :use fn-xc-install-decoded-bytes-installs-the-table-decision)))

(defthm fn-xc-install-entry-bytes-installs-the-table-decision-round5a
  (implies (and (fn-xcsp slots) (fn-xccp cells) (fn-xc-readyp slots cells)
                (<= (fn-xc-ne cells) (fn-xce-keys-length entries)) (natp elen)
                (equal (len stage) (+ elen *fn-frame-trailer-octets*)))
           (equal (take 5 (fn-xc-install-entry-bytes file eoff elen trailer token slots cells entries stage))
                  (fn-xc-install-entry file eoff elen trailer token slots cells)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-xc-install-entry-bytes fn-xc-install-decoded-bytes fn-xc-install-entry fn-xc-install-window fn-xcw-plan fn-xcw-window) :use fn-xc-install-entry-bytes-installs-the-table-decision)))

(defthm fn-xc-install-decoded-bytes-stores-the-pair-round5a
  (let* ((r (fn-xc-install-decoded-bytes token z slots cells wins buf))
         (row (fn-xc-row (mv-nth 1 r) (mv-nth 4 r))) (new (mv-nth 5 r)))
    (implies (and (fn-xcsp slots) (fn-xccp cells) (fn-xcwp wins) (fn-xc-readyp slots cells)
                  (<= (fn-xc-nw cells) (fn-xcw-plans-length wins))
                  (member-equal (mv-nth 0 r) '(:installed :replaced)))
             (and (equal (fn-xcw-plan row new) z)
                  (implies (and (natp j) (< j (fn-pwz-token-window-length token)))
                           (equal (nth j (nth 0 (fn-xcw-window row new))) (nth j (nth 0 buf)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-xc-install-entry-bytes fn-xc-install-decoded-bytes fn-xc-install-entry fn-xc-install-window fn-xcw-plan fn-xcw-window) :use fn-xc-install-decoded-bytes-stores-the-pair)))

(defthm fn-xc-install-entry-bytes-stores-the-pair-round5a
  (let* ((r (fn-xc-install-entry-bytes file eoff elen trailer token slots cells entries stage))
         (s (mv-nth 1 r)) (new (mv-nth 5 r)))
    (implies (and (fn-xcsp slots) (fn-xccp cells) (fn-xcep entries) (fn-xc-readyp slots cells)
                  (<= (fn-xc-ne cells) (fn-xce-keys-length entries))
                  (member-equal (mv-nth 0 r) '(:installed :replaced)))
             (and (equal (nth s (nth 0 new)) (fn-xc-entry-key file eoff elen trailer token))
                  (equal (nth s (nth 1 new)) stage)
                  (equal (mv-nth 6 r) (nth s (nth 1 entries))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-xc-install-entry-bytes fn-xc-install-decoded-bytes fn-xc-install-entry fn-xc-install-window fn-xcw-plan fn-xcw-window) :use fn-xc-install-entry-bytes-stores-the-pair)))
