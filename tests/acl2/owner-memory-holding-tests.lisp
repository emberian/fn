(in-package "ACL2")
(include-book "../../books/owner-memory-holding")
(include-book "../../books/owner-memory-run") ; fn-adm-installed-lease-allocation (R2 decrease fixture)
(include-book "../../books/defkeystone")
(include-book "../../books/config-observed")
(include-book "../../books/config-store-steps")
(assert-event
 (let* ((b0 (fn-adm-hh-initial))
        (b1 (fn-adm-hh-open b0 7 t)) (b2 (fn-adm-hh-close b1 7))
        (b3 (fn-adm-hh-return b2 7)) (b4 (fn-adm-hh-return b1 7))
        (b5 (fn-adm-hh-open b2 8 nil)) (b6 (fn-adm-hh-rearm b5 7 8)))
  (and (fn-adm-hhp b0) (fn-adm-hhp b1) (fn-adm-hhp b2) (fn-adm-hhp b3)
       (fn-adm-hhp b4) (fn-adm-hhp b5) (fn-adm-hhp b6)
       (fn-adm-hh-representsp b0) (fn-adm-hh-representsp b1) (fn-adm-hh-representsp b2)
       (fn-adm-hh-representsp b3) (fn-adm-hh-representsp b4) (fn-adm-hh-representsp b5)
       (fn-adm-hh-representsp b6)
       (equal (fn-adm-hh-count b0) 0) (equal (fn-adm-hh-count b1) 1)
       (equal (fn-adm-hh-count b2) 1) (equal (fn-adm-hh-count b3) 0)
       (equal (fn-adm-hh-count b4) 1) (equal (fn-adm-hh-count b5) 2)
       (equal (fn-adm-hh-count b6) 1))))

; Supporting teeth for fn-adm-hh-cached-count-is-the-union-cardinality.
; M24: the cached record accessor is plumbing, beneath the hosted held-bound claims.
(defteeth fn-adm-hh-cached-count-is-the-union-cardinality
 :claim (((representation (fn-adm-hh-representsp bank)))
  (and (no-duplicatesp-equal (fn-adm-hh-present-ids (fn-adm-hh-rows bank)))
       (equal (fn-adm-hh-count bank) (len (fn-adm-hh-present-ids (fn-adm-hh-rows bank))))))
 :subject fn-adm-hh-count
 :witness ((bank (fn-adm-hh-close (fn-adm-hh-open (fn-adm-hh-initial) 7 t) 7)))
 :breaks ((representation ((bank (fn-adm-hh-make 0 '((7 nil t)))))))
 :mutations ((logical-only-count
  (:conclusion (and (no-duplicatesp-equal (fn-adm-hh-present-ids (fn-adm-hh-rows bank)))
                    (equal 0 (len (fn-adm-hh-present-ids (fn-adm-hh-rows bank))))))
  ((bank (fn-adm-hh-close (fn-adm-hh-open (fn-adm-hh-initial) 7 t) 7)))
  :fault "a closed logical reader still owns physical disposal custody")))

; Approved whole witnesses and old-code teeth.

(defconst *m22a-config*
  (fn-config-replay 0 (fn-cnode-line-ceiling) (list *fn-cfg-default-record*)))

(defconst *m22a-opened-store*
  (fn-cpo-open-observed (list *fn-cfg-default-record*) 0 nil))

(defconst *m22a-store*
  (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-open-state *m22a-opened-store*)
     :recovery-barrier :ok) :recovery-barrier :ok) :recovery-barrier :ok))

(defconst *m22a-oc*
  (fn-ocfg-make (fn-own-start *m22a-store* 4) *m22a-config* nil nil))

(defconst *m22a-lim* (fn-exp-lim-make 8 8 0 0 0 0 0 :open))

(defconst *m22a-address* '(:inet 127 0 0 2))

(defconst *m22a-first*
  (fn-ocar-exp-open *m22a-oc* (fn-exp-initial) *m22a-lim*
                    nil nil *m22a-address* 0))

(defconst *m22a-id* (fn-exp-open-id *m22a-first*))

(defconst *m22a-closed-oc* (fn-ocfg-close (fn-exp-open-ocfg *m22a-first*) *m22a-id*))

(defconst *m22a-closed-xs* (fn-exp-release (fn-exp-open-state *m22a-first*) *m22a-id*))

(defconst *m22a-held*
  (fn-adm-hh-close (fn-adm-hh-open (fn-adm-hh-initial) *m22a-id* t) *m22a-id*))

(assert-event
  (and (fn-sn-open-okp *m22a-opened-store*) (fn-ocl-relation *m22a-oc*)
       (equal *m22a-id* 0) (fn-adm-hh-representsp *m22a-held*)
       (equal (len (fn-own-conns (fn-ocfg-owner *m22a-closed-oc*))) 0)
       (equal (fn-adm-hh-count *m22a-held*) 1)))

(assert-event
  (let* ((held (nfix (fn-adm-hh-count *m22a-held*)))
         (r (fn-adm-exposure-open *m22a-closed-oc* *m22a-closed-xs* *m22a-lim* nil nil *m22a-address* 1 *m22a-held* 2 2)))
    (and (equal (car r) :admit)
         (< held (fn-adm-reader-count 2 2))
         (equal (fn-exp-at 3 r) (1+ held))
         (equal (fn-adm-admission-held r) (1+ held)))))

(assert-event
  (let* ((held (nfix (fn-adm-hh-count *m22a-held*)))
         (r (fn-adm-peer-open *m22a-closed-oc* "peer" nil *m22a-held* 2 2)))
    (and (equal (car r) :admit)
         (< held (fn-adm-reader-count 2 2))
         (equal (fn-exp-at 3 r) (1+ held))
         (equal (fn-adm-admission-held r) (1+ held)))))

(assert-event
  (let* ((held (nfix (fn-adm-hh-count *m22a-held*)))
         (r (fn-adm-transport-rearm :exposure *m22a-closed-oc* *m22a-closed-xs*
              *m22a-lim* nil nil *m22a-address* 1 *m22a-held* *m22a-id* 1 1)))
    (and (equal (car r) :admit)
         (not (< held (fn-adm-reader-count 1 1)))
         (< (nfix (fn-adm-hh-count (fn-adm-hh-return *m22a-held* *m22a-id*)))
            (fn-adm-reader-count 1 1))
         (equal (fn-exp-at 3 r) held)
         (equal (fn-adm-admission-held r) held)
         (equal (fn-adm-admission-held r) 1))))

(assert-event
  (let* ((held (nfix (fn-adm-hh-count *m22a-held*)))
         (r (fn-adm-reader-open *m22a-closed-oc* nil *m22a-held* 2 2)))
    (and (equal (car r) :admit)
         (< held (fn-adm-reader-count 2 2))
         (equal (fn-exp-at 3 r) (1+ held))
         (equal (fn-adm-admission-held r) (1+ held)))))

(assert-event
  (let* ((held (nfix (fn-adm-hh-count *m22a-held*)))
         (lim (update-nth 1 (fn-adm-reader-count 1 1) *m22a-lim*))
         (old (fn-ocar-exp-open *m22a-closed-oc* *m22a-closed-xs*
                                lim nil nil *m22a-address* 1))
         (old-model (fn-exp-open *m22a-closed-oc* *m22a-closed-xs*
                                 lim nil nil *m22a-address* 1))
         (old-bank (fn-adm-hh-open *m22a-held* (fn-exp-open-id old) t))
         (new (fn-adm-exposure-open *m22a-closed-oc* *m22a-closed-xs*
                                    lim nil nil *m22a-address* 1 *m22a-held* 1 1)))
    (and (equal held (fn-adm-reader-count 1 1))
         (natp (fn-exp-open-id old)) (natp (fn-exp-open-id old-model))
         (equal (fn-adm-hh-count old-bank) 2)
         (not (< held (fn-adm-reader-count 1 1)))
         (equal (car new) :refuse) (equal (fn-exp-at 2 new) *m22a-held*))))

(assert-event
  (let* ((bank (fn-adm-hh-open *m22a-held* 99 t))
         (lim (update-nth 1 (fn-adm-reader-count 1 1) *m22a-lim*))
         (old (fn-ocar-exp-open *m22a-closed-oc* *m22a-closed-xs*
                                lim nil nil *m22a-address* 1))
         (peak (fn-adm-hh-open bank (fn-exp-open-id old) t))
         (after (fn-adm-hh-rearm peak *m22a-id* (fn-exp-open-id old)))
         (r (fn-adm-transport-rearm :exposure *m22a-closed-oc* *m22a-closed-xs*
              lim nil nil *m22a-address* 1 bank *m22a-id* 1 1)))
    (and (equal (fn-adm-hh-count bank) 2)
         (natp (fn-exp-open-id old))
         (equal (fn-adm-hh-count after) 2)
         (equal (car r) :refuse) (equal (fn-exp-at 2 r) bank))))

(assert-event
  (let* ((bank (fn-adm-hh-open (fn-adm-hh-initial) *m22a-id* t))
         (r (fn-adm-transport-rearm :exposure *m22a-closed-oc* *m22a-closed-xs*
              *m22a-lim* nil nil *m22a-address* 1 bank *m22a-id* 1 1)))
    (and (fn-exp-at 1 (fn-exp-lookup *m22a-id* (fn-adm-hh-rows bank)))
         (equal (car r) :refuse) (equal (fn-exp-at 2 r) bank))))

(assert-event
  (let* ((o (fn-ocfg-owner *m22a-closed-oc*)) (id (fn-own-next-id o))
         (old (fn-ocfg-open-peer *m22a-closed-oc* "peer" nil))
         (old-owner (fn-own-open-peer o "peer" (fn-ocfg-config *m22a-closed-oc*) nil))
         (zero (fn-adm-peer-open *m22a-closed-oc* "peer" nil *m22a-held* 1 0))
         (full (fn-adm-peer-open *m22a-closed-oc* "peer" nil *m22a-held* 1 1)))
    (and (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner (cdr old))))
         (fn-own-find-conn id (fn-own-conns (cdr old-owner)))
         (not (< (nfix (fn-adm-hh-count *m22a-held*)) (fn-adm-reader-count 1 0)))
         (not (< (nfix (fn-adm-hh-count *m22a-held*)) (fn-adm-reader-count 1 1)))
         (equal (car zero) :refuse) (equal (car full) :refuse)
         (equal (fn-exp-at 2 zero) *m22a-held*)
         (equal (fn-exp-at 2 full) *m22a-held*))))

(assert-event
  (let* ((id (fn-own-next-id (fn-ocfg-owner *m22a-closed-oc*)))
         (old (fn-ocfg-open-peer *m22a-closed-oc* "peer" nil))
         (r (fn-adm-transport-rearm :peer *m22a-closed-oc* nil nil nil
              "peer" nil 1 *m22a-held* *m22a-id* 1 0)))
    (and (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner (cdr old))))
         (equal (car r) :refuse) (equal (fn-exp-at 2 r) *m22a-held*))))

(assert-event
  (let* ((id (fn-own-next-id (fn-ocfg-owner *m22a-closed-oc*)))
         (old (fn-ocar-ocfg-open *m22a-closed-oc* nil))
         (full (fn-adm-reader-open *m22a-closed-oc* nil *m22a-held* 1 1))
         (zero (fn-adm-reader-open *m22a-closed-oc* nil *m22a-held* 1 0)))
    (and (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner (cdr old))))
         (not (< (nfix (fn-adm-hh-count *m22a-held*)) (fn-adm-reader-count 1 1)))
         (not (< (nfix (fn-adm-hh-count *m22a-held*)) (fn-adm-reader-count 1 0)))
         (equal (car full) :refuse) (equal (car zero) :refuse))))

(defconst *m22a-profile* *fn-heap-small-profile*)

(defconst *m22a-img* '(104857600 24117248 1090519))

(defconst *m22a-cfg* '(2 nil 8388608 8388608 nil 0 8388608 0 16384 0 nil))

(defconst *m22a-tot* '(0 0 0 0 0 0 0 0 :resident))

(defconst *m22a-limit*
  (max (fn-mm-sum *m22a-profile* *m22a-img* (fn-adm-public-readers-cfg *m22a-cfg* 2) *m22a-tot*)
       (fn-mm-reopen-need *m22a-profile* *m22a-img* (fn-adm-public-readers-cfg *m22a-cfg* 2) *m22a-tot*)))

(assert-event
  (let* ((run-cfg (update-nth 10 nil (true-list-fix *m22a-cfg*)))
         (configured (fn-mm-cfg-connections run-cfg))
         (capacity (fn-adm-installed-capacity *m22a-profile* *m22a-img*
                                               run-cfg *m22a-limit* *m22a-tot*))
         (reader-count (fn-adm-reader-count configured capacity))
         (exposure (fn-adm-exposure-open *m22a-closed-oc* *m22a-closed-xs*
                     *m22a-lim* nil nil *m22a-address* 1 *m22a-held* configured capacity))
         (peer-open (fn-adm-peer-open *m22a-closed-oc* "peer" nil
                                     *m22a-held* configured capacity))
         (rearm (fn-adm-transport-rearm :exposure *m22a-closed-oc* *m22a-closed-xs*
                  *m22a-lim* nil nil *m22a-address* 1 *m22a-held* *m22a-id* configured capacity))
         (reader (fn-adm-reader-open *m22a-closed-oc* nil *m22a-held* configured capacity)))
    (and (equal capacity 2)
         (fn-mm-gate-p *m22a-profile* *m22a-img* (fn-adm-cfg-at run-cfg capacity)
                        *m22a-limit* *m22a-tot*)
         (equal (car exposure) :admit)
         (<= (fn-exp-at 3 exposure) reader-count)
         (<= (fn-adm-admission-held exposure) reader-count)
         (equal (fn-adm-priced-connections (fn-adm-admission-held exposure) configured capacity) reader-count)
         (fn-mm-gate-p *m22a-profile* *m22a-img*
           (fn-adm-priced-cfg run-cfg (fn-adm-admission-held exposure) capacity)
           *m22a-limit* *m22a-tot*)
         (equal (car peer-open) :admit)
         (<= (fn-exp-at 3 peer-open) reader-count)
         (<= (fn-adm-admission-held peer-open) reader-count)
         (equal (fn-adm-priced-connections (fn-adm-admission-held peer-open) configured capacity) reader-count)
         (fn-mm-gate-p *m22a-profile* *m22a-img*
           (fn-adm-priced-cfg run-cfg (fn-adm-admission-held peer-open) capacity)
           *m22a-limit* *m22a-tot*)
         (equal (car rearm) :admit)
         (equal (fn-exp-at 3 rearm) (nfix (fn-adm-hh-count *m22a-held*)))
         (equal (fn-adm-admission-held rearm) (nfix (fn-adm-hh-count *m22a-held*)))
         (<= (fn-exp-at 3 rearm) reader-count)
         (<= (fn-adm-admission-held rearm) reader-count)
         (equal (fn-adm-priced-connections (fn-adm-admission-held rearm) configured capacity) reader-count)
         (fn-mm-gate-p *m22a-profile* *m22a-img*
           (fn-adm-priced-cfg run-cfg (fn-adm-admission-held rearm) capacity)
           *m22a-limit* *m22a-tot*)
         (equal (car reader) :admit)
         (<= (fn-exp-at 3 reader) reader-count)
         (<= (fn-adm-admission-held reader) reader-count)
         (equal (fn-adm-priced-connections (fn-adm-admission-held reader) configured capacity) reader-count)
         (fn-mm-gate-p *m22a-profile* *m22a-img*
           (fn-adm-priced-cfg run-cfg (fn-adm-admission-held reader) capacity)
           *m22a-limit* *m22a-tot*))))

(assert-event
  (let* ((cfg (fn-adm-cfg-at *m22a-cfg* 1))
         (priced (fn-adm-public-readers-cfg cfg 1))
         (limit (max (fn-mm-sum *m22a-profile* *m22a-img* priced *m22a-tot*)
                     (fn-mm-reopen-need *m22a-profile* *m22a-img* priced *m22a-tot*)))
         (capacity (fn-adm-installed-capacity *m22a-profile* *m22a-img* cfg limit *m22a-tot*))
         (lim (update-nth 1 (fn-adm-reader-count 1 capacity) *m22a-lim*))
         (extra-id (fn-own-next-id (fn-ocfg-owner *m22a-closed-oc*)))
         (extra (fn-ocar-ocfg-open *m22a-closed-oc* nil))
         (ended-oc (fn-ocfg-close (cdr extra) extra-id))
         (bank (fn-adm-hh-close (fn-adm-hh-open *m22a-held* extra-id t) extra-id))
         (old (fn-ocar-exp-open ended-oc *m22a-closed-xs* lim nil nil *m22a-address* 1))
         (next-bank (fn-adm-hh-open bank (fn-exp-open-id old) t))
         (next-held (nfix (fn-adm-hh-count next-bank))))
    (and (equal capacity 1)
         (fn-mm-gate-p *m22a-profile* *m22a-img* (fn-adm-cfg-at cfg capacity) limit *m22a-tot*)
         (fn-adm-hh-representsp bank)
         (natp (fn-exp-open-id old)) (equal next-held 3)
         (not (<= next-held (fn-adm-reader-count 1 capacity)))
         (not (equal (fn-adm-priced-connections next-held 1 capacity)
                     (fn-adm-reader-count 1 capacity)))
         (not (fn-mm-gate-p *m22a-profile* *m22a-img*
                (fn-adm-priced-cfg cfg next-held capacity) limit *m22a-tot*)))))

; Removal tooth: the bank type recognizer is necessary.
(defconst *m23-bad-count-bank*
  (fn-adm-hh-make 0 (fn-adm-hh-rows *m22a-held*)))
(assert-event
  (let* ((bank *m23-bad-count-bank*)
         (held (nfix (fn-adm-hh-count bank)))
         (returned (fn-adm-hh-return bank *m22a-id*))
         (r (fn-adm-transport-rearm :exposure *m22a-closed-oc* *m22a-closed-xs*
              *m22a-lim* nil nil *m22a-address* 1 bank *m22a-id* 1 1)))
    (and (not (fn-adm-hhp bank))
         (equal held 0)
         (equal (fn-adm-hh-rows bank) (list (list *m22a-id* nil t)))
         (equal (fn-adm-hh-count returned) 0)
         (equal (fn-adm-hh-rows returned) nil)
         (equal (car r) :admit)
         (equal (fn-exp-at 3 r) 1)
         (equal (fn-adm-admission-held r) 1)
         (not
           (and (< (nfix (fn-adm-hh-count returned)) (fn-adm-reader-count 1 1))
                (equal (fn-exp-at 3 r) held)
                (equal (fn-adm-admission-held r) held))))))


(defkeystone m24t-exposure-open-admits-below-held-reader-bound
 (let* ((held (nfix (fn-adm-hh-count bank)))
         (r (fn-adm-exposure-open oc xs lim acfg peer address now
                                  bank configured capacity)))
    (implies (equal (car r) :admit)
      (and (< held (fn-adm-reader-count configured capacity))
           (equal (fn-exp-at 3 r) (1+ held))
           (equal (fn-adm-admission-held r) (1+ held)))))
 :id "PRF-10017" :restates fn-adm-exposure-open-admits-below-held-reader-bound :subject fn-adm-exposure-open
  :hyps (admitted)
 :breaks ((admitted ((configured 1) (capacity 1))))
 :witness ((oc *m22a-closed-oc*) (xs *m22a-closed-xs*) (lim *m22a-lim*)
 (acfg nil) (peer nil) (address *m22a-address*) (now 1) (bank *m22a-held*)
 (configured 2) (capacity 2))
 :mutations ((retired-admission (:conclusion (equal (fn-adm-admission-held r) (len (fn-own-conns (fn-ocfg-owner (fn-exp-open-ocfg (fn-exp-at 1 r))))))) () :fault "The old logical-reader count misses the ended transport still held."))
 :rule-classes nil
 :hints (("Goal" :by fn-adm-exposure-open-admits-below-held-reader-bound)))

(defkeystone m24t-peer-open-admits-below-held-reader-bound
 (let* ((held (nfix (fn-adm-hh-count bank)))
         (r (fn-adm-peer-open oc peer acfg bank configured capacity)))
    (implies (equal (car r) :admit)
      (and (< held (fn-adm-reader-count configured capacity))
           (equal (fn-exp-at 3 r) (1+ held))
           (equal (fn-adm-admission-held r) (1+ held)))))
 :id "PRF-10017" :restates fn-adm-peer-open-admits-below-held-reader-bound :subject fn-adm-peer-open
  :hyps (admitted)
 :breaks ((admitted ((configured 1) (capacity 1))))
 :witness ((oc *m22a-closed-oc*) (xs *m22a-closed-xs*) (lim *m22a-lim*)
 (acfg nil) (peer "peer") (address *m22a-address*) (now 1) (bank *m22a-held*)
 (configured 2) (capacity 2))
 :mutations ((retired-admission (:conclusion (equal (fn-adm-admission-held r) (len (fn-own-conns (fn-ocfg-owner (cdr (fn-exp-at 1 r))))))) () :fault "The old logical-reader count misses the ended transport still held."))
 :rule-classes nil
 :hints (("Goal" :by fn-adm-peer-open-admits-below-held-reader-bound)))

(defkeystone m24t-transport-rearm-admits-below-held-reader-bound
 (let* ((held (nfix (fn-adm-hh-count bank)))
         (r (fn-adm-transport-rearm kind oc xs lim acfg peer address now
                                    bank old-id configured capacity)))
    (implies (and (fn-adm-hhp bank) (equal (car r) :admit))
      (and (< (nfix (fn-adm-hh-count (fn-adm-hh-return bank old-id)))
              (fn-adm-reader-count configured capacity))
           (equal (fn-exp-at 3 r) held)
           (equal (fn-adm-admission-held r) held))))
 :id "PRF-10017" :restates fn-adm-transport-rearm-admits-below-held-reader-bound :subject fn-adm-transport-rearm
  :hyps (bank-type admitted)
 :breaks ((bank-type ((bank *m23-bad-count-bank*)) :logical
            "Removing the carried record type permits a stale cached count.")
          (admitted ((capacity 0))))
 :witness ((oc *m22a-closed-oc*) (xs *m22a-closed-xs*) (lim *m22a-lim*)
 (acfg nil) (peer nil) (address *m22a-address*) (now 1) (bank *m22a-held*)
 (configured 1) (capacity 1) (kind :exposure) (old-id *m22a-id*))
 :mutations ((retired-admission (:conclusion (< held (fn-adm-reader-count configured capacity))) () :fault "The strict pre-check on the untransferred bank counts keep-alive custody twice."))
 :rule-classes nil
 :hints (("Goal" :by fn-adm-transport-rearm-admits-below-held-reader-bound)))

(defkeystone m24t-reader-open-admits-below-held-reader-bound
 (let* ((held (nfix (fn-adm-hh-count bank)))
         (r (fn-adm-reader-open oc acfg bank configured capacity)))
    (implies (equal (car r) :admit)
      (and (< held (fn-adm-reader-count configured capacity))
           (equal (fn-exp-at 3 r) (1+ held))
           (equal (fn-adm-admission-held r) (1+ held)))))
 :id "PRF-10017" :restates fn-adm-reader-open-admits-below-held-reader-bound :subject fn-adm-reader-open
  :hyps (admitted)
 :breaks ((admitted ((configured 1) (capacity 1))))
 :witness ((oc *m22a-closed-oc*) (xs *m22a-closed-xs*) (lim *m22a-lim*)
 (acfg nil) (peer nil) (address *m22a-address*) (now 1) (bank *m22a-held*)
 (configured 2) (capacity 2))
 :mutations ((retired-admission (:conclusion (equal (fn-adm-admission-held r) (len (fn-own-conns (fn-ocfg-owner (cdr (fn-exp-at 1 r))))))) () :fault "The old logical-reader count misses the ended transport still held."))
 :rule-classes nil
 :hints (("Goal" :by fn-adm-reader-open-admits-below-held-reader-bound)))

(defkeystone m24t-held-admissions-compose-with-installed-capacity
 (let* ((run-cfg (update-nth 10 nil (true-list-fix cfg))) (configured (fn-mm-cfg-connections run-cfg)) (capacity (fn-adm-installed-capacity profile img run-cfg limit tot)) (reader-count (fn-adm-reader-count configured capacity)) (exposure (fn-adm-exposure-open oc xs lim acfg peer address now bank configured capacity)) (peer-open (fn-adm-peer-open oc peer acfg bank configured capacity)) (rearm (fn-adm-transport-rearm kind oc xs lim acfg peer address now bank old-id configured capacity)) (reader (fn-adm-reader-open oc acfg bank configured capacity)) (operator (fn-adm-operator-open oc acfg bank configured capacity operator-id profile img run-cfg limit tot))) (and (implies (equal (car exposure) :admit) (and (<= (fn-exp-at 3 exposure) reader-count) (<= (fn-adm-admission-held exposure) reader-count) (equal (fn-adm-priced-connections (fn-adm-admission-held exposure) configured capacity) reader-count) (fn-mm-gate-p profile img (fn-adm-priced-cfg run-cfg (fn-adm-admission-held exposure) capacity) limit tot))) (implies (equal (car peer-open) :admit) (and (<= (fn-exp-at 3 peer-open) reader-count) (<= (fn-adm-admission-held peer-open) reader-count) (equal (fn-adm-priced-connections (fn-adm-admission-held peer-open) configured capacity) reader-count) (fn-mm-gate-p profile img (fn-adm-priced-cfg run-cfg (fn-adm-admission-held peer-open) capacity) limit tot))) (implies (equal (car rearm) :admit) (and (<= (fn-exp-at 3 rearm) reader-count) (<= (fn-adm-admission-held rearm) reader-count) (equal (fn-adm-priced-connections (fn-adm-admission-held rearm) configured capacity) reader-count) (fn-mm-gate-p profile img (fn-adm-priced-cfg run-cfg (fn-adm-admission-held rearm) capacity) limit tot))) (implies (equal (car reader) :admit) (and (<= (fn-exp-at 3 reader) reader-count) (<= (fn-adm-admission-held reader) reader-count) (equal (fn-adm-priced-connections (fn-adm-admission-held reader) configured capacity) reader-count) (fn-mm-gate-p profile img (fn-adm-priced-cfg run-cfg (fn-adm-admission-held reader) capacity) limit tot))) (implies (equal (car operator) :admit) (and (equal (fn-adm-admission-held operator) (1+ (nfix (fn-adm-hh-count bank)))) (or (and (<= (fn-adm-admission-held operator) reader-count) (equal (fn-exp-at 6 operator) operator-id)) (and (fn-adm-operator-slot-freep operator-id) (equal (fn-exp-at 6 operator) (fn-exp-at 4 operator)) (fn-adm-operator-fundedp profile img run-cfg limit tot capacity))) (fn-mm-gate-p profile img (fn-adm-priced-cfg run-cfg (fn-adm-admission-held operator) capacity) limit tot)))))
 :id "PRF-10017" :restates fn-adm-held-admissions-compose-with-installed-capacity :subject fn-adm-operator-open

 :witness ((oc *m22a-closed-oc*) (xs *m22a-closed-xs*) (lim *m22a-lim*)
 (acfg nil) (peer "peer") (address *m22a-address*) (now 1) (bank *m22a-held*)
 (configured 2) (capacity 2) (profile *m22a-profile*) (img *m22a-img*) (cfg *m22a-cfg*)
   (limit *m22a-limit*) (tot *m22a-tot*) (old-id *m22a-id*) (kind :exposure) (operator-id nil))
 :mutations ((retired-admission (:conclusion (let* ((run-cfg (update-nth 10 nil (true-list-fix cfg)))
         (configured (fn-mm-cfg-connections run-cfg))
         (capacity (fn-adm-installed-capacity profile img run-cfg limit tot))
         (reader-count (fn-adm-reader-count configured capacity))
         (exposure (fn-adm-exposure-open oc xs lim acfg peer address now
                                         bank configured capacity))
         (peer-open (fn-adm-peer-open oc peer acfg bank configured capacity))
         (rearm (fn-adm-transport-rearm kind oc xs lim acfg peer address now
                                        bank old-id configured capacity))
         (reader (fn-adm-reader-open oc acfg bank configured capacity)))
   (declare (ignorable exposure peer-open rearm reader-count))
   (equal (fn-adm-admission-held reader)
          (len (fn-own-conns (fn-ocfg-owner (cdr (fn-exp-at 1 reader)))))))) () :fault "The retired logical-only count omits ended physical custody."))
 :rule-classes nil
 :hints (("Goal" :by fn-adm-held-admissions-compose-with-installed-capacity)))




; M28 whole STEP 5 teeth: real model/owner producers and checked mutants.
(include-book "../../books/catalog-record")
(defun m28-tooth-row (n)
 (declare (xargs :guard t :verify-guards nil))
 (with-local-stobj fn-arena
  (mv-let (row fn-arena)
   (fn-cat-intern-list
    (fn-record-make 0 0 0 "<m28-step5@example.invalid>"
      (make-list (nfix n) :initial-element 65) '("fn.test") "o0" "s0" "e0" (nfix n) 841000011)
    nil 0 fn-arena)
   row)))
(defconst *m28-row* (m28-tooth-row 4))
(defconst *m28-after* (fn-adm-after *m22a-tot* *m28-row*))
(defconst *m28-limit0* (max
 (fn-mm-sum *m22a-profile* *m22a-img* (fn-adm-cfg-at *m22a-cfg* 0) *m22a-tot*)
 (fn-mm-reopen-need *m22a-profile* *m22a-img* (fn-adm-cfg-at *m22a-cfg* 0) *m22a-tot*)))
(defconst *m28-limit2* (max
 (fn-mm-sum *m22a-profile* *m22a-img* (fn-adm-priced-cfg *m22a-cfg* 2 2) *m22a-tot*)
 (fn-mm-reopen-need *m22a-profile* *m22a-img* (fn-adm-priced-cfg *m22a-cfg* 2 2) *m22a-tot*)))
(defconst *m28-limit3* (max
 (fn-mm-sum *m22a-profile* *m22a-img* (fn-adm-priced-cfg *m22a-cfg* 3 2) *m22a-tot*)
 (fn-mm-reopen-need *m22a-profile* *m22a-img* (fn-adm-priced-cfg *m22a-cfg* 3 2) *m22a-tot*)))
(defconst *m28-limit4* (max
 (fn-mm-sum *m22a-profile* *m22a-img* (fn-adm-priced-cfg *m22a-cfg* 4 2) *m22a-tot*)
 (fn-mm-reopen-need *m22a-profile* *m22a-img* (fn-adm-priced-cfg *m22a-cfg* 4 2) *m22a-tot*)))
(defconst *m28-after-limit2* (max
 (fn-mm-sum *m22a-profile* *m22a-img* (fn-adm-priced-cfg *m22a-cfg* 2 2) *m28-after*)
 (fn-mm-reopen-need *m22a-profile* *m22a-img* (fn-adm-priced-cfg *m22a-cfg* 2 2) *m28-after*)))
(defconst *m28-after-limit3* (max
 (fn-mm-sum *m22a-profile* *m22a-img* (fn-adm-priced-cfg *m22a-cfg* 3 2) *m28-after*)
 (fn-mm-reopen-need *m22a-profile* *m22a-img* (fn-adm-priced-cfg *m22a-cfg* 3 2) *m28-after*)))
(defconst *m28-after-limit4* (max
 (fn-mm-sum *m22a-profile* *m22a-img* (fn-adm-priced-cfg *m22a-cfg* 4 2) *m28-after*)
 (fn-mm-reopen-need *m22a-profile* *m22a-img* (fn-adm-priced-cfg *m22a-cfg* 4 2) *m28-after*)))
(defconst *m28-oc0*
 (fn-ocfg-make (fn-own-start *m22a-store* 3) *m22a-config* nil nil))
(defconst *m28-r1* (fn-adm-reader-open *m28-oc0* nil (fn-adm-hh-initial) 2 2))
(defconst *m28-oc1* (cdr (fn-exp-at 1 *m28-r1*)))
(defconst *m28-b1* (fn-exp-at 2 *m28-r1*))
(defconst *m28-r2* (fn-adm-reader-open *m28-oc1* nil *m28-b1* 2 2))
(defconst *m28-oc2* (cdr (fn-exp-at 1 *m28-r2*)))
(defconst *m28-b2* (fn-exp-at 2 *m28-r2*))
(defconst *m28-tight-oc0*
 (fn-ocfg-make (fn-own-start *m22a-store* 2) *m22a-config* nil nil))
(defconst *m28-tight-r1* (fn-adm-reader-open *m28-tight-oc0* nil (fn-adm-hh-initial) 2 2))
(defconst *m28-tight-oc1* (cdr (fn-exp-at 1 *m28-tight-r1*)))
(defconst *m28-tight-b1* (fn-exp-at 2 *m28-tight-r1*))
(defconst *m28-tight-r2* (fn-adm-reader-open *m28-tight-oc1* nil *m28-tight-b1* 2 2))
(defconst *m28-tight-oc2* (cdr (fn-exp-at 1 *m28-tight-r2*)))
(defconst *m28-tight-b2* (fn-exp-at 2 *m28-tight-r2*))
(defconst *m28-slot*
 (fn-adm-operator-open *m28-oc2* nil *m28-b2* 2 2 nil *m22a-profile* *m22a-img*
   *m22a-cfg* *m28-limit3* *m22a-tot*))
(defconst *m28-slot-oc* (cdr (fn-exp-at 1 *m28-slot*)))
(defconst *m28-slot-bank* (fn-exp-at 2 *m28-slot*))
(defconst *m28-slot-id* (fn-exp-at 6 *m28-slot*))
(defun m28-operator-reader-first
  (oc acfg bank configured capacity operator-id profile img cfg limit tot)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((held (nfix (fn-adm-hh-count bank)))
         (id (fn-own-next-id (fn-ocfg-owner oc)))
         (priced (fn-adm-priced-cfg cfg (1+ held) capacity)))
    (cond
      ((< held (fn-adm-reader-count configured capacity))
       (let ((r (fn-adm-reader-open oc acfg bank configured capacity)))
         (if (equal (car r) :admit)
           (list :admit (fn-exp-at 1 r) (fn-exp-at 2 r) (fn-exp-at 3 r) (fn-exp-at 4 r) nil (fn-exp-at 4 r))
           (list :refuse (fn-exp-at 1 r) bank held nil :operator-owner-bound operator-id))))
      ((not (fn-adm-operator-slot-freep operator-id))
       (fn-adm-operator-open-refusal oc bank operator-id :operator-slot-held))
      ((not (equal (fn-mm-cfg-connections cfg) (nfix configured)))
       (fn-adm-operator-open-refusal oc bank operator-id :operator-cfg-stale))
      ((or (not (natp id))
           (fn-exp-lookup id (fn-adm-hh-rows bank))
           (not (fn-adm-operator-fundedp profile img cfg limit tot capacity))
           (not (fn-mm-gate-p profile img priced limit tot)))
       (fn-adm-operator-open-refusal oc bank operator-id :operator-slot-memory))
      (t
       (let ((opened (fn-ocar-ocfg-open oc acfg)))
         (if (and (equal (fn-own-next-id (fn-ocfg-owner (cdr opened))) (1+ id))
                  (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner (cdr opened)))))
           (list :admit opened (fn-adm-hh-open bank id nil) (1+ held) id nil id)
           (fn-adm-operator-open-refusal oc bank operator-id :operator-owner-bound)))))))

(defun m28-operator-without-slot-check
  (oc acfg bank configured capacity operator-id profile img cfg limit tot)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((held (nfix (fn-adm-hh-count bank)))
         (id (fn-own-next-id (fn-ocfg-owner oc)))
         (priced (fn-adm-priced-cfg cfg (1+ held) capacity)))
    (cond
      ((< held (fn-adm-reader-count configured capacity))
       (let ((r (fn-adm-reader-open oc acfg bank configured capacity)))
         (if (equal (car r) :admit)
           (list :admit (fn-exp-at 1 r) (fn-exp-at 2 r) (fn-exp-at 3 r) (fn-exp-at 4 r) nil operator-id)
           (list :refuse (fn-exp-at 1 r) bank held nil :operator-owner-bound operator-id))))

      ((not (equal (fn-mm-cfg-connections cfg) (nfix configured)))
       (fn-adm-operator-open-refusal oc bank operator-id :operator-cfg-stale))
      ((or (not (natp id))
           (fn-exp-lookup id (fn-adm-hh-rows bank))
           (not (fn-adm-operator-fundedp profile img cfg limit tot capacity))
           (not (fn-mm-gate-p profile img priced limit tot)))
       (fn-adm-operator-open-refusal oc bank operator-id :operator-slot-memory))
      (t
       (let ((opened (fn-ocar-ocfg-open oc acfg)))
         (if (and (equal (fn-own-next-id (fn-ocfg-owner (cdr opened))) (1+ id))
                  (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner (cdr opened)))))
           (list :admit opened (fn-adm-hh-open bank id nil) (1+ held) id nil id)
           (fn-adm-operator-open-refusal oc bank operator-id :operator-owner-bound)))))))

(defun m28-operator-borrowed-slot
  (oc acfg bank configured capacity operator-id profile img cfg limit tot)
  (declare (xargs :guard t :verify-guards nil) (ignore profile img limit tot))
  (let* ((held (nfix (fn-adm-hh-count bank)))
         (id (fn-own-next-id (fn-ocfg-owner oc)))
         (priced (fn-adm-priced-cfg cfg (1+ held) capacity)))
    (declare (ignore priced))
    (cond
      ((< held (fn-adm-reader-count configured capacity))
       (let ((r (fn-adm-reader-open oc acfg bank configured capacity)))
         (if (equal (car r) :admit)
           (list :admit (fn-exp-at 1 r) (fn-exp-at 2 r) (fn-exp-at 3 r) (fn-exp-at 4 r) nil operator-id)
           (list :refuse (fn-exp-at 1 r) bank held nil :operator-owner-bound operator-id))))
      ((not (fn-adm-operator-slot-freep operator-id))
       (fn-adm-operator-open-refusal oc bank operator-id :operator-slot-held))
      ((not (equal (fn-mm-cfg-connections cfg) (nfix configured)))
       (fn-adm-operator-open-refusal oc bank operator-id :operator-cfg-stale))
      ((or (not (natp id))
           (fn-exp-lookup id (fn-adm-hh-rows bank))
)
       (fn-adm-operator-open-refusal oc bank operator-id :operator-slot-memory))
      (t
       (let ((opened (fn-ocar-ocfg-open oc acfg)))
         (if (and (equal (fn-own-next-id (fn-ocfg-owner (cdr opened))) (1+ id))
                  (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner (cdr opened)))))
           (list :admit opened (fn-adm-hh-open bank id nil) (1+ held) id nil id)
           (fn-adm-operator-open-refusal oc bank operator-id :operator-owner-bound)))))))

; Close both public readers after the legal saturated slot admission.
; The remaining private row reaches below saturation through real closes.
(defconst *m28-zero-slot-oc*
 (fn-ocfg-close (fn-ocfg-close *m28-slot-oc* 0) 1))
(defconst *m28-zero-slot-bank*
 (fn-adm-hh-close (fn-adm-hh-close *m28-slot-bank* 0) 1))
(defconst *m28-zero-slot-id* *m28-slot-id*)

(defconst *m28-edge-row* (m28-tooth-row (fn-bs-profile-max-article-octets *m22a-profile*)))
(defconst *m28-edge-next* (m28-tooth-row (1+ (fn-bs-profile-max-article-octets *m22a-profile*))))
(defconst *m28-edge-after* (fn-adm-after *m22a-tot* *m28-edge-row*))
(defconst *m28-edge-limit*
 (max (fn-mm-sum *m22a-profile* *m22a-img* (fn-adm-priced-cfg *m22a-cfg* 3 2) *m28-edge-after*)
      (fn-mm-reopen-need *m22a-profile* *m22a-img* (fn-adm-priced-cfg *m22a-cfg* 3 2) *m28-edge-after*)))


(defkeystone m28-capacity-is-nil-exactly-when-no-slot-fits
(iff (fn-adm-capacity profile img cfg limit tot)
       (fn-mm-gate-p profile img (fn-adm-public-readers-cfg cfg 0) limit tot))
 :id "PRF-100002" :restates fn-adm-capacity-is-nil-exactly-when-no-slot-fits :subject fn-adm-capacity :rule-classes nil
 :witness ((oc *m28-oc2*) (acfg nil) (bank *m28-b2*) (configured 2) (capacity 2) (operator-id nil) (profile *m22a-profile*) (img *m22a-img*) (cfg *m22a-cfg*) (limit *m28-limit3*) (tot *m22a-tot*) (held 2) (row *m28-row*) (id 2))
 :mutations ((old-zero-total-search (:conclusion (iff (fn-adm-capacity-search-top profile img cfg limit tot) (fn-mm-gate-p profile img (fn-adm-public-readers-cfg cfg 0) limit tot))) ((limit *m28-limit0*)) :fault "the retired total-zero search finds 0 when the private slot cannot fit"))
 :hints (("Goal" :by fn-adm-capacity-is-nil-exactly-when-no-slot-fits)))


(defkeystone m28-operator-open-admits-exactly-a-free-funded-slot
(let* ((held (nfix (fn-adm-hh-count bank)))
        (id (fn-own-next-id (fn-ocfg-owner oc)))
        (opened (fn-ocar-ocfg-open oc acfg))
        (r (fn-adm-operator-open oc acfg bank configured capacity operator-id profile img cfg limit tot)))
  (equal (equal (car r) :admit)
   (if (< held (fn-adm-reader-count configured capacity))
     (equal (car (fn-adm-reader-open oc acfg bank configured capacity)) :admit)
     (and (fn-adm-operator-slot-freep operator-id)
          (equal (fn-mm-cfg-connections cfg) (nfix configured))
          (natp id) (not (fn-exp-lookup id (fn-adm-hh-rows bank)))
          (fn-adm-operator-fundedp profile img cfg limit tot capacity)
          (fn-mm-gate-p profile img (fn-adm-priced-cfg cfg (1+ held) capacity) limit tot)
          (equal (fn-own-next-id (fn-ocfg-owner (cdr opened))) (1+ id))
          (and (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner (cdr opened)))) t)))))
 :id "PRF-100003" :restates fn-adm-operator-open-admits-exactly-a-free-funded-slot :subject fn-adm-operator-open :rule-classes nil
 :witness ((oc *m28-oc2*) (acfg nil) (bank *m28-b2*) (configured 2) (capacity 2) (operator-id nil) (profile *m22a-profile*) (img *m22a-img*) (cfg *m22a-cfg*) (limit *m28-limit3*) (tot *m22a-tot*) (held 2) (row *m28-row*) (id 2))
 :mutations ((borrowed-slot (:conclusion
  (let* ((held (nfix (fn-adm-hh-count bank)))
         (id (fn-own-next-id (fn-ocfg-owner oc)))
         (opened (fn-ocar-ocfg-open oc acfg))
         (r (fn-adm-operator-open oc acfg bank configured capacity operator-id profile img cfg limit tot)))
   (equal (equal (car r) :admit)
    (if (< held (fn-adm-reader-count configured capacity))
     (equal (car (fn-adm-reader-open oc acfg bank configured capacity)) :admit)
     (and (fn-adm-operator-slot-freep operator-id)
          (equal (fn-mm-cfg-connections cfg) (nfix configured))
          (natp id) (not (fn-exp-lookup id (fn-adm-hh-rows bank)))
          (equal (fn-own-next-id (fn-ocfg-owner (cdr opened))) (1+ id))
          (and (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner (cdr opened)))) t)))))) ((tot *m28-after*)) :fault "a legal initial run loses the slot if an old held-only record admission consumes its funding"))
 :hints (("Goal" :by fn-adm-operator-open-admits-exactly-a-free-funded-slot)))


(defkeystone m28-operator-refusal-is-named
(let ((r (fn-adm-operator-open oc acfg bank configured capacity operator-id profile img cfg limit tot)))
  (implies (equal (car r) :refuse)
   (member-eq (fn-adm-operator-open-reason r)
              '(:operator-slot-held :operator-slot-memory :operator-owner-bound :operator-cfg-stale))))
 :id "PRF-100004" :restates fn-adm-operator-refusal-is-named :subject fn-adm-operator-open :rule-classes nil
 :witness ((oc *m28-slot-oc*) (acfg nil) (bank *m28-slot-bank*) (configured 2) (capacity 2) (operator-id *m28-slot-id*) (profile *m22a-profile*) (img *m22a-img*) (cfg *m22a-cfg*) (limit *m28-limit3*) (tot *m22a-tot*) (held 2) (row *m28-row*) (id 2))
 :hyps (refused)
 :breaks ((refused ((oc *m28-oc0*) (bank (fn-adm-hh-initial)) (operator-id nil) (held 0))))
 :mutations ((host-none (:conclusion (equal (fn-adm-operator-open-reason r) :none)) () :fault "the old private-control path invents :none instead of forwarding the ACL2 refusal"))
 :hints (("Goal" :by fn-adm-operator-refusal-is-named)))


(defkeystone m28-operator-open-below-saturation-is-the-reader-open
(let ((r (fn-adm-operator-open oc acfg bank configured capacity operator-id profile img cfg limit tot))
        (q (fn-adm-reader-open oc acfg bank configured capacity)))
    (implies (< (nfix (fn-adm-hh-count bank)) (fn-adm-reader-count configured capacity))
      (and (equal (car r) (car q))
           (equal (fn-exp-at 1 r) (fn-exp-at 1 q))
           (equal (fn-exp-at 2 r) (fn-exp-at 2 q))
           (equal (fn-exp-at 3 r) (fn-exp-at 3 q))
           (equal (fn-exp-at 4 r) (fn-exp-at 4 q))
           (equal (fn-exp-at 6 r) operator-id))))
 :id "PRF-100005" :restates fn-adm-operator-open-below-saturation-is-the-reader-open :subject fn-adm-operator-open :rule-classes nil
 :witness ((oc *m28-oc0*) (acfg nil) (bank (fn-adm-hh-initial)) (configured 2) (capacity 2) (operator-id nil) (profile *m22a-profile*) (img *m22a-img*) (cfg *m22a-cfg*) (limit *m28-limit3*) (tot *m22a-tot*) (held 0) (row *m28-row*) (id 2))
 :hyps (below)
 :breaks ((below ((oc *m28-oc2*) (bank *m28-b2*))))
 :mutations ((reader-first-slot (:conclusion (equal (fn-exp-at 6 r) (fn-exp-at 4 r))) () :fault "taking the reserved slot for an ordinary reader open changes its NIL cached operator id"))
 :hints (("Goal" :by fn-adm-operator-open-below-saturation-is-the-reader-open)))


; R1 executable mutation: exactly the run gate with the free-slot term removed.
(defun m28-run-gate-without-free-slot (held configured capacity operator-id)
 (declare (xargs :guard t) (ignore operator-id))
 (if (natp capacity)
     (max (nfix held) (1+ (fn-adm-reader-count configured capacity)))
   (nfix held)))

(defkeystone m28-run-gate-keeps-the-operator-slot-funded
(implies (and (natp capacity)
                (fn-mm-gate-p profile img
                  (fn-adm-priced-cfg cfg (fn-adm-run-gate-held held (fn-mm-cfg-connections cfg) capacity operator-id)
                                     capacity)
                  limit tot))
           (fn-mm-gate-p profile img
             (fn-adm-priced-cfg cfg (+ (nfix held) (if operator-id 0 1)) capacity) limit tot))
 :id "PRF-100006" :restates fn-adm-run-gate-keeps-the-operator-slot-funded :subject fn-adm-run-gate-held :rule-classes nil
 :witness ((capacity 2) (operator-id nil) (profile *m22a-profile*) (img *m22a-img*)
           (cfg *m22a-cfg*) (limit *m28-limit4*) (tot *m22a-tot*) (held 3) (row *m28-row*))
 :hyps (capacity holding)
 :breaks ((capacity ((capacity nil) (held 2) (limit *m28-limit2*)))
          (holding ((limit 0))))
 :mutations ((old-held-only-gate
   (:hypothesis holding (fn-mm-gate-p profile img (fn-adm-priced-cfg cfg held capacity) limit tot))
   ((held 2) (limit *m28-limit2*)) :fault "the former held-only gate consumes the free slot")
  (without-free-slot-gate
   (:hypothesis holding (fn-mm-gate-p profile img (fn-adm-priced-cfg cfg (m28-run-gate-without-free-slot held (fn-mm-cfg-connections cfg) capacity operator-id) capacity) limit tot))
   ((held 3) (limit *m28-limit3*)) :fault "after decreasing public capacity to 2, price 3 leaves the operator's fourth place unfunded"))
 :hints (("Goal" :by fn-adm-run-gate-keeps-the-operator-slot-funded)))


; The old-held-only-admission tooth needs a gap (O8's measurement in the merged OVER world, 10-14): at
; *m28-after-limit2* the row fits beside two held readers, and three holders after it are unfunded.  The
; limit is derived, so a pricing under which one holder no longer separates them fails here by name,
; instead of leaving the mutant vacuous.
(assert-event
 (and (fn-adm-memory-admitp *m22a-profile* *m22a-img* (fn-adm-priced-cfg *m22a-cfg* 2 2)
                            *m28-after-limit2* *m22a-tot* *m28-row*)
      (not (fn-mm-gate-p *m22a-profile* *m22a-img* (fn-adm-priced-cfg *m22a-cfg* 3 2)
                         *m28-after-limit2* *m28-after*)))
 :msg "M28 OLD-HELD-ONLY-ADMISSION gap: three holders are unfunded at *m28-after-limit2*")

(defkeystone m28-run-admitted-record-keeps-the-operator-slot-funded
(implies (and (natp capacity)
                (fn-adm-run-memory-admitp profile img cfg limit tot row held capacity operator-id))
           (fn-mm-gate-p profile img (fn-adm-priced-cfg cfg (+ (nfix held) (if operator-id 0 1)) capacity) limit (fn-adm-after tot row)))
 :id "PRF-100007" :restates fn-adm-run-admitted-record-keeps-the-operator-slot-funded :subject fn-mm-gate-p :rule-classes nil
 :witness ((capacity 2) (operator-id nil) (profile *m22a-profile*) (img *m22a-img*)
           (cfg *m22a-cfg*) (limit *m28-after-limit4*) (tot *m22a-tot*) (held 3) (row *m28-row*))
 :hyps (capacity admitted)
 :breaks ((capacity ((capacity nil) (held 2) (limit *m28-after-limit2*)))
          (admitted ((limit 0))))
 :mutations ((old-held-only-admission
   (:hypothesis admitted (fn-adm-memory-admitp profile img (fn-adm-priced-cfg cfg held capacity) limit tot row))
   ((held 2) (limit *m28-after-limit2*)) :fault "the former held-only gate consumes the free slot")
  (without-free-slot-admission
   (:hypothesis admitted (fn-adm-memory-admitp profile img (fn-adm-priced-cfg cfg (m28-run-gate-without-free-slot held (fn-mm-cfg-connections cfg) capacity operator-id) capacity) limit tot row))
   ((held 3) (limit *m28-after-limit3*)) :fault "after decreasing public capacity to 2, price 3 leaves the operator's fourth place unfunded"))
 :hints (("Goal" :by fn-adm-run-admitted-record-keeps-the-operator-slot-funded)))


(defteeth fn-adm-operator-open-refuses-a-held-slot
 :claim (let ((r (fn-adm-operator-open oc acfg bank configured capacity operator-id profile img cfg limit tot))) (((id (natp operator-id)) (saturated (<= (fn-adm-reader-count configured capacity) (nfix (fn-adm-hh-count bank))))) (and (equal (car r) :refuse) (equal (fn-exp-at 2 r) bank) (equal (fn-adm-operator-open-reason r) :operator-slot-held) (equal (fn-exp-at 6 r) operator-id))))
 :subject fn-adm-operator-open
 :witness ((oc *m28-slot-oc*) (acfg nil) (bank *m28-slot-bank*) (configured 2) (capacity 2) (operator-id *m28-slot-id*) (profile *m22a-profile*) (img *m22a-img*) (cfg *m22a-cfg*) (limit *m28-limit3*) (tot *m22a-tot*) (held 2) (row *m28-row*) (id 2))
 :breaks ((id ((oc *m28-oc2*) (bank *m28-b2*) (operator-id nil)))
(saturated ((oc *m28-zero-slot-oc*) (bank *m28-zero-slot-bank*) (operator-id *m28-zero-slot-id*) (held 1))))
 :mutations ((without-slot-free-check (:conclusion (let ((r (m28-operator-without-slot-check oc acfg bank configured capacity operator-id profile img cfg limit tot))) (and (equal (car r) :refuse) (equal (fn-exp-at 2 r) bank) (equal (fn-adm-operator-open-reason r) :operator-slot-held) (equal (fn-exp-at 6 r) operator-id)))) () :fault "removing the occupied-slot check loses its required refusal reason even with a valid owner bound")))


(defteeth fn-adm-operator-open-preserves-bank-representation
 :claim (((representation (fn-adm-hh-representsp bank))) (fn-adm-hh-representsp (fn-exp-at 2 (fn-adm-operator-open oc acfg bank configured capacity operator-id profile img cfg limit tot))))
 :subject fn-adm-operator-open
 :witness ((oc *m28-oc2*) (acfg nil) (bank *m28-b2*) (configured 2) (capacity 2) (operator-id nil) (profile *m22a-profile*) (img *m22a-img*) (cfg *m22a-cfg*) (limit *m28-limit3*) (tot *m22a-tot*) (held 2) (row *m28-row*) (id 2))
 :breaks ((representation ((bank (fn-adm-hh-make 0 '((0 t nil) (1 t nil)))))))
 :mutations ((stale-cached-count (:conclusion (fn-adm-hh-representsp (fn-adm-hh-make 0 (fn-adm-hh-rows (fn-exp-at 2 (fn-adm-operator-open oc acfg bank configured capacity operator-id profile img cfg limit tot))))) ) () :fault "a slot admission with its old zero cache does not represent its live rows")))


(defteeth fn-adm-operator-close-preserves-bank-representation
 :claim (((representation (fn-adm-hh-representsp bank))) (fn-adm-hh-representsp (fn-exp-at 0 (fn-adm-operator-close bank operator-id id))))
 :subject fn-adm-operator-close
 :witness ((oc *m28-slot-oc*) (acfg nil) (bank *m28-slot-bank*) (configured 2) (capacity 2) (operator-id *m28-slot-id*) (profile *m22a-profile*) (img *m22a-img*) (cfg *m22a-cfg*) (limit *m28-limit3*) (tot *m22a-tot*) (held 2) (row *m28-row*) (id 2))
 :breaks ((representation ((bank (fn-adm-hh-make 0 '((0 t nil) (1 t nil)))) (id 99) (operator-id nil))))
 :mutations ((stale-cached-count (:conclusion (fn-adm-hh-representsp (fn-adm-hh-make 0 (fn-adm-hh-rows (fn-exp-at 0 (fn-adm-operator-close bank operator-id id)))))) () :fault "closing the slot must retain the two readers in the cached count")))


(defteeth fn-adm-operator-open-is-a-single-priced-admission
 :claim (let ((r (fn-adm-operator-open oc acfg bank configured capacity operator-id profile img cfg limit tot)) (held (nfix (fn-adm-hh-count bank)))) (((admitted (equal (car r) :admit))) (and (equal (fn-adm-admission-held r) (1+ held)) (if (< held (fn-adm-reader-count configured capacity)) (and (equal (fn-exp-at 6 r) operator-id) (<= (fn-adm-admission-held r) (fn-adm-reader-count configured capacity))) (and (fn-adm-operator-slot-freep operator-id) (equal (fn-exp-at 6 r) (fn-exp-at 4 r)) (fn-adm-operator-fundedp profile img cfg limit tot capacity) (fn-mm-gate-p profile img (fn-adm-priced-cfg cfg (fn-adm-admission-held r) capacity) limit tot))))))
 :subject fn-adm-operator-open
 :witness ((oc *m28-oc2*) (acfg nil) (bank *m28-b2*) (configured 2) (capacity 2) (operator-id nil) (profile *m22a-profile*) (img *m22a-img*) (cfg *m22a-cfg*) (limit *m28-limit3*) (tot *m22a-tot*) (held 2) (row *m28-row*) (id 2))
 :breaks ((admitted ((oc *m28-slot-oc*) (bank *m28-slot-bank*) (operator-id *m28-slot-id*))))
 :mutations ((missing-count-increment (:conclusion (equal (fn-adm-admission-held r) held)) () :fault "a successful open cannot keep the old cached held count")))


(defteeth fn-adm-operator-open-preserves-slot-representation
 :claim (((state (fn-adm-operator-statep bank operator-id))) (let ((r (fn-adm-operator-open oc acfg bank configured capacity operator-id profile img cfg limit tot))) (fn-adm-operator-statep (fn-exp-at 2 r) (fn-exp-at 6 r))))
 :subject fn-adm-operator-open
 :witness ((oc *m28-oc2*) (acfg nil) (bank *m28-b2*) (configured 2) (capacity 2) (operator-id nil) (profile *m22a-profile*) (img *m22a-img*) (cfg *m22a-cfg*) (limit *m28-limit3*) (tot *m22a-tot*) (held 2) (row *m28-row*) (id 2))
 :breaks ((state ((oc *m28-oc0*) (bank (fn-adm-hh-initial)) (operator-id 99) (held 0))))
 :mutations ((physical-private-row (:conclusion (let ((r (fn-adm-operator-open oc acfg bank configured capacity operator-id profile img cfg limit tot))) (fn-adm-operator-statep (fn-adm-hh-open (fn-exp-at 2 r) (fn-exp-at 6 r) t) (fn-exp-at 6 r)))) () :fault "the private logical slot must never acquire physical transport custody")))


(defteeth fn-adm-operator-close-preserves-slot-representation
 :claim (((state (fn-adm-operator-statep bank operator-id))) (let ((r (fn-adm-operator-close bank operator-id id))) (fn-adm-operator-statep (fn-exp-at 0 r) (fn-exp-at 1 r))))
 :subject fn-adm-operator-close
 :witness ((oc *m28-slot-oc*) (acfg nil) (bank *m28-slot-bank*) (configured 2) (capacity 2) (operator-id *m28-slot-id*) (profile *m22a-profile*) (img *m22a-img*) (cfg *m22a-cfg*) (limit *m28-limit3*) (tot *m22a-tot*) (held 2) (row *m28-row*) (id 0))
 :breaks ((state ((oc *m28-oc0*) (bank (fn-adm-hh-initial)) (operator-id 99) (held 0) (id 0))))
 :mutations ((wrong-reader-id (:conclusion (let ((r (fn-adm-operator-close bank operator-id id))) (fn-adm-operator-statep (fn-exp-at 0 r) id))) () :fault "a reader close cannot replace the carried private slot id with that ended reader id")))


(defteeth fn-adm-operator-admitted-id-is-the-slot-id
 :claim (let ((r (fn-adm-operator-open oc acfg bank configured capacity operator-id profile img cfg limit tot))) (((admitted (equal (fn-adm-operator-open-word r) :admitted))) (and (natp (fn-adm-operator-open-id r)) (equal (fn-exp-at 6 r) (if (< (nfix (fn-adm-hh-count bank)) (fn-adm-reader-count configured capacity)) operator-id (fn-adm-operator-open-id r))))))
 :subject fn-adm-operator-open
 :witness ((oc *m28-oc2*) (acfg nil) (bank *m28-b2*) (configured 2) (capacity 2) (operator-id nil) (profile *m22a-profile*) (img *m22a-img*) (cfg *m22a-cfg*) (limit *m28-limit3*) (tot *m22a-tot*) (held 2) (row *m28-row*) (id 2))
 :breaks ((admitted ((oc *m28-slot-oc*) (bank *m28-slot-bank*) (operator-id *m28-slot-id*))))
 :mutations ((reader-first-slot (:conclusion (equal (fn-exp-at 6 r) (fn-adm-operator-open-id r))) ((oc *m28-oc0*) (bank (fn-adm-hh-initial)) (operator-id nil) (held 0)) :fault "a below-saturation private open is an ordinary reader and must keep cached slot id NIL")))


(with-guard-checking-event :all
 (assert-event (and
 (fn-held-p *m28-row*) (fn-bs-profile-validp *m22a-profile*)
 (and (fn-ocl-relation *m28-oc0*)
       (fn-cstp-carriedp (fn-own-store (fn-ocfg-owner *m28-oc0*)))) (and (fn-ocl-relation *m28-oc1*)
       (fn-cstp-carriedp (fn-own-store (fn-ocfg-owner *m28-oc1*))))
 (and (fn-ocl-relation *m28-oc2*)
       (fn-cstp-carriedp (fn-own-store (fn-ocfg-owner *m28-oc2*)))) (and (fn-ocl-relation *m28-slot-oc*)
       (fn-cstp-carriedp (fn-own-store (fn-ocfg-owner *m28-slot-oc*))))
 (and (fn-ocl-relation *m28-tight-oc2*)
       (fn-cstp-carriedp (fn-own-store (fn-ocfg-owner *m28-tight-oc2*))))
 (fn-adm-hh-representsp *m28-b2*)
 (fn-adm-operator-statep *m28-slot-bank* *m28-slot-id*)
 (equal (fn-adm-installed-capacity *m22a-profile* *m22a-img* *m22a-cfg*
          *m28-limit3* *m22a-tot*) 2))
  :msg "M28-TYPED-PRODUCERS"))

(with-guard-checking-event :all
 (assert-event (let* ((r1 (fn-adm-operator-open *m28-oc0* nil (fn-adm-hh-initial) 2 2 nil
                              *m22a-profile* *m22a-img* *m22a-cfg* *m28-limit3* *m22a-tot*))
        (r2 (fn-adm-operator-open (cdr (fn-exp-at 1 r1)) nil (fn-exp-at 2 r1) 2 2 (fn-exp-at 6 r1)
                              *m22a-profile* *m22a-img* *m22a-cfg* *m28-limit3* *m22a-tot*)))
 (and (and (fn-ocl-relation *m28-oc0*)
       (fn-cstp-carriedp (fn-own-store (fn-ocfg-owner *m28-oc0*))))
      (equal (fn-adm-operator-open-word r1) :admitted)
      (equal (fn-adm-operator-open-word r2) :admitted)
      (equal (fn-exp-at 6 r1) nil) (equal (fn-exp-at 6 r2) nil)
      (equal (fn-adm-admission-held r1) 1) (equal (fn-adm-admission-held r2) 2)
      (fn-adm-operator-statep (fn-exp-at 2 r2) nil)))
  :msg "M28-TWO-PRIVATE-READERS"))

(with-guard-checking-event :all
 (assert-event (let ((second (fn-adm-operator-open *m28-slot-oc* nil *m28-slot-bank* 2 2 *m28-slot-id*
                       *m22a-profile* *m22a-img* *m22a-cfg* *m28-limit3* *m22a-tot*)))
 (and (equal (fn-adm-hh-count *m28-b2*) (fn-adm-reader-count 2 2))
      (fn-adm-operator-slot-freep nil)
      (fn-adm-operator-fundedp *m22a-profile* *m22a-img* *m22a-cfg* *m28-limit3* *m22a-tot* 2)
      (equal (fn-adm-operator-open-word *m28-slot*) :admitted)
      (equal (fn-adm-operator-open-id *m28-slot*) *m28-slot-id*)
      (equal (fn-adm-admission-held *m28-slot*) 3)
      (equal (fn-adm-operator-open-word second) :refused)
      (equal (fn-adm-operator-open-reason second) :operator-slot-held)
      (equal (fn-exp-at 2 second) *m28-slot-bank*)
      (equal (cdr (fn-exp-at 1 second)) *m28-slot-oc*)
      (equal (fn-exp-at 6 second) *m28-slot-id*)))
  :msg "M28-FUNDED-SATURATION-AND-SECOND"))

(with-guard-checking-event :all
 (assert-event (let* ((closed (fn-adm-operator-close *m28-slot-bank* *m28-slot-id* *m28-slot-id*))
        (oc (fn-ocfg-close *m28-slot-oc* *m28-slot-id*))
        (again (fn-adm-operator-open oc nil (fn-exp-at 0 closed) 2 2 (fn-exp-at 1 closed)
                   *m22a-profile* *m22a-img* *m22a-cfg* *m28-limit3* *m22a-tot*)))
 (and (fn-adm-operator-statep *m28-slot-bank* *m28-slot-id*)
      (equal (fn-adm-hh-count (fn-exp-at 0 closed)) 2)
      (equal (fn-exp-at 1 closed) nil)
      (not (fn-exp-lookup *m28-slot-id* (fn-adm-hh-rows (fn-exp-at 0 closed))))
      (and (fn-ocl-relation oc)
       (fn-cstp-carriedp (fn-own-store (fn-ocfg-owner oc))))
      (equal (fn-adm-operator-open-word again) :admitted)
      (equal (fn-adm-admission-held again) 3)
      (equal (fn-adm-operator-open-id again) (fn-exp-at 6 again))
      (not (equal (fn-exp-at 6 again) *m28-slot-id*))
      (fn-adm-operator-statep (fn-exp-at 2 again) (fn-exp-at 6 again))))
  :msg "M28-SLOT-CLOSE-AND-REOPEN"))

(with-guard-checking-event :all
 (assert-event (let* ((r (fn-adm-operator-open *m28-zero-slot-oc* nil *m28-zero-slot-bank* 2 2 *m28-zero-slot-id*
               *m22a-profile* *m22a-img* *m22a-cfg* *m28-limit3* *m22a-tot*))
        (id (fn-adm-operator-open-id r))
        (closed (fn-adm-operator-close (fn-exp-at 2 r) (fn-exp-at 6 r) id)))
 (and (and (fn-ocl-relation *m28-zero-slot-oc*)
       (fn-cstp-carriedp (fn-own-store (fn-ocfg-owner *m28-zero-slot-oc*))))
      (fn-adm-operator-statep *m28-zero-slot-bank* *m28-zero-slot-id*)
      (< (fn-adm-hh-count *m28-zero-slot-bank*) (fn-adm-reader-count 2 2))
      (equal (fn-adm-operator-open-word r) :admitted)
      (not (equal id *m28-zero-slot-id*))
      (equal (fn-exp-at 6 r) *m28-zero-slot-id*)
      (equal (fn-exp-at 1 closed) *m28-zero-slot-id*)
      (fn-adm-operator-statep (fn-exp-at 0 closed) (fn-exp-at 1 closed))))
  :msg "M28-READER-PRIVATE-CLOSE-KEEPS-SLOT"))

(with-guard-checking-event :all
 (assert-event (let ((r (fn-adm-operator-open *m28-oc2* nil *m28-b2* 3 2 nil
                *m22a-profile* *m22a-img* *m22a-cfg* *m28-limit3* *m22a-tot*)))
 (and (and (fn-ocl-relation *m28-oc2*)
       (fn-cstp-carriedp (fn-own-store (fn-ocfg-owner *m28-oc2*)))) (fn-adm-hh-representsp *m28-b2*)
      (= (fn-adm-hh-count *m28-b2*) (fn-adm-reader-count 3 2))
      (fn-adm-operator-fundedp *m22a-profile* *m22a-img* *m22a-cfg* *m28-limit3* *m22a-tot* 2)
      (not (equal (fn-mm-cfg-connections *m22a-cfg*) 3))
      (equal (fn-adm-operator-open-word r) :refused)
      (equal (fn-adm-operator-open-reason r) :operator-cfg-stale)
      (equal (fn-exp-at 2 r) *m28-b2*)))
  :msg "M28-STALENESS-IS-NAMED"))

(with-guard-checking-event :all
 (assert-event (let ((r (fn-adm-operator-open *m28-tight-oc2* nil *m28-tight-b2* 2 2 nil
                *m22a-profile* *m22a-img* *m22a-cfg* *m28-limit3* *m22a-tot*)))
 (and (and (fn-ocl-relation *m28-tight-oc2*)
       (fn-cstp-carriedp (fn-own-store (fn-ocfg-owner *m28-tight-oc2*))))
      (fn-adm-hh-representsp *m28-tight-b2*)
      (fn-adm-operator-fundedp *m22a-profile* *m22a-img* *m22a-cfg* *m28-limit3* *m22a-tot* 2)
      (equal (fn-adm-operator-open-word r) :refused)
      (equal (fn-adm-operator-open-reason r) :operator-owner-bound)
      (equal (fn-exp-at 2 r) *m28-tight-b2*)))
  :msg "M28-OWNER-BOUND-IS-NAMED"))

(with-guard-checking-event :all
 (assert-event (let ((old (fn-adm-reader-open *m28-oc2* nil *m28-b2* 2 2)))
 (and (and (fn-ocl-relation *m28-oc2*)
       (fn-cstp-carriedp (fn-own-store (fn-ocfg-owner *m28-oc2*)))) (fn-adm-hh-representsp *m28-b2*)
      (equal (fn-adm-hh-count *m28-b2*) (fn-adm-reader-count 2 2))
      (equal (car old) :refuse) (equal (fn-exp-at 2 old) *m28-b2*)
      (equal (fn-adm-operator-open-word *m28-slot*) :admitted)
      (equal (fn-adm-admission-held *m28-slot*) 3)))
  :msg "M28-OLD-READER-REFUSES-PRIVATE-SATURATION"))

(with-guard-checking-event :all
 (assert-event (let ((actual (fn-adm-operator-open *m28-slot-oc* nil *m28-slot-bank* 2 2 *m28-slot-id*
                     *m22a-profile* *m22a-img* *m22a-cfg* *m28-limit4* *m22a-tot*))
       (mutant (m28-operator-without-slot-check *m28-slot-oc* nil *m28-slot-bank* 2 2 *m28-slot-id*
                     *m22a-profile* *m22a-img* *m22a-cfg* *m28-limit4* *m22a-tot*)))
 (and (and (fn-ocl-relation *m28-slot-oc*)
       (fn-cstp-carriedp (fn-own-store (fn-ocfg-owner *m28-slot-oc*))))
      (fn-adm-operator-statep *m28-slot-bank* *m28-slot-id*)
      (not (fn-adm-operator-slot-freep *m28-slot-id*))
      (fn-mm-gate-p *m22a-profile* *m22a-img* (fn-adm-priced-cfg *m22a-cfg* 4 2) *m28-limit4* *m22a-tot*)
      (equal (fn-adm-operator-open-word actual) :refused)
      (equal (fn-adm-operator-open-reason actual) :operator-slot-held)
      (not (equal (fn-adm-operator-open-reason mutant) :operator-slot-held))))
  :msg "M28-SLOT-FREE-CHECK-MUTATION"))

(with-guard-checking-event :all
 (assert-event (let ((actual (fn-adm-operator-open *m28-oc0* nil (fn-adm-hh-initial) 2 2 nil
                     *m22a-profile* *m22a-img* *m22a-cfg* *m28-limit3* *m22a-tot*))
       (mutant (m28-operator-reader-first *m28-oc0* nil (fn-adm-hh-initial) 2 2 nil
                     *m22a-profile* *m22a-img* *m22a-cfg* *m28-limit3* *m22a-tot*)))
 (and (and (fn-ocl-relation *m28-oc0*)
       (fn-cstp-carriedp (fn-own-store (fn-ocfg-owner *m28-oc0*))))
      (equal (fn-adm-operator-open-word actual) :admitted)
      (equal (fn-adm-operator-open-word mutant) :admitted)
      (equal (fn-exp-at 6 actual) nil)
      (equal (fn-exp-at 6 mutant) (fn-adm-operator-open-id mutant))
      (not (equal (fn-exp-at 6 actual) (fn-exp-at 6 mutant)))))
  :msg "M28-READER-FIRST-CODE-MUTATION"))

(with-guard-checking-event :all
 (assert-event (and
 (fn-adm-hh-representsp *m28-slot-bank*)
 (fn-adm-operator-statep *m28-slot-bank* *m28-slot-id*)
 (not (fn-adm-operator-statep *m28-slot-bank* 99))
 (fn-adm-hh-representsp (fn-adm-hh-open *m28-slot-bank* *m28-slot-id* t))
 (not (fn-adm-operator-statep (fn-adm-hh-open *m28-slot-bank* *m28-slot-id* t) *m28-slot-id*)))
  :msg "M28-STALE-AND-PHYSICAL-IDS-FAIL-RECOGNIZER"))

(with-guard-checking-event :all
 (assert-event (let* ((reader (fn-adm-reader-open *m28-zero-slot-oc* nil *m28-zero-slot-bank* 2 2))
        (bank (fn-exp-at 2 reader))
        (old (fn-exp-lookup *m28-zero-slot-id* (fn-adm-hh-rows bank)))
        (r (fn-adm-transport-rearm :exposure (cdr (fn-exp-at 1 reader))
             (fn-exp-initial) *m22a-lim* nil nil *m22a-address* 0 bank *m28-zero-slot-id* 2 2)))
 (and (fn-adm-operator-statep *m28-zero-slot-bank* *m28-zero-slot-id*)
      (equal (car reader) :admit)
      (fn-adm-operator-statep bank *m28-zero-slot-id*)
      (equal old (fn-exp-lookup *m28-zero-slot-id* (fn-adm-hh-rows *m28-zero-slot-bank*)))
      (fn-exp-at 1 old) (not (fn-exp-at 2 old))
      (equal (car r) :refuse) (equal (fn-exp-at 2 r) bank)
      (fn-adm-operator-statep (fn-exp-at 2 r) *m28-zero-slot-id*)
      (equal (fn-adm-hh-rearm bank *m28-zero-slot-id* *m28-zero-slot-id*) bank)))
  :msg "M28-PUBLIC-ADMISSION-AND-REARM-KEEP-PRIVATE-ROW"))

;; The old-admission scenario's limit holds in BOTH pricings (this lane's window term and OVER's field-13
;; line, measured by O8 10-14): at least *m28-limit3* (three holders fit before the row), at least
;; *m28-after-limit2* (the row fits beside two), and below *m28-after-limit3* (three holders after it are
;; unfunded), since the row adds to both.
(defconst *m28-old-slot-limit* (max *m28-limit3* *m28-after-limit2*))

(with-guard-checking-event :all
 (assert-event (let ((actual (fn-adm-operator-open *m28-oc2* nil *m28-b2* 2 2 nil
                     *m22a-profile* *m22a-img* *m22a-cfg* *m28-old-slot-limit* *m28-after*))
       (mutant (m28-operator-borrowed-slot *m28-oc2* nil *m28-b2* 2 2 nil
                     *m22a-profile* *m22a-img* *m22a-cfg* *m28-old-slot-limit* *m28-after*)))
 (and (fn-held-p *m28-row*) (and (fn-ocl-relation *m28-oc2*)
       (fn-cstp-carriedp (fn-own-store (fn-ocfg-owner *m28-oc2*))))
      (equal (fn-adm-installed-capacity *m22a-profile* *m22a-img* *m22a-cfg* *m28-old-slot-limit* *m22a-tot*) 2)
      (fn-adm-run-memory-admitp *m22a-profile* *m22a-img* *m22a-cfg* *m28-after-limit3* *m22a-tot* *m28-row* 2 2 nil)
      (fn-mm-gate-p *m22a-profile* *m22a-img* (fn-adm-priced-cfg *m22a-cfg* 3 2) *m28-old-slot-limit* *m22a-tot*)
      (fn-adm-memory-admitp *m22a-profile* *m22a-img* (fn-adm-priced-cfg *m22a-cfg* 2 2)
          *m28-old-slot-limit* *m22a-tot* *m28-row*)
      (not (fn-mm-gate-p *m22a-profile* *m22a-img* (fn-adm-priced-cfg *m22a-cfg* 3 2) *m28-old-slot-limit* *m28-after*))
      (equal (fn-adm-operator-open-word actual) :refused)
      (equal (fn-adm-operator-open-reason actual) :operator-slot-memory)
      (equal (fn-adm-operator-open-word mutant) :admitted)
      (equal (fn-adm-admission-held mutant) 3)))
  :msg "M28-OLD-ADMISSION-CONSUMES-FUNDED-SLOT"))

; The same reserve/prepare/publish/finish machine as store-node-tests.
(defun m28-grown-store (s row)
 (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
 (let* ((reserved (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier nil)
                      :frontier-file :ok) :frontier-replace :ok) :frontier-directory :ok))
        (prepared (fn-sn-prepare reserved row))
        (published (fn-sn-io (fn-sn-io (fn-sn-io prepared :record-file :ok)
                      :record-link :ok) :record-directory :ok)))
  (fn-sn-finish published)))
(defconst *m28-grown-store* (m28-grown-store *m22a-store* *m28-edge-row*))
(defconst *m28-grown-oc0*
 (fn-ocfg-make (fn-own-start *m28-grown-store* 3) *m22a-config* nil nil))
(defconst *m28-grown-r1* (fn-adm-reader-open *m28-grown-oc0* nil (fn-adm-hh-initial) 2 2))
(defconst *m28-grown-r2* (fn-adm-reader-open (cdr (fn-exp-at 1 *m28-grown-r1*)) nil
                             (fn-exp-at 2 *m28-grown-r1*) 2 2))
(defconst *m28-grown-oc2* (cdr (fn-exp-at 1 *m28-grown-r2*)))
(defconst *m28-grown-b2* (fn-exp-at 2 *m28-grown-r2*))

(with-guard-checking-event :all
 (assert-event (let ((r (fn-adm-operator-open *m28-grown-oc2* nil *m28-grown-b2* 2 2 nil
               *m22a-profile* *m22a-img* *m22a-cfg* *m28-edge-limit* *m28-edge-after*)))
 (and (fn-bs-profile-validp *m22a-profile*) (fn-held-p *m28-edge-row*)
      (fn-sn-statep *m28-grown-store*)
      (equal (fn-sf-records-count (fn-sn-files *m28-grown-store*)) 1)
      (fn-sn-committed-recordp (fn-sn-node *m28-grown-store*) *m28-edge-row*)
      (and (fn-ocl-relation *m28-grown-oc2*)
       (fn-cstp-carriedp (fn-own-store (fn-ocfg-owner *m28-grown-oc2*)))) (fn-adm-operator-statep *m28-grown-b2* nil)
      (equal (fn-adm-hh-count *m28-grown-b2*) (fn-adm-reader-count 2 2))
      (equal (fn-adm-installed-capacity *m22a-profile* *m22a-img* *m22a-cfg*
                  *m28-edge-limit* *m22a-tot*) 2)
      (fn-adm-run-memory-admitp *m22a-profile* *m22a-img* *m22a-cfg* *m28-edge-limit*
                   *m22a-tot* *m28-edge-row* 2 2 nil)
      (equal *m28-edge-after* (fn-adm-after *m22a-tot* *m28-edge-row*))
      (fn-mm-gate-p *m22a-profile* *m22a-img* (fn-adm-priced-cfg *m22a-cfg* 3 2)
                   *m28-edge-limit* *m28-edge-after*)
      (not (fn-adm-run-memory-admitp *m22a-profile* *m22a-img* *m22a-cfg* *m28-edge-limit*
                    *m22a-tot* *m28-edge-next* 2 2 nil))
      (fn-adm-operator-slot-freep nil)
      (equal (fn-adm-operator-open-word r) :admitted)
      (equal (fn-adm-admission-held r) 3)
      (equal (fn-adm-operator-open-id r) (fn-exp-at 6 r))
      (fn-adm-operator-statep (fn-exp-at 2 r) (fn-exp-at 6 r))))
  :msg "M28-GROWN-STORE-EDGE-ADMITS-OPERATOR"))


; R2 exact staged encoding, unchanged C/H, at the pre-change edge.
(defconst *m28-config-deltas* (list (fn-cfg-set-policy "posting-policy" "open")))
(defconst *m28-config-record* (fn-ocfg-reconfig-record *m28-oc2* *m28-config-deltas*))
(defconst *m28-config-octets* (len (fn-cfg-encode *m28-config-record*)))
(defconst *m28-config-cfg*
 (update-nth 12 (+ (fn-mm-cfg-config *m22a-cfg*) *m28-config-octets*)
             (true-list-fix *m22a-cfg*)))
(defconst *m28-config-limit* (max
 (fn-mm-sum *m22a-profile* *m22a-img* (fn-adm-priced-cfg *m28-config-cfg* 3 2) *m22a-tot*)
 (fn-mm-reopen-need *m22a-profile* *m22a-img* (fn-adm-priced-cfg *m28-config-cfg* 3 2) *m22a-tot*)))

(defconst *m28-config-no-slot-limit* (max
 (fn-mm-sum *m22a-profile* *m22a-img* (fn-adm-priced-cfg *m28-config-cfg* 2 nil) *m22a-tot*)
 (fn-mm-reopen-need *m22a-profile* *m22a-img* (fn-adm-priced-cfg *m28-config-cfg* 2 nil) *m22a-tot*)))

(defkeystone m28-admitted-config-change-keeps-the-operator-slot-funded
(implies (and (natp capacity)
                (fn-adm-config-change-admitp profile img cfg limit tot held capacity operator-id octets))
           (fn-mm-gate-p profile img
             (fn-adm-priced-cfg (update-nth 12 (+ (fn-mm-cfg-config cfg) (nfix octets)) (true-list-fix cfg))
                                (+ (nfix held) (if operator-id 0 1)) capacity)
             limit tot))
 :id "PRF-10018" :restates fn-adm-admitted-config-change-keeps-the-operator-slot-funded
 :subject fn-mm-gate-p :rule-classes nil
 :witness ((capacity 2) (operator-id nil) (profile *m22a-profile*) (img *m22a-img*)
           (cfg *m22a-cfg*) (limit *m28-config-limit*) (tot *m22a-tot*) (held 2)
           (octets *m28-config-octets*))
 :hyps (capacity admitted)
 :breaks ((capacity ((capacity nil) (limit *m28-config-no-slot-limit*)))
          (admitted ((limit 0))))
 :mutations ((without-config-octets
   (:hypothesis admitted
    (fn-adm-config-change-admitp profile img cfg limit tot held capacity operator-id 0))
   ((limit *m28-limit3*)) :fault "an unchanged-C/H policy record still grows configuration history"))
 :hints (("Goal" :by fn-adm-admitted-config-change-keeps-the-operator-slot-funded)))

(with-guard-checking-event :all
 (assert-event
  (and (fn-cfg-recordp *m28-config-record*) (posp *m28-config-octets*)
       (equal (fn-mm-cfg-connections *m28-config-cfg*) (fn-mm-cfg-connections *m22a-cfg*))
       (equal (fn-mm-cfg-handshakes *m28-config-cfg*) (fn-mm-cfg-handshakes *m22a-cfg*))
       (fn-adm-config-change-admitp *m22a-profile* *m22a-img* *m22a-cfg*
         *m28-limit3* *m22a-tot* 2 2 nil 0)
       (not (fn-adm-config-change-admitp *m22a-profile* *m22a-img* *m22a-cfg*
         *m28-limit3* *m22a-tot* 2 2 nil *m28-config-octets*)))
  :msg "M28-UNCHANGED-CONFIG-HISTORY-EDGE"))

; R1: actual policy decrease with three public holders, paired private close,
; durable publication, actual record publication, then a fresh operator open.
(include-book "../../books/config-owner-publish")
(defconst *m28-decrease-configs*
 (list *fn-cfg-default-record*
       (fn-cfg-record-make 1 0 2
         (list (fn-cfg-set-limit "exposure-connections" 3)) *fn-cfg-default-stamp*)))
(defconst *m28-decrease-open* (fn-cpo-open-observed *m28-decrease-configs* 0 nil))
(defconst *m28-decrease-store3*
 (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-open-state *m28-decrease-open*)
   :recovery-barrier :ok) :recovery-barrier :ok) :recovery-barrier :ok))
(defconst *m28-decrease-config3* (fn-ocl-store-config *m28-decrease-store3*))
(defconst *m28-decrease-oc0*
 (fn-ocfg-make
   (fn-own-observe (fn-own-start *m28-decrease-store3* 4)
     (fn-clock-observation 5000000 1790000000000 0 t))
   *m28-decrease-config3* nil nil))
(defconst *m28-decrease-r1* (fn-adm-reader-open *m28-decrease-oc0* nil (fn-adm-hh-initial) 3 3))
(defconst *m28-decrease-r2* (fn-adm-reader-open (cdr (fn-exp-at 1 *m28-decrease-r1*)) nil
                           (fn-exp-at 2 *m28-decrease-r1*) 3 3))
(defconst *m28-decrease-r3* (fn-adm-reader-open (cdr (fn-exp-at 1 *m28-decrease-r2*)) nil
                           (fn-exp-at 2 *m28-decrease-r2*) 3 3))
(defconst *m28-decrease-oc3* (cdr (fn-exp-at 1 *m28-decrease-r3*)))
(defconst *m28-decrease-bank3* (fn-exp-at 2 *m28-decrease-r3*))
(defconst *m28-decrease-deltas* (list (fn-cfg-set-limit "exposure-connections" 2)))
(defconst *m28-decrease-record* (fn-ocfg-reconfig-record *m28-decrease-oc3* *m28-decrease-deltas*))
(defconst *m28-decrease-cfg3*
 (update-nth 14 (fn-adm-installed-lease-allocation *m22a-profile*
                  (fn-adm-public-readers-cfg (update-nth 0 3 *m22a-cfg*) 3) 16384)
   (update-nth 12 (+ (len (fn-cfg-encode (car *m28-decrease-configs*)))
                       (len (fn-cfg-encode (cadr *m28-decrease-configs*))))
     (update-nth 0 3 (true-list-fix *m22a-cfg*)))))
(defconst *m28-decrease-cfg2*
 (update-nth 12 (+ (fn-mm-cfg-config *m28-decrease-cfg3*)
                   (len (fn-cfg-encode *m28-decrease-record*)))
   (update-nth 0 2 *m28-decrease-cfg3*)))
(defconst *m28-decrease-limit* (max
 (fn-mm-sum *m22a-profile* *m22a-img* (fn-adm-priced-cfg *m28-decrease-cfg2* 4 2) *m28-after*)
 (fn-mm-reopen-need *m22a-profile* *m22a-img* (fn-adm-priced-cfg *m28-decrease-cfg2* 4 2) *m28-after*)))
(defconst *m28-decrease-private*
 (fn-adm-operator-open *m28-decrease-oc3* nil *m28-decrease-bank3* 3 3 nil
   *m22a-profile* *m22a-img* *m28-decrease-cfg3* *m28-decrease-limit* *m22a-tot*))
(defconst *m28-decrease-staged*
 (fn-ocfg-reconfigure (cdr (fn-exp-at 1 *m28-decrease-private*))
   (fn-adm-operator-open-id *m28-decrease-private*) *m28-decrease-deltas*))
(defconst *m28-decrease-closed*
 (fn-ocfg-close *m28-decrease-staged* (fn-adm-operator-open-id *m28-decrease-private*)))
(defconst *m28-decrease-paired-close*
 (fn-adm-operator-close (fn-exp-at 2 *m28-decrease-private*)
   (fn-exp-at 6 *m28-decrease-private*) (fn-adm-operator-open-id *m28-decrease-private*)))
(defconst *m28-decrease-published*
 (mv-list 2 (fn-ocl-publish *m28-decrease-closed* 3 32768)))
(defconst *m28-decrease-oc2* (cadr *m28-decrease-published*))
(defconst *m28-decrease-grown-store*
 (m28-grown-store (fn-own-store (fn-ocfg-owner *m28-decrease-oc2*)) *m28-row*))
(defconst *m28-decrease-grown-oc*
 (fn-ocfg-with-owner *m28-decrease-oc2*
   (fn-ocl-owner-with-store (fn-ocfg-owner *m28-decrease-oc2*) *m28-decrease-grown-store*)))

(with-guard-checking-event :all
 (assert-event
  (let* ((bank (fn-exp-at 0 *m28-decrease-paired-close*))
         (operator-id (fn-exp-at 1 *m28-decrease-paired-close*))
         (held (fn-adm-hh-count bank))
         (opened (fn-adm-operator-open *m28-decrease-grown-oc* nil bank 2 2 operator-id
                    *m22a-profile* *m22a-img* *m28-decrease-cfg2* *m28-decrease-limit* *m28-after*)))
   (and (fn-sn-open-okp *m28-decrease-open*)
        (fn-ocl-relation *m28-decrease-oc3*) (fn-adm-hh-representsp *m28-decrease-bank3*)
        (equal (fn-adm-hh-count *m28-decrease-bank3*) 3)
        (equal (fn-adm-operator-open-word *m28-decrease-private*) :admitted)
        (equal (fn-adm-admission-held *m28-decrease-private*) 4)
        (equal (fn-ocfg-staged *m28-decrease-staged*) *m28-decrease-record*)
        (fn-adm-config-change-admitp *m22a-profile* *m22a-img*
          (update-nth 0 2 *m28-decrease-cfg3*) *m28-decrease-limit* *m22a-tot* 4 2
          (fn-exp-at 6 *m28-decrease-private*) (len (fn-cfg-encode *m28-decrease-record*)))
        (equal (car *m28-decrease-published*) :durable)
        (equal (fn-exp-connections-capacity (fn-cfg-value (fn-ocfg-config *m28-decrease-oc2*))) 2)
        (equal held 3) (equal operator-id nil) (fn-adm-operator-statep bank operator-id)
        (fn-adm-run-memory-admitp *m22a-profile* *m22a-img* *m28-decrease-cfg2*
          *m28-decrease-limit* *m22a-tot* *m28-row* held 2 operator-id)
        (fn-mm-gate-p *m22a-profile* *m22a-img*
          (fn-adm-priced-cfg *m28-decrease-cfg2* (+ held (if operator-id 0 1)) 2)
          *m28-decrease-limit* *m28-after*)
        (fn-sn-statep *m28-decrease-grown-store*)
        (fn-cstp-carriedp *m28-decrease-grown-store*)
        (equal (fn-sf-records-count (fn-sn-files *m28-decrease-grown-store*)) 1)
        (equal (fn-ct-charged (fn-sf-records (fn-sn-files *m28-decrease-grown-store*)) :resident)
               *m28-after*)
        (fn-sn-committed-recordp (fn-sn-node *m28-decrease-grown-store*) *m28-row*)
        (fn-ocl-relation *m28-decrease-grown-oc*)
        (equal (fn-adm-operator-open-word opened) :admitted)
        (equal (fn-adm-admission-held opened) 4)
        (equal (fn-adm-operator-open-id opened) (fn-exp-at 6 opened))
        (fn-adm-operator-statep (fn-exp-at 2 opened) (fn-exp-at 6 opened))))
  :msg "M28-DECREASE-GROWTH-OPERATOR-OPEN"))

(with-guard-checking-event :all
 (assert-event
  (let* ((held 3) (capacity 2) (operator-id nil)
         (old-price (m28-run-gate-without-free-slot held 2 capacity operator-id)))
   (and (natp capacity) (equal operator-id nil) (equal held 3)
        (equal old-price 3)
        (equal (fn-adm-run-gate-held held 2 capacity operator-id) 4)
        (fn-mm-gate-p *m22a-profile* *m22a-img*
          (fn-adm-priced-cfg *m22a-cfg* old-price capacity) *m28-limit3* *m22a-tot*)
        (not (fn-mm-gate-p *m22a-profile* *m22a-img*
          (fn-adm-priced-cfg *m22a-cfg* (+ (nfix held) (if operator-id 0 1)) capacity)
          *m28-limit3* *m22a-tot*))))
  :msg "M28-OLD-PRICE-THREE-FAILS-FOUR"))


(with-guard-checking-event :all
 (assert-event
  (and (fn-adm-hh-representsp (fn-adm-hh-initial))
       (fn-adm-operator-statep (fn-adm-hh-initial) nil)
       (fn-adm-hh-representsp *m28-decrease-bank3*)
       (fn-adm-operator-statep *m28-decrease-bank3* nil))
  :msg "M28-NO-OPERATOR-ESTABLISHMENT"))
