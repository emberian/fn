(in-package "ACL2")
(include-book "../../books/owner-memory-holding")
(include-book "../../books/defkeystone")
(include-book "../../books/config-observed")
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
(defteeth fn-adm-hh-cached-union-keystone
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
  (max (fn-mm-sum *m22a-profile* *m22a-img* *m22a-cfg* *m22a-tot*)
       (fn-mm-reopen-need *m22a-profile* *m22a-img* *m22a-cfg* *m22a-tot*)))

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
         (limit (max (fn-mm-sum *m22a-profile* *m22a-img* cfg *m22a-tot*)
                     (fn-mm-reopen-need *m22a-profile* *m22a-img* cfg *m22a-tot*)))
         (capacity (fn-adm-installed-capacity *m22a-profile* *m22a-img* cfg limit *m22a-tot*))
         (lim (update-nth 1 (fn-adm-reader-count 1 capacity) *m22a-lim*))
         (old (fn-ocar-exp-open *m22a-closed-oc* *m22a-closed-xs* lim nil nil *m22a-address* 1))
         (next-bank (fn-adm-hh-open *m22a-held* (fn-exp-open-id old) t))
         (next-held (nfix (fn-adm-hh-count next-bank))))
    (and (equal capacity 1)
         (fn-mm-gate-p *m22a-profile* *m22a-img* (fn-adm-cfg-at cfg capacity) limit *m22a-tot*)
         (natp (fn-exp-open-id old)) (equal next-held 2)
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
 (let* ((run-cfg (update-nth 10 nil (true-list-fix cfg)))
         (configured (fn-mm-cfg-connections run-cfg))
         (capacity (fn-adm-installed-capacity profile img run-cfg limit tot))
         (reader-count (fn-adm-reader-count configured capacity))
         (exposure (fn-adm-exposure-open oc xs lim acfg peer address now
                                         bank configured capacity))
         (peer-open (fn-adm-peer-open oc peer acfg bank configured capacity))
         (rearm (fn-adm-transport-rearm kind oc xs lim acfg peer address now
                                        bank old-id configured capacity))
         (reader (fn-adm-reader-open oc acfg bank configured capacity)))
    (and
      (implies (equal (car exposure) :admit)
        (and (<= (fn-exp-at 3 exposure) reader-count)
             (<= (fn-adm-admission-held exposure) reader-count)
             (equal (fn-adm-priced-connections
                      (fn-adm-admission-held exposure) configured capacity) reader-count)
             (fn-mm-gate-p profile img
               (fn-adm-priced-cfg run-cfg (fn-adm-admission-held exposure) capacity)
               limit tot)))
      (implies (equal (car peer-open) :admit)
        (and (<= (fn-exp-at 3 peer-open) reader-count)
             (<= (fn-adm-admission-held peer-open) reader-count)
             (equal (fn-adm-priced-connections
                      (fn-adm-admission-held peer-open) configured capacity) reader-count)
             (fn-mm-gate-p profile img
               (fn-adm-priced-cfg run-cfg (fn-adm-admission-held peer-open) capacity)
               limit tot)))
      (implies (equal (car rearm) :admit)
        (and (<= (fn-exp-at 3 rearm) reader-count)
             (<= (fn-adm-admission-held rearm) reader-count)
             (equal (fn-adm-priced-connections
                      (fn-adm-admission-held rearm) configured capacity) reader-count)
             (fn-mm-gate-p profile img
               (fn-adm-priced-cfg run-cfg (fn-adm-admission-held rearm) capacity)
               limit tot)))
      (implies (equal (car reader) :admit)
        (and (<= (fn-exp-at 3 reader) reader-count)
             (<= (fn-adm-admission-held reader) reader-count)
             (equal (fn-adm-priced-connections
                      (fn-adm-admission-held reader) configured capacity) reader-count)
             (fn-mm-gate-p profile img
               (fn-adm-priced-cfg run-cfg (fn-adm-admission-held reader) capacity)
               limit tot)))))
 :id "PRF-10017" :restates fn-adm-held-admissions-compose-with-installed-capacity :subject fn-adm-exposure-open

 :witness ((oc *m22a-closed-oc*) (xs *m22a-closed-xs*) (lim *m22a-lim*)
 (acfg nil) (peer "peer") (address *m22a-address*) (now 1) (bank *m22a-held*)
 (configured 2) (capacity 2) (profile *m22a-profile*) (img *m22a-img*) (cfg *m22a-cfg*)
   (limit *m22a-limit*) (tot *m22a-tot*) (old-id *m22a-id*) (kind :exposure))
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
