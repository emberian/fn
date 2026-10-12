; POST acceptance instance definitions; no Section A packet keystones.
(in-package "ACL2")
(include-book "post-context")
(include-book "runtime-contract")
(include-book "owner-parse-carried")
(include-book "records-concrete")
(set-verify-guards-eagerness 1)

(defun fn-pacc-out-max ()
  (declare (xargs :guard t)) (fn-adm-acc-out-max))

; rtc-size counts each cons and atom once.  A context has six conses,
; two scalar atoms, four octet-list terminators and its own terminator:
; 13 + 2*sum(field lengths).  The surrounding (ktxid ctx) adds four.
; pctx-max minus its 29 fixed wire octets bounds sum(field lengths).
(defun fn-pacc-max-state ()
  (declare (xargs :guard t))
  (+ 17 (* 2 (- *fn-pctx-max* 29))))

(defun fn-pacc-begin (x)
  (declare (xargs :guard t))
  (let ((ktxid (fn-pctx-get 0 x)) (ctx (fn-pctx-get 1 x)))
    (list (if (and (natp ktxid) (< ktxid (expt 2 64))) ktxid nil)
          (if (fn-pctx-p ctx) ctx nil))))

(defun fn-pacc-norm (a)
  (declare (xargs :guard t))
  (let ((ktxid (fn-pctx-get 0 a)) (ctx (fn-pctx-get 1 a)))
    (if (and (true-listp a) (equal (len a) 2)
             (or (null ktxid) (and (natp ktxid) (< ktxid (expt 2 64))))
             (or (null ctx) (fn-pctx-p ctx)))
        a
      nil)))

(defun fn-pacc-feed (a octets)
  (declare (xargs :guard t) (ignore octets)) (mv (fn-pacc-norm a) nil))
(defun fn-pacc-feed-cost (a octets)
  (declare (xargs :guard t) (ignore a octets)) 0)
(defun fn-pacc-end (a blen)
  (declare (xargs :guard t) (ignore blen))
  (let* ((a (fn-pacc-norm a))
         (ctx (fn-pctx-get 1 a))
         (ok (and (fn-pctx-p ctx)
                  (equal (fn-pctx-get 0 a) (nth 0 ctx)))))
    (if ok (mv ok (nth 1 ctx) (nth 2 ctx) (nth 3 ctx)
               (nth 4 ctx) (nth 5 ctx))
      (mv nil nil nil 0 nil nil))))
(defun fn-pacc-feed* (a windows)
  (declare (xargs :guard t))
  (if (consp windows)
      (mv-let (next part) (fn-pacc-feed a (car windows))
        (declare (ignore part)) (fn-pacc-feed* next (cdr windows)))
    a))

(local
 (defthm fn-pacc-octet-size-l
   (implies (fn-cbor-octet-listp x)
            (equal (fn-rtc-size x) (+ 1 (* 2 (len x)))))
   :hints (("Goal" :in-theory (enable fn-rtc-size fn-cbor-octet-listp)))))
(local
 (defthm fn-pacc-context-size-l
   (implies (fn-pctx-p ctx)
            (<= (fn-rtc-size ctx) (- (fn-pacc-max-state) 4)))
   :hints (("Goal" :in-theory (enable fn-pctx-p fn-pacc-max-state
                                    fn-adm-acc-out-max fn-adm-injected-block-max
                                    fn-rtc-size)
            :expand ((fn-rtc-size ctx)
                     (fn-rtc-size (cdr ctx))
                     (fn-rtc-size (cddr ctx))
                     (fn-rtc-size (cdddr ctx))
                     (fn-rtc-size (cddddr ctx))
                     (fn-rtc-size (cdr (cddddr ctx)))
                     (fn-rtc-size (cddr (cddddr ctx))))))))
(local
 (defthm fn-pacc-begin-bounded-l
   (<= (fn-rtc-size (fn-pacc-begin x)) (fn-pacc-max-state))
   :hints (("Goal" :in-theory (enable fn-pacc-begin fn-rtc-size)
            :use ((:instance fn-pacc-context-size-l
                             (ctx (fn-pctx-get 1 x))))))))

; All seven constraint bodies are restated directly; including the
; transaction machine is unnecessary.  Normalization leaves every begin
; state unchanged and bounds the feed's result for arbitrary input states.
(defthm fn-pacc-meets-fn-ptx-acc-max-state-natp
  (natp (fn-pacc-max-state)) :rule-classes :type-prescription)
(defthm fn-pacc-meets-fn-ptx-acc-out-max-natp
  (natp (fn-pacc-out-max)) :rule-classes :type-prescription)
(defthm fn-pacc-meets-fn-ptx-acc-begin-bounded
  (<= (fn-rtc-size (fn-pacc-begin txid)) (fn-pacc-max-state))
  :hints (("Goal" :use ((:instance fn-pacc-begin-bounded-l (x txid)))))
  :rule-classes :linear)
(defthm fn-pacc-meets-fn-ptx-acc-feed-bounded
  (<= (fn-rtc-size (mv-nth 0 (fn-pacc-feed a octets))) (fn-pacc-max-state))
  :hints (("Goal" :in-theory (e/d (fn-pacc-feed fn-pacc-norm fn-pctx-get
                                             fn-rtc-size)
                                   (fn-pctx-p))
           :expand ((fn-rtc-size a) (fn-rtc-size (cdr a))
                    (fn-pctx-get 1 a) (fn-pctx-get 0 (cdr a))
                    (len a) (len (cdr a)) (len (cddr a))
                    (true-listp a) (true-listp (cdr a))
                    (true-listp (cddr a)))
           :use ((:instance fn-pacc-context-size-l
                            (ctx (fn-pctx-get 1 a))))))
  :rule-classes :linear)
(defthm fn-pacc-meets-fn-ptx-acc-feed-cost-bounded
  (and (natp (fn-pacc-feed-cost a octets))
       (<= (fn-pacc-feed-cost a octets)
           (+ (* 4 (len octets)) (fn-pacc-out-max)))) :rule-classes nil)
(defthm fn-pacc-meets-fn-ptx-acc-feed-shape
  (and (fn-cbor-octet-listp (mv-nth 1 (fn-pacc-feed a octets)))
       (<= (len (mv-nth 1 (fn-pacc-feed a octets)))
           (+ (* 2 (len octets)) (fn-pacc-out-max)))) :rule-classes nil)
(defthm fn-pacc-meets-fn-ptx-acc-end-shape
  (mv-let (ok pre ins ioff sufhead suf) (fn-pacc-end a blen)
    (declare (ignore ok))
    (and (fn-cbor-octet-listp pre) (fn-cbor-octet-listp ins) (natp ioff)
         (fn-cbor-octet-listp sufhead) (fn-cbor-octet-listp suf)
         (<= (len pre) (fn-pacc-out-max)) (<= (len ins) (fn-pacc-out-max))
         (<= (len sufhead) *fn-ptx-sufhead-max*)
         (<= (len suf) (fn-pacc-out-max))))
  :hints (("Goal" :in-theory (enable fn-pacc-end fn-pctx-p)))
  :rule-classes nil)

; INJ = (decision secret login live-cfg parse-carry injection-cfg injection-obs).
; secret serves both the ipp and Cancel-Lock ring arguments; login serves
; both login and account; msgid is decision-msgid, as in apc-take:258-264.
; The last two fields retain the decision inputs for the splice recipe.
(defun fn-pacc-stored-payload (art inj)
  (declare (xargs :guard t) (ignore art))
  (let ((d (fn-pctx-get 0 inj)) (secret (fn-pctx-get 1 inj))
        (login (fn-pctx-get 2 inj)) (cfg (fn-pctx-get 3 inj))
        (carry (fn-pctx-get 4 inj)))
    (fn-apc-cl-served-payload secret login (fn-inj-decision-msgid d)
                            (fn-ipp-injected-octets d secret login cfg) carry)))

; Successful local injection and the take's valid parse carry are the
; domains relied on here (inj-decide:968-1048; apc-take:251-264).
; ipp/cl callees have guard T: no invented secret/login/live-cfg predicate.
(defun fn-pacc-injectionp (inj art)
  (declare (xargs :guard t))
  (and (true-listp inj) (equal (len inj) 7)
       (fn-inj-configp (fn-pctx-get 5 inj))
       (fn-clock-observationp (fn-pctx-get 6 inj))
       (equal (fn-pctx-get 0 inj)
              (fn-inj-decide art (fn-pctx-get 5 inj) (fn-pctx-get 6 inj)))
       (fn-inj-injectedp (fn-pctx-get 0 inj))
       (fn-apc-p (fn-pctx-get 4 inj))))

(defun fn-pacc-splice (art inj)
  (declare (xargs :guard t))
  (let* ((d (fn-pctx-get 0 inj)) (secret (fn-pctx-get 1 inj))
         (login (fn-pctx-get 2 inj)) (cfg (fn-pctx-get 3 inj))
         (carry (fn-pctx-get 4 inj)) (icfg (fn-pctx-get 5 inj))
         (obs (fn-pctx-get 6 inj)) (msgid (fn-inj-decision-msgid d))
         (candidate (fn-pctx-get 1 (fn-article-parse art)))
         (parsed (if (fn-article-syntax-p candidate) candidate '(nil nil nil)))
         (gid (not (fn-inj-nth 1
                              (if (fn-article-syntax-p parsed)
                                  (fn-af-proto-article-check parsed) nil))))
         (gdate (fn-inj-absentp parsed *fn-inj-date-name*))
         (agent (fn-inj-config-agent icfg))
         (date (fn-inj-date-octets (fn-inj-instant-of (fn-clock-wall obs))))
         (pathp (not (fn-inj-absentp parsed *fn-inj-path-name*)))
         (block (if pathp (fn-inj-block date msgid agent gid gdate)
                  (fn-inj-prefix date msgid agent gid gdate)))
         (params (fn-ipp-params secret login (fn-ipp-complaints cfg)))
         (injected (fn-ipp-injected-octets d secret login cfg))
         (fields (fn-apc-received-fields injected carry))
         (cl (fn-cll-lines (fn-cl-lock-value secret login msgid fields)
                           (fn-cl-key-values secret login fields))))
    (mv (fn-pctx-cat cl (fn-ipp-with-params block msgid params))
        (if pathp (fn-inj-path-insert agent) nil)
        (if pathp (nfix (fn-inj-path-offset art)) 0))))

(defun fn-pctx-of-prepared (s rec art inj)
  (declare (xargs :guard t))
  (mv-let (p0 ins ioff) (fn-pacc-splice art inj)
    (let ((suffix (fn-pctx-cat (fn-record-groups-octets-impl rec)
                               (fn-record-tail-octets-impl rec))))
      (list (fn-state-next-txid (fn-node-acceptance (fn-sn-node s)))
            (fn-pctx-cat (fn-record-head-octets-impl rec) p0) ins ioff
            (fn-inj-take-n (min 9 (len suffix)) suffix)
            (fn-inj-drop-n 9 suffix)))))

; Logic composition of owner-host:2313,2351-2354,2816-2823 and native
; owner:3568-3572's seal between prepare and pending-octets.  ARENA is
; the pre-seal arena; h is its predicted next handle.  defun-nx allows
; this value-level stobj composition to return only octets.  No host
; :program wrapper is imported or called; this is not a live prepare.
(defun-nx fn-pacc-batch-record-octets (s obs art inj fields fn-arena)
  (declare (xargs :verify-guards nil))
  (let* ((rec (fn-sn-article-record s obs (fn-pctx-get 0 fields)
                                   (fn-pacc-stored-payload art inj)
                                   (fn-pctx-get 1 fields) (fn-pctx-get 2 fields)
                                   (fn-pctx-get 3 fields) (fn-pctx-get 4 fields)
                                   (fn-pctx-get 5 fields)))
         (row (fn-apc-intern-row-at rec (fn-sn-keyring s)
                                    (fn-sn-keyring-generation s)
                                    (fn-arena-count fn-arena)
                                    (fn-pctx-get 4 inj)))
         (sealed (fn-arena-seal-list (fn-record-payload rec) fn-arena)))
    (fn-rcon-store-event-encode (fn-row-wire-of row sealed))))
