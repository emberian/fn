; POST acceptance, context v2 layout, and the approved A0/A1/A3 and G-BOUND keystones.
(in-package "ACL2")
(include-book "post-context")
(include-book "nntp-post")
(include-book "runtime-contract")
(include-book "owner-parse-carried")
(include-book "records-concrete")
(include-book "post-fields")
(include-book "store-config")
(include-book "store-profile-carried")
(set-verify-guards-eagerness 1)

(defun fn-pacc-out-max ()
  (declare (xargs :guard t)) (fn-adm-acc-out-max))

; rtc-size counts each cons and atom once.  A context has seven conses,
; three scalar atoms, four octet-list terminators and its own terminator:
; 15 + 2*sum(field lengths).  The surrounding (ktxid ctx) adds four.
; pctx-max minus its 33 fixed wire octets bounds sum(field lengths).
(defun fn-pacc-max-state ()
  (declare (xargs :guard t))
  (+ 19 (* 2 (- *fn-pctx-max* 33))))

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
                     (fn-rtc-size (cddr (cddddr ctx)))
                     (fn-rtc-size (cdddr (cddddr ctx))))))))
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

; Successful gated injection and the take's valid parse carry are the
; domains relied on here (nntp-post:277-285; apc-take:251-264).  Slot 0
; holds the direct decision or the moderation-forward envelope decision.
; ipp/cl callees have guard T: no invented secret/login/live-cfg predicate.
(defun fn-pacc-injectionp (inj art)
  (declare (xargs :guard t))
  (and (true-listp inj) (equal (len inj) 7)
       (fn-inj-configp (fn-pctx-get 5 inj))
       (fn-clock-observationp (fn-pctx-get 6 inj))
       (equal (fn-pctx-get 0 inj)
              (fn-post-gated-decision art (fn-pctx-get 5 inj) (fn-pctx-get 6 inj)))
       (fn-inj-injectedp (fn-pctx-get 0 inj))
       (fn-apc-p (fn-pctx-get 4 inj))))

; Direct injection keeps the original recipe.  A forwarded envelope stores
; the untouched source as a suffix: its added octets are PRE, INS is nil,
; and the insertion offset is zero.
(defun fn-pacc-splice (art inj)
  (declare (xargs :guard t))
  (if (equal (fn-pctx-get 0 inj)
             (fn-inj-decide art (fn-pctx-get 5 inj) (fn-pctx-get 6 inj)))
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
        (if pathp (nfix (fn-inj-path-offset art)) 0)))
    (let ((stored (fn-pacc-stored-payload art inj)))
      (mv (fn-inj-take-n (nfix (- (len stored) (len art))) stored)
          nil 0))))

(defun fn-pacc-derived-names (xs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp xs)
      (cons (fn-record-octets-string (car xs)) (fn-pacc-derived-names (cdr xs)))
    nil))

(defun fn-pacc-derived-fields (s art inj)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((d (fn-pctx-get 0 inj)) (cfg (fn-pctx-get 3 inj))
         (payload (fn-pacc-stored-payload art inj))
         (mid (fn-inj-decision-msgid d))
         (domain (fn-state-groups (fn-node-acceptance (fn-sn-node s))))
         (filing (fn-apc-filing-plan payload (fn-inj-decision-groups d) domain
                                      (fn-pctx-get 4 inj)))
         (names (if (equal (fn-pctx-get 0 filing) :file)
                    (fn-pacc-derived-names (fn-pctx-get 1 filing))
                  :bad))
         (codes (fn-store-codes-from-groups names domain))
         (groups (fn-store-groups-from-codes codes domain))
         (subject (fn-id-subject-of-payload payload))
         (oid (fn-id-obligation-of mid subject)))
    (list (fn-record-octets-string mid) groups
          (fn-record-octets-string (fn-id-text oid))
          (fn-record-octets-string (fn-id-text subject))
          (fn-record-octets-string
           (fn-pfld-post-evidence (fn-cfg-policy (fn-cfg-value cfg) "path-identity")
                                  (fn-cfg-generation cfg)))
          (fn-charge-for-payload (len payload)))))

(defun fn-pacc-prepared-record (s obs art inj)
  (declare (xargs :guard t :verify-guards nil))
  (let ((fields (fn-pacc-derived-fields s art inj)))
    (fn-sn-article-record s obs (fn-pctx-get 0 fields) (fn-pacc-stored-payload art inj)
                          (fn-pctx-get 1 fields) (fn-pctx-get 2 fields)
                          (fn-pctx-get 3 fields) (fn-pctx-get 4 fields)
                          (fn-pctx-get 5 fields))))

(defun fn-pacc-profile-admitted-postp (s art inj profile pcarry)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((fields (fn-pacc-derived-fields s art inj))
         (d (fn-pctx-get 0 inj)) (icfg (fn-pctx-get 5 inj)))
    (and (fn-pvc-carryp pcarry)
         (equal (fn-pa-carrier-form (fn-pacc-stored-payload art inj)) :absent)
         (equal (fn-inj-config-header-limits icfg) (fn-bs-profile-header-limits profile))
         (equal (fn-pvc-post-boundary-carried
                 pcarry profile (fn-inj-decision-msgid d)
                 (len (fn-pacc-stored-payload art inj))
                 (len (fn-pctx-get 1 fields)) (fn-pctx-get 5 fields))
                :ok))))

(defun fn-pacc-prepared-gsec (rec)
  (declare (xargs :guard t)) (fn-record-groups-octets rec))

(defun fn-pacc-post-buffer (ctx art gsec)
  (declare (xargs :guard t))
  (fn-pctx-cat (fn-pctx-encode ctx) (fn-pctx-cat art gsec)))

(defun fn-pctx-of-prepared (s rec art inj)
  (declare (xargs :guard t))
  (mv-let (p0 ins ioff) (fn-pacc-splice art inj)
    (list (fn-state-next-txid (fn-node-acceptance (fn-sn-node s)))
          (fn-pctx-cat (fn-record-head-octets rec) p0)
          ins ioff nil (fn-record-tail-octets rec)
          (len (fn-record-groups-octets rec)))))

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

; Acceptance keystones: the record seam remains constrained.
(local (include-book "injection-info-params-invariants"))

(local
 (defthm fn-pacc-a0-inj-append-is-append
   (equal (fn-inj-append a b) (append a b))
   :hints (("Goal" :in-theory (enable fn-inj-append)))))

(local
 (defthm fn-pacc-a0-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(local
 (defthm fn-pacc-a0-line-of-append-lf-free
   (implies (not (member-equal 10 a))
            (equal (fn-pb-line (append a y)) (append a (fn-pb-line y))))))

(local
 (defthm fn-pacc-a0-strip-of-append-left
   (implies (true-listp a)
            (equal (fn-inj-strip a (append a b)) b))
   :hints (("Goal" :in-theory (enable fn-inj-strip)))))

(local
 (defthm fn-pacc-a0-take-of-append
   (implies (and (true-listp a) (equal n (len a)))
            (equal (fn-inj-take n (append a b)) a))
   :hints (("Goal" :in-theory (enable fn-inj-take)))))

(local
 (defthm fn-pacc-a0-len-of-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthm fn-pacc-a0-drop-of-append
   (implies (and (true-listp a) (equal n (len a)))
            (equal (fn-inj-drop n (append a b)) b))
   :hints (("Goal" :in-theory (enable fn-inj-drop)))))

(local
 (defthm fn-pacc-a0-info-line-agent-of-an-info-line
   (implies (and (true-listp agent) (consp agent)
                 (not (member-equal 10 agent)) (not (member-equal 59 agent)))
            (equal (fn-pb-info-line-agent
                    (append (fn-inj-injection-info-line agent) rest))
                   agent))
   :hints (("Goal" :in-theory (enable fn-pb-info-line-agent
                                      fn-inj-injection-info-line fn-inj-strip)))))

(local
 (defthm fn-pacc-a0-s1
   (fn-pb-opensp *fn-inj-injection-date-field*
                  (append (fn-inj-injection-date-line date) x))
   :hints (("Goal" :in-theory (enable fn-pb-opensp fn-inj-strip-optional fn-inj-strip
                                      fn-inj-drop fn-inj-injection-date-line fn-inj-date-line fn-inj-message-id-line fn-inj-injection-info-line)))))

(local
 (defthm fn-pacc-a0-s2
   (not (fn-pb-opensp *fn-inj-injection-date-field*
                       (append (fn-inj-injection-info-line agent) x)))
   :hints (("Goal" :in-theory (enable fn-pb-opensp fn-inj-strip-optional fn-inj-strip
                                      fn-inj-drop fn-inj-injection-date-line fn-inj-date-line fn-inj-message-id-line fn-inj-injection-info-line)))))

(local
 (defthm fn-pacc-a0-s3
   (implies (and (true-listp date) (equal (len date) 31))
            (equal (fn-inj-drop 49 (append (fn-inj-injection-date-line date) x)) x))
   :hints (("Goal" :in-theory (e/d (fn-inj-injection-date-line) (fn-inj-drop fn-pacc-a0-drop-of-append))
            :use ((:instance fn-pacc-a0-drop-of-append
                             (a (fn-inj-injection-date-line date)) (b x) (n 49)))))))

(local
 (defthm fn-pacc-a0-message-id-line-is-a-true-list
   (true-listp (fn-inj-message-id-line msgid))
   :hints (("Goal" :in-theory (enable fn-inj-message-id-line)))))

(local
 (defthm fn-pacc-a0-append-of-a-cons-is-not-no
   (implies (consp a) (not (equal (append a b) :no)))))

(local
 (defthm fn-pacc-a0-s4
   (implies (not (equal x :no))
            (equal (fn-inj-strip-optional (fn-inj-message-id-line msgid)
                                          (append (fn-inj-message-id-line msgid) x))
                   x))
   :hints (("Goal" :in-theory (e/d (fn-inj-strip-optional)
                                   (fn-inj-message-id-line fn-pacc-a0-strip-of-append-left))
            :use ((:instance fn-pacc-a0-strip-of-append-left
                             (a (fn-inj-message-id-line msgid)) (b x)))))))

(local
 (defthm fn-pacc-a0-s5
   (equal (fn-inj-strip-optional (fn-inj-message-id-line msgid)
                                 (append (fn-inj-date-line date) x))
          (append (fn-inj-date-line date) x))
   :hints (("Goal" :in-theory (enable fn-pb-opensp fn-inj-strip-optional fn-inj-strip
                                      fn-inj-drop fn-inj-injection-date-line fn-inj-date-line fn-inj-message-id-line fn-inj-injection-info-line)))))

(local
 (defthm fn-pacc-a0-s6
   (equal (fn-inj-strip-optional (fn-inj-message-id-line msgid)
                                 (append (fn-inj-injection-info-line agent) x))
          (append (fn-inj-injection-info-line agent) x))
   :hints (("Goal" :in-theory (enable fn-pb-opensp fn-inj-strip-optional fn-inj-strip
                                      fn-inj-drop fn-inj-injection-date-line fn-inj-date-line fn-inj-message-id-line fn-inj-injection-info-line)))))

(local
 (defthm fn-pacc-a0-s7
   (fn-pb-opensp *fn-inj-date-field* (append (fn-inj-date-line date) x))
   :hints (("Goal" :in-theory (enable fn-pb-opensp fn-inj-strip-optional fn-inj-strip
                                      fn-inj-drop fn-inj-injection-date-line fn-inj-date-line fn-inj-message-id-line fn-inj-injection-info-line)))))

(local
 (defthm fn-pacc-a0-s8
   (implies (and (true-listp date) (equal (len date) 31))
            (equal (fn-inj-drop 39 (append (fn-inj-date-line date) x)) x))
   :hints (("Goal" :in-theory (e/d (fn-inj-date-line) (fn-inj-drop fn-pacc-a0-drop-of-append))
            :use ((:instance fn-pacc-a0-drop-of-append
                             (a (fn-inj-date-line date)) (b x) (n 39)))))))

(local
 (defthm fn-pacc-a0-s9
   (not (fn-pb-opensp *fn-inj-date-field*
                       (append (fn-inj-injection-info-line agent) x)))
   :hints (("Goal" :in-theory (enable fn-pb-opensp fn-inj-strip-optional fn-inj-strip
                                      fn-inj-drop fn-inj-injection-date-line fn-inj-date-line fn-inj-message-id-line fn-inj-injection-info-line)))))

(local
 (defthm fn-pacc-a0-block-agent-of-a-block
   (implies (and (true-listp agent) (consp agent)
                 (not (member-equal 10 agent)) (not (member-equal 59 agent))
                 (true-listp date) (equal (len date) 31))
            (equal (fn-pb-block-agent
                    (append (fn-inj-block date msgid agent gid gdate) rest)
                    msgid)
                   agent))
   :hints (("Goal" :in-theory (e/d (fn-pb-block-agent fn-inj-block)
                                   (fn-pb-opensp fn-inj-strip-optional fn-inj-strip
                                    fn-inj-drop fn-pb-info-line-agent
                                    fn-inj-injection-date-line fn-inj-date-line fn-inj-message-id-line fn-inj-injection-info-line))
            :do-not-induct t
            :cases ((and gid gdate) (and gid (not gdate))
                    (and (not gid) gdate))))))

(local
 (defthm fn-pacc-a0-path-line-agent-of-another-line
   (implies (and (consp x) (not (equal (car x) 80)) (not (equal (car x) 10)))
            (not (fn-pb-path-line-agent x)))
   :hints (("Goal" :in-theory (enable fn-pb-path-line-agent fn-inj-strip)
            :expand ((fn-pb-line x))))))

(local
 (defthm fn-pacc-a0-a-block-opens-with-i
   (and (consp (append (fn-inj-block date msgid agent gid gdate) rest))
        (equal (car (append (fn-inj-block date msgid agent gid gdate) rest)) 73))
   :hints (("Goal" :in-theory (enable fn-inj-block fn-inj-injection-date-line
                                      fn-inj-injection-info-line)
            :cases ((or gid gdate))))))

(local
 (defthm fn-pacc-a0-path-agent-of-a-block
   (implies (and (true-listp agent) (consp agent)
                 (not (member-equal 10 agent)) (not (member-equal 59 agent))
                 (true-listp date) (equal (len date) 31))
            (equal (fn-pb-path-agent
                    (fn-inj-append (fn-inj-block date msgid agent gid gdate) rest)
                    msgid)
                   agent))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-pb-path-agent)
                            (fn-pb-block-agent fn-pb-path-line-agent fn-inj-block))))))

(local
 (defthm fn-pacc-a0-a-configured-agent-is-a-line-free-list
   (implies (fn-inj-configp config)
            (and (true-listp (fn-inj-config-agent config))
                 (consp (fn-inj-config-agent config))
                 (not (member-equal 10 (fn-inj-config-agent config)))
                 (not (member-equal 59 (fn-inj-config-agent config)))))
   :hints (("Goal" :in-theory (enable fn-inj-configp fn-af-dot-atom-textp)))))

(local
 (defthm fn-pacc-a0-date-octets-shape
   (and (true-listp (fn-inj-date-octets inst))
        (equal (len (fn-inj-date-octets inst)) 31))
   :hints (("Goal" :in-theory (enable fn-inj-date-octets)))))

(local
 (defthm fn-pacc-a0-strip-of-a-different-first-octet
   (implies (and (consp a) (consp b) (not (equal (car a) (car b))))
            (equal (fn-inj-strip a (append b x)) :no))
   :hints (("Goal" :in-theory (enable fn-inj-strip)))))

(local
 (defthm fn-pacc-a0-lines-shape
   (and (consp (fn-inj-path-line agent))
        (equal (car (fn-inj-path-line agent)) 80)
        (consp (fn-inj-injection-date-line date))
        (equal (car (fn-inj-injection-date-line date)) 73)
        (consp (fn-inj-injection-info-line agent))
        (equal (car (fn-inj-injection-info-line agent)) 73)
        (consp (fn-inj-injection-info-line-with agent params))
        (equal (car (fn-inj-injection-info-line-with agent params)) 73)
        (consp (fn-inj-message-id-line msgid))
        (equal (car (fn-inj-message-id-line msgid)) 77)
        (consp (fn-inj-date-line date))
        (equal (car (fn-inj-date-line date)) 68)
        (true-listp (fn-inj-path-line agent))
        (true-listp (fn-inj-injection-date-line date))
        (true-listp (fn-inj-injection-info-line agent))
        (true-listp (fn-inj-injection-info-line-with agent params))
        (true-listp (fn-inj-message-id-line msgid))
        (true-listp (fn-inj-date-line date)))
   :hints (("Goal" :in-theory (enable fn-inj-path-line fn-inj-injection-date-line
                                      fn-inj-injection-info-line
                                      fn-inj-injection-info-line-with
                                      fn-inj-message-id-line fn-inj-date-line)))))

(local
 (defthm fn-pacc-a0-len-of-the-dated-lines
   (implies (equal (len date) 31)
            (and (equal (len (fn-inj-injection-date-line date)) 49)
                 (equal (len (fn-inj-date-line date)) 39)))
   :hints (("Goal" :in-theory (enable fn-inj-injection-date-line fn-inj-date-line)))))

(local
 (defthm fn-pacc-a0-opens-of-the-lines
   (and (fn-pb-opensp *fn-inj-injection-date-field*
                      (append (fn-inj-injection-date-line date) x))
        (not (fn-pb-opensp *fn-inj-injection-date-field*
                           (append (fn-inj-injection-info-line agent) x)))
        (not (fn-pb-opensp *fn-inj-date-field*
                           (append (fn-inj-injection-info-line agent) x)))
        (fn-pb-opensp *fn-inj-date-field* (append (fn-inj-date-line date) x))
        (not (fn-pb-opensp *fn-inj-injection-date-field*
                           (append (fn-inj-message-id-line msgid) x)))
        (not (fn-pb-opensp *fn-inj-injection-date-field*
                           (append (fn-inj-date-line date) x))))
   :hints (("Goal" :in-theory (enable fn-pb-opensp fn-inj-strip
                                      fn-inj-injection-date-line fn-inj-date-line
                                      fn-inj-injection-info-line
                                      fn-inj-message-id-line)))))

(local
 (defthm fn-pacc-a0-at-stamp-of-a-block
   (implies (and (true-listp date) (equal (len date) 31)
                 (not (equal source :no)))
            (equal (fn-ipp-at-stamp (append (fn-inj-block date msgid agent gid gdate)
                                            source)
                                    agent msgid params)
                   (append (fn-ipp-block-with date msgid agent gid gdate params)
                           source)))
   :hints (("Goal" :in-theory (enable fn-inj-block fn-ipp-block-with)
            :cases ((and gid gdate) (and gid (not gdate))
                    (and (not gid) gdate))))))

(local
 (defthm fn-pacc-a0-a-block-is-not-a-path-line
   (equal (fn-inj-strip (fn-inj-path-line agent)
                        (append (fn-inj-block date msgid agent2 gid gdate) x))
          :no)
   :hints (("Goal" :in-theory (enable fn-inj-block)
            :cases ((or gid gdate))))))

(local
 (defthm fn-pacc-a0-prefix-is-the-path-line-and-the-block
   (equal (append (fn-inj-prefix date msgid agent gid gdate) x)
          (append (fn-inj-path-line agent)
                  (append (fn-inj-block date msgid agent gid gdate) x)))
   :hints (("Goal" :in-theory (enable fn-inj-prefix fn-inj-block)))))

(local
 (defthm fn-pacc-a0-with-params-of-a-prefix
   (implies (and (true-listp date) (equal (len date) 31) (consp params) agent
                 (not (equal source :no))
                 (equal (fn-pb-path-agent
                         (append (fn-inj-prefix date msgid agent gid gdate) source)
                         msgid)
                        agent))
            (equal (fn-ipp-with-params
                    (append (fn-inj-prefix date msgid agent gid gdate) source)
                    msgid params)
                   (append (fn-ipp-prefix-with date msgid agent gid gdate params)
                           source)))
   :hints (("Goal" :in-theory (e/d (fn-ipp-with-params fn-ipp-prefix-with)
                                   (fn-ipp-at-stamp fn-inj-prefix fn-inj-block
                                    fn-pb-path-agent fn-ipp-block-with))))))

(local
 (defthm fn-pacc-a0-with-params-of-a-block
   (implies (and (true-listp date) (equal (len date) 31) (consp params) agent
                 (not (equal rest :no))
                 (equal (fn-pb-path-agent
                         (append (fn-inj-block date msgid agent gid gdate) rest)
                         msgid)
                        agent))
            (equal (fn-ipp-with-params
                    (append (fn-inj-block date msgid agent gid gdate) rest)
                    msgid params)
                   (append (fn-ipp-block-with date msgid agent gid gdate params)
                           rest)))
   :hints (("Goal" :in-theory (e/d (fn-ipp-with-params)
                                   (fn-ipp-at-stamp fn-inj-prefix fn-inj-block
                                    fn-pb-path-agent fn-ipp-block-with))))))

(local
 (defthm fn-pacc-a0-no-params-lines
   (implies (not (consp params))
            (and (equal (fn-ipp-prefix-with date msgid agent gid gdate params)
                        (fn-inj-prefix date msgid agent gid gdate))
                 (equal (fn-ipp-block-with date msgid agent gid gdate params)
                        (fn-inj-block date msgid agent gid gdate))))
   :hints (("Goal" :in-theory (enable fn-ipp-prefix-with fn-ipp-block-with
                                      fn-inj-prefix fn-inj-block
                                      fn-inj-injection-info-line-with
                                      fn-inj-injection-info-line)))))

(local
 (defthm fn-pacc-a0-with-no-params
   (implies (not (consp params))
            (equal (fn-ipp-with-params x msgid params) x))
   :hints (("Goal" :in-theory (enable fn-ipp-with-params)))))

(local
 (defthm fn-pacc-intern-materializes-l
 (implies (and (fn-record-p w) (natp generation) (fn-apc-p carry))
  (equal (fn-row-wire-of
           (fn-apc-intern-row-at w keyring generation (fn-arena-count fn-arena) carry)
           (fn-arena-seal-list (fn-record-payload w) fn-arena)) w))
 :hints (("Goal"
  :use ((:instance fn-apc-intern-row-at-is-reference (h (fn-arena-count fn-arena)))
        (:instance fn-cat-intern-list-is-row-at-count)
        (:instance fn-held-p-of-intern-list)
        (:instance fn-cat-intern-list-materializes)
        (:instance fn-intern-list-handle))
  :in-theory (e/d (fn-row-wire-of fn-row-bytes fn-held-wire-of)
                 (fn-apc-intern-row-at fn-intern-row-at fn-cat-intern-list fn-record-p
                  fn-apc-intern-row-at-is-reference fn-intern-list-handle
                  fn-held-p fn-held-p-of-intern-list fn-cat-intern-list-materializes
                  fn-cat-intern-list-is-row-at-count))))))

(local
 (defthm fn-pacc-state-generation-l
 (implies (fn-sn-statep s) (natp (fn-sn-keyring-generation s)))
 :hints (("Goal" :in-theory '(fn-sn-statep)))))

(local
 (defthm fn-pacc-injection-carry-l
 (implies (fn-pacc-injectionp inj art) (fn-apc-p (fn-pctx-get 4 inj)))
 :hints (("Goal" :in-theory '(fn-pacc-injectionp)))))

(local
 (defthm fn-pacc-block-prefix-true-listp-l
 (and (true-listp (fn-inj-block date msgid agent gid gdate))
      (true-listp (fn-inj-prefix date msgid agent gid gdate))
      (true-listp (fn-ipp-block-with date msgid agent gid gdate params))
      (true-listp (fn-ipp-prefix-with date msgid agent gid gdate params)))
 :hints (("Goal" :in-theory
  (enable fn-inj-block fn-inj-prefix fn-ipp-block-with fn-ipp-prefix-with
          fn-inj-append fn-inj-injection-info-line-with)))))

(local
 (defthm fn-pacc-standalone-block-l
 (implies (and (true-listp date) (equal (len date) 31)
               (true-listp agent) (consp agent)
               (not (member-equal 10 agent)) (not (member-equal 59 agent)))
  (equal (fn-ipp-with-params (fn-inj-block date msgid agent gid gdate) msgid params)
         (fn-ipp-block-with date msgid agent gid gdate params)))
 :hints (("Goal" :cases ((consp params))
   :use ((:instance fn-pacc-a0-with-params-of-a-block (rest nil))
         (:instance fn-pacc-a0-path-agent-of-a-block (rest nil)))
   :in-theory (e/d (fn-pacc-a0-inj-append-is-append)
                  (fn-inj-block fn-ipp-block-with fn-ipp-with-params fn-pb-path-agent
                   fn-pacc-a0-with-params-of-a-block fn-pacc-a0-path-agent-of-a-block))))))

(local
 (defthm fn-pacc-prefix-path-l
 (equal (fn-inj-prefix date msgid agent gid gdate)
        (append (fn-inj-path-line agent) (fn-inj-block date msgid agent gid gdate)))
 :hints (("Goal" :in-theory (enable fn-inj-prefix fn-inj-block)))))

(local
 (defthm fn-pacc-standalone-prefix-l
 (implies (and (true-listp date) (equal (len date) 31)
               (true-listp agent) (consp agent)
               (not (member-equal 10 agent)) (not (member-equal 59 agent)))
  (equal (fn-ipp-with-params (fn-inj-prefix date msgid agent gid gdate) msgid params)
         (fn-ipp-prefix-with date msgid agent gid gdate params)))
 :hints (("Goal" :cases ((consp params))
   :use ((:instance fn-pacc-a0-with-params-of-a-prefix (source nil))
         (:instance fn-pb-path-agent-of-a-path-line
                    (rest (fn-inj-block date msgid agent gid gdate))))
   :in-theory (e/d (fn-pacc-prefix-path-l)
                  (fn-inj-prefix fn-inj-block fn-ipp-prefix-with fn-ipp-with-params fn-pb-path-agent
                   fn-pacc-a0-with-params-of-a-prefix fn-pb-path-agent-of-a-path-line))))))

(local
 (defthm fn-pacc-take-n-is-take-l
 (implies (and (natp n) (<= n (len x)))
          (equal (fn-inj-take-n n x) (take n x)))
 :hints (("Goal" :in-theory (enable fn-inj-take-n take)))))

(local
 (defthm fn-pacc-success-parse-l
 (implies (fn-inj-injectedp (fn-inj-decide art config obs))
  (and (fn-article-result-okp (fn-article-parse art))
       (fn-article-syntax-p (fn-article-result-article (fn-article-parse art)))))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
    '(fn-inj-decide fn-inj-refuse fn-inj-injectedp fn-inj-decision-status-of-fn-inj-make-decision))))))

(local
 (defthm fn-pacc-len-take-bound-l
 (<= (len (fn-inj-take-n n x)) (len x))
 :hints (("Goal" :in-theory (enable fn-inj-take-n))) :rule-classes :linear))

(local
 (defthm fn-pacc-path-open-bound-l
 (implies (fn-inj-path-openp x) (<= 6 (len x)))
 :hints (("Goal" :in-theory (enable fn-inj-path-openp))) :rule-classes :linear))

(local
 (defthm fn-pacc-path-bounds-l
 (implies (fn-inj-path-scan x bol)
          (and (natp (fn-inj-path-scan x bol))
               (<= (fn-inj-path-scan x bol) (len x))))
 :hints (("Goal" :induct (fn-inj-path-scan x bol)
                 :in-theory (e/d (fn-inj-path-scan) (fn-inj-path-openp))))))

(local
 (defthm fn-pacc-drop-n-is-nthcdr-l
 (implies (and (natp n) (true-listp x))
          (equal (fn-inj-drop-n n x) (nthcdr n x)))
 :hints (("Goal" :in-theory (enable fn-inj-drop-n nthcdr)))))

(local
 (defthm fn-pacc-cat-is-append-l (equal (fn-pctx-cat x y) (append x y)) :hints (("Goal" :in-theory (enable fn-pctx-cat)))))

(local
 (defthm fn-pacc-gated-injection-decision-l
 (implies (fn-pacc-injectionp inj art)
  (and (fn-inj-configp (fn-pctx-get 5 inj))
       (fn-inj-injectedp (fn-inj-decide art (fn-pctx-get 5 inj) (fn-pctx-get 6 inj)))
       (or (equal (fn-pctx-get 0 inj)
                  (fn-inj-decide art (fn-pctx-get 5 inj) (fn-pctx-get 6 inj)))
           (equal (fn-inj-decision-msgid (fn-pctx-get 0 inj))
                  (fn-mod-envelope-msgid
                   (fn-inj-decision-msgid
                    (fn-inj-decide art (fn-pctx-get 5 inj) (fn-pctx-get 6 inj))))))))
 :hints (("Goal" :use ((:instance fn-post-gated-decision-is-the-decision-or-its-envelope
                      (source art) (config (fn-pctx-get 5 inj))
                      (injection (fn-pctx-get 6 inj))))
          :in-theory (union-theories (theory 'ground-zero) '(fn-pacc-injectionp))))))

(local
 (defthm fn-pacc-parsed-candidate-l
 (equal (fn-pctx-get 1 x) (fn-article-result-article x))
 :hints (("Goal" :in-theory (enable fn-pctx-get fn-article-result-article)))))

(local
 (defthm fn-pacc-octets-true-listp-l
 (implies (fn-octet-listp x) (true-listp x))
 :hints (("Goal" :in-theory (enable fn-octet-listp)))))

(local
 (defthm fn-pacc-fix-true-list-l (implies (true-listp x) (equal (true-list-fix x) x)) :hints (("Goal" :in-theory (enable true-list-fix)))))

(local
 (defthm fn-pacc-fix-append-l (equal (true-list-fix (append x y)) (append x (true-list-fix y))) :hints (("Goal" :in-theory (enable true-list-fix append)))))

; Coordinator ruling 12:40: proof support for the reduced hypotheses.
(local
 (defthm fn-pacc-parse-requires-octets-l
 (implies (fn-article-result-okp (fn-article-parse art)) (fn-cbor-octet-listp art))
 :hints (("Goal" :do-not-induct t :in-theory
 (union-theories (theory 'ground-zero)
 '(fn-article-parse fn-article-parse-under fn-article-result-okp fn-article-error))))))

(local
 (defthm fn-pacc-cbor-is-octets-l
 (equal (fn-cbor-octet-listp x) (fn-octet-listp x))
 :hints (("Goal" :in-theory (enable fn-cbor-octet-listp fn-cbor-octetp fn-octet-listp fn-octetp)))))

(local
 (defthm fn-pacc-injection-requires-octets-l
 (implies (fn-pacc-injectionp inj art) (fn-octet-listp art))
 :hints (("Goal" :use ((:instance fn-pacc-gated-injection-decision-l)
 (:instance fn-pacc-success-parse-l (config (fn-pctx-get 5 inj)) (obs (fn-pctx-get 6 inj)))
 (:instance fn-pacc-parse-requires-octets-l))
 :in-theory (union-theories (theory 'ground-zero) '(fn-pacc-cbor-is-octets-l))))))

(local
 (defthm fn-pacc-carried-facts-shape-l
 (fn-hf-p (fn-apc-held-facts-of bytes carry))
 :hints (("Goal" :in-theory (e/d (fn-apc-held-facts-of fn-hf-p fn-hf-internals fn-hf-startp)
 (fn-apc-control-of fn-hnov-of-parsed fn-hf-control-with-nov fn-hf-split-index fn-hf-body-lines-of))))))

(local
 (defthm fn-pacc-verified-statement-shape-l
 (implies (fn-prin-verifiedp s keyring) (fn-stmt-p s))
 :hints (("Goal" :in-theory (enable fn-prin-verifiedp)))))

(local
 (defthm fn-pacc-carried-context-shape-l
 (implies (natp generation) (fn-hc-p (fn-apc-held-context-of bytes keyring generation carry)))
 :hints (("Goal" :in-theory (e/d (fn-apc-held-context-of fn-hc-p fn-hc-internals fn-hc-anyp fn-hc-verdictp fn-stx-verifiedp fn-stx-verdict fn-stx-make-verdict fn-stx-verdict-token fn-stx-verdict-generation)
 (fn-apc-stx-parse fn-stx-statement-of fn-stx-field fn-stx-parse-header fn-stx-reattach))))))

(local
 (defthm fn-pacc-carried-row-held-l
 (implies (and (fn-record-p w) (natp generation) (natp h))
 (fn-held-p (fn-apc-intern-row-at w keyring generation h carry)))
 :hints (("Goal" :in-theory (e/d (fn-apc-intern-row-at fn-record-p fn-held-p fn-record-internals fn-held-internals)
 (fn-apc-held-facts-of fn-apc-held-context-of))))))

(local
 (defthm fn-pacc-carried-row-alpha-l
 (implies (fn-record-shapep w)
 (equal (fn-held-wire (fn-apc-intern-row-at w keyring generation h carry) (fn-record-payload w)) w))
 :hints (("Goal" :in-theory (e/d (fn-held-wire fn-apc-intern-row-at)
 (fn-apc-held-facts-of fn-apc-held-context-of))))))

(local
 (defthm fn-pacc-carried-row-handle-l
 (equal (fn-record-payload (fn-apc-intern-row-at w keyring generation h carry)) h)
 :hints (("Goal" :in-theory (enable fn-apc-intern-row-at)))))

(local
 (defthm fn-pacc-direct-intern-materializes-l
 (implies (and (fn-record-p w) (natp generation))
  (equal (fn-row-wire-of
           (fn-apc-intern-row-at w keyring generation (fn-arena-count fn-arena) carry)
           (fn-arena-seal-list (fn-record-payload w) fn-arena)) w))
 :hints (("Goal" :in-theory
 (e/d (fn-row-wire-of fn-row-bytes)
      (fn-apc-intern-row-at fn-held-p fn-held-wire fn-arena-payload-is-nth
       fn-arena-count-is-len fn-arena-seal-list-is-append
       fn-pacc-carried-row-held-l fn-pacc-carried-row-alpha-l fn-arena-seal-new-handle))
 :use ((:instance fn-pacc-carried-row-held-l (h (fn-arena-count fn-arena)))
       (:instance fn-pacc-carried-row-alpha-l (h (fn-arena-count fn-arena)))
       (:instance fn-arena-seal-new-handle (xs (fn-record-payload w))))))))

(local
 (defthm fn-pacc-held-make-is-not-event-l
 (implies (natp sequence)
 (equal (fn-rcon-store-event-encode
 (fn-held-make sequence txid generation msgid payload groups oid subject evidence charge stamp facts context numbers withdrawn)) nil))
 :hints (("Goal" :in-theory (e/d
 (fn-rcon-store-event-encode fn-rcon-record-p-is-record-p fn-record-p fn-record-shapep
 fn-held-internals fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-stxa-p
 fn-stxe-internals fn-stxk-internals fn-stxa-internals fn-cpe-eventp fn-th-topic-eventp)
 (fn-store-retention-event-encode fn-stxe-encode fn-stxk-encode fn-stxa-encode fn-cpe-encode fn-th-topic-event-encode))))))

(local
 (defthm fn-pacc-carried-row-event-nil-l
 (implies (natp (fn-record-sequence w))
 (equal (fn-rcon-store-event-encode (fn-apc-intern-row-at w keyring generation h carry)) nil))
 :hints (("Goal" :in-theory (e/d (fn-apc-intern-row-at) (fn-apc-held-context-of fn-apc-held-facts-of))))))

(local
 (defthm fn-pacc-numeric-event-is-record-codec-l
 (implies (and (fn-record-shapep w) (natp (fn-record-sequence w)))
 (equal (fn-rcon-store-event-encode w) (fn-record-encode w)))
 :hints (("Goal" :in-theory (e/d
 (fn-rcon-store-event-encode fn-rcon-record-p-is-record-p fn-record-sequence fn-record-shapep fn-th-local-admin-eventp fn-th-at
 fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-stxa-p
 fn-stxe-internals fn-stxk-internals fn-stxa-internals fn-cpe-eventp fn-th-topic-eventp)
 (fn-record-p fn-store-retention-event-encode fn-stxe-encode fn-stxk-encode fn-stxa-encode fn-cpe-encode fn-th-topic-event-encode))))))

(local
 (defthm fn-pacc-carried-row-not-composite-l
 (not (fn-hstxa-p (fn-apc-intern-row-at w keyring generation h carry)))
 :hints (("Goal" :in-theory (e/d (fn-apc-intern-row-at fn-hstxa-p fn-held-internals)
 (fn-apc-held-facts-of fn-apc-held-context-of fn-stxa-p fn-held-p))))))

(local
 (defthm fn-pacc-encoded-intern-materializes-l
 (implies (and (fn-record-shapep w) (natp (fn-record-sequence w)) (natp generation))
  (equal (fn-rcon-store-event-encode (fn-row-wire-of
           (fn-apc-intern-row-at w keyring generation (fn-arena-count fn-arena) carry)
           (fn-arena-seal-list (fn-record-payload w) fn-arena))) (fn-record-encode w)))
 :hints (("Goal" :cases ((fn-record-p w)) :in-theory
 (e/d (fn-row-wire-of fn-row-bytes)
      (fn-apc-intern-row-at fn-held-p fn-held-wire fn-arena-payload-is-nth
       fn-arena-count-is-len fn-arena-seal-list-is-append fn-record-p fn-rcon-record-p
       fn-pacc-carried-row-alpha-l fn-arena-seal-new-handle))
 :use ((:instance fn-pacc-carried-row-alpha-l (h (fn-arena-count fn-arena)))
       (:instance fn-arena-seal-new-handle (xs (fn-record-payload w))))))))

(local
 (defthm fn-pacc-state-identity-next-l
 (implies (fn-sn-statep s) (natp (fn-sn-identity-next s)))
 :hints (("Goal" :in-theory '(fn-sn-statep)))))

(local
 (defthm fn-pacc-article-record-wire-shape-l
 (implies (fn-record-p (fn-sn-article-record s obs msgid payload groups oid subject evidence charge))
 (and (fn-record-shapep (fn-sn-article-record s obs msgid payload groups oid subject evidence charge))
 (equal (fn-record-sequence (fn-sn-article-record s obs msgid payload groups oid subject evidence charge))
 (fn-sn-identity-next s))))
 :hints (("Goal" :in-theory (enable fn-sn-article-record)))))

(local
 (defthm fn-pacc-refusal-intern-l
 (implies (atom refusal)
 (equal (fn-rcon-store-event-encode
 (fn-row-wire-of (fn-apc-intern-row-at refusal keyring generation h carry) arena)) nil))
 :hints (("Goal" :in-theory (e/d
 (fn-rcon-store-event-encode fn-apc-intern-row-at fn-row-wire-of fn-record-internals
 fn-held-internals fn-held-p fn-hstxa-p fn-rcon-record-p-is-record-p fn-record-p
 fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-stxa-p fn-stxe-internals fn-stxk-internals fn-stxa-internals fn-cpe-eventp fn-th-topic-eventp)
 (fn-store-retention-event-encode fn-stxe-encode fn-stxk-encode fn-stxa-encode fn-cpe-encode fn-th-topic-event-encode))))))

(local
 (defthm fn-pacc-clock-unusable-intern-l
 (equal (fn-rcon-store-event-encode
 (fn-row-wire-of (fn-apc-intern-row-at :clock-unusable keyring generation h carry) arena)) nil)
 :hints (("Goal" :in-theory (e/d
 (fn-rcon-store-event-encode fn-apc-intern-row-at fn-row-wire-of fn-record-internals
 fn-held-internals fn-held-p fn-hstxa-p fn-rcon-record-p-is-record-p fn-record-p
 fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-stxa-p fn-stxe-internals fn-stxk-internals fn-stxa-internals fn-cpe-eventp fn-th-topic-eventp)
 (fn-store-retention-event-encode fn-stxe-encode fn-stxk-encode fn-stxa-encode fn-cpe-encode fn-th-topic-event-encode))))))

; MOD4: local suffix lemmas preserve the approved keystone formulas.
(local (defthm fn-pacc-mod-append-suffix-l
 (fn-inj-suffixp tail (append pre tail))
 :hints (("Goal" :induct (append pre tail) :in-theory
          (union-theories (theory 'ground-zero) '(append fn-inj-suffixp))))))

(local (defthm fn-pacc-mod-suffix-transitive-l
 (implies (and (fn-inj-suffixp a b) (fn-inj-suffixp b c)) (fn-inj-suffixp a c))
 :hints (("Goal" :induct (fn-inj-suffixp b c) :in-theory
          (union-theories (theory 'ground-zero) '(fn-inj-suffixp))))
 :rule-classes nil))

(local (defthm fn-pacc-mod-forwarded-source-suffix-l
 (fn-inj-suffixp source (fn-mod-forwarded-source source facts msgid date))
 :hints (("Goal" :use ((:instance fn-pacc-mod-suffix-transitive-l (a source)
 (b (fn-inj-append (if (fn-inj-car (fn-inj-cdr (fn-inj-cdr facts))) (fn-inj-date-line date) nil) source))
 (c (fn-mod-forwarded-source source facts msgid date))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-mod-forwarded-source fn-inj-suffixp fn-pacc-a0-inj-append-is-append
   fn-pacc-mod-append-suffix-l fn-pacc-a0-append-assoc))))))

(local (defthm fn-pacc-mod-car-append-l
 (equal (car (append a b)) (if (consp a) (car a) (car b)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(append))))))

(local (defthm fn-pacc-mod-cdr-append-l
 (equal (cdr (append a b)) (if (consp a) (append (cdr a) b) (cdr b)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(append))))))

(local (defthm fn-pacc-mod-append-nil-l
 (equal (append a nil) (true-list-fix a))
 :hints (("Goal" :induct (true-list-fix a) :in-theory
 (union-theories (theory 'ground-zero) '(append true-list-fix))))))

(local (defthm fn-pacc-mod-suffix-self-l
 (fn-inj-suffixp a a)
 :hints (("Goal" :expand ((fn-inj-suffixp a a))))))

(local (defthm fn-pacc-mod-append-keeps-suffix-l
 (implies (fn-inj-suffixp tail b) (fn-inj-suffixp tail (append a b)))
 :hints (("Goal" :induct (append a b) :in-theory
 (union-theories (theory 'ground-zero) '(append fn-inj-suffixp))))))

(local (defthm fn-pacc-mod-len-positive-l
 (implies (consp x) (< 0 (len x)))
 :hints (("Goal" :expand ((len x)))) :rule-classes :linear))

(local (defthm fn-pacc-mod-path-open-before-separator-l
 (implies (fn-inj-path-openp (append pre '(13 10 13 10) tail))
          (<= 6 (len pre)))
 :hints (("Goal" :do-not-induct t :expand ((:free (x) (fn-inj-take-n 1 x)) (:free (x) (fn-inj-take-n 2 x)) (:free (x) (fn-inj-take-n 3 x)) (:free (x) (fn-inj-take-n 4 x)) (:free (x) (fn-inj-take-n 5 x)) (:free (x) (fn-inj-take-n 6 x))) :in-theory (union-theories (theory 'ground-zero)
 '(fn-inj-path-openp fn-inj-take-n fn-inj-downcase nth len append fn-pacc-mod-len-positive-l fn-pacc-mod-car-append-l fn-pacc-mod-cdr-append-l))
 :cases ((not (consp pre)) (not (consp (cdr pre))) (not (consp (cddr pre)))
         (not (consp (cdddr pre))) (not (consp (cddddr pre))) (not (consp (cdr (cddddr pre)))))))))

(local (defthm fn-pacc-mod-envelope-source-suffix-l
 (implies (true-listp forwarded)
  (fn-inj-suffixp forwarded (fn-mod-envelope-source agent group queue msgid forwarded)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-mod-envelope-source fn-mod-concat fn-pacc-a0-inj-append-is-append
   fn-pacc-a0-append-assoc fn-pacc-mod-append-suffix-l fn-pacc-fix-true-list-l
   fn-pacc-fix-append-l fn-pacc-mod-append-keeps-suffix-l fn-pacc-mod-suffix-self-l fn-pacc-mod-append-nil-l fn-inj-suffixp append))))))

(local (defthm fn-pacc-mod-take-append-l
 (implies (and (natp k) (<= k (len pre)))
  (equal (fn-inj-take-n k (append pre tail)) (fn-inj-take-n k pre)))
 :hints (("Goal" :induct (fn-inj-take-n k pre) :in-theory
 (union-theories (theory 'ground-zero) '(fn-inj-take-n len append))))))

(local (defthm fn-pacc-mod-drop-append-l
 (implies (and (natp k) (<= k (len pre)))
  (equal (fn-inj-drop-n k (append pre tail)) (append (fn-inj-drop-n k pre) tail)))
 :hints (("Goal" :induct (fn-inj-drop-n k pre) :in-theory
 (union-theories (theory 'ground-zero) '(fn-inj-drop-n len append))))))

(local (defthm fn-pacc-mod-splice-append-l
 (implies (and (natp k) (<= k (len pre)))
  (equal (fn-inj-splice (append pre tail) k ins)
         (append (fn-inj-splice pre k ins) tail)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-inj-splice fn-pacc-mod-take-append-l fn-pacc-mod-drop-append-l
   fn-pacc-a0-append-assoc))))))

(local (defthm fn-pacc-mod-suffix-layout-l
 (implies (and (true-listp tail) (fn-inj-suffixp tail stored))
  (and (<= (len tail) (len stored))
       (equal (append (fn-inj-take-n (nfix (- (len stored) (len tail))) stored) tail)
              stored)))
 :hints (("Goal" :induct (fn-inj-suffixp tail stored) :in-theory
 (union-theories (theory 'ground-zero)
 '(fn-inj-suffixp fn-inj-take-n len append true-listp))))))

(local (defun fn-pacc-mod-scan-induct (pre bol)
 (declare (xargs :guard t :measure (acl2-count pre)) (ignore bol))
 (cond ((atom pre) nil)
       ((and (equal (car pre) 13) (consp (cdr pre)) (equal (cadr pre) 10))
        (fn-pacc-mod-scan-induct (cddr pre) t))
       (t (fn-pacc-mod-scan-induct (cdr pre) nil)))))

(local (defthm fn-pacc-mod-append-true-list-l
 (implies (true-listp b) (true-listp (append a b)))
 :hints (("Goal" :induct (append a b) :in-theory
 (union-theories (theory 'ground-zero) '(append true-listp))))))

(local (defthm fn-pacc-mod-forwarded-true-list-l
 (implies (true-listp source)
          (true-listp (fn-mod-forwarded-source source facts msgid date)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-mod-forwarded-source fn-pacc-a0-inj-append-is-append fn-pacc-mod-append-true-list-l))))))

(local (defun fn-pacc-mod-envelope-prefix (agent group queue msgid)
 (declare (xargs :guard t))
 (fn-mod-concat (list *fn-mod-from* agent *fn-inj-crlf*
                     *fn-mod-subject* group *fn-inj-crlf*
                     *fn-mod-newsgroups* queue *fn-inj-crlf*
                     (fn-inj-message-id-line (fn-mod-envelope-msgid msgid))
                     *fn-mod-content-type*))))

(local (defthm fn-pacc-mod-envelope-by-definition-l
 (implies (true-listp forwarded)
  (equal (fn-mod-envelope-source agent group queue msgid forwarded)
         (append (fn-pacc-mod-envelope-prefix agent group queue msgid)
                 '(13 10 13 10) forwarded)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-mod-envelope-source fn-pacc-mod-envelope-prefix fn-mod-concat
   fn-pacc-a0-inj-append-is-append fn-pacc-a0-append-assoc
   fn-pacc-mod-append-nil-l fn-pacc-fix-true-list-l fn-pacc-fix-append-l))))))

(local (defthm fn-pacc-mod-scan-before-separator-l
 (let ((k (fn-inj-path-scan (append pre '(13 10 13 10) tail) bol)))
  (implies k (and (natp k) (<= k (+ 4 (len pre))))))
 :hints (("Goal" :induct (fn-pacc-mod-scan-induct pre bol)
 :in-theory (union-theories (set-difference-theories (theory 'ground-zero) '(binary-append fn-inj-path-openp))
 '(fn-pacc-mod-scan-induct fn-inj-path-scan fn-pacc-mod-path-open-before-separator-l
   len fn-pacc-mod-car-append-l fn-pacc-mod-cdr-append-l fn-pacc-mod-len-positive-l))
 :expand ((fn-inj-path-scan (append pre '(13 10 13 10) tail) bol) (fn-inj-path-openp (list* 13 10 13 10 tail))
          (fn-inj-path-openp (list* (car pre) 13 10 13 10 tail))))
 ("Subgoal *1/1" :in-theory (union-theories (theory 'ground-zero)
 '(fn-inj-path-scan fn-inj-path-openp fn-inj-take-n fn-inj-downcase nth append len)))
 ("Subgoal *1/3" :use ((:instance fn-pacc-mod-path-open-before-separator-l)))
 ("Subgoal *1/2" :use ((:instance fn-pacc-mod-path-open-before-separator-l)))
 )))

(local (defthm fn-pacc-mod-len-append-l
 (equal (len (append a b)) (+ (len a) (len b)))
 :hints (("Goal" :induct (append a b) :in-theory
 (union-theories (theory 'ground-zero) '(append len))))))

(local (defthm fn-pacc-mod-separated-splice-suffix-l
 (implies (and (natp k) (<= k (+ 4 (len pre))))
  (fn-inj-suffixp tail (fn-inj-splice (append pre '(13 10 13 10) tail) k ins)))
 :hints (("Goal" :use ((:instance fn-pacc-mod-splice-append-l (pre (append pre '(13 10 13 10)))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-pacc-mod-len-append-l fn-pacc-a0-append-assoc fn-pacc-mod-append-suffix-l))))))

(local (defthm fn-pacc-mod-separated-splice-normalized-l
 (implies (and (natp k) (<= k (+ 4 (len pre))))
  (fn-inj-suffixp tail (fn-inj-splice (append pre (list* 13 10 13 10 tail)) k ins)))
 :hints (("Goal" :use ((:instance fn-pacc-mod-separated-splice-suffix-l))
 :in-theory (union-theories (theory 'ground-zero) '(append))))))

(local (defthm fn-pacc-mod-ipp-separator-suffix-l
 (let* ((source (append pre '(13 10 13 10) tail))
        (d (fn-inj-decide source config obs)))
  (implies (fn-inj-injectedp d)
           (fn-inj-suffixp tail (fn-ipp-injected-octets d secret login cfg))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-ipp-injected-octets-carry-the-parameters
                  (source (append pre '(13 10 13 10) tail)))
       (:instance fn-inj-an-injected-supplied-path-has-an-offset
                  (source (append pre '(13 10 13 10) tail)))
       (:instance fn-pacc-mod-scan-before-separator-l (bol t)))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-ipp-injected-octets-carry-the-parameters fn-inj-suffixp fn-pacc-mod-suffix-self-l fn-inj-path-offset fn-pacc-mod-append-keeps-suffix-l fn-pacc-mod-append-suffix-l
   fn-pacc-mod-splice-append-l fn-pacc-mod-separated-splice-suffix-l fn-pacc-mod-separated-splice-normalized-l fn-pacc-a0-append-assoc len
   fn-inj-take-n fn-inj-drop-n))))))

(local (defthm fn-pacc-mod-cl-suffix-l
 (implies (fn-inj-suffixp tail payload)
          (fn-inj-suffixp tail (fn-apc-cl-served-payload ring account msgid payload carry)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-apc-cl-served-payload fn-cll-append-is-append fn-pacc-mod-append-keeps-suffix-l))))))

(local (defthm fn-pacc-mod-ipp-envelope-suffix-l
 (let* ((envelope (fn-mod-envelope-source agent group queue msgid forwarded))
        (d (fn-inj-decide envelope config obs)))
  (implies (and (true-listp forwarded) (fn-inj-injectedp d))
           (fn-inj-suffixp forwarded (fn-ipp-injected-octets d secret login cfg))))
 :hints (("Goal" :use ((:instance fn-pacc-mod-ipp-separator-suffix-l
                      (pre (fn-pacc-mod-envelope-prefix agent group queue msgid)) (tail forwarded)))
 :in-theory (union-theories (theory 'ground-zero) '(fn-pacc-mod-envelope-by-definition-l))))))

(local (defthm fn-pacc-mod-forward-ipp-suffix-l
 (implies (and (true-listp source)
               (fn-inj-injectedp (fn-mod-forward source config obs decision facts entry)))
  (fn-inj-suffixp source
   (fn-ipp-injected-octets (fn-mod-forward source config obs decision facts entry) secret login cfg)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-pacc-mod-ipp-envelope-suffix-l
        (agent (fn-inj-config-agent config)) (group (fn-mod-entry-group entry))
        (queue (fn-mod-entry-queue entry)) (msgid (fn-inj-decision-msgid decision))
        (forwarded (fn-mod-forwarded-source source facts (fn-inj-decision-msgid decision)
                     (fn-inj-date-octets (fn-inj-instant-of (fn-clock-wall obs))))))
       (:instance fn-pacc-mod-suffix-transitive-l (a source)
        (b (fn-mod-forwarded-source source facts (fn-inj-decision-msgid decision)
             (fn-inj-date-octets (fn-inj-instant-of (fn-clock-wall obs)))))
        (c (fn-ipp-injected-octets
            (fn-inj-decide
             (fn-mod-envelope-source (fn-inj-config-agent config)
              (fn-mod-entry-group entry) (fn-mod-entry-queue entry)
              (fn-inj-decision-msgid decision)
              (fn-mod-forwarded-source source facts (fn-inj-decision-msgid decision)
               (fn-inj-date-octets (fn-inj-instant-of (fn-clock-wall obs))))) config obs)
            secret login cfg))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-mod-forward fn-inj-refuse fn-inj-injectedp fn-inj-decision-status-of-fn-inj-make-decision
   fn-pacc-mod-forwarded-true-list-l fn-pacc-mod-forwarded-source-suffix-l))))))

(local (defthm fn-pacc-mod-gate-ipp-suffix-l
 (implies (and (true-listp source)
               (not (equal (fn-mod-gate source config obs decision) decision))
               (fn-inj-injectedp (fn-mod-gate source config obs decision)))
  (fn-inj-suffixp source
   (fn-ipp-injected-octets (fn-mod-gate source config obs decision) secret login cfg)))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-mod-gate fn-inj-refuse fn-inj-injectedp fn-inj-decision-status-of-fn-inj-make-decision
   fn-pacc-mod-forward-ipp-suffix-l))))))

(local (defthm fn-pacc-mod-post-gate-ipp-suffix-l
 (implies (and (true-listp source)
               (not (equal (fn-post-gated-decision source config obs) (fn-inj-decide source config obs)))
               (fn-inj-injectedp (fn-post-gated-decision source config obs)))
  (fn-inj-suffixp source
   (fn-ipp-injected-octets (fn-post-gated-decision source config obs) secret login cfg)))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-post-gated-decision fn-inj-refuse fn-inj-injectedp fn-inj-decision-status-of-fn-inj-make-decision
   fn-pacc-mod-gate-ipp-suffix-l))))))

(local (defthm fn-pacc-mod-stored-suffix-l
 (implies (and (fn-pacc-injectionp inj art)
               (not (equal (fn-pctx-get 0 inj)
                      (fn-inj-decide art (fn-pctx-get 5 inj) (fn-pctx-get 6 inj)))))
          (fn-inj-suffixp art (fn-pacc-stored-payload art inj)))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-pacc-injection-requires-octets-l))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-pacc-injectionp fn-pacc-stored-payload fn-pacc-mod-cl-suffix-l
   fn-pacc-mod-post-gate-ipp-suffix-l fn-pacc-octets-true-listp-l))))))

(defthm fn-pacc-stored-payload-is-one-splice
  (implies (fn-pacc-injectionp inj art)
           (mv-let (p0 ins ioff) (fn-pacc-splice art inj)
             (and (natp ioff) (<= ioff (len art))
                  (equal (fn-pacc-stored-payload art inj)
                         (append p0 (take ioff art) ins (nthcdr ioff art))))))
 :hints (("Goal" :do-not-induct t
 :cases ((equal (fn-pctx-get 0 inj) (fn-inj-decide art (fn-pctx-get 5 inj) (fn-pctx-get 6 inj))))
 :use ((:instance fn-pacc-mod-stored-suffix-l)
       (:instance fn-pacc-mod-suffix-layout-l (tail art) (stored (fn-pacc-stored-payload art inj)))
       (:instance fn-pacc-injection-requires-octets-l)
       (:instance fn-ipp-injected-octets-carry-the-parameters
       (source art) (config (fn-pctx-get 5 inj)) (obs (fn-pctx-get 6 inj))
       (secret (fn-pctx-get 1 inj)) (login (fn-pctx-get 2 inj)) (cfg (fn-pctx-get 3 inj)))
       (:instance fn-pacc-gated-injection-decision-l)
       (:instance fn-pacc-success-parse-l (config (fn-pctx-get 5 inj)) (obs (fn-pctx-get 6 inj)))
       (:instance fn-inj-an-injected-supplied-path-has-an-offset
        (source art) (config (fn-pctx-get 5 inj)) (obs (fn-pctx-get 6 inj)))
       (:instance fn-pacc-path-bounds-l (x art) (bol t)))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-pacc-splice fn-pacc-stored-payload fn-apc-cl-served-payload
   fn-inj-supplies-pathp fn-inj-path-offset fn-inj-splice
   fn-pacc-parsed-candidate-l fn-pacc-cat-is-append-l
   fn-pacc-standalone-block-l fn-pacc-standalone-prefix-l fn-pacc-take-n-is-take-l fn-pacc-drop-n-is-nthcdr-l
   fn-pacc-octets-true-listp-l fn-cll-append-is-append fn-pacc-a0-inj-append-is-append
   fn-pacc-a0-a-configured-agent-is-a-line-free-list fn-pacc-a0-date-octets-shape
   fn-inj-path-insert fn-pacc-fix-true-list-l fn-pacc-fix-append-l fn-pacc-a0-append-assoc)))))


(defthm fn-pacc-batch-record-is-the-encoded-record
  (let ((rec (fn-sn-article-record s obs msgid (fn-pacc-stored-payload art inj) groups oid subject evidence charge)))
    (implies (fn-sn-statep s)
             (equal (fn-pacc-batch-record-octets s obs art inj (list msgid groups oid subject evidence charge) fn-arena)
                    (fn-record-encode rec))))
  :hints (("Goal" :in-theory
    (union-theories (theory 'ground-zero)
      '(fn-pacc-batch-record-octets fn-pctx-get nfix zp
        fn-rcon-record-p-is-record-p fn-pacc-encoded-intern-materializes-l fn-pacc-state-identity-next-l fn-pacc-article-record-wire-shape-l fn-pacc-refusal-intern-l fn-pacc-clock-unusable-intern-l fn-record-encode-domain fn-sn-article-record fn-record-shapep fn-record-sequence fn-record-make (:executable-counterpart fn-record-p)
        fn-pacc-state-generation-l fn-pacc-injection-carry-l)))))


; A1: constructor/payload and seam composition; resource lemmas follow.
(local (defthm fn-pacc-constructor-payload-l
 (implies (fn-record-p (fn-sn-article-record s obs msgid payload groups oid subject evidence charge))
  (equal (fn-record-payload (fn-sn-article-record s obs msgid payload groups oid subject evidence charge)) payload))
 :hints (("Goal" :in-theory (enable fn-sn-article-record fn-record-payload fn-record-make fn-record-p fn-record-shapep)))))
(local
 (defthm fn-pacc-prepared-payload-l
  (implies (fn-record-p (fn-pacc-prepared-record s obs art inj))
           (equal (fn-record-payload (fn-pacc-prepared-record s obs art inj))
                  (fn-pacc-stored-payload art inj)))
  :hints (("Goal" :in-theory (e/d (fn-pacc-prepared-record)
    (fn-sn-article-record fn-pacc-derived-fields fn-pacc-stored-payload fn-pctx-get fn-record-p))
    :use ((:instance fn-pacc-constructor-payload-l
      (msgid (fn-pctx-get 0 (fn-pacc-derived-fields s art inj)))
      (payload (fn-pacc-stored-payload art inj))
      (groups (fn-pctx-get 1 (fn-pacc-derived-fields s art inj)))
      (oid (fn-pctx-get 2 (fn-pacc-derived-fields s art inj)))
      (subject (fn-pctx-get 3 (fn-pacc-derived-fields s art inj)))
      (evidence (fn-pctx-get 4 (fn-pacc-derived-fields s art inj)))
      (charge (fn-pctx-get 5 (fn-pacc-derived-fields s art inj)))))))))
(local
 (defthm fn-pacc-prepared-layout-l
  (let* ((rec (fn-pacc-prepared-record s obs art inj))
         (ctx (fn-pctx-of-prepared s rec art inj))
         (gsec (fn-pacc-prepared-gsec rec)))
   (implies (and (fn-record-p rec) (fn-pacc-injectionp inj art))
     (equal (append (nth 1 ctx) (take (nth 3 ctx) art) (nth 2 ctx)
                    (nthcdr (nth 3 ctx) art) (nth 4 ctx) gsec (nth 5 ctx))
            (fn-record-encode rec))))
  :hints (("Goal" :in-theory
    (e/d (fn-pctx-of-prepared fn-pacc-prepared-gsec fn-pacc-a0-append-assoc)
         (fn-pacc-splice fn-pacc-stored-payload fn-pacc-prepared-record
          fn-pacc-injectionp fn-record-p))
    :use ((:instance fn-record-encode-splits-at-the-payload
             (record (fn-pacc-prepared-record s obs art inj)))
          fn-pacc-stored-payload-is-one-splice)))))

; A1 context/profile proof support (local: not packet statements).
(local (defthm fn-pacc-constructor-groups-l
 (implies (fn-record-p (fn-sn-article-record s obs msgid payload groups oid subject evidence charge))
  (and (equal (fn-record-groups (fn-sn-article-record s obs msgid payload groups oid subject evidence charge)) groups)
       (fn-record-uint64p (fn-state-next-txid (fn-node-acceptance (fn-sn-node s))))))
 :hints (("Goal" :in-theory (enable fn-sn-article-record fn-record-groups fn-record-make fn-record-p fn-record-shapep)))))

(local (defun fn-pacc-injection-source-l (source config obs)
 (declare (xargs :guard t))
 (let* ((decision (fn-inj-decide source config obs))
        (facts (fn-mod-facts source config))
        (entries (and facts (fn-mod-named-entries (fn-inj-decision-groups decision)
                                      (fn-inj-config-closed config)))))
   (if (or (atom entries) (fn-mod-facts-approvedp facts)) source
     (fn-mod-envelope-source
       (fn-inj-config-agent config) (fn-mod-entry-group (car entries))
       (fn-mod-entry-queue (car entries)) (fn-inj-decision-msgid decision)
       (fn-mod-forwarded-source source facts (fn-inj-decision-msgid decision)
          (fn-inj-date-octets (fn-inj-instant-of (fn-clock-wall obs)))))))))

(local (defthm fn-pacc-gate-is-injection-of-source-l
 (implies (fn-inj-injectedp (fn-post-gated-decision source config obs))
  (equal (fn-post-gated-decision source config obs)
         (fn-inj-decide (fn-pacc-injection-source-l source config obs) config obs)))
 :rule-classes nil
 :hints (("Goal" :in-theory
   (e/d (fn-post-gated-decision fn-mod-gate fn-mod-forward
         fn-mod-facts-approvedp fn-pacc-injection-source-l)
        (fn-inj-decide fn-mod-facts fn-mod-named-entries fn-mod-envelope-source
         fn-mod-forwarded-source fn-inj-injectedp fn-gst-post-gate))))))

(local (defthm fn-pacc-injection-census-l
 (implies (fn-inj-injectedp (fn-inj-decide source config obs))
  (and (fn-article-result-okp (fn-article-parse source))
       (not (fn-article-census-refusal (fn-article-header-census source)
                                      (fn-inj-config-header-limits config)))))
 :hints (("Goal" :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-inj-decide fn-inj-injectedp fn-inj-refuse
     fn-inj-decision-status-of-fn-inj-make-decision))))))

(local (defthm fn-pacc-injection-source-admitted-l
 (implies (fn-inj-injectedp (fn-inj-decide source config obs))
  (fn-article-result-okp
    (fn-article-parse-under source (fn-inj-config-header-limits config))))
 :hints (("Goal" :in-theory (theory 'minimal-theory)
  :use (fn-pacc-injection-census-l
        (:instance fn-article-census-refusal-is-the-parse
         (octets source) (limits (fn-inj-config-header-limits config))))))))

(local (defthm fn-pacc-injection-groups-are-source-groups-l
 (implies (fn-inj-injectedp (fn-inj-decide source config obs))
  (equal (fn-inj-decision-groups (fn-inj-decide source config obs))
         (fn-o1-source-newsgroups source)))
 :hints (("Goal" :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-inj-decide fn-inj-injectedp fn-inj-refuse fn-inj-proto-reason
     fn-inj-car fn-inj-cdr fn-inj-nth nfix zp car-cons cdr-cons fn-af-proto-article-check
     fn-af-relayed-article-check fn-af-status-kind fn-af-status-value
     fn-af-status-field fn-af-newsgroups-status fn-o1-source-newsgroups
     fn-inj-decision-status-of-fn-inj-make-decision
     fn-inj-decision-groups-of-fn-inj-make-decision))))))

(local
 (defthm o1s-next-line-aux-of-a-line
  (implies (and (fn-ipp-no-crlfp a) (true-listp a) (natp left) (true-listp acc))
           (equal (fn-article-next-line-aux (append a (list* 13 10 r)) acc left)
                  (if (<= (len a) left)
                      (list :ok (append (reverse acc) a) r)
                    (list :error :limit))))
  :hints (("Goal" :induct (fn-article-next-line-aux a acc left)
           :in-theory (enable fn-article-next-line-aux fn-ipp-no-crlfp)))))

(local
 (defthm o1s-next-line-of-a-line
  (implies (and (fn-ipp-no-crlfp a) (true-listp a))
           (equal (fn-article-next-line (append a (list* 13 10 r)))
                  (if (<= (len a) 998)
                      (list :ok a r)
                    (list :error :limit))))
  :hints (("Goal" :in-theory (e/d (fn-article-next-line) (o1s-next-line-aux-of-a-line))
           :use ((:instance o1s-next-line-aux-of-a-line (acc nil) (left *fn-article-max-line-octets*)))))))

(local
 (encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm o1s-big-hi2 (<= 48 (fn-inj-hi2 n)) :rule-classes :linear :hints (("Goal" :in-theory (enable fn-inj-hi2))))
  (defthm o1s-big-lo2 (<= 48 (fn-inj-lo2 n)) :rule-classes :linear :hints (("Goal" :in-theory (enable fn-inj-lo2))))
  (defthm o1s-big-r1 (<= 0 (fn-inj-r1 n)) :rule-classes :linear :hints (("Goal" :in-theory (enable fn-inj-r1))))
  (defthm o1s-big-r2 (<= 0 (fn-inj-r2 n)) :rule-classes :linear :hints (("Goal" :in-theory (enable fn-inj-r2 fn-inj-r1))))
  (defthm o1s-big-yth (<= 48 (fn-inj-y-th n)) :rule-classes :linear :hints (("Goal" :in-theory (enable fn-inj-y-th))))
  (defthm o1s-big-yhu (<= 48 (fn-inj-y-hu n)) :rule-classes :linear :hints (("Goal" :in-theory (enable fn-inj-y-hu))))
  (defthm o1s-big-yte (<= 48 (fn-inj-y-te n)) :rule-classes :linear :hints (("Goal" :in-theory (enable fn-inj-y-te))))
  (defthm o1s-big-yun (<= 48 (fn-inj-y-un n)) :rule-classes :linear :hints (("Goal" :in-theory (enable fn-inj-y-un))))))

(local (defthm o1s-big-d1 (<= 63 (fn-inj-dow-c1 n)) :rule-classes :linear :hints (("Goal" :in-theory (enable fn-inj-dow-c1)))))

(local (defthm o1s-big-d2 (<= 63 (fn-inj-dow-c2 n)) :rule-classes :linear :hints (("Goal" :in-theory (enable fn-inj-dow-c2)))))

(local (defthm o1s-big-d3 (<= 63 (fn-inj-dow-c3 n)) :rule-classes :linear :hints (("Goal" :in-theory (enable fn-inj-dow-c3)))))

(local (defthm o1s-big-m1 (<= 63 (fn-inj-month-c1 n)) :rule-classes :linear :hints (("Goal" :in-theory (enable fn-inj-month-c1)))))

(local (defthm o1s-big-m2 (<= 63 (fn-inj-month-c2 n)) :rule-classes :linear :hints (("Goal" :in-theory (enable fn-inj-month-c2)))))

(local (defthm o1s-big-m3 (<= 63 (fn-inj-month-c3 n)) :rule-classes :linear :hints (("Goal" :in-theory (enable fn-inj-month-c3)))))

(local
 (defthm o1s-date-no-crlf
  (fn-ipp-no-crlfp (fn-inj-date-octets inst))
  :hints (("Goal" :in-theory (e/d (fn-inj-date-octets fn-ipp-no-crlfp)
                                  (fn-inj-hi2 fn-inj-lo2 fn-inj-y-th fn-inj-y-hu fn-inj-y-te fn-inj-y-un
                                   fn-inj-dow-c1 fn-inj-dow-c2 fn-inj-dow-c3 fn-inj-month-c1 fn-inj-month-c2
                                   fn-inj-month-c3 fn-inj-instant-year fn-inj-instant-month fn-inj-instant-day
                                   fn-inj-instant-hour fn-inj-instant-minute fn-inj-instant-second fn-inj-instant-dow))))))

(local
 (defthm o1s-dot-atom-no-crlf
  (implies (and (true-listp bytes) (fn-af-dot-atom-text-aux bytes want-atext))
           (fn-ipp-no-crlfp bytes))
  :hints (("Goal" :induct (fn-af-dot-atom-text-aux bytes want-atext)
           :in-theory (enable fn-af-dot-atom-text-aux fn-af-atextp fn-ipp-no-crlfp)))))

(local
 (defthm o1s-config-agent-facts
  (implies (fn-inj-configp config)
           (and (fn-ipp-no-crlfp (fn-inj-config-agent config))
                (consp (fn-inj-config-agent config))
                (true-listp (fn-inj-config-agent config))))
  :hints (("Goal" :in-theory (e/d (fn-inj-configp fn-af-dot-atom-textp)
                                  (fn-af-dot-atom-text-aux fn-inj-config-agent))
           :use ((:instance o1s-dot-atom-no-crlf
                            (bytes (fn-inj-config-agent config)) (want-atext t))
                 (:instance fn-article-octet-list-true-listp
                            (octets (fn-inj-config-agent config))))))))

(local
 (encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm o1s-digits-rev-facts
    (and (fn-ipp-no-crlfp (fn-inj-digits-rev n w))
         (true-listp (fn-inj-digits-rev n w))
         (equal (len (fn-inj-digits-rev n w)) (nfix w)))
    :hints (("Goal" :in-theory (enable fn-inj-digits-rev fn-ipp-no-crlfp))))))

(local
 (defthm o1s-rev-append-facts
  (implies (and (fn-ipp-no-crlfp xs) (fn-ipp-no-crlfp acc) (true-listp acc))
           (and (fn-ipp-no-crlfp (fn-inj-rev-append xs acc))
                (true-listp (fn-inj-rev-append xs acc))
                (equal (len (fn-inj-rev-append xs acc)) (+ (len xs) (len acc)))))
  :hints (("Goal" :in-theory (enable fn-inj-rev-append fn-ipp-no-crlfp)))))

(local
 (defthm o1s-digits-facts
    (and (fn-ipp-no-crlfp (fn-inj-digits n w))
         (true-listp (fn-inj-digits n w))
         (equal (len (fn-inj-digits n w)) (nfix w)))
    :hints (("Goal" :in-theory (e/d (fn-inj-digits fn-ipp-no-crlfp) (o1s-rev-append-facts o1s-digits-rev-facts))
             :use ((:instance o1s-rev-append-facts (xs (fn-inj-digits-rev n w)) (acc nil))
                   (:instance o1s-digits-rev-facts))))))

(local
 (defun o1s-linesp (ls)
  (declare (xargs :verify-guards nil))
  (if (consp ls)
      (and (true-listp (car ls)) (consp (car ls)) (fn-ipp-no-crlfp (car ls))
           (o1s-linesp (cdr ls)))
    (null ls))))

(local
 (defun o1s-octets (ls)
  (declare (xargs :verify-guards nil))
  (if (consp ls)
      (append (car ls) (list* 13 10 (o1s-octets (cdr ls))))
    nil)))

(local
 (defun o1s-cost (ls)
  (declare (xargs :verify-guards nil))
  (if (consp ls)
      (+ (if (< 1000 (+ 2 (len (car ls)))) 1000 (+ 2 (len (car ls))))
         (o1s-cost (cdr ls)))
    0)))

(local
 (defthm o1s-inj-append
  (equal (fn-inj-append a b) (append a b))
  :hints (("Goal" :in-theory (enable fn-inj-append)))))

(local
 (defun o1s-block-ls (date msgid agent gid gdate params)
  (declare (xargs :verify-guards nil))
  (append (if (or gid gdate) (list (append *fn-inj-injection-date-field* date)) nil)
   (append (if gid (list (append *fn-inj-message-id-field* msgid)) nil)
    (append (if gdate (list (append *fn-inj-date-field* date)) nil)
            (list (append *fn-inj-injection-info-field* (append agent params))))))))

(local
 (defthm o1s-block-with-is-lines
  (equal (fn-ipp-block-with date msgid agent gid gdate params)
         (o1s-octets (o1s-block-ls date msgid agent gid gdate params)))
  :hints (("Goal" :in-theory (enable fn-ipp-block-with fn-inj-injection-date-line fn-inj-message-id-line
                                     fn-inj-date-line fn-inj-injection-info-line-with
                                     o1s-block-ls o1s-octets o1s-inj-append)))))

(local
 (defthm o1s-no-crlf-append
  (equal (fn-ipp-no-crlfp (append a b))
         (and (fn-ipp-no-crlfp a) (fn-ipp-no-crlfp b)))
  :hints (("Goal" :in-theory (enable fn-ipp-no-crlfp)))))

(local
 (defthm o1s-no-crlf-cons
  (equal (fn-ipp-no-crlfp (cons x y))
         (and (not (equal x 13)) (not (equal x 10)) (fn-ipp-no-crlfp y)))
  :hints (("Goal" :in-theory (enable fn-ipp-no-crlfp)))))

(local
 (defthm o1s-block-facts
  (implies (and (true-listp date) (fn-ipp-no-crlfp date) (equal (len date) 31)
                (implies gid (and (true-listp msgid) (fn-ipp-no-crlfp msgid)
                                  (equal (len msgid) (+ 47 (len agent)))))
                (true-listp agent) (fn-ipp-no-crlfp agent)
                (true-listp params) (fn-ipp-no-crlfp params))
           (and (o1s-linesp (o1s-block-ls date msgid agent gid gdate params))
                (<= (len (o1s-block-ls date msgid agent gid gdate params)) 4)
                (<= (o1s-cost (o1s-block-ls date msgid agent gid gdate params))
                    (+ 1149 (len agent)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (o1s-block-ls o1s-linesp o1s-cost) (fn-ipp-no-crlfp))))))

(local
 (defthm o1s-prefix-with-is-lines
  (equal (fn-ipp-prefix-with date msgid agent gid gdate params)
         (o1s-octets (cons (append *fn-inj-path-field* (append agent *fn-inj-path-tail*))
                           (o1s-block-ls date msgid agent gid gdate params))))
  :hints (("Goal" :in-theory (enable fn-ipp-prefix-with fn-inj-path-line o1s-octets o1s-inj-append
                                     o1s-block-with-is-lines)))))

(local
 (defthm o1s-valuep-facts
  (implies (fn-cll-valuep v)
           (and (fn-ipp-no-crlfp v) (true-listp v)))
  :hints (("Goal" :in-theory (enable fn-cll-valuep fn-cll-b64-charp fn-ipp-no-crlfp)))))

(local
 (defthm o1s-key-values-facts
  (implies (fn-cll-values-p keys)
           (and (fn-ipp-no-crlfp (fn-cll-key-values keys))
                (true-listp (fn-cll-key-values keys))))
  :hints (("Goal" :in-theory (enable fn-cll-values-p fn-cll-key-values fn-cll-append-is-append)
           :induct (fn-cll-values-p keys)))))

(local
 (defun o1s-cl-ls (lock keys)
  (declare (xargs :verify-guards nil))
  (append (if lock (list (append *fn-cll-lock-head* lock)) nil)
          (if (consp keys) (list (append *fn-cll-key-field* (fn-cll-key-values keys))) nil))))

(local
 (defthm o1s-cl-lines-are-lines
  (equal (fn-cll-lines lock keys) (o1s-octets (o1s-cl-ls lock keys)))
  :hints (("Goal" :in-theory (enable fn-cll-lines fn-cll-line fn-cll-key-line o1s-cl-ls o1s-octets
                                     fn-cll-append-is-append)))))

(local (defthm fn-pacc-parse-lines-starts-with-a-valid-line-l
 (implies (fn-article-result-okp
    (fn-article-parse-lines x limits left count nfields fields cur hr))
  (fn-article-line-okp (fn-article-next-line x)))
 :hints (("Goal" :do-not-induct t
   :cases ((fn-article-line-okp (fn-article-next-line x)))
   :in-theory (union-theories (theory 'minimal-theory)
     '(fn-article-result-okp fn-article-line-okp fn-article-error fn-article-parse-lines))))))

(local (defthm fn-pacc-parsed-first-line-is-bounded-l
 (implies (and (true-listp a) (fn-ipp-no-crlfp a)
  (fn-article-result-okp
    (fn-article-parse-lines (append a (list* 13 10 r)) limits left count nfields fields cur hr)))
  (<= (len a) *fn-article-max-line-octets*))
 :rule-classes :linear
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
     '(fn-article-line-okp))
   :use ((:instance fn-pacc-parse-lines-starts-with-a-valid-line-l
            (x (append a (list* 13 10 r))))
         (:instance o1s-next-line-of-a-line))))))

(local (defthm fn-pacc-lines-assoc-l
 (equal (append (append a b) c) (append a b c))
 :hints (("Goal" :induct (append a b) :in-theory (enable append)))))

(local (defun fn-pacc-lines-induct-l (ls r limits left count nf fs cur hr)
 (declare (xargs :measure (len ls) :verify-guards nil))
 (if (consp ls)
  (let* ((line (car ls)) (fr (fn-article-new-field line)))
   (list
    (fn-pacc-lines-induct-l (cdr ls) r limits (1- left) (+ count (len line) 2)
      nf fs (fn-article-add-fold cur line) (fn-article-header-rev-add-line hr line))
    (fn-pacc-lines-induct-l (cdr ls) r limits (1- left) (+ count (len line) 2)
      (if cur (+ 1 (nfix nf)) nf) (if cur (cons cur fs) fs)
      (fn-article-line-value fr) (fn-article-header-rev-add-line hr line))))
  (list r limits left count nf fs cur hr))))

(local (defthm fn-pacc-parsed-lines-cost-is-length-l
 (implies (and (o1s-linesp ls)
  (fn-article-result-okp
   (fn-article-parse-lines (append (o1s-octets ls) r) limits left count nf fs cur hr)))
  (equal (o1s-cost ls) (len (o1s-octets ls))))
 :hints (("Goal" :induct (fn-pacc-lines-induct-l ls r limits left count nf fs cur hr)
   :do-not '(generalize eliminate-destructors)
   :in-theory (e/d (fn-pacc-lines-induct-l o1s-linesp o1s-octets o1s-cost)
      (fn-article-parse-lines fn-article-next-line fn-ipp-no-crlfp)))
  ("Subgoal *1/1" :use ((:instance fn-pacc-parsed-first-line-is-bounded-l
    (a (car ls)) (nfields nf) (fields fs)
    (r (append (o1s-octets (cdr ls)) r))))
   :expand ((:free (left count nf fs cur hr)
     (fn-article-parse-lines
       (append (car ls) (list* 13 10 (append (o1s-octets (cdr ls)) r)))
       limits left count nf fs cur hr)))
   :in-theory (e/d (o1s-linesp o1s-octets o1s-cost
                   fn-article-line-value fn-article-line-rest fn-article-line-okp
                   fn-article-result-okp fn-article-error)
                  (fn-article-parse-lines fn-article-next-line fn-ipp-no-crlfp))))))

(local
 (defthm o1s-lock-value-len
  (<= (len (fn-cl-lock-value ring account msgid fields)) 44)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-cl-lock-value)
           :use ((:instance fn-cl-lock-shape (entry (fn-ns-current ring))))))))

(local
 (defthm o1s-date-shape
  (and (true-listp (fn-inj-date-octets inst)) (equal (len (fn-inj-date-octets inst)) 31))
  :hints (("Goal" :in-theory (enable fn-inj-date-octets)))))

(local
 (defthm o1s-generated-id-facts
  (implies (fn-inj-configp config)
           (let ((id (fn-inj-generated-message-id obs config)))
             (and (true-listp id) (fn-ipp-no-crlfp id)
                  (equal (len id) (+ 47 (len (fn-inj-config-agent config)))))))
  :hints (("Goal" :in-theory (e/d (fn-inj-generated-message-id o1s-inj-append) (fn-inj-configp))
           :use (o1s-config-agent-facts)))))

(local
 (defthm o1s-params-true-listp
  (true-listp (fn-ipp-params secret login addr))
  :hints (("Goal" :in-theory (e/d (fn-ipp-params fn-ipp-account-param fn-ipp-complaints-param
                                   o1s-inj-append fn-ipp-accountp)
                                  ())))))

(local
 (defthm o1s-params-okp-no-crlf
  (implies (fn-ipp-params-okp p) (fn-ipp-no-crlfp p))
  :hints (("Goal" :in-theory (enable fn-ipp-params-okp)))))

(local
 (defthm o1s-params-facts
  (and (true-listp (fn-ipp-params secret login (fn-ipp-complaints cfg)))
       (fn-ipp-no-crlfp (fn-ipp-params secret login (fn-ipp-complaints cfg))))
  :hints (("Goal" :cases ((consp (fn-ipp-params secret login (fn-ipp-complaints cfg))))
           :in-theory (disable fn-ipp-params fn-ipp-complaints fn-ipp-params-okp)
           :use (fn-ipp-params-are-a-parameter-run
                 (:instance o1s-params-true-listp (addr (fn-ipp-complaints cfg))))))))

(local
 (defthm o1s-path-insert-facts
  (implies (fn-ipp-no-crlfp agent)
           (and (true-listp (fn-inj-path-insert agent))
                (fn-ipp-no-crlfp (fn-inj-path-insert agent))
                (equal (len (fn-inj-path-insert agent)) (+ 1 (len agent)))))
  :hints (("Goal" :in-theory (enable fn-inj-path-insert)))))

(local (defthm fn-pacc-lines-append-facts-l
 (and (equal (o1s-cost (append a b)) (+ (o1s-cost a) (o1s-cost b)))
      (equal (o1s-octets (append a b)) (append (o1s-octets a) (o1s-octets b)))
      (implies (and (o1s-linesp a) (o1s-linesp b)) (o1s-linesp (append a b))))
 :hints (("Goal" :in-theory (enable o1s-cost o1s-octets o1s-linesp)))))

(local (defthm fn-pacc-cl-cost-bound-l
 (implies (and (or (not lock) (fn-cll-valuep lock)) (fn-cll-values-p keys) (<= (len lock) 44))
 (and (o1s-linesp (o1s-cl-ls lock keys))
      (<= (o1s-cost (o1s-cl-ls lock keys)) 1066)))
 :hints (("Goal" :in-theory (e/d (o1s-cl-ls o1s-cost o1s-linesp) (fn-cll-valuep fn-cll-values-p fn-cll-key-values fn-ipp-no-crlfp))
 :use (o1s-valuep-facts o1s-key-values-facts)))))

(local (defthm fn-pacc-prefix-cost-bound-l
 (implies (and (true-listp date) (fn-ipp-no-crlfp date) (equal (len date) 31)
   (implies gid (and (true-listp msgid) (fn-ipp-no-crlfp msgid) (equal (len msgid) (+ 47 (len agent)))))
   (true-listp agent) (fn-ipp-no-crlfp agent) (true-listp params) (fn-ipp-no-crlfp params))
 (and (o1s-linesp (cons (append *fn-inj-path-field* (append agent *fn-inj-path-tail*))
                 (o1s-block-ls date msgid agent gid gdate params)))
      (<= (o1s-cost (cons (append *fn-inj-path-field* (append agent *fn-inj-path-tail*))
                 (o1s-block-ls date msgid agent gid gdate params))) (+ 1170 (* 2 (len agent))))))
 :hints (("Goal" :in-theory (e/d (o1s-cost o1s-linesp) (o1s-block-ls fn-ipp-no-crlfp))
 :use (o1s-block-facts)))))

(local
 (defthm fn-pacc-carrier-absence-requires-a-parse-l
 (implies (equal (fn-pa-carrier-form payload) :absent)
          (fn-article-result-okp (fn-article-parse payload)))
 :hints (("Goal" :in-theory (e/d (fn-pa-carrier-form fn-pa-carrier-kind) (fn-article-parse fn-article-result-okp fn-article-result-article))))))

(local
 (defthm fn-pacc-parsed-prefix-cost-is-length-l
 (implies (and (o1s-linesp ls)
               (fn-article-result-okp (fn-article-parse (append (o1s-octets ls) r))))
          (equal (o1s-cost ls) (len (o1s-octets ls))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-article-parse fn-article-parse-under fn-article-result-okp fn-article-error))
  :use ((:instance fn-pacc-parsed-lines-cost-is-length-l
    (left (+ 1 (fn-article-limit-lines *fn-article-ceiling-limits*)))
    (count 0) (nf 0) (fs nil) (cur nil) (hr nil)
    (limits *fn-article-ceiling-limits*)))))))

(local
 (defun fn-pacc-direct-lines-l (art inj)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((d (fn-pctx-get 0 inj)) (secret (fn-pctx-get 1 inj)) (login (fn-pctx-get 2 inj))
        (cfg (fn-pctx-get 3 inj)) (carry (fn-pctx-get 4 inj))
        (icfg (fn-pctx-get 5 inj)) (obs (fn-pctx-get 6 inj))
        (msgid (fn-inj-decision-msgid d))
        (parsed (fn-article-result-article (fn-article-parse art)))
        (gid (not (fn-inj-nth 1 (fn-af-proto-article-check parsed))))
        (gdate (fn-inj-absentp parsed *fn-inj-date-name*))
        (pathp (not (fn-inj-absentp parsed *fn-inj-path-name*)))
        (agent (fn-inj-config-agent icfg))
        (date (fn-inj-date-octets (fn-inj-instant-of (fn-clock-wall obs))))
        (params (fn-ipp-params secret login (fn-ipp-complaints cfg)))
        (injected (fn-ipp-injected-octets d secret login cfg))
        (fields (fn-apc-received-fields injected carry)))
   (append (o1s-cl-ls (fn-cl-lock-value secret login msgid fields) (fn-cl-key-values secret login fields))
    (if pathp (o1s-block-ls date msgid agent gid gdate params)
     (cons (append *fn-inj-path-field* (append agent *fn-inj-path-tail*))
        (o1s-block-ls date msgid agent gid gdate params)))))))

(local
 (defthm fn-pacc-direct-splice-is-lines-l
 (implies (and (fn-pacc-injectionp inj art)
              (equal (fn-pctx-get 0 inj) (fn-inj-decide art (fn-pctx-get 5 inj) (fn-pctx-get 6 inj))))
  (equal (mv-nth 0 (fn-pacc-splice art inj)) (o1s-octets (fn-pacc-direct-lines-l art inj))))
 :hints (("Goal" :in-theory
 (union-theories (theory 'minimal-theory)
  '(fn-pacc-splice fn-pacc-direct-lines-l fn-pacc-cat-is-append-l fn-pacc-parsed-candidate-l
    fn-pacc-injectionp fn-pctx-get fn-pacc-standalone-block-l fn-pacc-standalone-prefix-l
    o1s-block-with-is-lines o1s-prefix-with-is-lines o1s-cl-lines-are-lines fn-pacc-lines-append-facts-l))
 :use ((:instance fn-pacc-success-parse-l (config (fn-pctx-get 5 inj)) (obs (fn-pctx-get 6 inj)))
       (:instance fn-pacc-a0-a-configured-agent-is-a-line-free-list (config (fn-pctx-get 5 inj)))
       (:instance o1s-date-shape (inst (fn-inj-instant-of (fn-clock-wall (fn-pctx-get 6 inj))))))))))

(local
 (defthm fn-pacc-config-agent-bound-l
 (implies (fn-inj-configp config) (<= (len (fn-inj-config-agent config)) *fn-inj-max-agent-octets*))
 :rule-classes :linear
 :hints (("Goal" :in-theory (enable fn-inj-configp)))))

(local
 (defthm fn-pacc-direct-lines-bounded-l
 (implies (and (fn-pacc-injectionp inj art)
              (equal (fn-pctx-get 0 inj) (fn-inj-decide art (fn-pctx-get 5 inj) (fn-pctx-get 6 inj))))
  (and (o1s-linesp (fn-pacc-direct-lines-l art inj))
       (<= (o1s-cost (fn-pacc-direct-lines-l art inj)) (fn-adm-injected-block-max))))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pacc-direct-lines-l fn-pacc-injectionp fn-pctx-get fn-pacc-lines-append-facts-l fn-adm-injected-block-max fn-o1-injected-block-octets (:executable-counterpart len) (:executable-counterpart make-list-ac)))
 :use ((:instance fn-pacc-config-agent-bound-l (config (fn-pctx-get 5 inj)))
(:instance o1s-config-agent-facts (config (fn-pctx-get 5 inj)))
(:instance o1s-date-shape (inst (fn-inj-instant-of (fn-clock-wall (fn-pctx-get 6 inj)))))
(:instance o1s-date-no-crlf (inst (fn-inj-instant-of (fn-clock-wall (fn-pctx-get 6 inj)))))
(:instance o1s-generated-id-facts (config (fn-pctx-get 5 inj)) (obs (fn-pctx-get 6 inj)))
(:instance fn-inj-generated-identity-is-the-clock-identity (source art) (config (fn-pctx-get 5 inj)) (observation (fn-pctx-get 6 inj)))
(:instance o1s-params-facts (secret (fn-pctx-get 1 inj)) (login (fn-pctx-get 2 inj)) (cfg (fn-pctx-get 3 inj)))
(:instance fn-pacc-prefix-cost-bound-l (date (fn-inj-date-octets (fn-inj-instant-of (fn-clock-wall (fn-pctx-get 6 inj))))) (msgid (fn-inj-decision-msgid (fn-pctx-get 0 inj))) (agent (fn-inj-config-agent (fn-pctx-get 5 inj))) (gid (not (fn-inj-nth 1 (fn-af-proto-article-check (fn-article-result-article (fn-article-parse art)))))) (gdate (fn-inj-absentp (fn-article-result-article (fn-article-parse art)) *fn-inj-date-name*)) (params (fn-ipp-params (fn-pctx-get 1 inj) (fn-pctx-get 2 inj) (fn-ipp-complaints (fn-pctx-get 3 inj)))))
(:instance o1s-block-facts (date (fn-inj-date-octets (fn-inj-instant-of (fn-clock-wall (fn-pctx-get 6 inj))))) (msgid (fn-inj-decision-msgid (fn-pctx-get 0 inj))) (agent (fn-inj-config-agent (fn-pctx-get 5 inj))) (gid (not (fn-inj-nth 1 (fn-af-proto-article-check (fn-article-result-article (fn-article-parse art)))))) (gdate (fn-inj-absentp (fn-article-result-article (fn-article-parse art)) *fn-inj-date-name*)) (params (fn-ipp-params (fn-pctx-get 1 inj) (fn-pctx-get 2 inj) (fn-ipp-complaints (fn-pctx-get 3 inj)))))
(:instance fn-pacc-cl-cost-bound-l (lock (fn-cl-lock-value (fn-pctx-get 1 inj) (fn-pctx-get 2 inj) (fn-inj-decision-msgid (fn-pctx-get 0 inj)) (fn-apc-received-fields (fn-ipp-injected-octets (fn-pctx-get 0 inj) (fn-pctx-get 1 inj) (fn-pctx-get 2 inj) (fn-pctx-get 3 inj)) (fn-pctx-get 4 inj)))) (keys (fn-cl-key-values (fn-pctx-get 1 inj) (fn-pctx-get 2 inj) (fn-apc-received-fields (fn-ipp-injected-octets (fn-pctx-get 0 inj) (fn-pctx-get 1 inj) (fn-pctx-get 2 inj) (fn-pctx-get 3 inj)) (fn-pctx-get 4 inj)))))
(:instance fn-cl-lock-value-is-a-value (ring (fn-pctx-get 1 inj)) (account (fn-pctx-get 2 inj)) (msgid (fn-inj-decision-msgid (fn-pctx-get 0 inj))) (fields (fn-apc-received-fields (fn-ipp-injected-octets (fn-pctx-get 0 inj) (fn-pctx-get 1 inj) (fn-pctx-get 2 inj) (fn-pctx-get 3 inj)) (fn-pctx-get 4 inj))))
(:instance fn-cl-key-values-are-values (ring (fn-pctx-get 1 inj)) (account (fn-pctx-get 2 inj)) (fields (fn-apc-received-fields (fn-ipp-injected-octets (fn-pctx-get 0 inj) (fn-pctx-get 1 inj) (fn-pctx-get 2 inj) (fn-pctx-get 3 inj)) (fn-pctx-get 4 inj))))
(:instance o1s-lock-value-len (ring (fn-pctx-get 1 inj)) (account (fn-pctx-get 2 inj)) (msgid (fn-inj-decision-msgid (fn-pctx-get 0 inj))) (fields (fn-apc-received-fields (fn-ipp-injected-octets (fn-pctx-get 0 inj) (fn-pctx-get 1 inj) (fn-pctx-get 2 inj) (fn-pctx-get 3 inj)) (fn-pctx-get 4 inj)))))))))

(local
 (defthm fn-pacc-direct-prefix-length-bounded-l
 (implies (and (fn-pacc-injectionp inj art)
              (equal (fn-pctx-get 0 inj) (fn-inj-decide art (fn-pctx-get 5 inj) (fn-pctx-get 6 inj)))
              (equal (fn-pa-carrier-form (fn-pacc-stored-payload art inj)) :absent))
   (<= (len (mv-nth 0 (fn-pacc-splice art inj))) (fn-adm-injected-block-max)))
 :rule-classes :linear
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-direct-splice-is-lines-l))
 :use (fn-pacc-direct-lines-bounded-l
       fn-pacc-stored-payload-is-one-splice
       (:instance fn-pacc-carrier-absence-requires-a-parse-l (payload (fn-pacc-stored-payload art inj)))
       (:instance fn-pacc-parsed-prefix-cost-is-length-l
          (ls (fn-pacc-direct-lines-l art inj))
          (r (append (take (mv-nth 2 (fn-pacc-splice art inj)) art)
                     (mv-nth 1 (fn-pacc-splice art inj))
                     (nthcdr (mv-nth 2 (fn-pacc-splice art inj)) art)))))))))

(local
 (defun fn-pacc-forward-entry-l (source config obs)
 (declare (xargs :guard t))
 (fn-inj-car (and (fn-mod-facts source config)
     (fn-mod-named-entries (fn-inj-decision-groups (fn-inj-decide source config obs))
                          (fn-inj-config-closed config))))))

(local
 (defthm fn-pacc-forward-entry-is-well-formed-l
 (implies (and (fn-inj-injectedp (fn-post-gated-decision source config obs))
               (not (equal (fn-post-gated-decision source config obs) (fn-inj-decide source config obs))))
   (fn-mod-entry-well-formedp (fn-pacc-forward-entry-l source config obs)))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-post-gated-decision fn-mod-gate fn-mod-forward fn-pacc-forward-entry-l
     fn-inj-refuse fn-inj-injectedp fn-inj-decision-status-of-fn-inj-make-decision
     fn-inj-car car-cons cdr-cons))))))

; A1 moderation prefix, context shape, and the approved layout keystone.
(local
 (defun fn-pacc-fields-omit-name-l (fs name)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp fs) (and (not (equal (fn-article-field-name (car fs)) name))
                     (fn-pacc-fields-omit-name-l (cdr fs) name)) t)))

(local
 (defun fn-pacc-lines-omit-name-l (ls name)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp ls)
  (and (not (fn-article-wspp (car (car ls))))
       (not (equal (fn-article-field-name (fn-article-line-value (fn-article-new-field (car ls)))) name))
       (fn-pacc-lines-omit-name-l (cdr ls) name)) t)))

(local
 (defthm fn-pacc-fields-omit-append-l
 (equal (fn-pacc-fields-omit-name-l (append a b) name)
        (and (fn-pacc-fields-omit-name-l a name) (fn-pacc-fields-omit-name-l b name)))
 :hints (("Goal" :in-theory (enable fn-pacc-fields-omit-name-l)))))

(local
 (defthm fn-pacc-fields-omit-revappend-l
 (equal (fn-pacc-fields-omit-name-l (revappend a b) name)
        (and (fn-pacc-fields-omit-name-l a name) (fn-pacc-fields-omit-name-l b name)))
 :hints (("Goal" :in-theory (enable fn-pacc-fields-omit-name-l)))))

(local
 (defthm fn-pacc-fields-omit-reverse-l
 (equal (fn-pacc-fields-omit-name-l (reverse a) name) (fn-pacc-fields-omit-name-l a name))
 :hints (("Goal" :in-theory (enable reverse)))))

(local
 (defthm fn-pacc-fields-omit-rev-l
 (equal (fn-pacc-fields-omit-name-l (rev a) name) (fn-pacc-fields-omit-name-l a name))
 :hints (("Goal" :induct (len a) :in-theory (enable fn-pacc-fields-omit-name-l rev)))))

(local
 (defthm fn-pacc-fields-omit-cons-l
 (equal (fn-pacc-fields-omit-name-l (cons f fs) name)
   (and (not (equal (fn-article-field-name f) name)) (fn-pacc-fields-omit-name-l fs name)))
 :hints (("Goal" :in-theory (enable fn-pacc-fields-omit-name-l)))))

(local
 (defthm fn-pacc-next-blank-line-l
 (equal (fn-article-next-line (list* 13 10 body)) (list :ok nil body))
 :hints (("Goal" :in-theory (enable fn-article-next-line fn-article-next-line-aux)))))

(local
 (defthm fn-pacc-parsed-header-omits-name-l
 (implies (and (o1s-linesp ls) (fn-pacc-lines-omit-name-l ls name)
  (fn-pacc-fields-omit-name-l fs name)
  (or (not cur) (not (equal (fn-article-field-name cur) name)))
  (fn-article-result-okp (fn-article-parse-lines
      (append (o1s-octets ls) (list* 13 10 body)) limits left count nf fs cur hr)))
 (fn-pacc-fields-omit-name-l
  (fn-article-fields (fn-article-result-article (fn-article-parse-lines
      (append (o1s-octets ls) (list* 13 10 body)) limits left count nf fs cur hr))) name))

 :hints (("Goal" :induct (fn-pacc-lines-induct-l ls (list* 13 10 body) limits left count nf fs cur hr)
  :do-not '(generalize eliminate-destructors)
  :in-theory (union-theories (theory 'minimal-theory)
   '(binary-append fn-pacc-lines-induct-l o1s-linesp o1s-octets fn-pacc-lines-omit-name-l fn-pacc-fields-omit-cons-l
     fn-pacc-fields-omit-reverse-l fn-pacc-fields-omit-rev-l
     fn-article-result-okp fn-article-line-okp fn-article-line-value fn-article-line-rest
     fn-article-error fn-article-ok fn-article-make fn-article-fields fn-article-result-article
     fn-article-finish-fields o1s-next-line-of-a-line fn-pacc-lines-assoc-l
     car-cons cdr-cons fn-article-wspp fn-pacc-next-blank-line-l)))
 ("Subgoal *1/1" :expand ((:free (left count nf fs cur hr)
   (fn-article-parse-lines (append (car ls) (list* 13 10 (append (o1s-octets (cdr ls)) (list* 13 10 body))))
       limits left count nf fs cur hr))))
 ("Subgoal *1/2" :expand ((:free (left count nf fs cur hr)
   (fn-article-parse-lines (list* 13 10 body) limits left count nf fs cur hr)))))))

(local
 (defthm fn-pacc-no-crlf-rev-l
 (equal (fn-ipp-no-crlfp (rev x)) (fn-ipp-no-crlfp x))
 :hints (("Goal" :induct (len x) :in-theory (enable rev fn-ipp-no-crlfp)))))

(local
 (defthm fn-pacc-no-crlf-reverse-l
 (equal (fn-ipp-no-crlfp (reverse x)) (fn-ipp-no-crlfp x))
 :hints (("Goal" :in-theory (enable reverse)))))

(local
 (defthm fn-pacc-literal-no-crlf-l
 (implies (fn-af-no-fold-literal-restp bytes) (fn-ipp-no-crlfp bytes))
 :hints (("Goal" :in-theory (enable fn-af-no-fold-literal-restp fn-af-mdtextp fn-ipp-no-crlfp)))))

(local
 (defthm fn-pacc-dot-atom-no-crlf-l
 (implies (fn-af-dot-atom-text-aux bytes want) (fn-ipp-no-crlfp bytes))
 :hints (("Goal" :induct (fn-af-dot-atom-text-aux bytes want)
 :in-theory (enable fn-af-dot-atom-text-aux fn-af-atextp fn-ipp-no-crlfp)))))

(local
 (defthm fn-pacc-id-right-no-crlf-l
 (implies (fn-af-id-rightp bytes) (fn-ipp-no-crlfp bytes))
 :hints (("Goal" :in-theory (e/d (fn-af-id-rightp fn-af-dot-atom-textp) (fn-af-no-fold-literal-restp fn-af-dot-atom-text-aux fn-ipp-no-crlfp))
 :use ((:instance fn-pacc-dot-atom-no-crlf-l (want t)))))))

(local
 (defthm fn-pacc-id-core-aux-no-crlf-l
 (implies (fn-af-msg-id-core-aux bytes left-rev)
   (and (fn-ipp-no-crlfp bytes) (fn-ipp-no-crlfp left-rev)))
 :hints (("Goal" :induct (fn-af-msg-id-core-aux bytes left-rev)
  :in-theory (union-theories (theory 'minimal-theory) '(fn-af-msg-id-core-aux fn-af-dot-atom-textp fn-ipp-no-crlfp fn-pacc-no-crlf-reverse-l o1s-no-crlf-cons fn-pacc-id-right-no-crlf-l car-cons cdr-cons)))
 ("Subgoal *1/1" :use ((:instance fn-pacc-dot-atom-no-crlf-l
    (bytes (reverse left-rev)) (want t)))))))

(local
 (defthm fn-pacc-id-close-no-crlf-l
 (implies (fn-af-msg-id-closep bytes core-rev)
   (and (fn-ipp-no-crlfp bytes) (fn-ipp-no-crlfp core-rev)))
 :hints (("Goal" :induct (fn-af-msg-id-closep bytes core-rev)
  :in-theory (union-theories (theory 'minimal-theory) '(fn-af-msg-id-closep fn-af-msg-id-corep fn-ipp-no-crlfp fn-pacc-no-crlf-reverse-l fn-pacc-id-core-aux-no-crlf-l o1s-no-crlf-cons car-cons cdr-cons)))
 ("Subgoal *1/1" :use ((:instance fn-pacc-id-core-aux-no-crlf-l (bytes (reverse core-rev)) (left-rev nil)))))))

(local
 (defthm fn-pacc-at-most-bounds-length-l
 (implies (and (natp bound) (fn-cbor-at-mostp xs bound)) (<= (len xs) bound))
 :rule-classes :linear
 :hints (("Goal" :induct (fn-cbor-at-mostp xs bound) :in-theory (enable fn-cbor-at-mostp)))))

(local
 (defthm fn-pacc-message-id-shape-l
 (implies (fn-af-message-idp msgid)
  (and (true-listp msgid) (fn-ipp-no-crlfp msgid) (<= (len msgid) *fn-af-max-message-id-octets*)))
 :hints (("Goal" :in-theory (e/d (fn-af-message-idp) (fn-af-msg-id-closep fn-cbor-at-mostp fn-cbor-octet-listp fn-ipp-no-crlfp))
 :use ((:instance fn-pacc-at-most-bounds-length-l (xs msgid) (bound *fn-af-max-message-id-octets*))
       (:instance fn-cbor-octet-listp-implies-true-listp (xs msgid))
       (:instance fn-pacc-id-close-no-crlf-l (bytes (cdr msgid)) (core-rev nil)))))))

(local
 (defthm fn-pacc-injected-msgid-shape-l
 (implies (and (fn-inj-configp config) (fn-inj-injectedp (fn-inj-decide source config obs)))
  (let ((mid (fn-inj-decision-msgid (fn-inj-decide source config obs))))
   (and (true-listp mid) (fn-ipp-no-crlfp mid) (<= (len mid) *fn-af-max-message-id-octets*))))
 :hints (("Goal" :do-not-induct t
 :in-theory (e/d (fn-inj-decide fn-inj-injectedp fn-inj-refuse fn-inj-proto-reason
  fn-af-proto-article-check fn-af-relayed-article-check fn-af-status-kind fn-af-status-value
  fn-af-status-field fn-af-message-id-status fn-af-message-id-field-value fn-inj-nth fn-inj-car fn-inj-cdr)
 (fn-inj-configp fn-inj-generated-message-id fn-article-parse fn-article-result-okp fn-article-result-article
  fn-article-syntax-p fn-article-get-headers fn-af-newsgroups-status fn-af-message-idp
  fn-inj-mandatory-reason fn-inj-path-reason fn-inj-other-reason fn-inj-date-octets
  fn-inj-prefix fn-inj-block fn-inj-splice fn-inj-path-offset fn-inj-path-insert
  fn-inj-groups-admissiblep fn-clock-observationp fn-clock-has-wall fn-clock-wall
  fn-article-census-refusal fn-article-header-census fn-inj-config-header-limits fn-inj-absentp
  fn-ipp-no-crlfp fn-af-trim-wsp))
 :use (o1s-generated-id-facts fn-pacc-config-agent-bound-l)))))

(local
 (defun fn-pacc-envelope-lines-l (agent group queue msgid)
 (declare (xargs :guard t :verify-guards nil))
 (list (append *fn-mod-from* agent)
       (append *fn-mod-subject* group)
       (append *fn-mod-newsgroups* queue)
       (append *fn-inj-message-id-field* (fn-mod-envelope-msgid msgid))
       *fn-mod-content-type*)))

(local
 (defthm fn-pacc-envelope-is-lines-l
 (implies (true-listp forwarded)
  (equal (fn-mod-envelope-source agent group queue msgid forwarded)
   (append (o1s-octets (fn-pacc-envelope-lines-l agent group queue msgid))
           (list* 13 10 forwarded))))
 :hints (("Goal" :in-theory (enable fn-mod-envelope-source fn-mod-concat o1s-octets fn-pacc-envelope-lines-l
                                 fn-inj-message-id-line o1s-inj-append fn-pacc-a0-append-assoc)))))

(local
 (defthm fn-pacc-envelope-lines-omit-targets-l
 (and (fn-pacc-lines-omit-name-l (fn-pacc-envelope-lines-l agent group queue msgid) *fn-ctl-control-name*)
      (fn-pacc-lines-omit-name-l (fn-pacc-envelope-lines-l agent group queue msgid) *fn-ctl-supersedes-name*))
 :hints (("Goal" :do-not-induct t :in-theory
 (e/d (fn-pacc-envelope-lines-l fn-pacc-lines-omit-name-l
       fn-article-new-field fn-article-split-colon-aux fn-article-line-value fn-article-field-name
       fn-article-error fn-article-make-field fn-article-ascii-downcase fn-article-wspp)
      (fn-mod-envelope-msgid fn-article-header-bytes-p fn-article-namep))))))

(local
 (defthm fn-pacc-no-crlf-is-no-line-break-l
 (equal (fn-ipp-no-crlfp x) (and (not (member-equal 13 x)) (not (member-equal 10 x))))
 :hints (("Goal" :in-theory (enable fn-ipp-no-crlfp member-equal)))))

(local
 (defthm fn-pacc-mod-name-facts-l
 (implies (fn-mod-name-well-formedp x)
 (and (true-listp x) (fn-ipp-no-crlfp x) (<= (len x) *fn-record-max-group-name*)))
 :hints (("Goal" :in-theory (e/d (fn-mod-name-well-formedp fn-pacc-no-crlf-is-no-line-break-l)
                               (fn-cbor-octet-listp fn-af-newsgroup-namep))))))

(local (in-theory (disable fn-pacc-no-crlf-is-no-line-break-l)))

(local
 (defthm fn-pacc-mod-msgid-facts-l
 (implies (and (true-listp msgid) (fn-ipp-no-crlfp msgid))
 (and (true-listp (fn-mod-envelope-msgid msgid))
      (fn-ipp-no-crlfp (fn-mod-envelope-msgid msgid))
      (<= (len (fn-mod-envelope-msgid msgid)) (+ (len msgid) (len *fn-mod-id-prefix*)))))
 :hints (("Goal" :in-theory (enable fn-mod-envelope-msgid o1s-inj-append)))))

(local
 (defthm fn-pacc-len-cons-l
 (equal (len (cons x y)) (+ 1 (len y)))
 :hints (("Goal" :in-theory (enable len)))))

(local
 (defthm fn-pacc-envelope-lines-facts-l
 (implies (and (true-listp agent) (fn-ipp-no-crlfp agent) (<= (len agent) *fn-inj-max-agent-octets*)
               (fn-mod-name-well-formedp group) (fn-mod-name-well-formedp queue)
               (true-listp msgid) (fn-ipp-no-crlfp msgid) (<= (len msgid) *fn-af-max-message-id-octets*))
 (and (o1s-linesp (fn-pacc-envelope-lines-l agent group queue msgid))
      (<= (len (o1s-octets (fn-pacc-envelope-lines-l agent group queue msgid))) 1044)))
 :hints (("Goal" :in-theory (e/d (fn-pacc-envelope-lines-l o1s-linesp o1s-octets)
      (fn-pacc-mod-name-facts-l fn-pacc-mod-msgid-facts-l len fn-mod-envelope-msgid fn-ipp-no-crlfp fn-mod-name-well-formedp fn-pacc-no-crlf-is-no-line-break-l))
 :use ((:instance fn-pacc-mod-name-facts-l (x group))
       (:instance fn-pacc-mod-name-facts-l (x queue))
       fn-pacc-mod-msgid-facts-l)))))

(local
 (defthm fn-pacc-injection-lines-omit-targets-l
 (and (fn-pacc-lines-omit-name-l (o1s-block-ls date msgid agent gid gdate params) *fn-ctl-control-name*)
      (fn-pacc-lines-omit-name-l (o1s-block-ls date msgid agent gid gdate params) *fn-ctl-supersedes-name*)
      (fn-pacc-lines-omit-name-l
         (cons (append *fn-inj-path-field* (append agent *fn-inj-path-tail*))
                  (o1s-block-ls date msgid agent gid gdate params)) *fn-ctl-control-name*)
      (fn-pacc-lines-omit-name-l
         (cons (append *fn-inj-path-field* (append agent *fn-inj-path-tail*))
                  (o1s-block-ls date msgid agent gid gdate params)) *fn-ctl-supersedes-name*))
 :hints (("Goal" :do-not-induct t
 :in-theory (e/d (o1s-block-ls fn-pacc-lines-omit-name-l fn-article-new-field fn-article-split-colon-aux
  fn-article-line-value fn-article-field-name fn-article-error fn-article-make-field
  fn-article-ascii-downcase fn-article-wspp)
 (fn-article-header-bytes-p fn-article-namep))))))

(local
 (defthm fn-pacc-lines-omit-append-l
 (equal (fn-pacc-lines-omit-name-l (append a b) name)
    (and (fn-pacc-lines-omit-name-l a name) (fn-pacc-lines-omit-name-l b name)))
 :hints (("Goal" :in-theory (enable fn-pacc-lines-omit-name-l)))))

(local
 (defthm fn-pacc-omitted-name-lookup-nil-l
 (implies (and (consp name) (fn-pacc-fields-omit-name-l fs name)) (equal (fn-ctl-fields-named name fs) nil))
 :hints (("Goal" :in-theory (enable fn-pacc-fields-omit-name-l fn-ctl-fields-named)))))

(local
 (defthm fn-pacc-omitted-target-means-no-keys-l
 (implies (and (fn-pacc-fields-omit-name-l fs *fn-ctl-control-name*)
               (fn-pacc-fields-omit-name-l fs *fn-ctl-supersedes-name*))
          (equal (fn-cl-key-values ring account fs) nil))
 :hints (("Goal" :in-theory (enable fn-cl-key-values fn-cl-key-target fn-ctl-article-target
  fn-ctl-classify-fields fn-ctl-cancel-target fn-ctl-supersedes-target)))))

(local
 (defthm fn-pacc-parsed-header-fields-omit-name-l
 (implies (and (o1s-linesp ls) (fn-pacc-lines-omit-name-l ls name)
  (fn-article-result-okp (fn-article-parse (append (o1s-octets ls) (list* 13 10 body)))))
 (fn-pacc-fields-omit-name-l
    (fn-article-fields (fn-article-result-article
      (fn-article-parse (append (o1s-octets ls) (list* 13 10 body))))) name))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-article-parse fn-article-parse-under fn-article-result-okp fn-article-error
    fn-pacc-fields-omit-name-l))
 :use ((:instance fn-pacc-parsed-header-omits-name-l
  (limits *fn-article-ceiling-limits*)
  (left (+ 1 (fn-article-limit-lines *fn-article-ceiling-limits*)))
  (count 0) (nf 0) (fs nil) (cur nil) (hr nil)))))))

(local
 (defthm fn-pacc-envelope-lines-omit-gate-fields-l
 (and (fn-pacc-lines-omit-name-l (fn-pacc-envelope-lines-l agent group queue msgid) *fn-inj-path-name*)
      (fn-pacc-lines-omit-name-l (fn-pacc-envelope-lines-l agent group queue msgid) *fn-inj-date-name*))
 :hints (("Goal" :do-not-induct t :in-theory
 (e/d (fn-pacc-envelope-lines-l fn-pacc-lines-omit-name-l
       fn-article-new-field fn-article-split-colon-aux fn-article-line-value fn-article-field-name
       fn-article-error fn-article-make-field fn-article-ascii-downcase fn-article-wspp)
      (fn-mod-envelope-msgid fn-article-header-bytes-p fn-article-namep))))))

(local
 (defthm fn-pacc-omitted-name-article-lookup-nil-l
 (implies (fn-pacc-fields-omit-name-l fs (fn-article-ascii-downcase name))
          (equal (fn-article-get-headers-aux fs name) nil))
 :hints (("Goal" :in-theory (enable fn-article-get-headers-aux fn-article-field-name-equalp fn-pacc-fields-omit-name-l)))))

(local
 (defthm fn-pacc-safe-header-has-no-cancel-keys-l
 (implies (and (o1s-linesp ls)
  (fn-pacc-lines-omit-name-l ls *fn-ctl-control-name*)
  (fn-pacc-lines-omit-name-l ls *fn-ctl-supersedes-name*))
  (equal (fn-cl-key-values ring account
   (fn-ctl-received-fields (append (o1s-octets ls) (list* 13 10 body)))) nil))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'minimal-theory)
  '(fn-ctl-received-fields fn-pacc-fields-omit-name-l))
 :use ((:instance fn-pacc-parsed-header-fields-omit-name-l (name *fn-ctl-control-name*))
       (:instance fn-pacc-parsed-header-fields-omit-name-l (name *fn-ctl-supersedes-name*))
       (:instance fn-pacc-omitted-target-means-no-keys-l
         (fs (fn-ctl-received-fields (append (o1s-octets ls) (list* 13 10 body))))))))))

(local
 (defun fn-pacc-inj-prefix-lines-l (source config obs secret login cfg)
 (declare (xargs :guard t :verify-guards nil))
 (cons (append *fn-inj-path-field* (append (fn-inj-config-agent config) *fn-inj-path-tail*))
       (o1s-block-ls (fn-ipp-date obs) (fn-inj-decision-msgid (fn-inj-decide source config obs))
          (fn-inj-config-agent config) (fn-ipp-gid source) (fn-ipp-gdate source)
          (fn-ipp-params secret login (fn-ipp-complaints cfg))))))

(local
 (defthm fn-pacc-prefix-injection-is-lines-l
 (implies (and (fn-inj-injectedp (fn-inj-decide source config obs))
               (not (fn-inj-supplies-pathp source)))
  (equal (fn-ipp-injected-octets (fn-inj-decide source config obs) secret login cfg)
         (append (o1s-octets (fn-pacc-inj-prefix-lines-l source config obs secret login cfg)) source)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pacc-inj-prefix-lines-l o1s-prefix-with-is-lines))
  :use (fn-ipp-injected-octets-carry-the-parameters)))))

(local
 (defthm fn-pacc-inj-prefix-lines-facts-l
 (implies (and (fn-inj-configp config) (fn-inj-injectedp (fn-inj-decide source config obs)))
  (and (o1s-linesp (fn-pacc-inj-prefix-lines-l source config obs secret login cfg))
       (<= (o1s-cost (fn-pacc-inj-prefix-lines-l source config obs secret login cfg)) 1426)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-inj-prefix-lines-l))
  :use (fn-pacc-config-agent-bound-l
o1s-config-agent-facts
o1s-generated-id-facts
(:instance fn-inj-generated-identity-is-the-clock-identity (observation obs))
(:instance o1s-date-shape (inst (fn-inj-instant-of (fn-clock-wall obs))))
(:instance o1s-date-no-crlf (inst (fn-inj-instant-of (fn-clock-wall obs))))
o1s-params-facts
(:instance fn-pacc-prefix-cost-bound-l (date (fn-ipp-date obs)) (msgid (fn-inj-decision-msgid (fn-inj-decide source config obs))) (agent (fn-inj-config-agent config)) (gid (fn-ipp-gid source)) (gdate (fn-ipp-gdate source)) (params (fn-ipp-params secret login (fn-ipp-complaints cfg)))))))))

(local
 (defthm fn-pacc-envelope-supplies-no-path-l
 (implies (and (true-listp agent) (fn-ipp-no-crlfp agent) (<= (len agent) *fn-inj-max-agent-octets*)
               (fn-mod-name-well-formedp group) (fn-mod-name-well-formedp queue)
               (true-listp msgid) (fn-ipp-no-crlfp msgid) (<= (len msgid) *fn-af-max-message-id-octets*)
               (true-listp forwarded))
          (not (fn-inj-supplies-pathp (fn-mod-envelope-source agent group queue msgid forwarded))))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'minimal-theory)
  '(fn-inj-supplies-pathp fn-inj-absentp fn-article-get-headers
    fn-pacc-omitted-name-article-lookup-nil-l (:executable-counterpart fn-article-ascii-downcase)))
 :use (fn-pacc-envelope-is-lines-l fn-pacc-envelope-lines-facts-l
       fn-pacc-envelope-lines-omit-gate-fields-l
       (:instance fn-pacc-parsed-header-fields-omit-name-l
        (ls (fn-pacc-envelope-lines-l agent group queue msgid)) (body forwarded) (name *fn-inj-path-name*)))))))

(local
 (defthm fn-pacc-inj-prefix-omits-targets-l
 (and (fn-pacc-lines-omit-name-l (fn-pacc-inj-prefix-lines-l source config obs secret login cfg) *fn-ctl-control-name*)
      (fn-pacc-lines-omit-name-l (fn-pacc-inj-prefix-lines-l source config obs secret login cfg) *fn-ctl-supersedes-name*))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-inj-prefix-lines-l))
 :use ((:instance fn-pacc-injection-lines-omit-targets-l
  (date (fn-ipp-date obs)) (msgid (fn-inj-decision-msgid (fn-inj-decide source config obs)))
  (agent (fn-inj-config-agent config)) (gid (fn-ipp-gid source)) (gdate (fn-ipp-gdate source))
  (params (fn-ipp-params secret login (fn-ipp-complaints cfg)))))))))

(local
 (defthm fn-pacc-injected-envelope-has-no-cancel-keys-l
 (implies (and (fn-inj-configp config)
               (fn-mod-name-well-formedp group) (fn-mod-name-well-formedp queue)
               (true-listp msgid) (fn-ipp-no-crlfp msgid) (<= (len msgid) *fn-af-max-message-id-octets*)
               (true-listp forwarded)
               (fn-inj-injectedp (fn-inj-decide (fn-mod-envelope-source (fn-inj-config-agent config) group queue msgid forwarded) config obs)))
  (equal (fn-cl-key-values ring account
   (fn-ctl-received-fields (fn-ipp-injected-octets (fn-inj-decide (fn-mod-envelope-source (fn-inj-config-agent config) group queue msgid forwarded) config obs) secret login cfg))) nil))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pacc-lines-assoc-l fn-pacc-lines-append-facts-l fn-pacc-lines-omit-append-l))
 :use (fn-pacc-config-agent-bound-l o1s-config-agent-facts
       (:instance fn-pacc-envelope-is-lines-l (agent (fn-inj-config-agent config)))
       (:instance fn-pacc-envelope-lines-facts-l (agent (fn-inj-config-agent config)))
       (:instance fn-pacc-envelope-supplies-no-path-l (agent (fn-inj-config-agent config)))
       (:instance fn-pacc-envelope-lines-omit-targets-l (agent (fn-inj-config-agent config)))
       (:instance fn-pacc-prefix-injection-is-lines-l (source (fn-mod-envelope-source (fn-inj-config-agent config) group queue msgid forwarded)))
       (:instance fn-pacc-inj-prefix-lines-facts-l (source (fn-mod-envelope-source (fn-inj-config-agent config) group queue msgid forwarded)))
       (:instance fn-pacc-inj-prefix-omits-targets-l (source (fn-mod-envelope-source (fn-inj-config-agent config) group queue msgid forwarded)))
       (:instance fn-pacc-safe-header-has-no-cancel-keys-l (ls (append (fn-pacc-inj-prefix-lines-l (fn-mod-envelope-source (fn-inj-config-agent config) group queue msgid forwarded) config obs secret login cfg) (fn-pacc-envelope-lines-l (fn-inj-config-agent config) group queue msgid))) (body forwarded)))))))

(local
 (defthm fn-pacc-cl-lock-lines-bounded-l
 (implies (and (or (not lock) (fn-cll-valuep lock)) (<= (len lock) 44))
 (and (o1s-linesp (o1s-cl-ls lock nil)) (<= (o1s-cost (o1s-cl-ls lock nil)) 66)))
 :hints (("Goal" :in-theory (e/d (o1s-cl-ls o1s-cost o1s-linesp) (fn-ipp-no-crlfp fn-cll-valuep))
 :use (o1s-valuep-facts)))))

(local
 (defthm fn-pacc-served-without-keys-has-a-bounded-prefix-l
 (implies (and (fn-inj-configp config) (fn-inj-injectedp (fn-inj-decide source config obs))
               (not (fn-inj-supplies-pathp source))
               (not (fn-cl-key-values secret login (fn-ctl-received-fields
                    (fn-ipp-injected-octets (fn-inj-decide source config obs) secret login cfg))))
               (fn-article-result-okp (fn-article-parse
                 (fn-cl-served-payload secret login (fn-inj-decision-msgid (fn-inj-decide source config obs))
                   (fn-ipp-injected-octets (fn-inj-decide source config obs) secret login cfg)))))
  (<= (len (fn-cl-served-payload secret login (fn-inj-decision-msgid (fn-inj-decide source config obs))
                   (fn-ipp-injected-octets (fn-inj-decide source config obs) secret login cfg)))
      (+ (len source) 1492)))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-cl-served-payload fn-cll-append-is-append o1s-cl-lines-are-lines
   fn-pacc-lines-append-facts-l fn-pacc-lines-assoc-l fn-pacc-mod-len-append-l))
 :use (fn-pacc-prefix-injection-is-lines-l
fn-pacc-inj-prefix-lines-facts-l
(:instance fn-cl-lock-value-is-a-value (ring secret) (account login) (msgid (fn-inj-decision-msgid (fn-inj-decide source config obs))) (fields (fn-ctl-received-fields (fn-ipp-injected-octets (fn-inj-decide source config obs) secret login cfg))))
(:instance o1s-lock-value-len (ring secret) (account login) (msgid (fn-inj-decision-msgid (fn-inj-decide source config obs))) (fields (fn-ctl-received-fields (fn-ipp-injected-octets (fn-inj-decide source config obs) secret login cfg))))
(:instance fn-pacc-cl-lock-lines-bounded-l (lock (fn-cl-lock-value secret login (fn-inj-decision-msgid (fn-inj-decide source config obs)) (fn-ctl-received-fields (fn-ipp-injected-octets (fn-inj-decide source config obs) secret login cfg)))))
(:instance fn-pacc-parsed-prefix-cost-is-length-l (ls (append (o1s-cl-ls (fn-cl-lock-value secret login (fn-inj-decision-msgid (fn-inj-decide source config obs)) (fn-ctl-received-fields (fn-ipp-injected-octets (fn-inj-decide source config obs) secret login cfg))) nil) (fn-pacc-inj-prefix-lines-l source config obs secret login cfg))) (r source)))))))

(local
 (defthm fn-pacc-forwarded-source-length-l
 (<= (len (fn-mod-forwarded-source source facts msgid date))
     (+ (len source) (len *fn-inj-message-id-field*) (len msgid) (len *fn-inj-crlf*)
                    (len *fn-inj-date-field*) (len date) (len *fn-inj-crlf*)))
 :rule-classes :linear
 :hints (("Goal" :in-theory (e/d (fn-mod-forwarded-source fn-inj-message-id-line fn-inj-date-line o1s-inj-append)
                                (len fn-pacc-no-crlf-is-no-line-break-l))))))

(local
 (defthm fn-pacc-take-prefix-length-l
 (<= (len (fn-inj-take-n n x)) (nfix n))
 :rule-classes :linear
 :hints (("Goal" :in-theory (enable fn-inj-take-n)))))

(local
 (defthm fn-pacc-envelope-length-bounded-l
 (implies (and (true-listp agent) (fn-ipp-no-crlfp agent) (<= (len agent) *fn-inj-max-agent-octets*)
               (fn-mod-name-well-formedp group) (fn-mod-name-well-formedp queue)
               (true-listp msgid) (fn-ipp-no-crlfp msgid) (<= (len msgid) *fn-af-max-message-id-octets*)
               (true-listp forwarded))
  (<= (len (fn-mod-envelope-source agent group queue msgid forwarded)) (+ 1046 (len forwarded))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pacc-envelope-is-lines-l fn-pacc-mod-len-append-l fn-pacc-len-cons-l (:executable-counterpart len)))
 :use (fn-pacc-envelope-lines-facts-l)))))

(local
 (defthm fn-pacc-forwarded-envelope-stored-length-bounded-l
 (implies (and (true-listp source) (fn-inj-configp config)
  (fn-mod-name-well-formedp group) (fn-mod-name-well-formedp queue)
  (true-listp msgid) (fn-ipp-no-crlfp msgid) (<= (len msgid) *fn-af-max-message-id-octets*)
  (fn-inj-injectedp (fn-inj-decide (fn-mod-envelope-source (fn-inj-config-agent config) group queue msgid (fn-mod-forwarded-source source facts msgid (fn-ipp-date obs))) config obs)) (fn-article-result-okp (fn-article-parse (fn-cl-served-payload secret login (fn-inj-decision-msgid (fn-inj-decide (fn-mod-envelope-source (fn-inj-config-agent config) group queue msgid (fn-mod-forwarded-source source facts msgid (fn-ipp-date obs))) config obs)) (fn-ipp-injected-octets (fn-inj-decide (fn-mod-envelope-source (fn-inj-config-agent config) group queue msgid (fn-mod-forwarded-source source facts msgid (fn-ipp-date obs))) config obs) secret login cfg)))))
  (<= (len (fn-cl-served-payload secret login (fn-inj-decision-msgid (fn-inj-decide (fn-mod-envelope-source (fn-inj-config-agent config) group queue msgid (fn-mod-forwarded-source source facts msgid (fn-ipp-date obs))) config obs)) (fn-ipp-injected-octets (fn-inj-decide (fn-mod-envelope-source (fn-inj-config-agent config) group queue msgid (fn-mod-forwarded-source source facts msgid (fn-ipp-date obs))) config obs) secret login cfg))) (+ (len source) 2841)))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pacc-mod-len-append-l fn-pacc-len-cons-l (:executable-counterpart len)))
 :use (fn-pacc-config-agent-bound-l o1s-config-agent-facts
       (:instance fn-pacc-forwarded-source-length-l (date (fn-ipp-date obs)))
       (:instance o1s-date-shape (inst (fn-inj-instant-of (fn-clock-wall obs))))
       (:instance fn-pacc-mod-forwarded-true-list-l (date (fn-ipp-date obs)))
       (:instance fn-pacc-envelope-length-bounded-l (agent (fn-inj-config-agent config)) (forwarded (fn-mod-forwarded-source source facts msgid (fn-ipp-date obs))))
       (:instance fn-pacc-envelope-lines-facts-l (agent (fn-inj-config-agent config)))
       (:instance fn-pacc-envelope-supplies-no-path-l (agent (fn-inj-config-agent config)) (forwarded (fn-mod-forwarded-source source facts msgid (fn-ipp-date obs))))
       (:instance fn-pacc-injected-envelope-has-no-cancel-keys-l (ring secret) (account login) (forwarded (fn-mod-forwarded-source source facts msgid (fn-ipp-date obs))))
       (:instance fn-pacc-served-without-keys-has-a-bounded-prefix-l (source (fn-mod-envelope-source (fn-inj-config-agent config) group queue msgid (fn-mod-forwarded-source source facts msgid (fn-ipp-date obs))))))))))

(local
 (defthm fn-pacc-forwarded-source-is-the-envelope-l
 (implies (and (fn-inj-injectedp (fn-post-gated-decision source config obs))
               (not (equal (fn-post-gated-decision source config obs) (fn-inj-decide source config obs))))
  (equal (fn-pacc-injection-source-l source config obs)
    (fn-mod-envelope-source (fn-inj-config-agent config)
      (fn-mod-entry-group (fn-pacc-forward-entry-l source config obs))
      (fn-mod-entry-queue (fn-pacc-forward-entry-l source config obs))
      (fn-inj-decision-msgid (fn-inj-decide source config obs))
      (fn-mod-forwarded-source source (fn-mod-facts source config)
        (fn-inj-decision-msgid (fn-inj-decide source config obs)) (fn-ipp-date obs)))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
  '(fn-post-gated-decision fn-mod-gate fn-pacc-injection-source-l fn-pacc-forward-entry-l fn-inj-car fn-inj-injectedp fn-inj-refuse fn-inj-decision-status-of-fn-inj-make-decision))))))

(local
 (defthm fn-pacc-stored-is-source-served-l
 (implies (fn-pacc-injectionp inj art)
  (let* ((icfg (fn-pctx-get 5 inj)) (obs (fn-pctx-get 6 inj))
         (source (fn-pacc-injection-source-l art icfg obs))
         (d (fn-inj-decide source icfg obs)))
   (equal (fn-pacc-stored-payload art inj)
    (fn-cl-served-payload (fn-pctx-get 1 inj) (fn-pctx-get 2 inj) (fn-inj-decision-msgid d)
      (fn-ipp-injected-octets d (fn-pctx-get 1 inj) (fn-pctx-get 2 inj) (fn-pctx-get 3 inj))))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-stored-payload fn-pacc-injectionp))
 :use ((:instance fn-pacc-gate-is-injection-of-source-l
  (source art) (config (fn-pctx-get 5 inj)) (obs (fn-pctx-get 6 inj)))
       (:instance fn-apc-cl-served-payload-is-reference
         (ring (fn-pctx-get 1 inj)) (account (fn-pctx-get 2 inj))
         (msgid (fn-inj-decision-msgid (fn-pctx-get 0 inj)))
         (payload (fn-ipp-injected-octets (fn-pctx-get 0 inj) (fn-pctx-get 1 inj) (fn-pctx-get 2 inj) (fn-pctx-get 3 inj)))
         (carry (fn-pctx-get 4 inj))))))))

(local
 (defthm fn-pacc-forwarded-stored-length-bounded-l
 (implies (and (fn-pacc-injectionp inj art)
  (not (equal (fn-pctx-get 0 inj) (fn-inj-decide art (fn-pctx-get 5 inj) (fn-pctx-get 6 inj))))
  (equal (fn-pa-carrier-form (fn-pacc-stored-payload art inj)) :absent))
  (<= (len (fn-pacc-stored-payload art inj)) (+ (len art) 2841)))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pacc-injectionp fn-mod-entry-well-formedp
    fn-pacc-forwarded-source-is-the-envelope-l fn-pacc-stored-is-source-served-l))
 :use (fn-pacc-gated-injection-decision-l fn-pacc-injection-requires-octets-l
       (:instance fn-pacc-octets-true-listp-l (x art))
       (:instance fn-pacc-carrier-absence-requires-a-parse-l (payload (fn-pacc-stored-payload art inj)))
       (:instance fn-pacc-forward-entry-is-well-formed-l (source art) (config (fn-pctx-get 5 inj)) (obs (fn-pctx-get 6 inj)))
       (:instance fn-pacc-gate-is-injection-of-source-l (source art) (config (fn-pctx-get 5 inj)) (obs (fn-pctx-get 6 inj)))
       (:instance fn-pacc-injected-msgid-shape-l (source art) (config (fn-pctx-get 5 inj)) (obs (fn-pctx-get 6 inj)))
       (:instance fn-pacc-forwarded-envelope-stored-length-bounded-l
         (source art) (config (fn-pctx-get 5 inj)) (obs (fn-pctx-get 6 inj))
         (group (fn-mod-entry-group (fn-pacc-forward-entry-l art (fn-pctx-get 5 inj) (fn-pctx-get 6 inj)))) (queue (fn-mod-entry-queue (fn-pacc-forward-entry-l art (fn-pctx-get 5 inj) (fn-pctx-get 6 inj))))
         (facts (fn-mod-facts art (fn-pctx-get 5 inj))) (msgid (fn-inj-decision-msgid (fn-inj-decide art (fn-pctx-get 5 inj) (fn-pctx-get 6 inj))))
         (secret (fn-pctx-get 1 inj)) (login (fn-pctx-get 2 inj)) (cfg (fn-pctx-get 3 inj))))))))

(local
 (defthm fn-pacc-forwarded-prefix-length-bounded-l
 (implies (and (fn-pacc-injectionp inj art)
  (not (equal (fn-pctx-get 0 inj) (fn-inj-decide art (fn-pctx-get 5 inj) (fn-pctx-get 6 inj))))
  (equal (fn-pa-carrier-form (fn-pacc-stored-payload art inj)) :absent))
  (<= (len (mv-nth 0 (fn-pacc-splice art inj))) 2841))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pacc-splice mv-nth nfix natp (:type-prescription len)))
 :use (fn-pacc-forwarded-stored-length-bounded-l
       (:instance fn-pacc-take-prefix-length-l
         (n (nfix (- (len (fn-pacc-stored-payload art inj)) (len art))))
         (x (fn-pacc-stored-payload art inj))))))))

(local
 (defthm fn-pacc-splice-prefix-is-within-the-budget-l
 (implies (and (fn-pacc-injectionp inj art)
               (equal (fn-pa-carrier-form (fn-pacc-stored-payload art inj)) :absent))
          (<= (+ *fn-record-head-max-octets* (len (mv-nth 0 (fn-pacc-splice art inj))))
              (fn-adm-acc-out-max)))
 :hints (("Goal" :cases ((equal (fn-pctx-get 0 inj)
                    (fn-inj-decide art (fn-pctx-get 5 inj) (fn-pctx-get 6 inj))))
 :in-theory (theory 'minimal-theory)
 :use (fn-pacc-direct-prefix-length-bounded-l fn-pacc-forwarded-prefix-length-bounded-l
       fn-adm-acc-out-max-holds-the-head-and-the-block fn-adm-acc-out-max-is-derived)))))

(local
 (defthm fn-pacc-group-name-length-l
 (implies (fn-record-group-namep name) (<= (len (fn-record-string-octets name)) *fn-record-max-group-name*))
 :rule-classes :linear
 :hints (("Goal" :in-theory (theory 'minimal-theory)
  :use ((:instance fn-record-group-namep-bounds-length-by-definition (text name)))))))

(local
 (defthm fn-pacc-group-ceiling-within-count-l
 (implies (fn-record-group-listp groups)
  (<= (fn-record-groups-octets-ceiling groups) (+ 3 (* (+ 3 *fn-record-max-group-name*) (len groups)))))
 :hints (("Goal" :induct (len groups)
 :in-theory (e/d (fn-record-group-listp fn-record-groups-octets-ceiling)
               (fn-record-group-namep fn-record-string-octets))))))

(local
 (defthm fn-pacc-record-gsec-fits-u32-l
 (implies (fn-record-p rec) (< (len (fn-record-groups-octets rec)) (expt 2 32)))
 :hints (("Goal" :in-theory (e/d (fn-record-p fn-record-shapep fn-record-groups-validp fn-record-groupsp)
  (fn-pacc-group-ceiling-within-count-l fn-record-group-listp fn-record-no-duplicatesp fn-record-groups-octets-ceiling fn-record-groups))
 :use ((:instance fn-pacc-group-ceiling-within-count-l (groups (fn-record-groups rec)))
       (:instance fn-record-groups-octets-bound (record rec)))))))

(local
 (defthm fn-pacc-lines-octets-true-list-l
 (true-listp (o1s-octets ls))
 :hints (("Goal" :in-theory (enable o1s-octets)))))

(local
 (defthm fn-pacc-take-octets-true-list-l
 (true-listp (fn-inj-take-n n x))
 :hints (("Goal" :in-theory (enable fn-inj-take-n)))))

(local
 (defthm fn-pacc-path-insert-true-list-l
 (true-listp (fn-inj-path-insert agent))
 :hints (("Goal" :in-theory (enable fn-inj-path-insert o1s-inj-append)))))

(local
 (defthm fn-pacc-splice-prefix-true-list-l
 (implies (fn-pacc-injectionp inj art)
          (true-listp (mv-nth 0 (fn-pacc-splice art inj))))
 :hints (("Goal" :cases ((equal (fn-pctx-get 0 inj) (fn-inj-decide art (fn-pctx-get 5 inj) (fn-pctx-get 6 inj))))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-direct-splice-is-lines-l fn-pacc-lines-octets-true-list-l))
 :use ((:instance fn-pacc-take-octets-true-list-l
  (n (nfix (- (len (fn-pacc-stored-payload art inj)) (len art)))) (x (fn-pacc-stored-payload art inj)))))
 ("Subgoal 2" :in-theory (union-theories (theory 'minimal-theory)
       '(fn-pacc-splice mv-nth fn-pacc-take-octets-true-list-l))))))

(local
 (defthm fn-pacc-cbor-append-suffix-l
 (implies (fn-cbor-octet-listp (append a b)) (fn-cbor-octet-listp b))
 :hints (("Goal" :in-theory (enable fn-cbor-octet-listp append)))))

(local
 (defthm fn-pacc-cbor-append-prefix-l
 (implies (and (true-listp a) (fn-cbor-octet-listp (append a b))) (fn-cbor-octet-listp a))
 :hints (("Goal" :in-theory (enable fn-cbor-octet-listp append)))))

(local
 (defthm fn-pacc-record-payload-shape-l
 (implies (fn-record-p rec)
  (and (fn-cbor-octet-listp (fn-record-payload rec))
       (< (len (fn-record-payload rec)) (expt 2 32))))
 :hints (("Goal" :in-theory (e/d (fn-record-p fn-record-shapep fn-record-payloadp)
     (fn-cbor-octet-listp fn-record-payload fn-record-groups-validp fn-record-metadata-bytes-p
      fn-record-msgidp fn-record-stampp fn-record-uint64p))))))

(local
 (defthm fn-pacc-prepared-payload-shape-l
 (implies (fn-record-p (fn-pacc-prepared-record s obs art inj))
  (and (fn-cbor-octet-listp (fn-pacc-stored-payload art inj))
       (< (len (fn-pacc-stored-payload art inj)) (expt 2 32))))
 :hints (("Goal" :in-theory (theory 'minimal-theory)
 :use (fn-pacc-prepared-payload-l
       (:instance fn-pacc-record-payload-shape-l (rec (fn-pacc-prepared-record s obs art inj))))))))

(local
 (defthm fn-pacc-prepared-txid-shape-l
 (implies (fn-record-p (fn-pacc-prepared-record s obs art inj))
  (fn-record-uint64p (fn-state-next-txid (fn-node-acceptance (fn-sn-node s)))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-prepared-record))
 :use ((:instance fn-pacc-constructor-groups-l
    (msgid (fn-pctx-get 0 (fn-pacc-derived-fields s art inj)))
    (payload (fn-pacc-stored-payload art inj))
    (groups (fn-pctx-get 1 (fn-pacc-derived-fields s art inj)))
    (oid (fn-pctx-get 2 (fn-pacc-derived-fields s art inj)))
    (subject (fn-pctx-get 3 (fn-pacc-derived-fields s art inj)))
    (evidence (fn-pctx-get 4 (fn-pacc-derived-fields s art inj)))
    (charge (fn-pctx-get 5 (fn-pacc-derived-fields s art inj)))))))))

(local
 (defthm fn-pacc-splice-insert-true-list-l
 (true-listp (mv-nth 1 (fn-pacc-splice art inj)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pacc-splice mv-nth fn-pacc-path-insert-true-list-l (:executable-counterpart true-listp)))))))

(local
 (defthm fn-pacc-splice-insert-length-bounded-l
 (implies (fn-pacc-injectionp inj art)
          (<= (len (mv-nth 1 (fn-pacc-splice art inj))) (fn-adm-acc-out-max)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-splice mv-nth fn-pacc-injectionp (:executable-counterpart len)))
 :use (fn-adm-acc-out-max-is-derived
       (:instance fn-pacc-config-agent-bound-l (config (fn-pctx-get 5 inj)))
       (:instance o1s-config-agent-facts (config (fn-pctx-get 5 inj)))
       (:instance o1s-path-insert-facts (agent (fn-inj-config-agent (fn-pctx-get 5 inj)))))))))

(local
 (defthm fn-pacc-splice-parts-are-octets-l
 (implies (and (fn-pacc-injectionp inj art) (fn-cbor-octet-listp (fn-pacc-stored-payload art inj)))
  (and (fn-cbor-octet-listp (mv-nth 0 (fn-pacc-splice art inj))) (fn-cbor-octet-listp (mv-nth 1 (fn-pacc-splice art inj)))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-a0-append-assoc))
 :use (fn-pacc-stored-payload-is-one-splice fn-pacc-splice-prefix-true-list-l fn-pacc-splice-insert-true-list-l
       (:instance fn-pacc-cbor-append-prefix-l (a (mv-nth 0 (fn-pacc-splice art inj))) (b (append (take (mv-nth 2 (fn-pacc-splice art inj)) art) (mv-nth 1 (fn-pacc-splice art inj)) (nthcdr (mv-nth 2 (fn-pacc-splice art inj)) art))))
       (:instance fn-pacc-cbor-append-suffix-l (a (mv-nth 0 (fn-pacc-splice art inj))) (b (append (take (mv-nth 2 (fn-pacc-splice art inj)) art) (mv-nth 1 (fn-pacc-splice art inj)) (nthcdr (mv-nth 2 (fn-pacc-splice art inj)) art))))
       (:instance fn-pacc-cbor-append-suffix-l (a (take (mv-nth 2 (fn-pacc-splice art inj)) art)) (b (append (mv-nth 1 (fn-pacc-splice art inj)) (nthcdr (mv-nth 2 (fn-pacc-splice art inj)) art))))
       (:instance fn-pacc-cbor-append-prefix-l (a (mv-nth 1 (fn-pacc-splice art inj))) (b (nthcdr (mv-nth 2 (fn-pacc-splice art inj)) art))))))))

(local
 (defthm fn-pacc-take-drop-length-covers-source-l
 (implies (natp n) (<= (len art) (+ (len (take n art)) (len (nthcdr n art)))))
 :hints (("Goal" :induct (nthcdr n art) :in-theory (enable take nthcdr)))))

(local
 (defthm fn-pacc-splice-stored-length-covers-source-l
 (implies (fn-pacc-injectionp inj art)
          (<= (len art) (len (fn-pacc-stored-payload art inj))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
     '(fn-pacc-mod-len-append-l (:type-prescription len)))
 :use (fn-pacc-stored-payload-is-one-splice
       (:instance fn-pacc-take-drop-length-covers-source-l (n (mv-nth 2 (fn-pacc-splice art inj)))))))))

(local
 (defthm fn-pacc-splice-offset-within-source-l
 (and (natp (mv-nth 2 (fn-pacc-splice art inj)))
      (<= (mv-nth 2 (fn-pacc-splice art inj)) (len art)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pacc-splice mv-nth fn-inj-path-offset nfix natp (:type-prescription len)))
 :use ((:instance fn-pacc-path-bounds-l (x art) (bol t)))))))

(local
 (defthm fn-pacc-cbor-append-l
 (implies (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp b)) (fn-cbor-octet-listp (append a b)))
 :hints (("Goal" :in-theory (enable fn-cbor-octet-listp append)))))

(local
 (defthm fn-pacc-prepared-context-is-valid-l
 (implies (and (fn-record-p (fn-pacc-prepared-record s obs art inj)) (fn-pacc-injectionp inj art)
               (equal (fn-pa-carrier-form (fn-pacc-stored-payload art inj)) :absent))
          (fn-pctx-p (fn-pctx-of-prepared s (fn-pacc-prepared-record s obs art inj) art inj)))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'minimal-theory)
  '(nth nfix zp true-listp fn-pctx-p fn-pctx-of-prepared fn-pacc-cat-is-append-l fn-record-uint64p natp
    fn-pacc-mod-len-append-l fn-pacc-len-cons-l car-cons cdr-cons
    (:executable-counterpart fn-cbor-octet-listp) (:executable-counterpart true-listp)
    (:executable-counterpart len) (:executable-counterpart expt) (:type-prescription len)))
 :use (fn-pacc-prepared-payload-shape-l fn-pacc-prepared-txid-shape-l
       fn-pacc-splice-parts-are-octets-l fn-pacc-splice-prefix-is-within-the-budget-l
       fn-pacc-splice-insert-length-bounded-l fn-pacc-splice-offset-within-source-l
       fn-pacc-splice-stored-length-covers-source-l fn-adm-acc-out-max-holds-the-tail
       (:instance fn-pacc-record-gsec-fits-u32-l (rec (fn-pacc-prepared-record s obs art inj)))
       (:instance fn-record-pieces-are-octets (record (fn-pacc-prepared-record s obs art inj)))
       (:instance fn-record-tail-octets-bound (record (fn-pacc-prepared-record s obs art inj)))
       (:instance fn-record-head-octets-bound (record (fn-pacc-prepared-record s obs art inj)))
       (:instance fn-pacc-cbor-append-l (a (fn-record-head-octets (fn-pacc-prepared-record s obs art inj)))
                                      (b (mv-nth 0 (fn-pacc-splice art inj)))))))))
(defthm fn-pacc-lays-out-the-prepared-record
  (let* ((rec (fn-pacc-prepared-record s obs art inj))
         (ctx (fn-pctx-of-prepared s rec art inj))
         (gsec (fn-pacc-prepared-gsec rec)))
    (implies (and (fn-sn-statep s)
                  (fn-pacc-injectionp inj art)
                  (fn-pacc-profile-admitted-postp s art inj profile pcarry))
             (or (member rec *fn-sn-article-record-refusals*)
                 (and (fn-record-p rec)
                      (fn-pctx-p ctx)
                      (equal (nth 0 ctx)
                             (fn-state-next-txid (fn-node-acceptance (fn-sn-node s))))
                      (equal (nth 6 ctx) (len gsec))
                      (equal (append (nth 1 ctx) (take (nth 3 ctx) art) (nth 2 ctx)
                                     (nthcdr (nth 3 ctx) art) (nth 4 ctx) gsec (nth 5 ctx))
                             (fn-record-encode rec))))))
  :hints (("Goal" :do-not-induct t
    :in-theory (union-theories (theory 'minimal-theory)
      '(fn-pacc-prepared-record fn-pctx-of-prepared fn-pacc-prepared-gsec
        fn-pacc-profile-admitted-postp nth nfix zp car-cons cdr-cons))
    :use (fn-pacc-prepared-context-is-valid-l fn-pacc-prepared-layout-l
      (:instance fn-sn-article-record-is-a-record-or-a-named-refusal
        (msgid (fn-pctx-get 0 (fn-pacc-derived-fields s art inj)))
        (payload (fn-pacc-stored-payload art inj))
        (groups (fn-pctx-get 1 (fn-pacc-derived-fields s art inj)))
        (obligation-id (fn-pctx-get 2 (fn-pacc-derived-fields s art inj)))
        (subject (fn-pctx-get 3 (fn-pacc-derived-fields s art inj)))
        (evidence (fn-pctx-get 4 (fn-pacc-derived-fields s art inj)))
        (charge (fn-pctx-get 5 (fn-pacc-derived-fields s art inj)))))))
)

; G-BOUND: filing resolution and the configured header budget.
(local
 (defthm o1-get-headers-aux-member
  (implies (consp (fn-article-get-headers-aux fields name))
           (member-equal (car (fn-article-get-headers-aux fields name)) fields))
  :hints (("Goal" :induct (len fields) :in-theory (enable fn-article-get-headers-aux)))))

(local
 (defthm o1-field-listp-member
  (implies (and (fn-article-field-listp fields) (member-equal f fields))
           (fn-article-fieldp f))
  :hints (("Goal" :induct (len fields) :in-theory (e/d (fn-article-field-listp) (fn-article-fieldp))))))

(local
 (defthm o1-source-newsgroups-within-header
  (implies (fn-article-result-okp (fn-article-parse p))
           (<= (+ (fn-o1-octet-sum (fn-o1-source-newsgroups p)) (len (fn-o1-source-newsgroups p)))
               (+ 1 (len (fn-article-header (fn-article-result-article (fn-article-parse p)))))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (fn-o1-source-newsgroups fn-af-newsgroups-status fn-article-get-headers)
                           (fn-article-parse fn-af-newsgroups-field-value fn-article-get-headers-aux
                            fn-article-fieldp fn-article-field-listp fn-article-fields-octets
                            fn-article-fields-correspondp fn-article-header fn-article-fields
                            fn-article-result-article fn-o1-octet-sum))
           :use ((:instance fn-o1-newsgroups-names-within-the-field
                            (field (car (fn-article-get-headers-aux
                                         (fn-article-fields (fn-article-result-article (fn-article-parse p)))
                                         *fn-af-newsgroups-name*))))
                 (:instance fn-article-fields-unfolded-within-header
                            (fields (fn-article-fields (fn-article-result-article (fn-article-parse p))))
                            (field (car (fn-article-get-headers-aux
                                         (fn-article-fields (fn-article-result-article (fn-article-parse p)))
                                         *fn-af-newsgroups-name*))))
                 (:instance fn-article-successful-parse-fields-correspond (octets p))
                 (:instance fn-article-successful-parse-fields-recompose-header (octets p))
                 (:instance fn-article-successful-parse-syntax-p (octets p)))))))

(local
 (defthm fn-pacc-ascii-downcase-length-l
 (equal (len (fn-article-ascii-downcase x)) (len x))
 :hints (("Goal" :in-theory (enable fn-article-ascii-downcase)))))

(local
 (defthm fn-pacc-name-before-colon-length-l
 (<= (len (fn-article-name-before-colon x)) (len x))
 :rule-classes :linear
 :hints (("Goal" :in-theory (enable fn-article-name-before-colon)))))

(local
 (defthm fn-pacc-raw-lines-cover-first-line-l
 (implies (consp lines) (<= (len (car lines)) (len (fn-article-lines-octets lines))))
 :rule-classes :linear
 :hints (("Goal" :expand ((fn-article-lines-octets lines))
 :in-theory (e/d (fn-pacc-mod-len-append-l) (fn-article-lines-octets))))))

(local
 (defthm fn-pacc-corresponding-field-name-within-raw-l
 (implies (fn-article-field-correspondsp f)
  (<= (len (fn-article-field-name f)) (len (fn-article-lines-octets (fn-article-field-raw-lines f)))))
 :hints (("Goal" :in-theory (e/d (fn-article-field-correspondsp)
    (fn-article-plain-linesp fn-article-wsp-startsp fn-article-has-colonp fn-article-unfold-reference
     fn-article-field-name fn-article-field-raw-lines fn-article-field-unfolded-value
     fn-article-name-before-colon fn-article-ascii-downcase fn-article-lines-octets))
 :use ((:instance fn-pacc-ascii-downcase-length-l
         (x (fn-article-name-before-colon (car (fn-article-field-raw-lines f)))))
       (:instance fn-pacc-name-before-colon-length-l (x (car (fn-article-field-raw-lines f))))
       (:instance fn-pacc-raw-lines-cover-first-line-l (lines (fn-article-field-raw-lines f))))))))

(local
 (defun fn-pacc-required-field-weight-l (f)
 (declare (xargs :guard t :verify-guards nil))
 (let ((name (fn-article-field-name f)))
  (cond ((equal name *fn-inj-from-name*) (len *fn-inj-from-name*))
        ((equal name *fn-inj-subject-name*) (len *fn-inj-subject-name*))
        ((equal name *fn-af-newsgroups-name*) (len *fn-af-newsgroups-name*))
        (t 0)))))

(local
 (defun fn-pacc-header-required-weight-l (fs)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp fs) (+ (fn-pacc-required-field-weight-l (car fs)) (fn-pacc-header-required-weight-l (cdr fs))) 0)))

(local
 (defthm fn-pacc-required-field-weight-within-name-l
 (<= (fn-pacc-required-field-weight-l f) (len (fn-article-field-name f)))
 :rule-classes :linear
 :hints (("Goal" :in-theory (enable fn-pacc-required-field-weight-l)))))

(local
 (defthm fn-pacc-required-weight-within-header-l
 (implies (fn-article-fields-correspondp fs)
  (<= (fn-pacc-header-required-weight-l fs) (len (fn-article-fields-octets fs))))
 :hints (("Goal" :induct (len fs)
 :in-theory (e/d (fn-article-fields-correspondp fn-article-fields-octets fn-pacc-header-required-weight-l)
   (fn-article-field-name fn-article-field-raw-lines fn-article-field-correspondsp fn-pacc-required-field-weight-l fn-article-lines-octets)))
 ("Subgoal *1/1" :use ((:instance fn-pacc-corresponding-field-name-within-raw-l (f (car fs)))
       (:instance fn-pacc-required-field-weight-within-name-l (f (car fs))))))))

(local
 (defthm fn-pacc-required-headers-cover-their-name-weights-l
 (<= (+ (if (consp (fn-article-get-headers-aux fs *fn-inj-from-name*)) (len *fn-inj-from-name*) 0)
        (if (consp (fn-article-get-headers-aux fs *fn-inj-subject-name*)) (len *fn-inj-subject-name*) 0)
        (if (consp (fn-article-get-headers-aux fs *fn-af-newsgroups-name*)) (len *fn-af-newsgroups-name*) 0))
     (fn-pacc-header-required-weight-l fs))
 :hints (("Goal" :induct (len fs)
  :in-theory (e/d (fn-pacc-header-required-weight-l fn-pacc-required-field-weight-l
                  fn-article-get-headers-aux fn-article-field-name-equalp)
                 (fn-article-field-name))))))

(local
 (defthm fn-pacc-headers-are-proper-l
 (true-listp (fn-article-get-headers-aux fs name))
 :hints (("Goal" :in-theory (enable fn-article-get-headers-aux)))))

(local
 (defthm fn-pacc-injected-required-headers-l
 (implies (fn-inj-injectedp (fn-inj-decide source config obs))
   (let ((parsed (fn-article-result-article (fn-article-parse source))))
    (and (consp (fn-article-get-headers parsed *fn-inj-from-name*))
         (consp (fn-article-get-headers parsed *fn-inj-subject-name*))
         (consp (fn-article-get-headers parsed *fn-af-newsgroups-name*)))))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-inj-decide fn-inj-injectedp fn-inj-refuse fn-inj-proto-reason
     fn-inj-single-fieldp fn-inj-mandatory-reason fn-inj-other-reason fn-inj-absentp fn-article-get-headers
     fn-pacc-headers-are-proper-l (:type-prescription fn-article-get-headers-aux)
     fn-af-proto-article-check fn-af-relayed-article-check fn-af-newsgroups-status
     fn-af-status-kind fn-af-status-value fn-af-status-field
     fn-inj-nth fn-inj-car fn-inj-cdr nfix zp car-cons cdr-cons
     fn-inj-decision-status-of-fn-inj-make-decision))))))

(local
 (defthm fn-pacc-injected-header-budget-covers-control-name-l
 (implies (fn-inj-injectedp (fn-inj-decide source config obs))
          (<= 21 (fn-article-limit-octets (fn-inj-config-header-limits config))))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'minimal-theory)
  '(fn-article-get-headers fn-article-successful-parse-fields-recompose-header
    (:executable-counterpart len)))
 :use (fn-pacc-injection-source-admitted-l fn-pacc-injection-census-l
       fn-pacc-injected-required-headers-l
       (:instance fn-pacc-required-headers-cover-their-name-weights-l (fs (fn-article-fields (fn-article-result-article (fn-article-parse source)))))
       (:instance fn-pacc-required-weight-within-header-l (fs (fn-article-fields (fn-article-result-article (fn-article-parse source)))))
       (:instance fn-article-successful-parse-fields-correspond (octets source))
       (:instance fn-article-parse-agrees-with-parse-under (octets source)
          (limits (fn-inj-config-header-limits config)))
       (:instance fn-article-parse-under-header-within-the-limit (octets source)
          (limits (fn-inj-config-header-limits config))))))))

(local
 (defthm fn-pacc-octet-string-conversion-does-not-grow-l
 (<= (len (fn-record-string-octets (fn-record-octets-string xs))) (len xs))
 :rule-classes :linear
 :hints (("Goal" :cases ((fn-cbor-octet-listp xs))
 :in-theory (e/d (fn-record-octets-string) (fn-record-octets-chars fn-record-string-octets fn-cbor-octet-listp))
 :use ((:instance fn-record-string-octets-of-octets-string (octets xs)))))))

(local
 (defthm fn-pacc-derived-names-shape-l
 (and (true-listp (fn-pacc-derived-names xs))
      (not (member-equal nil (fn-pacc-derived-names xs)))
      (equal (len (fn-pacc-derived-names xs)) (len xs)))
 :hints (("Goal" :induct (len xs)
 :in-theory (e/d (fn-pacc-derived-names) (fn-record-octets-string))))))

(local
 (defthm fn-pacc-derived-group-ceiling-l
 (<= (fn-record-groups-octets-ceiling (fn-pacc-derived-names xs))
     (+ 3 (* 3 (len xs)) (fn-o1-octet-sum xs)))
 :hints (("Goal" :induct (len xs)
 :in-theory (e/d (fn-record-groups-octets-ceiling fn-pacc-derived-names fn-o1-octet-sum)
                (fn-record-string-octets fn-record-octets-string))))))

(local
 (defthm fn-pacc-bad-codes-cannot-produce-a-positive-group-count-l
 (equal (fn-store-groups-from-codes :bad domain) :bad)
 :hints (("Goal" :in-theory (enable fn-store-groups-from-codes)))))

(local
 (defthm fn-pacc-bad-names-cannot-produce-a-positive-group-count-l
 (equal (fn-store-codes-from-groups :bad domain) :bad)
 :hints (("Goal" :in-theory (enable fn-store-codes-from-groups)))))

(local
 (defthm fn-pacc-filing-resolution-is-the-derived-names-l
 (let* ((names (if (equal (fn-pctx-get 0 filing) :file)
                   (fn-pacc-derived-names (fn-pctx-get 1 filing)) :bad))
        (codes (fn-store-codes-from-groups names domain))
        (groups (fn-store-groups-from-codes codes domain)))
  (implies (posp (len groups))
   (and (equal (fn-pctx-get 0 filing) :file)
        (equal groups (fn-pacc-derived-names (fn-pctx-get 1 filing))))))
 :hints (("Goal" :do-not-induct t
 :cases ((equal (fn-store-codes-from-groups
  (if (equal (fn-pctx-get 0 filing) :file) (fn-pacc-derived-names (fn-pctx-get 1 filing)) :bad) domain) :bad))
 :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pacc-bad-codes-cannot-produce-a-positive-group-count-l
     fn-pacc-bad-names-cannot-produce-a-positive-group-count-l (:executable-counterpart len) posp))
 :use ((:instance fn-store-codes-from-groups-inverts
          (names (fn-pacc-derived-names (fn-pctx-get 1 filing))) (groups domain))
       (:instance fn-pacc-derived-names-shape-l (xs (fn-pctx-get 1 filing))))))))

(local
 (defthm fn-pacc-profile-admission-bounds-the-groups-l
 (implies (fn-pacc-profile-admitted-postp s art inj profile pcarry)
  (and (posp (len (fn-pctx-get 1 (fn-pacc-derived-fields s art inj))))
       (<= (len (fn-pctx-get 1 (fn-pacc-derived-fields s art inj)))
           (fn-bs-profile-max-groups-per-article profile))))
 :hints (("Goal" :in-theory
   (union-theories (theory 'minimal-theory)
    '(fn-pacc-profile-admitted-postp fn-sbud-post-boundary fn-sbud-group-bound fn-bs-profile-max-groups-per-article))
 :use ((:instance fn-pvc-post-boundary-carried-is-sbud-post-boundary
    (carry pcarry) (msgid (fn-inj-decision-msgid (fn-pctx-get 0 inj)))
    (payload-length (len (fn-pacc-stored-payload art inj)))
    (group-count (len (fn-pctx-get 1 (fn-pacc-derived-fields s art inj))))
    (charge (fn-pctx-get 5 (fn-pacc-derived-fields s art inj)))))))))

(local
 (defthm fn-pacc-injected-groups-within-header-budget-l
 (implies (fn-inj-injectedp (fn-inj-decide source config obs))
  (<= (+ (fn-o1-octet-sum (fn-inj-decision-groups (fn-inj-decide source config obs)))
         (len (fn-inj-decision-groups (fn-inj-decide source config obs))))
      (+ 1 (fn-article-limit-octets (fn-inj-config-header-limits config)))))
 :hints (("Goal" :do-not-induct t
 :in-theory (theory 'minimal-theory)
 :use (fn-pacc-injection-census-l fn-pacc-injection-source-admitted-l
       fn-pacc-injection-groups-are-source-groups-l
       (:instance o1-source-newsgroups-within-header (p source))
       (:instance fn-article-parse-agrees-with-parse-under (octets source)
          (limits (fn-inj-config-header-limits config)))
       (:instance fn-article-parse-under-header-within-the-limit (octets source)
          (limits (fn-inj-config-header-limits config))))))))

(local
 (defthm fn-pacc-control-filing-name-length-l
 (<= (len (fn-record-string-octets (fn-ctl-filing-group verb))) 19)
 :hints (("Goal" :in-theory (enable fn-ctl-filing-group)))))

(local
 (defthm fn-pacc-filing-groups-ceiling-within-source-budget-l
 (implies (and (fn-inj-injectedp (fn-inj-decide source config obs))
               (equal (car (fn-pa-filing-plan received (fn-inj-decision-groups (fn-inj-decide source config obs)) domain)) :file)
               (posp (len (fn-pacc-derived-names (cadr (fn-pa-filing-plan received (fn-inj-decision-groups (fn-inj-decide source config obs)) domain))))))
  (<= (fn-record-groups-octets-ceiling (fn-pacc-derived-names (cadr (fn-pa-filing-plan received (fn-inj-decision-groups (fn-inj-decide source config obs)) domain))))
      (+ 3 (* 3 (len (fn-pacc-derived-names (cadr (fn-pa-filing-plan received (fn-inj-decision-groups (fn-inj-decide source config obs)) domain)))))
           (fn-article-limit-octets (fn-inj-config-header-limits config)))))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pa-filing-plan fn-o1-octet-sum fn-pacc-derived-names-shape-l
    car-cons cdr-cons fn-pacc-len-cons-l (:executable-counterpart len)
    (:executable-counterpart fn-o1-octet-sum) posp))
 :use (fn-pacc-injected-groups-within-header-budget-l
       fn-pacc-injected-header-budget-covers-control-name-l
       (:instance fn-pacc-derived-group-ceiling-l (xs (cadr (fn-pa-filing-plan received (fn-inj-decision-groups (fn-inj-decide source config obs)) domain))))
       (:instance fn-pacc-control-filing-name-length-l (verb (cadr (fn-ctl-classify-octets received)))))))))

(local
 (defun fn-pacc-filing-l (s art inj)
 (declare (xargs :guard t :verify-guards nil))
 (fn-apc-filing-plan (fn-pacc-stored-payload art inj) (fn-inj-decision-groups (fn-pctx-get 0 inj))
   (fn-state-groups (fn-node-acceptance (fn-sn-node s))) (fn-pctx-get 4 inj))))

(local
 (defthm fn-pacc-profile-filing-is-the-resolved-names-l
 (implies (fn-pacc-profile-admitted-postp s art inj profile pcarry)
  (and (equal (fn-pctx-get 0 (fn-pacc-filing-l s art inj)) :file)
       (equal (fn-pctx-get 1 (fn-pacc-derived-fields s art inj))
              (fn-pacc-derived-names (fn-pctx-get 1 (fn-pacc-filing-l s art inj))))))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pacc-derived-fields fn-pacc-filing-l fn-pctx-get nfix zp car-cons cdr-cons))
 :use (fn-pacc-profile-admission-bounds-the-groups-l
       (:instance fn-pacc-filing-resolution-is-the-derived-names-l
        (filing (fn-pacc-filing-l s art inj))
        (domain (fn-state-groups (fn-node-acceptance (fn-sn-node s))))))))))

(local
 (defthm fn-pacc-prepared-groups-are-derived-l
 (implies (fn-record-p (fn-pacc-prepared-record s obs art inj))
  (equal (fn-record-groups (fn-pacc-prepared-record s obs art inj))
         (fn-pctx-get 1 (fn-pacc-derived-fields s art inj))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-prepared-record))
 :use ((:instance fn-pacc-constructor-groups-l
    (msgid (fn-pctx-get 0 (fn-pacc-derived-fields s art inj)))
    (payload (fn-pacc-stored-payload art inj))
    (groups (fn-pctx-get 1 (fn-pacc-derived-fields s art inj)))
    (oid (fn-pctx-get 2 (fn-pacc-derived-fields s art inj)))
    (subject (fn-pctx-get 3 (fn-pacc-derived-fields s art inj)))
    (evidence (fn-pctx-get 4 (fn-pacc-derived-fields s art inj)))
    (charge (fn-pctx-get 5 (fn-pacc-derived-fields s art inj)))))))))

(local
 (defthm fn-pacc-get-zero-is-car-l
 (equal (fn-pctx-get 0 x) (car x))
 :hints (("Goal" :in-theory (enable fn-pctx-get)))))

(local
 (defthm fn-pacc-get-one-is-cadr-l
 (equal (fn-pctx-get 1 x) (cadr x))
 :hints (("Goal" :in-theory (enable fn-pctx-get)))))

(local
 (defthm fn-pacc-prepared-gsec-within-profile-l
 (implies (and (fn-record-p (fn-pacc-prepared-record s obs art inj)) (fn-pacc-injectionp inj art)
               (fn-pacc-profile-admitted-postp s art inj profile pcarry))
  (<= (len (fn-record-groups-octets (fn-pacc-prepared-record s obs art inj)))
      (+ 3 (* 3 (fn-bs-profile-max-groups-per-article profile))
            (fn-article-limit-octets (fn-bs-profile-header-limits profile)))))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pacc-injectionp fn-pacc-profile-admitted-postp fn-pacc-filing-l
     fn-apc-filing-plan-is-reference fn-pacc-prepared-groups-are-derived-l
     fn-pacc-profile-filing-is-the-resolved-names-l
     fn-pacc-get-zero-is-car-l fn-pacc-get-one-is-cadr-l))
 :use (fn-pacc-profile-filing-is-the-resolved-names-l fn-pacc-profile-admission-bounds-the-groups-l
       (:instance fn-pacc-gate-is-injection-of-source-l (source art) (config (fn-pctx-get 5 inj)) (obs (fn-pctx-get 6 inj)))
       (:instance fn-record-groups-octets-bound (record (fn-pacc-prepared-record s obs art inj)))
       (:instance fn-pacc-filing-groups-ceiling-within-source-budget-l
        (source (fn-pacc-injection-source-l art (fn-pctx-get 5 inj) (fn-pctx-get 6 inj))) (config (fn-pctx-get 5 inj)) (obs (fn-pctx-get 6 inj))
        (received (fn-pacc-stored-payload art inj)) (domain (fn-state-groups (fn-node-acceptance (fn-sn-node s))))))))))
(defthm fn-pacc-prepared-groups-section-is-within-the-profile
  (let* ((rec (fn-pacc-prepared-record s obs art inj))
         (gsec (fn-pacc-prepared-gsec rec))
         (g (fn-bs-profile-max-groups-per-article profile))
         (h (fn-article-limit-octets (fn-bs-profile-header-limits profile))))
    (implies (and (fn-sn-statep s)
                  (fn-pacc-injectionp inj art)
                  (fn-pacc-profile-admitted-postp s art inj profile pcarry))
             (or (member rec *fn-sn-article-record-refusals*)
                 (and (fn-record-p rec)
                      (<= (len gsec) (+ 3 (* 3 g) h))))))
  :hints (("Goal" :do-not-induct t
    :in-theory (union-theories (theory 'minimal-theory)
      '(fn-pacc-prepared-record fn-pacc-prepared-gsec))
    :use (fn-pacc-prepared-gsec-within-profile-l
      (:instance fn-sn-article-record-is-a-record-or-a-named-refusal
        (msgid (fn-pctx-get 0 (fn-pacc-derived-fields s art inj)))
        (payload (fn-pacc-stored-payload art inj))
        (groups (fn-pctx-get 1 (fn-pacc-derived-fields s art inj)))
        (obligation-id (fn-pctx-get 2 (fn-pacc-derived-fields s art inj)))
        (subject (fn-pctx-get 3 (fn-pacc-derived-fields s art inj)))
        (evidence (fn-pctx-get 4 (fn-pacc-derived-fields s art inj)))
        (charge (fn-pctx-get 5 (fn-pacc-derived-fields s art inj)))))))
)
