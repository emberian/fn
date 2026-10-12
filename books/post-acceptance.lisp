; POST acceptance instance definitions and the approved A0/A3 keystones.
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
 (defthm fn-pacc-injection-decision-l
 (implies (fn-pacc-injectionp inj art)
  (and (fn-inj-configp (fn-pctx-get 5 inj))
       (equal (fn-pctx-get 0 inj) (fn-inj-decide art (fn-pctx-get 5 inj) (fn-pctx-get 6 inj)))
       (fn-inj-injectedp (fn-inj-decide art (fn-pctx-get 5 inj) (fn-pctx-get 6 inj)))))
 :hints (("Goal" :in-theory '(fn-pacc-injectionp)))))

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
 :hints (("Goal" :use ((:instance fn-pacc-injection-decision-l)
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
 (defthm fn-pacc-article-wire-shape-l
 (implies (natp (fn-record-stamp-of-observation obs))
 (and (fn-record-shapep (fn-sn-article-record s obs msgid payload groups oid subject evidence charge))
 (equal (fn-record-sequence (fn-sn-article-record s obs msgid payload groups oid subject evidence charge))
 (fn-sn-identity-next s))))
 :hints (("Goal" :in-theory (enable fn-sn-article-record)))))

(local
 (defthm fn-pacc-clock-unusable-intern-l
 (equal (fn-rcon-store-event-encode
 (fn-row-wire-of (fn-apc-intern-row-at :clock-unusable keyring generation h carry) arena)) nil)
 :hints (("Goal" :in-theory (e/d
 (fn-rcon-store-event-encode fn-apc-intern-row-at fn-row-wire-of fn-record-internals
 fn-held-internals fn-held-p fn-hstxa-p fn-rcon-record-p-is-record-p fn-record-p
 fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-stxa-p fn-stxe-internals fn-stxk-internals fn-stxa-internals fn-cpe-eventp fn-th-topic-eventp)
 (fn-store-retention-event-encode fn-stxe-encode fn-stxk-encode fn-stxa-encode fn-cpe-encode fn-th-topic-event-encode))))))

(defthm fn-pacc-stored-payload-is-one-splice
  (implies (fn-pacc-injectionp inj art)
           (mv-let (p0 ins ioff) (fn-pacc-splice art inj)
             (and (natp ioff) (<= ioff (len art))
                  (equal (fn-pacc-stored-payload art inj)
                         (append p0 (take ioff art) ins (nthcdr ioff art))))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-pacc-injection-requires-octets-l)
       (:instance fn-ipp-injected-octets-carry-the-parameters
       (source art) (config (fn-pctx-get 5 inj)) (obs (fn-pctx-get 6 inj))
       (secret (fn-pctx-get 1 inj)) (login (fn-pctx-get 2 inj)) (cfg (fn-pctx-get 3 inj)))
       (:instance fn-pacc-injection-decision-l)
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
        fn-rcon-record-p-is-record-p fn-pacc-encoded-intern-materializes-l fn-pacc-state-identity-next-l fn-pacc-article-wire-shape-l fn-pacc-clock-unusable-intern-l fn-record-encode-domain fn-sn-article-record fn-record-shapep fn-record-sequence fn-record-make (:executable-counterpart fn-record-p)
        fn-pacc-state-generation-l fn-pacc-injection-carry-l)))))

