; fn: what the Injection-Info parameters do to an injected article
; (PKT-597; the definitions are books/injection-info-params.lisp).
;
; Proved here, over fn-ipp-with-params (called by fn-ipp-stored-octets,
; which books/owner-served-invariants.lisp fn-own-sub-stored-octets-keyed
; calls for every local submission the owner stages; host/owner-host.lisp
; fn-owner-take stages that value and fn-owner-finish-submission compares
; the completed record with it):
;   * `fn-ipp-with-params-of-an-injection': with parameters, an injected
;     article is its injected block with the Injection-Info line carrying
;     them, followed by the source (the same block, the same place, the same
;     source octets): exactly one Injection-Info, since the proto-article
;     check refuses a source that carries one (books/article-fields.lisp
;     fn-af-proto-article-check, :injection-info).
;   * `fn-ipp-with-params-keeps-the-source': the injection inverse still
;     gives back the source (books/injection.lisp fn-inj-source-of reads
;     the line through fn-inj-strip-info), so D25's comparison and the
;     operator's retry test treat the article with parameters as the one
;     without.
;   * `fn-ipp-params-of-a-login' and `fn-ipp-params-without-a-login': the
;     parameters under a key and a login open with the posting-account
;     value of that login, and without a login they carry none.

(in-package "ACL2")
(include-book "injection-info-params")
(include-book "poster-bytes-invariants")

(local
 (defthm fn-ipp-inj-append-is-append
   (equal (fn-inj-append a b) (append a b))
   :hints (("Goal" :in-theory (enable fn-inj-append)))))

(local
 (defthm fn-ipp-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

; The prefix and block of books/injection.lisp with the parameter line.
(defun fn-ipp-block-with (date msgid agent generate-id generate-date params)
  (declare (xargs :guard t))
  (fn-inj-append
   (if (or generate-id generate-date) (fn-inj-injection-date-line date) nil)
   (fn-inj-append
    (if generate-id (fn-inj-message-id-line msgid) nil)
    (fn-inj-append
     (if generate-date (fn-inj-date-line date) nil)
     (fn-inj-injection-info-line-with agent params)))))

(defun fn-ipp-prefix-with (date msgid agent generate-id generate-date params)
  (declare (xargs :guard t))
  (fn-inj-append (fn-inj-path-line agent)
                 (fn-ipp-block-with date msgid agent generate-id generate-date
                                    params)))

; A parameter run the inverse reads past: it opens with ";" and has no CR
; or LF.
(defun fn-ipp-no-crlfp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (not (equal (car x) 13)) (not (equal (car x) 10))
           (fn-ipp-no-crlfp (cdr x)))
    t))

(defun fn-ipp-params-okp (params)
  (declare (xargs :guard t))
  (and (consp params) (equal (car params) 59) (true-listp params)
       (fn-ipp-no-crlfp params)))

; -----------------------------------------------------------------------------
; List facts about the injected lines.

(local
 (defthm fn-ipp-strip-of-append-left
   (implies (true-listp a)
            (equal (fn-inj-strip a (append a b)) b))
   :hints (("Goal" :in-theory (enable fn-inj-strip)))))

(local
 (defthm fn-ipp-strip-of-a-different-first-octet
   (implies (and (consp a) (consp b) (not (equal (car a) (car b))))
            (equal (fn-inj-strip a (append b x)) :no))
   :hints (("Goal" :in-theory (enable fn-inj-strip)))))

(local
 (defthm fn-ipp-take-of-append
   (implies (and (true-listp a) (equal n (len a)))
            (equal (fn-inj-take n (append a b)) a))
   :hints (("Goal" :in-theory (enable fn-inj-take)))))

(local
 (defthm fn-ipp-drop-of-append
   (implies (and (true-listp a) (equal n (len a)))
            (equal (fn-inj-drop n (append a b)) b))
   :hints (("Goal" :in-theory (enable fn-inj-drop)))))

(local
 (defthm fn-ipp-lines-shape
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
 (defthm fn-ipp-len-of-the-dated-lines
   (implies (equal (len date) 31)
            (and (equal (len (fn-inj-injection-date-line date)) 49)
                 (equal (len (fn-inj-date-line date)) 39)))
   :hints (("Goal" :in-theory (enable fn-inj-injection-date-line fn-inj-date-line)))))

; Which field a line opens with, as the walk asks it.
(local
 (defthm fn-ipp-opens-of-the-lines
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

(local (in-theory (disable fn-pb-opensp fn-inj-path-line fn-inj-injection-date-line
                           fn-inj-injection-info-line fn-inj-injection-info-line-with
                           fn-inj-message-id-line fn-inj-date-line)))

; -----------------------------------------------------------------------------
; The walk over the injected block.

(local
 (defthm fn-ipp-at-stamp-of-a-block
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
 (defthm fn-ipp-a-block-is-not-a-path-line
   (equal (fn-inj-strip (fn-inj-path-line agent)
                        (append (fn-inj-block date msgid agent2 gid gdate) x))
          :no)
   :hints (("Goal" :in-theory (enable fn-inj-block)
            :cases ((or gid gdate))))))

(local
 (defthm fn-ipp-prefix-is-the-path-line-and-the-block
   (equal (append (fn-inj-prefix date msgid agent gid gdate) x)
          (append (fn-inj-path-line agent)
                  (append (fn-inj-block date msgid agent gid gdate) x)))
   :hints (("Goal" :in-theory (enable fn-inj-prefix fn-inj-block)))))

; -----------------------------------------------------------------------------
; The rewrite of an injection.

(local
 (defthm fn-ipp-with-params-of-a-prefix
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
 (defthm fn-ipp-with-params-of-a-block
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
 (defthm fn-ipp-with-params-of-a-prefix-x
   (implies (and (equal x (append (fn-inj-prefix date msgid agent gid gdate) source))
                 (true-listp date) (equal (len date) 31) (consp params) agent
                 (not (equal source :no))
                 (equal (fn-pb-path-agent x msgid) agent))
            (equal (fn-ipp-with-params x msgid params)
                   (append (fn-ipp-prefix-with date msgid agent gid gdate params)
                           source)))
   :rule-classes nil
   :hints (("Goal" :use fn-ipp-with-params-of-a-prefix
            :in-theory (disable fn-ipp-with-params-of-a-prefix fn-ipp-with-params
                                fn-inj-prefix fn-ipp-prefix-with fn-pb-path-agent)))))

(local
 (defthm fn-ipp-with-params-of-a-block-x
   (implies (and (equal x (append (fn-inj-block date msgid agent gid gdate) rest))
                 (true-listp date) (equal (len date) 31) (consp params) agent
                 (not (equal rest :no))
                 (equal (fn-pb-path-agent x msgid) agent))
            (equal (fn-ipp-with-params x msgid params)
                   (append (fn-ipp-block-with date msgid agent gid gdate params)
                           rest)))
   :rule-classes nil
   :hints (("Goal" :use fn-ipp-with-params-of-a-block
            :in-theory (disable fn-ipp-with-params-of-a-block fn-ipp-with-params
                                fn-inj-block fn-ipp-block-with fn-pb-path-agent)))))

(local
 (defthm fn-ipp-a-configured-agent-is-a-cons
   (implies (fn-inj-configp config)
            (consp (fn-inj-config-agent config)))
   :hints (("Goal" :in-theory (enable fn-inj-configp fn-af-dot-atom-textp)))))

(local
 (defthm fn-ipp-an-injection-configures-first
   (implies (fn-inj-injectedp (fn-inj-decide source config obs))
            (fn-inj-configp config))
   :hints (("Goal" :in-theory (e/d (fn-inj-decide fn-inj-injectedp fn-inj-refuse)
                                   (fn-inj-configp fn-inj-mandatory-reason
                                    fn-inj-groups-admissiblep fn-inj-absentp
                                    fn-inj-prefix fn-inj-date-octets
                                    fn-inj-instant-of fn-inj-generated-message-id
                                    fn-inj-append floor fn-article-parse
                                    fn-af-proto-article-check fn-article-result-okp
                                    fn-article-result-article fn-article-syntax-p
                                    fn-clock-observationp fn-clock-has-wall
                                    fn-clock-wall))))))

(local
 (defthm fn-ipp-date-octets-shape
   (and (true-listp (fn-inj-date-octets inst))
        (equal (len (fn-inj-date-octets inst)) 31))
   :hints (("Goal" :in-theory (enable fn-inj-date-octets)))))

; The Injection-Date of an injection, its generated-field flags, and the
; configured agent, as the structure theorems of
; books/injection-invariants.lisp name them.
(defmacro fn-ipp-date (obs)
  `(fn-inj-date-octets (fn-inj-instant-of (fn-clock-wall ,obs))))
(defmacro fn-ipp-gid (source)
  `(not (fn-inj-nth 1 (fn-af-proto-article-check
                       (fn-article-result-article (fn-article-parse ,source))))))
(defmacro fn-ipp-gdate (source)
  `(fn-inj-absentp (fn-article-result-article (fn-article-parse ,source))
                   *fn-inj-date-name*))

(local
 (defthm fn-ipp-with-params-of-an-injection-with-some
  (implies (and (fn-inj-injectedp (fn-inj-decide source config obs))
                (consp params))
           (equal (fn-ipp-with-params
                   (fn-inj-decision-octets (fn-inj-decide source config obs))
                   (fn-inj-decision-msgid (fn-inj-decide source config obs))
                   params)
                  (if (fn-inj-supplies-pathp source)
                      (append (fn-ipp-block-with
                               (fn-ipp-date obs)
                               (fn-inj-decision-msgid (fn-inj-decide source config obs))
                               (fn-inj-config-agent config)
                               (fn-ipp-gid source) (fn-ipp-gdate source) params)
                              (fn-inj-splice source (fn-inj-path-offset source)
                                             (fn-inj-path-insert
                                              (fn-inj-config-agent config))))
                    (append (fn-ipp-prefix-with
                             (fn-ipp-date obs)
                             (fn-inj-decision-msgid (fn-inj-decide source config obs))
                             (fn-inj-config-agent config)
                             (fn-ipp-gid source) (fn-ipp-gdate source) params)
                            source))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                             '(fn-ipp-inj-append-is-append))
           :cases ((fn-inj-supplies-pathp source))
           :use ((:instance fn-inj-injected-octets-are-the-block-and-the-source)
                 (:instance fn-inj-injected-octets-are-the-block-and-the-prefixed-source)
                 (:instance fn-pb-path-agent-of-an-injection)
                 (:instance fn-inj-the-atom-no-is-never-injected (observation obs))
                 (:instance fn-inj-an-injected-supplied-path-has-an-offset)
                 (:instance fn-inj-a-splice-is-a-cons (x source)
                            (ins (fn-inj-path-insert (fn-inj-config-agent config))))
                 (:instance fn-ipp-date-octets-shape
                            (inst (fn-inj-instant-of (fn-clock-wall obs))))
                 (:instance fn-ipp-an-injection-configures-first)
                 (:instance fn-ipp-a-configured-agent-is-a-cons)
                 (:instance fn-ipp-with-params-of-a-prefix-x
                            (x (fn-inj-decision-octets (fn-inj-decide source config obs)))
                            (date (fn-ipp-date obs))
                            (msgid (fn-inj-decision-msgid (fn-inj-decide source config obs)))
                            (agent (fn-inj-config-agent config))
                            (gid (fn-ipp-gid source)) (gdate (fn-ipp-gdate source)))
                 (:instance fn-ipp-with-params-of-a-block-x
                            (x (fn-inj-decision-octets (fn-inj-decide source config obs)))
                            (rest (fn-inj-splice source (fn-inj-path-offset source)
                                                 (fn-inj-path-insert
                                                  (fn-inj-config-agent config))))
                            (date (fn-ipp-date obs))
                            (msgid (fn-inj-decision-msgid (fn-inj-decide source config obs)))
                            (agent (fn-inj-config-agent config))
                            (gid (fn-ipp-gid source)) (gdate (fn-ipp-gdate source))))))))

(local
 (defthm fn-ipp-no-params-lines
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
 (defthm fn-ipp-with-no-params
   (implies (not (consp params))
            (equal (fn-ipp-with-params x msgid params) x))
   :hints (("Goal" :in-theory (enable fn-ipp-with-params)))))

; KEYSTONE (PKT-597, the Injection-Info line with parameters; subject
; fn-ipp-with-params, which fn-ipp-injected-octets calls on every local
; submission the owner stages, books/owner-served-invariants.lisp
; fn-own-sub-stored-octets).  With parameters, an injected article is the
; injected block with its closing Injection-Info line carrying them,
; followed by what followed the block before: the source (recipe v2) or
; the source with AGENT! inserted into its Path (recipe v3).  Nothing else
; moves, and the line is the article's only Injection-Info
; (fn-af-proto-article-check refuses a source that carries one).
(defthm fn-ipp-with-params-of-an-injection
  (implies (fn-inj-injectedp (fn-inj-decide source config obs))
           (equal (fn-ipp-with-params
                   (fn-inj-decision-octets (fn-inj-decide source config obs))
                   (fn-inj-decision-msgid (fn-inj-decide source config obs))
                   params)
                  (if (fn-inj-supplies-pathp source)
                      (append (fn-ipp-block-with
                               (fn-ipp-date obs)
                               (fn-inj-decision-msgid (fn-inj-decide source config obs))
                               (fn-inj-config-agent config)
                               (fn-ipp-gid source) (fn-ipp-gdate source) params)
                              (fn-inj-splice source (fn-inj-path-offset source)
                                             (fn-inj-path-insert
                                              (fn-inj-config-agent config))))
                    (append (fn-ipp-prefix-with
                             (fn-ipp-date obs)
                             (fn-inj-decision-msgid (fn-inj-decide source config obs))
                             (fn-inj-config-agent config)
                             (fn-ipp-gid source) (fn-ipp-gdate source) params)
                            source))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                             '(fn-ipp-inj-append-is-append))
           :cases ((consp params))
           :use ((:instance fn-ipp-with-params-of-an-injection-with-some)
                 (:instance fn-ipp-with-no-params
                            (x (fn-inj-decision-octets (fn-inj-decide source config obs)))
                            (msgid (fn-inj-decision-msgid (fn-inj-decide source config obs))))
                 (:instance fn-ipp-no-params-lines
                            (date (fn-ipp-date obs))
                            (msgid (fn-inj-decision-msgid (fn-inj-decide source config obs)))
                            (agent (fn-inj-config-agent config))
                            (gid (fn-ipp-gid source)) (gdate (fn-ipp-gdate source)))
                 (:instance fn-inj-injected-octets-are-the-block-and-the-source)
                 (:instance fn-inj-injected-octets-are-the-block-and-the-prefixed-source)))))

; -----------------------------------------------------------------------------
; The inverse reads past the parameters.

(local
 (defthm fn-ipp-param-rest-of-a-run
   (implies (fn-ipp-no-crlfp p)
            (equal (fn-inj-param-rest (append p (cons 13 (cons 10 r)))) r))
   :hints (("Goal" :induct (fn-ipp-no-crlfp p)
            :in-theory (enable fn-inj-param-rest)))))

(local
 (defthm fn-ipp-strip-by-an-append
   (implies (true-listp a)
            (equal (fn-inj-strip (append a b) x)
                   (fn-inj-strip b (fn-inj-strip a x))))
   :hints (("Goal" :in-theory (enable fn-inj-strip)))))

(local
 (defthm fn-ipp-true-listp-of-inj-append
   (equal (true-listp (fn-inj-append a b)) (true-listp b))
   :hints (("Goal" :in-theory (enable fn-inj-append)))))

(local
 (defthm fn-ipp-info-lines-as-head
   (and (equal (fn-inj-injection-info-line agent)
               (append (fn-inj-append *fn-inj-injection-info-field* agent) '(13 10)))
        (equal (fn-inj-injection-info-line-with agent params)
               (append (fn-inj-append *fn-inj-injection-info-field* agent)
                       (append params '(13 10)))))
   :hints (("Goal" :in-theory (enable fn-inj-injection-info-line
                                      fn-inj-injection-info-line-with)))))

(local
 (defthm fn-ipp-strip-a-parameter-run
   (implies (and (true-listp h) (consp params) (equal (car params) 59))
            (and (equal (fn-inj-strip (append h '(13 10))
                                      (append h (append params y)))
                        :no)
                 (equal (fn-inj-strip h (append h (append params y)))
                        (append params y))))
   :hints (("Goal" :in-theory (disable fn-ipp-inj-append-is-append)))))

(local
 (defthm fn-ipp-strip-info-of-a-parameter-line
   (implies (and (fn-ipp-params-okp params) (true-listp agent))
            (equal (fn-inj-strip-info agent
                                      (append (fn-inj-injection-info-line-with
                                               agent params)
                                              r))
                   r))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-inj-strip-info)
                            (fn-ipp-inj-append-is-append
                             fn-inj-injection-info-line
                             fn-inj-injection-info-line-with))))))

(local (in-theory (disable fn-ipp-info-lines-as-head)))

(local
 (defthm fn-ipp-strip-info-of-another-line
   (implies (and (consp b) (not (equal (car b) 73)))
            (equal (fn-inj-strip-info agent (append b x)) :no))
   :hints (("Goal" :in-theory (enable fn-inj-strip-info fn-inj-injection-info-line)))))

(local (in-theory (disable fn-inj-strip-info)))

(local
 (defthm fn-ipp-the-stamp-date-is-read-back
   (implies (and (true-listp date) (equal (len date) 31))
            (equal (fn-inj-take 31 (fn-inj-drop 16 (append
                                                   (fn-inj-injection-date-line date)
                                                   x)))
                   date))
   :hints (("Goal" :in-theory (enable fn-inj-injection-date-line fn-inj-drop)))))

(local
 (defthm fn-ipp-stamp-field-of-the-lines
   (and (not (equal (fn-inj-strip *fn-inj-injection-date-field*
                                  (append (fn-inj-injection-date-line date) x))
                    :no))
        (equal (fn-inj-strip *fn-inj-injection-date-field*
                             (append (fn-inj-injection-info-line-with agent params) x))
               :no))
   :hints (("Goal" :in-theory (enable fn-inj-injection-date-line fn-inj-strip
                                      fn-inj-injection-info-line-with)))))

(local
 (defthm fn-ipp-source-of-v2-of-a-prefix-with
   (implies (and (true-listp date) (equal (len date) 31)
                 (true-listp agent) (fn-ipp-params-okp params)
                 (not (equal source :no)))
            (equal (fn-inj-source-of-v2
                    (append (fn-ipp-prefix-with date msgid agent gid gdate params)
                            source)
                    agent msgid)
                   (cons t source)))
   :hints (("Goal" :in-theory (e/d (fn-ipp-prefix-with fn-ipp-block-with
                                    fn-inj-source-of-v2 fn-inj-source-after-stamp
                                    fn-inj-strip-optional)
                                   ())
            :cases ((and gid gdate) (and gid (not gdate))
                    (and (not gid) gdate))))))

(local
 (defthm fn-ipp-source-of-a-prefix-with
   (implies (and (true-listp date) (equal (len date) 31)
                 (true-listp agent) (fn-ipp-params-okp params)
                 (not (equal source :no)))
            (equal (fn-inj-source-of
                    (append (fn-ipp-prefix-with date msgid agent gid gdate params)
                            source)
                    agent msgid)
                   (cons t source)))
   :hints (("Goal" :in-theory (e/d (fn-inj-source-of)
                                   (fn-inj-source-of-v2 fn-ipp-block-with))
            :use fn-ipp-source-of-v2-of-a-prefix-with
            :expand ((fn-ipp-prefix-with date msgid agent gid gdate params))))))

(local
 (defthm fn-ipp-a-block-with-is-not-a-path-line
   (equal (fn-inj-strip (fn-inj-path-line agent)
                        (append (fn-ipp-block-with date msgid agent2 gid gdate params)
                                x))
          :no)
   :hints (("Goal" :in-theory (enable fn-ipp-block-with)
            :cases ((or gid gdate))))))

(local
 (defthm fn-ipp-source-of-a-v3-record-with
   (implies (and (true-listp date) (equal (len date) 31)
                 (true-listp agent) (fn-ipp-params-okp params)
                 (fn-inj-path-offset source))
            (equal (fn-inj-source-of
                    (append (fn-ipp-block-with date msgid agent gid gdate params)
                            (fn-inj-splice source (fn-inj-path-offset source)
                                           (fn-inj-path-insert agent)))
                    agent msgid)
                   (cons t source)))
   :hints (("Goal" :in-theory (e/d (fn-inj-source-of fn-ipp-prefix-with)
                                   (fn-inj-source-of-v2 fn-ipp-block-with
                                    fn-inj-splice fn-inj-path-offset
                                    fn-inj-unsplice fn-inj-path-insert))
            :use ((:instance fn-ipp-source-of-v2-of-a-prefix-with
                             (source (fn-inj-splice source (fn-inj-path-offset source)
                                                    (fn-inj-path-insert agent))))
                  (:instance fn-inj-a-splice-is-a-cons
                             (x source) (ins (fn-inj-path-insert agent)))
                  (:instance fn-inj-unsplice-of-a-splice (x source)))))))

(local
 (defthm fn-ipp-a-configured-agent-is-a-true-list
   (implies (fn-inj-configp config)
            (true-listp (fn-inj-config-agent config)))
   :hints (("Goal" :in-theory (enable fn-inj-configp fn-af-dot-atom-textp)))))

; KEYSTONE (PKT-597, the inverse; subject fn-ipp-with-params).  The article
; with parameters gives back its source: books/injection.lisp
; fn-inj-source-of reads the Injection-Info line through fn-inj-strip-info,
; so D25's comparison (books/poster-bytes.lisp fn-pb-subject) and the
; operator's retry test (fn-inj-reinjectionp) answer for the stored article
; exactly as for the injection without parameters
; (fn-inj-source-of-inverts-the-injection).
(defthm fn-ipp-with-params-keeps-the-source
  (implies (and (fn-inj-injectedp (fn-inj-decide source config obs))
                (fn-ipp-params-okp params))
           (equal (fn-inj-source-of
                   (fn-ipp-with-params
                    (fn-inj-decision-octets (fn-inj-decide source config obs))
                    (fn-inj-decision-msgid (fn-inj-decide source config obs))
                    params)
                   (fn-inj-config-agent config)
                   (fn-inj-decision-msgid (fn-inj-decide source config obs)))
                  (cons t source)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                             '(fn-ipp-params-okp))
           :cases ((fn-inj-supplies-pathp source))
           :use ((:instance fn-ipp-with-params-of-an-injection)
                 (:instance fn-inj-the-atom-no-is-never-injected (observation obs))
                 (:instance fn-inj-an-injected-supplied-path-has-an-offset)
                 (:instance fn-ipp-date-octets-shape
                            (inst (fn-inj-instant-of (fn-clock-wall obs))))
                 (:instance fn-ipp-an-injection-configures-first)
                 (:instance fn-ipp-a-configured-agent-is-a-true-list)
                 (:instance fn-ipp-source-of-a-prefix-with
                            (date (fn-ipp-date obs))
                            (msgid (fn-inj-decision-msgid (fn-inj-decide source config obs)))
                            (agent (fn-inj-config-agent config))
                            (gid (fn-ipp-gid source)) (gdate (fn-ipp-gdate source)))
                 (:instance fn-ipp-source-of-a-v3-record-with
                            (date (fn-ipp-date obs))
                            (msgid (fn-inj-decision-msgid (fn-inj-decide source config obs)))
                            (agent (fn-inj-config-agent config))
                            (gid (fn-ipp-gid source)) (gdate (fn-ipp-gdate source)))))))

; -----------------------------------------------------------------------------
; The parameters.

(local
 (defthm fn-ipp-no-crlfp-of-append
   (equal (fn-ipp-no-crlfp (append a b))
          (and (fn-ipp-no-crlfp a) (fn-ipp-no-crlfp b)))))

(local
 (defthm fn-ipp-no-crlfp-of-hex
   (implies (fn-pa-hex-octetsp x) (fn-ipp-no-crlfp x))
   :hints (("Goal" :in-theory (enable fn-pa-hex-octetsp fn-pa-hex-octetp)))))

(local
 (defthm fn-ipp-no-crlfp-without-cr-or-lf
   (implies (and (not (member-equal 13 x)) (not (member-equal 10 x)))
            (fn-ipp-no-crlfp x))))

(local
 (defthm fn-ipp-complaints-is-an-addr-spec
   (implies (fn-ipp-complaints cfg)
            (fn-ipp-addr-specp (fn-ipp-complaints cfg)))))

; With a node secret and a login, the parameters open with the
; posting-account value of that login: `; posting-account="' HEX `"', HEX
; the 64 hexadecimal digits of fn-ns-posting-account-mac of the login's
; octets (books/posting-account.lisp fn-pa-account-value-is-hex), then the
; complaints address when one is set.
(defthm fn-ipp-params-of-a-login
  (implies (fn-ipp-accountp secret login)
           (equal (fn-ipp-params secret login addr)
                  (append *fn-ipp-account-open*
                          (fn-pa-account-value secret (fn-ipp-octets login))
                          *fn-ipp-quote*
                          (if (consp addr) (fn-ipp-complaints-param addr) nil))))
  :hints (("Goal" :in-theory (enable fn-ipp-params fn-ipp-account-param))))

; Without a login (or before the secret is installed) no posting-account is
; written: the parameters are the complaints address or nothing.
(defthm fn-ipp-params-without-a-login
  (implies (not (fn-ipp-accountp secret login))
           (equal (fn-ipp-params secret login addr)
                  (if (consp addr) (fn-ipp-complaints-param addr) nil)))
  :hints (("Goal" :in-theory (enable fn-ipp-params))))

; The parameters the owner writes are a run the inverse reads past.
(local
 (defthm fn-ipp-params-are-a-run-for-an-address
   (implies (and (or (not addr) (fn-ipp-addr-specp addr))
                 (consp (fn-ipp-params secret login addr)))
            (fn-ipp-params-okp (fn-ipp-params secret login addr)))
   :hints (("Goal" :in-theory (e/d (fn-ipp-params fn-ipp-account-param
                                    fn-ipp-complaints-param)
                                   (fn-ipp-addr-specp fn-pa-account-value
                                    fn-ipp-accountp fn-ipp-octets))))))

(defthm fn-ipp-params-are-a-parameter-run
  (implies (consp (fn-ipp-params secret login (fn-ipp-complaints cfg)))
           (fn-ipp-params-okp (fn-ipp-params secret login (fn-ipp-complaints cfg))))
  :hints (("Goal" :in-theory (disable fn-ipp-params fn-ipp-complaints fn-ipp-params-okp
                                      fn-ipp-addr-specp)
           :use ((:instance fn-ipp-params-are-a-run-for-an-address
                            (addr (fn-ipp-complaints cfg)))
                 (:instance fn-ipp-complaints-is-an-addr-spec)))))

(defthm fn-ipp-a-login-has-parameters
  (implies (fn-ipp-accountp secret login)
           (consp (fn-ipp-params secret login addr)))
  :hints (("Goal" :in-theory (enable fn-ipp-params fn-ipp-account-param))))

; KEYSTONE (PKT-597 (1); subject fn-ipp-injected-octets, which
; books/owner-served-invariants.lisp fn-own-sub-stored-octets calls with the
; submission's login, the owner's node secret and the live configuration).
; The stored injection is the injected block with its one Injection-Info
; line carrying the parameters, followed by the source, and the article
; still gives back its source.  Under a login with the node secret installed
; the parameters open with that login's posting-account value
; (fn-ipp-params-of-a-login); with neither a login nor a complaints address
; there are none and the line is the plain one
; (fn-ipp-injected-octets-without-parameters, fn-ipp-params-without-a-login).
(defthm fn-ipp-injected-octets-carry-the-parameters
  (let ((d (fn-inj-decide source config obs))
        (params (fn-ipp-params secret login (fn-ipp-complaints cfg))))
    (implies (fn-inj-injectedp d)
             (and (equal (fn-ipp-injected-octets d secret login cfg)
                         (if (fn-inj-supplies-pathp source)
                             (append (fn-ipp-block-with
                                      (fn-ipp-date obs) (fn-inj-decision-msgid d)
                                      (fn-inj-config-agent config)
                                      (fn-ipp-gid source) (fn-ipp-gdate source)
                                      params)
                                     (fn-inj-splice source (fn-inj-path-offset source)
                                                    (fn-inj-path-insert
                                                     (fn-inj-config-agent config))))
                           (append (fn-ipp-prefix-with
                                    (fn-ipp-date obs) (fn-inj-decision-msgid d)
                                    (fn-inj-config-agent config)
                                    (fn-ipp-gid source) (fn-ipp-gdate source)
                                    params)
                                   source)))
                  (equal (fn-inj-source-of (fn-ipp-injected-octets d secret login cfg)
                                           (fn-inj-config-agent config)
                                           (fn-inj-decision-msgid d))
                         (cons t source)))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                             '(fn-ipp-injected-octets))
           :cases ((consp (fn-ipp-params secret login (fn-ipp-complaints cfg))))
           :use ((:instance fn-ipp-params-are-a-parameter-run)
                 (:instance fn-ipp-with-params-of-an-injection
                            (params (fn-ipp-params secret login (fn-ipp-complaints cfg))))
                 (:instance fn-ipp-with-params-keeps-the-source
                            (params (fn-ipp-params secret login
                                                   (fn-ipp-complaints cfg))))
                 (:instance fn-ipp-with-no-params
                            (x (fn-inj-decision-octets (fn-inj-decide source config obs)))
                            (msgid (fn-inj-decision-msgid (fn-inj-decide source config obs)))
                            (params (fn-ipp-params secret login (fn-ipp-complaints cfg))))
                 (:instance fn-inj-source-of-inverts-the-injection
                            (observation obs))))))

; -----------------------------------------------------------------------------
; D25: the Injection-Info parameters are outside the authored-source identity.

; Neither an injection nor its stored form with parameters opens with "C":
; they open with this agent's Path line or with "Injection-" (so
; books/cancel-lock-lines.lisp fn-cll-skip leaves them as they are).
(local
 (defthm fn-ipp-lines-open-with
   (and (equal (car (append (fn-inj-path-line agent) x)) 80)
        (equal (car (append (fn-ipp-block-with date msgid agent gid gdate params) x)) 73)
        (equal (car (append (fn-inj-block date msgid agent gid gdate) x)) 73))
   :hints (("Goal" :in-theory (enable fn-inj-path-line fn-ipp-block-with fn-inj-block
                                      fn-inj-injection-date-line fn-inj-message-id-line
                                      fn-inj-date-line fn-inj-injection-info-line
                                      fn-inj-injection-info-line-with)
            :cases ((or gid gdate))))))

(defthm fn-ipp-an-injection-does-not-open-with-c
  (let ((d (fn-inj-decide source config obs)))
    (implies (fn-inj-injectedp d)
             (and (not (equal (car (fn-ipp-injected-octets d secret login cfg)) 67))
                  (not (equal (car (fn-inj-decision-octets d)) 67)))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                             '(fn-ipp-lines-open-with fn-ipp-prefix-with
                                               fn-ipp-inj-append-is-append
                                               fn-ipp-append-assoc))
           :cases ((fn-inj-supplies-pathp source))
           :use ((:instance fn-ipp-injected-octets-carry-the-parameters)
                 (:instance fn-inj-injected-octets-are-the-block-and-the-source)
                 (:instance fn-inj-injected-octets-are-the-block-and-the-prefixed-source)
                 (:instance fn-ipp-prefix-is-the-path-line-and-the-block
                            (date (fn-ipp-date obs))
                            (msgid (fn-inj-decision-msgid (fn-inj-decide source config obs)))
                            (agent (fn-inj-config-agent config))
                            (gid (fn-ipp-gid source)) (gdate (fn-ipp-gdate source))
                            (x source))))))

; KEYSTONE (D25 with parameters; subject books/poster-bytes.lisp
; fn-pb-subject, the comparison subject fn-pb-same-articlep reads for the
; Store's duplicate test, which host/owner-host.lisp fn-owner-existing-action-
; buffer runs through the buffer twin fn-pbb-existing-action).  The stored
; octets of an injection, with whatever parameters the owner writes, have the
; same D25 subject as the injection without them: the poster's source.  The
; node's Injection-Info line (and its parameters) is injecting-node metadata
; and never part of the authored-source identity.
(defthm fn-ipp-injected-octets-keep-the-d25-subject
  (let ((d (fn-inj-decide source config obs)))
    (implies (fn-inj-injectedp d)
             (and (equal (fn-pb-subject (fn-ipp-injected-octets d secret login cfg)
                                        (fn-inj-config-agent config)
                                        (fn-inj-decision-msgid d))
                         (cons :source source))
                  (equal (fn-pb-subject (fn-inj-decision-octets d)
                                        (fn-inj-config-agent config)
                                        (fn-inj-decision-msgid d))
                         (cons :source source)))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                             '(fn-pb-subject car-cons cdr-cons))
           :use ((:instance fn-ipp-injected-octets-carry-the-parameters)
                 (:instance fn-inj-source-of-inverts-the-injection
                            (observation obs))
                 (:instance fn-ipp-an-injection-does-not-open-with-c)
                 (:instance fn-cll-skip-of-an-article-not-opening-with-c
                            (x (fn-ipp-injected-octets (fn-inj-decide source config obs)
                                                       secret login cfg)))
                 (:instance fn-cll-skip-of-an-article-not-opening-with-c
                            (x (fn-inj-decision-octets
                                (fn-inj-decide source config obs))))))))

(local
 (defthm fn-ipp-a-configured-agent-has-no-lf
   (implies (fn-inj-configp config)
            (not (member-equal 10 (fn-inj-config-agent config))))
   :hints (("Goal" :in-theory (enable fn-inj-configp fn-af-dot-atom-textp)))))

; A same-source retry is the same article (recipe v2, the poster supplied
; the Message-ID and no Path): two injections of one source at any two clock
; readings, stored under any two logins' parameters and any two complaints
; addresses, are one article for the Store's duplicate test.
(defthm fn-ipp-a-same-source-retry-is-the-same-article
  (let ((d1 (fn-inj-decide source config obs1))
        (d2 (fn-inj-decide source config obs2)))
    (implies (and (fn-inj-injectedp d1) (fn-inj-injectedp d2)
                  (not (fn-inj-supplies-pathp source))
                  (equal (fn-inj-decision-msgid d1) (fn-inj-decision-msgid d2)))
             (fn-pb-same-articlep (fn-inj-decision-msgid d1)
                                  (fn-ipp-injected-octets d2 secret2 login2 cfg2)
                                  (fn-ipp-injected-octets d1 secret1 login1 cfg1))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                             '(fn-pb-same-articlep fn-ipp-prefix-with
                                               fn-ipp-inj-append-is-append
                                               fn-ipp-append-assoc car-cons cdr-cons))
           :use ((:instance fn-ipp-injected-octets-keep-the-d25-subject
                            (obs obs1) (secret secret1) (login login1) (cfg cfg1))
                 (:instance fn-ipp-injected-octets-keep-the-d25-subject
                            (obs obs2) (secret secret2) (login login2) (cfg cfg2))
                 (:instance fn-ipp-injected-octets-carry-the-parameters
                            (obs obs2) (secret secret2) (login login2) (cfg cfg2))
                 (:instance fn-ipp-an-injection-configures-first (obs obs2))
                 (:instance fn-ipp-a-configured-agent-is-a-true-list)
                 (:instance fn-ipp-a-configured-agent-is-a-cons)
                 (:instance fn-ipp-a-configured-agent-has-no-lf)
                 (:instance fn-pb-path-agent-of-a-path-line
                            (agent (fn-inj-config-agent config))
                            (msgid (fn-inj-decision-msgid (fn-inj-decide source config obs1)))
                            (rest (append (fn-ipp-block-with
                                           (fn-ipp-date obs2)
                                           (fn-inj-decision-msgid (fn-inj-decide source config obs2))
                                           (fn-inj-config-agent config)
                                           (fn-ipp-gid source) (fn-ipp-gdate source)
                                           (fn-ipp-params secret2 login2
                                                          (fn-ipp-complaints cfg2)))
                                          source)))))))

; NOT PROVED (packet PKT-597-v3, named in the record): the same-article
; theorem for a supplied Path (recipe v3).  The executed comparison reads
; the block's agent through books/poster-bytes.lisp fn-pb-params-line-agent
; (the plain branch refuses an "agent" holding ";", which a dot-atom never
; does), and tests/acl2/injection-info-params-tests.lisp checks a v3 retry
; under two logins concretely; the general walk is the open proof.
