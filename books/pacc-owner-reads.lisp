; PACC approved v3 per-connection and v4 per-item definitions.
(in-package "ACL2")

(include-book "../host/owner-host")

(include-book "post-acceptance")

(include-book "served-available-read")

(include-book "article-header-limits")

(include-book "article-buffer")

(defun fn-pacc-sub-inj (sub secret take-config parse-carry icfg iclock)
  (declare (xargs :guard t))
  (list (fn-own-sub-decision sub) secret (fn-own-sub-account sub)
        take-config parse-carry icfg iclock))

(defun fn-pacc-sub-read-bodyp (sub secret take-config parse-carry read-limits art icfg iclock)
  ; the defun-sk's body, named, so U and the teeth can quantify it explicitly
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-own-sub-shapep sub)
       (fn-inj-configp icfg)
       (fn-clock-observationp iclock)
       (equal (fn-inj-config-header-limits icfg) read-limits)
       (equal (fn-own-sub-decision sub) (fn-post-gated-decision art icfg iclock))
       (fn-inj-injectedp (fn-own-sub-decision sub))
       (not (fn-peer-submissionp (fn-own-sub-decision sub)))
       (equal (fn-own-sub-stored-octets take-config sub secret)
              (fn-pacc-stored-payload
               art (fn-pacc-sub-inj sub secret take-config parse-carry icfg iclock)))))

(defun-sk fn-pacc-sub-readp (sub secret take-config parse-carry read-limits)
  (exists (art icfg iclock)
    (fn-pacc-sub-read-bodyp sub secret take-config parse-carry read-limits art icfg iclock)))

(defun fn-pacc-pinned-header-triples (conns) (declare (xargs :guard t :verify-guards nil)) (if (consp conns) (let ((h (fn-inj-config-header-limits (fn-own-conn-config (car conns)))) (tail (fn-pacc-pinned-header-triples (cdr conns)))) (if (member-equal h tail) tail (cons h tail))) nil))

(defun fn-pacc-conn-reads-own-headersp (o c) (declare (xargs :guard t :verify-guards nil)) (let* ((sc (fn-own-served-conn o c (fn-own-conn-live-session o c))) (as (fn-served-conn-session sc)) (cfg (fn-served-conn-config sc))) (equal (fn-inj-config-header-limits (fn-auth-view-config as (fn-auth-moderation-config as cfg) (fn-served-conn-archive sc))) (fn-inj-config-header-limits (fn-own-conn-config c)))))

(defun fn-pacc-conns-read-own-headersp (o conns) (declare (xargs :guard t :verify-guards nil)) (if (consp conns) (and (fn-pacc-conn-reads-own-headersp o (car conns)) (fn-pacc-conns-read-own-headersp o (cdr conns))) t))

(defun fn-pacc-pins-read-own-headersp (o) (declare (xargs :guard t :verify-guards nil)) (fn-pacc-conns-read-own-headersp o (fn-own-conns o)))

(defun fn-pacc-sub-read-at-profilep (sub secret take-config parse-carry item-profile) (declare (xargs :guard t :verify-guards nil)) (and (fn-bs-profile-admittedp item-profile) (fn-pacc-sub-readp sub secret take-config parse-carry (fn-bs-profile-header-limits item-profile))))

(defun-sk fn-pacc-item-sub-readp (sub secret take-config parse-carry) (exists (item-profile) (fn-pacc-sub-read-at-profilep sub secret take-config parse-carry item-profile)))

(defun fn-pacc-local-sub-readp (sub secret take-config parse-carry) (declare (xargs :guard t :verify-guards nil)) (let ((d (fn-own-sub-decision sub))) (implies (and (equal (fn-own-sub-source-context sub) :post-d25) (fn-inj-injectedp d) (not (fn-peer-submissionp d))) (fn-pacc-item-sub-readp sub secret take-config parse-carry))))

(defun fn-pacc-queue-readp (queue secret take-config parse-carry) (declare (xargs :guard t :verify-guards nil)) (if (consp queue) (and (fn-pacc-local-sub-readp (fn-psub-unpack-sub (car queue)) secret take-config parse-carry) (fn-pacc-queue-readp (cdr queue) secret take-config parse-carry)) t))

(defun fn-pacc-inflight-readp (sub secret take-config parse-carry) (declare (xargs :guard t :verify-guards nil)) (fn-pacc-local-sub-readp sub secret take-config parse-carry))

(defun fn-pacc-owner-value-readsp (o) (declare (xargs :guard t :verify-guards nil)) (and (fn-pacc-pins-read-own-headersp o) (fn-pacc-queue-readp (fn-own-queue o) nil nil nil) (fn-pacc-inflight-readp (fn-own-inflight o) nil nil nil)))

(defun fn-pacc-owner-readsp (state) (declare (xargs :stobjs state :guard t :verify-guards nil)) (fn-pacc-owner-value-readsp (fn-ocfg-owner (fn-owner-ocfg state))))

(defun fn-pacc-pin3-enqueue-read-premisep (sub secret take-config parse-carry pin c art icfg iclock) (declare (xargs :guard t :verify-guards nil)) (and (fn-bs-profile-admittedp pin) (equal (fn-inj-config-header-limits (fn-own-conn-config c)) (fn-bs-profile-header-limits pin)) (fn-pacc-sub-read-bodyp sub secret take-config parse-carry (fn-bs-profile-header-limits pin) art icfg iclock)))

(local (in-theory (enable fn-pacc-sub-readp fn-pacc-sub-read-bodyp)))

(defthm fn-pacc-sub-readp-fixes-shape
  (implies (fn-pacc-sub-readp sub secret take-config parse-carry read-limits)
           (and (fn-own-sub-shapep sub)
                (fn-inj-injectedp (fn-own-sub-decision sub))
                (not (fn-peer-submissionp (fn-own-sub-decision sub)))))
  :rule-classes nil)

(local (defthm fn-pacc-mod-len-append-l
 (equal (len (append a b)) (+ (len a) (len b)))
 :hints (("Goal" :induct (append a b) :in-theory
 (union-theories (theory 'ground-zero) '(append len))))))

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

(defun fn-pacc-gated-header-roomp (decision read-limits)
  (declare (xargs :guard t))
  (or (not (fn-inj-injectedp decision))
      (<= 21 (fn-article-limit-octets read-limits))))

(defthm fn-pacc-gated-decision-has-header-room
  (fn-pacc-gated-header-roomp
   (fn-post-gated-decision art icfg iclock)
   (fn-inj-config-header-limits icfg))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-pacc-injected-header-budget-covers-control-name-l
                            (source art) (config icfg) (obs iclock))
                 (:instance fn-post-gated-decision-is-the-decision-or-its-envelope
                            (source art) (config icfg) (injection iclock)))
           :in-theory (e/d (fn-pacc-gated-header-roomp fn-post-gated-decision)
                           (fn-inj-decide fn-inj-injectedp fn-gst-post-gate fn-mod-gate)))))

(defthm fn-pacc-sub-readp-fixes-gated-header-room
  (implies (fn-pacc-sub-readp sub secret take-config parse-carry read-limits)
           (fn-pacc-gated-header-roomp (fn-own-sub-decision sub) read-limits))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-pacc-gated-decision-has-header-room
                           (art (mv-nth 0 (fn-pacc-sub-readp-witness sub secret take-config parse-carry read-limits)))
                           (icfg (mv-nth 1 (fn-pacc-sub-readp-witness sub secret take-config parse-carry read-limits)))
                           (iclock (mv-nth 2 (fn-pacc-sub-readp-witness sub secret take-config parse-carry read-limits)))))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-pacc-sub-readp fn-pacc-sub-read-bodyp)))))
