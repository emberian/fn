; fn: header-only injection edits with no recipe-validity hypothesis.
(in-package "ACL2")
(include-book "article-art")
(include-book "injection-info-params")

; A proof-only domain: HEAD contains a complete blank-line boundary, possibly
; followed by additional HEAD octets. It protects an appended BODY even when
; a malformed earlier line makes a header walk stop before HEAD's end.
(defun fn-art-rest-shielded-headp (h)
  (declare (xargs :guard t))
  (if (fn-art-double-crlfp h)
      (true-listp h)
    (and (consp h) (fn-art-rest-shielded-headp (cdr h)))))

(defun fn-art-shielded-headp (head)
  (declare (xargs :guard t))
  (and (true-listp head)
       (or (fn-art-crlfp head) (fn-art-rest-shielded-headp head))))

(defun fn-art-separated-headp (head)
  (declare (xargs :guard t))
  (and (true-listp head) (fn-art-first-separator-headp head)))

(local
 (defthm fn-art-rest-separated-is-shielded
   (implies (fn-art-rest-separated-headp h) (fn-art-rest-shielded-headp h))))

(defthm fn-art-separated-head-is-shielded
  (implies (fn-art-separated-headp h) (fn-art-shielded-headp h)))

(defthm fn-art-rest-shielded-head-true-listp
  (implies (fn-art-rest-shielded-headp h) (true-listp h)))

(defthm fn-art-separated-head-true-listp
  (implies (fn-art-shielded-headp h) (true-listp h)))
(defthm fn-art-separated-head-consp
  (implies (fn-art-shielded-headp h) (consp h)))

(local
 (defthm fn-art-rest-head-after-ordinary-octet
   (implies (and (fn-art-rest-shielded-headp h)
                 (not (equal (car h) 13)))
            (fn-art-rest-shielded-headp (cdr h)))))

(local
 (defthm fn-art-separated-head-has-lf
   (implies (fn-art-shielded-headp h) (member-equal 10 h))))

(local
 (defthm fn-art-rest-head-has-lf
   (implies (fn-art-rest-shielded-headp h) (member-equal 10 h))))

(local
 (defthm fn-art-rest-fixed-line-on-append
   (implies (fn-art-rest-shielded-headp h)
            (equal (fn-pb-fixed-linep n (append h b))
                   (fn-pb-fixed-linep n h)))
   :hints (("Goal" :induct (fn-pb-fixed-linep n h)))))

(defthm fn-art-fixed-line-on-append
  (implies (fn-art-shielded-headp h)
           (equal (fn-pb-fixed-linep n (append h b))
                  (fn-pb-fixed-linep n h)))
  :hints (("Goal" :in-theory (disable fn-art-rest-shielded-headp))))

(local
 (defthm fn-art-rest-head-after-line
   (implies (and (fn-art-rest-shielded-headp h)
                 (fn-pb-fixed-linep n h))
            (fn-art-shielded-headp (nthcdr n h)))
   :hints (("Goal" :in-theory
            (union-theories '(fn-art-rest-shielded-headp fn-art-shielded-headp
                              fn-art-crlfp fn-art-double-crlfp fn-pb-fixed-linep
                              nthcdr zp natp true-listp car-cons cdr-cons commutativity-of-+
                              default-car default-cdr
                              fn-art-rest-shielded-head-true-listp
                              (:type-prescription true-listp-nthcdr-type-prescription))
                            (theory 'minimal-theory))
            :expand ((nthcdr n h) (nthcdr 2 h) (nthcdr 1 (cdr h)))
            :induct (fn-pb-fixed-linep n h)))))

(defthm fn-art-head-after-nonempty-line
  (implies (and (fn-art-shielded-headp h)
                (< 2 n)
                (fn-pb-fixed-linep n h))
           (fn-art-shielded-headp (nthcdr n h)))
  :hints (("Goal" :in-theory (disable fn-art-rest-shielded-headp))))

(local
 (defun fn-art-line-pair-induct (n line h)
   (declare (xargs :measure (nfix n)))
   (if (or (not (natp n)) (<= n 2))
       (list line h)
     (fn-art-line-pair-induct (- n 1) (cdr line) (cdr h)))))
(local
 (defthm fn-art-strip-within-head
   (implies (and (true-listp h) (<= (len line) (len h)))
            (equal (fn-inj-strip line (append h b))
                   (if (equal (fn-inj-strip line h) :no)
                       :no
                     (append (fn-inj-strip line h) b))))
   :hints (("Goal" :in-theory (enable fn-inj-strip)
            :induct (fn-inj-strip line h)))))
(local
 (defthm fn-art-strip-needs-length
   (implies (< (len h) (len line))
            (equal (fn-inj-strip line h) :no))
   :hints (("Goal" :in-theory (enable fn-inj-strip)))))
(local
 (defthm fn-art-strip-transfers-fixed-check
   (implies (and (not (equal (fn-inj-strip line h) :no))
                 (<= n (len line))
                 (fn-pb-fixed-linep n line))
            (fn-pb-fixed-linep n h))
   :hints (("Goal" :in-theory (enable fn-inj-strip)
            :induct (fn-art-line-pair-induct n line h)))))

(defthm fn-art-strip-line-on-append
  (implies (fn-art-shielded-headp h)
           (equal (fn-pb-strip-header-line line (append h b))
                  (if (equal (fn-pb-strip-header-line line h) :no)
                      :no
                    (append (fn-pb-strip-header-line line h) b))))
  :hints (("Goal" :do-not-induct t
           :cases ((<= (len line) (len h)))
           :in-theory (e/d (fn-pb-strip-header-line)
                            (fn-art-shielded-headp fn-pb-fixed-linep fn-inj-strip))
           :use ((:instance fn-art-strip-transfers-fixed-check
                            (n (len line)) (h (append h b)))))))

(local
 (defthm fn-art-strip-is-drop
   (implies (not (equal (fn-inj-strip line h) :no))
            (equal (fn-inj-strip line h) (nthcdr (len line) h)))
   :hints (("Goal" :in-theory (enable fn-inj-strip)))))

(local
 (defthm fn-art-strip-transfers-line-check
   (implies (and (not (equal (fn-inj-strip line h) :no))
                 (fn-pb-fixed-linep (len line) line))
            (fn-pb-fixed-linep (len line) h))
   :hints (("Goal" :in-theory (enable fn-inj-strip)
            :induct (fn-inj-strip line h)))))

(defthm fn-art-head-after-strip-line
  (implies (and (fn-art-shielded-headp h)
                (not (equal (fn-pb-strip-header-line line h) :no)))
           (fn-art-shielded-headp (fn-pb-strip-header-line line h)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pb-strip-header-line)
                            (fn-art-shielded-headp fn-art-first-separator-headp
                             fn-art-rest-shielded-headp fn-pb-fixed-linep
                             fn-inj-strip)))))

(local
 (defthm fn-art-append-assoc
   (equal (append (append x y) z) (append x (append y z)))))
(local
 (defthm fn-art-inj-append-is-append
   (equal (fn-inj-append x y) (append x y))
   :hints (("Goal" :in-theory (enable fn-inj-append)))))

(local
 (defthm fn-art-separated-append-not-no
   (implies (fn-art-shielded-headp h)
            (not (equal (append h b) :no)))
   :hints (("Goal" :in-theory (disable fn-art-shielded-headp)))))

(defthm fn-art-ipp-info-head-local
  (implies (fn-art-shielded-headp h)
           (equal (fn-ipp-at-info (append h b) agent params)
                  (append (fn-ipp-at-info h agent params) b)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-ipp-at-info)
                            (fn-pb-strip-header-line fn-art-shielded-headp
                             fn-inj-injection-info-line-with fn-inj-injection-info-line)))))

(local
 (defthm fn-art-inj-drop-is-nthcdr
   (implies (<= (nfix n) (len x))
            (equal (fn-inj-drop n x) (nthcdr n x)))
   :hints (("Goal" :in-theory (enable fn-inj-drop)))))

(local
 (defthm fn-art-drop-within-head
   (implies (and (natp n) (<= n (len h)))
            (equal (nthcdr n (append h b)) (append (nthcdr n h) b)))))
(local
 (defthm fn-art-take-within-head
   (implies (and (natp n) (<= n (len h)))
            (equal (fn-inj-take n (append h b)) (fn-inj-take n h)))
   :hints (("Goal" :in-theory (enable fn-inj-take)))))

(local
 (defthm fn-art-rest-head-consp
   (implies (fn-art-rest-shielded-headp h) (consp h))))

(local (defthm fn-art-rest-head-cons-forward
         (implies (fn-art-rest-shielded-headp h) (consp h))
         :rule-classes :forward-chaining))
(local (defthm fn-art-consp-append
         (equal (consp (append x y)) (or (consp x) (consp y)))))
(local (defthm fn-art-car-append
         (implies (consp x) (equal (car (append x y)) (car x)))))
(local (defthm fn-art-cdr-append
         (implies (consp x) (equal (cdr (append x y)) (append (cdr x) y)))
         :hints (("Goal" :in-theory
                   (union-theories '(binary-append cdr-cons) (theory 'minimal-theory))))))

; Prefix recognition cannot see through the blank line: field names contain
; no CR or LF, so a matching field prefix finishes before the separator.
(local
 (defthm fn-art-strip-text-no-match-append
   (implies (and (fn-art-rest-shielded-headp h)
                 (fn-pb-line-textp prefix))
            (equal (equal (fn-inj-strip prefix (append h b)) :no)
                   (equal (fn-inj-strip prefix h) :no)))
   :hints (("Goal"  :in-theory
            (union-theories
             '(fn-inj-strip fn-pb-line-textp binary-append car-cons cdr-cons
               fn-art-consp-append fn-art-car-append fn-art-cdr-append
               fn-art-rest-head-consp fn-art-rest-head-cons-forward
               fn-art-rest-head-after-ordinary-octet
               (:executable-counterpart fn-art-rest-shielded-headp))
             (theory 'minimal-theory))
            :induct (fn-inj-strip prefix h)))))
(local
 (defthm fn-art-opens-text-on-append
   (implies (and (fn-art-shielded-headp h)
                 (fn-pb-line-textp prefix))
            (equal (fn-pb-opensp prefix (append h b))
                   (fn-pb-opensp prefix h)))
   :hints (("Goal" :in-theory (e/d (fn-pb-opensp fn-inj-strip)
                                  (fn-art-rest-shielded-headp))))))

(defthm fn-art-ipp-date-head-local
  (implies (fn-art-shielded-headp h)
           (equal (fn-ipp-at-date (append h b) agent params)
                  (append (fn-ipp-at-date h agent params) b)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-ipp-at-date)
                            (fn-ipp-at-info fn-art-shielded-headp
                             fn-pb-fixed-linep fn-pb-opensp fn-inj-take
                             nthcdr)))))

(defthm fn-art-ipp-msgid-head-local
  (implies (fn-art-shielded-headp h)
           (equal (fn-ipp-at-msgid (append h b) agent msgid params)
                  (append (fn-ipp-at-msgid h agent msgid params) b)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-ipp-at-msgid)
                            (fn-ipp-at-date fn-pb-strip-header-line
                             fn-art-shielded-headp fn-inj-message-id-line)))))

(defthm fn-art-ipp-stamp-head-local
  (implies (fn-art-shielded-headp h)
           (equal (fn-ipp-at-stamp (append h b) agent msgid params)
                  (append (fn-ipp-at-stamp h agent msgid params) b)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-ipp-at-stamp)
                            (fn-ipp-at-msgid fn-art-shielded-headp
                             fn-pb-fixed-linep fn-pb-opensp fn-inj-take nthcdr)))))

(local
 (defthm fn-art-pb-line-on-append
   (implies (member-equal 10 h)
            (equal (fn-pb-line (append h b)) (fn-pb-line h)))
   :hints (("Goal"  :in-theory
            (union-theories '(fn-pb-line member-equal binary-append
                              car-cons cdr-cons fn-art-consp-append
                              fn-art-car-append fn-art-cdr-append)
                            (theory 'minimal-theory))))))

(defthm fn-art-path-line-agent-head-local
  (implies (fn-art-shielded-headp h)
           (equal (fn-pb-path-line-agent (append h b))
                  (fn-pb-path-line-agent h)))
  :hints (("Goal" :in-theory
           (e/d (fn-pb-path-line-agent)
                (fn-pb-line fn-art-shielded-headp)))))

(defthm fn-art-info-line-agent-head-local
  (implies (fn-art-shielded-headp h)
           (equal (fn-pb-info-line-agent (append h b))
                  (fn-pb-info-line-agent h)))
  :hints (("Goal" :in-theory
           (e/d (fn-pb-info-line-agent)
                (fn-pb-line fn-art-shielded-headp)))))

(defthm fn-art-block-agent-head-local
  (implies (fn-art-shielded-headp h)
           (equal (fn-pb-block-agent (append h b) msgid)
                  (fn-pb-block-agent h msgid)))
  :hints (("Goal" :do-not-induct t
           :in-theory
           (e/d (fn-pb-block-agent)
                (fn-pb-info-line-agent fn-pb-opensp fn-art-shielded-headp
                 fn-pb-fixed-linep fn-pb-strip-header-line nthcdr)))))

(local
 (defthm fn-art-after-line-on-append
   (implies (member-equal 10 h)
            (equal (fn-cll-after-line (append h b))
                   (append (fn-cll-after-line h) b)))
   :hints (("Goal" :in-theory
            (union-theories '(fn-cll-after-line member-equal binary-append
                              car-cons cdr-cons fn-art-consp-append
                              fn-art-car-append fn-art-cdr-append)
                            (theory 'minimal-theory))))))

(local
 (defthm fn-art-rest-head-after-first-lf
   (implies (fn-art-rest-shielded-headp h)
            (fn-art-shielded-headp (fn-cll-after-line h)))
   :hints (("Goal" :in-theory
            (union-theories '(fn-cll-after-line fn-art-rest-shielded-headp
                              fn-art-shielded-headp fn-art-first-separator-headp
                              fn-art-crlfp fn-art-double-crlfp true-listp
                              car-cons cdr-cons default-car default-cdr)
                            (theory 'minimal-theory))
            :induct (fn-cll-after-line h)))))

(local
 (defthm fn-art-cll-strip-is-inj-strip
   (equal (fn-cll-strip field x) (fn-inj-strip field x))
   :hints (("Goal" :in-theory (enable fn-cll-strip fn-inj-strip)))))

(defthm fn-art-cll-skip-one-head-local
  (implies (and (fn-art-shielded-headp h)
                (consp field) (fn-pb-line-textp field))
           (equal (fn-cll-skip-one field (append h b))
                  (append (fn-cll-skip-one field h) b)))
  :hints (("Goal" :do-not-induct t
           :in-theory
           (union-theories '(fn-cll-skip-one fn-pb-opensp
                             fn-art-cll-strip-is-inj-strip fn-art-after-line-on-append
                             fn-art-separated-head-has-lf)
                           (theory 'minimal-theory))
           :use ((:instance fn-art-opens-text-on-append (prefix field))))))

(defthm fn-art-head-after-cll-skip-one
  (implies (and (fn-art-shielded-headp h)
                (consp field) (fn-pb-line-textp field))
           (fn-art-shielded-headp (fn-cll-skip-one field h)))
  :hints (("Goal" :do-not-induct t
           :expand ((fn-pb-line-textp field) (fn-inj-strip field h))
           :in-theory (union-theories
            '(fn-cll-skip-one fn-art-shielded-headp fn-art-crlfp fn-inj-strip
              fn-pb-line-textp fn-art-cll-strip-is-inj-strip
              fn-art-rest-head-after-first-lf true-listp car-cons cdr-cons)
            (theory 'minimal-theory)))))

(defthm fn-art-cll-skip-head-local
  (implies (fn-art-shielded-headp h)
           (equal (fn-cll-skip (append h b)) (append (fn-cll-skip h) b)))
  :hints (("Goal" :in-theory
           (e/d (fn-cll-skip)
                (fn-cll-skip-one fn-art-shielded-headp)))))

(defthm fn-art-head-after-cll-skip
  (implies (fn-art-shielded-headp h)
           (fn-art-shielded-headp (fn-cll-skip h)))
  :hints (("Goal" :in-theory
           (e/d (fn-cll-skip)
                (fn-cll-skip-one fn-art-shielded-headp)))))

(defthm fn-art-path-agent-head-local
  (implies (fn-art-shielded-headp h)
           (equal (fn-pb-path-agent (append h b) msgid)
                  (fn-pb-path-agent h msgid)))
  :hints (("Goal" :in-theory
           (e/d (fn-pb-path-agent)
                (fn-cll-skip fn-pb-path-line-agent fn-pb-block-agent
                 fn-art-shielded-headp)))))

(local
 (defthm fn-art-pb-line-first
   (and (equal (consp (fn-pb-line x)) (consp x))
        (equal (car (fn-pb-line x)) (car x)))
   :hints (("Goal" :in-theory
            (union-theories '(fn-pb-line car-cons default-car)
                            (theory 'minimal-theory))
            :expand ((fn-pb-line x))))))

(local
 (defthm fn-art-strip-of-pb-line
   (implies (member-equal 10 x)
            (equal (fn-inj-strip (fn-pb-line x) x) (fn-cll-after-line x)))
   :hints (("Goal" :in-theory
            (union-theories '(fn-pb-line fn-inj-strip fn-cll-after-line
                              member-equal car-cons cdr-cons)
                            (theory 'minimal-theory))
            :induct (fn-pb-line x)))))

(local
 (defthm fn-art-block-agent-not-path
   (implies (equal (car x) 80) (equal (fn-pb-block-agent x msgid) nil))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-pb-block-agent fn-pb-opensp fn-inj-strip
                              fn-pb-strip-header-line fn-inj-message-id-line
                              fn-pb-info-line-agent fn-pb-params-line-agent)
                             (fn-pb-line fn-pb-fixed-linep))
            :expand ((fn-inj-strip *fn-inj-injection-info-field* (fn-pb-line x)))))))

(local
 (defthm fn-art-path-agent-at-path
   (implies (equal (car x) 80)
            (equal (fn-pb-path-agent x msgid) (fn-pb-path-line-agent x)))
   :hints (("Goal" :in-theory (e/d (fn-pb-path-agent)
                                  (fn-pb-path-line-agent fn-pb-block-agent
                                   fn-cll-skip))))))

(local
 (defthm fn-art-named-path-is-line
   (implies (fn-pb-path-line-agent x)
            (equal (fn-inj-path-line (fn-pb-path-line-agent x)) (fn-pb-line x)))
   :hints (("Goal" :in-theory (enable fn-pb-path-line-agent)))))

(local
 (defthm fn-art-no-path-strip-if-not-p
   (implies (not (equal (car x) 80))
            (equal (fn-inj-strip (fn-inj-path-line agent) x) :no))
   :hints (("Goal" :in-theory (enable fn-inj-strip fn-inj-path-line)))))

(local
 (defthm fn-art-head-after-non-cr-line
   (implies (and (fn-art-shielded-headp h) (not (equal (car h) 13)))
            (fn-art-shielded-headp (fn-cll-after-line h)))
   :hints (("Goal" :in-theory
            (union-theories '(fn-art-shielded-headp fn-art-crlfp
                              fn-art-rest-head-after-first-lf)
                            (theory 'minimal-theory))))))

(local
 (defthm fn-art-member-append
   (implies (member-equal e h) (member-equal e (append h b)))
   :hints (("Goal" :in-theory
            (union-theories '(member-equal binary-append car-cons cdr-cons)
                            (theory 'minimal-theory))
            :induct (member-equal e h)))))
(local
 (defthm fn-art-strip-of-pb-line-on-append
   (implies (fn-art-shielded-headp h)
            (equal (fn-inj-strip (fn-pb-line h) (append h b))
                   (append (fn-cll-after-line h) b)))
   :hints (("Goal" :do-not-induct t
            :in-theory
            (union-theories '(fn-art-pb-line-on-append fn-art-after-line-on-append
                              fn-art-separated-head-has-lf fn-art-member-append member-equal
                              fn-art-consp-append fn-art-car-append fn-art-cdr-append)
                            (theory 'minimal-theory))
            :use ((:instance fn-art-strip-of-pb-line (x (append h b))))))))

(defthm fn-art-ipp-with-params-shielded
  (implies (fn-art-shielded-headp h)
           (equal (fn-ipp-with-params (append h b) msgid params)
                  (append (fn-ipp-with-params h msgid params) b)))
  :hints (("Goal" :do-not-induct t
           :cases ((equal (car h) 80))
           :in-theory
           (e/d (fn-ipp-with-params)
                (fn-pb-path-agent fn-pb-path-line-agent fn-pb-block-agent
                 fn-ipp-at-stamp fn-inj-path-line fn-pb-line fn-inj-strip
                 fn-art-shielded-headp fn-cll-after-line
                 fn-art-strip-is-drop)))))

; The audited public statement: only HEAD's first blank-line boundary.
(defthm fn-ipp-with-params-head-local
  (implies (fn-art-separated-headp head)
           (equal (fn-ipp-with-params (append head body) msgid params)
                  (append (fn-ipp-with-params head msgid params) body)))
  :hints (("Goal" :in-theory
           (union-theories '(fn-art-separated-head-is-shielded
                             fn-art-ipp-with-params-shielded)
                           (theory 'minimal-theory)))))
