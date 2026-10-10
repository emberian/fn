; fn: what bounds a stored article's filed groups by its own header (O1,
; packet 1).  An article's filed groups are its control filing group, or a
; subsequence of its own Newsgroups names (FN-O1-FILED-WITHIN-SOURCEP); the
; signed path binds exactly that (FN-HSIG-AUTHORIZED-GROUPS-FILED-WITHIN-THE-
; SOURCE); the names of one valid Newsgroups field fit in the field's value
; (FN-O1-NEWSGROUPS-NAMES-WITHIN-THE-FIELD); a subsequence costs no more
; (FN-O1-SUBSEQ-WITHIN); a control filing group is one name of at most 19
; octets (FN-O1-CONTROL-FILING-GROUP-WITHIN-19).  Packet 2 carries it to
; the served Xref: the carried signed constructor files within its source
; (FN-HSIG-CARRIED-GROUPS-FILED-WITHIN-THE-SOURCE); filed groups within an
; admitted payload cost at most the header limit plus one, or are one name
; of at most 19 octets (FN-O1-FILED-NAMES-WITHIN-THE-HEADER); positional
; memberships give Xref pairs naming a subsequence of the groups
; (FN-O1-XREF-PAIRS-WITHIN-THE-GROUPS); each location costs its name plus
; 12 (FN-O1-XREF-LOCATIONS-WITHIN); so an article meeting
; FN-O1-ARTICLE-WITHIN-HEADERP over its own admitted bytes renders Xref
; locations within max(31, 12(H + 1)) (FN-O1-XREF-WITHIN-THE-HEADER).

(in-package "ACL2")

(include-book "hybrid-store")
(include-book "records-canonicality")
(include-book "hybrid-store-injected")
(include-book "peer-authored-accept")
(include-book "article-header-limits")
(include-book "nntp-xref")
(include-book "nntp-session")


(defun fn-o1-groups-octets (groups)
  (declare (xargs :guard t))
  (if (consp groups)
      (cons (fn-record-string-octets (car groups)) (fn-o1-groups-octets (cdr groups)))
    nil))

(defun fn-o1-subseqp (xs ys)
  (declare (xargs :guard t))
  (cond ((atom xs) t)
        ((atom ys) nil)
        ((equal (car xs) (car ys)) (fn-o1-subseqp (cdr xs) (cdr ys)))
        (t (fn-o1-subseqp xs (cdr ys)))))

(defun fn-o1-octet-sum (names)
  (declare (xargs :guard t))
  (if (consp names) (+ (len (car names)) (fn-o1-octet-sum (cdr names))) 0))

(defun fn-o1-source-newsgroups (source)
  (declare (xargs :guard t :verify-guards nil))
  (let ((parsed (fn-article-parse source)))
    (if (fn-article-result-okp parsed)
        (let ((st (fn-af-newsgroups-status (fn-article-result-article parsed))))
          (if (equal (car st) :single) (cadr st) nil))
      nil)))

(defun fn-o1-control-filedp (groups source)
  (declare (xargs :guard t :verify-guards nil))
  (let ((c (fn-ctl-classify-octets source)))
    (and (consp c) (eq (car c) :control)
         (equal groups (list (fn-ctl-filing-group (cadr c)))))))

(defun fn-o1-filed-within-sourcep (groups source)
  (declare (xargs :guard t :verify-guards nil))
  (or (fn-o1-control-filedp groups source)
      (fn-o1-subseqp (fn-o1-groups-octets groups) (fn-o1-source-newsgroups source))))

(local
 (defun o1-octet-list-listp (xs) (declare (xargs :guard t))
  (if (consp xs) (and (fn-cbor-octet-listp (car xs)) (o1-octet-list-listp (cdr xs))) t)))

(local
 (defthm o1-groups-octets-of-strings
  (implies (o1-octet-list-listp names)
           (equal (fn-o1-groups-octets (fn-hsig-octet-fields-to-strings names)) (true-list-fix names)))
  :hints (("Goal" :induct (len names) :in-theory (e/d (fn-hsig-octet-fields-to-strings) (fn-record-string-octets fn-record-octets-string)))
          ("Subgoal *1/1" :use ((:instance fn-record-string-octets-of-octets-string (octets (car names))))))))

(local
 (defthm o1-newsgroups-status-kinds
  (or (equal (car (fn-af-newsgroups-status a)) :missing) (equal (car (fn-af-newsgroups-status a)) :duplicate)
      (equal (car (fn-af-newsgroups-status a)) :invalid) (equal (car (fn-af-newsgroups-status a)) :single))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-af-newsgroups-status)))))

(local
 (defthm o1-authored-fields-are-the-newsgroups
  (implies (fn-hsig-authored-source-fields source)
           (equal (cadr (fn-hsig-authored-source-fields source))
                  (fn-hsig-octet-fields-to-strings (fn-o1-source-newsgroups source))))
  :hints (("Goal" :use ((:instance o1-newsgroups-status-kinds (a (cadr (fn-article-parse source)))))
           :in-theory (e/d (fn-hsig-authored-source-fields fn-o1-source-newsgroups fn-af-proto-article-check
                            fn-af-relayed-article-check fn-af-status-kind fn-af-status-value fn-inj-nth fn-inj-car
                            fn-inj-cdr fn-inj-proto-reason)
            (fn-record-string-octets fn-record-octets-string fn-hsig-octet-fields-to-strings fn-ctl-classify-octets
             fn-article-parse fn-af-newsgroups-status fn-af-message-id-status fn-article-get-headers
             fn-inj-mandatory-reason fn-article-syntax-p))))))

(local
 (defun o1-names-okp (xs) (declare (xargs :guard t))
  (if (consp xs) (and (true-listp (car xs)) (fn-af-newsgroup-namep (car xs)) (o1-names-okp (cdr xs))) t)))

(local
 (defthm o1-name-aux-octets
  (implies (and (true-listp b) (fn-af-newsgroup-name-aux b w)) (fn-cbor-octet-listp b))
  :hints (("Goal" :in-theory (enable fn-af-newsgroup-name-aux fn-af-newsgroup-component-charp fn-cbor-octet-listp fn-cbor-octetp)))))

(local
 (defthm o1-names-ok-octets
  (implies (o1-names-okp xs) (o1-octet-list-listp xs))
  :hints (("Goal" :in-theory (enable fn-af-newsgroup-namep)))))

(local
 (defthm o1-names-ok-revappend
  (implies (and (o1-names-okp a) (o1-names-okp b)) (o1-names-okp (revappend a b)))
  :hints (("Goal" :induct (revappend a b) :in-theory (disable fn-af-newsgroup-namep)))))

(local
 (defthm o1-take-token-name-true-listp
  (implies (true-listp rev) (true-listp (cadr (fn-af-take-newsgroup-token bytes rev))))
  :hints (("Goal" :in-theory (enable fn-af-take-newsgroup-token)))))

(local
 (defthm o1-list-parse-aux-names-ok
  (implies (and (o1-names-okp names-rev)
                (equal (car (fn-af-newsgroup-list-parse-aux bytes names-rev need fuel)) :ok))
           (o1-names-okp (cadr (fn-af-newsgroup-list-parse-aux bytes names-rev need fuel))))
  :hints (("Goal" :induct (fn-af-newsgroup-list-parse-aux bytes names-rev need fuel)
           :in-theory (e/d (fn-af-newsgroup-list-parse-aux) (fn-af-newsgroup-namep fn-af-take-newsgroup-token fn-af-skip-wsp))))))

(local
 (defthm o1-source-newsgroups-octets
  (o1-octet-list-listp (fn-o1-source-newsgroups source))
  :hints (("Goal" :in-theory (e/d (fn-o1-source-newsgroups fn-af-newsgroups-status fn-af-newsgroups-field-value
                                     fn-af-newsgroup-list-parse)
                                  (fn-af-newsgroup-list-parse-aux fn-article-parse fn-article-get-headers))
           :use ((:instance o1-names-ok-octets (xs (fn-o1-source-newsgroups source)))
                 (:instance o1-list-parse-aux-names-ok
                            (bytes (fn-af-skip-wsp (cdr (fn-article-field-unfolded-value
                                    (car (fn-article-get-headers (cadr (fn-article-parse source)) *fn-af-newsgroups-name*))))))
                            (names-rev nil) (need t) (fuel *fn-af-max-field-value-octets*)))))))

(local
 (defthm o1-subseqp-self (fn-o1-subseqp x x)))

(local
 (defthm o1-subseqp-true-list-fix (equal (fn-o1-subseqp x (true-list-fix y)) (fn-o1-subseqp x y))))

(local
 (defthm o1-subseqp-true-list-fix-left (equal (fn-o1-subseqp (true-list-fix x) y) (fn-o1-subseqp x y))))

(local
 (defthm o1-event-binds-groups
  (implies (fn-hsig-authorized-submission-event
            sequence txid generation keyring-generation enrolled-snapshot
            msgid source groups obligation-id content-subject
            release-evidence charge principal keys signatures observed-ml-key
            ed25519-observation ml-dsa-65-observation observation)
           (and (fn-hsig-authored-source-fields source)
                (equal groups (fn-hsig-source-filed-groups source (fn-hsig-authored-source-fields source)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-hsig-authorized-submission-event)
                                  (fn-hsig-source-filed-groups fn-hsig-authored-source-fields fn-record-p fn-record-make
                                   fn-hsig-authorized-article-event))))))

(defthm fn-hsig-authorized-groups-filed-within-the-source
  (implies (fn-hsig-authorized-submission-event
            sequence txid generation keyring-generation enrolled-snapshot
            msgid source groups obligation-id content-subject
            release-evidence charge principal keys signatures observed-ml-key
            ed25519-observation ml-dsa-65-observation observation)
           (fn-o1-filed-within-sourcep groups source))
  :rule-classes nil
  :hints (("Goal" :use (o1-event-binds-groups
                        (:instance o1-authored-fields-are-the-newsgroups)
                        (:instance o1-groups-octets-of-strings (names (fn-o1-source-newsgroups source)))
                        o1-source-newsgroups-octets)
           :in-theory (e/d (fn-hsig-source-filed-groups fn-o1-filed-within-sourcep fn-o1-control-filedp fn-hsig-second)
                           (fn-hsig-authorized-submission-event fn-hsig-authored-source-fields fn-o1-source-newsgroups
                            fn-ctl-classify-octets fn-hsig-octet-fields-to-strings fn-o1-groups-octets fn-record-p)))))

(local
 (defthm o1-filing-group-octets-within-19
  (<= (len (fn-record-string-octets (fn-ctl-filing-group verb))) 19)
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ctl-filing-group)))))

(defthm fn-o1-control-filing-group-within-19
  (implies (fn-o1-control-filedp groups source)
           (and (equal (len groups) 1)
                (<= (len (fn-record-string-octets (car groups))) 19)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-o1-control-filedp) (fn-ctl-classify-octets fn-ctl-filing-group fn-record-string-octets))
           :use ((:instance o1-filing-group-octets-within-19 (verb (cadr (fn-ctl-classify-octets source))))))))

(local
 (defthm o1-octet-sum-append
  (equal (fn-o1-octet-sum (append a b)) (+ (fn-o1-octet-sum a) (fn-o1-octet-sum b)))))

(local
 (defthm o1-octet-sum-rev
  (equal (fn-o1-octet-sum (rev a)) (fn-o1-octet-sum a))))

(local
 (defthm o1-octet-sum-revappend
  (equal (fn-o1-octet-sum (revappend a b)) (+ (fn-o1-octet-sum a) (fn-o1-octet-sum b)))))

(local
 (defthm o1-take-token-lens
  (equal (+ (len (cadr (fn-af-take-newsgroup-token bytes rev)))
            (len (caddr (fn-af-take-newsgroup-token bytes rev))))
         (+ (len bytes) (len rev)))
  :hints (("Goal" :in-theory (enable fn-af-take-newsgroup-token)))))

(local
 (defthm o1-skip-wsp-len
  (<= (len (fn-af-skip-wsp bytes)) (len bytes))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-af-skip-wsp)))))

(local
 (defthm o1-comma-is-consp
  (implies (equal (car x) 44) (consp x))
  :rule-classes :forward-chaining))

(local
 (defthm o1-skip-comma-len
  (implies (equal (car (fn-af-skip-wsp b)) 44)
           (< (len (fn-af-skip-wsp (cdr (fn-af-skip-wsp b)))) (len b)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-af-skip-wsp)
           :use ((:instance o1-skip-wsp-len (bytes b))
                 (:instance o1-skip-wsp-len (bytes (cdr (fn-af-skip-wsp b)))))))))

(local
 (defthm o1-list-parse-aux-within
  (implies (equal (car (fn-af-newsgroup-list-parse-aux bytes names-rev need fuel)) :ok)
           (<= (+ (fn-o1-octet-sum (cadr (fn-af-newsgroup-list-parse-aux bytes names-rev need fuel)))
                  (len (cadr (fn-af-newsgroup-list-parse-aux bytes names-rev need fuel))))
               (+ (fn-o1-octet-sum names-rev) (len names-rev) (len bytes) (if need 1 0))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-af-newsgroup-list-parse-aux bytes names-rev need fuel)
           :in-theory (e/d (fn-af-newsgroup-list-parse-aux)
                           (fn-af-newsgroup-namep fn-af-take-newsgroup-token fn-af-skip-wsp)))
          ("Subgoal *1/2" :use ((:instance o1-take-token-lens (rev nil)))))))

(defthm fn-o1-newsgroups-names-within-the-field
  (let ((parsed (fn-af-newsgroups-field-value field)))
    (implies (and (fn-article-fieldp field)
                  (consp parsed) (equal (car parsed) :ok))
             (<= (+ (fn-o1-octet-sum (cadr parsed)) (len (cadr parsed)))
                 (+ 1 (len (fn-article-field-unfolded-value field))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-af-newsgroups-field-value fn-af-newsgroup-list-parse)
                                  (fn-af-newsgroup-list-parse-aux fn-af-skip-wsp fn-article-fieldp))
           :use ((:instance o1-list-parse-aux-within
                            (bytes (fn-af-skip-wsp (cdr (fn-article-field-unfolded-value field))))
                            (names-rev nil) (need t) (fuel *fn-af-max-field-value-octets*))
                 (:instance o1-skip-wsp-len (bytes (cdr (fn-article-field-unfolded-value field))))))))

(defthm fn-o1-subseq-within
  (implies (fn-o1-subseqp xs ys)
           (and (<= (fn-o1-octet-sum xs) (fn-o1-octet-sum ys))
                (<= (len xs) (len ys))))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; Packet 2: from the filed groups to the rendered Xref, bounded by the
; header limit.

; The group names of Xref pairs, in order.
(defun fn-o1-pair-names (pairs)
  (declare (xargs :guard t))
  (if (consp pairs)
      (cons (if (consp (car pairs)) (car (car pairs)) nil)
            (fn-o1-pair-names (cdr pairs)))
    nil))

; THE PER-ARTICLE INVARIANT OVER WHAT OVER READS: the article's memberships
; are positional with its groups (fn-membership-listp, books/acceptance-
; alloc.lisp), and its groups are filed within PAYLOAD, the bytes its handle
; denotes (the received article, not the signed source).
(defun fn-o1-article-within-headerp (article payload)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-membership-listp (fn-article-groups article)
                            (fn-article-memberships article))
       (fn-o1-filed-within-sourcep (fn-article-groups article) payload)))

(local
 (defthm o1-carried-event-binds-groups
  (implies (fn-hsig-authorized-carried-submission-event-base
            sequence txid generation keyring-generation enrolled-snapshot
            msgid source received groups obligation-id content-subject
            release-evidence charge principal keys signatures observed-ml-key
            ed25519-observation ml-dsa-65-observation observation
            projection-ok)
           (and (fn-hsig-authored-source-fields source)
                (equal groups (fn-hsig-source-filed-groups source (fn-hsig-authored-source-fields source)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-hsig-authorized-carried-submission-event-base)
                                  (fn-hsig-source-filed-groups fn-hsig-authored-source-fields fn-record-p fn-record-make
                                   fn-hsig-carried-record-metadatap fn-hsig-authorize-at fn-stxa-bindsp
                                   fn-stxa-make-carried fn-hsig-authored-source-id))))))

(defthm fn-hsig-carried-groups-filed-within-the-source
  (implies (fn-hsig-authorized-carried-submission-event-base
            sequence txid generation keyring-generation enrolled-snapshot
            msgid source received groups obligation-id content-subject
            release-evidence charge principal keys signatures observed-ml-key
            ed25519-observation ml-dsa-65-observation observation
            projection-ok)
           (fn-o1-filed-within-sourcep groups source))
  :rule-classes nil
  :hints (("Goal" :use (o1-carried-event-binds-groups
                        (:instance o1-authored-fields-are-the-newsgroups)
                        (:instance o1-groups-octets-of-strings (names (fn-o1-source-newsgroups source)))
                        o1-source-newsgroups-octets)
           :in-theory (e/d (fn-hsig-source-filed-groups fn-o1-filed-within-sourcep fn-o1-control-filedp fn-hsig-second)
                           (fn-hsig-authorized-carried-submission-event-base fn-hsig-authored-source-fields fn-o1-source-newsgroups
                            fn-ctl-classify-octets fn-hsig-octet-fields-to-strings fn-o1-groups-octets fn-record-p)))))

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
 (defthm o1-groups-octets-len
  (equal (len (fn-o1-groups-octets g)) (len g))))

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

(defthm fn-o1-filed-names-within-the-header
  (implies (and (fn-article-result-okp (fn-article-parse-under payload limits))
                (fn-o1-filed-within-sourcep groups payload))
           (or (and (equal (len groups) 1)
                    (<= (len (fn-record-string-octets (car groups))) 19))
               (<= (+ (fn-o1-octet-sum (fn-o1-groups-octets groups)) (len groups))
                   (+ 1 (fn-article-limit-octets limits)))))
  :rule-classes nil
  :hints (("Goal"
           :cases ((fn-article-result-okp (fn-article-parse payload)))
           :in-theory (e/d (fn-o1-filed-within-sourcep)
                           (fn-o1-control-filedp fn-o1-source-newsgroups fn-article-parse fn-article-parse-under
                            fn-o1-subseqp fn-o1-octet-sum fn-o1-groups-octets fn-article-limit-octets
                            fn-article-header fn-article-result-article fn-record-string-octets))
           :use ((:instance fn-o1-control-filing-group-within-19 (source payload))
                 (:instance fn-o1-subseq-within (xs (fn-o1-groups-octets groups))
                            (ys (fn-o1-source-newsgroups payload)))
                 (:instance o1-source-newsgroups-within-header (p payload))
                 (:instance fn-article-parse-agrees-with-parse-under (octets payload))
                 (:instance fn-article-parse-under-header-within-the-limit (octets payload))))
          ("Subgoal 2" :in-theory (e/d (fn-o1-filed-within-sourcep fn-o1-source-newsgroups)
                                       (fn-o1-control-filedp fn-article-parse fn-article-parse-under
                                        fn-o1-octet-sum fn-record-string-octets)))))

(local
 (defthm o1-nntp-string-octets-aux-is-record
  (equal (fn-nntp-string-octets-aux chars) (fn-record-string-octets-aux chars))
  :hints (("Goal" :in-theory (enable fn-nntp-string-octets-aux fn-record-string-octets-aux)))))

(local
 (defthm o1-nntp-string-octets-is-record
  (equal (fn-nntp-string-octets x) (fn-record-string-octets x))
  :hints (("Goal" :in-theory (enable fn-nntp-string-octets fn-record-string-octets)))))

(local
 (defun o1-subseqp-ind (xs ys)
  (declare (xargs :measure (len ys)))
  (if (atom ys) (list xs)
    (list (o1-subseqp-ind xs (cdr ys)) (o1-subseqp-ind (cdr xs) (cdr ys))))))

(local
 (defthm o1-subseqp-cdr-left
  (implies (fn-o1-subseqp xs ys) (fn-o1-subseqp (cdr xs) ys))
  :hints (("Goal" :induct (o1-subseqp-ind xs ys)))))

(local
 (defthm o1-subseqp-cons-right
  (implies (fn-o1-subseqp xs ys) (fn-o1-subseqp xs (cons y ys)))))

(local
 (defthm o1-xref-pairs-of-subseq
  (fn-o1-subseqp (fn-o1-groups-octets (fn-o1-pair-names (fn-xref-pairs-of ms a)))
                 (fn-o1-groups-octets (fn-o1-pair-names ms)))
  :hints (("Goal" :induct (fn-xref-pairs-of ms a)
           :in-theory (e/d (fn-xref-pairs-of) (fn-record-string-octets fn-nntp-article-number fn-xref-wordp))))))

(local
 (defthm o1-membership-names-are-groups
  (implies (fn-membership-listp groups ms)
           (equal (fn-o1-groups-octets (fn-o1-pair-names ms)) (fn-o1-groups-octets groups)))
  :hints (("Goal" :induct (fn-membership-listp groups ms)
           :in-theory (e/d (fn-membership-listp) (fn-record-string-octets))))))

(defthm fn-o1-xref-pairs-within-the-groups
  (implies (fn-membership-listp groups memberships)
           (fn-o1-subseqp (fn-o1-groups-octets
                           (fn-o1-pair-names (fn-xref-pairs-of memberships article)))
                          (fn-o1-groups-octets groups)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance o1-xref-pairs-of-subseq (ms memberships) (a article)))
           :in-theory (disable o1-xref-pairs-of-subseq fn-xref-pairs-of))))

(local
 (defthm o1-decimal-field-within-10
  (<= (len (fn-nntp-decimal-field number)) 10)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-nntp-decimal-field)))))

(defthm fn-o1-xref-locations-within
  (<= (len (fn-xref-locations pairs))
      (+ (fn-o1-octet-sum (fn-o1-groups-octets (fn-o1-pair-names pairs)))
         (* 12 (len pairs))))
  :rule-classes nil
  :hints (("Goal" :induct (len pairs)
           :in-theory (e/d (fn-xref-locations) (fn-record-string-octets fn-nntp-decimal-field)))))

(local
 (defthm o1-pair-names-len (equal (len (fn-o1-pair-names p)) (len p))))

(local
 (defthm o1-single-group-sum
  (implies (equal (len groups) 1)
           (equal (fn-o1-octet-sum (fn-o1-groups-octets groups))
                  (len (fn-record-string-octets (car groups)))))
  :hints (("Goal" :expand ((fn-o1-groups-octets groups) (fn-o1-groups-octets (cdr groups)))))))

(defthm fn-o1-xref-within-the-header
  (let ((payload (fn-nntp-article-bytes article fn-arena)))
    (implies (and (fn-article-result-okp (fn-article-parse-under payload limits))
                  (fn-o1-article-within-headerp article payload))
             (<= (len (fn-xref-locations (fn-xref-pairs article)))
                 (max 31 (* 12 (+ 1 (fn-article-limit-octets limits)))))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (fn-o1-article-within-headerp fn-xref-pairs)
                           (fn-xref-pairs-of fn-xref-locations fn-nntp-article-bytes fn-article-parse-under
                            fn-o1-filed-within-sourcep fn-membership-listp fn-o1-subseqp fn-o1-octet-sum
                            fn-o1-groups-octets fn-o1-pair-names fn-article-limit-octets fn-record-string-octets))
           :use ((:instance fn-o1-filed-names-within-the-header
                            (groups (fn-article-groups article))
                            (payload (fn-nntp-article-bytes article fn-arena)))
                 (:instance fn-o1-xref-pairs-within-the-groups
                            (groups (fn-article-groups article))
                            (memberships (fn-article-memberships article)))
                 (:instance fn-o1-xref-locations-within
                            (pairs (fn-xref-pairs-of (fn-article-memberships article) article)))
                 (:instance fn-o1-subseq-within
                            (xs (fn-o1-groups-octets (fn-o1-pair-names
                                 (fn-xref-pairs-of (fn-article-memberships article) article))))
                            (ys (fn-o1-groups-octets (fn-article-groups article))))
                 (:instance o1-single-group-sum (groups (fn-article-groups article)))))))
