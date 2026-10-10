; fn: what bounds a stored article's filed groups by its own header (O1,
; packet 1).  An article's filed groups are its control filing group, or a
; subsequence of its own Newsgroups names (FN-O1-FILED-WITHIN-SOURCEP); the
; signed path binds exactly that (FN-HSIG-AUTHORIZED-GROUPS-FILED-WITHIN-THE-
; SOURCE); the names of one valid Newsgroups field fit in the field's value
; (FN-O1-NEWSGROUPS-NAMES-WITHIN-THE-FIELD); a subsequence costs no more
; (FN-O1-SUBSEQ-WITHIN); a control filing group is one name of at most 19
; octets (FN-O1-CONTROL-FILING-GROUP-WITHIN-19).  Packet 2 carries it to
; the served Xref: the carried signed constructor files within its source
; (FN-HSIG-CARRIED-GROUPS-FILED-WITHIN-THE-SOURCE), and the native injected
; and peer signed events within the RECEIVED payload they store
; (FN-HSIG-INJECTED-GROUPS-FILED-WITHIN-THE-RECEIVED,
; FN-PA-AUTHORIZED-GROUPS-FILED-WITHIN-THE-RECEIVED); filed groups within an
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

; P2-2 and P2-3: the injected native event and the peer event file within
; the RECEIVED payload they store: injection prepends Path and
; Injection-Info, the carrier prepends FN-Authorship, the peer projection
; drops only reserved fields; none is Newsgroups, Control or Supersedes, so
; the reparse keeps the fields the invariant reads (o1e-filed-within-by-
; agreement).

(local
 (defun o1e-line-ind (l acc left)
  (declare (xargs :measure (len l)))
  (if (consp l)
      (o1e-line-ind (cdr l) (cons (car l) acc) (1- left))
    (list acc left))))

(local
 (defthm o1e-next-line-aux-of-a-line
  (implies (and (fn-article-crlf-freep l) (true-listp l)
                (<= (len l) (nfix left)) (true-listp acc))
           (equal (fn-article-next-line-aux (append l (list* 13 10 r)) acc left)
                  (list :ok (append (reverse acc) l) r)))
  :hints (("Goal" :induct (o1e-line-ind l acc left)
           :in-theory (enable fn-article-next-line-aux)))))

(local
 (defthm o1e-next-line-of-a-line
  (implies (and (fn-article-crlf-freep l) (true-listp l) (<= (len l) 998))
           (equal (fn-article-next-line (append l (list* 13 10 r)))
                  (list :ok l r)))
  :hints (("Goal" :in-theory (enable fn-article-next-line)
           :use ((:instance o1e-next-line-aux-of-a-line (acc nil) (left 998)))))))

(local
 (defthm o1e-next-line-of-blank
  (equal (fn-article-next-line (list* 13 10 r)) (list :ok nil r))
  :hints (("Goal" :in-theory (enable fn-article-next-line fn-article-next-line-aux)))))

(local
 (defthm o1e-next-line-aux-len
  (implies (and (true-listp line-rev)
                (fn-article-line-okp (fn-article-next-line-aux octets line-rev left)))
           (<= (len (fn-article-line-value (fn-article-next-line-aux octets line-rev left)))
               (+ (len line-rev) (nfix left))))
  :hints (("Goal" :induct (fn-article-next-line-aux octets line-rev left)
           :in-theory (enable fn-article-next-line-aux)))))

(local
 (defthm o1e-next-line-len
  (implies (fn-article-line-okp (fn-article-next-line octets))
           (<= (len (fn-article-line-value (fn-article-next-line octets))) 998))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-article-next-line)
           :use ((:instance o1e-next-line-aux-len (line-rev nil) (left 998)))))))

(local
 (defun o1e-line-okp (l)
  (declare (xargs :guard t))
  (and (true-listp l) (consp l) (fn-article-crlf-freep l) (<= (len l) 998))))

(local
 (defun o1e-folds-okp (ls)
  (declare (xargs :guard t))
  (if (consp ls)
      (and (o1e-line-okp (car ls)) (fn-article-fold-linep (car ls))
           (o1e-folds-okp (cdr ls)))
    (null ls))))

(local
 (defun o1e-fold-up (f ls)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ls)
      (o1e-fold-up (fn-article-add-fold f (car ls)) (cdr ls))
    f)))

(local
 (defun o1e-fieldvp (f)
  (declare (xargs :guard t :verify-guards nil))
  (and (true-listp f) (consp (car f))
       (o1e-line-okp (car (car f)))
       (not (fn-article-wspp (car (car (car f)))))
       (fn-article-line-okp (fn-article-new-field (car (car f))))
       (o1e-folds-okp (cdr (car f)))
       (equal f (o1e-fold-up (fn-article-line-value (fn-article-new-field (car (car f))))
                             (cdr (car f)))))))

(local
 (defun o1e-closedp (f)
  (declare (xargs :guard t :verify-guards nil))
  (fn-article-has-vcharp (fn-article-field-unfolded-value f))))

(local
 (defun o1e-fieldsvp (fs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp fs)
      (and (o1e-fieldvp (car fs)) (o1e-closedp (car fs)) (o1e-fieldsvp (cdr fs)))
    (null fs))))

(local
 (defthm o1e-fold-up-append
  (equal (o1e-fold-up f (append a b)) (o1e-fold-up (o1e-fold-up f a) b))))

(local
 (defthm o1e-folds-okp-true-listp
  (implies (o1e-folds-okp a) (true-listp a))
  :rule-classes :forward-chaining))

(local
 (defthm o1e-folds-okp-append
  (implies (true-listp a)
           (equal (o1e-folds-okp (append a b)) (and (o1e-folds-okp a) (o1e-folds-okp b))))
  :hints (("Goal" :induct (o1e-folds-okp a)))))

(local
 (defthm o1e-new-field-raw
  (implies (fn-article-line-okp (fn-article-new-field line))
           (equal (car (fn-article-line-value (fn-article-new-field line)))
                  (list line)))
  :hints (("Goal" :in-theory (enable fn-article-new-field)))))

(local
 (defthm o1e-new-field-true-listp
  (implies (fn-article-line-okp (fn-article-new-field line))
           (true-listp (fn-article-line-value (fn-article-new-field line))))
  :hints (("Goal" :in-theory (enable fn-article-new-field)))))

(local
 (defthm o1e-new-field-is-v
  (implies (and (o1e-line-okp line) (not (fn-article-wspp (car line)))
                (fn-article-line-okp (fn-article-new-field line)))
           (o1e-fieldvp (fn-article-line-value (fn-article-new-field line))))
  :hints (("Goal" :in-theory (e/d (o1e-fieldvp) (fn-article-new-field fn-article-line-value))))))

(local
 (defthm o1e-add-fold-is-v
  (implies (and (o1e-fieldvp f) (o1e-line-okp l) (fn-article-fold-linep l))
           (o1e-fieldvp (fn-article-add-fold f l)))
  :hints (("Goal" :in-theory (e/d (o1e-fieldvp fn-article-add-fold)
                                  (fn-article-new-field fn-article-line-value fn-article-fold-linep))
           :use ((:instance o1e-fold-up-append
                            (f (fn-article-line-value (fn-article-new-field (car (car f)))))
                            (a (cdr (car f))) (b (list l))))))))

(local
 (in-theory (disable o1e-fieldvp o1e-closedp)))

(local
 (defthm o1e-fieldsvp-true-listp
  (implies (o1e-fieldsvp fs) (true-listp fs))
  :rule-classes :forward-chaining))

(local
 (defthm o1e-fieldsvp-append
  (implies (true-listp a)
           (equal (o1e-fieldsvp (append a b)) (and (o1e-fieldsvp a) (o1e-fieldsvp b))))
  :hints (("Goal" :induct (o1e-fieldsvp a)))))

(local
 (defthm o1e-fieldsvp-rev
  (implies (o1e-fieldsvp a) (o1e-fieldsvp (rev a)))
  :hints (("Goal" :induct (o1e-fieldsvp a)
           :in-theory (enable rev)))))

(local
 (defthm o1e-fieldsvp-revappend
  (implies (and (o1e-fieldsvp a) (o1e-fieldsvp b))
           (o1e-fieldsvp (revappend a b)))))

(local
 (defthm o1e-fieldsvp-finish-fields
  (implies (and (o1e-fieldsvp fr)
                (or (null cur) (and (o1e-fieldvp cur) (o1e-closedp cur))))
           (o1e-fieldsvp (fn-article-finish-fields fr cur)))
  :hints (("Goal" :in-theory (enable fn-article-finish-fields)))))

(local
 (defthm o1e-true-list-nonnil-is-consp
  (implies (and (true-listp x) x) (consp x))
  :rule-classes nil))

(local
 (defthm o1e-next-line-value-consp
  (implies (and (fn-article-line-okp (fn-article-next-line octets))
                (fn-article-line-value (fn-article-next-line octets)))
           (consp (fn-article-line-value (fn-article-next-line octets))))
  :hints (("Goal" :in-theory (disable fn-article-next-line fn-article-line-value)
           :use (fn-article-next-line-value-is-list
                 (:instance o1e-true-list-nonnil-is-consp
                            (x (fn-article-line-value (fn-article-next-line octets)))))))))

(local
 (defthm o1e-next-line-value-is-a-line
  (implies (and (fn-article-line-okp (fn-article-next-line octets))
                (fn-article-line-value (fn-article-next-line octets)))
           (o1e-line-okp (fn-article-line-value (fn-article-next-line octets))))
  :hints (("Goal" :in-theory (e/d (o1e-line-okp)
                                  (fn-article-next-line fn-article-line-value))
           :use (fn-article-next-line-value-is-list
                 fn-article-next-line-value-crlf-free
                 o1e-next-line-value-consp
                 o1e-next-line-len)))))

(local
 (defthm o1e-parse-lines-fields-v
  (implies (and (true-listp octets)
                (o1e-fieldsvp fields-rev)
                (or (null current) (o1e-fieldvp current))
                (fn-article-result-okp
                 (fn-article-parse-lines octets limits lines-left header-bytes nfields
                                         fields-rev current header-rev)))
           (o1e-fieldsvp
            (fn-article-fields
             (fn-article-result-article
              (fn-article-parse-lines octets limits lines-left header-bytes nfields
                                      fields-rev current header-rev)))))
  :hints (("Goal"
           :induct (fn-article-parse-lines octets limits lines-left header-bytes nfields
                                           fields-rev current header-rev)
           :in-theory (e/d (fn-article-parse-lines fn-article-ok fn-article-make
                            fn-article-fields fn-article-result-okp fn-article-result-article
                            fn-article-field-closedp o1e-closedp)
                           (fn-article-next-line fn-article-next-line-aux
                            fn-article-new-field fn-article-add-fold
                            fn-article-finish-fields fn-article-body-crlfp
                            fn-article-header-rev-add-line
                            fn-article-line-value fn-article-line-rest
                            o1e-fieldvp))))))

(local
 (defthm o1e-parse-fields-v
  (implies (fn-article-result-okp (fn-article-parse octets))
           (o1e-fieldsvp (fn-article-fields (fn-article-result-article (fn-article-parse octets)))))
  :hints (("Goal"
           :use ((:instance o1e-parse-lines-fields-v
                  (limits *fn-article-ceiling-limits*) (lines-left (1+ *fn-article-max-octets*))
                  (header-bytes 0) (nfields 0) (fields-rev nil) (current nil)
                  (header-rev nil)))
           :in-theory (e/d (fn-article-parse fn-article-parse-under
                            fn-article-octets-are-proper-list)
                           (fn-article-parse-lines fn-cbor-at-mostp
                            o1e-parse-lines-fields-v))))))

(local
 (defun o1e-nlines (fs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp fs)
      (+ (len (car (car fs))) (o1e-nlines (cdr fs)))
    0)))

(local
 (defun o1e-hr-lines (hr lines)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp lines)
      (o1e-hr-lines (fn-article-header-rev-add-line hr (car lines)) (cdr lines))
    hr)))

(local
 (defun o1e-run-fr (fs fr cur)
  (declare (xargs :guard t))
  (if (consp fs)
      (o1e-run-fr (cdr fs) (if cur (cons cur fr) fr) (car fs))
    fr)))

(local
 (defun o1e-run-cur (fs cur)
  (declare (xargs :guard t))
  (if (consp fs) (o1e-run-cur (cdr fs) (car fs)) cur)))

(local
 (defun o1e-run-nf (fs nf cur)
  (declare (xargs :guard t))
  (if (consp fs)
      (o1e-run-nf (cdr fs) (if cur (+ 1 (nfix nf)) nf) (car fs))
    nf)))

(local
 (defun o1e-run-hr (fs hr)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp fs)
      (o1e-run-hr (cdr fs) (o1e-hr-lines hr (car (car fs))))
    hr)))

(local
 (defthm o1e-new-field-consp
  (implies (fn-article-line-okp (fn-article-new-field line))
           (consp (fn-article-line-value (fn-article-new-field line))))
  :hints (("Goal" :in-theory (enable fn-article-new-field)))))

(local
 (defthm o1e-parse-lines-of-a-fold
  (implies (and (o1e-line-okp l) (fn-article-fold-linep l) cur
                (posp nl) (natp hb)
                (<= (+ hb (len l) 2) (fn-article-limit-octets limits)))
           (equal (fn-article-parse-lines (append l (list* 13 10 rest))
                                          limits nl hb nf fr cur hr)
                  (fn-article-parse-lines rest limits (1- nl) (+ hb (len l) 2) nf fr
                                          (fn-article-add-fold cur l)
                                          (fn-article-header-rev-add-line hr l))))
  :hints (("Goal"
           :expand ((:free (cur hr nf fr)
                     (fn-article-parse-lines (append l (list* 13 10 rest))
                                             limits nl hb nf fr cur hr)))
           :in-theory (e/d (o1e-line-okp fn-article-fold-linep fn-article-wspp)
                           (fn-article-parse-lines fn-article-add-fold
                            fn-article-header-rev-add-line fn-article-limit-octets
                            fn-article-header-bytes-p fn-article-has-vcharp
                            binary-append))
           :do-not-induct t))))

(local
 (defun o1e-folds-ind (ls cur nl hb hr)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ls)
      (o1e-folds-ind (cdr ls) (fn-article-add-fold cur (car ls)) (1- nl)
                     (+ hb (len (car ls)) 2)
                     (fn-article-header-rev-add-line hr (car ls)))
    (list cur nl hb hr))))

(local
 (defthm o1e-parse-lines-of-folds
  (implies (and (o1e-folds-okp ls) cur (natp nl) (natp hb)
                (<= (len ls) nl)
                (<= (+ hb (len (fn-article-lines-octets ls))) (fn-article-limit-octets limits)))
           (equal (fn-article-parse-lines (append (fn-article-lines-octets ls) rest)
                                          limits nl hb nf fr cur hr)
                  (fn-article-parse-lines rest limits (- nl (len ls))
                                          (+ hb (len (fn-article-lines-octets ls)))
                                          nf fr (o1e-fold-up cur ls) (o1e-hr-lines hr ls))))
  :hints (("Goal"
           :induct (o1e-folds-ind ls cur nl hb hr)
           :in-theory (e/d (fn-article-lines-octets)
                           (fn-article-parse-lines fn-article-add-fold
                            fn-article-header-rev-add-line fn-article-limit-octets
                            fn-article-fold-linep))))))

(local
 (defthm o1e-parse-lines-of-a-new-field-line
  (implies (and (o1e-line-okp l) (not (fn-article-wspp (car l)))
                (fn-article-line-okp (fn-article-new-field l))
                (posp nl) (natp hb) (natp nf)
                (or (null cur) (fn-article-has-vcharp (fn-article-field-unfolded-value cur)))
                (<= (+ hb (len l) 2) (fn-article-limit-octets limits))
                (< (+ nf (if cur 1 0)) (fn-article-limit-fields limits)))
           (equal (fn-article-parse-lines (append l (list* 13 10 rest))
                                          limits nl hb nf fr cur hr)
                  (fn-article-parse-lines rest limits (1- nl) (+ hb (len l) 2)
                                          (if cur (+ 1 nf) nf)
                                          (if cur (cons cur fr) fr)
                                          (fn-article-line-value (fn-article-new-field l))
                                          (fn-article-header-rev-add-line hr l))))
  :hints (("Goal"
           :expand ((:free (cur hr nf fr)
                     (fn-article-parse-lines (append l (list* 13 10 rest))
                                             limits nl hb nf fr cur hr)))
           :in-theory (e/d (o1e-line-okp fn-article-field-closedp)
                           (fn-article-parse-lines fn-article-add-fold
                            fn-article-header-rev-add-line fn-article-limit-octets
                            fn-article-limit-fields fn-article-new-field
                            fn-article-header-bytes-p fn-article-has-vcharp
                            binary-append))
           :do-not-induct t))))

(local
 (defthm o1e-parse-lines-of-a-built-field
  (implies (and (o1e-line-okp l1) (not (fn-article-wspp (car l1)))
                (fn-article-line-okp (fn-article-new-field l1))
                (o1e-folds-okp folds)
                (natp nl) (natp hb) (natp nf)
                (or (null cur) (fn-article-has-vcharp (fn-article-field-unfolded-value cur)))
                (<= (+ 1 (len folds)) nl)
                (<= (+ hb (len l1) 2 (len (fn-article-lines-octets folds)))
                    (fn-article-limit-octets limits))
                (< (+ nf (if cur 1 0)) (fn-article-limit-fields limits)))
           (equal (fn-article-parse-lines
                   (append (fn-article-lines-octets (cons l1 folds)) rest)
                   limits nl hb nf fr cur hr)
                  (fn-article-parse-lines
                   rest limits (- nl (+ 1 (len folds)))
                   (+ hb (len l1) 2 (len (fn-article-lines-octets folds)))
                   (if cur (+ 1 nf) nf) (if cur (cons cur fr) fr)
                   (o1e-fold-up (fn-article-line-value (fn-article-new-field l1)) folds)
                   (o1e-hr-lines hr (cons l1 folds)))))
  :hints (("Goal"
           :in-theory (e/d (fn-article-lines-octets)
                           (fn-article-parse-lines fn-article-add-fold
                            fn-article-header-rev-add-line fn-article-limit-octets
                            fn-article-limit-fields fn-article-new-field
                            fn-article-has-vcharp fn-article-line-value
                            o1e-parse-lines-of-a-new-field-line
                            o1e-parse-lines-of-folds))
           :do-not-induct t
           :use ((:instance o1e-parse-lines-of-a-new-field-line
                            (l l1) (rest (append (fn-article-lines-octets folds) rest)))
                 (:instance o1e-parse-lines-of-folds
                            (ls folds) (cur (fn-article-line-value (fn-article-new-field l1)))
                            (nl (1- nl)) (hb (+ hb (len l1) 2))
                            (nf (if cur (+ 1 nf) nf)) (fr (if cur (cons cur fr) fr))
                            (hr (fn-article-header-rev-add-line hr l1))))))))

(local
 (defthm o1e-cons-car-cdr
  (implies (consp x) (equal (cons (car x) (cdr x)) x))))

(local
 (defthm o1e-parse-lines-of-a-built-field-ls
  (implies (and (consp ls) (o1e-line-okp (car ls)) (not (fn-article-wspp (car (car ls))))
                (fn-article-line-okp (fn-article-new-field (car ls)))
                (o1e-folds-okp (cdr ls))
                (natp nl) (natp hb) (natp nf)
                (or (null cur) (fn-article-has-vcharp (fn-article-field-unfolded-value cur)))
                (<= (len ls) nl)
                (<= (+ hb (len (fn-article-lines-octets ls))) (fn-article-limit-octets limits))
                (< (+ nf (if cur 1 0)) (fn-article-limit-fields limits)))
           (equal (fn-article-parse-lines
                   (append (fn-article-lines-octets ls) rest)
                   limits nl hb nf fr cur hr)
                  (fn-article-parse-lines
                   rest limits (- nl (len ls))
                   (+ hb (len (fn-article-lines-octets ls)))
                   (if cur (+ 1 nf) nf) (if cur (cons cur fr) fr)
                   (o1e-fold-up (fn-article-line-value (fn-article-new-field (car ls))) (cdr ls))
                   (o1e-hr-lines hr ls))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable fn-article-parse-lines fn-article-limit-octets fn-article-limit-fields
                               fn-article-new-field fn-article-line-value o1e-hr-lines
                               o1e-parse-lines-of-a-built-field)
           :expand ((len ls) (fn-article-lines-octets ls))
           :use ((:instance o1e-parse-lines-of-a-built-field
                            (l1 (car ls)) (folds (cdr ls))))))))

(local
 (defthm o1e-parse-lines-of-a-field
  (implies (and (o1e-fieldvp f)
                (natp nl) (natp hb) (natp nf)
                (or (null cur) (fn-article-has-vcharp (fn-article-field-unfolded-value cur)))
                (<= (len (car f)) nl)
                (<= (+ hb (len (fn-article-lines-octets (car f))))
                    (fn-article-limit-octets limits))
                (< (+ nf (if cur 1 0)) (fn-article-limit-fields limits)))
           (equal (fn-article-parse-lines
                   (append (fn-article-lines-octets (car f)) rest)
                   limits nl hb nf fr cur hr)
                  (fn-article-parse-lines
                   rest limits (- nl (len (car f)))
                   (+ hb (len (fn-article-lines-octets (car f))))
                   (if cur (+ 1 nf) nf) (if cur (cons cur fr) fr)
                   f (o1e-hr-lines hr (car f)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (o1e-fieldvp)
                           (fn-article-parse-lines fn-article-lines-octets
                            fn-article-limit-octets fn-article-limit-fields
                            fn-article-new-field fn-article-line-value
                            o1e-parse-lines-of-a-built-field-ls o1e-hr-lines))
           :use ((:instance o1e-parse-lines-of-a-built-field-ls (ls (car f))))))))

(local
 (defun o1e-fields-ind (fs nl hb nf fr cur hr)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp fs)
      (o1e-fields-ind (cdr fs) (- nl (len (car (car fs))))
                      (+ hb (len (fn-article-lines-octets (car (car fs)))))
                      (if cur (+ 1 nf) nf) (if cur (cons cur fr) fr) (car fs)
                      (o1e-hr-lines hr (car (car fs))))
    (list nl hb nf fr cur hr))))

(local
 (defthm o1e-parse-lines-of-fields
  (implies (and (o1e-fieldsvp fs) (natp nl) (natp hb) (natp nf)
                (or (null cur) (fn-article-has-vcharp (fn-article-field-unfolded-value cur)))
                (<= (o1e-nlines fs) nl)
                (<= (+ hb (len (fn-article-fields-octets fs))) (fn-article-limit-octets limits))
                (<= (+ nf (if cur 1 0) (len fs)) (fn-article-limit-fields limits)))
           (equal (fn-article-parse-lines
                   (append (fn-article-fields-octets fs) rest)
                   limits nl hb nf fr cur hr)
                  (fn-article-parse-lines
                   rest limits (- nl (o1e-nlines fs))
                   (+ hb (len (fn-article-fields-octets fs)))
                   (o1e-run-nf fs nf cur) (o1e-run-fr fs fr cur)
                   (o1e-run-cur fs cur) (o1e-run-hr fs hr))))
  :hints (("Goal"
           :induct (o1e-fields-ind fs nl hb nf fr cur hr)
           :in-theory (e/d (o1e-closedp)
                           (fn-article-parse-lines fn-article-limit-octets
                            fn-article-limit-fields fn-article-lines-octets
                            o1e-hr-lines))))))

(local
 (defthm o1e-parse-lines-of-the-blank-line
  (implies (and (posp nl) (fn-article-body-crlfp body)
                (fn-article-field-closedp cur) (true-listp hr))
           (equal (fn-article-parse-lines (cons 13 (cons 10 body))
                                          limits nl hb nf fr cur hr)
                  (fn-article-ok
                   (fn-article-make (rev hr) body (fn-article-finish-fields fr cur)))))
  :hints (("Goal"
           :expand ((fn-article-parse-lines (cons 13 (cons 10 body))
                                            limits nl hb nf fr cur hr))
           :in-theory (disable fn-article-parse-lines fn-article-field-closedp
                               fn-article-body-crlfp fn-article-finish-fields)
           :use ((:instance fn-article-blank-line-partitions-input (octets (cons 13 (cons 10 body)))))))))

(local
 (defthm o1e-hr-lines-true-listp
  (implies (true-listp hr) (true-listp (o1e-hr-lines hr lines)))
  :hints (("Goal" :in-theory (enable fn-article-header-rev-add-line)))))

(local
 (defthm o1e-run-hr-true-listp
  (implies (true-listp hr) (true-listp (o1e-run-hr fs hr)))
  :hints (("Goal" :in-theory (disable o1e-hr-lines)))))

(local
 (defthm o1e-run-cur-closed
  (implies (and (o1e-fieldsvp fs)
                (or (null cur) (fn-article-has-vcharp (fn-article-field-unfolded-value cur))))
           (fn-article-field-closedp (o1e-run-cur fs cur)))
  :hints (("Goal" :in-theory (enable fn-article-field-closedp o1e-closedp)))))

(local
 (defthm o1e-parse-lines-of-fields-and-body
  (implies (and (o1e-fieldsvp fs) (natp nl) (natp hb) (natp nf) (true-listp hr)
                (or (null cur) (fn-article-has-vcharp (fn-article-field-unfolded-value cur)))
                (< (o1e-nlines fs) nl)
                (<= (+ hb (len (fn-article-fields-octets fs))) (fn-article-limit-octets limits))
                (<= (+ nf (if cur 1 0) (len fs)) (fn-article-limit-fields limits))
                (fn-article-body-crlfp body))
           (equal (fn-article-parse-lines
                   (append (fn-article-fields-octets fs) (cons 13 (cons 10 body)))
                   limits nl hb nf fr cur hr)
                  (fn-article-ok
                   (fn-article-make (rev (o1e-run-hr fs hr)) body
                                    (fn-article-finish-fields (o1e-run-fr fs fr cur)
                                                              (o1e-run-cur fs cur))))))
  :hints (("Goal"
           :in-theory (disable fn-article-parse-lines fn-article-limit-octets
                               fn-article-limit-fields o1e-run-hr o1e-run-fr o1e-run-cur
                               o1e-run-nf fn-article-field-closedp o1e-nlines
                               fn-article-finish-fields fn-article-body-crlfp)
           :use ((:instance o1e-parse-lines-of-fields (rest (cons 13 (cons 10 body))))
                 (:instance o1e-parse-lines-of-the-blank-line
                            (nl (- nl (o1e-nlines fs)))
                            (hb (+ hb (len (fn-article-fields-octets fs))))
                            (nf (o1e-run-nf fs nf cur)) (fr (o1e-run-fr fs fr cur))
                            (cur (o1e-run-cur fs cur)) (hr (o1e-run-hr fs hr))))))))

(local
 (defthm o1e-reverse-is-rev
  (implies (true-listp x) (equal (reverse x) (rev x)))
  :hints (("Goal" :in-theory (enable rev)))))

(local
 (defthm o1e-finish-fields-of-the-run
  (implies (and (o1e-fieldsvp fs) (true-listp fr))
           (equal (fn-article-finish-fields (o1e-run-fr fs fr cur) (o1e-run-cur fs cur))
                  (append (fn-article-finish-fields fr cur) fs)))
  :hints (("Goal" :induct (o1e-fields-ind fs nl hb nf fr cur hr)
           :in-theory (e/d (fn-article-finish-fields) (o1e-hr-lines))))))

(local
 (defun o1e-tl-linesp (ls)
  (declare (xargs :guard t))
  (if (consp ls) (and (true-listp (car ls)) (o1e-tl-linesp (cdr ls))) t)))

(local
 (defthm o1e-folds-okp-tl-linesp
  (implies (o1e-folds-okp ls) (o1e-tl-linesp ls))))

(local
 (defthm o1e-fieldvp-tl-lines
  (implies (o1e-fieldvp f) (o1e-tl-linesp (car f)))
  :hints (("Goal" :in-theory (enable o1e-fieldvp)
           :use ((:instance o1e-cons-car-cdr (x (car f))))))))

(local
 (defthm o1e-hr-lines-recompose
  (implies (and (true-listp hr) (o1e-tl-linesp ls))
           (equal (rev (o1e-hr-lines hr ls))
                  (append (rev hr) (fn-article-lines-octets ls))))
  :hints (("Goal" :induct (o1e-hr-lines hr ls)
           :in-theory (e/d (fn-article-lines-octets)
                           (fn-article-header-rev-add-line fn-article-header-rev-add-line-recomposes))
           :do-not-induct t)
          ("Subgoal *1/1" :use ((:instance fn-article-header-rev-add-line-recomposes
                                           (header-rev hr) (line (car ls)))
                                (:instance fn-article-extended-header-is-list
                                           (header-rev hr) (line (car ls))))))))

(local
 (defthm o1e-run-hr-recompose
  (implies (and (o1e-fieldsvp fs) (true-listp hr))
           (equal (rev (o1e-run-hr fs hr))
                  (append (rev hr) (fn-article-fields-octets fs))))
  :hints (("Goal" :induct (o1e-fields-ind fs nl hb nf fr cur hr)
           :in-theory (e/d () (o1e-hr-lines fn-article-lines-octets))))))

(local
 (defthm o1e-len-le-len-append
  (<= (len b) (len (append a b)))
  :rule-classes :linear))

(local
 (defthm o1e-lines-le-octets
  (<= (len ls) (len (fn-article-lines-octets ls)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-article-lines-octets)))))

(local
 (defthm o1e-nlines-le-octets
  (implies (o1e-fieldsvp fs)
           (<= (o1e-nlines fs) (len (fn-article-fields-octets fs))))
  :rule-classes :linear
  :hints (("Goal" :induct (o1e-nlines fs)
           :in-theory (e/d () (fn-article-lines-octets))))))

(local
 (defthm o1e-fields-le-nlines
  (implies (o1e-fieldsvp fs)
           (<= (len fs) (o1e-nlines fs)))
  :rule-classes :linear
  :hints (("Goal" :induct (o1e-nlines fs)
           :in-theory (enable o1e-fieldvp)))))

(local
 (defthm o1e-parse-of-fields
  (implies (and (o1e-fieldsvp fs) (fn-article-body-crlfp body)
                (fn-cbor-octet-listp (append (fn-article-fields-octets fs)
                                             (cons 13 (cons 10 body))))
                (<= (len (append (fn-article-fields-octets fs) (cons 13 (cons 10 body))))
                    *fn-article-max-octets*))
           (equal (fn-article-parse (append (fn-article-fields-octets fs)
                                            (cons 13 (cons 10 body))))
                  (fn-article-ok (fn-article-make (fn-article-fields-octets fs) body fs))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-article-parse fn-article-parse-under fn-ap-at-most-is-length-bound)
                           (fn-article-parse-lines o1e-run-hr o1e-run-fr o1e-run-cur
                            o1e-nlines fn-article-fields-octets fn-article-finish-fields
                            fn-article-body-crlfp o1e-parse-lines-of-fields-and-body))
           :use ((:instance o1e-parse-lines-of-fields-and-body
                            (limits *fn-article-ceiling-limits*)
                            (nl (1+ *fn-article-max-octets*))
                            (hb 0) (nf 0) (fr nil) (cur nil) (hr nil))
                 (:instance o1e-finish-fields-of-the-run (fr nil) (cur nil))
                 (:instance o1e-run-hr-recompose (hr nil))
                 (:instance o1e-nlines-le-octets)
                 (:instance o1e-fields-le-nlines))))))

(local
 (defthm o1e-parse-lines-body-crlfp
  (implies (fn-article-result-okp
            (fn-article-parse-lines octets limits nl hb nf fr cur hr))
           (fn-article-body-crlfp
            (fn-article-body
             (fn-article-result-article
              (fn-article-parse-lines octets limits nl hb nf fr cur hr)))))
  :hints (("Goal"
           :induct (fn-article-parse-lines octets limits nl hb nf fr cur hr)
           :in-theory (e/d (fn-article-parse-lines fn-article-ok fn-article-make
                            fn-article-body fn-article-result-okp fn-article-result-article)
                           (fn-article-next-line fn-article-next-line-aux
                            fn-article-new-field fn-article-add-fold
                            fn-article-finish-fields fn-article-body-crlfp
                            fn-article-header-rev-add-line
                            fn-article-line-value fn-article-line-rest))))))

(local
 (defthm o1e-parse-body-crlfp
  (implies (fn-article-result-okp (fn-article-parse octets))
           (fn-article-body-crlfp
            (fn-article-body (fn-article-result-article (fn-article-parse octets)))))
  :hints (("Goal"
           :use ((:instance o1e-parse-lines-body-crlfp
                  (limits *fn-article-ceiling-limits*) (nl (1+ *fn-article-max-octets*))
                  (hb 0) (nf 0) (fr nil) (cur nil) (hr nil)))
           :in-theory (e/d (fn-article-parse fn-article-parse-under)
                           (fn-article-parse-lines fn-cbor-at-mostp
                            o1e-parse-lines-body-crlfp))))))

(local
 (defthm o1e-parse-reconstructs
  (implies (fn-article-result-okp (fn-article-parse y))
           (let ((article (fn-article-result-article (fn-article-parse y))))
             (and (true-listp article)
                  (o1e-fieldsvp (fn-article-fields article))
                  (fn-article-body-crlfp (fn-article-body article))
                  (true-listp (fn-article-body article))
                  (equal y (append (fn-article-fields-octets (fn-article-fields article))
                                   (cons 13 (cons 10 (fn-article-body article))))))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (union-theories '(fn-article-syntax-p fn-article-source
                                        fn-article-octet-list-true-listp
                                        fn-article-append-associative (:e binary-append)
                                        binary-append car-cons cdr-cons)
                                      (theory 'minimal-theory))
           :use ((:instance fn-article-successful-parse-syntax-p (octets y))
                 (:instance fn-article-successful-parse-preserves-source (octets y))
                 (:instance fn-article-successful-parse-fields-recompose-header (octets y))
                 (:instance o1e-parse-fields-v (octets y))
                 (:instance o1e-parse-body-crlfp (octets y)))))))

(local
 (defun o1e-authored (fields)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp fields)
      (if (fn-hc-reserved-namep (fn-article-field-name (car fields)))
          (o1e-authored (cdr fields))
        (cons (car fields) (o1e-authored (cdr fields))))
    nil)))

(local
 (defthm o1e-authored-fieldsvp
  (implies (o1e-fieldsvp fs) (o1e-fieldsvp (o1e-authored fs)))
  :hints (("Goal" :induct (o1e-fieldsvp fs)))))

(local
 (defthm o1e-stx-field-octets-is-lines-octets
  (implies (o1e-tl-linesp ls)
           (equal (fn-stx-field-octets ls) (fn-article-lines-octets ls)))
  :hints (("Goal" :induct (o1e-tl-linesp ls)
           :in-theory (enable fn-stx-field-octets fn-article-lines-octets)))))

(local
 (defthm o1e-fieldsvp-true-listp-fields
  (implies (and (o1e-fieldsvp fs) (consp fs)) (true-listp (car fs)))
  :hints (("Goal" :in-theory (enable o1e-fieldvp)))))

(local
 (defthm o1e-source-header-is-authored-octets
  (implies (o1e-fieldsvp fs)
           (equal (fn-hc-source-header fs)
                  (fn-article-fields-octets (o1e-authored fs))))
  :hints (("Goal" :induct (o1e-fieldsvp fs)
           :in-theory (e/d (fn-hc-source-header)
                           (fn-stx-field-octets fn-article-lines-octets))))))

(local
 (defthm o1e-authored-source-is-append
  (implies (and (true-listp a) (o1e-fieldsvp (fn-article-fields a))
                (true-listp (fn-article-body a)))
           (equal (fn-hc-authored-source a)
                  (append (fn-article-fields-octets (o1e-authored (fn-article-fields a)))
                          (cons 13 (cons 10 (fn-article-body a))))))
  :hints (("Goal" :in-theory (e/d (fn-hc-authored-source)
                                  (fn-hc-source-header o1e-authored fn-article-fields-octets))
           :use ((:instance o1e-source-header-is-authored-octets
                            (fs (fn-article-fields a))))))))

(local
 (defthm o1e-authored-source-parse
  (implies (and (fn-article-result-okp (fn-article-parse r))
                (fn-article-result-okp
                 (fn-article-parse
                  (fn-hc-authored-source (fn-article-result-article (fn-article-parse r))))))
           (and (equal (fn-article-fields
                        (fn-article-result-article
                         (fn-article-parse
                          (fn-hc-authored-source
                           (fn-article-result-article (fn-article-parse r))))))
                       (o1e-authored
                        (fn-article-fields (fn-article-result-article (fn-article-parse r)))))
                (true-listp
                 (fn-article-result-article
                  (fn-article-parse
                   (fn-hc-authored-source (fn-article-result-article (fn-article-parse r))))))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-ap-at-most-is-length-bound fn-article-ok fn-article-make
                            fn-article-fields fn-article-result-article)
                           (fn-article-parse fn-article-result-okp fn-hc-authored-source
                            o1e-authored fn-article-fields-octets
                            o1e-parse-of-fields o1e-authored-source-is-append))
           :use ((:instance o1e-parse-reconstructs (y r))
                 (:instance o1e-authored-source-is-append
                            (a (fn-article-result-article (fn-article-parse r))))
                 (:instance o1e-authored-fieldsvp
                            (fs (fn-article-fields (fn-article-result-article (fn-article-parse r)))))
                 (:instance o1e-parse-of-fields
                            (fs (o1e-authored
                                 (fn-article-fields (fn-article-result-article (fn-article-parse r)))))
                            (body (fn-article-body (fn-article-result-article (fn-article-parse r)))))
                 (:instance fn-article-successful-parse-input-octets
                            (octets (fn-hc-authored-source
                                     (fn-article-result-article (fn-article-parse r)))))
                 (:instance fn-article-successful-parse-input-bound
                            (octets (fn-hc-authored-source
                                     (fn-article-result-article (fn-article-parse r))))))))))

(local
 (defun o1e-fields-agree (fs gs)
  (declare (xargs :guard t :verify-guards nil))
  (and (equal (fn-article-get-headers-aux fs *fn-af-newsgroups-name*)
              (fn-article-get-headers-aux gs *fn-af-newsgroups-name*))
       (equal (fn-ctl-fields-named *fn-ctl-control-name* fs)
              (fn-ctl-fields-named *fn-ctl-control-name* gs))
       (equal (fn-ctl-fields-named *fn-ctl-supersedes-name* fs)
              (fn-ctl-fields-named *fn-ctl-supersedes-name* gs)))))

(local
 (defthm o1e-parse-article-true-listp
  (implies (fn-article-result-okp (fn-article-parse y))
           (true-listp (fn-article-result-article (fn-article-parse y))))
  :hints (("Goal" :use ((:instance fn-article-successful-parse-syntax-p (octets y)))
           :in-theory (e/d (fn-article-syntax-p) (fn-article-parse fn-article-result-article))))))

(local
 (defthm o1e-agree-source-newsgroups
  (implies (and (fn-article-result-okp (fn-article-parse s))
                (fn-article-result-okp (fn-article-parse r))
                (equal (fn-article-get-headers-aux
                        (fn-article-fields (fn-article-result-article (fn-article-parse s)))
                        *fn-af-newsgroups-name*)
                       (fn-article-get-headers-aux
                        (fn-article-fields (fn-article-result-article (fn-article-parse r)))
                        *fn-af-newsgroups-name*)))
           (equal (fn-o1-source-newsgroups s) (fn-o1-source-newsgroups r)))
  :hints (("Goal" :in-theory (e/d (fn-o1-source-newsgroups fn-af-newsgroups-status
                                   fn-article-get-headers)
                                  (fn-article-parse fn-article-get-headers-aux))))))

(local
 (defthm o1e-classify-fields-by-named
  (implies (and (equal (fn-ctl-fields-named *fn-ctl-control-name* fs)
                       (fn-ctl-fields-named *fn-ctl-control-name* gs))
                (equal (fn-ctl-fields-named *fn-ctl-supersedes-name* fs)
                       (fn-ctl-fields-named *fn-ctl-supersedes-name* gs)))
           (equal (fn-ctl-classify-fields fs) (fn-ctl-classify-fields gs)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ctl-classify-fields)
                                  (fn-ctl-fields-named fn-ctl-parse-command))))))

(local
 (defthm o1e-agree-classify
  (implies (and (fn-article-result-okp (fn-article-parse s))
                (fn-article-result-okp (fn-article-parse r))
                (equal (fn-ctl-fields-named
                        *fn-ctl-control-name*
                        (fn-article-fields (fn-article-result-article (fn-article-parse s))))
                       (fn-ctl-fields-named
                        *fn-ctl-control-name*
                        (fn-article-fields (fn-article-result-article (fn-article-parse r)))))
                (equal (fn-ctl-fields-named
                        *fn-ctl-supersedes-name*
                        (fn-article-fields (fn-article-result-article (fn-article-parse s))))
                       (fn-ctl-fields-named
                        *fn-ctl-supersedes-name*
                        (fn-article-fields (fn-article-result-article (fn-article-parse r))))))
           (equal (fn-ctl-classify-octets s) (fn-ctl-classify-octets r)))
  :hints (("Goal" :in-theory (e/d (fn-ctl-classify-octets fn-ctl-classify)
                                  (fn-article-parse fn-ctl-fields-named fn-ctl-parse-command
                                   fn-ctl-classify-fields fn-article-fields
                                   fn-article-result-article))
           :use (o1e-parse-article-true-listp
                 (:instance o1e-parse-article-true-listp (y r))
                 (:instance o1e-classify-fields-by-named
                            (fs (fn-article-fields (fn-article-result-article (fn-article-parse s))))
                            (gs (fn-article-fields (fn-article-result-article (fn-article-parse r))))))))))

(local
 (defthm o1e-filed-within-by-agreement
  (implies (and (fn-article-result-okp (fn-article-parse s))
                (fn-article-result-okp (fn-article-parse r))
                (o1e-fields-agree
                 (fn-article-fields (fn-article-result-article (fn-article-parse s)))
                 (fn-article-fields (fn-article-result-article (fn-article-parse r))))
                (fn-o1-filed-within-sourcep g s))
           (fn-o1-filed-within-sourcep g r))
  :hints (("Goal"
           :in-theory (e/d (o1e-fields-agree fn-o1-filed-within-sourcep fn-o1-control-filedp)
                           (fn-article-parse fn-article-get-headers-aux fn-ctl-fields-named
                            fn-o1-source-newsgroups fn-ctl-classify-octets))
           :use (o1e-agree-source-newsgroups o1e-agree-classify)))))

(local
 (defthm o1e-get-headers-aux-authored
  (implies (not (fn-hc-reserved-namep (fn-article-ascii-downcase name)))
           (equal (fn-article-get-headers-aux (o1e-authored fs) name)
                  (fn-article-get-headers-aux fs name)))
  :hints (("Goal" :induct (o1e-authored fs)
           :in-theory (enable fn-article-get-headers-aux fn-article-field-name-equalp)))))

(local
 (defthm o1e-fields-named-authored
  (implies (and name (not (fn-hc-reserved-namep name)))
           (equal (fn-ctl-fields-named name (o1e-authored fs))
                  (fn-ctl-fields-named name fs)))
  :hints (("Goal" :induct (o1e-authored fs)
           :in-theory (enable fn-ctl-fields-named fn-ctl-field-name)))))

(local
 (defthm o1e-authored-agrees
  (o1e-fields-agree (o1e-authored fs) fs)
  :hints (("Goal" :in-theory (e/d (o1e-fields-agree) (o1e-authored fn-article-get-headers-aux
                                                       fn-ctl-fields-named))))))

(local
 (defthm o1e-received-plan-facts
  (implies (fn-hc-okp (fn-hc-received-plan original))
           (and (fn-article-result-okp (fn-article-parse original))
                (equal (car (fn-hc-value (fn-hc-received-plan original)))
                       (fn-hc-authored-source
                        (fn-article-result-article (fn-article-parse original))))
                (fn-article-result-okp
                 (fn-article-parse (car (fn-hc-value (fn-hc-received-plan original)))))))
  :hints (("Goal" :in-theory (e/d (fn-hc-received-plan fn-hc-ok fn-hc-error fn-hc-okp fn-hc-value)
                                  (fn-article-parse fn-hc-authored-source fn-hc-field-decode-at
                                   fn-hc-count-name fn-hc-find-name fn-hc-no-other-reservedp
                                   fn-hc-required-sourcep fn-hc-fields-nativep
                                   fn-article-field-unfolded-value fn-hsig-source-version))))))

(local
 (defthm o1e-received-filed-within
  (implies (and (fn-hc-okp (fn-hc-received-plan r))
                (fn-o1-filed-within-sourcep g (car (fn-hc-value (fn-hc-received-plan r)))))
           (fn-o1-filed-within-sourcep g r))
  :hints (("Goal"
           :in-theory (disable fn-hc-received-plan fn-hc-okp fn-hc-value fn-hc-authored-source
                               fn-article-parse fn-article-result-okp
                               fn-article-result-article o1e-authored
                               o1e-filed-within-by-agreement o1e-authored-source-parse
                               o1e-received-plan-facts o1e-authored-agrees
                               fn-o1-filed-within-sourcep)
           :use ((:instance o1e-received-plan-facts (original r))
                 (:instance o1e-authored-source-parse (r r))
                 (:instance o1e-authored-agrees
                            (fs (fn-article-fields
                                 (fn-article-result-article (fn-article-parse r)))))
                 (:instance o1e-filed-within-by-agreement
                            (s (car (fn-hc-value (fn-hc-received-plan r))))))))))

(local
 (defthm o1e-base-needs-projection
  (implies (not projection-ok)
           (not (fn-hsig-authorized-carried-submission-event-base
                 sequence txid generation keyring-generation enrolled-snapshot
                 msgid source received groups obligation-id content-subject
                 release-evidence charge principal keys signatures observed-ml-key
                 ed25519-observation ml-dsa-65-observation observation
                 projection-ok)))
  :hints (("Goal" :in-theory (enable fn-hsig-authorized-carried-submission-event-base)))))

(local
 (defthm o1e-pa-event-has-an-ok-plan
  (implies (fn-pa-authorized-event
            sequence txid generation msgid received groups obligation-id
            content-subject release-evidence charge snapshots
            observed-ml-key ed-observation ml-observation clock-observation)
           (let ((plan (fn-pa-current-plan received snapshots nil nil)))
             (and (consp plan) (eq (car plan) :ok))))
  :hints (("Goal" :in-theory (enable fn-pa-authorized-event)))))

(local
 (defthm o1e-pa-plan-source
  (implies (and (consp (fn-pa-current-plan received snapshots carried transitp))
                (eq (car (fn-pa-current-plan received snapshots carried transitp)) :ok))
           (and (fn-hc-okp (fn-hc-received-plan received))
                (equal (nth 1 (fn-pa-current-plan received snapshots carried transitp))
                       (car (fn-hc-value (fn-hc-received-plan received))))))
  :hints (("Goal" :in-theory (e/d (fn-pa-current-plan fn-pa-carrier-form)
                                  (fn-hc-received-plan fn-hc-okp fn-hc-value fn-pa-carrier-kind
                                   fn-hl-current-for-principal fn-hl-current-enrollment
                                   fn-pa-carriesp fn-pa-revoked-tombstonep))))))

(local
 (include-book "injection-invariants"))

(local
 (defthm o1e-plan-injected-facts
  (implies (fn-inj-injectedp (fn-hsig-injected-carrier-plan source principal keys signatures config observation))
           (and (fn-hc-render-at-most *fn-article-max-octets* source principal keys signatures)
                (not (fn-inj-supplies-pathp
                      (fn-hc-render-at-most *fn-article-max-octets* source principal keys signatures)))
                (equal (fn-hsig-injected-carrier-plan source principal keys signatures config observation)
                       (fn-inj-decide
                        (fn-hc-render-at-most *fn-article-max-octets* source principal keys signatures)
                        config observation))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-hsig-injected-carrier-plan fn-inj-refuse fn-inj-injectedp)))))

(local
 (defthm o1e-injected-config-facts
  (implies (fn-inj-injectedp (fn-inj-decide src config obs))
           (fn-inj-configp config))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-inj-decide fn-inj-refuse fn-inj-injectedp)
                                  (fn-article-parse fn-af-proto-article-check
                                   fn-article-result-okp fn-article-result-article
                                   fn-article-syntax-p fn-article-get-headers
                                   fn-clock-observationp fn-clock-has-wall
                                   fn-clock-wall fn-clock-monotonic
                                   fn-inj-path-reason fn-inj-block fn-inj-splice
                                   fn-inj-groups-admissiblep fn-inj-configp
                                   fn-inj-prefix fn-inj-date-octets fn-inj-instant-of
                                   fn-inj-generated-message-id fn-inj-append floor
                                   fn-inj-mandatory-reason fn-inj-other-reason))))))

(local
 (defun o1e-vchars-p (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (integerp (car xs)) (<= 33 (car xs)) (<= (car xs) 126)
           (o1e-vchars-p (cdr xs)))
    (null xs))))

(local
 (defthm o1e-vchars-facts
  (implies (o1e-vchars-p xs)
           (and (true-listp xs) (fn-article-crlf-freep xs)
                (fn-article-header-bytes-p xs) (fn-cbor-octet-listp xs)))
  :hints (("Goal" :in-theory (enable fn-article-header-bytes-p fn-article-header-bytep
                                     fn-article-vcharp fn-article-wspp
                                     fn-cbor-octet-listp fn-cbor-octetp)))))

(local
 (defthm o1e-vchars-have-a-vchar
  (implies (and (o1e-vchars-p xs) (consp xs)) (fn-article-has-vcharp xs))
  :hints (("Goal" :expand ((o1e-vchars-p xs) (fn-article-has-vcharp xs))
           :in-theory (enable fn-article-vcharp)))))

(local
 (defthm o1e-vchars-of-append
  (implies (and (o1e-vchars-p a) (o1e-vchars-p b)) (o1e-vchars-p (append a b)))))

(local
 (defthm o1e-split-colon-of-a-name
  (implies (and (fn-article-ftext-listp name) (true-listp acc))
           (equal (fn-article-split-colon-aux (append name (cons 58 rest)) acc)
                  (list :ok (append (reverse acc) name) rest)))
  :hints (("Goal" :induct (o1e-line-ind name acc 0)
           :in-theory (enable fn-article-split-colon-aux fn-article-ftextp)))))

(local
 (defthm o1e-new-field-of-a-name-line
  (implies (and (fn-article-namep name) (true-listp name) (o1e-vchars-p v))
           (equal (fn-article-new-field (append name (cons 58 (cons 32 v))))
                  (list :ok (fn-article-make-field
                             (list (append name (cons 58 (cons 32 v))))
                             (fn-article-ascii-downcase name)
                             (cons 32 v)))))
  :hints (("Goal" :in-theory (e/d (fn-article-new-field fn-article-namep
                                   fn-article-header-bytes-p fn-article-header-bytep
                                   fn-article-wspp)
                                  (o1e-split-colon-of-a-name))
           :use ((:instance o1e-split-colon-of-a-name (acc nil) (rest (cons 32 v))))))))

(local
 (defthm o1e-car-of-fold-up
  (implies (and (true-listp (car f)) (true-listp ls))
           (equal (car (o1e-fold-up f ls)) (append (car f) ls)))
  :hints (("Goal" :induct (o1e-fold-up f ls) :in-theory (enable fn-article-add-fold)))))

(local
 (defthm o1e-cadr-of-fold-up
  (equal (cadr (o1e-fold-up f ls)) (cadr f))
  :hints (("Goal" :induct (o1e-fold-up f ls) :in-theory (enable fn-article-add-fold)))))

(local
 (defthm o1e-closed-of-fold-up
  (implies (fn-article-has-vcharp (caddr f))
           (fn-article-has-vcharp (caddr (o1e-fold-up f ls))))
  :hints (("Goal" :induct (o1e-fold-up f ls) :in-theory (enable fn-article-add-fold)))))

(local
 (defthm o1e-fold-up-true-listp
  (implies (true-listp f) (true-listp (o1e-fold-up f ls)))
  :hints (("Goal" :induct (o1e-fold-up f ls) :in-theory (enable fn-article-add-fold)))))

(local
 (defthm o1e-built-field-v
  (implies (and (o1e-line-okp l1) (not (fn-article-wspp (car l1)))
                (fn-article-line-okp (fn-article-new-field l1))
                (o1e-folds-okp folds))
           (and (o1e-fieldvp (o1e-fold-up (fn-article-line-value (fn-article-new-field l1)) folds))
                (equal (car (o1e-fold-up (fn-article-line-value (fn-article-new-field l1)) folds))
                       (cons l1 folds))))
  :hints (("Goal" :in-theory (e/d (o1e-fieldvp)
                                  (fn-article-new-field fn-article-line-value
                                   o1e-fold-up o1e-car-of-fold-up))
           :use ((:instance o1e-car-of-fold-up
                            (f (fn-article-line-value (fn-article-new-field l1)))
                            (ls folds)))))))

(local
 (defthm o1e-ftext-facts
  (implies (fn-article-ftext-listp name)
           (and (fn-article-crlf-freep name)
                (implies (consp name) (not (fn-article-wspp (car name))))))
  :hints (("Goal" :in-theory (enable fn-article-ftext-listp fn-article-ftextp
                                     fn-article-wspp fn-article-crlf-freep)))))

(local
 (defthm o1e-vchars-true-listp
  (implies (o1e-vchars-p v) (true-listp v))
  :rule-classes :forward-chaining))

(local
 (defthm o1e-car-append
  (implies (consp a) (equal (car (append a b)) (car a)))))

(local
 (defthm o1e-name-line-field
  (implies (and (fn-article-namep name) (true-listp name) (o1e-vchars-p v) (consp v)
                (<= (+ (len name) 2 (len v)) 998))
           (let ((f (fn-article-line-value
                     (fn-article-new-field (append name (cons 58 (cons 32 v)))))))
             (and (o1e-fieldvp f) (o1e-closedp f) (true-listp f)
                  (equal (car f) (list (append name (cons 58 (cons 32 v)))))
                  (equal (cadr f) (fn-article-ascii-downcase name)))))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (o1e-line-okp fn-article-namep o1e-closedp
                            fn-article-line-value fn-article-make-field)
                           (fn-article-new-field
                            o1e-built-field-v o1e-new-field-of-a-name-line))
           :use ((:instance o1e-built-field-v
                            (l1 (append name (cons 58 (cons 32 v)))) (folds nil))
                 (:instance o1e-new-field-of-a-name-line)
                 (:instance o1e-vchars-facts (xs v))
                 (:instance o1e-ftext-facts)
                 (:instance fn-article-crlf-freep-append
                            (left name) (right (cons 58 (cons 32 v)))))))))

(local
 (defthm o1e-vchars-of-hc-take
  (implies (o1e-vchars-p xs) (o1e-vchars-p (fn-hc-take n xs)))
  :hints (("Goal" :in-theory (enable fn-hc-take)))))

(local
 (defthm o1e-vchars-of-hc-drop
  (implies (o1e-vchars-p xs) (o1e-vchars-p (fn-hc-drop n xs)))
  :hints (("Goal" :in-theory (enable fn-hc-drop)))))

(local
 (defthm o1e-len-hc-take
  (<= (len (fn-hc-take n xs)) (nfix n))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-hc-take)))))

(local
 (defthm o1e-hc-take-consp
  (implies (and (consp xs) (posp n)) (consp (fn-hc-take n xs)))
  :hints (("Goal" :expand ((fn-hc-take n xs))))))

(local
 (defun o1e-chunks (r)
  (declare (xargs :measure (len r) :verify-guards nil))
  (if (atom r)
      nil
    (cons (cons 9 (fn-hc-take 72 r))
          (o1e-chunks (fn-hc-drop 72 r))))))

(local
 (defthm o1e-fold-rest-is-lines
  (equal (fn-hc-fold-rest r) (fn-article-lines-octets (o1e-chunks r)))
  :hints (("Goal" :induct (o1e-chunks r)
           :in-theory (e/d (fn-hc-fold-rest fn-article-lines-octets)
                           (fn-hc-take fn-hc-drop))))))

(local
 (defthm o1e-chunks-okp
  (implies (o1e-vchars-p r) (o1e-folds-okp (o1e-chunks r)))
  :hints (("Goal" :induct (o1e-chunks r)
           :in-theory (e/d (o1e-line-okp fn-article-fold-linep fn-article-wspp
                            fn-article-header-bytes-p fn-article-header-bytep
                            fn-article-has-vcharp)
                           (fn-hc-take fn-hc-drop)))
          ("Subgoal *1/2" :use ((:instance o1e-vchars-facts (xs (fn-hc-take 72 r)))
                                (:instance o1e-vchars-have-a-vchar (xs (fn-hc-take 72 r)))
                                (:instance o1e-hc-take-consp (n 72) (xs r))
                                (:instance o1e-len-hc-take (n 72) (xs r)))))))

(local
 (defun o1e-fna-line (v)
  (declare (xargs :guard t :verify-guards nil))
  (append '(70 78 45 65 117 116 104 111 114 115 104 105 112)
          (cons 58 (cons 32 (fn-hc-take 72 v))))))

(local
 (defun o1e-fna-field (v)
  (declare (xargs :guard t :verify-guards nil))
  (o1e-fold-up (fn-article-line-value (fn-article-new-field (o1e-fna-line v)))
               (o1e-chunks (fn-hc-drop 72 v)))))

(local
 (defthm o1e-fna-field-facts
  (implies (and (o1e-vchars-p v) (consp v))
           (and (o1e-fieldvp (o1e-fna-field v))
                (o1e-closedp (o1e-fna-field v))
                (true-listp (o1e-fna-field v))
                (equal (cadr (o1e-fna-field v))
                       '(102 110 45 97 117 116 104 111 114 115 104 105 112))
                (equal (fn-article-lines-octets (car (o1e-fna-field v)))
                       (fn-hc-field-lines v))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (o1e-fna-field o1e-line-okp o1e-closedp fn-article-line-value
                            fn-article-make-field fn-article-namep fn-hc-field-lines)
                           (fn-article-new-field o1e-built-field-v o1e-new-field-of-a-name-line
                            o1e-fold-up fn-hc-take fn-hc-drop o1e-chunks
                            o1e-car-of-fold-up o1e-chunks-okp
                            fn-hc-fold-rest))
           :use ((:instance o1e-built-field-v
                            (l1 (o1e-fna-line v)) (folds (o1e-chunks (fn-hc-drop 72 v))))
                 (:instance o1e-new-field-of-a-name-line
                            (name '(70 78 45 65 117 116 104 111 114 115 104 105 112))
                            (v (fn-hc-take 72 v)))
                 (:instance o1e-chunks-okp (r (fn-hc-drop 72 v)))
                 (:instance o1e-closed-of-fold-up
                            (f (fn-article-line-value (fn-article-new-field (o1e-fna-line v))))
                            (ls (o1e-chunks (fn-hc-drop 72 v))))
                 (:instance o1e-cadr-of-fold-up
                            (f (fn-article-line-value (fn-article-new-field (o1e-fna-line v))))
                            (ls (o1e-chunks (fn-hc-drop 72 v))))
                 (:instance o1e-vchars-facts (xs (fn-hc-take 72 v)))
                 (:instance o1e-vchars-have-a-vchar (xs (fn-hc-take 72 v)))
                 (:instance o1e-vchars-of-hc-take (n 72) (xs v))
                 (:instance o1e-hc-take-consp (n 72) (xs v))
                 (:instance o1e-len-hc-take (n 72) (xs v))
                 (:instance o1e-fold-rest-is-lines (r (fn-hc-drop 72 v)))
                 (:instance o1e-fold-up-true-listp
                            (f (fn-article-line-value (fn-article-new-field (o1e-fna-line v))))
                            (ls (o1e-chunks (fn-hc-drop 72 v)))))))))

(local
 (defthm o1e-vchars-of-b64-encode
  (o1e-vchars-p (fn-stx-b64-encode x))
  :hints (("Goal" :induct (fn-stx-b64-encode x)
           :in-theory (e/d (fn-stx-b64-encode) (fn-stx-b64-sextet))))))

(local
 (defthm o1e-field-encode-is-vchars
  (o1e-vchars-p (fn-hc-field-encode-at version principal keys signatures))
  :hints (("Goal" :in-theory (enable fn-hc-field-encode-at)))))

(local
 (defthm o1e-render-at-most-facts
  (implies (fn-hc-render-at-most max source principal keys signatures)
           (let ((field (fn-hc-field-encode-at (fn-hsig-source-version source)
                                               principal keys signatures)))
             (and (consp field)
                  (equal (fn-hc-render-at-most max source principal keys signatures)
                         (append (fn-hc-field-lines field) source))
                  (fn-article-result-okp (fn-article-parse source))
                  (fn-hc-required-sourcep (fn-article-result-article (fn-article-parse source)))
                  (fn-hc-fields-nativep
                   (fn-article-fields (fn-article-result-article (fn-article-parse source))))
                  (fn-cbor-octet-listp (fn-hc-render-at-most max source principal keys signatures))
                  (<= (len (fn-hc-render-at-most max source principal keys signatures))
                      max))))
  :hints (("Goal"
           :in-theory (e/d (fn-hc-render-at-most fn-hc-render fn-hc-native-plan fn-hc-ok
                            fn-hc-error fn-hc-okp fn-hc-value fn-ap-at-most-is-length-bound)
                           (fn-article-parse fn-hc-required-sourcep fn-hc-fields-nativep
                            fn-hc-field-encode-at fn-hc-field-lines fn-hsig-source-version
                            fn-article-result-okp fn-article-result-article fn-article-fields
                            fn-cbor-octet-listp))
           :use ((:instance o1e-field-encode-is-vchars
                            (version (fn-hsig-source-version source))))))))

(local
 (defthm o1e-fields-octets-append
  (equal (fn-article-fields-octets (append a b))
         (append (fn-article-fields-octets a) (fn-article-fields-octets b)))
  :hints (("Goal" :induct (fn-article-fields-octets a)
           :in-theory (enable fn-article-fields-octets)))))

(local
 (defthm o1e-prepend-parse
  (implies (and (fn-article-result-okp (fn-article-parse source))
                (o1e-fieldsvp pre)
                (fn-cbor-octet-listp (append (fn-article-fields-octets pre) source))
                (<= (len (append (fn-article-fields-octets pre) source))
                    *fn-article-max-octets*))
           (and (fn-article-result-okp
                 (fn-article-parse (append (fn-article-fields-octets pre) source)))
                (equal (fn-article-fields
                        (fn-article-result-article
                         (fn-article-parse (append (fn-article-fields-octets pre) source))))
                       (append pre (fn-article-fields
                                    (fn-article-result-article (fn-article-parse source)))))
                (true-listp
                 (fn-article-result-article
                  (fn-article-parse (append (fn-article-fields-octets pre) source))))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-article-ok fn-article-make fn-article-fields
                            fn-article-result-article fn-article-result-okp)
                           (fn-article-parse o1e-parse-of-fields fn-article-fields-octets
                            o1e-fields-octets-append o1e-fieldsvp-append
                            fn-article-successful-parse-is-parse-lines))
           :use ((:instance o1e-parse-reconstructs (y source))
                 (:instance o1e-parse-of-fields
                            (fs (append pre (fn-article-fields
                                             (fn-article-result-article (fn-article-parse source)))))
                            (body (fn-article-body (fn-article-result-article (fn-article-parse source)))))
                 (:instance o1e-fields-octets-append
                            (a pre) (b (fn-article-fields
                                        (fn-article-result-article (fn-article-parse source)))))
                 (:instance o1e-fieldsvp-append
                            (a pre) (b (fn-article-fields
                                        (fn-article-result-article (fn-article-parse source))))))))))

(local
 (defthm o1e-dot-atom-is-vchars
  (implies (and (true-listp bytes) (fn-af-dot-atom-text-aux bytes want-atext))
           (o1e-vchars-p bytes))
  :rule-classes nil
  :hints (("Goal" :induct (fn-af-dot-atom-text-aux bytes want-atext)
           :in-theory (enable fn-af-dot-atom-text-aux fn-af-atextp)))))

(local
 (defthm o1e-config-agent-facts
  (implies (fn-inj-configp config)
           (and (o1e-vchars-p (fn-inj-config-agent config))
                (consp (fn-inj-config-agent config))
                (<= (len (fn-inj-config-agent config)) 128)
                (fn-cbor-octet-listp (fn-inj-config-agent config))))
  :hints (("Goal" :in-theory (e/d (fn-inj-configp fn-af-dot-atom-textp)
                                  (fn-af-dot-atom-text-aux fn-inj-config-agent))
           :use ((:instance o1e-dot-atom-is-vchars
                            (bytes (fn-inj-config-agent config)) (want-atext t))
                 (:instance fn-article-octet-list-true-listp
                            (octets (fn-inj-config-agent config))))))))

(local
 (defthm o1e-path-field-facts
  (implies (and (o1e-vchars-p agent) (consp agent) (<= (len agent) 128))
           (let ((f (fn-article-line-value
                     (fn-article-new-field
                      (append '(80 97 116 104)
                              (cons 58 (cons 32 (append agent '(33 110 111 116 45 102 111 114 45 109 97 105 108)))))))))
             (and (o1e-fieldvp f) (o1e-closedp f) (true-listp f)
                  (equal (car f)
                         (list (append '(80 97 116 104)
                                       (cons 58 (cons 32 (append agent '(33 110 111 116 45 102 111 114 45 109 97 105 108)))))))
                  (equal (cadr f) '(112 97 116 104)))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (fn-article-namep) (fn-article-new-field
                                              fn-article-line-value))
           :use ((:instance o1e-name-line-field
                            (name '(80 97 116 104))
                            (v (append agent '(33 110 111 116 45 102 111 114 45 109 97 105 108))))
                 (:instance o1e-vchars-of-append
                            (a agent) (b '(33 110 111 116 45 102 111 114 45 109 97 105 108))))))))

(local
 (defthm o1e-info-field-facts
  (implies (and (o1e-vchars-p agent) (consp agent) (<= (len agent) 128))
           (let ((f (fn-article-line-value
                     (fn-article-new-field
                      (append '(73 110 106 101 99 116 105 111 110 45 73 110 102 111)
                              (cons 58 (cons 32 agent)))))))
             (and (o1e-fieldvp f) (o1e-closedp f) (true-listp f)
                  (equal (car f)
                         (list (append '(73 110 106 101 99 116 105 111 110 45 73 110 102 111)
                                       (cons 58 (cons 32 agent)))))
                  (equal (cadr f) '(105 110 106 101 99 116 105 111 110 45 105 110 102 111)))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (fn-article-namep) (fn-article-new-field
                                              fn-article-line-value))
           :use ((:instance o1e-name-line-field
                            (name '(73 110 106 101 99 116 105 111 110 45 73 110 102 111))
                            (v agent)))))))

(local
 (defthm o1e-get-headers-aux-skip
  (implies (not (equal (fn-article-field-name g) (fn-article-ascii-downcase name)))
           (equal (fn-article-get-headers-aux (cons g fs) name)
                  (fn-article-get-headers-aux fs name)))
  :hints (("Goal" :expand ((fn-article-get-headers-aux (cons g fs) name))
           :in-theory (enable fn-article-field-name-equalp)))))

(local
 (defun o1e-prefix-clearp (pre)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp pre)
      (and (true-listp (car pre))
           (not (equal (cadr (car pre)) *fn-af-newsgroups-name*))
           (not (equal (cadr (car pre)) *fn-ctl-control-name*))
           (not (equal (cadr (car pre)) *fn-ctl-supersedes-name*))
           (o1e-prefix-clearp (cdr pre)))
    t)))

(local
 (defthm o1e-prefix-agrees
  (implies (o1e-prefix-clearp pre)
           (o1e-fields-agree (append pre fs) fs))
  :hints (("Goal" :induct (o1e-prefix-clearp pre)
           :in-theory (e/d (o1e-fields-agree fn-ctl-fields-named fn-ctl-field-name
                            fn-article-get-headers-aux fn-article-field-name-equalp)
                           ())))))

(local
 (defthm o1e-proto-check-skip
  (implies (and (equal (fn-article-fields a) (cons g (fn-article-fields b)))
                (equal (fn-article-field-name g)
                       '(102 110 45 97 117 116 104 111 114 115 104 105 112)))
           (and (equal (fn-af-proto-article-check a) (fn-af-proto-article-check b))
                (equal (fn-article-get-headers a *fn-inj-date-name*)
                       (fn-article-get-headers b *fn-inj-date-name*))))
  :hints (("Goal" :in-theory (e/d (fn-af-proto-article-check fn-af-relayed-article-check
                                   fn-af-newsgroups-status fn-af-message-id-status
                                   fn-article-get-headers)
                                  (fn-article-get-headers-aux fn-af-message-id-field-value
                                   fn-af-newsgroups-field-value))))))

(local
 (defthm o1e-nativep-no-header
  (implies (and (fn-hc-fields-nativep fs)
                (fn-hc-reserved-namep (fn-article-ascii-downcase name)))
           (equal (fn-article-get-headers-aux fs name) nil))
  :hints (("Goal" :induct (fn-hc-fields-nativep fs)
           :in-theory (enable fn-hc-fields-nativep fn-article-get-headers-aux
                              fn-article-field-name-equalp)))))

(local
 (defthm o1e-message-id-single-has-a-value
  (implies (equal (car (fn-af-message-id-status a)) :single)
           (cadr (fn-af-message-id-status a)))
  :hints (("Goal" :in-theory (enable fn-af-message-id-status)))))

(local
 (defthm o1e-source-proto-check
  (implies (and (fn-hc-required-sourcep a) (fn-hc-fields-nativep (fn-article-fields a)))
           (fn-inj-nth 1 (fn-af-proto-article-check a)))
  :hints (("Goal" :in-theory (e/d (fn-af-proto-article-check fn-af-relayed-article-check
                                   fn-hc-required-sourcep fn-article-get-headers
                                   fn-af-status-kind fn-af-status-value fn-inj-nth fn-inj-car fn-inj-cdr
                                   fn-af-newsgroups-status)
                                  (fn-article-get-headers-aux fn-af-message-id-status
                                   fn-af-newsgroups-field-value fn-hc-fields-nativep
                                   fn-article-syntax-p fn-inj-single-fieldp))
           :use ((:instance o1e-nativep-no-header (fs (fn-article-fields a))
                            (name *fn-af-injection-info-name*))
                 (:instance o1e-nativep-no-header (fs (fn-article-fields a))
                            (name *fn-af-xref-name*))
                 (:instance o1e-message-id-single-has-a-value))))))

(local
 (defthm o1e-carrier-parse
  (implies (and (fn-article-result-okp (fn-article-parse source))
                (o1e-vchars-p field) (consp field)
                (fn-cbor-octet-listp (append (fn-hc-field-lines field) source))
                (<= (len (append (fn-hc-field-lines field) source)) *fn-article-max-octets*))
           (and (fn-article-result-okp
                 (fn-article-parse (append (fn-hc-field-lines field) source)))
                (equal (fn-article-fields
                        (fn-article-result-article
                         (fn-article-parse (append (fn-hc-field-lines field) source))))
                       (cons (o1e-fna-field field)
                             (fn-article-fields
                              (fn-article-result-article (fn-article-parse source)))))
                (true-listp
                 (fn-article-result-article
                  (fn-article-parse (append (fn-hc-field-lines field) source))))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-article-fields-octets)
                           (fn-article-parse o1e-prepend-parse o1e-fna-field-facts
                            fn-hc-field-lines o1e-fna-field))
           :use ((:instance o1e-fna-field-facts (v field))
                 (:instance o1e-prepend-parse (pre (list (o1e-fna-field field)))))))))

(local
 (defthm o1e-carrier-facts
  (implies (fn-inj-injectedp
            (fn-hsig-injected-carrier-plan source principal keys signatures config observation))
           (let* ((field (fn-hc-field-encode-at (fn-hsig-source-version source)
                                                principal keys signatures))
                  (carrier (fn-hc-render-at-most *fn-article-max-octets* source principal keys signatures))
                  (ac (fn-article-result-article (fn-article-parse carrier)))
                  (as (fn-article-result-article (fn-article-parse source))))
             (and (consp field) (o1e-vchars-p field)
                  (equal carrier (append (fn-hc-field-lines field) source))
                  (fn-article-result-okp (fn-article-parse source))
                  (fn-article-result-okp (fn-article-parse carrier))
                  (equal (fn-article-fields ac) (cons (o1e-fna-field field) (fn-article-fields as)))
                  (fn-hc-required-sourcep as)
                  (fn-hc-fields-nativep (fn-article-fields as))
                  (fn-cbor-octet-listp carrier)
                  (<= (len carrier) *fn-article-max-octets*)
                  (equal (fn-article-field-name (o1e-fna-field field))
                         '(102 110 45 97 117 116 104 111 114 115 104 105 112)))))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable fn-hsig-injected-carrier-plan fn-hc-render-at-most
                               fn-hc-field-encode-at fn-hsig-source-version fn-hc-field-lines
                               fn-article-parse fn-article-result-article fn-article-result-okp
                               fn-hc-required-sourcep fn-hc-fields-nativep o1e-fna-field
                               fn-article-fields fn-cbor-octet-listp o1e-render-at-most-facts
                               o1e-carrier-parse o1e-fna-field-facts)
           :use (o1e-plan-injected-facts
                 (:instance o1e-render-at-most-facts (max *fn-article-max-octets*))
                 (:instance o1e-field-encode-is-vchars
                            (version (fn-hsig-source-version source)))
                 (:instance o1e-fna-field-facts
                            (v (fn-hc-field-encode-at (fn-hsig-source-version source)
                                                      principal keys signatures)))
                 (:instance o1e-carrier-parse
                            (field (fn-hc-field-encode-at (fn-hsig-source-version source)
                                                          principal keys signatures))))))))

(local
 (defthm o1e-injection-hyps
  (implies (fn-inj-injectedp
            (fn-hsig-injected-carrier-plan source principal keys signatures config observation))
           (let* ((carrier (fn-hc-render-at-most *fn-article-max-octets* source principal keys signatures))
                  (ac (fn-article-result-article (fn-article-parse carrier))))
             (and (fn-inj-nth 1 (fn-af-proto-article-check ac))
                  (not (fn-inj-absentp ac *fn-inj-date-name*)))))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-inj-absentp fn-hc-required-sourcep fn-inj-single-fieldp)
                           (fn-hsig-injected-carrier-plan fn-hc-render-at-most
                            fn-hc-field-encode-at fn-hsig-source-version fn-hc-field-lines
                            fn-article-parse fn-article-result-article fn-article-result-okp
                            fn-hc-fields-nativep o1e-fna-field fn-af-proto-article-check
                            fn-article-fields fn-cbor-octet-listp
                            fn-article-get-headers o1e-proto-check-skip o1e-source-proto-check
                            fn-inj-nth fn-article-syntax-p
                            fn-article-successful-parse-is-parse-lines))
           :use (o1e-carrier-facts
                 (:instance o1e-proto-check-skip
                            (a (fn-article-result-article
                                (fn-article-parse
                                 (fn-hc-render-at-most *fn-article-max-octets* source principal keys signatures))))
                            (b (fn-article-result-article (fn-article-parse source)))
                            (g (o1e-fna-field (fn-hc-field-encode-at (fn-hsig-source-version source)
                                                                     principal keys signatures))))
                 (:instance o1e-source-proto-check
                            (a (fn-article-result-article (fn-article-parse source)))))))))

(local
 (defthm o1e-injected-octets
  (implies (fn-inj-injectedp
            (fn-hsig-injected-carrier-plan source principal keys signatures config observation))
           (equal (fn-inj-decision-octets
                   (fn-hsig-injected-carrier-plan source principal keys signatures config observation))
                  (fn-inj-append
                   (fn-inj-path-line (fn-inj-config-agent config))
                   (fn-inj-append
                    (fn-inj-injection-info-line (fn-inj-config-agent config))
                    (fn-hc-render-at-most *fn-article-max-octets* source principal keys signatures)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable fn-hsig-injected-carrier-plan fn-hc-render-at-most
                               fn-inj-decide fn-inj-injectedp fn-inj-supplies-pathp
                               fn-inj-decision-octets fn-inj-path-line
                               fn-inj-injection-info-line fn-inj-append
                               fn-af-proto-article-check fn-inj-nth fn-inj-absentp
                               fn-article-parse fn-article-result-article
                               fn-article-successful-parse-is-parse-lines)
           :use (o1e-plan-injected-facts
                 o1e-injection-hyps
                 (:instance fn-inj-no-injection-date-when-date-and-message-id-are-supplied
                            (source (fn-hc-render-at-most *fn-article-max-octets* source principal keys signatures))))))))

(local
 (defun o1e-path-field (agent)
  (declare (xargs :guard t :verify-guards nil))
  (fn-article-line-value
   (fn-article-new-field
    (append '(80 97 116 104)
            (cons 58 (cons 32 (append agent '(33 110 111 116 45 102 111 114 45 109 97 105 108)))))))))

(local
 (defun o1e-info-field (agent)
  (declare (xargs :guard t :verify-guards nil))
  (fn-article-line-value
   (fn-article-new-field
    (append '(73 110 106 101 99 116 105 111 110 45 73 110 102 111)
            (cons 58 (cons 32 agent)))))))

(local
 (defun o1e-prefix (agent field)
  (declare (xargs :guard t :verify-guards nil))
  (list (o1e-path-field agent) (o1e-info-field agent) (o1e-fna-field field))))

(local
 (defthm o1e-fn-inj-append-is-append
  (equal (fn-inj-append a b) (append a b))
  :hints (("Goal" :in-theory (enable fn-inj-append)))))

(local
 (defthm o1e-prefix-facts
  (implies (and (o1e-vchars-p agent) (consp agent) (<= (len agent) 128)
                (o1e-vchars-p field) (consp field))
           (and (o1e-fieldsvp (o1e-prefix agent field))
                (o1e-prefix-clearp (o1e-prefix agent field))
                (equal (fn-article-fields-octets (o1e-prefix agent field))
                       (append (fn-inj-path-line agent)
                               (append (fn-inj-injection-info-line agent)
                                       (fn-hc-field-lines field))))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (o1e-prefix o1e-path-field o1e-info-field o1e-fieldsvp
                            fn-article-fields-octets fn-article-lines-octets
                            fn-inj-path-line fn-inj-injection-info-line
                            o1e-prefix-clearp)
                           (fn-article-new-field fn-article-line-value
                            o1e-fna-field fn-hc-field-lines
                            o1e-fieldvp o1e-closedp))
           :use (o1e-path-field-facts o1e-info-field-facts
                 (:instance o1e-fna-field-facts (v field)))))))

(local
 (defthm o1e-octet-listp-append
  (implies (true-listp a)
           (equal (fn-cbor-octet-listp (append a b))
                  (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp b))))
  :hints (("Goal" :induct (fn-cbor-octet-listp a)))))

(local
 (defthm o1e-fields-agree-sym
  (equal (o1e-fields-agree fs gs) (o1e-fields-agree gs fs))
  :hints (("Goal" :in-theory (enable o1e-fields-agree)))))

(local
 (defthm o1e-trace-lines-are-octets
  (implies (fn-cbor-octet-listp agent)
           (and (fn-cbor-octet-listp (fn-inj-path-line agent))
                (fn-cbor-octet-listp (fn-inj-injection-info-line agent))))
  :hints (("Goal" :in-theory (e/d (fn-inj-path-line fn-inj-injection-info-line)
                                  (o1e-octet-listp-append))
           :use ((:instance fn-article-octet-list-true-listp (octets agent)))))))

(local
 (defthm o1e-config-max-is-within-the-ceiling
  (implies (fn-inj-configp config)
           (<= (fn-inj-config-max-octets config) *fn-article-max-octets*))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-inj-configp)))))

(local
 (defthm o1e-plan-config
  (implies (fn-inj-injectedp
            (fn-hsig-injected-carrier-plan source principal keys signatures config observation))
           (fn-inj-configp config))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable fn-hsig-injected-carrier-plan fn-hc-render-at-most fn-inj-decide
                               fn-inj-injectedp fn-inj-configp)
           :use (o1e-plan-injected-facts
                 (:instance o1e-injected-config-facts
                            (src (fn-hc-render-at-most *fn-article-max-octets* source principal keys
                                                       signatures))
                            (config config) (obs observation)))))))

(local
 (defthm o1e-received-eq
  (implies (fn-inj-injectedp
            (fn-hsig-injected-carrier-plan source principal keys signatures config observation))
           (equal (fn-inj-decision-octets
                   (fn-hsig-injected-carrier-plan source principal keys signatures config observation))
                  (append (fn-article-fields-octets
                           (o1e-prefix (fn-inj-config-agent config)
                                       (fn-hc-field-encode-at (fn-hsig-source-version source)
                                                              principal keys signatures)))
                          source)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable fn-hsig-injected-carrier-plan fn-hc-render-at-most fn-inj-decide
                               fn-inj-injectedp fn-inj-configp fn-hc-field-encode-at
                               fn-hsig-source-version fn-hc-field-lines fn-inj-decision-octets
                               fn-inj-path-line fn-inj-injection-info-line o1e-prefix
                               fn-article-fields-octets fn-inj-config-agent o1e-prefix-facts
                               fn-article-parse fn-article-result-article fn-article-result-okp
                               o1e-vchars-p o1e-injected-octets
                               o1e-plan-config o1e-config-agent-facts)
           :use (o1e-injected-octets o1e-carrier-facts o1e-plan-config
                 (:instance o1e-config-agent-facts)
                 (:instance o1e-prefix-facts
                            (agent (fn-inj-config-agent config))
                            (field (fn-hc-field-encode-at (fn-hsig-source-version source)
                                                          principal keys signatures))))))))

(local
 (defthm o1e-received-bounds
  (implies (fn-inj-injectedp
            (fn-hsig-injected-carrier-plan source principal keys signatures config observation))
           (and (fn-cbor-octet-listp
                 (fn-inj-decision-octets
                  (fn-hsig-injected-carrier-plan source principal keys signatures config observation)))
                (<= (len (fn-inj-decision-octets
                          (fn-hsig-injected-carrier-plan source principal keys signatures config observation)))
                    *fn-article-max-octets*)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable fn-hsig-injected-carrier-plan fn-hc-render-at-most fn-inj-decide
                               fn-inj-injectedp fn-inj-configp fn-hc-field-encode-at
                               fn-hsig-source-version fn-hc-field-lines fn-inj-decision-octets
                               fn-inj-path-line fn-inj-injection-info-line o1e-prefix
                               fn-article-fields-octets fn-inj-config-agent
                               fn-article-parse fn-article-result-article fn-article-result-okp
                               fn-cbor-octet-listp fn-inj-config-max-octets
                               o1e-config-max-is-within-the-ceiling o1e-trace-lines-are-octets
                               o1e-config-agent-facts o1e-octet-listp-append)
           :use (o1e-injected-octets o1e-carrier-facts o1e-plan-config o1e-plan-injected-facts
                 (:instance o1e-config-agent-facts)
                 (:instance o1e-config-max-is-within-the-ceiling)
                 (:instance o1e-trace-lines-are-octets (agent (fn-inj-config-agent config)))
                 (:instance o1e-octet-listp-append
                            (a (fn-inj-path-line (fn-inj-config-agent config)))
                            (b (append (fn-inj-injection-info-line (fn-inj-config-agent config))
                                       (fn-hc-render-at-most *fn-article-max-octets* source
                                                             principal keys signatures))))
                 (:instance o1e-octet-listp-append
                            (a (fn-inj-injection-info-line (fn-inj-config-agent config)))
                            (b (fn-hc-render-at-most *fn-article-max-octets* source
                                                     principal keys signatures)))
                 (:instance fn-inj-injected-article-is-within-the-configured-bound
                            (source (fn-hc-render-at-most *fn-article-max-octets* source
                                                          principal keys signatures))
                            (observation observation)))))))

(local
 (defthm o1e-injected-received-filed-within
  (implies (and (fn-inj-injectedp
                 (fn-hsig-injected-carrier-plan source principal keys signatures config observation))
                (equal received
                       (fn-inj-decision-octets
                        (fn-hsig-injected-carrier-plan source principal keys signatures config observation)))
                (fn-o1-filed-within-sourcep groups source))
           (fn-o1-filed-within-sourcep groups received))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable fn-hsig-injected-carrier-plan fn-hc-render-at-most fn-inj-decide
                               fn-inj-injectedp fn-inj-configp fn-hc-field-encode-at
                               fn-hsig-source-version fn-hc-field-lines fn-inj-decision-octets
                               fn-inj-path-line fn-inj-injection-info-line o1e-prefix
                               fn-article-fields-octets fn-inj-config-agent
                               fn-article-parse fn-article-result-article fn-article-result-okp
                               fn-cbor-octet-listp fn-o1-filed-within-sourcep
                               o1e-received-eq o1e-received-bounds o1e-prepend-parse
                               o1e-filed-within-by-agreement o1e-prefix-agrees
                               o1e-prefix-facts o1e-config-agent-facts
                               o1e-plan-config o1e-fields-agree-sym o1e-injected-octets
                               fn-article-successful-parse-is-parse-lines)
           :use (o1e-received-eq o1e-received-bounds o1e-carrier-facts o1e-plan-config
                 (:instance o1e-config-agent-facts)
                 (:instance o1e-prefix-facts
                            (agent (fn-inj-config-agent config))
                            (field (fn-hc-field-encode-at (fn-hsig-source-version source)
                                                          principal keys signatures)))
                 (:instance o1e-prepend-parse
                            (pre (o1e-prefix (fn-inj-config-agent config)
                                             (fn-hc-field-encode-at (fn-hsig-source-version source)
                                                                    principal keys signatures))))
                 (:instance o1e-prefix-agrees
                            (pre (o1e-prefix (fn-inj-config-agent config)
                                             (fn-hc-field-encode-at (fn-hsig-source-version source)
                                                                    principal keys signatures)))
                            (fs (fn-article-fields (fn-article-result-article (fn-article-parse source)))))
                 (:instance o1e-filed-within-by-agreement
                            (s source) (r received) (g groups)))))))

(defthm fn-hsig-injected-groups-filed-within-the-received
  (implies (fn-hsig-authorized-injected-carried-submission-event
            sequence txid generation keyring-generation enrolled-snapshot
            msgid source received groups obligation-id content-subject
            release-evidence charge principal keys signatures observed-ml-key
            ed25519-observation ml-dsa-65-observation config observation)
           (fn-o1-filed-within-sourcep groups received))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable fn-hsig-injected-carrier-plan fn-inj-injectedp fn-inj-decision-octets
                               fn-o1-filed-within-sourcep
                               fn-hsig-authorized-carried-submission-event-base
                               o1e-base-needs-projection o1e-injected-received-filed-within)
           :expand ((fn-hsig-authorized-injected-carried-submission-event
                     sequence txid generation keyring-generation enrolled-snapshot
                     msgid source received groups obligation-id content-subject
                     release-evidence charge principal keys signatures observed-ml-key
                     ed25519-observation ml-dsa-65-observation config observation))
           :use ((:instance o1e-base-needs-projection
                            (observation observation)
                            (projection-ok
                             (and (fn-inj-injectedp
                                   (fn-hsig-injected-carrier-plan source principal keys signatures config observation))
                                  (equal received
                                         (fn-inj-decision-octets
                                          (fn-hsig-injected-carrier-plan source principal keys signatures config observation))))))
                 (:instance fn-hsig-carried-groups-filed-within-the-source
                            (projection-ok
                             (and (fn-inj-injectedp
                                   (fn-hsig-injected-carrier-plan source principal keys signatures config observation))
                                  (equal received
                                         (fn-inj-decision-octets
                                          (fn-hsig-injected-carrier-plan source principal keys signatures config observation))))))
                 (:instance o1e-injected-received-filed-within)))))

(defthm fn-pa-authorized-groups-filed-within-the-received
  (implies (fn-pa-authorized-event
            sequence txid generation msgid received groups obligation-id
            content-subject release-evidence charge snapshots
            observed-ml-key ed-observation ml-observation clock-observation)
           (fn-o1-filed-within-sourcep groups received))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (disable fn-pa-current-plan fn-hc-received-plan fn-hc-okp fn-hc-value
                               fn-o1-filed-within-sourcep
                               fn-hsig-authorized-carried-submission-event-base
                               o1e-received-filed-within o1e-pa-plan-source
                               o1e-pa-event-has-an-ok-plan o1e-base-needs-projection)
           :expand ((fn-pa-authorized-event
                     sequence txid generation msgid received groups obligation-id
                     content-subject release-evidence charge snapshots
                     observed-ml-key ed-observation ml-observation clock-observation))
           :use (o1e-pa-event-has-an-ok-plan
                 (:instance o1e-pa-plan-source (carried nil) (transitp nil))
                 (:instance o1e-received-filed-within (r received) (g groups))
                 (:instance o1e-base-needs-projection
                            (keyring-generation (nth 6 (fn-pa-current-plan received snapshots nil nil)))
                            (enrolled-snapshot (fn-stxk-snapshot (nth 5 (fn-pa-current-plan received snapshots nil nil))))
                            (source (nth 1 (fn-pa-current-plan received snapshots nil nil)))
                            (principal (nth 2 (fn-pa-current-plan received snapshots nil nil)))
                            (keys (nth 3 (fn-pa-current-plan received snapshots nil nil)))
                            (signatures (nth 4 (fn-pa-current-plan received snapshots nil nil)))
                            (ed25519-observation ed-observation)
                            (ml-dsa-65-observation ml-observation)
                            (observation clock-observation)
                            (projection-ok (fn-hc-okp (fn-hc-received-plan received))))
                 (:instance fn-hsig-carried-groups-filed-within-the-source
                            (keyring-generation (nth 6 (fn-pa-current-plan received snapshots nil nil)))
                            (enrolled-snapshot (fn-stxk-snapshot (nth 5 (fn-pa-current-plan received snapshots nil nil))))
                            (source (nth 1 (fn-pa-current-plan received snapshots nil nil)))
                            (principal (nth 2 (fn-pa-current-plan received snapshots nil nil)))
                            (keys (nth 3 (fn-pa-current-plan received snapshots nil nil)))
                            (signatures (nth 4 (fn-pa-current-plan received snapshots nil nil)))
                            (ed25519-observation ed-observation)
                            (ml-dsa-65-observation ml-observation)
                            (observation clock-observation)
                            (projection-ok (fn-hc-okp (fn-hc-received-plan received))))))))
