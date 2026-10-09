; article-stream-owner-bridge.lisp -- the catalog-started capture and the walk-started
; capture take the same READY step (lane article-index-2, 2026-10-07).
;
; books/article-stream-owner.lisp equates the selection start the owner's capture
; installs (the catalog's, fn-asto-selection-start-cat) with the archive walk at the
; selection's START.  The READY step runs the walk: fn-asto-selection-ready steps
; the selection state and reads only the outcome fields of the result (mode,
; group, number, phase, and the article when selected: fn-asx-outcome).  So two
; captures that differ in their selection only, and whose selections step to one
; outcome, take one READY step.
(in-package "ACL2")
(include-book "article-stream-owner")
(include-book "served-catalog-join-conns")
(defthm fn-asx-outcome-fields-agree
  (implies (equal (fn-asx-outcome a) (fn-asx-outcome b))
           (and (equal (fn-ast-at 1 a) (fn-ast-at 1 b))
                (equal (fn-ast-at 2 a) (fn-ast-at 2 b))
                (equal (fn-ast-at 3 a) (fn-ast-at 3 b))
                (equal (fn-ast-at 9 a) (fn-ast-at 9 b))
                (implies (eq (fn-ast-at 9 a) :selected)
                         (equal (fn-ast-at 5 a) (fn-ast-at 5 b)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-asx-outcome))))

(defthm fn-asto-selection-missing-of-mode-phase
  (implies (and (equal (fn-ast-at 1 a) (fn-ast-at 1 b))
                (equal (fn-ast-at 9 a) (fn-ast-at 9 b)))
           (equal (mv-list 3 (fn-asto-selection-missing
                              oc (fn-asto-capture-with-selection cap a sc)))
                  (mv-list 3 (fn-asto-selection-missing
                              oc (fn-asto-capture-with-selection cap b sc)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-asto-selection-missing fn-asto-capture-with-selection) ()))))

(defthm fn-asto-selection-ready-on-of-outcome
  (implies (and (equal (fn-asx-outcome n1) (fn-asx-outcome n2))
                (or (fn-ast-select-donep n1) (equal n1 n2)))
           (equal (mv-list 3 (fn-asto-selection-ready-on oc cap n1 fn-arena))
                  (mv-list 3 (fn-asto-selection-ready-on
                              oc (fn-asto-capture-with-selection cap s sc) n2 fn-arena))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-asto-selection-ready-on fn-ast-select-donep)
                           (fn-asx-outcome fn-asto-selection-missing
                            fn-asto-payload-preflight fn-ast-select-state))
           :use ((:instance fn-asx-outcome-fields-agree (a n1) (b n2))
                 (:instance fn-asto-selection-missing-of-mode-phase (a n1) (b n2) (sc nil))))))

(defthm fn-asto-ready-rest-of-selection-preflight
  (implies (equal (fn-ast-at 0 (fn-ast-at 2 cap)) :article-select)
           (equal (mv-list 4 (fn-asto-ready-rest oc id (cons (list :article-preflight cap) rest0)
                                                 f fn-arena fn-ast-ws))
                  (if (equal id (fn-own-conn-id (fn-ast-at 0 cap)))
                      (list (mv-nth 0 (fn-asto-selection-ready oc cap f fn-arena))
                            (mv-nth 1 (fn-asto-selection-ready oc cap f fn-arena))
                            (append (mv-nth 2 (fn-asto-selection-ready oc cap f fn-arena))
                                    rest0)
                            fn-ast-ws)
                    (list :stale oc (cons (list :article-preflight cap) rest0) fn-ast-ws))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-asto-selection-ready fn-asto-capture-with-selection)
           :expand ((fn-asto-ready-rest oc id (cons (list :article-preflight cap) rest0) f fn-arena fn-ast-ws)))))

(defthm fn-asto-capture-with-selection-fields
  (and (equal (fn-ast-at 0 (fn-asto-capture-with-selection cap s sc)) (fn-ast-at 0 cap))
       (equal (fn-ast-at 2 (fn-asto-capture-with-selection cap s sc)) s))
  :hints (("Goal" :in-theory (enable fn-asto-capture-with-selection))))


(defthm fn-asto-ready-plan-step-of-selection-outcome
  (implies (and (equal (fn-splan-cur plan1) (fn-splan-cur plan2))
                (equal (fn-splan-rest plan1) (cons (list :article-preflight cap1) rest0))
                (equal (fn-splan-rest plan2) (cons (list :article-preflight cap2) rest0))
                (equal cap2 (fn-asto-capture-with-selection cap1 s2 (fn-ast-at 5 cap1)))
                (equal (fn-ast-at 0 (fn-ast-at 2 cap1)) :article-select)
                (equal (fn-ast-at 0 s2) :article-select)
                (equal id (fn-own-conn-id (fn-ast-at 0 cap1)))
                (equal n1 (fn-ast-select-step (fn-ast-at 2 cap1) (nfix f1)))
                (equal n2 (fn-ast-select-step s2 (nfix f2)))
                (equal (fn-asx-outcome n1) (fn-asx-outcome n2))
                (or (fn-ast-select-donep n1) (equal n1 n2)))
           (equal (mv-list 4 (fn-asto-ready-plan-step oc id plan1 f1 fn-arena fn-ast-ws))
                  (mv-list 4 (fn-asto-ready-plan-step oc id plan2 f2 fn-arena fn-ast-ws))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-asto-ready-plan-step fn-asto-selection-ready)
                           (fn-asx-outcome fn-ast-select-step fn-ast-select-donep
                            fn-asto-selection-ready-on fn-asto-capture-with-selection
                            fn-asto-ready-rest))
           :use ((:instance fn-asto-ready-rest-of-selection-preflight
                            (cap cap1) (id id) (f f1) (rest0 rest0))
                 (:instance fn-asto-ready-rest-of-selection-preflight
                            (cap cap2) (id id) (f f2) (rest0 rest0))
                 (:instance fn-asto-selection-ready-on-of-outcome
                            (cap cap1) (s s2) (sc (fn-ast-at 5 cap1)) (oc oc))))))

(defthm fn-asto-select-step-of-done
  (implies (fn-ast-select-donep it) (equal (fn-ast-select-step it fuel) it))
  :hints (("Goal" :in-theory (enable fn-ast-select-step))))

(defthm fn-asto-start-cat-number-done
  (implies (and (fn-nntp-session-group session)
                (consp args) (null (cdr args)) (fn-nntp-number-tokenp (car args)))
           (fn-ast-select-donep (fn-asto-selection-start-cat session v args fn-arena fn-cat)))
  :hints (("Goal" :in-theory (enable fn-asto-selection-start-cat fn-asx-done-state fn-ast-select-donep
                                     fn-ast-select-state fn-ast-at))))

(defthm fn-asto-start-cat-current-done
  (implies (and (fn-nntp-session-group session) (null args)
                (posp (fn-nntp-session-current session))
                (<= (fn-nntp-session-current session) *fn-nntp-max-article-number*))
           (fn-ast-select-donep (fn-asto-selection-start-cat session v args fn-arena fn-cat)))
  :hints (("Goal" :in-theory (enable fn-asto-selection-start-cat fn-asx-done-state fn-ast-select-donep
                                     fn-ast-select-state fn-ast-at))))

(defthm fn-asto-start-number-shape
  (implies (and (fn-nntp-session-group session)
                (consp args) (null (cdr args)) (fn-nntp-number-tokenp (car args)))
           (and (consp (fn-asto-selection-start session archive index args))
                (consp (fn-asto-selection-start-cat session v args fn-arena fn-cat))
                (equal (fn-ast-at 0 (fn-asto-selection-start session archive index args)) :article-select)
                (equal (fn-ast-at 0 (fn-asto-selection-start-cat session v args fn-arena fn-cat))
                       :article-select)))
  :hints (("Goal" :in-theory (enable fn-asto-selection-start fn-asto-selection-start-cat fn-asx-done-state
                                     fn-ast-select-state fn-ast-at))))

(defthm fn-asto-start-current-shape
  (implies (and (fn-nntp-session-group session) (null args)
                (posp (fn-nntp-session-current session))
                (<= (fn-nntp-session-current session) *fn-nntp-max-article-number*))
           (and (consp (fn-asto-selection-start session archive index args))
                (consp (fn-asto-selection-start-cat session v args fn-arena fn-cat))
                (equal (fn-ast-at 0 (fn-asto-selection-start session archive index args)) :article-select)
                (equal (fn-ast-at 0 (fn-asto-selection-start-cat session v args fn-arena fn-cat))
                       :article-select)))
  :hints (("Goal" :in-theory (enable fn-asto-selection-start fn-asto-selection-start-cat fn-asx-done-state
                                     fn-ast-select-state fn-ast-at))))

(defthm fn-asto-bridge-msgid-token-not-number-token
  (implies (fn-nntp-message-id-tokenp token) (not (fn-nntp-number-tokenp token)))
  :hints (("Goal" :in-theory (enable fn-nntp-message-id-tokenp fn-nntp-number-tokenp
                                     fn-nntp-decimal-tokenp))))

(defthm fn-asto-start-msgid-shape
  (implies (and (consp args) (null (cdr args))
                (fn-nntp-message-id-tokenp (car args)) (fn-octet-listp (car args)))
           (and (consp (fn-asto-selection-start session archive index args))
                (consp (fn-asto-selection-start-cat session v args fn-arena fn-cat))
                (equal (fn-ast-at 0 (fn-asto-selection-start session archive index args)) :article-select)
                (equal (fn-ast-at 0 (fn-asto-selection-start-cat session v args fn-arena fn-cat))
                       :article-select)))
  :hints (("Goal" :in-theory (e/d (fn-asto-selection-start fn-asto-selection-start-cat
                                   fn-ast-select-state fn-ast-at fn-ast-msgid-local-start)
                                  (fn-scat-msgid-article fn-midx-lookup fn-gidx-pinp))
           :use ((:instance fn-asto-bridge-msgid-token-not-number-token (token (car args)))))))

(defthm fn-asto-ready-plan-step-of-capture-selection
  (implies (and (not (fn-auth-access-read as config))
                (equal (fn-splan-cur plan1) (fn-splan-cur plan2))
                (equal (fn-splan-rest plan1) (cons (list :article-preflight cap1) rest0))
                (equal (fn-splan-rest plan2) (cons (list :article-preflight cap2) rest0))
                (equal (fn-ast-at 2 cap1)
                       (fn-asto-capture-selection as config session va vi args v fn-arena fn-cat))
                (equal cap2 (fn-asto-capture-with-selection
                             cap1 (fn-asto-selection-start session archive index args)
                             (fn-ast-at 5 cap1)))
                (equal id (fn-own-conn-id (fn-ast-at 0 cap1)))
                (equal (fn-ast-at 0 (fn-asto-selection-start session archive index args))
                       :article-select)
                (equal (fn-ast-at 0 (fn-asto-selection-start-cat session v args fn-arena fn-cat))
                       :article-select)
                (equal (fn-asx-outcome (fn-ast-select-step
                                        (fn-asto-selection-start-cat session v args fn-arena fn-cat)
                                        (nfix f1)))
                       (fn-asx-outcome (fn-ast-select-step
                                        (fn-asto-selection-start session archive index args)
                                        (nfix f2))))
                (or (fn-ast-select-donep
                     (fn-ast-select-step (fn-asto-selection-start-cat session v args fn-arena fn-cat)
                                         (nfix f1)))
                    (equal (fn-ast-select-step
                            (fn-asto-selection-start-cat session v args fn-arena fn-cat) (nfix f1))
                           (fn-ast-select-step
                            (fn-asto-selection-start session archive index args) (nfix f2)))))
           (equal (mv-list 4 (fn-asto-ready-plan-step oc id plan1 f1 fn-arena fn-ast-ws))
                  (mv-list 4 (fn-asto-ready-plan-step oc id plan2 f2 fn-arena fn-ast-ws))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-asto-selection-start fn-asto-selection-start-cat fn-asto-capture-selection
                               fn-asx-outcome fn-ast-select-step fn-ast-select-donep
                               fn-asto-capture-with-selection fn-asto-ready-plan-step)
           :use ((:instance fn-asto-ready-plan-step-of-selection-outcome
                            (s2 (fn-asto-selection-start session archive index args))
                            (n1 (fn-ast-select-step (fn-ast-at 2 cap1) (nfix f1)))
                            (n2 (fn-ast-select-step (fn-asto-selection-start session archive index args)
                                                    (nfix f2))))
                 fn-asto-capture-selection-unrestricted))))

(defthm fn-asto-ready-plan-step-capture-number
  (implies (and (not (fn-auth-access-read as config))
                (equal (fn-splan-cur plan1) (fn-splan-cur plan2))
                (equal (fn-splan-rest plan1) (cons (list :article-preflight cap1) rest0))
                (equal (fn-splan-rest plan2) (cons (list :article-preflight cap2) rest0))
                (equal (fn-ast-at 2 cap1)
                       (fn-asto-capture-selection as config session va vi args v fn-arena fn-cat))
                (equal cap2 (fn-asto-capture-with-selection
                             cap1 (fn-asto-selection-start session archive index args)
                             (fn-ast-at 5 cap1)))
                (equal id (fn-own-conn-id (fn-ast-at 0 cap1)))
                (fn-scr-catalogp archive index v fn-arena fn-cat)
                (fn-nntp-session-group session)
                (consp args) (null (cdr args)) (fn-nntp-number-tokenp (car args))
                (posp fuel)
                (<= (fn-asx-need (fn-asto-selection-start session archive index args)) fuel))
           (equal (mv-list 4 (fn-asto-ready-plan-step oc id plan1 fuel fn-arena fn-ast-ws))
                  (mv-list 4 (fn-asto-ready-plan-step oc id plan2 fuel fn-arena fn-ast-ws))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-asto-selection-start fn-asto-selection-start-cat fn-asto-capture-selection
                               fn-asx-outcome fn-ast-select-step fn-ast-select-donep fn-asx-need
                               fn-asto-capture-with-selection fn-asto-ready-plan-step
                               fn-scr-catalogp fn-asto-selection-start-cat-number fn-asto-start-number-shape fn-ast-at)
           :use ((:instance fn-asto-ready-plan-step-of-capture-selection (f1 fuel) (f2 fuel))
                 fn-asto-selection-start-cat-number
                 fn-asto-start-cat-number-done
                 (:instance fn-asto-select-step-of-done
                            (it (fn-asto-selection-start-cat session v args fn-arena fn-cat)) (fuel fuel))
                 (:instance fn-asto-start-number-shape)
                 fn-asto-capture-selection-unrestricted))))

(defthm fn-asto-ready-plan-step-capture-current
  (implies (and (not (fn-auth-access-read as config))
                (equal (fn-splan-cur plan1) (fn-splan-cur plan2))
                (equal (fn-splan-rest plan1) (cons (list :article-preflight cap1) rest0))
                (equal (fn-splan-rest plan2) (cons (list :article-preflight cap2) rest0))
                (equal (fn-ast-at 2 cap1)
                       (fn-asto-capture-selection as config session va vi args v fn-arena fn-cat))
                (equal cap2 (fn-asto-capture-with-selection
                             cap1 (fn-asto-selection-start session archive index args)
                             (fn-ast-at 5 cap1)))
                (equal id (fn-own-conn-id (fn-ast-at 0 cap1)))
                (fn-scr-catalogp archive index v fn-arena fn-cat)
                (fn-nntp-session-group session)
                (null args)
                (posp (fn-nntp-session-current session))
                (<= (fn-nntp-session-current session) *fn-nntp-max-article-number*)
                (posp fuel)
                (<= (fn-asx-need (fn-asto-selection-start session archive index args)) fuel))
           (equal (mv-list 4 (fn-asto-ready-plan-step oc id plan1 fuel fn-arena fn-ast-ws))
                  (mv-list 4 (fn-asto-ready-plan-step oc id plan2 fuel fn-arena fn-ast-ws))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-asto-selection-start fn-asto-selection-start-cat fn-asto-capture-selection
                               fn-asx-outcome fn-ast-select-step fn-ast-select-donep fn-asx-need
                               fn-asto-capture-with-selection fn-asto-ready-plan-step
                               fn-scr-catalogp fn-asto-selection-start-cat-current fn-asto-start-current-shape fn-ast-at)
           :use ((:instance fn-asto-ready-plan-step-of-capture-selection (f1 fuel) (f2 fuel))
                 fn-asto-selection-start-cat-current
                 fn-asto-start-cat-current-done
                 (:instance fn-asto-select-step-of-done
                            (it (fn-asto-selection-start-cat session v args fn-arena fn-cat)) (fuel fuel))
                 (:instance fn-asto-start-current-shape)
                 fn-asto-capture-selection-unrestricted))))

(defthm fn-asto-ready-plan-step-capture-msgid
  (implies (and (not (fn-auth-access-read as config))
                (equal (fn-splan-cur plan1) (fn-splan-cur plan2))
                (equal (fn-splan-rest plan1) (cons (list :article-preflight cap1) rest0))
                (equal (fn-splan-rest plan2) (cons (list :article-preflight cap2) rest0))
                (equal (fn-ast-at 2 cap1)
                       (fn-asto-capture-selection as config session va vi args v fn-arena fn-cat))
                (equal cap2 (fn-asto-capture-with-selection
                             cap1 (fn-asto-selection-start session archive index args)
                             (fn-ast-at 5 cap1)))
                (equal id (fn-own-conn-id (fn-ast-at 0 cap1)))
                (fn-scr-catalogp archive index v fn-arena fn-cat)
                (fn-gidx-pinp index)
                (consp args) (null (cdr args))
                (fn-nntp-message-id-tokenp (car args)) (fn-octet-listp (car args)))
           (equal (mv-list 4 (fn-asto-ready-plan-step oc id plan1 fuel fn-arena fn-ast-ws))
                  (mv-list 4 (fn-asto-ready-plan-step oc id plan2 fuel fn-arena fn-ast-ws))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-asto-selection-start fn-asto-selection-start-cat fn-asto-capture-selection
                               fn-asx-outcome fn-ast-select-step fn-ast-select-donep
                               fn-asto-capture-with-selection fn-asto-ready-plan-step
                               fn-scr-catalogp fn-asto-selection-start-cat-msgid
                               fn-asto-start-msgid-shape fn-ast-at)
           :use ((:instance fn-asto-ready-plan-step-of-capture-selection (f1 fuel) (f2 fuel))
                 fn-asto-selection-start-cat-msgid
                 fn-asto-start-msgid-shape
                 fn-asto-capture-selection-unrestricted))))

(defthm fn-asto-ready-plan-step-capture-msgid-unpinned
  (implies (and (not (fn-auth-access-read as config))
                (equal (fn-splan-cur plan1) (fn-splan-cur plan2))
                (equal (fn-splan-rest plan1) (cons (list :article-preflight cap1) rest0))
                (equal (fn-splan-rest plan2) (cons (list :article-preflight cap2) rest0))
                (equal (fn-ast-at 2 cap1)
                       (fn-asto-capture-selection as config session va vi args v fn-arena fn-cat))
                (equal cap2 (fn-asto-capture-with-selection
                             cap1 (fn-asto-selection-start session archive index args)
                             (fn-ast-at 5 cap1)))
                (equal id (fn-own-conn-id (fn-ast-at 0 cap1)))
                (fn-scr-catalogp archive index v fn-arena fn-cat)
                (not (fn-gidx-pinp index))
                (consp args) (null (cdr args))
                (fn-nntp-message-id-tokenp (car args)) (fn-octet-listp (car args))
                (natp e))
           (equal (mv-list 4 (fn-asto-ready-plan-step oc id plan1 e fn-arena fn-ast-ws))
                  (mv-list 4 (fn-asto-ready-plan-step
                              oc id plan2
                              (+ (fn-asx-nc (fn-nntp-token-string (car args)) (fn-state-articles archive)) e)
                              fn-arena))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-asto-selection-start fn-asto-selection-start-cat fn-asto-capture-selection
                               fn-asx-outcome fn-ast-select-step fn-ast-select-donep
                               fn-asto-capture-with-selection fn-asto-ready-plan-step
                               fn-scr-catalogp fn-asto-selection-start-cat-msgid-unpinned
                               fn-asto-start-msgid-shape fn-ast-at fn-asx-nc fn-nntp-token-string)
           :use ((:instance fn-asto-ready-plan-step-of-capture-selection
                            (f1 e) (f2 (+ (fn-asx-nc (fn-nntp-token-string (car args))
                                                     (fn-state-articles archive)) e)))
                 fn-asto-selection-start-cat-msgid-unpinned
                 fn-asto-start-msgid-shape
                 fn-asto-capture-selection-unrestricted))))

(defthm fn-asto-find-conn-id
  (implies (fn-own-find-conn id conns)
           (equal (fn-own-conn-id (fn-own-find-conn id conns)) id))
  :hints (("Goal" :induct (fn-own-find-conn id conns))))

(defthm fn-asto-with-wire-session-id
  (equal (fn-own-conn-id (fn-asto-with-wire-session conn wire session)) (fn-own-conn-id conn))
  :hints (("Goal" :in-theory (enable fn-asto-with-wire-session))))

(defthm fn-asto-capture-catalogp-of-conn-pinp
  (implies (fn-scj-conn-pinp conn fn-arena fn-cat)
           (fn-scr-catalogp (fn-served-conn-archive (fn-own-tls-served-conn o conn))
                            (fn-served-conn-pinned-index (fn-own-tls-served-conn o conn))
                            (fn-scr-view-of (fn-own-conn-version conn) fn-cat)
                            fn-arena fn-cat))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-scj-conn-pinp fn-scj-conn-pinned-index fn-own-tls-served-conn
                            fn-own-served-conn fn-served-conn-pinned-index)
                           (fn-scr-catalogp fn-scr-view-of fn-served-pinned-index)))))

(defthm fn-asto-capture-catalogp-of-conns-pinp
  (implies (and (fn-scj-conns-pinp (fn-own-conns o) fn-arena fn-cat)
                (fn-own-find-conn id (fn-own-conns o)))
           (fn-scr-catalogp
            (fn-served-conn-archive (fn-own-tls-served-conn o (fn-own-find-conn id (fn-own-conns o))))
            (fn-served-conn-pinned-index
             (fn-own-tls-served-conn o (fn-own-find-conn id (fn-own-conns o))))
            (fn-scr-view-of (fn-own-conn-version (fn-own-find-conn id (fn-own-conns o))) fn-cat)
            fn-arena fn-cat))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-scj-conn-pinp fn-scj-conns-pinp-find fn-scr-catalogp fn-scr-view-of
                               fn-own-tls-served-conn fn-served-conn-archive fn-served-conn-pinned-index)
           :use ((:instance fn-scj-conns-pinp-find (conns (fn-own-conns o)))
                 (:instance fn-asto-capture-catalogp-of-conn-pinp
                            (conn (fn-own-find-conn id (fn-own-conns o))))))))

(defthm fn-asto-ready-plan-step-capture-number-owner
  (implies (and (not (fn-auth-access-read as config))
                (equal (fn-splan-cur plan1) (fn-splan-cur plan2))
                (equal (fn-splan-rest plan1) (cons (list :article-preflight cap1) rest0))
                (equal (fn-splan-rest plan2) (cons (list :article-preflight cap2) rest0))
                (equal (fn-ast-at 2 cap1)
                       (fn-asto-capture-selection as config session va vi args v fn-arena fn-cat))
                (equal cap2 (fn-asto-capture-with-selection
                             cap1 (fn-asto-selection-start session archive index args)
                             (fn-ast-at 5 cap1)))
                (equal (fn-ast-at 0 cap1) (fn-asto-with-wire-session conn wire sess))
                (equal conn (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))
                conn
                (fn-scj-conns-pinp (fn-own-conns (fn-ocfg-owner oc)) fn-arena fn-cat)
                (equal archive (fn-served-conn-archive
                                (fn-own-tls-served-conn (fn-ocfg-owner oc) conn)))
                (equal index (fn-served-conn-pinned-index
                              (fn-own-tls-served-conn (fn-ocfg-owner oc) conn)))
                (equal v (fn-scr-view-of (fn-own-conn-version conn) fn-cat))
                (fn-nntp-session-group session)
                (consp args) (null (cdr args)) (fn-nntp-number-tokenp (car args))
                (posp fuel)
                (<= (fn-asx-need (fn-asto-selection-start session archive index args)) fuel))
           (equal (mv-list 4 (fn-asto-ready-plan-step oc id plan1 fuel fn-arena fn-ast-ws))
                  (mv-list 4 (fn-asto-ready-plan-step oc id plan2 fuel fn-arena fn-ast-ws))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'minimal-theory)
           :use ((:instance fn-asto-ready-plan-step-capture-number (id id))
                 (:instance fn-asto-capture-catalogp-of-conns-pinp (o (fn-ocfg-owner oc)))
                 (:instance fn-asto-find-conn-id (conns (fn-own-conns (fn-ocfg-owner oc))))
                 (:instance fn-asto-with-wire-session-id (session sess))))))


(defthm fn-asto-ready-plan-step-capture-current-owner
  (implies (and (not (fn-auth-access-read as config))
                (equal (fn-splan-cur plan1) (fn-splan-cur plan2))
                (equal (fn-splan-rest plan1) (cons (list :article-preflight cap1) rest0))
                (equal (fn-splan-rest plan2) (cons (list :article-preflight cap2) rest0))
                (equal (fn-ast-at 2 cap1)
                       (fn-asto-capture-selection as config session va vi args v fn-arena fn-cat))
                (equal cap2 (fn-asto-capture-with-selection
                             cap1 (fn-asto-selection-start session archive index args)
                             (fn-ast-at 5 cap1)))
                (equal (fn-ast-at 0 cap1) (fn-asto-with-wire-session conn wire sess))
                (equal conn (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))
                conn
                (fn-scj-conns-pinp (fn-own-conns (fn-ocfg-owner oc)) fn-arena fn-cat)
                (equal archive (fn-served-conn-archive
                                (fn-own-tls-served-conn (fn-ocfg-owner oc) conn)))
                (equal index (fn-served-conn-pinned-index
                              (fn-own-tls-served-conn (fn-ocfg-owner oc) conn)))
                (equal v (fn-scr-view-of (fn-own-conn-version conn) fn-cat))
                (fn-nntp-session-group session)
                (null args)
                (posp (fn-nntp-session-current session))
                (<= (fn-nntp-session-current session) *fn-nntp-max-article-number*)
                (posp fuel)
                (<= (fn-asx-need (fn-asto-selection-start session archive index args)) fuel))
           (equal (mv-list 4 (fn-asto-ready-plan-step oc id plan1 fuel fn-arena fn-ast-ws))
                  (mv-list 4 (fn-asto-ready-plan-step oc id plan2 fuel fn-arena fn-ast-ws))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'minimal-theory)
           :use ((:instance fn-asto-ready-plan-step-capture-current (id id))
                 (:instance fn-asto-capture-catalogp-of-conns-pinp (o (fn-ocfg-owner oc)))
                 (:instance fn-asto-find-conn-id (conns (fn-own-conns (fn-ocfg-owner oc))))
                 (:instance fn-asto-with-wire-session-id (session sess))))))


(defthm fn-asto-ready-plan-step-capture-msgid-owner
  (implies (and (not (fn-auth-access-read as config))
                (equal (fn-splan-cur plan1) (fn-splan-cur plan2))
                (equal (fn-splan-rest plan1) (cons (list :article-preflight cap1) rest0))
                (equal (fn-splan-rest plan2) (cons (list :article-preflight cap2) rest0))
                (equal (fn-ast-at 2 cap1)
                       (fn-asto-capture-selection as config session va vi args v fn-arena fn-cat))
                (equal cap2 (fn-asto-capture-with-selection
                             cap1 (fn-asto-selection-start session archive index args)
                             (fn-ast-at 5 cap1)))
                (equal (fn-ast-at 0 cap1) (fn-asto-with-wire-session conn wire sess))
                (equal conn (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))
                conn
                (fn-scj-conns-pinp (fn-own-conns (fn-ocfg-owner oc)) fn-arena fn-cat)
                (equal archive (fn-served-conn-archive
                                (fn-own-tls-served-conn (fn-ocfg-owner oc) conn)))
                (equal index (fn-served-conn-pinned-index
                              (fn-own-tls-served-conn (fn-ocfg-owner oc) conn)))
                (equal v (fn-scr-view-of (fn-own-conn-version conn) fn-cat))
                (fn-gidx-pinp index)
                (consp args) (null (cdr args))
                (fn-nntp-message-id-tokenp (car args)) (fn-octet-listp (car args)))
           (equal (mv-list 4 (fn-asto-ready-plan-step oc id plan1 fuel fn-arena fn-ast-ws))
                  (mv-list 4 (fn-asto-ready-plan-step oc id plan2 fuel fn-arena fn-ast-ws))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'minimal-theory)
           :use ((:instance fn-asto-ready-plan-step-capture-msgid (id id))
                 (:instance fn-asto-capture-catalogp-of-conns-pinp (o (fn-ocfg-owner oc)))
                 (:instance fn-asto-find-conn-id (conns (fn-own-conns (fn-ocfg-owner oc))))
                 (:instance fn-asto-with-wire-session-id (session sess))))))


(defthm fn-asto-ready-plan-step-capture-msgid-unpinned-owner
  (implies (and (not (fn-auth-access-read as config))
                (equal (fn-splan-cur plan1) (fn-splan-cur plan2))
                (equal (fn-splan-rest plan1) (cons (list :article-preflight cap1) rest0))
                (equal (fn-splan-rest plan2) (cons (list :article-preflight cap2) rest0))
                (equal (fn-ast-at 2 cap1)
                       (fn-asto-capture-selection as config session va vi args v fn-arena fn-cat))
                (equal cap2 (fn-asto-capture-with-selection
                             cap1 (fn-asto-selection-start session archive index args)
                             (fn-ast-at 5 cap1)))
                (equal (fn-ast-at 0 cap1) (fn-asto-with-wire-session conn wire sess))
                (equal conn (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))
                conn
                (fn-scj-conns-pinp (fn-own-conns (fn-ocfg-owner oc)) fn-arena fn-cat)
                (equal archive (fn-served-conn-archive
                                (fn-own-tls-served-conn (fn-ocfg-owner oc) conn)))
                (equal index (fn-served-conn-pinned-index
                              (fn-own-tls-served-conn (fn-ocfg-owner oc) conn)))
                (equal v (fn-scr-view-of (fn-own-conn-version conn) fn-cat))
                (not (fn-gidx-pinp index))
                (consp args) (null (cdr args))
                (fn-nntp-message-id-tokenp (car args)) (fn-octet-listp (car args))
                (natp e))
           (equal (mv-list 4 (fn-asto-ready-plan-step oc id plan1 e fn-arena fn-ast-ws))
                  (mv-list 4 (fn-asto-ready-plan-step
                              oc id plan2
                              (+ (fn-asx-nc (fn-nntp-token-string (car args)) (fn-state-articles archive)) e)
                              fn-arena))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'minimal-theory)
           :use ((:instance fn-asto-ready-plan-step-capture-msgid-unpinned (id id))
                 (:instance fn-asto-capture-catalogp-of-conns-pinp (o (fn-ocfg-owner oc)))
                 (:instance fn-asto-find-conn-id (conns (fn-own-conns (fn-ocfg-owner oc))))
                 (:instance fn-asto-with-wire-session-id (session sess))))))

