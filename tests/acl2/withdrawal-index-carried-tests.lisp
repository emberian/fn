; Teeth for books/withdrawal-index-carried.lisp (lane served-incremental-4;
; declared through def-carried-view by lane generators-2): the carried
; withdrawal index a POST's duplicate test and a completion's targets read.
; The withdrawal records are the plan's own shape (fn-ctl-withdrawal-make,
; what fn-ctl-withdrawal-plan makes), and every carry is the host writer's:
; fn-wix-refresh of nil or of a carry it made.  The carry is (WS TSET CSET).
(in-package "ACL2")
(include-book "../../books/withdrawal-index-carried")
(include-book "../../books/defkeystone")
(include-book "must-fail-checked")

(defconst *wit-ws0*
  (list (fn-ctl-withdrawal-make "<t1@x>" "<c1@x>" "p" :all 0)
        (fn-ctl-withdrawal-make "<t2@x>" "<c1@x>" "p" :all 0)
        (fn-ctl-withdrawal-make "<t3@x>" "<c2@x>" "p" :all 0)))
(defconst *wit-new* (fn-ctl-withdrawal-make "<t4@x>" "<c3@x>" "p" :all 0))
(defconst *wit-ws1* (cons *wit-new* *wit-ws0*))
(defconst *wit-c0* (fn-wix-refresh nil *wit-ws0*))
(defconst *wit-c1* (fn-wix-refresh *wit-c0* *wit-ws1*))

; -----------------------------------------------------------------------------
; fn-wix-carryp-of-refresh.  Positive: the antecedent holds (nil, then the
; carry it made), and the conclusion; the second refresh took the delta walk
; (the carried list was found as a tail), the third rebuilt.
(assert-event (fn-wix-carryp nil))
(assert-event (fn-wix-carryp *wit-c0*))
(assert-event (equal (fn-wix-ws *wit-c0*) *wit-ws0*))
(assert-event (nth 0 (mv-list 2 (fn-cv-walk *wit-ws1* *wit-ws0* nil))))
(assert-event (equal (fn-cv-walk-steps *wit-ws1* *wit-ws0*) 1))
(assert-event (fn-wix-carryp *wit-c1*))
(assert-event (equal (fn-wix-ws *wit-c1*) *wit-ws1*))
(defconst *wit-ws2* (list (fn-ctl-withdrawal-make "<t9@x>" "<c9@x>" "p" :all 0)))
(assert-event (not (nth 0 (mv-list 2 (fn-cv-walk *wit-ws2* *wit-ws1* nil)))))
(assert-event (fn-wix-carryp (fn-wix-refresh *wit-c1* *wit-ws2*)))
; Hypothesis removal (the only hypothesis): from a carry that is not
; complete, the refresh that finds its list as a tail keeps the gap.
(defconst *wit-bad0* (cons *wit-ws0* (cons nil nil)))
(assert-event (not (fn-wix-carryp *wit-bad0*)))
(assert-event (not (fn-wix-carryp (fn-wix-refresh *wit-bad0* *wit-ws1*))))

; -----------------------------------------------------------------------------
; fn-wix-targetedp-is-pidx-targetedp.  Positive: the antecedent holds and
; both answers agree, on the fast path (an untargeted Message-ID absent from
; the trie) and on the walk (a targeted one); and after the delta refresh,
; for the new record's target.
(assert-event (and (fn-wix-carryp *wit-c0*)
                   (not (fn-rit-hasp "<n@x>" 0 (fn-wix-tset *wit-c0*)))
                   (equal (fn-wix-targetedp "<n@x>" *wit-ws0* *wit-c0*)
                          (fn-pidx-targetedp "<n@x>" *wit-ws0*))
                   (equal (fn-wix-targetedp "<n@x>" *wit-ws0* *wit-c0*) nil)))
(assert-event (and (fn-wix-carryp *wit-c0*)
                   (equal (fn-wix-targetedp "<t2@x>" *wit-ws0* *wit-c0*)
                          (fn-pidx-targetedp "<t2@x>" *wit-ws0*))
                   (fn-wix-targetedp "<t2@x>" *wit-ws0* *wit-c0*)))
(assert-event (and (fn-wix-carryp *wit-c1*)
                   (equal (fn-wix-targetedp "<t4@x>" *wit-ws1* *wit-c1*)
                          (fn-pidx-targetedp "<t4@x>" *wit-ws1*))
                   (fn-wix-targetedp "<t4@x>" *wit-ws1* *wit-c1*)))
; Hypothesis removal: the incomplete carry fails the antecedent and the
; conclusion (it calls a targeted Message-ID untargeted).
(assert-event (and (not (fn-wix-carryp *wit-bad0*))
                   (not (equal (fn-wix-targetedp "<t1@x>" *wit-ws0* *wit-bad0*)
                               (fn-pidx-targetedp "<t1@x>" *wit-ws0*)))))

; -----------------------------------------------------------------------------
; fn-wix-targets-of-is-sca-targets-of.  Positive: a cause with two records
; (the walk), an ordinary article's Message-ID (the fast path, nil).
(assert-event (and (fn-wix-carryp *wit-c1*)
                   (equal (fn-wix-targets-of "<c1@x>" *wit-ws1* *wit-c1*)
                          (fn-sca-targets-of "<c1@x>" *wit-ws1*))
                   (equal (fn-wix-targets-of "<c1@x>" *wit-ws1* *wit-c1*)
                          '("<t1@x>" "<t2@x>"))))
(assert-event (and (fn-wix-carryp *wit-c1*)
                   (not (fn-rit-hasp "<n@x>" 0 (fn-wix-cset *wit-c1*)))
                   (equal (fn-wix-targets-of "<n@x>" *wit-ws1* *wit-c1*)
                          (fn-sca-targets-of "<n@x>" *wit-ws1*))))
(assert-event (and (not (fn-wix-carryp *wit-bad0*))
                   (not (equal (fn-wix-targets-of "<c2@x>" *wit-ws0* *wit-bad0*)
                               (fn-sca-targets-of "<c2@x>" *wit-ws0*)))))

; MUTATION witness (labelled): a refresh that installs the new list but
; keeps the old tries (drops the delta walk) is not complete, and calls the
; new record's target untargeted and its cause target-free.
(defconst *wit-mut* (cons *wit-ws1* (cdr *wit-c0*)))
(assert-event (and (not (fn-wix-carryp *wit-mut*))
                   (not (equal (fn-wix-targetedp "<t4@x>" *wit-ws1* *wit-mut*)
                               (fn-pidx-targetedp "<t4@x>" *wit-ws1*)))
                   (not (equal (fn-wix-targets-of "<c3@x>" *wit-ws1* *wit-mut*)
                               (fn-sca-targets-of "<c3@x>" *wit-ws1*)))))

; -----------------------------------------------------------------------------
; fn-wix-find-article-cat-is-pidx-find-article-cat (and through it
; fn-wix-existing-action-cat-is-pidx-existing-action-cat, whose body differs
; only by this call).  A view whose raw list holds a cancelled article
; "<t1@x>" and whose withdrawal list targets it; the catalog is the empty
; live one.
(defconst *wit-art* (fn-make-article "<t1@x>" nil nil nil t 0))
(defconst *wit-view*
  (fn-own-view-make-visible 0 nil nil nil nil nil *wit-ws0* (list *wit-art*) nil nil))
(defconst *wit-cv* (fn-wix-refresh nil (fn-own-view-withdrawals *wit-view*)))
; Positive: the antecedent and the conclusion, targeted (the walk finds the
; raw article) and untargeted (the catalog answers).
(assert-event (fn-wix-carryp *wit-cv*))
(assert-event (equal (fn-wix-find-article-cat "<t1@x>" (list *wit-art*) *wit-view*
                                              *wit-cv* fn-arena fn-cat)
                     (fn-pidx-find-article-cat "<t1@x>" (list *wit-art*) *wit-view*
                                               fn-arena fn-cat)))
(assert-event (equal (fn-wix-find-article-cat "<t1@x>" (list *wit-art*) *wit-view*
                                              *wit-cv* fn-arena fn-cat)
                     *wit-art*))
(assert-event (equal (fn-wix-find-article-cat "<n@x>" (list *wit-art*) *wit-view*
                                              *wit-cv* fn-arena fn-cat)
                     (fn-pidx-find-article-cat "<n@x>" (list *wit-art*) *wit-view*
                                               fn-arena fn-cat)))
; Hypothesis removal: with the incomplete carry the cancelled article is
; looked up in the catalog (not found) instead of the raw list.
(defconst *wit-bad-v* (cons (fn-own-view-withdrawals *wit-view*) (cons nil nil)))
(assert-event (not (fn-wix-carryp *wit-bad-v*)))
(assert-event (not (equal (fn-wix-find-article-cat "<t1@x>" (list *wit-art*) *wit-view*
                                                   *wit-bad-v* fn-arena fn-cat)
                          (fn-pidx-find-article-cat "<t1@x>" (list *wit-art*) *wit-view*
                                                    fn-arena fn-cat))))
; fn-wix-existing-action-cat over the empty owner: equal to the reference.
(assert-event (equal (fn-wix-existing-action-cat "<n@x>" fn-octets nil nil *wit-cv*
                                                 fn-arena fn-cat)
                     (fn-pidx-existing-action-cat "<n@x>" fn-octets nil nil
                                                  fn-arena fn-cat)))

; -----------------------------------------------------------------------------
; The generated keystones' teeth (TEETH CONTRACT v1): what the declarations owe
; (table fn-teeth-owed), stated with the same claims, and checked.

(defteeth fn-wix-carryp-of-refresh
  :claim (((carried (fn-wix-carryp carry))) (fn-wix-carryp (fn-wix-refresh carry ws)))
  :subject fn-wix-refresh
  :witness ((carry *wit-c0*) (ws *wit-ws1*))
  :breaks ((carried ((carry *wit-bad0*))))
  :mutations ((old-tries (:conclusion (fn-wix-carryp (cons ws (cdr carry))))
                         ((carry *wit-c0*) (ws *wit-ws1*))
                         :fault "a refresh that installs the new list over the old tries")))

(defteeth fn-wix-targetedp-is-pidx-targetedp
  :claim (((carried (fn-wix-carryp carry)))
          (equal (fn-wix-targetedp msgid ws carry) (fn-pidx-targetedp msgid ws)))
  :subject fn-wix-targetedp
  :witness ((msgid "<n@x>") (ws *wit-ws0*) (carry *wit-c0*))
  :breaks ((carried ((msgid "<t1@x>") (carry *wit-bad0*))))
  :mutations ((positive-trusted (:conclusion (equal (fn-wix-targetedp msgid ws carry)
                                                    (fn-rit-hasp msgid 0 (fn-wix-tset carry))))
                                ((msgid "<n@x>") (ws *wit-ws0*)
                                 (carry (fn-wix-refresh nil (cons (fn-ctl-withdrawal-make "<n@x>" "<c9@x>" "p" :all 0)
                                                                  *wit-ws0*))))
                                :fault "a reader that trusts a positive probe")))

(defteeth fn-wix-targets-of-is-sca-targets-of
  :claim (((carried (fn-wix-carryp carry)))
          (equal (fn-wix-targets-of cause ws carry) (fn-sca-targets-of cause ws)))
  :subject fn-wix-targets-of
  :witness ((cause "<c1@x>") (ws *wit-ws1*) (carry *wit-c1*))
  :breaks ((carried ((cause "<c2@x>") (ws *wit-ws0*) (carry *wit-bad0*))))
  :mutations ((positive-trusted (:conclusion (equal (fn-wix-targets-of cause ws carry)
                                                    (if (fn-rit-hasp cause 0 (fn-wix-cset carry)) t nil)))
                                ((cause "<c1@x>") (ws *wit-ws1*) (carry *wit-c1*))
                                :fault "a reader that answers the probe's bit for the targets")))

(defteeth-check)
