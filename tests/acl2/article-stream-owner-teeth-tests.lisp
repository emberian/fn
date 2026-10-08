; article-stream-owner-teeth-tests.lisp -- teeth for the catalog-start keystones of
; books/article-stream-owner.lisp and books/article-select-index.lisp (repair item
; ARTICLE-INDEX-TEETH, lane article-index-2).
;
; The four fn-asto-selection-start-cat-* keystones take the arena and the catalog
; (stobjs, whose logical values the ground witnesses name), and defteeth refuses a
; claim over a stobj for its lemma-mode witnesses; their witnesses are ground
; theorems over the served-catalog fixture, hypothesis by hypothesis (fn-scr-catalogp
; is a defun-nx: its conjuncts, as served-catalog-chain-tests states them).
; Each ground theorem has its positive (the keystone's complete antecedent and
; conclusion) and its negatives: a mutated lookup the conclusion catches.
(in-package "ACL2")
(include-book "../../books/article-stream-owner")
(include-book "served-catalog-chain-tests")

; The fixture's view 3 articles, as the served-catalog tests build them.
(defconst *aot-articles*
  '(("<c@x>" 2 ("fn.test") (("fn.test" . 3)) t 5)
    ("<b@x>" 1 ("fn.test" "fn.other") (("fn.test" . 2) ("fn.other" . 1)) t 5)
    ("<a@x>" 0 ("fn.test") (("fn.test" . 1)) t 5)))

(defthm aot-articles-are-the-fixture-view
  (equal *aot-articles* (fn-cat-view-articles 3 *scct-a* *scct-c*))
  :rule-classes nil)


; ---- fn-asx-walk-is-lookup (books/article-select-index.lisp)
(defthm aot-walk-witness
  (implies (and (member-eq :number '(:number :current)) (stringp "fn.test") (posp 2) (natp 200)
                (<= (fn-asx-need (fn-ast-select-state :number "fn.test" 2 *aot-articles* nil nil nil 0 :next))
                    200))
           (equal (fn-asx-outcome
                   (fn-ast-select-step
                    (fn-ast-select-state :number "fn.test" 2 *aot-articles* nil nil nil 0 :next) 200))
                  (fn-asx-outcome
                   (fn-asx-done-state :number "fn.test" 2
                                      (fn-asx-first :number "fn.test" 2 *aot-articles*)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-asx-need fn-asx-goodp fn-ast-select-one fn-ast-select-donep
                                     fn-asx-prefix-equalp fn-asx-first fn-asx-hitp fn-asx-done-state
                                     fn-asx-outcome)
           :expand ((:free (it) (fn-asx-need it))
                    (:free (a b c) (fn-asx-prefix-equalp a b c))))))
(defthm aot-walk-wrong-number
  (and (implies (and (member-eq :number '(:number :current)) (stringp "fn.test") (posp 2) (natp 200)
                (<= (fn-asx-need (fn-ast-select-state :number "fn.test" 2 *aot-articles* nil nil nil 0 :next))
                    200))
           (equal (fn-asx-outcome
                   (fn-ast-select-step
                    (fn-ast-select-state :number "fn.test" 2 *aot-articles* nil nil nil 0 :next) 200))
                  (fn-asx-outcome (fn-asx-done-state :number "fn.test" 2 (fn-asx-first :number "fn.test" 2 *aot-articles*)))))
       (not (implies (and (member-eq :number '(:number :current)) (stringp "fn.test") (posp 2) (natp 200)
                (<= (fn-asx-need (fn-ast-select-state :number "fn.test" 2 *aot-articles* nil nil nil 0 :next))
                    200))
           (equal (fn-asx-outcome
                   (fn-ast-select-step
                    (fn-ast-select-state :number "fn.test" 2 *aot-articles* nil nil nil 0 :next) 200))
                  (fn-asx-outcome (fn-asx-done-state :number "fn.test" (+ 1 2) (fn-asx-first :number "fn.test" 2 *aot-articles*)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-asx-need fn-asx-goodp fn-ast-select-one fn-ast-select-donep
                                     fn-asx-prefix-equalp fn-asx-first fn-asx-hitp fn-asx-done-state
                                     fn-asx-outcome)
           :expand ((:free (it) (fn-asx-need it))
                    (:free (a b c) (fn-asx-prefix-equalp a b c))))))

(defthm aot-walk-withdrawn-row
  (and (implies (and (member-eq :number '(:number :current)) (stringp "fn.test") (posp 2) (natp 200)
                (<= (fn-asx-need (fn-ast-select-state :number "fn.test" 2 *aot-articles* nil nil nil 0 :next))
                    200))
           (equal (fn-asx-outcome
                   (fn-ast-select-step
                    (fn-ast-select-state :number "fn.test" 2 *aot-articles* nil nil nil 0 :next) 200))
                  (fn-asx-outcome (fn-asx-done-state :number "fn.test" 2 (fn-asx-first :number "fn.test" 2 *aot-articles*)))))
       (not (implies (and (member-eq :number '(:number :current)) (stringp "fn.test") (posp 2) (natp 200)
                (<= (fn-asx-need (fn-ast-select-state :number "fn.test" 2 *aot-articles* nil nil nil 0 :next))
                    200))
           (equal (fn-asx-outcome
                   (fn-ast-select-step
                    (fn-ast-select-state :number "fn.test" 2 *aot-articles* nil nil nil 0 :next) 200))
                  (fn-asx-outcome (fn-asx-done-state :number "fn.test" 2 nil))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-asx-need fn-asx-goodp fn-ast-select-one fn-ast-select-donep
                                     fn-asx-prefix-equalp fn-asx-first fn-asx-hitp fn-asx-done-state
                                     fn-asx-outcome)
           :expand ((:free (it) (fn-asx-need it))
                    (:free (a b c) (fn-asx-prefix-equalp a b c))))))

(defteeth fn-asx-walk-is-lookup
  :claim (()
   (implies (and (member-eq mode '(:number :current)) (stringp group) (posp number)
                (natp fuel)
                (<= (fn-asx-need (fn-ast-select-state mode group number articles nil nil nil 0 :next))
                    fuel))
           (equal (fn-asx-outcome
                   (fn-ast-select-step
                    (fn-ast-select-state mode group number articles nil nil nil 0 :next) fuel))
                  (fn-asx-outcome
                   (fn-asx-done-state mode group number
                                      (fn-asx-first mode group number articles))))))
  :subject fn-ast-select-step
  :witness ((mode :number) (group "fn.test") (number 2) (fuel 200) (articles *aot-articles*))
  :witness-lemma aot-walk-witness
  :breaks nil
  :mutations ((wrong-number (:conclusion (implies (and (member-eq mode '(:number :current)) (stringp group) (posp number)
                (natp fuel)
                (<= (fn-asx-need (fn-ast-select-state mode group number articles nil nil nil 0 :next))
                    fuel))
           (equal (fn-asx-outcome
                   (fn-ast-select-step
                    (fn-ast-select-state mode group number articles nil nil nil 0 :next) fuel))
                  (fn-asx-outcome (fn-asx-done-state mode group (+ 1 number) (fn-asx-first mode group number articles))))))
               ((mode :number) (group "fn.test") (number 2) (fuel 200) (articles *aot-articles*))
               :fault "a lookup that answers the next number's row"
               :lemma aot-walk-wrong-number)
              (withdrawn-row (:conclusion (implies (and (member-eq mode '(:number :current)) (stringp group) (posp number)
                (natp fuel)
                (<= (fn-asx-need (fn-ast-select-state mode group number articles nil nil nil 0 :next))
                    fuel))
           (equal (fn-asx-outcome
                   (fn-ast-select-step
                    (fn-ast-select-state mode group number articles nil nil nil 0 :next) fuel))
                  (fn-asx-outcome (fn-asx-done-state mode group number nil)))))
               ((mode :number) (group "fn.test") (number 2) (fuel 200) (articles *aot-articles*))
               :fault "a lookup that has lost (withdrawn) the row the walk finds"
               :lemma aot-walk-withdrawn-row)))

; ---- fn-asx-msgid-walk-is-lookup
(defthm aot-msgid-walk-witness
  (implies (and (stringp "<b@x>") (natp 200) (<= (fn-asx-nc "<b@x>" *aot-articles*) 200))
  (equal (fn-ast-select-step (fn-ast-select-state :msgid "fn.test" "<b@x>" *aot-articles* nil nil nil 0 :msgid-next) 200)
                  (fn-ast-select-step
                   (let ((article (fn-find-article "<b@x>" *aot-articles*)) (key "<b@x>") (group "fn.test"))
                     (if (consp article)
                         (fn-ast-msgid-local-start group article)
                       (fn-ast-select-state :msgid group key nil nil nil nil 0 :missing)))
                   (- 200 (fn-asx-nc "<b@x>" *aot-articles*)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ast-msgid-local-start fn-find-article fn-asx-nc))))

(defthm aot-msgid-walk-wrong-id
  (and (implies (and (stringp "<b@x>") (natp 200) (<= (fn-asx-nc "<b@x>" *aot-articles*) 200))
  (equal (fn-ast-select-step (fn-ast-select-state :msgid "fn.test" "<b@x>" *aot-articles* nil nil nil 0 :msgid-next) 200)
                  (fn-ast-select-step
                   (let ((article (fn-find-article "<b@x>" *aot-articles*)) (key "<b@x>") (group "fn.test"))
                     (if (consp article)
                         (fn-ast-msgid-local-start group article)
                       (fn-ast-select-state :msgid group key nil nil nil nil 0 :missing)))
                   (- 200 (fn-asx-nc "<b@x>" *aot-articles*)))))
       (not (implies (and (stringp "<b@x>") (natp 200) (<= (fn-asx-nc "<b@x>" *aot-articles*) 200))
  (equal (fn-ast-select-step (fn-ast-select-state :msgid "fn.test" "<b@x>" *aot-articles* nil nil nil 0 :msgid-next) 200)
                  (fn-ast-select-step
                   (let ((article (fn-find-article "<c@x>" *aot-articles*)) (key "<b@x>") (group "fn.test"))
                     (if (consp article)
                         (fn-ast-msgid-local-start group article)
                       (fn-ast-select-state :msgid group key nil nil nil nil 0 :missing)))
                   (- 200 (fn-asx-nc "<b@x>" *aot-articles*)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ast-msgid-local-start fn-find-article fn-asx-nc))))

(defthm aot-msgid-walk-withdrawn-row
  (and (implies (and (stringp "<b@x>") (natp 200) (<= (fn-asx-nc "<b@x>" *aot-articles*) 200))
  (equal (fn-ast-select-step (fn-ast-select-state :msgid "fn.test" "<b@x>" *aot-articles* nil nil nil 0 :msgid-next) 200)
                  (fn-ast-select-step
                   (let ((article (fn-find-article "<b@x>" *aot-articles*)) (key "<b@x>") (group "fn.test"))
                     (if (consp article)
                         (fn-ast-msgid-local-start group article)
                       (fn-ast-select-state :msgid group key nil nil nil nil 0 :missing)))
                   (- 200 (fn-asx-nc "<b@x>" *aot-articles*)))))
       (not (implies (and (stringp "<b@x>") (natp 200) (<= (fn-asx-nc "<b@x>" *aot-articles*) 200))
  (equal (fn-ast-select-step (fn-ast-select-state :msgid "fn.test" "<b@x>" *aot-articles* nil nil nil 0 :msgid-next) 200)
                  (fn-ast-select-step
                   (let ((article nil) (key "<b@x>") (group "fn.test"))
                     (if (consp article)
                         (fn-ast-msgid-local-start group article)
                       (fn-ast-select-state :msgid group key nil nil nil nil 0 :missing)))
                   (- 200 (fn-asx-nc "<b@x>" *aot-articles*)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ast-msgid-local-start fn-find-article fn-asx-nc))))

(defteeth fn-asx-msgid-walk-is-lookup
  :claim (() (implies (and (stringp key) (natp fuel) (<= (fn-asx-nc key rem) fuel))
  (equal (fn-ast-select-step (fn-ast-select-state :msgid group key rem nil nil nil 0 :msgid-next) fuel)
                  (fn-ast-select-step
                   (let ((article (fn-find-article key rem)))
                     (if (consp article)
                         (fn-ast-msgid-local-start group article)
                       (fn-ast-select-state :msgid group key nil nil nil nil 0 :missing)))
                   (- fuel (fn-asx-nc key rem))))))
  :subject fn-ast-select-step
  :witness ((key "<b@x>") (group "fn.test") (fuel 200) (rem *aot-articles*))
  :witness-lemma aot-msgid-walk-witness
  :breaks nil
  :mutations ((wrong-message-id (:conclusion (implies (and (stringp key) (natp fuel) (<= (fn-asx-nc key rem) fuel))
  (equal (fn-ast-select-step (fn-ast-select-state :msgid group key rem nil nil nil 0 :msgid-next) fuel)
                  (fn-ast-select-step
                   (let ((article (fn-find-article "<c@x>" rem)))
                     (if (consp article)
                         (fn-ast-msgid-local-start group article)
                       (fn-ast-select-state :msgid group key nil nil nil nil 0 :missing)))
                   (- fuel (fn-asx-nc key rem))))))
               ((key "<b@x>") (group "fn.test") (fuel 200) (rem *aot-articles*))
               :fault "a catalog column that answers another message-id's row"
               :lemma aot-msgid-walk-wrong-id)
              (withdrawn-row (:conclusion (implies (and (stringp key) (natp fuel) (<= (fn-asx-nc key rem) fuel))
  (equal (fn-ast-select-step (fn-ast-select-state :msgid group key rem nil nil nil 0 :msgid-next) fuel)
                  (fn-ast-select-step
                   (let ((article nil))
                     (if (consp article)
                         (fn-ast-msgid-local-start group article)
                       (fn-ast-select-state :msgid group key nil nil nil nil 0 :missing)))
                   (- fuel (fn-asx-nc key rem))))))
               ((key "<b@x>") (group "fn.test") (fuel 200) (rem *aot-articles*))
               :fault "a catalog column that has lost (withdrawn) the row the walk finds"
               :lemma aot-msgid-walk-withdrawn-row)))

; ---------------------------------------------------------------------------
; The four catalog-start keystones, at the served-catalog fixture's view 3
; (three rows: <a@x> fn.test 1, <b@x> fn.test 2 and fn.other 1, <c@x> fn.test 3).
(defmacro aot-arch () '(scct-arch 3))
(defmacro aot-index () '(scct-index 3))
(defmacro aot-v () '(fn-scr-view-of 3 *scct-c*))
; the view one record behind: the catalog has lost (withdrawn) the rows after <a@x>
(defmacro aot-v1 () '(fn-scr-view-of 1 *scct-c*))
(defmacro aot-start-cat-at (session args v)
  `(fn-asto-selection-start-cat ,session ,v ,args *scct-a* *scct-c*))
(defmacro aot-start (session args)
  `(fn-asto-selection-start ,session (aot-arch) (aot-index) ,args))
(defmacro aot-args (s) `(list (fn-nntp-string-octets ,s)))
(defconst *aot-session* (fn-nntp-make-session t "fn.test" 2 t))
(defconst *aot-session-3* (fn-nntp-make-session t "fn.test" 3 t))

; A stale view is no catalog of the archive: the first conjunct of fn-scr-catalogp.
(defthm aot-stale-view-is-no-catalog
  (and (fn-scr-catalogp (aot-arch) (aot-index) (aot-v) *scct-a* *scct-c*)
       (not (fn-scr-catalogp (aot-arch) (aot-index) (aot-v1) *scct-a* *scct-c*)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-scr-catalogp fn-asx-need fn-asx-goodp fn-ast-select-one
                                     fn-ast-select-donep fn-asx-prefix-equalp fn-asx-first fn-asx-hitp
                                     fn-asx-done-state fn-asx-outcome fn-asto-selection-start
                                     fn-asto-selection-start-cat fn-ast-msgid-local-start
                                     fn-find-article fn-asx-nc fn-nntp-number-tokenp
                                     fn-nntp-message-id-tokenp)
           :expand ((:free (it) (fn-asx-need it))
                    (:free (a b c) (fn-asx-prefix-equalp a b c))))))

; ---- fn-asto-selection-start-cat-number (hypotheses by conjunct, then the conclusion)
(defthm aot-cat-number-positive
  (and (fn-scr-catalogp (aot-arch) (aot-index) (aot-v) *scct-a* *scct-c*)
       (fn-nntp-session-group *aot-session*)
       (consp (aot-args "2")) (null (cdr (aot-args "2")))
       (fn-nntp-number-tokenp (car (aot-args "2")))
       (posp 200)
       (<= (fn-asx-need (aot-start *aot-session* (aot-args "2"))) 200)
       (equal (fn-asx-outcome (fn-ast-select-step (aot-start *aot-session* (aot-args "2")) 200))
              (fn-asx-outcome (aot-start-cat-at *aot-session* (aot-args "2") (aot-v))))
       (equal (fn-asx-outcome (aot-start-cat-at *aot-session* (aot-args "2") (aot-v)))
              (list :number "fn.test" 2 :selected '("<b@x>" 1 ("fn.test" "fn.other") (("fn.test" . 2) ("fn.other" . 1)) t 5))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-scr-catalogp fn-asx-need fn-asx-goodp fn-ast-select-one
                                     fn-ast-select-donep fn-asx-prefix-equalp fn-asx-first fn-asx-hitp
                                     fn-asx-done-state fn-asx-outcome fn-asto-selection-start
                                     fn-asto-selection-start-cat fn-ast-msgid-local-start
                                     fn-find-article fn-asx-nc fn-nntp-number-tokenp
                                     fn-nntp-message-id-tokenp)
           :expand ((:free (it) (fn-asx-need it))
                    (:free (a b c) (fn-asx-prefix-equalp a b c))))))

; Teeth: a lookup that answers the wrong number, and one that has lost the row.
(defthm aot-cat-number-wrong-number
  (and (fn-scr-catalogp (aot-arch) (aot-index) (aot-v) *scct-a* *scct-c*)
       (<= (fn-asx-need (aot-start *aot-session* (aot-args "2"))) 200)
       (equal (fn-asx-outcome (fn-ast-select-step (aot-start *aot-session* (aot-args "2")) 200))
              (list :number "fn.test" 2 :selected '("<b@x>" 1 ("fn.test" "fn.other") (("fn.test" . 2) ("fn.other" . 1)) t 5)))
       (not (equal (fn-asx-outcome (fn-ast-select-step (aot-start *aot-session* (aot-args "2")) 200))
                   (fn-asx-outcome (aot-start-cat-at *aot-session* (aot-args "3") (aot-v))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-scr-catalogp fn-asx-need fn-asx-goodp fn-ast-select-one
                                     fn-ast-select-donep fn-asx-prefix-equalp fn-asx-first fn-asx-hitp
                                     fn-asx-done-state fn-asx-outcome fn-asto-selection-start
                                     fn-asto-selection-start-cat fn-ast-msgid-local-start
                                     fn-find-article fn-asx-nc fn-nntp-number-tokenp
                                     fn-nntp-message-id-tokenp)
           :expand ((:free (it) (fn-asx-need it))
                    (:free (a b c) (fn-asx-prefix-equalp a b c))))))

(defthm aot-cat-number-withdrawn-row
  (and (<= (fn-asx-need (aot-start *aot-session* (aot-args "2"))) 200)
       (not (fn-scr-catalogp (aot-arch) (aot-index) (aot-v1) *scct-a* *scct-c*))
       (equal (fn-asx-outcome (fn-ast-select-step (aot-start *aot-session* (aot-args "2")) 200))
              (list :number "fn.test" 2 :selected '("<b@x>" 1 ("fn.test" "fn.other") (("fn.test" . 2) ("fn.other" . 1)) t 5)))
       (equal (fn-asx-outcome (aot-start-cat-at *aot-session* (aot-args "2") (aot-v1)))
              (list :number "fn.test" 2 :missing nil)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-scr-catalogp fn-asx-need fn-asx-goodp fn-ast-select-one
                                     fn-ast-select-donep fn-asx-prefix-equalp fn-asx-first fn-asx-hitp
                                     fn-asx-done-state fn-asx-outcome fn-asto-selection-start
                                     fn-asto-selection-start-cat fn-ast-msgid-local-start
                                     fn-find-article fn-asx-nc fn-nntp-number-tokenp
                                     fn-nntp-message-id-tokenp)
           :expand ((:free (it) (fn-asx-need it))
                    (:free (a b c) (fn-asx-prefix-equalp a b c))))))

; ---- fn-asto-selection-start-cat-current
(defthm aot-cat-current-positive
  (and (fn-scr-catalogp (aot-arch) (aot-index) (aot-v) *scct-a* *scct-c*)
       (fn-nntp-session-group *aot-session*) (null nil)
       (posp (fn-nntp-session-current *aot-session*))
       (<= (fn-nntp-session-current *aot-session*) *fn-nntp-max-article-number*)
       (posp 200)
       (<= (fn-asx-need (aot-start *aot-session* nil)) 200)
       (equal (fn-asx-outcome (fn-ast-select-step (aot-start *aot-session* nil) 200))
              (fn-asx-outcome (aot-start-cat-at *aot-session* nil (aot-v))))
       (equal (fn-asx-outcome (aot-start-cat-at *aot-session* nil (aot-v)))
              (list :current "fn.test" 2 :selected '("<b@x>" 1 ("fn.test" "fn.other") (("fn.test" . 2) ("fn.other" . 1)) t 5))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-scr-catalogp fn-asx-need fn-asx-goodp fn-ast-select-one
                                     fn-ast-select-donep fn-asx-prefix-equalp fn-asx-first fn-asx-hitp
                                     fn-asx-done-state fn-asx-outcome fn-asto-selection-start
                                     fn-asto-selection-start-cat fn-ast-msgid-local-start
                                     fn-find-article fn-asx-nc fn-nntp-number-tokenp
                                     fn-nntp-message-id-tokenp)
           :expand ((:free (it) (fn-asx-need it))
                    (:free (a b c) (fn-asx-prefix-equalp a b c))))))

(defthm aot-cat-current-wrong-number
  (and (fn-scr-catalogp (aot-arch) (aot-index) (aot-v) *scct-a* *scct-c*)
       (<= (fn-asx-need (aot-start *aot-session* nil)) 200)
       (equal (fn-asx-outcome (fn-ast-select-step (aot-start *aot-session* nil) 200))
              (list :current "fn.test" 2 :selected '("<b@x>" 1 ("fn.test" "fn.other") (("fn.test" . 2) ("fn.other" . 1)) t 5)))
       (not (equal (fn-asx-outcome (fn-ast-select-step (aot-start *aot-session* nil) 200))
                   (fn-asx-outcome (aot-start-cat-at *aot-session-3* nil (aot-v))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-scr-catalogp fn-asx-need fn-asx-goodp fn-ast-select-one
                                     fn-ast-select-donep fn-asx-prefix-equalp fn-asx-first fn-asx-hitp
                                     fn-asx-done-state fn-asx-outcome fn-asto-selection-start
                                     fn-asto-selection-start-cat fn-ast-msgid-local-start
                                     fn-find-article fn-asx-nc fn-nntp-number-tokenp
                                     fn-nntp-message-id-tokenp)
           :expand ((:free (it) (fn-asx-need it))
                    (:free (a b c) (fn-asx-prefix-equalp a b c))))))

(defthm aot-cat-current-withdrawn-row
  (and (<= (fn-asx-need (aot-start *aot-session* nil)) 200)
       (not (fn-scr-catalogp (aot-arch) (aot-index) (aot-v1) *scct-a* *scct-c*))
       (equal (fn-asx-outcome (fn-ast-select-step (aot-start *aot-session* nil) 200))
              (list :current "fn.test" 2 :selected '("<b@x>" 1 ("fn.test" "fn.other") (("fn.test" . 2) ("fn.other" . 1)) t 5)))
       (equal (fn-asx-outcome (aot-start-cat-at *aot-session* nil (aot-v1)))
              (list :current "fn.test" 2 :missing nil)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-scr-catalogp fn-asx-need fn-asx-goodp fn-ast-select-one
                                     fn-ast-select-donep fn-asx-prefix-equalp fn-asx-first fn-asx-hitp
                                     fn-asx-done-state fn-asx-outcome fn-asto-selection-start
                                     fn-asto-selection-start-cat fn-ast-msgid-local-start
                                     fn-find-article fn-asx-nc fn-nntp-number-tokenp
                                     fn-nntp-message-id-tokenp)
           :expand ((:free (it) (fn-asx-need it))
                    (:free (a b c) (fn-asx-prefix-equalp a b c))))))

; ---- fn-asto-selection-start-cat-msgid (the pinned trie answers the same start state)
(defthm aot-cat-msgid-positive
  (and (fn-scr-catalogp (aot-arch) (aot-index) (aot-v) *scct-a* *scct-c*)
       (fn-gidx-pinp (aot-index))
       (consp (aot-args "<b@x>")) (null (cdr (aot-args "<b@x>")))
       (fn-nntp-message-id-tokenp (car (aot-args "<b@x>"))) (fn-octet-listp (car (aot-args "<b@x>")))
       (equal (aot-start *aot-session* (aot-args "<b@x>"))
              (aot-start-cat-at *aot-session* (aot-args "<b@x>") (aot-v)))
       (consp (fn-ast-at 5 (aot-start *aot-session* (aot-args "<b@x>"))))
       (equal (aot-start *aot-session* (aot-args "<zz@x>"))
              (aot-start-cat-at *aot-session* (aot-args "<zz@x>") (aot-v)))
       (equal (fn-ast-at 9 (aot-start *aot-session* (aot-args "<zz@x>"))) :missing))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-scr-catalogp fn-asx-need fn-asx-goodp fn-ast-select-one
                                     fn-ast-select-donep fn-asx-prefix-equalp fn-asx-first fn-asx-hitp
                                     fn-asx-done-state fn-asx-outcome fn-asto-selection-start
                                     fn-asto-selection-start-cat fn-ast-msgid-local-start
                                     fn-find-article fn-asx-nc fn-nntp-number-tokenp
                                     fn-nntp-message-id-tokenp)
           :expand ((:free (it) (fn-asx-need it))
                    (:free (a b c) (fn-asx-prefix-equalp a b c))))))

(defthm aot-cat-msgid-wrong-message-id
  (and (fn-scr-catalogp (aot-arch) (aot-index) (aot-v) *scct-a* *scct-c*)
       (not (equal (aot-start *aot-session* (aot-args "<b@x>"))
                   (aot-start-cat-at *aot-session* (aot-args "<c@x>") (aot-v)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-scr-catalogp fn-asx-need fn-asx-goodp fn-ast-select-one
                                     fn-ast-select-donep fn-asx-prefix-equalp fn-asx-first fn-asx-hitp
                                     fn-asx-done-state fn-asx-outcome fn-asto-selection-start
                                     fn-asto-selection-start-cat fn-ast-msgid-local-start
                                     fn-find-article fn-asx-nc fn-nntp-number-tokenp
                                     fn-nntp-message-id-tokenp)
           :expand ((:free (it) (fn-asx-need it))
                    (:free (a b c) (fn-asx-prefix-equalp a b c))))))

(defthm aot-cat-msgid-withdrawn-row
  (and (not (fn-scr-catalogp (aot-arch) (aot-index) (aot-v1) *scct-a* *scct-c*))
       (consp (fn-ast-at 5 (aot-start *aot-session* (aot-args "<b@x>"))))
       (equal (fn-ast-at 9 (aot-start-cat-at *aot-session* (aot-args "<b@x>") (aot-v1))) :missing)
       (not (equal (aot-start *aot-session* (aot-args "<b@x>"))
                   (aot-start-cat-at *aot-session* (aot-args "<b@x>") (aot-v1)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-scr-catalogp fn-asx-need fn-asx-goodp fn-ast-select-one
                                     fn-ast-select-donep fn-asx-prefix-equalp fn-asx-first fn-asx-hitp
                                     fn-asx-done-state fn-asx-outcome fn-asto-selection-start
                                     fn-asto-selection-start-cat fn-ast-msgid-local-start
                                     fn-find-article fn-asx-nc fn-nntp-number-tokenp
                                     fn-nntp-message-id-tokenp)
           :expand ((:free (it) (fn-asx-need it))
                    (:free (a b c) (fn-asx-prefix-equalp a b c))))))

; ---- fn-asto-selection-start-cat-msgid-unpinned (no trie: the walk's nc steps, then the lookup)
; the archive with no pin: the index is the Message-ID trie itself
(defmacro aot-trie () '(fn-midx-build (fn-cat-view-articles 3 *scct-a* *scct-c*)))
(defmacro aot-start-unpinned (session args)
  `(fn-asto-selection-start ,session (aot-arch) (aot-trie) ,args))

(defthm aot-cat-msgid-unpinned-positive
  (and (fn-scr-catalogp (aot-arch) (aot-trie) (aot-v) *scct-a* *scct-c*)
       (not (fn-gidx-pinp (aot-trie)))
       (consp (aot-args "<b@x>")) (null (cdr (aot-args "<b@x>")))
       (fn-nntp-message-id-tokenp (car (aot-args "<b@x>"))) (fn-octet-listp (car (aot-args "<b@x>")))
       (natp 200)
       (equal (fn-ast-select-step (aot-start-unpinned *aot-session* (aot-args "<b@x>"))
                                  (+ (fn-asx-nc "<b@x>" *aot-articles*) 200))
              (fn-ast-select-step (aot-start-cat-at *aot-session* (aot-args "<b@x>") (aot-v)) 200))
       (equal (fn-ast-at 9 (fn-ast-select-step (aot-start-cat-at *aot-session* (aot-args "<b@x>") (aot-v)) 200))
              :selected))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-scr-catalogp fn-asx-need fn-asx-goodp fn-ast-select-one
                                     fn-ast-select-donep fn-asx-prefix-equalp fn-asx-first fn-asx-hitp
                                     fn-asx-done-state fn-asx-outcome fn-asto-selection-start
                                     fn-asto-selection-start-cat fn-ast-msgid-local-start
                                     fn-find-article fn-asx-nc fn-nntp-number-tokenp
                                     fn-nntp-message-id-tokenp)
           :expand ((:free (it) (fn-asx-need it))
                    (:free (a b c) (fn-asx-prefix-equalp a b c))))))

(defthm aot-cat-msgid-unpinned-wrong-message-id
  (and (fn-scr-catalogp (aot-arch) (aot-trie) (aot-v) *scct-a* *scct-c*)
       (not (equal (fn-ast-select-step (aot-start-unpinned *aot-session* (aot-args "<b@x>"))
                                       (+ (fn-asx-nc "<b@x>" *aot-articles*) 200))
                   (fn-ast-select-step (aot-start-cat-at *aot-session* (aot-args "<c@x>") (aot-v)) 200))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-scr-catalogp fn-asx-need fn-asx-goodp fn-ast-select-one
                                     fn-ast-select-donep fn-asx-prefix-equalp fn-asx-first fn-asx-hitp
                                     fn-asx-done-state fn-asx-outcome fn-asto-selection-start
                                     fn-asto-selection-start-cat fn-ast-msgid-local-start
                                     fn-find-article fn-asx-nc fn-nntp-number-tokenp
                                     fn-nntp-message-id-tokenp)
           :expand ((:free (it) (fn-asx-need it))
                    (:free (a b c) (fn-asx-prefix-equalp a b c))))))

(defthm aot-cat-msgid-unpinned-withdrawn-row
  (and (not (fn-scr-catalogp (aot-arch) (aot-trie) (aot-v1) *scct-a* *scct-c*))
       (equal (fn-ast-at 9 (fn-ast-select-step (aot-start-unpinned *aot-session* (aot-args "<b@x>"))
                                               (+ (fn-asx-nc "<b@x>" *aot-articles*) 200)))
              :selected)
       (equal (fn-ast-at 9 (fn-ast-select-step (aot-start-cat-at *aot-session* (aot-args "<b@x>") (aot-v1)) 200))
              :missing)
       (not (equal (fn-ast-select-step (aot-start-unpinned *aot-session* (aot-args "<b@x>"))
                                       (+ (fn-asx-nc "<b@x>" *aot-articles*) 200))
                   (fn-ast-select-step (aot-start-cat-at *aot-session* (aot-args "<b@x>") (aot-v1)) 200))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-scr-catalogp fn-asx-need fn-asx-goodp fn-ast-select-one
                                     fn-ast-select-donep fn-asx-prefix-equalp fn-asx-first fn-asx-hitp
                                     fn-asx-done-state fn-asx-outcome fn-asto-selection-start
                                     fn-asto-selection-start-cat fn-ast-msgid-local-start
                                     fn-find-article fn-asx-nc fn-nntp-number-tokenp
                                     fn-nntp-message-id-tokenp)
           :expand ((:free (it) (fn-asx-need it))
                    (:free (a b c) (fn-asx-prefix-equalp a b c))))))


; ---- fn-asto-resume-ms (books/article-stream-owner.lisp): a LIST quantum is
; due on the loop's next pass, an OVER/NEWNEWS quantum waits ACL2's delay.
(defconst *aot-lst-plan* '(nil (:list-cursor (nil (x)))))
(defconst *aot-over-plan* '(nil (:over-cursor (x))))
(defconst *aot-article-plan* '(nil (:article-cursor x)))
(defconst *aot-preflight-plan* '(nil (:article-preflight x)))

(defteeth fn-asto-resume-ms-lst-is-immediate
  :claim (((lst (fn-qplan-lst-cursorp plan)))
          (equal (fn-asto-resume-ms plan) 0))
  :subject fn-asto-resume-ms
  :witness ((plan *aot-lst-plan*))
  :breaks ((lst ((plan *aot-over-plan*))))
  :mutations ((lst-waits
               (:conclusion (equal (fn-asto-resume-ms plan) 1))
               ((plan *aot-lst-plan*))
               :fault "a LIST yield that idles for the OVER delay")))

(defteeth fn-asto-resume-ms-over-waits
  :claim (((not-article (not (fn-asto-plan-articlep plan)))
           (not-preflight (not (fn-asto-preflight-planp plan)))
           (not-lst (not (fn-qplan-lst-cursorp plan))))
          (posp (fn-asto-resume-ms plan)))
  :subject fn-asto-resume-ms
  :witness ((plan *aot-over-plan*))
  :breaks ((not-article ((plan *aot-article-plan*)))
           (not-preflight ((plan *aot-preflight-plan*)))
           (not-lst ((plan *aot-lst-plan*))))
  :mutations ((over-immediate
               (:conclusion (equal (fn-asto-resume-ms plan) 0))
               ((plan *aot-over-plan*))
               :fault "an OVER quantum with no delay, rescanning a sparse range in one event")))
