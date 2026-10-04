; Teeth of the family tariff generator (books/output-tariff-family.lisp) and
; witnesses of its rows (books/output-tariff-families.lisp) over the
; served-catalog fixture of tests/acl2/output-tariff-article-row-tests.lisp
; (three committed articles, views are counts).  The descriptor's keystones
; carry defteeth; the producer's take stobj formals, so their witnesses are
; ground theorems proved by evaluation, and a must-fail form follows the
; affirmative check of what it omits.
(in-package "ACL2")
(include-book "../../books/output-tariff-families")
(include-book "../../books/defkeystone")
(include-book "must-fail-checked")
(include-book "std/testing/assert-bang" :dir :system)

(defconst *tfm-preview* '(:preview 9 :head ((72 69 65 68) (50))))
(defconst *tfm-capacity* 1048576)

; ---------------------------------------------------------------------------
; The descriptor, every family.

; The ARTICLE figure at ELEN 1000: 2 * 16 * (293 + 2*1000 + 3) + 1000.
(assert! (equal *fn-tariff-article-initial-octets* 293))
(assert! (equal (fn-tariff-article-octets 1000) 74472))
(assert! (equal (fn-tariff-descriptor :head 1000) '(:tariff :head 1000)))
(assert! (equal (fn-tariff-descriptor :head *fn-tariff-u64*) '(:unrepresentable :head)))
(assert! (equal (fn-tariff-descriptor "head" 1000) '(:unrepresentable "head")))

(defteeth fn-tariff-descriptor-is-a-tariff
  :claim (((family (keywordp family))
           (natural (natp octets))
           (representable (< octets *fn-tariff-u64*)))
          (fn-ocap-tariffp (fn-tariff-descriptor family octets)))
  :subject fn-tariff-descriptor
  :witness ((family :head) (octets 1000))
  :breaks ((family ((family "head") (octets 1000)))
           (natural ((family :head) (octets -1)))
           (representable ((family :head) (octets 18446744073709551616))))
  :mutations ((other-family
               (:conclusion (equal (fn-ocap-at 1 (fn-tariff-descriptor family octets)) :article))
               ((family :head) (octets 1000))
               :fault "a producer that names a family other than the one it priced")))

(defteeth fn-tariff-descriptor-admits-exactly-within-capacity
  :claim (((preview (fn-ocap-previewp preview))
           (family (equal (fn-ocap-at 2 preview) family))
           (natural (natp octets))
           (representable (< octets *fn-tariff-u64*))
           (capacity-natural (natp capacity))
           (capacity-u64 (< capacity *fn-tariff-u64*)))
          (equal (fn-ocap-admit-preview preview (fn-tariff-descriptor family octets) capacity)
                 (if (<= octets capacity)
                     (list :hold (fn-ocap-at 1 preview) family)
                   (list :refused :output-tariff-unaffordable family))))
  :subject fn-tariff-descriptor
  :witness ((preview *tfm-preview*) (family :head) (octets 1000) (capacity *tfm-capacity*))
  :breaks ((preview ((preview '(:preview -1 :head nil)) (family :head) (octets 1000)
                     (capacity *tfm-capacity*)))
           (family ((preview '(:preview 9 :newnews nil)) (family :head) (octets 1000)
                    (capacity *tfm-capacity*)))
           (natural ((preview *tfm-preview*) (family :head) (octets -1) (capacity *tfm-capacity*))
                    :logical "a negative price is refused as unrepresentable while the figure would admit")
           (representable ((preview *tfm-preview*) (family :head) (octets 18446744073709551616)
                           (capacity 18446744073709551615)))
           (capacity-natural ((preview *tfm-preview*) (family :head) (octets 1000)
                              (capacity 4194305/2)))
           (capacity-u64 ((preview *tfm-preview*) (family :head) (octets 1000)
                          (capacity 18446744073709551616))))
  :mutations ((strict-boundary
               (:conclusion (equal (fn-ocap-admit-preview preview (fn-tariff-descriptor family octets) capacity)
                                   (if (< octets capacity)
                                       (list :hold (fn-ocap-at 1 preview) family)
                                     (list :refused :output-tariff-unaffordable family))))
               ((preview *tfm-preview*) (family :head) (octets 1000) (capacity 1000))
               :fault "an affordable reply refused at exactly its price")
              (always-hold
               (:conclusion (equal (fn-ocap-at 0 (fn-ocap-admit-preview preview (fn-tariff-descriptor family octets) capacity))
                                   :hold))
               ((preview *tfm-preview*) (family :head) (octets 1000) (capacity 999))
               :fault "an unaffordable reply admitted for lack of a price check")))

(defteeth fn-tariff-descriptor-unrepresentable-is-refused
  :claim (((unrepresentable (not (and (natp octets) (< octets *fn-tariff-u64*)))))
          (equal (fn-ocap-at 0 (fn-ocap-admit-preview preview (fn-tariff-descriptor family octets)
                                                      capacity))
                 :refused))
  :subject fn-tariff-descriptor
  :witness ((preview *tfm-preview*) (family :head) (octets 18446744073709551616)
            (capacity 18446744073709551615))
  :breaks ((unrepresentable ((preview *tfm-preview*) (family :head) (octets 1000)
                             (capacity *tfm-capacity*))))
  :mutations ((saturated
               (:conclusion (equal (fn-ocap-admit-preview preview (fn-tariff-descriptor family octets) capacity)
                                   (list :refused :output-tariff-unaffordable family)))
               ((preview *tfm-preview*) (family :head) (octets 18446744073709551616)
                (capacity 18446744073709551615))
               :fault "an unrepresentable price saturated to an unaffordable one instead of refused by name")))


; ---------------------------------------------------------------------------
; The rows, over the catalog fixture.

(defconst *tfm-p0* (append (fn-record-string-octets "Subject: a") '(13 10 13 10 65 13 10)))
(defconst *tfm-p1* (append (fn-record-string-octets "Subject: bb") '(13 10 13 10 66 66 13 10)))
(defconst *tfm-p2* (append (fn-record-string-octets "Subject: c") '(13 10 13 10 67 13 10)))
(defconst *tfm-w0* (fn-record-make 0 1 1 "<a@x>" *tfm-p0* '("fn.test") "o" "s" "e" 1 5))
(defconst *tfm-w1* (fn-record-make 1 2 2 "<b@x>" *tfm-p1* '("fn.test" "fn.other") "o" "s" "e" 1 5))
(defconst *tfm-w2* (fn-record-make 2 3 3 "<c@x>" *tfm-p2* '("fn.test") "o" "s" "e" 1 5))

(defun tfm-held (w handle numbers)
  (fn-held-make (fn-record-sequence w) (fn-record-txid w) (fn-record-generation w)
                (fn-record-msgid w) handle (fn-record-groups w) (fn-record-obligation-id w)
                (fn-record-content-subject w) (fn-record-release-evidence w)
                (fn-record-charge w) (fn-record-stamp w)
                (fn-held-facts-of (fn-record-payload w))
                (fn-held-context-of (fn-record-payload w) nil 0) numbers nil))

(defconst *tfm-a* (list *tfm-p0* *tfm-p1* *tfm-p2*))
(defconst *tfm-r0* (fn-cat-assign (tfm-held *tfm-w0* 0 nil) nil))
(defconst *tfm-r1* (fn-cat-assign (tfm-held *tfm-w1* 1 nil) (list *tfm-r0*)))
(defconst *tfm-r2* (fn-cat-assign (tfm-held *tfm-w2* 2 nil) (list *tfm-r0* *tfm-r1*)))
(defconst *tfm-c* (list *tfm-r0* *tfm-r1* *tfm-r2*))
; The connection's authenticated session: its reader session selects
; fn.test with current article 3 (the auth, peer and post layers each keep
; the next one as their first field), no access policy, no Xref server.
(defconst *tfm-as* '((((:session "fn.test" 3) nil))))

(defun tfm-preview (family number)
  (declare (xargs :guard (natp number)))
  (list :preview 9 family (list '(1) (list (+ 48 number)))))

; The figures at row 2 (19 octets): ARTICLE, HEAD and BODY the two spines
; of the dot-stuffed reply and the extent, STAT its line and the extent.
(defthm tfm-row-prices
  (and (equal (fn-tariff-family-price (tfm-preview :article 2) *tfm-as* nil *tfm-a* *tfm-c*)
              (fn-tariff-article-octets 19))
       (equal (fn-tariff-article-octets 19) 10707)
       (equal (fn-tariff-family-price (tfm-preview :head 2) *tfm-as* nil *tfm-a* *tfm-c*) 10707)
       (equal (fn-tariff-family-price (tfm-preview :body 2) *tfm-as* nil *tfm-a* *tfm-c*) 10707)
       (equal (fn-tariff-family-price (tfm-preview :stat 2) *tfm-as* nil *tfm-a* *tfm-c*)
              (fn-tariff-stat-octets 19))
       (equal (fn-tariff-stat-octets 19) 9395)
       ; the row 1's 17 octets, and no row
       (equal (fn-tariff-family-price (tfm-preview :head 1) *tfm-as* nil *tfm-a* *tfm-c*)
              (fn-tariff-article-octets 17))
       (equal (fn-tariff-family-price (tfm-preview :head 9) *tfm-as* nil *tfm-a* *tfm-c*)
              (fn-tariff-article-octets 0)))
  :rule-classes nil)

; RED BEFORE: the producer of lane tariff2 answered (:unpriced F) for every
; family but ARTICLE.  GREEN: HEAD, BODY and STAT are priced from the row;
; NEWNEWS stays unpriced.
(defthm tfm-producer-prices-the-retrieval-row
  (and (equal (fn-tariff-family-preview (tfm-preview :head 2) *tfm-as* nil *tfm-a* *tfm-c*)
              '(:tariff :head 10707))
       (equal (fn-tariff-family-preview (tfm-preview :body 2) *tfm-as* nil *tfm-a* *tfm-c*)
              '(:tariff :body 10707))
       (equal (fn-tariff-family-preview (tfm-preview :stat 2) *tfm-as* nil *tfm-a* *tfm-c*)
              '(:tariff :stat 9395))
       (equal (fn-tariff-family-preview (tfm-preview :article 2) *tfm-as* nil *tfm-a* *tfm-c*)
              '(:tariff :article 10707))
       (equal (fn-tariff-family-preview '(:preview 9 :newnews nil) *tfm-as* nil *tfm-a* *tfm-c*)
              '(:unpriced :newnews)))
  :rule-classes nil)

; The producer's keystone at its witness: held at exactly the price,
; unaffordable one octet under it, unpriced for a family no row names.
(defthm tfm-charges-before-effect-witness
  (and (fn-ocap-previewp (tfm-preview :head 2))
       (equal (fn-ocap-admit-preview (tfm-preview :head 2)
                                     (fn-tariff-family-preview (tfm-preview :head 2) *tfm-as* nil
                                                               *tfm-a* *tfm-c*)
                                     10707)
              '(:hold 9 :head))
       (equal (fn-ocap-admit-preview (tfm-preview :head 2)
                                     (fn-tariff-family-preview (tfm-preview :head 2) *tfm-as* nil
                                                               *tfm-a* *tfm-c*)
                                     10706)
              '(:refused :output-tariff-unaffordable :head))
       (equal (fn-ocap-admit-preview '(:preview 9 :newnews nil)
                                     (fn-tariff-family-preview '(:preview 9 :newnews nil) *tfm-as*
                                                               nil *tfm-a* *tfm-c*)
                                     10707)
              '(:refused :unpriced-output-family :newnews)))
  :rule-classes nil)

; Removal of the keystone's one hypothesis: a malformed preview is refused
; as invalid, which the family admission does not say.
(defthm tfm-charges-before-effect-without-preview
  (let ((preview '(:preview -1 :head nil)))
    (and (not (fn-ocap-previewp preview))
         (not (equal (fn-ocap-admit-preview preview
                                            (fn-tariff-family-preview preview *tfm-as* nil
                                                                      *tfm-a* *tfm-c*)
                                            10707)
                     (fn-tariff-family-admission
                      preview (member-eq (fn-ocap-at 2 preview) *fn-tariff-priced-families*)
                      (fn-tariff-family-price preview *tfm-as* nil *tfm-a* *tfm-c*)
                      10707)))))
  :rule-classes nil)

; Teeth: the HEAD price is not STAT's (the figure is the family's, not one
; shared number), and a family no row names is not held at any price.
(must-fail-checked
 (defthm tfm-teeth-head-is-not-stat
   (equal (fn-tariff-family-price (tfm-preview :head 2) *tfm-as* nil *tfm-a* *tfm-c*)
          (fn-tariff-family-price (tfm-preview :stat 2) *tfm-as* nil *tfm-a* *tfm-c*))
   :rule-classes nil))
(must-fail-checked
 (defthm tfm-teeth-every-family-held-at-the-head-price
   (equal (fn-ocap-at 0 (fn-ocap-admit-preview '(:preview 9 :newnews nil)
                                               (fn-tariff-family-preview '(:preview 9 :newnews nil)
                                                                         *tfm-as* nil *tfm-a* *tfm-c*)
                                               10707))
          :hold)
   :rule-classes nil))

; ---------------------------------------------------------------------------
; The line rows (lane tariff4): GROUP and the neighbour family.
;
; RED BEFORE: (:unpriced :group) and (:unpriced :neighbour).  GREEN: GROUP
; "fn.test" replies "211 n l h fn.test": 39 + 7 = 46 octets, 16 * (10 * 46 +
; 32) = 7872; NEXT and LAST the retrieval initial line, 16 * (10 * 293 + 32)
; = 47392, whatever the session's current article.
(defconst *tfm-group-preview*
  '(:preview 9 :group ((71 82 79 85 80) (102 110 46 116 101 115 116))))
(defconst *tfm-group-long-preview*
  '(:preview 9 :group ((71 82 79 85 80) (102 110 46 116 101 115 116 46 111 116 104 101 114))))
(defconst *tfm-next-preview* '(:preview 9 :neighbour ((78 69 88 84))))
(defconst *tfm-last-preview* '(:preview 9 :neighbour ((76 65 83 84))))

(assert! (equal (fn-tariff-line-octets 46) 7872))
(assert! (equal (fn-tariff-line-octets *fn-tariff-article-initial-octets*) 47392))

(defthm tfm-producer-prices-the-line-rows
  (and (equal (fn-tariff-family-preview *tfm-group-preview* *tfm-as* nil *tfm-a* *tfm-c*)
              '(:tariff :group 7872))
       ; the name's length is the price's argument: 6 more octets, 6 * 10 * 16 more
       (equal (fn-tariff-family-preview *tfm-group-long-preview* *tfm-as* nil *tfm-a* *tfm-c*)
              '(:tariff :group 8832))
       (equal (fn-tariff-family-preview *tfm-next-preview* *tfm-as* nil *tfm-a* *tfm-c*)
              '(:tariff :neighbour 47392))
       (equal (fn-tariff-family-preview *tfm-last-preview* *tfm-as* nil *tfm-a* *tfm-c*)
              '(:tariff :neighbour 47392))
       ; no argument: the syntax line, the literal part only
       (equal (fn-tariff-family-preview '(:preview 9 :group ((71 82 79 85 80))) *tfm-as* nil
                                        *tfm-a* *tfm-c*)
              '(:tariff :group 6752)))
  :rule-classes nil)

; The tariffs at the gate: GROUP held at exactly 7872, unaffordable at 7871.
(defthm tfm-line-rows-charge-before-effect-witness
  (and (equal (fn-ocap-admit-preview *tfm-group-preview*
                                     (fn-tariff-family-preview *tfm-group-preview* *tfm-as* nil
                                                               *tfm-a* *tfm-c*)
                                     7872)
              '(:hold 9 :group))
       (equal (fn-ocap-admit-preview *tfm-group-preview*
                                     (fn-tariff-family-preview *tfm-group-preview* *tfm-as* nil
                                                               *tfm-a* *tfm-c*)
                                     7871)
              '(:refused :output-tariff-unaffordable :group))
       (equal (fn-ocap-admit-preview *tfm-next-preview*
                                     (fn-tariff-family-preview *tfm-next-preview* *tfm-as* nil
                                                               *tfm-a* *tfm-c*)
                                     47391)
              '(:refused :output-tariff-unaffordable :neighbour)))
  :rule-classes nil)

; The reply bounds hold at the witness: the factories' own replies over the
; fixture catalog are within the figures the rows multiply.
(defconst *tfm-archive*
  (fn-make-state '("fn.test" "fn.other") '(("fn.test" . 4) ("fn.other" . 2))
                 nil 0 nil nil))

(defthm tfm-line-reply-bounds-witness
  (and (equal (fn-tariff-effects-octets
               (fn-nntp-result-effects
                (fn-av-nntp-group-result-cat '(t nil nil nil) *tfm-archive* "fn.test" 3 *tfm-c*)))
              19)
       (<= (fn-tariff-effects-octets
            (fn-nntp-result-effects
             (fn-av-nntp-next-or-last-cat '(t "fn.test" 1 nil) *tfm-archive* :next 3 *tfm-a* *tfm-c*)))
           *fn-tariff-article-initial-octets*))
  :rule-classes nil)

; Teeth: GROUP's price is not the neighbour's, and a longer name costs more.
(must-fail-checked
 (defthm tfm-teeth-group-is-not-neighbour
   (equal (fn-tariff-family-price *tfm-group-preview* *tfm-as* nil *tfm-a* *tfm-c*)
          (fn-tariff-family-price *tfm-next-preview* *tfm-as* nil *tfm-a* *tfm-c*))
   :rule-classes nil))
(must-fail-checked
 (defthm tfm-teeth-name-length-is-free
   (equal (fn-tariff-family-price *tfm-group-preview* *tfm-as* nil *tfm-a* *tfm-c*)
          (fn-tariff-family-price *tfm-group-long-preview* *tfm-as* nil *tfm-a* *tfm-c*))
   :rule-classes nil))

; DATE, MODE, QUIT (:close) and HELP: the session arm's fixed replies.  The
; session's reply bound is 64 octets, 16 * (10 * 64 + 32) = 10752; HELP's
; block is 248 octets, 16 * (10 * 248 + 32) = 40192.
(assert! (equal (fn-tariff-line-octets *fn-tariff-session-line-octets*) 10752))
(assert! (equal (fn-tariff-line-octets *fn-tariff-help-reply-octets*) 40192))

(defthm tfm-producer-prices-the-session-rows
  (and (equal (fn-tariff-family-preview '(:preview 9 :date ((68 65 84 69))) *tfm-as* nil *tfm-a* *tfm-c*)
              '(:tariff :date 10752))
       (equal (fn-tariff-family-preview '(:preview 9 :mode ((77 79 68 69) (82))) *tfm-as* nil *tfm-a* *tfm-c*)
              '(:tariff :mode 10752))
       (equal (fn-tariff-family-preview '(:preview 9 :close ((81 85 73 84))) *tfm-as* nil *tfm-a* *tfm-c*)
              '(:tariff :close 10752))
       (equal (fn-tariff-family-preview '(:preview 9 :help ((72 69 76 80))) *tfm-as* nil *tfm-a* *tfm-c*)
              '(:tariff :help 40192)))
  :rule-classes nil)

; The session arm's own replies, at ground sessions: HELP's block is exactly
; the 248 octets its row names; a DATE with no observation, MODE READER and
; QUIT answer within the session bound.
(defconst *tfm-session* '(t "fn.test" 3 nil))
(defthm tfm-session-reply-witness
  (and (equal (fn-tariff-effects-octets
               (fn-nntp-result-effects
                (fn-nntp-session-command *tfm-session* nil (fn-record-string-octets "HELP") nil)))
              *fn-tariff-help-reply-octets*)
       (<= (fn-tariff-effects-octets
            (fn-nntp-result-effects
             (fn-nntp-session-command *tfm-session* nil (fn-record-string-octets "DATE") nil)))
           *fn-tariff-session-line-octets*)
       (<= (fn-tariff-effects-octets
            (fn-nntp-result-effects
             (fn-nntp-session-command *tfm-session* nil (fn-record-string-octets "QUIT") nil)))
           *fn-tariff-session-line-octets*))
  :rule-classes nil)

; Teeth: HELP's block is not a DATE line.
(must-fail-checked
 (defthm tfm-teeth-help-is-not-date
   (equal (fn-tariff-family-price '(:preview 9 :help ((72 69 76 80))) *tfm-as* nil *tfm-a* *tfm-c*)
          (fn-tariff-family-price '(:preview 9 :date ((68 65 84 69))) *tfm-as* nil *tfm-a* *tfm-c*))
   :rule-classes nil))
