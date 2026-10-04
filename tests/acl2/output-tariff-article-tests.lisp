; Teeth of the ARTICLE tariff's keystones (books/output-tariff-article.lisp;
; planning/design/tariff-2026-10-04.md Q3).  Each claim is bound to the
; theorem as the world stores it; one removal witness per declared
; hypothesis; the boundary mutation is the off-by-one admission.
(in-package "ACL2")
(include-book "../../books/output-tariff-article")
(include-book "../../books/defkeystone")
(include-book "std/testing/assert-bang" :dir :system)

(defconst *tat-preview* '(:preview 9 :article ((65 82 84 73 67 76 69) (49))))
(defconst *tat-capacity* 1048576)
(defconst *tat-u64* 18446744073709551616)

; The figure at the witness: 2 * 16 * (293 + 2*1000 + 3) + 1000.
(assert! (equal *fn-tariff-article-initial-octets* 293))
(assert! (equal (fn-tariff-article-octets 1000) 74472))
(assert! (equal (fn-tariff-article-descriptor 1000) '(:tariff :article 74472)))
(assert! (equal (fn-tariff-article-descriptor *fn-tariff-article-elen-max*)
                '(:unrepresentable :article)))
; The largest representable length still fits the descriptor's u64 domain.
(assert! (< (fn-tariff-article-octets (1- *fn-tariff-article-elen-max*)) *tat-u64*))

(defteeth fn-tariff-article-descriptor-is-a-tariff
  :claim (((natural (natp elen))
           (representable (< elen *fn-tariff-article-elen-max*)))
          (fn-ocap-tariffp (fn-tariff-article-descriptor elen)))
  :subject fn-tariff-article-descriptor
  :witness ((elen 1000))
  :breaks ((natural ((elen -1)))
           (representable ((elen 72057594037927936))))
  :mutations ((other-family
               (:conclusion (equal (fn-ocap-at 1 (fn-tariff-article-descriptor elen)) :head))
               ((elen 1000))
               :fault "a producer that names a family other than the one it priced")))

(defteeth fn-tariff-article-admits-exactly-within-capacity
  :claim (((natural (natp elen))
           (representable (< elen *fn-tariff-article-elen-max*))
           (preview (fn-ocap-previewp preview))
           (article (equal (fn-ocap-at 2 preview) :article))
           (capacity-natural (natp capacity))
           (capacity-u64 (< capacity 18446744073709551616)))
          (equal (fn-ocap-admit-preview preview (fn-tariff-article-descriptor elen) capacity)
                 (if (<= (fn-tariff-article-octets elen) capacity)
                     (list :hold (fn-ocap-at 1 preview) :article)
                   (list :refused :output-tariff-unaffordable :article))))
  :subject fn-tariff-article-descriptor
  :witness ((elen 1000) (preview *tat-preview*) (capacity *tat-capacity*))
  :breaks ((natural ((elen -1) (preview *tat-preview*) (capacity *tat-capacity*))
                    :logical "a negative length is outside the octet count's guard; the descriptor refuses it as unrepresentable while the figure would admit")
           (representable ((elen 72057594037927936) (preview *tat-preview*)
                           (capacity 18446744073709551615)))
           (preview ((elen 1000) (preview '(:preview -1 :article nil)) (capacity *tat-capacity*)))
           (article ((elen 1000) (preview '(:preview 9 :newnews nil)) (capacity *tat-capacity*)))
           (capacity-natural ((elen 1000) (preview *tat-preview*) (capacity 4194305/2)))
           (capacity-u64 ((elen 1000) (preview *tat-preview*) (capacity 18446744073709551616))))
  :mutations ((strict-boundary
               (:conclusion (equal (fn-ocap-admit-preview preview (fn-tariff-article-descriptor elen) capacity)
                                   (if (< (fn-tariff-article-octets elen) capacity)
                                       (list :hold (fn-ocap-at 1 preview) :article)
                                     (list :refused :output-tariff-unaffordable :article))))
               ((elen 1000) (preview *tat-preview*) (capacity 74472))
               :fault "an affordable article refused at exactly its price")
              (always-hold
               (:conclusion (equal (fn-ocap-at 0 (fn-ocap-admit-preview preview (fn-tariff-article-descriptor elen) capacity))
                                   :hold))
               ((elen 1000) (preview *tat-preview*) (capacity 74471))
               :fault "an unaffordable article admitted for lack of a price check")))

(defteeth fn-tariff-article-unrepresentable-is-refused
  :claim (((unrepresentable (not (and (natp elen) (< elen *fn-tariff-article-elen-max*)))))
          (equal (fn-ocap-at 0 (fn-ocap-admit-preview preview (fn-tariff-article-descriptor elen) capacity))
                 :refused))
  :subject fn-tariff-article-descriptor
  :witness ((elen 72057594037927936) (preview *tat-preview*) (capacity 18446744073709551615))
  :breaks ((unrepresentable ((elen 1000) (preview *tat-preview*) (capacity *tat-capacity*))))
  :mutations ((saturated
               (:conclusion (equal (fn-ocap-admit-preview preview (fn-tariff-article-descriptor elen) capacity)
                                   (list :refused :output-tariff-unaffordable :article)))
               ((elen 72057594037927936) (preview *tat-preview*) (capacity 18446744073709551615))
               :fault "an unrepresentable length saturated to an unaffordable price instead of refused by name")))

(defteeth-check)
