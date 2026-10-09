; peer-offer-catalog.lisp -- the IHAVE/CHECK duplicate test is the catalog's
; Message-ID column (lane s-viewidx, 2026-10-08; P2 of
; planning/design/owner-view-index-removal-2026-10-08.md).
;
; fn-peer-history-hasp (books/peer-inbound.lisp) is raw membership: the
; node's acceptance articles, withdrawn ones included, plus its bindings.
; Under fn-node-statep a binding names an accepted article
; (fn-pix-peer-history-hasp-is-acceptedp), so the binding disjunct adds
; nothing and is not carried.  The catalog holds one row per acceptance
; article (fn-scj-acc-rowsp, the row relation the open establishes), so the
; history test is whether the Message-ID's column has a row.

(in-package "ACL2")

(include-book "peer-offer-indexed")
(include-book "served-catalog-join-number")

(local (defthm fn-poc-accepted-of-append
  (iff (fn-acceptedp m (append a b)) (or (fn-acceptedp m a) (fn-acceptedp m b)))
  :hints (("Goal" :in-theory (enable fn-acceptedp)))))

(local (defthm fn-poc-accepted-of-rev
  (iff (fn-acceptedp m (rev xs)) (fn-acceptedp m xs))
  :hints (("Goal" :in-theory (enable fn-acceptedp rev)))))

(local (defthm fn-poc-accepted-of-map
  (iff (fn-acceptedp m (fn-scj-arts-map c)) (consp (fn-cat-seqs-for m c i)))
  :hints (("Goal" :in-theory (enable fn-acceptedp fn-scj-arts-map fn-scj-row-art)
           :induct (fn-cat-seqs-for m c i)))))

; KEYSTONE.  The host's duplicate test is the column's non-emptiness: raw
; membership, so a withdrawn article's id is still known.  The node
; invariant carries the bindings (they are accepted articles'); the row
; relation carries the catalog.
(defthm fn-peer-history-hasp-is-the-catalog-column
  (implies (and (fn-node-statep node)
                (fn-scj-acc-rowsp (fn-node-acceptance node) fn-cat))
           (equal (fn-peer-history-hasp msgid node)
                  (if (consp (fn-cat-msgid-seqs msgid fn-cat)) t nil)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-scj-acc-rowsp fn-scj-rows-arts fn-cat-msgid-seqs-is-seqs-for)
                                  (fn-peer-history-hasp fn-node-statep fn-acceptedp fn-scj-arts-map
                                   fn-pix-peer-history-hasp-is-acceptedp fn-poc-accepted-of-rev
                                   fn-poc-accepted-of-map))
           :use ((:instance fn-pix-peer-history-hasp-is-acceptedp)
                 (:instance fn-poc-accepted-of-map (m msgid) (c fn-cat) (i 0))
                 (:instance fn-poc-accepted-of-rev (m msgid) (xs (fn-scj-arts-map fn-cat)))))))
