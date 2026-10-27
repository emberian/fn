; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-open-rows-correspondence")

(local (defthm fn-lbnme-hons-get-cons
 (equal (cdr (hons-assoc-equal query (cons (cons key value) table)))
        (if (equal query key) value (cdr (hons-assoc-equal query table))))
 :hints (("Goal" :in-theory (enable hons-assoc-equal assoc-equal)))))

(defthm fn-dmap-get-of-put
 (implies (and (fn-dm-lanep lane) (fn-dm-lanep read-lane))
 (equal (fn-dmap-get read-lane read-key (fn-dmap-put lane key value map))
        (if (and (equal read-lane lane) (equal read-key key)) value
            (fn-dmap-get read-lane read-key map))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-dmap-get fn-dmap$a-get fn-dmap-put fn-dmap$a-put fn-dm-nth-update-nth
 fn-dm-lanep fn-lbnme-hons-get-cons)))))

(defthm fn-dmap-get-of-clear
 (implies (fn-dm-lanep lane) (equal (fn-dmap-get lane key (fn-dmap-clear map)) nil))
 :hints (("Goal" :cases ((equal lane 0) (equal lane 1))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-dmap-get fn-dmap$a-get fn-dmap-clear fn-dmap$a-clear fn-dm-lanep
 nth hons-assoc-equal assoc-equal)))))

(defthm fn-lbc-number-get-frame-by-definition
 (implies (equal (nth 3 new) (nth 3 fn-lbc))
 (equal (fn-lbc-number-get group number new) (fn-lbc-number-get group number fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-number-get fn-lbc-number-store)))))

(defthm fn-lbc-summary-word-frame-by-definition
 (implies (equal (nth 3 new) (nth 3 fn-lbc))
 (equal (fn-lbc-summary-word group field new) (fn-lbc-summary-word group field fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-summary-word fn-lbc-number-store)))))

(defthm fn-lbc-tables-corr-frame-by-definition
 (implies (equal (nth 3 new) (nth 3 fn-lbc))
 (equal (fn-lbc-tables-corr new rows) (fn-lbc-tables-corr fn-lbc rows)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-tables-corr)))))

(defthm fn-lbc-number-get-of-number-put-first
 (equal (fn-lbc-number-get read-group read-number
          (fn-lbc-number-put-first group number i fn-lbc))
  (if (natp (fn-lbc-number-get group number fn-lbc))
      (fn-lbc-number-get read-group read-number fn-lbc)
    (if (and (equal read-group group) (equal read-number number)) i
        (fn-lbc-number-get read-group read-number fn-lbc))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-number-put-first fn-lbc-number-get fn-lbc-number-store update-fn-lbc-number-store
 fn-dm-nth-update-nth fn-dmap-get-of-put fn-dm-lanep)))))
