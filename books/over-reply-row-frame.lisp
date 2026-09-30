; Exact old NOV line framing, including the status owed transition.
(in-package "ACL2")
(include-book "over-reply-source")
(include-book "nov-render-line")

(local
 (defthm fn-orrf-decimal-field-is-non-dot
  (and (consp (fn-nntp-decimal-field number))
       (not (equal (car (fn-nntp-decimal-field number)) 46)))
  :hints (("Goal" :in-theory
   (e/d (fn-nntp-decimal-field fn-nntp-decimal-tokenp fn-nntp-decimal-digitp)
        (fn-nntp-decimal fn-nntp-decimal-rev))))))

(local
 (defthm fn-orrf-car-of-append
  (implies (consp a) (equal (car (append a b)) (car a)))))

(local
 (defthm fn-orrf-line-is-non-dot
  (not (equal (car (fn-nov-line number over)) 46))
  :hints (("Goal" :in-theory
   (e/d (fn-nov-line fn-nntp-append-pieces)
        (fn-nntp-decimal-field fn-nntp-decimal fn-nov-subject fn-nov-from
         fn-nov-date fn-nov-msgid fn-nov-references fn-nov-bytes fn-nov-lines))))))

(local
 (defthm fn-orrf-append-associative
  (equal (append (append a b) c) (append a (append b c)))))

(defthm fn-ovw-reply-current-row-frame-unfolds
 (equal (fn-ovw-reply (cons (fn-nov-line number over) rest) legacyp owedp)
        (append (if owedp (fn-ovw-status (fn-proto-text * :overview)) nil)
                (append (fn-nov-line number over) '(13 10))
                (fn-ovw-reply rest legacyp nil)))
 :rule-classes nil
 :hints (("Goal" :expand ((fn-nntp-stuff-lines (cons (fn-nov-line number over) rest)))
  :in-theory (e/d (fn-ovw-reply fn-wire-stuff-line fn-nntp-crlf)
                 (fn-nntp-stuff-lines fn-nov-line fn-ovw-status)))))
