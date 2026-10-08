; Domain counterexample to statement 4's unconditional ART take equality.
; This is a synthetic total-function input, not a served reachability claim.
(in-package "ACL2")
(include-book "../../books/owner-parse-carried")
(include-book "../../books/article-art")
(include-book "must-fail-checked")

(defconst *patd-sub*
  (fn-own-sub-make 1 0 nil
   (fn-inj-make-decision :injected nil '(60 120 64 121 62) nil 7) nil))

(assert-event
 (and (fn-own-sub-shapep *patd-sub*)
      (fn-inj-injectedp (fn-own-sub-decision *patd-sub*))
      (equal (fn-own-sub-octets *patd-sub*) 7)
      (equal (car (fn-apc-take nil *patd-sub* nil)) 7)
      (fn-apc-p (cdr (fn-apc-take nil *patd-sub* nil)))))

(local
 (defthm patd-unpack-is-list
   (true-listp (fn-bch-unpack n))
   :hints (("Goal" :in-theory (enable fn-bch-unpack)))))

; No possible result R of a new take can abstract to the reference's 7.
(defthm patd-art-abstraction-is-list
  (true-listp (fn-art-octets r))
  :hints (("Goal" :in-theory (e/d (fn-art-octets) (fn-bch-unpack)))))
(defthm patd-no-art-can-match-this-take
  (not (equal (fn-art-octets r) (car (fn-apc-take nil *patd-sub* nil))))
  :hints (("Goal" :in-theory (disable fn-art-octets fn-apc-take)
           :use ((:instance patd-art-abstraction-is-list)))))

(must-fail-checked
 (assert-event (true-listp (car (fn-apc-take nil *patd-sub* nil)))))
