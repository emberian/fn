; The captured response generation as an immutable cursor token, PRF-1059.
(in-package "ACL2")
(include-book "response-plan-pins")

(defun fn-rpin-token (id owners)
  (declare (xargs :guard t))
  (let ((owner (fn-rpin-owner id owners)))
    (and owner (list :response id (cdr owner)))))

(defun fn-rpin-tokenp (token)
  (declare (xargs :guard t))
  (and (true-listp token) (equal (len token) 3)
       (eq (car token) :response) (natp (cadr token)) (natp (caddr token))))

(local (defthm fn-rpin-token-old-pin-count-natural
  (implies (fn-arpn-pinsp pins) (natp (fn-arpn-pins-of h pins)))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-arpn-pins-of h pins)
                  :in-theory (enable fn-arpn-pins-of fn-arpn-pinsp)))))

; The token is read from the acquired ownership table, never reconstructed
; from a catalog view count. The theorem records the real arena generation.
(defthm fn-rpin-token-after-acquire-is-captured-generation
  (implies (and (fn-arpn-okp st) (natp id)
                (not (fn-rpin-owner id owners)))
           (let ((next (fn-rpin-step owners st (list :acquire id))))
             (and (equal (fn-rpin-token id (mv-nth 0 next))
                         (list :response id (car st)))
                  (fn-rpin-tokenp (fn-rpin-token id (mv-nth 0 next)))
                  (< 0 (fn-arpn-pins-of (car st) (second (mv-nth 1 next)))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-rpin-acquire-holds-the-captured-generation
                            (h (car st))))
           :in-theory (e/d (fn-rpin-token fn-rpin-tokenp fn-arpn-okp)
                           (fn-rpin-step fn-rpin-owner fn-arpn-pins-of
                            fn-rpin-acquire-holds-the-captured-generation)))))

(in-theory (disable fn-rpin-token fn-rpin-tokenp))
