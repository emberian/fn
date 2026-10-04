; P12 named resource refusal (PRF-1073): refusal before allocating a cold
; dependency is not a deadline observation. RFC 3977 section 3.2.1 code 403.
(in-package "ACL2")
(include-book "owner-cold-line")

(defun fn-orln-refusalp (word)
  (declare (xargs :guard t))
  (and (member-equal word '(:read-resources-unavailable :read-identities-exhausted)) t))

(defun fn-orln-unavailable-line (word)
  (declare (xargs :guard t))
  (append (fn-osch-text
           (if (equal word :read-identities-exhausted)
               "403 article temporarily unavailable; cold read identities exhausted; try after restart"
             "403 article temporarily unavailable; cold read resources unavailable; try again later"))
          '(13 10)))

(defun fn-orln-unavailable-result (oc id i end word)
  (declare (xargs :guard t))
  (fn-own-tls-make-result (nfix (- (nfix end) (nfix i)))
                         (list (fn-nntp-reply-effect (fn-orln-unavailable-line word)))
                         (fn-ocln-owner-at-line oc id) nil))

(defun fn-orln-unavailable-span (oc id i word fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (<= i (fn-octets-len fn-octets)))))
  (if (and (fn-orln-refusalp word) (fn-ocln-commandp oc id))
      (fn-orln-unavailable-result oc id i (fn-oct-line-end i fn-octets) word)
    nil))

(local
 (defthm fn-orln-line-end-progress
   (implies (and (natp i) (< i (fn-octets-len fn-octets)))
            (< i (fn-oct-line-end i fn-octets)))
   :hints (("Goal" :in-theory (enable fn-oct-line-end)))
   :rule-classes :linear))

(defthm fn-orln-a-refused-cold-line-is-answered-unavailable
  (implies (and (natp i) (<= i (fn-octets-len fn-octets))
                (fn-orln-refusalp word) (fn-ocln-commandp oc id))
           (let ((r (fn-orln-unavailable-span oc id i word fn-octets)))
             (and (equal (fn-own-tls-result-consumed r)
                         (- (fn-oct-line-end i fn-octets) i))
                  (implies (< i (fn-octets-len fn-octets))
                           (< 0 (fn-own-tls-result-consumed r)))
                  (equal (fn-own-tls-result-effects r)
                         (list (list :reply (fn-orln-unavailable-line word))))
                  (equal (take 3 (fn-orln-unavailable-line word)) '(52 48 51))
                  (equal (fn-own-tls-result-owner r) (fn-ocln-owner-at-line oc id)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-orln-unavailable-span
                                    fn-orln-unavailable-result fn-orln-refusalp
                                    fn-orln-unavailable-line fn-osch-text
                                    fn-own-tls-make-result fn-own-tls-result-consumed
                                    fn-own-tls-result-effects fn-own-tls-result-owner
                                    fn-nntp-reply-effect fn-oct-line-end))))

(defthm fn-orln-not-refused-or-not-command-by-definition
  (implies (or (not (fn-orln-refusalp word)) (not (fn-ocln-commandp oc id)))
           (equal (fn-orln-unavailable-span oc id i word fn-octets) nil)))

(in-theory (disable fn-orln-refusalp fn-orln-unavailable-line
                    fn-orln-unavailable-result fn-orln-unavailable-span))

; The 403 that answers a retrieval whose payload read did not come
; (books/article-stream-owner.lisp fn-asto-plan-unavailable): past its
; dependency deadline it is time-bars' line (fn-otb-unavailable-line, C3);
; refused by name before allocation it is this book's line (P12).  NIL for
; any other word: the host has no reply to give in its place.
(defun fn-orln-preflight-line (word since now limit)
  (declare (xargs :guard t))
  (cond ((equal word :unavailable) (fn-otb-unavailable-line since now limit))
        ((fn-orln-refusalp word) (fn-orln-unavailable-line word))
        (t nil)))

; KEYSTONE.  Every line it gives begins with the 403 code, and it gives one
; exactly for the deadline and the two named refusals.
(defthm fn-orln-preflight-line-is-a-403
  (let ((line (fn-orln-preflight-line word since now limit)))
    (and (iff line (or (equal word :unavailable) (fn-orln-refusalp word)))
         (implies line (equal (take 3 line) '(52 48 51)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-orln-preflight-line fn-orln-unavailable-line
                                     fn-otb-unavailable-line fn-osch-text fn-orln-refusalp))))

(in-theory (disable fn-orln-preflight-line))
