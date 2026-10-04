; fn: the wire line of an output-admission refusal (lane tariff2, 2026-10-04;
; planning/design/tariff-2026-10-04.md Q5, ruled by the root 10-04).
;
; In accounted mode (an operator configured [resources] output_heap_octets)
; every first command passes fn-ocap-admit-preview before any factory.  Its
; two client-visible refusals are answered here, over the refused command's
; line, before any factory runs:
;
;   :unpriced-output-family F   -> 403, the connection kept.  An unpriced
;                                  family is the server's gap, not the
;                                  client's load (RFC 3977 3.2.1.1).
;   :output-tariff-unaffordable -> 400 and close: the reply's price exceeds
;                                  the configured output quantum.
;
; Any other admission word (:invalid-output-preview) is the host's defect and
; is not answered here (nil): the host faults.

(in-package "ACL2")
(include-book "owner-resource-line")
(include-book "output-command-admission")

(defun fn-oadl-wordp (admission)
  (declare (xargs :guard t))
  (and (equal (fn-ocap-at 0 admission) :refused)
       (or (equal (fn-ocap-at 1 admission) :unpriced-output-family)
           (equal (fn-ocap-at 1 admission) :output-tariff-unaffordable))))

(defun fn-oadl-line (admission)
  (declare (xargs :guard t))
  (append (fn-osch-text
           (if (eq (fn-ocap-at 1 admission) :output-tariff-unaffordable)
               "400 reply exceeds this server's output quantum; closing"
             "403 command unavailable; its output is not priced on this server"))
          '(13 10)))

(defun fn-oadl-effects (admission)
  (declare (xargs :guard t))
  (if (eq (fn-ocap-at 1 admission) :output-tariff-unaffordable)
      (list (fn-nntp-reply-effect (fn-oadl-line admission)) (fn-nntp-close-effect))
    (list (fn-nntp-reply-effect (fn-oadl-line admission)))))

; The service-log line of a refusal answered on the wire: loud, since an
; unpriced family is the server's gap.  ACL2 renders it; the host writes it.
(defun fn-oadl-log-line (admission cid)
  (declare (xargs :guard t))
  (append (fn-osch-text (if (eq (fn-ocap-at 1 admission) :output-tariff-unaffordable)
                            "output admission: reply over quantum, refused 400, connection "
                          "output admission: family unpriced, refused 403, connection "))
          (fn-osch-decimal cid)
          (fn-osch-text " family ")
          (let ((f (fn-ocap-at 2 admission)))
            (if (symbolp f) (fn-osch-text (symbol-name f)) (fn-osch-text "?")))))

; Over [I, line end): the refusal's effects, the line consumed, the owner OC
; at the line (the same owner step as the cold-read refusal,
; books/owner-resource-line.lisp).
(defun fn-oadl-refusal-span (oc id i admission fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (<= i (fn-octets-len fn-octets)))))
  (if (and (fn-oadl-wordp admission) (fn-ocln-commandp oc id))
      (fn-own-tls-make-result (nfix (- (nfix (fn-oct-line-end i fn-octets)) (nfix i)))
                              (fn-oadl-effects admission)
                              (fn-ocln-owner-at-line oc id) nil)
    nil))

; KEYSTONE.  An unpriced family is answered 403 over exactly its line and
; the connection is kept; an unaffordable one is answered 400 and closed; no
; other word is answered.
(defthm fn-oadl-refusal-is-one-line
  (implies (and (natp i) (<= i (fn-octets-len fn-octets))
                (fn-oadl-wordp admission) (fn-ocln-commandp oc id))
           (let ((r (fn-oadl-refusal-span oc id i admission fn-octets)))
             (and (equal (fn-own-tls-result-consumed r)
                         (- (fn-oct-line-end i fn-octets) i))
                  (equal (fn-own-tls-result-owner r) (fn-ocln-owner-at-line oc id))
                  (if (equal (fn-ocap-at 1 admission) :unpriced-output-family)
                      (and (equal (take 3 (fn-oadl-line admission)) '(52 48 51))
                           (not (fn-served-closingp (fn-own-tls-result-effects r))))
                    (and (equal (take 3 (fn-oadl-line admission)) '(52 48 48))
                         (fn-served-closingp (fn-own-tls-result-effects r)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-oadl-refusal-span fn-oadl-wordp fn-oadl-effects
                                     fn-oadl-line fn-osch-text fn-served-closingp
                                     fn-own-tls-make-result fn-own-tls-result-consumed
                                     fn-own-tls-result-effects fn-own-tls-result-owner
                                     fn-nntp-reply-effect fn-nntp-close-effect fn-oct-line-end))))

(defthm fn-oadl-other-words-are-not-answered
  (implies (not (fn-oadl-wordp admission))
           (equal (fn-oadl-refusal-span oc id i admission fn-octets) nil)))

(in-theory (disable fn-oadl-wordp fn-oadl-line fn-oadl-effects fn-oadl-refusal-span))
