; The historical HDR extension emits a typed NNTP reply.  This book sits
; above nntp-effects so the response leaf can remain below nntp dispatch.
(in-package "ACL2")
(include-book "nntp-effects")
(include-book "nntp-verdict")

(defthm fn-stx-printable-is-nntp-clean-field
  (implies (fn-stx-printablep bytes)
           (fn-nov-clean-fieldp bytes))
  :hints (("Goal" :induct (fn-stx-printablep bytes)
           :in-theory (enable fn-stx-printablep fn-nov-clean-fieldp
                              fn-nov-field-octetp))))

(defthm fn-nntp-verdict-line-is-block-text
  (implies (fn-nov-clean-fieldp label)
           (fn-nntp-block-textp
            (list (fn-nntp-hdr-line label (fn-stx-reader-item verdict)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-nntp-hdr-line-is-a-clean-field
                            (content (fn-stx-reader-item verdict)))
                 (:instance fn-nntp-clean-field-is-response-text
                            (bytes (fn-nntp-hdr-line
                                    label (fn-stx-reader-item verdict)))))
           :in-theory (e/d (fn-nntp-block-textp)
                           (fn-nntp-hdr-line fn-stx-reader-item)))))

(defthm fn-nntp-verdict-lookup-line-is-response-text
  (implies (fn-nov-clean-fieldp label)
           (fn-nntp-response-textp
            (fn-nntp-hdr-line label
                              (fn-stx-reader-verdict msgid verdicts))))
  :hints (("Goal" :use ((:instance fn-nntp-verdict-line-is-block-text
                            (verdict (fn-stx-reader-lookup msgid verdicts))))
           :in-theory (e/d (fn-nntp-block-textp fn-stx-reader-verdict)
                           (fn-nntp-hdr-line fn-stx-reader-item)))))

(defthm fn-nntp-verdict-hdr-lines-are-block-text
  (fn-nntp-block-textp
   (fn-nntp-verdict-hdr-lines group numbers articles verdicts))
  :hints (("Goal" :induct (fn-nntp-verdict-hdr-lines
                            group numbers articles verdicts)
           :in-theory (e/d (fn-nntp-verdict-hdr-lines
                            fn-nntp-block-textp
                            fn-nov-decimal-field-is-clean)
                           (fn-nntp-hdr-line fn-stx-reader-verdict
                            fn-stx-reader-item
                            fn-stx-reader-verdict-is-the-recorded-verdict
                            fn-nntp-available-article)))))

(defthm fn-nntp-verdict-hdr-response-effects
  (fn-nntp-effectsp
   (fn-nntp-result-effects
    (fn-nntp-verdict-hdr-response session archive verdicts args)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-verdict-hdr-response
                                    fn-nntp-verdict-hdr-current
                                    fn-nntp-verdict-hdr-range
                                    fn-nntp-verdict-hdr-msgid
                                    fn-nov-decimal-field-is-clean)
                                   (fn-nntp-single fn-nntp-multi
                                    fn-nntp-verdict-hdr-lines
                                    fn-stx-reader-verdict
                                    fn-stx-reader-item
                                    fn-stx-reader-verdict-is-the-recorded-verdict
                                    fn-nntp-available-article)))))

;; SPIKE: defers the proof of the :fn-control arm's effect shape (proof owner
;; books/nntp-verdict-effects.lisp; the :fn-verified arm above is the model).
(skip-proofs
 (defthm fn-nntp-control-hdr-response-effects
   (fn-nntp-effectsp
    (fn-nntp-result-effects
     (fn-nntp-control-hdr-response session archive verdicts args)))))
