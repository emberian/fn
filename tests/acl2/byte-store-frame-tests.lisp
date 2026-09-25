; Reachable witnesses and corruption teeth for P4 metadata frames.
(in-package "ACL2")
(include-book "../../books/byte-store-frame")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

;  The development profile and zero frontier are the actual bytes init writes
; for `--profile development' (the developer initializer's default).
(assert-event (fn-bs-config-okp (fn-bs-initial-config-octets)))
(assert-event (equal (fn-bs-config-decode (fn-bs-initial-config-octets))
                     *fn-bs-profile-development*))
(assert-event (equal (fn-bs-frontier-decode (fn-bs-initial-frontier-octets)) 0))
(assert-event (equal (fn-bs-frontier-decode
                      (fn-bs-frontier-encode 4294967295))
                     4294967295))
(assert-event (equal (fn-bs-frontier-next 4294967294) 4294967295))
(assert-event (not (fn-bs-frontier-next 4294967295)))

; -----------------------------------------------------------------------------
; Format 8: the operator's fields, validated by relations

; The presets are the format-7 tuples' translations, and valid; the defaults
; are valid and are neither preset.
(assert-event (fn-bs-profile-validp *fn-bs-profile-development*))
(assert-event (fn-bs-profile-validp *fn-bs-profile-scale*))
(assert-event (fn-bs-profile-validp *fn-bs-profile-defaults*))
(assert-event (equal (fn-bs-profile-max-transactions *fn-bs-profile-defaults*)
                     4294967295))
(assert-event (equal (fn-bs-profile-max-history-octets *fn-bs-profile-defaults*)
                     1099511627776))
(assert-event (equal (fn-bs-profile-max-open-suffix *fn-bs-profile-defaults*)
                     65536))
(assert-event (equal (fn-bs-profile-record-ceiling *fn-bs-profile-development*)
                     196608))
(assert-event (equal (fn-bs-profile-max-transactions *fn-bs-profile-development*)
                     128))
(assert-event (equal (fn-bs-profile-max-transactions *fn-bs-profile-scale*) 4096))

; A free-field profile no preset equals (T = 1000, A = 20000, K = 1000):
; valid, admitted, round-trips through the frame, and gates publication at
; its own T and R.  R stays 196608: on this tree the largest Store event
; kind's ceiling (the accepted statement's) equals the FNST store payload
; codec ceiling, so R has exactly one valid value until P2 raises the codec.
(assert-event (equal *fn-bs-profile-min-record-octets* 196608))
(assert-event (equal *fn-bs-profile-record-ceiling-codec* 196608))
(defconst *bsft-free*
  (fn-bs-profile-set-fields *fn-bs-profile-defaults*
                            '((2 . 1000) (5 . 20000) (8 . 1000))))
(assert-event (fn-bs-profile-validp *bsft-free*))
(assert-event (not (member-equal *bsft-free*
                                 (list *fn-bs-profile-development*
                                       *fn-bs-profile-scale*
                                       *fn-bs-profile-defaults*))))
(assert-event (equal (fn-bs-config-decode (fn-bs-config-encode *bsft-free*))
                     *bsft-free*))
(assert-event (fn-bs-publication-admissiblep *bsft-free* 999 196608))
(assert-event (not (fn-bs-publication-admissiblep *bsft-free* 1000 196608)))
(assert-event (not (fn-bs-publication-admissiblep *bsft-free* 0 196609)))
(assert-event (fn-bs-history-admissiblep
               *bsft-free* (- (fn-bs-profile-max-history-octets *bsft-free*) 10) 10))
(assert-event (not (fn-bs-history-admissiblep
                    *bsft-free* (- (fn-bs-profile-max-history-octets *bsft-free*) 10) 11)))
(assert-event (equal (fn-bs-profile-resolve '(:default ((2 . 1000) (5 . 20000)
                                                       (8 . 1000)))
                                            nil)
                     *bsft-free*))
; K follows a lowered T when the operator does not name K.
(assert-event (equal (fn-bs-profile-resolve '(:default ((2 . 1000) (5 . 20000)))
                                            nil)
                     *bsft-free*))

; One refusal per validity relation: each profile below breaks exactly one,
; and is refused by that relation's name.
(defmacro bsft-refuses (overrides reason)
  `(assert-event
    (and (equal (fn-bs-profile-invalid-reason
                 (fn-bs-profile-set-fields *bsft-free* ',overrides))
                ,reason)
         (not (fn-bs-profile-validp
               (fn-bs-profile-set-fields *bsft-free* ',overrides))))))
(bsft-refuses ((2 . 0)) :max-transactions-outside-txid-width)
(bsft-refuses ((2 . 4294967296) (8 . 1000)) :max-transactions-outside-txid-width)
(bsft-refuses ((3 . 196607)) :max-history-octets-below-max-record-octets)
(bsft-refuses ((4 . 100) (3 . 100)) :max-record-octets-below-an-event-kind)
(bsft-refuses ((4 . 196609)) :max-record-octets-above-codec)
(bsft-refuses ((5 . 0)) :max-article-octets-outside-codec)
(bsft-refuses ((5 . 32769)) :max-article-octets-outside-codec)
(bsft-refuses ((6 . 0)) :max-groups-per-article-outside-codec)
(bsft-refuses ((6 . 17)) :max-groups-per-article-outside-codec)
(bsft-refuses ((7 . 0)) :max-group-name-octets-outside-codec)
(bsft-refuses ((7 . 129)) :max-group-name-octets-outside-codec)
(bsft-refuses ((8 . 0)) :max-open-suffix-outside-transactions)
(bsft-refuses ((8 . 1001)) :max-open-suffix-outside-transactions)
(bsft-refuses ((9 . 0)) :namespace-count-outside-width)
(bsft-refuses ((13 . 4294967296)) :namespace-count-outside-width)
(assert-event (equal (fn-bs-profile-invalid-reason
                      (fn-bs-profile-put 0 *fn-bs-meta-format-development* *bsft-free*))
                     :format))
(assert-event (equal (fn-bs-profile-invalid-reason (butlast *bsft-free* 1))
                     :layout))
; A profile whose R is below kind 4's (the article record's) ceiling is refused.
(assert-event (< 100 (fn-store-publication-ceiling :article)))
(assert-event (equal (fn-bs-profile-init-verdict '(:default ((4 . 100) (3 . 100))))
                     '(:refused :max-record-octets-below-an-event-kind)))

;  Teeth for fn-bs-profile-validp-codecs-accept: its guarded half needs the
; profile to be admitted.  A value that is not a profile reads as zero, so
; without the hypothesis each guarded conclusion has a counterexample.
(assert-event (not (fn-bs-profile-admittedp '(1 2 3))))
(assert-event (not (<= 1 (fn-bs-profile-max-transactions '(1 2 3)))))
(assert-event (not (<= (fn-store-publication-ceiling :article)
                       (fn-bs-profile-max-record-octets '(1 2 3)))))
(assert-event (not (<= 1 (fn-bs-profile-max-article-octets '(1 2 3)))))
(assert-event (not (<= 1 (fn-bs-profile-max-groups-per-article '(1 2 3)))))

; -----------------------------------------------------------------------------
; Format 7 is still decoded and served under its translation; format 6 is not

(defun bsft-format-7-frame (values)
  (fn-frame-seal *fn-bs-meta-magic* *fn-bs-meta-version*
                 *fn-bs-meta-config-kind*
                 (fn-frame-fields-octets *fn-bs-meta-format-7-spec* values)))
(assert-event (equal (fn-bs-config-decode
                      (bsft-format-7-frame *fn-bs-meta-format-7-scale-values*))
                     *fn-bs-meta-format-7-scale-values*))
(assert-event (fn-bs-profile-admittedp *fn-bs-meta-format-7-scale-values*))
(assert-event (equal (fn-bs-profile-of *fn-bs-meta-format-7-scale-values*)
                     *fn-bs-profile-scale*))
(assert-event (equal (fn-bs-profile-max-transactions
                      *fn-bs-meta-format-7-scale-values*) 4096))
(assert-event (equal (fn-bs-profile-record-ceiling
                      *fn-bs-meta-format-7-development-values*) 196608))
(assert-event (equal (cdr (assoc-equal "format" (fn-bs-profile-report
                                                 *fn-bs-meta-format-7-scale-values*)))
                     7))
(assert-event (equal (fn-bs-profile-report *bsft-free*)
                     (cons '("format" . 8)
                           (pairlis$ (strip-cdrs *fn-bs-profile-field-names*)
                                     (nthcdr 2 *bsft-free*)))))
; A format-6 tuple (65538-octet records, below the article kind's ceiling) is
; neither a format-7 tuple nor decoded.
(defconst *bsft-format-6*
  (list '(102 110 45 115 116 111 114 101 45 101 120 112 101 114 105 109
          101 110 116 45 54)
        1048576 32768 8388864 128 *fn-bs-meta-frontier-format*))
(assert-event (not (fn-bs-config-decode (bsft-format-7-frame *bsft-format-6*))))
(assert-event (not (fn-bs-profile-admittedp *bsft-format-6*)))
(assert-event (not (fn-bs-publication-admissiblep *bsft-format-6* 0 1)))

; A truncated authentic frame must not become a frontier.  The visible value
; is not merely a wrong integer: decoding reports no value at all.
(assert-event
 (let ((cut (take (1- (len (fn-bs-initial-frontier-octets)))
                  (fn-bs-initial-frontier-octets))))
   (and (not (fn-bs-frontier-decode cut))
        (not (fn-bs-config-okp cut)))))

; A frame with a valid trailer but the wrong metadata kind is also rejected.
(assert-event
 (let ((wrong (fn-frame-seal *fn-bs-meta-magic* *fn-bs-meta-version*
                             *fn-bs-meta-config-kind*
                             (fn-cbor-encode (cons :uint 0)))))
   (not (fn-bs-frontier-decode wrong))))
