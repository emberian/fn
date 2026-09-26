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
; The translation's R is the article record of (32 768, 65 535) at the
; record overhead of the widths the runtime produces (1 083 fixed octets,
; unchanged by packet P6), above the format-7 H / T of 196 608.
(assert-event (equal (fn-bs-profile-record-ceiling *fn-bs-profile-development*)
                     17138486))
(assert-event (equal (fn-bs-profile-record-ceiling *fn-bs-profile-scale*)
                     17138486))
(assert-event (equal (fn-bs-profile-max-transactions *fn-bs-profile-development*)
                     128))
(assert-event (equal (fn-bs-profile-max-transactions *fn-bs-profile-scale*) 4096))
; The defaults read P2's ceilings: R 64 MiB, A 16 MiB, G 4096, names 256 (the
; D27 figure 460 capped at the label width).  The presets translate format 7
; with the codec ceilings, 65 535 groups of 256 octets.
(assert-event (equal (fn-bs-profile-max-record-octets *fn-bs-profile-defaults*)
                     67108864))
(assert-event (equal (fn-bs-profile-max-article-octets *fn-bs-profile-defaults*)
                     16777216))
(assert-event (equal (fn-bs-profile-max-groups-per-article *fn-bs-profile-defaults*)
                     4096))
(assert-event (equal (fn-bs-profile-max-group-name-octets *fn-bs-profile-defaults*)
                     256))
(assert-event (equal (fn-record-encoded-octets-ceiling 16777216 4096) 17847355))
(assert-event (equal (fn-bs-profile-max-groups-per-article *fn-bs-profile-scale*)
                     65535))
(assert-event (equal (fn-bs-profile-max-group-name-octets *fn-bs-profile-development*)
                     256))

; A free-field profile no preset equals (T = 1000, A = 20000, K = 1000):
; valid, admitted, round-trips through the frame, and gates publication at
; its own T and R.  R is the defaults' 64 MiB: the largest Store event kind's
; ceiling (the accepted statement's) is 196608 and the FNST store payload
; codec ceiling is now the u32 width, so R is free between them.
(assert-event (equal *fn-bs-profile-min-record-octets* 196608))
(assert-event (equal *fn-bs-profile-record-ceiling-codec* 4294967295))
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
(assert-event (fn-bs-publication-admissiblep *bsft-free* 999 67108864))
(assert-event (not (fn-bs-publication-admissiblep *bsft-free* 1000 196608)))
(assert-event (not (fn-bs-publication-admissiblep *bsft-free* 0 67108865)))
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
(bsft-refuses ((4 . 4294967296) (3 . 4294967296)) :max-record-octets-above-codec)
; PKT-467: R above the kind-6 poll reply's report ceiling (the Store frame's
; u32 less the reply's 9 header and 346 cursor octets) is refused by its own
; name, up to and including the codec's u32; at the ceiling R is valid.
(assert-event (equal *fn-stxa-max-octets* 4294966940))
(bsft-refuses ((4 . 4294966941) (3 . 4294966941))
              :max-record-octets-above-the-poll-reply)
(bsft-refuses ((4 . 4294967295) (3 . 4294967295))
              :max-record-octets-above-the-poll-reply)
(defconst *bsft-poll-top*
  (fn-bs-profile-set-fields *bsft-free* '((4 . 4294966940) (3 . 4294966940))))
(assert-event (fn-bs-profile-validp *bsft-poll-top*))
(bsft-refuses ((5 . 0)) :max-article-octets-outside-codec)
(bsft-refuses ((5 . 4261412865)) :max-article-octets-outside-codec)
(bsft-refuses ((6 . 0)) :max-groups-per-article-outside-codec)
(bsft-refuses ((6 . 65536)) :max-groups-per-article-outside-codec)
(bsft-refuses ((7 . 0)) :max-group-name-octets-outside-codec)
(bsft-refuses ((7 . 257)) :max-group-name-octets-outside-codec)
; The article relation: R must hold the worst-case record of an article of A
; octets in G groups, `fn-record-encoded-octets-ceiling' 20000 4096 =
; 1 090 139.  One octet below it is refused by name; at it the profile is
; valid.  A 16 MiB article under 4096 groups needs 17 847 355.
(assert-event (equal (fn-record-encoded-octets-ceiling 20000 4096) 1090139))
(bsft-refuses ((4 . 1090138)) :max-record-octets-below-the-article-record)
(assert-event (fn-bs-profile-validp
               (fn-bs-profile-set-fields *bsft-free* '((4 . 1090139)))))
(bsft-refuses ((4 . 1090139) (5 . 20001)) :max-record-octets-below-the-article-record)
(bsft-refuses ((4 . 1090139) (6 . 4097)) :max-record-octets-below-the-article-record)
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

;  Teeth for fn-bs-profile-valid-record-fits-a-poll-reply (PKT-467).
; Reachable and tight: the profile whose R is the poll reply's report ceiling
; admits a payload of exactly that many octets, which the conclusion bounds.
(assert-event (fn-bs-publication-admissiblep *bsft-poll-top* 0 4294966940))
(assert-event (<= 4294966940 *fn-stxa-max-octets*))
; Every preset and both format-7 translations: R well within the ceiling.
(assert-event (<= (fn-bs-profile-max-record-octets *fn-bs-profile-development*)
                  *fn-stxa-max-octets*))
(assert-event (<= (fn-bs-profile-max-record-octets *fn-bs-profile-scale*)
                  *fn-stxa-max-octets*))
(assert-event (<= (fn-bs-profile-max-record-octets *fn-bs-profile-defaults*)
                  *fn-stxa-max-octets*))
(assert-event (fn-bs-profile-admittedp *fn-bs-meta-format-7-development-values*))
(assert-event (fn-bs-profile-admittedp *fn-bs-meta-format-7-scale-values*))
; The hypothesis: without the gate's admission a payload one octet past the
; ceiling is a counterexample; and the gate refuses it even under the profile
; that asks for R one octet past the ceiling (that profile is not admitted).
(must-fail
 (thm (implies (equal octets 4294966941) (<= octets *fn-stxa-max-octets*))))
(assert-event
 (not (fn-bs-publication-admissiblep
       (fn-bs-profile-set-fields *bsft-free* '((4 . 4294966941) (3 . 4294966941)))
       0 4294966941)))

;  Teeth for fn-bs-profile-admits-every-article-record.  Non-degenerate: the
; free profile's R is exactly the article record of its (A, G), so the bound
; is tight at the witness.  Each hypothesis dropped admits a concrete
; counterexample, below.
(defconst *bsft-tight* (fn-bs-profile-set-fields *bsft-free* '((4 . 1090139))))
(assert-event (fn-bs-profile-admittedp *bsft-tight*))
(assert-event (equal (fn-bs-profile-max-record-octets *bsft-tight*)
                     (fn-record-encoded-octets-ceiling
                      (fn-bs-profile-max-article-octets *bsft-tight*)
                      (fn-bs-profile-max-groups-per-article *bsft-tight*))))
;  Concrete counterexamples for the two bound hypotheses, under a profile
; whose R is exactly the article record of (A, G) = (195 264, 1): a record one
; octet past R (so past A) in one group, and a record at A in six 256-octet groups, each
; encode past R.  A record at A in one 256-octet group is within R.
(defconst *bsft-g1* (fn-bs-profile-set-fields *bsft-free*
                                              '((4 . 196608) (5 . 195264) (6 . 1))))
(assert-event (fn-bs-profile-admittedp *bsft-g1*))
(defun bsft-name (c) (coerce (make-list 256 :initial-element c) 'string))
(defun bsft-record (payload-octets groups)
  (fn-record-make 1 2 3 "<bsft@example.invalid>"
                  (make-list payload-octets :initial-element 65)
                  groups "archive-a" "content-a" "release-a" 4 841000000))
(assert-event
 (let ((r (bsft-record 195264 (list (bsft-name #\a)))))
   (and (fn-record-p r)
        (< 195264 (len (fn-record-encode r)))
        (<= (len (fn-record-encode r)) 196608))))
(assert-event
 (let ((r (bsft-record 196609 (list "g"))))
   (and (fn-record-p r)
        (< 195264 (len (fn-record-payload r)))
        (<= (len (fn-record-groups r)) 1)
        (< 196608 (len (fn-record-encode r))))))
(assert-event
 (let ((r (bsft-record 195264 (list (bsft-name #\a) (bsft-name #\b)
                                    (bsft-name #\c) (bsft-name #\d)
                                    (bsft-name #\e) (bsft-name #\f)))))
   (and (fn-record-p r)
        (<= (len (fn-record-payload r)) 195264)
        (< 196608 (len (fn-record-encode r))))))
;  The admitted hypothesis: a value that is not a profile reads every field
; as 0, and a record with no payload and no groups (within both 0 bounds)
; still encodes to 70 octets, past R = 0.
(assert-event
 (let ((r (bsft-record 0 nil)))
   (and (not (fn-bs-profile-admittedp '(1 2 3)))
        (equal (len (fn-record-payload r)) 0)
        (equal (len (fn-record-groups r)) 0)
        (< (fn-bs-profile-max-record-octets '(1 2 3))
           (len (fn-record-encode r))))))

;  The width hypothesis (packet P6).  Under *bsft-g1* (R the article record
; of (195 264, 1) at the 1 083-octet overhead), a record at A in one 256-octet
; group with a 250-octet Message-ID and 256-octet metadata strings encodes
; within R while its integer fields fit u32 (196 589 octets), and one octet
; past R (196 609) when the same five fields are 2^32: the wide heads add 4
; octets each.  So the conclusion fails without the hypothesis, at a record
; that meets every other one.
(defun bsft-full-record (n)
  (fn-record-make n n n (coerce (make-list 250 :initial-element #\m) 'string)
                  (make-list 195264 :initial-element 65)
                  (list (bsft-name #\a))
                  (bsft-name #\o) (bsft-name #\s) (bsft-name #\e) n n))
(assert-event
 (let ((r (bsft-full-record 4294967295)))
   (and (fn-record-p r)
        (not (fn-record-widep r))
        (equal (len (fn-record-encode r)) 196589)
        (<= (len (fn-record-encode r))
            (fn-bs-profile-max-record-octets *bsft-g1*)))))
(assert-event
 (let ((r (bsft-full-record 4294967296)))
   (and (fn-record-p r)
        (fn-record-widep r)
        (<= (len (fn-record-payload r))
            (fn-bs-profile-max-article-octets *bsft-g1*))
        (<= (len (fn-record-groups r))
            (fn-bs-profile-max-groups-per-article *bsft-g1*))
        (equal (len (fn-record-encode r)) 196609)
        (< (fn-bs-profile-max-record-octets *bsft-g1*)
           (len (fn-record-encode r))))))

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
                      *fn-bs-meta-format-7-development-values*) 17138486))
(assert-event (equal (cdr (assoc-equal "format" (fn-bs-profile-report
                                                 *fn-bs-meta-format-7-scale-values*)))
                     7))
(assert-event (equal (fn-bs-profile-report *bsft-free*)
                     (cons '("format" . 8)
                           (append
                            (pairlis$ (strip-cdrs (butlast *fn-bs-profile-field-names* 1))
                                      (butlast (nthcdr 2 *bsft-free*) 1))
                            '(("history-marker" . "unmarked"))))))
; D31: the history requirement reads as its word.
(assert-event (equal (cdr (assoc-equal "history-marker"
                                       (fn-bs-profile-report
                                        (fn-bs-profile-put 14 1 *bsft-free*))))
                     "required"))
(assert-event (equal (cdr (assoc-equal "history-marker"
                                       (fn-bs-profile-report
                                        *fn-bs-meta-format-7-scale-values*)))
                     "unmarked"))
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

; ---------------------------------------------------------------------------
; PRF-126: frontier format 3.  The frame carries u64; a format-2 frame reads
; to the same value; the allocator's successor still stops at 2^32 - 1.
; KEYSTONE fn-bs-frontier-impl-round-trip, positive witnesses on both sides
; of 2^32 and at 2^64 - 1; the separating witness: the frame for 2^32 has a
; nine-octet payload, which the format-2 reader refuses and format 3 reads.
(defmacro bsft-f2-top () '(fn-bs-frontier-encode-impl 4294967295))
(defmacro bsft-f3-first () '(fn-bs-frontier-encode-impl 4294967296))
(defmacro bsft-f3-top () '(fn-bs-frontier-encode-impl 18446744073709551615))
(assert-event (equal (fn-bs-frontier-decode-impl (bsft-f2-top)) 4294967295))
(assert-event (equal (fn-bs-frontier-v2-decode (bsft-f2-top)) 4294967295))
(assert-event (equal (fn-bs-frontier-decode-impl (bsft-f3-first)) 4294967296))
(assert-event (null (fn-bs-frontier-v2-decode (bsft-f3-first))))
(assert-event (equal (fn-bs-frontier-decode-impl (bsft-f3-top))
                     18446744073709551615))
(assert-event (equal (- (len (bsft-f3-first)) (len (bsft-f2-top))) 4))
; The round trip's width hypothesis: 2^64 has no frame, so without it the
; conclusion fails.
(assert-event (null (fn-bs-frontier-encode-impl 18446744073709551616)))
(assert-event (not (equal (fn-bs-frontier-decode-impl
                           (fn-bs-frontier-encode-impl 18446744073709551616))
                          18446744073709551616)))
(must-fail
 (defthm bsft-round-trip-without-the-width
   (implies (natp n)
            (equal (fn-bs-frontier-decode-impl (fn-bs-frontier-encode-impl n))
                   n))
   :hints (("Goal" :do-not-induct t
            :in-theory (theory 'minimal-theory)))))
; A nine-octet head holding a value below 2^32 is not canonical (RFC 8949
; §4.2.1) and no reader accepts it.
(defmacro bsft-noncanonical ()
  '(fn-frame-seal *fn-bs-meta-magic* *fn-bs-meta-version*
                  *fn-bs-meta-frontier-kind* '(27 0 0 0 0 0 0 0 5)))
(assert-event (null (fn-bs-frontier-decode-impl (bsft-noncanonical))))
(assert-event (null (fn-bs-frontier-v2-decode (bsft-noncanonical))))
; KEYSTONE fn-bs-frontier-decode-extends-format-2: every format-2 frame the
; old reader accepts (0, 2, 2^32 - 1 here, and the frame init writes) reads
; the same under format 3.  Its hypothesis: at the format-3 frame for 2^32 the
; old reader answers NIL and the new one 2^32, so the conclusion fails
; without it.
(assert-event (equal (fn-bs-frontier-decode-impl (fn-bs-initial-frontier-octets))
                     (fn-bs-frontier-v2-decode (fn-bs-initial-frontier-octets))))
(assert-event (equal (fn-bs-frontier-decode-impl (fn-bs-frontier-encode-impl 2))
                     (fn-bs-frontier-v2-decode (fn-bs-frontier-encode-impl 2))))
(assert-event (not (equal (fn-bs-frontier-decode-impl (bsft-f3-first))
                          (fn-bs-frontier-v2-decode (bsft-f3-first)))))
(must-fail
 (defthm bsft-extends-without-the-format-2-hypothesis
   (equal (fn-bs-frontier-decode-impl octets)
          (fn-bs-frontier-v2-decode octets))
   :hints (("Goal" :do-not-induct t
            :in-theory (theory 'minimal-theory)))))
; The allocator ceiling is unchanged: no successor at 2^32 - 1 (PKT-244).
(assert-event (null (fn-bs-frontier-next 4294967295)))
