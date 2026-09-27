; Teeth for books/bp-request-reference.lisp (PKT-646, PRF-244).
(in-package "ACL2")
(include-book "../../books/bp-request-reference")
(include-book "bp-native-app-tests")

; R is the native-app tests' request; R2 has R's metadata and another
; article; BIG has a 100,000-octet article.
(defconst *bprf-r* *bpaj-request*)
(defconst *bprf-r-octets* *bpaj-request-octets*)
(make-event `(defconst *bprf-ref* ',(fn-bpaj-request-ref *bprf-r*)))
(defconst *bprf-r2*
  (fn-bpa-make-request
   "work-native" (fn-record-content-subject *bpr-record*)
   "dtn://sender.lab" "dtn://fn.lab/inbox" "receiver-policy"
   "sender-inc-native" "wire-auth-context" "terms-1"
   (append *bpr-adu* '(32 32))))
(defconst *bprf-r2-octets* (fn-bpa-encode *bprf-r2*))
(defconst *bprf-big*
  (fn-bpa-make-request
   "work-big" "subject-big" "dtn://sender.lab" "dtn://fn.lab/inbox"
   "receiver-policy" "sender-inc-native" "wire-auth-context" "terms-1"
   (make-list 100000 :initial-element 65)))
(defconst *bprf-big-octets* (fn-bpa-encode *bprf-big*))
(defconst *bprf-ctx* *bpaj-context*)
(make-event `(defconst *bprf-ctx2* ',(fn-bpaj-context-v2-record "bundle-original" *bprf-r2-octets*
                             (fn-record-encode-impl *bpr-record*) 7
                             (fn-record-txid *bpr-record*)
                             (fn-record-generation *bpr-record*) :duplicate)))

(assert-event (and (fn-bpa-requestp *bprf-r*) (fn-bpa-requestp *bprf-r2*)
                   (fn-bpa-requestp *bprf-big*)
                   (equal (fn-bpaj-request *bprf-r2-octets*) *bprf-r2*)
                   (equal (fn-bpaj-request *bprf-big-octets*) *bprf-big*)
                   *bprf-ctx* *bprf-ctx2*))

; ---------------------------------------------------------------------------
; The records carry the reference, not the bytes: the 100,000-octet
; article's intent holds a HEAD under 2,200 octets, its LENGTH and DIGEST,
; and no article.
(make-event `(defconst *bprf-big-intent* ',(fn-bpaj-intent-record "bundle-big" *bprf-big-octets* 1 2 :accepted)))
(assert-event
 (and (fn-bpaj-intentp *bprf-big-intent*)
      (equal (len *bprf-big-intent*) 8)
      (< (len (fn-bpaj-nth 2 *bprf-big-intent*)) 2200)
      (equal (fn-bpaj-nth 6 *bprf-big-intent*) 100000)
      (equal (fn-bpaj-nth 7 *bprf-big-intent*)
             (fn-frame-digest (fn-bpa-request-article *bprf-big*)))
      (not (member-equal (fn-bpa-request-article *bprf-big*)
                         *bprf-big-intent*))
      (< (len *bprf-big-octets*) (+ 100000 2200))))
; The FNRJ codec encodes it (its wire values: the text field as octets) in
; under 4,096 octets.
(assert-event
 (let ((payload (fn-frame-fields-octets
                 (fn-frame-spec-for :request-intent *fn-frame-receipt-specs*)
                 (cons (fn-record-string-octets
                        (fn-bpaj-nth 1 *bprf-big-intent*))
                       (cddr *bprf-big-intent*)))))
   (< (len payload) 4096)))

; ---------------------------------------------------------------------------
; KEYSTONE fn-bpaj-ref-request-resolves-exactly.
; Positive: R's reference over R's article is R.
(assert-event
 (equal (fn-bpaj-ref-request (car *bprf-ref*) (cadr *bprf-ref*)
                             (caddr *bprf-ref*)
                             (fn-bpa-request-article *bprf-r*))
        *bprf-r*))
; Without (fn-bpa-requestp request): an eleven-element list whose accessors
; are R's; the resolution is R, not it.
(defconst *bprf-not-request* (append *bprf-r* '(:extra)))
(assert-event (not (fn-bpa-requestp *bprf-not-request*)))
(assert-event
 (let ((ref (fn-bpaj-request-ref *bprf-not-request*)))
   (not (equal (fn-bpaj-ref-request (car ref) (cadr ref) (caddr ref)
                                    (fn-bpa-request-article
                                     *bprf-not-request*))
               *bprf-not-request*))))
; KEYSTONE fn-bpaj-ref-request-resolves-to-the-bytes.
(assert-event
 (equal (fn-bpa-encode
         (fn-bpaj-ref-request (car *bprf-ref*) (cadr *bprf-ref*)
                              (caddr *bprf-ref*)
                              (fn-bpa-request-article *bprf-r*)))
        *bprf-r-octets*))
; Without (fn-bpaj-request octets): R's octets and one trailing octet decode
; to nothing, and nothing resolves to them.
(defconst *bprf-trailing* (append *bprf-r-octets* '(0)))
(assert-event (not (fn-bpaj-request *bprf-trailing*)))
(assert-event
 (let* ((request (fn-bpaj-request *bprf-trailing*))
        (ref (fn-bpaj-request-ref request)))
   (not (equal (fn-bpa-encode
                (fn-bpaj-ref-request (car ref) (cadr ref) (caddr ref)
                                     (fn-bpa-request-article request)))
               *bprf-trailing*))))

; ---------------------------------------------------------------------------
; fn-bpaj-context-request-is-the-referenced-article.
; Positive: the native-app context over the Store record resolves to R, whose
; article is the record's payload, of the recorded length and digest.
(assert-event
 (let ((resolved (fn-bpaj-context-request *bprf-ctx* *bpr-record*)))
   (and (equal resolved *bprf-r*)
        (fn-bpa-requestp resolved)
        (equal (fn-bpa-request-article resolved)
               (fn-record-payload *bpr-record*))
        (equal (len (fn-record-payload *bpr-record*))
               (fn-bpaj-nth 9 *bprf-ctx*))
        (equal (fn-frame-digest (fn-record-payload *bpr-record*))
               (fn-bpaj-nth 10 *bprf-ctx*)))))
; Without a resolution: R2's context over the same record (another length
; and digest) resolves to nothing, which is no request.
(assert-event (not (fn-bpaj-context-request *bprf-ctx2* *bpr-record*)))
(assert-event
 (not (fn-bpa-requestp (fn-bpaj-context-request *bprf-ctx2* *bpr-record*))))

; ---------------------------------------------------------------------------
; KEYSTONE fn-bpaj-context-read-resolves-exactly, over the native-app
; tests' Store (*bpr-store*, which committed *bpr-record*).
(defmacro bprf-read-hyps (octets ctx store record)
  `(and (equal ,ctx (fn-bpaj-context-v2-record
                     "bundle-original" ,octets
                     (fn-record-encode-impl *bpr-record*) 7
                     (fn-record-txid *bpr-record*)
                     (fn-record-generation *bpr-record*) :duplicate))
        (equal (fn-bpaj-context-record ,store ,ctx) ,record)
        (fn-record-p ,record)
        (equal (fn-record-payload ,record)
               (fn-bpa-request-article (fn-bpaj-request ,octets)))))
(defmacro bprf-read-concl (octets ctx store)
  `(and (equal (fn-bpaj-context-request
                ,ctx (fn-bpaj-context-record ,store ,ctx))
               (fn-bpaj-request ,octets))
        (equal (fn-bpa-encode
                (fn-bpaj-context-request
                 ,ctx (fn-bpaj-context-record ,store ,ctx)))
               ,octets)))
; Positive, reachable: every hypothesis and the conclusion.
(assert-event (bprf-read-hyps *bprf-r-octets* *bprf-ctx* *bpr-store*
                              *bpr-record*))
(assert-event (bprf-read-concl *bprf-r-octets* *bprf-ctx* *bpr-store*))
; The replay that reads it binds R into the receiver.
(assert-event
 (equal (fn-bpr-context-request
         (car (fn-bpr-state-contexts
               (fn-bpaj-receiver (fn-bpaj-nth 1 *bpaj-context-replay*)))))
        *bprf-r*))
; Without (equal ctx (fn-bpaj-context-v2-record ...)): R's request with R2's
; context; the other three hold, the read resolves to nothing.
(assert-event
 (and (not (equal *bprf-ctx2* *bprf-ctx*))
      (equal (fn-bpaj-context-record *bpr-store* *bprf-ctx2*) *bpr-record*)
      (fn-record-p *bpr-record*)
      (equal (fn-record-payload *bpr-record*)
             (fn-bpa-request-article *bprf-r*))
      (not (bprf-read-concl *bprf-r-octets* *bprf-ctx2* *bpr-store*))))
; Without the Store naming the record: a fresh Store names none; the other
; three hold (the record is R's), the read resolves to nothing.
(assert-event
 (and (not (equal (fn-bpaj-context-record *bpaj-fresh-store* *bprf-ctx*)
                  *bpr-record*))
      (fn-record-p *bpr-record*)
      (equal (fn-record-payload *bpr-record*)
             (fn-bpa-request-article *bprf-r*))
      (not (bprf-read-concl *bprf-r-octets* *bprf-ctx* *bpaj-fresh-store*))))
; Without the payload being the request's article: R2's context over the
; Store's record (R's article); the other three hold, the read resolves to
; nothing, not R2.
(assert-event
 (and (equal (fn-bpaj-context-record *bpr-store* *bprf-ctx2*) *bpr-record*)
      (fn-record-p *bpr-record*)
      (not (equal (fn-record-payload *bpr-record*)
                  (fn-bpa-request-article *bprf-r2*)))
      (not (bprf-read-concl *bprf-r2-octets* *bprf-ctx2* *bpr-store*))))
; Without (fn-record-p record): a request with an empty article (a valid
; request) and no Store record: the fresh Store names none, the absent
; record's payload is the empty article, and the read resolves to nothing.
(defconst *bprf-r0*
  (fn-bpa-make-request "work-empty" "subject-empty" "dtn://sender.lab"
                       "dtn://fn.lab/inbox" "receiver-policy"
                       "sender-inc-native" "wire-auth-context" "terms-1" nil))
(defconst *bprf-r0-octets* (fn-bpa-encode *bprf-r0*))
(make-event `(defconst *bprf-ctx0* ',(fn-bpaj-context-v2-record "bundle-original" *bprf-r0-octets*
                             (fn-record-encode-impl *bpr-record*) 7
                             (fn-record-txid *bpr-record*)
                             (fn-record-generation *bpr-record*) :duplicate)))
(assert-event
 (and (fn-bpa-requestp *bprf-r0*)
      *bprf-ctx0*
      (equal (fn-bpaj-context-record *bpaj-fresh-store* *bprf-ctx0*) nil)
      (not (fn-record-p nil))
      (equal (fn-record-payload nil)
             (fn-bpa-request-article (fn-bpaj-request *bprf-r0-octets*)))
      (not (bprf-read-concl *bprf-r0-octets* *bprf-ctx0*
                            *bpaj-fresh-store*))))

; And the replay refuses that context: an intent for R2 and R2's context
; over R's Store record do not bind.
(assert-event
 (not (car (fn-bpaj-replay
            *bpr-store*
            (list *bpaj-config*
                  (fn-bpaj-intent-record "bundle-original" *bprf-r2-octets* 7
                                         (fn-record-txid *bpr-record*)
                                         :duplicate)
                  *bprf-ctx2*)))))

; ---------------------------------------------------------------------------
; fn-bpaj-intent-names-its-request.
(assert-event (fn-bpaj-intent-names-requestp *bpaj-intent* *bprf-r*))
; A live request with R's metadata and another article is a conflict with
; R's intent (the reference differs), not R.
(assert-event (not (fn-bpaj-intent-names-requestp *bpaj-intent* *bprf-r2*)))
(assert-event
 (equal (fn-bpaj-request-status (fn-bpaj-nth 1 *bpaj-intent-replay*)
                                *bprf-r2-octets*)
        :conflict))
; Without the builder answering (an empty inbound identity): no intent, and
; nil names no request.
(assert-event
 (and (not (fn-bpaj-intent-record "" *bprf-r-octets* 7 0 :duplicate))
      (not (fn-bpaj-intent-names-requestp
            (fn-bpaj-intent-record "" *bprf-r-octets* 7 0 :duplicate)
            (fn-bpaj-request *bprf-r-octets*)))))

; ---------------------------------------------------------------------------
; fn-bpaj-one-reference-is-one-request-or-a-digest-collision.
(assert-event (equal (fn-bpaj-request-ref *bprf-r*)
                     (fn-bpaj-request-ref *bprf-r*)))
; Without (fn-bpa-requestp a): the eleven-element list shares R's reference
; and article and is not R: neither disjunct.
(assert-event
 (and (fn-bpa-requestp *bprf-r*)
      (not (fn-bpa-requestp *bprf-not-request*))
      (equal (fn-bpaj-request-ref *bprf-not-request*)
             (fn-bpaj-request-ref *bprf-r*))
      (not (equal *bprf-not-request* *bprf-r*))
      (equal (fn-bpa-request-article *bprf-not-request*)
             (fn-bpa-request-article *bprf-r*))))
; Without the equal references: R and R2, different, with different lengths.
(assert-event
 (and (not (equal (fn-bpaj-request-ref *bprf-r*)
                  (fn-bpaj-request-ref *bprf-r2*)))
      (not (equal *bprf-r* *bprf-r2*))
      (not (equal (len (fn-bpa-request-article *bprf-r*))
                  (len (fn-bpa-request-article *bprf-r2*))))))
