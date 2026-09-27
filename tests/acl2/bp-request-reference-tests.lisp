; Teeth for books/bp-request-reference.lisp (PKT-646, PRF-249).
(in-package "ACL2")
(include-book "../../books/bp-request-reference")
(include-book "bp-native-app-tests")
(include-book "bp-transit-join-tests")

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
(make-event `(defconst *bprf-ctx2* ',(fn-bpaj-transit-context-record "bundle-original" *bprf-r2-octets*
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
; article's intent holds a HEAD under 2,200 octets, the article's LENGTH and
; DIGEST, the projection's LENGTH and DIGEST, and no article.
(make-event `(defconst *bprf-big-intent* ',(bpaj-test-intent "bundle-big" *bprf-big-octets* 1 2 :accepted
                                           (fn-bpa-request-article *bprf-big*))))
(assert-event
 (and (fn-bpaj-transit-intentp *bprf-big-intent*)
      (equal (len *bprf-big-intent*) 13)
      (< (len (fn-bpaj-nth 2 *bprf-big-intent*)) 2200)
      (equal (fn-bpaj-nth 9 *bprf-big-intent*) 100000)
      (equal (fn-bpaj-nth 10 *bprf-big-intent*)
             (fn-frame-digest (fn-bpa-request-article *bprf-big*)))
      (not (member-equal (fn-bpa-request-article *bprf-big*)
                         *bprf-big-intent*))
      (< (len *bprf-big-octets*) (+ 100000 2200))))
; The FNRJ codec encodes it (its wire values: the text fields as octets) in
; under 4,096 octets.
(assert-event
 (let ((payload (fn-frame-fields-octets
                 (fn-frame-spec-for :request-transit-intent
                                    *fn-frame-receipt-specs*)
                 (list* (fn-record-string-octets
                         (fn-bpaj-nth 1 *bprf-big-intent*))
                        (fn-bpaj-nth 2 *bprf-big-intent*)
                        (fn-bpaj-nth 3 *bprf-big-intent*)
                        (fn-bpaj-nth 4 *bprf-big-intent*)
                        (fn-bpaj-nth 5 *bprf-big-intent*)
                        (fn-record-string-octets (fn-bpaj-nth 6 *bprf-big-intent*))
                        (fn-record-string-octets (fn-bpaj-nth 7 *bprf-big-intent*))
                        (fn-record-string-octets (fn-bpaj-nth 8 *bprf-big-intent*))
                        (nthcdr 9 *bprf-big-intent*)))))
   (and payload (< (len payload) 4096))))

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
; KEYSTONE fn-bpaj-transit-context-binds-the-live-request, over the
; native-app tests' Store (*bpr-store*, which committed *bpr-record*).
(defmacro bprf-binds-concl (octets ctx record)
  `(and (equal (fn-bpr-context-from-ref ,record (fn-bpaj-context-ref ,ctx))
               (fn-bpr-context-from-request ,record (fn-bpaj-request ,octets)))
        (equal (fn-bpr-context-request-ref
                (fn-bpr-context-from-ref ,record (fn-bpaj-context-ref ,ctx)))
               (fn-bpaj-request-ref (fn-bpaj-request ,octets)))))
; Positive, reachable: the context the host builds for R, and the record the
; replay resolves for it.
(assert-event
 (and *bprf-ctx*
      (equal (fn-bpaj-context-record *bpr-store* *bprf-ctx*) *bpr-record*)
      (bprf-binds-concl *bprf-r-octets* *bprf-ctx* *bpr-record*)))
; The replay that reads it binds exactly that context into the receiver, and
; the receiver's reference is R's.
(assert-event
 (equal (car (fn-bpr-state-contexts
              (fn-bpaj-receiver (fn-bpaj-nth 1 *bpaj-context-replay*))))
        (fn-bpr-context-from-request *bpr-record* *bprf-r*)))
(assert-event
 (equal (fn-bpr-context-request-ref
         (car (fn-bpr-state-contexts
               (fn-bpaj-receiver (fn-bpaj-nth 1 *bpaj-context-replay*)))))
        (fn-bpaj-request-ref *bprf-r*)))
; Without the builder answering (an empty inbound identity): no context, and
; the conclusion fails.
(assert-event
 (and (not (fn-bpaj-transit-context-record
            "" *bprf-r-octets* (fn-record-encode-impl *bpr-record*) 7
            (fn-record-txid *bpr-record*) (fn-record-generation *bpr-record*)
            :duplicate))
      (not (bprf-binds-concl *bprf-r-octets* nil *bpr-record*))))
; And the replay refuses R2's context under R's intent (the references
; differ), and R2's intent over R's Store record (its pinned projection is
; R2's article, not the record's payload).
(assert-event
 (not (car (fn-bpaj-replay *bpr-store*
                           (list *bpaj-config* *bpaj-intent* *bprf-ctx2*)))))
(assert-event
 (not (car (fn-bpaj-replay
            *bpr-store*
            (list *bpaj-config*
                  (bpaj-test-intent "bundle-original" *bprf-r2-octets* 7
                                    (fn-record-txid *bpr-record*) :duplicate
                                    (fn-bpa-request-article *bprf-r2*))
                  *bprf-ctx2*)))))

; ---------------------------------------------------------------------------
; KEYSTONE fn-bpaj-transit-intent-pins-its-request-and-projection, over the
; transit-join tests' plan (*btj-plan*, a Path-bearing request).
(defmacro bprf-pins-concl (intent octets plan)
  `(let ((projection (fn-pu-relay-article
                      (fn-bpa-request-article (fn-bpaj-request ,octets))
                      (fn-record-string-octets (fn-bpaj-nth 7 ,intent))
                      (fn-record-string-octets (fn-bpaj-nth 8 ,intent)))))
     (and (fn-bpaj-transit-intentp ,intent)
          (fn-bpaj-intent-names-requestp ,intent (fn-bpaj-request ,octets))
          (equal (fn-bpaj-nth 11 ,intent) (len projection))
          (equal (fn-bpaj-nth 12 ,intent) (fn-frame-digest projection))
          (equal projection (fn-bpaj-transit-stored-octets ,plan)))))
(assert-event
 (and *btj-intent*
      (bprf-pins-concl *btj-intent* *btj-request-octets* *btj-plan*)
      ; the projection is not the request's article: the pin is not vacuous
      (not (equal (fn-bpaj-transit-stored-octets *btj-plan*)
                  (fn-bpa-request-article *btj-request*)))))
; Without the builder answering (a refused plan): no intent, and the
; conclusion fails.
(assert-event
 (let ((plan (cons :refused (cdr *btj-plan*))))
   (and (not (fn-bpaj-transit-intent-from-plan
              *btj-cfg* "bundle-btj" *btj-request-octets* 1 0 :accepted plan))
        (not (bprf-pins-concl nil *btj-request-octets* plan)))))

; ---------------------------------------------------------------------------
; The live comparison (`fn-bpaj-intent-names-requestp').
(assert-event (fn-bpaj-intent-names-requestp *bpaj-intent* *bprf-r*))
; A live request with R's metadata and another article is a conflict with
; R's intent (the reference differs), not R.
(assert-event (not (fn-bpaj-intent-names-requestp *bpaj-intent* *bprf-r2*)))
(assert-event
 (equal (fn-bpaj-request-status (fn-bpaj-nth 1 *bpaj-intent-replay*)
                                *bprf-r2-octets*)
        :conflict))

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
