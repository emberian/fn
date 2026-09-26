; fn: the store profile's open gates, and the profile frame's round trip.
;
; A store's profile (books/byte-store-frame.lisp, `config.json', an FNSM
; frame) bounds the work of opening the store before any configuration record
; is replayed.  It is written once, at `init' (or `store import', which is an
; `init' and a replay), and never rewritten in place (D34, fresh deploys: a
; different profile is a reinstall and an import; the offline upgrade, its
; relation and its byte program were removed with it).  This book holds the
; gates the host consults when it opens a store, over the functions it calls:
;   - the transaction namespace observation, `fn-profile-txn-observation'
;     (host/store-host.lisp `fn-store-txn-observation-selected', called from
;     host/native/io.lisp `fnn-transaction-files' with field 4);
;   - the aggregate replay bound, `fn-profile-replay-within-boundp'
;     (host/store-host.lisp `fn-store-profile-replay-within-bound', called
;     per record from host/native/io.lisp `fnn-durable-records');
; and the metadata codec's round trip for every valid profile
; (`fn-bs-config-decode-of-encode'): what `init' writes is what the next
; open decodes.
(in-package "ACL2")
(include-book "store-budget")
(include-book "byte-store-txn-name")
(local (include-book "frame-invariants"))
(local (include-book "cbor-invariants"))

; -----------------------------------------------------------------------------
; The open gates, as the host calls them

; The transaction-namespace observation: at most MAXIMUM names (the profile's
; max_transactions, host/native/io.lisp `fnn-transaction-files'), then ACL2's
; name grammar and sequence binding.
(defun fn-profile-txn-observation (names maximum selected-lower)
  (declare (xargs :guard t))
  (if (and (natp maximum) (natp selected-lower) (true-listp names)
           (<= (len names) maximum))
      (fn-bs-txn-observation-selected names selected-lower)
    :invalid))

; The aggregate replay input: at most the profile's max_history_octets.
(defun fn-profile-replay-within-boundp (profile aggregate)
  (declare (xargs :guard t))
  (and (fn-bs-profile-admittedp profile)
       (natp aggregate)
       (<= aggregate (fn-bs-profile-max-history-octets profile))))

(local (in-theory (enable fn-bs-profile-validp)))

; -----------------------------------------------------------------------------
; The frame `init' writes

(local
 (defthm fn-profile-octet-list-is-true-list
   (implies (fn-cbor-octet-listp xs) (true-listp xs))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))

(local
 (defthm fn-profile-seal-octet-listp
   (implies (fn-frame-inputp magic version kind payload max-payload)
            (fn-cbor-octet-listp (fn-frame-seal magic version kind payload)))
   :hints (("Goal"
            :use ((:instance fn-frame-digestp-of-fn-frame-digest
                             (octets (fn-frame-protected magic version kind payload)))
                  (:instance fn-cbor-u32-bytes-are-octets (n (len payload))))
            :in-theory (e/d (fn-frame-seal fn-frame-encode fn-frame-protected
                             fn-frame-header fn-frame-inputp fn-frame-magicp
                             fn-frame-digestp fn-cbor-octet-listp-append)
                            (fn-frame-digestp-of-fn-frame-digest
                             fn-cbor-u32-bytes-are-octets))))))

(local
 (defthm fn-profile-fields-round-trip
   (implies (fn-bs-profile-validp values)
            (equal (fn-frame-fields-parse
                    *fn-bs-meta-profile-spec*
                    (fn-frame-fields-octets *fn-bs-meta-profile-spec* values))
                   (fn-frame-parse-ok values nil)))
   :hints (("Goal" :use ((:instance fn-bs-profile-validp-facts)
                         (:instance fn-frame-fields-parse-of-octets
                                    (specs *fn-bs-meta-profile-spec*)))
            :in-theory (disable fn-bs-profile-validp-facts
                                fn-frame-fields-parse-of-octets
                                fn-bs-profile-validp)))))

; The metadata codec's round trip for EVERY valid profile: what `init'
; writes is what the next open decodes (under A-CRYPTO, through
; fn-frame-open-of-seal).
(defthm fn-bs-config-decode-of-encode
  (implies (fn-bs-profile-validp values)
           (equal (fn-bs-config-decode (fn-bs-config-encode values))
                  values))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-frame-open-of-seal
                            (magic *fn-bs-meta-magic*)
                            (version *fn-bs-meta-version*)
                            (kind *fn-bs-meta-config-kind*)
                            (payload (fn-frame-fields-octets
                                      *fn-bs-meta-profile-spec* values))
                            (max-payload *fn-bs-meta-max-config-payload*))
                 (:instance fn-profile-seal-octet-listp
                            (magic *fn-bs-meta-magic*)
                            (version *fn-bs-meta-version*)
                            (kind *fn-bs-meta-config-kind*)
                            (payload (fn-frame-fields-octets
                                      *fn-bs-meta-profile-spec* values))
                            (max-payload *fn-bs-meta-max-config-payload*))
                 (:instance fn-bs-profile-frame-inputp)
                 (:instance fn-profile-fields-round-trip))
           :in-theory (e/d (fn-bs-config-decode fn-bs-config-encode
                            fn-bs-meta-frame-okp fn-frame-inputp)
                           (fn-frame-open-of-seal fn-profile-seal-octet-listp
                            fn-bs-profile-frame-inputp
                            fn-profile-fields-round-trip
                            fn-bs-profile-validp)))))

(in-theory (disable fn-profile-txn-observation fn-profile-replay-within-boundp))
