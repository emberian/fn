; fn: the field checks of the Store's prepares, owned by ACL2 (lane
; host-decisions, 2026-09-27).
;
; Before this book the POST's field checks were an `or' in host code over two
; predicates DEFINED IN HOST CODE (host/store-host.lisp fn-store-text-octetsp
; and fn-store-msgid-octetsp), with a host constant `*fn-store-max-text*' of
; 512 octets that no book owned and the record codec contradicted: the record's
; three metadata fields (obligation id, content subject, release evidence) are
; at most `*fn-record-max-metadata*' = 256 octets (books/records-shape.lisp),
; so a field of 257 to 512 octets passed the host check and built a record
; `fn-record-p' refuses.
;
; What the fields are decides where their bound belongs (D27).  None of the
; three metadata fields is data a poster or a peer supplies: the obligation id
; and the content subject are the node's renderings of two digests
; (books/identity.lisp fn-id-text), the release evidence is the node's
; provenance wire (books/provenance-codec.lisp fn-prov-wire, bounded by
; construction: fn-prov-durable-wire-is-metadata).  Their bound is therefore
; the record codec's field domain, not an admission limit on stored data, and
; it is not an operator profile field.  The data a POST does carry is bounded
; where it already is: the Message-ID by RFC 5536 section 3.1.3
; (books/article-fields.lisp fn-af-message-idp, 250 octets), the payload and
; group count by the store profile (fn-sbud-post-boundary), the headers by the
; profile's header limits (fn-bs-profile-header-limits, header-limits-profile).
;
; A group name in a configuration request is operator data; its bound is the
; group name's codec ceiling (`*fn-record-max-group-name*', the configuration
; label's), which the configuration itself also enforces.
;
; Every check below bounds its work before it walks its input
; (fn-cbor-at-mostp stops at the bound), and each composed verdict is the one
; the host calls: the host keeps no test of its own.

(in-package "ACL2")
(include-book "records-shape")
(include-book "article-fields")
(include-book "acceptance-alloc")
(include-book "provenance-codec")

(local (in-theory (enable fn-record-shape-vocabulary)))

; -----------------------------------------------------------------------------
; Field domains

; Printable ASCII without space: RFC 5322 section 3.2.3's VCHAR, which the
; node's hexadecimal renderings and its provenance wire are made of.
(defun fn-pfld-printable-octetsp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (integerp (car xs)) (<= 33 (car xs)) (<= (car xs) 126)
           (fn-pfld-printable-octetsp (cdr xs)))
    (null xs)))

; A node-generated metadata field of a Store record.
(defun fn-pfld-textp (xs)
  (declare (xargs :guard t))
  (and (consp xs)
       (fn-cbor-at-mostp xs *fn-record-max-metadata*)
       (fn-pfld-printable-octetsp xs)))

; A group name in a configuration request (declare, reconfigure).
(defun fn-pfld-group-name-requestp (xs)
  (declare (xargs :guard t))
  (and (consp xs)
       (fn-cbor-at-mostp xs *fn-record-max-group-name*)
       (fn-pfld-printable-octetsp xs)))

; The Message-ID check as a boolean, for the bridge (tools/frame_bridge.py).
(defun fn-pfld-msgid-validp (xs)
  (declare (xargs :guard t))
  (if (fn-af-message-idp xs) t nil))

; -----------------------------------------------------------------------------
; The composed verdicts the host calls

; An article's payload size is representable by the record codec.  The
; operator's bound is the profile's (fn-sbud-post-boundary, asked before the
; prepare); this is the codec's ceiling, which every profile sits below.
(defun fn-pfld-payload-sizep (n)
  (declare (xargs :guard t))
  (and (natp n) (<= n *fn-record-max-payload*)))

; GROUPS is ACL2's resolution of the POST's group codes
; (books/store-config.lisp fn-store-groups-from-codes): :bad or a list.
(defun fn-pfld-article-inputsp (msgid payload-octets groups id subject
                                      evidence charge)
  (declare (xargs :guard t))
  (and (fn-af-message-idp msgid)
       (fn-pfld-payload-sizep payload-octets)
       (consp groups)
       (fn-pfld-textp id)
       (fn-pfld-textp subject)
       (fn-pfld-textp evidence)
       (posp charge)
       t))

; A retention event ACL2's workflow authored (host/native/owner.lisp
; fnn-owner-retention-commit).
(defun fn-pfld-retention-inputsp (kind id subject evidence charge)
  (declare (xargs :guard t))
  (and (member-equal kind '(:undertake :release))
       (fn-pfld-textp id)
       (fn-pfld-textp subject)
       (fn-pfld-textp evidence)
       (natp charge)
       t))

; The lab BP ingress host's per-ADU inputs (host/bp-ingress-host.lisp
; fn-bpi-host-inputsp): the transport context's three identifiers, the
; policy's archive id, subject and evidence, all in the record's metadata
; domain (books/bp-ingress.lisp asks `fn-record-metadata-bytes-p' of the
; context again), and u32 lifetime and positive u32 charge.
(defun fn-pfld-bp-ingress-inputsp (destination source-eid bundle-id lifetime
                                               archive-id subject evidence
                                               charge)
  (declare (xargs :guard t))
  (and (fn-pfld-textp destination) (fn-pfld-textp source-eid)
       (fn-pfld-textp bundle-id) (fn-record-uint32p lifetime)
       (fn-pfld-textp archive-id) (fn-pfld-textp subject)
       (fn-pfld-textp evidence) (fn-record-uint32p charge) (posp charge)
       t))

; A Message-ID and resolved groups, for the existing-article test.
(defun fn-pfld-lookup-inputsp (msgid groups)
  (declare (xargs :guard t))
  (and (fn-af-message-idp msgid)
       (consp groups)
       t))

; -----------------------------------------------------------------------------
; What an admitted field is, and that the check is exactly the codec's domain

(local
 (defthm fn-pfld-printable-is-octets
   (implies (fn-pfld-printable-octetsp xs)
            (and (fn-cbor-octet-listp xs)
                 (fn-record-ascii-octet-listp xs)
                 (true-listp xs)))
   :hints (("Goal" :in-theory (enable fn-cbor-octet-listp fn-cbor-octetp)))))

(local
 (defthm fn-pfld-at-mostp-is-len
   (implies (natp bound)
            (equal (fn-cbor-at-mostp xs bound) (<= (len xs) bound)))
   :hints (("Goal" :in-theory (enable fn-cbor-at-mostp)))))

(local
 (defthm fn-pfld-string-octets-aux-of-octets-chars
   (implies (fn-cbor-octet-listp xs)
            (equal (fn-record-string-octets-aux (fn-record-octets-chars xs))
                   xs))
   :hints (("Goal" :in-theory (enable fn-cbor-octet-listp fn-cbor-octetp)))))

(local
 (defthm fn-pfld-character-listp-of-octets-chars
   (character-listp (fn-record-octets-chars xs))))

(defthm fn-pfld-string-round-trip
  (implies (fn-cbor-octet-listp xs)
           (equal (fn-record-string-octets (fn-record-octets-string xs)) xs))
  :hints (("Goal" :in-theory (enable fn-record-string-octets
                                     fn-record-octets-string))))

; KEYSTONE.  A field the check admits is a Store record metadata field
; (`fn-record-metadata-bytes-p', the domain `fn-record-p' asks of the three
; fields), whose octets are the field's own.
(defthm fn-pfld-textp-is-a-record-metadata-field
  (implies (fn-pfld-textp xs)
           (and (fn-record-metadata-bytes-p (fn-record-octets-string xs))
                (fn-record-ascii-stringp (fn-record-octets-string xs))
                (equal (fn-record-string-octets (fn-record-octets-string xs))
                       xs)))
  :hints (("Goal" :in-theory (enable fn-record-metadata-bytes-p
                                     fn-record-octet-stringp
                                     fn-record-ascii-stringp
                                     fn-record-nonempty-at-mostp))))

; KEYSTONE.  The check refuses no printable field the record would carry: over
; printable octets it is exactly the record's metadata domain, so the host's
; old 512-octet ceiling (which admitted fields the record refuses) is gone and
; no tighter one replaced it.
(defthm fn-pfld-textp-is-exactly-the-record-metadata-domain
  (implies (fn-pfld-printable-octetsp xs)
           (equal (fn-pfld-textp xs)
                  (fn-record-metadata-bytes-p (fn-record-octets-string xs))))
  :hints (("Goal" :in-theory (enable fn-record-metadata-bytes-p
                                     fn-record-octet-stringp
                                     fn-record-nonempty-at-mostp))))

; The group-name request check is the group name's codec ceiling over
; printable octets.
(defthm fn-pfld-group-name-requestp-is-bounded-by-the-codec
  (implies (fn-pfld-group-name-requestp xs)
           (and (fn-record-octet-stringp (fn-record-octets-string xs))
                (fn-record-nonempty-at-mostp
                 (fn-record-string-octets (fn-record-octets-string xs))
                 *fn-record-max-group-name*)))
  :hints (("Goal" :in-theory (enable fn-record-octet-stringp
                                     fn-record-nonempty-at-mostp))))

; -by-definition: the composed article verdict names each field's check.
(defthm fn-pfld-article-inputsp-by-definition
  (iff (fn-pfld-article-inputsp msgid payload-octets groups id subject
                                evidence charge)
       (and (fn-af-message-idp msgid)
            (natp payload-octets)
            (<= payload-octets *fn-record-max-payload*)
            (consp groups)
            (fn-pfld-textp id) (fn-pfld-textp subject) (fn-pfld-textp evidence)
            (posp charge)))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; The node-generated fields are admitted: the check never refuses a POST the
; node itself describes

(local
 (defthm fn-pfld-printable-of-append
   (equal (fn-pfld-printable-octetsp (append xs ys))
          (and (fn-pfld-printable-octetsp (true-list-fix xs))
               (fn-pfld-printable-octetsp ys)))))

(local
 (defthm fn-pfld-hex-is-printable
   (implies (fn-id-hex-listp xs)
            (fn-pfld-printable-octetsp xs))
   :hints (("Goal" :in-theory (enable fn-id-hex-listp fn-id-hex-digitp)))))

(local
 (defthm fn-pfld-consp-of-hex-octets
   (equal (consp (fn-id-hex-octets xs)) (consp xs))
   :hints (("Goal" :in-theory (enable fn-id-hex-octets)))))

(local
 (defthm fn-pfld-len-of-hex-octets
   (equal (len (fn-id-hex-octets xs)) (* 2 (len xs)))
   :hints (("Goal" :in-theory (enable fn-id-hex-octets)))))

; An identity rendering (books/identity.lisp fn-id-text: the obligation id and
; the content subject the host puts in the record) is admitted whenever the
; identity is a nonempty octet list of at most 128 octets; a SHA-256 identity
; is 32.
(defthm fn-pfld-identity-text-is-admitted
  (implies (and (fn-cbor-octet-listp identity)
                (consp identity)
                (<= (len identity) 128))
           (fn-pfld-textp (fn-id-text identity)))
  :hints (("Goal"
           :use ((:instance fn-id-hex-octets-are-hex (octets identity))
                 (:instance fn-pfld-hex-is-printable
                            (xs (fn-id-hex-octets identity))))
           :in-theory (e/d (fn-pfld-textp fn-id-text)
                           (fn-id-hex-octets fn-pfld-printable-octetsp
                            fn-id-hex-listp fn-pfld-hex-is-printable
                            fn-id-hex-octets-are-hex)))))

; The evidence of a locally posted article (host/store-node-host.lisp
; fn-store-prov-post marshals it): the post provenance under the node's path
; identity ("local" when none is configured) and the configuration generation,
; in its canonical wire form when the record's evidence field carries it
; (fn-prov-durablep) and its legacy rendering otherwise.  This was a host
; decision until lane host-decisions.
(defun fn-pfld-post-evidence (identity generation)
  (declare (xargs :guard t))
  (let* ((principal (if (and (stringp identity) (not (equal identity "")))
                        identity
                      "local"))
         (p (fn-prov-make-post principal generation)))
    (fn-record-string-octets
     (if (fn-prov-durablep p) (fn-prov-wire p) (fn-prov-render p)))))

(local
 (defthm fn-pfld-structured-octets-are-octets
   (fn-cbor-octet-listp (fn-prov-structured-octets p))
   :hints (("Goal" :in-theory (enable fn-prov-structured-octets
                                      fn-cbor-invariants-vocabulary)))))

(local
 (defthm fn-pfld-wire-octets-are-printable
   (fn-pfld-printable-octetsp (fn-prov-wire-octets p))
   :hints (("Goal" :in-theory (e/d (fn-prov-wire-octets)
                                   (fn-prov-structured-octets))))))

(local
 (defthm fn-pfld-string-octets-of-wire
   (implies (not (stringp p))
            (equal (fn-record-string-octets (fn-prov-wire p))
                   (fn-prov-wire-octets p)))
   :hints (("Goal" :in-theory (e/d (fn-prov-wire)
                                   (fn-prov-wire-octets))))))

; KEYSTONE.  Every evidence value the node generates for a POST is admitted by
; the field check (and so is a record metadata field:
; fn-pfld-textp-is-a-record-metadata-field).
(defthm fn-pfld-post-evidence-is-admitted
  (implies (natp generation)
           (fn-pfld-textp (fn-pfld-post-evidence identity generation)))
  :hints (("Goal"
           :cases ((fn-prov-durablep
                    (fn-prov-make-post
                     (if (and (stringp identity) (not (equal identity "")))
                         identity
                       "local")
                     generation)))
           :use ((:instance fn-prov-durable-wire-is-metadata
                            (p (fn-prov-make-post
                                (if (and (stringp identity)
                                         (not (equal identity "")))
                                    identity
                                  "local")
                                generation))))
           :in-theory (e/d (fn-pfld-post-evidence fn-pfld-textp
                            fn-record-metadata-bytes-p
                            fn-record-nonempty-at-mostp)
                           (fn-prov-wire fn-prov-wire-octets
                            fn-prov-durablep fn-prov-render)))))

(in-theory (disable fn-pfld-textp fn-pfld-group-name-requestp
                    fn-pfld-article-inputsp fn-pfld-retention-inputsp
                    fn-pfld-lookup-inputsp fn-pfld-payload-sizep
                    fn-pfld-bp-ingress-inputsp fn-pfld-post-evidence
                    fn-pfld-msgid-validp))
