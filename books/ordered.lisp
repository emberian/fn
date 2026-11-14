; Layer C3: the ordered schemas (STORAGE-DESIGN 1; INBOX-DELIVERY 4.1-4.2).
; Each is a run schema (defrunschema), declared before a world's run
; assembly. Overview and addressing are streams: within one group (one
; principal) the entry's commit position grows with the key, so a range
; read over one stream stops exactly at a position (range.lisp).
(in-package "ACL2")
(include-book "runs-schema")
(fn2-book-layer :c)

; Article metadata, latest-only: the article's birth event, its state, the
; version of this row, the source's content identity and its sizes, and
; where the stored source is (S-ARTICLE-LOCATION, c-ordered-runs.md 14): one
; reference in the format's shape, LOCATION-UNIT the physical unit it starts
; at, LOCATION-EPOCH and LOCATION-ALLOCATION the allocation handle that must
; still name its extent, LOCATION-KIND what the reference names (the raw
; source, or a source manifest). The reference's encoded length is BYTES and
; its expected hash SOURCE (the stored octets are the source the identity
; digests); its storage domain is the node's one domain. Written by the
; transaction at :prepare from its upload's payload extent; read by
; ARTICLE/HEAD/BODY before fn2-block-read.
(defrunschema fn2-article :id 2
 :key ((article (:id article)))
 :value ((birth (:id event)) (state (:enum fn2-article-state (:live :withdrawn))) (version (:id version))
         (source :digest) (bytes :varint) (lines :varint)
         (location-unit (:id physical-unit)) (location-epoch (:id writer-epoch))
         (location-allocation (:id allocation))
          (location-kind (:enum fn2-article-location-kind (:raw-source :source-manifest)))
          (membership-count :varint))
 :merge :latest)

; Original admitted stream identifiers, independent of later group-directory
; renumbering. The article row's persisted count owns exactly ordinals [0,count).
; One successor transaction publishes the article, every membership and count.
; A reader must treat a missing ordinal below count as a fault, not end-of-list.
(defrunschema fn2-article-membership :id 20
 :key ((article (:id article)) (ordinal (:id membership-ordinal)))
 :value ((stream (:id stream)))
 :merge :unique)

; Overview, keyed (group, number) from first materialization; the stored
; overview line (subject, from, date, message-id, references, bytes,
; lines, without the number) is the exact octets the reader serves.
(defconst *fn2-overview-octets-max* 1024)
(defrunschema fn2-overview :id 3
 :key ((group (:id group)) (number (:id group-number)))
 :value ((article (:id article)) (position (:id position)) (line (:octets 1024)))
 :merge :unique)

; The addressing index: one entry per addressed principal per event.
(defrunschema fn2-addr :id 4
 :key ((principal (:id principal)) (position (:id position)))
 :value ((article (:id article)) (stream (:id stream)) (reasons :u8))
 :merge :unique)

; The group directory (seam S-GROUP): a newsgroup's exact name octets to its
; group identifier, the (:id group) key of fn2-group-counts and fn2-overview.
; Latest-only: a renumbering or a later configuration replaces the row. The
; configured groups enter at genesis from the profile's :groups list
; (machines-c-groups.lisp; E owns the configuration later); a POST's
; Newsgroups octets are looked up exactly, and an absent name is the 441
; "no such newsgroup" refusal.
(defrunschema fn2-groups :id 8
 :key ((name (:octets 250)))
 :value ((group (:id group)))
 :merge :latest)

; Operation outcomes (seam S-OUTCOME; d-machines-nntp.md 14.4.1): the outcome
; of (principal, operation), a record of the batch that carried it. A retry
; with the same operation identity reads the original outcome; the request
; digest refuses a contradictory reuse. OUTCOME is the operation's reply code,
; EVENT the member's commit position.
(defrunschema fn2-outcome :id 9
 :key ((principal (:id principal)) (operation (:id operation)))
 :value ((request :digest) (outcome :u16) (event (:id event)))
 :merge :unique)

; Consumer names (E's consumer port): a principal's registered wire name
; (at most 64 octets) to the consumer identifier that keys
; fn2-consumer-cursor. Unique: a second registration of (principal, name)
; is refused at stage (:duplicate), so a name maps to one consumer for the
; store's life. Written by register's transaction (D's txn port, :consumer
; mode); E's cursor verbs read it by an exact lookup.
(defrunschema fn2-consumer-names :id 15
 :key ((principal (:id principal)) (name (:octets 64)))
 :value ((consumer (:id consumer)))
 :merge :unique)
