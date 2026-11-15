; Layer C3: the ordered schemas (STORAGE-DESIGN 1; INBOX-DELIVERY 4.1-4.2).
; Each is a run schema (defrunschema), declared before a world's run
; assembly. Overview and addressing are streams: within one group (one
; principal) the entry's commit position grows with the key, so a range
; read over one stream stops exactly at a position (range.lisp).
(in-package "ACL2")
(include-book "upload-window-geometry")
(include-book "runs-schema")
(include-book "commit-format")

(include-book "upload-page-geometry")
(fn2-book-layer :c)

; Article metadata, latest-only: the article's birth event, its state, the
; version of this row, the source's content identity and its sizes, and
; where the stored source is (S-ARTICLE-LOCATION, c-ordered-runs.md 14): one
; reference in the format's shape, LOCATION-UNIT the physical unit it starts
; at, LOCATION-EPOCH and LOCATION-ALLOCATION the allocation handle that must
; still name its extent, LOCATION-KIND what the reference names (the raw
; source, or a source manifest). BYTES counts the stored article, including
; any injected Message-ID. SOURCE identifies the incoming subject;
; STORED-SOURCE commits the complete stored article. LOCATION-HASHES is the
; ordered, length-delimited vector of hashes for the location's written
; units: exact raw-source unit lengths (including the final short unit), or
; complete padded manifest units. Its bound follows the supported article
; location write span, not every sector reserved by the physical allocator.
; All fields publish in the same article row; the cursor copies the vector
; while that row is current and verifies a location unit before consuming it.
(make-event
 `(defrunschema fn2-article :id 2
 :key ((article (:id article)))
 :value ((birth (:id event)) (state (:enum fn2-article-state (:live :withdrawn))) (version (:id version))
         (source :digest) (bytes :varint) (lines :varint)
         (location-unit (:id physical-unit)) (location-epoch (:id writer-epoch))
         (location-allocation (:id allocation))
         (location-kind (:enum fn2-article-location-kind (:raw-source :source-manifest)))
         ;; BLAKE3 of actual stored bytes, including an injected Message-ID.
         (stored-source :digest)
         (location-hashes (:octets ,*fn2-article-location-hashes-max*)))
 :merge :latest))

; Overview, keyed (group, number) from first materialization; the stored
; overview line (subject, from, date, message-id, references, bytes,
; lines, without the number) is the exact octets the reader serves.

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
