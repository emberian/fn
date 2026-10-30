; Layer C3: the ordered schemas (STORAGE-DESIGN 1; INBOX-DELIVERY 4.1-4.2).
; Each is a run schema (defrunschema), declared before a world's run
; assembly. Overview and addressing are streams: within one group (one
; principal) the entry's commit position grows with the key, so a range
; read over one stream stops exactly at a position (range.lisp).
(in-package "ACL2")
(include-book "runs-schema")
(fn2-book-layer :c)

; Article metadata, latest-only: the article's birth event, its state, the
; version of this row, the source's content identity and its sizes.
(defrunschema fn2-article :id 2
 :key ((article (:id article)))
 :value ((birth (:id event)) (state (:enum fn2-article-state (:live :withdrawn))) (version (:id version))
         (source :digest) (bytes :varint) (lines :varint))
 :merge :latest)

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
