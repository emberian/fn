; The byte-store model's alpha is the entries' alpha (the records flip).
;
; books/byte-store-scan.lisp states the byte-store relation over
; fn-bs-row-wire / fn-bs-rows-wire: the wire event a retained row stands
; for, read through the arena's LOGICAL value (the list of sealed payloads),
; so that the byte model stays free of the stobj.  The host's entries
; (books/store-intern.lisp) read the same thing through the fn-arena stobj:
; fn-row-wire-of / fn-rows-wire-of, which is what the entry encodes into the
; frame it hands to the P-RECORD program and what the recover's intern reads
; back.  This book is the boundary theorem between the two: they are the same
; function of the arena's logical value (books/payload-arena.lisp
; fn-arena-payload-is-nth, fn-arena-count-is-len), and the K0 article input
; stated over the entry's alpha.
(in-package "ACL2")
(include-book "byte-store-record-provenance-bytes")
(include-book "store-intern")

(defthm fn-bs-row-wire-is-the-entries-alpha
  (equal (fn-row-wire-of row fn-arena) (fn-bs-row-wire row fn-arena))
  :hints (("Goal" :in-theory (enable fn-row-wire-of fn-row-bytes
                                     fn-bs-row-wire fn-bs-handle-bytes))))

(defthm fn-bs-rows-wire-is-the-entries-alpha
  (equal (fn-rows-wire-of rows fn-arena) (fn-bs-rows-wire rows fn-arena))
  :hints (("Goal" :induct (fn-bs-rows-wire rows fn-arena)
           :in-theory (e/d (fn-rows-wire-of fn-bs-rows-wire)
                           (fn-row-wire-of fn-bs-row-wire)))))

; K0 for the host's article arguments, stated over the entry's alpha: the
; staged candidate is the retained row the prepare entry staged, the frame is
; the codec's encoding of fn-row-wire-of of it, and the relation's arena is
; the entry's.  The hypothesis that the row's alpha is a wire record is what
; the intern establishes for a row it made.
(defthm fn-bs-k0-entry-article-arguments-are-typed-record-input
  (implies (and (fn-record-p (fn-row-wire-of row fn-arena))
                (equal (fn-sf-phase ks) :record-staged)
                (equal (fn-sf-record-candidate ks) row)
                (fn-bs-namep stage))
           (fn-bs-record-inputp
            ks stage
            (fn-bs-txn-name (fn-store-event-sequence row))
            (append
             (fn-frame-store-protected
              (fn-store-event-encode (fn-row-wire-of row fn-arena)))
             (fn-frame-trailer
              (fn-frame-store-protected
               (fn-store-event-encode (fn-row-wire-of row fn-arena)))))
            fn-arena))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bs-k0-article-host-arguments-are-typed-record-input
                                   (arena fn-arena)))
           :in-theory (union-theories '(fn-bs-row-wire-is-the-entries-alpha)
                                      (theory 'minimal-theory)))))
