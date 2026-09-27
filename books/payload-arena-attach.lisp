; fn: the arena's PAGED implementation ATTACHED to the generic (the
; records freeze, lane records-freeze 2026-09-26; the consolidation design
; section 3; gpt-6's section 4: the concrete handle behind an explicit
; abstraction).  Lane arena-offheap (2026-09-27) replaced the byte-array
; attachment `fn-arena-bytes' (one array doubled when full: at the last
; doubling the old and the new array were live together) by `fn-arena-paged'
; (books/payload-arena-paged.lisp: fixed 64 KiB pages, a sealed octet never
; moves, growth allocates one page).  The logical side is the same, so no
; book above the generic recertifies.
;
; Three events, in this order, are the whole mechanism:
;   1. the implementation is introduced (`fn-arena-paged',
;      books/payload-arena-paged.lisp: the page table with an offset and a
;      size per handle);
;   2. `(attach-stobj fn-arena fn-arena-paged)' names it as the attachment of
;      a stobj not yet introduced;
;   3. the generic is introduced (`fn-arena', books/payload-arena.lisp,
;      `:attachable t'), and BECAUSE the attachment precedes it, its
;      foundation and every export's executable are the byte array's, while
;      its logical side is unchanged (the two share their :logic functions by
;      construction).
; A book certified over the generic -- the held record and its interns
; (books/catalog-record.lisp), the catalog and everything above it -- is then
; included unchanged: its certificate is the generic's, and its functions
; run over the pages.  The image (host/native/build.lisp) includes THIS
; book before any book that names `fn-arena', so the node's arena is one
; byte per payload octet.  Nothing above this book names an implementation.
;
; What runs at certification time (skipped by include-book): the intern of a
; ground wire record into the live `fn-arena', whose foundation is now the
; page table (six fields: pages, off, size, count, fill, npages; the list
; foundation has one), and its materialization by handle, asserted equal to
; the record;
; the fold `fn-arn-seal-many' and the reads.  The values are the logical
; ones either way; the foundation is the pages'.

(in-package "ACL2")
(include-book "payload-arena-paged")
(attach-stobj fn-arena fn-arena-paged)
(include-book "payload-arena")
(include-book "catalog-record")

; A ground wire record: an article "Subject: a" CRLF CRLF "line1" CRLF.
(defconst *paa-art*
  (append (fn-record-string-octets "Subject: a") '(13 10 13 10)
          (fn-record-string-octets "line1") '(13 10)))

(defconst *paa-w*
  (fn-record-make 0 1 0 "<a@x>" *paa-art* '("fn.test") "o" "s" "e" 1 5))

; The exec path on the live generic under the attachment: a clear, two
; seals, the intern of *paa-w* (a third seal, handle 2), the materialization
; by handle, a read of handle 0 after the later seals, the count.
(defun fn-paa-smoke (fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard-hints (("Goal" :in-theory (enable fn-record-p fn-record-payloadp)))))
  (let* ((fn-arena (fn-arena-clear fn-arena))
         (fn-arena (fn-arn-seal-many '((1 2 3) (4 5)) fn-arena)))
    (mv-let (held fn-arena)
      (fn-cat-intern-list *paa-w* nil 0 fn-arena)
      (let ((result (list (fn-arena-count fn-arena)
                          (fn-record-payload held)
                          (fn-hf-octets (fn-held-facts held))
                          (fn-arena-payload-len (fn-record-payload held) fn-arena)
                          (equal (fn-held-wire-of held fn-arena) *paa-w*)
                          (fn-arena-payload 0 fn-arena)
                          (fn-arena-get 1 1 fn-arena))))
        (mv result fn-arena)))))

(value-triple (fn-paa-smoke fn-arena) :stobjs-out '(nil fn-arena))

(assert-event (mv-let (result fn-arena) (fn-paa-smoke fn-arena)
                (mv (equal result (list 3 2 (len *paa-art*) (len *paa-art*) t '(1 2 3) 5))
                    fn-arena))
              :stobjs-out '(nil fn-arena))
