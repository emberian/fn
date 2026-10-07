; fn: the payload arena's PAGED implementation, `fn-arena-paged' (D27; lane
; arena-offheap 2026-09-27, stage 1; recover-memory-2's packet P1; derived
; from one declaration, lane s-vocab 2026-10-07).
;
; `fn-arena-bytes' (books/payload-arena-bytes.lisp) keeps every payload in
; ONE resizable byte array and doubles it when full: on the 10k x 32 KiB
; fixture the open's 333.6 MB of payloads sat in a 512 MiB array, and at the
; last doubling the old 256 MiB array and the new 512 MiB one were live
; together (recover-memory-2's record, lane/recover-memory-2 655867c9b, section 3).
; This implementation keeps the payloads in fixed pool pages, reached through
; a two-level directory, and grows by adding one page: a sealed octet never
; moves, a seal never copies an older payload, growth allocates one pool page
; (and the directory's pointers), so the arena's footprint is its payload
; octets plus under one page, and nothing is live twice.
;
; It is ONE `def-representation' declaration (books/def-representation.lisp:
; `:paged t', the :octets vocabulary).  The geometry is the generator's, the
; one every paged instance has: a row page of 256 handles (an offset and a
; length column), pool pages of 16384 octets (`*adt-pg-octets*', the page
; store's page size, so a frame pool bounds the arena in the same pages), a
; table of 64 pages to a table page.  The relation, the page invariant, every
; {CORRESPONDENCE}, {PRESERVED} and {GUARD-THM} obligation, and the three
; executables of the vocabulary (the length and inner-octet reads over the
; directory; a seal copying a source buffer's cells straight into the pool
; pages at the fill, no octet list) are the generator's, proved once over the
; schema (books/def-representation-paged.lisp, -lib.lisp).
;
; The logical side is `fn-arena-bytes''s, verbatim (`fn-arena$ap',
; `create-fn-arena$a', the eight `fn-arena$a-*'), given as :model, so
; `(attach-stobj fn-arena fn-arena-paged)' (books/payload-arena-attach.lisp)
; makes the generic (books/payload-arena.lisp) execute here while every
; certificate above it stays the generic's.  The export list is the eight
; exports of the arena, in the arena's order, without NAME-RESERVE.
; No `skip-proofs'.

(in-package "ACL2")
(include-book "payload-arena-bytes")

;; The two rules the arena book withdraws from includers; the obligations
;; below read them.
(local (in-theory (enable (:rewrite fn-arn-payload-listp-nth)
                          (:rewrite fn-arn-payload-listp-true-listp))))

; The theorems the generator's proofs read the logical side through, all
; about lists (as in books/payload-arena-bytes.lisp): the recognizer is the
; scalar sequence of octet lists, a source buffer is a list of octets.
(local
 (defthm fn-arp-octet-listp-is-adt-octetsp
   (equal (fn-cbor-octet-listp x) (adt-octetsp x))
   :hints (("Goal" :in-theory (enable adt-octetsp fn-cbor-octet-listp fn-cbor-octetp
                                      unsigned-byte-p)))))

(local
 (defthm fn-arp-recognizer-is-the-scalar-sequence
   (equal (fn-arena$ap x) (adt-scalar-seq-p '(:octets) x))
   :hints (("Goal" :in-theory (enable fn-arena$ap fn-arn-payload-listp adt-scalar-seq-p adt-val-okp
                                      fn-arp-octet-listp-is-adt-octetsp)))))

(local
 (defthm fn-arp-source-octets-are-adt-octets
   (implies (fn-octets-p x) (adt-octetsp x))
   :hints (("Goal" :in-theory (enable fn-oct-octets-p-is-octet-listp
                                      fn-arp-octet-listp-is-adt-octetsp)))))

(def-representation fn-arena-paged (payload :octets) :scalar t :paged t
  :source fn-octets
  :model (:recognizer fn-arena$ap :creator create-fn-arena$a)
  :lemmas (fn-arp-recognizer-is-the-scalar-sequence fn-arp-octet-listp-is-adt-octetsp
           fn-arp-source-octets-are-adt-octets
           fn-oct-nth-is-nth fn-oct-snoc-is-append fn-oct-list-is-identity
           fn-oct-slice-list-is-take-nthcdr)
  :exports ((count :logic fn-arena$a-count)
            (payload-len :logic fn-arena$a-payload-len)
            (inner-get :as fn-arena-paged-get :logic fn-arena$a-get)
            (get :as fn-arena-paged-payload :logic fn-arena$a-payload)
            (append :as fn-arena-paged-seal-list :logic fn-arena$a-seal-list)
            (seal-buffer :logic fn-arena$a-seal-buffer)
            (clear :logic fn-arena$a-clear)
            (seal-range :logic fn-arena$a-seal-range)))

;; The generated rewrite rules of the exports (each says what the export
;; computes in the list vocabulary) are withdrawn from includers: the hand
;; implementation exported none, and the books above state the arena through
;; `fn-arena$a-*' (books/payload-arena-extent.lisp's correspondence proofs
;; compare the child's `fn-arena$a-seal-range' with take-of-nthcdr).  An
;; includer that wants one enables it where it is used.
(in-theory (disable fn-arena-paged-count-is-len fn-arena-paged-payload-len-is-len-of-nth
                    fn-arena-paged-get-is-nth-of-nth fn-arena-paged-payload-is-nth
                    fn-arena-paged-seal-list-is-append fn-arena-paged-clear-is-nil
                    fn-arena-paged-seal-buffer-is-source fn-arena-paged-seal-range-is-slice
                    fn-arena-pagedp-is-scalar-seq-p))
