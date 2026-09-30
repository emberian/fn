; Exact parser-piece shape bridge from the original OBC source.
(in-package "ACL2")
(include-book "over-row-pieces")
(include-book "legacy-parser-header")

(local
 (defthm fn-obc-at-is-nth
   (equal (fn-lpc-at i x) (nth (nfix i) x))
   :hints (("Goal" :in-theory (enable fn-lpc-at fn-ag-car fn-ag-cdr nth)))))

; Bounds are carried by the parser; this bridge does not inspect a source
; byte or validate its complete header. Keep the free bound local.
(local
 (defthm fn-obc-span-piece-shape
   (implies (and (fn-lpc-span-bound-p span h pin bound)
                 (natp h) (< h (fn-arena-count fn-arena))
                 (<= (nfix bound) (fn-arena-payload-len h fn-arena)))
            (fn-npw-partp (fn-obc-span-piece span) fn-arena))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-obc-span-piece fn-lpc-span-bound-p
                             fn-npw-partp fn-lpc-at)
                            (fn-arena-count-is-len
                             fn-arena-payload-len-is-len-nth))))))

(local
 (defthm fn-obc-digit-run-is-octets
   (implies (and (true-listp bytes) (fn-nntp-decimal-tokenp bytes))
            (fn-cbor-octet-listp bytes))
   :hints (("Goal" :induct (fn-nntp-decimal-tokenp bytes)
            :in-theory (enable fn-nntp-decimal-tokenp fn-nntp-decimal-digitp
                               fn-cbor-octet-listp fn-cbor-octetp)))))

(local
 (defthm fn-obc-number-piece-shape
   (fn-npw-partp (fn-nntp-decimal-field number) fn-arena)
   :hints (("Goal" :in-theory
            (enable fn-npw-partp fn-nntp-decimal-field
                    fn-nntp-decimal-tokenp fn-nntp-decimal-digitp)))))

(local
 (defthm fn-obc-parser-field-piece-has-shape
   (implies (and (natp k) (fn-lpc-ready-p parser fn-arena)
                 (fn-lpc-cursor-bounds-p parser))
            (fn-npw-partp (fn-obc-span-piece (fn-lpc-field parser k)) fn-arena))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-lpc-field-retains-pinned-source (s parser))
                  (:instance fn-obc-span-piece-shape
                             (span (fn-lpc-field parser k))
                             (h (fn-lpc-at 0 parser))
                             (pin (fn-lpc-at 2 parser))
                             (bound (fn-lpc-at 3 parser))))
            :in-theory
            (e/d (fn-lpc-ready-p)
                 (fn-lpc-field fn-lpc-at fn-lpc-cursor-bounds-p
                  fn-lpc-span-bound-p fn-obc-span-piece fn-npw-partp
                  fn-obc-span-piece-shape fn-lpc-field-retains-pinned-source
                  fn-arena-count-is-len fn-arena-payload-len-is-len-nth))))))

(local
 (defthm fn-obc-decimal-piece-shape
   (implies (natp n) (fn-npw-partp (list :decimal n nil) fn-arena))
   :hints (("Goal" :in-theory (enable fn-npw-partp)))))

(local
 (defthm fn-obc-fixed-separators-shape
   (and (fn-npw-partp '(9) fn-arena) (fn-npw-partp '(13 10) fn-arena))
   :hints (("Goal" :in-theory (enable fn-npw-partp)))))

(defthm fn-obc-parser-pieces-have-shape
  (implies (and (fn-lpc-ready-p parser fn-arena)
                (fn-lpc-cursor-bounds-p parser))
           (fn-npw-piecesp (fn-obc-parser-pieces number parser) fn-arena))
  :hints (("Goal" :in-theory
           (e/d (fn-obc-parser-pieces fn-npw-piecesp)
                (fn-npw-partp fn-obc-span-piece fn-lpc-field fn-lpc-ready-p
                 fn-lpc-at fn-lpc-body-lines fn-lpc-cursor-bounds-p
                 fn-nntp-decimal-field)))))

