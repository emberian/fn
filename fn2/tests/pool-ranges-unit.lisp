; R6a1 range primitives: each against its per-byte meaning, the refusals
; (wrong owner, out of bounds), compare across two owners, the CR LF scan,
; and drop-prefix as a resumable continuation.
(in-package "ACL2")
(include-book "../books/pool-ranges")
(include-book "std/util/bstar" :dir :system)

(defun fn2-prt-write (slot gen bytes idx fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil))
  (if (atom bytes) fn2-pool
    (mv-let (code fn2-pool) (fn2-pool-write slot gen idx (car bytes) 1 10 3 fn2-pool)
      (declare (ignore code))
      (fn2-prt-write slot gen (cdr bytes) (+ 1 idx) fn2-pool))))
(defun fn2-prt-read (slot gen idx n okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil :measure (nfix n)))
  (if (zp n) nil
    (mv-let (code byte) (fn2-pool-read slot gen idx okind oslot ogen fn2-pool)
      (declare (ignore code))
      (cons byte (fn2-prt-read slot gen (+ 1 idx) (- n 1) okind oslot ogen fn2-pool)))))
(defun fn2-prt-fnv (hash bytes)
  (declare (xargs :verify-guards nil))
  (if (atom bytes) hash (fn2-prt-fnv (fn2-fnv-step hash (car bytes)) (cdr bytes))))

(defconst *fn2-prt-text* '(71 82 79 85 80 13 10 65 82 84 13 10 80 79))  ; "GROUP\r\nART\r\nPO"
(defun fn2-prt-run (fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil))
  (b* ((fn2-pool (fn2-pool-init '((4 . 64) (2 . 256)) 5 20 fn2-pool))
       ((mv & a ag fn2-pool) (fn2-pool-reserve 0 1 10 3 fn2-pool))        ; owner (1 10 3)
       ((mv & b bg fn2-pool) (fn2-pool-reserve 0 1 10 3 fn2-pool))
       ((mv & c cg fn2-pool) (fn2-pool-reserve 0 2 11 4 fn2-pool))        ; another owner (2 11 4)
       (fn2-pool (fn2-prt-write a ag *fn2-prt-text* 0 fn2-pool))
       ; scan: the first CR LF ends GROUP at 5; the byte 65 is at 7; absent -> len
       ((mv c1 crlf) (fn2-pool-scan a ag 0 14 *fn2-pool-scan-crlf* 1 10 3 fn2-pool))
       ((mv & at-a) (fn2-pool-scan a ag 0 14 65 1 10 3 fn2-pool))
       ((mv & none) (fn2-pool-scan a ag 0 14 0 1 10 3 fn2-pool))
       ((mv & crlf2) (fn2-pool-scan a ag 7 7 *fn2-pool-scan-crlf* 1 10 3 fn2-pool))
       ; a CR at the range's last byte is not a line end
       ((mv & cr-edge) (fn2-pool-scan a ag 0 6 *fn2-pool-scan-crlf* 1 10 3 fn2-pool))
       ; fold = the per-byte FNV over the same bytes
       ((mv cf h) (fn2-pool-fold a ag 0 14 *fn2-fnv-offset-basis* 1 10 3 fn2-pool))
       ; copy GROUP\r\n into b, then compare across owners after copying into c's? (c is another owner)
       ((mv cc fn2-pool) (fn2-pool-copy-range a ag 0 b bg 0 7 1 10 3 fn2-pool))
       (copied (fn2-prt-read b bg 0 7 1 10 3 fn2-pool))
       ((mv cw fn2-pool) (fn2-pool-copy-range a ag 0 c cg 0 7 1 10 3 fn2-pool))   ; refused: c is not ours
       ((mv cmp1 r1 i1) (fn2-pool-compare a ag 0 1 10 3 b bg 0 1 10 3 7 fn2-pool))
       ((mv cmp2 r2 i2) (fn2-pool-compare a ag 7 1 10 3 b bg 0 1 10 3 3 fn2-pool))
       ((mv cmp3 & &) (fn2-pool-compare a ag 0 1 10 3 c cg 0 1 10 3 1 fn2-pool))  ; c's owner is not (1 10 3)
       ((mv cb fn2-pool) (fn2-pool-copy-range a ag 10 b bg 0 7 1 10 3 fn2-pool))   ; past a's fill
       ; overlapping move within one slot (to a higher offset): bytes 0-4 -> 2-6
       ((mv co fn2-pool) (fn2-pool-copy-range b bg 0 b bg 2 5 1 10 3 fn2-pool))
       (moved (fn2-prt-read b bg 0 7 1 10 3 fn2-pool))
       ; drop the consumed "GROUP\r\n" (7 bytes) of a in steps of 3: :more, :more, :ok
       ((mv d1 k1 fn2-pool) (fn2-pool-drop-prefix a ag 7 0 3 1 10 3 fn2-pool))
       ((mv d2 k2 fn2-pool) (fn2-pool-drop-prefix a ag 7 k1 3 1 10 3 fn2-pool))
       ((mv d3 k3 fn2-pool) (fn2-pool-drop-prefix a ag 7 k2 3 1 10 3 fn2-pool))
       (tail (fn2-prt-read a ag 0 7 1 10 3 fn2-pool))
       (a-fill (fn2-pool-slot-fill a fn2-pool)))
    (mv (list :scan (list c1 crlf at-a none crlf2 cr-edge)
              :fold (list cf (equal h (fn2-prt-fnv *fn2-fnv-offset-basis* *fn2-prt-text*)))
              :copy (list cc copied cw cb)
              :compare (list cmp1 r1 i1 cmp2 r2 i2 cmp3)
              :overlap (list co moved)
              :drop (list d1 k1 d2 k2 d3 k3 tail a-fill))
        fn2-pool)))
(defun fn2-prt ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-pool (mv-let (r fn2-pool) (fn2-prt-run fn2-pool) r)))
(defconst *fn2-prt-expected*
  '(:scan (:ok 5 7 14 3 6)
    :fold (:ok t)
    :copy (:ok (71 82 79 85 80 13 10) :owner :bounds)
    :compare (:ok :equal 7 :ok :less 0 :owner)
    :overlap (:ok (71 82 71 82 79 85 80))
    :drop (:more 3 :more 6 :ok 7 (65 82 84 13 10 80 79) 7)))
(assert-event (equal (fn2-prt) *fn2-prt-expected*))
(value-triple (cw "POOL RANGES: scan (byte, CR LF, edge), fold = per-byte FNV, copy (refusals, overlap), compare across owners, drop-prefix continuation PASS~%"))
