; The existing locator events are stronger than v7's approved formulas;
; retain those proofs and give their entire actual statements teeth.
(in-package "ACL2")
(include-book "log-locator")
(include-book "defkeystone")

(defthm fn-locp-of-make
  (implies (and (unsigned-byte-p 64 seg)
                (unsigned-byte-p 32 off)
                (unsigned-byte-p 32 len))
           (fn-locp (mv-nth 0 (fn-loc-make seg off len))
                    (mv-nth 1 (fn-loc-make seg off len))))
  :rule-classes nil
  :hints (("Goal" :use fn-loc-accessors-of-make)))

(defteeth fn-loc-accessors-of-make
  :claim (((segment (unsigned-byte-p 64 seg)) (offset (unsigned-byte-p 32 off)) (length (unsigned-byte-p 32 len)))
    (mv-let (loc0 loc1) (fn-loc-make seg off len)
               (and (fn-locp loc0 loc1)
                    (equal (fn-loc-segment loc0 loc1) seg)
                    (equal (fn-loc-offset loc0 loc1) off)
                    (equal (fn-loc-len loc0 loc1) len))))
  :subject fn-loc-make
  :witness ((seg 1) (off 2) (len 3))
  :breaks ((segment ((seg -1) (off 2) (len 3)) :logical "outside the omitted locator width guard")
(offset ((seg 1) (off -1) (len 3)) :logical "outside the omitted locator width guard")
(length ((seg 1) (off 2) (len 4294967296)) :logical "outside the omitted locator width guard"))
  :mutations ((codec (:conclusion (mv-let (loc0 loc1) (fn-loc-make seg off len)
               (and (fn-locp loc0 loc1)
                    (equal (fn-loc-segment loc0 loc1) seg)
                    (equal (fn-loc-offset loc0 loc1) (+ 1 off))
                    (equal (fn-loc-len loc0 loc1) len))))
               ((seg 1) (off 2) (len 3)) :fault "offset decoder shifts the served range by one")))

(defteeth fn-locp-of-make
  :claim (((segment (unsigned-byte-p 64 seg)) (offset (unsigned-byte-p 32 off)) (length (unsigned-byte-p 32 len)))
    (fn-locp (mv-nth 0 (fn-loc-make seg off len))
                    (mv-nth 1 (fn-loc-make seg off len))))
  :subject fn-loc-make
  :witness ((seg 1) (off 2) (len 3))
  :breaks ((segment ((seg 18446744073709551616) (off 2) (len 3)) :logical "outside the omitted locator width guard")
(offset ((seg 1) (off 4294967296) (len 3)) :logical "outside the omitted locator width guard")
(length ((seg 1) (off 2) (len 18446744073709551616)) :logical "outside the omitted locator width guard"))
  :mutations ((codec (:conclusion (fn-locp (mv-nth 0 (fn-loc-make seg off len))
                    (+ 18446744073709551616 (mv-nth 1 (fn-loc-make seg off len)))))
               ((seg 1) (off 2) (len 3)) :fault "assembler overflows the packed u64 word")))

(defteeth fn-loc-make-of-accessors
  :claim (((locator (fn-locp loc0 loc1)))
    (and (unsigned-byte-p 32 (fn-loc-offset loc0 loc1))
                  (unsigned-byte-p 32 (fn-loc-len loc0 loc1))
                  (equal (fn-loc-make (fn-loc-segment loc0 loc1)
                                      (fn-loc-offset loc0 loc1)
                                      (fn-loc-len loc0 loc1))
                         (mv loc0 loc1))))
  :subject fn-loc-make
  :witness ((loc0 1) (loc1 8589934595))
  :breaks ((locator ((loc0 -1) (loc1 0)) :logical "negative segment is outside the locator guard"))
  :mutations ((codec (:conclusion (and (unsigned-byte-p 32 (fn-loc-offset loc0 loc1))
                  (unsigned-byte-p 32 (fn-loc-len loc0 loc1))
                  (equal (fn-loc-make (fn-loc-segment loc0 loc1)
                                      (fn-loc-offset loc0 loc1)
                                      (fn-loc-len loc0 loc1))
                         (mv (+ 1 loc0) loc1))))
               ((loc0 1) (loc1 8589934595)) :fault "reconstructor changes the durable segment id")))

(defteeth-check (fn-loc-accessors-of-make fn-locp-of-make fn-loc-make-of-accessors))
