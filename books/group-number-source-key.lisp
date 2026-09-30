; Logical leading-one binary key. Never executed on the served path.
(in-package "ACL2")
(include-book "group-number-source-update")
(local (include-book "arithmetic-5/top" :dir :system))
(defthm fn-gns-bit-is-binary
  (or (equal (fn-gns-bit group pos bit) 0) (equal (fn-gns-bit group pos bit) 1))
  :rule-classes nil)
(defun fn-gns-group-key (group pos bit)
  (declare (xargs :guard t
                  :measure (nfix (+ (* 8 (- (length group) (nfix pos))) (- 8 (nfix bit))))))
  (if (not (and (stringp group) (natp pos) (< pos (length group)) (natp bit) (< bit 8))) 1
    (+ (fn-gns-bit group pos bit)
       (* 2 (fn-gns-group-key group (if (= bit 7) (1+ pos) pos)
                              (if (= bit 7) 0 (1+ bit)))))))
(defthm fn-gns-group-key-positive
  (posp (fn-gns-group-key group pos bit))
  :hints (("Goal" :induct (fn-gns-group-key group pos bit))))
(defthm fn-gns-group-get-is-generic-trie
  (implies (and (stringp group) (natp pos) (<= pos (length group)) (natp bit) (< bit 8))
           (equal (fn-gns-group-get group pos bit node)
                  (fn-gnix-get (fn-gns-group-key group pos bit) node)))
  :hints (("Goal" :induct (fn-gns-group-get group pos bit node)
           :in-theory (disable fn-gns-bit)
           :expand ((fn-gns-group-key group pos bit)))
          ("Subgoal *1/2" :use ((:instance fn-gns-bit-is-binary)))))
(defthm fn-gns-group-set-is-generic-trie
  (implies (and (stringp group) (natp pos) (<= pos (length group)) (natp bit) (< bit 8))
           (equal (fn-gns-group-set group pos bit value node)
                  (fn-gnix-set (fn-gns-group-key group pos bit) value node)))
  :hints (("Goal" :induct (fn-gns-group-set group pos bit value node)
           :in-theory (e/d (fn-gnix-set) (fn-gns-bit))
           :expand ((fn-gns-group-key group pos bit)))
          ("Subgoal *1/2" :use ((:instance fn-gns-bit-is-binary)))
          ("Subgoal *1/3" :use ((:instance fn-gns-bit-is-binary)))))

(defthm fn-gns-byte-bits-reassemble
  (implies (and (natp code) (< code 256))
           (equal (+ (* 1 (mod (floor code 1) 2)) (* 2 (mod (floor code 2) 2)) (* 4 (mod (floor code 4) 2)) (* 8 (mod (floor code 8) 2)) (* 16 (mod (floor code 16) 2)) (* 32 (mod (floor code 32) 2)) (* 64 (mod (floor code 64) 2)) (* 128 (mod (floor code 128) 2))) code))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable (tau-system)) :cases ((equal code 0) (equal code 1) (equal code 2) (equal code 3) (equal code 4) (equal code 5) (equal code 6) (equal code 7) (equal code 8) (equal code 9) (equal code 10) (equal code 11) (equal code 12) (equal code 13) (equal code 14) (equal code 15) (equal code 16) (equal code 17) (equal code 18) (equal code 19) (equal code 20) (equal code 21) (equal code 22) (equal code 23) (equal code 24) (equal code 25) (equal code 26) (equal code 27) (equal code 28) (equal code 29) (equal code 30) (equal code 31) (equal code 32) (equal code 33) (equal code 34) (equal code 35) (equal code 36) (equal code 37) (equal code 38) (equal code 39) (equal code 40) (equal code 41) (equal code 42) (equal code 43) (equal code 44) (equal code 45) (equal code 46) (equal code 47) (equal code 48) (equal code 49) (equal code 50) (equal code 51) (equal code 52) (equal code 53) (equal code 54) (equal code 55) (equal code 56) (equal code 57) (equal code 58) (equal code 59) (equal code 60) (equal code 61) (equal code 62) (equal code 63) (equal code 64) (equal code 65) (equal code 66) (equal code 67) (equal code 68) (equal code 69) (equal code 70) (equal code 71) (equal code 72) (equal code 73) (equal code 74) (equal code 75) (equal code 76) (equal code 77) (equal code 78) (equal code 79) (equal code 80) (equal code 81) (equal code 82) (equal code 83) (equal code 84) (equal code 85) (equal code 86) (equal code 87) (equal code 88) (equal code 89) (equal code 90) (equal code 91) (equal code 92) (equal code 93) (equal code 94) (equal code 95) (equal code 96) (equal code 97) (equal code 98) (equal code 99) (equal code 100) (equal code 101) (equal code 102) (equal code 103) (equal code 104) (equal code 105) (equal code 106) (equal code 107) (equal code 108) (equal code 109) (equal code 110) (equal code 111) (equal code 112) (equal code 113) (equal code 114) (equal code 115) (equal code 116) (equal code 117) (equal code 118) (equal code 119) (equal code 120) (equal code 121) (equal code 122) (equal code 123) (equal code 124) (equal code 125) (equal code 126) (equal code 127) (equal code 128) (equal code 129) (equal code 130) (equal code 131) (equal code 132) (equal code 133) (equal code 134) (equal code 135) (equal code 136) (equal code 137) (equal code 138) (equal code 139) (equal code 140) (equal code 141) (equal code 142) (equal code 143) (equal code 144) (equal code 145) (equal code 146) (equal code 147) (equal code 148) (equal code 149) (equal code 150) (equal code 151) (equal code 152) (equal code 153) (equal code 154) (equal code 155) (equal code 156) (equal code 157) (equal code 158) (equal code 159) (equal code 160) (equal code 161) (equal code 162) (equal code 163) (equal code 164) (equal code 165) (equal code 166) (equal code 167) (equal code 168) (equal code 169) (equal code 170) (equal code 171) (equal code 172) (equal code 173) (equal code 174) (equal code 175) (equal code 176) (equal code 177) (equal code 178) (equal code 179) (equal code 180) (equal code 181) (equal code 182) (equal code 183) (equal code 184) (equal code 185) (equal code 186) (equal code 187) (equal code 188) (equal code 189) (equal code 190) (equal code 191) (equal code 192) (equal code 193) (equal code 194) (equal code 195) (equal code 196) (equal code 197) (equal code 198) (equal code 199) (equal code 200) (equal code 201) (equal code 202) (equal code 203) (equal code 204) (equal code 205) (equal code 206) (equal code 207) (equal code 208) (equal code 209) (equal code 210) (equal code 211) (equal code 212) (equal code 213) (equal code 214) (equal code 215) (equal code 216) (equal code 217) (equal code 218) (equal code 219) (equal code 220) (equal code 221) (equal code 222) (equal code 223) (equal code 224) (equal code 225) (equal code 226) (equal code 227) (equal code 228) (equal code 229) (equal code 230) (equal code 231) (equal code 232) (equal code 233) (equal code 234) (equal code 235) (equal code 236) (equal code 237) (equal code 238) (equal code 239) (equal code 240) (equal code 241) (equal code 242) (equal code 243) (equal code 244) (equal code 245) (equal code 246) (equal code 247) (equal code 248) (equal code 249) (equal code 250) (equal code 251) (equal code 252) (equal code 253) (equal code 254) (equal code 255)))))

(defthm fn-gns-character-is-byte
  (implies (and (stringp group) (natp pos) (< pos (length group)))
           (and (natp (char-code (char group pos)))
                (< (char-code (char group pos)) 256)))
  :rule-classes nil)

(defthm fn-gns-group-key-byte
  (implies (and (stringp group) (natp pos) (< pos (length group)))
           (equal (fn-gns-group-key group pos 0)
                  (+ (char-code (char group pos))
                     (* 256 (fn-gns-group-key group (1+ pos) 0)))))
  :hints (("Goal"
           :in-theory (union-theories (theory 'minimal-theory)
             '(fn-gns-bit natp nfix
               (:executable-counterpart expt) (:executable-counterpart binary-*)
               (:executable-counterpart binary-+)
               (:executable-counterpart floor) (:executable-counterpart mod)
               associativity-of-+ commutativity-of-+ commutativity-2-of-+
               associativity-of-* commutativity-of-*
               distributivity normalize-addends normalize-factors-gather-exponents))
           :use ((:instance fn-gns-character-is-byte)
                 (:instance fn-gns-byte-bits-reassemble
                            (code (char-code (char group pos)))))
           :expand ((fn-gns-group-key group pos 0) (fn-gns-group-key group pos 1) (fn-gns-group-key group pos 2) (fn-gns-group-key group pos 3) (fn-gns-group-key group pos 4) (fn-gns-group-key group pos 5) (fn-gns-group-key group pos 6) (fn-gns-group-key group pos 7) ))))
(defun fn-gns-key-decode (key)
  (declare (xargs :guard t :measure (nfix key)))
  (if (or (not (natp key)) (<= key 1)) nil
    (cons (code-char (mod key 256)) (fn-gns-key-decode (floor key 256)))))
(local
 (defun fn-gns-string-induct (group pos)
   (declare (xargs :guard t :measure (nfix (- (length group) (nfix pos)))))
   (if (and (stringp group) (natp pos) (< pos (length group)))
       (fn-gns-string-induct group (1+ pos))
     nil)))
(defthm fn-gns-key-at-end
  (implies (and (stringp group) (natp pos) (<= (length group) pos))
           (equal (fn-gns-group-key group pos 0) 1))
  :hints (("Goal" :expand ((fn-gns-group-key group pos 0)))))
(defthm fn-gns-nthcdr-at-end
  (implies (and (true-listp xs) (natp pos) (<= (len xs) pos))
           (equal (nthcdr pos xs) nil)))
(defthm fn-gns-nthcdr-split
  (implies (and (true-listp xs) (natp pos) (< pos (len xs)))
           (equal (nthcdr pos xs) (cons (nth pos xs) (nthcdr (1+ pos) xs))))
  :rule-classes nil
  :hints (("Goal" :induct (nthcdr pos xs))))
(defthm fn-gns-key-decode-of-group-key
  (implies (and (stringp group) (natp pos) (<= pos (length group)))
           (equal (fn-gns-key-decode (fn-gns-group-key group pos 0))
                  (nthcdr pos (coerce group 'list))))
  :hints (("Goal" :induct (fn-gns-string-induct group pos)
           :in-theory (e/d (fn-gns-key-decode char)
                           (fn-gns-group-key fn-gns-bit nthcdr)) )
          ("Subgoal *1/1" :use ((:instance fn-gns-nthcdr-split
                                           (xs (coerce group 'list)))))))
(defthm fn-gns-group-key-injective
  (implies (and (stringp a) (stringp b))
           (equal (equal (fn-gns-group-key a 0 0) (fn-gns-group-key b 0 0))
                  (equal a b)))
  :hints (("Goal" :use ((:instance coerce-inverse-2 (x a))
                         (:instance coerce-inverse-2 (x b))
                         (:instance fn-gns-key-decode-of-group-key (group a) (pos 0))
                         (:instance fn-gns-key-decode-of-group-key (group b) (pos 0)))
           :in-theory (disable fn-gns-group-key fn-gns-key-decode
                               fn-gns-key-decode-of-group-key coerce-inverse-2))))
(local
 (defthm fn-gns-group-get-of-set-strings
  (implies (and (stringp a) (stringp b))
           (equal (fn-gns-group-get a 0 0 (fn-gns-group-set b 0 0 value root))
                  (if (equal a b) value (fn-gns-group-get a 0 0 root))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-gns-group-get fn-gns-group-set
                                     fn-gns-group-key fn-gnix-get fn-gnix-set)))))
(defthm fn-gns-group-get-of-set
  (implies (or (stringp a) (stringp b))
           (equal (fn-gns-group-get a 0 0 (fn-gns-group-set b 0 0 value root))
                  (if (equal a b) value (fn-gns-group-get a 0 0 root))))
  :hints (("Goal" :use ((:instance fn-gns-group-get-of-set-strings))
           :cases ((stringp a) (stringp b)))))
; Logical key construction is opened only in its selected proofs.
(in-theory (disable fn-gns-group-key fn-gns-key-decode
                    fn-gns-group-get-is-generic-trie
                    fn-gns-group-set-is-generic-trie))
