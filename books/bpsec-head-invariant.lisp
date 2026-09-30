; Carried CBOR-head profile for the actual ASB parser's typed field boundary.
; This ghost invariant is never a served whole-state validation.
(in-package "ACL2")
(include-book "bpsec-head")

(defun fn-bps-head-profilep (head)
  (declare (xargs :guard t))
  (and (fn-bps-headp head)
       (if (member-equal (fn-bps-field 1 head) '(:argument :ready))
           (member-equal (fn-bps-field 2 head) '(0 2 3 4)) t)
       (if (eq (fn-bps-field 1 head) :argument)
           (and (member-equal (fn-bps-field 3 head) '(24 25 26 27))
                (< 0 (nfix (fn-bps-field 4 head)))) t)
       (if (eq (fn-bps-field 1 head) :ready)
           (equal (fn-bps-field 4 head) 0) t)))

(defun fn-bps-ready-headp (value)
  (declare (xargs :guard t))
  (and (true-listp value) (equal (len value) 2)
       (member-equal (fn-bps-field 0 value) '(0 2 3 4))
       (fn-bps-uintp (fn-bps-field 1 value))))

(defthm fn-bps-head-start-establishes-profile
  (fn-bps-head-profilep (fn-bps-head-start)))

(local
 (defthm fn-bps-octet-head-fields-by-definition
   (implies (fn-cbor-octetp octet)
            (and (natp (floor octet 32)) (< (floor octet 32) 8)
                 (natp (mod octet 32)) (< (mod octet 32) 32)))
   :hints (("Goal" :cases ((equal octet 0) (equal octet 1) (equal octet 2) (equal octet 3) (equal octet 4) (equal octet 5) (equal octet 6) (equal octet 7) (equal octet 8) (equal octet 9) (equal octet 10) (equal octet 11) (equal octet 12) (equal octet 13) (equal octet 14) (equal octet 15) (equal octet 16) (equal octet 17) (equal octet 18) (equal octet 19) (equal octet 20) (equal octet 21) (equal octet 22) (equal octet 23) (equal octet 24) (equal octet 25) (equal octet 26) (equal octet 27) (equal octet 28) (equal octet 29) (equal octet 30) (equal octet 31) (equal octet 32) (equal octet 33) (equal octet 34) (equal octet 35) (equal octet 36) (equal octet 37) (equal octet 38) (equal octet 39) (equal octet 40) (equal octet 41) (equal octet 42) (equal octet 43) (equal octet 44) (equal octet 45) (equal octet 46) (equal octet 47) (equal octet 48) (equal octet 49) (equal octet 50) (equal octet 51) (equal octet 52) (equal octet 53) (equal octet 54) (equal octet 55) (equal octet 56) (equal octet 57) (equal octet 58) (equal octet 59) (equal octet 60) (equal octet 61) (equal octet 62) (equal octet 63) (equal octet 64) (equal octet 65) (equal octet 66) (equal octet 67) (equal octet 68) (equal octet 69) (equal octet 70) (equal octet 71) (equal octet 72) (equal octet 73) (equal octet 74) (equal octet 75) (equal octet 76) (equal octet 77) (equal octet 78) (equal octet 79) (equal octet 80) (equal octet 81) (equal octet 82) (equal octet 83) (equal octet 84) (equal octet 85) (equal octet 86) (equal octet 87) (equal octet 88) (equal octet 89) (equal octet 90) (equal octet 91) (equal octet 92) (equal octet 93) (equal octet 94) (equal octet 95) (equal octet 96) (equal octet 97) (equal octet 98) (equal octet 99) (equal octet 100) (equal octet 101) (equal octet 102) (equal octet 103) (equal octet 104) (equal octet 105) (equal octet 106) (equal octet 107) (equal octet 108) (equal octet 109) (equal octet 110) (equal octet 111) (equal octet 112) (equal octet 113) (equal octet 114) (equal octet 115) (equal octet 116) (equal octet 117) (equal octet 118) (equal octet 119) (equal octet 120) (equal octet 121) (equal octet 122) (equal octet 123) (equal octet 124) (equal octet 125) (equal octet 126) (equal octet 127) (equal octet 128) (equal octet 129) (equal octet 130) (equal octet 131) (equal octet 132) (equal octet 133) (equal octet 134) (equal octet 135) (equal octet 136) (equal octet 137) (equal octet 138) (equal octet 139) (equal octet 140) (equal octet 141) (equal octet 142) (equal octet 143) (equal octet 144) (equal octet 145) (equal octet 146) (equal octet 147) (equal octet 148) (equal octet 149) (equal octet 150) (equal octet 151) (equal octet 152) (equal octet 153) (equal octet 154) (equal octet 155) (equal octet 156) (equal octet 157) (equal octet 158) (equal octet 159) (equal octet 160) (equal octet 161) (equal octet 162) (equal octet 163) (equal octet 164) (equal octet 165) (equal octet 166) (equal octet 167) (equal octet 168) (equal octet 169) (equal octet 170) (equal octet 171) (equal octet 172) (equal octet 173) (equal octet 174) (equal octet 175) (equal octet 176) (equal octet 177) (equal octet 178) (equal octet 179) (equal octet 180) (equal octet 181) (equal octet 182) (equal octet 183) (equal octet 184) (equal octet 185) (equal octet 186) (equal octet 187) (equal octet 188) (equal octet 189) (equal octet 190) (equal octet 191) (equal octet 192) (equal octet 193) (equal octet 194) (equal octet 195) (equal octet 196) (equal octet 197) (equal octet 198) (equal octet 199) (equal octet 200) (equal octet 201) (equal octet 202) (equal octet 203) (equal octet 204) (equal octet 205) (equal octet 206) (equal octet 207) (equal octet 208) (equal octet 209) (equal octet 210) (equal octet 211) (equal octet 212) (equal octet 213) (equal octet 214) (equal octet 215) (equal octet 216) (equal octet 217) (equal octet 218) (equal octet 219) (equal octet 220) (equal octet 221) (equal octet 222) (equal octet 223) (equal octet 224) (equal octet 225) (equal octet 226) (equal octet 227) (equal octet 228) (equal octet 229) (equal octet 230) (equal octet 231) (equal octet 232) (equal octet 233) (equal octet 234) (equal octet 235) (equal octet 236) (equal octet 237) (equal octet 238) (equal octet 239) (equal octet 240) (equal octet 241) (equal octet 242) (equal octet 243) (equal octet 244) (equal octet 245) (equal octet 246) (equal octet 247) (equal octet 248) (equal octet 249) (equal octet 250) (equal octet 251) (equal octet 252) (equal octet 253) (equal octet 254) (equal octet 255) )
            :in-theory (e/d (fn-cbor-octetp) ((:definition floor) (:definition mod)))))))

(defthm fn-bps-head-feed-preserves-profile
  (implies (fn-bps-head-profilep head)
           (fn-bps-head-profilep (fn-bps-field 2 (fn-bps-head-feed head octet))))
  :hints (("Goal" :in-theory (e/d (fn-bps-head-profilep fn-bps-headp
                                    fn-bps-head-feed fn-bps-field fn-bps-uintp
                                    fn-cbor-octetp fn-bps-head-width fn-bps-head-minimum)
                           ((:definition floor) (:definition mod))))))

(defthm fn-bps-head-feed-ready-is-typed-uint64
  (implies (and (fn-bps-head-profilep head)
                (eq (fn-bps-field 0 (fn-bps-head-feed head octet)) :ready))
           (fn-bps-ready-headp (fn-bps-field 1 (fn-bps-head-feed head octet))))
  :hints (("Goal" :in-theory (e/d (fn-bps-head-profilep fn-bps-headp fn-bps-ready-headp
                                    fn-bps-head-feed fn-bps-field fn-bps-uintp
                                    fn-cbor-octetp fn-bps-head-width fn-bps-head-minimum)
                           ((:definition floor) (:definition mod))))))

(defthm fn-bps-head-drive-preserves-profile
  (implies (fn-bps-head-profilep head)
           (fn-bps-head-profilep (fn-bps-field 2 (fn-bps-head-drive head octets quantum))))
  :hints (("Goal" :induct (fn-bps-head-drive head octets quantum)
           :in-theory (e/d (fn-bps-head-drive fn-bps-field)
                           (fn-bps-head-profilep fn-bps-head-feed)))))

(defthm fn-bps-head-drive-ready-is-typed-uint64
  (implies (and (fn-bps-head-profilep head)
                (eq (fn-bps-field 0 (fn-bps-head-drive head octets quantum)) :ready))
           (fn-bps-ready-headp (fn-bps-field 1 (fn-bps-head-drive head octets quantum))))
  :hints (("Goal" :induct (fn-bps-head-drive head octets quantum)
           :in-theory (e/d (fn-bps-head-drive fn-bps-field)
                           (fn-bps-head-profilep fn-bps-ready-headp fn-bps-head-feed)))))
