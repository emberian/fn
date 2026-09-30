; SCN-1020: bounded decoder components and explicit old-domain regressions.
(in-package "ACL2")
(include-book "../../books/payload-window")
(include-book "deflate-inflate-vectors")
(include-book "payload-deflate-vectors")

(defconst *pwt-high-ratio* '(237 193 1 13 0 0 0 194 160 108 239 95 202 30 14 40 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 95 3))

; Historical old-ahead success at c48f7db94 is preserved by the new stored
; policy. It remains a concrete counterexample to stored/network equality.
(assert-event
 (let* ((b (fn-pzd-budget (len *pwt-high-ratio*) 93100))
        (stored (fn-zin-payload-with b nil *pwt-high-ratio* 93101))
        (wire (fn-zin-inflate-with b nil *pwt-high-ratio* 93101)))
   (and (equal (len *pwt-high-ratio*) 108)
        (equal (car stored) '(:refused :stream-ended))
        (equal (cadr stored) (make-list 93100 :initial-element 65))
        (equal (car (fn-pzd-answer (car stored) (cadr stored) 93100)) :ok)
        (equal (car wire) '(:refused :bomb))
        (equal (len (cadr wire)) 92672))))

; Failed-before terminal defect: a final stored-block header lacks LEN/NLEN.
; Recorded here against legacy decoder; updated to refusal with the fix.
(assert-event (equal (fn-pzd-decode nil '(1) 0) '(:error (:refused :truncated))))
; Trailing compressed bytes are deliberately allowed after the final block.
(assert-event (equal (fn-pzd-decode nil '(3 0 255 255) 0) '(:ok nil)))

(defun pwt-window-loop (fuel q remaining ip expected offset wanted acc peak
                       fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
  (declare (xargs :mode :program
                  :stobjs (fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
  (if (zp fuel)
      (mv (list :test-fuel) fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
    (let* ((end (min (fn-octets-len fn-octets) (+ ip 64)))
           (before (fn-zin-tout fn-zin-st)))
      (mv-let (status left next fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
        (fn-pzw-stored-chunk q remaining ip end (fn-octets-len fn-octets) expected
                             fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
        (mv-let (src count dst)
          (fn-pzw-select before (fn-zin-out-len fn-zin-out) offset wanted)
          (declare (ignore dst))
          (let* ((acc (append acc (take count (nthcdr src (fn-zin-out-list fn-zin-out)))))
                 (peak (max peak (fn-zin-out-len fn-zin-out)))
                 (remaining (fn-pzw-budget-left q remaining left))
                 (decision (fn-pzw-stored-decision status (fn-octets-len fn-octets) expected remaining
                                           (or (equal next (fn-octets-len fn-octets))
                                               (equal status '(:refused :stream-ended))) fn-zin-st)))
            (if (member-eq decision '(:resume :input))
                (pwt-window-loop (1- fuel) q remaining next expected offset wanted acc peak
                                 fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
              (mv (list decision (fn-zin-tin fn-zin-st) (fn-zin-tout fn-zin-st)
                        acc remaining peak)
                  fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))))))

(defun pwt-window-with-dict (q c expected offset wanted dict)
  (declare (xargs :mode :program))
  (with-local-stobj fn-zin-st
    (mv-let (r fn-zin-st)
      (with-local-stobj fn-octets
        (mv-let (r fn-octets fn-zin-st)
          (with-local-stobj fn-zin-win
            (mv-let (r fn-zin-win fn-octets fn-zin-st)
              (with-local-stobj fn-zin-tab
                (mv-let (r fn-zin-tab fn-zin-win fn-octets fn-zin-st)
                  (with-local-stobj fn-zin-out
                    (mv-let (r fn-zin-out fn-zin-tab fn-zin-win fn-octets fn-zin-st)
                      (let* ((fn-zin-st (fn-zin-reset fn-zin-st))
                             (fn-octets (fn-octets-from-list c fn-octets)))
                        (mv-let (fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                          (fn-pzw-initialize dict fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                          (mv-let (r fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                            (pwt-window-loop 100000 q (fn-pzd-budget (len c) expected) 0
                                             expected offset wanted nil 0
                                             fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
                            (mv r fn-zin-out fn-zin-tab fn-zin-win fn-octets fn-zin-st))))
                      (mv r fn-zin-tab fn-zin-win fn-octets fn-zin-st)))
                  (mv r fn-zin-win fn-octets fn-zin-st)))
              (mv r fn-octets fn-zin-st)))
          (mv r fn-zin-st)))
      r)))

(defun pwt-window (q c expected offset wanted)
  (declare (xargs :mode :program))
  (pwt-window-with-dict q c expected offset wanted nil))

(assert-event
 (let ((r (pwt-window 7 *pwt-high-ratio* 93100 92900 17)))
   (and (equal (car r) :decoded) (equal (nth 2 r) 93100)
        (equal (nth 3 r) (make-list 17 :initial-element 65))
        (<= (nth 1 r) 108) (<= (nth 5 r) 64))))
(assert-event
 (let ((r (pwt-window 1024 *dzv-session-z* (len *dzv-session*) 3 17)))
   (and (equal (car r) :decoded)
        (equal (nth 3 r) (take 17 (nthcdr 3 *dzv-session*)))
        (<= (nth 5 r) 64))))
(assert-event
 (let ((r (pwt-window 2 *dzv-final-z* 0 0 17)))
   (equal (car r) '(:error :length))))
(assert-event
 (and (equal (mv-list 3 (fn-pzw-select 20 64 30 10)) '(10 10 0))
      (equal (mv-list 3 (fn-pzw-select 0 64 80 10)) '(0 0 0))
      (equal (mv-list 3 (fn-pzw-select 90 64 80 17)) '(0 7 10))
      (equal (mv-list 3 (fn-pzw-select 0 64 0 0)) '(0 0 0))
      (equal (fn-pzw-decision :more 5 5 100 nil) :input)
      (equal (fn-pzw-decision '(:refused :stream-ended) 5 5 100 nil) :drain)
      (equal (fn-pzw-decision :yield 5 5 0 t) '(:error :yield))
      (equal (fn-pzw-decision :full 6 5 100 t) '(:error :length))))

; Input fragments that used to be accepted merely because they returned :more.
(assert-event (equal (car (pwt-window 7 '(1) 0 0 1)) '(:error (:refused :truncated))))
(assert-event (equal (car (pwt-window 7 '(0 0 0 255) 0 0 1)) '(:error (:refused :truncated))))
(assert-event (equal (car (pwt-window 7 '(0 0 0 255 255) 0 0 1)) :decoded))
(assert-event (equal (car (pwt-window 7 '(3 0 255 255) 0 0 1)) :decoded))

(defconst *pwt-total-domain* '(237 207 131 182 16 6 0 0 208 108 173 150 237 182 108 227 101 215 106 217 182 109 219 92 230 178 109 219 182 109 219 253 70 231 116 239 31 220 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 224 87 21 40 112 144 160 193 130 135 8 25 42 116 152 176 225 194 71 136 24 233 143 200 81 254 140 26 45 122 140 152 177 98 199 137 27 47 126 130 132 137 18 39 73 154 44 121 138 191 254 78 153 42 117 154 180 233 210 103 200 152 41 115 150 172 217 178 231 200 153 43 119 158 188 249 2 242 23 40 88 168 112 145 162 197 138 151 40 89 170 116 153 178 255 148 43 255 111 133 138 149 42 87 169 90 173 122 141 154 181 106 215 169 91 175 126 131 134 141 26 55 105 218 172 121 139 150 173 90 183 105 219 174 125 135 142 157 58 119 233 218 173 123 143 158 189 122 247 233 219 175 255 128 129 131 6 15 25 58 108 248 136 145 163 70 143 25 59 110 252 132 137 255 77 154 60 101 234 180 233 51 102 206 154 61 103 238 255 243 230 47 88 184 104 241 146 165 203 150 175 88 185 106 245 154 181 235 214 111 216 184 105 243 150 173 219 182 239 216 185 107 247 158 189 251 246 31 56 120 232 240 145 163 199 142 159 56 121 234 244 153 179 231 206 95 184 120 233 242 149 171 215 174 223 184 121 235 246 157 187 247 238 63 120 248 232 241 147 167 207 158 191 120 249 234 245 155 183 239 222 127 248 248 233 243 151 175 223 190 255 240 247 247 247 247 247 247 247 247 247 247 247 247 247 255 29 254 63 1))

; Total-length policy admits a valid high-ratio prefix followed by ordinary
; data, while keeping output private and constant-sized per call.
(assert-event
 (let ((r (pwt-window 7 *pwt-total-domain* 104096 99998 6)))
   (and (equal (car r) :decoded) (equal (nth 2 r) 104096)
        (equal (nth 3 r) '(65 65 0 1 2 3)) (<= (nth 5 r) 64))))

(assert-event
 (let ((r (pwt-window-with-dict 3 *plz-dict-block* 750 13 19 *plz-dict*)))
   (and (equal (car r) :decoded) (equal (nth 2 r) 750)
        (equal (nth 3 r) (take 19 (nthcdr 13 *plz-article*)))
        (<= (nth 5 r) 64))))
; A nonempty stored block ending in 00 00 ff ff is not a sync flush.
(assert-event
 (equal (car (pwt-window 3 '(0 4 0 251 255 0 0 255 255) 4 0 4))
        '(:error (:refused :truncated))))
(assert-event (equal (car (pwt-window 3 '(1 0 0 255 255) 0 0 1)) :decoded))
(assert-event
 (let ((r (pwt-window 3 *dzv-final-z* 104 3 17)))
   (and (equal (car r) :decoded) (equal (nth 3 r) (take 17 (nthcdr 3 *dzv-session*))))))

; Literal teeth for fn-pzw-empty-stored-block-establishes-terminal. These
; name every retained hypothesis, the omitted hypothesis's failure, and
; the complete conclusion (all octets and total output unchanged).
(defmacro pwt-terminal-conclusion (s)
  `(let* ((a (fn-zin-act ,s nil nil nil))
          (b (fn-zin-act (mv-nth 1 a) (mv-nth 2 a) (mv-nth 3 a) (mv-nth 4 a))))
     (and (equal (car a) nil) (equal (car b) nil)
          (fn-zin-stored-terminalp :more (mv-nth 1 b))
          (equal (fn-zin-tout (mv-nth 1 b)) (fn-zin-tout ,s))
          (equal (mv-nth 2 b) nil) (equal (mv-nth 3 b) nil)
          (equal (mv-nth 4 b) nil))))

(defthm pwt-terminal-positive
  (let ((s '((2 4294901760 32 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0))))
    (and (equal (fn-zin-mode s) 2) (equal (fn-zin-bits s) 4294901760)
         (equal (fn-zin-nbits s) 32) (equal (fn-zin-final s) 0)
         (pwt-terminal-conclusion s)))
  :rule-classes nil)

(defthm pwt-terminal-without-mode
  (let ((s '((13 4294901760 32 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0))))
    (and (not (equal (fn-zin-mode s) 2)) (equal (fn-zin-bits s) 4294901760)
         (equal (fn-zin-nbits s) 32) (equal (fn-zin-final s) 0)
         (not (pwt-terminal-conclusion s))))
  :rule-classes nil)

(defthm pwt-terminal-without-complement
  (let ((s '((2 0 32 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0))))
    (and (equal (fn-zin-mode s) 2) (not (equal (fn-zin-bits s) 4294901760))
         (equal (fn-zin-nbits s) 32) (equal (fn-zin-final s) 0)
         (not (pwt-terminal-conclusion s))))
  :rule-classes nil)

; Corrupted-state hypothesis removal: an extra buffered bit is retained.
(defthm pwt-terminal-without-bit-count
  (let ((s '((2 4294901760 33 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0))))
    (and (equal (fn-zin-mode s) 2) (equal (fn-zin-bits s) 4294901760)
         (not (equal (fn-zin-nbits s) 32)) (equal (fn-zin-final s) 0)
         (not (pwt-terminal-conclusion s))))
  :rule-classes nil)

(defthm pwt-terminal-without-nonfinal
  (let ((s '((2 4294901760 32 0 0 0 0 0 0 0 0 1 1 0 0 0 0 0 0 0))))
    (and (equal (fn-zin-mode s) 2) (equal (fn-zin-bits s) 4294901760)
         (equal (fn-zin-nbits s) 32) (not (equal (fn-zin-final s) 0))
         (not (pwt-terminal-conclusion s))))
  :rule-classes nil)
