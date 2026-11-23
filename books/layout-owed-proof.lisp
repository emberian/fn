(in-package "ACL2")
(include-book "layout")
(include-book "owed-discharge")
(local (include-book "pool-read-contracts"))

;; A scan can only write field rows at or beyond its current cursor.
(local
 (defun-nx fn2-layout-proof-row (j f)
   (list (fn2-fields-value j f) (fn2-fields-ref-slot j f)
         (fn2-fields-ref-off j f) (fn2-fields-ref-len j f))))

(local
 (defthm fn2-layout-proof-row-of-store
   (equal (fn2-layout-proof-row j (fn2-layout-store i v slot gen ref size status f))
          (if (and (equal (nfix j) i) (natp i) (< i (fn2-fields-rows f))
                   (unsigned-byte-p 60 v) (unsigned-byte-p 32 slot)
                   (unsigned-byte-p 60 gen) (unsigned-byte-p 32 ref)
                   (unsigned-byte-p 32 size) (unsigned-byte-p 8 status))
              (list v slot ref size)
            (fn2-layout-proof-row j f)))
   :hints (("Goal" :in-theory (e/d (fn2-layout-store) (unsigned-byte-p nth update-nth fn2-fields-rows))))))

(local
 (defthm fn2-layout-proof-row-of-save
   (equal (fn2-layout-proof-row j (fn2-layout-save i pos v hi size ref phase next f))
          (fn2-layout-proof-row j f))
   :hints (("Goal" :in-theory (enable fn2-layout-save)))))

(local
 (defthm fn2-layout-proof-mv-nth-of-cons
   (equal (mv-nth n (cons a b))
          (if (zp n) a (mv-nth (1- n) b)))))
(local (in-theory (disable fn2-layout-proof-row mv-nth)))
(local
 (defthm fn2-layout-proof-row-before-store
   (implies (and (natp j) (< j i))
            (equal (fn2-layout-proof-row j (fn2-layout-store i v slot gen ref size status f))
                   (fn2-layout-proof-row j f)))))
(local (in-theory (disable fn2-layout-proof-row-of-store)))

(local
 (defthm fn2-layout-scan-preserves-earlier-row
   (implies (and (natp j) (natp i) (< j i))
            (equal (fn2-layout-proof-row
                    j (mv-nth 9 (fn2-layout-scan layout fuel i pos v hi size ref phase next
                                                 slot gen end okind oslot ogen f p)))
                   (fn2-layout-proof-row j f)))
   :hints (("Goal"
            :induct (fn2-layout-scan layout fuel i pos v hi size ref phase next
                                     slot gen end okind oslot ogen f p)
            :expand ((fn2-layout-scan layout fuel i pos v hi size ref phase next
                                      slot gen end okind oslot ogen f p))
            :in-theory (e/d ((:induction fn2-layout-scan))
                            (fn2-pool-read fn2-fields-rows fn2-layout-proof-row
                             fn2-fields-value fn2-fields-ref-slot fn2-fields-ref-off
                             fn2-fields-ref-len fn2-fields-status fn2-fields-ref-gen
                             mod nfix unsigned-byte-p))))))

(local (include-book "std/lists/rev" :dir :system))
(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))
(local (deftheory fn2-layout-proof-ground
         (union-theories (theory 'minimal-theory)
                         (intersection-theories (current-theory :here) (executable-counterpart-theory :here)))))
(local (deftheory fn2-layout-proof-roundtrip-start (current-theory :here)))
(local (deftheory fn2-layout-proof-list-index-rules
         (union-theories '(natp posp nfix zp-open normalize-addends |(+ y x)| |(+ 0 x)| |(+ y (+ x z))|
             |(+ x (- x))| |(- (- x))|)
                         (theory 'fn2-layout-proof-ground))))
(local (deftheory fn2-layout-proof-index-rules
         (union-theories '(normalize-addends |(+ y x)| |(+ y (+ x z))| |(+ x (- x))| |(+ 0 x)| |(- (- x))| natp posp
             nfix zp-open default-car default-cdr car-cons cdr-cons fn2-layoutp-head)
                         (theory 'fn2-layout-proof-ground))))
(local
 (defun fn2-layout-proof-cont (n v)
   (if (zp n) nil
     (cons (+ 128 (mod (nfix v) 128))
           (fn2-layout-proof-cont (1- n) (floor (nfix v) 128))))))

(local
 (defun fn2-layout-proof-scale (base n)
   (if (zp n) 1 (* (nfix base) (fn2-layout-proof-scale base (1- n))))))
(local (in-theory (disable fn2-layout-proof-scale)))

(local
 (defthm fn2-layout-proof-floor-upper
   (implies (and (natp v) (posp base) (integerp m) (< v (* base m)))
            (< (floor v base) m))
   :hints (("Goal" :nonlinearp t))
   :rule-classes nil))

(local
 (defthm fn2-layout-le-extend-high
   (implies (and (natp n) (natp v) (< v (fn2-layout-proof-scale 256 n))
                 (unsigned-byte-p 8 b))
            (equal (fn2-layout-le (1+ n) (+ v (* b (fn2-layout-proof-scale 256 n))))
                   (append (fn2-layout-le n v) (list b))))
   :hints (("Goal" :induct (fn2-layout-le n v))
           ("Subgoal *1/2"
            :use ((:instance fn2-layout-proof-floor-upper (base 256)
                             (m (fn2-layout-proof-scale 256 (1- n)))))
            :expand ((fn2-layout-proof-scale 256 n)))
           ("Subgoal *1/1" :expand ((fn2-layout-proof-scale 256 n))))))

(local
 (defthm fn2-layout-cont-extend-high
   (implies (and (natp n) (natp v) (< v (fn2-layout-proof-scale 128 n))
                 (unsigned-byte-p 7 b))
            (equal (fn2-layout-proof-cont (1+ n) (+ v (* b (fn2-layout-proof-scale 128 n))))
                   (append (fn2-layout-proof-cont n v) (list (+ 128 b)))))
   :hints (("Goal" :induct (fn2-layout-proof-cont n v))
           ("Subgoal *1/2"
            :use ((:instance fn2-layout-proof-floor-upper (base 128)
                             (m (fn2-layout-proof-scale 128 (1- n)))))
            :expand ((fn2-layout-proof-scale 128 n)))
           ("Subgoal *1/1" :expand ((fn2-layout-proof-scale 128 n))))))

(local
 (defthm fn2-layout-varoctets-extend-high
   (implies (and (natp n) (natp v) (< v (fn2-layout-proof-scale 128 n))
                 (unsigned-byte-p 7 b) (or (zp n) (posp b)))
            (equal (fn2-layout-varoctets (+ v (* b (fn2-layout-proof-scale 128 n))))
                   (append (fn2-layout-proof-cont n v) (list b))))
   :hints (("Goal" :induct (fn2-layout-proof-cont n v))
           ("Subgoal *1/2"
            :use ((:instance fn2-layout-proof-floor-upper (base 128)
                             (m (fn2-layout-proof-scale 128 (1- n)))))
            :expand ((fn2-layout-varoctets (+ v (* b (fn2-layout-proof-scale 128 n))))
                     (fn2-layout-proof-scale 128 n)))
           ("Subgoal *1/1"
            :expand ((fn2-layout-proof-scale 128 n) (fn2-layout-varoctets b))))))

(local
 (defthm fn2-layout-be-extend-low
   (implies (and (natp n) (natp v) (unsigned-byte-p 8 b))
            (equal (fn2-layout-be (1+ n) (+ (* 256 v) b))
                   (append (fn2-layout-be n v) (list b))))
   :hints (("Goal" :expand ((fn2-layout-le (1+ n) (+ (* 256 v) b)))))))

(local
 (defun fn2-layout-proof-width (tag)
   (case tag ((1 6 9) 1) ((2 12 15) 2) ((3 13 16) 4) (otherwise 8))))
(local
 (defun fn2-layout-proof-header (tag size)
   (case tag (7 '(1)) (10 (fn2-layout-varoctets size))
         (otherwise (fn2-layout-be (fn2-layout-proof-width tag) size)))))
(local
 (defun-nx fn2-layout-proof-prefix (tag pos v size phase ref base p)
   (cond ((equal phase 1)
          (append (fn2-layout-proof-header tag size)
                  (fn2-pool-logical-octets pos (+ base ref) p)))
         ((member tag '(1 2 3 4)) (fn2-layout-le pos v))
         ((member tag '(12 13 14 15 16)) (fn2-layout-be pos v))
         ((member tag '(5 8 10)) (fn2-layout-proof-cont pos v))
         ((equal tag 11) (make-list pos :initial-element 0))
         (t nil))))
(local
 (defun fn2-layout-proof-statep (k pos v hi size phase ref next)
   (let ((tag (fn2-layout-kind-code k)))
     (and (natp pos) (natp v) (equal hi 0)
          (if (equal phase 1)
              (and (member tag '(7 10 15 16))
                   (unsigned-byte-p 32 size) (< pos size)
                   (equal (+ ref pos) next)
                   (if (equal tag 7) (and (equal v 1) (equal size 32))
                     (equal v 0)))
            (and (equal phase 0) (equal size 0) (equal ref 0)
                 (cond ((member tag '(1 2 3 4 12 13 14 15 16))
                        (and (< pos (fn2-layout-proof-width tag))
                             (< v (fn2-layout-proof-scale 256 pos))
                             (or (not (equal tag 14)) (zp pos)
                                 (< v (/ (fn2-layout-proof-scale 256 pos) 16)))))
                       ((member tag '(5 8 10))
                        (and (<= pos 8) (< v (fn2-layout-proof-scale 128 pos))))
                       ((equal tag 11)
                        (and (equal v 0) (or (equal pos 0) (< pos (nfix (cadr k))))))
                       (t (and (equal pos 0) (equal v 0))))))))))
(local
 (defun-nx fn2-layout-proof-value (tag v size ref base p)
   (case tag (7 (cons v (fn2-pool-logical-octets size (+ base ref) p)))
         ((10 15 16) (fn2-pool-logical-octets size (+ base ref) p))
         (11 nil) (otherwise v))))
(local
 (defthm fn2-layout-proof-octets-length
   (equal (len (fn2-pool-logical-octets n a p)) (nfix n))))
(local
 (defthm fn2-layout-proof-octets-extend
   (implies (and (natp n) (acl2-numberp a))
            (equal (fn2-pool-logical-octets (+ 1 n) a p)
                   (append (fn2-pool-logical-octets n a p)
                           (list (fn2-pool-datai (+ a n) p)))))
   :hints (("Goal" :induct (fn2-pool-logical-octets n a p)
            :in-theory (disable fn2-pool-datai)) ("Subgoal *1/1" :expand ((fn2-pool-logical-octets 1 a p))))))
(local (in-theory (disable fn2-layout-proof-octets-extend)))
(local (include-book "std/lists/repeat" :dir :system))
(local
 (defthm fn2-layout-proof-extend-zeros
   (implies (natp n)
            (equal (make-list (1+ n) :initial-element 0)
                   (append (make-list n :initial-element 0) '(0))))
   :hints (("Goal" :expand ((repeat (1+ n) 0))))))

(local
 (defun fn2-layout-proof-widep (tag pos hi phase)
   (and (member tag '(5 8 10)) (equal phase 0)
        (or (not (equal hi 0)) (< 8 pos)))))

(local
 (defun-nx fn2-layout-proof-byte-law (k pos v hi size phase ref base next byte p)
   (let* ((tag (fn2-layout-kind-code k))
          (empty (equal k '(:zero 0)))
          (nnext (if empty next (1+ next)))
          (consumed (append (fn2-layout-proof-prefix tag pos v size phase ref base p)
                            (if empty nil (list byte)))))
     (mv-let (code nv nh ns ph)
       (if empty (mv :done 0 0 0 0) (fn2-layout-byte k pos v hi size phase byte))
       (let* ((nv (nfix nv)) (nh (nfix nh)) (ns (nfix ns)) (ph (nfix ph))
              (r (if (or (eq code :payload) (and (= ph 1) (= ns 0))) nnext ref))
             (np (if (eq code :payload) 0 (1+ pos))))
         (case code
           (:done (and (unsigned-byte-p 60 nv) (unsigned-byte-p 32 ns)
                       (equal consumed
                              (fn2-layout-field-octets
                               k (fn2-layout-proof-value tag nv ns r base p)))))
           ((:part :payload)
            (or (fn2-layout-proof-widep tag np nh ph)
                (and (fn2-layout-proof-statep k np nv nh ns ph r nnext)
                     (equal consumed
                            (fn2-layout-proof-prefix tag np nv ns ph r base p)))))
           (otherwise t)))))))

(local (in-theory (disable fn2-layout-le fn2-layout-be fn2-layout-varoctets
                           fn2-layout-proof-cont fn2-pool-logical-octets fn2-pool-datai
                           fn2-layout-kind-code make-list-ac-removal fn2-layout-proof-extend-zeros)))

(local
 (defthm fn2-layout-proof-octets-empty
   (equal (fn2-pool-logical-octets 0 a p) nil)
   :hints (("Goal" :expand ((fn2-pool-logical-octets 0 a p))))))
(local
 (defthm fn2-layout-proof-append-assoc
   (equal (append (append a b) c) (append a b c))))
(local
 (defthm fn2-layout-proof-payload-byte
   (implies (and (member (fn2-layout-kind-code k) '(7 10 15 16))
                 (equal phase 1)
                 (fn2-layout-proof-statep k pos v hi size phase ref next)
                 (unsigned-byte-p 8 byte)
                 (natp base) (natp ref)
                 (equal byte (fn2-pool-datai (+ base next) p))
                 (not (equal k '(:zero 0))))
            (fn2-layout-proof-byte-law k pos v hi size phase ref base next byte p))
   :rule-classes nil
   :hints (("Goal"
            :cases ((equal size (1+ pos)))
            :use ((:instance fn2-layout-proof-octets-extend (n pos) (a (+ base ref))))
            :in-theory (enable fn2-layout-byte)))))

(local
 (defthm fn2-layout-proof-high-digit
   (implies (and (unsigned-byte-p 8 byte) (<= 128 byte))
            (equal (mod byte 128) (- byte 128)))
   :hints (("Goal" :cases ((< (floor byte 128) 1) (< 1 (floor byte 128))) :in-theory (enable mod)
            :use ((:instance floor-bounds-1 (x byte) (y 128)))))))

(local
 (defthm fn2-layout-proof-low-seven-bits
   (implies (unsigned-byte-p 8 byte)
            (equal (mod byte 128) (if (< byte 128) byte (- byte 128))))))

;; POS is bounded by the width of the current word or length prefix.  Split
;; on the wire position so ACL2 evaluates the shift and its byte bound once.
(local
 (defmacro fn2-layout-proof-word-law (name tag width endian)
   (let* ((variable (eq endian :varint))
          (extension (cond (variable 'fn2-layout-cont-extend-high)
                           ((eq endian :be) 'fn2-layout-be-extend-low)
                           (t 'fn2-layout-le-extend-high)))
          (digit (if variable '(mod byte 128) 'byte)))
     `(defthm ,name
        (implies (and (equal (fn2-layout-kind-code k) ,tag)
                      (not (equal k '(:zero 0)))
                      (equal phase 0)
                      (fn2-layout-proof-statep k pos v hi size phase ref next)
                      (unsigned-byte-p 8 byte)
                      ,@(and (member tag '(10 15 16)) '((unsigned-byte-p 32 (cadr k)))))
                 (fn2-layout-proof-byte-law k pos v hi size phase ref base next byte p))
        :rule-classes nil
        :hints (("Goal"
                 :cases ,(take width '((equal pos 0) (equal pos 1) (equal pos 2)
                                      (equal pos 3) (equal pos 4) (equal pos 5)
                                      (equal pos 6) (equal pos 7) (equal pos 8)))
                 :use ((:instance ,extension (n pos) (b ,digit))
                       ,@(and variable '((:instance fn2-layout-varoctets-extend-high
                                                    (n pos) (b (mod byte 128))))))
                 :in-theory (e/d (fn2-layout-byte ash)
                                 (fn2-layout-le-extend-high fn2-layout-be-extend-low
                                  fn2-layout-cont-extend-high fn2-layout-varoctets-extend-high))))))))
(local (fn2-layout-proof-word-law fn2-layout-proof-u8 1 1 :le))
(local (fn2-layout-proof-word-law fn2-layout-proof-u16 2 2 :le))
(local (fn2-layout-proof-word-law fn2-layout-proof-u32 3 4 :le))
(local (fn2-layout-proof-word-law fn2-layout-proof-u64 4 8 :le))
(local (fn2-layout-proof-word-law fn2-layout-proof-u16be 12 2 :be))
(local (fn2-layout-proof-word-law fn2-layout-proof-u32be 13 4 :be))
(local (fn2-layout-proof-word-law fn2-layout-proof-u64be 14 8 :be))
(local (fn2-layout-proof-word-law fn2-layout-proof-octets16 15 2 :be))
(local (fn2-layout-proof-word-law fn2-layout-proof-octets32 16 4 :be))
(local (fn2-layout-proof-word-law fn2-layout-proof-varint 5 9 :varint))
(local (fn2-layout-proof-word-law fn2-layout-proof-id 8 9 :varint))
(local (fn2-layout-proof-word-law fn2-layout-proof-octets 10 9 :varint))

(local
 (defthm fn2-layout-proof-single-octet
   (implies (and (member (fn2-layout-kind-code k) '(6 7 9))
                 (not (equal k '(:zero 0)))
                 (equal phase 0)
                 (fn2-layout-proof-statep k pos v hi size phase ref next)
                 (unsigned-byte-p 8 byte))
            (fn2-layout-proof-byte-law k pos v hi size phase ref base next byte p))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn2-layout-byte)))))
(local
 (defthm fn2-layout-proof-padding
   (implies (and (equal k (list :zero n)) (unsigned-byte-p 32 n)
                 (equal phase 0)
                 (fn2-layout-proof-statep k pos v hi size phase ref next)
                 (unsigned-byte-p 8 byte))
            (fn2-layout-proof-byte-law k pos v hi size phase ref base next byte p))
   :rule-classes nil
   :hints (("Goal" :cases ((equal n (1+ pos)))
            :use ((:instance fn2-layout-proof-extend-zeros (n pos)))
            :in-theory (enable fn2-layout-byte fn2-layout-kind-code)))))

(local
 (defthm fn2-layout-proof-pair-shape
   (implies (and (true-listp k) (equal (len k) 2))
            (equal (list (car k) (cadr k)) k))
   :rule-classes nil
   :hints (("Goal" :cases ((consp k) (consp (cdr k)) (consp (cddr k)))
            :in-theory (union-theories '(len true-listp default-car default-cdr car-cons cdr-cons car-cdr-elim
                                        (:type-prescription len)) (theory 'minimal-theory))
            :expand ((len k) (len (cdr k)) (len (cddr k)))))))
(local
 (defthm fn2-layout-proof-kind-facts
   (implies (fn2-layout-kindp k)
            (let ((tag (fn2-layout-kind-code k)))
              (and (member tag '(1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16))
                   (implies (member tag '(10 15 16)) (unsigned-byte-p 32 (cadr k)))
                   (implies (equal tag 11)
                            (and (equal k (list :zero (cadr k)))
                                 (unsigned-byte-p 32 (cadr k)))))))
   :rule-classes nil
   :hints (("Goal" :backchain-limit-rw 0 :use fn2-layout-proof-pair-shape :in-theory (enable fn2-layout-kind-code)))))

(local
 (defthm fn2-layout-proof-byte-preserves-prefix
   (implies (and (fn2-layout-kindp k)
                 (fn2-layout-proof-statep k pos v hi size phase ref next)
                 (unsigned-byte-p 8 byte) (natp base) (natp ref)
                 (or (not (equal phase 1))
                     (equal byte (fn2-pool-datai (+ base next) p))))
            (fn2-layout-proof-byte-law k pos v hi size phase ref base next byte p))
   :rule-classes nil
   :hints (("Goal"
            :use (fn2-layout-proof-kind-facts fn2-layout-proof-single-octet
                  (:instance fn2-layout-proof-padding (n (cadr k)))
                  fn2-layout-proof-payload-byte fn2-layout-proof-u8
                  fn2-layout-proof-u16 fn2-layout-proof-u32 fn2-layout-proof-u64
                  fn2-layout-proof-u16be fn2-layout-proof-u32be fn2-layout-proof-u64be
                  fn2-layout-proof-varint fn2-layout-proof-id fn2-layout-proof-octets
                  fn2-layout-proof-octets16 fn2-layout-proof-octets32)
            :in-theory (disable fn2-layout-proof-byte-law fn2-layout-kindp
                                fn2-pool-datai unsigned-byte-p)
            :do-not-induct t))))

;; Keep the cursor together so the induction uses one recursive call for a
;; partial field and one for a completed row.  Failure has no result to read.
(local
 (defun-nx fn2-layout-proof-tick (k cursor byte)
   (let* ((pos (nth 0 cursor)) (ref (nth 4 cursor))
          (empty (equal k '(:zero 0)))
          (next (if empty (nth 6 cursor) (+ 1 (nth 6 cursor)))))
     (mv-let (code v hi size phase)
       (if empty (mv :done 0 0 0 0)
         (fn2-layout-byte k pos (nth 1 cursor) (nth 2 cursor) (nth 3 cursor)
                          (nth 5 cursor) byte))
       (list code (if (eq code :payload) 0 (+ 1 pos)) (nfix v) (nfix hi) (nfix size)
             (if (or (eq code :payload) (and (= (nfix phase) 1) (= (nfix size) 0))) next ref)
             (nfix phase) next)))))
(local
 (defun-nx fn2-layout-proof-run (layout fuel i cursor slot gen end okind oslot ogen f p)
   (declare (xargs :measure (+ (nfix fuel) (len layout))
                   :hints (("Goal" :in-theory (disable fn2-layout-proof-tick
                              fn2-pool-read fn2-fields-rows nth mod member-equal)))))
   (let* ((next (nth 6 cursor)) (k (cadar layout)) (empty (equal k '(:zero 0))))
     (cond ((atom layout) (cons next f))
           ((or (and (not empty) (or (zp fuel) (>= next end)))
                (not (natp i)) (>= i (fn2-fields-rows f))) nil)
           (t
            (mv-let (rc byte)
              (if empty (mv :ok 0) (fn2-pool-read slot gen next okind oslot ogen p))
              (let* ((tick (fn2-layout-proof-tick k cursor (mod (nfix byte) 256)))
                     (code (car tick)) (c (cdr tick))
                     (fuel (if empty fuel (1- fuel))))
                (cond ((not (eq rc :ok)) nil)
                      ((eq code :done)
                       (fn2-layout-proof-run
                        (cdr layout) fuel (+ 1 i) (list 0 0 0 0 0 0 (nth 6 c))
                        slot gen end okind oslot ogen
                        (fn2-layout-store i (nth 1 c) slot gen (nth 4 c) (nth 3 c) 0 f) p))
                      ((and (not empty) (member-eq code '(:part :payload)))
                       (fn2-layout-proof-run layout fuel i c slot gen end okind oslot ogen f p))
                      (t nil)))))))))
(local
 (defthm fn2-layout-byte-status
   (not (equal (mv-nth 0 (fn2-layout-byte k pos v hi size phase byte)) :ok))
   :hints (("Goal" :in-theory (enable fn2-layout-byte)))))
(local
 (defthm fn2-layout-proof-run-is-scan
   (let ((result (fn2-layout-scan layout fuel i pos v hi size ref phase next
                                  slot gen end okind oslot ogen f p)))
     (equal (fn2-layout-proof-run layout fuel i (list pos v hi size ref phase next)
                                  slot gen end okind oslot ogen f p)
            (and (eq (mv-nth 0 result) :ok)
                 (cons (mv-nth 8 result) (mv-nth 9 result)))))
   :rule-classes nil
   :hints (("Goal"
            :induct (fn2-layout-scan layout fuel i pos v hi size ref phase next
                                     slot gen end okind oslot ogen f p)
            :expand ((fn2-layout-scan layout fuel i pos v hi size ref phase next
                                      slot gen end okind oslot ogen f p)
                     (fn2-layout-proof-run layout fuel i (list pos v hi size ref phase next)
                                           slot gen end okind oslot ogen f p))
            :in-theory (e/d ((:induction fn2-layout-scan))
                            (fn2-layout-proof-run fn2-pool-read fn2-fields-rows
                             fn2-fields-value fn2-fields-ref-slot fn2-fields-ref-gen
                             fn2-fields-ref-off fn2-fields-ref-len fn2-fields-status
                             mod nfix nth))))))

(local
 (defthm fn2-layout-proof-read-value
   (implies (equal (mv-nth 0 (fn2-pool-read slot gen next okind oslot ogen p)) :ok)
            (equal (mv-nth 1 (fn2-pool-read slot gen next okind oslot ogen p))
                   (fn2-pool-datai (+ (fn2-pool-base slot p) next) p)))
   :hints (("Goal" :in-theory (e/d (fn2-pool-read) (fn2-pool-readable-code
                      fn2-pool-base fn2-pool-fill fn2-pool-data-length))))))
(local
 (defthm fn2-layout-proof-read-in-range
   (implies (and (fn2-poolp p) (fn2-pool-wfp p)
                 (equal (mv-nth 0 (fn2-pool-read slot gen next okind oslot ogen p)) :ok))
            (unsigned-byte-p 8 (fn2-pool-datai (+ (fn2-pool-base slot p) next) p)))
   :hints (("Goal" :use ((:instance fn2-pool-read-byte-type (idx next) (fn2-pool p)))
            :in-theory (disable fn2-pool-read-byte-type fn2-pool-read fn2-pool-base
                                unsigned-byte-p)))))

(local
 (defun fn2-layout-proof-cursor-okp (k c)
   (fn2-layout-proof-statep k (nth 0 c) (nth 1 c) (nth 2 c) (nth 3 c)
                            (nth 5 c) (nth 4 c) (nth 6 c))))
(local
 (defun fn2-layout-proof-cursor-widep (k c)
   (fn2-layout-proof-widep (fn2-layout-kind-code k) (nth 0 c) (nth 2 c) (nth 5 c))))
(local
 (defun-nx fn2-layout-proof-consumed (k c base p)
   (fn2-layout-proof-prefix (fn2-layout-kind-code k) (nth 0 c) (nth 1 c)
                            (nth 3 c) (nth 5 c) (nth 4 c) base p)))
(local
 (defun-nx fn2-layout-proof-decoded (k c base p)
   (fn2-layout-proof-value (fn2-layout-kind-code k) (nth 1 c) (nth 3 c)
                           (nth 4 c) base p)))
(local
 (defthm fn2-layout-proof-initial-cursor
   (and (fn2-layout-proof-cursor-okp k (list 0 0 0 0 0 0 next))
        (not (fn2-layout-proof-cursor-widep k (list 0 0 0 0 0 0 next)))
        (equal (fn2-layout-proof-consumed k (list 0 0 0 0 0 0 next) base p) nil))))
(local
 (defthm fn2-layout-proof-tick-wide
   (implies (fn2-layout-proof-cursor-widep k c)
            (let ((tick (fn2-layout-proof-tick k c byte)))
              (and (not (equal (car tick) :done))
                   (implies (member (car tick) '(:part :payload))
                            (fn2-layout-proof-cursor-widep k (cdr tick))))))
   :hints (("Goal" :in-theory (e/d (fn2-layout-byte) (ash mod nth))))))
(local
 (defthm fn2-layout-proof-tick-position
   (let* ((tick (fn2-layout-proof-tick k c byte)) (out (cdr tick)))
     (and (equal (nth 6 out) (if (equal k '(:zero 0)) (nth 6 c) (1+ (nth 6 c))))
          (implies (and (unsigned-byte-p 32 (nth 4 c)) (unsigned-byte-p 32 (nth 6 out)))
                   (unsigned-byte-p 32 (nth 4 out)))))
   :hints (("Goal" :in-theory (disable fn2-layout-byte nth unsigned-byte-p nfix)))))

(local
 (defthm fn2-layout-proof-tick-law
   (implies (and (fn2-layout-kindp k) (fn2-layout-proof-cursor-okp k c)
                 (unsigned-byte-p 8 byte) (natp base) (natp (nth 4 c))
                 (or (not (equal (nth 5 c) 1))
                     (equal byte (fn2-pool-datai (+ base (nth 6 c)) p))))
            (let* ((tick (fn2-layout-proof-tick k c byte))
                   (out (cdr tick))
                   (bytes (append (fn2-layout-proof-consumed k c base p)
                                  (if (equal k '(:zero 0)) nil (list byte)))))
              (and (implies (eq (car tick) :done)
                            (and (unsigned-byte-p 60 (nth 1 out))
                                 (unsigned-byte-p 32 (nth 3 out))
                                 (equal (fn2-layout-field-octets k (fn2-layout-proof-decoded k out base p))
                                        bytes)))
                   (implies (and (member (car tick) '(:part :payload))
                                 (not (fn2-layout-proof-cursor-widep k out)))
                            (and (fn2-layout-proof-cursor-okp k out)
                                 (equal (fn2-layout-proof-consumed k out base p) bytes))))))
   :hints (("Goal"
            :use ((:instance fn2-layout-proof-byte-preserves-prefix
                             (pos (nth 0 c)) (v (nth 1 c)) (hi (nth 2 c))
                             (size (nth 3 c)) (ref (nth 4 c)) (phase (nth 5 c))
                             (next (nth 6 c))))
            :in-theory (disable fn2-layout-kindp fn2-layout-field-octets fn2-layout-proof-statep
                                fn2-layout-proof-prefix fn2-layout-proof-widep fn2-layout-proof-value
                                unsigned-byte-p mod nth nfix)))))

(local (in-theory (disable fn2-layout-proof-run fn2-layout-proof-tick
                           fn2-layout-proof-consumed fn2-layout-proof-cursor-okp
                           fn2-layout-proof-cursor-widep fn2-layout-proof-decoded
                           fn2-pool-read fn2-pool-base fn2-layout-kindp fn2-layoutp
                           fn2-fields-rows nth)))
(local
 (defthm fn2-layout-proof-run-frame
   (let ((run (fn2-layout-proof-run layout fuel i c slot gen end okind oslot ogen f p)))
     (implies (and run (natp i) (natp j) (< j i))
              (equal (fn2-layout-proof-row j (cdr run)) (fn2-layout-proof-row j f))))
   :hints (("Goal"
            :induct (fn2-layout-proof-run layout fuel i c slot gen end okind oslot ogen f p)
            :expand ((fn2-layout-proof-run layout fuel i c slot gen end okind oslot ogen f p))
            :in-theory (enable (:induction fn2-layout-proof-run))))))
(local
 (defun-nx fn2-layout-proof-at (k row p)
   (fn2-layout-proof-value (fn2-layout-kind-code k) (nth 0 row) (nth 3 row)
                           (nth 2 row) (fn2-pool-base (nth 1 row) p) p)))
(local
 (defthm fn2-layout-proof-values-unfolds
   (equal (fn2-layout-values layout i f p)
          (if (consp layout)
              (cons (fn2-layout-proof-at (cadar layout) (fn2-layout-proof-row i f) p)
                    (fn2-layout-values (cdr layout) (1+ (nfix i)) f p))
            nil))
   :rule-classes :definition
   :hints (("Goal" :expand ((fn2-layout-values layout i f p))
            :in-theory (enable fn2-layout-proof-row)))))
(local (in-theory (disable fn2-layout-values fn2-layout-proof-values-unfolds)))
(local
 (defthm fn2-layout-values-of-save
   (equal (fn2-layout-values layout j (fn2-layout-save i pos v hi size ref phase next f) p)
          (fn2-layout-values layout j f p))
   :hints (("Goal" :induct (fn2-layout-values layout j f p)
            :in-theory (e/d ((:induction fn2-layout-values) fn2-layout-proof-values-unfolds)
                            (fn2-layout-proof-at))))))
(local
 (defthm fn2-layout-proof-at-stored
   (equal (fn2-layout-proof-at k (list (nth 1 c) slot (nth 4 c) (nth 3 c)) p)
          (fn2-layout-proof-decoded k c (fn2-pool-base slot p) p))
   :hints (("Goal" :in-theory (e/d (fn2-layout-proof-decoded) (fn2-layout-proof-value))))))
(local (in-theory (disable fn2-layout-proof-at)))
(local
 (defthm fn2-layout-proof-slice-step
   (implies (and (integerp next) (integerp finish) (< next finish) (integerp base))
            (equal (fn2-pool-logical-octets (- finish next) (+ base next) p)
                   (cons (fn2-pool-datai (+ base next) p)
                         (fn2-pool-logical-octets (- finish (1+ next)) (+ base (1+ next)) p))))
   :rule-classes nil
   :hints (("Goal" :expand ((fn2-pool-logical-octets (- finish next) (+ base next) p))))))
(local
 (defthm fn2-layout-proof-unsigned-octet-fix
   (implies (unsigned-byte-p 8 x) (equal (mod (nfix x) 256) x))))

(local
 (defthm fn2-layout-proof-finish-position
   (let ((run (fn2-layout-proof-run layout fuel i c slot gen end okind oslot ogen f p)))
     (implies (and run (natp (nth 6 c)))
              (and (integerp (car run)) (<= (nth 6 c) (car run)))))
   :hints (("Goal" :induct (fn2-layout-proof-run layout fuel i c slot gen end okind oslot ogen f p)
            :expand ((fn2-layout-proof-run layout fuel i c slot gen end okind oslot ogen f p))
            :in-theory (enable (:induction fn2-layout-proof-run))))))
(local
 (defthm fn2-layout-proof-kind-at-head
   (implies (and (fn2-layoutp layout) (consp layout)) (fn2-layout-kindp (cadar layout)))
   :hints (("Goal" :use fn2-layoutp-head))))
(local
 (defun-nx fn2-layout-proof-slice (next finish base p)
   (fn2-pool-logical-octets (- finish next) (+ base next) p)))
(local
 (defthm fn2-layout-proof-slice-of-tick
   (let* ((next (nth 6 c))
          (tick (fn2-layout-proof-tick k c byte))
          (pos (nth 6 (cdr tick))))
     (implies (and (natp next) (natp finish) (<= pos finish) (natp base))
              (equal (fn2-layout-proof-slice next finish base p)
                     (append (if (equal k '(:zero 0)) nil
                               (list (fn2-pool-datai (+ base next) p)))
                             (fn2-layout-proof-slice pos finish base p)))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-layout-proof-slice-step (next (nth 6 c))))))))
(local
 (defthm fn2-layout-proof-slice-empty
   (equal (fn2-layout-proof-slice next next base p) nil)))
(local (in-theory (disable fn2-layout-proof-slice fn2-layout-field-octets
                           unsigned-byte-p nfix fn2-poolp fn2-pool-wfp)))
(local
 (defthm fn2-layout-proof-cursor-bounds
   (let* ((tick (fn2-layout-proof-tick k c byte)) (pos (nth 6 (cdr tick))))
     (implies (and (unsigned-byte-p 32 (nth 6 c)) (unsigned-byte-p 32 end)
                   (<= (nth 6 c) end) (or (equal k '(:zero 0)) (< (nth 6 c) end)))
              (and (unsigned-byte-p 32 pos) (<= pos end))))
   :hints (("Goal" :in-theory (enable unsigned-byte-p)))))
(local
 (defthm fn2-layout-proof-u32-natural
   (implies (unsigned-byte-p 32 x) (natp x))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable unsigned-byte-p)))))
(local
 (defthm fn2-layout-proof-wide-fails
   (implies (and (consp layout) (fn2-layout-proof-cursor-widep (cadar layout) c))
            (not (fn2-layout-proof-run layout fuel i c slot gen end okind oslot ogen f p)))
   :hints (("Goal" :induct (fn2-layout-proof-run layout fuel i c slot gen end okind oslot ogen f p)
            :expand ((fn2-layout-proof-run layout fuel i c slot gen end okind oslot ogen f p))
            :in-theory (enable (:induction fn2-layout-proof-run))))))

;; Remaining model bytes include the prefix already accumulated for this row.
(local
 (defun-nx fn2-layout-proof-remaining (layout c finish base p)
   (append (if (consp layout) (fn2-layout-proof-consumed (cadar layout) c base p) nil)
           (fn2-layout-proof-slice (nth 6 c) finish base p))))
(local
 (defthm fn2-layout-proof-combine-tick
   (let* ((k (cadar layout)) (next (nth 6 c))
          (base (fn2-pool-base slot p))
          (tick (fn2-layout-proof-tick k c byte))
          (out (cdr tick)) (pos (nth 6 out)))
     (implies (and (consp layout) (fn2-layoutp layout)
                   (fn2-layout-proof-cursor-okp k c)
                   (unsigned-byte-p 32 (nth 4 c)) (unsigned-byte-p 32 next)
                   (natp base) (natp finish) (<= pos finish)
                   (unsigned-byte-p 8 byte)
                   (if (equal k '(:zero 0)) (not (equal (nth 5 c) 1))
                     (equal byte (fn2-pool-datai (+ base next) p))))
              (and
               (implies (equal (car tick) :done)
                        (equal (append (fn2-layout-field-octets k (fn2-layout-proof-decoded k out base p))
                                       (fn2-layout-proof-slice pos finish base p))
                               (fn2-layout-proof-remaining layout c finish base p)))
               (implies (and (member (car tick) '(:part :payload))
                             (not (fn2-layout-proof-cursor-widep k out)))
                        (equal (fn2-layout-proof-remaining layout out finish base p)
                               (fn2-layout-proof-remaining layout c finish base p))))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-layout-proof-slice-of-tick (k (cadar layout)) (base (fn2-pool-base slot p)))
                         (:instance fn2-layout-proof-tick-law (k (cadar layout)) (base (fn2-pool-base slot p))))
            :in-theory (disable fn2-layout-proof-tick-law)))))
(local
 (defthm fn2-layout-proof-empty-phase
   (implies (fn2-layout-proof-cursor-okp '(:zero 0) c)
            (not (equal (nth 5 c) 1)))
   :hints (("Goal" :in-theory (enable fn2-layout-proof-cursor-okp fn2-layout-kind-code)))))
(local
 (defthm fn2-layout-proof-initial-remaining
   (equal (fn2-layout-proof-remaining layout (list 0 0 0 0 0 0 next) finish base p)
          (fn2-layout-proof-slice next finish base p))))
(local
 (defthm fn2-layout-proof-empty-remaining
   (implies (atom layout)
            (equal (fn2-layout-proof-remaining layout c (nth 6 c) base p) nil))))
(local (in-theory (disable fn2-layout-proof-remaining fn2-layout-proof-wide-fails)))

(local
 (defun-nx fn2-layout-proof-ready (layout i c slot gen end p)
   (and (fn2-layoutp layout) (natp i)
        (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
        (unsigned-byte-p 32 (nth 6 c)) (unsigned-byte-p 32 end) (<= (nth 6 c) end)
        (unsigned-byte-p 32 (nth 4 c))
        (fn2-layout-proof-cursor-okp (cadar layout) c)
        (fn2-poolp p) (fn2-pool-wfp p) (natp (fn2-pool-base slot p)))))
(local
 (defun-nx fn2-layout-proof-result (layout i c r slot p)
   (and (natp (car r)) (<= (nth 6 c) (car r))
        (equal (fn2-layout-octets layout (fn2-layout-values layout i (cdr r) p))
               (fn2-layout-proof-remaining layout c (car r) (fn2-pool-base slot p) p)))))
(local
 (defun-nx fn2-layout-proof-inputp (k c byte slot p)
   (and (unsigned-byte-p 8 byte)
        (or (equal k '(:zero 0))
            (equal byte (fn2-pool-datai (+ (fn2-pool-base slot p) (nth 6 c)) p))))))
(local
 (defthm fn2-layout-proof-read-input
   (let ((k (cadar layout)) (next (nth 6 c)))
     (implies (and (fn2-layout-proof-ready layout i c slot gen end p)
                   (or (equal k '(:zero 0))
                       (equal (mv-nth 0 (fn2-pool-read slot gen next okind oslot ogen p)) :ok)))
              (fn2-layout-proof-inputp k c
               (mod (nfix (if (equal k '(:zero 0)) 0
                            (mv-nth 1 (fn2-pool-read slot gen next okind oslot ogen p)))) 256) slot p)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-layout-proof-read-in-range (next (nth 6 c))))
            :in-theory (disable mod)))))
(local
 (defthm fn2-layout-proof-octets-cons
   (implies (and (consp layout) (natp i))
            (equal (fn2-layout-octets layout (fn2-layout-values layout i f p))
                   (append (fn2-layout-field-octets (cadar layout)
                            (fn2-layout-proof-at (cadar layout) (fn2-layout-proof-row i f) p))
                           (fn2-layout-octets (cdr layout) (fn2-layout-values (cdr layout) (1+ i) f p)))))
   :rule-classes nil
   :hints (("Goal" :expand ((:free (vals) (fn2-layout-octets layout vals))
                     (:with fn2-layout-proof-values-unfolds (fn2-layout-values layout i f p)))
            :in-theory (enable nfix)))))
(local
 (defthm fn2-layout-proof-done-ready
   (let* ((k (cadar layout)) (tick (fn2-layout-proof-tick k c byte))
          (out (cdr tick)) (c2 (list 0 0 0 0 0 0 (nth 6 out))))
     (implies (and (consp layout) (fn2-layout-proof-ready layout i c slot gen end p)
                   (or (equal k '(:zero 0)) (< (nth 6 c) end))
                   (fn2-layout-proof-inputp k c byte slot p)
                   (equal (car tick) :done))
              (fn2-layout-proof-ready (cdr layout) (1+ i) c2 slot gen end p)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-layout-proof-cursor-bounds (k (cadar layout))))
            :in-theory (e/d (fn2-layout-proof-row-of-store nfix) (fn2-layout-octets fn2-layout-proof-tick-law mod))
            :do-not-induct t))))
(local
 (defthm fn2-layout-proof-done-values
   (let* ((k (cadar layout)) (tick (fn2-layout-proof-tick k c byte))
          (out (cdr tick)) (c2 (list 0 0 0 0 0 0 (nth 6 out))))
     (implies (and (consp layout) (fn2-layout-proof-ready layout i c slot gen end p)
                   (or (equal k '(:zero 0)) (< (nth 6 c) end))
                   (fn2-layout-proof-inputp k c byte slot p)
                   (equal (car tick) :done))
              (implies (and (fn2-layout-proof-result (cdr layout) (1+ i) c2 r slot p)
                                 (equal (fn2-layout-proof-row i (cdr r))
                                        (list (nth 1 out) slot (nth 4 out) (nth 3 out))))
                            (fn2-layout-proof-result layout i c r slot p))))
   :rule-classes nil
   :hints (("Goal" :cases ((equal (cadar layout) '(:zero 0))) :use ((:instance fn2-layout-proof-octets-cons (f (cdr r)))
                         (:instance fn2-layout-proof-combine-tick (finish (car r)))
                         (:instance fn2-layout-proof-cursor-bounds (k (cadar layout))))
            :in-theory (union-theories '(fn2-layout-proof-ready fn2-layout-proof-inputp fn2-layout-proof-result
                fn2-layout-proof-at-stored fn2-layout-proof-tick-position fn2-layout-proof-initial-remaining
                fn2-layout-proof-empty-phase fn2-layout-proof-u32-natural fn2-layout-proof-kind-at-head
                fn2-layoutp-cdr car-cons cdr-cons default-car default-cdr nth-0-cons nth-add1) (theory
                'fn2-layout-proof-list-index-rules))
            :do-not-induct t))))
(local
 (defthm fn2-layout-proof-done-store
   (let* ((k (cadar layout)) (tick (fn2-layout-proof-tick k c byte))
          (out (cdr tick)))
     (implies (and (consp layout) (fn2-layout-proof-ready layout i c slot gen end p)
                   (or (equal k '(:zero 0)) (< (nth 6 c) end))
                   (fn2-layout-proof-inputp k c byte slot p)
                   (equal (car tick) :done))
              (implies (< i (fn2-fields-rows f))
                            (equal (fn2-layout-proof-row i (fn2-layout-store i (nth 1 out) slot gen
                                                          (nth 4 out) (nth 3 out) 0 f))
                                   (list (nth 1 out) slot (nth 4 out) (nth 3 out))))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-layout-proof-cursor-bounds (k (cadar layout)))
                         (:instance fn2-layout-proof-tick-law (k (cadar layout)) (base (fn2-pool-base slot p))))
            :in-theory (e/d (fn2-layout-proof-row-of-store nfix) (fn2-layout-octets fn2-layout-proof-tick-law mod))
            :do-not-induct t))))
(local
 (defthm fn2-layout-proof-done-step
   (let* ((k (cadar layout)) (tick (fn2-layout-proof-tick k c byte))
          (out (cdr tick)) (c2 (list 0 0 0 0 0 0 (nth 6 out))))
     (implies (and (consp layout) (fn2-layout-proof-ready layout i c slot gen end p)
                   (or (equal k '(:zero 0)) (< (nth 6 c) end))
                   (fn2-layout-proof-inputp k c byte slot p)
                   (equal (car tick) :done))
              (and (fn2-layout-proof-ready (cdr layout) (1+ i) c2 slot gen end p)
                   (implies (and (fn2-layout-proof-result (cdr layout) (1+ i) c2 r slot p)
                                 (equal (fn2-layout-proof-row i (cdr r))
                                        (list (nth 1 out) slot (nth 4 out) (nth 3 out))))
                            (fn2-layout-proof-result layout i c r slot p))
                   (implies (< i (fn2-fields-rows f))
                            (equal (fn2-layout-proof-row i (fn2-layout-store i (nth 1 out) slot gen
                                                          (nth 4 out) (nth 3 out) 0 f))
                                   (list (nth 1 out) slot (nth 4 out) (nth 3 out)))))))
   :rule-classes nil
   :hints (("Goal" :use (fn2-layout-proof-done-ready fn2-layout-proof-done-values fn2-layout-proof-done-store)
       :in-theory (theory 'minimal-theory)))))
(local
 (defthm fn2-layout-proof-part-step
   (let* ((k (cadar layout)) (tick (fn2-layout-proof-tick k c byte)) (out (cdr tick)))
     (implies (and (consp layout) (fn2-layout-proof-ready layout i c slot gen end p)
                   (< (nth 6 c) end)
                   (fn2-layout-proof-inputp k c byte slot p)
                   (member (car tick) '(:part :payload))
                   (not (fn2-layout-proof-cursor-widep k out)))
              (and (fn2-layout-proof-ready layout i out slot gen end p)
                   (implies (fn2-layout-proof-result layout i out r slot p)
                            (fn2-layout-proof-result layout i c r slot p)))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-layout-proof-combine-tick (finish (car r)))
                         (:instance fn2-layout-proof-cursor-bounds (k (cadar layout)))
                         (:instance fn2-layout-proof-tick-law (k (cadar layout)) (base (fn2-pool-base slot p))))
            :in-theory (disable fn2-layout-octets fn2-layout-proof-tick-law mod)
            :do-not-induct t))))
(local
 (defthm fn2-layout-proof-empty-result
   (implies (and (atom layout) (fn2-layout-proof-ready layout i c slot gen end p))
            (fn2-layout-proof-result layout i c (cons (nth 6 c) f) slot p))))
(local (in-theory (disable fn2-layout-proof-ready fn2-layout-proof-result
                           fn2-layout-proof-inputp fn2-layout-proof-read-value
                           fn2-layout-proof-tick-position)))
(local
 (defmacro fn2-layout-proof-induction ()
   (let* ((k '(cadar layout)) (empty `(equal ,k '(:zero 0)))
          (read-byte '(fn2-pool-read slot gen (nth 6 c) okind oslot ogen p))
          (byte `(mod (nfix (if ,empty 0 (mv-nth 1 ,read-byte))) 256))
          (out `(cdr (fn2-layout-proof-tick ,k c ,byte)))
          (run '(fn2-layout-proof-run layout fuel i c slot gen end okind oslot ogen f p)))
     `(defthm fn2-layout-proof-run-canonical
        (implies (and ,run (fn2-layout-proof-ready layout i c slot gen end p))
                 (fn2-layout-proof-result layout i c ,run slot p))
        :rule-classes nil
        :hints (("Goal" :induct ,run :expand (,run)
                 :in-theory (e/d ((:induction fn2-layout-proof-run)) (mod)))
                ("Subgoal *1/5" :use (fn2-layout-proof-read-input
                                       (:instance fn2-layout-proof-part-step (byte ,byte) (r ,run))
                                       (:instance fn2-layout-proof-wide-fails (c ,out) (fuel (1- fuel)))))
                ("Subgoal *1/4" :use (fn2-layout-proof-read-input
                                       (:instance fn2-layout-proof-done-step (byte ,byte) (r ,run)))))))))
(local (fn2-layout-proof-induction))

(local
 (defthm fn2-layout-proof-range-types
   (implies (and (fn2-poolp p) (fn2-pool-wfp p)
                 (equal (fn2-layout-range-code slot gen off end nil okind oslot ogen p) :ok))
            (and (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
                 (natp (fn2-pool-base slot p))))
   :hints (("Goal" :use ((:instance fn2-pool-gen-bound (fn2-pool p) (i slot))
                         (:instance fn2-pool-gen-natp (fn2-pool p) (i slot))
                         (:instance fn2-pool-base-natp (fn2-pool p) (i slot)))
            :in-theory (e/d (fn2-layout-range-code fn2-pool-readable-code fn2-pool-handle-code
                             unsigned-byte-p)
                            (fn2-pool-ownerp fn2-pool-base fn2-pool-rows fn2-pool-state
                             fn2-pool-gen fn2-pool-cap fn2-pool-fill))))))
(local
 (defthm fn2-layout-proof-initial-scan
   (let ((scan (fn2-layout-scan layout 4096 0 0 0 0 0 0 0 off slot gen end okind oslot ogen f p)))
     (implies (and (equal (mv-nth 0 scan) :ok)
                   (fn2-layoutp layout) (fn2-poolp p) (fn2-pool-wfp p)
                   (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
                   (unsigned-byte-p 32 off) (unsigned-byte-p 32 end) (<= off end)
                   (natp (fn2-pool-base slot p)))
              (equal (fn2-layout-octets layout (fn2-layout-values layout 0 (mv-nth 9 scan) p))
                     (fn2-pool-logical-octets (- (mv-nth 8 scan) off) (+ (fn2-pool-base slot p) off) p))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-layout-proof-run-canonical (i 0) (fuel 4096)
                                    (c (list 0 0 0 0 0 0 off)))
                         (:instance fn2-layout-proof-run-is-scan (i 0) (fuel 4096)
                                    (pos 0) (v 0) (hi 0) (size 0) (ref 0) (phase 0) (next off)))
            :in-theory (e/d (fn2-layout-proof-ready fn2-layout-proof-result fn2-layout-proof-slice)
                            (fn2-layout-octets))))))
(defthm fn2-layout-canonical-proved
  (fn2-layout-canonical$owed layout slot gen off end okind oslot ogen f p)
  :rule-classes nil
  :hints (("Goal" :use (fn2-layout-proof-initial-scan fn2-layout-proof-range-types)
           :in-theory (e/d (fn2-layout-canonical$owed fn2-layout-decode fn2-layout-decode-run fn2-pool-semanticp)
                           (fn2-layout-octets fn2-layout-max-size fn2-fieldsp fn2-fields-wfp
                            fn2-layout-proof-range-types fn2-pool-row-invariantp fn2-pool-class-accountsp
                            fn2-pool-retired-slots)))))
(fn2-owed-discharge fn2-layout-canonical fn2-layout-canonical-proved)

(local (in-theory (union-theories '(mv-nth) (theory 'fn2-layout-proof-roundtrip-start))))
;; The numeric portion of a field is emitted least- or most-significant
;; digit first. A payload starts after that portion, at its own offset.
(local
 (defun fn2-layout-proof-prefix-size (tag x)
   (case tag ((1 6 7 9) 1) ((2 12 15) 2) ((3 13 16) 4)
         ((4 14) 8) ((5 8 10) (fn2-layout-varsize x)) (otherwise 0))))
(local
 (defun fn2-layout-proof-emit-digit (tag pos x)
   (let* ((varp (member tag '(5 8 10)))
          (bew (case tag ((12 15) 2) ((13 16) 4) (14 8) (otherwise 0)))
          (shift (cond (varp (* 7 (min 8 pos)))
                       ((< 0 bew) (* 8 (nfix (- (1- bew) (min pos (1- bew))))))
                       (t (* 8 (min pos 7)))))
          (part (ash x (- shift))))
     (cond ((equal tag 11) 0) ((equal tag 7) 1)
           (varp (+ (mod part 128) (if (>= part 128) 128 0)))
           (t (mod part 256))))))
(local
 (defun fn2-layout-proof-accumulator (tag pos x)
   (cond ((zp pos) 0)
         ((member tag '(12 13 14 15 16))
          (floor x (expt 256 (nfix (- (fn2-layout-proof-prefix-size tag x) pos)))))
         ((member tag '(5 8 10)) (mod x (expt 128 pos)))
         (t (mod x (expt 256 pos))))))
(local
 (defun fn2-layout-proof-number-okp (tag x limit)
   (and (natp x)
        (case tag
          (1 (< x 256)) ((2 12) (< x 65536)) ((3 13) (< x 4294967296))
          ((4 5 8 14) (< x (expt 2 60)))
          (6 (< x 2)) (7 (equal x 1)) (9 (and (< x 256) (< x limit)))
          ((10 15 16) (and (<= x limit) (< x (if (equal tag 15) 65536 4294967296))))
          (otherwise nil)))))
(local
 (defun fn2-layout-proof-expected-header (k pos x)
   (let* ((tag (fn2-layout-kind-code k))
          (last (= (1+ pos) (fn2-layout-proof-prefix-size tag x))))
     (cond ((not last) (mv :part (fn2-layout-proof-accumulator tag (1+ pos) x) 0 0 0))
           ((equal tag 7) (mv :payload 1 0 32 1))
           ((member tag '(10 15 16)) (mv (if (zp x) :done :payload) 0 0 x 1))
           (t (mv :done x 0 0 0))))))
(local
 (defun-nx fn2-layout-proof-header-inverse (k pos x)
   (let* ((tag (fn2-layout-kind-code k))
          (byte (fn2-layout-proof-emit-digit tag pos x)))
     (and (unsigned-byte-p 8 byte)
          (equal (fn2-layout-byte k pos (fn2-layout-proof-accumulator tag pos x)
                                  0 0 0 byte)
                 (fn2-layout-proof-expected-header k pos x))))))
;; Split off one digit without expanding MOD into a nest of floors.
(local
 (defthm fn2-layout-proof-low-digits
   (implies (and (natp x) (posp s) (posp radix))
            (equal (+ (mod x s) (* s (mod (floor x s) radix)))
                   (mod x (* s radix))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable mod)))))
(local
 (defthm fn2-layout-proof-high-digits
   (implies (and (natp x) (posp s) (posp radix))
            (equal (+ (* radix (floor x (* s radix))) (mod (floor x s) radix))
                   (floor x s)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable mod)))))
(local
 (defthm fn2-layout-proof-shift-right
   (implies (and (integerp x) (natp n))
            (equal (ash x (- n)) (floor x (expt 2 n))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable ash floor)))))
(local
 (defthm fn2-layout-proof-shift-left
   (implies (and (integerp x) (natp n))
            (equal (ash x n) (* (expt 2 n) x)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable ash)))))
(local
 (defthm fn2-layout-proof-word-arith
   (let* ((q (floor x s)) (digit (mod q 256)))
     (implies (and (natp x) (posp s))
              (and (unsigned-byte-p 8 digit)
                   (equal (+ (mod x s) (* s digit)) (mod x (* s 256)))
                   (equal (+ (* 256 (floor x (* s 256))) digit) q)
                   (implies (< x (* s 256)) (and (equal (mod x (* s 256)) x)
                                                 (equal (floor x (* s 256)) 0)))
                   (implies (< x (* s 16)) (< digit 16)))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-layout-proof-low-digits (radix 256))
                         (:instance fn2-layout-proof-high-digits (radix 256))
                         (:instance floor-bounds-1 (y s)))
            :in-theory (disable floor) :nonlinearp t))))
(local
 (defmacro fn2-layout-proof-inverse-word (name tag width endian)
   (let ((limit (if (equal tag 9) '(len (caddr k)) '(nfix (cadr k)))))
     `(defthm ,name
        (implies (and (equal (fn2-layout-kind-code k) ,tag) (natp pos) (< pos ,width)
                      (fn2-layout-proof-number-okp ,tag x ,limit))
                 (fn2-layout-proof-header-inverse k pos x))
        :rule-classes nil
        :hints (("Goal" :backchain-limit-rw 1 :cases ,(take width '((equal pos 0) (equal pos 1) (equal pos 2)
                                            (equal pos 3) (equal pos 4) (equal pos 5)
                                            (equal pos 6) (equal pos 7)))

                 :use ((:instance fn2-layout-proof-word-arith
                         (s ,(if (equal endian :be) `(expt 256 (nfix (- ,(1- width) pos))) '(expt 256 pos))))
                       (:instance fn2-layout-proof-shift-right
                         (n ,(if (equal endian :be) `(* 8 (nfix (- ,(1- width) (min pos ,(1- width))))) '(* 8 (min
                             pos 7)))))
                       (:instance fn2-layout-proof-shift-left (x (fn2-layout-proof-emit-digit ,tag pos x)) (n (* 8
                           (min pos 7)))))
                 :in-theory (union-theories
                             '(fn2-layout-byte fn2-layout-proof-header-inverse fn2-layout-proof-number-okp
                               fn2-layout-proof-expected-header fn2-layout-proof-prefix-size
                                   fn2-layout-proof-accumulator
                               fn2-layout-proof-emit-digit natp nfix min member-equal unsigned-byte-p integer-range-p
                               integerp-mod mod-x-1 floor-x-1 |(* 1 x)| |(+ 0 x)| |(* 0 x)| |(+ y x)| |(* y x)|
                               default-car default-cdr)
                             (theory 'fn2-layout-proof-ground))))))))
(local (fn2-layout-proof-inverse-word fn2-layout-proof-inv-u8 1 1 :le))
(local (fn2-layout-proof-inverse-word fn2-layout-proof-inv-u16 2 2 :le))
(local (fn2-layout-proof-inverse-word fn2-layout-proof-inv-u32 3 4 :le))
(local (fn2-layout-proof-inverse-word fn2-layout-proof-inv-u64 4 8 :le))
(local (fn2-layout-proof-inverse-word fn2-layout-proof-inv-u16be 12 2 :be))
(local (fn2-layout-proof-inverse-word fn2-layout-proof-inv-u32be 13 4 :be))
(local (fn2-layout-proof-inverse-word fn2-layout-proof-inv-u64be 14 8 :be))
(local (fn2-layout-proof-inverse-word fn2-layout-proof-inv-octets16 15 2 :be))
(local (fn2-layout-proof-inverse-word fn2-layout-proof-inv-octets32 16 4 :be))
(local (fn2-layout-proof-inverse-word fn2-layout-proof-inv-bool 6 1 :le))
(local (fn2-layout-proof-inverse-word fn2-layout-proof-inv-digest 7 1 :le))
(local (fn2-layout-proof-inverse-word fn2-layout-proof-inv-enum 9 1 :le))
(local
 (defun fn2-layout-proof-power128 (n)
   (if (zp n) 1 (* 128 (fn2-layout-proof-power128 (1- n))))))
(local
 (defthm fn2-layout-proof-power128-positive
   (posp (fn2-layout-proof-power128 n)) :rule-classes :type-prescription))
(local (in-theory (disable fn2-layout-proof-power128)))
(local
 (defun fn2-layout-proof-var-ind (pos x)
   (if (or (zp pos) (< (nfix x) 128)) (list pos x)
     (fn2-layout-proof-var-ind (1- pos) (floor (nfix x) 128)))))
(local
 (defthm fn2-layout-proof-varsize-limit
   (implies (and (natp x) (natp pos))
            (equal (< pos (fn2-layout-varsize x))
                   (or (zp pos) (<= (fn2-layout-proof-power128 pos) x))))
   :hints (("Goal" :induct (fn2-layout-proof-var-ind pos x)
            :expand ((fn2-layout-varsize x) (fn2-layout-proof-power128 pos)))
           ("Subgoal *1/2" :use ((:instance floor-bounds-1 (y 128)))
            :in-theory (disable floor)))))
(local
 (defthm fn2-layout-proof-varsize-positive
   (posp (fn2-layout-varsize x)) :rule-classes :type-prescription))
(local
 (defthm fn2-layout-proof-varsize-u60
   (implies (unsigned-byte-p 60 x) (<= (fn2-layout-varsize x) 9))
   :hints (("Goal" :use ((:instance fn2-layout-proof-varsize-limit (pos 9)))
            :in-theory (disable fn2-layout-proof-varsize-limit fn2-layout-varsize)))))
(local
 (defthm fn2-layout-proof-varsize-last
   (implies (and (natp pos) (natp x) (< pos (fn2-layout-varsize x)))
            (equal (equal (1+ pos) (fn2-layout-varsize x))
                   (< x (fn2-layout-proof-power128 (1+ pos)))))
   :hints (("Goal" :use ((:instance fn2-layout-proof-varsize-limit (pos (1+ pos))))
            :in-theory (disable fn2-layout-proof-varsize-limit fn2-layout-varsize expt)))))
(local
 (defun fn2-layout-proof-group-byte (q)
   (+ (mod q 128) (if (< q 128) 0 128))))
(local
 (defthm fn2-layout-proof-group-bits
   (implies (natp q)
            (let ((b (fn2-layout-proof-group-byte q)))
              (and (unsigned-byte-p 8 b)
                   (equal (mod b 128) (mod q 128))
                   (equal (< b 128) (< q 128)))))
   :hints (("Goal" :in-theory (enable mod)))))
(local (in-theory (disable fn2-layout-proof-group-byte)))
(local
 (defthm fn2-layout-proof-group-arith
   (let* ((q (floor x s)) (lo (mod q 128)) (sum (+ (mod x s) (* s lo))))
     (implies (and (natp x) (posp s))
              (and (natp q)
                   (equal (< q 128) (< x (* 128 s)))
                   (implies (and (<= s x) (< q 128)) (< 0 lo))
                   (implies (< x (* s 16)) (< lo 16))
                   (implies (< q 128) (equal sum x))
                   (equal sum (mod x (* s 128))))))
   :rule-classes :rewrite
   :hints (("Goal" :use ((:instance fn2-layout-proof-low-digits (radix 128))
                         (:instance floor-bounds-1 (y s)))
            :in-theory (disable floor) :nonlinearp t))))
(local
 (defthm fn2-layout-proof-group-scale
   (let ((s (fn2-layout-proof-power128 pos)))
     (implies (and (natp pos) (< pos 9))
              (and (equal (expt 2 (* 7 (min 8 pos))) s)
                   (equal (expt 128 pos) s)
                   (equal (expt 128 (1+ pos)) (* 128 s))
                   (equal (fn2-layout-proof-power128 (1+ pos)) (* 128 s))
                   (natp (* 7 (min 8 pos)))
                   (implies (equal pos 8) (equal s 72057594037927936)))))
   :rule-classes :rewrite
   :hints (("Goal" :cases ((equal pos 0) (equal pos 1) (equal pos 2) (equal pos 3) (equal pos 4)
                           (equal pos 5) (equal pos 6) (equal pos 7) (equal pos 8))
            :in-theory (disable fn2-layout-proof-power128 expt min)))))
(local
 (defthm fn2-layout-proof-group-emit
   (implies (and (natp pos) (< pos 9) (natp x))
            (equal (fn2-layout-proof-emit-digit 5 pos x)
                   (fn2-layout-proof-group-byte (floor x (fn2-layout-proof-power128 pos)))))
   :hints (("Goal" :use (fn2-layout-proof-group-scale
                         (:instance fn2-layout-proof-shift-right (n (* 7 (min 8 pos)))))
            :in-theory (e/d (fn2-layout-proof-group-byte)
                             (fn2-layout-proof-group-bits min expt ash floor mod)))) ))
(local
 (defthm fn2-layout-proof-group-ash
   (implies (and (natp pos) (< pos 9) (integerp digit))
            (equal (ash digit (* 7 (min 8 pos))) (* (fn2-layout-proof-power128 pos) digit)))
   :hints (("Goal" :use (fn2-layout-proof-group-scale
                         (:instance fn2-layout-proof-shift-left (x digit) (n (* 7 (min 8 pos)))))
            :in-theory (disable min expt ash floor mod)))))
(local
 (defthm fn2-layout-proof-group-fields
   (let* ((byte (fn2-layout-proof-group-byte (floor x s))) (low (mod byte 128)))
     (implies (and (natp x) (posp s))
              (and (unsigned-byte-p 8 byte) (integerp low)
                   (equal (< byte 128) (< x (* 128 s)))
                   (implies (and (<= s x) (< x (* 128 s))) (< 0 low))
                   (implies (< x (* 16 s)) (< low 16))
                   (equal (+ (mod x s) (* s low))
                          (if (< x (* 128 s)) x (mod x (* 128 s)))))))
   :rule-classes nil
   :hints (("Goal" :use (fn2-layout-proof-group-arith (:instance fn2-layout-proof-group-bits (q (floor x s))))
            :in-theory (union-theories '(integerp-mod unsigned-byte-p integer-range-p natp |(* y x)|)
                                       (theory 'fn2-layout-proof-ground))))))
(local
 (defthm fn2-layout-proof-group-position
   (let ((s (fn2-layout-proof-power128 pos)))
     (implies (and (unsigned-byte-p 60 x) (natp pos) (< pos (fn2-layout-varsize x)))
              (and (natp x) (posp s) (< pos 9)
                   (implies (equal pos 8) (< x (* 16 s)))
                   (implies (< 0 pos) (<= s x))
                   (equal (equal (1+ pos) (fn2-layout-varsize x)) (< x (* 128 s))))))
   :rule-classes nil
   :hints (("Goal" :use (fn2-layout-proof-varsize-u60 fn2-layout-proof-varsize-limit
                         fn2-layout-proof-varsize-last fn2-layout-proof-group-scale)
            :in-theory (union-theories '(unsigned-byte-p integer-range-p natp zp-open
                                        fn2-layout-proof-power128-positive)
                                       (theory 'fn2-layout-proof-ground))))))
(local
 (defthm fn2-layout-proof-group-acc
   (implies (and (natp x) (natp pos) (< pos 9))
            (and (equal (fn2-layout-proof-accumulator 5 pos x) (mod x (fn2-layout-proof-power128 pos)))
                 (equal (fn2-layout-proof-accumulator 5 (1+ pos) x) (mod x (* 128 (fn2-layout-proof-power128 pos))))))
   :rule-classes nil
   :hints (("Goal" :cases ((equal pos 0)) :use fn2-layout-proof-group-scale
            :in-theory (union-theories '(fn2-layout-proof-accumulator natp zp-open mod-x-1)
                                       (theory 'fn2-layout-proof-ground))))))
(local
 (defthm fn2-layout-proof-group-step
   (let* ((byte (fn2-layout-proof-emit-digit 5 pos x)) (low (mod byte 128))
          (last (equal (1+ pos) (fn2-layout-varsize x))))
     (implies (and (unsigned-byte-p 60 x) (natp pos) (< pos (fn2-layout-varsize x)))
              (and (unsigned-byte-p 8 byte) (<= pos 8)
                   (implies (equal pos 8) (< low 16))
                   (equal (< byte 128) last)
                   (implies (and last (< 0 pos)) (< 0 low))
                   (equal (+ (fn2-layout-proof-accumulator 5 pos x)
                             (ash low (* 7 (min 8 pos))))
                          (if last x (fn2-layout-proof-accumulator 5 (1+ pos) x))))))
   :rule-classes nil
   :hints (("Goal"
            :use (fn2-layout-proof-group-position fn2-layout-proof-group-acc
                  (:instance fn2-layout-proof-group-fields (s (fn2-layout-proof-power128 pos))))
            :in-theory (union-theories '(fn2-layout-proof-group-ash fn2-layout-proof-group-emit natp)
                                       (theory 'minimal-theory))))))
(local
 (defthm fn2-layout-proof-var-tag-digits
   (implies (member tag '(5 8 10))
            (and (equal (fn2-layout-proof-accumulator tag pos x) (fn2-layout-proof-accumulator 5 pos x))
                 (equal (fn2-layout-proof-emit-digit tag pos x) (fn2-layout-proof-emit-digit 5 pos x))))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable min expt ash mod)))))
(local
 (defthm fn2-layout-proof-var-header-inverse
   (let ((tag (fn2-layout-kind-code k)))
     (implies (and (member tag '(5 8 10)) (natp pos) (< pos (fn2-layout-varsize x))
                   (fn2-layout-proof-number-okp tag x (nfix (cadr k))))
              (fn2-layout-proof-header-inverse k pos x)))
   :rule-classes nil
   :hints (("Goal" :use (fn2-layout-proof-group-step
                         (:instance fn2-layout-proof-var-tag-digits (tag (fn2-layout-kind-code k)))
                         (:instance fn2-layout-proof-var-tag-digits (tag (fn2-layout-kind-code k)) (pos (1+ pos))))
            :in-theory (union-theories
                         '(fn2-layout-byte fn2-layout-proof-header-inverse fn2-layout-proof-expected-header
                           fn2-layout-proof-number-okp fn2-layout-proof-prefix-size member-equal
                           unsigned-byte-p integer-range-p natp nfix)
                         (theory 'fn2-layout-proof-ground))))))
(local
 (defthm fn2-layout-proof-header-digit-inverse
   (let ((tag (fn2-layout-kind-code k)))
     (implies (and (natp pos) (< pos (fn2-layout-proof-prefix-size tag x))
                   (fn2-layout-proof-number-okp tag x
                    (if (= tag 9) (len (caddr k)) (nfix (cadr k)))))
              (fn2-layout-proof-header-inverse k pos x)))
   :rule-classes nil
   :hints (("Goal" :cases ((equal (fn2-layout-kind-code k) 1) (equal (fn2-layout-kind-code k) 2) (equal
       (fn2-layout-kind-code k) 3) (equal (fn2-layout-kind-code k) 4) (equal (fn2-layout-kind-code k) 5) (equal
       (fn2-layout-kind-code k) 6) (equal (fn2-layout-kind-code k) 7) (equal (fn2-layout-kind-code k) 8) (equal
       (fn2-layout-kind-code k) 9) (equal (fn2-layout-kind-code k) 10) (equal (fn2-layout-kind-code k) 11) (equal
       (fn2-layout-kind-code k) 12) (equal (fn2-layout-kind-code k) 13) (equal (fn2-layout-kind-code k) 14) (equal
       (fn2-layout-kind-code k) 15) (equal (fn2-layout-kind-code k) 16))
            :use (fn2-layout-proof-inv-u8 fn2-layout-proof-inv-u16
                         fn2-layout-proof-inv-u32 fn2-layout-proof-inv-u64
                         fn2-layout-proof-inv-u16be fn2-layout-proof-inv-u32be
                         fn2-layout-proof-inv-u64be fn2-layout-proof-inv-octets16
                         fn2-layout-proof-inv-octets32 fn2-layout-proof-inv-bool
                         fn2-layout-proof-inv-digest fn2-layout-proof-inv-enum
                         fn2-layout-proof-var-header-inverse)
            :in-theory (disable fn2-layout-proof-header-inverse fn2-layout-kind-code
                                fn2-layout-proof-number-okp fn2-layout-varsize)))))
(local
 (defun-nx fn2-layout-proof-magnitude (k i f)
   (if (member (fn2-layout-kind-code k) '(10 15 16))
       (fn2-fields-ref-len i f) (fn2-fields-value i f))))
(local
 (defthm fn2-layout-proof-emit-header
   (let* ((tag (fn2-layout-kind-code k)) (x (fn2-layout-proof-magnitude k i f)))
     (implies (< pos (fn2-layout-proof-prefix-size tag x))
              (equal (fn2-layout-emit-byte k i pos slot gen next okind oslot ogen f p)
                     (fn2-pool-write slot gen next (fn2-layout-proof-emit-digit tag pos x)
                                     okind oslot ogen p))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn2-layout-emit-byte)
                         (fn2-layout-kind-code fn2-fields-value fn2-fields-ref-len
                          fn2-layout-varsize fn2-pool-write fn2-layout-copy ash mod))))))

(local (in-theory (disable fn2-pool-base fn2-pool-cap fn2-pool-fill fn2-pool-datai
                           fn2-pool-data-length fn2-pool-state fn2-pool-ownerp
                           fn2-pool-rows fn2-pool-gen fn2-poolp fn2-pool-wfp
                           fn2-pool-semanticp fn2-pool-workspace-code fn2-pool-readable-code
                           fn2-pool-out-count fn2-pool-query-ref-count)))
(local
 (defthm fn2-layout-proof-workspace-readable
   (implies (equal (fn2-pool-workspace-code slot gen okind oslot ogen p) :ok)
            (equal (fn2-pool-readable-code slot gen okind oslot ogen p) :ok))
   :hints (("Goal" :in-theory (e/d (fn2-pool-workspace-code fn2-pool-readable-code)
                                   (fn2-pool-handle-code))))))
(local
 (defthm fn2-layout-proof-range-step
   (implies (and (equal (fn2-layout-range-code slot gen start end writep okind oslot ogen p) :ok)
                 (natp next) (<= start next) (< next end)
                 (or (not writep) (<= next (fn2-pool-fill slot p))))
            (and (equal (fn2-layout-range-code slot gen next (1+ next) writep okind oslot ogen p) :ok)
                 (implies (not writep)
                          (equal (fn2-pool-read slot gen next okind oslot ogen p)
                                 (list :ok (fn2-pool-datai (+ (fn2-pool-base slot p) next) p))))))
   :hints (("Goal" :in-theory (enable fn2-pool-read fn2-layout-range-code)))))
(local
 (defthm fn2-layout-proof-after-write
   (let* ((w (fn2-pool-write slot gen next byte okind oslot ogen p)) (q (mv-nth 1 w)))
     (implies (and (equal (fn2-layout-range-code slot gen next end t okind oslot ogen p) :ok)
                   (< next end) (unsigned-byte-p 8 byte))
              (and (equal (mv-nth 0 w) :ok)
                   (equal q (fn2-pool-set-fill slot (max (fn2-pool-fill slot p) (1+ next))
                              (update-fn2-pool-datai (+ (fn2-pool-base slot p) next) byte p))))))
   :hints (("Goal" :in-theory (enable fn2-pool-write fn2-layout-range-code)))))
(local
 (defthm fn2-layout-proof-semantic-types
   (implies (fn2-pool-semanticp p) (and (fn2-poolp p) (fn2-pool-wfp p)))
   :hints (("Goal" :in-theory (e/d (fn2-pool-semanticp)
                           (fn2-pool-row-invariantp fn2-pool-class-accountsp fn2-pool-retired-slots))))))
(local
 (defthm fn2-layout-proof-readable-row
   (implies (equal (fn2-layout-range-code slot gen start end writep okind oslot ogen p) :ok)
            (and (natp slot) (< slot (fn2-pool-rows p))
                 (unsigned-byte-p 32 start) (unsigned-byte-p 32 end)
                 (<= start end) (<= start (fn2-pool-fill slot p))
                 (<= end (if writep (fn2-pool-cap slot p) (fn2-pool-fill slot p)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn2-layout-range-code fn2-pool-workspace-code
                                      fn2-pool-readable-code fn2-pool-handle-code)))))
(local
 (defthm fn2-layout-proof-fill-and-byte
   (let ((q (fn2-pool-set-fill slot new-fill (update-fn2-pool-datai addr byte p))))
     (and (equal (fn2-pool-base other q) (fn2-pool-base other p))
          (equal (fn2-pool-cap other q) (fn2-pool-cap other p))
          (equal (fn2-pool-fill other q)
                 (if (equal (nfix slot) (nfix other)) new-fill (fn2-pool-fill other p)))
          (equal (fn2-pool-datai a q)
                 (if (equal (nfix a) (nfix addr)) byte (fn2-pool-datai a p)))
          (equal (fn2-pool-rows q) (fn2-pool-rows p))
          (equal (fn2-pool-workspace-code other g k s h q) (fn2-pool-workspace-code other g k s h p))
          (equal (fn2-pool-readable-code other g k s h q) (fn2-pool-readable-code other g k s h p))))
   :hints (("Goal" :in-theory (e/d (fn2-pool-base fn2-pool-cap fn2-pool-fill fn2-pool-datai
                       fn2-pool-workspace-code fn2-pool-readable-code fn2-pool-handle-code
                       fn2-pool-ownerp fn2-pool-state fn2-pool-rows fn2-pool-gen
                       fn2-pool-out-count fn2-pool-query-ref-count fn2-pool-set-fill update-fn2-pool-fill$ai
                           update-fn2-pool-datai)
                       (nth update-nth))))))
(local
 (defthm fn2-layout-proof-data-length-of-put
   (implies (and (natp addr) (< addr (fn2-pool-data-length p)))
            (equal (fn2-pool-data-length (fn2-pool-set-fill slot new-fill (update-fn2-pool-datai addr byte p)))
                   (fn2-pool-data-length p)))
   :hints (("Goal" :in-theory (e/d (fn2-pool-data-length fn2-pool-set-fill update-fn2-pool-fill$ai
       update-fn2-pool-datai) (nth update-nth))))))
(local (in-theory (disable fn2-pool-set-fill update-fn2-pool-datai)))
(local
 (defthm fn2-layout-proof-put-range-frame
   (let* ((base (fn2-pool-base slot p)) (addr (+ base next))
          (q (fn2-pool-set-fill slot (max (fn2-pool-fill slot p) (1+ next))
                                (update-fn2-pool-datai addr byte p))))
     (implies (and (natp slot) (natp src) (natp addr) (< addr (fn2-pool-data-length p))
                   (equal (fn2-layout-range-code src g a b nil okind oslot ogen p) :ok))
              (equal (fn2-layout-range-code src g a b nil okind oslot ogen q) :ok)))
   :hints (("Goal" :in-theory (enable fn2-layout-range-code)))))
(local
 (defthm fn2-layout-proof-range-advance
   (let* ((addr (+ (fn2-pool-base slot p) next))
          (q (fn2-pool-set-fill slot (max (fn2-pool-fill slot p) (1+ next))
                                (update-fn2-pool-datai addr byte p))))
     (implies (and (natp addr) (equal (fn2-layout-range-code slot gen next end t okind oslot ogen p) :ok)
                   (< next end))
              (and (< addr (fn2-pool-data-length p))
                   (equal (fn2-layout-range-code slot gen (1+ next) end t okind oslot ogen q) :ok))))
   :hints (("Goal" :in-theory (enable fn2-layout-range-code)))))
(local
 (defthm fn2-layout-proof-write-step
   (let* ((w (fn2-pool-write slot gen next byte okind oslot ogen p)) (q (mv-nth 1 w)))
     (implies (and (fn2-pool-semanticp p)
                   (equal (fn2-layout-range-code slot gen next end t okind oslot ogen p) :ok)
                   (< next end) (unsigned-byte-p 8 byte))
              (and (equal (mv-nth 0 w) :ok)
                   (fn2-pool-semanticp q)
                   (equal (fn2-layout-range-code slot gen (1+ next) end t okind oslot ogen q) :ok)
                   (equal (fn2-pool-base src q) (fn2-pool-base src p))
                   (equal (fn2-pool-datai (+ (fn2-pool-base slot p) next) q) byte)
                   (implies (equal (fn2-layout-range-code src g a b nil okind oslot ogen p) :ok)
                            (equal (fn2-layout-range-code src g a b nil okind oslot ogen q) :ok))
                   (implies (and (natp n) (natp abs)
                                 (or (<= (+ abs n) (+ (fn2-pool-base slot p) next))
                                     (< (+ (fn2-pool-base slot p) next) abs)))
                            (equal (fn2-pool-logical-octets n abs q)
                                   (fn2-pool-logical-octets n abs p))))))
   :rule-classes nil
   :hints (("Goal" :use (fn2-layout-proof-put-range-frame fn2-layout-proof-range-advance
                         (:instance fn2-layout-proof-readable-row (start next) (writep t))
                         (:instance fn2-pool-semanticp-row-bounds (fn2-pool p) (i slot))
                         (:instance fn2-layout-proof-readable-row (slot src) (gen g) (start a) (end b) (writep nil))
                         (:instance fn2-pool-write-conservation (fn2-pool p) (idx next)))
            :in-theory (disable fn2-layout-range-code fn2-pool-write-conservation fn2-pool-write
                                fn2-pool-logical-octets fn2-pool-set-fill max unsigned-byte-p)))))
(local
 (defthm fn2-layout-proof-apart
   (implies (and (fn2-pool-semanticp p)
                 (equal (fn2-layout-range-code src g a b nil okind oslot ogen p) :ok)
                 (equal (fn2-layout-range-code slot gen next end t okind oslot ogen p) :ok)
                 (< next end) (or (not (equal slot src)) (< next a) (<= b next)))
            (or (< (+ (fn2-pool-base slot p) next) (+ (fn2-pool-base src p) a))
                (<= (+ (fn2-pool-base src p) b) (+ (fn2-pool-base slot p) next))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-layout-proof-readable-row (start next) (writep t))
                         (:instance fn2-layout-proof-readable-row (start a) (end b) (slot src) (gen g) (writep nil))
                         (:instance fn2-pool-semanticp-row-bounds (fn2-pool p) (i src))
                         (:instance fn2-pool-extents-apart (fn2-pool p) (i src) (j slot)))))))
(local (in-theory (disable fn2-layout-proof-after-write fn2-layout-proof-range-advance
                           fn2-layout-proof-put-range-frame fn2-pool-logical-octets
                           fn2-layout-kind-code fn2-fields-value fn2-fields-ref-slot
                           fn2-fields-ref-gen fn2-fields-ref-off fn2-fields-ref-len
                           fn2-fields-rows fn2-fieldsp fn2-fields-wfp)))
(local
 (defun-nx fn2-layout-proof-reference-ok (k i slot lo end okind oslot ogen f p)
   (let ((src (fn2-fields-ref-slot i f)) (g (fn2-fields-ref-gen i f))
         (a (fn2-fields-ref-off i f)) (n (fn2-fields-ref-len i f)))
     (or (not (member (fn2-layout-kind-code k) '(7 10 15 16)))
         (and (natp a) (natp n)
              (equal (fn2-layout-range-code src g a (+ a n) nil okind oslot ogen p) :ok)
              (or (zp n) (not (equal src slot)) (<= (+ a n) lo) (<= end a)))))))
(local
 (defun-nx fn2-layout-proof-refs (layout i slot lo end okind oslot ogen f p)
   (if (atom layout) t
     (and (fn2-layout-proof-reference-ok (cadar layout) i slot lo end okind oslot ogen f p)
          (fn2-layout-proof-refs (cdr layout) (1+ i) slot lo end okind oslot ogen f p)))))
(local
 (defthm fn2-layout-proof-refs-from-preflight
   (implies (and (fn2-fieldsp f) (fn2-fields-wfp f) (natp i)
                 (equal (fn2-layout-check-values layout i slot lo end okind oslot ogen f p) :ok))
            (fn2-layout-proof-refs layout i slot lo end okind oslot ogen f p))
   :hints (("Goal" :induct (fn2-layout-proof-refs layout i slot lo end okind oslot ogen f p)
            :expand ((fn2-layout-check-values layout i slot lo end okind oslot ogen f p))
            :in-theory (disable unsigned-byte-p)))))
(local
 (defun-nx fn2-layout-proof-payload (i f p)
   (fn2-pool-logical-octets
    (fn2-fields-ref-len i f)
    (+ (fn2-pool-base (fn2-fields-ref-slot i f) p) (fn2-fields-ref-off i f)) p)))
(local
 (defthm fn2-layout-proof-empty-payload
   (equal (fn2-pool-logical-octets 0 addr p) nil)
   :hints (("Goal" :expand ((fn2-pool-logical-octets 0 addr p))))))
(local
 (defthm fn2-layout-proof-reference-frame
   (let ((q (mv-nth 1 (fn2-pool-write slot gen next byte okind oslot ogen p))))
     (implies (and (fn2-pool-semanticp p) (unsigned-byte-p 8 byte)
                   (equal (fn2-layout-range-code slot gen next end t okind oslot ogen p) :ok)
                   (<= lo next) (< next end)
                   (fn2-layout-proof-reference-ok k i slot lo end okind oslot ogen f p))
              (and (fn2-layout-proof-reference-ok k i slot lo end okind oslot ogen f q)
                   (implies (member (fn2-layout-kind-code k) '(7 10 15 16))
                            (equal (fn2-layout-proof-payload i f q)
                                   (fn2-layout-proof-payload i f p))))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-layout-proof-apart
                            (src (fn2-fields-ref-slot i f)) (g (fn2-fields-ref-gen i f))
                            (a (fn2-fields-ref-off i f))
                            (b (+ (fn2-fields-ref-off i f) (fn2-fields-ref-len i f))))
                         (:instance fn2-layout-proof-write-step
                            (src (fn2-fields-ref-slot i f)) (g (fn2-fields-ref-gen i f))
                            (a (fn2-fields-ref-off i f))
                            (b (+ (fn2-fields-ref-off i f) (fn2-fields-ref-len i f)))
                            (n (fn2-fields-ref-len i f))
                            (abs (+ (fn2-pool-base (fn2-fields-ref-slot i f) p) (fn2-fields-ref-off i f))))
                         (:instance fn2-pool-semanticp-row-bounds (fn2-pool p) (i (fn2-fields-ref-slot i f)))
                         (:instance fn2-layout-proof-readable-row (slot (fn2-fields-ref-slot i f))
                            (gen (fn2-fields-ref-gen i f)) (start (fn2-fields-ref-off i f))
                            (end (+ (fn2-fields-ref-off i f) (fn2-fields-ref-len i f))) (writep nil)))
            :in-theory (union-theories '(fn2-layout-proof-reference-ok fn2-layout-proof-payload
                fn2-layout-proof-semantic-types fn2-pool-logical-octets car-cons cdr-cons default-car default-cdr
                nth-0-cons nth-add1) (theory 'fn2-layout-proof-list-index-rules))))))
(local
 (defthm fn2-layout-proof-layout-frame
   (let ((q (mv-nth 1 (fn2-pool-write slot gen next byte okind oslot ogen p))))
     (implies (and (fn2-pool-semanticp p) (unsigned-byte-p 8 byte)
                   (equal (fn2-layout-range-code slot gen next end t okind oslot ogen p) :ok)
                   (<= lo next) (< next end) (natp i)
                   (fn2-layout-proof-refs layout i slot lo end okind oslot ogen f p))
              (and (fn2-layout-proof-refs layout i slot lo end okind oslot ogen f q)
                   (equal (fn2-layout-values layout i f q) (fn2-layout-values layout i f p)))))
   :rule-classes nil
   :hints (("Goal" :induct (fn2-layout-proof-refs layout i slot lo end okind oslot ogen f p)
            :expand ((:free (q) (fn2-layout-values layout i f q)))
            :in-theory (disable fn2-layout-proof-reference-ok fn2-pool-write unsigned-byte-p))
           ("Subgoal *1/2" :use ((:instance fn2-layout-proof-reference-frame (k (cadar layout))))))))
(local
 (defthm fn2-layout-proof-write-pair
   (let ((w (fn2-pool-write slot gen next byte okind oslot ogen p)))
     (equal (list (car w) (mv-nth 1 w)) w))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn2-pool-write)))))
(local
 (defthm fn2-layout-proof-copy-one
   (implies (and (fn2-pool-semanticp p)
                 (equal (fn2-layout-range-code src g a b nil okind oslot ogen p) :ok)
                 (equal (fn2-layout-range-code slot gen next end t okind oslot ogen p) :ok)
                 (natp at) (<= a at) (< at b) (< next end)
                 (or (not (equal src slot)) (< at next) (< next at)))
            (equal (fn2-layout-copy src g at slot gen next 1 okind oslot ogen p)
                   (fn2-pool-write slot gen next (fn2-pool-datai (+ (fn2-pool-base src p) at) p)
                                   okind oslot ogen p)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-layout-proof-write-pair (byte (fn2-pool-datai (+ (fn2-pool-base src p) at) p)))
                         (:instance fn2-layout-proof-readable-row (slot src) (gen g) (start a) (end b) (writep nil))
                         (:instance fn2-layout-proof-readable-row (start next) (writep t))
                         (:instance fn2-layout-proof-range-step (slot src) (gen g) (start a) (end b) (next at)
                             (writep nil))
                         (:instance fn2-layout-proof-range-step (start next) (writep t)))
            :expand ((:free (src slot) (fn2-layout-copy-loop src g at slot gen next 1 okind oslot ogen p))
                     (:free (i j q src slot) (fn2-layout-copy-loop src g i slot gen j 0 okind oslot ogen q)))
            :in-theory (e/d (fn2-layout-copy) (fn2-pool-read fn2-pool-write fn2-layout-proof-range-step))))))
(local
 (defthm fn2-layout-proof-readable-byte
   (implies (and (fn2-pool-semanticp p) (equal (fn2-layout-range-code src g a b nil okind oslot ogen p) :ok)
                 (natp at) (<= a at) (< at b))
            (unsigned-byte-p 8 (fn2-pool-datai (+ (fn2-pool-base src p) at) p)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-layout-proof-range-step (slot src) (gen g) (start a) (end b) (next at)
       (writep nil))
                         (:instance fn2-pool-read-byte-type (slot src) (gen g) (idx at) (fn2-pool p)))
            :in-theory (disable fn2-pool-read unsigned-byte-p fn2-layout-proof-range-step)))))

(local
 (defun fn2-layout-proof-payload-tagp (k)
   (member (fn2-layout-kind-code k) '(7 10 15 16))))
(local
 (defun fn2-layout-proof-bytes-of-value (k val)
   (if (equal (fn2-layout-kind-code k) 7) (cdr val) val)))
(local
 (defun fn2-layout-proof-bytes-from (k x size pos val)
   (declare (xargs :measure (nfix (- (nfix size) (nfix pos)))))
   (let* ((pos (nfix pos)) (tag (fn2-layout-kind-code k))
          (prefix (fn2-layout-proof-prefix-size tag x)))
     (cond ((>= pos (nfix size)) nil)
           ((and (fn2-layout-proof-payload-tagp k) (>= pos prefix))
            (nthcdr (- pos prefix) (fn2-layout-proof-bytes-of-value k val)))
           (t (cons (fn2-layout-proof-emit-digit tag pos x)
                    (fn2-layout-proof-bytes-from k x size (1+ pos) val)))))))
(local
 (defun-nx fn2-layout-proof-wire (layout i pos f values)
   (if (atom layout) nil
     (let ((k (cadar layout)))
       (append (fn2-layout-proof-bytes-from k (fn2-layout-proof-magnitude k i f)
                                             (fn2-layout-field-size k i f) pos (car values))
               (fn2-layout-proof-wire (cdr layout) (1+ i) 0 f (cdr values)))))))
(local
 (defun-nx fn2-layout-proof-value-at (k i f p)
   (let ((v (fn2-fields-value i f)) (bytes (fn2-layout-proof-payload i f p)))
     (case (fn2-layout-kind-code k)
       (7 (cons v bytes)) ((10 15 16) bytes) (11 nil) (otherwise v)))))
(local
 (defthm fn2-layout-proof-fields-view
   (implies (and (consp layout) (natp i))
            (and (equal (car (fn2-layout-values layout i f p))
                        (fn2-layout-proof-value-at (cadar layout) i f p))
                 (equal (cdr (fn2-layout-values layout i f p))
                        (fn2-layout-values (cdr layout) (1+ i) f p))))
   :hints (("Goal" :expand ((fn2-layout-values layout i f p))))))
(local
 (defthm fn2-layout-proof-payload-length
   (equal (len (fn2-pool-logical-octets n a p)) (nfix n))
   :hints (("Goal" :in-theory (enable fn2-pool-logical-octets)))))
(local
 (defun fn2-layout-proof-offset-ind (j n a)
   (if (zp j) (list n a)
     (fn2-layout-proof-offset-ind (1- j) (1- n) (1+ a)))))
(local
 (defthm fn2-layout-proof-nth-in-payload
   (implies (and (natp j) (natp n) (< j n) (natp a))
            (equal (nth j (fn2-pool-logical-octets n a p))
                   (fn2-pool-datai (+ a j) p)))
   :hints (("Goal" :induct (fn2-layout-proof-offset-ind j n a)
            :expand ((fn2-pool-logical-octets n a p) (:free (v xs) (nth j (cons v xs))))
            :in-theory (enable fn2-pool-logical-octets)))))
(local
 (defun-nx fn2-layout-proof-shape (k i f)
   (let* ((tag (fn2-layout-kind-code k)) (x (fn2-layout-proof-magnitude k i f))
          (n (fn2-fields-ref-len i f)) (size (fn2-layout-field-size k i f)))
     (and (natp size) (natp n)
          (if (equal tag 11)
              (and (equal k (list :zero (nfix (cadr k)))) (equal size (cadr k)))
            (and (fn2-layout-proof-number-okp tag x (if (= tag 9) (len (caddr k)) (nfix (cadr k))))
                 (implies (equal tag 7) (equal n 32))
                 (equal size (+ (fn2-layout-proof-prefix-size tag x)
                                (if (fn2-layout-proof-payload-tagp k) n 0)))))))))
(local
 (defun-nx fn2-layout-proof-shapes (layout i f)
   (if (atom layout) t
     (and (natp i) (< i (fn2-fields-rows f))
          (fn2-layout-proof-shape (cadar layout) i f)
          (fn2-layout-proof-shapes (cdr layout) (1+ i) f)))))
(local
 (defthm fn2-layout-proof-check-cons
   (implies (consp layout)
            (equal (equal (fn2-layout-check-values layout i slot lo end okind oslot ogen f p) :ok)
                   (and (equal (fn2-layout-check-values (list (car layout)) i slot lo end okind oslot ogen f p) :ok)
                        (equal (fn2-layout-check-values (cdr layout) (1+ i) slot lo end okind oslot ogen f p) :ok))))
   :rule-classes nil
   :hints (("Goal" :expand ((fn2-layout-check-values layout i slot lo end okind oslot ogen f p)
                            (fn2-layout-check-values (list (car layout)) i slot lo end okind oslot ogen f p)
                            (:free (j) (fn2-layout-check-values nil j slot lo end okind oslot ogen f p)))))))
(local
 (defthm fn2-layout-proof-field-shape
   (let ((k (cadr field)))
     (implies (and (fn2-layout-kindp k) (natp i) (fn2-fieldsp f) (fn2-fields-wfp f)
                   (equal (fn2-layout-check-values (list field) i slot lo end okind oslot ogen f p) :ok))
              (and (< i (fn2-fields-rows f)) (fn2-layout-proof-shape k i f))))
   :rule-classes nil
   :hints (("Goal" :backchain-limit-rw 0 :use ((:instance fn2-layout-proof-pair-shape (k (cadr field)))
                         (:instance fn2-fields-value-natp (fn2-fields f))
                         (:instance fn2-fields-value-bound (fn2-fields f))
                         (:instance fn2-fields-ref-len-natp (fn2-fields f))
                         (:instance fn2-fields-ref-len-bound (fn2-fields f)))
            :expand ((fn2-layout-check-values (list field) i slot lo end okind oslot ogen f p)
                     (:free (j) (fn2-layout-check-values nil j slot lo end okind oslot ogen f p)))
            :in-theory (e/d (fn2-layout-kind-code) (fn2-layout-varsize))
            :do-not-induct t))))
(local
 (defun fn2-layout-proof-layout-ind (layout i)
   (if (atom layout) i (fn2-layout-proof-layout-ind (cdr layout) (1+ i)))))
(local
 (defthm fn2-layout-proof-shapes-from-preflight
   (implies (and (fn2-layoutp layout) (fn2-fieldsp f) (fn2-fields-wfp f) (natp i)
                 (equal (fn2-layout-check-values layout i slot lo end okind oslot ogen f p) :ok))
            (fn2-layout-proof-shapes layout i f))
   :hints (("Goal" :induct (fn2-layout-proof-layout-ind layout i)
            :in-theory (disable fn2-layout-proof-shape fn2-layoutp fn2-layout-kindp))
           ("Subgoal *1/2" :use (fn2-layoutp-head fn2-layout-proof-check-cons
                                 (:instance fn2-layout-proof-field-shape (field (car layout))))))))

(local
 (defun fn2-layout-proof-wire-byte (k x pos val)
   (let* ((tag (fn2-layout-kind-code k)) (h (fn2-layout-proof-prefix-size tag x)))
     (if (and (fn2-layout-proof-payload-tagp k) (>= pos h))
         (nth (- pos h) (fn2-layout-proof-bytes-of-value k val))
       (fn2-layout-proof-emit-digit tag pos x)))))
(local
 (defthm fn2-layout-proof-digit-type
   (implies (and (natp x) (natp pos)) (unsigned-byte-p 8 (fn2-layout-proof-emit-digit tag pos x)))
   :hints (("Goal" :in-theory (disable ash)))))
(local
 (defthm fn2-layout-proof-payload-copy-call
   (let* ((x (fn2-layout-proof-magnitude k i f)) (h (fn2-layout-proof-prefix-size (fn2-layout-kind-code k) x)))
     (implies (and (fn2-layout-proof-payload-tagp k) (<= h pos))
              (equal (fn2-layout-emit-byte k i pos slot gen next okind oslot ogen f p)
                     (fn2-layout-copy (fn2-fields-ref-slot i f) (fn2-fields-ref-gen i f)
                        (+ (fn2-fields-ref-off i f) (- pos h)) slot gen next 1 okind oslot ogen p))))
   :hints (("Goal" :in-theory (e/d (fn2-layout-emit-byte) (fn2-layout-copy fn2-pool-write fn2-layout-varsize ash
       mod))))))
(local
 (defthm fn2-layout-proof-payload-wire-byte
   (let* ((h (fn2-layout-proof-prefix-size (fn2-layout-kind-code k) x))
          (a (fn2-fields-ref-off i f)) (src (fn2-fields-ref-slot i f)))
     (implies (and (fn2-layout-proof-payload-tagp k) (natp pos) (natp h) (<= h pos)
                   (natp a) (natp (fn2-fields-ref-len i f)) (< (- pos h) (fn2-fields-ref-len i f))
                   (natp (fn2-pool-base src p)))
              (equal (fn2-layout-proof-wire-byte k x pos (fn2-layout-proof-value-at k i f p))
                     (fn2-pool-datai (+ (fn2-pool-base src p) a (- pos h)) p))))
   :hints (("Goal" :in-theory (disable fn2-layout-proof-prefix-size fn2-layout-proof-emit-digit nth)))))
(local
 (defthm fn2-layout-proof-zero-byte
   (implies (equal (fn2-layout-kind-code k) 11)
            (and (equal (fn2-layout-proof-emit-digit 11 pos x) 0)
                 (equal (fn2-layout-emit-byte k i pos slot gen next okind oslot ogen f p)
                        (fn2-pool-write slot gen next 0 okind oslot ogen p))))
   :hints (("Goal" :in-theory (e/d (fn2-layout-emit-byte) (fn2-pool-write))))))
(local
 (defthm fn2-layout-proof-range-base
   (implies (and (fn2-pool-semanticp p)
                 (equal (fn2-layout-range-code src g a b nil okind oslot ogen p) :ok))
            (natp (fn2-pool-base src p)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-layout-proof-readable-row (slot src) (gen g) (start a) (end b) (writep nil))
                         (:instance fn2-pool-semanticp-row-bounds (fn2-pool p) (i src)))))))
(local
 (defthm fn2-layout-proof-source-index
   (let ((at (+ a (- pos h))))
     (implies (and (natp a) (natp n) (natp pos) (natp h) (<= h pos) (< pos (+ h n))
                   (<= lo next) (< next end)
                   (or (zp n) (not (equal src slot)) (<= (+ a n) lo) (<= end a)))
              (and (natp at) (<= a at) (< at (+ a n))
                   (or (not (equal src slot)) (< at next) (< next at)))))
   :rule-classes nil))
(local
 (defthm fn2-layout-proof-payload-transfer
   (let* ((at (+ a (- pos h))) (byte (fn2-pool-datai (+ (fn2-pool-base src p) at) p)))
     (implies (and (fn2-pool-semanticp p) (natp a) (natp n)
                   (equal (fn2-layout-range-code src g a (+ a n) nil okind oslot ogen p) :ok)
                   (or (zp n) (not (equal src slot)) (<= (+ a n) lo) (<= end a))
                   (equal (fn2-layout-range-code slot gen next end t okind oslot ogen p) :ok)
                   (natp pos) (natp h) (<= h pos) (< pos (+ h n)) (<= lo next) (< next end))
              (and (natp (fn2-pool-base src p)) (unsigned-byte-p 8 byte)
                   (equal (fn2-layout-copy src g at slot gen next 1 okind oslot ogen p)
                          (fn2-pool-write slot gen next byte okind oslot ogen p)))))
   :rule-classes nil
   :hints (("Goal" :use (fn2-layout-proof-source-index (:instance fn2-layout-proof-range-base (b (+ a n)))
                         (:instance fn2-layout-proof-copy-one (at (+ a (- pos h))) (b (+ a n)))
                         (:instance fn2-layout-proof-readable-byte (at (+ a (- pos h))) (b (+ a n))))
            :in-theory (theory 'minimal-theory)))))
(local
 (defthm fn2-layout-proof-emit-payload
   (let* ((tag (fn2-layout-kind-code k)) (x (fn2-layout-proof-magnitude k i f))
          (h (fn2-layout-proof-prefix-size tag x)) (len (fn2-fields-ref-len i f))
          (src (fn2-fields-ref-slot i f)) (a (fn2-fields-ref-off i f))
          (at (+ a (- pos h)))
          (byte (fn2-pool-datai (+ (fn2-pool-base src p) at) p)))
     (implies (and (fn2-layout-proof-payload-tagp k) (fn2-layout-proof-reference-ok k i slot lo end okind oslot ogen
         f p)
                   (fn2-pool-semanticp p) (equal (fn2-layout-range-code slot gen next end t okind oslot ogen p) :ok)
                   (natp pos) (natp h) (<= h pos) (< pos (+ h len)) (<= lo next) (< next end))
              (and (unsigned-byte-p 8 byte)
                   (equal (fn2-layout-proof-wire-byte k x pos (fn2-layout-proof-value-at k i f p)) byte)
                   (equal (fn2-layout-emit-byte k i pos slot gen next okind oslot ogen f p)
                          (fn2-pool-write slot gen next byte okind oslot ogen p)))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance fn2-layout-proof-payload-wire-byte (x (fn2-layout-proof-magnitude k i f)))
                  fn2-layout-proof-payload-copy-call
                  (:instance fn2-layout-proof-payload-transfer (src (fn2-fields-ref-slot i f)) (g
                      (fn2-fields-ref-gen i f))
                    (a (fn2-fields-ref-off i f)) (n (fn2-fields-ref-len i f))
                    (h (fn2-layout-proof-prefix-size (fn2-layout-kind-code k) (fn2-layout-proof-magnitude k i f)))))
            :in-theory (disable fn2-layout-proof-prefix-size fn2-layout-proof-magnitude fn2-layout-proof-wire-byte
                       fn2-layout-proof-value-at fn2-pool-write fn2-layout-copy fn2-layout-proof-payload-copy-call
                       fn2-layout-proof-payload-wire-byte unsigned-byte-p member-equal)
            :do-not-induct t))))
(local
 (defthm fn2-layout-proof-header-or-payload
   (let* ((tag (fn2-layout-kind-code k)) (x (fn2-layout-proof-magnitude k i f))
          (h (fn2-layout-proof-prefix-size tag x)))
     (implies (and (fn2-layout-proof-shape k i f) (natp pos) (< pos (fn2-layout-field-size k i f)))
              (and (natp h)
                   (or (equal tag 11)
                       (and (natp x) (< pos h))
                       (and (fn2-layout-proof-payload-tagp k) (<= h pos)
                            (< pos (+ h (fn2-fields-ref-len i f))))))))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable fn2-layout-proof-magnitude fn2-layout-field-size fn2-layout-varsize)))))
(local
 (defthm fn2-layout-proof-header-wire-byte
   (implies (< pos (fn2-layout-proof-prefix-size (fn2-layout-kind-code k) x))
            (equal (fn2-layout-proof-wire-byte k x pos val) (fn2-layout-proof-emit-digit (fn2-layout-kind-code k)
                pos x)))
   :hints (("Goal" :in-theory (disable fn2-layout-proof-prefix-size fn2-layout-proof-payload-tagp
       fn2-layout-proof-emit-digit)))))
(local
 (defthm fn2-layout-proof-zero-wire-byte
   (implies (equal (fn2-layout-kind-code k) 11)
            (equal (fn2-layout-proof-wire-byte k x pos val) 0))))
(local
 (defthm fn2-layout-proof-emit-byte-contract
   (let* ((x (fn2-layout-proof-magnitude k i f))
          (byte (fn2-layout-proof-wire-byte k x pos (fn2-layout-proof-value-at k i f p))))
     (implies (and (fn2-layout-proof-shape k i f) (natp pos) (< pos (fn2-layout-field-size k i f))
                   (fn2-layout-proof-reference-ok k i slot lo end okind oslot ogen f p)
                   (fn2-pool-semanticp p) (equal (fn2-layout-range-code slot gen next end t okind oslot ogen p) :ok)
                   (<= lo next) (< next end))
              (and (unsigned-byte-p 8 byte)
                   (equal (fn2-layout-emit-byte k i pos slot gen next okind oslot ogen f p)
                          (fn2-pool-write slot gen next byte okind oslot ogen p)))))
   :rule-classes nil
   :hints (("Goal" :use (fn2-layout-proof-header-or-payload
                         fn2-layout-proof-emit-payload fn2-layout-proof-emit-header
                         (:instance fn2-layout-proof-header-wire-byte (x (fn2-layout-proof-magnitude k i f))
                                    (val (fn2-layout-proof-value-at k i f p)))
                         (:instance fn2-layout-proof-digit-type (tag (fn2-layout-kind-code k))
                                    (x (fn2-layout-proof-magnitude k i f)))
                         (:instance fn2-layout-proof-zero-wire-byte (x (fn2-layout-proof-magnitude k i f))
                                    (val (fn2-layout-proof-value-at k i f p)))
                         fn2-layout-proof-zero-byte)
            :in-theory (union-theories '((:executable-counterpart unsigned-byte-p)) (theory 'minimal-theory))))))
(local (include-book "std/lists/nthcdr" :dir :system))
(local
 (defthm fn2-layout-proof-nthcdr-uncons
   (implies (and (natp j) (< j (len xs)) (true-listp xs))
            (equal (cons (nth j xs) (nthcdr (1+ j) xs)) (nthcdr j xs)))
   :hints (("Goal" :use ((:instance consp-of-nthcdr (n j) (x xs))
                          (:instance car-of-nthcdr (i j) (x xs))
                          (:instance nthcdr-of-nthcdr (a 1) (b j) (x xs)))
              :expand ((nthcdr 1 (nthcdr j xs)))
              :in-theory (union-theories '(nthcdr-when-zp natp nfix car-cdr-elim cons-car-cdr)
                                          (theory 'fn2-layout-proof-ground))))))
(local
 (defthm fn2-layout-proof-bytes-of-payload-list
   (true-listp (fn2-pool-logical-octets n a p))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn2-pool-logical-octets)))))
(local
 (defthm fn2-layout-proof-bytes-after-field
   (implies (and (natp pos) (natp size) (<= size pos))
            (equal (fn2-layout-proof-bytes-from k x size pos val) nil))
   :hints (("Goal" :expand ((fn2-layout-proof-bytes-from k x size pos val))))))
(local
 (defthm fn2-layout-proof-nthcdr-at-end
   (implies (and (natp j) (true-listp xs) (<= (len xs) j)) (equal (nthcdr j xs) nil))
   :hints (("Goal" :use ((:instance consp-of-nthcdr (n j) (x xs))
                          (:instance true-listp-of-nthcdr (n j) (x xs)))
              :in-theory (union-theories '(true-listp nfix natp) (theory 'fn2-layout-proof-ground))))))
(local
 (defthm fn2-layout-proof-bytes-in-payload
   (let ((h (fn2-layout-proof-prefix-size (fn2-layout-kind-code k) x))
         (xs (fn2-layout-proof-bytes-of-value k val)))
     (implies (and (natp pos) (natp size) (natp h) (<= h pos)
                   (fn2-layout-proof-payload-tagp k) (true-listp xs) (equal (+ h (len xs)) size))
              (equal (fn2-layout-proof-bytes-from k x size pos val)
                     (nthcdr (- pos h) xs))))
   :hints (("Goal" :expand ((fn2-layout-proof-bytes-from k x size pos val))
            :in-theory (disable fn2-layout-proof-prefix-size fn2-layout-proof-payload-tagp
                fn2-layout-proof-bytes-of-value)))))
(local
 (defthm fn2-layout-proof-next-byte
   (let ((h (fn2-layout-proof-prefix-size (fn2-layout-kind-code k) x))
         (xs (fn2-layout-proof-bytes-of-value k val)))
     (implies (and (natp pos) (natp size) (< pos size) (natp h)
                   (implies (fn2-layout-proof-payload-tagp k) (and (true-listp xs) (equal (+ h (len xs)) size))))
              (equal (fn2-layout-proof-bytes-from k x size pos val)
                     (cons (fn2-layout-proof-wire-byte k x pos val)
                           (fn2-layout-proof-bytes-from k x size (1+ pos) val)))))
   :rule-classes nil
   :hints (("Goal" :expand ((fn2-layout-proof-bytes-from k x size pos val))
            :use ((:instance fn2-layout-proof-nthcdr-uncons
                   (j (- pos (fn2-layout-proof-prefix-size (fn2-layout-kind-code k) x)))
                   (xs (fn2-layout-proof-bytes-of-value k val))))
            :in-theory (disable fn2-layout-proof-prefix-size fn2-layout-proof-payload-tagp
                fn2-layout-proof-bytes-of-value
                                fn2-layout-proof-emit-digit fn2-layout-proof-bytes-from nthcdr nth)))))

(local
 (defun-nx fn2-layout-proof-window (lo next slot p)
   (fn2-pool-logical-octets (- next lo) (+ (fn2-pool-base slot p) lo) p)))
(local
 (defthm fn2-layout-proof-window-extend-raw
   (implies (and (natp j) (natp a))
            (equal (fn2-pool-logical-octets (1+ j) a p)
                   (append (fn2-pool-logical-octets j a p) (list (fn2-pool-datai (+ a j) p)))))
   :hints (("Goal" :induct (fn2-pool-logical-octets j a p) :in-theory (enable fn2-pool-logical-octets))
           ("Subgoal *1/1" :expand ((fn2-pool-logical-octets 1 a p))))))
(local
 (defthm fn2-layout-proof-write-window
   (let ((q (mv-nth 1 (fn2-pool-write slot gen next byte okind oslot ogen p))))
     (implies (and (fn2-pool-semanticp p) (unsigned-byte-p 8 byte)
                   (equal (fn2-layout-range-code slot gen next end t okind oslot ogen p) :ok)
                   (natp lo) (<= lo next) (< next end))
              (equal (fn2-layout-proof-window lo (1+ next) slot q)
                     (append (fn2-layout-proof-window lo next slot p) (list byte)))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-layout-proof-write-step (src slot) (abs (+ (fn2-pool-base slot p) lo)) (n (-
       next lo)))
                         (:instance fn2-layout-proof-window-extend-raw (a (+ (fn2-pool-base slot p) lo))
                          (j (- next lo)) (p (mv-nth 1 (fn2-pool-write slot gen next byte okind oslot ogen p))))
                         (:instance fn2-layout-proof-readable-row (start next) (writep t))
                         (:instance fn2-pool-semanticp-row-bounds (fn2-pool p) (i slot)))
            :in-theory (disable fn2-pool-write fn2-layout-proof-window-extend-raw fn2-layout-proof-range-step)))))
(local (in-theory (disable fn2-layout-proof-window fn2-layout-proof-window-extend-raw)))
(local
 (defthm fn2-layout-proof-end-readable
   (implies (and (equal (fn2-layout-range-code slot gen end end t okind oslot ogen p) :ok)
                 (natp lo) (<= lo end))
            (equal (fn2-layout-range-code slot gen lo end nil okind oslot ogen p) :ok))
   :hints (("Goal" :in-theory (enable fn2-layout-range-code)))))
(local
 (defthm fn2-layout-proof-shape-size
   (implies (fn2-layout-proof-shape k i f)
            (and (natp (fn2-layout-field-size k i f))
                 (natp (fn2-layout-proof-prefix-size (fn2-layout-kind-code k) (fn2-layout-proof-magnitude k i f)))
                 (implies (fn2-layout-proof-payload-tagp k)
                          (let ((xs (fn2-layout-proof-bytes-of-value k (fn2-layout-proof-value-at k i f p))))
                            (and (true-listp xs)
                                 (equal (+ (fn2-layout-proof-prefix-size (fn2-layout-kind-code k)
                                                   (fn2-layout-proof-magnitude k i f)) (len xs))
                                        (fn2-layout-field-size k i f)))))))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable fn2-layout-varsize fn2-layout-field-size
                                       fn2-layout-proof-number-okp fn2-layout-proof-magnitude)))))
(local
 (defthm fn2-layout-proof-wire-step
   (let* ((k (cadar layout)) (size (fn2-layout-field-size k i f)) (empty (zp size))
          (done (<= size (1+ pos))) (vals (fn2-layout-values layout i f p))
          (byte (fn2-layout-proof-wire-byte k (fn2-layout-proof-magnitude k i f) pos (car vals)))
          (rest (if done (fn2-layout-proof-wire (cdr layout) (1+ i) 0 f (cdr vals))
                  (fn2-layout-proof-wire layout i (1+ pos) f vals))))
     (implies (and (consp layout) (natp i) (fn2-layout-proof-shape k i f) (natp pos)
                   (if empty (equal pos 0) (< pos size)))
              (equal (fn2-layout-proof-wire layout i pos f vals)
                     (if empty rest (cons byte rest)))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-layout-proof-shape-size (k (cadar layout)))
                         (:instance fn2-layout-proof-next-byte (k (cadar layout))
                          (x (fn2-layout-proof-magnitude (cadar layout) i f))
                          (size (fn2-layout-field-size (cadar layout) i f)) (val (fn2-layout-proof-value-at (cadar
                              layout) i f p))))
            :expand ((:free (j vals) (fn2-layout-proof-wire layout i j f vals)))
            :in-theory (union-theories '(fn2-layout-proof-fields-view fn2-layout-proof-bytes-after-field
                fn2-layout-proof-bytes-of-payload-list append fn2-layout-size-natp) (theory
                'fn2-layout-proof-index-rules))))))
(local
 (defun-nx fn2-layout-proof-emit-ready (layout fuel i pos next lo end slot gen okind oslot ogen f p)
   (let ((size (fn2-layout-field-size (cadar layout) i f)))
     (and (natp lo) (natp next) (natp pos) (natp fuel) (natp i) (<= lo next)
          (equal end (+ next (- (fn2-layout-size layout i f) pos)))
          (<= (- end next) fuel)
          (if (and (consp layout) (not (zp size))) (< pos size) (equal pos 0))
          (fn2-layout-proof-shapes layout i f)
          (fn2-layout-proof-refs layout i slot lo end okind oslot ogen f p)
          (fn2-pool-semanticp p) (equal (fn2-layout-range-code slot gen next end t okind oslot ogen p) :ok)))))
(local
 (defun-nx fn2-layout-proof-emit-result (layout i pos next lo end slot gen okind oslot ogen f p r)
   (let ((q (mv-nth 4 r)))
     (and (equal (mv-nth 0 r) :ok) (equal (mv-nth 3 r) end) (fn2-pool-semanticp q)
          (equal (fn2-layout-range-code slot gen lo end nil okind oslot ogen q) :ok)
          (equal (fn2-layout-proof-window lo end slot q)
                 (append (fn2-layout-proof-window lo next slot p)
                         (fn2-layout-proof-wire layout i pos f (fn2-layout-values layout i f p))))))))
(local (in-theory (disable fn2-layout-proof-shape fn2-layout-proof-reference-ok
                           fn2-layout-proof-wire fn2-layout-values fn2-layout-proof-value-at
                           fn2-layout-proof-wire-byte fn2-layout-proof-magnitude fn2-layout-field-size
                           fn2-layout-proof-bytes-from fn2-layout-proof-range-step)))
(local
 (defthm fn2-layout-proof-emit-ready-head
   (let* ((k (cadar layout)) (size (fn2-layout-field-size k i f)))
     (implies (and (consp layout)
                   (fn2-layout-proof-emit-ready layout fuel i pos next lo end slot gen okind oslot ogen f p))
              (and (natp size) (< i (fn2-fields-rows f)) (fn2-layout-proof-shape k i f)
                   (fn2-layout-proof-reference-ok k i slot lo end okind oslot ogen f p)
                   (implies (not (zp size)) (and (< pos size) (< 0 fuel) (< next end))))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-layout-proof-shape-size (k (cadar layout))))
            :expand ((fn2-layout-proof-shapes layout i f)
                     (fn2-layout-proof-refs layout i slot lo end okind oslot ogen f p)
                     (fn2-layout-size layout i f))
            :in-theory (union-theories '(fn2-layout-proof-emit-ready fn2-layout-size-natp) (theory
                'fn2-layout-proof-index-rules))))))
(local
 (defthm fn2-layout-proof-advance-ready
   (let* ((k (cadar layout)) (size (fn2-layout-field-size k i f))
          (empty (zp size)) (done (<= size (1+ pos))) (nx (if empty next (1+ next))))
     (implies (and (consp layout) (natp size) (< i (fn2-fields-rows f))
                   (fn2-layout-proof-emit-ready layout fuel i pos next lo end slot gen okind oslot ogen f p)
                   (fn2-pool-semanticp q) (equal (fn2-layout-range-code slot gen nx end t okind oslot ogen q) :ok)
                   (fn2-layout-proof-refs layout i slot lo end okind oslot ogen f q))
              (fn2-layout-proof-emit-ready (if done (cdr layout) layout) (if empty fuel (1- fuel))
                 (if done (1+ i) i) (if done 0 (1+ pos)) nx lo end slot gen okind oslot ogen f q)))
   :rule-classes nil
   :hints (("Goal" :expand ((fn2-layout-proof-shapes layout i f) (fn2-layout-size layout i f)
                            (fn2-layout-proof-refs layout i slot lo end okind oslot ogen f q))
            :in-theory (union-theories '(fn2-layout-proof-emit-ready fn2-layout-size-natp) (theory
                'fn2-layout-proof-index-rules))))))
(local
 (defthm fn2-layout-proof-window-listp
   (true-listp (fn2-layout-proof-window lo next slot p))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn2-layout-proof-window)))))
(local (include-book "std/lists/append" :dir :system))
(local
 (defthm fn2-layout-proof-advance-result
   (let* ((k (cadar layout)) (size (fn2-layout-field-size k i f))
          (empty (zp size)) (done (<= size (1+ pos))) (nx (if empty next (1+ next)))
          (vals (fn2-layout-values layout i f p))
          (byte (fn2-layout-proof-wire-byte k (fn2-layout-proof-magnitude k i f) pos (car vals))))
     (implies (and (consp layout) (natp pos) (natp i) (fn2-layout-proof-shape k i f)
                   (if empty (equal pos 0) (< pos size))
                   (equal (fn2-layout-values layout i f q) vals)
                   (equal (fn2-layout-proof-window lo nx slot q)
                          (if empty (fn2-layout-proof-window lo next slot p)
                            (append (fn2-layout-proof-window lo next slot p) (list byte))))
                   (fn2-layout-proof-emit-result (if done (cdr layout) layout) (if done (1+ i) i)
                           (if done 0 (1+ pos)) nx lo end slot gen okind oslot ogen f q r))
              (fn2-layout-proof-emit-result layout i pos next lo end slot gen okind oslot ogen f p r)))
   :rule-classes nil
   :hints (("Goal" :use (fn2-layout-proof-wire-step
                         (:instance fn2-layout-proof-fields-view (p q)) fn2-layout-proof-fields-view)
            :in-theory (union-theories '(fn2-layout-proof-emit-result fn2-layout-proof-fields-view
                associativity-of-append append) (theory 'fn2-layout-proof-index-rules))))))
(local
 (defthm fn2-layout-proof-write-permission
   (let* ((w (fn2-pool-write slot gen next byte okind oslot ogen p)) (q (mv-nth 1 w)))
     (implies (and (fn2-pool-semanticp p) (unsigned-byte-p 8 byte)
                   (equal (fn2-layout-range-code slot gen next end t okind oslot ogen p) :ok) (< next end))
              (and (equal (mv-nth 0 w) :ok) (fn2-pool-semanticp q)
                   (equal (fn2-layout-range-code slot gen (1+ next) end t okind oslot ogen q) :ok))))
   :hints (("Goal" :use ((:instance fn2-layout-proof-write-step (src slot) (g gen) (a next) (b end) (abs 0) (n 0)))
            :in-theory (theory 'minimal-theory)))))
(local
 (defthm fn2-layout-proof-write-views
   (let ((q (mv-nth 1 (fn2-pool-write slot gen next byte okind oslot ogen p))))
     (implies (and (fn2-pool-semanticp p) (unsigned-byte-p 8 byte) (natp i) (natp lo)
                   (fn2-layout-proof-refs layout i slot lo end okind oslot ogen f p)
                   (equal (fn2-layout-range-code slot gen next end t okind oslot ogen p) :ok) (<= lo next) (< next end))
              (and (fn2-layout-proof-refs layout i slot lo end okind oslot ogen f q)
                   (equal (fn2-layout-values layout i f q) (fn2-layout-values layout i f p))
                   (equal (fn2-layout-proof-window lo (1+ next) slot q)
                          (append (fn2-layout-proof-window lo next slot p) (list byte))))))
   :hints (("Goal" :use (fn2-layout-proof-layout-frame fn2-layout-proof-write-window)
            :in-theory (theory 'minimal-theory)))))
(local
 (defmacro fn2-layout-proof-emit-effects-contract-event ()
   (let* ((k '(cadar layout))
          (size `(fn2-layout-field-size ,k i f))
          (vals '(fn2-layout-values layout i f p))
          (byte `(fn2-layout-proof-wire-byte ,k (fn2-layout-proof-magnitude ,k i f) pos (car ,vals)))
          (step `(fn2-layout-emit-byte ,k i pos slot gen next okind oslot ogen f p))
          (q `(mv-nth 1 ,step)))
     `(defthm fn2-layout-proof-emit-effects
        (implies (and (consp layout) (not (zp ,size))
                      (fn2-layout-proof-emit-ready layout fuel i pos next lo end slot gen okind oslot ogen f p))
                 (and (eq (mv-nth 0 ,step) :ok)
                      (fn2-pool-semanticp ,q)
                      (equal (fn2-layout-range-code slot gen (1+ next) end t okind oslot ogen ,q) :ok)
                      (fn2-layout-proof-refs layout i slot lo end okind oslot ogen f ,q)
                      (equal (fn2-layout-values layout i f ,q) ,vals)
                      (equal (fn2-layout-proof-window lo (1+ next) slot ,q)
                             (append (fn2-layout-proof-window lo next slot p) (list ,byte)))))
        :rule-classes nil
        :hints (("Goal" :use (fn2-layout-proof-emit-ready-head
                              (:instance fn2-layout-proof-emit-byte-contract (k ,k)))
                 :in-theory (union-theories '(fn2-layout-proof-emit-ready fn2-layout-proof-fields-view
                                             fn2-layout-proof-write-permission fn2-layout-proof-write-views)
                                            (theory 'minimal-theory))))))))
(local (fn2-layout-proof-emit-effects-contract-event))
(local
 (defmacro fn2-layout-proof-emit-step-event ()
   (let* ((k '(cadar layout)) (size `(fn2-layout-field-size ,k i f))
          (empty `(zp ,size)) (done `(<= ,size (1+ pos)))
          (step `(if ,empty (list :ok p) (fn2-layout-emit-byte ,k i pos slot gen next okind oslot ogen f p)))
          (q `(mv-nth 1 ,step)) (l2 `(if ,done (cdr layout) layout))
          (i2 `(if ,done (1+ i) i)) (pos2 `(if ,done 0 (1+ pos)))
          (nx `(if ,empty next (1+ next))) (fu `(if ,empty fuel (1- fuel))))
     `(defthm fn2-layout-proof-emit-step
        (implies (and (consp layout) (fn2-layout-proof-emit-ready layout fuel i pos next lo end slot gen okind oslot
            ogen f p))
                 (and (natp ,size) (< i (fn2-fields-rows f)) (or ,empty (posp fuel))
                      (equal (mv-nth 0 ,step) :ok)
                      (fn2-layout-proof-emit-ready ,l2 ,fu ,i2 ,pos2 ,nx lo end slot gen okind oslot ogen f ,q)
                      (implies (fn2-layout-proof-emit-result ,l2 ,i2 ,pos2 ,nx lo end slot gen okind oslot ogen f ,q r)
                               (fn2-layout-proof-emit-result layout i pos next lo end slot gen okind oslot ogen f p
                                   r))))
        :rule-classes nil
        :hints (("Goal" :use (fn2-layout-proof-emit-ready-head fn2-layout-proof-emit-effects
                              (:instance fn2-layout-proof-advance-ready (q ,q))
                              (:instance fn2-layout-proof-advance-result (q ,q)))
                 :cases (,empty)
                 :in-theory (union-theories '(fn2-layout-proof-emit-ready mv-nth car-cons cdr-cons natp posp zp)
                                            (theory 'minimal-theory))))))))
(local (fn2-layout-proof-emit-step-event))
(local
 (defthm fn2-layout-proof-emit-base
   (implies (and (atom layout) (fn2-layout-proof-emit-ready layout fuel i pos next lo end slot gen okind oslot ogen
       f p))
            (fn2-layout-proof-emit-result layout i pos next lo end slot gen okind oslot ogen f p (list :ok i pos
                next p)))
   :hints (("Goal" :expand ((fn2-layout-size layout i f) (:free (pos vs) (fn2-layout-proof-wire layout i pos f vs)))
            :in-theory (disable fn2-layout-proof-shapes fn2-layout-proof-refs)))))
(local
 (defthm fn2-layout-proof-ready-types
   (implies (fn2-layout-proof-emit-ready layout fuel i pos next lo end slot gen okind oslot ogen f p)
            (and (natp pos) (natp fuel) (natp next) (natp i)))
   :rule-classes :forward-chaining))
(local
 (defthm fn2-layout-proof-ready-resources
   (implies (and (fn2-layout-proof-emit-ready layout fuel i pos next lo end slot gen okind oslot ogen f p)
                 (consp layout))
            (and (< i (fn2-fields-rows f))
                 (natp (fn2-layout-field-size (cadar layout) i f))
                 (implies (not (equal (fn2-layout-field-size (cadar layout) i f) 0))
                          (not (zp fuel)))))
   :rule-classes ((:forward-chaining :trigger-terms
                  ((fn2-layout-proof-emit-ready layout fuel i pos next lo end slot gen okind oslot ogen f p))))
   :hints (("Goal" :use fn2-layout-proof-emit-ready-head
            :in-theory (disable fn2-layout-proof-emit-ready fn2-layout-proof-reference-ok)))))
(local
 (defthm fn2-layout-proof-emit-correct
   (implies (fn2-layout-proof-emit-ready layout fuel i pos next lo end slot gen okind oslot ogen f p)
            (fn2-layout-proof-emit-result layout i pos next lo end slot gen okind oslot ogen f p
             (fn2-layout-emit layout fuel i pos next slot gen okind oslot ogen f p)))
   :rule-classes nil
   :hints (("Goal" :induct (fn2-layout-emit layout fuel i pos next slot gen okind oslot ogen f p)
            :expand ((fn2-layout-emit layout fuel i pos next slot gen okind oslot ogen f p))
            :in-theory (e/d ((:induction fn2-layout-emit))
                  (fn2-layout-proof-emit-result fn2-layout-proof-emit-ready fn2-layout-emit-byte
                   fn2-layout-proof-zero-byte fn2-layout-proof-payload-copy-call)))
           ("Subgoal *1/2" :use fn2-layout-proof-ready-resources)
           ("Subgoal *1/3" :use fn2-layout-proof-ready-resources :in-theory (e/d (zp) (fn2-layout-proof-emit-ready
               fn2-layout-proof-emit-result)))
           (and (equal (length (cadr id)) 2)
                '(:use ((:instance fn2-layout-proof-emit-step
                         (r (fn2-layout-emit layout fuel i pos next slot gen okind oslot ogen f p)))))))))

(local
 (defthm fn2-layout-proof-varsize-monotone
   (implies (and (natp x) (natp limit) (<= x limit))
            (<= (fn2-layout-varsize x) (fn2-layout-varsize limit)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-layout-proof-varsize-limit (pos (fn2-layout-varsize limit)))
                         (:instance fn2-layout-proof-varsize-limit (x limit) (pos (fn2-layout-varsize limit))))
            :in-theory (disable fn2-layout-varsize fn2-layout-proof-varsize-limit)))))
;; The public maximum uses field names for the three length encodings.
;; Expose just this dispatch to the proof of the per-field size bound.
(local
 (defthm fn2-layout-proof-length-tags
   (let ((tag (fn2-layout-kind-code k)))
     (and (implies (equal tag 10) (and (consp k) (equal (car k) :octets)))
          (implies (equal tag 15) (and (consp k) (equal (car k) :octets16)))
          (implies (equal tag 16) (and (consp k) (equal (car k) :octets32)))
          (implies (member tag '(5 8)) (not (member (car k) '(:octets :octets16 :octets32))))))
   :hints (("Goal" :in-theory (enable fn2-layout-kind-code)))))
(local
 (defthm fn2-layout-proof-field-ceiling
   (let* ((k (cadr field)) (tag (fn2-layout-kind-code k)))
     (implies (fn2-layout-kindp k)
              (equal (fn2-layout-max-size (list field))
                     (case tag ((5 8) 9) (10 (+ (fn2-layout-varsize (cadr k)) (cadr k)))
                           (15 (+ 2 (cadr k))) (16 (+ 4 (cadr k))) (otherwise (fn2-layout-width k))))))
   :hints (("Goal" :use ((:instance fn2-layout-proof-kind-facts (k (cadr field)))
                         (:instance fn2-layout-proof-length-tags (k (cadr field))))
            :expand ((fn2-layout-max-size (list field)))
            :in-theory (disable fn2-layout-kindp fn2-layout-kind-code fn2-layout-proof-length-tags
                fn2-layout-varsize)))))
(local
 (defthm fn2-layout-proof-shape-max
   (let ((k (cadr field)))
     (implies (and (fn2-layout-kindp k) (fn2-layout-proof-shape k i f))
              (<= (fn2-layout-field-size k i f) (fn2-layout-max-size (list field)))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-layout-proof-kind-facts (k (cadr field)))
                         (:instance fn2-layout-proof-varsize-monotone (x (fn2-fields-ref-len i f)) (limit (cadr
                             (cadr field))))
                         (:instance fn2-layout-proof-varsize-u60 (x (fn2-fields-value i f))))
            :in-theory (e/d (fn2-layout-field-size fn2-layout-proof-shape fn2-layout-proof-magnitude
                fn2-layout-proof-field-ceiling)
                           (fn2-layout-kindp fn2-layout-varsize fn2-layout-proof-varsize-u60))))))
(local (in-theory (disable fn2-layout-proof-field-ceiling fn2-layout-proof-length-tags)))
(local
 (defthm fn2-layout-proof-size-max
   (implies (and (fn2-layoutp layout) (fn2-layout-proof-shapes layout i f))
            (<= (fn2-layout-size layout i f) (fn2-layout-max-size layout)))
   :rule-classes nil
   :hints (("Goal" :induct (fn2-layout-proof-layout-ind layout i)
            :expand ((fn2-layout-size layout i f) (fn2-layout-max-size layout) (fn2-layout-proof-shapes layout i f))
            :in-theory (disable fn2-layoutp fn2-layout-proof-shape fn2-layout-kindp fn2-layout-varsize
                fn2-layout-width fn2-layout-max-size))
           ("Subgoal *1/2" :use (fn2-layoutp-head (:instance fn2-layout-proof-shape-max (field (car layout)))
                                 (:instance fn2-layout-proof-shape-size (k (cadar layout))))
            :expand ((fn2-layout-size layout i f) (fn2-layout-max-size layout) (fn2-layout-max-size (list (car layout)))
                     (fn2-layout-proof-shapes layout i f))))))
(local
 (defthm fn2-layout-proof-roundtrip-ready
   (implies (fn2-layout-roundtrip-hyps layout slot gen off okind oslot ogen f p)
            (let ((end (+ off (fn2-layout-size layout 0 f))))
              (and (fn2-layout-proof-emit-ready layout 4096 0 0 off off end slot gen okind oslot ogen f p)
                   (fn2-layout-proof-shapes layout 0 f) (<= (fn2-layout-size layout 0 f) 4096))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-layout-proof-refs-from-preflight (lo off) (i 0) (end (+ off (fn2-layout-size
       layout 0 f))))
                         (:instance fn2-layout-proof-shapes-from-preflight (lo off) (i 0) (end (+ off
                             (fn2-layout-size layout 0 f))))
                         (:instance fn2-layout-proof-size-max (i 0)))
            :in-theory (disable fn2-layoutp fn2-layout-proof-shapes fn2-layout-proof-refs fn2-layout-max-size
                                fn2-layout-proof-shapes-from-preflight fn2-layout-proof-refs-from-preflight)))))
(local
 (defthm fn2-layout-proof-roundtrip-encode
   (let* ((enc (fn2-layout-encode layout slot gen off okind oslot ogen f p))
          (end (+ off (fn2-layout-size layout 0 f))) (q (mv-nth 2 enc)))
     (implies (fn2-layout-roundtrip-hyps layout slot gen off okind oslot ogen f p)
              (and (equal (mv-nth 0 enc) :ok) (equal (mv-nth 1 enc) end)
                   (fn2-pool-semanticp q) (equal (fn2-layout-range-code slot gen off end nil okind oslot ogen q) :ok)
                   (equal (fn2-layout-proof-window off end slot q)
                          (fn2-layout-proof-wire layout 0 0 f (fn2-layout-values layout 0 f p)))
                   (fn2-layout-proof-shapes layout 0 f) (<= (fn2-layout-size layout 0 f) 4096))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-layout-proof-emit-correct (next off) (lo off)
                             (end (+ off (fn2-layout-size layout 0 f))) (i 0) (pos 0) (fuel 4096))
                         fn2-layout-proof-roundtrip-ready)
            :in-theory (e/d (fn2-layout-encode fn2-layout-proof-window)
                      (fn2-layoutp fn2-layout-proof-emit-ready fn2-layout-max-size fn2-layout-size
                          fn2-layout-proof-shapes fn2-layout-proof-refs
                       fn2-layout-proof-shapes-from-preflight fn2-layout-proof-refs-from-preflight))))))

(local
 (defun fn2-layout-proof-expected-cursor (k x size pos next)
   (let* ((tag (fn2-layout-kind-code k)) (h (fn2-layout-proof-prefix-size tag x))
          (payload (and (fn2-layout-proof-payload-tagp k) (<= h pos))))
     (if payload
         (list (- pos h) (if (equal tag 7) 1 0) 0 (- size h) (- next (- pos h)) 1 next)
       (list pos (if (equal tag 11) 0 (fn2-layout-proof-accumulator tag pos x)) 0 0 0 0 next)))))
(local
 (defun fn2-layout-proof-last-row (k x size start)
   (let* ((tag (fn2-layout-kind-code k)) (h (fn2-layout-proof-prefix-size tag x)))
     ;; Scalar, reference offset, and reference length, in store order.
     (cond ((fn2-layout-proof-payload-tagp k)
            (list (if (equal tag 7) 1 0) (+ start h) (- size h)))
           ((equal tag 11) '(0 0 0))
           (t (list x 0 0))))))
(local
 (defun fn2-layout-proof-valid-field (k x size)
   (let ((tag (fn2-layout-kind-code k)) (h (fn2-layout-proof-prefix-size (fn2-layout-kind-code k) x)))
     (and (natp size)
          (if (equal tag 11) (equal k (list :zero size))
            (and (fn2-layout-proof-number-okp tag x (if (= tag 9) (len (caddr k)) (nfix (cadr k))))
                 (equal size (+ h (cond ((= tag 7) 32) ((member tag '(10 15 16)) x) (t 0))))))))))
(local
 (defthm fn2-layout-proof-shape-valid-field
   (implies (fn2-layout-proof-shape k i f)
            (fn2-layout-proof-valid-field k (fn2-layout-proof-magnitude k i f) (fn2-layout-field-size k i f)))
   :hints (("Goal" :in-theory (e/d (fn2-layout-proof-shape fn2-layout-proof-magnitude)
                            (fn2-layout-field-size fn2-layout-proof-number-okp fn2-layout-proof-prefix-size))))))
(local
 (defun-nx fn2-layout-proof-inverse-step (k x size pos next byte)
   (let* ((empty (zp size)) (done (<= size (1+ pos))) (nx (if empty next (1+ next)))
          (tick (fn2-layout-proof-tick k (fn2-layout-proof-expected-cursor k x size pos next) byte))
          (out (cdr tick)))
     (if done
         (and (equal (car tick) :done) (equal (nth 6 out) nx)
              (equal (list (nth 1 out) (nth 4 out) (nth 3 out))
                     (fn2-layout-proof-last-row k x size (- next pos))))
       (and (member (car tick) '(:part :payload))
            (equal out (fn2-layout-proof-expected-cursor k x size (1+ pos) nx)))))))
(local
 (defthm fn2-layout-proof-inverse-padding
   (implies (and (equal (fn2-layout-kind-code k) 11)
                 (fn2-layout-proof-valid-field k x size)
                 (natp pos) (if (zp size) (equal pos 0) (< pos size))
                 (natp next) (equal byte 0))
            (fn2-layout-proof-inverse-step k x size pos next byte))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn2-layout-byte fn2-layout-proof-tick)
                     (fn2-layout-kind-code fn2-layout-proof-accumulator fn2-layout-proof-number-okp))))))
(local
 (defthm fn2-layout-proof-inverse-payload
   (let* ((tag (fn2-layout-kind-code k)) (h (fn2-layout-proof-prefix-size tag x)))
     (implies (and (fn2-layout-proof-payload-tagp k) (fn2-layout-proof-valid-field k x size)
                   (natp pos) (natp next) (<= pos next) (natp h) (<= h pos) (< pos size))
              (fn2-layout-proof-inverse-step k x size pos next byte)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn2-layout-byte fn2-layout-proof-tick)
                     (fn2-layout-kind-code fn2-layout-proof-prefix-size fn2-layout-proof-accumulator
                      fn2-layout-proof-number-okp))))))
(local
 (defthm fn2-layout-proof-header-acc-type
   (implies (and (natp x) (natp pos)) (natp (fn2-layout-proof-accumulator tag pos x)))
   :hints (("Goal" :in-theory (disable fn2-layout-proof-prefix-size)))))
(local
 (defthm fn2-layout-proof-header-prefix-positive
   (implies (fn2-layout-proof-number-okp tag x limit)
            (posp (fn2-layout-proof-prefix-size tag x)))
   :hints (("Goal" :in-theory (disable fn2-layout-varsize)))))
(local
 (defthm fn2-layout-proof-header-call
   (let ((tag (fn2-layout-kind-code k)))
     (implies (and (natp pos) (< pos (fn2-layout-proof-prefix-size tag x))
                   (fn2-layout-proof-number-okp tag x (if (= tag 9) (len (caddr k)) (nfix (cadr k)))))
              (equal (fn2-layout-byte k pos (fn2-layout-proof-accumulator tag pos x) 0 0 0
                                      (fn2-layout-proof-emit-digit tag pos x))
                     (fn2-layout-proof-expected-header k pos x))))
   :hints (("Goal" :use fn2-layout-proof-header-digit-inverse
            :in-theory (union-theories '(fn2-layout-proof-header-inverse return-last) (theory 'minimal-theory))))))
(local
 (defthm fn2-layout-proof-ok-natural
   (implies (fn2-layout-proof-number-okp tag x limit) (natp x))
   :rule-classes :forward-chaining))
(local
 (defthm fn2-layout-proof-under-header
   (let ((tag (fn2-layout-kind-code k)))
     (implies (and (natp pos) (< pos (fn2-layout-proof-prefix-size tag x)) (not (equal tag 11)))
              (equal (fn2-layout-proof-expected-cursor k x size pos next)
                     (list pos (fn2-layout-proof-accumulator tag pos x) 0 0 0 0 next))))
   :hints (("Goal" :in-theory (disable fn2-layout-proof-prefix-size fn2-layout-proof-payload-tagp
                                       fn2-layout-proof-accumulator)))))
(local
 (defthm fn2-layout-proof-first-cursor
   (implies (fn2-layout-proof-valid-field k x size)
            (equal (fn2-layout-proof-expected-cursor k x size 0 next) (list 0 0 0 0 0 0 next)))
   :hints (("Goal" :in-theory (disable fn2-layout-varsize fn2-layout-proof-number-okp)))))
(local
 (defthm fn2-layout-proof-empty-shape
   (implies (and (fn2-layout-proof-shape k i f) (zp (fn2-layout-field-size k i f)))
            (equal k '(:zero 0)))
   :rule-classes nil
   :hints (("Goal" :use fn2-layout-proof-shape-valid-field
            :in-theory (e/d (fn2-layout-proof-shape) (fn2-layout-field-size fn2-layout-varsize
                fn2-layout-proof-magnitude))))))
(local
 (defthm fn2-layout-proof-header-transition
   (let* ((tag (fn2-layout-kind-code k)) (h (fn2-layout-proof-prefix-size tag x)))
     (implies (and (not (equal tag 11)) (fn2-layout-proof-valid-field k x size)
                   (natp pos) (natp next) (<= pos next) (natp h) (< pos h)
                   (equal byte (fn2-layout-proof-emit-digit tag pos x)))
              (fn2-layout-proof-inverse-step k x size pos next byte)))
   :rule-classes nil
   :hints (("Goal" :cases ((equal (1+ pos) (fn2-layout-proof-prefix-size (fn2-layout-kind-code k) x))
                            (equal (fn2-layout-kind-code k) 7) (member (fn2-layout-kind-code k) '(10 15 16)))
            :use ((:instance fn2-layout-proof-header-acc-type (tag (fn2-layout-kind-code k)) (pos (1+ pos)))
                  fn2-layout-proof-header-call)
            :in-theory (e/d (fn2-layout-proof-tick)
                            (fn2-layout-kind-code fn2-layout-byte fn2-layout-proof-prefix-size
                             fn2-layout-proof-header-call fn2-layout-proof-number-okp
                             fn2-layout-proof-emit-digit fn2-layout-proof-accumulator))
            :do-not-induct t))))
(local
 (defthm fn2-layout-proof-full-inverse
   (let* ((k (cadar layout)) (x (fn2-layout-proof-magnitude k i f)) (size (fn2-layout-field-size k i f))
          (val (fn2-layout-proof-value-at k i f p)) (byte (fn2-layout-proof-wire-byte k x pos val)))
     (implies (and (fn2-layout-kindp k) (fn2-layout-proof-shape k i f) (natp pos) (natp next) (<= pos next)
                   (if (zp size) (equal pos 0) (< pos size)))
              (fn2-layout-proof-inverse-step k x size pos next byte)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-layout-proof-empty-shape (k (cadar layout)))
                         (:instance fn2-layout-proof-shape-valid-field (k (cadar layout)))
                         (:instance fn2-layout-proof-header-or-payload (k (cadar layout)))
                         (:instance fn2-layout-proof-inverse-padding
                          (k (cadar layout)) (x (fn2-layout-proof-magnitude (cadar layout) i f))
                          (size (fn2-layout-field-size (cadar layout) i f))
                          (byte (fn2-layout-proof-wire-byte (cadar layout) (fn2-layout-proof-magnitude (cadar
                              layout) i f)
                                                            pos (fn2-layout-proof-value-at (cadar layout) i f p))))
                         (:instance fn2-layout-proof-inverse-payload
                          (k (cadar layout)) (x (fn2-layout-proof-magnitude (cadar layout) i f))
                          (size (fn2-layout-field-size (cadar layout) i f))
                          (byte (fn2-layout-proof-wire-byte (cadar layout) (fn2-layout-proof-magnitude (cadar
                              layout) i f)
                                                            pos (fn2-layout-proof-value-at (cadar layout) i f p))))
                         (:instance fn2-layout-proof-header-transition
                          (k (cadar layout)) (x (fn2-layout-proof-magnitude (cadar layout) i f))
                          (size (fn2-layout-field-size (cadar layout) i f))
                          (byte (fn2-layout-proof-wire-byte (cadar layout) (fn2-layout-proof-magnitude (cadar
                              layout) i f)
                                                            pos (fn2-layout-proof-value-at (cadar layout) i f p))))
)
            :in-theory (union-theories '(fn2-layout-proof-zero-wire-byte fn2-layout-proof-header-wire-byte)
                                       (theory 'fn2-layout-proof-ground))))))
(local
 (defthm fn2-layout-proof-read-window
   (implies (and (natp (fn2-pool-base slot p)) (equal (fn2-layout-range-code slot gen lo end nil okind oslot ogen p)
       :ok)
                 (natp next) (<= lo next) (< next end))
            (let ((rd (fn2-pool-read slot gen next okind oslot ogen p)))
              (and (equal (mv-nth 0 rd) :ok)
                   (equal (fn2-layout-proof-window next end slot p)
                          (cons (mv-nth 1 rd) (fn2-layout-proof-window (1+ next) end slot p))))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-layout-proof-slice-step (base (fn2-pool-base slot p)) (finish end))
                         (:instance fn2-layout-proof-range-step (start lo) (writep nil))
                         (:instance fn2-layout-proof-readable-row (start lo) (writep nil)))
            :expand ((fn2-pool-logical-octets (- end next) (+ (fn2-pool-base slot p) next) p))
            :in-theory (e/d (fn2-layout-proof-window) (fn2-pool-read fn2-layout-proof-range-step))))))
(local
 (defthm fn2-layout-proof-take-region
   (implies (and (natp n) (natp total) (<= n total) (natp a))
            (equal (take n (fn2-pool-logical-octets total a p)) (fn2-pool-logical-octets n a p)))
   :hints (("Goal" :induct (fn2-layout-proof-offset-ind n total a)
            :expand ((fn2-pool-logical-octets total a p) (fn2-pool-logical-octets n a p))
            :in-theory (enable take)))))
(local (include-book "std/lists/take" :dir :system))
(local
 (defthm fn2-layout-proof-prefix-of-list
   (implies (and (true-listp xs) (equal ys (append xs suffix)))
            (and (<= (len xs) (len ys)) (equal (take (len xs) ys) xs)))
   :rule-classes nil))
(local
 (defthm fn2-layout-proof-view-prefix
   (implies (and (true-listp xs) (natp next) (natp end) (<= next end) (natp (fn2-pool-base slot p))
                 (equal (fn2-layout-proof-window next end slot p) (append xs suffix)))
            (equal (fn2-pool-logical-octets (len xs) (+ (fn2-pool-base slot p) next) p) xs))
   :rule-classes nil
   :hints (("Goal" :backchain-limit-rw 0 :use ((:instance fn2-layout-proof-prefix-of-list (ys
       (fn2-layout-proof-window next end slot p)))
                         (:instance fn2-layout-proof-take-region (a (+ (fn2-pool-base slot p) next)) (n (len xs))
                             (total (- end next)))
                         (:instance fn2-layout-proof-payload-length (n (- end next)) (a (+ (fn2-pool-base slot p)
                             next))))
            :in-theory (e/d (fn2-layout-proof-window) (fn2-layout-proof-payload-length fn2-layout-proof-take-region
                len-of-append take-of-append))
            :do-not-induct t))))
(local
 (defun-nx fn2-layout-proof-bound-bytes (k x size pos next val slot p)
   (let ((h (fn2-layout-proof-prefix-size (fn2-layout-kind-code k) x)))
     (equal (fn2-pool-logical-octets (- size h) (+ (fn2-pool-base slot p) (- next pos) h) p)
            (fn2-layout-proof-bytes-of-value k val)))))
(local
 (defthm fn2-layout-proof-bound-at-payload
   (let* ((k (cadar layout)) (x (fn2-layout-proof-magnitude k i src))
          (size (fn2-layout-field-size k i src)) (val (fn2-layout-proof-value-at k i src orig))
          (h (fn2-layout-proof-prefix-size (fn2-layout-kind-code k) x)))
     (implies (and (consp layout) (natp i) (fn2-layout-proof-shape k i src)
                   (natp next) (natp end) (<= next end) (natp (fn2-pool-base slot p))
                   (fn2-layout-proof-payload-tagp k)
                   (equal (fn2-layout-proof-window next end slot p)
                          (fn2-layout-proof-wire layout i h src (fn2-layout-values layout i src orig))))
              (fn2-layout-proof-bound-bytes k x size h next val slot p)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-layout-proof-shape-size (k (cadar layout)) (i i) (f src) (p orig))
                         (:instance fn2-layout-proof-view-prefix (xs (fn2-layout-proof-bytes-of-value (cadar layout)
                             (fn2-layout-proof-value-at (cadar layout) i src orig)))
                          (suffix (fn2-layout-proof-wire (cdr layout) (1+ i) 0 src (cdr (fn2-layout-values layout i
                              src orig))))))
            :expand ((:free (j vs) (fn2-layout-proof-wire layout i j src vs)))
            :in-theory (disable fn2-layout-proof-prefix-size fn2-layout-proof-bytes-of-value
                fn2-layout-proof-payload-tagp
                                fn2-layout-proof-bytes-from fn2-layout-proof-wire fn2-layout-proof-value-at
                                fn2-layout-field-size fn2-layout-proof-magnitude fn2-layout-values nthcdr)))))
(local
 (defun-nx fn2-layout-proof-reader-ready (layout fuel i pos next lo end slot gen okind oslot ogen src orig f p)
   (let* ((k (cadar layout)) (x (fn2-layout-proof-magnitude k i src)) (size (fn2-layout-field-size k i src))
          (h (fn2-layout-proof-prefix-size (fn2-layout-kind-code k) x)))
     (and (natp i) (natp fuel) (natp pos) (natp lo) (natp next) (<= pos next)
          (<= lo next) (<= next end) (unsigned-byte-p 32 end) (natp (fn2-pool-base slot p))
          (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
          (equal end (+ next (- (fn2-layout-size layout i src) pos))) (<= (- end next) fuel)
          (if (and (consp layout) (not (zp size))) (< pos size) (equal pos 0))
          (fn2-layoutp layout) (fn2-layout-proof-shapes layout i src)
          (<= (+ i (len layout)) (fn2-fields-rows f))
          (equal (fn2-layout-range-code slot gen lo end nil okind oslot ogen p) :ok)
          (equal (fn2-layout-proof-window next end slot p)
                 (fn2-layout-proof-wire layout i pos src (fn2-layout-values layout i src orig)))
          (implies (and (consp layout) (fn2-layout-proof-payload-tagp k) (< h pos))
                   (fn2-layout-proof-bound-bytes k x size pos next (fn2-layout-proof-value-at k i src orig) slot p))))))

(local
 (defthm fn2-layout-proof-empty-field-size
   (equal (fn2-layout-field-size '(:zero 0) i f) 0)
   :hints (("Goal" :in-theory (enable fn2-layout-field-size)))))
(local
 (defthm fn2-layout-proof-reader-range
   (implies (fn2-layout-proof-reader-ready layout fuel i pos next lo end slot gen okind oslot ogen src orig f p)
            (and (natp (fn2-pool-base slot p)) (natp next) (natp end) (<= lo next) (<= next end)
                 (equal (fn2-layout-range-code slot gen lo end nil okind oslot ogen p) :ok)
                 (equal (fn2-layout-proof-window next end slot p)
                        (fn2-layout-proof-wire layout i pos src (fn2-layout-values layout i src orig)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (union-theories '(fn2-layout-proof-reader-ready unsigned-byte-p integer-range-p natp)
                                              (theory 'minimal-theory))))))
(local
 (defthm fn2-layout-proof-read-cons
   (let ((rd (fn2-pool-read slot gen next okind oslot ogen p)))
     (implies (and (equal (fn2-layout-proof-window next end slot p) (cons byte rest))
                   (natp (fn2-pool-base slot p)) (fn2-pool-semanticp p)
                   (equal (fn2-layout-range-code slot gen lo end nil okind oslot ogen p) :ok)
                   (natp next) (<= lo next) (< next end))
              (and (equal (fn2-layout-proof-window (1+ next) end slot p) rest)
                   (equal (mv-nth 0 rd) :ok) (equal (mod (nfix (mv-nth 1 rd)) 256) byte))))
   :rule-classes nil
   :hints (("Goal" :use (fn2-layout-proof-read-window fn2-layout-proof-semantic-types
                         (:instance fn2-pool-read-byte-type (idx next) (fn2-pool p))
                         (:instance fn2-layout-proof-unsigned-octet-fix
                          (x (mv-nth 1 (fn2-pool-read slot gen next okind oslot ogen p)))))
            :in-theory (union-theories '(cons-equal) (theory 'minimal-theory))))))
(local
 (defmacro fn2-layout-proof-reader-events (index)
   (let* ((k '(cadar layout)) (x `(fn2-layout-proof-magnitude ,k i src))
          (size `(fn2-layout-field-size ,k i src)) (h `(fn2-layout-proof-prefix-size (fn2-layout-kind-code ,k) ,x))
          (val `(fn2-layout-proof-value-at ,k i src orig)) (byte `(fn2-layout-proof-wire-byte ,k ,x pos ,val))
          (empty `(zp ,size)) (done `(<= ,size (1+ pos))) (nx `(if ,empty next (1+ next)))
          (fu `(if ,empty fuel (1- fuel))) (l2 `(if ,done (cdr layout) layout))
          (i2 `(if ,done (1+ i) i)) (pos2 `(if ,done 0 (1+ pos)))
          (rest `(fn2-layout-proof-wire ,l2 ,i2 ,pos2 src (fn2-layout-values ,l2 ,i2 src orig)))
          (win '(fn2-layout-proof-window next end slot p))
          (read '(fn2-pool-read slot gen next okind oslot ogen p))
          (cur `(fn2-layout-proof-expected-cursor ,k ,x ,size pos next))
          (tick `(fn2-layout-proof-tick ,k ,cur ,byte))
          (lastrow `(fn2-layout-proof-last-row ,k ,x ,size (- next pos)))
          (ready '(fn2-layout-proof-reader-ready layout fuel i pos next lo end slot gen okind oslot ogen src orig f p))
          (bound `(fn2-layout-proof-bound-bytes ,k ,x ,size pos next ,val slot p)))
     (nth index `(
        (defthm fn2-layout-proof-reader-head
          (implies (and (consp layout) ,ready)
                   (and (natp i) (natp pos) (natp next) (<= pos next)
                        (fn2-layout-kindp ,k) (fn2-layout-proof-shape ,k i src) (natp ,size)
                        (< i (fn2-fields-rows f))
                        (if ,empty (and (equal pos 0) (equal ,k '(:zero 0)))
                          (and (< pos ,size) (< next end) (posp fuel) (not (equal ,k '(:zero 0)))))))
          :rule-classes nil
          :hints (("Goal" :use (fn2-layoutp-head
                               (:instance fn2-layout-proof-shape-size (k ,k) (f src) (p orig))
                               (:instance fn2-layout-proof-empty-shape (k ,k) (f src))
                               (:instance fn2-layout-proof-shape-valid-field (k ,k) (f src)))
                   :expand ((fn2-layout-size layout i src) (fn2-layout-proof-shapes layout i src) (len layout))
                   :in-theory (union-theories '(fn2-layout-proof-reader-ready fn2-layout-proof-empty-field-size
                       fn2-layout-size-natp fn2-layoutp-head (:type-prescription len) (:type-prescription
                       fn2-layout-field-size) natp posp nfix zp-open normalize-addends |(+ y x)| |(+ 0 x)|
                       |(+ y (+ x z))| |(+ x (- x))| |(- (- x))| car-cons cdr-cons default-car default-cdr
                       nth-0-cons nth-add1 ) (theory 'fn2-layout-proof-ground)))))
        (defthm fn2-layout-proof-reader-wire
          (implies (and (consp layout) ,ready)
                   (equal ,win (if ,empty ,rest (cons ,byte ,rest))))
          :rule-classes nil
          :hints (("Goal" :use (fn2-layout-proof-reader-head (:instance fn2-layout-proof-wire-step (f src) (p orig)))
                   :cases (,empty ,done)
                   :in-theory (union-theories '(fn2-layout-proof-reader-ready fn2-layout-proof-fields-view)
                                              (theory 'minimal-theory)))))
        (defthm fn2-layout-proof-reader-input
          (implies (and (consp layout) ,ready (fn2-pool-semanticp p))
                   (and (equal (fn2-layout-proof-window ,nx end slot p) ,rest)
                        (implies (not ,empty)
                                 (and (equal (mv-nth 0 ,read) :ok)
                                      (equal (mod (nfix (mv-nth 1 ,read)) 256) ,byte)))))
          :rule-classes nil
          :hints (("Goal" :use (fn2-layout-proof-reader-head fn2-layout-proof-reader-wire fn2-layout-proof-reader-range
                         (:instance fn2-layout-proof-read-cons (byte ,byte) (rest ,rest)))
                   :cases (,empty)
                   :in-theory (theory 'minimal-theory))))
        (defthm fn2-layout-proof-payload-bound-now
          (implies (and (consp layout) ,ready (fn2-layout-proof-payload-tagp ,k) (<= ,h pos)) ,bound)
          :rule-classes nil
          :hints (("Goal" :use (fn2-layout-proof-reader-head fn2-layout-proof-reader-range
              fn2-layout-proof-bound-at-payload)
                   :cases ((equal ,h pos))
                   :in-theory (union-theories '(fn2-layout-proof-reader-ready natp (:type-prescription
                       fn2-layout-proof-prefix-size) fn2-layout-proof-varsize-positive) (theory 'minimal-theory)))))
        (defthm fn2-layout-proof-reader-advance-state
          (implies (and (consp layout) ,ready (natp ,size) (< i (fn2-fields-rows src))
                        (implies (and (fn2-layout-proof-payload-tagp ,k) (<= ,h pos)) ,bound)
                        (equal (fn2-layout-proof-window ,nx end slot p) ,rest)
                        (equal (fn2-fields-rows f2) (fn2-fields-rows f)))
                   (fn2-layout-proof-reader-ready ,l2 ,fu ,i2 ,pos2 ,nx lo end slot gen okind oslot ogen src orig f2 p))
          :rule-classes nil
          :hints (("Goal" :cases (,empty ,done)
                   :expand ((fn2-layout-proof-shapes layout i src) (fn2-layout-size layout i src) (len layout))
                   :in-theory (disable fn2-layoutp fn2-layout-kindp fn2-pool-read unsigned-byte-p member-equal
                       fn2-layout-proof-payload-tagp fn2-layout-proof-prefix-size
                              fn2-layout-proof-bytes-of-value fn2-layout-proof-value-at fn2-layout-proof-emit-digit
                                  fn2-layout-proof-last-row fn2-layout-proof-header-wire-byte
                                  fn2-layout-proof-zero-wire-byte fn2-layout-proof-shapes))))
        (defthm fn2-layout-proof-reader-next-ready
          (implies (and (consp layout) ,ready (fn2-pool-semanticp p)
                        (equal (fn2-fields-rows f2) (fn2-fields-rows f)))
                   (fn2-layout-proof-reader-ready ,l2 ,fu ,i2 ,pos2 ,nx lo end slot gen okind oslot ogen src orig f2 p))
          :rule-classes nil
          :hints (("Goal" :use (fn2-layout-proof-reader-advance-state fn2-layout-proof-reader-head
                                 fn2-layout-proof-reader-input fn2-layout-proof-payload-bound-now)
                   :expand ((fn2-layout-proof-shapes layout i src))
                   :in-theory (union-theories '(fn2-layout-proof-reader-ready) (theory 'minimal-theory)))))
        (defthm fn2-layout-proof-reader-tick
          (implies (and (consp layout) ,ready)
                   (if ,done
                       (and (equal (car ,tick) :done) (equal (nth 6 (cdr ,tick)) ,nx)
                            (equal (nth 1 (cdr ,tick)) (nth 0 ,lastrow))
                            (equal (nth 4 (cdr ,tick)) (nth 1 ,lastrow))
                            (equal (nth 3 (cdr ,tick)) (nth 2 ,lastrow)))
                     (and (member (car ,tick) '(:part :payload))
                          (equal (cdr ,tick) (fn2-layout-proof-expected-cursor ,k ,x ,size (1+ pos) ,nx)))))
          :rule-classes nil
          :hints (("Goal" :use (fn2-layout-proof-reader-head (:instance fn2-layout-proof-full-inverse (f src) (p orig)))
                   :in-theory (union-theories '(natp posp nfix zp-open default-car default-cdr car-cons cdr-cons
                       fn2-layoutp-head fn2-layout-proof-inverse-step nth) (theory 'minimal-theory)))))
)))))
(local (fn2-layout-proof-reader-events 0))
(local (fn2-layout-proof-reader-events 1))
(local (fn2-layout-proof-reader-events 2))
(local (fn2-layout-proof-reader-events 3))
(local (fn2-layout-proof-reader-events 4))
(local (fn2-layout-proof-reader-events 5))
(local (fn2-layout-proof-reader-events 6))

(local
 (defthm fn2-layout-proof-done-descriptor
   (let* ((k (cadar layout)) (x (fn2-layout-proof-magnitude k i src))
          (val (fn2-layout-proof-value-at k i src orig))
          (size (fn2-layout-field-size k i src))
          (h (fn2-layout-proof-prefix-size (fn2-layout-kind-code k) x))
          (start (- next pos)) (row (fn2-layout-proof-last-row k x size start)))
     (implies (and (fn2-layout-proof-shape k i src) (natp pos) (natp next) (<= pos next)
                   (unsigned-byte-p 32 end) (<= next end) (<= size (1+ pos))
                   (if (zp size) (equal pos 0) (and (< pos size) (< next end)))
                   (implies (and (fn2-layout-proof-payload-tagp k) (<= h pos))
                            (fn2-layout-proof-bound-bytes k x size pos next val slot p)))
              (and (unsigned-byte-p 60 (nth 0 row)) (unsigned-byte-p 32 (nth 1 row))
                   (unsigned-byte-p 32 (nth 2 row))
                   (equal (fn2-layout-proof-at k (list (nth 0 row) slot (nth 1 row) (nth 2 row)) p) val))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn2-layout-proof-value fn2-layout-proof-at fn2-layout-proof-value-at
       fn2-layout-proof-magnitude
                                    fn2-layout-proof-shape fn2-layout-proof-payload)
                                  (fn2-layout-field-size fn2-layout-proof-prefix-size fn2-pool-logical-octets
                                   fn2-layout-kind-code))
            :do-not-induct t))))
(local
 (defun-nx fn2-layout-proof-place (k x size pos next i slot gen f)
   (let ((row (fn2-layout-proof-last-row k x size (- next pos))))
     (fn2-layout-store i (nth 0 row) slot gen (nth 1 row) (nth 2 row) 0 f))))
(local
 (defthm fn2-layout-proof-place-rows
   (equal (fn2-fields-rows (fn2-layout-proof-place k x size pos next i slot gen f))
          (fn2-fields-rows f))))
(local
 (defthm fn2-layout-proof-placed-value
   (let* ((k (cadar layout)) (x (fn2-layout-proof-magnitude k i src))
          (size (fn2-layout-field-size k i src)) (g (fn2-layout-proof-place k x size pos next i slot gen f)))
     (implies (and (consp layout) (fn2-layout-proof-reader-ready layout fuel i pos next lo end slot gen okind oslot
         ogen src orig f p)
                   (<= size (1+ pos)))
              (equal (fn2-layout-proof-at k (fn2-layout-proof-row i g) p) (fn2-layout-proof-value-at k i src orig))))
   :rule-classes nil
   :hints (("Goal" :use (fn2-layout-proof-reader-head fn2-layout-proof-payload-bound-now
       fn2-layout-proof-done-descriptor)
            :in-theory (union-theories '(fn2-layout-proof-reader-ready fn2-layout-proof-place
                fn2-layout-proof-row-of-store) (theory 'fn2-layout-proof-index-rules))))))

(local
 (defun-nx fn2-layout-proof-walk (layout fuel i pos next slot gen src f)
   (declare (xargs :measure (+ (nfix fuel) (len layout))
                   :hints (("Goal" :in-theory (disable fn2-layout-field-size fn2-layout-proof-place)))))
   (let* ((k (cadar layout)) (x (fn2-layout-proof-magnitude k i src)) (size (fn2-layout-field-size k i src))
          (empty (zp size)) (done (or empty (<= size (1+ pos))))
          (nx (if empty next (1+ next))) (fu (if empty fuel (1- fuel))))
     (cond ((or (atom layout) (and (not empty) (zp fuel))) (list next f))
           (done (fn2-layout-proof-walk (cdr layout) fu (1+ i) 0 nx slot gen src
                  (fn2-layout-proof-place k x size pos next i slot gen f)))
           (t (fn2-layout-proof-walk layout fu i (1+ pos) nx slot gen src f))))))
(local
 (defun-nx fn2-layout-proof-replay (layout fuel i pos next slot gen end okind oslot ogen src f p)
   (let* ((k (cadar layout)) (x (fn2-layout-proof-magnitude k i src))
          (c (fn2-layout-proof-expected-cursor k x (fn2-layout-field-size k i src) pos next)))
     (fn2-layout-proof-run layout fuel i c slot gen end okind oslot ogen f p))))
(local
 (defthm fn2-layout-proof-expected-next
   (equal (nth 6 (fn2-layout-proof-expected-cursor k x size pos next)) next)
   :hints (("Goal" :in-theory (disable fn2-layout-proof-prefix-size fn2-layout-proof-payload-tagp
       fn2-layout-proof-accumulator)))))
(local
 (defthm fn2-layout-proof-zero-cursor
   (equal (fn2-layout-proof-expected-cursor k x size 0 next) (list 0 0 0 0 0 0 next))
   :hints (("Goal" :in-theory (disable fn2-layout-varsize)))))
(local
 (defthm fn2-layout-proof-empty-tick
   (equal (fn2-layout-proof-tick '(:zero 0) c byte)
          (list :done (+ 1 (nth 0 c)) 0 0 0 (nth 4 c) 0 (nth 6 c)))
   :hints (("Goal" :in-theory (enable fn2-layout-proof-tick)))))
(local
 (defun-nx fn2-layout-proof-recovered (layout i end src orig r p)
   (and (consp r) (equal (car r) end)
        (equal (fn2-layout-values layout i (cdr r) p) (fn2-layout-values layout i src orig)))))
(local
 (defthm fn2-layout-proof-replay-frame
   (let ((r (fn2-layout-proof-replay layout fuel i pos next slot gen end okind oslot ogen src f p)))
     (implies (and r (natp j) (natp i) (< j i))
              (equal (fn2-layout-proof-row j (cdr r)) (fn2-layout-proof-row j f))))
   :hints (("Goal" :in-theory (e/d (fn2-layout-proof-run-frame) (fn2-layout-proof-expected-cursor fn2-layout-proof-row
                                          fn2-layout-proof-run))))))
(local
 (defthm fn2-layout-proof-recovered-nonempty
   (implies (fn2-layout-proof-recovered layout i end src orig r p) (consp r))
   :rule-classes :forward-chaining))
(local
 (defmacro fn2-layout-proof-replay-events (index)
   (let* ((k '(cadar layout)) (x `(fn2-layout-proof-magnitude ,k i src))
          (size `(fn2-layout-field-size ,k i src)) (empty `(zp ,size)) (done `(or ,empty (<= ,size (1+ pos))))
          (val `(fn2-layout-proof-value-at ,k i src orig))

          (l2 `(if ,done (cdr layout) layout)) (i2 `(if ,done (1+ i) i)) (pos2 `(if ,done 0 (1+ pos)))
          (fu `(if ,empty fuel (1- fuel))) (nx `(if ,empty next (1+ next)))
          (place `(fn2-layout-proof-place ,k ,x ,size pos next i slot gen f))
          (f2 `(if ,done ,place f))
          (r '(fn2-layout-proof-replay layout fuel i pos next slot gen end okind oslot ogen src f p))
          (r2 `(fn2-layout-proof-replay ,l2 ,fu ,i2 ,pos2 ,nx slot gen end okind oslot ogen src ,f2 p))
          (ready '(fn2-layout-proof-reader-ready layout fuel i pos next lo end slot gen okind oslot ogen src orig f p)))
     (nth index
      `((defthm fn2-layout-proof-replay-unfold
          (implies (and (consp layout) ,ready (fn2-pool-semanticp p))
                   (equal ,r ,r2))
          :rule-classes nil
          :hints (("Goal" :cases (,empty ,done)
                   :use (fn2-layout-proof-reader-head fn2-layout-proof-reader-input fn2-layout-proof-reader-tick)
                   :expand ((:free (cursor) (fn2-layout-proof-run layout fuel i cursor slot gen end okind oslot ogen
                       f p)))
                   :in-theory (e/d (fn2-layout-proof-place)
                            (fn2-layout-proof-reader-ready fn2-layout-proof-run fn2-layout-proof-tick
                                fn2-layout-proof-expected-cursor
                             fn2-layout-proof-last-row fn2-layout-proof-wire-byte fn2-layout-proof-zero-wire-byte
                             fn2-layout-proof-header-wire-byte fn2-pool-read fn2-layout-proof-value-at
                                 fn2-layout-kindp nfix mod
                             fn2-layout-proof-bound-bytes fn2-layout-proof-window)))))
        (defthm fn2-layout-proof-recovered-cons
          (implies (and (natp i) (consp layout) (fn2-layout-proof-recovered (cdr layout) (1+ i) end src orig child p)
                        (equal (fn2-layout-proof-at ,k (fn2-layout-proof-row i (cdr child)) p) ,val))
                   (fn2-layout-proof-recovered layout i end src orig child p))
          :rule-classes nil
          :hints (("Goal" :expand ((:free (j ff pp) (:with fn2-layout-proof-values-unfolds (fn2-layout-values layout
              j ff pp))))
                   :use ((:instance fn2-layout-proof-fields-view (f src) (p orig)))
                   :in-theory (disable fn2-layout-proof-at fn2-layout-proof-row fn2-layout-proof-value-at))))
        (defthm fn2-layout-proof-replay-step
          (implies (and (consp layout) ,ready (fn2-pool-semanticp p))
                   (and (or ,empty (posp fuel))
                        (fn2-layout-proof-reader-ready ,l2 ,fu ,i2 ,pos2 ,nx lo end slot gen okind oslot ogen src
                            orig ,f2 p)
                        (implies (fn2-layout-proof-recovered ,l2 ,i2 end src orig ,r2 p)
                                 (fn2-layout-proof-recovered layout i end src orig ,r p))))
          :rule-classes nil
          :hints (("Goal" :cases (,empty ,done)
                   :use (fn2-layout-proof-reader-head fn2-layout-proof-replay-unfold
                         (:instance fn2-layout-proof-reader-next-ready (f2 ,f2))
                         (:instance fn2-layout-proof-replay-frame (layout (cdr layout)) (fuel ,fu) (i (1+ i))
                          (pos 0) (next ,nx) (f ,place) (j i))
                         fn2-layout-proof-placed-value
                         (:instance fn2-layout-proof-recovered-cons (child ,r2)))
                   :in-theory (disable fn2-layout-proof-reader-ready fn2-layout-proof-place
                             fn2-layout-proof-replay fn2-layout-proof-recovered fn2-layout-proof-value-at
                                 fn2-layout-kindp
                             fn2-layout-proof-at fn2-layout-proof-row)))))))))
(local (fn2-layout-proof-replay-events 0))
(local (fn2-layout-proof-replay-events 1))
(local (fn2-layout-proof-replay-events 2))

(local
 (defthm fn2-layout-proof-replay-empty
   (implies (and (atom layout) (fn2-layout-proof-reader-ready layout fuel i pos next lo end slot gen okind oslot
       ogen src orig f p))
            (fn2-layout-proof-recovered layout i end src orig
              (fn2-layout-proof-replay layout fuel i pos next slot gen end okind oslot ogen src f p) p))
   :rule-classes nil
   :hints (("Goal" :expand ((fn2-layout-size layout i src)
                            (:free (cursor) (fn2-layout-proof-run layout fuel i cursor slot gen end okind oslot ogen
                                f p))
                            (:free (j ff pp) (fn2-layout-values layout j ff pp)))
            :in-theory (e/d (fn2-layout-proof-run fn2-layout-values) (fn2-layout-proof-expected-cursor
                fn2-layout-proof-window fn2-layout-proof-wire
                                fn2-layout-field-size fn2-layout-proof-bound-bytes fn2-layout-proof-shapes))))))
(local
 (defthm fn2-layout-proof-replay-correct
   (implies (and (fn2-layout-proof-reader-ready layout fuel i pos next lo end slot gen okind oslot ogen src orig f p)
                 (fn2-pool-semanticp p))
            (fn2-layout-proof-recovered layout i end src orig
              (fn2-layout-proof-replay layout fuel i pos next slot gen end okind oslot ogen src f p) p))
   :rule-classes nil
   :hints (("Goal" :induct (fn2-layout-proof-walk layout fuel i pos next slot gen src f)
            :in-theory (disable fn2-layout-proof-replay fn2-layout-proof-recovered fn2-layout-proof-reader-ready
                                fn2-layout-proof-place fn2-layout-field-size fn2-layout-proof-magnitude))
           (and (equal (length (cadr id)) 2)
                '(:use (fn2-layout-proof-replay-step fn2-layout-proof-replay-empty))))))
(local
 (defthm fn2-layout-proof-shapes-fit
   (implies (and (fn2-layout-proof-shapes layout i f) (natp i)
                 (integerp (fn2-fields-rows f)) (<= i (fn2-fields-rows f)))
            (<= (+ i (len layout)) (fn2-fields-rows f)))
   :rule-classes nil
   :hints (("Goal" :induct (fn2-layout-proof-layout-ind layout i)
            :expand ((fn2-layout-proof-shapes layout i f) (len layout))
            :in-theory (union-theories '(natp posp nfix zp-open default-car default-cdr car-cons cdr-cons
                fn2-layoutp-head len (:induction fn2-layout-proof-layout-ind)) (theory 'minimal-theory))))))
(local
 (defthm fn2-layout-proof-reader-start
   (implies (and (fn2-layout-roundtrip-hyps layout slot gen off okind oslot ogen f orig)
                 (equal end (+ off (fn2-layout-size layout 0 f)))
                 (fn2-pool-semanticp p) (equal (fn2-layout-range-code slot gen off end nil okind oslot ogen p) :ok)
                 (equal (fn2-layout-proof-window off end slot p)
                        (fn2-layout-proof-wire layout 0 0 f (fn2-layout-values layout 0 f orig)))
                 (fn2-layout-proof-shapes layout 0 f) (<= (fn2-layout-size layout 0 f) 4096))
            (fn2-layout-proof-reader-ready layout 4096 0 0 off off end slot gen okind oslot ogen f orig f p))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-layout-proof-shapes-fit (i 0))
                         fn2-layout-proof-range-types fn2-layout-proof-semantic-types
                         (:instance fn2-layout-proof-readable-row (start off) (writep nil)))
            :in-theory (disable fn2-layout-proof-wire fn2-layout-proof-window fn2-layout-proof-shapes fn2-layout-values
                                fn2-layout-field-size fn2-layout-proof-prefix-size fn2-layout-proof-bound-bytes
                                fn2-layout-proof-payload-tagp fn2-layout-proof-magnitude fn2-layout-size
                                fn2-layout-proof-range-types fn2-layoutp fn2-layout-max-size fn2-fields-wfp
                                    fn2-fieldsp)))))
(local
 (defthm fn2-layout-proof-read-back
   (let ((d (fn2-layout-decode layout slot gen off end okind oslot ogen f p)))
     (implies (and (fn2-layout-proof-reader-ready layout 4096 0 0 off off end slot gen okind oslot ogen f orig f p)
                   (fn2-pool-semanticp p) (<= (fn2-layout-max-size layout) 4096) (unsigned-byte-p 32 off))
              (and (equal (mv-nth 0 d) :ok) (equal (mv-nth 1 d) end)
                   (equal (fn2-layout-values layout 0 (mv-nth 2 d) p) (fn2-layout-values layout 0 f orig)))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-layout-proof-replay-correct (fuel 4096) (i 0) (pos 0) (next off) (lo off)
       (src f))
                         (:instance fn2-layout-proof-run-is-scan (i 0) (fuel 4096) (pos 0) (v 0) (hi 0) (size 0) (ref 0)
                                    (phase 0) (next off)))
            :in-theory (e/d (fn2-layout-decode fn2-layout-decode-run fn2-layout-values-of-save)
                             (fn2-layout-proof-expected-cursor fn2-layout-proof-run fn2-layout-max-size fn2-layout-size
                              fn2-layoutp fn2-layout-proof-wire fn2-layout-proof-window fn2-layout-proof-shapes
                              fn2-layout-field-size fn2-layout-values fn2-layout-scan fn2-layout-proof-nthcdr-at-end
                                  nthcdr-when-atom))))))
(local
 (defthm fn2-layout-proof-decode-encoded
   (let ((d (fn2-layout-decode layout slot gen off end okind oslot ogen f p)))
     (implies (and (fn2-layout-roundtrip-hyps layout slot gen off okind oslot ogen f orig)
                   (equal end (+ off (fn2-layout-size layout 0 f)))
                   (fn2-pool-semanticp p) (equal (fn2-layout-range-code slot gen off end nil okind oslot ogen p) :ok)
                   (equal (fn2-layout-proof-window off end slot p)
                          (fn2-layout-proof-wire layout 0 0 f (fn2-layout-values layout 0 f orig)))
                   (fn2-layout-proof-shapes layout 0 f) (<= (fn2-layout-size layout 0 f) 4096))
              (fn2-layout-roundtrip-resultp layout (fn2-layout-values layout 0 f orig) (mv-nth 0 d) (mv-nth 1 d) end
                  (fn2-layout-values layout 0 (mv-nth 2 d) p)
                  (fn2-pool-logical-octets (- end off) (+ (fn2-pool-base slot p) off) p))))
   :rule-classes nil
   :hints (("Goal" :use (fn2-layout-proof-reader-start fn2-layout-proof-read-back fn2-layout-canonical-proved)
            :in-theory (e/d (fn2-layout-canonical$owed)
                  (fn2-layout-proof-reader-ready fn2-layout-values fn2-layout-size fn2-layout-max-size fn2-layoutp
                      fn2-fieldsp
                   fn2-fields-wfp fn2-layout-proof-shapes fn2-layout-proof-window fn2-layout-proof-wire
                       fn2-layout-octets))))))
(defthm fn2-layout-roundtrip-proved
  (fn2-layout-roundtrip$owed layout slot gen off okind oslot ogen f p)
  :rule-classes nil
  :hints (("Goal" :use (fn2-layout-proof-roundtrip-encode
                       (:instance fn2-layout-proof-decode-encoded (orig p)
                        (p (mv-nth 2 (fn2-layout-encode layout slot gen off okind oslot ogen f p)))
                        (end (mv-nth 1 (fn2-layout-encode layout slot gen off okind oslot ogen f p)))))
           :in-theory (e/d (fn2-layout-roundtrip$owed fn2-layout-roundtrip-conclusion)
                     (fn2-layout-roundtrip-hyps fn2-layout-roundtrip-resultp fn2-layout-size fn2-layout-values
                      fn2-layout-proof-wire fn2-layout-proof-window fn2-layout-proof-shapes)))))
(fn2-owed-discharge fn2-layout-roundtrip fn2-layout-roundtrip-proved)
