; fn: the poster-bytes existing-article test over the octet buffer (D27
; boundary 6, wave B; prefix `fn-pbb-').
;
; `fn-pb-existing-action' (books/poster-bytes.lisp) is what the owner host
; asks before a prepare: is this Message-ID already held, and if so is the
; submission the same article (then :duplicate) or a different one (then
; :conflict).  "The same article" reads the injection source out of both
; payloads (`fn-inj-source-of', books/injection.lisp: strip the Path line,
; the Injection-Date line and the Injection-Info line, each a `fn-inj-strip'
; of a prefix off a suffix of the octets) and compares the sources, or the
; whole payloads when either has no readable source.
;
; Here the submitted payload is the octet buffer `fn-octets' instead of a
; list.  Every strip is an index walk (`fn-pbb-strip-at'), the source is a
; description of buffer positions, and the compare against the held
; record's payload (an octet list in the logical store, until wave C) reads
; the buffer in place: nothing of the submitted payload is consed.  A
; recipe v2 record's source is a suffix of the buffer; a recipe v3 record
; (D32, a supplied Path, `fn-inj-unsplice') gives its source back with the
; AGENT! insertion cut out of the Path content, so a source is (K A B):
; st[K..A) followed by st[B..), with K = A = B for a suffix, and the
; compare is `fn-pbb-range-match' over the first piece and
; `fn-oct-suffix-equalp' over the second.  The one keystone,
; `fn-pbb-existing-action-is-pb-existing-action', says the buffer function
; equals the list function on the buffer's logical value; the host calls
; the buffer function (host/owner-host.lisp `fn-owner-existing-action-buffer'
; and `fn-owner-prepare-buffer').

(in-package "ACL2")
(include-book "poster-bytes")
(include-book "octets-stobj")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; The list facts (local twins of the ones octets-stobj keeps local).

(local
 (defthm fn-pbb-nthcdr-of-true-listp
   (implies (true-listp xs) (true-listp (nthcdr i xs)))
   :hints (("Goal" :induct (nthcdr i xs) :in-theory (enable nthcdr)))))

(local
 (defthm fn-pbb-consp-nthcdr-within
   (implies (and (natp i) (true-listp xs) (< i (len xs)))
            (consp (nthcdr i xs)))
   :hints (("Goal" :induct (nthcdr i xs) :in-theory (enable nthcdr)))))

(local
 (defthm fn-pbb-nthcdr-beyond-is-nil
   (implies (and (natp i) (true-listp xs) (<= (len xs) i))
            (equal (nthcdr i xs) nil))
   :hints (("Goal" :induct (nthcdr i xs) :in-theory (enable nthcdr)))))

(local
 (defthm fn-pbb-car-nthcdr
   (equal (car (nthcdr i xs)) (nth i xs))
   :hints (("Goal" :induct (nthcdr i xs) :in-theory (enable nth nthcdr)))))

(local
 (defthm fn-pbb-cdr-nthcdr
   (implies (natp i)
            (equal (cdr (nthcdr i xs)) (nthcdr (1+ i) xs)))
   :hints (("Goal" :induct (nthcdr i xs) :in-theory (enable nthcdr)))))

(local
 (defthm fn-pbb-nthcdr-of-nthcdr
   (implies (and (natp i) (natp j))
            (equal (nthcdr j (nthcdr i xs)) (nthcdr (+ i j) xs)))
   :hints (("Goal" :induct (nthcdr i xs) :in-theory (enable nthcdr)))))

(local
 (defthm fn-pbb-len-nthcdr
   (implies (and (natp i) (<= i (len xs)))
            (equal (len (nthcdr i xs)) (- (len xs) i)))
   :hints (("Goal" :induct (nthcdr i xs) :in-theory (enable nthcdr)))))

(local (in-theory (disable nthcdr nth)))

; -----------------------------------------------------------------------------
; A prefix stripped at an index: the index past it, or :no.

(defun fn-pbb-strip-at (prefix i fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (<= i (fn-octets-len fn-octets)))
                  :measure (len prefix)))
  (if (consp prefix)
      (if (and (< i (fn-octets-len fn-octets))
               (equal (fn-octets-get i fn-octets) (car prefix)))
          (fn-pbb-strip-at (cdr prefix) (1+ i) fn-octets)
        :no)
    i))

(defthm fn-pbb-strip-at-bounds
  (implies (and (natp i) (<= i (len fn-octets))
                (not (equal (fn-pbb-strip-at prefix i fn-octets) :no)))
           (and (integerp (fn-pbb-strip-at prefix i fn-octets))
                (<= i (fn-pbb-strip-at prefix i fn-octets))
                (<= (fn-pbb-strip-at prefix i fn-octets) (len fn-octets))))
  :rule-classes ((:rewrite :corollary
                  (implies (and (natp i) (<= i (len fn-octets))
                                (not (equal (fn-pbb-strip-at prefix i fn-octets) :no)))
                           (integerp (fn-pbb-strip-at prefix i fn-octets))))
                 (:linear :trigger-terms ((fn-pbb-strip-at prefix i fn-octets))
                  :corollary
                  (implies (and (natp i) (<= i (len fn-octets))
                                (not (equal (fn-pbb-strip-at prefix i fn-octets) :no)))
                           (and (<= i (fn-pbb-strip-at prefix i fn-octets))
                                (<= (fn-pbb-strip-at prefix i fn-octets) (len fn-octets)))))))

; The same bounds as facts the arithmetic sees: a `:use' of the rewrite
; corollary above rewrites its own `integerp' conjunct away, and a sum with
; the index stays unnormalised.  Forward chaining keeps them in the type
; alist wherever the strip appears in a hypothesis.
(local
 (defthm fn-pbb-strip-at-bounds-fc
   (implies (and (natp i) (<= i (len fn-octets))
                 (not (equal (fn-pbb-strip-at prefix i fn-octets) :no)))
            (and (integerp (fn-pbb-strip-at prefix i fn-octets))
                 (<= i (fn-pbb-strip-at prefix i fn-octets))
                 (<= (fn-pbb-strip-at prefix i fn-octets) (len fn-octets))))
   :rule-classes ((:forward-chaining :trigger-terms ((fn-pbb-strip-at prefix i fn-octets))))
   :hints (("Goal" :use fn-pbb-strip-at-bounds))))

(defthm fn-pbb-strip-at-is-inj-strip
  (implies (and (natp i) (<= i (len fn-octets)) (true-listp fn-octets))
           (equal (fn-inj-strip prefix (nthcdr i fn-octets))
                  (if (equal (fn-pbb-strip-at prefix i fn-octets) :no)
                      :no
                    (nthcdr (fn-pbb-strip-at prefix i fn-octets) fn-octets))))
  :hints (("Goal" :induct (fn-pbb-strip-at prefix i fn-octets)
           :in-theory (enable fn-inj-strip))))

(in-theory (disable fn-pbb-strip-at))

(defun fn-pbb-strip-optional-at (line i fn-octets)
  ; The index past LINE when st[i..) opens with it, else I.
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (<= i (fn-octets-len fn-octets)))))
  (let ((r (fn-pbb-strip-at line i fn-octets)))
    (if (equal r :no) i r)))

(defthm fn-pbb-strip-optional-at-bounds
  (implies (and (natp i) (<= i (len fn-octets)))
           (and (integerp (fn-pbb-strip-optional-at line i fn-octets))
                (<= i (fn-pbb-strip-optional-at line i fn-octets))
                (<= (fn-pbb-strip-optional-at line i fn-octets) (len fn-octets))))
  :rule-classes ((:rewrite :corollary
                  (implies (and (natp i) (<= i (len fn-octets)))
                           (integerp (fn-pbb-strip-optional-at line i fn-octets))))
                 (:linear :trigger-terms ((fn-pbb-strip-optional-at line i fn-octets))
                  :corollary
                  (implies (and (natp i) (<= i (len fn-octets)))
                           (and (<= i (fn-pbb-strip-optional-at line i fn-octets))
                                (<= (fn-pbb-strip-optional-at line i fn-octets)
                                    (len fn-octets)))))))

(local
 (defthm fn-pbb-strip-optional-at-bounds-fc
   (implies (and (natp i) (<= i (len fn-octets)))
            (and (integerp (fn-pbb-strip-optional-at line i fn-octets))
                 (<= i (fn-pbb-strip-optional-at line i fn-octets))
                 (<= (fn-pbb-strip-optional-at line i fn-octets) (len fn-octets))))
   :rule-classes ((:forward-chaining
                   :trigger-terms ((fn-pbb-strip-optional-at line i fn-octets))))
   :hints (("Goal" :use fn-pbb-strip-optional-at-bounds))))

(defthm fn-pbb-strip-optional-at-is-inj-strip-optional
  (implies (and (natp i) (<= i (len fn-octets)) (true-listp fn-octets))
           (equal (fn-inj-strip-optional line (nthcdr i fn-octets))
                  (nthcdr (fn-pbb-strip-optional-at line i fn-octets) fn-octets)))
  :hints (("Goal" :in-theory (enable fn-inj-strip-optional))))

(in-theory (disable fn-pbb-strip-optional-at))

; -----------------------------------------------------------------------------
; The source walk: the index of the source, or nil.

(defun fn-pbb-source-after-stamp (k date agent msgid fn-octets)
  ; K is the index of what follows an Injection-Date line carrying DATE.
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp k) (<= k (fn-octets-len fn-octets)))))
  (let ((v1 (fn-pbb-strip-at (fn-inj-injection-info-line agent) k fn-octets)))
    (if (not (equal v1 :no))
        (if (or (not (equal (fn-pbb-strip-at (fn-inj-message-id-line msgid) v1 fn-octets)
                            :no))
                (not (equal (fn-pbb-strip-at (fn-inj-date-line date) v1 fn-octets) :no)))
            nil
          v1)
      (let ((s (fn-pbb-strip-at
                (fn-inj-injection-info-line agent)
                (fn-pbb-strip-optional-at
                 (fn-inj-date-line date)
                 (fn-pbb-strip-optional-at (fn-inj-message-id-line msgid) k fn-octets)
                 fn-octets)
                fn-octets)))
        (if (equal s :no) nil s)))))

(defthm fn-pbb-source-after-stamp-bounds
  (implies (and (natp k) (<= k (len fn-octets))
                (fn-pbb-source-after-stamp k date agent msgid fn-octets))
           (and (integerp (fn-pbb-source-after-stamp k date agent msgid fn-octets))
                (<= 0 (fn-pbb-source-after-stamp k date agent msgid fn-octets))
                (<= (fn-pbb-source-after-stamp k date agent msgid fn-octets)
                    (len fn-octets))))
  :rule-classes ((:rewrite :corollary
                  (implies (and (natp k) (<= k (len fn-octets))
                                (fn-pbb-source-after-stamp k date agent msgid fn-octets))
                           (integerp (fn-pbb-source-after-stamp k date agent msgid fn-octets))))
                 (:linear :trigger-terms ((fn-pbb-source-after-stamp k date agent msgid fn-octets))
                  :corollary
                  (implies (and (natp k) (<= k (len fn-octets))
                                (fn-pbb-source-after-stamp k date agent msgid fn-octets))
                           (and (<= 0 (fn-pbb-source-after-stamp k date agent msgid fn-octets))
                                (<= (fn-pbb-source-after-stamp k date agent msgid fn-octets)
                                    (len fn-octets)))))))

(defthm fn-pbb-source-after-stamp-is-inj-source-after-stamp
  (implies (and (natp k) (<= k (len fn-octets)) (true-listp fn-octets))
           (equal (fn-inj-source-after-stamp (nthcdr k fn-octets) date agent msgid)
                  (if (fn-pbb-source-after-stamp k date agent msgid fn-octets)
                      (cons t (nthcdr (fn-pbb-source-after-stamp k date agent msgid fn-octets)
                                      fn-octets))
                    nil)))
  :hints (("Goal" :in-theory (enable fn-inj-source-after-stamp))))

(in-theory (disable fn-pbb-source-after-stamp))

; `fn-inj-take' and `fn-inj-drop' on a suffix of a true list.

(local
 (defthm fn-pbb-inj-drop-is-nthcdr
   (implies (true-listp x)
            (equal (fn-inj-drop n x) (nthcdr (nfix n) x)))
   :hints (("Goal" :in-theory (enable fn-inj-drop nthcdr)))))

(local
 (defthm fn-pbb-inj-take-is-take
   (implies (true-listp x)
            (equal (fn-inj-take n x) (take (min (nfix n) (len x)) x)))
   :hints (("Goal" :induct (fn-inj-take n x) :in-theory (enable fn-inj-take)))))

; -----------------------------------------------------------------------------
; The walk past the Path line: the index of the source, or nil.
;
; A recipe v2 (or v1) record opens with this agent's Path line and the walk
; starts past it.  A recipe v3 record (D32, a supplied Path) opens with the
; injected block, never with a Path line, and `fn-inj-source-of' reads it
; as the v2 inverse of the record with the agent's Path line prepended:
; over the buffer that is the same walk from index 0.

(defun fn-pbb-source-after-path (r1 agent msgid fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp r1) (<= r1 (fn-octets-len fn-octets)))
                  :guard-hints (("Goal" :in-theory (disable len)))))
  (cond ((equal (fn-pbb-strip-at *fn-inj-injection-date-field* r1 fn-octets) :no)
         (let ((s (fn-pbb-strip-at (fn-inj-injection-info-line agent) r1 fn-octets)))
           (if (equal s :no) nil s)))
        (t
         (let* ((j (fn-pbb-strip-at *fn-inj-injection-date-field* r1 fn-octets))
                (date (fn-oct-slice-list j (min (+ j 31) (fn-octets-len fn-octets))
                                         fn-octets))
                (r2 (fn-pbb-strip-at (fn-inj-injection-date-line date) r1 fn-octets)))
           (if (equal r2 :no)
               nil
             (fn-pbb-source-after-stamp r2 date agent msgid fn-octets))))))

; A strip that succeeds lands exactly (len prefix) past its start.
(local
 (defthm fn-pbb-strip-at-success-index
   (implies (and (natp i) (true-listp prefix)
                 (not (equal (fn-pbb-strip-at prefix i fn-octets) :no)))
            (equal (fn-pbb-strip-at prefix i fn-octets) (+ i (len prefix))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-pbb-strip-at)
            :induct (fn-pbb-strip-at prefix i fn-octets)))))

(local
 (defthm fn-pbb-nthcdr-0
   (equal (nthcdr 0 x) x)
   :hints (("Goal" :in-theory (enable nthcdr)))))

; The three indices of the walk past R1, named for the hints below: J past
; the Injection-Date field, DATE the 31 octets there, R2 past the
; Injection-Date line.
(local
 (defmacro fn-pbb-j () '(fn-pbb-strip-at *fn-inj-injection-date-field* r1 fn-octets)))
(local
 (defmacro fn-pbb-date ()
   '(fn-oct-slice-list (fn-pbb-j) (min (+ (fn-pbb-j) 31) (len fn-octets)) fn-octets)))
(local
 (defmacro fn-pbb-r2 ()
   '(fn-pbb-strip-at (fn-inj-injection-date-line (fn-pbb-date)) r1 fn-octets)))

(defthm fn-pbb-source-after-path-bounds
  (implies (and (natp r1) (<= r1 (len fn-octets))
                (fn-pbb-source-after-path r1 agent msgid fn-octets))
           (and (integerp (fn-pbb-source-after-path r1 agent msgid fn-octets))
                (<= 0 (fn-pbb-source-after-path r1 agent msgid fn-octets))
                (<= (fn-pbb-source-after-path r1 agent msgid fn-octets)
                    (len fn-octets))))
  :rule-classes ((:rewrite :corollary
                  (implies (and (natp r1) (<= r1 (len fn-octets))
                                (fn-pbb-source-after-path r1 agent msgid fn-octets))
                           (integerp (fn-pbb-source-after-path r1 agent msgid fn-octets))))
                 (:linear :trigger-terms ((fn-pbb-source-after-path r1 agent msgid fn-octets))
                  :corollary
                  (implies (and (natp r1) (<= r1 (len fn-octets))
                                (fn-pbb-source-after-path r1 agent msgid fn-octets))
                           (and (<= 0 (fn-pbb-source-after-path r1 agent msgid fn-octets))
                                (<= (fn-pbb-source-after-path r1 agent msgid fn-octets)
                                    (len fn-octets))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pbb-source-after-path) (len))
           :use ((:instance fn-pbb-strip-at-bounds (prefix *fn-inj-injection-date-field*)
                            (i r1))
                 (:instance fn-pbb-strip-at-bounds (prefix (fn-inj-injection-info-line agent))
                            (i r1))
                 (:instance fn-pbb-strip-at-bounds
                            (prefix (fn-inj-injection-date-line (fn-pbb-date))) (i r1))
                 (:instance fn-pbb-source-after-stamp-bounds (k (fn-pbb-r2))
                            (date (fn-pbb-date)))))))

; The list walk past the Path line, as `fn-inj-source-of-v2' continues
; after its strip: the local twin the correspondence is stated against.
(local
 (defun fn-pbb-v2-tail (r1 agent msgid)
   (cond ((equal (fn-inj-strip *fn-inj-injection-date-field* r1) :no)
          (let ((s (fn-inj-strip (fn-inj-injection-info-line agent) r1)))
            (if (equal s :no) nil (cons t s))))
         (t
          (let* ((date (fn-inj-take 31 (fn-inj-drop (len *fn-inj-injection-date-field*)
                                                    r1)))
                 (r2 (fn-inj-strip (fn-inj-injection-date-line date) r1)))
            (if (equal r2 :no)
                nil
              (fn-inj-source-after-stamp r2 date agent msgid)))))))

(local
 (defthm fn-pbb-source-of-v2-splits
   (equal (fn-inj-source-of-v2 stored agent msgid)
          (let ((r1 (fn-inj-strip (fn-inj-path-line agent) stored)))
            (if (equal r1 :no) nil (fn-pbb-v2-tail r1 agent msgid))))
   :hints (("Goal" :in-theory (enable fn-inj-source-of-v2)))))

(local
 (defthm fn-pbb-source-after-path-is-v2-tail
   (implies (and (natp r1) (<= r1 (len fn-octets)) (true-listp fn-octets))
            (equal (fn-pbb-v2-tail (nthcdr r1 fn-octets) agent msgid)
                   (if (fn-pbb-source-after-path r1 agent msgid fn-octets)
                       (cons t (nthcdr (fn-pbb-source-after-path r1 agent msgid fn-octets)
                                       fn-octets))
                     nil)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-pbb-source-after-path) (len))
            :use ((:instance fn-pbb-strip-at-bounds (prefix *fn-inj-injection-date-field*)
                             (i r1))
                  (:instance fn-pbb-strip-at-success-index
                             (prefix *fn-inj-injection-date-field*) (i r1))
                  (:instance fn-pbb-strip-at-bounds
                             (prefix (fn-inj-injection-date-line (fn-pbb-date))) (i r1)))))))

(in-theory (disable fn-pbb-source-after-path))

; -----------------------------------------------------------------------------
; The list facts the v3 inverse rests on: `fn-inj-take-n', `fn-inj-drop-n'
; and `fn-inj-frontp' (books/injection-path.lisp) on a suffix of a true
; list, and the lines this book strips are true lists.

(local
 (defthm fn-pbb-inj-take-n-is-take
   (implies (true-listp x)
            (equal (fn-inj-take-n n x) (take (min (nfix n) (len x)) x)))
   :hints (("Goal" :induct (fn-inj-take-n n x) :in-theory (enable fn-inj-take-n)))))

(local
 (defthm fn-pbb-inj-drop-n-is-nthcdr
   (implies (true-listp x)
            (equal (fn-inj-drop-n n x) (nthcdr (nfix n) x)))
   :hints (("Goal" :in-theory (enable fn-inj-drop-n nthcdr)))))

(local
 (defthm fn-pbb-frontp-is-strip
   (implies (true-listp x)
            (equal (fn-inj-frontp p x) (not (equal (fn-inj-strip p x) :no))))
   :hints (("Goal" :induct (fn-inj-frontp p x)
            :in-theory (enable fn-inj-frontp fn-inj-strip)))))

(local
 (defthm fn-pbb-strip-of-append
   (implies (true-listp p)
            (equal (fn-inj-strip p (fn-inj-append p x)) x))
   :hints (("Goal" :induct (fn-inj-append p x)
            :in-theory (enable fn-inj-strip fn-inj-append)))))

(local
 (defthm fn-pbb-append-true-listp
   (implies (true-listp b) (true-listp (fn-inj-append a b)))
   :hints (("Goal" :in-theory (enable fn-inj-append)))))

(local
 (defthm fn-pbb-path-line-true-listp
   (true-listp (fn-inj-path-line agent))
   :hints (("Goal" :in-theory (enable fn-inj-path-line)))))

(local
 (defthm fn-pbb-path-insert-true-listp
   (true-listp (fn-inj-path-insert agent))
   :hints (("Goal" :in-theory (enable fn-inj-path-insert)))))

(local
 (defthm fn-pbb-path-insert-consp
   (consp (fn-inj-path-insert agent))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-inj-path-insert)))))

; A line stripped where the buffer ends: what `fn-inj-strip' answers on
; the nil suffix, which the nthcdr rules reach before the index twin does.
(local
 (defthm fn-pbb-strip-consp-of-nil
   (implies (consp p) (equal (fn-inj-strip p nil) :no))
   :hints (("Goal" :in-theory (enable fn-inj-strip)))))

(local
 (defthm fn-pbb-slice-true-listp
   (true-listp (fn-oct-slice-list i n fn-octets))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (e/d (fn-oct-slice-list) (fn-oct-slice-list-is-take-nthcdr))))))

(local
 (defthm fn-pbb-len-of-slice
   (implies (and (natp i) (natp n))
            (equal (len (fn-oct-slice-list i n fn-octets)) (nfix (- n i))))
   :hints (("Goal" :induct (fn-oct-slice-list i n fn-octets)
            :in-theory (e/d (fn-oct-slice-list) (fn-oct-slice-list-is-take-nthcdr))))))

(local
 (defthm fn-pbb-nthcdr-min-len
   (implies (and (natp m) (true-listp xs))
            (equal (nthcdr (min m (len xs)) xs) (nthcdr m xs)))))

; -----------------------------------------------------------------------------
; The Path scan by index: where the Path content begins in st[i..).

(defun fn-pbb-path-openp (i fn-octets)
  ; `fn-inj-path-openp' on st[i..): "Path: " with the name in any case.
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (<= i (fn-octets-len fn-octets)))))
  (let ((h (fn-oct-slice-list i (min (+ i 6) (fn-octets-len fn-octets)) fn-octets)))
    (and (equal (len h) 6)
         (equal (fn-inj-downcase (fn-inj-take-n 4 h)) '(112 97 116 104))
         (equal (nth 4 h) 58)
         (equal (nth 5 h) 32))))

(defthm fn-pbb-path-openp-is-inj-path-openp
  (implies (and (natp i) (<= i (len fn-octets)) (true-listp fn-octets))
           (equal (fn-inj-path-openp (nthcdr i fn-octets))
                  (fn-pbb-path-openp i fn-octets)))
  :hints (("Goal" :in-theory (enable fn-inj-path-openp))))

(local
 (defthm fn-pbb-path-openp-needs-six
   (implies (and (natp i) (<= i (len fn-octets)) (fn-pbb-path-openp i fn-octets))
            (<= (+ i 6) (len fn-octets)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (e/d (fn-pbb-path-openp)
                                   (fn-oct-slice-list-is-take-nthcdr))))))

(in-theory (disable fn-pbb-path-openp))

(defun fn-pbb-path-scan (i bol fn-octets)
  ; `fn-inj-path-scan' on st[i..), as an index into the buffer: the index
  ; past "Path: " on the first header line at or after I that opens with
  ; it, or nil.  BOL says I is at the start of a line; an empty line ends
  ; the header.
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (<= i (fn-octets-len fn-octets)))
                  :measure (nfix (- (fn-octets-len fn-octets) (nfix i)))))
  (cond ((or (not (natp i)) (>= i (fn-octets-len fn-octets))) nil)
        ((and bol (fn-pbb-path-openp i fn-octets)) (+ i 6))
        ((and bol (equal (fn-octets-get i fn-octets) 13)) nil)
        ((and (equal (fn-octets-get i fn-octets) 13)
              (< (1+ i) (fn-octets-len fn-octets))
              (equal (fn-octets-get (1+ i) fn-octets) 10))
         (fn-pbb-path-scan (+ i 2) t fn-octets))
        (t (fn-pbb-path-scan (1+ i) nil fn-octets))))

(defthm fn-pbb-path-scan-bounds
  (implies (and (natp i) (<= i (len fn-octets))
                (fn-pbb-path-scan i bol fn-octets))
           (and (integerp (fn-pbb-path-scan i bol fn-octets))
                (<= (+ i 6) (fn-pbb-path-scan i bol fn-octets))
                (<= (fn-pbb-path-scan i bol fn-octets) (len fn-octets))))
  :rule-classes ((:rewrite :corollary
                  (implies (and (natp i) (<= i (len fn-octets))
                                (fn-pbb-path-scan i bol fn-octets))
                           (integerp (fn-pbb-path-scan i bol fn-octets))))
                 (:linear :trigger-terms ((fn-pbb-path-scan i bol fn-octets))
                  :corollary
                  (implies (and (natp i) (<= i (len fn-octets))
                                (fn-pbb-path-scan i bol fn-octets))
                           (and (<= (+ i 6) (fn-pbb-path-scan i bol fn-octets))
                                (<= (fn-pbb-path-scan i bol fn-octets) (len fn-octets))))))
  :hints (("Goal" :induct (fn-pbb-path-scan i bol fn-octets))))

(local
 (defthm fn-pbb-path-scan-bounds-fc
   (implies (and (natp i) (<= i (len fn-octets)) (fn-pbb-path-scan i bol fn-octets))
            (and (integerp (fn-pbb-path-scan i bol fn-octets))
                 (<= (+ i 6) (fn-pbb-path-scan i bol fn-octets))
                 (<= (fn-pbb-path-scan i bol fn-octets) (len fn-octets))))
   :rule-classes ((:forward-chaining :trigger-terms ((fn-pbb-path-scan i bol fn-octets))))
   :hints (("Goal" :use fn-pbb-path-scan-bounds))))

(defthm fn-pbb-path-scan-is-inj-path-scan
  (implies (and (natp i) (<= i (len fn-octets)) (true-listp fn-octets))
           (equal (fn-inj-path-scan (nthcdr i fn-octets) bol)
                  (if (fn-pbb-path-scan i bol fn-octets)
                      (- (fn-pbb-path-scan i bol fn-octets) i)
                    nil)))
  :hints (("Goal" :induct (fn-pbb-path-scan i bol fn-octets)
           :in-theory (enable fn-inj-path-scan))))

(in-theory (disable fn-pbb-path-scan))

; -----------------------------------------------------------------------------
; A source in the buffer is described, never copied: (K A B) names the
; octets st[K..A) followed by st[B..).  A v2 record's source is a suffix
; (K = A = B); a v3 record's source is its suffix at K with the AGENT!
; insertion st[A..B) cut out of its Path content.

(defun fn-pbb-descp (d n)
  (declare (xargs :guard t))
  (and (consp d) (consp (cdr d)) (consp (cddr d))
       (natp (car d)) (natp (cadr d)) (natp (caddr d))
       (<= (car d) (cadr d)) (<= (cadr d) (caddr d))
       (natp n) (<= (caddr d) n)))

(defun fn-pbb-desc-list (d xs)
  ; The octets a description names, as a list: the logical twin of the
  ; source the list inverse gives back.  Never run on the served path.
  (declare (xargs :guard (and (true-listp xs) (fn-pbb-descp d (len xs)))))
  (append (take (- (cadr d) (car d)) (nthcdr (car d) xs))
          (nthcdr (caddr d) xs)))

(defun fn-pbb-unsplice-at (k agent fn-octets)
  ; `fn-inj-unsplice' of st[k..): the description of that suffix with
  ; AGENT! removed from the start of its Path content, or nil when it has
  ; no Path line or its content does not open with AGENT!.
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp k) (<= k (fn-octets-len fn-octets)))))
  (let ((p (fn-pbb-path-scan k t fn-octets)))
    (if (not p)
        nil
      (let ((b (fn-pbb-strip-at (fn-inj-path-insert agent) p fn-octets)))
        (if (equal b :no) nil (list k p b))))))

(defthm fn-pbb-unsplice-at-bounds
  (implies (and (natp k) (<= k (len fn-octets))
                (fn-pbb-unsplice-at k agent fn-octets))
           (fn-pbb-descp (fn-pbb-unsplice-at k agent fn-octets) (len fn-octets)))
  :hints (("Goal" :in-theory (disable len)
           :use ((:instance fn-pbb-strip-at-bounds (prefix (fn-inj-path-insert agent))
                            (i (fn-pbb-path-scan k t fn-octets)))))))

(defthm fn-pbb-unsplice-at-is-inj-unsplice
  (implies (and (natp k) (<= k (len fn-octets)) (true-listp fn-octets))
           (equal (fn-inj-unsplice (nthcdr k fn-octets) agent)
                  (if (fn-pbb-unsplice-at k agent fn-octets)
                      (cons t (fn-pbb-desc-list (fn-pbb-unsplice-at k agent fn-octets)
                                                fn-octets))
                    nil)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-inj-unsplice fn-inj-path-offset) (len))
           :use ((:instance fn-pbb-strip-at-success-index
                            (prefix (fn-inj-path-insert agent))
                            (i (fn-pbb-path-scan k t fn-octets)))
                 (:instance fn-pbb-strip-at-bounds (prefix (fn-inj-path-insert agent))
                            (i (fn-pbb-path-scan k t fn-octets)))))))

(in-theory (disable fn-pbb-unsplice-at))

(defun fn-pbb-source-index (agent msgid fn-octets)
  ; The description (K A B) of the injection source in the buffer, or nil.
  (declare (xargs :stobjs fn-octets :guard t
                  :guard-hints
                  (("Goal"
                    :in-theory (disable len)
                    :use ((:instance fn-pbb-strip-at-bounds
                                     (prefix (fn-inj-path-line agent)) (i 0)))))))
  (let ((r1 (fn-pbb-strip-at (fn-inj-path-line agent) 0 fn-octets)))
    (if (not (equal r1 :no))
        (let ((k (fn-pbb-source-after-path r1 agent msgid fn-octets)))
          (if k (list k k k) nil))
      (let ((k (fn-pbb-source-after-path 0 agent msgid fn-octets)))
        (if k (fn-pbb-unsplice-at k agent fn-octets) nil)))))

(defthm fn-pbb-source-index-bounds
  (implies (and (true-listp fn-octets)
                (fn-pbb-source-index agent msgid fn-octets))
           (fn-pbb-descp (fn-pbb-source-index agent msgid fn-octets) (len fn-octets)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pbb-source-index) (len))
           :use ((:instance fn-pbb-strip-at-bounds (prefix (fn-inj-path-line agent)) (i 0))))))

(defthm fn-pbb-source-index-is-inj-source-of
  (implies (true-listp fn-octets)
           (equal (fn-inj-source-of fn-octets agent msgid)
                  (if (fn-pbb-source-index agent msgid fn-octets)
                      (cons t (fn-pbb-desc-list (fn-pbb-source-index agent msgid fn-octets)
                                                fn-octets))
                    nil)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-inj-source-of fn-pbb-source-index) (len))
           :use ((:instance fn-pbb-strip-at-is-inj-strip (prefix (fn-inj-path-line agent)) (i 0))
                 (:instance fn-pbb-strip-at-bounds (prefix (fn-inj-path-line agent)) (i 0))
                 (:instance fn-pbb-source-after-path-is-v2-tail
                            (r1 (fn-pbb-strip-at (fn-inj-path-line agent) 0 fn-octets)))
                 (:instance fn-pbb-source-after-path-is-v2-tail (r1 0))))))

(in-theory (disable fn-pbb-source-index))

; -----------------------------------------------------------------------------
; The compare of a described source against a list, read in place.

(defun fn-pbb-range-match (i n xs fn-octets)
  ; XS with the octets st[i..n) removed from its front, or :no when it does
  ; not open with them.
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp n) (<= i n) (<= n (fn-octets-len fn-octets)))
                  :measure (nfix (- n i))))
  (if (or (not (natp i)) (not (natp n)) (<= n i))
      xs
    (if (and (consp xs) (equal (fn-octets-get i fn-octets) (car xs)))
        (fn-pbb-range-match (1+ i) n (cdr xs) fn-octets)
      :no)))

(defthm fn-pbb-range-match-is-equal-of-append
  (implies (and (natp i) (natp n) (<= i n) (<= n (len fn-octets))
                (true-listp fn-octets) (true-listp tail))
           (equal (equal (append (fn-oct-slice-list i n fn-octets) tail) xs)
                  (let ((r (fn-pbb-range-match i n xs fn-octets)))
                    (and (not (equal r :no)) (equal tail r)))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-pbb-range-match i n xs fn-octets)
           :in-theory (e/d (fn-oct-slice-list) (fn-oct-slice-list-is-take-nthcdr)))))

(in-theory (disable fn-pbb-range-match))

(defun fn-pbb-desc-equalp (d xs fn-octets)
  ; Whether the octets D names are exactly XS, read in place: XS opens with
  ; st[K..A) and the rest of it is st[B..).
  (declare (xargs :stobjs fn-octets
                  :guard (fn-pbb-descp d (fn-octets-len fn-octets))))
  (let ((r (fn-pbb-range-match (car d) (cadr d) xs fn-octets)))
    (if (equal r :no) nil (fn-oct-suffix-equalp (caddr d) r fn-octets))))

(defthm fn-pbb-desc-equalp-is-equal
  (implies (and (fn-pbb-descp d (len fn-octets)) (true-listp fn-octets))
           (equal (fn-pbb-desc-equalp d xs fn-octets)
                  (equal (fn-pbb-desc-list d fn-octets) xs)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-pbb-range-match-is-equal-of-append
                            (i (car d)) (n (cadr d))
                            (tail (nthcdr (caddr d) fn-octets)))))))

(in-theory (disable fn-pbb-desc-equalp))

; -----------------------------------------------------------------------------
; The first line, the Path agent, and the compare.

(defun fn-pbb-line (fn-octets)
  ; The first line of the buffer through its LF, or all of it: `fn-pb-line'.
  (declare (xargs :stobjs fn-octets :guard t))
  (fn-oct-slice-list 0 (fn-oct-line-end 0 fn-octets) fn-octets))

(defun fn-pbb-line-at (i fn-octets)
  ; The line at I through its LF, or the rest of the buffer: `fn-pb-line'
  ; of st[i..).
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (<= i (fn-octets-len fn-octets)))))
  (fn-oct-slice-list i (fn-oct-line-end i fn-octets) fn-octets))

(local
 (defthm fn-pbb-line-at-is-pb-line-slice
   (implies (and (natp i) (<= i (len fn-octets)) (true-listp fn-octets))
            (equal (fn-pb-line (nthcdr i fn-octets))
                   (fn-oct-slice-list i (fn-oct-line-end i fn-octets) fn-octets)))
   ; The slice stays in its recursive form here: as `take' (the exported
   ; rule) it no longer follows the line-end recursion.
   :hints (("Goal" :induct (fn-oct-line-end i fn-octets)
            :in-theory (e/d (fn-oct-line-end fn-oct-slice-list fn-pb-line)
                            (fn-oct-slice-list-is-take-nthcdr))))))

(defthm fn-pbb-line-is-pb-line
  (implies (true-listp fn-octets)
           (equal (fn-pbb-line fn-octets) (fn-pb-line fn-octets)))
  :hints (("Goal" :use ((:instance fn-pbb-line-at-is-pb-line-slice (i 0)))
           :in-theory (enable nthcdr))))

(defthm fn-pbb-line-at-is-pb-line
  (implies (and (natp i) (<= i (len fn-octets)) (true-listp fn-octets))
           (equal (fn-pb-line (nthcdr i fn-octets)) (fn-pbb-line-at i fn-octets))))

(in-theory (disable fn-pbb-line fn-pbb-line-at))

(defun fn-pbb-path-line-agent (fn-octets)
  ; `fn-pb-path-line-agent' with its line read from the buffer.
  (declare (xargs :stobjs fn-octets :guard t))
  (let* ((line (fn-pbb-line fn-octets))
         (r (fn-inj-strip *fn-inj-path-field* line)))
    (if (and (true-listp r) (< *fn-pb-path-tail-length* (len r)))
        (let ((agent (fn-inj-take (- (len r) *fn-pb-path-tail-length*) r)))
          (if (equal (fn-inj-path-line agent) line) agent nil))
      nil)))

(defthm fn-pbb-path-line-agent-is-pb-path-line-agent
  (implies (true-listp fn-octets)
           (equal (fn-pbb-path-line-agent fn-octets) (fn-pb-path-line-agent fn-octets)))
  :hints (("Goal" :in-theory (enable fn-pb-path-line-agent))))

(in-theory (disable fn-pbb-path-line-agent))

(defun fn-pbb-info-line-agent (i fn-octets)
  ; `fn-pb-info-line-agent' of st[i..): the agent an Injection-Info line at
  ; I names.
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (<= i (fn-octets-len fn-octets)))))
  (let* ((line (fn-pbb-line-at i fn-octets))
         (r (fn-inj-strip *fn-inj-injection-info-field* line)))
    (if (and (true-listp r) (< 2 (len r)))
        (let ((agent (fn-inj-take (- (len r) 2) r)))
          (if (equal (fn-inj-injection-info-line agent) line) agent nil))
      nil)))

(defthm fn-pbb-info-line-agent-is-pb-info-line-agent
  (implies (and (natp i) (<= i (len fn-octets)) (true-listp fn-octets))
           (equal (fn-pb-info-line-agent (nthcdr i fn-octets))
                  (fn-pbb-info-line-agent i fn-octets)))
  :hints (("Goal" :in-theory (enable fn-pb-info-line-agent))))

(in-theory (disable fn-pbb-info-line-agent))

(defun fn-pbb-block-agent (msgid fn-octets)
  ; `fn-pb-block-agent' over the buffer: past an Injection-Date line (49
  ; octets), a Message-ID line of MSGID and a Date line (39 octets), each
  ; when present, the agent the Injection-Info line names.
  (declare (xargs :stobjs fn-octets :guard t
                  :guard-hints (("Goal" :in-theory (disable len)))))
  (let* ((n (fn-octets-len fn-octets))
         (i1 (if (equal (fn-pbb-strip-at *fn-inj-injection-date-field* 0 fn-octets) :no)
                 0
               (min *fn-pb-stamp-line-length* n)))
         (i2 (fn-pbb-strip-optional-at (fn-inj-message-id-line msgid) i1 fn-octets))
         (i3 (if (equal (fn-pbb-strip-at *fn-inj-date-field* i2 fn-octets) :no)
                 i2
               (min (+ i2 *fn-pb-date-line-length*) n))))
    (fn-pbb-info-line-agent i3 fn-octets)))

; The three indices of the block walk, named for the hint below.
(local
 (defmacro fn-pbb-i1 ()
   '(if (equal (fn-pbb-strip-at *fn-inj-injection-date-field* 0 fn-octets) :no)
        0
      (min *fn-pb-stamp-line-length* (len fn-octets)))))
(local
 (defmacro fn-pbb-i2 ()
   '(fn-pbb-strip-optional-at (fn-inj-message-id-line msgid) (fn-pbb-i1) fn-octets)))
(local
 (defmacro fn-pbb-i3 ()
   '(if (equal (fn-pbb-strip-at *fn-inj-date-field* (fn-pbb-i2) fn-octets) :no)
        (fn-pbb-i2)
      (min (+ (fn-pbb-i2) *fn-pb-date-line-length*) (len fn-octets)))))

(defthm fn-pbb-block-agent-is-pb-block-agent
  (implies (true-listp fn-octets)
           (equal (fn-pb-block-agent fn-octets msgid)
                  (fn-pbb-block-agent msgid fn-octets)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pb-block-agent fn-pb-opensp) (len))
           :use ((:instance fn-pbb-strip-at-is-inj-strip
                            (prefix *fn-inj-injection-date-field*) (i 0))
                 (:instance fn-pbb-strip-optional-at-is-inj-strip-optional
                            (line (fn-inj-message-id-line msgid)) (i (fn-pbb-i1)))
                 (:instance fn-pbb-strip-optional-at-bounds
                            (line (fn-inj-message-id-line msgid)) (i (fn-pbb-i1)))
                 (:instance fn-pbb-strip-at-is-inj-strip
                            (prefix *fn-inj-date-field*) (i (fn-pbb-i2)))
                 (:instance fn-pbb-info-line-agent-is-pb-info-line-agent
                            (i (fn-pbb-i3)))))))

(in-theory (disable fn-pbb-block-agent))

(defun fn-pbb-path-agent (msgid fn-octets)
  ; `fn-pb-path-agent' over the buffer: the agent the leading Path line
  ; names (recipe v1 and v2), else the one the v3 block's Injection-Info
  ; line names.
  (declare (xargs :stobjs fn-octets :guard t))
  (or (fn-pbb-path-line-agent fn-octets) (fn-pbb-block-agent msgid fn-octets)))

(defthm fn-pbb-path-agent-is-pb-path-agent
  (implies (true-listp fn-octets)
           (equal (fn-pbb-path-agent msgid fn-octets)
                  (fn-pb-path-agent fn-octets msgid)))
  :hints (("Goal" :in-theory (enable fn-pb-path-agent))))

(in-theory (disable fn-pbb-path-agent))

(defun fn-pbb-same-articlep (msgid fn-octets held-payload)
  ; `fn-pb-same-articlep' with the submitted payload in the buffer: the
  ; sources compared by index when both read, else the whole payloads.
  (declare (xargs :stobjs fn-octets :guard t))
  (let* ((agent (fn-pbb-path-agent msgid fn-octets))
         (d (fn-pbb-source-index agent msgid fn-octets))
         (b (fn-pb-subject held-payload agent msgid)))
    (if (and d (equal (car b) :source))
        (fn-pbb-desc-equalp d (cdr b) fn-octets)
      (fn-oct-suffix-equalp 0 held-payload fn-octets))))

(defthm fn-pbb-same-articlep-is-pb-same-articlep
  (implies (true-listp fn-octets)
           (equal (fn-pbb-same-articlep msgid fn-octets held-payload)
                  (fn-pb-same-articlep msgid fn-octets held-payload)))
  :hints (("Goal" :in-theory (enable fn-pb-same-articlep fn-pb-subject nthcdr))))

(in-theory (disable fn-pbb-same-articlep
                    fn-pbb-line-is-pb-line fn-pbb-line-at-is-pb-line
                    fn-pbb-path-line-agent-is-pb-path-line-agent
                    fn-pbb-info-line-agent-is-pb-info-line-agent
                    fn-pbb-block-agent-is-pb-block-agent
                    fn-pbb-path-agent-is-pb-path-agent))

(defun fn-pbb-existing-action (msgid fn-octets groups s)
  ; `fn-pb-existing-action' with the submitted payload in the buffer.
  (declare (xargs :stobjs fn-octets :guard t))
  (let ((article (fn-find-article
                  msgid (fn-state-articles
                         (fn-node-acceptance (fn-sn-node s))))))
    (if article
        (if (and (fn-pbb-same-articlep (fn-record-string-octets msgid) fn-octets
                                       (fn-article-payload article))
                 (equal groups (fn-article-groups article)))
            :duplicate
          :conflict)
      nil)))

; The keystone: on the buffer's logical value the buffer function is the
; list function.  The hypothesis is the stobj's recognizer, which every
; live buffer satisfies (it is the guard of every stobj argument).
(defthm fn-pbb-existing-action-is-pb-existing-action
  (implies (fn-octets-p fn-octets)
           (equal (fn-pbb-existing-action msgid fn-octets groups s)
                  (fn-pb-existing-action msgid fn-octets groups s)))
  :hints (("Goal" :in-theory (enable fn-pb-existing-action fn-octets-p))))

(in-theory (disable fn-pbb-existing-action))

; The buffer's logical value is an octet list in the acceptance model's
; vocabulary too: the recognizer test the list entry made is discharged by
; the representation.
(defthm fn-pbb-buffer-is-octet-listp
  (implies (fn-octets-p fn-octets)
           (fn-octet-listp fn-octets))
  :hints (("Goal" :induct (fn-cbor-octet-listp fn-octets)
           :in-theory (enable fn-octets-p fn-cbor-octet-listp fn-cbor-octetp
                              fn-octet-listp fn-octetp))))
