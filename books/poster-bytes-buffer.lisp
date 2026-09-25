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
; list.  Every strip is an index walk (`fn-pbb-strip-at'), the source is an
; index into the buffer, and the compare against the held record's payload
; (an octet list in the logical store, until wave C) is `fn-oct-suffix-equalp':
; nothing of the submitted payload is consed.  The one keystone,
; `fn-pbb-existing-action-is-pb-existing-action', says the buffer function
; equals the list function on the buffer's logical value; the host calls
; the buffer function (host/owner-host.lisp `fn-owner-existing-action-buffer'
; and `fn-owner-prepare-buffer').

(in-package "ACL2")
(include-book "poster-bytes")
(include-book "octets-stobj")

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

(defun fn-pbb-source-index (agent msgid fn-octets)
  ; The index of the injection source in the buffer, or nil.
  (declare (xargs :stobjs fn-octets :guard t
                  :guard-hints
                  (("Goal"
                    :in-theory (disable len)
                    :use ((:instance fn-pbb-strip-at-bounds
                                     (prefix (fn-inj-path-line agent)) (i 0))
                          (:instance fn-pbb-strip-at-bounds
                                     (prefix *fn-inj-injection-date-field*)
                                     (i (fn-pbb-strip-at (fn-inj-path-line agent)
                                                         0 fn-octets))))))))
  (let ((r1 (fn-pbb-strip-at (fn-inj-path-line agent) 0 fn-octets)))
    (cond ((equal r1 :no) nil)
          ((equal (fn-pbb-strip-at *fn-inj-injection-date-field* r1 fn-octets) :no)
           (let ((s (fn-pbb-strip-at (fn-inj-injection-info-line agent) r1 fn-octets)))
             (if (equal s :no) nil s)))
          (t
           (let* ((j (fn-pbb-strip-at *fn-inj-injection-date-field* r1 fn-octets))
                  (date (fn-oct-slice-list j (min (+ j 31) (fn-octets-len fn-octets))
                                           fn-octets))
                  (r2 (fn-pbb-strip-at (fn-inj-injection-date-line date) r1 fn-octets)))
             (if (equal r2 :no)
                 nil
               (fn-pbb-source-after-stamp r2 date agent msgid fn-octets)))))))

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

; The four indices of the walk, named for the hints below: R1 past the
; Path line, J past the Injection-Date field, DATE the 31 octets there, R2
; past the Injection-Date line.
(local
 (defmacro fn-pbb-r1 () '(fn-pbb-strip-at (fn-inj-path-line agent) 0 fn-octets)))
(local
 (defmacro fn-pbb-j () '(fn-pbb-strip-at *fn-inj-injection-date-field* (fn-pbb-r1) fn-octets)))
(local
 (defmacro fn-pbb-date ()
   '(fn-oct-slice-list (fn-pbb-j) (min (+ (fn-pbb-j) 31) (len fn-octets)) fn-octets)))
(local
 (defmacro fn-pbb-r2 ()
   '(fn-pbb-strip-at (fn-inj-injection-date-line (fn-pbb-date)) (fn-pbb-r1) fn-octets)))

(defthm fn-pbb-source-index-bounds
  (implies (and (true-listp fn-octets)
                (fn-pbb-source-index agent msgid fn-octets))
           (and (integerp (fn-pbb-source-index agent msgid fn-octets))
                (<= 0 (fn-pbb-source-index agent msgid fn-octets))
                (<= (fn-pbb-source-index agent msgid fn-octets) (len fn-octets))))
  :rule-classes ((:rewrite :corollary
                  (implies (and (true-listp fn-octets)
                                (fn-pbb-source-index agent msgid fn-octets))
                           (integerp (fn-pbb-source-index agent msgid fn-octets))))
                 (:linear :trigger-terms ((fn-pbb-source-index agent msgid fn-octets))
                  :corollary
                  (implies (and (true-listp fn-octets)
                                (fn-pbb-source-index agent msgid fn-octets))
                           (and (<= 0 (fn-pbb-source-index agent msgid fn-octets))
                                (<= (fn-pbb-source-index agent msgid fn-octets)
                                    (len fn-octets))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pbb-source-index) (len))
           :use ((:instance fn-pbb-strip-at-bounds (prefix (fn-inj-path-line agent)) (i 0))
                 (:instance fn-pbb-strip-at-bounds (prefix *fn-inj-injection-date-field*)
                            (i (fn-pbb-r1)))
                 (:instance fn-pbb-strip-at-bounds (prefix (fn-inj-injection-info-line agent))
                            (i (fn-pbb-r1)))
                 (:instance fn-pbb-strip-at-bounds
                            (prefix (fn-inj-injection-date-line (fn-pbb-date))) (i (fn-pbb-r1)))
                 (:instance fn-pbb-source-after-stamp-bounds (k (fn-pbb-r2)) (date (fn-pbb-date)))))))

(defthm fn-pbb-source-index-is-inj-source-of
  (implies (true-listp fn-octets)
           (equal (fn-inj-source-of fn-octets agent msgid)
                  (if (fn-pbb-source-index agent msgid fn-octets)
                      (cons t (nthcdr (fn-pbb-source-index agent msgid fn-octets) fn-octets))
                    nil)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-inj-source-of fn-pbb-source-index) (len))
           :use ((:instance fn-pbb-strip-at-is-inj-strip (prefix (fn-inj-path-line agent)) (i 0))
                 (:instance fn-pbb-strip-at-bounds (prefix (fn-inj-path-line agent)) (i 0))
                 (:instance fn-pbb-strip-at-bounds (prefix *fn-inj-injection-date-field*)
                            (i (fn-pbb-r1)))
                 (:instance fn-pbb-strip-at-success-index (prefix *fn-inj-injection-date-field*)
                            (i (fn-pbb-r1)))
                 (:instance fn-pbb-strip-at-bounds
                            (prefix (fn-inj-injection-date-line (fn-pbb-date))) (i (fn-pbb-r1)))))))

(in-theory (disable fn-pbb-source-index))

; -----------------------------------------------------------------------------
; The first line, the Path agent, and the compare.

(defun fn-pbb-line (fn-octets)
  ; The first line of the buffer through its LF, or all of it: `fn-pb-line'.
  (declare (xargs :stobjs fn-octets :guard t))
  (fn-oct-slice-list 0 (fn-oct-line-end 0 fn-octets) fn-octets))

(local
 (defthm fn-pbb-line-at-is-pb-line
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
  :hints (("Goal" :use ((:instance fn-pbb-line-at-is-pb-line (i 0)))
           :in-theory (enable nthcdr))))

(in-theory (disable fn-pbb-line))

(defun fn-pbb-path-agent (fn-octets)
  ; `fn-pb-path-agent' with its line read from the buffer.
  (declare (xargs :stobjs fn-octets :guard t))
  (let* ((line (fn-pbb-line fn-octets))
         (r (fn-inj-strip *fn-inj-path-field* line)))
    (if (and (true-listp r) (< *fn-pb-path-tail-length* (len r)))
        (let ((agent (fn-inj-take (- (len r) *fn-pb-path-tail-length*) r)))
          (if (equal (fn-inj-path-line agent) line) agent nil))
      nil)))

(defthm fn-pbb-path-agent-is-pb-path-agent
  (implies (true-listp fn-octets)
           (equal (fn-pbb-path-agent fn-octets) (fn-pb-path-agent fn-octets)))
  :hints (("Goal" :in-theory (enable fn-pb-path-agent))))

(in-theory (disable fn-pbb-path-agent))

(defun fn-pbb-same-articlep (msgid fn-octets held-payload)
  ; `fn-pb-same-articlep' with the submitted payload in the buffer: the
  ; sources compared by index when both read, else the whole payloads.
  (declare (xargs :stobjs fn-octets :guard t))
  (let* ((agent (fn-pbb-path-agent fn-octets))
         (a (fn-pbb-source-index agent msgid fn-octets))
         (b (fn-pb-subject held-payload agent msgid)))
    (if (and a (equal (car b) :source))
        (fn-oct-suffix-equalp a (cdr b) fn-octets)
      (fn-oct-suffix-equalp 0 held-payload fn-octets))))

(defthm fn-pbb-same-articlep-is-pb-same-articlep
  (implies (true-listp fn-octets)
           (equal (fn-pbb-same-articlep msgid fn-octets held-payload)
                  (fn-pb-same-articlep msgid fn-octets held-payload)))
  :hints (("Goal" :in-theory (enable fn-pb-same-articlep fn-pb-subject nthcdr))))

(in-theory (disable fn-pbb-same-articlep
                    fn-pbb-line-is-pb-line fn-pbb-path-agent-is-pb-path-agent))

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
