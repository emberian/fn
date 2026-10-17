; Digest-free history logical interface, shared by P3 and the generic.
(in-package "ACL2")
(include-book "consumer-event-index")

(local (include-book "arithmetic/top" :dir :system))

;; The tau system is off in this book (lane tau-pass, tools/tau_cost.py).
;; Its work is proof time no prover step counts (docs/proof-style.md
;; 9.1); planning/evidence/tau-cost-*.json has this book's figures.
(local (in-theory (disable (tau-system))))

; -----------------------------------------------------------------------------
; The key: the Message-ID of an event's article, taken by SHAPE.
;
; `fn-cei-event-article' (the article an event commits) tests `fn-hstxa-p',
; whose supporters reach `fn-digest'.  The index keys by the digest-free
; shape instead: an event headed :hstxa is read at its held position, any
; other event is its own article.  This over-approximates (a malformed
; :hstxa event is keyed and then refused at lookup), and every event whose
; exact article is a held record is keyed by that record's Message-ID
; (`fn-hist-key-article-of-held').

(defun fn-hist-key-article (ev)
  (declare (xargs :guard t))
  (if (and (consp ev) (eq (car ev) :hstxa)) (fn-hstxa-held ev) ev))

(defun fn-hist-key-msgid (ev)
  (declare (xargs :guard t))
  (fn-record-msgid (fn-hist-key-article ev)))

; FNV-1a over the Message-ID's characters (ACL2 characters are octets),
; 32 bits, from the salted offset basis.
(defconst *fn-hist-fnv-prime* 16777619)
(defconst *fn-hist-fnv-basis* 2166136261)
(defconst *fn-hist-u32-modulus* 4294967296)

(defun fn-hist-fnv (s i h)
  (declare (xargs :guard (and (stringp s) (natp i) (natp h))
                  :measure (nfix (- (length s) (nfix i)))))
  (if (and (stringp s) (natp i) (< i (length s)))
      (fn-hist-fnv s (1+ i)
                   (mod (* (logxor (nfix h) (char-code (char s i)))
                           *fn-hist-fnv-prime*)
                        *fn-hist-u32-modulus*))
    (nfix h)))

(defun fn-hist-hash (msgid salt)
  (declare (xargs :guard (stringp msgid)))
  (fn-hist-fnv msgid 0 (mod (logxor *fn-hist-fnv-basis* (nfix salt))
                            *fn-hist-u32-modulus*)))

(defthm fn-hist-fnv-natp
  (natp (fn-hist-fnv s i h))
  :rule-classes :type-prescription)

(defthm fn-hist-hash-natp
  (natp (fn-hist-hash msgid salt))
  :rule-classes :type-prescription)

(verify-guards fn-hist-fnv)
(verify-guards fn-hist-hash)

; -----------------------------------------------------------------------------
; The logical side: the history list.

(defun fn-hist$ap (x)
  (declare (xargs :guard t))
  (true-listp x))

(defun create-fn-hist$a ()
  (declare (xargs :guard t))
  nil)

(defun fn-hist$a-count (fn-hist$a)
  (declare (xargs :guard (fn-hist$ap fn-hist$a)))
  (len fn-hist$a))

(defun fn-hist$a-at (seq fn-hist$a)
  (declare (xargs :guard (and (natp seq) (fn-hist$ap fn-hist$a)
                              (< seq (fn-hist$a-count fn-hist$a)))))
  (nth seq fn-hist$a))

(defun fn-hist$a-msgid-records (msgid fn-hist$a)
  (declare (xargs :guard (and (stringp msgid) (fn-hist$ap fn-hist$a))))
  (fn-cei-article-records-for msgid fn-hist$a))

(defun fn-hist$a-append (ev fn-hist$a)
  (declare (xargs :guard (fn-hist$ap fn-hist$a)))
  (append fn-hist$a (list ev)))

(defun fn-hist$a-clear (salt fn-hist$a)
  (declare (xargs :guard (unsigned-byte-p 32 salt))
           (ignore salt fn-hist$a))
  nil)

; -----------------------------------------------------------------------------
