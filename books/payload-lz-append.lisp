; fn: the append of a compressed record (lane compression-extents-2, the host
; wiring of C2; PRF-341, continuing PRF-326).  Prefix
; `fn-lzr-'.
;
; books/payload-lz-record.lisp proved the frame: `fn-lzr-seal' frames a record
; R only when the host's candidate block decodes to R's payload span, and the
; expansion of the seal is R (KEYSTONE `fn-lzr-expand-of-seal').  The seal is
; total: whatever goes wrong, R is kept.  At the append that is not enough.
; A candidate the proved decoder refuses means the encoder (liblz4-HC,
; untrusted) produced something that is not the span: that is a FAULT, named,
; never a silent uncompressed record.  So the append decides through
; `fn-lzr-append-decide', whose outcomes are distinct:
;
;   (:framed Z)             the frame the log takes: the seal's own octets
;   (:kept :lz-no-gain)     POLICY (by name): the encoder answered that no
;                           block fits in fewer than N - 21 octets, or the
;                           candidate decodes to the span and the frame would
;                           not be shorter than R; the record is taken as R
;   (:kept :lz-span)        the span is not R's (a host that did not take it
;                           from `fn-lzr-append-plan'); R is taken as it is
;   (:refused :lz-candidate) the candidate does not decode to the span: the
;                           host signals a named store fault, nothing is taken
;
; THE PLAN.  `fn-lzr-append-plan MIN R' is the host's one question before it
; runs the encoder: the payload span (K . N) of the article record R, when
; the threshold MIN (the configuration row compress-min-octets; 0 is off) wants
; it compressed, and NIL otherwise.  The span is ACL2's: R decodes as a record
; (the codec, books/records-seam.lisp) and its payload opens at K
; (books/payload-extent.lisp fn-arx-record-suffix-len; checked, never
; assumed).  A span above LZ4_MAX_INPUT_SIZE is not planned (the host
; primitive's domain; the policy keeps R).  With MIN = 0 the plan is NIL for
; every record (`fn-lzr-append-plan-off'): the host takes R, byte for byte
; what it took before this book.
;
; THE DIGESTS stay over the ORIGINAL octets: the content identity, the
; Message-ID's D25 comparison, a signature and Cancel-Lock are computed before
; the append, and the replay reads R back from the frame
; (`fn-lzr-append-replay-reads-the-record', from the predecessor's
; `fn-lzr-replay-reads-the-sealed-record').
;
; THE READ.  Every record the log hands out goes through `fn-lzr-expand'
; (host/native/io.lisp fnn-log-stream-segment: the one place records leave
; the log): R for a record that is not a frame, the expansion of a frame, or
; a refusal whose line `fn-lzr-read-refusal-text' names.  A record is never
; mistaken for a frame (`fn-lzr-record-is-not-a-frame': the codec's magic is
; not the frame's head).
(in-package "ACL2")
(include-book "payload-lz-record")
(include-book "config")

; -----------------------------------------------------------------------------
; 1. The plan.

; LZ4_MAX_INPUT_SIZE (third_party/lz4/lz4.h, 1.10.0): the largest source the
; host's encoder accepts.  The decoder has no such bound.
(defconst *fn-lzr-encoder-max-input* 2113929216)

(defthm fn-lzr-decoded-record-p
  (implies (fn-record-result-okp (fn-record-decode-exact r))
           (fn-record-p (fn-record-result-record (fn-record-decode-exact r))))
  :hints (("Goal" :use ((:instance fn-record-accepted-input-is-canonical (octets r))
                        (:instance fn-record-accepted-input-bounds (octets r))
                        (:instance fn-record-encode-domain
                                   (record (fn-record-result-record
                                            (fn-record-decode-exact r)))))
           :in-theory (disable fn-record-accepted-input-is-canonical
                               fn-record-encode-domain fn-record-result-okp
                               fn-record-result-record))))

; The payload span of the article record R: (K . N), R's octets [K, K+N)
; being the payload of the record R decodes to; NIL for anything else.
(defun fn-lzr-record-span (r)
  (declare (xargs :guard (fn-cbor-octet-listp r)
                  :guard-hints (("Goal" :use fn-lzr-decoded-record-p
                                 :in-theory (disable fn-lzr-decoded-record-p
                                                     fn-record-result-okp
                                                     fn-record-result-record
                                                     fn-arx-record-suffix-len)))))
  (let ((d (fn-record-decode-exact r)))
    (if (fn-record-result-okp d)
        (let* ((w (fn-record-result-record d))
               (p (fn-record-payload w))
               (k (- (len r) (+ (fn-arx-record-suffix-len w) (len p)))))
          (if (and (natp k) (fn-arx-prefixp p (nthcdr k r)))
              (cons k (len p))
            nil))
      nil)))

(defun fn-lzr-append-plan (min r)
  (declare (xargs :guard (fn-cbor-octet-listp r)))
  (let ((s (fn-lzr-record-span r)))
    (if (and (consp s)
             (fn-lzr-want-p min (cdr s))
             (<= (cdr s) *fn-lzr-encoder-max-input*))
        s
      nil)))

; Compression off: no record is planned, so the host takes every record as
; it is.
(defthm fn-lzr-append-plan-off
  (implies (zp min)
           (equal (fn-lzr-append-plan min r) nil)))

; THE SWITCH is a configuration row, not a profile field (the coordinator's
; decision, 2026-09-27: per-store codec switches are configuration events in
; the log; the profile is capacity).  `policy set compress-min-octets N'
; (books/native-admin.lisp) publishes the `:set-limit' row (SLOT, "", N);
; the owner reads it from its live configuration (host/owner-host.lisp
; fn-owner-compress-min-octets) and hands it to the plan as MIN.  No row is
; off (`fn-lzr-config-min-without-a-row-is-off'), so every store written
; before this book, and every store whose operator never sets the row,
; appends exactly as before.  The frame represents every span of every
; record the codec accepts (a record has a u32 length:
; fn-record-accepted-input-bounds), so no profile needs validating for it.
(defconst *fn-lzr-slot* "compress-min-octets")

(defun fn-lzr-config-min (v)
  (declare (xargs :guard t))
  (fn-cfg-limit v *fn-lzr-slot*))

(defthm fn-lzr-config-min-without-a-row-is-off
  (implies (not (consp (fn-cfg-row-lookup (fn-cfg-limits v) *fn-lzr-slot*)))
           (and (equal (fn-lzr-config-min v) 0)
                (equal (fn-lzr-append-plan (fn-lzr-config-min v) r) nil)))
  :hints (("Goal" :in-theory (e/d (fn-cfg-limit) (fn-lzr-append-plan)))))

; The capacity the host gives the encoder: a block of more octets than this
; frames no shorter than R, so the host asks for no more
; (`fn-lzr-compress-p': CLEN + 21 < N).
(defun fn-lzr-candidate-cap (n)
  (declare (xargs :guard t))
  (if (and (natp n) (< (+ *fn-lzr-head-len* 1) n))
      (- n (+ *fn-lzr-head-len* 1))
    0))

; -----------------------------------------------------------------------------
; 2. The decision.

(defun fn-lzr-span-okp (r k n)
  (declare (xargs :guard t))
  (and (fn-cbor-octet-listp r)
       (fn-lzr-u32p k) (fn-lzr-u32p n) (fn-lzr-u32p (len r))
       (<= (+ k n) (len r))))

; CANDIDATE is the encoder's block (octets) or :NONE (it answered that no
; block fits `fn-lzr-candidate-cap').
(defun fn-lzr-append-decide (dict dict-id min r k n candidate)
  (declare (xargs :guard (and (fn-cbor-octet-listp dict) (fn-cbor-octet-listp r)
                              (natp k) (natp n)
                              (or (eq candidate :none) (fn-cbor-octet-listp candidate)))))
  (cond ((not (and (fn-lzr-span-okp r k n) (fn-lzr-u32p dict-id)))
         (list :kept :lz-span))
        ((eq candidate :none) (list :kept :lz-no-gain))
        ((not (equal (fn-lz-decode dict candidate n) (list :ok (take n (nthcdr k r)))))
         (list :refused :lz-candidate))
        ((not (fn-lzr-compress-p min n (len candidate))) (list :kept :lz-no-gain))
        (t (list :framed (fn-lzr-seal dict dict-id min r k n candidate)))))

; The octets the log takes for a decision (R unless framed).
(defun fn-lzr-append-octets (decision r)
  (declare (xargs :guard t))
  (if (and (consp decision) (eq (car decision) :framed) (consp (cdr decision)))
      (cadr decision)
    r))

(defun fn-lzr-append-refusal-text (decision)
  (declare (xargs :guard t))
  (if (and (consp decision) (eq (car decision) :refused))
      "lz-candidate: the LZ4 encoder's block does not decode to the record's payload (the encoder is untrusted; nothing was taken)"
    nil))

; -----------------------------------------------------------------------------
; 3. What each outcome means.

; KEYSTONE (the append's frame is the record).  A framed decision's octets
; expand, under any table binding DICT-ID to DICT, to R.
(defthm fn-lzr-append-decide-framed-expands
  (implies (and (equal (car (fn-lzr-append-decide dict dict-id min r k n candidate)) :framed)
                (equal (assoc-equal dict-id dicts) (cons dict-id dict)))
           (equal (fn-lzr-expand dicts (cadr (fn-lzr-append-decide dict dict-id min r k n
                                                                   candidate)))
                  (list :ok r)))
  :hints (("Goal" :in-theory (e/d (fn-lzr-span-okp)
                                  (fn-lzr-seal fn-lzr-expand fn-lz-decode fn-lzr-compress-p
                                   fn-lzr-u32p take nthcdr)))))

; The framed octets are the seal's, and a frame (not R).
(defthm fn-lzr-append-decide-framed-is-the-seal
  (implies (equal (car (fn-lzr-append-decide dict dict-id min r k n candidate)) :framed)
           (and (equal (cadr (fn-lzr-append-decide dict dict-id min r k n candidate))
                       (fn-lzr-seal dict dict-id min r k n candidate))
                (fn-lzr-compress-p min n (len candidate))
                (equal (fn-lz-decode dict candidate n) (list :ok (take n (nthcdr k r))))))
  :hints (("Goal" :in-theory (disable fn-lzr-seal fn-lz-decode fn-lzr-compress-p take nthcdr))))

; A refusal is exactly a candidate the proved decoder does not decode to the
; span: the fault is the encoder's, and it is named.
(defthm fn-lzr-append-decide-refuses-exactly-a-bad-candidate
  (iff (equal (fn-lzr-append-decide dict dict-id min r k n candidate)
              (list :refused :lz-candidate))
       (and (fn-lzr-span-okp r k n) (fn-lzr-u32p dict-id)
            (not (eq candidate :none))
            (not (equal (fn-lz-decode dict candidate n) (list :ok (take n (nthcdr k r)))))))
  :hints (("Goal" :in-theory (disable fn-lzr-seal fn-lz-decode fn-lzr-compress-p take nthcdr
                                      fn-lzr-span-okp))))

; The policy by name: R is kept for no gain only when the encoder found no
; block within the cap, or the frame would not be shorter than R.
(defthm fn-lzr-append-decide-keeps-only-without-gain
  (implies (equal (fn-lzr-append-decide dict dict-id min r k n candidate)
                  (list :kept :lz-no-gain))
           (or (eq candidate :none)
               (not (fn-lzr-compress-p min n (len candidate)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-lzr-seal fn-lz-decode fn-lzr-compress-p take nthcdr
                                      fn-lzr-span-okp))))

(local
 (defthm fn-lzr-len-frame-local
   (equal (len (fn-lzr-frame dict-id k n stub c))
          (+ *fn-lzr-head-len* (len stub) (len c)))
   :hints (("Goal" :in-theory (enable fn-lzr-frame fn-lzr-u32)))))

(local
 (defthm fn-lzr-len-take-local
   (equal (len (take n x)) (nfix n))
   :hints (("Goal" :in-theory (enable take)))))

(local
 (defthm fn-lzr-len-nthcdr-local
   (equal (len (nthcdr n x)) (nfix (- (len x) (nfix n))))
   :hints (("Goal" :induct (nthcdr n x) :in-theory (enable nthcdr)))))

; The frame is shorter than R: it fits every bound R fits (the profile's
; max-record-octets, the log kernel's take).
(defthm fn-lzr-append-decide-framed-is-shorter
  (implies (equal (car (fn-lzr-append-decide dict dict-id min r k n candidate)) :framed)
           (< (len (cadr (fn-lzr-append-decide dict dict-id min r k n candidate)))
              (len r)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (fn-lzr-seal fn-lzr-span-okp fn-lzr-compress-p)
                                  (fn-lz-decode fn-lzr-frame take nthcdr)))))

(defthm fn-lzr-append-octets-of-decide
  (equal (fn-lzr-append-octets (fn-lzr-append-decide dict dict-id min r k n candidate) r)
         (if (equal (car (fn-lzr-append-decide dict dict-id min r k n candidate)) :framed)
             (cadr (fn-lzr-append-decide dict dict-id min r k n candidate))
           r))
  :hints (("Goal" :in-theory (disable fn-lzr-seal fn-lz-decode fn-lzr-compress-p take nthcdr
                                      fn-lzr-span-okp))))

; -----------------------------------------------------------------------------
; 5. The read step the host calls, and the store's report.
;
; host/native/io.lisp fnn-log-read-record calls `fn-lzr-read-step' for every
; record the log hands out (fnn-log-stream-segment): the expansion, and the
; tally of what the log holds -- records, compressed records, the octets the
; log holds for them and their expansions, the dictionary ids in use -- that
; `store ROOT compression' prints through `fn-lzr-tally-text'.

(defun fn-lzr-tally-empty ()
  (declare (xargs :guard t))
  (list 0 0 0 0 nil))

(defun fn-lzr-tally-add (tally z r)
  (declare (xargs :guard (and (true-listp tally) (true-listp z) (true-listp r))))
  (let* ((records (nfix (nth 0 tally))) (framed (nfix (nth 1 tally)))
         (stored (nfix (nth 2 tally))) (original (nfix (nth 3 tally)))
         (ids (nth 4 tally))
         (framep (fn-lzr-magicp z))
         (id (and framep (fn-arx-u32-list (nthcdr 5 z)))))
    (list (1+ records)
          (if framep (1+ framed) framed)
          (+ stored (len z))
          (+ original (len r))
          (if (and framep (true-listp ids) (not (member-equal id ids)))
              (cons id ids)
            ids))))

(defun fn-lzr-read-step (tally dicts z)
  (declare (xargs :guard (and (true-listp tally) (fn-lzr-dictsp dicts) (fn-cbor-octet-listp z))
                  :guard-hints (("Goal" :in-theory (disable fn-lzr-expand fn-lzr-magicp)))))
  (let ((x (fn-lzr-expand dicts z)))
    (mv x (if (and (eq (car x) :ok) (true-listp (cadr x)))
              (fn-lzr-tally-add tally z (cadr x))
            tally))))

; The read step's record is the expansion (the subject of the keystones above).
(defthm fn-lzr-read-step-expands-by-definition
  (equal (mv-nth 0 (fn-lzr-read-step tally dicts z)) (fn-lzr-expand dicts z))
  :hints (("Goal" :in-theory (disable fn-lzr-expand fn-lzr-tally-add))))

(local
 (defthm fn-lzr-explode-is-characters
   (implies (character-listp acc)
            (character-listp (explode-nonnegative-integer n base acc)))
   :hints (("Goal" :in-theory (disable floor mod)))))

(defun fn-lzr-nat-text (n)
  (declare (xargs :guard t))
  (coerce (explode-nonnegative-integer (nfix n) 10 nil) 'string))

(defun fn-lzr-nats-text (ns)
  (declare (xargs :guard t))
  (if (atom ns)
      ""
    (if (atom (cdr ns))
        (fn-lzr-nat-text (car ns))
      (concatenate 'string (fn-lzr-nat-text (car ns)) "," (fn-lzr-nats-text (cdr ns))))))

(defthm fn-lzr-nats-text-stringp
  (stringp (fn-lzr-nats-text ns))
  :rule-classes :type-prescription)

; `store ROOT compression': MIN the profile's compress-min-octets.
(defun fn-lzr-tally-text (min tally)
  (declare (xargs :guard (true-listp tally)))
  (concatenate 'string
               "compression: compress-min-octets=" (fn-lzr-nat-text min)
               (if (posp min) "" " (off)")
               " records=" (fn-lzr-nat-text (nth 0 tally))
               " compressed-records=" (fn-lzr-nat-text (nth 1 tally))
               " stored-octets=" (fn-lzr-nat-text (nth 2 tally))
               " uncompressed-octets=" (fn-lzr-nat-text (nth 3 tally))
               " dictionaries=" (if (consp (nth 4 tally)) (fn-lzr-nats-text (nth 4 tally)) "none")))

; -----------------------------------------------------------------------------
; 4. The read, and the digests: the replay reads the record back.

; A record's encoding begins with the codec's magic, which is not the frame's
; head: the read passes it through unchanged.
(defthm fn-lzr-record-is-not-a-frame
  (implies (fn-record-result-okp (fn-record-decode-exact r))
           (and (not (fn-lzr-magicp r))
                (equal (fn-lzr-expand dicts r) (list :ok r))))
  :hints (("Goal" :use ((:instance fn-record-accepted-input-magic (octets r)))
           :in-theory (disable fn-record-result-okp))))

(defun fn-lzr-read-refusal-text (x)
  (declare (xargs :guard t))
  (cond ((equal x (list :refused :lz-frame))
         "log-frame-malformed: a compressed record's frame does not parse")
        ((equal x (list :refused :lz-dictionary))
         "log-frame-dictionary: a compressed record names a dictionary this store does not hold")
        ((equal x (list :refused :lz-decode))
         "log-frame-decode: a compressed record's block does not decode to its span")
        (t nil)))

; The record the log takes for an article record R (whatever the decision:
; a refused one takes nothing, and its octets are R) expands, under the
; store's table, to R, and decodes as the record R decodes to: its payload is
; the authored article the identities were computed over.
(defthm fn-lzr-append-replay-reads-the-record
  (implies (and (fn-record-result-okp (fn-record-decode-exact r))
                (equal (assoc-equal dict-id dicts) (cons dict-id dict)))
           (let ((x (fn-lzr-expand
                     dicts (fn-lzr-append-octets
                            (fn-lzr-append-decide dict dict-id min r k n candidate) r))))
             (and (equal (car x) :ok)
                  (equal (cadr x) r)
                  (equal (fn-record-decode-exact (cadr x)) (fn-record-decode-exact r)))))
  :hints (("Goal" :use (fn-lzr-append-decide-framed-expands
                        (:instance fn-lzr-record-is-not-a-frame))
           :in-theory (disable fn-lzr-append-decide fn-lzr-expand fn-lzr-append-decide-framed-expands
                               fn-lzr-record-is-not-a-frame fn-record-result-okp))))
