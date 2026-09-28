; tools/synth-log-store.lisp: the log a synthesized fixture store holds,
; written by ACL2.  tools/synth_log_store.py `ld's this file into a developer
; image's own session (`fn acl2 session', host/native/acl2-session.lisp) and
; calls `synth-log-store'; Python only lays out the directory and fsyncs.
;
; Every value the node itself decides comes from the books the image holds:
; the genesis frame and its trailer (books/store-genesis.lisp fn-gen-decode,
; fn-gen-trailer), the seed's entries and their chain (books/store-log.lisp
; fn-lg-scan), the article records (fn-record-decode-exact, fn-record-encode),
; the content identities (books/identity.lisp fn-id-subject-of-payload,
; fn-id-obligation-of, fn-id-text) and every new entry (fn-lg-frame, its
; trailer fn-lg-trailer, its padding fn-lg-pad-len).  What is this file's own
; is fixture policy: record i is template i mod |seed| renumbered to sequence
; i, txid and generation i + 1, under a fresh Message-ID of the template's
; length ("s<i>" left-padded with zeros), substituted once in the payload.
;
; A TEST FIXTURE writer: it decides nothing the node relies on.  The node's
; open verifies every frame, chain link and record of what this writes.

(in-package "ACL2")
(set-inhibit-output-lst '(summary event observation warning prove proof-tree))
(set-state-ok t)
(program)

(defconst *synth-unit* 4096)
(defconst *synth-record-bound* 4294967295)

; --- bytes in and out, through ACL2's own channels -------------------------

(defun synth-read-loop (channel acc state)
  (mv-let (byte state) (read-byte$ channel state)
    (if (null byte)
        (mv (reverse acc) state)
      (synth-read-loop channel (cons byte acc) state))))

(defun synth-read-file (path state)
  (mv-let (channel state) (open-input-channel path :byte state)
    (if (null channel)
        (mv nil state)
      (mv-let (octets state) (synth-read-loop channel nil state)
        (let ((state (close-input-channel channel state)))
          (mv octets state))))))

(defun synth-write-octets (octets channel state)
  (if (endp octets)
      state
    (let ((state (write-byte$ (car octets) channel state)))
      (synth-write-octets (cdr octets) channel state))))

(defun synth-write-zeros (n channel state)
  (if (zp n)
      state
    (let ((state (write-byte$ 0 channel state)))
      (synth-write-zeros (1- n) channel state))))

; --- the Message-ID substitution --------------------------------------------

(defun synth-prefixp (p x)
  (cond ((endp p) t)
        ((endp x) nil)
        ((eql (car p) (car x)) (synth-prefixp (cdr p) (cdr x)))
        (t nil)))

(defun synth-count (old x n)
  (cond ((endp x) n)
        ((synth-prefixp old x) (synth-count old (cdr x) (1+ n)))
        (t (synth-count old (cdr x) n))))

(defun synth-replace (old new x acc)
  (cond ((endp x) (reverse acc))
        ((synth-prefixp old x) (revappend acc (append new (nthcdr (len old) x))))
        (t (synth-replace old new (cdr x) (cons (car x) acc)))))

; "<" + ("s<i>" left-padded with #\0 to the template's local width) + "@host>"
(defun synth-msgid (template i)
  (let* ((chars (coerce template 'list))
         (at (position #\@ chars))
         (width (if at (- at 1) 0))
         (local (cons #\s (explode-nonnegative-integer i 10 nil))))
    (if (or (null at) (> (len local) width))
        nil
      (coerce (append (list #\<)
                      (make-list (- width (len local)) :initial-element #\0)
                      local
                      (nthcdr at chars))
              'string))))

; --- records ------------------------------------------------------------------

; (mv SUBJECT-TEXT OBLIGATION-TEXT) of a payload under a Message-ID, as the
; strings a record's metadata fields hold.
(defun synth-identities (msgid payload)
  (let* ((subject (fn-id-subject-of-payload payload))
         (obligation (fn-id-obligation-of (fn-record-string-octets msgid) subject)))
    (mv (fn-record-octets-string (fn-id-text subject))
        (fn-record-octets-string (fn-id-text obligation)))))

; RAW (one seed record, number K) as a template, or a refusal keyword.
(defun synth-template (raw k)
  (let ((result (fn-record-decode-exact raw)))
    (if (not (fn-record-result-okp result))
        :not-an-article-record
      (let ((record (fn-record-result-record result)))
        (cond ((not (equal (fn-record-encode record) raw)) :not-the-shortest-encoding)
              ((not (and (equal (fn-record-sequence record) k)
                         (equal (fn-record-txid record) (1+ k))
                         (equal (fn-record-generation record) (1+ k))))
               :not-the-renumbering)
              ((not (equal (synth-count (fn-record-string-octets (fn-record-msgid record))
                                        (fn-record-payload record) 0)
                           1))
               :payload-does-not-name-its-message-id-once)
              (t (mv-let (subject obligation)
                     (synth-identities (fn-record-msgid record) (fn-record-payload record))
                   (if (and (equal subject (fn-record-content-subject record))
                            (equal obligation (fn-record-obligation-id record)))
                       record
                     :identities-do-not-recompute))))))))

(defun synth-templates (raws k acc)
  (if (endp raws)
      (reverse acc)
    (let ((template (synth-template (car raws) k)))
      (if (keywordp template)
          (list template k)
        (synth-templates (cdr raws) (1+ k) (cons template acc))))))

(defun synth-record (template i)
  (let* ((msgid (synth-msgid (fn-record-msgid template) i))
         (payload (synth-replace (fn-record-string-octets (fn-record-msgid template))
                                 (fn-record-string-octets msgid)
                                 (fn-record-payload template) nil)))
    (mv-let (subject obligation) (synth-identities msgid payload)
      (fn-record-encode
       (fn-record-make i (1+ i) (1+ i) msgid payload
                       (fn-record-groups template) obligation subject
                       (fn-record-release-evidence template)
                       (fn-record-charge template)
                       (fn-record-stamp template))))))

(defun synth-chunk (i end templates k acc)
  (if (>= i end)
      (reverse acc)
    (synth-chunk (1+ i) end templates k
                 (cons (synth-record (nth (mod i k) templates) i) acc))))

; --- the log ------------------------------------------------------------------

(defun synth-emit (i n batch templates k prev written channel state)
  (if (>= i n)
      (mv written state)
    (let* ((end (min n (+ i batch)))
           (frame (fn-lg-frame prev (synth-chunk i end templates k nil)))
           (pad (fn-lg-pad-len (len frame) *synth-unit*))
           (state (synth-write-octets frame channel state))
           (state (synth-write-zeros pad channel state)))
      (synth-emit end n batch templates k (fn-lg-trailer frame)
                  (+ written (len frame) pad) channel state))))

; The seed's templates from its genesis (journal/000000.log) and segment
; (journal/000001.log): (:templates K TEMPLATES GENESIS-TRAILER) or (:refused ...).
(defun synth-seed (genesis-path segment-path state)
  (mv-let (genesis state) (synth-read-file genesis-path state)
    (if (null (fn-gen-decode genesis))
        (mv (list :refused :seed-genesis) state)
      (mv-let (segment state) (synth-read-file segment-path state)
        (let* ((trailer (fn-gen-trailer genesis))
               (scan (fn-lg-scan segment trailer *synth-unit* *synth-record-bound*))
               (raws (car scan))
               (templates (synth-templates raws 0 nil)))
          (cond ((endp raws) (mv (list :refused :seed-log-empty) state))
                ; The scan stops at the first entry that does not verify or
                ; chain; one that stops at another FNLG frame is damage.
                ((synth-prefixp *fn-lg-magic* (nthcdr (cdr scan) segment))
                 (mv (list :refused :seed-log-damaged :at (cdr scan)) state))
                ((keywordp (car templates))
                 (mv (list :refused (car templates) :seed-record (cadr templates)) state))
                (t (mv (list :templates (len templates) templates trailer) state))))))))

; Verify the seed; unless CHECK-ONLY, write N records in BATCH-record entries
; to OUT-PATH (which the caller made sure did not exist), then the
; preallocated zero tail (at least 4 MiB, rounded to MiB).  The value printed:
; (:checked K), (:wrote N OCTETS-OF-ENTRIES) or (:refused ...).
(defun synth-log-store (genesis-path segment-path out-path n batch check-only state)
  (mv-let (seed state) (synth-seed genesis-path segment-path state)
    (cond ((eq (car seed) :refused) (value seed))
          (check-only (value (list :checked (cadr seed))))
          (t (mv-let (channel state) (open-output-channel out-path :byte state)
               (if (null channel)
                   (value (list :refused :cannot-open-output))
                 (mv-let (written state)
                     (synth-emit 0 n (max 1 batch) (caddr seed) (cadr seed)
                                 (cadddr seed) 0 channel state)
                   (let* ((tail (- (max 4194304 (+ written *synth-unit*)) written))
                          (round (mod (- (+ written tail)) 1048576))
                          (state (synth-write-zeros (+ tail round) channel state))
                          (state (close-output-channel channel state)))
                     (value (list :wrote n written))))))))))
