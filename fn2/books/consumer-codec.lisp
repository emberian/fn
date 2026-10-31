; Layer E3b: the consumer port's frames as layouts (fn2/docs/e-surface.md
; sections 3.1, 4). Every octet form is a DEFLAYOUT row: the generated codec
; is the served path, and B's list codec (fn2-layout-octets, fn2-layout-parse)
; is the specification the fixtures are checked against.
;
; fn1's bytes are kept where a client speaks them: the FNCT frame, the fncu v1
; cursor, kind 4's request codes 0-10 with fn1's payloads, and the kind 5, 6
; and 9 replies (books/native-control.lisp, consumer-position.lisp,
; consumer-local-control.lisp, consumer-wait-codec.lisp). Codes 11-18 carry
; the port's own payloads and are answered in reply kind 28. Which verb each
; code is, and how L translates fn1's codes, is data (section 5) checked
; against the port's declaration.
(in-package "ACL2")
(include-book "layout")
(include-book "blake3-spec")
(include-book "consumer-port")
(fn2-book-layer :e)

;; ---------------------------------------------------------------------------
;; 1. The FNCT frame: "FNCT", version 1, kind, a four-octet length, the
;; payload, then BLAKE3-256 of everything before it. The trailer is not a
;; field; it is computed over the protected prefix and compared.
(defconst *fn2-fnct-magic* 1179534164)        ; "FNCT"
(defconst *fn2-fnct-version* 1)
(defconst *fn2-fnct-header-layout* '((magic :u32be) (version :u8) (kind :u8) (length :u32be)))
(deflayout fn2-fnct-header *fn2-fnct-header-layout*)

(defun fn2-fnct-seal (kind payload)
  (declare (xargs :verify-guards nil))
  (let ((prefix (append (fn2-layout-octets *fn2-fnct-header-layout*
                                           (list *fn2-fnct-magic* *fn2-fnct-version* kind (len payload)))
                        payload)))
    (append prefix (fn-blake3 prefix))))
; (:ok KIND PAYLOAD) or (:refused WORD): the frame is exactly its extent, its
; trailer is the digest of its prefix, and its payload is within MAX.
(defun fn2-fnct-open (octets max)
  (declare (xargs :verify-guards nil))
  (b* (((unless (and (true-listp octets) (<= 42 (len octets)))) '(:refused :frame))
       ((mv code vs rest) (fn2-layout-parse *fn2-fnct-header-layout* (take 10 octets)))
       ((unless (and (eq code :ok) (null rest)
                     (equal (car vs) *fn2-fnct-magic*) (equal (cadr vs) *fn2-fnct-version*)))
        '(:refused :frame))
       (n (cadddr vs))
       ((unless (<= n max)) '(:refused :size))
       ((unless (equal (len octets) (+ 42 n))) '(:refused :frame))
       (prefix (take (+ 10 n) octets))
       ((unless (equal (nthcdr (+ 10 n) octets) (fn-blake3 prefix))) '(:refused :frame)))
    (list :ok (caddr vs) (nthcdr 10 prefix))))

;; ---------------------------------------------------------------------------
;; 2. The cursor. v1 is fn1's (at most 346 octets); v2 names the position's
;; domain and widens the counters (at most 366). IDs are one to 64 octets;
;; below 128 a varint length is fn1's one length octet.
(defconst *fn2-fncu-magic* 1718510453)        ; "fncu"
(defconst *fn2-fncu-ids*
  '((history (:octets 64)) (incarnation (:octets 64)) (consumer (:octets 64))
    (principal (:octets 64)) (query (:octets 64))))
(defconst *fn2-fncu-v1-layout*
  (append '((magic :u32be) (version :u8)) *fn2-fncu-ids*
          '((query-version :u32be) (view-version :u32be) (epoch :u32be) (position :u32be))))
(defconst *fn2-fncu-v2-layout*
  (append '((magic :u32be) (version :u8)) *fn2-fncu-ids*
          '((domain :u32be) (query-version :u64be) (view-version :u64be) (epoch :u64be) (position :u64be))))
(deflayout fn2-fncu-v1 *fn2-fncu-v1-layout*)
(deflayout fn2-fncu-v2 *fn2-fncu-v2-layout*)
(assert-event (and (equal (fn2-layout-max-size *fn2-fncu-v1-layout*) 346)
                   (equal (fn2-layout-max-size *fn2-fncu-v2-layout*) 366)))

; A cursor: (:cursor DOMAIN HISTORY INCARNATION CONSUMER PRINCIPAL QUERY QVER
; VIEW EPOCH POSITION). Issued as v1 while every field fits it (domain 0, the
; counters below 2^32), otherwise as v2; never truncated (e-surface.md 3.1).
(defun fn2-fncu-wordp (n) (declare (xargs :guard t)) (and (natp n) (< n 4294967296)))
(defun fn2-fncu-v1-fits (c)
  (declare (xargs :verify-guards nil))
  (and (equal (nth 1 c) 0) (fn2-fncu-wordp (nth 7 c)) (fn2-fncu-wordp (nth 8 c))
       (fn2-fncu-wordp (nth 9 c)) (fn2-fncu-wordp (nth 10 c))))
(defun fn2-fncu-encode (c)
  (declare (xargs :verify-guards nil))
  (if (fn2-fncu-v1-fits c)
      (fn2-layout-octets *fn2-fncu-v1-layout* (list* *fn2-fncu-magic* 1 (nthcdr 2 c)))
    (fn2-layout-octets *fn2-fncu-v2-layout*
                       (list* *fn2-fncu-magic* 2 (append (take 5 (nthcdr 2 c)) (list (nth 1 c)) (nthcdr 7 c))))))
(defun fn2-fncu-ids-ok (ids)
  (declare (xargs :verify-guards nil))
  (if (atom ids) t (and (consp (car ids)) (fn2-fncu-ids-ok (cdr ids)))))
; (:ok CURSOR) or (:refused WORD) with fn1's words (octets, version,
; grammar). A v1 cursor whose fields would need v2 cannot exist; a v2 cursor
; whose fields fit v1 is refused (one form per cursor).
(defun fn2-fncu-decode (octets)
  (declare (xargs :verify-guards nil))
  (b* (((unless (and (true-listp octets) (<= (len octets) 512))) '(:refused :octets))
       ((unless (and (<= 5 (len octets)) (member (nth 4 octets) '(1 2)))) '(:refused :version))
       (v1 (equal (nth 4 octets) 1))
       ((mv code vs rest) (fn2-layout-parse (if v1 *fn2-fncu-v1-layout* *fn2-fncu-v2-layout*) octets))
       ((unless (and (eq code :ok) (null rest))) '(:refused :grammar))
       ((unless (equal (car vs) *fn2-fncu-magic*)) '(:refused :version))
       (ids (take 5 (cddr vs)))
       (tail (nthcdr 7 vs))
       (c (append (list :cursor (if v1 0 (car tail))) ids (if v1 tail (cdr tail))))
       ((unless (and (fn2-fncu-ids-ok ids) (posp (nth 9 c)))) '(:refused :grammar))
       ((unless (or v1 (not (fn2-fncu-v1-fits c)))) '(:refused :grammar)))
    (list :ok c)))

;; ---------------------------------------------------------------------------
;; 3. Kind 4 requests: one code octet, then the code's fields. A row is (CODE
;; WORD FIELDS CURSOR-TAIL): when CURSOR-TAIL, the octets after FIELDS are a
;; cursor (fn1's ack and bound-ack).
(defconst *fn2-fnct-request-kind* 4)
(defconst *fn2-fnct-reason-request-kind* 22)  ; fn1: the same payload, a reasoned reply
(defconst *fn2-fnct-max-wait-seconds* 3600)
(defconst *fn2-fnct-codes*
  '((0 :register ((consumer (:octets 64)) (group (:octets 64))) nil)
    (1 :ack () t)
    (2 :position ((consumer (:octets 64))) nil)
    (3 :unregister ((consumer (:octets 64))) nil)
    (4 :bootstrap () nil)
    (5 :poll ((consumer (:octets 64))) nil)
    (6 :status ((consumer (:octets 64))) nil)
    (7 :bound-poll ((consumer (:octets 64)) (secret (:octets16 496))) nil)
    (8 :bound-ack ((secret (:octets16 496))) t)
    (9 :wait ((consumer (:octets 64)) (seconds :u32be)) nil)
    (10 :bound-wait ((consumer (:octets 64)) (seconds :u32be) (secret (:octets16 496))) nil)
    ; The port's payloads. A cursor followed by other fields is length-prefixed;
    ; a query is the canonical concatenation of its stream names, each (:octets 64).
    (11 :append ((stream (:octets 64)) (op (:octets16 64)) (article (:octets32 2147483647))) nil)
    (12 :rebase ((cursor (:octets16 366)) (streams (:octets16 4160))
                 (start (:enum fn2-fnct-rebase-start (:keep :now :history)))) nil)
    (13 :fetch ((message-id (:octets16 250)) (domain :u32be) (position :u64be)) nil)
    (14 :register-query ((consumer (:octets 64)) (streams (:octets16 4160))
                         (start (:enum fn2-fnct-start (:now :history)))) nil)
    (15 :read ((cursor (:octets16 366)) (max-items :u32be) (max-octets :u32be)) nil)
    (16 :wait-cursor ((cursor (:octets16 366)) (max-items :u32be) (max-octets :u32be) (seconds :u32be)) nil)
    (17 :unregister-cursor ((cursor (:octets16 366))) nil)
    (18 :status-wide ((consumer (:octets 64))) nil)))
(defconst *fn2-fnct-bound-codes* '(7 8 10))
(defun fn2-fnct-codes-ok (rows seen)
  (declare (xargs :verify-guards nil))
  (if (atom rows) t
    (and (natp (caar rows)) (< (caar rows) 256) (not (member (caar rows) seen))
         (keywordp (cadar rows)) (fn2-layoutp (caddar rows)) (booleanp (cadddr (car rows)))
         (fn2-fnct-codes-ok (cdr rows) (cons (caar rows) seen)))))
(assert-event (fn2-fnct-codes-ok *fn2-fnct-codes* nil))
; Every code's whole payload is a served layout, named FN2-FNCT-K4-WORD.
(defun fn2-fnct-deflayout-forms (rows)
  (declare (xargs :verify-guards nil))
  (if (atom rows) nil
    (cons `(deflayout ,(intern-in-package-of-symbol
                        (concatenate 'string "FN2-FNCT-K4-" (symbol-name (cadar rows))) 'fn2-fnct-codes)
             '((code :u8) ,@(caddar rows)))
          (fn2-fnct-deflayout-forms (cdr rows)))))
(make-event (value `(progn ,@(fn2-fnct-deflayout-forms *fn2-fnct-codes*))))

; The payload ceiling: fn1's for its codes (513, or 1024 for the bound
; forms); a port code's is its layout's, below the policy bound the carrier
; applies first (max-consumer-request-octets, e-surface.md 8).
(defun fn2-fnct-max-payload (code)
  (declare (xargs :verify-guards nil))
  (cond ((member code *fn2-fnct-bound-codes*) 1024)
        ((or (<= (nfix code) 10) (not (assoc code *fn2-fnct-codes*))) 513)
        (t (+ 1 (fn2-layout-max-size (caddr (assoc code *fn2-fnct-codes*)))))))
; A refusal names the field that failed, in fn1's words; octets past the last
; field are that field's failure.
(defun fn2-fnct-field-word (name)
  (declare (xargs :guard t))
  (case name (consumer :consumer) (group :group) (secret :secret) (seconds :timeout)
    (cursor :cursor) (stream :stream) (otherwise :grammar)))
(defun fn2-fnct-nonempty-field (name)
  (declare (xargs :guard t))
  (member-eq name '(consumer group secret stream cursor message-id)))
(defun fn2-fnct-parse-fields (layout octets tail acc)
  ; (:ok ALIST REST) or (:refused WORD). An empty op means none was given.
  (declare (xargs :verify-guards nil :measure (len layout)
                  :hints (("Goal" :in-theory (disable fn2-layout-parse fn2-fncu-decode)))))
  (if (atom layout) (list :ok (reverse acc) octets)
    (b* ((name (caar layout))
         (word (fn2-fnct-field-word name))
         ((mv code vs rest) (fn2-layout-parse (list (car layout)) octets))
         ((unless (eq code :ok)) (list :refused word))
         (v (car vs))
         ((when (and (fn2-fnct-nonempty-field name) (atom v))) (list :refused word))
         ((when (and (eq name 'seconds) (> v *fn2-fnct-max-wait-seconds*))) (list :refused word))
         ((when (and (eq name 'cursor) (not (eq (car (fn2-fncu-decode v)) :ok)))) (list :refused word))
         ((when (and (atom (cdr layout)) (not tail) (consp rest))) (list :refused word)))
      (fn2-fnct-parse-fields (cdr layout) rest tail (cons (cons name v) acc)))))
; (:request WORD ALIST) or (:refused WORD), over an opened payload.
(defun fn2-fnct-request-decode (payload)
  (declare (xargs :verify-guards nil))
  (b* (((unless (and (consp payload) (true-listp payload))) '(:refused :size))
       (code (car payload))
       ((unless (<= (len payload) (fn2-fnct-max-payload code))) '(:refused :size))
       (row (assoc code *fn2-fnct-codes*))
       ((unless row) '(:refused :kind))
       ((list & word layout tail) row)
       ((when (and (eq word :bootstrap) (consp (cdr payload)))) '(:refused :bootstrap))
       (r (fn2-fnct-parse-fields layout (cdr payload) tail nil))
       ((unless (eq (car r) :ok)) r)
       ((unless tail) (list :request word (cadr r)))
       (c (fn2-fncu-decode (caddr r)))
       ((unless (eq (car c) :ok)) '(:refused :cursor)))
    (list :request word (append (cadr r) (list (cons 'cursor (caddr r)))))))
(defun fn2-fnct-word-row (word rows)
  (declare (xargs :verify-guards nil))
  (cond ((atom rows) nil) ((eq (cadar rows) word) (car rows)) (t (fn2-fnct-word-row word (cdr rows)))))
(defun fn2-fnct-alist-values (layout alist)
  (declare (xargs :verify-guards nil))
  (if (atom layout) nil
    (cons (cdr (assoc-eq (caar layout) alist)) (fn2-fnct-alist-values (cdr layout) alist))))
(defun fn2-fnct-request-encode (word alist)
  ; The payload for WORD from its fields, or nil when the row has none.
  (declare (xargs :verify-guards nil))
  (b* ((row (fn2-fnct-word-row word *fn2-fnct-codes*))
       ((unless row) nil)
       ((list code & layout tail) row))
    (append (list code)
            (fn2-layout-octets layout (fn2-fnct-alist-values layout alist))
            (and tail (cdr (assoc-eq 'cursor alist))))))

;; ---------------------------------------------------------------------------
;; 4. Replies. fn1's: kind 5 (status, then the cursor when accepted), kind 6
;; (status, four-octet-prefixed cursor and report), kind 9 (status, then on
;; acceptance the committed ack, the frontier and their difference). Status
;; octets: 0 accepted, 1 refused, 2 uncertain, 3 fault. The port's: kind 28,
;; the class, the reason word and the verb's result octets.
(defconst *fn2-fnct-reply-kind* 5)
(defconst *fn2-fnct-poll-reply-kind* 6)
(defconst *fn2-fnct-status-reply-kind* 9)
(defconst *fn2-fnct-port-reply-kind* 28)
(defconst *fn2-fnct-statuses* '(:accepted :refused :uncertain :fault))
(defconst *fn2-fnct-poll-reply-layout*
  '((status (:enum fn2-fnct-status (:accepted :refused :uncertain :fault)))
    (cursor (:octets32 346)) (report (:octets32 4294966940))))
(defconst *fn2-fnct-status-reply-layout*
  '((status (:enum fn2-fnct-status (:accepted :refused :uncertain :fault)))
    (ack :u32be) (frontier :u32be) (gap :u32be)))
(deflayout fn2-fnct-k6-reply *fn2-fnct-poll-reply-layout*)
(deflayout fn2-fnct-k9-reply *fn2-fnct-status-reply-layout*)

(defun fn2-fnct-status-octet (status)
  (declare (xargs :guard t))
  (case status (:accepted 0) (:refused 1) (:uncertain 2) (:fault 3) (otherwise nil)))
(defun fn2-fnct-reply (status cursor)
  ; Kind 5: the status, and the cursor octets only on acceptance.
  (declare (xargs :verify-guards nil))
  (cons (fn2-fnct-status-octet status) (and (eq status :accepted) cursor)))
(defun fn2-fnct-poll-reply (status cursor report)
  (declare (xargs :verify-guards nil))
  (fn2-layout-octets *fn2-fnct-poll-reply-layout*
                     (list (- (fn2-fnct-status-octet status) 0) cursor report)))
(defun fn2-fnct-status-reply (status ack frontier)
  ; Accepted carries exactly three words with GAP = FRONTIER - ACK; a refusal none.
  (declare (xargs :verify-guards nil))
  (if (eq status :accepted)
      (fn2-layout-octets *fn2-fnct-status-reply-layout* (list 0 ack frontier (- frontier ack)))
    (list (fn2-fnct-status-octet status))))

; The port's reply: CLASS, the reason word (empty on acceptance), the result.
(defconst *fn2-fnct-port-reply-layout*
  '((class (:enum fn2-fnct-class (:accepted :refused :uncertain :fault)))
    (reason (:octets16 64)) (result (:octets32 4294967295))))
(deflayout fn2-fnct-k28-reply *fn2-fnct-port-reply-layout*)
; Each verb's result octets (inside RESULT). A cursor result is the cursor's
; own octets (v1 or v2); a page's items follow its count.
(defconst *fn2-fnct-reasons-bits* '((room . 1) (dm . 2) (mention . 4) (group-address . 8) (backfill . 16)))
(defconst *fn2-fnct-results*
  '((register :cursor) (rebase :cursor) (position :cursor) (unregister ())
    (ack ((domain :u32be) (position :u64be)))
    (status ((domain :u32be) (position :u64be) (frontier :u64be) (gap :u64be)))
    (read ((more :bool) (next (:octets16 366)) (count :u32be) (items (:octets32 4294967200))))
    (wait ((more :bool) (next (:octets16 366)) (count :u32be) (items (:octets32 4294967200))))
    (fetch ((article (:octets32 2147483647))))
    (append ((message-id (:octets16 250)) (domain :u32be) (position :u64be) (numbers (:octets16 4160))
             (receipt (:octets16 1024)) (evidence (:enum fn2-fnct-evidence (:none :committed :uncertain :refused)))))))
; One item of a page (e-surface.md 4.1): its type, position, the reasons bit
; set, the streams it was selected through, its Message-ID and its body (the
; record's octets; a reference's octet count and content identity; empty for
; a withdrawal or a gap).
(defconst *fn2-fnct-item-layout*
  '((type (:enum fn2-fnct-item (:record :withdrawn :reference :gap)))
    (domain :u32be) (position :u64be) (reasons :u8) (streams (:octets16 4160))
    (message-id (:octets16 250)) (body (:octets32 2147483647))))
(defconst *fn2-fnct-reference-layout* '((octets :u64be) (content :digest)))
(deflayout fn2-fnct-item *fn2-fnct-item-layout*)
(deflayout fn2-fnct-reference *fn2-fnct-reference-layout*)
(deflayout fn2-fnct-result-ack (cadr (assoc-eq 'ack *fn2-fnct-results*)))
(deflayout fn2-fnct-result-status (cadr (assoc-eq 'status *fn2-fnct-results*)))
(deflayout fn2-fnct-result-page (cadr (assoc-eq 'read *fn2-fnct-results*)))
(deflayout fn2-fnct-result-append (cadr (assoc-eq 'append *fn2-fnct-results*)))

;; ---------------------------------------------------------------------------
;; 5. What each code is. A port code names its verb; fn1's codes name the verb
;; L translates them to: fn1's poll and wait read from POSITION's cursor with
;; fn1's one-article limits, its unregister drops POSITION's cursor, its
;; register's two IDs are (consumer, group) from history, bootstrap is an
;; accepted no-op once init has minted the store's identities, and the bound
;; forms run as the configured account (the secret checked by AUTHINFO's
;; verifier) and are never carried by R.
(defconst *fn2-fnct-code-verbs*
  '((:register register :legacy (:query (group) :start :history))
    (:ack ack :legacy ())
    (:position position :legacy ())
    (:unregister unregister :legacy (:cursor-of consumer))
    (:bootstrap nil :legacy (:answer :accepted-noop))
    (:poll read :legacy (:cursor-of consumer :limits :one-article))
    (:status status :legacy (:reply :k9))
    (:bound-poll read :legacy (:cursor-of consumer :limits :one-article :bound secret))
    (:bound-ack ack :legacy (:bound secret))
    (:wait wait :legacy (:cursor-of consumer :limits :one-article :timeout seconds))
    (:bound-wait wait :legacy (:cursor-of consumer :limits :one-article :timeout seconds :bound secret))
    (:append append :port ())
    (:rebase rebase :port ())
    (:fetch fetch :port ())
    (:register-query register :port ())
    (:read read :port ())
    (:wait-cursor wait :port ())
    (:unregister-cursor unregister :port ())
    (:status-wide status :port ())))
(defun fn2-fnct-code-verbs-ok (rows)
  (declare (xargs :verify-guards nil))
  (if (atom rows) t
    (b* (((list word verb mode &) (car rows))
         (row (fn2-fnct-word-row word *fn2-fnct-codes*)))
      (and row (or (null verb) (fn2-consumer-verb-p verb))
           (eq mode (if (<= (car row) 10) :legacy :port))
           (fn2-fnct-code-verbs-ok (cdr rows))))))
(assert-event (and (fn2-fnct-code-verbs-ok *fn2-fnct-code-verbs*)
                   (equal (len *fn2-fnct-code-verbs*) (len *fn2-fnct-codes*))))
; The port codes are the carriers' bindings: every verb the port declares has
; one, and R and L bind exactly it (consumer-port.lisp).
(defun fn2-fnct-port-code (verb rows)
  (declare (xargs :verify-guards nil))
  (cond ((atom rows) nil)
        ((and (eq (cadar rows) verb)
              (or (eq (caddar rows) :port) (member-eq verb '(ack position))))
         (car (fn2-fnct-word-row (caar rows) *fn2-fnct-codes*)))
        (t (fn2-fnct-port-code verb (cdr rows)))))
(defun fn2-fnct-bindings-agree (verbs)
  (declare (xargs :verify-guards nil))
  (if (atom verbs) t
    (let ((code (fn2-fnct-port-code (car verbs) *fn2-fnct-code-verbs*)))
      (and code
           (equal (fn2-consumer-local-binding (car verbs)) (list 4 code))
           (equal (fn2-consumer-remote-binding (car verbs)) (list 4 code))
           (fn2-fnct-bindings-agree (cdr verbs))))))
(assert-event (fn2-fnct-bindings-agree *fn2-consumer-verbs*))
