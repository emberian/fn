; CONSUMER (ROUND2 section F.1; layer E; e-surface.md sections 9, 14): the
; served consumer port refines the reference model through crashes. An
; independent checker over what the simulator saw: the FNCT frames each L
; connection carried, the scenario's own world steps, the published frontier,
; and the ledger's rows read at every boundary (the consumer-cursor fold and
; the :wait-row holding), as ACCOUNT reads them. Its oracle is
; consumer-model.lisp; the frames are read with consumer-codec.lisp's list
; specification, never the served codec.
;
; The observation stream, in the order the simulator saw it:
;   (:connect CONN PRINCIPAL)  the L carrier admitted CONN for PRINCIPAL (its id octets)
;   (:request CONN OCTETS)     one whole request frame the server received on CONN
;   (:reply CONN OCTETS)       one whole reply frame the client received on CONN
;   (:close CONN)              CONN ended; a request without its reply is uncertain
;   (:world OP)                a model world step: (:grant P SCOPE STREAM), (:revoke ...),
;                              (:limit P N), (:reclaim POS), (:crash);
;                              (:post P STREAM (MID OCTETS TO) POS) and
;                              (:withdraw P MID POS), each when published at POS
;   (:publish F)               the published frontier is F
;   (:ledger CURSORS WAITS)    CURSORS ((P C EPOCH POSITION) ...), the consumer-cursor
;                              fold; WAITS ((P HELD) ...), the :wait-row holdings
;   (:settled WAITS)           nothing runnable and the network drained
;
; Model values are the wire's: principals, consumers, history and incarnation
; are their id octets; a group is its name as a string; the principal's own
; addr stream is the one-octet name "@" (no RFC 5536 group name holds "@").
; Positions are the store's commit positions: (:publish F) pads the model's
; log with commits nothing selects (consumer-model's :commit step).
;
; The checker keeps every model state the observations allow (a candidate)
; with each connection's pending request in it:
;   (:mut VERB FORM OP)          a mutation not yet linearized: it may take effect
;                                at any boundary until its reply, after a lost reply
;                                or a crash as an orphan, until the next settle
;   (:done VERB FORM ANSWER)     linearized, its answer fixed
;   (:read VERB FORM OP ALLOWED) read, wait, position, status, fetch: it answers what
;                                the model answers at some boundary while pending
;                                (a wait parked and woken late answers the read at the
;                                moment it answers, K4)
; A reply prunes the candidates whose answer differs; a reading prunes those
; whose rows differ; a settle prunes those holding a parked wait whose read is
; due (K4b, no lost wake) and requires every wait-row held to be a pending
; wait. No candidate left is a failure naming the observation.
;
; Declared limits, each a failure, never a pass: one request in flight per
; connection (:pipelined); fn1's legacy codes other than 1 (ack) and 2
; (position), kind 22, and kinds 6 and 9 (:unchecked-legacy); more than
; *fn2-cnsk-max-candidates* candidates. A page item's reference body is
; compared by its octet count; its content identity is checked when fetch
; serves (D6 2/n). A withdrawal report and a withdrawn article share FNWD's
; item type on the wire and are compared as that type.
;
; INTERIMS names the verbs the served node answers `unavailable` until their
; source lands (e-surface.md 14, E.P1), and register-groups when a register
; for anything but the principal's own addr stream is one of them.
(in-package "ACL2")
(include-book "../books/consumer-codec")
(include-book "../books/consumer-model")
(include-book "std/util/bstar" :dir :system)

(defconst *fn2-cnsk-max-candidates* 512)
(defconst *fn2-cnsk-frame-max* 2147484672)
(defconst *fn2-cnsk-durable-verbs* '(register rebase unregister ack append))
(defconst *fn2-cnsk-item-types* '(:record :withdrawn :reference :gap))
(defconst *fn2-cnsk-classes* '(:accepted :refused :uncertain :fault))

;; Octets and names ------------------------------------------------------------
(defun fn2-cnsk-codes (cs)
  (declare (xargs :verify-guards nil))
  (if (atom cs) nil (cons (char-code (car cs)) (fn2-cnsk-codes (cdr cs)))))
(defun fn2-cnsk-octets (s) (declare (xargs :verify-guards nil)) (and (stringp s) (fn2-cnsk-codes (coerce s 'list))))
(defun fn2-cnsk-chars (os)
  (declare (xargs :verify-guards nil))
  (if (atom os) nil (cons (code-char (nfix (car os))) (fn2-cnsk-chars (cdr os)))))
(defun fn2-cnsk-string (os) (declare (xargs :verify-guards nil)) (coerce (fn2-cnsk-chars os) 'string))
(defun fn2-cnsk-word (w)
  (declare (xargs :verify-guards nil))
  (and (symbolp w) w (fn2-cnsk-octets (string-downcase (symbol-name w)))))
(defun fn2-cnsk-index (x l n)
  (declare (xargs :verify-guards nil))
  (cond ((atom l) nil) ((equal x (car l)) n) (t (fn2-cnsk-index x (cdr l) (+ 1 n)))))

; A stream as a wire name, and back for principal P.
(defun fn2-cnsk-stream-name (s)
  (declare (xargs :verify-guards nil))
  (if (and (consp s) (eq (car s) :addr)) '(64) (fn2-cnsk-octets s)))
(defun fn2-cnsk-name-stream (n p)
  (declare (xargs :verify-guards nil))
  (if (equal n '(64)) (list :addr p) (fn2-cnsk-string n)))
(defun fn2-cnsk-names-octets (streams)
  (declare (xargs :verify-guards nil))
  (if (atom streams) nil
    (append (fn2-layout-octets '((name (:octets 64))) (list (fn2-cnsk-stream-name (car streams))))
            (fn2-cnsk-names-octets (cdr streams)))))
(defun fn2-cnsk-names (octets)
  ; (:ok NAMES) or nil: the canonical concatenation of names, each (:octets 64).
  (declare (xargs :verify-guards nil :measure (len octets)))
  (if (atom octets) (list :ok nil)
    (mv-let (code vs rest) (fn2-layout-parse '((name (:octets 64))) octets)
      (if (not (and (eq code :ok) (< (len rest) (len octets)))) nil
        (let ((r (fn2-cnsk-names rest))) (and r (list :ok (cons (car vs) (cadr r)))))))))
(defun fn2-cnsk-streams (names p)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil (cons (fn2-cnsk-name-stream (car names) p) (fn2-cnsk-streams (cdr names) p))))
(defun fn2-cnsk-stream-names (streams)
  (declare (xargs :verify-guards nil))
  (if (atom streams) nil (cons (fn2-cnsk-stream-name (car streams)) (fn2-cnsk-stream-names (cdr streams)))))

;; Answers ------------------------------------------------------------------------
; An answer is (CLASS WORD RESULT): CLASS a keyword, WORD the reason's octets
; (nil on acceptance, and in fn1's kind 5, which carries none), RESULT the
; verb's decoded values. A cursor is (:cursor DOMAIN HISTORY INCARNATION
; CONSUMER PRINCIPAL QUERY QVER VIEW EPOCH POSITION), the model's nine fields
; behind domain 0. A page is (MORE NEXT COUNT ITEMS), an item (TYPE DOMAIN
; POSITION REASONS STREAMS MESSAGE-ID BODY) with TYPE and MORE as the wire's
; numbers, a reference's BODY its octet count.
(defun fn2-cnsk-cursor (k) (declare (xargs :verify-guards nil)) (list* :cursor 0 k))
(defun fn2-cnsk-model-cursor (c)
  ; The model's cursor from a decoded one, or nil off domain 0.
  (declare (xargs :verify-guards nil))
  (and (consp c) (eq (car c) :cursor) (equal (nth 1 c) 0) (nthcdr 2 c)))
(defun fn2-cnsk-reason-bits (reasons)
  (declare (xargs :verify-guards nil))
  (if (atom reasons) 0
    (+ (case (car reasons) (:room 1) (:dm 2) (:mention 4) (:group-address 8) (:backfill 16) (otherwise 0))
       (fn2-cnsk-reason-bits (cdr reasons)))))
(defun fn2-cnsk-item (i)
  (declare (xargs :verify-guards nil))
  (let ((type (fn2-cns-item-type i)) (payload (fn2-cns-item-payload i)))
    (list (case type (:record 0) (:ref 2) (:gap 3) (otherwise 1))
          0 (fn2-cns-item-pos i) (fn2-cnsk-reason-bits (nth 4 i))
          (fn2-cnsk-stream-names (nth 5 i)) (fn2-cnsk-octets (fn2-cns-item-mid i))
          (case type (:record (fn2-cnsk-octets payload)) (:ref (nfix payload)) (otherwise nil)))))
(defun fn2-cnsk-items (items)
  (declare (xargs :verify-guards nil))
  (if (atom items) nil (cons (fn2-cnsk-item (car items)) (fn2-cnsk-items (cdr items)))))

; The answer the model's outcome O to OP is, in reply FORM (:k28, or :k5 for
; fn1's codes 1 and 2), over the state ST the verb left.
(defun fn2-cnsk-render (verb form o op st)
  (declare (xargs :verify-guards nil))
  (let ((v (and (consp o) (cadr o))))
    (case (fn2-cns-class o)
      (:refused (list :refused (and (eq form :k28) (fn2-cnsk-word (cadr o))) nil))
      (:uncertain (list :uncertain nil nil))
      (:accepted
       (list :accepted nil
             (case verb
               ((register rebase position) (fn2-cnsk-cursor (car v)))
               (ack (if (eq form :k5)
                        (let* ((k (nth 2 op)) (p (nth 1 op)) (c (fn2-cns-cursor-consumer k)))
                          (fn2-cnsk-cursor (fn2-cns-cursor st p c (fn2-cns-reg st p c) (car v))))
                      (list 0 (car v))))
               (status (list 0 (nth 0 v) (nth 1 v) (car (nth 2 v))))
               ((read wait) (list (if (nth 1 v) 1 0) (fn2-cnsk-cursor (nth 2 v)) (len (nth 0 v))
                                  (fn2-cnsk-items (nth 0 v))))
               (fetch (list (fn2-cnsk-octets (car v))))
               (otherwise v))))
      (otherwise (list :fault nil nil)))))

;; Decoding replies -------------------------------------------------------------
(defun fn2-cnsk-parse (layout octets)
  ; (:ok VALUES) when LAYOUT consumes OCTETS exactly, else nil.
  (declare (xargs :verify-guards nil))
  (mv-let (code vs rest) (fn2-layout-parse layout octets)
    (and (eq code :ok) (null rest) (list :ok vs))))
(defun fn2-cnsk-decode-cursor (octets)
  (declare (xargs :verify-guards nil))
  (let ((r (fn2-fncu-decode octets))) (if (eq (car r) :ok) (cadr r) (list :bad-cursor octets))))
(defun fn2-cnsk-decode-items (octets n)
  ; (:ok ITEMS) for exactly N items filling OCTETS, else nil.
  (declare (xargs :verify-guards nil :measure (nfix n) :hints (("Goal" :in-theory (disable fn2-layout-parse fn2-fncu-decode fn2-fnct-open fn2-fnct-request-decode fn2-cns-verb-step fn2-cns-append fn2-cns-withdraw fn2-cnsk-names fn2-cnsk-parse)))))
  (if (zp n) (and (atom octets) (list :ok nil))
    (mv-let (code vs rest) (fn2-layout-parse *fn2-fnct-item-layout* octets)
      (b* (((unless (eq code :ok)) nil)
           (names (fn2-cnsk-names (nth 4 vs)))
           ((unless names) nil)
           (body (if (equal (nth 0 vs) 2)
                     (let ((r (fn2-cnsk-parse *fn2-fnct-reference-layout* (nth 6 vs)))) (and r (car (cadr r))))
                   (nth 6 vs)))
           (more (fn2-cnsk-decode-items rest (- n 1))))
        (and more (list :ok (cons (list (nth 0 vs) (nth 1 vs) (nth 2 vs) (nth 3 vs) (cadr names) (nth 5 vs) body)
                                  (cadr more))))))))
(defun fn2-cnsk-decode-result (verb octets)
  (declare (xargs :verify-guards nil))
  (case verb
    ((register rebase position) (fn2-cnsk-decode-cursor octets))
    (unregister (if (atom octets) nil (list :bad-result octets)))
    ((ack status fetch append)
     (let ((r (fn2-cnsk-parse (cadr (assoc-eq verb *fn2-fnct-results*)) octets)))
       (if r (cadr r) (list :bad-result octets))))
    ((read wait)
     (b* ((r (fn2-cnsk-parse (cadr (assoc-eq 'read *fn2-fnct-results*)) octets))
          ((unless r) (list :bad-result octets))
          ((list more next count items) (cadr r))
          (decoded (fn2-cnsk-decode-items items count)))
       (if decoded (list (if (equal more 0) 0 1) (fn2-cnsk-decode-cursor next) count (cadr decoded))
         (list :bad-items items))))
    (otherwise (list :bad-result octets))))
(defun fn2-cnsk-decode-reply (verb form octets)
  ; The answer a reply frame carries, or (:malformed WHY).
  (declare (xargs :verify-guards nil))
  (b* ((f (fn2-fnct-open octets *fn2-cnsk-frame-max*))
       ((unless (eq (car f) :ok)) (list :malformed (cadr f)))
       ((list & kind payload) f))
    (case form
      (:k5 (cond ((not (equal kind *fn2-fnct-reply-kind*)) (list :malformed :kind kind))
                 ((equal payload '(0)) (list :malformed :empty-acceptance))
                 ((and (consp payload) (equal (car payload) 0))
                  (list :accepted nil (fn2-cnsk-decode-cursor (cdr payload))))
                 ((and (consp payload) (null (cdr payload)) (member (car payload) '(1 2 3)))
                  (list (nth (car payload) *fn2-fnct-statuses*) nil nil))
                 (t (list :malformed :k5 payload))))
      (otherwise
       (b* (((unless (equal kind *fn2-fnct-port-reply-kind*)) (list :malformed :kind kind))
            (r (fn2-cnsk-parse *fn2-fnct-port-reply-layout* payload))
            ((unless r) (list :malformed :k28 payload))
            ((list class word result) (cadr r))
            (class (nth class *fn2-cnsk-classes*)))
         (if (eq class :accepted)
             (list :accepted (and (consp word) word) (fn2-cnsk-decode-result verb result))
           (list class word (and (consp result) (list :bad-result result)))))))))

;; Encoding replies (the oracle node's and the controls'; the inverse of the above)
(defun fn2-cnsk-encode-cursor (c) (declare (xargs :verify-guards nil)) (fn2-fncu-encode c))
(defun fn2-cnsk-encode-items (items)
  (declare (xargs :verify-guards nil))
  (if (atom items) nil
    (let ((i (car items)))
      (append (fn2-layout-octets *fn2-fnct-item-layout*
                                 (list (nth 0 i) (nth 1 i) (nth 2 i) (nth 3 i)
                                       (fn2-cnsk-names-octets (fn2-cnsk-streams (nth 4 i) nil))
                                       (nth 5 i)
                                       (if (equal (nth 0 i) 2)
                                           (fn2-layout-octets *fn2-fnct-reference-layout*
                                                              (list (nth 6 i) (cons 1 (make-list 32 :initial-element 0))))
                                         (nth 6 i))))
              (fn2-cnsk-encode-items (cdr items))))))
(defun fn2-cnsk-encode-result (verb result)
  (declare (xargs :verify-guards nil))
  (case verb
    ((register rebase position) (fn2-cnsk-encode-cursor result))
    (unregister nil)
    ((ack status fetch append) (fn2-layout-octets (cadr (assoc-eq verb *fn2-fnct-results*)) result))
    ((read wait) (fn2-layout-octets (cadr (assoc-eq 'read *fn2-fnct-results*))
                                    (list (nth 0 result) (fn2-cnsk-encode-cursor (nth 1 result)) (nth 2 result)
                                          (fn2-cnsk-encode-items (nth 3 result)))))
    (otherwise nil)))
(defun fn2-cnsk-encode-reply (verb form answer)
  (declare (xargs :verify-guards nil))
  (let ((class (nth 0 answer)))
    (if (eq form :k5)
        (fn2-fnct-seal *fn2-fnct-reply-kind*
                       (cons (fn2-fnct-status-octet class)
                             (and (eq class :accepted) (fn2-cnsk-encode-cursor (nth 2 answer)))))
      (fn2-fnct-seal *fn2-fnct-port-reply-kind*
                     (fn2-layout-octets *fn2-fnct-port-reply-layout*
                                        (list (fn2-cnsk-index class *fn2-cnsk-classes* 0) (nth 1 answer)
                                              (and (eq class :accepted) (fn2-cnsk-encode-result verb (nth 2 answer)))))))))
; The names in a decoded item are the wire's; the encoder takes them back
; through FN2-CNSK-STREAMS, so a name round-trips whatever P is.

;; Decoding requests ------------------------------------------------------------
(defun fn2-cnsk-field (name alist) (declare (xargs :verify-guards nil)) (cdr (assoc-eq name alist)))
(defun fn2-cnsk-k (alist)
  (declare (xargs :verify-guards nil))
  (let ((c (fn2-fncu-decode (fn2-cnsk-field 'cursor alist))))
    (and (eq (car c) :ok) (fn2-cnsk-model-cursor (cadr c)))))
(defun fn2-cnsk-request-streams (alist p)
  (declare (xargs :verify-guards nil))
  (let ((n (fn2-cnsk-names (fn2-cnsk-field 'streams alist)))) (and n (fn2-cnsk-streams (cadr n) p))))
; What a request frame from principal P is: (:op VERB FORM OP), (:answer
; VERB FORM ANSWER) for an answer fixed at decode, (:close) when the carrier
; must drop the connection without a reply, or (:unchecked WHAT).
(defun fn2-cnsk-request (octets p interims)
  (declare (xargs :verify-guards nil))
  (b* ((f (fn2-fnct-open octets *fn2-cnsk-frame-max*))
       ((unless (eq (car f) :ok)) '(:close))
       ((list & kind payload) f)
       ((unless (equal kind *fn2-fnct-request-kind*)) (list :unchecked :kind kind))
       (code (and (consp payload) (car payload)))
       (r (fn2-fnct-request-decode payload))
       ((unless (eq (car r) :request))
        (if (and (natp code) (<= code 10) (not (member code '(1 2)))) (list :unchecked :legacy code)
          (list :answer 'read (if (member code '(1 2)) :k5 :k28)
                (list :refused (if (member code '(1 2)) nil (fn2-cnsk-word (cadr r))) nil))))
       ((list & word alist) r)
       (row (assoc-eq word *fn2-fnct-code-verbs*))
       (verb (cadr row))
       (form (if (member code '(1 2)) :k5 :k28))
       ((unless (or (>= code 11) (member code '(1 2)))) (list :unchecked :legacy code))
       ((when (member-eq verb interims)) (list :answer verb form (list :refused (fn2-cnsk-word 'unavailable) nil)))
       (k (fn2-cnsk-k alist))
       (limits (list (fn2-cnsk-field 'max-items alist) (fn2-cnsk-field 'max-octets alist)))
       (consumer (fn2-cnsk-field 'consumer alist))
       (streams (fn2-cnsk-request-streams alist p))
       ((when (and (eq verb 'register) (member-eq 'register-groups interims)
                   (not (equal streams (list (list :addr p))))))
        (list :answer verb form (list :refused (fn2-cnsk-word 'unavailable) nil))))
    (case verb
      (register (list :op verb form (list 'register p consumer streams
                                          (nth (fn2-cnsk-field 'start alist) '(:now :history)))))
      (rebase (list :op verb form (list 'rebase p k streams (nth (fn2-cnsk-field 'start alist) '(:keep :now :history)))))
      (unregister (list :op verb form (list 'unregister p k)))
      (ack (list :op verb form (list 'ack p k)))
      ((read wait) (list :op verb form (list 'read p k limits)))
      (position (list :op verb form (list 'position p consumer)))
      (status (list :op verb form (list 'status p consumer)))
      (fetch (list :op verb form (list 'fetch p (list (fn2-cnsk-string (fn2-cnsk-field 'message-id alist))))))
      (otherwise (list :unchecked :verb verb)))))

;; Candidates ------------------------------------------------------------------
; A candidate is (STATE PENDING ORPHANS): PENDING ((CONN . ENTRY) ...), ORPHANS
; the mutations whose replies will never come.
(defun fn2-cnsk-answer-of (verb form op st)
  ; The model's answer to a non-mutating OP now (a wait's is its read's).
  (declare (xargs :verify-guards nil))
  (mv-let (o st2) (fn2-cns-verb-step op st nil) (fn2-cnsk-render verb form o op st2)))
(defun fn2-cnsk-refresh-entries (pending st)
  (declare (xargs :verify-guards nil))
  (if (atom pending) nil
    (let* ((key (caar pending)) (e (cdar pending))
           (e (if (and (eq (car e) :read) (nth 3 e))
                  (let ((a (fn2-cnsk-answer-of (nth 1 e) (nth 2 e) (nth 3 e) st)))
                    (if (member-equal a (nth 4 e)) e (list :read (nth 1 e) (nth 2 e) (nth 3 e) (cons a (nth 4 e)))))
                e)))
      (cons (cons key e) (fn2-cnsk-refresh-entries (cdr pending) st)))))
(defun fn2-cnsk-refresh (cand)
  (declare (xargs :verify-guards nil))
  (list (nth 0 cand) (fn2-cnsk-refresh-entries (nth 1 cand) (nth 0 cand)) (nth 2 cand)))
(defun fn2-cnsk-apply-entry (key cand)
  ; CAND with the pending mutation at KEY linearized now.
  (declare (xargs :verify-guards nil))
  (b* ((st (nth 0 cand)) (e (cdr (assoc-equal key (nth 1 cand))))
       ((list & verb form op) e)
       ((mv o st2) (fn2-cns-verb-step op st nil)))
    (fn2-cnsk-refresh (list st2 (put-assoc-equal key (list :done verb form (fn2-cnsk-render verb form o op st2)) (nth 1 cand))
                            (nth 2 cand)))))
(defun fn2-cnsk-apply-orphan (n cand)
  (declare (xargs :verify-guards nil))
  (b* ((st (nth 0 cand)) (orphans (nth 2 cand)) (op (nth n orphans))
       ((mv & st2) (fn2-cns-verb-step op st nil)))
    (fn2-cnsk-refresh (list st2 (nth 1 cand) (append (take n orphans) (nthcdr (+ 1 n) orphans))))))
(defun fn2-cnsk-mut-steps (pending cand)
  (declare (xargs :verify-guards nil))
  (cond ((atom pending) nil)
        ((eq (car (cdar pending)) :mut) (cons (fn2-cnsk-apply-entry (caar pending) cand) (fn2-cnsk-mut-steps (cdr pending) cand)))
        (t (fn2-cnsk-mut-steps (cdr pending) cand))))
(defun fn2-cnsk-orphan-steps (n cand)
  (declare (xargs :verify-guards nil :measure (nfix (- (len (nth 2 cand)) (nfix n)))))
  (if (or (not (natp n)) (>= n (len (nth 2 cand)))) nil
    (cons (fn2-cnsk-apply-orphan n cand) (fn2-cnsk-orphan-steps (+ 1 n) cand))))
(defun fn2-cnsk-steps (cands)
  (declare (xargs :verify-guards nil))
  (if (atom cands) nil
    (append (fn2-cnsk-mut-steps (nth 1 (car cands)) (car cands)) (fn2-cnsk-orphan-steps 0 (car cands))
            (fn2-cnsk-steps (cdr cands)))))
; Every way the pending mutations may have linearized by now: the closure
; under one more step, each step removing one mutation, so it ends.
(defun fn2-cnsk-close (cands fuel)
  (declare (xargs :verify-guards nil :measure (nfix fuel)
                  :hints (("Goal" :in-theory (disable fn2-cnsk-steps remove-duplicates-equal binary-append len)))))
  (if (or (zp fuel) (< *fn2-cnsk-max-candidates* (len cands))) cands
    (let ((next (remove-duplicates-equal (append cands (fn2-cnsk-steps cands)))))
      (if (equal (len next) (len cands)) cands (fn2-cnsk-close next (- fuel 1))))))
(defun fn2-cnsk-map-refresh (cands)
  (declare (xargs :verify-guards nil))
  (if (atom cands) nil (cons (fn2-cnsk-refresh (car cands)) (fn2-cnsk-map-refresh (cdr cands)))))
(defun fn2-cnsk-boundary (cands)
  (declare (xargs :verify-guards nil))
  (fn2-cnsk-close (remove-duplicates-equal (fn2-cnsk-map-refresh cands)) 64))

;; The observations ----------------------------------------------------------------
(defun fn2-cnsk-add (key entry cands)
  (declare (xargs :verify-guards nil))
  (if (atom cands) nil
    (let ((c (car cands)))
      (cons (list (nth 0 c) (put-assoc-equal key entry (nth 1 c)) (nth 2 c)) (fn2-cnsk-add key entry (cdr cands))))))
(defun fn2-cnsk-drop-key (key pending)
  (declare (xargs :verify-guards nil))
  (cond ((atom pending) nil)
        ((equal (caar pending) key) (fn2-cnsk-drop-key key (cdr pending)))
        (t (cons (car pending) (fn2-cnsk-drop-key key (cdr pending))))))
; A connection ends: a mutation not yet linearized becomes an orphan.
(defun fn2-cnsk-close-conn (key cands)
  (declare (xargs :verify-guards nil))
  (if (atom cands) nil
    (let* ((c (car cands)) (e (cdr (assoc-equal key (nth 1 c)))))
      (cons (list (nth 0 c) (fn2-cnsk-drop-key key (nth 1 c))
                  (if (eq (car e) :mut) (append (nth 2 c) (list (nth 3 e))) (nth 2 c)))
            (fn2-cnsk-close-conn key (cdr cands))))))
(defun fn2-cnsk-close-all (keys cands)
  (declare (xargs :verify-guards nil))
  (if (atom keys) cands (fn2-cnsk-close-all (cdr keys) (fn2-cnsk-close-conn (car keys) cands))))
(defun fn2-cnsk-reply-keep (key answer durable cands)
  (declare (xargs :verify-guards nil))
  (if (atom cands) nil
    (b* ((c (car cands)) (rest (fn2-cnsk-reply-keep key answer durable (cdr cands)))
         (e (cdr (assoc-equal key (nth 1 c))))
         (gone (list (nth 0 c) (fn2-cnsk-drop-key key (nth 1 c)) (nth 2 c))))
      (cond ((null e) rest)
            ((eq (car answer) :uncertain)
             (cond ((not durable) rest)
                   ((eq (car e) :mut) (cons (list (nth 0 c) (fn2-cnsk-drop-key key (nth 1 c)) (append (nth 2 c) (list (nth 3 e)))) rest))
                   ((eq (car e) :done) (cons gone rest))
                   (t rest)))
            ((eq (car e) :done) (if (equal (nth 3 e) answer) (cons gone rest) rest))
            ((eq (car e) :mut)
             (let ((a (fn2-cnsk-apply-entry key c)))
               (if (equal (nth 3 (cdr (assoc-equal key (nth 1 a)))) answer)
                   (cons (list (nth 0 a) (fn2-cnsk-drop-key key (nth 1 a)) (nth 2 a)) rest)
                 rest)))
            ((member-equal answer (nth 4 e)) (cons gone rest))
            (t rest)))))
(defun fn2-cnsk-entry-somewhere (key cands)
  (declare (xargs :verify-guards nil))
  (cond ((atom cands) nil)
        ((assoc-equal key (nth 1 (car cands))) (cdr (assoc-equal key (nth 1 (car cands)))))
        (t (fn2-cnsk-entry-somewhere key (cdr cands)))))
(defun fn2-cnsk-world (op cands)
  (declare (xargs :verify-guards nil))
  (if (atom cands) nil
    (b* ((c (car cands)) (st (nth 0 c)) (rest (fn2-cnsk-world op (cdr cands)))
         (kind (car op)))
      (case kind
        (:post (b* (((list & p stream article pos) op)
                    ((unless (and (posp pos) (< (fn2-cns-frontier st) pos))) rest)
                    ((mv & st1) (fn2-cns-verb-step (list :commit (- pos 1)) st nil))
                    ((mv o st2) (fn2-cns-append st1 p stream article nil nil)))
                 (if (eq (fn2-cns-class o) :accepted) (cons (list st2 (nth 1 c) (nth 2 c)) rest) rest)))
        (:withdraw (b* (((list & p mid pos) op)
                        ((unless (and (posp pos) (< (fn2-cns-frontier st) pos))) rest)
                        ((mv & st1) (fn2-cns-verb-step (list :commit (- pos 1)) st nil))
                        (st2 (fn2-cns-withdraw st1 p mid)))
                     (if (equal (fn2-cns-frontier st2) pos) (cons (list st2 (nth 1 c) (nth 2 c)) rest) rest)))
        (otherwise (mv-let (o st2) (fn2-cns-verb-step op st nil) (declare (ignore o)) (cons (list st2 (nth 1 c) (nth 2 c)) rest)))))))
(defun fn2-cnsk-publish (f cands)
  (declare (xargs :verify-guards nil))
  (if (atom cands) nil
    (let ((c (car cands)) (rest (fn2-cnsk-publish f (cdr cands))))
      (if (< (nfix f) (fn2-cns-frontier (nth 0 c))) rest
        (mv-let (o st2) (fn2-cns-verb-step (list :commit f) (nth 0 c) nil)
          (declare (ignore o))
          (cons (list st2 (nth 1 c) (nth 2 c)) rest))))))

;; Readings ------------------------------------------------------------------------
(defun fn2-cnsk-cursor-rows (regs st)
  (declare (xargs :verify-guards nil))
  (if (atom regs) nil
    (let* ((p (caar (car regs))) (c (cdar (car regs))) (epoch (fn2-cns-reg-epoch (cdar regs))))
      (cons (list p c epoch (fn2-cns-acked st p c epoch)) (fn2-cnsk-cursor-rows (cdr regs) st)))))
(defun fn2-cnsk-same-set (a b)
  (declare (xargs :verify-guards nil))
  (and (equal (len a) (len b)) (subsetp-equal a b) (subsetp-equal b a)))
(defun fn2-cnsk-waits-of (p pending)
  (declare (xargs :verify-guards nil))
  (cond ((atom pending) 0)
        ((let ((e (cdar pending))) (and (eq (car e) :read) (eq (nth 1 e) 'wait) (equal (nth 1 (nth 3 e)) p)))
         (+ 1 (fn2-cnsk-waits-of p (cdr pending))))
        (t (fn2-cnsk-waits-of p (cdr pending)))))
(defun fn2-cnsk-waits-ok (waits pending exact)
  (declare (xargs :verify-guards nil))
  (if (atom waits) t
    (let ((held (nfix (cadr (car waits)))) (n (fn2-cnsk-waits-of (car (car waits)) pending)))
      (and (if exact (equal held n) (<= held n)) (fn2-cnsk-waits-ok (cdr waits) pending exact)))))
(defun fn2-cnsk-ledger (cursors waits cands)
  (declare (xargs :verify-guards nil))
  (if (atom cands) nil
    (let ((c (car cands)) (rest (fn2-cnsk-ledger cursors waits (cdr cands))))
      (if (and (fn2-cnsk-same-set cursors (fn2-cnsk-cursor-rows (fn2-cns-get :regs (nth 0 c)) (nth 0 c)))
               (fn2-cnsk-waits-ok waits (nth 1 c) nil))
          (cons c rest) rest))))
; A pending wait whose read is due now: a step made it answerable and it has not answered.
(defun fn2-cnsk-due-wait (pending st)
  (declare (xargs :verify-guards nil))
  (cond ((atom pending) nil)
        ((let ((e (cdar pending)))
           (and (eq (car e) :read) (eq (nth 1 e) 'wait)
                (let ((a (fn2-cnsk-answer-of 'wait (nth 2 e) (nth 3 e) st)))
                  (or (not (eq (car a) :accepted)) (< 0 (nfix (nth 2 (nth 2 a))))))))
         (caar pending))
        (t (fn2-cnsk-due-wait (cdr pending) st))))
(defun fn2-cnsk-settle (waits cands)
  (declare (xargs :verify-guards nil))
  (if (atom cands) nil
    (let ((c (car cands)) (rest (fn2-cnsk-settle waits (cdr cands))))
      (if (and (not (fn2-cnsk-due-wait (nth 1 c) (nth 0 c))) (fn2-cnsk-waits-ok waits (nth 1 c) t))
          (cons (list (nth 0 c) (nth 1 c) nil) rest) rest))))

;; The checker -----------------------------------------------------------------------
; CONNS ((CONN . PRINCIPAL) ...). (:pass) or (:fail WHAT INDEX ...).
(defun fn2-cnsk-run (obs i conns cands interims)
  (declare (xargs :verify-guards nil :measure (len obs)
                  :hints (("Goal" :in-theory (disable fn2-layout-parse fn2-fncu-decode fn2-fnct-open fn2-fnct-request-decode fn2-cns-verb-step fn2-cns-append fn2-cns-withdraw fn2-cnsk-request fn2-cnsk-decode-reply fn2-cnsk-reply-keep fn2-cnsk-boundary
                                          fn2-cnsk-world fn2-cnsk-publish fn2-cnsk-ledger fn2-cnsk-settle
                                          fn2-cnsk-close-conn fn2-cnsk-close-all fn2-cnsk-add fn2-cnsk-entry-somewhere
                                          fn2-cnsk-due-wait fn2-cnsk-cursor-rows)))))
  (b* (((when (atom obs)) :pass)
       (x (car obs)) (kind (car x))
       ((when (atom cands)) (list :fail :no-candidate i))
       ((when (< *fn2-cnsk-max-candidates* (len cands))) (list :fail :candidates i (len cands))))
    (case kind
      (:connect
       (if (fn2-cnsk-entry-somewhere (nth 1 x) cands) (list :fail :connect-with-pending i (nth 1 x))
         (fn2-cnsk-run (cdr obs) (+ 1 i) (put-assoc-equal (nth 1 x) (nth 2 x) conns) cands interims)))
      (:request
       (b* ((conn (nth 1 x)) (p (cdr (assoc-equal conn conns)))
            ((unless (assoc-equal conn conns)) (list :fail :unknown-connection i conn))
            ((when (fn2-cnsk-entry-somewhere conn cands)) (list :fail :pipelined i conn))
            (r (fn2-cnsk-request (nth 2 x) p interims)))
         (case (car r)
           (:unchecked (list :fail :unchecked-legacy i (cdr r)))
           (:close (fn2-cnsk-run (cdr obs) (+ 1 i) conns (fn2-cnsk-add conn (list :read 'read :k28 nil nil) cands) interims))
           (:answer (fn2-cnsk-run (cdr obs) (+ 1 i) conns
                                  (fn2-cnsk-add conn (list :read (nth 1 r) (nth 2 r) nil (list (nth 3 r))) cands) interims))
           (otherwise
            (b* (((list & verb form op) r)
                 (entry (if (member-eq verb *fn2-cnsk-durable-verbs*) (list :mut verb form op) (list :read verb form op nil))))
              (fn2-cnsk-run (cdr obs) (+ 1 i) conns (fn2-cnsk-boundary (fn2-cnsk-add conn entry cands)) interims))))))
      (:reply
       (b* ((conn (nth 1 x)) (e (fn2-cnsk-entry-somewhere conn cands))
            ((unless e) (list :fail :unsolicited-reply i conn))
            (verb (nth 1 e)) (form (nth 2 e))
            (answer (fn2-cnsk-decode-reply verb form (nth 2 x)))
            ((when (eq (car answer) :malformed)) (list :fail :malformed-reply i conn answer))
            (kept (fn2-cnsk-reply-keep conn answer (member-eq verb *fn2-cnsk-durable-verbs*) cands))
            ((unless kept) (list :fail :reply i conn verb answer e)))
         (fn2-cnsk-run (cdr obs) (+ 1 i) conns (fn2-cnsk-boundary kept) interims)))
      (:close (fn2-cnsk-run (cdr obs) (+ 1 i) (remove1-equal (assoc-equal (nth 1 x) conns) conns)
                            (fn2-cnsk-boundary (fn2-cnsk-close-conn (nth 1 x) cands)) interims))
      (:world
       (b* ((op (nth 1 x))
            (cands (if (eq (car op) :crash) (fn2-cnsk-close-all (strip-cars conns) cands) cands))
            (conns (if (eq (car op) :crash) nil conns))
            (next (fn2-cnsk-world op cands)))
         (if next (fn2-cnsk-run (cdr obs) (+ 1 i) conns (fn2-cnsk-boundary next) interims)
           (list :fail :world i op))))
      (:publish
       (let ((next (fn2-cnsk-publish (nth 1 x) cands)))
         (if next (fn2-cnsk-run (cdr obs) (+ 1 i) conns (fn2-cnsk-boundary next) interims)
           (list :fail :publish i (nth 1 x)))))
      (:ledger
       (let ((next (fn2-cnsk-ledger (nth 1 x) (nth 2 x) cands)))
         (if next (fn2-cnsk-run (cdr obs) (+ 1 i) conns next interims)
           (list :fail :ledger i (nth 1 x) (nth 2 x)
                 (fn2-cnsk-cursor-rows (fn2-cns-get :regs (nth 0 (car cands))) (nth 0 (car cands)))))))
      (:settled
       (let ((next (fn2-cnsk-settle (nth 1 x) cands)))
         (if next (fn2-cnsk-run (cdr obs) (+ 1 i) conns (remove-duplicates-equal next) interims)
           (list :fail (if (fn2-cnsk-due-wait (nth 1 (car cands)) (nth 0 (car cands))) :lost-wake :settled-holding)
                 i (nth 1 x)))))
      (otherwise (list :fail :unknown-observation i x)))))
; The checker: OBS from a store with HISTORY and INCARNATION (id octets).
(defun fn2-consumer-check (obs history incarnation interims)
  (declare (xargs :verify-guards nil))
  (fn2-cnsk-run obs 0 nil (list (list (fn2-cns-init history incarnation) nil nil)) interims))
