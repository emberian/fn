; The L carrier's client at the list level (e-surface.md 4.2): the frames a
; scripted client sends to the served fn2-ctl and fn2-cns (tests/sim-layer-e,
; tests/m2-cuts) and the summary it reads off a reply, built and read by
; consumer-codec.lisp's specification (fn2-fnct-seal, fn2-fnct-open,
; fn2-fnct-request-encode, fn2-layout-parse, fn2-fncu-decode), never by the
; served codecs under test. The client computes no value the port computes:
; a cursor is the one the node issued, re-sent, or re-sent with a proposed
; position (an ack's proposal).
(in-package "ACL2")
(include-book "../books/fnct-pool")

(defun fnc-be (n)
  ; N's fewest big-endian octets, at least one.
  (declare (xargs :verify-guards nil :measure (nfix n)))
  (if (< (nfix n) 256) (list (nfix n)) (append (fnc-be (ash (nfix n) -8)) (list (mod (nfix n) 256)))))
(defun fnc-chars (octets)
  (declare (xargs :verify-guards nil))
  (if (atom octets) nil (cons (code-char (nfix (car octets))) (fnc-chars (cdr octets)))))
(defun fnc-chars-string (octets) (declare (xargs :verify-guards nil)) (coerce (fnc-chars octets) 'string))

;; Requests -----------------------------------------------------------------------
(defun fnc-control (cmd)
  ; Kind 1: one command octet (1 status, 2 pause, 3 resume, 4 drain, 5 stop).
  (declare (xargs :verify-guards nil))
  (fn2-fnct-seal *fn2-fnct-control-kind* (list cmd)))
(defun fnc-request (word alist)
  (declare (xargs :verify-guards nil))
  (fn2-fnct-seal *fn2-fnct-request-kind* (fn2-fnct-request-encode word alist)))
; START 1 is :history, 0 :now; the stream list is empty (the principal's inbox).
(defun fnc-register (cid start)
  (declare (xargs :verify-guards nil))
  (fnc-request :register-query (list (cons 'consumer (fnc-be cid)) (cons 'streams nil) (cons 'start start))))
(defun fnc-position (cid)
  (declare (xargs :verify-guards nil))
  (fnc-request :position (list (cons 'consumer (fnc-be cid)))))
(defun fnc-status (cid)
  (declare (xargs :verify-guards nil))
  (fnc-request :status-wide (list (cons 'consumer (fnc-be cid)))))
(defun fnc-read (cursor items)
  (declare (xargs :verify-guards nil))
  (fnc-request :read (list (cons 'cursor cursor) (cons 'max-items items) (cons 'max-octets 65536))))
(defun fnc-wait (cursor items seconds)
  (declare (xargs :verify-guards nil))
  (fnc-request :wait-cursor (list (cons 'cursor cursor) (cons 'max-items items) (cons 'max-octets 65536)
                                  (cons 'seconds seconds))))
(defun fnc-fetch (mid position)
  ; fetch (13) of the occurrence at POSITION whose Message-ID is MID (octets), domain 0.
  (declare (xargs :verify-guards nil))
  (fnc-request :fetch (list (cons 'message-id mid) (cons 'domain 0) (cons 'position position))))
(defun fnc-at (cursor position)
  ; The issued CURSOR proposing POSITION.
  (declare (xargs :verify-guards nil))
  (let ((c (fn2-fncu-decode cursor)))
    (if (eq (car c) :ok) (fn2-fncu-encode (update-nth 10 position (cadr c))) cursor)))
(defun fnc-ack (cursor position)
  (declare (xargs :verify-guards nil))
  (fnc-request :ack (list (cons 'cursor (fnc-at cursor position)))))
(defun fnc-append (op article)
  ; OP 0 is none; ARTICLE the article's octets (CR LF lines, not dot-stuffed).
  (declare (xargs :verify-guards nil))
  (fnc-request :append (list (cons 'stream nil) (cons 'op (if (equal op 0) nil (fnc-be op))) (cons 'article article))))

;; Replies ------------------------------------------------------------------------
(defun fnc-be-value (octets acc)
  (declare (xargs :verify-guards nil))
  (if (atom octets) (nfix acc) (fnc-be-value (cdr octets) (+ (* 256 (nfix acc)) (nfix (car octets))))))
(defun fnc-frame-extent (octets)
  ; The octets of the first frame in OCTETS (its header's length plus 42).
  (declare (xargs :verify-guards nil))
  (if (< (len octets) 10) octets
    (take (min (len octets) (+ 42 (fnc-be-value (take 4 (nthcdr 6 octets)) 0))) octets)))
(defun fnc-parse (layout octets)
  (declare (xargs :verify-guards nil))
  (mv-let (code vs rest) (fn2-layout-parse layout octets)
    (and (eq code :ok) (null rest) (list :ok vs))))
(defun fnc-cursor-position (octets)
  (declare (xargs :verify-guards nil))
  (let ((c (fn2-fncu-decode octets))) (if (eq (car c) :ok) (nth 10 (cadr c)) (list :bad-cursor octets))))
; A page's items (consumer-codec.lisp *fn2-fnct-item-layout*), each
; (TYPE POSITION MESSAGE-ID BODY) with TYPE a keyword and MESSAGE-ID a
; string; :bad for octets that are not whole items. FUEL bounds the walk.
(defun fnc-items (octets fuel)
  (declare (xargs :verify-guards nil :measure (nfix fuel)
                  :hints (("Goal" :in-theory (disable fn2-layout-parse)))))
  (if (or (atom octets) (zp fuel)) nil
    (mv-let (code vs rest) (fn2-layout-parse *fn2-fnct-item-layout* octets)
      (if (not (and (eq code :ok) (< (len rest) (len octets)))) (list :bad)
        (cons (list (nth (nth 0 vs) '(:record :withdrawn :reference :gap)) (nth 2 vs)
                    (fnc-chars-string (nth 5 vs)) (nth 6 vs))
              (fnc-items rest (- fuel 1)))))))
; An accepted result's summary: a cursor's POSITION; ack's POSITION;
; status's (POSITION FRONTIER GAP); a page's (MORE NEXT-POSITION COUNT ITEMS);
; append's (POSITION EVIDENCE).
(defun fnc-result (verb octets)
  (declare (xargs :verify-guards nil))
  (case verb
    ((register position) (fnc-cursor-position octets))
    (ack (let ((r (fnc-parse (cadr (assoc-eq 'ack *fn2-fnct-results*)) octets))) (if r (nth 1 (cadr r)) (list :bad octets))))
    (status (let ((r (fnc-parse (cadr (assoc-eq 'status *fn2-fnct-results*)) octets))) (if r (cdr (cadr r)) (list :bad octets))))
    ((read wait)
     (let* ((r (fnc-parse (cadr (assoc-eq 'read *fn2-fnct-results*)) octets))
            (items (and r (fnc-items (nth 3 (cadr r)) (len octets)))))
       (if (and r (equal (len items) (nth 2 (cadr r))) (not (member-eq :bad items)))
           (list (nth 0 (cadr r)) (fnc-cursor-position (nth 1 (cadr r))) (nth 2 (cadr r)) items)
         (list :bad octets))))
    (fetch (let ((r (fnc-parse (cadr (assoc-eq 'fetch *fn2-fnct-results*)) octets))) (if r (car (cadr r)) (list :bad octets))))
    (append (let ((r (fnc-parse (cadr (assoc-eq 'append *fn2-fnct-results*)) octets)))
              (if r (list (nth 2 (cadr r)) (nth 5 (cadr r))) (list :bad octets))))
    (otherwise octets)))
(defun fnc-k28-result (octets)
  ; The result octets of the first frame in OCTETS when it is an accepted kind 28 reply.
  (declare (xargs :verify-guards nil))
  (b* ((f (fn2-fnct-open (fnc-frame-extent octets) 4096))
       ((unless (and (eq (car f) :ok) (equal (cadr f) *fn2-fnct-port-reply-kind*))) nil)
       (r (fnc-parse *fn2-fnct-port-reply-layout* (caddr f))))
    (and r (equal (car (cadr r)) 0) (caddr (cadr r)))))
(defun fnc-reply-cursor (verb octets)
  ; The cursor an accepted register, position or page reply issued.
  (declare (xargs :verify-guards nil))
  (let ((q (fnc-k28-result octets)))
    (if (member-eq verb '(read wait))
        (let ((r (fnc-parse (cadr (assoc-eq 'read *fn2-fnct-results*)) q))) (and r (nth 1 (cadr r))))
      q)))
(defun fnc-reply (verb octets)
  ; The first frame in OCTETS: (:posture P) for kind 2; (CLASS WORD RESULT)
  ; for kind 28, WORD a string and RESULT the accepted verb's summary (nil
  ; otherwise); (:malformed ...) for anything else.
  (declare (xargs :verify-guards nil))
  (b* ((f (fn2-fnct-open (fnc-frame-extent octets) 4096))
       ((unless (eq (car f) :ok)) (list :malformed (cadr f) octets))
       ((list & kind payload) f))
    (cond ((and (equal kind *fn2-fnct-control-reply-kind*) (consp payload) (null (cdr payload)))
           (list :posture (car payload)))
          ((equal kind *fn2-fnct-port-reply-kind*)
           (b* ((r (fnc-parse *fn2-fnct-port-reply-layout* payload))
                ((unless r) (list :malformed :k28 payload))
                ((list class word result) (cadr r))
                (class (nth class *fn2-fnct-statuses*)))
             (list class (fnc-chars-string word)
                   (if (eq class :accepted) (fnc-result verb result) (and (consp result) (list :bad result))))))
          (t (list :malformed :kind kind)))))
(defun fnc-replies (verbs octets)
  ; Every frame in OCTETS, the i-th read as VERBS's i-th.
  (declare (xargs :verify-guards nil :measure (len verbs)))
  (if (or (atom octets) (atom verbs) (< (len octets) 42)) nil
    (let ((n (len (fnc-frame-extent octets))))
      (cons (fnc-reply (car verbs) octets)
            (if (< 0 n) (fnc-replies (cdr verbs) (nthcdr n octets)) nil)))))
; The cursor a node issues under e-surface.md 14 item 8's interim rule: history
; and incarnation one 0 octet each, the consumer id, the principal's slot and
; query 1, each in its fewest big-endian octets. A fixture's expectation, never
; a client's input to the node it judges.
(defun fnc-issued (cid principal version epoch position)
  (declare (xargs :verify-guards nil))
  (fn2-fncu-encode (list :cursor 0 '(0) '(0) (fnc-be cid) (fnc-be principal) '(1) version version epoch position)))
