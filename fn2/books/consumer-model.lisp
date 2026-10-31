; The consumer port's meaning (layer E3; fn2/docs/e-surface.md section 9): a
; logic-only interpreter of FN2-CONSUMER's verbs over lists, the reference
; the served machine refines and the CONSUMER checker's oracle. Nothing here
; is on a served path: octets are strings, the log is a list.
;
; The state is an alist of named parts:
;   :log       events in position order (positions 1, 2, ...):
;              (POS :article STREAMS MID OCTETS TO AUTHOR NUMBERS) or (POS :withdraw STREAMS TARGET AUTHOR)
;   :regs      (principal . consumer) -> (EPOCH QV VV EDGES GRANTS-AT-REGISTRATION)
;   :acks      (principal consumer epoch) -> acknowledged position
;   :outcomes  (principal . op) -> (DIGEST OUTCOME): the retry table (C's S-OUTCOME)
;   :grants    (principal scope stream) facts, scope :read, :append or :consume
;   :auth      principal -> authority version, bumped by every grant change
;   :charged   principal -> durable octets charged;  :limit principal -> its limit
;   :waits     (principal . consumer) -> (CURSOR LIMITS PARKED-PAGE): volatile, a crash drops it
;   :numbers   group -> high;  :reclaimed positions;  :evidence (MID OCTETS PRINCIPAL)
;   :epoch     the next registration epoch;  :history :incarnation the store's identity
; A stream is a group name (a string) or (:addr PRINCIPAL); a principal's
; consumers are its own namespace, so another principal's consumer is simply
; unknown. A cursor is fncu's nine fields (HISTORY INCARNATION CONSUMER
; PRINCIPAL QUERY QV VV EPOCH POSITION), QUERY being the consumer id as in
; fn1. A rebase is a new registration epoch, so a recorded position is
; monotone per (principal, consumer, epoch).
;
; FAULT is nil in every statement. Each fault is a deliberately wrong node a
; keystone's negative tooth must catch (e-surface.md section 9):
;   :skip          a page that stops early drops its last item
;   :rewind        an ack behind the recorded position is recorded
;   :equal-behind  an equal ack is refused as behind
;   :reappend      an append ignores the retry table
;   :stale-wait    a woken wait answers the page it saw when it parked
;   :pinned-grant  a read uses the grants of its registration and no view check
;   :meter-first   the meter charges before the grant check, and keeps it
;   :rerender      the NNTP view re-renders the article it serves
;   :lost-wake     a step that makes a parked wait's read due does not answer it
(in-package "ACL2")
(include-book "consumer-port")
(fn2-book-layer :e)

(defconst *fn2-cns-faults*
  '(:skip :rewind :equal-behind :reappend :stale-wait :pinned-grant :meter-first :rerender :lost-wake))
(defconst *fn2-cns-record-octets* 64)        ; the nominal size of a consumer record
(defconst *fn2-cns-default-limit* 1000000000000)
(defconst *fn2-cns-max-addressees* 16)       ; the model's policy row max-addressees

(defun fn2-cns-class (o) (declare (xargs :guard t)) (and (consp o) (car o)))
(defun fn2-cns-get (k st) (declare (xargs :verify-guards nil)) (and (alistp st) (cdr (assoc-eq k st))))
(defun fn2-cns-put (k v st) (declare (xargs :verify-guards nil)) (put-assoc-eq k v st))
(defun fn2-cns-at (k al) (declare (xargs :verify-guards nil)) (and (alistp al) (cdr (assoc-equal k al))))
(defun fn2-cns-set (k v al) (declare (xargs :verify-guards nil)) (put-assoc-equal k v (if (alistp al) al nil)))

(defun fn2-cns-init (history incarnation)
  (declare (xargs :verify-guards nil))
  (list (cons :log nil) (cons :regs nil) (cons :acks nil) (cons :outcomes nil) (cons :grants nil)
        (cons :auth nil) (cons :charged nil) (cons :limit nil) (cons :waits nil) (cons :numbers nil)
        (cons :reclaimed nil) (cons :evidence nil) (cons :epoch 1)
        (cons :history history) (cons :incarnation incarnation)))

;; Events ------------------------------------------------------------------
(defun fn2-cns-ev-pos (e) (declare (xargs :verify-guards nil)) (nfix (nth 0 e)))
(defun fn2-cns-ev-kind (e) (declare (xargs :verify-guards nil)) (nth 1 e))
(defun fn2-cns-ev-streams (e) (declare (xargs :verify-guards nil)) (nth 2 e))
(defun fn2-cns-ev-mid (e) (declare (xargs :verify-guards nil)) (nth 3 e))
(defun fn2-cns-ev-octets (e) (declare (xargs :verify-guards nil)) (nth 4 e))
(defun fn2-cns-ev-to (e) (declare (xargs :verify-guards nil)) (nth 5 e))
(defun fn2-cns-ev-numbers (e) (declare (xargs :verify-guards nil)) (nth 7 e))
(defun fn2-cns-frontier (st) (declare (xargs :verify-guards nil)) (len (fn2-cns-get :log st)))

(defun fn2-cns-article-of (mid log)
  (declare (xargs :verify-guards nil))
  (cond ((atom log) nil)
        ((and (eq (fn2-cns-ev-kind (car log)) :article) (equal (fn2-cns-ev-mid (car log)) mid)) (car log))
        (t (fn2-cns-article-of mid (cdr log)))))
(defun fn2-cns-withdrawn-p (mid log)
  (declare (xargs :verify-guards nil))
  (cond ((atom log) nil)
        ((and (eq (fn2-cns-ev-kind (car log)) :withdraw) (equal (fn2-cns-ev-mid (car log)) mid)) t)
        (t (fn2-cns-withdrawn-p mid (cdr log)))))

;; Grant and visibility -------------------------------------------------------
(defun fn2-cns-allows (grants p scope stream)
  (declare (xargs :verify-guards nil))
  (if (member-equal (list p scope stream) grants) t nil))
(defun fn2-cns-readable (grants p streams)
  (declare (xargs :verify-guards nil))
  (cond ((atom streams) nil)
        ((fn2-cns-allows grants p :read (car streams)) (cons (car streams) (fn2-cns-readable grants p (cdr streams))))
        (t (fn2-cns-readable grants p (cdr streams)))))
(defun fn2-cns-auth (st p) (declare (xargs :verify-guards nil)) (nfix (fn2-cns-at p (fn2-cns-get :auth st))))
(defun fn2-cns-bump-auth (p st)
  (declare (xargs :verify-guards nil))
  (fn2-cns-put :auth (fn2-cns-set p (+ 1 (fn2-cns-auth st p)) (fn2-cns-get :auth st)) st))

; Why an event is selected for P with EDGES under GRANTS: its reasons, or nil.
; An article is visible only through a stream P may read (the pullback along
; the grant); a mention needs the addr edge and a readable stream; a
; withdrawal is selected when its target would be.
; EDGES are ((STREAM . START) ...): an edge selects events after its start
; (INBOX 4.3: a stream added later is added from then, so the scalar cursor
; stays valid). A group-address flag (:room in TO) is one entry with one more
; reason, never an entry per member.
(defun fn2-cns-edge-live (stream edges pos)
  (declare (xargs :verify-guards nil))
  (let ((a (assoc-equal stream edges))) (and a (< (nfix (cdr a)) (nfix pos)))))
(defun fn2-cns-live-readable (readable edges pos)
  (declare (xargs :verify-guards nil))
  (cond ((atom readable) nil)
        ((fn2-cns-edge-live (car readable) edges pos) t)
        (t (fn2-cns-live-readable (cdr readable) edges pos))))
(defun fn2-cns-article-reasons (streams to edges grants p pos)
  (declare (xargs :verify-guards nil))
  (let* ((readable (fn2-cns-readable grants p streams))
         (room (fn2-cns-live-readable readable edges pos))
         (mention (and readable (fn2-cns-edge-live (list :addr p) edges pos) (member-equal p to))))
    (append (and room '(:room)) (and room (member-eq :room to) '(:group-address)) (and mention '(:mention)))))
(defun fn2-cns-reasons (e edges grants p log)
  (declare (xargs :verify-guards nil))
  (if (eq (fn2-cns-ev-kind e) :article)
      (fn2-cns-article-reasons (fn2-cns-ev-streams e) (fn2-cns-ev-to e) edges grants p (fn2-cns-ev-pos e))
    (let ((target (fn2-cns-article-of (fn2-cns-ev-mid e) log)))
      (and target (fn2-cns-article-reasons (fn2-cns-ev-streams target) (fn2-cns-ev-to target) edges grants p
                                           (fn2-cns-ev-pos target))))))

; The item an event is delivered as (e-surface.md 3.4, 4.1): (POS TYPE MID PAYLOAD REASONS).
(defun fn2-cns-item (e reasons st octet-limit)
  (declare (xargs :verify-guards nil))
  (let ((pos (fn2-cns-ev-pos e)) (mid (fn2-cns-ev-mid e)) (octets (fn2-cns-ev-octets e)))
    (cond ((eq (fn2-cns-ev-kind e) :withdraw) (list pos :withdrawal mid nil reasons))
          ((member pos (fn2-cns-get :reclaimed st)) (list pos :gap mid :unavailable reasons))
          ((fn2-cns-withdrawn-p mid (fn2-cns-get :log st)) (list pos :withdrawn mid nil reasons))
          ((< (nfix octet-limit) (length octets)) (list pos :ref mid (length octets) reasons))
          (t (list pos :record mid octets reasons)))))
(defun fn2-cns-item-pos (i) (declare (xargs :verify-guards nil)) (nfix (nth 0 i)))
(defun fn2-cns-item-type (i) (declare (xargs :verify-guards nil)) (nth 1 i))
(defun fn2-cns-item-mid (i) (declare (xargs :verify-guards nil)) (nth 2 i))
(defun fn2-cns-item-payload (i) (declare (xargs :verify-guards nil)) (nth 3 i))

;; The page --------------------------------------------------------------------
; Walk EVENTS after position P, collecting selected items until ITEMS are
; held. (mv items more next): NEXT is the position through which the walk is
; complete, the last item's when a held page met one more selected event,
; else the last event walked.
(defun fn2-cns-walk (events p edges grants principal st items octet-limit acc last fault)
  (declare (xargs :verify-guards nil :measure (len events)))
  (if (atom events) (mv (reverse acc) nil last)
    (let* ((e (car events))
           (reasons (and (< (nfix p) (fn2-cns-ev-pos e))
                         (fn2-cns-reasons e edges grants principal (fn2-cns-get :log st)))))
      (cond ((not reasons)
             (fn2-cns-walk (cdr events) p edges grants principal st items octet-limit acc
                           (max (nfix last) (fn2-cns-ev-pos e)) fault))
            ((<= (nfix items) (len acc))
             (mv (reverse (if (and (eq fault :skip) (consp acc)) (cdr acc) acc)) t last))
            (t (fn2-cns-walk (cdr events) p edges grants principal st items octet-limit
                             (cons (fn2-cns-item e reasons st octet-limit) acc) (fn2-cns-ev-pos e) fault))))))

;; Registrations and cursors --------------------------------------------------
(defun fn2-cns-reg-epoch (r) (declare (xargs :verify-guards nil)) (nth 0 r))
(defun fn2-cns-reg-qv (r) (declare (xargs :verify-guards nil)) (nth 1 r))
(defun fn2-cns-reg-vv (r) (declare (xargs :verify-guards nil)) (nth 2 r))
(defun fn2-cns-reg-edges (r) (declare (xargs :verify-guards nil)) (nth 3 r))
(defun fn2-cns-reg-grants (r) (declare (xargs :verify-guards nil)) (nth 4 r))
(defun fn2-cns-reg (st p c) (declare (xargs :verify-guards nil)) (fn2-cns-at (cons p c) (fn2-cns-get :regs st)))
(defun fn2-cns-acked (st p c epoch)
  (declare (xargs :verify-guards nil))
  (nfix (fn2-cns-at (list p c epoch) (fn2-cns-get :acks st))))
(defun fn2-cns-cursor (st p c r position)
  (declare (xargs :verify-guards nil))
  (list (fn2-cns-get :history st) (fn2-cns-get :incarnation st) c p c
        (fn2-cns-reg-qv r) (fn2-cns-reg-vv r) (fn2-cns-reg-epoch r) position))
(defun fn2-cns-cursor-consumer (k) (declare (xargs :verify-guards nil)) (nth 2 k))
(defun fn2-cns-cursor-position (k) (declare (xargs :verify-guards nil)) (nfix (nth 8 k)))
; The cursor's scope, checked before any mutation: nil, or the refusal word.
; VIEW says whether the view version must be current.
(defun fn2-cns-scope-problem (st p k view)
  (declare (xargs :verify-guards nil))
  (let* ((c (fn2-cns-cursor-consumer k)) (r (fn2-cns-reg st p c)))
    (cond ((not (and (true-listp k) (equal (len k) 9) (natp (nth 8 k)))) 'scope)
          ((null r) 'unknown-consumer)
          ((not (equal (take 6 k) (take 6 (fn2-cns-cursor st p c r 0)))) 'scope)
          ((not (equal (nth 7 k) (fn2-cns-reg-epoch r))) 'scope)
          ((and view (not (equal (nth 6 k) (fn2-cns-reg-vv r)))) 'scope)
          (t nil))))

;; Meter -------------------------------------------------------------------
(defun fn2-cns-charged (st p) (declare (xargs :verify-guards nil)) (nfix (fn2-cns-at p (fn2-cns-get :charged st))))
(defun fn2-cns-limit (st p)
  (declare (xargs :verify-guards nil))
  (let ((l (fn2-cns-at p (fn2-cns-get :limit st)))) (if (natp l) l *fn2-cns-default-limit*)))
(defun fn2-cns-meter (st p amount)
  (declare (xargs :verify-guards nil))
  (if (< (fn2-cns-limit st p) (+ (fn2-cns-charged st p) (nfix amount))) :limit :ok))
(defun fn2-cns-charge (st p amount)
  (declare (xargs :verify-guards nil))
  (fn2-cns-put :charged (fn2-cns-set p (+ (fn2-cns-charged st p) (nfix amount)) (fn2-cns-get :charged st)) st))

; The generated precondition order (port.lisp FN2-CONSUMER-ADMIT) over the
; model: (mv answer state). AMOUNT is the durable reservation; with
; :meter-first it is charged before the grant is looked at, and kept.
(defun fn2-cns-admit (verb st p grant-ok amount fault)
  (declare (xargs :verify-guards nil))
  (let ((answer (fn2-consumer-admit verb grant-ok (fn2-cns-meter st p amount))))
    (mv answer (if (and (eq fault :meter-first) (< 0 (nfix amount))) (fn2-cns-charge st p amount) st))))
(defun fn2-cns-may-consume (st p) (declare (xargs :verify-guards nil)) (fn2-cns-allows (fn2-cns-get :grants st) p :consume :any))

;; read ---------------------------------------------------------------------
(defun fn2-cns-page (st p k limits fault)
  (declare (xargs :verify-guards nil))
  (let* ((problem (fn2-cns-scope-problem st p k nil))
         (c (fn2-cns-cursor-consumer k)) (r (fn2-cns-reg st p c)))
    (cond (problem (list :refused problem))
          ((and (not (eq fault :pinned-grant)) (not (equal (nth 6 k) (fn2-cns-auth st p))))
           '(:refused rebase-required))
          (t (let ((grants (if (eq fault :pinned-grant) (fn2-cns-reg-grants r) (fn2-cns-get :grants st)))
                   (from (fn2-cns-cursor-position k)))
               (mv-let (items more next)
                 (fn2-cns-walk (fn2-cns-get :log st) from (fn2-cns-reg-edges r) grants p st
                               (nfix (car limits)) (nfix (cadr limits)) nil from fault)
                 (list :accepted (list items more (fn2-cns-cursor st p c r (max from (nfix next)))))))))))
(defun fn2-cns-read (st p k limits fault)
  (declare (xargs :verify-guards nil))
  (mv-let (answer st1) (fn2-cns-admit 'read st p (fn2-cns-may-consume st p) 0 fault)
    (if (not (eq answer :proceed)) (mv answer st1)
      (mv (fn2-cns-page st p k limits fault) st))))
(defun fn2-cns-page-items (o) (declare (xargs :verify-guards nil)) (and (eq (fn2-cns-class o) :accepted) (car (cadr o))))
(defun fn2-cns-page-more (o) (declare (xargs :verify-guards nil)) (and (eq (fn2-cns-class o) :accepted) (cadr (cadr o))))
(defun fn2-cns-page-next (o) (declare (xargs :verify-guards nil)) (and (eq (fn2-cns-class o) :accepted) (caddr (cadr o))))

;; wait -----------------------------------------------------------------
; A wait whose read is due answers it at once; otherwise it parks (:parked is
; no wire outcome: the reply comes from FN2-CNS-WAKE or the timeout).
(defun fn2-cns-wait (st p k limits fault)
  (declare (xargs :verify-guards nil))
  (mv-let (answer st1) (fn2-cns-admit 'wait st p (fn2-cns-may-consume st p) 0 fault)
    (if (not (eq answer :proceed)) (mv answer st1)
      (let ((o (fn2-cns-page st p k limits fault)))
        (if (or (not (eq (fn2-cns-class o) :accepted)) (fn2-cns-page-items o)) (mv o st)
          (mv :parked (fn2-cns-put :waits (fn2-cns-set (cons p (fn2-cns-cursor-consumer k)) (list k limits o)
                                                       (fn2-cns-get :waits st)) st)))))))
; The answer a parked wait gives now: the read at this moment (the final
; frontier check: a lost or late wake costs latency, never an event).
(defun fn2-cns-wait-answer (st key w fault)
  (declare (xargs :verify-guards nil))
  (if (eq fault :stale-wait) (caddr w) (fn2-cns-page st (car key) (car w) (cadr w) fault)))
; After a step, the parked waits whose read is now due (items, or a refusal
; such as rebase-required after an authority change) answer and unpark.
(defun fn2-cns-wake-list (waits st fault)
  (declare (xargs :verify-guards nil))
  (if (atom waits) (mv nil nil)
    (mv-let (answers keep) (fn2-cns-wake-list (cdr waits) st fault)
      (let* ((key (caar waits)) (w (cdar waits))
             (now (fn2-cns-page st (car key) (car w) (cadr w) nil)))
        (if (or (not (eq (fn2-cns-class now) :accepted)) (fn2-cns-page-items now))
            (mv (cons (cons key (fn2-cns-wait-answer st key w fault)) answers) keep)
          (mv answers (cons (car waits) keep)))))))
(defun fn2-cns-wake (st fault)
  (declare (xargs :verify-guards nil))
  (if (eq fault :lost-wake) (mv nil st)
  (mv-let (answers keep) (fn2-cns-wake-list (fn2-cns-get :waits st) st fault)
    (mv answers (fn2-cns-put :waits keep st)))))
(defun fn2-cns-timeout (st p c fault)
  (declare (xargs :verify-guards nil))
  (let* ((key (cons p c)) (w (fn2-cns-at key (fn2-cns-get :waits st))))
    (if (null w) (mv nil st)
      (mv (list (cons key (fn2-cns-wait-answer st key w fault)))
          (fn2-cns-put :waits (remove1-equal (cons key w) (fn2-cns-get :waits st)) st)))))

;; register, rebase, unregister ------------------------------------------------
(defun fn2-cns-edges-p (edges p)
  (declare (xargs :verify-guards nil))
  (if (atom edges) (null edges)
    (and (or (stringp (car edges)) (equal (car edges) (list :addr p)))
         (not (member-equal (car edges) (cdr edges)))
         (fn2-cns-edges-p (cdr edges) p))))
(defun fn2-cns-edges-from (streams start)
  (declare (xargs :verify-guards nil))
  (if (atom streams) nil (cons (cons (car streams) start) (fn2-cns-edges-from (cdr streams) start))))
(defun fn2-cns-edges-keep (streams old start)
  ; Keep the starts of edges that stay; a new stream starts at START.
  (declare (xargs :verify-guards nil))
  (if (atom streams) nil
    (cons (or (assoc-equal (car streams) old) (cons (car streams) start))
          (fn2-cns-edges-keep (cdr streams) old start))))
(defun fn2-cns-install (st p c edges pos qv)
  ; A new registration epoch for (P, C) with EDGES and the cursor at POS: (mv cursor state).
  (declare (xargs :verify-guards nil))
  (let* ((epoch (nfix (fn2-cns-get :epoch st)))
         (r (list epoch qv (fn2-cns-auth st p) edges (fn2-cns-get :grants st)))
         (st (fn2-cns-put :epoch (+ 1 epoch) st))
         (st (fn2-cns-put :regs (fn2-cns-set (cons p c) r (fn2-cns-get :regs st)) st))
         (st (fn2-cns-put :acks (fn2-cns-set (list p c epoch) pos (fn2-cns-get :acks st)) st))
         (st (fn2-cns-charge st p *fn2-cns-record-octets*)))
    (mv (fn2-cns-cursor st p c r pos) st)))
; START is :now (from the frontier) or :history (from the beginning).
(defun fn2-cns-register (st p c streams start fault)
  (declare (xargs :verify-guards nil))
  (mv-let (answer st1) (fn2-cns-admit 'register st p (fn2-cns-may-consume st p) *fn2-cns-record-octets* fault)
    (let ((r (fn2-cns-reg st p c)) (pos (if (eq start :now) (fn2-cns-frontier st) 0)))
      (cond ((not (eq answer :proceed)) (mv answer st1))
            ((not (and (consp streams) (fn2-cns-edges-p streams p) (member start '(:now :history)))) (mv '(:refused query) st))
            ; The same registration again answers the recorded one (a lost reply never resets progress).
            ((and r (equal (strip-cars (fn2-cns-reg-edges r)) streams))
             (mv (list :accepted (list (fn2-cns-cursor st p c r (fn2-cns-acked st p c (fn2-cns-reg-epoch r))))) st))
            (r (mv '(:refused rebase-required) st))
            (t (mv-let (k st2) (fn2-cns-install st p c (fn2-cns-edges-from streams pos) pos 1)
                 (mv (list :accepted (list k)) st2)))))))
; A rebase is a new epoch under the newer query or the current view (an old
; cursor is then refused by scope). START :keep keeps the recorded position
; and the starts of the edges that stay, a new stream added from now (the
; default; INBOX 4.3); :now moves everything to the frontier; :history to 0.
(defun fn2-cns-rebase (st p k streams start fault)
  (declare (xargs :verify-guards nil))
  (mv-let (answer st1) (fn2-cns-admit 'rebase st p (fn2-cns-may-consume st p) *fn2-cns-record-octets* fault)
    (let* ((problem (fn2-cns-scope-problem st p k nil)) (c (fn2-cns-cursor-consumer k)) (r (fn2-cns-reg st p c))
           (new (if streams streams (strip-cars (fn2-cns-reg-edges r))))
           (front (fn2-cns-frontier st)))
      (cond ((not (eq answer :proceed)) (mv answer st1))
            (problem (mv (list :refused problem) st))
            ((not (and (fn2-cns-edges-p new p) (consp new) (member start '(:keep :now :history)))) (mv '(:refused query) st))
            (t (let* ((qv (+ (if streams 1 0) (nfix (fn2-cns-reg-qv r))))
                      (at (fn2-cns-acked st p c (fn2-cns-reg-epoch r))))
                 (mv-let (k2 st2)
                   (case start
                     (:keep (fn2-cns-install st p c (fn2-cns-edges-keep new (fn2-cns-reg-edges r) front) at qv))
                     (:now (fn2-cns-install st p c (fn2-cns-edges-from new front) front qv))
                     (otherwise (fn2-cns-install st p c (fn2-cns-edges-from new 0) 0 qv)))
                   (mv (list :accepted (list k2)) st2))))))))
(defun fn2-cns-unregister (st p k fault)
  (declare (xargs :verify-guards nil))
  (mv-let (answer st1) (fn2-cns-admit 'unregister st p (fn2-cns-may-consume st p) *fn2-cns-record-octets* fault)
    (let ((problem (fn2-cns-scope-problem st p k nil)) (c (fn2-cns-cursor-consumer k)))
      (cond ((not (eq answer :proceed)) (mv answer st1))
            (problem (mv (list :refused problem) st))
            (t (let ((st (fn2-cns-put :regs (remove1-equal (cons (cons p c) (fn2-cns-reg st p c)) (fn2-cns-get :regs st)) st)))
                 (mv '(:accepted nil) (fn2-cns-charge st p *fn2-cns-record-octets*))))))))

;; ack, position, status ------------------------------------------------------
(defun fn2-cns-ack (st p k fault)
  (declare (xargs :verify-guards nil))
  (mv-let (answer st1) (fn2-cns-admit 'ack st p (fn2-cns-may-consume st p) *fn2-cns-record-octets* fault)
    (let* ((problem (or (fn2-cns-scope-problem st p k nil)
                        (and (not (equal (nth 6 k) (fn2-cns-auth st p))) 'rebase-required)))
           (c (fn2-cns-cursor-consumer k))
           (r (fn2-cns-reg st p c)) (to (fn2-cns-cursor-position k))
           (at (and r (fn2-cns-acked st p c (fn2-cns-reg-epoch r)))))
      (cond ((not (eq answer :proceed)) (mv answer st1))
            (problem (mv (list :refused problem) st))
            ((< (fn2-cns-frontier st) to) (mv '(:refused beyond-frontier) st))
            ((< to at) (if (eq fault :rewind)
                           (mv (list :accepted (list to))
                               (fn2-cns-put :acks (fn2-cns-set (list p c (fn2-cns-reg-epoch r)) to (fn2-cns-get :acks st)) st))
                         (mv '(:refused behind) st)))
            ((equal to at) (if (eq fault :equal-behind) (mv '(:refused behind) st) (mv (list :accepted (list to)) st)))
            (t (mv (list :accepted (list to))
                   (fn2-cns-charge (fn2-cns-put :acks (fn2-cns-set (list p c (fn2-cns-reg-epoch r)) to (fn2-cns-get :acks st)) st)
                                   p *fn2-cns-record-octets*)))))))
(defun fn2-cns-position (st p c fault)
  (declare (xargs :verify-guards nil))
  (mv-let (answer st1) (fn2-cns-admit 'position st p (fn2-cns-may-consume st p) 0 fault)
    (let ((r (fn2-cns-reg st p c)))
      (cond ((not (eq answer :proceed)) (mv answer st1))
            ((null r) (mv '(:refused unknown-consumer) st))
            (t (mv (list :accepted (list (fn2-cns-cursor st p c r (fn2-cns-acked st p c (fn2-cns-reg-epoch r))))) st))))))
(defun fn2-cns-status (st p c fault)
  (declare (xargs :verify-guards nil))
  (mv-let (answer st1) (fn2-cns-admit 'status st p (fn2-cns-may-consume st p) 0 fault)
    (let ((r (fn2-cns-reg st p c)))
      (cond ((not (eq answer :proceed)) (mv answer st1))
            ((null r) (mv '(:refused unknown-consumer) st))
            (t (let ((at (fn2-cns-acked st p c (fn2-cns-reg-epoch r))))
                 (mv (list :accepted (list at (fn2-cns-frontier st) (list (- (fn2-cns-frontier st) at)))) st)))))))

;; fetch ------------------------------------------------------------------
; REFERENCE is (MID): the octets under the grants current now, or why not
; (an absent and an unreadable article answer alike).
(defun fn2-cns-fetch (st p reference fault)
  (declare (xargs :verify-guards nil))
  (mv-let (answer st1) (fn2-cns-admit 'fetch st p (fn2-cns-may-consume st p) 0 fault)
    (let* ((mid (car reference)) (log (fn2-cns-get :log st)) (a (fn2-cns-article-of mid log)))
      (cond ((not (eq answer :proceed)) (mv answer st1))
            ((not (and a (fn2-cns-readable (fn2-cns-get :grants st) p (fn2-cns-ev-streams a)))) (mv '(:refused unavailable) st))
            ((fn2-cns-withdrawn-p mid log) (mv '(:refused withdrawn) st))
            ((member (fn2-cns-ev-pos a) (fn2-cns-get :reclaimed st)) (mv '(:refused unavailable) st))
            (t (mv (list :accepted (list (fn2-cns-ev-octets a))) st))))))

;; append -----------------------------------------------------------------
; ARTICLE is (MID OCTETS TO): MID nil asks the node for one, minted from
; (principal, op) so a retry names the same article on every carrier.
(defun fn2-cns-mint (p op pos)
  (declare (xargs :verify-guards nil))
  (if op (concatenate 'string "<op-" (fn2-gram-cat (list p)) "-" (fn2-gram-cat (list op)) "@node>")
    (concatenate 'string "<" (fn2-gram-cat (list pos)) "@node>")))
(defun fn2-cns-append (st p stream article op fault)
  (declare (xargs :verify-guards nil))
  (let* ((octets (cadr article)) (to (caddr article))
         (digest (list stream article))
         (prior (and op (fn2-cns-at (cons p op) (fn2-cns-get :outcomes st)))))
    (mv-let (answer st1) (fn2-cns-admit 'append st p (fn2-cns-allows (fn2-cns-get :grants st) p :append stream)
                                        (length octets) fault)
      (let* ((pos (+ 1 (fn2-cns-frontier st)))
             (mid (or (car article) (fn2-cns-mint p op pos)))
             (old (fn2-cns-article-of mid (fn2-cns-get :log st))))
        (cond ((not (eq answer :proceed)) (mv answer st1))
              ((not (and (stringp stream) (stringp octets) (true-listp to))) (mv '(:refused malformed-article) st))
              ((and prior (not (eq fault :reappend)))
               (if (equal (car prior) digest) (mv (cadr prior) st) (mv '(:refused operation-reused) st)))
              ((< *fn2-cns-max-addressees* (len to)) (mv '(:refused addressees) st))
              ((and old (equal (fn2-cns-ev-octets old) octets)) (mv '(:refused duplicate) st))
              ; IDENTITY ruling 6: the article is refused and its evidence commits.
              (old (mv '(:refused conflict :evidence-committed)
                       (fn2-cns-put :evidence (cons (list mid octets p) (fn2-cns-get :evidence st)) st)))
              (t (let* ((n (+ 1 (nfix (fn2-cns-at stream (fn2-cns-get :numbers st)))))
                        (numbers (list (cons stream n)))
                        (o (list :accepted (list mid pos numbers (list (fn2-cns-get :history st) pos))))
                        (st (fn2-cns-put :log (append (fn2-cns-get :log st)
                                                      (list (list pos :article (list stream) mid octets to p numbers))) st))
                        (st (fn2-cns-put :numbers (fn2-cns-set stream n (fn2-cns-get :numbers st)) st))
                        (st (if op (fn2-cns-put :outcomes (fn2-cns-set (cons p op) (list digest o) (fn2-cns-get :outcomes st)) st) st)))
                   (mv o (fn2-cns-charge st p (length octets))))))))))

;; The world's own steps (not port verbs): an operator's grants and limits, a
;; cancel, a reclamation, a timeout, a crash.
(defun fn2-cns-withdraw (st p mid)
  (declare (xargs :verify-guards nil))
  (let ((a (fn2-cns-article-of mid (fn2-cns-get :log st))))
    (if (and a (equal (nth 6 a) p) (not (fn2-cns-withdrawn-p mid (fn2-cns-get :log st))))
        (fn2-cns-put :log (append (fn2-cns-get :log st)
                                  (list (list (+ 1 (fn2-cns-frontier st)) :withdraw '("control.cancel") mid p))) st)
      st)))

;; One step -----------------------------------------------------------------
; OP is (VERB PRINCIPAL ARG ...). (mv outcome answers state): ANSWERS are the
; parked waits that answered during the step, as ((principal . consumer) . outcome).
(defun fn2-cns-verb-step (op st fault)
  (declare (xargs :verify-guards nil))
  (let ((p (nth 1 op)) (a (nth 2 op)) (b (nth 3 op)) (c (nth 4 op)))
    (case (fn2-cns-class op)
      (register (fn2-cns-register st p a b c fault))
      (rebase (fn2-cns-rebase st p a b c fault))
      (unregister (fn2-cns-unregister st p a fault))
      (read (fn2-cns-read st p a b fault))
      (wait (fn2-cns-wait st p a b fault))
      (ack (fn2-cns-ack st p a fault))
      (position (fn2-cns-position st p a fault))
      (status (fn2-cns-status st p a fault))
      (fetch (fn2-cns-fetch st p a fault))
      (append (fn2-cns-append st p a b c fault))
      (:grant (mv :done (fn2-cns-bump-auth p (fn2-cns-put :grants (cons (list p a b) (fn2-cns-get :grants st)) st))))
      (:revoke (mv :done (fn2-cns-bump-auth p (fn2-cns-put :grants (remove-equal (list p a b) (fn2-cns-get :grants st)) st))))
      (:limit (mv :done (fn2-cns-put :limit (fn2-cns-set p a (fn2-cns-get :limit st)) st)))
      (:withdraw (mv :done (fn2-cns-withdraw st p a)))
      (:reclaim (mv :done (fn2-cns-put :reclaimed (cons a (fn2-cns-get :reclaimed st)) st)))
      (:crash (mv :done (fn2-cns-put :waits nil st)))
      (otherwise (mv '(:refused :no-such-verb) st)))))
(defun fn2-cns-step (op st fault)
  (declare (xargs :verify-guards nil))
  (if (eq (fn2-cns-class op) :timeout)
      (mv-let (answers st2) (fn2-cns-timeout st (nth 1 op) (nth 2 op) fault) (mv :done answers st2))
    (mv-let (o st2) (fn2-cns-verb-step op st fault)
      (mv-let (answers st3) (fn2-cns-wake st2 fault) (mv o answers st3)))))

; A run: the trace ((OP OUTCOME ANSWERS STATE-BEFORE STATE-AFTER) ...) and the final state.
(defun fn2-cns-run (ops st fault)
  (declare (xargs :verify-guards nil))
  (if (atom ops) (mv nil st)
    (mv-let (o answers st2) (fn2-cns-step (car ops) st fault)
      (mv-let (trace st3) (fn2-cns-run (cdr ops) st2 fault)
        (mv (cons (list (car ops) o answers st st2) trace) st3)))))
(defun fn2-cns-final (ops fault)
  (declare (xargs :verify-guards nil))
  (mv-let (trace st) (fn2-cns-run ops (fn2-cns-init "fn2-history" "fn2-incarnation") fault)
    (declare (ignore trace)) st))
(defun fn2-cns-trace (ops fault)
  (declare (xargs :verify-guards nil))
  (mv-let (trace st) (fn2-cns-run ops (fn2-cns-init "fn2-history" "fn2-incarnation") fault)
    (declare (ignore st)) trace))

;; The NNTP view (carrier N): what ARTICLE and GROUP answer over the same log.
(defun fn2-cns-nntp-article (st mid fault)
  (declare (xargs :verify-guards nil))
  (let ((a (fn2-cns-article-of mid (fn2-cns-get :log st))))
    (and a (not (fn2-cns-withdrawn-p mid (fn2-cns-get :log st)))
         (not (member (fn2-cns-ev-pos a) (fn2-cns-get :reclaimed st)))
         (if (eq fault :rerender) (concatenate 'string "X-Fn: rendered" (fn2-cns-ev-octets a)) (fn2-cns-ev-octets a)))))
(defun fn2-cns-nntp-group (group log)
  ; ((number . mid) ...) for GROUP's articles, in number order.
  (declare (xargs :verify-guards nil))
  (cond ((atom log) nil)
        ((and (eq (fn2-cns-ev-kind (car log)) :article) (assoc-equal group (fn2-cns-ev-numbers (car log))))
         (cons (cons (cdr (assoc-equal group (fn2-cns-ev-numbers (car log)))) (fn2-cns-ev-mid (car log)))
               (fn2-cns-nntp-group group (cdr log))))
        (t (fn2-cns-nntp-group group (cdr log)))))

;; The keystones' bodies (e-surface.md section 9) ----------------------------
; A trace entry is (OP OUTCOME ANSWERS STATE-BEFORE STATE-AFTER).
(defun fn2-cns-port-verb (op)
  (declare (xargs :verify-guards nil))
  (and (consp op) (fn2-consumer-verb-p (fn2-cns-class op)) (fn2-cns-class op)))

; K0: every reply the model gives is one the port declares for its verb.
(defun fn2-cns-answers-declared-p (answers)
  (declare (xargs :verify-guards nil))
  (if (atom answers) t
    (and (fn2-consumer-outcome-p 'wait (cdar answers)) (fn2-cns-answers-declared-p (cdr answers)))))
(defun fn2-cns-declared-p (trace)
  (declare (xargs :verify-guards nil))
  (if (atom trace) t
    (let* ((op (nth 0 (car trace))) (o (nth 1 (car trace))) (verb (fn2-cns-port-verb op)))
      (and (or (not verb) (fn2-consumer-outcome-p verb o)
               (and (eq o :parked) (eq (fn2-consumer-verb-effect verb) :park)))
           (fn2-cns-answers-declared-p (nth 2 (car trace)))
           (fn2-cns-declared-p (cdr trace))))))

; K1: the items a chain of pages delivers from the acknowledged position
; through the frontier are exactly the selected events, in order.
(defun fn2-cns-drain (st p k limits fault fuel)
  (declare (xargs :verify-guards nil :measure (nfix fuel)))
  (if (zp fuel) (mv nil nil)
    (let ((o (fn2-cns-page st p k limits fault)))
      (if (not (eq (fn2-cns-class o) :accepted)) (mv nil o)
        (let ((here (strip-cars (fn2-cns-page-items o))))
          (if (not (fn2-cns-page-more o)) (mv here nil)
            (mv-let (rest problem) (fn2-cns-drain st p (fn2-cns-page-next o) limits fault (- fuel 1))
              (mv (append here rest) problem))))))))
(defun fn2-cns-selected-positions (log whole edges grants principal from)
  ; The specification: the events after FROM with a reason, by position.
  (declare (xargs :verify-guards nil))
  (cond ((atom log) nil)
        ((and (< (nfix from) (fn2-cns-ev-pos (car log)))
              (fn2-cns-reasons (car log) edges grants principal whole))
         (cons (fn2-cns-ev-pos (car log)) (fn2-cns-selected-positions (cdr log) whole edges grants principal from)))
        (t (fn2-cns-selected-positions (cdr log) whole edges grants principal from))))
(defun fn2-cns-k1-regs (regs st limits fault)
  (declare (xargs :verify-guards nil))
  (if (atom regs) t
    (let* ((p (caaar regs)) (c (cdaar regs)) (r (cdar regs))
           (k (fn2-cns-cursor st p c r (fn2-cns-acked st p c (fn2-cns-reg-epoch r)))))
      (and (or (not (equal (fn2-cns-reg-vv r) (fn2-cns-auth st p)))
               (mv-let (got problem) (fn2-cns-drain st p k limits fault (+ 2 (fn2-cns-frontier st)))
                 (and (null problem)
                      (equal got (fn2-cns-selected-positions (fn2-cns-get :log st) (fn2-cns-get :log st)
                                                             (fn2-cns-reg-edges r) (fn2-cns-get :grants st) p
                                                             (fn2-cns-acked st p c (fn2-cns-reg-epoch r)))))))
           (fn2-cns-k1-regs (cdr regs) st limits fault)))))
(defun fn2-cns-k1 (st limits fault)
  (declare (xargs :verify-guards nil))
  (fn2-cns-k1-regs (fn2-cns-get :regs st) st limits fault))
; K1 at every state a trace reaches.
(defun fn2-cns-k1-trace (trace limits fault)
  (declare (xargs :verify-guards nil))
  (or (atom trace) (and (fn2-cns-k1 (nth 4 (car trace)) limits fault) (fn2-cns-k1-trace (cdr trace) limits fault))))

; K2: no recorded position ever decreases.
(defun fn2-cns-acks-ge (acks st2)
  (declare (xargs :verify-guards nil))
  (if (atom acks) t
    (and (<= (nfix (cdar acks)) (nfix (fn2-cns-at (caar acks) (fn2-cns-get :acks st2))))
         (fn2-cns-acks-ge (cdr acks) st2))))
(defun fn2-cns-k2 (trace)
  (declare (xargs :verify-guards nil))
  (if (atom trace) t
    (and (fn2-cns-acks-ge (fn2-cns-get :acks (nth 3 (car trace))) (nth 4 (car trace))) (fn2-cns-k2 (cdr trace)))))

; K3: a retried append (same principal, op and request) answers its first
; outcome and adds no article.
(defun fn2-cns-k3 (trace)
  (declare (xargs :verify-guards nil))
  (if (atom trace) t
    (let* ((e (car trace)) (op (nth 0 e)) (st (nth 3 e))
           (prior (and (eq (fn2-cns-class op) 'append) (nth 4 op)
                       (fn2-cns-at (cons (nth 1 op) (nth 4 op)) (fn2-cns-get :outcomes st)))))
      (and (or (not prior) (not (equal (car prior) (list (nth 2 op) (nth 3 op))))
               (and (equal (nth 1 e) (cadr prior))
                    (equal (fn2-cns-get :log (nth 4 e)) (fn2-cns-get :log st))))
           (fn2-cns-k3 (cdr trace))))))

; K4: a parked wait answers what a read gives at the moment it answers.
(defun fn2-cns-answers-are-reads (answers st st2)
  (declare (xargs :verify-guards nil))
  (if (atom answers) t
    (let ((w (fn2-cns-at (caar answers) (fn2-cns-get :waits st))))
      (and w (equal (cdar answers) (fn2-cns-page st2 (car (caar answers)) (car w) (cadr w) nil))
           (fn2-cns-answers-are-reads (cdr answers) st st2)))))
(defun fn2-cns-k4 (trace)
  (declare (xargs :verify-guards nil))
  (if (atom trace) t
    (and (fn2-cns-answers-are-reads (nth 2 (car trace)) (nth 3 (car trace)) (nth 4 (car trace)))
         (fn2-cns-k4 (cdr trace)))))

; K4b: after every step no parked wait has a read that is due: a step that
; makes one due answers it (no lost wake).
(defun fn2-cns-none-due (waits st)
  (declare (xargs :verify-guards nil))
  (if (atom waits) t
    (let ((now (fn2-cns-page st (car (caar waits)) (cadr (car waits)) (caddr (car waits)) nil)))
      (and (eq (fn2-cns-class now) :accepted) (null (fn2-cns-page-items now))
           (fn2-cns-none-due (cdr waits) st)))))
(defun fn2-cns-k4b (trace)
  (declare (xargs :verify-guards nil))
  (if (atom trace) t
    (and (fn2-cns-none-due (fn2-cns-get :waits (nth 4 (car trace))) (nth 4 (car trace))) (fn2-cns-k4b (cdr trace)))))

; K5: an accepted append's article is what the NNTP view serves, exact
; octets, at the numbers the append answered.
(defun fn2-cns-numbers-name (numbers st mid)
  (declare (xargs :verify-guards nil))
  (if (atom numbers) t
    (and (equal (cdr (assoc-equal (cdar numbers) (fn2-cns-nntp-group (caar numbers) (fn2-cns-get :log st)))) mid)
         (fn2-cns-numbers-name (cdr numbers) st mid))))
(defun fn2-cns-k5 (trace fault)
  (declare (xargs :verify-guards nil))
  (if (atom trace) t
    (let* ((e (car trace)) (op (nth 0 e)) (o (nth 1 e)) (st2 (nth 4 e)))
      (and (or (not (and (eq (fn2-cns-class op) 'append) (eq (fn2-cns-class o) :accepted)))
               (let ((mid (car (cadr o))))
                 (and (equal (fn2-cns-nntp-article st2 mid fault) (cadr (nth 3 op)))
                      (fn2-cns-numbers-name (caddr (cadr o)) st2 mid))))
           (fn2-cns-k5 (cdr trace) fault)))))

; K6: whether or not an ack whose reply was lost committed, POSITION answers
; the old or the proposed position and repeating the ack is accepted.
(defun fn2-cns-k6 (trace fault)
  (declare (xargs :verify-guards nil))
  (if (atom trace) t
    (let* ((e (car trace)) (op (nth 0 e)) (st (nth 3 e)) (st2 (nth 4 e)))
      (and (or (not (and (eq (fn2-cns-class op) 'ack) (eq (fn2-cns-class (nth 1 e)) :accepted)))
               (let* ((p (nth 1 op)) (k (nth 2 op)) (c (fn2-cns-cursor-consumer k)) (to (fn2-cns-cursor-position k)))
                 (mv-let (again st3) (fn2-cns-ack st2 p k fault)
                   (declare (ignore st3))
                   (mv-let (pos-new st4) (fn2-cns-position st2 p c fault)
                     (declare (ignore st4))
                     (mv-let (pos-old st5) (fn2-cns-position st p c fault)
                       (declare (ignore st5))
                       (and (equal again (list :accepted (list to)))
                            (equal (fn2-cns-cursor-position (car (cadr pos-new))) to)
                            (<= (fn2-cns-cursor-position (car (cadr pos-old))) to)))))))
           (fn2-cns-k6 (cdr trace) fault)))))

; K7: every item a page delivers is readable by its principal under the
; grants current when the page is answered.
(defun fn2-cns-event-at (pos log)
  (declare (xargs :verify-guards nil))
  (cond ((atom log) nil) ((equal (fn2-cns-ev-pos (car log)) pos) (car log)) (t (fn2-cns-event-at pos (cdr log)))))
(defun fn2-cns-items-allowed (items p st)
  (declare (xargs :verify-guards nil))
  (if (atom items) t
    (let* ((log (fn2-cns-get :log st)) (e (fn2-cns-event-at (fn2-cns-item-pos (car items)) log))
           (a (if (eq (fn2-cns-ev-kind e) :withdraw) (fn2-cns-article-of (fn2-cns-ev-mid e) log) e)))
      (and a (fn2-cns-readable (fn2-cns-get :grants st) p (fn2-cns-ev-streams a))
           (fn2-cns-items-allowed (cdr items) p st)))))
(defun fn2-cns-answers-allowed (answers st)
  (declare (xargs :verify-guards nil))
  (if (atom answers) t
    (and (fn2-cns-items-allowed (fn2-cns-page-items (cdar answers)) (car (caar answers)) st)
         (fn2-cns-answers-allowed (cdr answers) st))))
(defun fn2-cns-k7 (trace)
  (declare (xargs :verify-guards nil))
  (if (atom trace) t
    (let* ((e (car trace)) (op (nth 0 e)))
      (and (or (not (member (fn2-cns-class op) '(read wait))) (fn2-cns-items-allowed (fn2-cns-page-items (nth 1 e)) (nth 1 op) (nth 3 e)))
           (fn2-cns-answers-allowed (nth 2 e) (nth 4 e))
           (fn2-cns-k7 (cdr trace))))))

; K8: a refused verb changes nothing, but for the conflict evidence that
; IDENTITY ruling 6 commits beside an article's refusal.
(defun fn2-cns-k8 (trace)
  (declare (xargs :verify-guards nil))
  (if (atom trace) t
    (let* ((e (car trace)) (o (nth 1 e)))
      (and (or (not (and (fn2-cns-port-verb (nth 0 e)) (consp o) (eq (fn2-cns-class o) :refused)))
               (equal (fn2-cns-put :evidence nil (nth 4 e)) (fn2-cns-put :evidence nil (nth 3 e))))
           (fn2-cns-k8 (cdr trace))))))
