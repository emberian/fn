; Layer E's scenarios (e-surface.md sections 9, 14; ROUND2 F scenarios 7-9):
; the consumer port's K0-K8 fixtures as wire scenarios, each run by a client
; speaking FNCT frames to a node and checked by CONSUMER
; (sim/check-consumer.lisp) over the observations.
;
; The node here is the oracle: the reference model answering through the
; checker's renderer, every mutation linearized at its request, every due
; parked wait answered at the step that made it due. It shows the scenarios,
; the client and the checker agree with the model, and its controls show the
; checker refuses a wrong node. The served node is the simulator running
; fn2-ctl and fn2-cns at the L carrier: the same scripts, the client's
; frames as a :local connection's input, the replies from its output, and
; the readings from the consumer-cursor fold (fn2-read-lookup) and the
; :wait-row holdings. That adapter lands with the kinds (A's :local listener,
; D's :consumer transaction), and K10 (owed-consumer.lisp) is CONSUMER over
; its observations.
(in-package "ACL2")
(include-book "../sim/check-consumer")
(include-book "std/testing/assert-bang" :dir :system)

(defun sle-o (s) (declare (xargs :verify-guards nil)) (fn2-cnsk-octets s))
(defconst *sle-history* (fn2-cnsk-octets "fn2-history"))
(defconst *sle-incarnation* (fn2-cnsk-octets "fn2-incarnation"))
(defconst *sle-mini* (fn2-cnsk-octets "mini"))
(defconst *sle-origin* (fn2-cnsk-octets "origin"))
(defconst *sle-group* "dregg.fn.e1")
(defconst *sle-interims* '(append fetch rebase unregister register-groups))

;; The client: a request's fields from the script, with the cursors it holds.
; MEM ((C . (CURSOR . NEXT)) ...): the last cursor a register or position
; answered for consumer C, and the last page's next cursor.
(defun sle-arg (v mem)
  (declare (xargs :verify-guards nil))
  (cond ((and (consp v) (eq (car v) :cursor-of)) (fn2-fncu-encode (car (cdr (assoc-equal (sle-o (cadr v)) mem)))))
        ((and (consp v) (eq (car v) :next-of)) (fn2-fncu-encode (cdr (cdr (assoc-equal (sle-o (cadr v)) mem)))))
        ((and (consp v) (eq (car v) :streams)) (fn2-cnsk-names-octets (cdr v)))
        ((stringp v) (sle-o v))
        (t v)))
(defun sle-alist (spec mem)
  (declare (xargs :verify-guards nil))
  (if (atom spec) nil (cons (cons (caar spec) (sle-arg (cdar spec) mem)) (sle-alist (cdr spec) mem))))
(defun sle-frame (word spec mem)
  (declare (xargs :verify-guards nil))
  (fn2-fnct-seal *fn2-fnct-request-kind* (fn2-fnct-request-encode word (sle-alist spec mem))))
(defun sle-remember (c verb answer mem)
  ; A register or position answers the cursor; a page answers its next.
  (declare (xargs :verify-guards nil))
  (let ((held (cdr (assoc-equal c mem))))
    (cond ((not (eq (car answer) :accepted)) mem)
          ((member-eq verb '(register position)) (put-assoc-equal c (cons (nth 2 answer) (cdr held)) mem))
          ((member-eq verb '(read wait)) (put-assoc-equal c (cons (car held) (nth 1 (nth 2 answer))) mem))
          (t mem))))

;; The oracle node. PENDING ((CONN VERB FORM OP C) ...) holds parked waits.
(defun sle-answer (verb form op st)
  (declare (xargs :verify-guards nil))
  (mv-let (o st2) (fn2-cns-verb-step op st nil) (mv (fn2-cnsk-render verb form o op st2) st2)))
(defun sle-due (a) (declare (xargs :verify-guards nil)) (or (not (eq (car a) :accepted)) (< 0 (nfix (nth 2 (nth 2 a))))))
(defun sle-wake (pending st mem obs)
  ; Answer every parked wait whose read is due: (mv pending mem obs).
  (declare (xargs :verify-guards nil))
  (if (atom pending) (mv nil mem obs)
    (b* (((list conn verb form op c) (car pending))
         ((mv a &) (sle-answer verb form op st))
         ((mv rest mem obs) (sle-wake (cdr pending) st mem obs)))
      (if (sle-due a)
          (mv rest (sle-remember c verb a mem) (cons (list :reply conn (fn2-cnsk-encode-reply verb form a)) obs))
        (mv (cons (car pending) rest) mem obs)))))
(defun sle-held (p pending)
  (declare (xargs :verify-guards nil))
  (cond ((atom pending) 0) ((equal (nth 1 (nth 3 (car pending))) p) (+ 1 (sle-held p (cdr pending))))
        (t (sle-held p (cdr pending)))))
(defun sle-holdings (ps pending)
  (declare (xargs :verify-guards nil))
  (if (atom ps) nil (cons (list (car ps) (sle-held (car ps) pending)) (sle-holdings (cdr ps) pending))))
(defun sle-drop-conn (conn pending)
  (declare (xargs :verify-guards nil))
  (cond ((atom pending) nil) ((equal (caar pending) conn) (sle-drop-conn conn (cdr pending)))
        (t (cons (car pending) (sle-drop-conn conn (cdr pending))))))

; One script step: (mv st pending conns mem obs), OBS reversed.
(defun sle-step (s st pending conns mem obs)
  (declare (xargs :verify-guards nil))
  (case (car s)
    (:connect (mv st pending (put-assoc-equal (nth 1 s) (nth 2 s) conns) mem (cons s obs)))
    (:send
     (b* (((list & conn word spec deliver) s)
          (p (cdr (assoc-equal conn conns)))
          (frame (sle-frame word spec mem))
          (obs (cons (list :request conn frame) obs))
          (r (fn2-cnsk-request frame p *sle-interims*))
          (c (or (cdr (assoc-eq 'consumer (sle-alist spec mem)))
                 (let ((v (cdr (assoc-eq 'cursor spec)))) (and (consp v) (sle-o (cadr v)))))))
       (if (eq (car r) :answer)
           (mv st pending conns mem
               (if deliver (cons (list :reply conn (fn2-cnsk-encode-reply (nth 1 r) (nth 2 r) (nth 3 r))) obs) obs))
         (b* (((list & verb form op) r)
              ((mv a st2) (sle-answer verb form op st))
              ((when (and (eq verb 'wait) (not (sle-due a))))
               (mv st2 (cons (list conn verb form op c) pending) conns mem obs)))
           (cond ((eq deliver :lose) (mv st2 pending conns mem (cons (list :close conn) obs)))
                 (t (mv st2 pending conns (sle-remember c verb a mem)
                        (cons (list :reply conn (fn2-cnsk-encode-reply verb form a)) obs))))))))
    (:timeout
     (b* ((e (assoc-equal (nth 1 s) pending))
          ((unless e) (mv st pending conns mem obs))
          ((list conn verb form op c) e)
          ((mv a &) (sle-answer verb form op st)))
       (mv st (sle-drop-conn conn pending) conns (sle-remember c verb a mem)
           (cons (list :reply conn (fn2-cnsk-encode-reply verb form a)) obs))))
    (:world
     (b* ((op (nth 1 s))
          (crash (eq (car op) :crash))
          (next (car (fn2-cnsk-world op (list (list st nil nil)))))
          (st2 (if next (car next) st))
          (pending (if crash nil pending))
          (conns (if crash nil conns))
          (obs (cons s obs))
          ((mv pending mem obs) (sle-wake pending st2 mem obs)))
       (mv st2 pending conns mem obs)))
    (:publish
     (b* ((next (car (fn2-cnsk-publish (nth 1 s) (list (list st nil nil)))))
          (st2 (if next (car next) st))
          ((mv pending mem obs) (sle-wake pending st2 mem (cons s obs))))
       (mv st2 pending conns mem obs)))
    (:ledger (mv st pending conns mem
                 (cons (list :ledger (fn2-cnsk-cursor-rows (fn2-cns-get :regs st) st) (sle-holdings (nth 1 s) pending)) obs)))
    (:settle (mv st pending conns mem (cons (list :settled (sle-holdings (nth 1 s) pending)) obs)))
    (otherwise (mv st pending conns mem obs))))
(defun sle-run-steps (script st pending conns mem obs)
  (declare (xargs :verify-guards nil))
  (if (atom script) (reverse obs)
    (mv-let (st pending conns mem obs) (sle-step (car script) st pending conns mem obs)
      (sle-run-steps (cdr script) st pending conns mem obs))))
(defun sle-observe (script)
  (declare (xargs :verify-guards nil))
  (sle-run-steps script (fn2-cns-init *sle-history* *sle-incarnation*) nil nil nil nil))
(defun sle-check (obs)
  (declare (xargs :verify-guards nil))
  (fn2-consumer-check obs *sle-history* *sle-incarnation* *sle-interims*))

;; The scenarios --------------------------------------------------------------------
(defconst *sle-grants*
  `((:world (:grant ,*sle-mini* :consume :any)) (:world (:grant ,*sle-mini* :read ,*sle-group*))
    (:world (:grant ,*sle-origin* :append ,*sle-group*))))
(defun sle-post (n pos)
  (declare (xargs :verify-guards nil))
  (list :world (list :post *sle-origin* *sle-group*
                     (list (concatenate 'string "<r" (fn2-gram-cat (list n)) "@origin>")
                           (concatenate 'string "report " (fn2-gram-cat (list n))) (list *sle-mini*))
                     pos)))
(defun sle-posts (n from pos)
  (declare (xargs :verify-guards nil :measure (nfix n)))
  (if (zp n) nil (cons (sle-post from pos) (sle-posts (- n 1) (+ 1 from) (+ 1 pos)))))
(defconst *sle-register*
  '(:send 1 :register-query ((consumer . "c1") (streams :streams (:addr nil)) (start . 0)) t))
; The register's "@" is the principal's own addr stream whatever the script's P.
(defconst *sle-mini-ps* (list *sle-mini*))

; Scenario 7 (K4, K1, K2): a wait parks, an addressed report wakes it, Mini
; acknowledges the page's next, POSITION answers it.
(defconst *sle-wait*
  (append *sle-grants*
          `((:connect 1 ,*sle-mini*) ,*sle-register* (:publish 1)
            (:send 1 :wait-cursor ((cursor :cursor-of "c1") (max-items . 8) (max-octets . 65536) (seconds . 30)) t)
            (:ledger ,*sle-mini-ps*)
            ,(sle-post 1 2) (:publish 2) (:ledger ,*sle-mini-ps*)
            (:send 1 :ack ((cursor :next-of "c1")) t) (:publish 3)
            (:send 1 :position ((consumer . "c1")) t)
            (:ledger ,*sle-mini-ps*) (:settle ,*sle-mini-ps*))))
; K6: the ack's reply is lost; a new connection's POSITION settles it and the
; same ack again is accepted; a stale ack is behind (K2); an ack beyond the
; frontier is refused and changes nothing (K8).
(defconst *sle-lost-ack*
  (append *sle-grants*
          `((:connect 1 ,*sle-mini*) ,*sle-register* (:publish 1) ,(sle-post 1 2) (:publish 2)
            (:send 1 :read ((cursor :cursor-of "c1") (max-items . 8) (max-octets . 65536)) t)
            (:send 1 :ack ((cursor :next-of "c1")) :lose) (:publish 3)
            (:connect 2 ,*sle-mini*) (:send 2 :position ((consumer . "c1")) t)
            (:send 2 :ack ((cursor :next-of "c1")) t)
            (:send 2 :ack ((cursor :cursor-of "c1")) t)
            (:ledger ,*sle-mini-ps*) (:settle ,*sle-mini-ps*))))
; K1: six reports, pages of four: the first page says more, the ack of its
; next and the second page deliver the rest, none skipped.
(defconst *sle-pages*
  (append *sle-grants*
          `((:connect 1 ,*sle-mini*) ,*sle-register* (:publish 1)) (sle-posts 6 1 2)
          `((:publish 7)
            (:send 1 :read ((cursor :cursor-of "c1") (max-items . 4) (max-octets . 65536)) t)
            (:send 1 :ack ((cursor :next-of "c1")) t) (:publish 8)
            (:send 1 :position ((consumer . "c1")) t)
            (:send 1 :read ((cursor :cursor-of "c1") (max-items . 4) (max-octets . 65536)) t)
            (:ledger ,*sle-mini-ps*) (:settle ,*sle-mini-ps*))))
; Scenario 8: a crash under a parked wait; after it the report is read, and a
; revocation makes the old cursor answer rebase-required (K7); the interim
; verbs answer unavailable.
(defconst *sle-crash*
  (append *sle-grants*
          `((:connect 1 ,*sle-mini*) ,*sle-register* (:publish 1)
            (:send 1 :wait-cursor ((cursor :cursor-of "c1") (max-items . 8) (max-octets . 65536) (seconds . 30)) t)
            (:world (:crash)) ,(sle-post 1 2) (:publish 2)
            (:connect 2 ,*sle-mini*)
            (:send 2 :read ((cursor :cursor-of "c1") (max-items . 8) (max-octets . 65536)) t)
            (:world (:revoke ,*sle-mini* :read ,*sle-group*))
            (:send 2 :read ((cursor :cursor-of "c1") (max-items . 8) (max-octets . 65536)) t)
            (:send 2 :fetch ((message-id . "<r1@origin>") (domain . 0) (position . 2)) t)
            (:ledger ,*sle-mini-ps*) (:settle ,*sle-mini-ps*))))
; Scenario 9: a parked wait times out on an empty page.
(defconst *sle-timeout*
  (append *sle-grants*
          `((:connect 1 ,*sle-mini*) ,*sle-register* (:publish 1)
            (:send 1 :wait-cursor ((cursor :cursor-of "c1") (max-items . 8) (max-octets . 65536) (seconds . 1)) t)
            (:ledger ,*sle-mini-ps*) (:timeout 1) (:settle ,*sle-mini-ps*))))
(defconst *sle-scenarios*
  (list (cons :wait *sle-wait*) (cons :lost-ack *sle-lost-ack*) (cons :pages *sle-pages*)
        (cons :crash *sle-crash*) (cons :timeout *sle-timeout*)))

;; Controls: a wrong node, each caught --------------------------------------------
(defun sle-replies (obs)
  (declare (xargs :verify-guards nil))
  (cond ((atom obs) nil) ((eq (caar obs) :reply) (cons (car obs) (sle-replies (cdr obs)))) (t (sle-replies (cdr obs)))))
(defun sle-replace (old new obs)
  (declare (xargs :verify-guards nil))
  (cond ((atom obs) nil) ((equal (car obs) old) (append (and new (list new)) (cdr obs)))
        (t (cons (car obs) (sle-replace old new (cdr obs))))))
(defun sle-page-reply (replies)
  ; The first reply that is a page with items.
  (declare (xargs :verify-guards nil))
  (if (atom replies) nil
    (let ((a (fn2-cnsk-decode-reply 'read :k28 (nth 2 (car replies)))))
      (if (and (eq (car a) :accepted) (consp (nth 2 a)) (natp (nth 2 (nth 2 a))) (< 0 (nth 2 (nth 2 a))))
          (car replies) (sle-page-reply (cdr replies))))))
(defun sle-skip-item (obs)
  ; A page whose last item is dropped (the model's :skip, on the wire).
  (declare (xargs :verify-guards nil))
  (let* ((r (sle-page-reply (sle-replies obs))) (a (fn2-cnsk-decode-reply 'read :k28 (nth 2 r)))
         (page (nth 2 a)) (items (nth 3 page))
         (bad (list (nth 0 page) (nth 1 page) (- (nth 2 page) 1) (take (- (len items) 1) items))))
    (sle-replace r (list :reply (nth 1 r) (fn2-cnsk-encode-reply 'read :k28 (list :accepted nil bad))) obs)))
(defun sle-uncertain-read (obs)
  (declare (xargs :verify-guards nil))
  (let ((r (sle-page-reply (sle-replies obs))))
    (sle-replace r (list :reply (nth 1 r) (fn2-cnsk-encode-reply 'read :k28 '(:uncertain nil nil))) obs)))
;; the ledgers, and the observations through one
(defun sle-ledgers (obs)
  (declare (xargs :verify-guards nil))
  (cond ((atom obs) nil) ((eq (caar obs) :ledger) (cons (car obs) (sle-ledgers (cdr obs)))) (t (sle-ledgers (cdr obs)))))
(defun sle-upto (x obs)
  (declare (xargs :verify-guards nil))
  (cond ((atom obs) nil) ((equal (car obs) x) (list x)) (t (cons (car obs) (sle-upto x (cdr obs))))))
(defun sle-rewind-ledger (obs)
  ; The last ledger reading's cursor one position behind (the model's :rewind, read back).
  (declare (xargs :verify-guards nil))
  (let* ((l (car (last (sle-ledgers obs)))) (row (car (nth 1 l))))
    (sle-replace l (list :ledger (cons (update-nth 3 (- (nth 3 row) 1) row) (cdr (nth 1 l))) (nth 2 l)) obs)))
(defun sle-lose-wake (obs)
  ; Scenario 7 through the post that wakes the wait, whose reply never comes
  ; (the model's :lost-wake on the wire): the settle finds a due wait.
  (declare (xargs :verify-guards nil))
  (let ((r (cadr (sle-replies obs))))
    (append (sle-replace r nil (sle-upto r obs))
            (list '(:publish 2) (list :settled (list (list *sle-mini* 1)))))))
(defun sle-leak (obs)
  ; A wait-row still held after every wait answered.
  (declare (xargs :verify-guards nil))
  (append (butlast obs 1) (list (list :settled (list (list *sle-mini* 1))))))

;; What each scenario exercised (the runs pass because they do these things) --
; Every reply read as a page: (MORE COUNT) for an accepted page, the word for a refusal.
(defun sle-shape (rs)
  (declare (xargs :verify-guards nil))
  (if (atom rs) nil
    (let* ((a (fn2-cnsk-decode-reply 'read :k28 (nth 2 (car rs))))
           (page (and (eq (car a) :accepted) (nth 2 a)))
           (s (cond ((and (consp page) (natp (car page)) (consp (cdr page)) (eq (car (nth 1 page)) :cursor))
                     (list (car page) (nth 2 page)))
                    ((eq (car a) :refused) (fn2-cnsk-string (nth 1 a)))
                    (t nil))))
      (if s (cons s (sle-shape (cdr rs))) (sle-shape (cdr rs))))))
(defun sle-shapes (ss)
  (declare (xargs :verify-guards nil))
  (if (atom ss) nil
    (cons (cons (caar ss) (sle-shape (sle-replies (sle-observe (cdar ss))))) (sle-shapes (cdr ss)))))
(defun sle-verdicts (ss)
  (declare (xargs :verify-guards nil))
  (if (atom ss) nil (cons (cons (caar ss) (sle-check (sle-observe (cdar ss)))) (sle-verdicts (cdr ss)))))
(defun sle-fail-word (v) (declare (xargs :verify-guards nil)) (and (consp v) (eq (car v) :fail) (cadr v)))

; The oracle node passes CONSUMER on every scenario, and each scenario did
; what it is for: scenario 7's wait answered one report; pages of four
; delivered four then two, the first saying more; after the crash the report
; was read, then the revocation answered rebase-required and fetch its
; interim; the wait on nothing timed out on an empty page.
(defun fn2-sle-test-oracle ()
  (declare (xargs :verify-guards nil))
  (and (equal (sle-verdicts *sle-scenarios*)
              '((:wait . :pass) (:lost-ack . :pass) (:pages . :pass) (:crash . :pass) (:timeout . :pass)))
       (equal (sle-shapes *sle-scenarios*)
              '((:wait (0 1)) (:lost-ack (0 1)) (:pages (1 4) (0 2))
                (:crash (0 1) "rebase-required" "unavailable") (:timeout (0 0))))))
; A wrong node, each caught for its own reason: a page that drops its last
; item, a read answered uncertain, a cursor read back behind its ack, a woken
; wait that never answers (K4b), a wait-row held with no wait.
(defun fn2-sle-test-controls ()
  (declare (xargs :verify-guards nil))
  (equal (list (sle-fail-word (sle-check (sle-skip-item (sle-observe *sle-pages*))))
               (sle-fail-word (sle-check (sle-uncertain-read (sle-observe *sle-pages*))))
               (sle-fail-word (sle-check (sle-rewind-ledger (sle-observe *sle-wait*))))
               (sle-fail-word (sle-check (sle-lose-wake (sle-observe *sle-wait*))))
               (sle-fail-word (sle-check (sle-leak (sle-observe *sle-wait*)))))
         '(:reply :reply :ledger :lost-wake :settled-holding)))
(assert! (fn2-sle-test-oracle))
(assert! (fn2-sle-test-controls))
