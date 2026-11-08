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
(include-book "../books/cns")
(include-book "fnct-client")

;; End-to-end turn test (Brick F6): drive fn2-ctl and fn2-cns through fn2-turn
;; and the adapter loop (fn2-cw-loop). Placed in an encapsulate before
;; sim/check-consumer so assembly-callbacks-e-cns's fn2-cns-run does not
;; collide in the global namespace with consumer-model's fn2-cns-run.
(encapsulate ()
  (local (include-book "../books/owed-conn"))
  (local (include-book "../books/owed-cursor"))
  (local (include-book "../books/assembly-attach"))
  (local
   (defconst *fn2-sle-turn-profile*
     (put-assoc-equal :cns 2
       (put-assoc-equal :control-connections 2
         (put-assoc-equal :identity-overlays 32
           (put-assoc-equal :identity-arena-bytes 4096
             (put-assoc-equal :pool-classes '((8 . 1024) (64 . 4096) (16 . 65536)) *fn2-conn-wire-profile*)))))))
  (local
   (defun fn2-sle-set-published (pos fn2-core)
     (declare (xargs :stobjs fn2-core :verify-guards nil))
     (stobj-let ((fn2-id-engine (fn2-core-id-engine fn2-core)))
       (fn2-id-engine)
       (fn2-id-engine-set-published 0 pos fn2-id-engine)
       fn2-core)))
  (local
   (defun fn2-sle-wake-stream (stream pos fn2-core)
     (declare (xargs :stobjs fn2-core :verify-guards nil))
     (stobj-let ((fn2-cns-edges (fn2-core-cns-edges fn2-core)))
       (fn2-cns-edges)
       (fn2-cns-wake-stream stream pos fn2-cns-edges)
       fn2-core)))
  (local
   (defun fn2-sle-seed-article (principal stream art pos fn2-core)
     (declare (xargs :stobjs fn2-core :verify-guards nil))
     (b* (((mv & fn2-core) (fn2-successor-release 0 fn2-core))
          ((mv c0 fn2-core)
           (fn2-addr-put 0 0 (principal principal) (position pos) (article art) (stream stream) (reasons 1) fn2-core))
          ((unless (eq c0 :ok)) fn2-core)
          ((mv rc fn2-core) (fn2-cns-resolve-loop 32 0 fn2-core))
          ((unless (eq rc :ok)) fn2-core)
          ((mv scode & fn2-core) (fn2-successor-stage 0 fn2-core))
          ((unless (eq scode :ok)) fn2-core)
          ((mv bcode fn2-core) (fn2-successor-bind 0 pos pos fn2-core))
          ((unless (eq bcode :ok)) fn2-core)
          ((mv pcode fn2-core) (fn2-succ-core-publish pos fn2-core))
          ((unless (eq pcode :ok)) fn2-core)
          ((mv & fn2-core) (fn2-cns-core-stream-wake pos fn2-core))
          ((mv & fn2-core) (fn2-successor-release 0 fn2-core)))
       fn2-core)))
  (local
   (defun fn2-sle-cat (frames)
     (declare (xargs :verify-guards nil))
     (if (atom frames) nil (append (car frames) (fn2-sle-cat (cdr frames))))))
  (local
   (defun fn2-sle-lens (frames)
     (declare (xargs :verify-guards nil))
     (if (atom frames) nil (cons (len (car frames)) (fn2-sle-lens (cdr frames))))))
  (local
   (defun fn2-sle-test-turn-read-and-stop ()
     (declare (xargs :verify-guards nil))
     (with-local-stobj fn2-core
       (mv-let (ok fn2-core)
         (b* ((fn2-core (fn2-init-executor *fn2-sle-turn-profile* :echo nil fn2-core))
              (fn2-core (fn2-sle-set-published 3 fn2-core))
              (fn2-core (fn2-listener-take-credit *fn2-ctl-admission-ordinal* fn2-core))
              ((mv acode fn2-core) (fn2-machine-admit-fn2-ctl 0 77 3 0 fn2-core))
              ((unless (eq acode :ok)) (mv nil fn2-core))
              ((mv wake fn2-core) (fn2-machine-take-wake fn2-core))
              (fn2-core (fn2-exec-wake wake fn2-core))
              ;; pause and resume (kind 1, each answered by its posture in
              ;; kind 2), a read of consumer 1's cursor at 0 arriving in two
              ;; receives (the first a prefix: the frame waits for the rest;
              ;; nothing recorded, so the page walks from 0 to the published 3 and,
              ;; no addr entry of the principal's there, holds no item),
              ;; then stop (closed, no reply)
              (pause (fnc-control 2)) (resume (fnc-control 3))
              (read (fnc-read (fnc-issued 1 0 0 1 0) 8))
              (stop (fnc-control 5))
              (clients (list (list (append pause resume read stop)
                                   (list (len pause) (len resume) 20 (- (len read) 20) (len stop)) nil nil)))
              ((mv status clients & fn2-core) (fn2-cw-loop 200 0 1 clients nil fn2-core))
              (res (car (fn2-cw-results clients)))
              (wire (car res))
              (closed (cadr res)))
           (mv (and (eq status :quiet)
                    (equal (fn2-core-stop-reason fn2-core) 0)
                    (equal (fnc-replies '(control control read) wire)
                           '((:posture 1) (:posture 0) (:accepted "" (0 3 0 nil))))
                    (equal (len (fnc-replies '(control control read read) wire)) 3)
                    (eq closed t))
               fn2-core))
         ok))))
  (local
   (defun fn2-sle-test-turn-wait-wake ()
     (declare (xargs :verify-guards nil))
     (with-local-stobj fn2-core
       (mv-let (ok fn2-core)
         (b* ((fn2-core (fn2-init-executor *fn2-sle-turn-profile* :echo nil fn2-core))
              (fn2-core (fn2-listener-take-credit *fn2-ctl-admission-ordinal* fn2-core))
              ((mv acode fn2-core) (fn2-machine-admit-fn2-ctl 0 77 3 0 fn2-core))
              ((unless (eq acode :ok)) (mv nil fn2-core))
              ((mv wake fn2-core) (fn2-machine-take-wake fn2-core))
              (fn2-core (fn2-exec-wake wake fn2-core))
              (wait (fnc-wait (fnc-issued 1 0 0 1 0) 8 30))
              (clients (list (list wait (list (len wait)) nil nil)))
              ((mv status1 clients & fn2-core) (fn2-cw-loop 100 0 1 clients nil fn2-core))
              (wire1 (car (car (fn2-cw-results clients))))
              ((unless (and (eq status1 :quiet) (null wire1) (equal (fn2-core-stop-reason fn2-core) 0)))
               (mv nil fn2-core))
              (fn2-core (fn2-sle-set-published 1 fn2-core))
              (fn2-core (fn2-sle-wake-stream 0 1 fn2-core))
              ((mv status2 clients & fn2-core) (fn2-cw-loop 100 0 1 clients nil fn2-core))
              (wire2 (car (car (fn2-cw-results clients)))))
           (mv (and (eq status2 :quiet)
                    (equal (fn2-core-stop-reason fn2-core) 0)
                    (equal (fnc-replies '(wait) wire2) '((:accepted "" (0 1 0 nil)))))
               fn2-core))
         ok))))
  (local
   (defun fn2-sle-test-turn-full-verbs ()
     (declare (xargs :verify-guards nil))
     (with-local-stobj fn2-core
       (mv-let (ok fn2-core)
         (b* ((fn2-core (fn2-init-executor *fn2-sle-turn-profile* :echo nil fn2-core))
              ;; register and the advancing ack are B members: B's writer epoch begun
              ((mv & fn2-core)
               (stobj-let ((fn2-extents (fn2-core-extents fn2-core))) (code fn2-extents)
                 (fn2-alloc-begin-epoch 1 fn2-extents) (mv code fn2-core)))
              (fn2-core (fn2-listener-take-credit *fn2-ctl-admission-ordinal* fn2-core))
              ((mv acode fn2-core) (fn2-machine-admit-fn2-ctl 0 77 3 0 fn2-core))
              ((unless (eq acode :ok)) (mv nil fn2-core))
              ((mv wake fn2-core) (fn2-machine-take-wake fn2-core))
              (fn2-core (fn2-exec-wake wake fn2-core))
              ;; Phase 1: register (consumer 1 from :history) then wait on the
              ;; cursor it issues, followed by Phase 2's post-wake verbs (read,
              ;; ack, dup-ack, behind-ack, beyond-frontier-ack, position,
              ;; status, read-after-ack, stop): each frame its own chunk. The
              ;; wait parks while fn2-ctl is in :waiting, so Phase 1 stops at
              ;; :quiet right after it parks, before the remaining chunks.
              (c (fnc-issued 1 0 1 1 0))
              (frames (list (fnc-register 1 1) (fnc-wait c 8 30) (fnc-read c 8) (fnc-ack c 2) (fnc-ack c 2)
                            (fnc-ack c 1) (fnc-ack c 9) (fnc-position 1) (fnc-status 1) (fnc-read c 8)
                            (fnc-control 5)))
              (clients (list (list (fn2-sle-cat frames) (fn2-sle-lens frames) nil nil)))
              ((mv status1 clients & fn2-core) (fn2-cw-loop 200 0 1 clients nil fn2-core))
              (wire1 (car (car (fn2-cw-results clients))))
              ((unless (and (eq status1 :quiet)
                            (equal (fn2-core-stop-reason fn2-core) 0)
                            (equal (fnc-replies '(register) wire1) '((:accepted "" 0)))
                            ;; the register's cursor is the issued one (version 1, epoch 1, at 0)
                            (equal (fnc-reply-cursor 'register wire1) c)))
               (mv nil fn2-core))
              ;; Phase 2: post/publish article 1 at commit position 2 on stream 0, waking parked wait,
              ;; which then answers the wait and drains the remaining verbs through stop.
              ;; Its addr entry's stream (1, the group it is filed through) is not
              ;; its principal (0): the wake is the principal's own addr stream.
              ;; No article row stands behind the seeded entry, so its item is a
              ;; gap (the article reclaimed) with no Message-ID.
              (fn2-core (fn2-sle-seed-article 0 1 1 2 fn2-core))
              ((mv status2 clients & fn2-core) (fn2-cw-loop 800 0 1 clients nil fn2-core))
              (res2 (car (fn2-cw-results clients)))
              (wire2 (car res2))
              (closed2 (cadr res2)))
           (mv (and (eq status2 :quiet)
                    (equal (fn2-core-stop-reason fn2-core) 0)
                    (equal (fnc-replies '(register wait read ack ack ack ack position status read) wire2)
                           '((:accepted "" 0)
                             (:accepted "" (0 2 1 ((:gap 2 "" nil))))
                             (:accepted "" (0 2 1 ((:gap 2 "" nil))))
                             (:accepted "" 2)
                             (:accepted "" 2)
                             (:refused "behind" nil)
                             (:refused "beyond-frontier" nil)
                             (:accepted "" 2)
                             (:accepted "" (2 2 0))
                             (:accepted "" (0 2 0 nil))))
                    (eq closed2 t))
               fn2-core))
         ok))))
  ;; The listener admits by peer family (D 4.5, E's carrier L): with
  ;; :listener-local-target fn2-ctl a :local Accept is admitted into fn2-ctl
  ;; (one of its control credits taken) and an :inet one into fn2-conn (no
  ;; control credit); without the key a :local Accept is fn2-conn's too, the
  ;; hypothesis-removal witness. (CTL-CREDITS-TAKEN CONN-CREDITS) after the
  ;; Accept's turn.
  (local (include-book "../books/owed-host"))
  ;; turns until one does nothing (at most FUEL): the Accept's harvest and
  ;; the admission take as many turns as the calendar's kinds need
  (local
   (defun fn2-sle-quiet (fuel fn2-core)
     (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix fuel)))
     (if (zp fuel) fn2-core
       (mv-let (status nobs nvisits nactions fn2-core) (fn2-turn fn2-core)
         (declare (ignore status))
         (if (and (equal nobs 0) (equal nvisits 0) (equal nactions 0)) fn2-core
           (fn2-sle-quiet (- fuel 1) fn2-core))))))
  (local
   (defun fn2-sle-admit-run (profile family w0)
     (declare (xargs :verify-guards nil))
     (with-local-stobj fn2-core
       (mv-let (r fn2-core)
         (b* ((fn2-core (fn2-init-executor profile :echo nil fn2-core))
              (ctl0 (fn2-machine-admission-credits *fn2-ctl-admission-ordinal* fn2-core))
              ((mv found op opgen & fn2-core) (fn2-ah-take-accept 8 fn2-core))
              ((unless found) (mv :no-accept fn2-core))
              (fn2-core (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (fn2-ops)
                          (fn2-post-accept-result op opgen *fn2-outcome-done* *fn2-reason-none* 5 9
                                                  family (if (equal family *fn2-peer-family-local*) 0 119)
                                                  w0 (if (equal family *fn2-peer-family-local*) 20 0) 0 0 fn2-ops)
                          fn2-core))
              (fn2-core (fn2-sle-quiet 16 fn2-core)))
           (mv (list (- ctl0 (fn2-machine-admission-credits *fn2-ctl-admission-ordinal* fn2-core))
                     (fn2-machine-admission-credits *fn2-conn-admission-ordinal* fn2-core))
               fn2-core))
         r))))
  (local
   (defconst *fn2-sle-local-profile*
     (put-assoc-equal :owner-uid 1000 (put-assoc-equal :listener-local-target 'fn2-ctl *fn2-sle-turn-profile*))))
  (local
   (defun fn2-sle-test-admit-by-family ()
     (declare (xargs :verify-guards nil))
     (let ((local (fn2-sle-admit-run *fn2-sle-local-profile* *fn2-peer-family-local* 1000))
           (inet (fn2-sle-admit-run *fn2-sle-local-profile* *fn2-peer-family-inet* #x7f000001))
           (bare (fn2-sle-admit-run (put-assoc-equal :owner-uid 1000 *fn2-sle-turn-profile*)
                                    *fn2-peer-family-local* 1000)))
       (and (consp local) (consp inet) (consp bare)
            (equal (car local) 1) (equal (car inet) 0) (equal (car bare) 0)
            ;; the conn credit the local Accept took at issue went back
            (equal (cadr local) (+ 1 (cadr inet)))
            (equal (cadr bare) (cadr inet))))))
  (local (assert-event (fn2-sle-test-admit-by-family)))
  ;; An append is a POST (e-surface.md 3.3): a control connection's append
  ;; frame (cmd 1, fkind 7, a one-octet operation identity 9, the article
  ;; with no Message-ID) runs the upload and the transaction a POST runs; the
  ;; reply is accepted at the article's commit position, and an NNTP reader
  ;; then reads the same article by GROUP, by number and by the generated
  ;; Message-ID <op-0-9@fn2.invalid>.
  (local
   (defconst *fn2-sle-append-profile*
     (put-assoc-equal :cns 1 (put-assoc-equal :control-connections 1
       (put-assoc-equal :extent-slots 128 *fn2-cursor-profile*)))))
  (local
   (defconst *fn2-sle-append-article*
     '("From: mini@example.invalid" "Subject: r1" "Newsgroups: local.test" "" "report r1")))
  (local
   (defconst *fn2-sle-append-mid* "<op-0-9@fn2.invalid>"))
  (local
   (defun fn2-sle-append-wire ()
     (declare (xargs :verify-guards nil))
     (fnc-append 9 (fn2-cw-crlf-octets *fn2-sle-append-article*))))
  (local
   (defun fn2-sle-append-nntp-expected ()
     (declare (xargs :verify-guards nil))
     (fn2-cw-crlf-octets
      (append (list "200 fn-nntp experimental server ready" "211 1 1 1 local.test"
                    (fn2-csp-cat (list "220 1 " *fn2-sle-append-mid* " article follows"))
                    "Xref: fn2.invalid local.test:1" (fn2-csp-cat (list "Message-ID: " *fn2-sle-append-mid*)))
              *fn2-sle-append-article*
              (list "." (fn2-csp-cat (list "220 0 " *fn2-sle-append-mid* " article follows"))
                    "Xref: fn2.invalid local.test:1" (fn2-csp-cat (list "Message-ID: " *fn2-sle-append-mid*)))
              *fn2-sle-append-article*
              (list "." "205 closing connection")))))
  (local
   (defun fn2-sle-chars (octets)
     (declare (xargs :verify-guards nil))
     (if (atom octets) nil (cons (code-char (nfix (car octets))) (fn2-sle-chars (cdr octets))))))
  ;; The NNTP listener's Accept is the outbox's first action; the reader
  ;; connects only after the append's reply, so the Accept is taken off the
  ;; outbox and held, (op . opgen), and completed for client 1 then (as
  ;; m2-cuts defers a starved Receive).
  (local
   (defun fn2-sle-hold-accept (held fn2-core)
     (declare (xargs :stobjs fn2-core :verify-guards nil))
     (if held (mv nil held fn2-core)
       (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
         (took held fn2-ops)
         (mv-let (code op opgen) (fn2-outbox-peek 0 fn2-ops)
           (if (not (and (eq code :ok) (equal (fn2-ops-kind op fn2-ops) *fn2-action-accept*)))
               (mv nil nil fn2-ops)
             (mv-let (ack fn2-ops) (fn2-outbox-ack 1 fn2-ops)
               (mv (eq ack :ok) (and (eq ack :ok) (cons op opgen)) fn2-ops))))
         (mv took held fn2-core)))))
  (local
   (defun fn2-sle-loop (fuel idle clients store held fn2-core)
     (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix fuel)))
     (if (zp fuel) (mv :fuel clients store held fn2-core)
       (b* (((mv & nobs nvisits nactions fn2-core) (fn2-turn fn2-core))
            ((mv h held fn2-core) (fn2-sle-hold-accept held fn2-core))
            ((mv took & clients store fn2-core)
             (if h (mv t 1 clients store fn2-core) (fn2-cw-adapter-one 1 clients store fn2-core)))
            (idle (if (or took (< 0 nobs) (< 0 nvisits) (< 0 nactions)) 0 (+ 1 idle))))
         (if (or (<= 3 idle) (not (equal (fn2-core-stop-reason fn2-core) 0)))
             (mv :quiet clients store held fn2-core)
           (fn2-sle-loop (- fuel 1) idle clients store held fn2-core))))))
  (local
   (defun fn2-sle-test-turn-append ()
     (declare (xargs :verify-guards nil))
     (with-local-stobj fn2-core
       (mv-let (r fn2-core)
         (b* ((fn2-core (fn2-init-executor *fn2-sle-append-profile* :echo nil fn2-core))
              ((mv & fn2-core)
               (stobj-let ((fn2-extents (fn2-core-extents fn2-core))) (code fn2-extents)
                 (fn2-alloc-begin-epoch 1 fn2-extents) (mv code fn2-core)))
              (fn2-core (fn2-listener-take-credit *fn2-ctl-admission-ordinal* fn2-core))
              ((mv acode fn2-core) (fn2-machine-admit-fn2-ctl 0 77 3 0 fn2-core))
              ((unless (eq acode :ok)) (mv (list :admit acode) fn2-core))
              ((mv wake fn2-core) (fn2-machine-take-wake fn2-core))
              (fn2-core (fn2-exec-wake wake fn2-core))
              (frame (fn2-sle-append-wire))
              (stop (fnc-control 5))
              (clients (list (list (append frame stop) (list (len frame) (len stop)) nil nil)))
              ((mv status1 clients store held fn2-core) (fn2-sle-loop 4000 0 clients nil nil fn2-core))
              ((unless held) (mv (list :no-accept status1) fn2-core))
              (wire1 (car (car (fn2-cw-results clients))))
              (reader (fn2-cw-crlf-octets (list "GROUP local.test" "ARTICLE 1"
                                                (fn2-csp-cat (list "ARTICLE " *fn2-sle-append-mid*)) "QUIT")))
              (clients (append clients (fn2-cw-clients (list (list reader nil)))))
              (fn2-core (fn2-cw-post-accept (car held) (cdr held) 1 77 nil fn2-core))
              ((mv status2 clients & fn2-core) (fn2-cw-loop 8000 0 2 clients store fn2-core))
              (wire2 (car (cadr (fn2-cw-results clients)))))
           (mv (list status1 wire1 status2 wire2 (fn2-core-stop-reason fn2-core)) fn2-core))
         (let ((ok (and (eq (nth 0 r) :quiet) (equal (fnc-replies '(append) (nth 1 r)) '((:accepted "" (1 1))))
                        (eq (nth 2 r) :quiet) (equal (nth 3 r) (fn2-sle-append-nntp-expected))
                        (equal (nth 4 r) 0))))
           (or ok (cw "append ~x0 ~x1 ~x2 stop ~x3~%nntp ~s4~%" (nth 0 r) (nth 1 r) (nth 2 r) (nth 4 r)
                      (coerce (fn2-sle-chars (nth 3 r)) 'string))))))))
  (local (assert-event (fn2-sle-test-turn-append)))
  (local (assert-event (fn2-sle-test-turn-read-and-stop)))
  (local (assert-event (fn2-sle-test-turn-wait-wake)))
  (local (assert-event (fn2-sle-test-turn-full-verbs)))
  (defun fn2-sle-turn-e2e-witness () (declare (xargs :guard t)) t))

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
  (sle-run-steps script (fn2-cns-model-init *sle-history* *sle-incarnation*) nil nil nil nil))
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
(defun sle-pages-of (replies)
  ; Every reply that is a page with items, in order.
  (declare (xargs :verify-guards nil))
  (if (atom replies) nil
    (let ((a (fn2-cnsk-decode-reply 'read :k28 (nth 2 (car replies)))))
      (if (and (eq (car a) :accepted) (consp (nth 2 a)) (natp (nth 2 (nth 2 a))) (< 0 (nth 2 (nth 2 a))))
          (cons (car replies) (sle-pages-of (cdr replies))) (sle-pages-of (cdr replies))))))
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
(defun sle-from-head (obs)
  ; The read after the ack answered from the run head instead of the cursor's
  ; position (the positioned seek skipped): the second page repeats the first.
  (declare (xargs :verify-guards nil))
  (let* ((pages (sle-pages-of (sle-replies obs))) (first (car pages)) (second (cadr pages)))
    (sle-replace second (list :reply (nth 1 second) (nth 2 first)) obs)))
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
; wait that never answers (K4b), a wait-row held with no wait, a read after an
; ack answered from the run head instead of the cursor's position.
(defun fn2-sle-test-controls ()
  (declare (xargs :verify-guards nil))
  (equal (list (sle-fail-word (sle-check (sle-skip-item (sle-observe *sle-pages*))))
               (sle-fail-word (sle-check (sle-uncertain-read (sle-observe *sle-pages*))))
               (sle-fail-word (sle-check (sle-rewind-ledger (sle-observe *sle-wait*))))
               (sle-fail-word (sle-check (sle-lose-wake (sle-observe *sle-wait*))))
               (sle-fail-word (sle-check (sle-leak (sle-observe *sle-wait*))))
               (sle-fail-word (sle-check (sle-from-head (sle-observe *sle-pages*)))))
         '(:reply :reply :ledger :lost-wake :settled-holding :reply)))
(assert! (fn2-sle-test-oracle))
(assert! (fn2-sle-test-controls))

;; ---------------------------------------------------------------------------
;; Local control carrier (fn2-ctl) and consumer request machine (fn2-cns)
;; end-to-end verification (M2: STATUS / PAUSE / RESUME / DRAIN / STOP and
;; subscription-edge parking/waking).
(defun fn2-sle-test-ctl-commands ()
  (declare (xargs :verify-guards nil))
  (and
   ;; Owner check: local peer family 3 with configured owner uid is owner; mismatched uid or non-local is refused.
   (fn2-ctl-owner-uid-p 3 0 0)
   (fn2-ctl-owner-uid-p 3 1000 1000)
   (not (fn2-ctl-owner-uid-p 3 0 1000))
   (not (fn2-ctl-owner-uid-p 3 1000 0))
   (not (fn2-ctl-owner-uid-p 1 1000 1000))
   ;; End-to-end STATUS / PAUSE / RESUME / DRAIN / STOP posture sequence:
   ;; STOP terminates the session so any trailing command after STOP is not executed.
   (equal (fn2-ctl-eval-commands '(:status :pause :status :resume :drain :stop :status)
                                 *fn2-ctl-posture-running*)
          '((:ok :status :running)
            (:ok :pause :paused)
            (:ok :status :paused)
            (:ok :resume :running)
            (:ok :drain :draining)
            (:ok :stop :stopped)))))

(defun fn2-sle-test-cns-park-wake ()
  (declare (xargs :verify-guards nil))
  ;; Verify the subscription-edge link, publish wake, and grant cycle that
  ;; backs fn2-cns :park and :wait-row (cns.lisp).
  (with-local-stobj fn2-cns-edges
    (mv-let (ok fn2-cns-edges)
      (with-local-stobj fn2-machines
        (mv-let (ok fn2-cns-edges fn2-machines)
          (with-local-stobj fn2-control
            (mv-let (ok fn2-cns-edges fn2-machines fn2-control)
              (b* ((fn2-cns-edges (fn2-cns-edges-init 16 fn2-cns-edges))
                   (fn2-machines (fn2-machines-columns-init 8 fn2-machines))
                   (fn2-control (fn2-control-init (put-assoc-equal :owner-uid 1000 *fn2-profile-tiny*) fn2-control))
                   ((unless (and (fn2-ctl-owner-p 3 1000 fn2-control)
                                 (not (fn2-ctl-owner-p 3 0 fn2-control))))
                    (mv nil fn2-cns-edges fn2-machines fn2-control))
                   ;; Stale edge with generation 1 does not wake row 2 when row 2 is at generation 9.
                   (fn2-machines (fn2-machines-set-wait-reason 2 *fn2-wait-wait-row* fn2-machines))
                   ((mv code0 edge0 fn2-cns-edges) (fn2-cns-edge-link 0 2 1 3 fn2-cns-edges))
                   ((unless (and (eq code0 :ok) (natp edge0)))
                    (mv nil fn2-cns-edges fn2-machines fn2-control))
                   (fn2-cns-edges (fn2-cns-wake-stream 0 3 fn2-cns-edges))
                   ((mv & fn2-cns-edges fn2-machines fn2-control)
                    (fn2-cns-grant-one-gen 9 fn2-cns-edges fn2-machines fn2-control))
                   ((unless (equal (fn2-machines-wait-reason 2 fn2-machines) *fn2-wait-wait-row*))
                    (mv nil fn2-cns-edges fn2-machines fn2-control))
                   (fn2-cns-edges (fn2-cns-edge-unlink edge0 fn2-cns-edges))
                   ;; Matching generation 1 wakes row 2 and clears its :wait-row wait reason.
                   ((mv code edge fn2-cns-edges) (fn2-cns-edge-link 0 2 1 5 fn2-cns-edges))
                   ((unless (and (eq code :ok) (natp edge)))
                    (mv nil fn2-cns-edges fn2-machines fn2-control))
                   ;; Before publish at >= 5, no waiter is ready.
                   ((when (fn2-cns-ready-p fn2-cns-edges))
                    (mv nil fn2-cns-edges fn2-machines fn2-control))
                   ;; Publish at position 5 on stream 0 wakes the bucket.
                   (fn2-cns-edges (fn2-cns-wake-stream 0 5 fn2-cns-edges))
                   ((unless (fn2-cns-ready-p fn2-cns-edges))
                    (mv nil fn2-cns-edges fn2-machines fn2-control))
                   ;; Grant wakes waiter 2 and clears its :wait-row wait reason.
                   ((mv w fn2-cns-edges fn2-machines fn2-control)
                    (fn2-cns-grant-one fn2-cns-edges fn2-machines fn2-control))
                   (fn2-cns-edges (fn2-cns-edge-unlink edge fn2-cns-edges)))
                (mv (and (equal w 2)
                         (equal (fn2-machines-wait-reason 2 fn2-machines) *fn2-wait-none*)
                         (not (fn2-cns-ready-p fn2-cns-edges)))
                    fn2-cns-edges fn2-machines fn2-control))
              (mv ok fn2-cns-edges fn2-machines)))
          (mv ok fn2-cns-edges)))
      ok)))

(defun fn2-k10-consumer-delivery-comes-from-committed-log-positive ()
  (declare (xargs :verify-guards nil))
  (and (fn2-sle-test-oracle)
       (fn2-sle-turn-e2e-witness)))

(defun fn2-k10-consumer-delivery-comes-from-committed-log-negative ()
  (declare (xargs :verify-guards nil))
  (fn2-sle-test-controls))

(assert! (fn2-sle-test-ctl-commands))
(assert! (fn2-sle-test-cns-park-wake))
(assert! (fn2-sle-turn-e2e-witness))
(assert! (fn2-k10-consumer-delivery-comes-from-committed-log-positive))
(assert! (fn2-k10-consumer-delivery-comes-from-committed-log-negative))
