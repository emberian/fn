; M2 spine cuts (REVIEW-ARGON-RESPONSE-20261031 section 9.12): Mini's twelve
; cuts (docs/e-surface.md 10.1, *mini-cuts* in tests/consumer-mini.lisp) run
; by Mini as a client of the SERVED core: fn2-ctl and fn2-cns admitted at the
; Brick F6 profile, every request a frame on a :local connection driven
; through fn2-turn and the adapter (fn2-cw-adapter-one, owed-conn.lisp), every
; reply read off the connection's wire. The reference model is not consulted
; for any answer; consumer-mini.lisp supplies only the scripts, Mini's own
; database (mini-db-init, mini-commit) and the oracle's verdict for the
; control.
;
; A cut passes only when every step it takes is served and Mini's acceptance
; holds over what it observed. A step the served node cannot take (no verb, no
; world step, a reply without the fields Mini needs) is a named reason and
; the cut FAILs; it is never skipped. Where the served node refuses origin's
; append of R, R is put in Mini's addr stream by the same direct core writes
; F6 uses (fn2-addr-put, bind, publish, wake) so the later steps are still
; exercised; the refusal stays a reason.
;
; tests/m2-cuts.lsp prints one line per cut and the total; tests/m2_json.py
; writes OUT/m2.json for H's nightly line.
(in-package "ACL2")
(include-book "consumer-mini")
(include-book "../books/owed-conn")
(include-book "std/testing/assert-bang" :dir :system)

; F6's profile (tests/sim-layer-e.lisp *fn2-sle-turn-profile*): two control
; connections (Mini's and origin's), two consumer request rows.
(defconst *m2-profile*
  (put-assoc-equal :cns 2
    (put-assoc-equal :control-connections 2
      (put-assoc-equal :identity-overlays 32
        (put-assoc-equal :identity-arena-bytes 4096
          (put-assoc-equal :pool-classes '((8 . 1024) (64 . 4096) (16 . 65536)) *fn2-conn-wire-profile*))))))
(defconst *m2-mini-conn* 0)
(defconst *m2-origin-conn* 1)

;; The served wire --------------------------------------------------------------
; A request frame is (cmd fkind consumer arg3 limit epoch) (fn2-ctl-parse-frame,
; fn2-cns-decode-frame): cmd 1 keeps the posture, fkind the verb, consumer 1
; is Mini's, arg3 the register's start or the ack's target, Mini's 8 items,
; epoch 1. A reply is (outcome reason cpos pfront count more) (fn2-cns-encode-reply-pool).
(defun m2-frame (fkind arg3) (declare (xargs :guard t)) (list 1 fkind 1 arg3 8 1))
(defun m2-outcome (r) (declare (xargs :guard t)) (and (consp r) (car r)))
(defun m2-accepted-p (r) (declare (xargs :guard t)) (equal (m2-outcome r) *fn2-cns-outcome-accepted*))

; The adapter's Receive completion consumes the operation even when the client
; has nothing to send (fn2-cw-adapter-one). A scripted client sends its next
; frame only after it has read the reply, so the loop holds a Receive at the
; outbox head until that client's frame is there.
(defun m2-starved-p (clients fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (starved)
    (mv-let (code op opgen) (fn2-outbox-peek 0 fn2-ops)
      (declare (ignore opgen))
      (and (eq code :ok)
           (equal (fn2-ops-kind op fn2-ops) *fn2-action-receive*)
           (mv-let (cap nonce) (fn2-op-capability op fn2-ops)
             (declare (ignore nonce))
             (atom (nth 0 (nth cap clients))))))
    starved))
(defun m2-loop (fuel idle clients fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix fuel)))
  (if (zp fuel) (mv :fuel clients fn2-core)
    (b* (((mv & nobs nvisits nactions fn2-core) (fn2-turn fn2-core))
         (hold (m2-starved-p clients fn2-core))
         ((mv took & clients fn2-core)
          (if hold (mv nil (len clients) clients fn2-core) (fn2-cw-adapter-one (len clients) clients fn2-core)))
         (idle (if (or took (< 0 nobs) (< 0 nvisits) (< 0 nactions)) 0 (+ 1 idle))))
      (if (or (<= 3 idle) (not (equal (fn2-core-stop-reason fn2-core) 0)))
          (mv :quiet clients fn2-core)
        (m2-loop (- fuel 1) idle clients fn2-core)))))
; Send FRAME on connection CONN (nil: send nothing, only run the core) and
; return what arrived on every connection's wire meanwhile: (mv new clients fn2-core),
; NEW ((conn . octets) ...) in connection order.
(defun m2-wire-lens (clients)
  (declare (xargs :verify-guards nil))
  (if (atom clients) nil (cons (len (nth 2 (car clients))) (m2-wire-lens (cdr clients)))))
(defun m2-new-octets (i clients lens)
  (declare (xargs :verify-guards nil))
  (if (atom clients) nil
    (let ((wire (nth 2 (car clients))))
      (cons (cons i (reverse (take (- (len wire) (nfix (car lens))) wire)))
            (m2-new-octets (+ 1 i) (cdr clients) (cdr lens))))))
(defun m2-exchange (conn frame clients fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((lens (m2-wire-lens clients))
       (c (nth conn clients))
       (clients (if frame
                    (update-nth conn (list (append (nth 0 c) frame) (append (nth 1 c) (list (len frame)))
                                           (nth 2 c) (nth 3 c) (nth 4 c))
                                clients)
                  clients))
       ((mv & clients fn2-core) (m2-loop 2000 0 clients fn2-core)))
    (mv (m2-new-octets 0 clients lens) clients fn2-core)))

; Origin's R where the served append refuses it: the direct core writes of F6
; (sim-layer-e.lisp fn2-sle-seed-article) at the next commit position.
(defun m2-seed-article (art fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* (((mv pcode pf) (fn2-successor-published fn2-core))
       (pos (+ 1 (if (eq pcode :ok) (nfix pf) 0)))
       ((mv & fn2-core) (fn2-successor-release 0 fn2-core))
       ((mv c0 fn2-core)
        (fn2-addr-put 0 0 (principal 0) (position pos) (article art) (stream 0) (reasons 1) fn2-core))
       ((unless (eq c0 :ok)) (mv c0 fn2-core))
       ((mv rc fn2-core) (fn2-cns-resolve-loop 32 0 fn2-core))
       ((unless (eq rc :ok)) (mv rc fn2-core))
       ((mv scode & fn2-core) (fn2-successor-stage 0 fn2-core))
       ((unless (eq scode :ok)) (mv scode fn2-core))
       ((mv bcode fn2-core) (fn2-successor-bind 0 pos pos fn2-core))
       ((unless (eq bcode :ok)) (mv bcode fn2-core))
       ((mv pcode fn2-core) (fn2-succ-core-publish pos fn2-core))
       ((unless (eq pcode :ok)) (mv pcode fn2-core))
       ((mv & fn2-core) (fn2-cns-core-stream-wake pos fn2-core))
       ((mv & fn2-core) (fn2-successor-release 0 fn2-core)))
    (mv :ok fn2-core)))

;; Mini over the served node --------------------------------------------------------
; S is (clients db reasons mutate): the connections, Mini's database
; (consumer-mini.lisp), the reasons the cut cannot pass (in order, no
; duplicates) and the control's mutation of the replies Mini reads.
(defun m2-s (clients db reasons mutate) (declare (xargs :guard t)) (list clients db reasons mutate))
(defun m2-why (reason s)
  (declare (xargs :verify-guards nil))
  (let ((rs (nth 2 s)))
    (m2-s (nth 0 s) (nth 1 s) (if (member-equal reason rs) rs (append rs (list reason))) (nth 3 s))))
(defun m2-db (db s) (declare (xargs :verify-guards nil)) (m2-s (nth 0 s) db (nth 2 s) (nth 3 s)))
(defun m2-reply-text (r) (declare (xargs :verify-guards nil)) (fms-to-string "~x0" (list (cons #\0 r))))
(defun m2-reason-text (what r)
  (declare (xargs :verify-guards nil))
  (concatenate 'string what " answered " (m2-reply-text r)))

; Mini's request on its own connection: (mv reply new s fn2-core). REPLY is
; Mini's six octets (nil while a wait is parked); NEW is everything that
; arrived. The control's mutation (:register-refused) rewrites one reply.
(defun m2-mini-send (verb frame s fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* (((mv new clients fn2-core) (m2-exchange *m2-mini-conn* frame (nth 0 s) fn2-core))
       (r (cdr (assoc-equal *m2-mini-conn* new)))
       (r (if (and r (eq verb 'register) (eq (nth 3 s) :register-refused))
              (update-nth 0 *fn2-cns-outcome-refused* r)
            r)))
    (mv r new (m2-s clients (nth 1 s) (nth 2 s) (nth 3 s)) fn2-core)))

(defconst *m2-no-items*
  "page: the served reply is six octets (outcome reason cpos pfront count more) and carries no item, so Mini sees no Message-ID, source or reference")
(defconst *m2-append*
  "append (fkind 7) refused unavailable at fn2-cns :check")
(defconst *m2-append-r*
  "origin's append of R (fkind 7) refused unavailable; R stood in by a direct fn2-addr-put")

; Mini's half after a page (consumer-mini.lisp mini-after-page): references
; fetched, the items committed, the page's next acknowledged, the outbox posted.
(defun m2-post-outbox (outbox lose s fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (cond ((atom outbox) (mv s fn2-core))
        ((eq lose :request) (mv s fn2-core))
        (t (b* (((mv r & s fn2-core) (m2-mini-send 'append (m2-frame 7 0) s fn2-core))
                (db (nth 1 s))
                (o (cond ((m2-accepted-p r) (list :accepted nil))
                         ((equal (m2-outcome r) *fn2-cns-outcome-uncertain*) (list :uncertain nil))
                         (t (list :refused (nth 1 r)))))
                (s (if (m2-accepted-p r)
                       (m2-why "append accepted: the six-octet reply carries no Message-ID to hold across retries" s)
                     (m2-why *m2-append* s)))
                (db (mini-put :posted (cons (cons (caar outbox) o) (mini-get :posted db)) db))
                (db (if (or lose (eq (car o) :uncertain)) db
                      (mini-put :outbox (remove1-equal (car outbox) (mini-get :outbox db)) db))))
             (m2-post-outbox (cdr outbox) lose (m2-db db s) fn2-core)))))
(defun m2-page-next (r)
  ; The page's next position: its frontier when the page is the whole range,
  ; else the position of its last item.
  (declare (xargs :verify-guards nil))
  (if (equal (nfix (nth 5 r)) 0) (nfix (nth 3 r)) (+ (nfix (nth 2 r)) (nfix (nth 4 r)))))
(defun m2-after-page (r flag s fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((s (if (eq flag :reclaim-before-fetch)
              (m2-why "reclaim: no served world step reclaims a stored article (fn2-cns has no reclaim of R)" s)
            s))
       (s (if (and (m2-accepted-p r) (< 0 (nfix (nth 4 r)))) (m2-why *m2-no-items* s) s))
       (items nil)
       (db (mini-put :parked nil (nth 1 s)))
       (s (m2-db db s)))
    (cond
     ((not (m2-accepted-p r)) (mv (m2-why (m2-reason-text "a page" r) s) fn2-core))
     ((eq flag :die-before-commit) (mv (m2-db (mini-put :uncertain-ack t db) s) fn2-core))
     (t
      (b* ((db (mini-commit items db))
           ((when (eq flag :die-after-commit)) (mv (m2-db (mini-put :uncertain-ack t db) s) fn2-core))
           (next (m2-page-next r))
           ((mv a & s fn2-core) (m2-mini-send 'ack (m2-frame 4 next) (m2-db db s) fn2-core))
           (s (if (m2-accepted-p a) s (m2-why (m2-reason-text "the ack of a page's next" a) s)))
           (db (if (or (eq flag :lose-ack) (not (m2-accepted-p a))) (mini-put :uncertain-ack t (nth 1 s))
                 (mini-put :cursor next (nth 1 s)))))
        (m2-post-outbox (mini-get :outbox db)
                        (case flag (:lose-append t) (:append-lost :request) (otherwise nil))
                        (m2-db db s) fn2-core))))))
(defun m2-settle (s fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((db (nth 1 s))
       ((unless (mini-get :uncertain-ack db)) (m2-post-outbox (mini-get :outbox db) nil s fn2-core))
       ((mv r & s fn2-core) (m2-mini-send 'position (m2-frame 5 0) s fn2-core))
       (s (if (m2-accepted-p r) s (m2-why (m2-reason-text "position" r) s)))
       (db (if (m2-accepted-p r) (mini-put :uncertain-ack nil (mini-put :cursor (nfix (nth 2 r)) (nth 1 s))) (nth 1 s))))
    (m2-post-outbox (mini-get :outbox db) nil (m2-db db s) fn2-core)))
; Whatever reached Mini's connection while it had a wait parked is that wait's answer.
(defun m2-woken (new s fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let ((r (cdr (assoc-equal *m2-mini-conn* new))))
    (if (and r (mini-get :parked (nth 1 s))) (m2-after-page r nil s fn2-core) (mv s fn2-core))))

(defun m2-world (op s fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (case (car op)
    (append
     ; Origin appends R on its own connection; Mini's may hold a parked wait.
     (b* ((art (if (equal (car (nth 3 op)) "<r2@origin>") 2 1))
          ((mv new clients fn2-core) (m2-exchange *m2-origin-conn* (m2-frame 7 0) (nth 0 s) fn2-core))
          (s (m2-s clients (nth 1 s) (nth 2 s) (nth 3 s)))
          (ro (cdr (assoc-equal *m2-origin-conn* new)))
          ((mv s fn2-core) (m2-woken new s fn2-core))
          ((when (m2-accepted-p ro)) (mv s fn2-core))
          (s (m2-why *m2-append-r* s))
          ((mv code fn2-core) (m2-seed-article art fn2-core))
          (s (if (eq code :ok) s (m2-why (concatenate 'string "the stand-in seed of R stopped: " (m2-reply-text code)) s)))
          ((mv new clients fn2-core) (m2-exchange *m2-mini-conn* nil (nth 0 s) fn2-core)))
       (m2-woken new (m2-s clients (nth 1 s) (nth 2 s) (nth 3 s)) fn2-core)))
    (:grant (mv (m2-why "grant: the served node has no authority verb (fn2-ctl admits the owner only; every frame is the owner's)" s) fn2-core))
    (:withdraw (mv (m2-why "withdraw: no served cancel, and fn2-cns delivers no withdrawal report" s) fn2-core))
    (otherwise (mv (m2-why (concatenate 'string "world step " (m2-reply-text (car op)) " is not served") s) fn2-core))))

(defun m2-drive (script s fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (atom script) (mv s fn2-core)
    (let ((st (car script)))
      (case (car st)
        (:register
         (b* (((mv r & s fn2-core) (m2-mini-send 'register (m2-frame 1 0) s fn2-core))
              (s (if (m2-accepted-p r) s (m2-why (m2-reason-text "register" r) s))))
           (m2-drive (cdr script) (m2-db (mini-db-init (nfix (nth 2 r))) s) fn2-core)))
        (:world (b* (((mv s fn2-core) (m2-world (cadr st) s fn2-core))) (m2-drive (cdr script) s fn2-core)))
        (:crash
         (m2-drive (cdr script)
                   (m2-why "crash: the adapter loop has no crash and recovery of the served core (no durable image under fn2-cw; K10, D5 2/n)" s)
                   fn2-core))
        (:wait
         (b* (((mv s fn2-core) (m2-settle s fn2-core))
              ((mv r & s fn2-core) (m2-mini-send 'wait (m2-frame 3 0) s fn2-core))
              ((mv s fn2-core) (if r (m2-after-page r nil s fn2-core)
                                 (mv (m2-db (mini-put :parked t (nth 1 s)) s) fn2-core))))
           (m2-drive (cdr script) s fn2-core)))
        (:turn
         (b* (((mv s fn2-core) (m2-settle s fn2-core))
              ((mv r & s fn2-core)
               (if (mini-get :parked (nth 1 s))
                   (mv nil nil (m2-why "a read while Mini's wait is still parked: the wait never answered" s) fn2-core)
                 (m2-mini-send 'read (m2-frame 2 0) s fn2-core)))
              ((mv s fn2-core) (if r (m2-after-page r (cadr st) s fn2-core) (mv s fn2-core))))
           (m2-drive (cdr script) s fn2-core)))
        (:stale-ack
         (b* (((mv r & s fn2-core) (m2-mini-send 'ack (m2-frame 4 (nfix (cadr st))) s fn2-core))
              ; The stale duplicate is refused behind and changes nothing (K2).
              (s (if (and (equal (m2-outcome r) *fn2-cns-outcome-refused*) (equal (nth 1 r) *fn2-cns-reason-behind*))
                     s (m2-why (m2-reason-text "a stale duplicate ack" r) s))))
           (m2-drive (cdr script) s fn2-core)))
        (otherwise (m2-drive (cdr script) s fn2-core))))))

;; The acceptance (e-surface.md 10.1) over what Mini holds -------------------------
(defun m2-accept (cut db)
  (declare (xargs :verify-guards nil))
  (let* ((ops (strip-cars (mini-get :index db)))
         (accepted (mini-accepted-mids (mini-get :posted db) "m-o1")))
    (and (null (mini-get :outbox db))
         (equal (len (remove-duplicates-equal accepted)) (len ops))
         (case cut
           (:c8-withdrawn-after-ack (and (equal ops '("o1")) (equal (mini-get :withdrawn db) (list "<r1@origin>"))))
           (:c11-reclaimed-before-fetch (and (null ops) (equal (mini-get :gaps db) (list "<r1@origin>"))))
           (:c4-changed-source (and (equal ops '("o1")) (equal (mini-get :evidence db) (list (list "o1" *mini-r2*)))))
           (:c5-cancelled (and (null ops) (equal (mini-get :withdrawn db) (list "<r1@origin>" "<r1@origin>"))))
           (otherwise (equal (cdr (assoc-equal "o1" (mini-get :index db))) *mini-r1*))))))

; A cut's run from the initialized core: (mv pass reasons).
(defun m2-admit (cap fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((fn2-core (fn2-listener-take-credit *fn2-ctl-admission-ordinal* fn2-core))
       ((mv acode fn2-core) (fn2-machine-admit-fn2-ctl cap 77 3 0 fn2-core))
       ((unless (eq acode :ok)) (mv acode fn2-core))
       ((mv wake fn2-core) (fn2-machine-take-wake fn2-core))
       (fn2-core (fn2-exec-wake wake fn2-core)))
    (mv :ok fn2-core)))
(defun m2-cut-run (cut mutate)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (pass reasons fn2-core)
      (b* ((fn2-core (fn2-init-executor *m2-profile* :echo nil fn2-core))
           ((mv a0 fn2-core) (m2-admit *m2-mini-conn* fn2-core))
           ((mv a1 fn2-core) (m2-admit *m2-origin-conn* fn2-core))
           ((unless (and (eq a0 :ok) (eq a1 :ok)))
            (mv nil (list (concatenate 'string "admitting the two fn2-ctl connections answered " (m2-reply-text (list a0 a1)))) fn2-core))
           (clients (list (list nil nil nil nil nil) (list nil nil nil nil nil)))
           (script (append (pairlis$ (make-list (len *mini-grants*) :initial-element :world) (pairlis$ *mini-grants* nil))
                           (cdr (assoc-eq cut *mini-cuts*))))
           ((mv s fn2-core) (m2-drive script (m2-s clients (mini-db-init 0) nil mutate) fn2-core))
           (s (if (equal (fn2-core-stop-reason fn2-core) 0) s
                (m2-why (concatenate 'string "the core stopped: " (m2-reply-text (fn2-core-stop-reason fn2-core))) s)))
           (ok (m2-accept cut (nth 1 s)))
           (s (if ok s (m2-why "Mini's acceptance fails over what it observed (e-surface.md 10.1)" s)))
           ; R's and Q's octets through NNTP's ARTICLE and GROUP are not read
           ; back by this driver; a cut cannot pass before they are.
           (s (if (nth 2 s) s (m2-why "NNTP readback of R and Q (GROUP, ARTICLE over fn2-conn) is not driven yet" s))))
        (mv (null (nth 2 s)) (nth 2 s) fn2-core))
      (mv pass reasons))))

(defun m2-cut-name (cut)
  (declare (xargs :verify-guards nil))
  (let ((n (symbol-name cut))) (string-downcase (subseq n 0 (search "-" n)))))
(defun m2-join (rs)
  (declare (xargs :verify-guards nil))
  (cond ((atom rs) "") ((atom (cdr rs)) (car rs)) (t (concatenate 'string (car rs) " | " (m2-join (cdr rs))))))
(defun m2-report (cuts n)
  ; Print M2CUT lines; answer the number passed.
  (declare (xargs :verify-guards nil))
  (if (atom cuts) n
    (mv-let (pass reasons) (m2-cut-run (caar cuts) nil)
      (prog2$ (cw "M2CUT ~s0 ~s1 ~s2~%" (m2-cut-name (caar cuts)) (if pass "PASS" "FAIL") (m2-join reasons))
              (m2-report (cdr cuts) (if pass (+ 1 n) n))))))

;; The controls -------------------------------------------------------------------
; The oracle passes all twelve over the reference model (consumer-mini.lisp).
(assert! (fn2-cns-test-mini))
; A wrong served answer is judged: register's reply rewritten to a refusal
; adds its reason to c0's.
(defun m2-register-refused-p (rs)
  (declare (xargs :verify-guards nil))
  (and (consp rs)
       (or (and (stringp (car rs)) (equal (search "register answered (2 " (car rs)) 0))
           (m2-register-refused-p (cdr rs)))))
(defun m2-test-mutation ()
  (declare (xargs :verify-guards nil))
  (mv-let (pass0 r0) (m2-cut-run :c0-wait nil)
    (declare (ignore pass0))
    (mv-let (pass1 r1) (m2-cut-run :c0-wait :register-refused)
      (and (not pass1) (m2-register-refused-p r1) (not (m2-register-refused-p r0))))))
(assert! (m2-test-mutation))
