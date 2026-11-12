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
; the cut FAILs; it is never skipped. Origin's append of R and Mini's of Q
; are served appends (e-surface.md 3.3: the upload and transaction a POST
; runs), each a frame carrying its operation identity and its article.
;
; tests/m2-cuts.lsp prints one line per cut and the total; tests/m2_json.py
; writes OUT/m2.json for H's nightly line.
(in-package "ACL2")
(include-book "consumer-mini")
(include-book "../books/owed-conn")
(include-book "../books/owed-cursor")
(include-book "authority-client")
(include-book "std/testing/assert-bang" :dir :system)

; The reading and posting profile (owed-cursor.lisp *fn2-cursor-profile*,
; its device sized as sealer-capacity-unit's) with Mini's two groups, two
; control connections (Mini's and origin's) and two consumer request rows.
(defconst *m2-profile*
  ;; T 4: fn2-txn's row, fn2-auth's and the two consumer rows' successors (fn2-txn-consumer-share)
  (put-assoc-equal :t 4
  (put-assoc-equal :p 8
  (put-assoc-equal :c 8
  (put-assoc-equal :o 32
  (put-assoc-equal :qa 16
  (put-assoc-equal :authority 1
  (put-assoc-equal :owner-account 2
  (put-assoc-equal :cns 2
    (put-assoc-equal :control-connections 3
      (put-assoc-equal :extent-slots 32
        (put-assoc-equal :pool-classes '((32 . 1024) (128 . 16384) (64 . 65536))
          (put-assoc-equal :groups (list (cons *mini-group* 1) (cons *mini-reply-group* 2)) *fn2-cursor-profile*)))))))))))))
(defconst *m2-mini-conn* 0)
(defconst *m2-origin-conn* 1)
; The administrator's connection (an owner connection never bound): it
; creates mini and origin and sets Mini's world's grants (AUTHORITY-20261105
; section 5); Mini's and origin's connections bind to their principals.
(defconst *m2-admin-conn* 2)
(defconst *m2-mini-id* (+ (* 1 4294967296) 1))     ; slot 1, incarnation 1
(defconst *m2-origin-id* (+ (* 3 4294967296) 1))   ; slot 3 (the owner's slot 2 skipped)
(defconst *m2-reader-id* 1)                        ; "reader": the persisted anonymous principal

;; The served wire --------------------------------------------------------------
; Frames are the L carrier's FNCT (tests/fnct-client.lisp, e-surface.md 4.2):
; Mini registers consumer 1 on its inbox from history and re-sends the cursor
; the node issued (held in its database as :fncu) with every read, wait and
; ack; position and status name consumer 1. A reply is read as (CLASS WORD
; RESULT) (fnc-reply): a cursor's position, a page's (MORE NEXT COUNT).
; An append frame (code 11): no stream (the article's Newsgroups names its
; group), the operation identity (OP a string of at most 7 octets, read
; big-endian by the node), the article's CR LF lines.
(defun m2-append-frame (op lines)
  (declare (xargs :verify-guards nil))
  (fnc-request :append (list (cons 'stream nil) (cons 'op (fn2-cw-chars (coerce op 'list)))
                             (cons 'article (fn2-cw-crlf-octets lines)))))
; R as origin appends it: Mini's group, R's Message-ID and its source's
; operation tag; Q as Mini appends it to the reply group under its opid.
; R's carried size (198,919 octets) is past one L frame (one receive of
; *fn2-ctl-io-bytes*), so the frame carries R's header and tag only.
(defun m2-r-lines (mid source)
  (declare (xargs :verify-guards nil))
  (list "From: origin@example.invalid" "Subject: R" (concatenate 'string "Newsgroups: " *mini-group*)
        (concatenate 'string "Message-ID: " mid) ""
        (let ((at (search "op=" source))) (if at (subseq source at (+ at 10)) "op="))))
(defun m2-q-lines (opid)
  (declare (xargs :verify-guards nil))
  (list "From: mini@example.invalid" (concatenate 'string "Subject: Q for " opid)
        (concatenate 'string "Newsgroups: " *mini-reply-group*) "" (concatenate 'string "Q for " opid)))
(defun m2-outcome (r) (declare (xargs :guard t)) (and (consp r) (car r)))
(defun m2-accepted-p (r) (declare (xargs :guard t)) (eq (m2-outcome r) :accepted))
(defun m2-cursor (s) (declare (xargs :verify-guards nil)) (mini-get :fncu (nth 1 s)))

;; The adapter's Receive completion consumes the operation even when the
; client has nothing to send (fn2-cw-adapter-one), and the outbox is one FIFO
; across connections. A scripted client sends its next frame only after it
; has read its reply, so a Receive that finds its client empty is taken off
; the outbox here and DEFERRED, ((cap op opgen rslot rgen roff rlen) ...), and
; completed exactly as the adapter completes one once that client's frame is
; there.
(defun m2-take-starved (clients deferred fn2-core)
  ; (mv took deferred fn2-core): the outbox head deferred when it is a
  ; Receive whose client has nothing to send.
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* (((mv hit d fn2-core)
        (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
          (hit d fn2-ops)
          (mv-let (code op opgen) (fn2-outbox-peek 0 fn2-ops)
            (if (not (and (eq code :ok) (equal (fn2-ops-kind op fn2-ops) *fn2-action-receive*)))
                (mv nil nil fn2-ops)
              (mv-let (cap nonce) (fn2-op-capability op fn2-ops)
                (declare (ignore nonce))
                (if (consp (nth 0 (nth cap clients)))
                    (mv nil nil fn2-ops)
                  (mv-let (rslot rgen roff rlen) (fn2-op-range op fn2-ops)
                    (mv-let (ack fn2-ops) (fn2-outbox-ack 1 fn2-ops)
                      (mv (eq ack :ok) (list cap op opgen rslot rgen roff rlen) fn2-ops)))))))
          (mv hit d fn2-core))))
    (mv hit (if hit (append deferred (list d)) deferred) fn2-core)))
(defun m2-complete-deferred (deferred clients fn2-core)
  ; (mv took deferred clients fn2-core): every deferred Receive whose client
  ; now has octets is given its next chunk.
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (atom deferred) (mv nil nil clients fn2-core)
    (b* (((list cap op opgen rslot rgen roff rlen) (car deferred))
         (c (nth cap clients))
         (input (nth 0 c)) (sizes (nth 1 c))
         ((when (atom input))
          (mv-let (took rest clients fn2-core) (m2-complete-deferred (cdr deferred) clients fn2-core)
            (mv took (cons (car deferred) rest) clients fn2-core)))
         (want (if (and (consp sizes) (posp (car sizes))) (car sizes) (len input)))
         (n (min want (min rlen (len input))))
         (fn2-core (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (fn2-pool)
                     (fn2-cw-write-loan roff (take n input) rslot rgen op opgen fn2-pool) fn2-core))
         (fn2-core (fn2-cw-post 0 op opgen *fn2-event-receive-result* *fn2-outcome-done* n 0 0 fn2-core))
         (clients (update-nth cap (list (nthcdr n input) (if (consp sizes) (cdr sizes) nil) (nth 2 c) (nth 3 c) (nth 4 c))
                              clients))
         ((mv & rest clients fn2-core) (m2-complete-deferred (cdr deferred) clients fn2-core)))
      (mv t rest clients fn2-core))))
(defun m2-loop (fuel idle clients store deferred fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix fuel)))
  (if (zp fuel) (mv :fuel clients store deferred fn2-core)
    (b* (((mv done deferred clients fn2-core) (m2-complete-deferred deferred clients fn2-core))
         ((mv & nobs nvisits nactions fn2-core) (fn2-turn fn2-core))
         ((mv held deferred fn2-core) (m2-take-starved clients deferred fn2-core))
         ((mv took & clients store fn2-core)
          (if held (mv t (len clients) clients store fn2-core)
            (fn2-cw-adapter-one (len clients) clients store fn2-core)))
         (idle (if (or done took (< 0 nobs) (< 0 nvisits) (< 0 nactions)) 0 (+ 1 idle))))
      (if (or (<= 3 idle) (not (equal (fn2-core-stop-reason fn2-core) 0)))
          (mv :quiet clients store deferred fn2-core)
        (m2-loop (- fuel 1) idle clients store deferred fn2-core)))))
; Send FRAME on connection CONN (nil: send nothing, only run the core) and
; return what arrived on every connection's wire meanwhile: (mv new clients
; io fn2-core), IO the adapter's storage device and the deferred Receives,
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
(defun m2-exchange (conn frame clients io fn2-core)
  ; IO is (store . deferred).
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((lens (m2-wire-lens clients))
       (c (nth conn clients))
       (clients (if frame
                    (update-nth conn (list (append (nth 0 c) frame) (append (nth 1 c) (list (len frame)))
                                           (nth 2 c) (nth 3 c) (nth 4 c))
                                clients)
                  clients))
       ((mv & clients store deferred fn2-core) (m2-loop 2000 0 clients (car io) (cdr io) fn2-core)))
    (mv (m2-new-octets 0 clients lens) clients (cons store deferred) fn2-core)))

;; Mini over the served node --------------------------------------------------------
; S is (clients db reasons mutate store): the connections, Mini's database
; (consumer-mini.lisp), the reasons the cut cannot pass (in order, no
; duplicates), the control's mutation of the replies Mini reads, and the
; adapter's storage device with the deferred Receives (m2-exchange's IO).
(defun m2-s (clients db reasons mutate store auth) (declare (xargs :guard t)) (list clients db reasons mutate store auth))
(defun m2-why (reason s)
  (declare (xargs :verify-guards nil))
  (let ((rs (nth 2 s)))
    (m2-s (nth 0 s) (nth 1 s) (if (member-equal reason rs) rs (append rs (list reason))) (nth 3 s) (nth 4 s) (nth 5 s))))
(defun m2-db (db s) (declare (xargs :verify-guards nil)) (m2-s (nth 0 s) db (nth 2 s) (nth 3 s) (nth 4 s) (nth 5 s)))
(defun m2-wired (clients io s) (declare (xargs :verify-guards nil)) (m2-s clients (nth 1 s) (nth 2 s) (nth 3 s) io (nth 5 s)))
(defun m2-auth-get (k s) (declare (xargs :verify-guards nil)) (cdr (assoc-eq k (nth 5 s))))
(defun m2-auth-put (k v s) (declare (xargs :verify-guards nil))
  (m2-s (nth 0 s) (nth 1 s) (nth 2 s) (nth 3 s) (nth 4 s) (put-assoc-eq k v (nth 5 s))))
; Replies and codes as text: a natural, a symbol, or a flat list of them.
(defun m2-atom-text (x)
  (declare (xargs :verify-guards nil))
  (cond ((natp x) (coerce (explode-nonnegative-integer x 10 nil) 'string))
        ((symbolp x) (symbol-name x))
        ((stringp x) x)
        (t "?")))
(defun m2-items-text (xs)
  (declare (xargs :verify-guards nil))
  (cond ((atom xs) "")
        ((atom (cdr xs)) (m2-atom-text (car xs)))
        (t (concatenate 'string (m2-atom-text (car xs)) " " (m2-items-text (cdr xs))))))
(defun m2-reply-text (r)
  (declare (xargs :verify-guards nil))
  (if (consp r) (concatenate 'string "(" (m2-items-text r) ")") (m2-atom-text r)))
(defun m2-reason-text (what r)
  (declare (xargs :verify-guards nil))
  (concatenate 'string what " answered " (m2-reply-text r)))

; Mini's request on its own connection: (mv reply new s fn2-core). REPLY is
; Mini's reply read as VERB's (nil while a wait is parked); NEW is everything
; that arrived. The control's mutation (:register-refused) rewrites one reply.
(defun m2-mini-send (verb frame s fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* (((mv new clients store fn2-core) (m2-exchange *m2-mini-conn* frame (nth 0 s) (nth 4 s) fn2-core))
       (o (cdr (assoc-equal *m2-mini-conn* new)))
       (r (and (consp o) (fnc-reply verb o)))
       (r (if (and r (eq verb 'register) (eq (nth 3 s) :register-refused))
              (list :refused "unavailable" nil)
            r)))
    (mv r new (m2-wired clients store s) fn2-core)))

; The served page's items (tests/fnct-client.lisp fnc-items) as the model's
; (POSITION TYPE MESSAGE-ID PAYLOAD): a record's payload its octets as a string.
(defun m2-model-items (items)
  (declare (xargs :verify-guards nil))
  (if (atom items) nil
    (let ((i (car items)))
      (cons (list (nth 1 i) (if (eq (nth 0 i) :reference) :ref (nth 0 i)) (nth 2 i)
                  (and (eq (nth 0 i) :record) (fnc-chars-string (nth 3 i))))
            (m2-model-items (cdr items))))))
; Resolve every :ref item on a served page through fetch (code 13):
; (mv items ok s fn2-core). A failed fetch leaves the page uncommitted.
(defun m2-resolve (items s fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (atom items) (mv nil t s fn2-core)
    (let ((i (car items)))
      (if (not (eq (nth 1 i) :ref))
          (mv-let (rest ok s fn2-core) (m2-resolve (cdr items) s fn2-core)
            (mv (cons i rest) ok s fn2-core))
        (b* ((pos (nfix (nth 0 i)))
             (mid (nth 2 i))
             ((mv fr & s fn2-core)
              (m2-mini-send 'fetch (fnc-fetch (fn2-cw-chars (coerce mid 'list)) pos) s fn2-core)))
          (if (not (m2-accepted-p fr))
              (mv nil nil (m2-why (m2-reason-text "fetch" fr) s) fn2-core)
            (mv-let (rest ok s fn2-core) (m2-resolve (cdr items) s fn2-core)
              (mv (cons (list pos :record mid (fnc-chars-string (nth 2 fr))) rest) ok s fn2-core))))))))
(defconst *m2-r-size*
  "R is appended as its header and operation tag: its 198,919 octets are past one L frame (one receive)")

; Mini's half after a page (consumer-mini.lisp mini-after-page): references
; fetched, the items committed, the page's next acknowledged, the outbox posted.
(defun m2-post-outbox (outbox lose s fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (cond ((atom outbox) (mv s fn2-core))
        ((eq lose :request) (mv s fn2-core))
        (t (b* (((mv r & s fn2-core)
                 (m2-mini-send 'append (m2-append-frame (caar outbox) (m2-q-lines (caar outbox))) s fn2-core))
                (db (nth 1 s))
                (o (cond ((m2-accepted-p r) (list :accepted nil))
                         ((eq (m2-outcome r) :uncertain) (list :uncertain nil))
                         (t (list :refused (nth 1 r)))))
                (s (if (m2-accepted-p r)
                       (m2-why "append accepted: the kind 28 append result carries no Message-ID to hold across retries" s)
                     (m2-why (m2-reason-text "Mini's append of Q" r) s)))
                (db (mini-put :posted (cons (cons (caar outbox) o) (mini-get :posted db)) db))
                (db (if (or lose (eq (car o) :uncertain)) db
                      (mini-put :outbox (remove1-equal (car outbox) (mini-get :outbox db)) db))))
             (m2-post-outbox (cdr outbox) lose (m2-db db s) fn2-core)))))
(defun m2-page-next (r)
  ; The page's next proposal: its next cursor's position.
  (declare (xargs :verify-guards nil))
  (nfix (nth 1 (nth 2 r))))
(defun m2-after-page (r flag s fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((s (if (eq flag :reclaim-before-fetch)
              (m2-why "reclaim: no served world step reclaims a stored article (fn2-cns has no reclaim of R)" s)
            s))
       (db (mini-put :parked nil (nth 1 s)))
       (s (m2-db db s))
       ((unless (m2-accepted-p r)) (mv (m2-why (m2-reason-text "a page" r) s) fn2-core))
       ((mv items ok s fn2-core) (m2-resolve (m2-model-items (nth 3 (nth 2 r))) s fn2-core))
       (db (nth 1 s)))
    (cond
     ((not ok) (mv s fn2-core))
     ((eq flag :die-before-commit) (mv (m2-db (mini-put :uncertain-ack t db) s) fn2-core))
     (t
      (b* ((db (mini-commit items db))
           ((when (eq flag :die-after-commit)) (mv (m2-db (mini-put :uncertain-ack t db) s) fn2-core))
           (next (m2-page-next r))
           ((mv a & s fn2-core) (m2-mini-send 'ack (fnc-ack (mini-get :fncu db) next) (m2-db db s) fn2-core))
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
       ((mv r & s fn2-core) (m2-mini-send 'position (fnc-position 1) s fn2-core))
       (s (if (m2-accepted-p r) s (m2-why (m2-reason-text "position" r) s)))
       (db (if (m2-accepted-p r) (mini-put :uncertain-ack nil (mini-put :cursor (nfix (nth 2 r)) (nth 1 s))) (nth 1 s))))
    (m2-post-outbox (mini-get :outbox db) nil (m2-db db s) fn2-core)))
; Whatever reached Mini's connection while it had a wait parked is that wait's answer.
(defun m2-woken (new s fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let ((r (cdr (assoc-equal *m2-mini-conn* new))))
    (if (and r (mini-get :parked (nth 1 s))) (m2-after-page (fnc-reply 'wait r) nil s fn2-core) (mv s fn2-core))))

;; Mini's grants (AUTHORITY-20261105 section 5), served ------------------------------
; CONN's one frame: (mv octets s fn2-core), OCTETS what arrived on CONN.
(defun m2-send-on (conn frame s fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* (((mv new clients store fn2-core) (m2-exchange conn frame (nth 0 s) (nth 4 s) fn2-core)))
    (mv (cdr (assoc-equal conn new)) (m2-wired clients store s) fn2-core)))
(defun m2-judge (what got want s)
  (declare (xargs :verify-guards nil))
  (if (equal got want) s (m2-why (concatenate 'string what " did not answer its accepted reply") s)))
; Once: the administrator creates mini and origin; each binds its connection.
(defun m2-auth-setup (s fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* (((when (m2-auth-get :setup s)) (mv s fn2-core))
       ((mv o s fn2-core) (m2-send-on *m2-admin-conn* (fnca-frame 'principal-create (list (fnca-octets "mini"))) s fn2-core))
       (s (m2-judge "principal-create mini" o (fnca-reply 'principal-create :accepted nil (list *m2-mini-id*) nil) s))
       ((mv o s fn2-core) (m2-send-on *m2-admin-conn* (fnca-frame 'principal-create (list (fnca-octets "origin"))) s fn2-core))
       (s (m2-judge "principal-create origin" o (fnca-reply 'principal-create :accepted nil (list *m2-origin-id*) nil) s))
       ((mv o s fn2-core) (m2-send-on *m2-mini-conn* (fnca-frame 'principal-bind (list (fnca-octets "mini"))) s fn2-core))
       (s (m2-judge "Mini's principal-bind" o (fnca-reply 'principal-bind :accepted nil (list *m2-mini-id* 0) nil) s))
       ((mv o s fn2-core) (m2-send-on *m2-origin-conn* (fnca-frame 'principal-bind (list (fnca-octets "origin"))) s fn2-core))
       (s (m2-judge "origin's principal-bind" o (fnca-reply 'principal-bind :accepted nil (list *m2-origin-id* 0) nil) s)))
    (mv (m2-auth-put :setup t s) fn2-core)))
(defun m2-principal (name)
  (declare (xargs :guard t))
  (cond ((equal name "mini") *m2-mini-id*) ((equal name "origin") *m2-origin-id*) (t *m2-reader-id*)))
(defun m2-right (r) (declare (xargs :guard t)) (case r (:consume 0) (:read 1) (otherwise 2)))
(defun m2-stream (g) (declare (xargs :verify-guards nil)) (nfix (cdr (assoc-equal g (cdr (assoc-eq :groups *m2-profile*))))))
; OP (:grant NAME RIGHT TARGET): a grant-set on the administrator's
; connection at the grantee's head, judged by its reply (grant = head).
(defun m2-grant (op s fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* (((mv s fn2-core) (m2-auth-setup s fn2-core))
       (ge (m2-principal (nth 1 op))) (rt (m2-right (nth 2 op)))
       (any (eq (nth 3 op) :any))
       (sc (if any 0 1)) (tg (if any 0 (m2-stream (nth 3 op))))
       (heads (m2-auth-get :heads s)) (eh (nfix (cdr (assoc-equal ge heads))))
       (opn (+ 1 (nfix (m2-auth-get :op s))))
       ((mv o s fn2-core) (m2-send-on *m2-admin-conn* (fnca-frame 'grant-set (list ge rt sc tg 1 eh (list opn))) s fn2-core))
       ((mv g h &) (fnca-set-reply o))
       (s (m2-auth-put :op opn s))
       ((unless (and (posp g) (equal g h)))
        (mv (m2-why (concatenate 'string "grant-set for " (nth 1 op) " did not answer accepted") s) fn2-core)))
    (mv (m2-auth-put :heads (put-assoc-equal ge g heads) s) fn2-core)))

(defun m2-world (op s fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (case (car op)
    (append
     ; Origin appends R on its own connection; Mini's may hold a parked wait.
     (b* ((r (nth 3 op))
          (frame (m2-append-frame (nth 4 op) (m2-r-lines (car r) (cadr r))))
          ((mv new clients store fn2-core) (m2-exchange *m2-origin-conn* frame (nth 0 s) (nth 4 s) fn2-core))
          (s (m2-why *m2-r-size* (m2-wired clients store s)))
          (ro (fnc-reply 'append (cdr (assoc-equal *m2-origin-conn* new))))
          (s (if (m2-accepted-p ro) s (m2-why (m2-reason-text "origin's append of R" ro) s))))
       (m2-woken new s fn2-core)))
    (:grant (m2-grant op s fn2-core))
    (:withdraw (mv (m2-why "withdraw: no served cancel, and fn2-cns delivers no withdrawal report" s) fn2-core))
    (otherwise (mv (m2-why (concatenate 'string "world step " (m2-reply-text (car op)) " is not served") s) fn2-core))))

(defun m2-admit (cap fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((fn2-core (fn2-listener-take-credit *fn2-ctl-admission-ordinal* fn2-core))
       ((mv acode fn2-core) (fn2-machine-admit-fn2-ctl cap 77 3 0 fn2-core))
       ((unless (eq acode :ok)) (mv acode fn2-core))
       ((mv wake fn2-core) (fn2-machine-take-wake fn2-core))
       (fn2-core (fn2-exec-wake wake fn2-core)))
    (mv :ok fn2-core)))

; Process death and cold-restart recovery over the adapter's persisted device:
; a fresh core runs B5 recovery + M7 fn2-member-replay, opens the next writer
; epoch, re-admits the three local control connections, and re-binds Mini and
; origin (judging both principals' recovered identities and authority heads).
(defun m2-crash (s fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((store (car (nth 4 s)))
       (fn2-core (fn2-init-executor *m2-profile* :echo nil fn2-core))
       (rid (fn2-machine-global-id *fn2-recovery-machine-kind* 0 *m2-profile*))
       ((mv start fn2-core) (fn2-recovery-start rid 2 0 fn2-core))
       ((mv & & store & fn2-core) (m2-loop 400000 0 nil store nil fn2-core))
       (done (equal (fn2-machine-phase rid fn2-core) *fn2-recovery-machine-state-done*))
       (class (nth (fn2-machine-rc-class rid fn2-core) *fn2-rec-classes*))
       (stop (fn2-core-stop-reason fn2-core))
       ((unless (and (eq start :ok) done (eq class :intact) (equal stop 0)))
        (mv (m2-why (concatenate 'string "crash recovery answered "
                                 (m2-reply-text (list start done class stop))) s)
            fn2-core))
       ((mv a0 fn2-core) (m2-admit *m2-mini-conn* fn2-core))
       ((mv a1 fn2-core) (m2-admit *m2-origin-conn* fn2-core))
       ((mv a2 fn2-core) (m2-admit *m2-admin-conn* fn2-core))
       ((unless (and (eq a0 :ok) (eq a1 :ok) (eq a2 :ok)))
        (mv (m2-why (concatenate 'string "crash re-admit answered " (m2-reply-text (list a0 a1 a2))) s) fn2-core))
       (clients (list (list nil nil nil nil nil) (list nil nil nil nil nil) (list nil nil nil nil nil)))
       (db (mini-put :parked nil (nth 1 s)))
       (s (m2-db db (m2-wired clients (cons store nil) s)))
       ((unless (m2-auth-get :setup s)) (mv s fn2-core))
       (heads (m2-auth-get :heads s))
       (mh (nfix (cdr (assoc-equal *m2-mini-id* heads))))
       (oh (nfix (cdr (assoc-equal *m2-origin-id* heads))))
       ((mv o s fn2-core) (m2-send-on *m2-mini-conn* (fnca-frame 'principal-bind (list (fnca-octets "mini"))) s fn2-core))
       (s (m2-judge "Mini's post-crash principal-bind" o
                    (fnca-reply 'principal-bind :accepted nil (list *m2-mini-id* mh) nil) s))
       ((mv o s fn2-core) (m2-send-on *m2-origin-conn* (fnca-frame 'principal-bind (list (fnca-octets "origin"))) s fn2-core))
       (s (m2-judge "origin's post-crash principal-bind" o
                    (fnca-reply 'principal-bind :accepted nil (list *m2-origin-id* oh) nil) s)))
    (mv s fn2-core)))

(defun m2-drive (script s fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (atom script) (mv s fn2-core)
    (let ((st (car script)))
      (case (car st)
        (:register
         (b* (((mv r new s fn2-core) (m2-mini-send 'register (fnc-register 1 1) s fn2-core))
              (s (if (m2-accepted-p r) s (m2-why (m2-reason-text "register" r) s)))
              (c (and (m2-accepted-p r) (fnc-reply-cursor 'register (cdr (assoc-equal *m2-mini-conn* new))))))
           (m2-drive (cdr script) (m2-db (mini-put :fncu c (mini-db-init (nfix (nth 2 r)))) s) fn2-core)))
        (:world (b* (((mv s fn2-core) (m2-world (cadr st) s fn2-core))) (m2-drive (cdr script) s fn2-core)))
        (:crash (b* (((mv s fn2-core) (m2-crash s fn2-core))) (m2-drive (cdr script) s fn2-core)))
        (:wait
         (b* (((mv s fn2-core) (m2-settle s fn2-core))
              ((mv r & s fn2-core) (m2-mini-send 'wait (fnc-wait (m2-cursor s) 8 30) s fn2-core))
              ((mv s fn2-core) (if r (m2-after-page r nil s fn2-core)
                                 (mv (m2-db (mini-put :parked t (nth 1 s)) s) fn2-core))))
           (m2-drive (cdr script) s fn2-core)))
        (:turn
         (b* (((mv s fn2-core) (m2-settle s fn2-core))
              ((mv r & s fn2-core)
               (if (mini-get :parked (nth 1 s))
                   (mv nil nil (m2-why "a read while Mini's wait is still parked: the wait never answered" s) fn2-core)
                 (m2-mini-send 'read (fnc-read (m2-cursor s) 8) s fn2-core)))
              ((mv s fn2-core) (if r (m2-after-page r (cadr st) s fn2-core) (mv s fn2-core))))
           (m2-drive (cdr script) s fn2-core)))
        (:stale-ack
         (b* (((mv r & s fn2-core) (m2-mini-send 'ack (fnc-ack (m2-cursor s) (nfix (cadr st))) s fn2-core))
              ; The stale duplicate is refused behind and changes nothing (K2).
              (s (if (and (eq (m2-outcome r) :refused) (equal (nth 1 r) "behind"))
                     s (m2-why (m2-reason-text "a stale duplicate ack" r) s))))
           (m2-drive (cdr script) s fn2-core)))
        (otherwise (m2-drive (cdr script) s fn2-core))))))

;; NNTP GROUP and ARTICLE readback over fn2-conn --------------------------------
(defun m2-pending-accept (left i fn2-ops)
  (declare (xargs :stobjs fn2-ops :verify-guards nil :measure (nfix left)))
  (cond ((or (zp left) (>= (nfix i) (fn2-ops-rows fn2-ops))) nil)
        ((and (equal (fn2-ops-kind (nfix i) fn2-ops) *fn2-action-accept*)
              (equal (fn2-ops-phase (nfix i) fn2-ops) *fn2-op-phase-submitted*))
         (list (nfix i) (fn2-ops-gen (nfix i) fn2-ops)))
        (t (m2-pending-accept (- left 1) (+ 1 (nfix i)) fn2-ops))))

(defun m2-until-gt (xs)
  (declare (xargs :verify-guards nil))
  (cond ((atom xs) nil)
        ((equal (car xs) 62) (list 62))
        (t (let ((r (m2-until-gt (cdr xs)))) (and r (cons (car xs) r))))))

(defun m2-nntp-readback (cut s fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((db (nth 1 s))
       (want-q (and (consp (mini-get :index db)) (null (mini-get :outbox db))))
       (cmds (if want-q
                 (list (concatenate 'string "GROUP " *mini-group*) "ARTICLE 1"
                       (concatenate 'string "GROUP " *mini-reply-group*) "ARTICLE 1" "QUIT")
               (list (concatenate 'string "GROUP " *mini-group*) "ARTICLE 1" "QUIT")))
       (in (fn2-cw-crlf-octets cmds))
       (acc (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (acc)
              (m2-pending-accept (fn2-ops-rows fn2-ops) 0 fn2-ops) acc))
       ((unless acc)
        (mv (m2-why "NNTP readback: no pending listener Accept for fn2-conn" s) fn2-core))
       (io (nth 4 s))
       (clients4 (append (nth 0 s) (list (list in (list (len in)) nil nil nil))))
       (fn2-core (fn2-cw-post-accept (nth 0 acc) (nth 1 acc) 3 77 nil fn2-core))
       ((mv & clients4 store deferred fn2-core)
        (m2-loop 20000 0 clients4 (car io) (cdr io) fn2-core))
       (wire (reverse (nth 2 (nth 3 clients4))))
       (s (m2-wired (take 3 clients4) (cons store deferred) s))
       (prefix-lines
        (append (list "200 fn-nntp experimental server ready"
                      (if (eq cut :c4-changed-source)
                          (concatenate 'string "211 2 1 2 " *mini-group*)
                        (concatenate 'string "211 1 1 1 " *mini-group*))
                      "220 1 <r1@origin> article follows"
                      (concatenate 'string "Xref: fn2.invalid " *mini-group* ":1"))
                (m2-r-lines "<r1@origin>" *mini-r1*)
                (list ".")))
       ((unless want-q)
        (let ((expected (fn2-cw-crlf-octets (append prefix-lines (list "205 closing connection")))))
          (mv (if (equal wire expected) s (m2-why "NNTP readback of R over fn2-conn mismatched" s)) fn2-core)))
       (pre (append (fn2-cw-crlf-octets (append prefix-lines
                                                (list (concatenate 'string "211 1 1 1 " *mini-reply-group*))))
                    (fn2-cw-chars (coerce "220 1 " 'list))))
       (qmid-octets (m2-until-gt (nthcdr (len pre) wire)))
       (qmid (and (consp qmid-octets) (equal (car qmid-octets) 60) (< 2 (len qmid-octets))
                  (fnc-chars-string qmid-octets)))
       (expected
        (and qmid
             (fn2-cw-crlf-octets
              (append prefix-lines
                      (list (concatenate 'string "211 1 1 1 " *mini-reply-group*)
                            (concatenate 'string "220 1 " qmid " article follows")
                            (concatenate 'string "Xref: fn2.invalid " *mini-reply-group* ":1")
                            (concatenate 'string "Message-ID: " qmid))
                      (m2-q-lines "m-o1")
                      (list "." "205 closing connection"))))))
    (mv (if (and expected (equal wire expected))
            s
          (m2-why "NNTP readback of R and Q over fn2-conn mismatched" s))
        fn2-core)))

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
(defun m2-cut-run (cut mutate)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (pass reasons fn2-core)
      (b* ((fn2-core (fn2-init-executor *m2-profile* :echo nil fn2-core))
           ((mv & fn2-core)
            (stobj-let ((fn2-extents (fn2-core-extents fn2-core))) (code fn2-extents)
              (fn2-alloc-begin-epoch 1 fn2-extents) (mv code fn2-core)))
           ((mv a0 fn2-core) (m2-admit *m2-mini-conn* fn2-core))
           ((mv a1 fn2-core) (m2-admit *m2-origin-conn* fn2-core))
           ((mv a2 fn2-core) (m2-admit *m2-admin-conn* fn2-core))
           ((unless (and (eq a0 :ok) (eq a1 :ok) (eq a2 :ok)))
            (mv nil (list (concatenate 'string "admitting the three fn2-ctl connections answered " (m2-reply-text (list a0 a1 a2)))) fn2-core))
           (clients (list (list nil nil nil nil nil) (list nil nil nil nil nil) (list nil nil nil nil nil)))
           (script (append (pairlis$ (make-list (len *mini-grants*) :initial-element :world) (pairlis$ *mini-grants* nil))
                           (cdr (assoc-eq cut *mini-cuts*))))
           ((mv s fn2-core) (m2-drive script (m2-s clients (mini-db-init 0) nil mutate (cons nil nil) nil) fn2-core))
           ((mv s fn2-core)
            (if (equal (fn2-core-stop-reason fn2-core) 0)
                (m2-nntp-readback cut s fn2-core)
              (mv (m2-why (concatenate 'string "the core stopped: " (m2-reply-text (fn2-core-stop-reason fn2-core))) s) fn2-core)))
           (s (if (equal (fn2-core-stop-reason fn2-core) 0) s
                (m2-why (concatenate 'string "the core stopped: " (m2-reply-text (fn2-core-stop-reason fn2-core))) s)))
           (ok (m2-accept cut (nth 1 s)))
           (s (if ok s (m2-why "Mini's acceptance fails over what it observed (e-surface.md 10.1)" s))))
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
       (or (and (stringp (car rs)) (equal (search "register answered (REFUSED " (car rs)) 0))
           (m2-register-refused-p (cdr rs)))))
(defun m2-test-mutation ()
  (declare (xargs :verify-guards nil))
  (mv-let (pass0 r0) (m2-cut-run :c0-wait nil)
    (declare (ignore pass0))
    (mv-let (pass1 r1) (m2-cut-run :c0-wait :register-refused)
      (and (not pass1) (m2-register-refused-p r1) (not (m2-register-refused-p r0))))))
(make-event
 ; The control prints both runs' reasons so a red names what the judge saw.
 (mv-let (pass0 r0) (m2-cut-run :c0-wait nil)
   (mv-let (pass1 r1) (m2-cut-run :c0-wait :register-refused)
     (prog2$ (cw "M2CONTROL plain ~x0 ~x1~%M2CONTROL mutated ~x2 ~x3~%" pass0 r0 pass1 r1)
             (if (m2-test-mutation) (value '(value-triple :m2-control-ok))
               (er soft 'm2-control "the mutated register reply was not judged"))))))

; Cold-restart replay teeth:
; 1) c6-node-crash survives two full node crashes (B5 recovery + M7 replay of
;    principals, accounts, grants, grant-current, authority-head, consumer
;    cursors, groups, articles, overviews, addr, outcomes + NNTP readback of R
;    and Q over fn2-conn) with zero storage/crash/NNTP failures.
(defun m2-test-c6-crash ()
  (declare (xargs :verify-guards nil))
  (mv-let (pass rs) (m2-cut-run :c6-node-crash nil)
    (and (not pass)
         (equal rs
                (list *m2-r-size*
                      "append accepted: the kind 28 append result carries no Message-ID to hold across retries"
                      "Mini's acceptance fails over what it observed (e-surface.md 10.1)")))))
(assert! (m2-test-c6-crash))

; 2) Replayed principals configure their slots in fn2-core-accounts, so a
;    post-crash principal-create allocates slot 4 (never re-issuing mini's
;    slot 1 or origin's slot 3) and binds cleanly.
(defun m2-test-post-crash-principal-create ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (ok fn2-core)
      (b* ((fn2-core (fn2-init-executor *m2-profile* :echo nil fn2-core))
           ((mv & fn2-core)
            (stobj-let ((fn2-extents (fn2-core-extents fn2-core))) (code fn2-extents)
              (fn2-alloc-begin-epoch 1 fn2-extents) (mv code fn2-core)))
           ((mv a0 fn2-core) (m2-admit *m2-mini-conn* fn2-core))
           ((mv a1 fn2-core) (m2-admit *m2-origin-conn* fn2-core))
           ((mv a2 fn2-core) (m2-admit *m2-admin-conn* fn2-core))
           ((unless (and (eq a0 :ok) (eq a1 :ok) (eq a2 :ok))) (mv nil fn2-core))
           (clients (list (list nil nil nil nil nil) (list nil nil nil nil nil) (list nil nil nil nil nil)))
           (s (m2-s clients (mini-db-init 0) nil nil (cons nil nil) nil))
           ((mv s fn2-core) (m2-auth-setup s fn2-core))
           ((mv s fn2-core) (m2-crash s fn2-core))
           (peer2-id (+ (* 4 4294967296) 1))
           ((mv o1 s fn2-core)
            (m2-send-on *m2-admin-conn* (fnca-frame 'principal-create (list (fnca-octets "peer2"))) s fn2-core))
           ((mv o2 s fn2-core)
            (m2-send-on *m2-admin-conn* (fnca-frame 'principal-bind (list (fnca-octets "peer2"))) s fn2-core)))
        (mv (and (null (nth 2 s))
                 (equal o1 (fnca-reply 'principal-create :accepted nil (list peer2-id) nil))
                 (equal o2 (fnca-reply 'principal-bind :accepted nil (list peer2-id 0) nil)))
            fn2-core))
      ok)))
(assert! (m2-test-post-crash-principal-create))
