; Mini's processing transaction against the consumer port (fn2/docs/e-surface.md
; section 10.1), over the reference model. Mini is driven as a client: it
; registers on the report group, waits or reads, commits its own transaction
; (an operation index keyed by Mini's operation, an outbox holding reply Q),
; acknowledges, and posts Q from its outbox with an operation id, so a lost
; reply is settled by repeating with the same id. The cuts are fn1's and
; Mini's: a death after its commit, a lost append reply, a lost ack reply, a
; changed source under the same operation, a cancelled report, a node crash
; under a parked wait, a stale duplicate ack.
(in-package "ACL2")
(include-book "../books/consumer-model")
(include-book "std/testing/assert-bang" :dir :system)

(defconst *mini-group* "dregg.fn.e1")
(defconst *mini-reply-group* "dregg.fn.e1.reply")
(defconst *mini-limits* '(8 65536))   ; 8 items; 64 KiB of report octets
; One AgentGrain: 191,283 octets of signed source carried as a 198,919-octet
; article (the carrier adds 7,636 octets of FN-Authorship), CLIENTS 1.1.
(defconst *mini-source-octets* 191283)
(defconst *mini-article-octets* 198919)
(defun mini-article (tag)
  (declare (xargs :verify-guards nil))
  (concatenate 'string (coerce (make-list (- *mini-article-octets* *mini-source-octets*) :initial-element #\h) 'string)
               tag (coerce (make-list (- *mini-source-octets* (length tag)) :initial-element #\s) 'string)))
(defconst *mini-r1* (mini-article "op=o1;v=1;"))
(defconst *mini-r2* (mini-article "op=o1;v=2;"))   ; another source under the same Mini operation
; Mini's operation for a report, as its E1 adapter derives it from the source.
(defun mini-operation (source)
  (declare (xargs :verify-guards nil))
  (let ((at (search "op=" source)))
    (and at (subseq source (+ at 3) (+ at 5)))))

(defconst *mini-grants*
  `((:grant "mini" :consume :any) (:grant "mini" :read ,*mini-group*) (:grant "mini" :read ,*mini-reply-group*)
    (:grant "mini" :append ,*mini-reply-group*) (:grant "origin" :append ,*mini-group*)
    (:grant "reader" :read ,*mini-group*) (:grant "reader" :read ,*mini-reply-group*)))

;; Mini's own database ----------------------------------------------------------
; :index op -> source; :outbox ((opid . Q) ...) to post; :posted opid -> outcomes seen;
; :evidence (op source) conflicts; :withdrawn mids; :uncertain-ack t when an
; ack's reply was lost (settle with POSITION); :cursor the cursor Mini holds.
(defun mini-db-init (k) (declare (xargs :verify-guards nil))
  (list (cons :index nil) (cons :outbox nil) (cons :posted nil) (cons :evidence nil)
        (cons :withdrawn nil) (cons :gaps nil) (cons :uncertain-ack nil) (cons :cursor k)))
(defun mini-get (k db) (declare (xargs :verify-guards nil)) (cdr (assoc-eq k db)))
(defun mini-put (k v db) (declare (xargs :verify-guards nil)) (put-assoc-eq k v db))
(defun mini-q (op) (declare (xargs :verify-guards nil)) (list nil (concatenate 'string "Q for " op) nil))
(defun mini-opid (op) (declare (xargs :verify-guards nil)) (concatenate 'string "m-" op))

; Mini's transaction over one page's items (one atomic commit in its own
; store): a new operation gets its index row and Q in the outbox; the same
; source again reuses the prior verdict (Q is re-posted with the same opid);
; another source under the same operation is conflict evidence, no second Q.
(defun mini-commit (items db)
  (declare (xargs :verify-guards nil))
  (if (atom items) db
    (let* ((i (car items)) (type (fn2-cns-item-type i)) (mid (fn2-cns-item-mid i))
           (source (and (eq type :record) (fn2-cns-item-payload i)))
           (op (and (stringp source) (mini-operation source)))
           (prior (and op (assoc-equal op (mini-get :index db))))
           (db (cond ((member type '(:withdrawn :withdrawal)) (mini-put :withdrawn (cons mid (mini-get :withdrawn db)) db))
                     ; An unavailable item is acknowledged past knowingly: the ack is the waiver.
                     ((eq type :gap) (mini-put :gaps (cons mid (mini-get :gaps db)) db))
                     ((not op) db)
                     ((not prior) (mini-put :outbox (cons (cons (mini-opid op) (mini-q op)) (mini-get :outbox db))
                                            (mini-put :index (cons (cons op source) (mini-get :index db)) db)))
                     ((equal (cdr prior) source)
                      (if (assoc-equal (mini-opid op) (mini-get :outbox db)) db
                        (mini-put :outbox (cons (cons (mini-opid op) (mini-q op)) (mini-get :outbox db)) db)))
                     (t (mini-put :evidence (cons (list op source) (mini-get :evidence db)) db)))))
      (mini-commit (cdr items) db))))

;; The driver: each step sends exactly the requests Mini would and records them.
; (mv st db ops-reversed). FAULT is the node's.
(defun mini-send (op st ops fault)
  (declare (xargs :verify-guards nil))
  (mv-let (o answers st2) (fn2-cns-step op st fault)
    (mv o answers st2 (cons op ops))))
(defun mini-post-outbox (outbox lose st db ops fault)
  ; Post every outbox entry; a lost reply leaves it in the outbox (uncertain).
  ; LOSE :request: the request never reached the node (nothing committed).
  (declare (xargs :verify-guards nil))
  (cond ((atom outbox) (mv st db ops))
        ((eq lose :request) (mv st db ops))
        (t (mv-let (o answers st ops) (mini-send (list 'append "mini" *mini-reply-group* (cdar outbox) (caar outbox)) st ops fault)
      (declare (ignore answers))
      (let* ((db (mini-put :posted (cons (cons (caar outbox) o) (mini-get :posted db)) db))
             (db (if (or lose (eq (fn2-cns-class o) :uncertain)) db
                   (mini-put :outbox (remove1-equal (car outbox) (mini-get :outbox db)) db))))
        (mini-post-outbox (cdr outbox) lose st db ops fault))))))
(defun mini-resolve (items st ops fault)
  ; Fetch every reference item: (mv items ok st ops); a failed fetch means
  ; the page is not processed (it never becomes processed content).
  (declare (xargs :verify-guards nil))
  (if (atom items) (mv nil t st ops)
    (let ((i (car items)))
      (if (not (eq (fn2-cns-item-type i) :ref))
          (mv-let (rest ok st ops) (mini-resolve (cdr items) st ops fault) (mv (cons i rest) ok st ops))
        (mv-let (o answers st ops) (mini-send (list 'fetch "mini" (list (fn2-cns-item-mid i))) st ops fault)
          (declare (ignore answers))
          (if (not (eq (fn2-cns-class o) :accepted)) (mv nil nil st ops)
            (mv-let (rest ok st ops) (mini-resolve (cdr items) st ops fault)
              (mv (cons (list (fn2-cns-item-pos i) :record (fn2-cns-item-mid i) (car (cadr o)) (nth 4 i)) rest) ok st ops))))))))
(defun mini-after-page (o flag st db ops fault)
  ; Mini's half after a page: fetch references, commit, ack, post. FLAG: nil,
  ; :die-before-commit, :die-after-commit, :lose-append, :append-lost, :lose-ack,
  ; :reclaim-before-fetch.
  (declare (xargs :verify-guards nil))
  (mv-let (o2 answers st ops)
    (if (eq flag :reclaim-before-fetch) (mini-send '(:reclaim nil 1) st ops fault) (mv nil nil st ops))
    (declare (ignore o2 answers))
  (mv-let (items ok st ops) (mini-resolve (fn2-cns-page-items o) st ops fault)
  (cond
   ((or (not (eq (fn2-cns-class o) :accepted)) (not ok)) (mv st db ops))
   ((eq flag :die-before-commit) (mv st (mini-put :uncertain-ack t db) ops))
   (t
    (let ((db (mini-commit items db)))
      (if (eq flag :die-after-commit)
          (mv st (mini-put :uncertain-ack t db) ops)       ; it restarts knowing nothing of its cursor
        (mv-let (a answers st ops) (mini-send (list 'ack "mini" (fn2-cns-page-next o)) st ops fault)
          (declare (ignore answers))
          (let ((db (if (or (eq flag :lose-ack) (not (eq (fn2-cns-class a) :accepted))) (mini-put :uncertain-ack t db)
                      (mini-put :cursor (fn2-cns-page-next o) db))))
            (mini-post-outbox (mini-get :outbox db)
                              (case flag (:lose-append t) (:append-lost :request) (otherwise nil)) st db ops fault))))))))))
(defun mini-settle (st db ops fault)
  ; A restarted or uncertain Mini asks POSITION first, then re-posts its outbox.
  (declare (xargs :verify-guards nil))
  (if (not (mini-get :uncertain-ack db)) (mini-post-outbox (mini-get :outbox db) nil st db ops fault)
    (mv-let (o answers st ops) (mini-send (list 'position "mini" "m") st ops fault)
      (declare (ignore answers))
      (let ((db (if (eq (fn2-cns-class o) :accepted) (mini-put :uncertain-ack nil (mini-put :cursor (car (cadr o)) db)) db)))
        (mini-post-outbox (mini-get :outbox db) nil st db ops fault)))))
(defun mini-answers (answers flag st db ops fault)
  ; A world step's answers: Mini's parked wait may have answered.
  (declare (xargs :verify-guards nil))
  (let ((a (assoc-equal (cons "mini" "m") answers)))
    (if a (mini-after-page (cdr a) flag st db ops fault) (mv st db ops))))

(defun mini-drive (script st db ops fault)
  (declare (xargs :verify-guards nil))
  (if (atom script) (mv st db ops)
    (let ((s (car script)))
      (case (car s)
        (:register
         (mv-let (o answers st ops) (mini-send (list 'register "mini" "m" (list *mini-group*) :history) st ops fault)
           (declare (ignore answers))
           (mini-drive (cdr script) st (mini-db-init (car (cadr o))) ops fault)))
        (:world
         (mv-let (o answers st ops) (mini-send (cadr s) st ops fault)
           (declare (ignore o))
           (mv-let (st db ops) (mini-answers answers nil st db ops fault)
             (mini-drive (cdr script) st db ops fault))))
        (:crash
         (mv-let (o answers st ops) (mini-send '(:crash) st ops fault)
           (declare (ignore o answers))
           (mini-drive (cdr script) st db ops fault)))
        (:wait
         (mv-let (st db ops) (mini-settle st db ops fault)
           (mv-let (o answers st ops) (mini-send (list 'wait "mini" (mini-get :cursor db) *mini-limits* 3600) st ops fault)
             (declare (ignore answers))
             (mv-let (st db ops) (if (eq o :parked) (mv st db ops) (mini-after-page o nil st db ops fault))
               (mini-drive (cdr script) st db ops fault)))))
        (:turn
         (mv-let (st db ops) (mini-settle st db ops fault)
           (mv-let (o answers st ops) (mini-send (list 'read "mini" (mini-get :cursor db) *mini-limits*) st ops fault)
             (declare (ignore answers))
             (mv-let (st db ops) (mini-after-page o (cadr s) st db ops fault)
               (mini-drive (cdr script) st db ops fault)))))
        (:stale-ack
         ; A delayed duplicate of an earlier ack arrives with an older position.
         (let ((k (mini-get :cursor db)))
           (mv-let (o answers st ops) (mini-send (list 'ack "mini" (update-nth 8 (cadr s) k)) st ops fault)
             (declare (ignore o answers))
             (mini-drive (cdr script) st db ops fault))))
        (otherwise (mini-drive (cdr script) st db ops fault))))))

(defun mini-run (script fault)
  ; (mv final-state db ops)
  (declare (xargs :verify-guards nil))
  (mv-let (st db ops) (mini-drive (append (pairlis$ (make-list (len *mini-grants*) :initial-element :world)
                                                    (pairlis$ *mini-grants* nil))
                                          script)
                                  (fn2-cns-init "fn2-history" "fn2-incarnation") nil nil fault)
    (mv st db (reverse ops))))

(defconst *mini-append-r1* `(:world (append "origin" ,*mini-group* ("<r1@origin>" ,*mini-r1* nil) "o-r1")))
(defconst *mini-append-r2* `(:world (append "origin" ,*mini-group* ("<r2@origin>" ,*mini-r2* nil) "o-r2")))
(defconst *mini-cuts*
  `((:c0-wait (:register) (:wait) ,*mini-append-r1* (:turn nil))
    (:c1-die-after-commit (:register) ,*mini-append-r1* (:turn :die-after-commit) (:turn nil))
    (:c2-lost-append-reply (:register) ,*mini-append-r1* (:turn :lose-append) (:turn nil))
    (:c3-lost-ack-reply (:register) ,*mini-append-r1* (:turn :lose-ack) (:turn nil))
    (:c4-changed-source (:register) ,*mini-append-r1* (:turn nil) ,*mini-append-r2* (:turn nil))
    (:c5-cancelled (:register) ,*mini-append-r1* (:world (:withdraw "origin" "<r1@origin>")) (:turn nil))
    (:c6-node-crash (:register) (:wait) (:crash) ,*mini-append-r1* (:wait) (:crash) (:turn nil))
    (:c7-stale-ack (:register) ,*mini-append-r1* (:turn nil) (:stale-ack 0) (:turn nil))
    (:c8-withdrawn-after-ack (:register) ,*mini-append-r1* (:turn nil) (:world (:withdraw "origin" "<r1@origin>")) (:turn nil))
    (:c9-die-before-commit (:register) ,*mini-append-r1* (:turn :die-before-commit) (:turn nil))
    (:c10-append-never-arrived (:register) ,*mini-append-r1* (:turn :append-lost) (:turn nil))
    (:c11-reclaimed-before-fetch (:register) ,*mini-append-r1* (:turn :reclaim-before-fetch) (:turn nil))))

;; The acceptance (e-surface.md 10.1) -------------------------------------------
(defun mini-q-articles (log)
  (declare (xargs :verify-guards nil))
  (cond ((atom log) nil)
        ((and (eq (fn2-cns-ev-kind (car log)) :article) (equal (fn2-cns-ev-streams (car log)) (list *mini-reply-group*)))
         (cons (fn2-cns-ev-mid (car log)) (mini-q-articles (cdr log))))
        (t (mini-q-articles (cdr log)))))
(defun mini-accepted-mids (posted opid)
  ; The Message-IDs of every accepted outcome Mini saw for OPID.
  (declare (xargs :verify-guards nil))
  (cond ((atom posted) nil)
        ((and (equal (caar posted) opid) (eq (car (cdar posted)) :accepted))
         (cons (car (cadr (cdar posted))) (mini-accepted-mids (cdr posted) opid)))
        (t (mini-accepted-mids (cdr posted) opid))))
(defun mini-accept (cut st db)
  ; One Q article per operation Mini processed (none for a report withdrawn
  ; or unavailable before it was processed), its Message-ID the same on every retry,
  ; the outbox drained, R's octets at Mini equal to NNTP's ARTICLE, GROUP
  ; showing R and Q, and the cut's own expectation.
  (declare (xargs :verify-guards nil))
  (let* ((qs (mini-q-articles (fn2-cns-get :log st)))
         (ops (strip-cars (mini-get :index db)))
         (mids (mini-accepted-mids (mini-get :posted db) "m-o1")))
    (and (no-duplicatesp-equal qs)
         (equal (len qs) (len ops))
         (null (mini-get :outbox db))
         (or (null mids) (equal (remove-duplicates-equal mids) (list "<op-mini-m-o1@node>")))
         (case cut
           (:c8-withdrawn-after-ack (and (equal (len qs) 1) (equal (mini-get :withdrawn db) (list "<r1@origin>"))
                                         (null (fn2-cns-nntp-article st "<r1@origin>" nil))))
           (:c11-reclaimed-before-fetch (and (null qs) (equal (mini-get :gaps db) (list "<r1@origin>"))))
           (:c4-changed-source (and (equal (len qs) 1) (equal (mini-get :evidence db) (list (list "o1" *mini-r2*)))))
           (:c5-cancelled (and (null qs) (equal (mini-get :withdrawn db) (list "<r1@origin>" "<r1@origin>"))
                               (null (fn2-cns-nntp-article st "<r1@origin>" nil))))
           (otherwise (and (equal (len qs) 1)
                           (equal (cdr (assoc-equal "o1" (mini-get :index db))) *mini-r1*)
                           (equal (fn2-cns-nntp-article st "<r1@origin>" nil) *mini-r1*)
                           (equal (length *mini-r1*) *mini-article-octets*)
                           (equal (fn2-cns-nntp-group *mini-group* (fn2-cns-get :log st)) '((1 . "<r1@origin>")))
                           (equal (fn2-cns-nntp-group *mini-reply-group* (fn2-cns-get :log st))
                                  '((1 . "<op-mini-m-o1@node>")))))))))
(defun mini-keystones (ops fault)
  (declare (xargs :verify-guards nil))
  (let ((trace (fn2-cns-trace ops fault)))
    (list :k0 (fn2-cns-declared-p trace) :k1 (fn2-cns-k1-trace trace *mini-limits* fault) :k2 (fn2-cns-k2 trace)
          :k3 (fn2-cns-k3 trace) :k4 (fn2-cns-k4 trace) :k4b (fn2-cns-k4b trace) :k5 (fn2-cns-k5 trace fault) :k6 (fn2-cns-k6 trace fault)
          :k7 (fn2-cns-k7 trace) :k8 (fn2-cns-k8 trace))))
(defun mini-all-true (plist) (declare (xargs :verify-guards nil))
  (or (atom plist) (and (cadr plist) (mini-all-true (cddr plist)))))
(defun mini-cut-ok (cut fault)
  (declare (xargs :verify-guards nil))
  (mv-let (st db ops) (mini-run (cdr (assoc-eq cut *mini-cuts*)) fault)
    (and (mini-accept cut st db) (mini-all-true (mini-keystones ops fault)))))
(defun mini-cuts-ok (cuts)
  (declare (xargs :verify-guards nil))
  (or (atom cuts) (and (mini-cut-ok (caar cuts) nil) (mini-cuts-ok (cdr cuts)))))

;; The teeth (owed-consumer.lisp names them) ----------------------------------
(defun fn2-cns-test-mini () (declare (xargs :verify-guards nil)) (mini-cuts-ok *mini-cuts*))
(defun mini-keystone-under (cut fault key)
  (declare (xargs :verify-guards nil))
  (mv-let (st db ops) (mini-run (cdr (assoc-eq cut *mini-cuts*)) fault)
    (declare (ignore st db))
    (cadr (member-eq key (mini-keystones ops fault)))))
(defun fn2-cns-test-mini-negative ()
  ; Each fault is caught by the keystone that names it, on the cut that exercises it.
  (declare (xargs :verify-guards nil))
  (and (not (mini-keystone-under :c7-stale-ack :rewind :k2))
       (not (mini-keystone-under :c2-lost-append-reply :reappend :k3))
       (not (mini-keystone-under :c0-wait :stale-wait :k4))
       (not (mini-keystone-under :c0-wait :lost-wake :k4b))
       (not (mini-keystone-under :c0-wait :rerender :k5))
       (not (mini-keystone-under :c0-wait :equal-behind :k6))))

(assert! (fn2-cns-test-mini))
(assert! (fn2-cns-test-mini-negative))

; K0's negative: a trace whose ack answered a word the port does not give ack.
(defun fn2-cns-test-declared-negative ()
  (declare (xargs :verify-guards nil))
  (and (not (fn2-cns-declared-p (list (list (list 'ack "mini" nil) '(:refused duplicate) nil nil nil))))
       (not (fn2-cns-declared-p (list (list (list 'read "mini" nil nil) '(:uncertain :log-write) nil nil nil))))))
(assert! (fn2-cns-test-declared-negative))
