; Served authority's keystone (AUTHORITY-20261105 section 6; CRITICAL:
; authorization, identity-binding; Ruling 22's evidence package).
;
; The subject is the served core itself: fn2-oa-trace runs a script through
; fn2-init-executor's core, the FNCT adapter (fn2-cw-adapter-one) and
; fn2-turn, one new owner connection per round, every frame on the wire
; (kind 29 authority requests, kind 4 consumer requests) and every reply read
; off the wire by the list-level clients (tests/authority-client,
; tests/fnct-client), never by the served codecs. fn2-oa-enforced-p judges
; the trace against an independent replay of what the replies themselves
; establish (the principals created, the bindings accepted, the grants set),
; in reply order: rounds run to quiet one after another, so reply order is
; the store's commit order for every mutation the trace contains.
;
; PERTURB names which of the statement's three hypotheses a run removes
; (nil: none, the served core as it is). Each removal is a state change the
; driver makes between turns, never a second copy of the served code:
;   :binding      a bound connection's acting principal is rewritten to the
;                 first principal the trace created (binding removed);
;   :current      a consume decision about to read its current grant's row
;                 reads the first grant the trace set instead (current-grant
;                 validation removed: a pinned grant decides);
;   :publication  a consume decision about to read its current grant's
;                 row reads the grant published just before the newest one
;                 (publication coherence removed: the reader's view is not
;                 the published grant state).
(in-package "ACL2")
(include-book "owed-txn")
(include-book "../tests/authority-client")
(fn2-book-layer :e)

(defconst *fn2-oa-groups* '(("dregg.fn.e1" . 1) ("dregg.fn.e1.reply" . 2)))
;; tests/authority-served's append profile: authority served, the owner at
;; account slot 2, eight control connections, two consumer request rows
(defconst *fn2-oa-profile*
  ;; T 4: fn2-txn's row, fn2-auth's and the two consumer rows' successors (fn2-txn-consumer-share)
  (put-assoc-equal :t 4
  (put-assoc-equal :cns 2
   (put-assoc-equal :groups *fn2-oa-groups*
    (put-assoc-equal :control-connections 8
     (put-assoc-equal :authority 1
      (put-assoc-equal :owner-account 2 *fn2-txn-posting-profile*)))))))

;; ---------------------------------------------------------------------------
;; The script. A round is (AUTH-STEPS CNS-STEPS) on one new connection: its
; authority frames first, then its consumer frames.
;   (:create NAME) (:bind NAME) (:set NAME RIGHT SCOPE GROUP ENABLED)
;   (:append OP MID GROUP) (:register CID) (:position CID)
; RIGHT :consume :read :append; SCOPE :own (target 0) or :stream (GROUP's id).
(defun fn2-oa-right (r) (declare (xargs :guard t)) (case r (:consume 0) (:read 1) (otherwise 2)))
(defun fn2-oa-scope (s) (declare (xargs :guard t)) (if (eq s :own) 0 1))
(defun fn2-oa-auth-step-p (s)
  (declare (xargs :guard t))
  (and (true-listp s)
       (case (car s)
         ((:create :bind) (and (equal (len s) 2) (stringp (cadr s))))
         (:set (and (equal (len s) 6) (stringp (nth 1 s)) (member-eq (nth 2 s) '(:consume :read :append))
                    (member-eq (nth 3 s) '(:own :stream)) (or (null (nth 4 s)) (stringp (nth 4 s)))
                    (member (nth 5 s) '(0 1))))
         (otherwise nil))))
(defun fn2-oa-cns-step-p (s)
  (declare (xargs :guard t))
  (and (true-listp s)
       (case (car s)
         (:append (and (equal (len s) 4) (posp (nth 1 s)) (stringp (nth 2 s)) (stringp (nth 3 s))))
         ((:register :position) (and (equal (len s) 2) (posp (nth 1 s))))
         (otherwise nil))))
(defun fn2-oa-steps-p (xs pred)
  (declare (xargs :guard t))
  (if (atom xs) (null xs)
    (and (if (eq pred :auth) (fn2-oa-auth-step-p (car xs)) (fn2-oa-cns-step-p (car xs)))
         (fn2-oa-steps-p (cdr xs) pred))))
(defun fn2-oa-rounds-p (script)
  (declare (xargs :guard t))
  (if (atom script) (null script)
    (and (true-listp (car script)) (equal (len (car script)) 2)
         (fn2-oa-steps-p (car (car script)) :auth) (fn2-oa-steps-p (cadr (car script)) :cns)
         (fn2-oa-rounds-p (cdr script)))))
;; at most six rounds: a seventh admitted control connection is not answered
;; in this profile (lane authority's finding, named in its READY)
(defun fn2-oa-script-p (script)
  (declare (xargs :guard t))
  (and (true-listp script) (<= (len script) 6)
       (fn2-oa-rounds-p script)))

;; ---------------------------------------------------------------------------
;; The driver's view (to build frames only; the judge keeps its own): the
;; directory NAME -> id and each principal's head, from the replies.
(defun fn2-oa-o (s) (declare (xargs :verify-guards nil)) (fnca-octets s))
;; GROUP's stream id in GS (the trace's lookups through fn2-groups), 0 for none
(defun fn2-oa-gid (g gs) (declare (xargs :verify-guards nil)) (if (stringp g) (nfix (cdr (assoc-equal g gs))) 0))
(defun fn2-oa-id (name dir) (declare (xargs :verify-guards nil)) (nfix (cdr (assoc-equal name dir))))
(defun fn2-oa-auth-frame (s dir heads op gs)
  (declare (xargs :verify-guards nil))
  (case (car s)
    (:create (fnca-frame 'principal-create (list (fn2-oa-o (nth 1 s)))))
    (:bind (fnca-frame 'principal-bind (list (fn2-oa-o (nth 1 s)))))
    (otherwise
     (let ((ge (fn2-oa-id (nth 1 s) dir)))
       (fnca-frame 'grant-set (list ge (fn2-oa-right (nth 2 s)) (fn2-oa-scope (nth 3 s)) (fn2-oa-gid (nth 4 s) gs)
                                    (nth 5 s) (nfix (cdr (assoc-equal ge heads))) (list op)))))))
(defun fn2-oa-article (mid group)
  (declare (xargs :verify-guards nil))
  (fn2-cw-crlf-octets (list "From: oa@example.invalid" "Subject: oa" (concatenate 'string "Newsgroups: " group)
                            (concatenate 'string "Message-ID: " mid) "" "body")))
(defun fn2-oa-cns-frame (s)
  (declare (xargs :verify-guards nil))
  (case (car s)
    (:append (fnc-append (nth 1 s) (fn2-oa-article (nth 2 s) (nth 3 s))))
    (:register (fnc-register (nth 1 s) 1))
    (otherwise (fnc-position (nth 1 s)))))
(defun fn2-oa-cns-frames (xs) (declare (xargs :verify-guards nil)) (if (atom xs) nil (cons (fn2-oa-cns-frame (car xs)) (fn2-oa-cns-frames (cdr xs)))))
(defun fn2-oa-cns-verb (s) (declare (xargs :verify-guards nil)) (case (car s) (:append 'append) (:register 'register) (otherwise 'position)))
(defun fn2-oa-cns-verbs (xs) (declare (xargs :verify-guards nil)) (if (atom xs) nil (cons (fn2-oa-cns-verb (car xs)) (fn2-oa-cns-verbs (cdr xs)))))

;; A kind 30 reply's payload: (CODE CLASS V1 V2) with CLASS :accepted or
; :other, V1 V2 the first two result fields (LEB128) when accepted.
(defun fn2-oa-k30 (pl)
  (declare (xargs :verify-guards nil))
  (if (not (and (consp pl) (equal (nth 1 pl) 0) (equal (nth 2 pl) 0) (equal (nth 3 pl) 0)))
      (list (car pl) :other 0 0)
    (mv-let (a r1) (fnca-leb (nthcdr 4 pl) 0 0)
      (mv-let (b r2) (fnca-leb r1 0 0) (declare (ignore r2))
        (list (car pl) :accepted (nfix a) (nfix b))))))
;; the first N kind 30 replies of XS and the octets after them
(defun fn2-oa-k30s (n xs)
  (declare (xargs :verify-guards nil :measure (nfix n)))
  (if (zp n) (mv nil xs)
    (mv-let (pl rest) (fnca-unseal xs)
      (mv-let (rs tail) (fn2-oa-k30s (- n 1) rest)
        (mv (cons (fn2-oa-k30 pl) rs) tail)))))

;; The driver's view after a round's authority replies.
(defun fn2-oa-learn (steps replies dir heads)
  (declare (xargs :verify-guards nil))
  (if (or (atom steps) (atom replies)) (mv dir heads)
    (let* ((s (car steps)) (r (car replies)) (ok (eq (nth 1 r) :accepted)))
      (fn2-oa-learn (cdr steps) (cdr replies)
                    (if (and ok (eq (car s) :create)) (put-assoc-equal (nth 1 s) (nth 2 r) dir) dir)
                    (if (and ok (eq (car s) :set)) (put-assoc-equal (fn2-oa-id (nth 1 s) dir) (nth 3 r) heads) heads)))))
(defun fn2-oa-auth-frames (steps dir heads op gs)
  (declare (xargs :verify-guards nil))
  (if (atom steps) nil
    (cons (fn2-oa-auth-frame (car steps) dir heads op gs) (fn2-oa-auth-frames (cdr steps) dir heads (+ 1 op) gs))))
;; the grant ids of a round's accepted grant-sets, in order
(defun fn2-oa-grants-of (replies steps)
  (declare (xargs :verify-guards nil))
  (cond ((or (atom replies) (atom steps)) nil)
        ((and (eq (car (car steps)) :set) (eq (nth 1 (car replies)) :accepted))
         (cons (nth 2 (car replies)) (fn2-oa-grants-of (cdr replies) (cdr steps))))
        (t (fn2-oa-grants-of (cdr replies) (cdr steps)))))
;; the grant a perturbed decision reads: the first the trace set (:current),
;; the one before the newest (:publication)
(defun fn2-oa-pin (perturb seen)
  (declare (xargs :verify-guards nil))
  (nfix (if (eq perturb :current) (car seen) (and (consp (cdr seen)) (nth (- (len seen) 2) seen)))))

;; ---------------------------------------------------------------------------
;; The perturbations, between turns (see the header).
(defun fn2-oa-forge-ctl (k first fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix k)))
  (if (zp k) fn2-core
    (let* ((c (+ (fn2-machine-kind-base *fn2-ctl-kind* fn2-core) (- k 1)))
           (fn2-core (if (and (eq (fn2-ctl-snapshot-read-code c fn2-core) :ok)
                              (equal (fn2-ctl-row-admin c fn2-core) 0)
                              (posp (fn2-ctl-row-principal c fn2-core)) (posp first))
                         (fn2-ctl-put-core c (principal first))
                       fn2-core)))
      (fn2-oa-forge-ctl (- k 1) first fn2-core))))
(defun fn2-oa-forge-cns (k perturb pin fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix k)))
  (if (zp k) fn2-core
    (let* ((c (+ (fn2-machine-kind-base *fn2-cns-kind* fn2-core) (- k 1)))
           (live (eq (fn2-cns-snapshot-read-code c fn2-core) :ok))
           (xs (if live (fn2-cns-row-xstep c fn2-core) 0))
           (fn2-core (if (and live (member-eq perturb '(:current :publication)) (equal xs 3) (posp pin))
                         (fn2-cns-put-core c (xgrant pin))
                       fn2-core)))
      (fn2-oa-forge-cns (- k 1) perturb pin fn2-core))))
(defun fn2-oa-perturb (perturb first pin fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (case perturb
    (:binding (fn2-oa-forge-ctl (fn2-machine-connection-count *fn2-ctl-admission-ordinal* fn2-core) first fn2-core))
    ((:current :publication)
     (fn2-oa-forge-cns (fn2-machine-connection-count *fn2-cns-admission-ordinal* fn2-core) perturb pin fn2-core))
    (otherwise fn2-core)))
;; fn2-cw-loop with the perturbation after every turn (nil: fn2-cw-loop's steps exactly)
(defun fn2-oa-loop (fuel idle accepted clients store perturb first pin fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix fuel)))
  (if (zp fuel) (mv :fuel clients store fn2-core)
    (b* (((mv & nobs nvisits nactions fn2-core) (fn2-turn fn2-core))
         (fn2-core (fn2-oa-perturb perturb first pin fn2-core))
         ((mv took accepted clients store fn2-core) (fn2-cw-adapter-one accepted clients store fn2-core))
         (idle (if (or took (< 0 nobs) (< 0 nvisits) (< 0 nactions)) 0 (+ 1 idle))))
      (if (or (<= 3 idle) (not (equal (fn2-core-stop-reason fn2-core) 0)))
          (mv :quiet clients store fn2-core)
        (fn2-oa-loop (- fuel 1) idle accepted clients store perturb first pin fn2-core)))))
(defun fn2-oa-admit (cap fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((fn2-core (fn2-listener-take-credit *fn2-ctl-admission-ordinal* fn2-core))
       ((mv acode fn2-core) (fn2-machine-admit-fn2-ctl cap 77 3 0 fn2-core))
       ((unless (eq acode :ok)) (mv acode fn2-core))
       ((mv wake fn2-core) (fn2-machine-take-wake fn2-core))
       (fn2-core (fn2-exec-wake wake fn2-core)))
    (mv :ok fn2-core)))
(defun fn2-oa-wire (frames)
  (declare (xargs :verify-guards nil))
  (if (atom frames) (mv nil nil)
    (mv-let (bytes sizes) (fn2-oa-wire (cdr frames))
      (mv (append (car frames) bytes) (cons (len (car frames)) sizes)))))

;; The groups' stream ids, looked up through fn2-groups as a reader does
;; (tests/authority-served's fn2-as-group): (mv ((NAME . ID) ...) fn2-core).
(defun fn2-oa-gdrive (fuel slot gen len fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (zp fuel) (mv :fuel 0 fn2-core)
    (mv-let (code g fn2-core) (fn2-group-lookup 0 slot gen 0 len 5 1 1 4096 fn2-core)
      (if (eq code :more) (fn2-oa-gdrive (- fuel 1) slot gen len fn2-core) (mv code g fn2-core)))))
(defun fn2-oa-write (bytes slot gen off fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (atom bytes) (mv :ok fn2-core)
    (mv-let (code fn2-core) (fn2-core-write slot gen off (car bytes) 5 1 1 fn2-core)
      (if (eq code :ok) (fn2-oa-write (cdr bytes) slot gen (+ 1 off) fn2-core) (mv code fn2-core)))))
(defun fn2-oa-groups (names fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (atom names) (mv nil fn2-core)
    (b* (((mv & slot gen fn2-core) (fn2-core-reserve 1 5 1 1 fn2-core))
         (octets (fn2-oa-o (car names)))
         ((mv & fn2-core) (fn2-oa-write octets slot gen 0 fn2-core))
         ((mv code g fn2-core) (fn2-oa-gdrive 20 slot gen (len octets) fn2-core))
         ((mv & fn2-core) (fn2-core-release slot gen 5 1 1 fn2-core))
         ((mv rest fn2-core) (fn2-oa-groups (cdr names) fn2-core)))
      (mv (cons (cons (car names) (if (eq code :ok) (nfix g) 0)) rest) fn2-core))))
;; (CLASS WORD) of each consumer reply
(defun fn2-oa-class-words (rs)
  (declare (xargs :verify-guards nil))
  (if (atom rs) nil (cons (list (nth 0 (car rs)) (nth 1 (car rs))) (fn2-oa-class-words (cdr rs)))))
;; The rounds from K: (mv rounds fn2-core), each round (STEPS AUTH-REPLIES
; CNS-REPLIES STATUS); an unadmitted connection ends the trace (:admit).
(defun fn2-oa-rounds (script k clients dir heads op perturb seen gs fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil :measure (len script)))
  (if (atom script) (mv nil fn2-core)
    (b* ((auth (car (car script))) (cns (cadr (car script)))
         (frames (append (fn2-oa-auth-frames auth dir heads op gs) (fn2-oa-cns-frames cns)))
         ((mv acode fn2-core) (fn2-oa-admit k fn2-core))
         ((unless (eq acode :ok)) (mv (list (list (car script) nil nil (list :admit acode))) fn2-core))
         (clients (append clients (list (mv-let (b s) (fn2-oa-wire frames) (list b s nil nil)))))
         (first (nfix (cdr (car dir))))
         ((mv status clients & fn2-core)
          (fn2-oa-loop 4000 0 (len clients) clients nil perturb first (fn2-oa-pin perturb seen) fn2-core))
         (wire (car (nth k (fn2-cw-results clients))))
         ((mv areplies rest) (fn2-oa-k30s (len auth) wire))
         (creplies (fn2-oa-class-words (fnc-replies (fn2-oa-cns-verbs cns) rest)))
         ((mv dir heads) (fn2-oa-learn auth areplies dir heads))
         (seen (append seen (fn2-oa-grants-of areplies auth)))
         ((mv more fn2-core) (fn2-oa-rounds (cdr script) (+ 1 k) clients dir heads (+ op (len auth)) perturb seen gs fn2-core)))
      (mv (cons (list (car script) areplies creplies status) more) fn2-core))))
(defun fn2-oa-trace (script perturb)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (r fn2-core)
      (b* ((fn2-core (fn2-init-executor *fn2-oa-profile* :echo nil fn2-core))
           ((mv & fn2-core)
            (stobj-let ((fn2-extents (fn2-core-extents fn2-core))) (code fn2-extents)
              (fn2-alloc-begin-epoch 1 fn2-extents) (mv code fn2-core)))
           ((mv gs fn2-core) (fn2-oa-groups (strip-cars *fn2-oa-groups*) fn2-core))
           ((mv rounds fn2-core) (fn2-oa-rounds script 0 nil nil nil 1 perturb nil gs fn2-core)))
        (mv (cons gs rounds) fn2-core))
      r)))

;; ---------------------------------------------------------------------------
;; The judge: an independent replay of what the replies establish.
; DIR name -> id (accepted creates), GRANTS (grantee right scope target) ->
; enabled (accepted grant-sets), P the round's bound principal (nil: the
; connection administers, the owner's bootstrap authority). Each accepted
; reply must be authorized at that point: a create or grant-set only on an
; administering connection; a bind only to a principal the directory names;
; an append under a bound principal only with an enabled append grant on its
; group's stream; a consumer verb under a bound principal only with an
; enabled consume grant on its own consumers. Delivered items: the script has
; no read or wait (kind 28 items, lane e-frames); owed with them.
(defun fn2-oa-granted (p rt sc tg grants)
  (declare (xargs :verify-guards nil))
  (equal (cdr (assoc-equal (list p rt sc tg) grants)) 1))
(defun fn2-oa-judge-auth (steps replies dir grants p gs)
  ; (mv ok dir grants p)
  (declare (xargs :verify-guards nil))
  (if (or (atom steps) (atom replies)) (mv t dir grants p)
    (b* ((s (car steps)) (ok (eq (nth 1 (car replies)) :accepted)) (v (nth 2 (car replies))))
      (cond ((not ok) (fn2-oa-judge-auth (cdr steps) (cdr replies) dir grants p gs))
            ((eq (car s) :create)
             (if p (mv nil dir grants p) (fn2-oa-judge-auth (cdr steps) (cdr replies) (put-assoc-equal (nth 1 s) v dir) grants p gs)))
            ((eq (car s) :bind)
             (let ((id (cdr (assoc-equal (nth 1 s) dir))))
               (if (and (posp id) (equal id v)) (fn2-oa-judge-auth (cdr steps) (cdr replies) dir grants id gs) (mv nil dir grants p))))
            (t (if p (mv nil dir grants p)
                 (fn2-oa-judge-auth (cdr steps) (cdr replies) dir
                                    (put-assoc-equal (list (nfix (cdr (assoc-equal (nth 1 s) dir))) (fn2-oa-right (nth 2 s))
                                                           (fn2-oa-scope (nth 3 s)) (fn2-oa-gid (nth 4 s) gs))
                                                     (nth 5 s) grants)
                                    p gs)))))))
(defun fn2-oa-judge-cns (steps replies grants p gs)
  (declare (xargs :verify-guards nil))
  (if (or (atom steps) (atom replies)) t
    (and (or (not (eq (car (car replies)) :accepted)) (null p)
             (if (eq (car (car steps)) :append)
                 (fn2-oa-granted p 2 1 (fn2-oa-gid (nth 3 (car steps)) gs) grants)
               (fn2-oa-granted p 0 0 0 grants)))
         (fn2-oa-judge-cns (cdr steps) (cdr replies) grants p gs))))
(defun fn2-oa-judge (rounds dir grants gs)
  (declare (xargs :verify-guards nil))
  (if (atom rounds) t
    (b* (((list round areplies creplies &) (car rounds))
         ((mv ok dir grants p) (fn2-oa-judge-auth (car round) areplies dir grants nil gs)))
      (and ok (fn2-oa-judge-cns (cadr round) creplies grants p gs)
           (fn2-oa-judge (cdr rounds) dir grants gs)))))
;; every round answered every frame and ran to quiet
(defun fn2-oa-complete (rounds)
  (declare (xargs :verify-guards nil))
  (if (atom rounds) t
    (b* (((list round areplies creplies status) (car rounds)))
      (and (eq status :quiet) (equal (len areplies) (len (car round))) (equal (len creplies) (len (cadr round)))
           (fn2-oa-complete (cdr rounds))))))
;; TR is (GS . ROUNDS)
(defun fn2-oa-enforced-p (tr)
  (declare (xargs :verify-guards nil))
  (and (fn2-oa-complete (cdr tr)) (fn2-oa-judge (cdr tr) nil nil (car tr))))

;; The hypotheses, each removed by its perturbation.
(defun fn2-oa-binding-intact (perturb) (declare (xargs :guard t)) (not (eq perturb :binding)))
(defun fn2-oa-current-validated (perturb) (declare (xargs :guard t)) (not (eq perturb :current)))
(defun fn2-oa-publication-coherent (perturb) (declare (xargs :guard t)) (not (eq perturb :publication)))

;; ---------------------------------------------------------------------------
;; The evidence. The positive script (six rounds, each a new connection):
; the administrator creates mini and origin and appends (bootstrap
; authority); grants mini consume and origin append on dregg.fn.e1; mini,
; bound, appends (refused: no append grant), registers and asks position
; (accepted); origin, bound, appends (accepted) and asks position (refused:
; no consume grant); the administrator revokes mini's consume at its head;
; mini, bound, asks position (refused). (A round's frames are built before
; it runs, so a principal is granted in a later round than its creation.)
(defconst *fn2-oa-positive-script*
  '((((:create "mini") (:create "origin")) ((:append 1 "<oa0@authority.invalid>" "dregg.fn.e1")))
    (((:set "mini" :consume :own nil 1) (:set "origin" :append :stream "dregg.fn.e1" 1)) nil)
    (((:bind "mini")) ((:append 2 "<oa1@authority.invalid>" "dregg.fn.e1") (:register 1) (:position 1)))
    (((:bind "origin")) ((:append 3 "<oa2@authority.invalid>" "dregg.fn.e1") (:position 1)))
    (((:set "mini" :consume :own nil 0)) nil)
    (((:bind "mini")) ((:position 1)))))
(defun fn2-oa-classes (rounds)
  (declare (xargs :verify-guards nil))
  (if (atom rounds) nil
    (list* (strip-cadrs (nth 1 (car rounds))) (strip-cars (nth 2 (car rounds))) (fn2-oa-classes (cdr rounds)))))
;; The whole antecedent (the script, every hypothesis) and the conclusion,
; and that the trace exercised each branch the judge reads: accepted and
; refused appends and consumer verbs under a bound principal, accepted
; grant-sets and binds (the reply classes, round by round).
(defun fn2-authority-served-enforced-positive ()
  (declare (xargs :verify-guards nil))
  (let ((tr (fn2-oa-trace *fn2-oa-positive-script* nil)))
    (and (fn2-oa-script-p *fn2-oa-positive-script*)
         (fn2-oa-binding-intact nil) (fn2-oa-current-validated nil) (fn2-oa-publication-coherent nil)
         (fn2-oa-enforced-p tr)
         (equal (fn2-oa-classes (cdr tr))
                '((:accepted :accepted) (:accepted)
                  (:accepted :accepted) nil
                  (:accepted) (:refused :accepted :accepted)
                  (:accepted) (:accepted :refused)
                  (:accepted) nil
                  (:accepted) (:refused))))))
;; Hypothesis removal: the same script under each perturbation satisfies the
; other two hypotheses and the served trace violates the conclusion:
; origin's position accepted as mini, under a consume grant origin does not
; hold (binding); mini's position after the revocation accepted under the
; first grant the trace set (current), and under the grant published just
; before the revocation (publication).
(defun fn2-oa-removal (perturb)
  (declare (xargs :verify-guards nil))
  (let ((tr (fn2-oa-trace *fn2-oa-positive-script* perturb)))
    (and (fn2-oa-complete (cdr tr)) (not (fn2-oa-judge (cdr tr) nil nil (car tr))))))
(defun fn2-authority-served-binding-removed ()
  (declare (xargs :verify-guards nil))
  (and (not (fn2-oa-binding-intact :binding)) (fn2-oa-current-validated :binding) (fn2-oa-publication-coherent :binding)
       (fn2-oa-removal :binding)))
(defun fn2-authority-served-current-removed ()
  (declare (xargs :verify-guards nil))
  (and (fn2-oa-binding-intact :current) (not (fn2-oa-current-validated :current)) (fn2-oa-publication-coherent :current)
       (fn2-oa-removal :current)))
(defun fn2-authority-served-publication-removed ()
  (declare (xargs :verify-guards nil))
  (and (fn2-oa-binding-intact :publication) (fn2-oa-current-validated :publication)
       (not (fn2-oa-publication-coherent :publication))
       (fn2-oa-removal :publication)))

(defthm-owed fn2-authority-served-enforced (script perturb)
  (implies (and (fn2-oa-script-p script)
                (fn2-oa-binding-intact perturb) (fn2-oa-current-validated perturb) (fn2-oa-publication-coherent perturb))
           (fn2-oa-enforced-p (fn2-oa-trace script perturb)))
  :schema :invariant :from (:operation-set fn2-auth)
  :teeth (fn2-authority-served-enforced-positive fn2-authority-served-binding-removed
          fn2-authority-served-current-removed fn2-authority-served-publication-removed)
  :doc "CRITICAL (authorization, identity-binding; AUTHORITY-20261105 section 6): from the store's genesis, for every script of rounds served through fn2-turn, the FNCT adapter and the wire, every reply is answered, and every accepted mutation is authorized by what the trace's own replies establish, in commit order: a principal-create or grant-set only on an administering connection; a principal-bind only to a principal the directory names; an append under a bound principal only with an enabled append grant on its group's stream at commit eligibility; a consumer verb under a bound principal only with its current consume grant (each consumer mutation in that principal's namespace). Hypotheses: binding (the connection acts as the principal it bound), current-grant validation (a decision reads the current pointer and its grant row), publication coherence (the decision reads the published grant state, linearized at a re-read head). Teeth: the positive trace exercising every branch; one removal witness per hypothesis, each an unauthorized commit on the served path. Delivered items (read, wait) are owed with kind 28 items (lane e-frames).")

;; The named refinement obligations (concrete to model) the keystone rests on.
(defthm-owed fn2-authority-binding-refines (script)
  (implies (fn2-oa-script-p script)
           (fn2-oa-enforced-p (fn2-oa-trace script nil)))
  :schema :invariant :from (:operation-set fn2-auth)
  :teeth (fn2-authority-served-enforced-positive fn2-authority-served-binding-removed)
  :doc "Principal binding (section 1): fn2-auth's principal-bind sets the connection row's principal to the directory's identity of the name it carries (fn2-principals, exact read), once; every later request of that connection is decided as that principal. Refines the judge's binding step (fn2-oa-judge-auth :bind).")
(defthm-owed fn2-authority-grant-lookup-refines (script)
  (implies (fn2-oa-script-p script)
           (fn2-oa-enforced-p (fn2-oa-trace script nil)))
  :schema :invariant :from (:operation-set fn2-auth)
  :teeth (fn2-authority-served-enforced-positive fn2-authority-served-current-removed)
  :doc "Grant lookup (section 4): fn2-cns-authority-allows and the transaction's append check (txn.lisp) answer :ok iff the principal's current grant for (right scope target), read by exact lookup of fn2-grant-current and its fn2-grants row at a head re-read unchanged, is enabled: fn2-grant-allows over the published fold state. Refines fn2-oa-granted.")
(defthm-owed fn2-authority-grant-publication-refines (script)
  (implies (fn2-oa-script-p script)
           (fn2-oa-enforced-p (fn2-oa-trace script nil)))
  :schema :invariant :from (:operation-set fn2-auth)
  :teeth (fn2-authority-served-enforced-positive fn2-authority-served-publication-removed)
  :doc "Grant publication (section 2): grant-set's member writes the immutable grant row, the fn2-grant-current and fn2-authority-head fold events (their grant the member's own commit position, fn2-fold-event-field) and the outcome in one transaction, validated against the expected head at stage; the folds equal the interpretation of the grant events (folds-served's summary keystones), so a reader sees a grant state only as one published revision. Refines the judge's grant-set step.")
;; K7 (books/owed-consumer.lisp fn2-cns-authority-current) and K10
; (fn2-cns-served-refines) are linked: their served operations are these.
(defconst *fn2-authority-keystone-links*
  '((fn2-cns-authority-current . (fn2-authority-grant-lookup-refines fn2-authority-grant-publication-refines))
    (fn2-cns-served-refines . (fn2-authority-served-enforced fn2-authority-binding-refines))))
