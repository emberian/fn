; Served authority's fixtures (docs/design/AUTHORITY-20261105.md section 6),
; over the real assembled core. This book grows with the lane, one witness
; per landed step; the witnesses the ruling names and this book does not yet
; carry are owed (docs/e-surface.md, the authority seam).
;
; fn2-authority-genesis-positive (the store's two persisted principals, the
; first half of fn2-authority-local-binding-positive): store genesis names
; "anonymous" (account slot 0) and "owner" (the profile's :owner-account) in
; fn2-principals with distinct positive durable ids, slot * 2^32 + 1; the
; exact lookup answers each; an unnamed principal, "mini" before its
; principal-create, is :absent; a second boot names the same ids (the ids are
; functions of the profile, never of boot order); and a profile with no owner
; slot below the system row names "anonymous" only; a profile serving no
; authority binds the accounts and names none (no reader of the names). Its controls: a lookup
; of a name one octet longer and one shorter than "owner" is :absent.
;
; fn2-authority-local-binding-positive (served, through fn2-turn and the
; adapter: the clients' kind-29 frames are a :local connection's input and
; their replies its output, judged octet for octet against the generated
; codec's list specification). Two owner connections of one kernel UID:
; the first creates "mini" and "origin" (distinct durable ids, each a fresh
; account slot's first incarnation, the owner's slot skipped), a repeat
; create of "mini" answers its recorded id and creates nothing; it binds to
; "mini" and its later create is refused access (the bound connection
; administers nothing) and a second bind refused access (once). The second
; binds to "origin". After the run fn2-principals answers both names with
; the replies' ids (the create was a committed, published transaction), and
; the core never stopped. Controls: a bind to an unknown name is refused
; unknown-principal (no forged principal); a bind after consumer work is
; refused access; a frame that is not exactly its layout is refused frame;
; a grant-get of a right never granted answers found 0 at head 0.
; fn2-authority-grant-roundtrip-positive (served): the seven Mini grants,
; each a grant-set on an administrator connection judged by its sealed wire
; reply, its expected head the grantee's previous grant; an identical retry
; of an operation answers its recorded grant and adds no event; the same
; operation with a changed request is refused operation-reused; a new one
; with a stale head stale-revision; a consume right with a stream target
; scope; then grant-get reads every grant back (grantor the owner, the
; predecessor chain, the head), and an absent right answers found 0.
(in-package "ACL2")
(include-book "../books/assembly-attach")
(include-book "../books/owed-txn")
(include-book "authority-client")
(include-book "std/util/bstar" :dir :system)

;; a profile serving authority (:authority 1): store genesis names the principals
(defconst *fn2-as-profile*
 (put-assoc-equal :authority 1
 (put-assoc-equal :owner-account 2
  (put-assoc-equal :identity-arena-bytes 4096
   (put-assoc-equal :pool-classes '((8 . 64) (4 . 256) (16 . 4096)) *fn2-profile-tiny*)))))
(defun fn2-as-write (bytes slot gen off fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (if (atom bytes) (mv :ok fn2-core)
  (mv-let (code fn2-core) (fn2-core-write slot gen off (car bytes) 5 1 1 fn2-core)
   (if (eq code :ok) (fn2-as-write (cdr bytes) slot gen (+ 1 off) fn2-core) (mv code fn2-core)))))
(defun fn2-as-chars (cs) (declare (xargs :verify-guards nil)) (if (atom cs) nil (cons (char-code (car cs)) (fn2-as-chars (cdr cs)))))
(defun fn2-as-drive (fuel tx slot gen len fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (if (zp fuel) (mv :fuel 0 fn2-core)
  (mv-let (code p fn2-core) (fn2-principal-lookup tx slot gen 0 len 5 1 1 4096 fn2-core)
   (if (eq code :more) (fn2-as-drive (- fuel 1) tx slot gen len fn2-core) (mv code p fn2-core)))))
(defun fn2-as-lookup (name fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* (((mv & slot gen fn2-core) (fn2-core-reserve 1 5 1 1 fn2-core))
      (octets (fn2-as-chars (coerce name 'list)))
      ((mv & fn2-core) (fn2-as-write octets slot gen 0 fn2-core))
      ((mv code p fn2-core) (fn2-as-drive 20 0 slot gen (len octets) fn2-core))
      ((mv & fn2-core) (fn2-core-release slot gen 5 1 1 fn2-core)))
  (mv (list code p) fn2-core)))
(defun fn2-as-genesis-run (profile fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((fn2-core (fn2-core-init profile fn2-core))
      ((mv g fn2-core) (fn2-principals-genesis profile fn2-core))
      ((mv a fn2-core) (fn2-as-lookup "anonymous" fn2-core))
      ((mv o fn2-core) (fn2-as-lookup "owner" fn2-core))
      ((mv m fn2-core) (fn2-as-lookup "mini" fn2-core))
      ((mv o1 fn2-core) (fn2-as-lookup "owners" fn2-core))
      ((mv o2 fn2-core) (fn2-as-lookup "owne" fn2-core))
      ((mv sc sid fn2-core) (mv-let (c i) (fn2-principal-of-slot 2 fn2-core) (mv c i fn2-core))))
  (mv (list g a o m o1 o2 (list sc sid)) fn2-core)))
(defun fn2-as-genesis (profile)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core (mv-let (r fn2-core) (fn2-as-genesis-run profile fn2-core) r)))

(defconst *fn2-as-anonymous-id* 1)                        ; slot 0, incarnation 1
(defconst *fn2-as-owner-id* (+ (* 2 4294967296) 1))       ; slot 2, incarnation 1
(defun fn2-authority-genesis-positive ()
 (declare (xargs :verify-guards nil))
 (let ((boot1 (fn2-as-genesis *fn2-as-profile*))
       (boot2 (fn2-as-genesis *fn2-as-profile*)))
  (and (equal boot1
              (list :ok (list :ok *fn2-as-anonymous-id*) (list :ok *fn2-as-owner-id*)
                    '(:absent 0) '(:absent 0) '(:absent 0) (list :ok *fn2-as-owner-id*)))
       (not (equal *fn2-as-anonymous-id* *fn2-as-owner-id*))
       (equal boot2 boot1))))
(assert-event (fn2-authority-genesis-positive))
;; No owner slot below the system row (P = 1): anonymous only.
(assert-event
 (let ((r (fn2-as-genesis (put-assoc-equal :p 1 *fn2-as-profile*))))
  (and (equal (nth 0 r) :ok) (equal (nth 1 r) (list :ok *fn2-as-anonymous-id*)) (equal (car (nth 2 r)) :absent))))
;; A profile serving no authority (every tiny unit profile, whose pool
;; classes hold no directory overlay) boots: genesis answers :ok, the
;; owner's account is bound to its id, and no name is written.
(assert-event
 (let ((r (fn2-as-genesis (put-assoc-equal :authority 0 *fn2-as-profile*))))
  (and (equal (nth 0 r) :ok) (equal (car (nth 1 r)) :absent) (equal (car (nth 2 r)) :absent)
       (equal (nth 6 r) (list :ok *fn2-as-owner-id*)))))
(assert-event
 (let ((r (fn2-as-genesis (put-assoc-equal :listener-targets 'fn2-conn
                           (put-assoc-equal :pool-classes '((8 . 1024) (4 . 256)) *fn2-profile-tiny*)))))
  (equal (nth 0 r) :ok)))

;; ---------------------------------------------------------------------------
;; fn2-authority-local-binding-positive
(defconst *fn2-as-served-profile*
 ;; T 4: fn2-txn's row, fn2-auth's and up to two consumer rows' successors (fn2-txn-consumer-share)
 (put-assoc-equal :t 4
 (put-assoc-equal :authority 1
  (put-assoc-equal :owner-account 2
   (put-assoc-equal :control-connections 3
    (put-assoc-equal :cns 1 *fn2-txn-posting-profile*))))))
(defun fn2-as-o (s) (declare (xargs :verify-guards nil)) (fn2-as-chars (coerce s 'list)))
;; a client's kind-29 frame: FNCT (consumer-codec.lisp fn2-fnct-seal) whose payload is the request
(defun fn2-as-frame (verb values)
 (declare (xargs :verify-guards nil))
 (fn2-fnct-seal *fn2-authority-request-kind* (fn2-authority-request-octets verb values)))
(defun fn2-as-frames (frames)
 (declare (xargs :verify-guards nil))
 (if (atom frames) (mv nil nil)
  (mv-let (bytes sizes) (fn2-as-frames (cdr frames))
   (mv (append (car frames) bytes) (cons (len (car frames)) sizes)))))
(defun fn2-as-client (frames)
 (declare (xargs :verify-guards nil))
 (mv-let (bytes sizes) (fn2-as-frames frames) (list bytes sizes nil nil)))
(defun fn2-as-admit (caps fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (if (atom caps) (mv :ok fn2-core)
  (b* ((fn2-core (fn2-listener-take-credit *fn2-ctl-admission-ordinal* fn2-core))
       ((mv acode fn2-core) (fn2-machine-admit-fn2-ctl (car caps) 77 3 0 fn2-core))
       ((unless (eq acode :ok)) (mv acode fn2-core))
       ((mv wake fn2-core) (fn2-machine-take-wake fn2-core))
       (fn2-core (fn2-exec-wake wake fn2-core)))
   (fn2-as-admit (cdr caps) fn2-core))))
;; the capability indices 0 .. N-1, one per client
(defun fn2-as-range (i n)
 (declare (xargs :verify-guards nil :measure (nfix (- (nfix n) (nfix i)))))
 (if (>= (nfix i) (nfix n)) nil (cons (nfix i) (fn2-as-range (+ 1 (nfix i)) n))))
(defun fn2-as-lookups (names fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (if (atom names) (mv nil fn2-core)
  (b* (((mv r fn2-core) (fn2-as-lookup (car names) fn2-core))
       ((mv rs fn2-core) (fn2-as-lookups (cdr names) fn2-core)))
   (mv (cons r rs) fn2-core))))
;; (status stop-reason wires lookups): every client's wire, then the names' lookups
(defun fn2-as-served-run (profile clients names)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (r fn2-core)
   (b* ((fn2-core (fn2-init-executor profile :echo nil fn2-core))
        ((mv & fn2-core)
         (stobj-let ((fn2-extents (fn2-core-extents fn2-core))) (code fn2-extents)
          (fn2-alloc-begin-epoch 1 fn2-extents) (mv code fn2-core)))
        ((mv acode fn2-core) (fn2-as-admit (fn2-as-range 0 (len clients)) fn2-core))
        ((unless (eq acode :ok)) (mv (list :admit acode) fn2-core))
        ((mv status clients & fn2-core) (fn2-cw-loop 4000 0 (len clients) clients nil fn2-core))
        ((mv looks fn2-core) (fn2-as-lookups names fn2-core)))
    (mv (list status (fn2-core-stop-reason fn2-core) (strip-cars (fn2-cw-results clients)) looks) fn2-core))
   r)))

;; The replies, as the list specification renders them, sealed (FNCT kind 30).
(defun fn2-as-reply (verb class reason values found-values)
 (declare (xargs :verify-guards nil))
 (fn2-fnct-seal *fn2-authority-reply-kind* (fn2-authority-reply-octets verb class reason values found-values)))
(defun fn2-as-accepted (verb values) (declare (xargs :verify-guards nil)) (fn2-as-reply verb :accepted nil values nil))
(defun fn2-as-refused (verb word) (declare (xargs :verify-guards nil)) (fn2-as-reply verb :refused (fn2-as-o word) nil nil))
(defconst *fn2-as-mini-id* (+ (* 1 4294967296) 1))        ; slot 1, incarnation 1
(defconst *fn2-as-origin-id* (+ (* 3 4294967296) 1))      ; slot 3 (the owner's slot 2 skipped)
(defconst *fn2-as-admin-frames*
 (list (fn2-as-frame 'principal-create (list (fn2-as-o "mini")))
       (fn2-as-frame 'principal-create (list (fn2-as-o "origin")))
       (fn2-as-frame 'principal-create (list (fn2-as-o "mini")))
       (fn2-as-frame 'principal-bind (list (fn2-as-o "nobody")))
       (fn2-as-frame 'principal-bind (list (fn2-as-o "mini")))
       (fn2-as-frame 'principal-create (list (fn2-as-o "third")))
       (fn2-as-frame 'principal-bind (list (fn2-as-o "origin")))))
(defconst *fn2-as-admin-wire*
 (append (fn2-as-accepted 'principal-create (list *fn2-as-mini-id*))
         (fn2-as-accepted 'principal-create (list *fn2-as-origin-id*))
         (fn2-as-accepted 'principal-create (list *fn2-as-mini-id*))
         (fn2-as-refused 'principal-bind "unknown-principal")
         (fn2-as-accepted 'principal-bind (list *fn2-as-mini-id* 0))
         (fn2-as-refused 'principal-create "access")
         (fn2-as-refused 'principal-bind "access")))
;; the second connection waits for the first's creates (its frames arrive
;; after the first's replies only when the loop interleaves them; a bind of a
;; name not yet created is refused unknown-principal, so it binds twice)
(defconst *fn2-as-origin-frames*
 (list (fn2-as-frame 'principal-bind (list (fn2-as-o "origin")))))
(defun fn2-authority-local-binding-run ()
 (declare (xargs :verify-guards nil))
 (fn2-as-served-run *fn2-as-served-profile*
                    (list (fn2-as-client *fn2-as-admin-frames*))
                    (list "mini" "origin" "third")))
(defun fn2-authority-origin-bind-run ()
 (declare (xargs :verify-guards nil))
 (fn2-as-served-run *fn2-as-served-profile*
                    (list (fn2-as-client (append (take 2 *fn2-as-admin-frames*) *fn2-as-origin-frames*)))
                    (list "origin")))
(defun fn2-authority-local-binding-positive ()
 (declare (xargs :verify-guards nil))
 (let ((r (fn2-authority-local-binding-run))
       (o (fn2-authority-origin-bind-run)))
  (and (equal (nth 0 r) :quiet) (equal (nth 1 r) 0)
       (equal (car (nth 2 r)) *fn2-as-admin-wire*)
       (equal (nth 3 r) (list (list :ok *fn2-as-mini-id*) (list :ok *fn2-as-origin-id*) '(:absent 0)))
       (not (equal *fn2-as-mini-id* *fn2-as-origin-id*))
       (equal (nth 0 o) :quiet) (equal (nth 1 o) 0)
       (equal (car (nth 2 o))
              (append (fn2-as-accepted 'principal-create (list *fn2-as-mini-id*))
                      (fn2-as-accepted 'principal-create (list *fn2-as-origin-id*))
                      (fn2-as-accepted 'principal-bind (list *fn2-as-origin-id* 0))))
       (equal (nth 3 o) (list (list :ok *fn2-as-origin-id*))))))
(assert-event (fn2-authority-local-binding-positive))

;; Controls, each a served branch.
;; A bind after consumer work (a consumer read frame, kind 4, first) is refused access.
(assert-event
 (let ((r (fn2-as-served-run *fn2-as-served-profile*
                             (list (fn2-as-client (list (fnc-read (fnc-issued 1 0 0 1 0) 8) (fn2-as-frame 'principal-bind (list (fn2-as-o "owner"))))))
                             nil)))
  (and (equal (nth 1 r) 0)
       (equal (nthcdr (- (len (car (nth 2 r))) (len (fn2-as-refused 'principal-bind "access"))) (car (nth 2 r)))
              (fn2-as-refused 'principal-bind "access")))))
;; A payload one octet longer than its layout, and an unknown opcode, are refused frame;
;; a grant-get of a right never granted answers found 0 at head 0.
(assert-event
 (let ((r (fn2-as-served-run *fn2-as-served-profile*
                             (list (fn2-as-client (list (fn2-fnct-seal *fn2-authority-request-kind*
                                                                       (append (fn2-authority-request-octets 'principal-create (list (fn2-as-o "mini"))) '(0)))
                                                        (fn2-fnct-seal *fn2-authority-request-kind* '(9 0 0))
                                                        (fn2-as-frame 'grant-get (list 1 0 0 0)))))
                             (list "mini"))))
  (and (equal (nth 1 r) 0)
       (equal (car (nth 2 r))
              (append (fn2-as-refused 'principal-create "frame")
                      (fn2-as-refused 'principal-create "frame")
                      (fn2-as-reply 'grant-get :accepted nil (list 0 0) nil)))
       (equal (nth 3 r) '((:absent 0))))))

;; ---------------------------------------------------------------------------
;; fn2-authority-grant-roundtrip-positive (served): the seven Mini grants
;; (consumer-mini.lisp), each a grant-set on the administrator connection
;; judged by its wire reply, its expected head the grantee's previous grant
;; (read from the previous reply: each round is a new connection whose frames
;; are built from the last round's replies), then grant-get of each.
;; "reader" is the anonymous principal; groups resolved by fn2-groups.
(defconst *fn2-as-grant-profile*
 (put-assoc-equal :groups '(("dregg.fn.e1" . 1) ("dregg.fn.e1.reply" . 2))
  (put-assoc-equal :control-connections 8 *fn2-as-served-profile*)))
(defun fn2-as-op (n) (declare (xargs :verify-guards nil)) (list n))
(defun fn2-as-set (grantee right scope target enabled eh op)
 (declare (xargs :verify-guards nil))
 (fn2-as-frame 'grant-set (list grantee right scope target enabled eh (fn2-as-op op))))
(defun fn2-as-get (grantee right scope target)
 (declare (xargs :verify-guards nil))
 (fn2-as-frame 'grant-get (list grantee right scope target)))
;; one round: a new administrator connection CAP with FRAMES, run to quiet;
;; (mv status its-wire clients fn2-core)
(defun fn2-as-round (cap frames clients fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* (((mv acode fn2-core) (fn2-as-admit (list cap) fn2-core))
      ((unless (eq acode :ok)) (mv (list :admit acode) nil clients fn2-core))
      (clients (append clients (list (fn2-as-client frames))))
      ((mv status clients & fn2-core) (fn2-cw-loop 4000 0 (len clients) clients nil fn2-core)))
  (mv status (car (nth cap (fn2-cw-results clients))) clients fn2-core)))
;; a group's id through fn2-groups (as fn2-as-lookup reads fn2-principals)
(defun fn2-as-gdrive (fuel slot gen len fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (if (zp fuel) (mv :fuel 0 fn2-core)
  (mv-let (code g fn2-core) (fn2-group-lookup 0 slot gen 0 len 5 1 1 4096 fn2-core)
   (if (eq code :more) (fn2-as-gdrive (- fuel 1) slot gen len fn2-core) (mv code g fn2-core)))))
(defun fn2-as-group (name fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* (((mv & slot gen fn2-core) (fn2-core-reserve 1 5 1 1 fn2-core))
      (octets (fn2-as-chars (coerce name 'list)))
      ((mv & fn2-core) (fn2-as-write octets slot gen 0 fn2-core))
      ((mv code g fn2-core) (fn2-as-gdrive 20 slot gen (len octets) fn2-core))
      ((mv & fn2-core) (fn2-core-release slot gen 5 1 1 fn2-core)))
  (mv (if (eq code :ok) g 0) fn2-core)))
;; the grant ids of a round's accepted grant-set replies, in order (nil if any is not one)
(defun fn2-as-set-grants (xs n)
 (declare (xargs :verify-guards nil :measure (nfix n)))
 (if (zp n) nil
  (mv-let (g h rest) (fnca-set-reply xs)
   (if (and g (equal g h)) (cons g (fn2-as-set-grants rest (- n 1))) (list nil)))))
(defconst *fn2-as-c* *fn2-authority-right-consume*)
(defconst *fn2-as-r* *fn2-authority-right-read*)
(defconst *fn2-as-a* *fn2-authority-right-append*)
(defconst *fn2-as-own* *fn2-authority-scope-own-consumers*)
(defconst *fn2-as-st* *fn2-authority-scope-stream*)
(defun fn2-as-get-found (g h grantor previous)
 (declare (xargs :verify-guards nil))
 (fn2-as-reply 'grant-get :accepted nil (list 1 h) (list g grantor 1 previous)))
;; (ok detail): the seven Mini grants, served
(defun fn2-authority-grant-roundtrip-run ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (r fn2-core)
   (b* ((m *fn2-as-mini-id*) (o *fn2-as-origin-id*) (a *fn2-as-anonymous-id*) (w *fn2-as-owner-id*)
        (fn2-core (fn2-init-executor *fn2-as-grant-profile* :echo nil fn2-core))
        ((mv & fn2-core)
         (stobj-let ((fn2-extents (fn2-core-extents fn2-core))) (code fn2-extents)
          (fn2-alloc-begin-epoch 1 fn2-extents) (mv code fn2-core)))
        ((mv e1 fn2-core) (fn2-as-group "dregg.fn.e1" fn2-core))
        ((mv e2 fn2-core) (fn2-as-group "dregg.fn.e1.reply" fn2-core))
        ((unless (and (posp e1) (posp e2))) (mv (list :groups e1 e2) fn2-core))
        ((mv s0 w0 cl fn2-core)
         (fn2-as-round 0 (list (fn2-as-frame 'principal-create (list (fn2-as-o "mini")))
                               (fn2-as-frame 'principal-create (list (fn2-as-o "origin")))) nil fn2-core))
        ((unless (equal w0 (append (fn2-as-accepted 'principal-create (list m))
                                   (fn2-as-accepted 'principal-create (list o)))))
         (mv (list :r0 s0 w0) fn2-core))
        ((mv s1 w1 cl fn2-core)
         (fn2-as-round 1 (list (fn2-as-set m *fn2-as-c* *fn2-as-own* 0 1 0 1)
                               (fn2-as-set o *fn2-as-a* *fn2-as-st* e1 1 0 2)
                               (fn2-as-set a *fn2-as-r* *fn2-as-st* e1 1 0 3)) cl fn2-core))
        (g1 (fn2-as-set-grants w1 3))
        ((unless (and (equal (len g1) 3) (natp (nth 0 g1)) (natp (nth 1 g1)) (natp (nth 2 g1))))
         (mv (list :r1 s1 w1) fn2-core))
        ((mv s2 w2 cl fn2-core)
         (fn2-as-round 2 (list (fn2-as-set m *fn2-as-r* *fn2-as-st* e1 1 (nth 0 g1) 4)
                               (fn2-as-set a *fn2-as-r* *fn2-as-st* e2 1 (nth 2 g1) 5)) cl fn2-core))
        (g2 (fn2-as-set-grants w2 2))
        ((unless (and (equal (len g2) 2) (natp (nth 0 g2)) (natp (nth 1 g2)))) (mv (list :r2 s2 w2) fn2-core))
        ((mv s3 w3 cl fn2-core)
         (fn2-as-round 3 (list (fn2-as-set m *fn2-as-r* *fn2-as-st* e2 1 (nth 0 g2) 6)) cl fn2-core))
        (g3 (fn2-as-set-grants w3 1))
        ((unless (natp (car g3))) (mv (list :r3 s3 w3) fn2-core))
        ((mv s4 w4 cl fn2-core)
         (fn2-as-round 4 (list (fn2-as-set m *fn2-as-a* *fn2-as-st* e2 1 (car g3) 7)) cl fn2-core))
        (g4 (fn2-as-set-grants w4 1))
        ((unless (natp (car g4))) (mv (list :r4 s4 w4) fn2-core))
        (gm (list (nth 0 g1) (nth 0 g2) (car g3) (car g4)))
        ;; round 5: retry, reuse, stale, scope; then every grant read back
        ((mv s5 w5 & fn2-core)
         (fn2-as-round 5 (list (fn2-as-set m *fn2-as-a* *fn2-as-st* e2 1 (car g3) 7)
                               (fn2-as-set m *fn2-as-a* *fn2-as-st* e1 1 (car g3) 7)
                               (fn2-as-set m *fn2-as-a* *fn2-as-st* e1 1 (car g3) 8)
                               (fn2-as-set m *fn2-as-c* *fn2-as-own* e1 1 (car g4) 9)
                               (fn2-as-get m *fn2-as-c* *fn2-as-own* 0)
                               (fn2-as-get m *fn2-as-r* *fn2-as-st* e1)
                               (fn2-as-get m *fn2-as-r* *fn2-as-st* e2)
                               (fn2-as-get m *fn2-as-a* *fn2-as-st* e2)
                               (fn2-as-get o *fn2-as-a* *fn2-as-st* e1)
                               (fn2-as-get a *fn2-as-r* *fn2-as-st* e1)
                               (fn2-as-get a *fn2-as-r* *fn2-as-st* e2)
                               (fn2-as-get o *fn2-as-a* *fn2-as-st* e2)) cl fn2-core))
        (want (append (fn2-as-reply 'grant-set :accepted nil (list (car g4) (car g4) nil) nil)
                      (fn2-as-refused 'grant-set "operation-reused")
                      (fn2-as-refused 'grant-set "stale-revision")
                      (fn2-as-refused 'grant-set "scope")
                      (fn2-as-get-found (nth 0 gm) (nth 3 gm) w 0)
                      (fn2-as-get-found (nth 1 gm) (nth 3 gm) w (nth 0 gm))
                      (fn2-as-get-found (nth 2 gm) (nth 3 gm) w (nth 1 gm))
                      (fn2-as-get-found (nth 3 gm) (nth 3 gm) w (nth 2 gm))
                      (fn2-as-get-found (nth 1 g1) (nth 1 g1) w 0)
                      (fn2-as-get-found (nth 2 g1) (nth 1 g2) w 0)
                      (fn2-as-get-found (nth 1 g2) (nth 1 g2) w (nth 2 g1))
                      (fn2-as-reply 'grant-get :accepted nil (list 0 (nth 1 g1)) nil))))
    (mv (list (and (equal s5 :quiet) (equal (fn2-core-stop-reason fn2-core) 0) (equal w5 want)
                   (no-duplicatesp (append g1 g2 g3 g4)))
              w5 want)
        fn2-core))
   r)))
(defun fn2-authority-grant-roundtrip-positive ()
 (declare (xargs :verify-guards nil))
 (equal (car (fn2-authority-grant-roundtrip-run)) t))
(assert-event (fn2-authority-grant-roundtrip-positive))

;; ---------------------------------------------------------------------------
;; fn2-authority-commit-race-positive (C's successor, the read dependency of
;; step 3a, over the assembled core): a member that decided under authority
;; head H validates it at stage against the immediate predecessor, an earlier
;; prepared (bound, unpublished) batch included. Transaction 0 publishes
;; principal P's head 5. Transaction 1 decided under 5 (its :depend slot P ->
;; 5) and stages :ok; transaction 2, a grant event ordered before it, binds
;; head 9 into batch 2 (not yet published): transaction 1 is open again (its
;; bind answers :state) and its stage now answers :changed (re-decide;
;; nothing was submitted). Transaction 3 decided under 9 stages :ok, binds
;; into batch 3 and writes no row (its slot is unchanged, size 0); a grant
;; event ordered after it (transaction 4, head 12) binds, and transaction 3
;; stays bound: a later grant does not undo it. Controls: a :depend slot
;; takes values only (an :event arg is :kind) and integer fields only (the
;; principals directory's octet name is :kind).
(defconst *fn2-as-head-sid* 19)
(defconst *fn2-as-race-profile* (put-assoc-equal :t 6 *fn2-as-profile*))
(defun fn2-as-resolve (fuel tx fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (if (zp fuel) (mv :fuel fn2-core)
  (mv-let (answer fn2-core) (fn2-successor-resolve tx 4096 fn2-core)
   (if (eq answer :more) (fn2-as-resolve (- fuel 1) tx fn2-core) (mv answer fn2-core)))))
;; slot 0 of TX: KIND (the fold's :grant event, or :depend) of fn2-authority-head, P -> H
(defun fn2-as-head-slot (tx kind p h fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* (((mv c1 fn2-core) (fn2-successor-put tx 0 *fn2-as-head-sid* kind fn2-core))
      ((mv c2 fn2-core) (fn2-successor-arg tx 0 0 :value p fn2-core))
      ((mv c3 fn2-core) (fn2-successor-arg tx 0 1 :value h fn2-core))
      ((mv c4 fn2-core) (fn2-as-resolve 40 tx fn2-core)))
  (mv (list c1 c2 c3 c4) fn2-core)))
(defun fn2-as-phase (tx fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (stobj-let ((fn2-succ-txns (fn2-core-succ-txns fn2-core))) (p) (fn2-succ-txns-phase tx fn2-succ-txns) p))
;; the entries of fn2-authority-head in overlays O.. (K of them) a reader or a batch holds
(defun fn2-as-count-entries (o k fn2-overlays)
 (declare (xargs :stobjs fn2-overlays :verify-guards nil :measure (nfix (- (nfix k) (nfix o)))))
 (if (>= (nfix o) (nfix k)) 0
  (+ (if (and (equal (fn2-overlays-schema o fn2-overlays) *fn2-as-head-sid*)
              (member (fn2-overlays-phase o fn2-overlays)
                      (list *fn2-overlay-phase-active* *fn2-overlay-phase-frozen* *fn2-overlay-phase-private*)))
         (nfix (fn2-overlays-count o fn2-overlays)) 0)
     (fn2-as-count-entries (+ 1 (nfix o)) k fn2-overlays))))
(defun fn2-as-overlay-entries (fn2-core)
 ;; entries of fn2-authority-head in every overlay
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (stobj-let ((fn2-overlays (fn2-core-overlays fn2-core))) (n)
  (fn2-as-count-entries 0 (fn2-overlays-rows fn2-overlays) fn2-overlays) n))
(defun fn2-as-race (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((fn2-core (fn2-core-init *fn2-as-race-profile* fn2-core))
      (p 77)
      ((mv d0 fn2-core) (fn2-as-head-slot 0 :grant p 5 fn2-core))
      ((mv s0 & fn2-core) (fn2-successor-stage 0 fn2-core))
      ((mv b0 fn2-core) (fn2-successor-bind 0 1 5 fn2-core))
      ((mv p0 fn2-core) (fn2-successor-publish 1 fn2-core))
      ((mv & fn2-core) (fn2-successor-release 0 fn2-core))
      ;; decided under 5, staged before the grant event
      ((mv d1 fn2-core) (fn2-as-head-slot 1 :depend p 5 fn2-core))
      ((mv s1 i1 fn2-core) (fn2-successor-stage 1 fn2-core))
      ;; the grant event ordered before it: head 9 bound into batch 2
      ((mv d2 fn2-core) (fn2-as-head-slot 2 :grant p 9 fn2-core))
      ((mv s2 & fn2-core) (fn2-successor-stage 2 fn2-core))
      ((mv b2 fn2-core) (fn2-successor-bind 2 2 9 fn2-core))
      (ph1 (fn2-as-phase 1 fn2-core))
      ((mv b1 fn2-core) (fn2-successor-bind 1 2 10 fn2-core))
      ((mv s1b i1b fn2-core) (fn2-successor-stage 1 fn2-core))
      ;; decided under 9: staged and bound, writing nothing
      ((mv d3 fn2-core) (fn2-as-head-slot 3 :depend p 9 fn2-core))
      ((mv s3 & fn2-core) (fn2-successor-stage 3 fn2-core))
      (n0 (fn2-as-overlay-entries fn2-core))
      ((mv b3 fn2-core) (fn2-successor-bind 3 3 11 fn2-core))
      (n1 (fn2-as-overlay-entries fn2-core))
      ;; the grant event ordered after it
      ((mv d4 fn2-core) (fn2-as-head-slot 4 :grant p 12 fn2-core))
      ((mv s4 & fn2-core) (fn2-successor-stage 4 fn2-core))
      ((mv b4 fn2-core) (fn2-successor-bind 4 4 12 fn2-core))
      (ph3 (fn2-as-phase 3 fn2-core))
      ;; controls: values only, integer fields only
      ((mv k1 fn2-core) (fn2-successor-put 5 0 *fn2-as-head-sid* :depend fn2-core))
      ((mv k2 fn2-core) (fn2-successor-arg 5 0 1 :event 0 fn2-core))
      ((mv k3 fn2-core) (fn2-successor-put 5 1 16 :depend fn2-core))
      ((mv k4 fn2-core) (fn2-successor-arg 5 1 0 :value 3 fn2-core)))
  (mv (list :publish d0 s0 b0 p0 :before d1 s1 i1 d2 s2 b2 ph1 b1 s1b i1b
            :after d3 s3 b3 (- n1 n0) d4 s4 b4 ph3 :controls k1 k2 k3 k4)
      fn2-core)))
(defun fn2-as-race-result ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core (mv-let (r fn2-core) (fn2-as-race fn2-core) r)))
(defun fn2-authority-commit-race-positive ()
 (declare (xargs :verify-guards nil))
 (equal (fn2-as-race-result)
        (list :publish '(:ok :ok :ok :ok) :ok :ok :ok
              :before '(:ok :ok :ok :ok) :ok 0 '(:ok :ok :ok :ok) :ok :ok *fn2-succ-phase-open* :state :changed 0
              :after '(:ok :ok :ok :ok) :ok :ok 0 '(:ok :ok :ok :ok) :ok :ok *fn2-succ-phase-bound*
              :controls :ok :kind :ok :kind)))
(assert-event (fn2-authority-commit-race-positive))

;; ---------------------------------------------------------------------------
;; fn2-authority-append-retry-after-revoke-positive (served): appends are
;; governed by the bound principal's current append grant, read at the
;; transaction's :prepare and held as its read dependency. The administrator
;; creates "mini" and "origin" and grants mini append on dregg.fn.e1; mini's
;; connection (bound) appends A: accepted. The administrator revokes the grant
;; (an enabled-0 grant-set at mini's head). Mini, bound again, retries A and
;; appends B: A's retry answers A's recorded identity (never the authority
;; refusal: a revocation ordered after A does not undo it), and B is refused.
;; Controls: origin, holding no append grant, is refused; an unbound
;; administrator connection appends under the owner's bootstrap authority.
;; A's retry is answered "duplicate" (its Message-ID is recorded; observed at
;; c6, the authority refusal never reaches it). The owner's append rides the
;; revoking connection: in this profile (:control-connections 8) a seventh
;; admitted connection's append was never answered, authority aside (an
;; owner-only probe at cap 6 answered nothing; open, named in the lane dump).
(defconst *fn2-as-append-profile* (put-assoc-equal :cns 2 *fn2-as-grant-profile*))
(defun fn2-as-article (mid subject)
 (declare (xargs :verify-guards nil))
 (fn2-cw-crlf-octets (list "From: mini@example.invalid" (concatenate 'string "Subject: " subject)
                           "Newsgroups: dregg.fn.e1" (concatenate 'string "Message-ID: " mid) "" "body")))
(defun fn2-as-append (op mid subject)
 (declare (xargs :verify-guards nil))
 (fnc-append op (fn2-as-article mid subject)))
(defun fn2-as-bind (name) (declare (xargs :verify-guards nil)) (fn2-as-frame 'principal-bind (list (fn2-as-o name))))
;; (CLASS WORD) of each reply in RS (fnc-replies')
(defun fn2-as-class-words (rs)
 (declare (xargs :verify-guards nil))
 (if (atom rs) nil (cons (list (nth 0 (car rs)) (nth 1 (car rs))) (fn2-as-class-words (cdr rs)))))
;; the first N append replies (CLASS WORD) in XS
(defun fn2-as-append-replies (xs n)
 (declare (xargs :verify-guards nil))
 (fn2-as-class-words (fnc-replies (make-list (nfix n) :initial-element 'append) xs)))
(defun fn2-as-after-bind (xs n)
 (declare (xargs :verify-guards nil))
 (mv-let (pl rest) (fnca-unseal xs) (declare (ignore pl)) (fn2-as-append-replies rest n)))
(defun fn2-authority-append-run ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (r fn2-core)
   (b* ((m *fn2-as-mini-id*)
        (fn2-core (fn2-init-executor *fn2-as-append-profile* :echo nil fn2-core))
        ((mv & fn2-core)
         (stobj-let ((fn2-extents (fn2-core-extents fn2-core))) (code fn2-extents)
          (fn2-alloc-begin-epoch 1 fn2-extents) (mv code fn2-core)))
        ((mv e1 fn2-core) (fn2-as-group "dregg.fn.e1" fn2-core))
        ((unless (posp e1)) (mv (list :groups e1) fn2-core))
        ((mv & w0 cl fn2-core)
         (fn2-as-round 0 (list (fn2-as-frame 'principal-create (list (fn2-as-o "mini")))
                               (fn2-as-frame 'principal-create (list (fn2-as-o "origin")))) nil fn2-core))
        ((mv & w1 cl fn2-core) (fn2-as-round 1 (list (fn2-as-set m *fn2-as-a* *fn2-as-st* e1 1 0 1)) cl fn2-core))
        (g1 (car (fn2-as-set-grants w1 1)))
        ((unless (natp g1)) (mv (list :grant w0 w1) fn2-core))
        ((mv & w2 cl fn2-core) (fn2-as-round 2 (list (fn2-as-bind "mini") (fn2-as-append 11 "<a@authority.invalid>" "A")) cl fn2-core))
        ;; the revoking (unbound administrator) connection then appends D
        ;; under the owner's bootstrap authority
        ((mv & w3 cl fn2-core)
         (fn2-as-round 3 (list (fn2-as-set m *fn2-as-a* *fn2-as-st* e1 0 g1 2) (fn2-as-append 14 "<d@authority.invalid>" "D"))
                       cl fn2-core))
        (g2 (car (fn2-as-set-grants w3 1)))
        ((mv & w4 cl fn2-core)
         (fn2-as-round 4 (list (fn2-as-bind "mini") (fn2-as-append 11 "<a@authority.invalid>" "A")
                               (fn2-as-append 12 "<b@authority.invalid>" "B")) cl fn2-core))
        ((mv s5 w5 & fn2-core) (fn2-as-round 5 (list (fn2-as-bind "origin") (fn2-as-append 13 "<c@authority.invalid>" "C")) cl fn2-core)))
    (mv (list :revoked (and (natp g2) (< g1 g2))
              :a (fn2-as-after-bind w2 1) :retry-and-b (fn2-as-after-bind w4 2) :origin (fn2-as-after-bind w5 1)
              :owner (mv-let (g h rest) (fnca-set-reply w3) (declare (ignore g h)) (fn2-as-append-replies rest 1))
              :end s5 (fn2-core-stop-reason fn2-core))
        fn2-core))
   r)))
(defun fn2-authority-append-retry-after-revoke-positive ()
 (declare (xargs :verify-guards nil))
 (let ((r (fn2-authority-append-run)))
  (and (equal (nth 1 r) t)
       (equal (nth 3 r) '((:accepted "")))
       (equal (car (nth 5 r)) '(:refused "duplicate"))
       (equal (cadr (nth 5 r)) '(:refused "refused"))
       (equal (nth 7 r) '((:refused "refused")))
       (equal (nth 9 r) '((:accepted "")))
       (equal (nth 11 r) :quiet) (equal (nth 12 r) 0))))
(assert-event (fn2-authority-append-retry-after-revoke-positive))

;; ---------------------------------------------------------------------------
;; fn2-authority-current-positive (served; step 3c): the consumer surface is
;; governed by the bound principal's CURRENT consume grant, read at :check on
;; the request's own read row. The administrator creates "mini". Mini, bound,
;; asks position: refused "access" (no grant). The administrator grants mini
;; consume on its own consumers; mini, bound, registers consumer 1 and asks
;; position: both accepted. The administrator revokes the grant (an enabled-0
;; grant-set at mini's head); mini, bound, asks position: refused "access".
;; Observed at c10 (bb2) as predicted. Control: the granting administrator connection, unbound (the owner's
;; bootstrap authority), registers its own consumer 1 and asks position:
;; accepted.
;; (CLASS WORD) of each kind 28 reply in XS, read as VERBS
(defun fn2-as-cns-replies (verbs xs)
 (declare (xargs :verify-guards nil))
 (fn2-as-class-words (fnc-replies verbs xs)))
(defun fn2-as-after-bind-cns (verbs xs)
 (declare (xargs :verify-guards nil))
 (mv-let (pl rest) (fnca-unseal xs) (declare (ignore pl)) (fn2-as-cns-replies verbs rest)))
(defun fn2-authority-current-run ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (r fn2-core)
   (b* ((m *fn2-as-mini-id*)
        (fn2-core (fn2-init-executor *fn2-as-append-profile* :echo nil fn2-core))
        ((mv & fn2-core)
         (stobj-let ((fn2-extents (fn2-core-extents fn2-core))) (code fn2-extents)
          (fn2-alloc-begin-epoch 1 fn2-extents) (mv code fn2-core)))
        ((mv & w0 cl fn2-core)
         (fn2-as-round 0 (list (fn2-as-frame 'principal-create (list (fn2-as-o "mini")))) nil fn2-core))
        ((mv & w1 cl fn2-core) (fn2-as-round 1 (list (fn2-as-bind "mini") (fnc-position 1)) cl fn2-core))
        ;; the granting (unbound administrator) connection then registers and
        ;; asks position under the owner's bootstrap authority
        ((mv & w2 cl fn2-core)
         (fn2-as-round 2 (list (fn2-as-set m *fn2-as-c* *fn2-as-own* 0 1 0 1) (fnc-register 1 1) (fnc-position 1)) cl fn2-core))
        (g1 (car (fn2-as-set-grants w2 1)))
        ((unless (natp g1)) (mv (list :grant w0 w2) fn2-core))
        ((mv & w3 cl fn2-core) (fn2-as-round 3 (list (fn2-as-bind "mini") (fnc-register 1 1) (fnc-position 1)) cl fn2-core))
        ((mv & w4 cl fn2-core) (fn2-as-round 4 (list (fn2-as-set m *fn2-as-c* *fn2-as-own* 0 0 g1 2)) cl fn2-core))
        (g2 (car (fn2-as-set-grants w4 1)))
        ((mv s5 w5 & fn2-core) (fn2-as-round 5 (list (fn2-as-bind "mini") (fnc-position 1)) cl fn2-core)))
    (mv (list :revoked (and (natp g2) (< g1 g2))
              :ungranted (fn2-as-after-bind-cns '(position) w1)
              :granted (fn2-as-after-bind-cns '(register position) w3)
              :after-revoke (fn2-as-after-bind-cns '(position) w5)
              :owner (mv-let (g h rest) (fnca-set-reply w2) (declare (ignore g h)) (fn2-as-cns-replies '(register position) rest))
              :end s5 (fn2-core-stop-reason fn2-core))
        fn2-core))
   r)))
(defun fn2-authority-current-positive ()
 (declare (xargs :verify-guards nil))
 (equal (fn2-authority-current-run)
        (list :revoked t
              :ungranted '((:refused "access"))
              :granted '((:accepted "") (:accepted ""))
              :after-revoke '((:refused "access"))
              :owner '((:accepted "") (:accepted ""))
              :end :quiet 0)))
(assert-event (fn2-authority-current-positive))
