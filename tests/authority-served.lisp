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
; slot below the system row names "anonymous" only. Its controls: a lookup
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
; grant-set answers fault until the grants land.
(in-package "ACL2")
(include-book "../books/assembly-attach")
(include-book "../books/owed-txn")
(include-book "fnct-client")
(include-book "std/util/bstar" :dir :system)

(defconst *fn2-as-profile*
 (put-assoc-equal :owner-account 2
  (put-assoc-equal :identity-arena-bytes 4096
   (put-assoc-equal :pool-classes '((8 . 64) (4 . 256) (16 . 4096)) *fn2-profile-tiny*))))
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

;; ---------------------------------------------------------------------------
;; fn2-authority-local-binding-positive
(defconst *fn2-as-served-profile*
 (put-assoc-equal :authority 1
  (put-assoc-equal :owner-account 2
   (put-assoc-equal :control-connections 3
    (put-assoc-equal :cns 1 *fn2-txn-posting-profile*)))))
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

;; The replies, as the list specification renders them.
(defun fn2-as-accepted (verb values) (declare (xargs :verify-guards nil)) (fn2-authority-reply-octets verb :accepted nil values nil))
(defun fn2-as-refused (verb word) (declare (xargs :verify-guards nil)) (fn2-authority-reply-octets verb :refused (fn2-as-o word) nil nil))
(defun fn2-as-fault (verb) (declare (xargs :verify-guards nil)) (fn2-authority-reply-octets verb :fault nil nil nil))
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
;; grant-set answers fault (not served until the grants land).
(assert-event
 (let ((r (fn2-as-served-run *fn2-as-served-profile*
                             (list (fn2-as-client (list (fn2-fnct-seal *fn2-authority-request-kind*
                                                                       (append (fn2-authority-request-octets 'principal-create (list (fn2-as-o "mini"))) '(0)))
                                                        (fn2-fnct-seal *fn2-authority-request-kind* '(9 0 0))
                                                        (fn2-as-frame 'grant-set (list 1 0 0 0 1 0 (fn2-as-o "op"))))))
                             (list "mini"))))
  (and (equal (nth 1 r) 0)
       (equal (car (nth 2 r))
              (append (fn2-as-refused 'principal-create "frame")
                      (fn2-authority-reply-octets 'principal-create :refused (fn2-as-o "frame") nil nil)
                      (fn2-as-fault 'grant-set)))
       (equal (nth 3 r) '((:absent 0))))))
