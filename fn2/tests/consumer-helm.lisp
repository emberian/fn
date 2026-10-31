; helm's rooms against the consumer port (fn2/docs/e-surface.md section 10.2),
; tiny profile, over the reference model. helm's transport port maps one to
; one: append(row) is APPEND with the mentions in TO and an operation id;
; read(room, after) is a one-edge READ; wait(seat, timeout) is the seat's
; WAIT; ack(seat, row) is ACK. Rooms are groups, DM lanes two-member private
; groups, each seat one consumer whose edges are its rooms, its DM lanes and
; its own addr stream. Three seats, four rooms, two DM lanes, 60 rows with
; mentions, a group-address row, a mention in a room the mentioned seat may
; not read, a grant that adds a room (rebase keeping the cursor, the room
; added from now), a revocation, a withdrawal after every reader acked, a
; crash under parked waits, and a lagging seat that catches up page by page.
(in-package "ACL2")
(include-book "../books/consumer-model")
(include-book "std/testing/assert-bang" :dir :system)

(defconst *helm-limits* '(4 4096))   ; four items a page: pagination is exercised
(defconst *helm-seats* '("s1" "s2" "s3"))
(defconst *helm-streams*             ; what each seat reads and posts to at the start
  '(("s1" "r1" "r2" "dm.s1.s2") ("s2" "r2" "r3" "dm.s1.s2" "dm.s2.s3") ("s3" "r1" "r3" "r4" "dm.s2.s3")))
(defun helm-grants (rows)
  (declare (xargs :verify-guards nil))
  (if (atom rows) nil
    (append (list (list :grant (caar rows) :consume :any))
            (pairlis$ (make-list (len (cdar rows)) :initial-element :grant)
                      (pairlis$ (make-list (len (cdar rows)) :initial-element (caar rows))
                                (pairlis$ (make-list (len (cdar rows)) :initial-element :read) (pairlis$ (cdar rows) nil))))
            (pairlis$ (make-list (len (cdar rows)) :initial-element :grant)
                      (pairlis$ (make-list (len (cdar rows)) :initial-element (caar rows))
                                (pairlis$ (make-list (len (cdar rows)) :initial-element :append) (pairlis$ (cdar rows) nil))))
            (helm-grants (cdr rows)))))

;; The rows. Row I is posted by seat (I-1) mod 3 into one of its streams; every
;; seventh mentions the next seat; row 14 mentions s1 in r3, which s1 cannot
;; read; row 21 carries the @room flag in r2.
(defun helm-row (i)
  (declare (xargs :verify-guards nil))
  (let* ((author (nth (mod (- i 1) 3) *helm-seats*))
         (streams (cdr (assoc-equal author *helm-streams*)))
         (stream (nth (mod (floor (- i 1) 3) (len streams)) streams))
         (to (cond ((equal i 14) '("s1")) ((equal i 21) '(:room))
                   ((equal (mod i 7) 0) (list (nth (mod i 3) *helm-seats*))) (t nil))))
    (case i
      (14 (list "s2" "r3" '("s1")))
      (21 (list "s1" "r2" '(:room)))
      (otherwise (list author stream to)))))
(defun helm-post (i)
  (declare (xargs :verify-guards nil))
  (let ((r (helm-row i)))
    (list :post (car r) (cadr r)
          (list nil (concatenate 'string "row " (fn2-gram-cat (list i)) " body") (caddr r))
          (concatenate 'string "row-" (fn2-gram-cat (list i))))))
(defun helm-posts (i n)
  (declare (xargs :verify-guards nil :measure (nfix (- (+ 1 n) i))))
  (if (or (not (natp i)) (not (natp n)) (< n i)) nil (cons (helm-post i) (helm-posts (+ 1 i) n))))

;; The seats' client ---------------------------------------------------------
; DB: seat -> (CURSOR DELIVERED STREAMS WAITING), DELIVERED newest first as (POS TYPE REASONS).
(defun helm-seat (s db) (declare (xargs :verify-guards nil)) (cdr (assoc-equal s db)))
(defun helm-put (s field v db)
  (declare (xargs :verify-guards nil))
  (put-assoc-equal s (update-nth field v (helm-seat s db)) db))
(defun helm-send (op st ops fault)
  (declare (xargs :verify-guards nil))
  (mv-let (o answers st2) (fn2-cns-step op st fault) (mv o answers st2 (cons op ops))))
(defun helm-record (items s db)
  (declare (xargs :verify-guards nil))
  (if (atom items) db
    (helm-record (cdr items) s
                 (helm-put s 1 (cons (list (fn2-cns-item-pos (car items)) (fn2-cns-item-type (car items)) (nth 4 (car items)))
                                     (nth 1 (helm-seat s db))) db))))

(mutual-recursion
 ; A page for seat S: record it, ack, and if the page said more, read on;
 ; a refusal of rebase-required rebases keeping the cursor, the new
 ; streams added from now. Then re-park if the seat is a waiter. FUEL bounds
 ; the pages (each is a strict advance or a rebase).
 (defun helm-on-page (o s st db ops fault fuel)
   (declare (xargs :verify-guards nil :measure (nfix fuel)))
   (cond ((zp fuel) (mv st db ops))
         ((eq (fn2-cns-class o) :accepted)
          (let ((db (helm-record (fn2-cns-page-items o) s db)))
            (mv-let (a answers st ops) (helm-send (list 'ack s (fn2-cns-page-next o)) st ops fault)
              (declare (ignore a answers))
              (let ((db (helm-put s 0 (fn2-cns-page-next o) db)))
                (if (fn2-cns-page-more o) (helm-turn s st db ops fault (- fuel 1))
                  (helm-rewait s st db ops fault (- fuel 1)))))))
         ((equal o '(:refused rebase-required))
          (mv-let (r answers st ops)
            (helm-send (list 'rebase s (nth 0 (helm-seat s db)) (nth 2 (helm-seat s db)) :keep) st ops fault)
            (declare (ignore answers))
            (if (eq (fn2-cns-class r) :accepted)
                (helm-turn s st (helm-put s 0 (car (cadr r)) db) ops fault (- fuel 1))
              (mv st db ops))))
         (t (mv st db ops))))
 (defun helm-turn (s st db ops fault fuel)
   (declare (xargs :verify-guards nil :measure (nfix fuel)))
   (if (zp fuel) (mv st db ops)
     (mv-let (o answers st ops) (helm-send (list 'read s (nth 0 (helm-seat s db)) *helm-limits*) st ops fault)
       (declare (ignore answers))
       (helm-on-page o s st db ops fault (- fuel 1)))))
 (defun helm-rewait (s st db ops fault fuel)
   (declare (xargs :verify-guards nil :measure (nfix fuel)))
   (if (or (zp fuel) (not (nth 3 (helm-seat s db)))) (mv st db ops)
     (mv-let (o answers st ops) (helm-send (list 'wait s (nth 0 (helm-seat s db)) *helm-limits* 3600) st ops fault)
       (declare (ignore answers))
       (if (eq o :parked) (mv st db ops) (helm-on-page o s st db ops fault (- fuel 1)))))))

(defun helm-answers (answers st db ops fault)
  ; The parked waits that answered during a step.
  (declare (xargs :verify-guards nil))
  (if (atom answers) (mv st db ops)
    (mv-let (st db ops) (helm-on-page (cdar answers) (car (caar answers)) st db ops fault 64)
      (helm-answers (cdr answers) st db ops fault))))

(defun helm-drive (script st db ops woken fault)
  ; (mv st db ops woken): WOKEN records, per world step, the seats its answers woke.
  (declare (xargs :verify-guards nil))
  (if (atom script) (mv st db ops (reverse woken))
    (let ((x (car script)))
      (case (car x)
        (:register
         (let* ((s (cadr x)) (streams (append (cdr (assoc-equal s *helm-streams*)) (list (list :addr s)))))
           (mv-let (o answers st ops) (helm-send (list 'register s s streams :now) st ops fault)
             (declare (ignore answers))
             (helm-drive (cdr script) st (put-assoc-equal s (list (car (cadr o)) nil streams nil) db) ops woken fault))))
        (:wait
         (let ((db (helm-put (cadr x) 3 t db)))
           (mv-let (st db ops) (helm-rewait (cadr x) st db ops fault 64)
             (helm-drive (cdr script) st db ops woken fault))))
        (:stop-waiting (helm-drive (cdr script) st (helm-put (cadr x) 3 nil db) ops woken fault))
        (:turn
         (mv-let (st db ops) (helm-turn (cadr x) st db ops fault 64)
           (helm-drive (cdr script) st db ops woken fault)))
        (:add-stream
         (helm-drive (cdr script) st (helm-put (cadr x) 2 (append (nth 2 (helm-seat (cadr x) db)) (list (caddr x))) db)
                     ops woken fault))
        (otherwise
         (let ((op (if (eq (car x) :post) (list 'append (nth 1 x) (nth 2 x) (nth 3 x) (nth 4 x)) (cadr x))))
           (mv-let (o answers st ops) (helm-send op st ops fault)
             (declare (ignore o))
             (mv-let (st db ops) (helm-answers answers st db ops fault)
               (helm-drive (cdr script) st db ops (cons (cons op (strip-cars (strip-cars answers))) woken) fault)))))))))

(defun helm-world (ops) (declare (xargs :verify-guards nil))
  (if (atom ops) nil (cons (list :world (car ops)) (helm-world (cdr ops)))))
(defun helm-script ()
  (declare (xargs :verify-guards nil))
  (append (helm-world (helm-grants *helm-streams*))
          '((:register "s1") (:register "s2") (:register "s3") (:wait "s1") (:wait "s2") (:wait "s3"))
          (helm-posts 1 20)
          ; s1 tries to post into r3, which it may not: refused by the grant step.
          '((:post "s1" "r3" (nil "not allowed" nil) "s1-denied"))
          (helm-posts 21 30)
          ; s1 is granted r3: its parked wait answers rebase-required; it
          ; rebases keeping its cursor, r3 added from now.
          '((:add-stream "s1" "r3") (:world (:grant "s1" :read "r3")))
          (helm-posts 31 40)
          ; s3 loses r4 but may still post there; its later r4 rows reach nobody.
          '((:world (:revoke "s3" :read "r4")))
          ; Row 10's author withdraws it after every reader acknowledged it.
          '((:world (:withdraw "s1" "<op-s1-row-10@node>")))
          '((:world (:crash)) (:stop-waiting "s2") (:wait "s1") (:wait "s3"))
          (helm-posts 41 60)
          '((:turn "s2") (:turn "s1") (:turn "s3"))))

(defun helm-run (fault)
  (declare (xargs :verify-guards nil))
  (mv-let (st db ops woken) (helm-drive (helm-script) (fn2-cns-init "fn2-history" "fn2-incarnation") nil nil nil fault)
    (mv st db (reverse ops) woken)))

;; The acceptance (e-surface.md 10.2) -----------------------------------------
(defun helm-positions (delivered) (declare (xargs :verify-guards nil)) (reverse (strip-cars delivered)))
(defun helm-strictly-increasing (xs)
  (declare (xargs :verify-guards nil))
  (or (atom xs) (atom (cdr xs)) (and (< (car xs) (cadr xs)) (helm-strictly-increasing (cdr xs)))))
(defun helm-pos-of-mid (mid log)
  (declare (xargs :verify-guards nil))
  (let ((a (fn2-cns-article-of mid log))) (and a (fn2-cns-ev-pos a))))
(defun helm-delivered-at (pos delivered)
  (declare (xargs :verify-guards nil))
  (cond ((atom delivered) nil) ((equal (caar delivered) pos) (car delivered)) (t (helm-delivered-at pos (cdr delivered)))))
(defun helm-room-rows (room log)
  ; Positions of the articles filed in ROOM.
  (declare (xargs :verify-guards nil))
  (cond ((atom log) nil)
        ((and (eq (fn2-cns-ev-kind (car log)) :article) (equal (fn2-cns-ev-streams (car log)) (list room)))
         (cons (fn2-cns-ev-pos (car log)) (helm-room-rows room (cdr log))))
        (t (helm-room-rows room (cdr log)))))
(defun helm-all-delivered (positions delivered)
  (declare (xargs :verify-guards nil))
  (or (atom positions) (and (helm-delivered-at (car positions) delivered) (helm-all-delivered (cdr positions) delivered))))
(defun helm-none-delivered (positions delivered)
  (declare (xargs :verify-guards nil))
  (or (atom positions) (and (not (helm-delivered-at (car positions) delivered)) (helm-none-delivered (cdr positions) delivered))))
(defun helm-split (positions at)
  ; (mv before after) around position AT.
  (declare (xargs :verify-guards nil))
  (if (atom positions) (mv nil nil)
    (mv-let (b a) (helm-split (cdr positions) at)
      (if (< (car positions) at) (mv (cons (car positions) b) a) (mv b (cons (car positions) a))))))

(defun helm-withdraw-pos (log)
  (declare (xargs :verify-guards nil))
  (cond ((atom log) nil) ((eq (fn2-cns-ev-kind (car log)) :withdraw) (fn2-cns-ev-pos (car log))) (t (helm-withdraw-pos (cdr log)))))
(defun helm-woken-by (opid woken)
  ; The seats whose parked waits the append with OPID answered.
  (declare (xargs :verify-guards nil))
  (cond ((atom woken) :not-found)
        ((and (eq (car (caar woken)) 'append) (equal (nth 4 (caar woken)) opid)) (cdar woken))
        (t (helm-woken-by opid (cdr woken)))))
(defun helm-same-set (a b) (declare (xargs :verify-guards nil)) (and (subsetp-equal a b) (subsetp-equal b a)))

(defun helm-accept (st db woken)
  (declare (xargs :verify-guards nil))
  (let* ((log (fn2-cns-get :log st))
         (d1 (nth 1 (helm-seat "s1" db))) (d2 (nth 1 (helm-seat "s2" db))) (d3 (nth 1 (helm-seat "s3" db)))
         (row14 (helm-pos-of-mid "<op-s2-row-14@node>" log))
         (row21 (helm-pos-of-mid "<op-s1-row-21@node>" log))
         (row10 (helm-pos-of-mid "<op-s1-row-10@node>" log))
         (rebase-at (helm-pos-of-mid "<op-s1-row-31@node>" log))   ; the first row after s1's rebase
         (revoke-at (helm-pos-of-mid "<op-s2-row-41@node>" log))   ; the first row after s3's revocation
         (wpos (helm-withdraw-pos log)))
    (mv-let (r3-before r3-after) (helm-split (helm-room-rows "r3" log) rebase-at)
      (mv-let (r4-before r4-after) (helm-split (helm-room-rows "r4" log) revoke-at)
        (and
         ; deliveries in position order with no repeat: an acknowledged row is
         ; never redelivered, across the crash too
         (helm-strictly-increasing (helm-positions d1)) (helm-strictly-increasing (helm-positions d2))
         (helm-strictly-increasing (helm-positions d3))
         ; the group-address row is one entry for each reader of r2, with its reason
         (member :group-address (nth 2 (helm-delivered-at row21 d1)))
         (member :group-address (nth 2 (helm-delivered-at row21 d2)))
         (not (helm-delivered-at row21 d3))
         ; a mention in a room the mentioned seat may not read is never delivered
         (not (helm-delivered-at row14 d1))
         (equal (nth 2 (helm-delivered-at row14 d2)) '(:room))
         ; a mention in a lane the mentioned seat reads carries its reason
         (equal (nth 2 (helm-delivered-at (helm-pos-of-mid "<op-s1-row-7@node>" log) d2)) '(:room :mention))
         ; s1's r3: none before its rebase, every row after it
         (consp r3-after) (helm-none-delivered r3-before d1) (helm-all-delivered r3-after d1)
         ; rooms reach their readers; DM lanes their two members only
         (helm-all-delivered (helm-room-rows "r1" log) d1) (helm-all-delivered (helm-room-rows "r1" log) d3)
         (helm-all-delivered (helm-room-rows "r2" log) d2) (helm-none-delivered (helm-room-rows "r2" log) d3)
         (helm-all-delivered (helm-room-rows "dm.s1.s2" log) d1) (helm-all-delivered (helm-room-rows "dm.s1.s2" log) d2)
         (helm-none-delivered (helm-room-rows "dm.s1.s2" log) d3)
         ; s3's r4 rows reach it until the revocation and never after
         (consp r4-after) (helm-all-delivered r4-before d3) (helm-none-delivered r4-after d3)
         ; row 10 was delivered, then its withdrawal reached both its readers
         (equal (nth 1 (helm-delivered-at row10 d1)) :record)
         (equal (nth 1 (helm-delivered-at wpos d1)) :withdrawal)
         (equal (nth 1 (helm-delivered-at wpos d3)) :withdrawal)
         (not (helm-delivered-at wpos d2))
         ; a row wakes exactly the parked seats whose edges it touches
         (helm-same-set (helm-woken-by "row-1" woken) '("s1" "s3"))
         (helm-same-set (helm-woken-by "row-2" woken) '("s1" "s2")))))))

(defun helm-keystones (ops fault)
  (declare (xargs :verify-guards nil))
  (let ((trace (fn2-cns-trace ops fault)))
    (list :k0 (fn2-cns-declared-p trace) :k1 (fn2-cns-k1-trace trace *helm-limits* fault) :k2 (fn2-cns-k2 trace)
          :k3 (fn2-cns-k3 trace) :k4 (fn2-cns-k4 trace) :k4b (fn2-cns-k4b trace) :k5 (fn2-cns-k5 trace fault)
          :k6 (fn2-cns-k6 trace fault) :k7 (fn2-cns-k7 trace) :k8 (fn2-cns-k8 trace))))
(defun helm-all-true (plist) (declare (xargs :verify-guards nil))
  (or (atom plist) (and (cadr plist) (helm-all-true (cddr plist)))))
(defun helm-keystone-under (fault key)
  (declare (xargs :verify-guards nil))
  (mv-let (st db ops woken) (helm-run fault)
    (declare (ignore st db woken))
    (cadr (member-eq key (helm-keystones ops fault)))))

;; The teeth (owed-consumer.lisp names them).
(defun fn2-cns-test-helm ()
  (declare (xargs :verify-guards nil))
  (mv-let (st db ops woken) (helm-run nil)
    (and (helm-accept st db woken) (helm-all-true (helm-keystones ops nil)))))
(defun fn2-cns-test-helm-negative ()
  (declare (xargs :verify-guards nil))
  (and (not (helm-keystone-under :skip :k1))
       (not (helm-keystone-under :pinned-grant :k7))
       (not (helm-keystone-under :meter-first :k8))))

(assert! (fn2-cns-test-helm))
(assert! (fn2-cns-test-helm-negative))
