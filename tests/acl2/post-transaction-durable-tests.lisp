; Teeth for books/post-transaction-durable (Builder L, landing 1, P4): the
; commit driver fn-ptd on a ground log -- two records recovered at the open,
; a 700-octet record whose entry needs the segment extended, a 4070-octet
; record past the frame -- the commit point (P4-1) and the keystone
; fn-ptd-posted-records-are-recovered-at-every-later-cut with its positive
; witness, one removal per hypothesis and a mutation.
;
; Crash images are fn-bs-crash under explicit choices; fn-bs-crash-imagep is
; a defun-sk, so the keystone's witnesses are ground lemmas
; (teeth-ground-lemma) citing fn-bs-crash-imagep-suff.
(in-package "ACL2")
(include-book "../../books/post-transaction-durable")
(include-book "../../books/frame-trailer")
(include-book "../../books/codec-attach")
(include-book "../../books/defkeystone")
(include-book "teeth-ground-lemma")

(defun ptdt-unit () (declare (xargs :guard t)) 4)
(defun ptdt-max () (declare (xargs :guard t)) 4096)
(defun ptdt-genesis () (declare (xargs :guard t :verify-guards nil)) *fn-lg-genesis*)
(defun ptdt-r (i) (declare (xargs :guard t)) (list i (+ 1 (nfix i)) 7))
(defun ptdt-big () (declare (xargs :guard t)) (make-list 700 :initial-element 5))
(defun ptdt-store (content pending)
  (declare (xargs :guard t))
  (fn-bs-make (ptdt-unit) (list (cons 0 content)) nil pending 1))
; The segment a crash left: two records logged, a torn unit, zeros.
(defun ptdt-content ()
  (declare (xargs :guard t :verify-guards nil))
  (append (fn-lg-log (list (ptdt-r 1) (ptdt-r 2)) (ptdt-genesis) (ptdt-unit))
          '(9 9 9 9 0 0 0 0 0 0 0 0)
          (fn-bs-zeros 512)))
; The string the open read (fn-lgd-octets of it is the content).
(defun ptdt-chars (octets)
  (declare (xargs :guard t))
  (if (atom octets) nil
    (cons (code-char (if (and (natp (car octets)) (< (car octets) 256)) (car octets) 0))
          (ptdt-chars (cdr octets)))))
(defun ptdt-s () (declare (xargs :guard t :verify-guards nil)) (coerce (ptdt-chars (ptdt-content)) 'string))
(defun ptdt-ks0 ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-lgt-recover (fn-lgd-octets (ptdt-s)) (ptdt-genesis) (ptdt-unit) (ptdt-max) 0))
; The store the open's copy leaves: the read's prefix, then zeros.
(defun ptdt-bs0 ()
  (declare (xargs :guard t :verify-guards nil))
  (let ((f (fn-lgk-frontier (ptdt-ks0))))
    (ptdt-store (append (fn-bs-take f (ptdt-content)) (fn-bs-zeros (- (len (ptdt-content)) f))) nil)))
(defun ptdt-st0 ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-ptd-init (ptdt-ks0) (len (fn-bs-durable-content (ptdt-bs0) 0))))
(defun ptdt-run (ins)
  (declare (xargs :guard t :verify-guards nil))
  (fn-ptd-run (ptdt-st0) ins 0 (ptdt-unit) (ptdt-max)))
(defun ptdt-recovered (image)
  (declare (xargs :guard t :verify-guards nil))
  (fn-lgk-committed (fn-lgk-recover (fn-bs-durable-content image 0) (ptdt-genesis) (ptdt-unit) (ptdt-max) 0)))

(defconst *ptdt-post-one* (list (list :begin '(11 12 7)) '(:pwrite . :ok) '(:fsync . :ok)))
(defconst *ptdt-post-big* (list (list :begin (make-list 700 :initial-element 5))
                                '(:pwrite . :ok) '(:fsync . :ok) '(:pwrite . :ok) '(:fsync . :ok)))
(defconst *ptdt-uncertain* (list (list :begin '(11 12 7)) '(:pwrite . :ok) '(:fsync :eio (nil))))

; -----------------------------------------------------------------------------
; Reachable: the open is related; one post and an extending post are answered
; :posted, acknowledged, and their records are the kernel's new ones; an
; oversize record is refused; a failed barrier answers :uncertain.
(assert-event
 (and (equal (fn-lgd-octets (ptdt-s)) (ptdt-content))
      (fn-lgk-relp (ptdt-bs0) (ptdt-ks0) 0 (ptdt-genesis) (ptdt-max))
      (mv-let (st a ans ops) (ptdt-run *ptdt-post-one*)
        (declare (ignore a ops))
        (and (equal ans '((:posted 11 12 7)))
             (equal (fn-ptd-ph st) :ready)
             (equal (fn-lgk-acked (fn-ptd-ks st)) 3)))
      (mv-let (st a ans ops) (ptdt-run *ptdt-post-big*)
        (declare (ignore ops))
        (and (equal (strip-cars ans) '(:posted))
             (equal (len a) 4)
             (< (fn-ptd-ext (ptdt-st0)) (fn-ptd-ext st))))
      (mv-let (st a ans ops) (ptdt-run (list (list :begin (make-list 4070 :initial-element 6))))
        (declare (ignore st a ops))
        (equal (strip-cars ans) '(:refused)))
      (mv-let (st a ans ops) (ptdt-run *ptdt-uncertain*)
        (declare (ignore a ops))
        (and (equal (strip-cars ans) '(:uncertain)) (equal (fn-ptd-ph st) :fenced)))))

; -----------------------------------------------------------------------------
; P4-1: the commit point is the barrier's completion.
(defconst-eval *ptdt-syncing*
  (mv-let (st a ans ops) (ptdt-run (take 2 *ptdt-post-one*)) (declare (ignore a ans ops)) st))
(defteeth fn-ptd-posted-only-at-the-barrier-completion
  :claim (() (mv-let (st1 acts ans ops) (fn-ptd-step st in ino unit max)
               (declare (ignore st1 acts))
               (and (iff (consp (fn-ptd-posted ans))
                         (and (equal (fn-ptd-ph st) :syncing) (equal in '(:fsync . :ok))))
                    (implies (consp (fn-ptd-posted ans))
                             (and (equal ans (list (cons :posted (fn-ptd-rec st))))
                                  (equal ops '((:fence :ok) (:finish-one))))))))
  :subject fn-ptd-step
  :witness ((st *ptdt-syncing*) (in '(:fsync . :ok)) (ino 0) (unit 4) (max 4096))
  :mutations ((posts-on-the-record-write
               (:conclusion (mv-let (st1 acts ans ops) (fn-ptd-step st in ino unit max)
                              (declare (ignore st1 acts ops))
                              (iff (consp (fn-ptd-posted ans))
                                   (and (equal (fn-ptd-ph st) :writing) (equal in '(:pwrite . :ok))))))
               ((st *ptdt-syncing*) (in '(:fsync . :ok)) (ino 0) (unit 4) (max 4096))
               :fault "the commit point placed at the record write's completion instead of the barrier's")))

; -----------------------------------------------------------------------------
; The keystone: the open's two records and one post, every later cut.

(defconst-eval *ptdt-k-s* (ptdt-s))
(defconst-eval *ptdt-k-g* (ptdt-genesis))
(defconst-eval *ptdt-k-bs0* (ptdt-bs0))
(defconst-eval *ptdt-k-ks0* (ptdt-ks0))
(defconst-eval *ptdt-k-ops1*
  (mv-let (st a ans ops) (ptdt-run *ptdt-post-one*) (declare (ignore st a ans)) ops))
(defconst-eval *ptdt-k-run1* (fn-lgu-host-run *ptdt-k-bs0* *ptdt-k-ks0* *ptdt-k-ops1* 0 4096))
(defconst-eval *ptdt-k-f1* (fn-lgu-host-final *ptdt-k-bs0* *ptdt-k-ks0* *ptdt-k-ops1* 0 4096))
(defconst-eval *ptdt-k-image* (fn-bs-crash (car *ptdt-k-f1*) nil))
(assert-event (and (equal (len (ptdt-recovered *ptdt-k-image*)) 3)
                   (null (fn-bs-pending (car *ptdt-k-f1*)))))

; Without R: the open's store with a write of zeros pending over its first
; unit; the start cut's image that lands it recovers nothing.
(defconst-eval *ptdt-k-bs-unrel*
  (fn-bs-make 4 (fn-bs-inodes *ptdt-k-bs0*) nil (list (list :write 0 0 (fn-bs-zeros 4))) 1))
(defconst-eval *ptdt-k-unrel-image* (fn-bs-crash *ptdt-k-bs-unrel* '((:new))))
; Without the membership: the cut where the record's write is pending, which
; is before the answer, not after it; its image that lands nothing.
(defconst-eval *ptdt-k-early-pair* (nth 3 *ptdt-k-run1*))
(defconst-eval *ptdt-k-early-image* (fn-bs-crash (car *ptdt-k-early-pair*) nil))
; Without the image: a wiped segment.
(defconst-eval *ptdt-k-wiped*
  (ptdt-store (fn-bs-zeros (len (fn-bs-durable-content (car *ptdt-k-f1*) 0))) nil))
; The mutation's run: a barrier that fails having landed nothing.
(defconst-eval *ptdt-k-u-ops1*
  (mv-let (st a ans ops) (ptdt-run *ptdt-uncertain*) (declare (ignore st a ans)) ops))
(defconst-eval *ptdt-k-u-f1* (fn-lgu-host-final *ptdt-k-bs0* *ptdt-k-ks0* *ptdt-k-u-ops1* 0 4096))
(defconst-eval *ptdt-k-u-image* (fn-bs-crash (car *ptdt-k-u-f1*) nil))

; The records answered :posted or :uncertain, in order (the mutation's
; claim: an uncertain answer counted as durable).
(defun ptdt-answered (answers)
  (declare (xargs :guard t))
  (cond ((atom answers) nil)
        ((and (consp (car answers)) (member-eq (car (car answers)) '(:posted :uncertain)))
         (cons (cdr (car answers)) (ptdt-answered (cdr answers))))
        (t (ptdt-answered (cdr answers)))))

(defconst-eval *ptdt-k-ks-unacked*
  (fn-lgk-make (fn-lgk-committed *ptdt-k-ks0*) (fn-lgk-last *ptdt-k-ks0*) (fn-lgk-frontier *ptdt-k-ks0*)
               (fn-lgk-next-txid *ptdt-k-ks0*) nil nil 0 (fn-lgk-phase *ptdt-k-ks0*)))
(defconst-eval *ptdt-k-ua-f1*
  (fn-lgu-host-final *ptdt-k-bs0* *ptdt-k-ks-unacked*
                     (mv-let (st a ans ops)
                       (fn-ptd-run (fn-ptd-init *ptdt-k-ks-unacked* (len (fn-bs-durable-content *ptdt-k-bs0* 0)))
                                   *ptdt-post-one* 0 4 4096)
                       (declare (ignore st a ans)) ops)
                     0 4096))
(defconst-eval *ptdt-k-ua-image* (fn-bs-crash (car *ptdt-k-ua-f1*) nil))

(defconst *ptdt-c-key*
  '(let* ((unit (fn-bs-unit bs))
          (r1 (fn-ptd-run (fn-ptd-init ks0 (len (fn-bs-durable-content bs ino))) e1 ino unit max))
          (r2 (fn-ptd-run (mv-nth 0 r1) e2 ino unit max))
          (f1 (fn-lgu-host-final bs ks0 (mv-nth 3 r1) ino max))
          (p (fn-ptd-posted (mv-nth 2 r1)))
          (a0 (fn-lgk-acked ks0))
          (recovered (fn-lgk-committed (fn-lgk-recover (fn-bs-durable-content image ino)
                                                       genesis unit max next-txid))))
     (((rel (fn-lgk-relp bs ks0 ino genesis max))
       (opened (fn-ptd-open-kernelp ks0))
       (member (member-equal pair (fn-lgu-host-run (car f1) (cdr f1) (mv-nth 3 r2) ino max)))
       (img (fn-bs-crash-imagep (car pair) image)))
      (and (<= (+ a0 (len p)) (len recovered))
           (equal (take a0 recovered) (take a0 (fn-lgk-committed ks0)))
           (equal (take (len p) (nthcdr a0 recovered)) p)))))

; The ground lemmas instantiate the claim's LET* at the witnesses, which
; leaves bindings unused.
(set-ignore-ok t)

(teeth-ground-lemma ptdt-gl-key-witness *ptdt-c-key*
  ((bs *ptdt-k-bs0*) (ks0 *ptdt-k-ks0*) (genesis *ptdt-k-g*) (max 4096) (ino 0) (next-txid 0) (e1 *ptdt-post-one*) (e2 nil) (pair *ptdt-k-f1*) (image *ptdt-k-image*))

  :hints (("Goal" :in-theory (set-difference-theories (executable-counterpart-theory :here)
                                                      '((:executable-counterpart fn-bs-crash-imagep)))
           :use ((:instance fn-bs-crash-imagep-suff (s (car *ptdt-k-f1*)) (image *ptdt-k-image*) (choices nil))))))
(teeth-ground-lemma ptdt-gl-key-no-rel *ptdt-c-key*
  ((bs *ptdt-k-bs-unrel*) (ks0 *ptdt-k-ks0*) (genesis *ptdt-k-g*) (max 4096) (ino 0) (next-txid 0) (e1 nil) (e2 nil) (pair (cons *ptdt-k-bs-unrel* *ptdt-k-ks0*)) (image *ptdt-k-unrel-image*))
  :without rel
  :hints (("Goal" :in-theory (set-difference-theories (executable-counterpart-theory :here)
                                                      '((:executable-counterpart fn-bs-crash-imagep)))
           :use ((:instance fn-bs-crash-imagep-suff (s *ptdt-k-bs-unrel*) (image *ptdt-k-unrel-image*) (choices '((:new))))))))
(teeth-ground-lemma ptdt-gl-key-no-opened *ptdt-c-key*
  ((bs *ptdt-k-bs0*) (ks0 *ptdt-k-ks-unacked*) (genesis *ptdt-k-g*) (max 4096) (ino 0) (next-txid 0) (e1 *ptdt-post-one*) (e2 nil) (pair *ptdt-k-ua-f1*) (image *ptdt-k-ua-image*))
  :without opened
  :hints (("Goal" :in-theory (set-difference-theories (executable-counterpart-theory :here)
                                                      '((:executable-counterpart fn-bs-crash-imagep)))
           :use ((:instance fn-bs-crash-imagep-suff (s (car *ptdt-k-ua-f1*)) (image *ptdt-k-ua-image*) (choices nil))))))
(teeth-ground-lemma ptdt-gl-key-no-member *ptdt-c-key*
  ((bs *ptdt-k-bs0*) (ks0 *ptdt-k-ks0*) (genesis *ptdt-k-g*) (max 4096) (ino 0) (next-txid 0) (e1 *ptdt-post-one*) (e2 nil) (pair *ptdt-k-early-pair*) (image *ptdt-k-early-image*))
  :without member
  :hints (("Goal" :in-theory (set-difference-theories (executable-counterpart-theory :here)
                                                      '((:executable-counterpart fn-bs-crash-imagep)))
           :use ((:instance fn-bs-crash-imagep-suff (s (car *ptdt-k-early-pair*)) (image *ptdt-k-early-image*) (choices nil))))))
(teeth-ground-lemma ptdt-gl-key-no-img *ptdt-c-key*
  ((bs *ptdt-k-bs0*) (ks0 *ptdt-k-ks0*) (genesis *ptdt-k-g*) (max 4096) (ino 0) (next-txid 0) (e1 *ptdt-post-one*) (e2 nil) (pair *ptdt-k-f1*) (image *ptdt-k-wiped*))
  :without img :keystone fn-ptd-posted-records-are-recovered-at-every-later-cut)
(teeth-ground-lemma ptdt-gl-key-mutant *ptdt-c-key*
  ((bs *ptdt-k-bs0*) (ks0 *ptdt-k-ks0*) (genesis *ptdt-k-g*) (max 4096) (ino 0) (next-txid 0) (e1 *ptdt-uncertain*) (e2 nil) (pair *ptdt-k-u-f1*) (image *ptdt-k-u-image*))
  :mutation (:conclusion
             (let ((q (ptdt-answered (mv-nth 2 r1))))
               (and (<= (+ a0 (len q)) (len recovered))
                    (equal (take a0 recovered) (take a0 (fn-lgk-committed ks0)))
                    (equal (take (len q) (nthcdr a0 recovered)) q))))
  :hints (("Goal" :in-theory (set-difference-theories (executable-counterpart-theory :here)
                                                      '((:executable-counterpart fn-bs-crash-imagep)))
           :use ((:instance fn-bs-crash-imagep-suff (s (car *ptdt-k-u-f1*)) (image *ptdt-k-u-image*) (choices nil))))))

(defteeth fn-ptd-posted-records-are-recovered-at-every-later-cut
  :claim (let* ((unit (fn-bs-unit bs))
          (r1 (fn-ptd-run (fn-ptd-init ks0 (len (fn-bs-durable-content bs ino))) e1 ino unit max))
          (r2 (fn-ptd-run (mv-nth 0 r1) e2 ino unit max))
          (f1 (fn-lgu-host-final bs ks0 (mv-nth 3 r1) ino max))
          (p (fn-ptd-posted (mv-nth 2 r1)))
          (a0 (fn-lgk-acked ks0))
          (recovered (fn-lgk-committed (fn-lgk-recover (fn-bs-durable-content image ino)
                                                       genesis unit max next-txid))))
     (((rel (fn-lgk-relp bs ks0 ino genesis max))
       (opened (fn-ptd-open-kernelp ks0))
       (member (member-equal pair (fn-lgu-host-run (car f1) (cdr f1) (mv-nth 3 r2) ino max)))
       (img (fn-bs-crash-imagep (car pair) image)))
      (and (<= (+ a0 (len p)) (len recovered))
           (equal (take a0 recovered) (take a0 (fn-lgk-committed ks0)))
           (equal (take (len p) (nthcdr a0 recovered)) p))))
  :subject fn-ptd-run
  :witness ((bs *ptdt-k-bs0*) (ks0 *ptdt-k-ks0*) (genesis *ptdt-k-g*) (max 4096) (ino 0) (next-txid 0) (e1 *ptdt-post-one*) (e2 nil) (pair *ptdt-k-f1*) (image *ptdt-k-image*))
  :witness-lemma ptdt-gl-key-witness
  :breaks ((rel ((bs *ptdt-k-bs-unrel*) (e1 nil) (pair (cons *ptdt-k-bs-unrel* *ptdt-k-ks0*))
                 (image *ptdt-k-unrel-image*))
                :lemma ptdt-gl-key-no-rel)
           (opened ((ks0 *ptdt-k-ks-unacked*) (pair *ptdt-k-ua-f1*) (image *ptdt-k-ua-image*))
                   :lemma ptdt-gl-key-no-opened)
           (member ((pair *ptdt-k-early-pair*) (image *ptdt-k-early-image*))
                   :lemma ptdt-gl-key-no-member)
           (img ((image *ptdt-k-wiped*)) :lemma ptdt-gl-key-no-img))
  :mutations ((uncertain-counted-as-durable
               (:conclusion
                (let ((q (ptdt-answered (mv-nth 2 r1))))
                  (and (<= (+ a0 (len q)) (len recovered))
                       (equal (take a0 recovered) (take a0 (fn-lgk-committed ks0)))
                       (equal (take (len q) (nthcdr a0 recovered)) q))))
               ((bs *ptdt-k-bs0*) (ks0 *ptdt-k-ks0*) (genesis *ptdt-k-g*) (max 4096) (ino 0) (next-txid 0) (e1 *ptdt-uncertain*) (e2 nil) (pair *ptdt-k-u-f1*) (image *ptdt-k-u-image*))
               :fault "a record answered :uncertain (its barrier failed) claimed recovered like a :posted one"
               :lemma ptdt-gl-key-mutant)))
