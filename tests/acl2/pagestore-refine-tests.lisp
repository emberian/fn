; fn: teeth for books/pagestore-refine.lisp (lane arena-store-5, 2026-09-28).
;
; What this book is evidence FOR.  The two squares the host's page-store
; commands stand on: pgs-x-commit-refines-plan (and its disk forms
; pgs-x-commit-refines-crash, pgs-x-commit-refines-commit) -- the plan
; `pgs-x-commit' answers, abstracted, IS `pgs-plan-commit' over the
; abstraction of the handle and the files -- and pgs-x-fork-refines -- the
; root page `pgs-x-fork' leaves, abstracted, IS `pgs-fork''s.
;
; The digest seam is attached to the REALIZED digest (`pgs-rt-digest'):
; BLAKE3 of the words the executable hashes for the same object (a data
; page's words; a table's encoded run; a record body's sixteen words), so
; the A-PGS-OBSERVE hypotheses of the square are TRUE on the ground
; states below, not assumed.  Each digest-hypothesis removal witness
; re-attaches a digest that disagrees with BLAKE3 on exactly one object.
;
; The store (`pgs-rt-scene'): 342 logical pages, so two table pages (341
; and 1 entries) at 10 and 11 and a one-page directory at 5; its record
; (txid 2, entries txid 1) sits in slot 0; the page file's model pages are
; the directory and the two table pages (a :lazy open checks only the
; entries its own commit wrote, so no data page is read).  The commit:
; page 0 dirty (its 2048 words), txid 3, record to slot 512, allocator
; (nil 1000).  Positive witnesses assert every hypothesis and the complete
; conclusion; per hypothesis a removal witness asserts every retained
; hypothesis, the failure of the removed one and of the conclusion, and a
; must-fail-checked of the weakened statement.
;
; Not witnessed (named, not hidden): the representation and type
; preconditions pgs-x-tab-inv, pgs-x-dir-inv, pgs-memp, (natp n),
; (nat-listp lpages) of the commit square are the preconditions of
; pgs-x-commit-refines, the keystone the square is built on; no violation
; found keeps the digest observations true and the conclusion false, and
; none is shown redundant (a failed proof search is not a counterexample).
; The fork's (<= 1024 (pgs-m-length pgs-mem)) has its counterexample named
; below but not evaluated (a live stobj cannot be read past its end).
(in-package "ACL2")
(include-book "../../books/pagestore-refine")
(include-book "../../books/pagestore-words-blake3")
(include-book "must-fail-checked")

; -----------------------------------------------------------------------------
; The realized digest.

(defun pgs-rt-wd (ws)
  (declare (xargs :guard t))
  (pgs-octets-be-nat (fn-blake3 (pgs-words-le-octets ws))))

(defun pgs-rt-rec-words (b)
  ; The sixteen words `pgs-x-write-rec' writes for the body B.
  (declare (xargs :guard (true-listp b)))
  (let ((d (nfix (fifth b))))
    (list *pgs-magic* (pgs-dlo (second b)) (pgs-dlo (third b)) (pgs-dlo (fourth b)) *pgs-page-words* 0 0 0
          (pgs-dlo (pgs-dhi (pgs-dhi (pgs-dhi d)))) (pgs-dlo (pgs-dhi (pgs-dhi d))) (pgs-dlo (pgs-dhi d)) (pgs-dlo d)
          0 0 0 0)))

(defconst *pgs-rt-empty* (pgs-rt-wd (pgs-encode-run nil 1)))   ; the empty table's page

(defun pgs-rt-digest (x)
  ; BLAKE3 of the words the executable hashes for X: a record body's
  ; sixteen words, a table's encoded run (the empty one's precomputed:
  ; every empty slot's validity asks for it), else X as words.
  (declare (xargs :guard t))
  (cond ((null x) *pgs-rt-empty*)
        ((and (true-listp x) (equal (len x) 5) (eq (car x) :pgs-commit))
         (pgs-rt-wd (pgs-rt-rec-words x)))
        ((pgs-ptab-p x) (pgs-rt-wd (pgs-encode-run x (pgs-ptab-run-pages (len x)))))
        (t (pgs-rt-wd x))))

(defattach pgs-digest pgs-rt-digest)

; -----------------------------------------------------------------------------
; The store and the two commands, on the executable.

(defun pgs-rt-page-words (k seed)
  (declare (xargs :guard (and (natp k) (natp seed))))
  (if (zp k) nil (cons (mod (+ (nfix seed) (* 7 k)) 18446744073709551616) (pgs-rt-page-words (1- k) seed))))

(defun pgs-rt-fill-w (i ws pgs-mem)
  (declare (xargs :stobjs pgs-mem :verify-guards nil))
  (if (atom ws)
      pgs-mem
    (let ((pgs-mem (update-pgs-wi i (car ws) pgs-mem)))
      (pgs-rt-fill-w (+ 1 i) (cdr ws) pgs-mem))))

(defmacro pgs-rt-knob (k default) `(let ((a (assoc-eq ,k kn))) (if a (cdr a) ,default)))

(defun pgs-rt-scene (kn)
  ; The store, the handle open on its record, then either the commit or
  ; the fork, per the knobs KN (an alist): :lpages :txid :alloc :slot
  ; :bad-ddig (the record names a wrong directory digest) :rec-slot (0 or
  ; 512) :perturb-tab :perturb-dir :mlen :fork-k.
  (declare (xargs :verify-guards nil))
  (let ((lpages (pgs-rt-knob :lpages '(0))) (txid (pgs-rt-knob :txid 3))
        (alloc (pgs-rt-knob :alloc '(nil 1000))) (slot (pgs-rt-knob :slot 512))
        (rec-slot (pgs-rt-knob :rec-slot 0)) (fork-k (pgs-rt-knob :fork-k nil)))
    (with-local-stobj pgs-mem
      (mv-let (r pgs-mem)
        (with-local-stobj fn-octets-pg
          (mv-let (r pgs-mem fn-octets-pg)
            (let* ((pgs-mem (pgs-x-reset-table 0 pgs-mem))
                   (pgs-mem (resize-pgs-m 0 pgs-mem))
                   (pgs-mem (resize-pgs-m (+ *pgs-x-dir-base* 2048) pgs-mem)))
              (mv-let (n pgs-mem)
                (pgs-x-plan-tab (pgs-x-iota 0 342) (pgs-x-iota 100 442) (pgs-x-iota 0 342) 1 0 pgs-mem)
                (mv-let (nd pgs-mem)
                  (pgs-x-plan-dir '(0 1) '(10 11) '(7 8) 1 0 pgs-mem)
                  (let* ((tab (pgs-x-tab n pgs-mem)) (dir (pgs-x-dir nd pgs-mem))
                         (cs (cons (list (cons 5 dir) (cons 10 (take 341 tab)) (cons 11 (nthcdr 341 tab))) nil)))
                    (mv-let (ddig fn-octets-pg)
                      (pgs-x-words-digest 1 *pgs-x-dir-base* 256 pgs-mem fn-octets-pg)
                      (mv-let (rec pgs-mem fn-octets-pg)
                        (pgs-x-write-rec rec-slot 2 5 342 (+ ddig (if (pgs-rt-knob :bad-ddig nil) 1 0))
                                         pgs-mem fn-octets-pg)
                        (declare (ignore rec))
                        (let* ((pgs-mem (resize-pgs-tv 2 pgs-mem))
                               (pgs-mem (update-pgs-tvi 0 2 pgs-mem))
                               (pgs-mem (update-pgs-tvi 1 2 pgs-mem))
                               (pgs-mem (resize-pgs-w 2048 pgs-mem))
                               (pgs-mem (resize-pgs-v 1 pgs-mem))
                               (pgs-mem (resize-pgs-d 1 pgs-mem))
                               (pgs-mem (pgs-rt-fill-w 0 (pgs-rt-page-words 2048 17) pgs-mem))
                               (pgs-mem (update-pgs-di 0 1 pgs-mem))
                               (pgs-mem (if (pgs-rt-knob :perturb-tab nil)
                                            (pgs-x-set-entry 2 0 5 '(999 1 3) pgs-mem) pgs-mem))
                               (pgs-mem (if (pgs-rt-knob :perturb-dir nil)
                                            (pgs-x-set-entry 1 *pgs-x-dir-base* 1 '(11 1 9) pgs-mem) pgs-mem))
                               (pgs-mem (if (pgs-rt-knob :mlen nil)
                                            (resize-pgs-m (pgs-rt-knob :mlen nil) pgs-mem) pgs-mem))
                               (w (pgs-x-words 1 0 1024 pgs-mem))
                               (base (list :d (pgs-x-abs-disk cs :main pgs-mem) :w w :cs cs
                                           :mlen (pgs-m-length pgs-mem))))
                          (if fork-k
                              (mv-let (v pgs-mem)
                                (pgs-x-fork fork-k pgs-mem)
                                (mv (append base
                                            (list :v v
                                                  :lhs (pgs-x-abs-disk (pgs-x-cs-put-root :main w cs) :br pgs-mem)))
                                    pgs-mem fn-octets-pg))
                            (let ((dirty (pgs-x-abs-dirty lpages pgs-mem))
                                  (tabx (pgs-x-tab 342 pgs-mem)) (dirx (pgs-x-dir 2 pgs-mem))
                                  (invs (and (pgs-x-tab-inv 342 pgs-mem)
                                             (pgs-x-dir-inv *pgs-x-dir-base* 2 pgs-mem)))
                                  (memp (pgs-memp pgs-mem)))
                              (mv-let (xdig fn-octets-pg)
                                (pgs-x-dirty-digests lpages pgs-mem fn-octets-pg)
                                (mv-let (res pgs-mem fn-octets-pg)
                                  (pgs-x-commit lpages 342 txid alloc slot pgs-mem fn-octets-pg)
                                  (mv (append base
                                              (list :dirty dirty :tabx tabx :dirx dirx :invs invs :memp memp
                                                    :xdig xdig :res res
                                                    :writes (pgs-x-abs-writes lpages res pgs-mem)
                                                    :tab2 (pgs-x-tab (pgs-grown-len lpages 342) pgs-mem)
                                                    :dir2 (pgs-x-dir (pgs-ntables (pgs-grown-len lpages 342)) pgs-mem)
                                                    :lhs (pgs-x-abs-disk (pgs-x-commit-files cs :main nil lpages w res
                                                                                             pgs-mem)
                                                                         :main pgs-mem)
                                                    :lhs-keep (pgs-x-abs-disk (pgs-x-commit-files cs :main '(t nil t)
                                                                                                  lpages w res pgs-mem)
                                                                              :main pgs-mem)
                                                    :lpages lpages :txid txid :alloc alloc :slot slot))
                                      pgs-mem fn-octets-pg))))))))))))
            (mv r pgs-mem)))
        r))))

(defmacro pgs-rt (s k) `(cadr (member-eq ,k ,s)))

; -----------------------------------------------------------------------------
; The commit square's hypotheses and conclusions over a scene S (:lazy).

(defun pgs-rt-commit-check (s)
  ; (HYPS . CONCLS): HYPS (KEY . VALUE) per hypothesis of
  ; pgs-x-commit-refines-plan in order; CONCLS the three conclusions (the
  ; plan square, the complete commit, the crash image with the second write
  ; lost).  The open once for the hypotheses.
  (declare (xargs :verify-guards nil))
  (let* ((d (pgs-rt s :d)) (res (pgs-rt s :res)) (lpages (pgs-rt s :lpages)) (alloc (pgs-rt s :alloc))
         (dirty (pgs-rt s :dirty))
         (o (pgs-open d :main :lazy))
         (cur (pgs-slot (second o) (pgs-root-slots :main d)))
         (p (pgs-plan-commit d :main :lazy dirty alloc)))
    (cons (list (cons :open (equal (car o) :ok))
                (cons :slot (equal (pgs-rt s :slot) (if (equal (second o) 1) 0 512)))
                (cons :txid (equal (pgs-rt s :txid) (pgs-next-txid (pgs-x-slots-of-words (pgs-rt s :w)))))
                (cons :tab (equal (pgs-rt s :tabx) (pgs-sp cur (car (pgs-rt s :cs)))))
                (cons :dir (equal (pgs-rt s :dirx) (pgs-sd cur (car (pgs-rt s :cs)))))
                (cons :invs (pgs-rt s :invs))
                (cons :memp (pgs-rt s :memp))
                (cons :n (natp 342))
                (cons :lpages (nat-listp lpages))
                (cons :free (nat-listp (pgs-alloc-free alloc)))
                (cons :dig (equal (pgs-rt s :xdig) (pgs-dirty-digests dirty)))
                (cons :tdig (equal (nth 9 res)
                                   (pgs-dirty-digests (pgs-table-dirty (pgs-touched lpages nil)
                                                                       (pgs-chunk (pgs-rt s :tab2))))))
                (cons :rec (pgs-rec-valid (nth 1 res)))
                (cons :ddig (equal (pgs-rec-dir-digest (nth 1 res)) (pgs-digest (pgs-rt s :dir2)))))
          (list (equal p (list :plan (pgs-rt s :writes) (if (equal (pgs-rt s :slot) 0) 0 1) (nth 1 res) (nth 7 res)))
                (equal (pgs-rt s :lhs) (pgs-commit d :main :lazy dirty alloc))
                (equal (pgs-rt s :lhs-keep) (pgs-crash d :main (second p) '(t nil t) (third p) (fourth p)))))))

(defun pgs-rt-all-but (key hyps)
  ; Every hypothesis but KEY holds, and KEY fails.
  (declare (xargs :guard (alistp hyps)))
  (if (atom hyps)
      t
    (and (if (equal (caar hyps) key) (not (cdar hyps)) (cdar hyps))
         (pgs-rt-all-but key (cdr hyps)))))

(defconst *pgs-rt-base* (pgs-rt-scene nil))

; Positive witness: every hypothesis, and all three conclusions.
(assert-event (let ((c (pgs-rt-commit-check *pgs-rt-base*)))
                (and (pgs-rt-all-but :none (car c)) (equal (cdr c) '(t t t)))))
; ... on a real plan: the run at 1000, page 0 to 1001, table page 0 to 1002.
(assert-event (equal (take 6 (pgs-rt *pgs-rt-base* :res))
                     (list :plan (nth 1 (pgs-rt *pgs-rt-base* :res)) '(1001) '(0) '(1002) 1000)))

; -----------------------------------------------------------------------------
; The commit square's hypothesis removals.  Each: the retained hypotheses
; hold, the removed one fails, the conclusion fails; then the weakened
; statement does not prove.

(defmacro pgs-rt-plan-weakened (name drop)
  ; pgs-x-commit-refines-plan without the hypothesis keyed DROP.
  (let ((hyps (remove-assoc-eq
               drop
               '((:open . (equal (car (pgs-open (pgs-x-abs-disk cs r pgs-mem) r mode)) :ok))
                 (:slot . (equal slot (if (equal (second (pgs-open (pgs-x-abs-disk cs r pgs-mem) r mode)) 1) 0 512)))
                 (:txid . (equal txid (pgs-next-txid (pgs-x-slots-of-words (pgs-x-words 1 0 1024 pgs-mem)))))
                 (:tab . (equal (pgs-x-tab n pgs-mem)
                                (pgs-sp (pgs-c-cur (pgs-x-abs-disk cs r pgs-mem) r mode) (car cs))))
                 (:dir . (equal (pgs-x-dir (pgs-ntables n) pgs-mem)
                                (pgs-sd (pgs-c-cur (pgs-x-abs-disk cs r pgs-mem) r mode) (car cs))))
                 (:tinv . (pgs-x-tab-inv n pgs-mem))
                 (:dinv . (pgs-x-dir-inv *pgs-x-dir-base* (pgs-ntables n) pgs-mem))
                 (:memp . (pgs-memp pgs-mem)) (:n . (natp n)) (:lpages . (nat-listp lpages))
                 (:free . (nat-listp (pgs-alloc-free alloc)))
                 (:dig . (equal (mv-nth 0 (pgs-x-dirty-digests lpages pgs-mem fn-octets-pg))
                                (pgs-dirty-digests (pgs-x-abs-dirty lpages pgs-mem))))
                 (:tdig . (equal (nth 9 (mv-nth 0 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg)))
                                 (pgs-dirty-digests
                                  (pgs-table-dirty (pgs-touched lpages nil)
                                                   (pgs-chunk (pgs-x-tab (pgs-grown-len lpages n)
                                                                         (mv-nth 1 (pgs-x-commit lpages n txid alloc slot
                                                                                                 pgs-mem fn-octets-pg))))))))
                 (:rec . (pgs-rec-valid (nth 1 (mv-nth 0 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg)))))
                 (:ddig . (equal (pgs-rec-dir-digest (nth 1 (mv-nth 0 (pgs-x-commit lpages n txid alloc slot pgs-mem
                                                                                   fn-octets-pg))))
                                 (pgs-digest (pgs-x-dir (pgs-ntables (pgs-grown-len lpages n))
                                                        (mv-nth 1 (pgs-x-commit lpages n txid alloc slot pgs-mem
                                                                                fn-octets-pg))))))))))
    `(must-fail-checked
      (defthm ,name
        (implies (and ,@(strip-cdrs hyps))
                 (equal (pgs-plan-commit (pgs-x-abs-disk cs r pgs-mem) r mode (pgs-x-abs-dirty lpages pgs-mem) alloc)
                        (list :plan
                              (pgs-x-abs-writes lpages (mv-nth 0 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg))
                                                (mv-nth 1 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg)))
                              (if (equal slot 0) 0 1)
                              (nth 1 (mv-nth 0 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg)))
                              (nth 7 (mv-nth 0 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg)))))))
      :step-limit 20000)))

(defmacro pgs-rt-removal (key knobs name)
  `(progn
     (assert-event (let ((c (pgs-rt-commit-check (pgs-rt-scene ',knobs))))
                     (and (pgs-rt-all-but ,key (car c)) (not (car (cdr c))))))
     (pgs-rt-plan-weakened ,name ,key)))

; The open: the record names a wrong directory digest, so R does not open
; (the host's handle is the same); the model refuses, the executable plans.
(pgs-rt-removal :open ((:bad-ddig . t)) pgs-rt-false-plan-without-open)
; The slot: the record goes over the slot the open landed on.
(pgs-rt-removal :slot ((:slot . 0)) pgs-rt-false-plan-without-slot)
; The txid: 7, not one past the newest valid slot.
(pgs-rt-removal :txid ((:txid . 7)) pgs-rt-false-plan-without-txid)
; The table: the handle's entry 5 (table page 0, the one the commit writes)
; is not the record's.
(pgs-rt-removal :tab ((:perturb-tab . t)) pgs-rt-false-plan-without-tab)
; The directory: the handle's entry for table page 1 (not written) is not
; the record's; the new directory carries it.
(pgs-rt-removal :dir ((:perturb-dir . t)) pgs-rt-false-plan-without-dir)
; The free list: a non-natural at its head; the model's run starts there,
; the executable's at 0.
(pgs-rt-removal :free ((:alloc . ((:x) 1000))) pgs-rt-false-plan-without-free)

; -----------------------------------------------------------------------------
; The fork square: pgs-x-fork-refines.

(defun pgs-rt-fork-hyps (s k)
  (declare (xargs :verify-guards nil))
  (let ((o (pgs-open (pgs-rt s :d) :main :lazy)))
    (list (cons :open (equal (car o) :ok))
          (cons :k (equal (second o) k))
          (cons :mlen (<= 1024 (pgs-rt s :mlen))))))

(defun pgs-rt-fork-concl (s)
  (declare (xargs :verify-guards nil))
  (equal (pgs-rt s :lhs) (pgs-fork (pgs-rt s :d) :main :br :lazy)))

(defmacro pgs-rt-fork-weakened (name drop)
  (let ((hyps (remove-assoc-eq
               drop
               '((:open . (equal (car (pgs-open (pgs-x-abs-disk cs r pgs-mem) r mode)) :ok))
                 (:k . (equal (second (pgs-open (pgs-x-abs-disk cs r pgs-mem) r mode)) k))
                 (:mlen . (<= 1024 (pgs-m-length pgs-mem)))))))
    `(must-fail-checked
      (defthm ,name
        (implies (and ,@(strip-cdrs hyps))
                 (equal (pgs-x-abs-disk (pgs-x-cs-put-root r (pgs-x-words 1 0 1024 pgs-mem) cs) r2
                                        (mv-nth 1 (pgs-x-fork k pgs-mem)))
                        (pgs-fork (pgs-x-abs-disk cs r pgs-mem) r r2 mode))))
      :step-limit 20000)))

; Positive witness: the fork of the record in slot 0.
(defconst *pgs-rt-fork* (pgs-rt-scene '((:fork-k . 0))))
(assert-event (and (pgs-rt-all-but :none (pgs-rt-fork-hyps *pgs-rt-fork* 0))
                   (null (pgs-rt *pgs-rt-fork* :v))
                   (pgs-rt-fork-concl *pgs-rt-fork*)))
; ... and the new root opens on the source's state (pgs-fork-denotes' view).
(assert-event (let ((d (pgs-rt *pgs-rt-fork* :lhs)))
                (and (equal (car (pgs-open d :br :lazy)) :ok)
                     (equal (pgs-view (pgs-open d :br :lazy)) (pgs-view (pgs-open (pgs-rt *pgs-rt-fork* :d) :main :lazy))))))

; K: the slot the open did not land on (slot 1, empty).
(assert-event (let ((s (pgs-rt-scene '((:fork-k . 1)))))
                (and (pgs-rt-all-but :k (pgs-rt-fork-hyps s 1))
                     (not (pgs-rt-fork-concl s)))))
(pgs-rt-fork-weakened pgs-rt-false-fork-without-k :k)

; The open: R does not open (a wrong directory digest); K is what the open
; answers in that place, the executable refuses and the model forks nothing.
(make-event (let ((k (second (pgs-open (pgs-rt (pgs-rt-scene '((:bad-ddig . t) (:fork-k . 0))) :d) :main :lazy))))
              `(defconst *pgs-rt-fork-open-k* ',k)))
(assert-event (let ((s (pgs-rt-scene (list '(:bad-ddig . t) (cons :fork-k *pgs-rt-fork-open-k*)))))
                (and (pgs-rt-all-but :open (pgs-rt-fork-hyps s *pgs-rt-fork-open-k*))
                     (not (pgs-rt-fork-concl s)))))
(pgs-rt-fork-weakened pgs-rt-false-fork-without-open :open)

; The metadata length (<= 1024 (pgs-m-length pgs-mem)): NOT witnessed.
; The counterexample is a handle whose record is in slot 512 with pgs-m cut
; to 600 words: the executable refuses (:state-unloaded) and leaves slot 1
; holding the record, while the model's fork puts it in slot 0.  Its
; abstraction reads words 600..1023 of the live stobj, which ACL2 refuses
; even with guard checking off ("non-compliant live stobj manipulation"),
; so the ground witness cannot be evaluated here; only the weakened
; statement's failure to prove is recorded (not a counterexample).
(pgs-rt-fork-weakened pgs-rt-false-fork-without-mlen :mlen)

; -----------------------------------------------------------------------------
; The digest observations (A-PGS-OBSERVE): the seam re-attached to a digest
; that disagrees with BLAKE3 on exactly one object the commit hashes.  The
; executable's words are *pgs-rt-base*'s; only the model's view changes.

(defconst *pgs-rt-page0* (pgs-rt-page-words 2048 17))
(defconst *pgs-rt-chunk0* (car (pgs-chunk (pgs-rt *pgs-rt-base* :tab2))))
(defconst *pgs-rt-body* (take 5 (nth 1 (pgs-rt *pgs-rt-base* :res))))
(defconst *pgs-rt-dir2* (pgs-rt *pgs-rt-base* :dir2))

(defmacro pgs-rt-digest-removal (key obj fn name)
  `(progn
     (defun ,fn (x)
       (declare (xargs :guard t))
       (if (equal x ,obj) 1 (pgs-rt-digest x)))
     (defattach pgs-digest ,fn)
     (assert-event (let ((c (pgs-rt-commit-check *pgs-rt-base*)))
                     (and (pgs-rt-all-but ,key (car c)) (not (car (cdr c))))))
     (pgs-rt-plan-weakened ,name ,key)))

; The dirty page's digest (the table entry the model writes differs).
(pgs-rt-digest-removal :dig *pgs-rt-page0* pgs-rt-digest-page pgs-rt-false-plan-without-dig)
; The rewritten table page's digest (the directory entry differs).
(pgs-rt-digest-removal :tdig *pgs-rt-chunk0* pgs-rt-digest-table pgs-rt-false-plan-without-tdig)
; The record's check (the model's record differs).
(pgs-rt-digest-removal :rec *pgs-rt-body* pgs-rt-digest-record pgs-rt-false-plan-without-rec)
; The directory's digest in the record (the model's record differs).
(pgs-rt-digest-removal :ddig *pgs-rt-dir2* pgs-rt-digest-dir pgs-rt-false-plan-without-ddig)

(defattach pgs-digest pgs-rt-digest)
