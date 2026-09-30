(in-package "ACL2")
(include-book "../../books/index-backing-row-carry")

; Current schema witness: an actual typed binding, not a historical held15.
(defconst *ibrct-binding*
  (fn-ab-make :relay-v1
    (append *fn-ab-subject-head* (make-list 32 :initial-element 0))))
(defconst *ibrct-wire*
  (fn-record-make 0 1 0 "<row@test>" nil '("g") "o" "s" "e" 1 0
                  *ibrct-binding*))
(defconst *ibrct-row*
  (fn-held-plain *ibrct-wire* 0))
(assert-event (and (fn-record-p *ibrct-wire*) (fn-held-p *ibrct-row*)
                   (equal (len *ibrct-row*) 16)
                   (fn-ab-p *ibrct-binding*)))

; Literal intern antecedent and conclusion, produced by the actual intern.
(defun-nx ibrct-intern ()
  (let* ((result (mv-list 2 (fn-cat-intern-list *ibrct-wire* nil 0 (create-fn-arena))))
         (row (mv-nth 0 result)) (arena (mv-nth 1 result)))
    (and (fn-record-p *ibrct-wire*) (fn-prin-keyringp nil) (natp 0)
         (fn-ab-p (fn-row-binding *ibrct-wire*))
         (fn-ibrc-row-domainp row (fn-arena-count arena))
         (fn-hnov-p (fn-hf-nov (fn-held-facts row)))
         (equal (fn-record-payload row) 0) (equal (fn-arena-count arena) 1))))
(defthm ibrct-intern-witness (ibrct-intern) :rule-classes nil)

; Intern hypothesis removal: all other wire positions unchanged.
(defun-nx ibrct-intern-no-binding ()
  (let* ((wire (update-nth 11 nil *ibrct-wire*))
         (result (mv-list 2 (fn-cat-intern-list wire nil 0 (create-fn-arena)))))
    (and (not (fn-ab-p (fn-row-binding wire)))
         (not (fn-ibrc-row-domainp (mv-nth 0 result)
                                   (fn-arena-count (mv-nth 1 result)))))))
(defthm ibrct-intern-no-binding-witness (ibrct-intern-no-binding) :rule-classes nil)

; Actual assignment and actual withdrawal preserve the exact current row.
(assert-event
 (and (fn-ibrc-row-domainp *ibrct-row* 1)
      (fn-ibrc-row-domainp (fn-cat-assign *ibrct-row* nil) 1)
      (equal (fn-held-numbers (fn-cat-assign *ibrct-row* nil)) '(("g" . 1)))
      (fn-held-withdrawnp '(2 . 3))
      (fn-ibrc-row-domainp (fn-held-with-withdrawn *ibrct-row* '(2 . 3)) 1)))
; Literal assignment antecedent removal.
(assert-event
 (and (not (fn-ibrc-row-domainp nil 1))
      (not (fn-ibrc-row-domainp (fn-cat-assign nil nil) 1))))
; Literal withdrawal removals, each keeps its other hypothesis.
(assert-event
 (and (fn-ibrc-row-domainp *ibrct-row* 1)
      (not (fn-held-withdrawnp :bad))
      (not (fn-ibrc-row-domainp (fn-held-with-withdrawn *ibrct-row* :bad) 1))))
(assert-event
 (and (not (fn-ibrc-row-domainp nil 1)) (fn-held-withdrawnp '(2 . 3))
      (not (fn-ibrc-row-domainp (fn-held-with-withdrawn nil '(2 . 3)) 1))))

; Actual physical initialize->append->seal->copy->append->seal->read.
; Every carried prefix and the actual caller's physical bounds are checked.
(defun-nx ibrct-page-lifecycle ()
 (let* ((init (mv-list 2 (fn-ibp-row-initialize 7 3 (create-fn-ibp-row-page))))
        (page0 (mv-nth 1 init))
        (page1 (fn-ibp-row-set 0 *ibrct-row* page0))
        (sealed (mv-list 2 (fn-ibp-row-seal 7 3 page1)))
        (source (mv-nth 1 sealed))
        (dest-init (mv-list 2 (fn-ibp-row-initialize 8 3 (create-fn-ibp-row-page2))))
        (dest0 (mv-nth 1 dest-init))
        (dest1 (fn-ibp-row-copy-span 0 1 source dest0))
        (assigned (fn-cat-assign *ibrct-row* (list *ibrct-row*)))
        (dest2 (fn-ibp-row-set 1 assigned dest1))
        (dest-seal (mv-list 2 (fn-ibp-row-seal 8 3 dest2)))
        (dest (mv-nth 1 dest-seal)))
   (and (equal (mv-nth 0 init) :initialized)
        (fn-ibp-row-pagep page0) (equal (fn-ibp-row-sealed page0) 0)
        (fn-ibrc-prefixp (nth 0 page0) 0 1) (fn-ibrc-row-domainp *ibrct-row* 1)
        (fn-ibrc-prefixp (nth 0 page1) 1 1)
        (equal (mv-nth 0 sealed) :sealed)
        (fn-ibrc-prefixp (nth 0 source) 1 1)
        (equal (mv-nth 0 dest-init) :initialized)
        (natp 0) (natp 1) (<= 1 32) (<= (+ 0 1) 256)
        (equal (fn-ibp-row-sealed dest0) 0)
        (fn-ibrc-prefixp (nth 0 dest0) 0 1)
        (fn-ibrc-prefixp (nth 0 dest1) 1 1)
        (fn-ibrc-row-domainp assigned 1)
        (fn-ibrc-prefixp (nth 0 dest2) 2 1)
        (equal (mv-nth 0 dest-seal) :sealed)
        (fn-ibrc-prefixp (nth 0 dest) 2 1)
        (< (nfix 1) (nfix 2))
        (fn-ibrc-row-domainp (fn-ibp-row 1 dest) 1)
        (equal (fn-ibp-row 0 dest) *ibrct-row*)
        (equal (fn-ibp-row 1 dest) assigned))))
(defthm ibrct-page-lifecycle-witness (ibrct-page-lifecycle) :rule-classes nil)

; CORRUPTED-STATE: real header/seal accepts an unrestricted malformed row.
; This exposes why neither stamp nor filled cursor can establish the carry.
(defun-nx ibrct-sealed-bad-row ()
 (let* ((init (mv-list 2 (fn-ibp-row-initialize 7 3 (create-fn-ibp-row-page))))
        (bad (update-nth 4 99 *ibrct-row*))
        (page (fn-ibp-row-set 0 bad (mv-nth 1 init)))
        (sealed (mv-list 2 (fn-ibp-row-seal 7 3 page))))
   (and (fn-ibp-row-pagep page) (equal (fn-ibp-row-sealed page) 0)
        (equal (mv-nth 0 sealed) :sealed)
        (equal (fn-ibp-row-id (mv-nth 1 sealed)) 7)
        (equal (fn-ibp-row-incarnation (mv-nth 1 sealed)) 3)
        (equal (fn-ibp-row-sealed (mv-nth 1 sealed)) 1)
        (not (fn-ibrc-prefixp (nth 0 page) 1 1))
        (not (fn-ibrc-prefixp (nth 0 (mv-nth 1 sealed)) 1 1))
        (not (fn-ibrc-row-domainp (fn-ibp-row 0 (mv-nth 1 sealed)) 1)))))
(defthm ibrct-sealed-bad-row-witness (ibrct-sealed-bad-row) :rule-classes nil)

; Physical-read literal removals: missing carry, then out-of-prefix slot.
(assert-event
 (and (< (nfix 0) (nfix 1))
      (not (fn-ibrc-prefixp '(nil) 1 1))
      (not (fn-ibrc-row-domainp (nth 0 '(nil)) 1))))
(assert-event
 (and (fn-ibrc-prefixp (list *ibrct-row* nil) 1 1)
      (not (< (nfix 1) (nfix 1)))
      (not (fn-ibrc-row-domainp (nth 1 (list *ibrct-row* nil)) 1))))

; Independent field mutations: held15, withdrawal, NOV, binding and bound.
; None is licensed by a page's sealed header or by a catalog count.
(assert-event
 (and (fn-ibrc-row-domainp *ibrct-row* 1)
      (not (fn-ibrc-row-domainp (take 15 *ibrct-row*) 1))
      (not (fn-ibrc-row-domainp (update-nth 14 :bad *ibrct-row*) 1))
      (not (fn-ibrc-row-domainp
        (update-nth 11 (fn-hf-make 0 nil 0 '(nil nil nil :bad)) *ibrct-row*) 1))
      (not (fn-ibrc-row-domainp (update-nth 15 nil *ibrct-row*) 1))
      (not (fn-ibrc-row-domainp *ibrct-row* 0))))

; Actual buffer intern is the served producer; its binding hypothesis is
; checked independently of the list-intern witness.
(defun-nx ibrct-buffer-intern ()
 (let* ((result (mv-list 2 (fn-cat-intern *ibrct-wire* (create-fn-octets)
                              nil 0 (create-fn-arena))))
        (bad (mv-list 2 (fn-cat-intern (update-nth 11 nil *ibrct-wire*)
                           (create-fn-octets) nil 0 (create-fn-arena)))))
   (and (fn-ab-p (fn-row-binding *ibrct-wire*))
        (fn-ibrc-row-domainp (nth 0 result) (fn-arena-count (nth 1 result)))
        (not (fn-ab-p (fn-row-binding (update-nth 11 nil *ibrct-wire*))))
        (not (fn-ibrc-row-domainp (nth 0 bad) (fn-arena-count (nth 1 bad)))))))
(defthm ibrct-buffer-intern-witness (ibrct-buffer-intern) :rule-classes nil)

; Literal ROW-SET prefix removals. Both writes satisfy physical guards;
; the producer domain, rather than the setter, excludes the corrupt input.
(defun-nx ibrct-append-removals ()
 (let* ((page (create-fn-ibp-row-page))
        (prior-bad (fn-ibp-row-set 1 *ibrct-row* page))
        (new-bad (fn-ibp-row-set 0 nil page)))
   (and (fn-ibrc-row-domainp *ibrct-row* 1)
        (not (fn-ibrc-prefixp (nth 0 page) 1 1))
        (not (fn-ibrc-prefixp (nth 0 prior-bad) 2 1))
        (fn-ibrc-prefixp (nth 0 page) 0 1)
        (not (fn-ibrc-row-domainp nil 1))
        (not (fn-ibrc-prefixp (nth 0 new-bad) 1 1)))))
(defthm ibrct-append-removals-witness (ibrct-append-removals) :rule-classes nil)

; Literal normalized-copy removals, affirming the other prefix hypothesis.
(defun-nx ibrct-copy-removals ()
 (let* ((empty (create-fn-ibp-row-page))
        (dest (create-fn-ibp-row-page2))
        (good (fn-ibp-row-set 1 *ibrct-row* (fn-ibp-row-set 0 *ibrct-row* empty)))
        (bad-source (fn-ibp-row-copy-span (nfix 0) (nfix 1) empty dest))
        (bad-dest (fn-ibp-row-copy-span (nfix 1) (nfix 1) good dest)))
   (and (not (fn-ibrc-prefixp (nth 0 empty) (+ (nfix 0) (nfix 1)) 1))
        (fn-ibrc-prefixp (nth 0 dest) (nfix 0) 1)
        (not (fn-ibrc-prefixp (nth 0 bad-source) (+ (nfix 0) (nfix 1)) 1))
        (fn-ibrc-prefixp (nth 0 good) (+ (nfix 1) (nfix 1)) 1)
        (not (fn-ibrc-prefixp (nth 0 dest) (nfix 1) 1))
        (not (fn-ibrc-prefixp (nth 0 bad-dest) (+ (nfix 1) (nfix 1)) 1)))))
(defthm ibrct-copy-removals-witness (ibrct-copy-removals) :rule-classes nil)

; Literal actual selector removals. This is distinct from pure NTH teeth.
(defun-nx ibrct-physical-read-removals ()
 (let* ((empty (create-fn-ibp-row-page))
        (good (fn-ibp-row-set 0 *ibrct-row* empty)))
  (and (not (fn-ibrc-prefixp (nth 0 empty) 1 1))
       (< (nfix 0) (nfix 1))
       (not (fn-ibrc-row-domainp (fn-ibp-row 0 empty) 1))
       (fn-ibrc-prefixp (nth 0 good) 1 1)
       (not (< (nfix 1) (nfix 1)))
       (not (fn-ibrc-row-domainp (fn-ibp-row 1 good) 1)))))
(defthm ibrct-physical-read-removals-witness
 (ibrct-physical-read-removals) :rule-classes nil)

; Repeated actual bounded steps over one genuine modern pending held row.
; The iteration count is a fixture budget, never a production data ceiling.
(defun ibrct-assign-steps (fuel cursor)
 (declare (xargs :guard (and (natp fuel) (fn-gns-assign-cursorp cursor))
                 :measure (nfix fuel)
                 :guard-hints (("Goal"
                   :use ((:instance fn-gns-assign-step-cursorp (c cursor)))
                   :in-theory (disable fn-gns-assign-step fn-gns-assign-cursorp)))))
 (if (zp fuel) cursor
   (ibrct-assign-steps (- fuel 1) (fn-gns-assign-step cursor))))
(defconst *ibrct-pending* (fn-pc-make '(1 . 0) 0 *ibrct-row* nil nil))
(defconst *ibrct-begin* (fn-gns-pending-begin *ibrct-pending* nil 9))
(defconst *ibrct-done* (ibrct-assign-steps 64 *ibrct-begin*))
(assert-event
 (and (fn-pc-p *ibrct-pending*)
      (fn-ibrc-row-domainp (fn-pc-held *ibrct-pending*) 1)
      (fn-ibrc-assignment-carryp *ibrct-begin* 1)
      (fn-ibrc-assignment-carryp (fn-gns-assign-step *ibrct-begin*) 1)
      (equal (fn-gns-at 0 *ibrct-done*) :done)
      (fn-ibrc-row-domainp (fn-gns-at 7 *ibrct-done*) 1)
      (fn-ibrc-row-domainp (fn-gns-at 5 (fn-gns-pending-result *ibrct-done*)) 1)
      (equal (fn-held-numbers (fn-gns-at 5 (fn-gns-pending-result *ibrct-done*)))
             '(("g" . 1)))
      (equal (fn-held-binding (fn-gns-at 5 (fn-gns-pending-result *ibrct-done*)))
             *ibrct-binding*)))
; Begin/step literal antecedent removals, retained original source unavailable.
(assert-event
 (let* ((pending (fn-pc-make '(1 . 0) 0 nil nil nil))
        (begin (fn-gns-pending-begin pending nil 9)))
  (and (not (fn-ibrc-row-domainp (fn-pc-held pending) 1))
       (not (fn-ibrc-assignment-carryp begin 1))
       (not (fn-ibrc-assignment-carryp (fn-gns-assign-step begin) 1)))))
; Actual assigned-row theorem: independently remove completion and row carry.
(assert-event
 (and (fn-ibrc-row-domainp (fn-gns-at 7 *ibrct-begin*) 1)
      (not (equal (fn-gns-at 0 *ibrct-begin*) :done))
      (not (fn-ibrc-row-domainp
             (fn-gns-at 5 (fn-gns-pending-result *ibrct-begin*)) 1))))
(assert-event
 (let ((bad (update-nth 7 nil *ibrct-done*)))
  (and (equal (fn-gns-at 0 bad) :done)
       (not (fn-ibrc-row-domainp (fn-gns-at 7 bad) 1))
       (not (fn-ibrc-row-domainp (fn-gns-at 5 (fn-gns-pending-result bad)) 1)))))
(assert-event
 (and (eq (symbol-class 'fn-ibrc-row-domainp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ibrc-prefixp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ibrc-assignment-carryp (w state)) :common-lisp-compliant)))

; Reachable complete producer chain: the held pointer comes from actual
; intern, passes the actual pending assignment steps/result, and is the
; SAME reference written, sealed and selected. PREFIX is this actual arena.
(defun-nx ibrct-intern-to-selected-page ()
 (let* ((intern (mv-list 2 (fn-cat-intern-list *ibrct-wire* nil 0 (create-fn-arena))))
        (held (nth 0 intern)) (arena (nth 1 intern))
        (prefix (fn-arena-count arena))
        (pending (fn-pc-make '(1 . 0) 0 held nil nil))
        (begin (fn-gns-pending-begin pending nil 9))
        (done (ibrct-assign-steps 64 begin))
        (assigned (fn-gns-at 5 (fn-gns-pending-result done)))
        (init (mv-list 2 (fn-ibp-row-initialize 7 3 (create-fn-ibp-row-page))))
        (page0 (nth 1 init))
        (page1 (fn-ibp-row-set 0 assigned page0))
        (seal (mv-list 2 (fn-ibp-row-seal 7 3 page1)))
        (selected (fn-ibp-row 0 (nth 1 seal))))
  (and (fn-ab-p (fn-row-binding *ibrct-wire*))
       (fn-ibrc-row-domainp held prefix)
       (fn-ibrc-assignment-carryp begin prefix)
       (fn-ibrc-assignment-carryp done prefix)
       (equal (fn-gns-at 0 done) :done)
       (fn-ibrc-row-domainp (fn-gns-at 7 done) prefix)
       (fn-ibrc-row-domainp assigned prefix)
       (fn-ibrc-prefixp (nth 0 page0) 0 prefix)
       (fn-ibrc-prefixp (nth 0 page1) 1 prefix)
       (equal (nth 0 seal) :sealed)
       (fn-ibrc-prefixp (nth 0 (nth 1 seal)) 1 prefix)
       (< (nfix 0) (nfix 1))
       (fn-ibrc-row-domainp selected prefix)
       (equal selected assigned)
       (fn-held-withdrawnp (fn-held-withdrawn selected))
       (natp (fn-record-payload selected))
       (< (fn-record-payload selected) (fn-arena-count arena))
       (fn-hnov-p (fn-hf-nov (fn-held-facts selected)))
       (fn-ab-p (fn-held-binding selected)))))
(defthm ibrct-intern-to-selected-page-witness
 (ibrct-intern-to-selected-page) :rule-classes nil)
