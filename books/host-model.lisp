; HM02 proof continuation. Executable machine is in the separately
; certifiable host-model-machine book; current proof targets remain owed.
(in-package "ACL2")
(include-book "host-model-machine")

; =============================================================================
; THE THEOREMS.

; The accessors over a made state.
(defthm fn-hmc-fields-of-make
  (let ((st (fn-hmc-make locks fds reqs arpn owners pass readers rows workers next results
                         leases released closed ended holds)))
    (and (equal (fn-hmc-locks st) locks) (equal (fn-hmc-fds st) fds)
         (equal (fn-hmc-reqs st) reqs) (equal (fn-hmc-arpn st) arpn)
         (equal (fn-hmc-owners st) owners) (equal (fn-hmc-pass st) pass)
         (equal (fn-hmc-readers st) readers) (equal (fn-hmc-rows st) rows)
         (equal (fn-hmc-workers st) workers) (equal (fn-hmc-next st) next)
         (equal (fn-hmc-results st) results) (equal (fn-hmc-leases st) leases)
         (equal (fn-hmc-released st) released) (equal (fn-hmc-closed st) closed)
         (equal (fn-hmc-ended st) ended) (equal (fn-hmc-holds st) holds)
         (true-listp st) (equal (len st) 16))))

; The accessors over a set field: the field set, every other one kept.
(defthm fn-hmc-field-of-set
  (implies (and (natp i) (natp j) (true-listp st) (equal (len st) 16) (< i 16) (< j 16))
           (equal (fn-hmc-field j (fn-hmc-set i v st))
                  (if (equal i j) v (fn-hmc-field j st)))))

(defthm fn-hmc-set-keeps-shape
  (implies (and (natp i) (< i 16) (true-listp st) (equal (len st) 16))
           (and (true-listp (fn-hmc-set i v st))
                (equal (len (fn-hmc-set i v st)) 16))))

(in-theory (disable fn-hmc-field fn-hmc-set fn-hmc-make))

; The row, worker and request accessors stay closed in every proof below
; (a goal keeps fn-hmc-row-id, never its car); these bridges are :use-only.
(defthm fn-hmc-row-accessors-are-nths
  (implies (true-listp r)
           (and (equal (fn-hmc-row-id r) (nth 0 r))
                (equal (fn-hmc-row-file r) (nth 2 r))
                (equal (fn-hmc-row-phase r) (nth 6 r))
                (equal (fn-hmc-row-settledp r) (eq (nth 6 r) :settled))))
  :rule-classes nil)

(defthm fn-hmc-worker-accessors-are-nths
  (implies (true-listp w)
           (and (equal (fn-hmc-worker-slot w) (nth 0 w))
                (equal (fn-hmc-worker-phase w) (nth 2 w))
                (equal (fn-hmc-worker-token w) (nth 3 w))))
  :rule-classes nil)

(in-theory (disable fn-hmc-row-id fn-hmc-row-file fn-hmc-row-phase fn-hmc-row-settledp
                    fn-hmc-worker-slot fn-hmc-worker-phase fn-hmc-worker-token
                    fn-hmc-req-key fn-hmc-req-fd fn-hmc-req-inc))

(defthm fn-hmc-req-accessors-of-make
  (and (equal (fn-hmc-req-key (list key fd inc)) key)
       (equal (fn-hmc-req-fd (list key fd inc)) fd)
       (equal (fn-hmc-req-inc (list key fd inc)) inc))
  :hints (("Goal" :in-theory (enable fn-hmc-req-key fn-hmc-req-fd fn-hmc-req-inc))))

; The initial state satisfies the invariant (by evaluation).
(defthm fn-hmc-init-invp
  (fn-hmc-invp (fn-hmc-init)))

; -----------------------------------------------------------------------------
; Preservation, one lemma per label.  Each opens the step and the invariant
; and leans on the component books' keystones.

(local (in-theory (disable fn-arpn-step fn-arpn-okp fn-rpin-step fn-pio-direct-admit
                           fn-pio-direct-settle fn-pio-cancel fn-pxe-return
                           fn-pio-file-clear-p fn-pio-rowp fn-pxe-rowp fn-pio-token
                           fn-arpn-pins-of fn-arpn-count fn-arpn-held-p fn-rpin-count-at)))

; ---- the primitives

(defthm fn-hmc-do-acquire-keeps-invp
  (implies (and (fn-hmc-invp st) (not (fn-hmc-ended st)))
           (fn-hmc-invp (mv-nth 0 (fn-hmc-do-acquire st ev)))))

(local
 (defthm fn-hmc-alistp-of-remove1-assoc-equal
   (implies (alistp l) (alistp (remove1-assoc-equal k l)))))

(defthm fn-hmc-do-release-keeps-invp
  (implies (and (fn-hmc-invp st) (not (fn-hmc-ended st)))
           (fn-hmc-invp (mv-nth 0 (fn-hmc-do-release st ev)))))

; An fd bound to a fresh number and an unbound, unclosed incarnation keeps
; every binding, every row open and every request consistent.
(local
 (defthm fn-hmc-boundp-of-cons
   (equal (fn-hmc-boundp inc (cons (cons fd inc2) fds))
          (or (equal inc inc2) (fn-hmc-boundp inc fds)))))

(local
 (defthm fn-hmc-rows-open-p-of-fd-cons
   (implies (fn-hmc-rows-open-p rows fds closed)
            (fn-hmc-rows-open-p rows (cons (cons fd inc) fds) closed))))

(local
 (defthm fn-hmc-leases-open-p-of-fd-cons
   (implies (fn-hmc-leases-open-p leases fds closed)
            (fn-hmc-leases-open-p leases (cons (cons fd inc) fds) closed))))

(local
 (defthm fn-hmc-memberp-is-member-equal
   (implies (true-listp l)
            (equal (fn-hmc-memberp x l) (and (member-equal x l) t)))))

(local
 (defthm fn-hmc-not-assoc-not-in-strip-cars
   (implies (and (alistp fds) (not (assoc-equal fd fds)))
            (not (member-equal fd (strip-cars fds))))))

(local
 (defthm fn-hmc-fd-inc-of-cons-other
   (implies (and (alistp fds) (not (assoc-equal fd fds)))
            (equal (fn-hmc-fd-inc fd2 (cons (cons fd inc) fds))
                   (if (equal fd2 fd) inc (fn-hmc-fd-inc fd2 fds))))))

(local
 (defthm fn-hmc-reqs-okp-fd-bound
   (implies (and (fn-hmc-reqs-okp reqs fds rows leases) (member-equal q reqs))
            (equal (fn-hmc-fd-inc (fn-hmc-req-fd q) fds) (fn-hmc-req-inc q)))))

(local
 (defthm fn-hmc-reqs-okp-of-fd-cons
   (implies (and (fn-hmc-reqs-okp reqs fds rows leases)
                 (alistp fds) (not (assoc-equal fd fds)))
            (fn-hmc-reqs-okp reqs (cons (cons fd inc) fds) rows leases))
   :hints (("Goal" :induct (fn-hmc-reqs-okp reqs fds rows leases)))))

(defthm fn-hmc-do-fd-open-keeps-invp
  (implies (and (fn-hmc-invp st) (not (fn-hmc-ended st)))
           (fn-hmc-invp (mv-nth 0 (fn-hmc-do-fd-open st ev)))))

; A request begun on a key that resolves to a bound incarnation is consistent.
(local
 (defthm fn-hmc-fd-of-inc-in-strip-cars
   (implies (fn-hmc-fd-of-inc inc fds)
            (member-equal (fn-hmc-fd-of-inc inc fds) (strip-cars fds)))))

(local
 (defthm fn-hmc-assoc-of-a-key-not-in-front
   (implies (and (alistp fds) (consp fds) (not (equal fd (caar fds))))
            (equal (assoc-equal fd fds) (assoc-equal fd (cdr fds))))))

(local
 (defthm fn-hmc-found-fd-is-not-an-absent-key
   (implies (and (alistp l) (not (assoc-equal k l)) k)
            (not (equal (fn-hmc-fd-of-inc inc l) k)))
   :hints (("Goal" :cases ((fn-hmc-fd-of-inc inc l))
            :use ((:instance fn-hmc-fd-of-inc-in-strip-cars (fds l))
                  (:instance fn-hmc-not-assoc-not-in-strip-cars (fds l) (fd k)))))))

(local
 (defthm fn-hmc-fd-inc-of-fd-of-inc
   (implies (and (alistp fds) (no-duplicatesp-equal (strip-cars fds))
                 (fn-hmc-fd-of-inc inc fds))
            (equal (fn-hmc-fd-inc (fn-hmc-fd-of-inc inc fds) fds) inc))
   :hints (("Goal" :induct (fn-hmc-fd-of-inc inc fds)
            :in-theory (enable fn-hmc-fd-inc)))))

(local
 (defthm fn-hmc-results-landed-p-of-reqs-cons
   (implies (and (fn-hmc-results-landed-p results reqs)
                 (not (assoc-equal key results)))
            (fn-hmc-results-landed-p results (cons (list key fd inc) reqs)))))

(local
 (defthm fn-hmc-req-of-is-assoc-like
   (implies (and (alistp results) (fn-hmc-results-landed-p results reqs)
                 (assoc-equal key results))
            (not (fn-hmc-req-of key reqs)))))

(defthm fn-hmc-do-io-begin-keeps-invp
  (implies (and (fn-hmc-invp st) (not (fn-hmc-ended st)))
           (fn-hmc-invp (mv-nth 0 (fn-hmc-do-io-begin st ev)))))

; A completion removes a request and lands its verdict.
(local
 (defthm fn-hmc-reqs-okp-of-remove
   (implies (fn-hmc-reqs-okp reqs fds rows leases)
            (fn-hmc-reqs-okp (fn-hmc-reqs-remove key reqs) fds rows leases))))

(local
 (defthm fn-hmc-req-of-after-remove
   (equal (fn-hmc-req-of key (fn-hmc-reqs-remove key2 reqs))
          (if (equal key key2) nil (fn-hmc-req-of key reqs)))))

(local
 (defthm fn-hmc-results-landed-p-of-reqs-remove
   (implies (fn-hmc-results-landed-p results reqs)
            (fn-hmc-results-landed-p results (fn-hmc-reqs-remove key reqs)))))

(defthm fn-hmc-do-io-complete-keeps-invp
  (implies (and (fn-hmc-invp st) (not (fn-hmc-ended st)))
           (fn-hmc-invp (mv-nth 0 (fn-hmc-do-io-complete st ev)))))

(defthm fn-hmc-do-job-result-keeps-invp
  (implies (fn-hmc-invp st)
           (fn-hmc-invp (mv-nth 0 (fn-hmc-do-job-result st ev)))))

(defthm fn-hmc-do-crash-keeps-invp
  (implies (and (fn-hmc-invp st) (not (fn-hmc-ended st)))
           (fn-hmc-invp (mv-nth 0 (fn-hmc-do-crash st)))))

; ---- the leases

(local
 (defthm fn-hmc-leases-open-p-of-cons
   (implies (and (fn-hmc-leases-open-p leases fds closed)
                 (member-eq kind '(:window :discovery))
                 (fn-hmc-boundp inc fds) (not (fn-hmc-memberp inc closed)))
            (fn-hmc-leases-open-p (cons (cons kind inc) leases) fds closed))))

(local
 (defthm fn-hmc-lease-names-p-of-cons
   (equal (fn-hmc-lease-names-p inc (cons (cons kind inc2) leases))
          (or (equal inc inc2) (fn-hmc-lease-names-p inc leases)))))

(local
 (defthm fn-hmc-key-inc-of-lease-cons
   (implies (fn-hmc-key-inc key rows leases)
            (equal (fn-hmc-key-inc key rows (cons (cons kind inc) leases))
                   (fn-hmc-key-inc key rows leases)))))

(local
 (defthm fn-hmc-reqs-okp-of-lease-cons
   (implies (fn-hmc-reqs-okp reqs fds rows leases)
            (fn-hmc-reqs-okp reqs fds rows (cons (cons kind inc) leases)))))

(defthm fn-hmc-do-lease-acquire-keeps-invp
  (implies (and (fn-hmc-invp st) (not (fn-hmc-ended st)) (member-eq kind '(:window :discovery)))
           (fn-hmc-invp (mv-nth 0 (fn-hmc-do-lease-acquire st ev kind)))))

(local
 (defthm fn-hmc-leases-open-p-of-remove1
   (implies (fn-hmc-leases-open-p leases fds closed)
            (fn-hmc-leases-open-p (fn-hmc-remove1 x leases) fds closed))))

; Removing one lease keeps every request consistent: a request on a lease
; key of that incarnation is refused by the release itself; a request on a
; row key does not read the leases.
(local
 (defthm fn-hmc-memberp-of-remove1-other
   (implies (and (fn-hmc-memberp y leases) (not (equal y x)))
            (fn-hmc-memberp y (fn-hmc-remove1 x leases)))))

; A request whose key is not the released lease keeps its incarnation.
(local
 (defthm fn-hmc-key-inc-of-lease-remove1
   (implies (and (fn-hmc-key-inc key rows leases)
                 (not (equal key (list (car x) (cdr x)))))
            (equal (fn-hmc-key-inc key rows (fn-hmc-remove1 x leases))
                   (fn-hmc-key-inc key rows leases)))))

(local
 (defthm fn-hmc-reqs-okp-of-lease-remove1
   (implies (and (fn-hmc-reqs-okp reqs fds rows leases)
                 (not (fn-hmc-req-of (list (car x) (cdr x)) reqs)))
            (fn-hmc-reqs-okp reqs fds rows (fn-hmc-remove1 x leases)))
   :hints (("Goal" :induct (fn-hmc-reqs-okp reqs fds rows leases)))))

(defthm fn-hmc-do-lease-release-keeps-invp
  (implies (and (fn-hmc-invp st) (not (fn-hmc-ended st)) (member-eq kind '(:window :discovery)))
           (fn-hmc-invp (mv-nth 0 (fn-hmc-do-lease-release st ev kind)))))

; ---- the generation table: retire, release, swap change no pin

; In a proof (mv-nth 0 x) is (car x) and (mv-nth 1 x) is (cadr x): the
; component books' keystones are restated in that form.
(local
 (defthm fn-hmc-arpn-okp-of-car-step
   (implies (fn-arpn-okp st)
            (fn-arpn-okp (car (fn-arpn-step st ev))))
   :hints (("Goal" :use fn-arpn-step-preserves-okp :in-theory (enable mv-nth)))))

(local
 (defthm fn-hmc-arpn-retire-keeps-pins
   (implies (fn-arpn-okp st)
            (equal (cadr (car (fn-arpn-step st (list :retire items))))
                   (cadr st)))
   :hints (("Goal" :in-theory (enable fn-arpn-step fn-arpn-okp)))))

(local
 (defthm fn-hmc-arpn-release-keeps-pins
   (implies (fn-arpn-okp st)
            (equal (cadr (car (fn-arpn-step st '(:release))))
                   (cadr st)))
   :hints (("Goal" :in-theory (enable fn-arpn-step fn-arpn-okp)))))

(local
 (defthm fn-hmc-arpn-okp-pinsp
   (implies (fn-arpn-okp st) (fn-arpn-pinsp (cadr st)))
   :hints (("Goal" :in-theory (enable fn-arpn-okp)))))

(defthm fn-hmc-do-retire-keeps-invp
  (implies (and (fn-hmc-invp st) (not (fn-hmc-ended st)))
           (fn-hmc-invp (mv-nth 0 (fn-hmc-do-retire st ev)))))

(local
 (defthm fn-hmc-items-of-true-listp
   (true-listp (fn-hmc-items-of rel))))

(defthm fn-hmc-do-release-retired-keeps-invp
  (implies (and (fn-hmc-invp st) (not (fn-hmc-ended st)))
           (fn-hmc-invp (mv-nth 0 (fn-hmc-do-release-retired st ev)))))

(defthm fn-hmc-do-swap-keeps-invp
  (implies (and (fn-hmc-invp st) (not (fn-hmc-ended st)))
           (fn-hmc-invp (mv-nth 0 (fn-hmc-do-swap st ev)))))

; ---- the rows: helpers over rows-put (rows keyed by id)

(local
 (defthm fn-hmc-row-ids-of-rows-remove
   (equal (fn-hmc-row-ids (fn-hmc-rows-remove id rows))
          (remove-equal id (fn-hmc-row-ids rows)))))

(local
 (defthm fn-hmc-member-of-remove-equal-early
   (implies (member-equal x (remove-equal y l)) (member-equal x l))))

(local
 (defthm fn-hmc-no-dup-of-remove-equal
   (implies (no-duplicatesp-equal l)
            (no-duplicatesp-equal (remove-equal x l)))))

(local
 (defthm fn-hmc-not-member-of-remove-equal
   (not (member-equal x (remove-equal x l)))))

(local
 (defthm fn-hmc-no-dup-row-ids-of-rows-put
   (implies (no-duplicatesp-equal (fn-hmc-row-ids rows))
            (no-duplicatesp-equal (fn-hmc-row-ids (fn-hmc-rows-put row rows))))))

(local
 (defthm fn-hmc-rowsp-of-rows-remove
   (implies (fn-hmc-rowsp rows) (fn-hmc-rowsp (fn-hmc-rows-remove id rows)))))

(local
 (defthm fn-hmc-rowsp-of-rows-put
   (implies (and (fn-hmc-rowsp rows) (fn-pio-rowp row))
            (fn-hmc-rowsp (fn-hmc-rows-put row rows)))))

(local
 (defthm fn-hmc-rowsp-member
   (implies (and (fn-hmc-rowsp rows) (member-equal r rows))
            (fn-pio-rowp r))))

(local
 (defthm fn-hmc-pio-rowp-true-listp
   (implies (fn-pio-rowp r) (and (true-listp r) (equal (len r) 7)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-pio-rowp)))))

(local
 (defthm fn-hmc-pxe-rowp-true-listp
   (implies (fn-pxe-rowp w) (and (true-listp w) (equal (len w) 4)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-pxe-rowp)))))

(local
 (defthm fn-hmc-row-of-is-a-member
   (implies (fn-hmc-row-of key rows)
            (member-equal (fn-hmc-row-of key rows) rows))))

(local
 (defthm fn-hmc-row-of-has-the-token
   (implies (fn-hmc-row-of key rows)
            (equal (fn-pio-token (fn-hmc-row-of key rows)) key))))

(local
 (defthm fn-hmc-row-of-is-a-true-list
   (implies (fn-hmc-row-of key rows)
            (true-listp (fn-hmc-row-of key rows)))))

(local
 (defthm fn-hmc-car-of-token
   (implies (true-listp r)
            (equal (car (fn-pio-token r)) (fn-hmc-row-id r)))
   :hints (("Goal" :in-theory (enable fn-pio-token fn-hmc-row-id)))))

(local
 (defthm fn-hmc-member-row-id
   (implies (member-equal r rows)
            (member-equal (fn-hmc-row-id r) (fn-hmc-row-ids rows)))))

(local
 (defthm fn-hmc-rowsp-member-true-listp
   (implies (and (fn-hmc-rowsp rows) (member-equal r rows))
            (true-listp r))))

(local
 (defthm fn-hmc-pio-rowp-shape
   (implies (fn-pio-rowp r)
            (and (consp r) (natp (fn-hmc-row-id r)) (natp (fn-hmc-row-file r))))
   :hints (("Goal" :in-theory (enable fn-pio-rowp fn-hmc-row-id fn-hmc-row-file)))))

(local
 (defthm fn-hmc-rowsp-member-shape
   (implies (and (fn-hmc-rowsp rows) (member-equal r rows))
            (and (consp r) (natp (fn-hmc-row-id r))))))

; Two members of a list of distinct ids with the same id are the same row.
(local
 (defthm fn-hmc-same-id-same-row
   (implies (and (fn-hmc-rowsp rows) (no-duplicatesp-equal (fn-hmc-row-ids rows))
                 (member-equal r1 rows) (member-equal r2 rows)
                 (equal (fn-hmc-row-id r1) (fn-hmc-row-id r2)))
            (equal r1 r2))
   :rule-classes nil
   :hints (("Goal" :induct (fn-hmc-rowsp rows)))))

; ... so two tokens found in the rows with the same id are the same token.
(local
 (defthm fn-hmc-same-id-same-token
   (implies (and (fn-hmc-rowsp rows) (no-duplicatesp-equal (fn-hmc-row-ids rows))
                 (fn-hmc-row-of k1 rows) (fn-hmc-row-of k2 rows)
                 (equal (nth 0 k1) (nth 0 k2)))
            (equal k1 k2))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-hmc-same-id-same-row
                                    (r1 (fn-hmc-row-of k1 rows)) (r2 (fn-hmc-row-of k2 rows)))
                         (:instance fn-hmc-row-of-has-the-token (key k1))
                         (:instance fn-hmc-row-of-has-the-token (key k2))
                         (:instance fn-hmc-car-of-token (r (fn-hmc-row-of k1 rows)))
                         (:instance fn-hmc-car-of-token (r (fn-hmc-row-of k2 rows))))
            :do-not-induct t))))

; A removal by id drops exactly the rows of that id: looking a token up in
; the remainder answers nil for that id and the old row otherwise.
(local
 (defthm fn-hmc-row-of-rows-remove
   (implies (fn-hmc-rowsp rows)
            (equal (fn-hmc-row-of key (fn-hmc-rows-remove id rows))
                   (if (equal (nth 0 key) id) nil (fn-hmc-row-of key rows))))
   :hints (("Goal" :induct (fn-hmc-rows-remove id rows)))))

(local
 (defthm fn-hmc-row-of-rows-put
   (implies (and (fn-hmc-rowsp rows) (true-listp row))
            (equal (fn-hmc-row-of key (fn-hmc-rows-put row rows))
                   (cond ((equal key (fn-pio-token row)) row)
                         ((equal (nth 0 key) (fn-hmc-row-id row)) nil)
                         (t (fn-hmc-row-of key rows)))))))

; With both the looked-up token and the put row present, the put row is
; found only under its own token (the other case needs two rows of one id).
(local
 (defthm fn-hmc-row-of-rows-put-when-present
   (implies (and (fn-hmc-rowsp rows) (no-duplicatesp-equal (fn-hmc-row-ids rows))
                 (fn-pio-rowp row)
                 (fn-hmc-row-of key rows)
                 (fn-hmc-row-of (fn-pio-token row) rows))
            (equal (fn-hmc-row-of key (fn-hmc-rows-put row rows))
                   (if (equal key (fn-pio-token row)) row (fn-hmc-row-of key rows))))
   :hints (("Goal" :use ((:instance fn-hmc-same-id-same-token (k1 key) (k2 (fn-pio-token row))))
            :do-not-induct t))))

; A key no row of ROWS answers (a lease key) is not answered after a put of
; a real row either: the put row's token is a list of naturals.
(local
 (defthm fn-hmc-row-of-rows-put-when-absent
   (implies (and (fn-hmc-rowsp rows) (fn-pio-rowp row)
                 (not (fn-hmc-row-of key rows))
                 (not (natp (nth 0 key))))
            (not (fn-hmc-row-of key (fn-hmc-rows-put row rows))))
   :hints (("Goal" :do-not-induct t))))

(local
 (defthm fn-hmc-rows-open-p-member
   (implies (and (fn-hmc-rows-open-p rows fds closed) (member-equal r rows)
                 (not (fn-hmc-row-settledp r)))
            (and (fn-hmc-boundp (fn-hmc-row-file r) fds)
                 (not (fn-hmc-memberp (fn-hmc-row-file r) closed))))))

(local
 (defthm fn-hmc-rows-open-p-of-rows-remove
   (implies (fn-hmc-rows-open-p rows fds closed)
            (fn-hmc-rows-open-p (fn-hmc-rows-remove id rows) fds closed))))

(local
 (defthm fn-hmc-rows-open-p-of-rows-put
   (implies (and (fn-hmc-rows-open-p rows fds closed)
                 (or (fn-hmc-row-settledp row)
                     (and (fn-hmc-boundp (fn-hmc-row-file row) fds)
                          (not (fn-hmc-memberp (fn-hmc-row-file row) closed)))))
            (fn-hmc-rows-open-p (fn-hmc-rows-put row rows) fds closed))))

(local
 (defthm fn-hmc-rows-below-p-of-rows-remove
   (implies (fn-hmc-rows-below-p rows next)
            (fn-hmc-rows-below-p (fn-hmc-rows-remove id rows) next))))

(local
 (defthm fn-hmc-rows-below-p-of-rows-put
   (implies (and (fn-hmc-rows-below-p rows next) (natp next)
                 (natp (fn-hmc-row-id row)) (< (fn-hmc-row-id row) next))
            (fn-hmc-rows-below-p (fn-hmc-rows-put row rows) next))))

(local
 (defthm fn-hmc-rows-below-p-member
   (implies (and (fn-hmc-rows-below-p rows next) (member-equal r rows))
            (and (natp (fn-hmc-row-id r)) (natp next) (< (fn-hmc-row-id r) next)))))

(local (in-theory (disable fn-hmc-rows-put fn-hmc-rows-remove)))

; fn-pio-cancel keeps the token, the id and the file, and settles nothing.
(local
 (defthm fn-hmc-cancel-keeps-identity
   (and (equal (fn-hmc-row-id (fn-pio-cancel r tok)) (fn-hmc-row-id r))
        (equal (fn-hmc-row-file (fn-pio-cancel r tok)) (fn-hmc-row-file r))
        (equal (fn-hmc-row-settledp (fn-pio-cancel r tok)) (fn-hmc-row-settledp r))
        (implies (true-listp r) (true-listp (fn-pio-cancel r tok)))
        (implies (true-listp r)
                 (equal (fn-pio-token (fn-pio-cancel r tok)) (fn-pio-token r))))
   :hints (("Goal" :in-theory (enable fn-pio-cancel fn-pio-token fn-pio-rowp
                                      fn-hmc-row-id fn-hmc-row-file fn-hmc-row-phase
                                      fn-hmc-row-settledp)))))

; A put of an unsettled row that replaces a row of the same token (the
; cancel) keeps every worker's and every request's row.
(local
 (defthm fn-hmc-workersp-of-rows-put-same-token
   (implies (and (fn-hmc-rowsp rows) (no-duplicatesp-equal (fn-hmc-row-ids rows))
                 (fn-hmc-workersp workers rows)
                 (fn-pio-rowp row) (not (fn-hmc-row-settledp row))
                 (fn-hmc-row-of (fn-pio-token row) rows))
            (fn-hmc-workersp workers (fn-hmc-rows-put row rows)))
   :hints (("Goal" :induct (fn-hmc-workersp workers rows)
            :in-theory (disable fn-hmc-row-of-rows-put)))))

(local
 (defthm fn-hmc-key-inc-of-rows-put-same-token
   (implies (and (fn-hmc-rowsp rows) (no-duplicatesp-equal (fn-hmc-row-ids rows))
                 (fn-pio-rowp row) (not (fn-hmc-row-settledp row))
                 (fn-hmc-row-of (fn-pio-token row) rows)
                 (not (fn-hmc-row-settledp (fn-hmc-row-of (fn-pio-token row) rows)))
                 (equal (fn-hmc-row-file row)
                        (fn-hmc-row-file (fn-hmc-row-of (fn-pio-token row) rows)))
                 (fn-hmc-key-inc key rows leases))
            (equal (fn-hmc-key-inc key (fn-hmc-rows-put row rows) leases)
                   (fn-hmc-key-inc key rows leases)))
   :hints (("Goal" :in-theory (e/d (fn-hmc-key-inc) (fn-hmc-row-of-rows-put))
            :do-not-induct t
            :cases ((fn-hmc-row-of key rows))))))

(local
 (defthm fn-hmc-reqs-okp-of-rows-put-same-token
   (implies (and (fn-hmc-rowsp rows) (no-duplicatesp-equal (fn-hmc-row-ids rows))
                 (fn-hmc-reqs-okp reqs fds rows leases)
                 (fn-pio-rowp row) (not (fn-hmc-row-settledp row))
                 (fn-hmc-row-of (fn-pio-token row) rows)
                 (not (fn-hmc-row-settledp (fn-hmc-row-of (fn-pio-token row) rows)))
                 (equal (fn-hmc-row-file row)
                        (fn-hmc-row-file (fn-hmc-row-of (fn-pio-token row) rows))))
            (fn-hmc-reqs-okp reqs fds (fn-hmc-rows-put row rows) leases))
   :hints (("Goal" :induct (fn-hmc-reqs-okp reqs fds rows leases)
            :in-theory (disable fn-hmc-key-inc fn-hmc-row-of-rows-put)))))

; Actual direct cancellation updates its issued row in place and retains
; the physical hold table. These LOCAL bridges keep that order and prove
; every carried invariant component, instead of assuming rows-put equality.
(local
 (defthm fn-hmc-issued-rows-of-issued
  (implies (fn-hmc-rowsp rows)
           (equal (fn-pio-issued-rows (fn-hmc-issued rows)) rows))
  :hints (("Goal" :induct (fn-hmc-rowsp rows)
           :in-theory (enable fn-hmc-issued fn-pio-issued-rows fn-hmc-rowsp fn-pio-rowp)))))

(local
 (defthm fn-hmc-issued-row-of-issued
  (implies (fn-hmc-rowsp rows)
           (equal (fn-pio-issued-row token (fn-hmc-issued rows))
                  (fn-hmc-row-of token rows)))
  :hints (("Goal" :induct (fn-hmc-rowsp rows)
           :in-theory (enable fn-hmc-issued fn-pio-issued-row fn-hmc-row-of fn-hmc-rowsp fn-pio-rowp)))))

(local
 (defun fn-hmc-cancel-row-view (token rows)
  (declare (xargs :guard t))
  (cond ((atom rows) nil)
        ((and (true-listp (car rows)) (equal token (fn-pio-token (car rows))))
         (cons (fn-pio-cancel (car rows) token) (cdr rows)))
        (t (cons (car rows) (fn-hmc-cancel-row-view token (cdr rows)))))))

(local
 (defthm fn-hmc-direct-cancel-row-view
  (implies (fn-hmc-rowsp rows)
   (equal (fn-pio-issued-rows (fn-pio-direct-cancel token (fn-hmc-issued rows)))
          (fn-hmc-cancel-row-view token rows)))
  :hints (("Goal" :induct (fn-hmc-rowsp rows)
   :in-theory (enable fn-pio-direct-cancel fn-pio-issued-put fn-hmc-cancel-row-view
                      fn-hmc-issued fn-pio-issued-row fn-pio-issued-rows fn-hmc-rowsp fn-pio-rowp)))))

(local
 (defthm fn-hmc-rowsp-of-cancel-row-view
  (implies (fn-hmc-rowsp rows)
   (fn-hmc-rowsp (fn-hmc-cancel-row-view token rows)))
  :hints (("Goal" :induct (fn-hmc-rowsp rows)
           :in-theory (enable fn-hmc-cancel-row-view fn-hmc-rowsp)))))

(local
 (defthm fn-hmc-row-of-cancel-row-view
  (implies (fn-hmc-rowsp rows)
   (equal (fn-hmc-row-of other (fn-hmc-cancel-row-view token rows))
    (if (and (equal other token) (fn-hmc-row-of token rows))
        (fn-pio-cancel (fn-hmc-row-of token rows) token)
      (fn-hmc-row-of other rows))))
  :hints (("Goal" :induct (fn-hmc-cancel-row-view token rows)
           :in-theory (enable fn-hmc-cancel-row-view fn-hmc-row-of fn-hmc-rowsp)))))

(local
 (defthm fn-hmc-row-ids-of-cancel-row-view
  (equal (fn-hmc-row-ids (fn-hmc-cancel-row-view token rows)) (fn-hmc-row-ids rows))
  :hints (("Goal" :induct (fn-hmc-cancel-row-view token rows)
           :in-theory (enable fn-hmc-cancel-row-view fn-hmc-row-ids)))))

(local
 (defthm fn-hmc-rows-below-p-of-cancel-row-view
  (equal (fn-hmc-rows-below-p (fn-hmc-cancel-row-view token rows) next)
         (fn-hmc-rows-below-p rows next))
  :hints (("Goal" :induct (fn-hmc-cancel-row-view token rows)
           :in-theory (enable fn-hmc-cancel-row-view fn-hmc-rows-below-p)))))

(local
 (defthm fn-hmc-rows-open-p-of-cancel-row-view
  (equal (fn-hmc-rows-open-p (fn-hmc-cancel-row-view token rows) fds closed)
         (fn-hmc-rows-open-p rows fds closed))
  :hints (("Goal" :induct (fn-hmc-cancel-row-view token rows)
           :in-theory (enable fn-hmc-cancel-row-view fn-hmc-rows-open-p)))))

(local
 (defthm fn-hmc-workersp-of-cancel-row-view
  (implies (fn-hmc-rowsp rows)
   (equal (fn-hmc-workersp workers (fn-hmc-cancel-row-view token rows))
          (fn-hmc-workersp workers rows)))
  :hints (("Goal" :induct (fn-hmc-workersp workers rows)
           :in-theory (enable fn-hmc-workersp)))))

(local
 (defthm fn-hmc-key-inc-of-cancel-row-view
  (implies (fn-hmc-rowsp rows)
   (equal (fn-hmc-key-inc key (fn-hmc-cancel-row-view token rows) leases)
          (fn-hmc-key-inc key rows leases)))
  :hints (("Goal" :in-theory (enable fn-hmc-key-inc)))))

(local
 (defthm fn-hmc-reqs-okp-of-cancel-row-view
  (implies (fn-hmc-rowsp rows)
   (equal (fn-hmc-reqs-okp reqs fds (fn-hmc-cancel-row-view token rows) leases)
          (fn-hmc-reqs-okp reqs fds rows leases)))
  :hints (("Goal" :induct (fn-hmc-reqs-okp reqs fds rows leases)
           :in-theory (enable fn-hmc-reqs-okp)))))

(local
 (defthm fn-hmc-cancel-nth6-settled
  (implies (true-listp r)
   (equal (equal (nth 6 (fn-pio-cancel r tok)) :settled)
          (equal (nth 6 r) :settled)))
  :hints (("Goal" :use ((:instance fn-hmc-cancel-keeps-identity))
   :in-theory (e/d (fn-hmc-row-settledp fn-hmc-row-phase)
                   (fn-hmc-cancel-keeps-identity))))))

(local
 (defthm fn-hmc-issuedp-of-cancel-row-view
  (implies (and (fn-hmc-rowsp rows) (fn-pio-issuedp (fn-hmc-issued rows)))
   (fn-pio-issuedp (fn-hmc-issued (fn-hmc-cancel-row-view token rows))))
  :hints (("Goal" :induct (fn-hmc-cancel-row-view token rows)
   :in-theory (enable fn-hmc-cancel-row-view fn-hmc-issued fn-pio-issuedp fn-hmc-rowsp)))))

(local
 (defthm fn-hmc-issued-in-holds-p-of-cancel-row-view
   (implies (fn-hmc-rowsp rows)
     (equal (fn-pio-issued-in-holds-p
              (fn-hmc-issued (fn-hmc-cancel-row-view token rows)) holds)
            (fn-pio-issued-in-holds-p (fn-hmc-issued rows) holds)))
   :hints (("Goal" :induct (fn-hmc-cancel-row-view token rows)
            :in-theory (enable fn-hmc-cancel-row-view fn-hmc-issued
                               fn-pio-issued-in-holds-p fn-hmc-rowsp)))))

(local
 (defthm fn-hmc-tokens-in-issued-p-of-cancel-row-view
  (implies (fn-hmc-rowsp rows)
   (equal (fn-pio-tokens-in-issued-p file tokens (fn-hmc-issued (fn-hmc-cancel-row-view token rows)))
          (fn-pio-tokens-in-issued-p file tokens (fn-hmc-issued rows))))
  :hints (("Goal" :induct (len tokens)
   :in-theory (e/d (fn-pio-tokens-in-issued-p)
                   (fn-hmc-issued fn-hmc-cancel-row-view fn-hmc-rowsp fn-hmc-row-of fn-pio-issued-row))))))

(local
 (defthm fn-hmc-holds-in-issued-p-of-cancel-row-view (implies (fn-hmc-rowsp rows) (equal (fn-pio-holds-in-issued-p holds (fn-hmc-issued (fn-hmc-cancel-row-view token rows))) (fn-pio-holds-in-issued-p holds (fn-hmc-issued rows)))) :hints (("Goal" :induct (len holds) :in-theory (e/d (fn-pio-holds-in-issued-p) (fn-hmc-issued fn-hmc-cancel-row-view fn-hmc-rowsp fn-pio-tokens-in-issued-p))))))

(local
 (defthm fn-hmc-direct-okp-of-cancel-row-view (implies (and (fn-hmc-rowsp rows) (fn-pio-direct-okp (fn-hmc-issued rows) holds)) (fn-pio-direct-okp (fn-hmc-issued (fn-hmc-cancel-row-view token rows)) holds)) :hints (("Goal" :in-theory (e/d (fn-pio-direct-okp) (fn-hmc-issued fn-hmc-cancel-row-view fn-hmc-rowsp fn-pio-issuedp fn-pio-issued-in-holds-p fn-pio-holds-in-issued-p))))))

(defthm fn-hmc-do-cancel-keeps-invp (implies (and (fn-hmc-invp st) (not (fn-hmc-ended st))) (fn-hmc-invp (mv-nth 0 (fn-hmc-do-cancel st ev)))) :hints (("Goal" :in-theory (e/d (fn-hmc-do-cancel fn-hmc-invp) (fn-pio-direct-cancel fn-pio-issued-rows fn-hmc-issued fn-hmc-cancel-row-view fn-hmc-rowsp fn-pio-direct-okp fn-hmc-rows-open-p fn-hmc-rows-below-p fn-hmc-workersp fn-hmc-reqs-okp fn-hmc-row-ids)))))

; ---- the generation pins: funding under pin, unpin, capture, drain

; The arena table's events, opened: a pin adds one at the current
; generation; an unpin of a held generation removes one there.
(local
 (defthm fn-hmc-arpn-pin-form
   (implies (fn-arpn-okp st)
            (and (equal (cadr (fn-arpn-step st '(:pin))) (car st))
                 (equal (car (car (fn-arpn-step st '(:pin)))) (car st))
                 (equal (cadr (car (fn-arpn-step st '(:pin))))
                        (fn-arpn-pin-at (car st) (cadr st)))))
   :hints (("Goal" :in-theory (enable fn-arpn-step fn-arpn-okp)))))

(local
 (defthm fn-hmc-arpn-unpin-form
   (implies (and (fn-arpn-okp st) (natp g) (fn-arpn-held-p g (cadr st)))
            (and (equal (cadr (fn-arpn-step st (list :unpin g))) :ok)
                 (equal (car (car (fn-arpn-step st (list :unpin g)))) (car st))
                 (equal (cadr (car (fn-arpn-step st (list :unpin g))))
                        (fn-arpn-unpin-at g (cadr st)))))
   :hints (("Goal" :in-theory (enable fn-arpn-step fn-arpn-okp)))))

; Response holds, opened: a fresh acquire adds (cid . cur) and pins; a
; release of a held response removes it and unpins its generation.
(local
 (defthm fn-hmc-rpin-acquire-form
   (implies (and (fn-arpn-okp st) (natp cid) (not (fn-rpin-owner cid owners)))
            (and (equal (caddr (fn-rpin-step owners st (list :acquire cid))) :acquired)
                 (equal (car (fn-rpin-step owners st (list :acquire cid)))
                        (cons (cons cid (car st)) owners))
                 (equal (cadr (fn-rpin-step owners st (list :acquire cid)))
                        (car (fn-arpn-step st '(:pin))))))
   :hints (("Goal" :in-theory (enable fn-rpin-step)))))

(local
 (defthm fn-hmc-rpin-release-form
   (implies (and (fn-arpn-okp st) (fn-rpin-owner cid owners)
                 (natp (cdr (fn-rpin-owner cid owners)))
                 (fn-arpn-held-p (cdr (fn-rpin-owner cid owners)) (cadr st)))
            (and (equal (caddr (fn-rpin-step owners st (list :release cid))) :released)
                 (equal (car (fn-rpin-step owners st (list :release cid)))
                        (fn-rpin-remove cid owners))
                 (equal (cadr (fn-rpin-step owners st (list :release cid)))
                        (car (fn-arpn-step st (list :unpin (cdr (fn-rpin-owner cid owners))))))))
   :hints (("Goal" :in-theory (enable fn-rpin-step)))))

; The funding predicate pointwise, and its universal consequence: once it
; holds over every generation an owner or a reader names, it holds at every
; generation (the others have no holds).
(defun fn-hmc-funded-g-p (g owners readers pins)
  (declare (xargs :guard (fn-arpn-pinsp pins)))
  (<= (+ (fn-rpin-count-at g owners) (fn-hmc-readers-at g readers))
      (fn-arpn-pins-of g pins)))

(local
 (defthm fn-hmc-funded-at-p-member
   (implies (and (fn-hmc-funded-at-p gs owners readers pins) (member-equal g gs))
            (fn-hmc-funded-g-p g owners readers pins))))

(local
 (defthm fn-hmc-count-at-zero-when-absent
   (implies (not (member-equal g (fn-hmc-cdrs owners)))
            (equal (fn-rpin-count-at g owners) 0))
   :hints (("Goal" :in-theory (enable fn-rpin-count-at)))))

(local
 (defthm fn-hmc-readers-at-zero-when-absent
   (implies (not (member-equal g (fn-hmc-cdrs readers)))
            (equal (fn-hmc-readers-at g readers) 0))))

(local
 (defthm fn-hmc-funded-at-p-of-append
   (equal (fn-hmc-funded-at-p (append a b) owners readers pins)
          (and (fn-hmc-funded-at-p a owners readers pins)
               (fn-hmc-funded-at-p b owners readers pins)))))

(local
 (defthm fn-hmc-member-of-append
   (iff (member-equal g (append a b))
        (or (member-equal g a) (member-equal g b)))))

(local
 (defthm fn-hmc-funded-universal
   (implies (and (fn-arpn-pinsp pins)
                 (fn-hmc-funded-at-p (append (fn-hmc-cdrs owners)
                                            (fn-hmc-cdrs readers))
                                     owners readers pins))
            (fn-hmc-funded-g-p g owners readers pins))
   :hints (("Goal" :cases ((member-equal g (fn-hmc-cdrs owners))
                           (member-equal g (fn-hmc-cdrs readers)))
            :in-theory (e/d (fn-hmc-funded-g-p)
                            (fn-hmc-funded-at-p-of-append
                             fn-hmc-funded-at-p-member fn-hmc-funded-at-p
                             fn-rpin-count-at fn-hmc-readers-at
                             fn-arpn-pins-of fn-hmc-cdrs))
            :use ((:instance fn-hmc-funded-at-p-member
                             (gs (append (fn-hmc-cdrs owners)
                                         (fn-hmc-cdrs readers)))))))))

(defun fn-hmc-nat-listp (xs)
  (declare (xargs :guard t))
  (cond ((atom xs) t)
        (t (and (natp (car xs)) (fn-hmc-nat-listp (cdr xs))))))

(local
 (defthm fn-hmc-funded-at-p-nat-listp
   (implies (fn-hmc-funded-at-p gs owners readers pins)
            (fn-hmc-nat-listp gs))))

(local
 (defthm fn-hmc-nat-listp-of-append
   (equal (fn-hmc-nat-listp (append a b))
          (and (fn-hmc-nat-listp a) (fn-hmc-nat-listp b)))))

; The counts under the four table edits.
(local
 (defthm fn-hmc-readers-at-of-cons
   (equal (fn-hmc-readers-at g (cons (cons tid g2) readers))
          (+ (if (equal g g2) 1 0) (fn-hmc-readers-at g readers)))))

(local
 (defthm fn-hmc-count-at-of-cons
   (equal (fn-rpin-count-at g (cons (cons cid g2) owners))
          (+ (if (equal g g2) 1 0) (fn-rpin-count-at g owners)))
   :hints (("Goal" :in-theory (enable fn-rpin-count-at)))))

(local
 (defthm fn-hmc-readers-at-of-remove1
   (implies (fn-hmc-memberp (cons tid g2) readers)
            (equal (fn-hmc-readers-at g (fn-hmc-remove1 (cons tid g2) readers))
                   (- (fn-hmc-readers-at g readers) (if (equal g g2) 1 0))))))

(local
 (defthm fn-hmc-readers-at-natp
   (natp (fn-hmc-readers-at g readers))
   :rule-classes :type-prescription))

(local
 (defthm fn-hmc-count-at-natp
   (natp (fn-rpin-count-at g owners))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-rpin-count-at)))))

(local
 (defthm fn-hmc-count-at-of-rpin-remove
   (implies (and (alistp owners) (fn-rpin-owner cid owners))
            (equal (fn-rpin-count-at g (fn-rpin-remove cid owners))
                   (- (fn-rpin-count-at g owners)
                      (if (equal g (cdr (fn-rpin-owner cid owners))) 1 0))))
   :hints (("Goal" :in-theory (enable fn-rpin-count-at fn-rpin-remove fn-rpin-owner)))))

(local
 (defthm fn-hmc-owner-counts-at-its-generation
   (implies (and (alistp owners) (fn-rpin-owner cid owners))
            (< 0 (fn-rpin-count-at (cdr (fn-rpin-owner cid owners)) owners)))
   :hints (("Goal" :in-theory (enable fn-rpin-count-at fn-rpin-owner)))))

; A funded table stays funded through each edit, at every generation.
(local
 (defthm fn-hmc-funded-g-p-after-pin
   (implies (and (fn-arpn-pinsp pins) (fn-hmc-funded-g-p g owners readers pins))
            (fn-hmc-funded-g-p g owners (cons (cons tid g2) readers)
                               (fn-arpn-pin-at g2 pins)))))

(local
 (defthm fn-hmc-funded-g-p-after-capture
   (implies (and (fn-arpn-pinsp pins) (fn-hmc-funded-g-p g owners readers pins))
            (fn-hmc-funded-g-p g (cons (cons cid g2) owners) readers
                               (fn-arpn-pin-at g2 pins)))))

(local
 (defthm fn-hmc-funded-g-p-after-unpin
   (implies (and (fn-arpn-pinsp pins) (fn-hmc-funded-g-p g owners readers pins)
                 (fn-hmc-memberp (cons tid g2) readers))
            (fn-hmc-funded-g-p g owners (fn-hmc-remove1 (cons tid g2) readers)
                               (fn-arpn-unpin-at g2 pins)))))

(local
 (defthm fn-hmc-funded-g-p-after-drain
   (implies (and (fn-arpn-pinsp pins) (alistp owners)
                 (fn-hmc-funded-g-p g owners readers pins)
                 (fn-rpin-owner cid owners))
            (fn-hmc-funded-g-p g (fn-rpin-remove cid owners) readers
                               (fn-arpn-unpin-at (cdr (fn-rpin-owner cid owners)) pins)))))

(local
 (defthm fn-hmc-funded-at-p-of-cons
   (equal (fn-hmc-funded-at-p (cons g gs) owners readers pins)
          (and (natp g) (fn-hmc-funded-g-p g owners readers pins)
               (fn-hmc-funded-at-p gs owners readers pins)))
   :hints (("Goal" :in-theory (enable fn-hmc-funded-at-p fn-hmc-funded-g-p)))))

(local
 (defthm fn-hmc-funded-at-p-when-atom
   (implies (not (consp gs)) (fn-hmc-funded-at-p gs owners readers pins))
   :hints (("Goal" :in-theory (enable fn-hmc-funded-at-p)))))

; ... so funded-at-p holds over any list of naturals after the edit, from
; the universal fact before it.
(local
 (defthm fn-hmc-funded-at-p-after-pin
   (implies (and (fn-arpn-pinsp pins) (fn-hmc-nat-listp gs)
                 (fn-hmc-funded-at-p (append (fn-hmc-cdrs owners) (fn-hmc-cdrs readers))
                                     owners readers pins))
            (fn-hmc-funded-at-p gs owners (cons (cons tid g2) readers)
                                (fn-arpn-pin-at g2 pins)))
   :hints (("Goal" :induct (fn-hmc-nat-listp gs)
            :in-theory (disable fn-hmc-funded-g-p fn-hmc-funded-at-p
                                fn-hmc-funded-at-p-of-append fn-arpn-pin-at
                                fn-arpn-unpin-at fn-hmc-cdrs fn-hmc-readers-at
                                fn-rpin-count-at fn-arpn-pins-of)))))

(local
 (defthm fn-hmc-funded-at-p-after-capture
   (implies (and (fn-arpn-pinsp pins) (fn-hmc-nat-listp gs)
                 (fn-hmc-funded-at-p (append (fn-hmc-cdrs owners) (fn-hmc-cdrs readers))
                                     owners readers pins))
            (fn-hmc-funded-at-p gs (cons (cons cid g2) owners) readers
                                (fn-arpn-pin-at g2 pins)))
   :hints (("Goal" :induct (fn-hmc-nat-listp gs)
            :in-theory (disable fn-hmc-funded-g-p fn-hmc-funded-at-p
                                fn-hmc-funded-at-p-of-append fn-arpn-pin-at
                                fn-arpn-unpin-at fn-hmc-cdrs fn-hmc-readers-at
                                fn-rpin-count-at fn-arpn-pins-of)))))

(local
 (defthm fn-hmc-funded-at-p-after-unpin
   (implies (and (fn-arpn-pinsp pins) (fn-hmc-nat-listp gs)
                 (fn-hmc-memberp (cons tid g2) readers)
                 (fn-hmc-funded-at-p (append (fn-hmc-cdrs owners) (fn-hmc-cdrs readers))
                                     owners readers pins))
            (fn-hmc-funded-at-p gs owners (fn-hmc-remove1 (cons tid g2) readers)
                                (fn-arpn-unpin-at g2 pins)))
   :hints (("Goal" :induct (fn-hmc-nat-listp gs)
            :in-theory (disable fn-hmc-funded-g-p fn-hmc-funded-at-p
                                fn-hmc-funded-at-p-of-append fn-arpn-pin-at
                                fn-arpn-unpin-at fn-hmc-cdrs fn-hmc-readers-at
                                fn-rpin-count-at fn-arpn-pins-of)))))

(local
 (defthm fn-hmc-funded-at-p-after-drain
   (implies (and (fn-arpn-pinsp pins) (fn-hmc-nat-listp gs) (alistp owners)
                 (fn-rpin-owner cid owners)
                 (fn-hmc-funded-at-p (append (fn-hmc-cdrs owners) (fn-hmc-cdrs readers))
                                     owners readers pins))
            (fn-hmc-funded-at-p gs (fn-rpin-remove cid owners) readers
                                (fn-arpn-unpin-at (cdr (fn-rpin-owner cid owners)) pins)))
   :hints (("Goal" :induct (fn-hmc-nat-listp gs)
            :in-theory (disable fn-hmc-funded-g-p fn-hmc-funded-at-p
                                fn-hmc-funded-at-p-of-append fn-arpn-pin-at
                                fn-arpn-unpin-at fn-hmc-cdrs fn-hmc-readers-at
                                fn-rpin-count-at fn-arpn-pins-of)))))

(local
 (defthm fn-hmc-cdrs-of-cons
   (equal (fn-hmc-cdrs (cons (cons a g) xs)) (cons g (fn-hmc-cdrs xs)))))

(local
 (defthm fn-hmc-cdrs-of-remove1-nat-listp
   (implies (fn-hmc-nat-listp (fn-hmc-cdrs xs))
            (fn-hmc-nat-listp (fn-hmc-cdrs (fn-hmc-remove1 x xs))))))

(local
 (defthm fn-hmc-cdrs-of-rpin-remove-nat-listp
   (implies (fn-hmc-nat-listp (fn-hmc-cdrs owners))
            (fn-hmc-nat-listp (fn-hmc-cdrs (fn-rpin-remove cid owners))))
   :hints (("Goal" :in-theory (enable fn-rpin-remove)))))

(local
 (defthm fn-hmc-pairsp-of-remove1
   (implies (fn-hmc-pairsp xs) (fn-hmc-pairsp (fn-hmc-remove1 x xs)))))

(local
 (defthm fn-hmc-alistp-of-rpin-remove
   (implies (alistp owners) (alistp (fn-rpin-remove cid owners)))
   :hints (("Goal" :in-theory (enable fn-rpin-remove)))))

(local
 (defthm fn-hmc-arpn-okp-of-pin-form
   (implies (fn-arpn-okp st)
            (fn-arpn-okp (list (car st) (fn-arpn-pin-at (car st) (cadr st)) (caddr st))))
   :hints (("Goal" :use ((:instance fn-hmc-arpn-okp-of-car-step (ev '(:pin))))
            :in-theory (e/d (fn-arpn-step)
                            (fn-hmc-arpn-okp-of-car-step fn-arpn-okp
                             fn-arpn-pin-at))))))

(local
 (defthm fn-hmc-arpn-okp-of-unpin-form
   (implies (and (fn-arpn-okp st) (natp g) (fn-arpn-held-p g (cadr st)))
            (fn-arpn-okp (list (car st) (fn-arpn-unpin-at g (cadr st)) (caddr st))))
   :hints (("Goal" :use ((:instance fn-hmc-arpn-okp-of-car-step (ev (list :unpin g))))
            :in-theory (e/d (fn-arpn-step)
                            (fn-hmc-arpn-okp-of-car-step fn-arpn-okp
                             fn-arpn-held-p fn-arpn-unpin-at))))))

(local
 (defthm fn-hmc-arpn-okp-car-natp
   (implies (fn-arpn-okp st) (natp (car st)))
   :hints (("Goal" :in-theory (enable fn-arpn-okp)))))

(defthm fn-hmc-do-pin-keeps-invp
  (implies (and (fn-hmc-invp st) (not (fn-hmc-ended st)))
           (fn-hmc-invp (mv-nth 0 (fn-hmc-do-pin st ev)))))

(defthm fn-hmc-do-pass-pin-keeps-invp
  (implies (and (fn-hmc-invp st) (not (fn-hmc-ended st)))
           (fn-hmc-invp (mv-nth 0 (fn-hmc-do-pass-pin st ev)))))

(defthm fn-hmc-do-unpin-keeps-invp
  (implies (and (fn-hmc-invp st) (not (fn-hmc-ended st)))
           (fn-hmc-invp (mv-nth 0 (fn-hmc-do-unpin st ev)))))

(defthm fn-hmc-do-capture-keeps-invp
  (implies (and (fn-hmc-invp st) (not (fn-hmc-ended st)))
           (fn-hmc-invp (mv-nth 0 (fn-hmc-do-capture st ev))))
  :hints (("Goal" :in-theory (enable fn-rpin-step))))

(local
 (defthm fn-hmc-rpin-owner-generation-natp
   (implies (and (alistp owners) (fn-hmc-nat-listp (fn-hmc-cdrs owners))
                 (fn-rpin-owner cid owners))
            (natp (cdr (fn-rpin-owner cid owners))))
   :hints (("Goal" :in-theory (enable fn-rpin-owner)))))

(local
 (defthm fn-hmc-rpin-owner-generation-held
   (implies (and (alistp owners) (fn-arpn-pinsp pins) (fn-rpin-owner cid owners)
                 (fn-hmc-funded-at-p (append (fn-hmc-cdrs owners) (fn-hmc-cdrs readers))
                                     owners readers pins))
            (fn-arpn-held-p (cdr (fn-rpin-owner cid owners)) pins))
   :hints (("Goal"
            :in-theory (e/d (fn-arpn-held-p fn-hmc-funded-g-p)
                            (fn-hmc-funded-universal fn-hmc-funded-at-p
                             fn-hmc-funded-at-p-of-append
                             fn-hmc-funded-at-p-of-cons fn-rpin-count-at
                             fn-hmc-readers-at fn-arpn-pins-of fn-rpin-owner
                             fn-hmc-cdrs fn-arpn-pinsp))
            :use ((:instance fn-hmc-funded-universal
                             (g (cdr (fn-rpin-owner cid owners)))))))))

(defthm fn-hmc-do-drain-keeps-invp
  (implies (and (fn-hmc-invp st) (not (fn-hmc-ended st)))
           (fn-hmc-invp (mv-nth 0 (fn-hmc-do-drain st ev))))
  :hints (("Goal"
           :use ((:instance fn-hmc-funded-at-p-nat-listp
                            (gs (append (fn-hmc-cdrs (fn-hmc-owners st))
                                        (fn-hmc-cdrs (fn-hmc-readers st))))
                            (owners (fn-hmc-owners st))
                            (readers (fn-hmc-readers st))
                            (pins (cadr (fn-hmc-arpn st)))))
           :in-theory (e/d (fn-rpin-step fn-arpn-step)
                           (fn-hmc-funded-at-p fn-hmc-funded-at-p-of-append
                            fn-hmc-funded-at-p-of-cons fn-hmc-funded-g-p
                            fn-rpin-owner fn-rpin-remove fn-arpn-pin-at
                            fn-arpn-unpin-at fn-hmc-cdrs fn-rpin-count-at
                            fn-hmc-readers-at fn-arpn-pins-of)))))

; ---- physical worker return: preserve identity and ownership until settlement

(local
 (defthm fn-hmc-workersp-of-workers-remove (implies (fn-hmc-workersp ws rows) (fn-hmc-workersp
   (fn-hmc-workers-remove slot ws) rows)) :hints (("Goal" :induct (fn-hmc-workers-remove slot ws)
   :in-theory (enable fn-hmc-workers-remove fn-hmc-workersp)))))

(local
 (defthm fn-hmc-worker-slots-of-workers-remove (equal (fn-hmc-worker-slots (fn-hmc-workers-remove
   slot ws)) (remove-equal slot (fn-hmc-worker-slots ws))) :hints (("Goal" :induct
   (fn-hmc-workers-remove slot ws) :in-theory (enable fn-hmc-workers-remove fn-hmc-worker-slots
   remove-equal)))))

(local
 (defthm fn-hmc-worker-slots-remove-absent (not (member-equal slot (fn-hmc-worker-slots
   (fn-hmc-workers-remove slot ws)))) :hints (("Goal" :in-theory (enable remove-equal)))))

(local
 (defthm fn-hmc-workersp-of-worker-of (implies (and (fn-hmc-workersp ws rows) (fn-hmc-worker-of tok
   ws)) (and (fn-pxe-rowp (fn-hmc-worker-of tok ws)) (not (equal (fn-hmc-worker-phase
   (fn-hmc-worker-of tok ws)) :idle)) (equal (fn-hmc-worker-token (fn-hmc-worker-of tok ws)) tok)
   (fn-hmc-row-of tok rows) (not (fn-hmc-row-settledp (fn-hmc-row-of tok rows))))) :hints (("Goal"
   :induct (fn-hmc-worker-of tok ws) :in-theory (enable fn-hmc-worker-of fn-hmc-workersp)))))

(local
 (defthm fn-hmc-busy-member-of-workers-remove (implies (member-equal tok (fn-hmc-busy-tokens
   (fn-hmc-workers-remove slot ws))) (member-equal tok (fn-hmc-busy-tokens ws))) :hints (("Goal"
   :induct (fn-hmc-workers-remove slot ws) :in-theory (enable fn-hmc-workers-remove
   fn-hmc-busy-tokens)))))

(local
 (defthm fn-hmc-busy-no-dup-of-workers-remove (implies (no-duplicatesp-equal (fn-hmc-busy-tokens
   ws)) (no-duplicatesp-equal (fn-hmc-busy-tokens (fn-hmc-workers-remove slot ws)))) :hints (("Goal"
   :induct (fn-hmc-workers-remove slot ws) :in-theory (enable fn-hmc-workers-remove
   fn-hmc-busy-tokens)))))

(local
 (defthm fn-hmc-worker-token-absent-after-removing-found-slot (implies (and (no-duplicatesp-equal
   (fn-hmc-busy-tokens ws)) (fn-hmc-worker-of tok ws)) (not (member-equal tok (fn-hmc-busy-tokens
   (fn-hmc-workers-remove (fn-hmc-worker-slot (fn-hmc-worker-of tok ws)) ws))))) :hints (("Goal"
   :induct (fn-hmc-worker-of tok ws) :in-theory (enable fn-hmc-worker-of fn-hmc-busy-tokens
   fn-hmc-workers-remove)))))

(local
 (defthm fn-hmc-prl-nth-unfolds (implies (natp n) (equal (fn-prl-nth n x) (nth n x))) :hints
   (("Goal" :induct (fn-prl-nth n x) :in-theory (enable fn-prl-nth nth)))))

(local
 (defthm fn-hmc-return-worker-fields (implies (equal (mv-nth 0 (fn-pxe-return w tok)) :returned)
   (and (fn-pxe-rowp w) (equal (fn-hmc-worker-slot (mv-nth 1 (fn-pxe-return w tok)))
   (fn-hmc-worker-slot w)) (equal (fn-hmc-worker-token (mv-nth 1 (fn-pxe-return w tok)))
   (fn-hmc-worker-token w)) (not (equal (fn-hmc-worker-phase (mv-nth 1 (fn-pxe-return w tok)))
   :idle)))) :hints (("Goal" :in-theory (e/d (fn-pxe-return fn-hmc-worker-slot fn-hmc-worker-token
   fn-hmc-worker-phase) (fn-prl-nth))))))

(local
 (defthm fn-hmc-do-return-keeps-invp (implies (and (fn-hmc-invp st) (not (fn-hmc-ended st)))
   (fn-hmc-invp (mv-nth 0 (fn-hmc-do-return st ev)))) :hints (("Goal" :in-theory (disable
   fn-pxe-return fn-hmc-workers-remove fn-hmc-worker-of fn-hmc-worker-slot fn-hmc-worker-token
   fn-hmc-worker-phase fn-hmc-funded-at-p-of-append)))))

(local
 (defthm fn-hmc-worker-of-nil (equal (fn-hmc-worker-of tok nil) nil)))

(local
 (defthm fn-hmc-return-refused-with-no-workers (implies (not (fn-hmc-workers st)) (equal
   (fn-hmc-do-return st ev) (mv st :refused))) :hints (("Goal" :in-theory (e/d (fn-hmc-do-return)
   (fn-hmc-worker-of))))))

(local
 (defthm fn-hmc-ended-invariant-has-no-workers (implies (and (fn-hmc-invp st) (fn-hmc-ended st))
   (not (fn-hmc-workers st))) :hints (("Goal" :in-theory (enable fn-hmc-invp)))))

(defthm fn-hmc-do-return-preserves-invp (implies (fn-hmc-invp st) (fn-hmc-invp (mv-nth 0
   (fn-hmc-do-return st ev)))) :hints (("Goal" :cases ((fn-hmc-ended st)) :in-theory (disable
   fn-hmc-invp fn-hmc-do-return) :use ((:instance fn-hmc-do-return-keeps-invp)))))

; ---- the close: an incarnation no read, lease or request names is unbound

(local
 (defthm fn-hmc-alistp-of-unbind-inc
   (implies (alistp fds) (alistp (fn-hmc-unbind-inc inc fds)))))

(local
 (defthm fn-hmc-fds-incs-of-unbind-inc
   (equal (fn-hmc-fds-incs (fn-hmc-unbind-inc inc fds))
          (remove-equal inc (fn-hmc-fds-incs fds)))))

(local
 (defthm fn-hmc-strip-cars-of-unbind-inc-member
   (implies (member-equal fd (strip-cars (fn-hmc-unbind-inc inc fds)))
            (member-equal fd (strip-cars fds)))))

(local
 (defthm fn-hmc-strip-cars-of-unbind-inc-no-dups
   (implies (no-duplicatesp-equal (strip-cars fds))
            (no-duplicatesp-equal (strip-cars (fn-hmc-unbind-inc inc fds))))))

(local
 (defthm fn-hmc-intersect-of-remove-cons
   (implies (not (intersectp-equal x closed))
            (not (intersectp-equal (remove-equal inc x) (cons inc closed))))))

(local
 (defthm fn-hmc-boundp-of-unbind-inc
   (equal (fn-hmc-boundp x (fn-hmc-unbind-inc inc fds))
          (and (not (equal x inc)) (fn-hmc-boundp x fds)))))

(local
 (defthm fn-hmc-fd-inc-of-unbind-inc
   (implies (and (alistp fds) (not (equal (fn-hmc-fd-inc fd fds) inc)))
            (equal (fn-hmc-fd-inc fd (fn-hmc-unbind-inc inc fds))
                   (fn-hmc-fd-inc fd fds)))
   :hints (("Goal" :induct (fn-hmc-unbind-inc inc fds)
            :in-theory (enable fn-hmc-fd-inc)))))

(local
 (defthm fn-hmc-lease-names-of-member
   (implies (and (fn-hmc-memberp (cons kind inc) leases))
            (fn-hmc-lease-names-p inc leases))))

(local
 (defthm fn-hmc-row-of-file-not-clear
   (implies (and (fn-hmc-rowsp rows) (fn-hmc-row-of key rows)
                 (not (fn-hmc-row-settledp (fn-hmc-row-of key rows)))
                 (fn-pio-file-clear-p inc rows))
            (not (equal (fn-hmc-row-file (fn-hmc-row-of key rows)) inc)))
   :hints (("Goal" :in-theory (enable fn-pio-file-clear-p fn-hmc-row-of fn-hmc-rowsp
                                      fn-hmc-row-file fn-hmc-row-settledp fn-hmc-row-phase)))))

(local
 (defthm fn-hmc-key-inc-not-the-closed
   (implies (and (fn-hmc-rowsp rows) (fn-pio-file-clear-p inc rows)
                 (not (fn-hmc-lease-names-p inc leases))
                 (fn-hmc-key-inc key rows leases))
            (not (equal (fn-hmc-key-inc key rows leases) inc)))
   :hints (("Goal" :use ((:instance fn-hmc-row-of-file-not-clear)
                         (:instance fn-hmc-lease-names-of-member (kind (car key)) (inc (cadr key))))
            :in-theory (e/d (fn-hmc-key-inc) (fn-hmc-row-of fn-hmc-rowsp fn-pio-file-clear-p
                                              fn-hmc-row-of-file-not-clear
                                              fn-hmc-lease-names-of-member))))))

(local
 (defthm fn-hmc-reqs-okp-of-unbind-inc
   (implies (and (fn-hmc-reqs-okp reqs fds rows leases) (alistp fds)
                 (fn-hmc-rowsp rows) (fn-pio-file-clear-p inc rows)
                 (not (fn-hmc-lease-names-p inc leases)))
            (fn-hmc-reqs-okp reqs (fn-hmc-unbind-inc inc fds) rows leases))
   :hints (("Goal" :induct (fn-hmc-reqs-okp reqs fds rows leases)
            :in-theory (disable fn-hmc-key-inc fn-hmc-unbind-inc fn-hmc-rowsp
                                fn-pio-file-clear-p fn-hmc-fd-inc))
           ("Subgoal *1/2" :use ((:instance fn-hmc-key-inc-not-the-closed
                                            (key (fn-hmc-req-key (car reqs)))))))))

(local
 (defthm fn-hmc-rows-open-p-of-close
   (implies (and (fn-hmc-rows-open-p rows fds closed) (fn-hmc-rowsp rows)
                 (fn-pio-file-clear-p inc rows) (true-listp closed))
            (fn-hmc-rows-open-p rows (fn-hmc-unbind-inc inc fds) (cons inc closed)))
   :hints (("Goal" :induct (fn-hmc-rows-open-p rows fds closed)
            :in-theory (e/d (fn-pio-file-clear-p fn-hmc-rowsp fn-hmc-row-file
                             fn-hmc-row-settledp fn-hmc-row-phase)
                            (fn-hmc-unbind-inc fn-hmc-boundp))))))

(local
 (defthm fn-hmc-leases-open-p-of-close
   (implies (and (fn-hmc-leases-open-p leases fds closed)
                 (not (fn-hmc-lease-names-p inc leases)) (true-listp closed))
            (fn-hmc-leases-open-p leases (fn-hmc-unbind-inc inc fds) (cons inc closed)))
   :hints (("Goal" :in-theory (disable fn-hmc-unbind-inc fn-hmc-boundp)))))

(local
 (defthm fn-hmc-quiet-close-is-clear
   (implies (and (fn-pio-direct-okp (fn-hmc-issued rows) holds) (fn-hmc-rowsp rows)
                 (fn-pio-direct-quiet-p inc holds))
            (fn-pio-file-clear-p inc rows))
   :hints (("Goal" :use ((:instance fn-pio-direct-quiet-is-clear
                                    (issued (fn-hmc-issued rows)) (file inc)))
            :in-theory (disable fn-pio-direct-quiet-p fn-pio-direct-okp fn-hmc-issued
                                fn-pio-file-clear-p)))))

(local
 (defthm fn-hmc-true-listp-of-remove1
   (implies (true-listp l) (true-listp (fn-hmc-remove1 x l)))))

(defthm fn-hmc-do-close-keeps-invp
  (implies (and (fn-hmc-invp st) (not (fn-hmc-ended st)))
           (fn-hmc-invp (mv-nth 0 (fn-hmc-do-close st ev))))
  :hints (("Goal" :in-theory (e/d (fn-hmc-do-close fn-hmc-invp)
                                  (fn-hmc-unbind-inc fn-hmc-issued fn-hmc-rowsp fn-pio-direct-okp
                                   fn-pio-direct-quiet-p fn-pio-file-clear-p
                                   fn-hmc-rows-open-p fn-hmc-leases-open-p fn-hmc-reqs-okp
                                   fn-hmc-workersp fn-hmc-rows-below-p fn-hmc-row-ids)))))

; ---- the issue: a fresh row joins the end of the rows, a running worker its slot

(local
 (defthm fn-hmc-issued-put-fresh-is-append
   (implies (and (fn-hmc-rowsp rows) (not (fn-pio-issued-row tok (fn-hmc-issued rows)))
                 (true-listp row) (equal (fn-pio-token row) tok))
            (equal (fn-pio-issued-put tok row (fn-hmc-issued rows))
                   (fn-hmc-issued (append rows (list row)))))
   :hints (("Goal" :induct (fn-hmc-rowsp rows)
            :in-theory (enable fn-hmc-issued fn-pio-issued-put fn-pio-issued-row fn-hmc-rowsp)))))

(local
 (defthm fn-hmc-row-of-absent-from-issued
   (implies (and (fn-hmc-rowsp rows) (not (fn-pio-issued-row tok (fn-hmc-issued rows))))
            (not (fn-hmc-row-of tok rows)))
   :hints (("Goal" :induct (fn-hmc-rowsp rows)
            :in-theory (enable fn-hmc-issued fn-pio-issued-row fn-hmc-rowsp fn-hmc-row-of)))))

(local
 (defthm fn-hmc-rowsp-of-append-row
   (implies (and (fn-hmc-rowsp rows) (fn-pio-rowp row))
            (fn-hmc-rowsp (append rows (list row))))))

(local
 (defthm fn-hmc-row-ids-of-append
   (equal (fn-hmc-row-ids (append rows x))
          (append (fn-hmc-row-ids rows) (fn-hmc-row-ids x)))))

(local
 (defthm fn-hmc-no-dup-of-append-fresh
   (implies (and (no-duplicatesp-equal x) (not (member-equal a x)))
            (no-duplicatesp-equal (append x (list a))))))

(local
 (defthm fn-hmc-rows-below-p-not-member
   (implies (fn-hmc-rows-below-p rows next)
            (not (member-equal next (fn-hmc-row-ids rows))))))

(local
 (defthm fn-hmc-rows-below-p-of-append-next
   (implies (and (fn-hmc-rows-below-p rows next) (natp next)
                 (equal (fn-hmc-row-id row) next))
            (fn-hmc-rows-below-p (append rows (list row)) (+ 1 next)))))

(local
 (defthm fn-hmc-rows-open-p-of-append-row
   (implies (and (fn-hmc-rows-open-p rows fds closed)
                 (fn-hmc-boundp (fn-hmc-row-file row) fds)
                 (not (fn-hmc-memberp (fn-hmc-row-file row) closed)))
            (fn-hmc-rows-open-p (append rows (list row)) fds closed))
   :hints (("Goal" :in-theory (disable fn-hmc-boundp fn-hmc-memberp)))))

(local
 (defthm fn-hmc-row-of-append
   (implies (fn-hmc-rowsp rows)
            (equal (fn-hmc-row-of key (append rows x))
                   (if (fn-hmc-row-of key rows) (fn-hmc-row-of key rows) (fn-hmc-row-of key x))))
   :hints (("Goal" :induct (fn-hmc-rowsp rows)
            :in-theory (enable fn-hmc-rowsp fn-hmc-row-of)))))

(local
 (defthm fn-hmc-workersp-of-append-row
   (implies (and (fn-hmc-workersp ws rows) (fn-hmc-rowsp rows))
            (fn-hmc-workersp ws (append rows (list row))))
   :hints (("Goal" :induct (fn-hmc-workersp ws rows)
            :in-theory (e/d (fn-hmc-workersp) (fn-hmc-row-of))))))

(local
 (defthm fn-hmc-key-inc-of-append-row
   (implies (and (fn-hmc-rowsp rows) (fn-hmc-key-inc key rows leases)
                 (natp (car (fn-pio-token row))) (true-listp row))
            (equal (fn-hmc-key-inc key (append rows (list row)) leases)
                   (fn-hmc-key-inc key rows leases)))
   :hints (("Goal" :in-theory (e/d (fn-hmc-key-inc fn-hmc-row-of) ())))))

(local
 (defthm fn-hmc-reqs-okp-of-append-row
   (implies (and (fn-hmc-reqs-okp reqs fds rows leases) (fn-hmc-rowsp rows)
                 (natp (car (fn-pio-token row))) (true-listp row))
            (fn-hmc-reqs-okp reqs fds (append rows (list row)) leases))
   :hints (("Goal" :induct (fn-hmc-reqs-okp reqs fds rows leases)
            :in-theory (disable fn-hmc-key-inc)))))

; A busy worker's token names a row, so its id is below the counter: the
; fresh token (whose id is the counter) is nobody's.
(local
 (defthm fn-hmc-busy-token-names-a-row
   (implies (and (fn-hmc-workersp ws rows) (member-equal tk (fn-hmc-busy-tokens ws)))
            (fn-hmc-row-of tk rows))
   :hints (("Goal" :induct (fn-hmc-workersp ws rows)
            :in-theory (e/d (fn-hmc-workersp fn-hmc-busy-tokens) (fn-hmc-row-of))))))

(local
 (defthm fn-hmc-no-row-at-the-counter
   (implies (and (fn-hmc-rowsp rows) (fn-hmc-rows-below-p rows next))
            (not (fn-hmc-row-of (cons next rest) rows)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-hmc-row-of-has-the-token (key (cons next rest)))
                  (:instance fn-hmc-row-of-is-a-true-list (key (cons next rest)))
                  (:instance fn-hmc-row-of-is-a-member (key (cons next rest)))
                  (:instance fn-hmc-car-of-token (r (fn-hmc-row-of (cons next rest) rows)))
                  (:instance fn-hmc-rows-below-p-member (r (fn-hmc-row-of (cons next rest) rows))))
            :in-theory (disable fn-hmc-row-of fn-hmc-rows-below-p fn-hmc-row-of-has-the-token
                                fn-hmc-row-of-is-a-true-list fn-hmc-row-of-is-a-member
                                fn-hmc-car-of-token fn-hmc-rows-below-p-member)))))

(local
 (defthm fn-hmc-busy-token-below-next
   (implies (and (fn-hmc-workersp ws rows) (fn-hmc-rowsp rows)
                 (fn-hmc-rows-below-p rows next))
            (not (member-equal (cons next rest) (fn-hmc-busy-tokens ws))))
   :hints (("Goal" :use ((:instance fn-hmc-busy-token-names-a-row (tk (cons next rest))))
            :in-theory (disable fn-hmc-busy-token-names-a-row fn-hmc-workersp
                                fn-hmc-busy-tokens fn-hmc-rows-below-p)))))

(local
 (defthm fn-hmc-rows-open-p-of-append-issued-row
   (implies (and (fn-hmc-rows-open-p rows fds closed)
                 (member-equal file (fn-hmc-fds-incs fds))
                 (not (member-equal file closed)) (true-listp closed))
            (fn-hmc-rows-open-p (append rows (list (list* n cid file eoff elen trailer '(:issued))))
                                fds closed))
   :hints (("Goal" :use ((:instance fn-hmc-rows-open-p-of-append-row
                                    (row (list* n cid file eoff elen trailer '(:issued)))))
            :in-theory (e/d (fn-hmc-row-file fn-hmc-row-settledp fn-hmc-row-phase)
                            (fn-hmc-rows-open-p-of-append-row))))))

(local
 (defthm fn-hmc-issued-row-accessors
   (and (equal (fn-hmc-row-id (list* n cid file eoff elen trailer '(:issued))) n)
        (equal (fn-hmc-row-file (list* n cid file eoff elen trailer '(:issued))) file)
        (not (fn-hmc-row-settledp (list* n cid file eoff elen trailer '(:issued)))))
   :hints (("Goal" :in-theory (enable fn-hmc-row-id fn-hmc-row-file fn-hmc-row-settledp
                                      fn-hmc-row-phase)))))

(local
 (defthm fn-hmc-row-ids-of-append-one
   (equal (fn-hmc-row-ids (append rows (list r)))
          (append (fn-hmc-row-ids rows) (list (fn-hmc-row-id r))))))

(local
 (defthm fn-hmc-worker-slots-of-workers-put-no-dup
   (implies (no-duplicatesp-equal (fn-hmc-worker-slots ws))
            (no-duplicatesp-equal
             (fn-hmc-worker-slots (cons w (fn-hmc-workers-remove (fn-hmc-worker-slot w) ws)))))
   :hints (("Goal" :in-theory (disable fn-hmc-workers-remove)))))

(local
 (defthm fn-hmc-busy-tokens-of-running-cons
   (implies (and (no-duplicatesp-equal (fn-hmc-busy-tokens ws))
                 (not (member-equal (fn-hmc-worker-token w) (fn-hmc-busy-tokens ws))))
            (no-duplicatesp-equal
             (fn-hmc-busy-tokens (cons w (fn-hmc-workers-remove slot ws)))))
   :hints (("Goal" :in-theory (disable fn-hmc-workers-remove)))))

(local
 (defthm fn-hmc-workersp-of-running-cons
   (implies (and (fn-hmc-workersp rest rows) (fn-pxe-rowp w)
                 (fn-hmc-row-of (fn-hmc-worker-token w) rows)
                 (not (fn-hmc-row-settledp (fn-hmc-row-of (fn-hmc-worker-token w) rows))))
            (fn-hmc-workersp (cons w rest) rows))
   :hints (("Goal" :in-theory (disable fn-hmc-row-of fn-pxe-rowp)))))

(local
 (defthm fn-hmc-worker-fields-are-nths
   (implies (true-listp w)
            (and (equal (fn-hmc-worker-token w) (nth 3 w))
                 (equal (fn-hmc-worker-phase w) (nth 2 w))))
   :hints (("Goal" :in-theory (enable fn-hmc-worker-token fn-hmc-worker-phase)))))

(local
 (defthm fn-hmc-row-of-singleton
   (equal (fn-hmc-row-of key (list r))
          (if (and (true-listp r) (equal (fn-pio-token r) key)) r nil))
   :hints (("Goal" :in-theory (enable fn-hmc-row-of)))))


; PRF-1242's issue step: an admitted read joins the rows (a fresh :issued row
; at the counter, for a bound and unclosed incarnation), runs on the idle
; worker's slot, holds its file, and advances the counter.
(defthm fn-hmc-do-issue-keeps-invp
  (implies (and (fn-hmc-invp st) (not (fn-hmc-ended st)))
           (fn-hmc-invp (mv-nth 0 (fn-hmc-do-issue st ev))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-pio-direct-admit-issues-exactly-its-row
                            (next (fn-hmc-next st)) (cid (fn-hmc-arg 2 ev)) (file (fn-hmc-arg 3 ev))
                            (eoff (fn-hmc-arg 4 ev)) (elen (fn-hmc-arg 5 ev)) (trailer (fn-hmc-arg 6 ev))
                            (worker (fn-hmc-idle-worker (fn-hmc-workers st)))
                            (issued (fn-hmc-issued (fn-hmc-rows st))) (holds (fn-hmc-holds st)))
                 (:instance fn-pio-direct-admit-keeps-okp
                            (next (fn-hmc-next st)) (cid (fn-hmc-arg 2 ev)) (file (fn-hmc-arg 3 ev))
                            (eoff (fn-hmc-arg 4 ev)) (elen (fn-hmc-arg 5 ev)) (trailer (fn-hmc-arg 6 ev))
                            (worker (fn-hmc-idle-worker (fn-hmc-workers st)))
                            (issued (fn-hmc-issued (fn-hmc-rows st))) (holds (fn-hmc-holds st))))
           :in-theory (e/d (fn-hmc-do-issue fn-hmc-invp)
                           (fn-pio-direct-admit fn-hmc-issued fn-pio-issued-put fn-pio-issued-rows
                            fn-hmc-rowsp fn-pio-direct-okp fn-hmc-workersp fn-hmc-reqs-okp
                            fn-hmc-rows-open-p fn-hmc-rows-below-p fn-hmc-row-ids
                            fn-hmc-idle-worker fn-hmc-workers-remove fn-hmc-busy-tokens
                            fn-hmc-worker-slots fn-pxe-rowp fn-pio-rowp fn-pio-token
                            fn-pio-issued-row fn-hmc-row-of)))))

; ---- the settle: the token's row leaves the rows, its worker idles in its slot

(local
 (defun fn-hmc-rows-drop (tok rows)
   (cond ((atom rows) nil)
         ((and (true-listp (car rows)) (equal (fn-pio-token (car rows)) tok)) (cdr rows))
         (t (cons (car rows) (fn-hmc-rows-drop tok (cdr rows)))))))

(local
 (defthm fn-hmc-issued-remove-is-rows-drop
   (implies (fn-hmc-rowsp rows)
            (equal (fn-pio-issued-remove tok (fn-hmc-issued rows))
                   (fn-hmc-issued (fn-hmc-rows-drop tok rows))))
   :hints (("Goal" :induct (fn-hmc-rows-drop tok rows)
            :in-theory (enable fn-hmc-issued fn-pio-issued-remove fn-hmc-rowsp)))))

(local
 (defthm fn-hmc-rowsp-of-rows-drop
   (implies (fn-hmc-rowsp rows) (fn-hmc-rowsp (fn-hmc-rows-drop tok rows)))))

(local
 (defthm fn-hmc-row-ids-of-rows-drop-member
   (implies (member-equal x (fn-hmc-row-ids (fn-hmc-rows-drop tok rows)))
            (member-equal x (fn-hmc-row-ids rows)))))

(local
 (defthm fn-hmc-row-ids-of-rows-drop-no-dup
   (implies (no-duplicatesp-equal (fn-hmc-row-ids rows))
            (no-duplicatesp-equal (fn-hmc-row-ids (fn-hmc-rows-drop tok rows))))))

(local
 (defthm fn-hmc-rows-below-p-of-rows-drop
   (implies (fn-hmc-rows-below-p rows next)
            (fn-hmc-rows-below-p (fn-hmc-rows-drop tok rows) next))))

(local
 (defthm fn-hmc-rows-open-p-of-rows-drop
   (implies (fn-hmc-rows-open-p rows fds closed)
            (fn-hmc-rows-open-p (fn-hmc-rows-drop tok rows) fds closed))
   :hints (("Goal" :in-theory (disable fn-hmc-boundp fn-hmc-memberp)))))

(local
 (defthm fn-hmc-row-of-rows-drop-other
   (implies (not (equal key tok))
            (equal (fn-hmc-row-of key (fn-hmc-rows-drop tok rows))
                   (fn-hmc-row-of key rows)))
   :hints (("Goal" :in-theory (enable fn-hmc-row-of)))))

(local
 (defthm fn-hmc-workersp-of-rows-drop
   (implies (and (fn-hmc-workersp ws rows)
                 (not (member-equal tok (fn-hmc-busy-tokens ws))))
            (fn-hmc-workersp ws (fn-hmc-rows-drop tok rows)))
   :hints (("Goal" :induct (fn-hmc-workersp ws rows)
            :in-theory (e/d (fn-hmc-workersp fn-hmc-busy-tokens)
                            (fn-hmc-row-of fn-hmc-rows-drop))))))

(local
 (defthm fn-hmc-key-inc-of-rows-drop-other
   (implies (not (equal key tok))
            (equal (fn-hmc-key-inc key (fn-hmc-rows-drop tok rows) leases)
                   (fn-hmc-key-inc key rows leases)))
   :hints (("Goal" :in-theory (e/d (fn-hmc-key-inc) (fn-hmc-row-of fn-hmc-rows-drop))))))

(local
 (defthm fn-hmc-reqs-okp-of-rows-drop
   (implies (and (fn-hmc-reqs-okp reqs fds rows leases) (not (fn-hmc-req-of tok reqs)))
            (fn-hmc-reqs-okp reqs fds (fn-hmc-rows-drop tok rows) leases))
   :hints (("Goal" :induct (fn-hmc-reqs-okp reqs fds rows leases)
            :in-theory (disable fn-hmc-key-inc fn-hmc-rows-drop)))))

(local
 (defthm fn-hmc-results-landed-p-of-remove1-assoc
   (implies (fn-hmc-results-landed-p results reqs)
            (fn-hmc-results-landed-p (remove1-assoc-equal key results) reqs))))

(local
 (defthm fn-hmc-workersp-of-idle-cons
   (implies (and (fn-hmc-workersp rest rows) (fn-pxe-rowp w)
                 (equal (fn-hmc-worker-phase w) :idle))
            (fn-hmc-workersp (cons w rest) rows))
   :hints (("Goal" :in-theory (disable fn-pxe-rowp)))))

(local
 (defthm fn-hmc-busy-tokens-of-idle-cons
   (implies (equal (fn-hmc-worker-phase w) :idle)
            (equal (fn-hmc-busy-tokens (cons w rest)) (fn-hmc-busy-tokens rest)))))


(local
 (defthm fn-hmc-idle-worker-of-row
   (implies (fn-pxe-rowp w)
            (and (fn-pxe-rowp (list* (car w) (nth 1 w) '(:idle nil)))
                 (equal (fn-hmc-worker-phase (list* (car w) (nth 1 w) '(:idle nil))) :idle)
                 (equal (fn-hmc-worker-slot (list* (car w) (nth 1 w) '(:idle nil)))
                        (fn-hmc-worker-slot w))))
   :hints (("Goal" :in-theory (enable fn-pxe-rowp fn-hmc-worker-phase fn-hmc-worker-slot)))))

(local
 (defthm fn-hmc-worker-slots-of-cons-same-slot-no-dup
   (implies (and (no-duplicatesp-equal (fn-hmc-worker-slots ws))
                 (equal (fn-hmc-worker-slot w) slot))
            (no-duplicatesp-equal
             (fn-hmc-worker-slots (cons w (fn-hmc-workers-remove slot ws)))))
   :hints (("Goal" :in-theory (disable fn-hmc-workers-remove)))))

(local
 (defthm fn-hmc-token-of-row-is-consp
   (implies (fn-pio-rowp r) (consp (fn-pio-token r)))
   :hints (("Goal" :in-theory (enable fn-pio-rowp fn-pio-token)))))

(local
 (defthm fn-hmc-pxe-row-is-consp
   (implies (fn-pxe-rowp w) (consp w))
   :rule-classes (:rewrite :forward-chaining)
   :hints (("Goal" :in-theory (enable fn-pxe-rowp)))))


; PRF-1242's settle step: a settlement that settles drops the token's row (no
; request is in flight for it: its verdict has landed), idles its worker in
; the same slot, drops the token's hold and consumes the verdict.
(defthm fn-hmc-do-settle-keeps-invp
  (implies (and (fn-hmc-invp st) (not (fn-hmc-ended st)))
           (fn-hmc-invp (mv-nth 0 (fn-hmc-do-settle st ev))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-pio-direct-settle-removes-exactly-its-row
                            (token (fn-hmc-arg 2 ev))
                            (worker (fn-hmc-worker-of (fn-hmc-arg 2 ev) (fn-hmc-workers st)))
                            (verdict (cdr (assoc-equal (fn-hmc-arg 2 ev) (fn-hmc-results st))))
                            (issued (fn-hmc-issued (fn-hmc-rows st))) (holds (fn-hmc-holds st)))
                 (:instance fn-pio-direct-settle-keeps-okp
                            (token (fn-hmc-arg 2 ev))
                            (worker (fn-hmc-worker-of (fn-hmc-arg 2 ev) (fn-hmc-workers st)))
                            (verdict (cdr (assoc-equal (fn-hmc-arg 2 ev) (fn-hmc-results st))))
                            (issued (fn-hmc-issued (fn-hmc-rows st))) (holds (fn-hmc-holds st)))
                 (:instance fn-hmc-worker-token-absent-after-removing-found-slot
                            (tok (fn-hmc-arg 2 ev)) (ws (fn-hmc-workers st)))
                 (:instance fn-hmc-req-of-is-assoc-like
                            (key (fn-hmc-arg 2 ev)) (results (fn-hmc-results st))
                            (reqs (fn-hmc-reqs st))))
           :in-theory (e/d (fn-hmc-do-settle fn-hmc-invp)
                           (fn-pio-direct-settle fn-hmc-issued fn-pio-issued-remove fn-pio-issued-rows
                            fn-hmc-rowsp fn-pio-direct-okp fn-hmc-workersp fn-hmc-reqs-okp
                            fn-hmc-rows-open-p fn-hmc-rows-below-p fn-hmc-row-ids
                            fn-hmc-worker-of fn-hmc-workers-remove fn-hmc-busy-tokens
                            fn-hmc-worker-slots fn-pxe-rowp fn-pio-rowp fn-pio-token
                            fn-pio-issued-row fn-hmc-row-of fn-hmc-rows-drop
                            fn-hmc-worker-token-absent-after-removing-found-slot
                            fn-hmc-req-of-is-assoc-like fn-hmc-results-landed-p fn-hmc-req-of)))))

; -----------------------------------------------------------------------------
; PRF-1242: the invariant of the concurrent reference holds over every run.
; One step keeps it whatever the event (each label's lemma above; an ended
; state and an unknown label refuse and change nothing), so every schedule
; from an invariant state ends in one -- in particular every schedule from
; fn-hmc-init (fn-hmc-init-invp).

(defthm fn-hmc-step-keeps-invp
  (implies (fn-hmc-invp st)
           (fn-hmc-invp (mv-nth 0 (fn-hmc-step st ev))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hmc-do-acquire-keeps-invp)
                 (:instance fn-hmc-do-release-keeps-invp)
                 (:instance fn-hmc-do-fd-open-keeps-invp)
                 (:instance fn-hmc-do-io-begin-keeps-invp)
                 (:instance fn-hmc-do-io-complete-keeps-invp)
                 (:instance fn-hmc-do-issue-keeps-invp)
                 (:instance fn-hmc-do-job-result-keeps-invp)
                 (:instance fn-hmc-do-cancel-keeps-invp)
                 (:instance fn-hmc-do-settle-keeps-invp)
                 (:instance fn-hmc-do-pin-keeps-invp)
                 (:instance fn-hmc-do-unpin-keeps-invp)
                 (:instance fn-hmc-do-pass-pin-keeps-invp)
                 (:instance fn-hmc-do-capture-keeps-invp)
                 (:instance fn-hmc-do-drain-keeps-invp)
                 (:instance fn-hmc-do-retire-keeps-invp)
                 (:instance fn-hmc-do-release-retired-keeps-invp)
                 (:instance fn-hmc-do-swap-keeps-invp)
                 (:instance fn-hmc-do-close-keeps-invp)
                 (:instance fn-hmc-do-crash-keeps-invp)
                 (:instance fn-hmc-do-return-preserves-invp)
                 (:instance fn-hmc-do-lease-acquire-keeps-invp (kind :window))
                 (:instance fn-hmc-do-lease-release-keeps-invp (kind :window))
                 (:instance fn-hmc-do-lease-acquire-keeps-invp (kind :discovery))
                 (:instance fn-hmc-do-lease-release-keeps-invp (kind :discovery)))
           :in-theory (e/d (fn-hmc-step)
                           (fn-hmc-invp fn-hmc-do-acquire fn-hmc-do-release fn-hmc-do-fd-open fn-hmc-do-io-begin fn-hmc-do-io-complete fn-hmc-do-issue fn-hmc-do-job-result fn-hmc-do-cancel fn-hmc-do-settle fn-hmc-do-pin fn-hmc-do-unpin fn-hmc-do-pass-pin fn-hmc-do-capture fn-hmc-do-drain fn-hmc-do-retire fn-hmc-do-release-retired fn-hmc-do-swap fn-hmc-do-close fn-hmc-do-crash fn-hmc-do-return fn-hmc-do-lease-acquire fn-hmc-do-lease-release fn-hmc-do-acquire-keeps-invp fn-hmc-do-release-keeps-invp fn-hmc-do-fd-open-keeps-invp fn-hmc-do-io-begin-keeps-invp fn-hmc-do-io-complete-keeps-invp fn-hmc-do-issue-keeps-invp fn-hmc-do-job-result-keeps-invp fn-hmc-do-cancel-keeps-invp fn-hmc-do-settle-keeps-invp fn-hmc-do-pin-keeps-invp fn-hmc-do-unpin-keeps-invp fn-hmc-do-pass-pin-keeps-invp fn-hmc-do-capture-keeps-invp fn-hmc-do-drain-keeps-invp fn-hmc-do-retire-keeps-invp fn-hmc-do-release-retired-keeps-invp fn-hmc-do-swap-keeps-invp fn-hmc-do-close-keeps-invp fn-hmc-do-crash-keeps-invp fn-hmc-do-lease-acquire-keeps-invp fn-hmc-do-lease-release-keeps-invp fn-hmc-do-return-preserves-invp)))))

(local
 (defthm fn-hmc-step-keeps-invp-car
   (implies (fn-hmc-invp st) (fn-hmc-invp (car (fn-hmc-step st ev))))
   :hints (("Goal" :use fn-hmc-step-keeps-invp
            :in-theory (disable fn-hmc-invp fn-hmc-step fn-hmc-step-keeps-invp)))))

(defthm fn-hmc-run-keeps-invp
  (implies (fn-hmc-invp st)
           (fn-hmc-invp (fn-hmc-run st sched)))
  :hints (("Goal" :induct (fn-hmc-run st sched)
           :in-theory (e/d (fn-hmc-run) (fn-hmc-invp fn-hmc-step)))))

(defthm fn-hmc-init-run-keeps-invp
  (fn-hmc-invp (fn-hmc-run (fn-hmc-init) sched))
  :hints (("Goal" :in-theory (disable fn-hmc-invp fn-hmc-run fn-hmc-init))))
