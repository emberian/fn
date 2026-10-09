; fn: the executable layer equals the contract, proved.
;
; Each function of books/runtime-contract-exec.lisp is proved EQUAL to its
; contract twin on every recognized state `fn-rtc-st-p', so the contract's
; keystones hold of the executable layer by rewriting.  The completion the
; contract sees is `fn-rtc-landed' (an :in completion's data, read from the
; leased buffer):
;
;   (fn-rtc-x-step* e q st) = (fn-rtc-step* st (fn-rtc-landed e st) q)
;
; Order matters.  The `-keeps-st-p' lemmas come first, before any `-is' rule
; exists: an `-is' rule would rewrite the layer's call into the contract's
; before the recognizer lemma could fire.

(in-package "ACL2")
(include-book "runtime-contract-exec")

(defthm fn-rtc-st-p-is-shapep
  (equal (fn-rtc-st-p x) (fn-rtc-shapep x))
  :hints (("Goal" :in-theory (enable fn-rtc-st-p fn-rtc-st$ap))))

(in-theory (disable fn-rtc-st-p-is-shapep))

(defthm fn-rtc-x-req-acquire-keeps-st-p
  (implies (fn-rtc-st-p fn-rtc-st)
           (fn-rtc-st-p (mv-nth 0 (fn-rtc-x-req-acquire r id inc fn-rtc-st))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-x-req-acquire)
                                  (fn-rtc-x-submit-okp fn-rtc-x-live-p fn-rtc-x-current-p
                                   fn-rtc-kind-out-p fn-rtc-extrap)))))

(defthm fn-rtc-x-req-write-keeps-st-p
  (implies (fn-rtc-st-p fn-rtc-st)
           (fn-rtc-st-p (mv-nth 0 (fn-rtc-x-req-write r id inc fn-rtc-st))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-x-req-write)
                                  (fn-rtc-x-submit-okp fn-rtc-x-live-p fn-rtc-x-current-p
                                   fn-rtc-kind-out-p fn-rtc-extrap)))))

(defthm fn-rtc-x-req-release-keeps-st-p
  (implies (fn-rtc-st-p fn-rtc-st)
           (fn-rtc-st-p (mv-nth 0 (fn-rtc-x-req-release r id inc fn-rtc-st))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-x-req-release)
                                  (fn-rtc-x-submit-okp fn-rtc-x-live-p fn-rtc-x-current-p
                                   fn-rtc-kind-out-p fn-rtc-extrap)))))

(defthm fn-rtc-x-req-close-keeps-st-p
  (implies (fn-rtc-st-p fn-rtc-st)
           (fn-rtc-st-p (mv-nth 0 (fn-rtc-x-req-close r id inc fn-rtc-st))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-x-req-close)
                                  (fn-rtc-x-submit-okp fn-rtc-x-live-p fn-rtc-x-current-p
                                   fn-rtc-kind-out-p fn-rtc-extrap)))))

(defthm fn-rtc-x-req-submit-keeps-st-p
  (implies (fn-rtc-st-p fn-rtc-st)
           (fn-rtc-st-p (mv-nth 0 (fn-rtc-x-req-submit r id inc fn-rtc-st))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-x-req-submit)
                                  (fn-rtc-x-submit-okp fn-rtc-x-live-p fn-rtc-x-current-p
                                   fn-rtc-kind-out-p fn-rtc-extrap)))))

(defthm fn-rtc-x-req-cancel-keeps-st-p
  (implies (fn-rtc-st-p fn-rtc-st)
           (fn-rtc-st-p (mv-nth 0 (fn-rtc-x-req-cancel r id inc fn-rtc-st))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-x-req-cancel)
                                  (fn-rtc-x-submit-okp fn-rtc-x-live-p fn-rtc-x-current-p
                                   fn-rtc-kind-out-p fn-rtc-extrap)))))

(defthm fn-rtc-x-request-keeps-st-p
  (implies (fn-rtc-st-p fn-rtc-st)
           (fn-rtc-st-p (mv-nth 0 (fn-rtc-x-request r id inc fn-rtc-st))))
  :hints (("Goal" :expand ((fn-rtc-x-request r id inc fn-rtc-st)) :in-theory (disable mv-nth))))

(defthm fn-rtc-x-requests-keeps-st-p
  (implies (fn-rtc-st-p fn-rtc-st)
           (fn-rtc-st-p (mv-nth 0 (fn-rtc-x-requests reqs id inc fn-rtc-st)))))

(defthm fn-rtc-x-retire-drained-keeps-st-p
  (implies (fn-rtc-st-p fn-rtc-st)
           (fn-rtc-st-p (fn-rtc-x-retire-drained id fn-rtc-st)))
  :hints (("Goal" :in-theory (enable fn-rtc-x-retire-drained))))

(defthm fn-rtc-x-end-lease-keeps-st-p
  (implies (fn-rtc-st-p fn-rtc-st)
           (fn-rtc-st-p (fn-rtc-x-end-lease u fn-rtc-st)))
  :hints (("Goal" :in-theory (enable fn-rtc-x-end-lease))))

(defthm fn-rtc-x-end-use-keeps-st-p
  (implies (fn-rtc-st-p fn-rtc-st)
           (fn-rtc-st-p (fn-rtc-x-end-use e fn-rtc-st)))
  :hints (("Goal" :in-theory (enable fn-rtc-x-end-use))))

(defthm fn-rtc-x-current-p-is
  (equal (fn-rtc-x-current-p id inc fn-rtc-st) (fn-rtc-current-p id inc fn-rtc-st))
  :hints (("Goal" :in-theory (enable fn-rtc-st-slot))))

(defthm fn-rtc-x-live-p-is
  (equal (fn-rtc-x-live-p id inc fn-rtc-st) (fn-rtc-live-p id inc fn-rtc-st))
  :hints (("Goal" :in-theory (enable fn-rtc-st-slot))))

(defthm fn-rtc-x-retire-drained-is
  (equal (fn-rtc-x-retire-drained id fn-rtc-st) (fn-rtc-retire-drained id fn-rtc-st))
  :hints (("Goal" :in-theory (enable fn-rtc-retire-drained fn-rtc-st-slot fn-rtc-st-uses fn-rtc-st-set-slot))))

(defthm fn-rtc-x-acts-on-p-is
  (equal (fn-rtc-x-acts-on-p e fn-rtc-st) (fn-rtc-acts-on-p fn-rtc-st e))
  :hints (("Goal" :in-theory (enable fn-rtc-x-acts-on-p fn-rtc-st-slot fn-rtc-st-uses))))

(defthm fn-rtc-x-rearm-is
  (equal (fn-rtc-x-rearm fn-rtc-st) (fn-rtc-rearm fn-rtc-st))
  :hints (("Goal" :in-theory (enable fn-rtc-x-rearm fn-rtc-rearm fn-rtc-st-free-slot fn-rtc-st-uses
                                     fn-rtc-st-next-op fn-rtc-st-issue))))

(defthm fn-rtc-x-req-acquire-is
  (equal (fn-rtc-x-req-acquire r id inc fn-rtc-st) (fn-rtc-req-acquire r id inc fn-rtc-st))
  :hints (("Goal" :in-theory (enable fn-rtc-x-req-acquire fn-rtc-st-config fn-rtc-st-owner fn-rtc-st-gen
                                     fn-rtc-st-reset))))

(defthm fn-rtc-x-req-release-is
  (implies (fn-rtc-shapep fn-rtc-st)
           (equal (fn-rtc-x-req-release r id inc fn-rtc-st) (fn-rtc-req-release r id inc fn-rtc-st)))
  :hints (("Goal" :in-theory (enable fn-rtc-x-req-release fn-rtc-st-config fn-rtc-st-owner fn-rtc-st-gen
                                     fn-rtc-st-set-meta))))

(defthm fn-rtc-x-req-cancel-is
  (equal (fn-rtc-x-req-cancel r id inc fn-rtc-st) (fn-rtc-req-cancel r id inc fn-rtc-st))
  :hints (("Goal" :in-theory (enable fn-rtc-x-req-cancel fn-rtc-st-config fn-rtc-st-uses))))

(defthm fn-rtc-x-req-close-is
  (equal (fn-rtc-x-req-close r id inc fn-rtc-st) (fn-rtc-req-close r id inc fn-rtc-st))
  :hints (("Goal" :in-theory (enable fn-rtc-x-req-close fn-rtc-st-config fn-rtc-st-slot fn-rtc-st-next-op
                                     fn-rtc-st-set-slot fn-rtc-st-issue))))

(defthm fn-rtc-x-req-write-is
  (implies (fn-rtc-shapep fn-rtc-st)
           (equal (fn-rtc-x-req-write r id inc fn-rtc-st) (fn-rtc-req-write r id inc fn-rtc-st)))
  :hints (("Goal" :in-theory (enable fn-rtc-x-req-write fn-rtc-st-config fn-rtc-st-owner fn-rtc-st-gen
                                     fn-rtc-st-fill fn-rtc-st-splice)
           :use ((:instance fn-rtc-c-shapep-buffer (s fn-rtc-st) (h (fn-rtc-get 1 r)))))))

(defthm fn-rtc-x-submit-okp-is
  (equal (fn-rtc-x-submit-okp kind hd id inc fn-rtc-st) (fn-rtc-submit-okp kind hd id inc fn-rtc-st))
  :hints (("Goal" :in-theory (enable fn-rtc-x-submit-okp fn-rtc-st-config fn-rtc-st-owner fn-rtc-st-gen
                                     fn-rtc-st-fill))))


(defthm fn-rtc-x-req-submit-is
  (implies (fn-rtc-shapep fn-rtc-st)
           (equal (fn-rtc-x-req-submit r id inc fn-rtc-st) (fn-rtc-req-submit r id inc fn-rtc-st)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-x-req-submit fn-rtc-st-config fn-rtc-st-owner fn-rtc-st-gen
                                     fn-rtc-st-slot fn-rtc-st-uses fn-rtc-st-next-op fn-rtc-st-set-meta
                                     fn-rtc-st-issue)
                                  (fn-rtc-get fn-rtc-get-out-of-range fn-rtc-buffer-out-of-range
                                   fn-rtc-c-shapep-buffer fn-rtc-nbufs fn-rtc-cap fn-rtc-h-buf fn-rtc-h-off
                                   fn-rtc-h-len fn-rtc-h-gen fn-rtc-s-res fn-rtc-use-bound fn-rtc-submit-okp
                                   fn-rtc-x-submit-okp fn-rtc-kind-out-p fn-rtc-extrap))
           :use ((:instance fn-rtc-c-shapep-buffer (s fn-rtc-st) (h (fn-rtc-h-buf (fn-rtc-get 2 r))))))))

(defthm fn-rtc-x-request-is
  (implies (fn-rtc-st-p fn-rtc-st)
           (equal (fn-rtc-x-request r id inc fn-rtc-st) (fn-rtc-request r id inc fn-rtc-st)))
  :hints (("Goal" :expand ((fn-rtc-x-request r id inc fn-rtc-st))
           :in-theory (enable fn-rtc-request fn-rtc-st-p-is-shapep))))

(defthm fn-rtc-request-keeps-st-p
  (implies (fn-rtc-st-p fn-rtc-st)
           (fn-rtc-st-p (mv-nth 0 (fn-rtc-request r id inc fn-rtc-st))))
  :hints (("Goal" :use (fn-rtc-x-request-keeps-st-p fn-rtc-x-request-is)
           :in-theory (disable fn-rtc-x-request-keeps-st-p fn-rtc-x-request-is))))


(defthm fn-rtc-x-requests-is
  (implies (fn-rtc-st-p fn-rtc-st)
           (equal (fn-rtc-x-requests reqs id inc fn-rtc-st) (fn-rtc-requests reqs id inc fn-rtc-st)))
  :hints (("Goal" :induct (fn-rtc-x-requests reqs id inc fn-rtc-st)
           :in-theory (e/d (fn-rtc-requests) (mv-nth)))))

(defthm fn-rtc-st-p-of-with-slot
  (implies (fn-rtc-st-p fn-rtc-st) (fn-rtc-st-p (fn-rtc-with-slot id slot fn-rtc-st)))
  :hints (("Goal" :use fn-rtc-st-p-of-set-slot :in-theory (e/d (fn-rtc-st-set-slot) (fn-rtc-st-p-of-set-slot)))))

(defthm fn-rtc-st-p-of-with-mstate
  (implies (fn-rtc-st-p fn-rtc-st) (fn-rtc-st-p (fn-rtc-with-mstate id m fn-rtc-st)))
  :hints (("Goal" :use fn-rtc-st-p-of-set-mstate :in-theory (e/d (fn-rtc-st-set-mstate) (fn-rtc-st-p-of-set-mstate)))))

(defthm fn-rtc-st-p-of-with-uses
  (implies (fn-rtc-st-p fn-rtc-st) (fn-rtc-st-p (fn-rtc-with-uses uses fn-rtc-st)))
  :hints (("Goal" :use fn-rtc-st-p-of-set-uses :in-theory (e/d (fn-rtc-st-set-uses) (fn-rtc-st-p-of-set-uses)))))

(defthm fn-rtc-st-p-of-spec-issue
  (implies (fn-rtc-st-p fn-rtc-st) (fn-rtc-st-p (fn-rtc-issue use fn-rtc-st)))
  :hints (("Goal" :use fn-rtc-st-p-of-issue :in-theory (e/d (fn-rtc-st-issue) (fn-rtc-st-p-of-issue)))))

(defthm fn-rtc-x-deliver-is
  (implies (fn-rtc-st-p fn-rtc-st)
           (equal (fn-rtc-x-deliver id inc ev q fn-rtc-st) (fn-rtc-deliver fn-rtc-st id inc ev q)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-x-deliver fn-rtc-deliver fn-rtc-st-mstate fn-rtc-st-b-pool)
                                  (mv-nth fn-rtc-st-p-is-shapep))
           :expand ((:free (x) (fn-rtc-st-set-mstate id x fn-rtc-st))))))

(defthm fn-rtc-x-close-branch-is
  (implies (fn-rtc-st-p fn-rtc-st)
           (equal (fn-rtc-x-close-branch id inc fn-rtc-st) (fn-rtc-close-branch fn-rtc-st id inc)))
  :hints (("Goal" :in-theory (enable fn-rtc-x-close-branch fn-rtc-close-branch fn-rtc-st-release-all
                                     fn-rtc-st-uses fn-rtc-st-slot fn-rtc-st-set-slot fn-rtc-st-set-mstate
                                     fn-rtc-with-slot fn-rtc-with-mstate))))

(defthm fn-rtc-x-accept-branch-is
  (implies (fn-rtc-st-p fn-rtc-st)
           (equal (fn-rtc-x-accept-branch out q fn-rtc-st) (fn-rtc-accept-branch fn-rtc-st out q)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-x-accept-branch fn-rtc-accept-branch fn-rtc-st-free-slot
                                   fn-rtc-st-slot fn-rtc-st-set-slot fn-rtc-st-set-mstate)
                                  (mv-nth fn-rtc-deliver fn-rtc-rearm fn-rtc-free-slot)))))

(defun fn-rtc-ind-octets-n (b off n)
  (if (zp n) (list b off) (fn-rtc-ind-octets-n (cdr b) off (- n 1))))

(defthm fn-rtc-octets-n-p-of-take
  (implies (and (fn-cbor-octet-listp b) (natp n))
           (equal (fn-rtc-octets-n-p (take n b) n)
                  (or (zp n) (<= n (len b)))))
  :hints (("Goal" :induct (fn-rtc-ind-octets-n b off n))))

(defthm fn-rtc-octet-listp-of-nthcdr
  (implies (fn-cbor-octet-listp b) (fn-cbor-octet-listp (nthcdr n b))))

(defthm fn-rtc-append-take-nthcdr
  (implies (and (true-listp b) (natp n) (<= n (len b)))
           (equal (append (take n b) (nthcdr n b)) b)))

(defthm fn-rtc-nthcdr-of-nthcdr
  (implies (and (natp a) (natp c))
           (equal (nthcdr a (nthcdr c x)) (nthcdr (+ a c) x))))

(defthm fn-rtc-append-assoc-x
  (equal (append (append a b) c) (append a (append b c))))

(defthm fn-rtc-splice-landed-identity
  (implies (and (true-listp b) (natp off) (natp n)
                (or (zp n) (<= (+ off n) (len b))))
           (equal (fn-rtc-splice b off (take n (nthcdr off b))) b))
  :hints (("Goal" :in-theory (e/d (fn-rtc-splice) (fn-rtc-append-take-nthcdr fn-rtc-nthcdr-of-nthcdr))
           :cases ((zp n)))
          ("Subgoal 2" :use ((:instance fn-rtc-append-take-nthcdr (n off))
                             (:instance fn-rtc-append-take-nthcdr (n n) (b (nthcdr off b)))
                             (:instance fn-rtc-nthcdr-of-nthcdr (a n) (c off) (x b))))
          ("Subgoal 1" :cases ((<= off (len b)))
           :use ((:instance fn-rtc-append-take-nthcdr (n off))))))

(defthm fn-rtc-landed-trivial
  (implies (not (and (fn-rtc-completionp e) (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))
           (equal (fn-rtc-landed e s) e))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-landed)))))

; The fields of the landed completion are read off its definition alone: the
; ambient theory searches the use table and the list readers on every
; conjunct, millions of steps for what is a rebuilt five-element list.
(deftheory fn-rtc-landed-thy
  (union-theories (theory 'minimal-theory)
                  '(fn-rtc-landed fn-rtc-e-outcome fn-rtc-get fn-rtc-key fn-rtc-e-kind fn-rtc-e-id fn-rtc-e-inc
                    (:executable-counterpart nfix) (:executable-counterpart zp)
                    (:executable-counterpart binary-+) (:executable-counterpart fn-rtc-get)
                    (:executable-counterpart consp) car-cons cdr-cons)))

(defthm fn-rtc-landed-key
  (equal (fn-rtc-key (fn-rtc-landed e s)) (fn-rtc-key e))
  :hints (("Goal" :in-theory (theory 'fn-rtc-landed-thy))))

(defthm fn-rtc-outcomep-boolean
  (booleanp (fn-rtc-outcomep o))
  :rule-classes :type-prescription)

(defthm fn-rtc-completionp-boolean
  (booleanp (fn-rtc-completionp e))
  :rule-classes :type-prescription)

(defthm fn-rtc-completionp-of-rebuilt
  (implies (fn-rtc-completionp e)
           (fn-rtc-completionp (list (fn-rtc-get 0 e) (fn-rtc-get 1 e) (fn-rtc-get 2 e) (fn-rtc-get 3 e)
                                     (fn-rtc-get 4 e) data)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                             '(fn-rtc-completionp fn-rtc-get (:executable-counterpart nfix)
                                               (:executable-counterpart zp) (:executable-counterpart binary-+)
                                               (:executable-counterpart consp) car-cons cdr-cons
                                               (:executable-counterpart len) len)))))

(defthm fn-rtc-landed-completionp
  (equal (fn-rtc-completionp (fn-rtc-landed e s)) (fn-rtc-completionp e))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                             '(fn-rtc-landed fn-rtc-e-outcome fn-rtc-completionp-of-rebuilt
                                               fn-rtc-completionp-boolean)))))

(defthm fn-rtc-landed-kind
  (equal (fn-rtc-e-kind (fn-rtc-landed e s)) (fn-rtc-e-kind e))
  :hints (("Goal" :in-theory (theory 'fn-rtc-landed-thy))))

(defthm fn-rtc-landed-id
  (equal (fn-rtc-e-id (fn-rtc-landed e s)) (fn-rtc-e-id e))
  :hints (("Goal" :in-theory (theory 'fn-rtc-landed-thy))))

(defthm fn-rtc-landed-inc
  (equal (fn-rtc-e-inc (fn-rtc-landed e s)) (fn-rtc-e-inc e))
  :hints (("Goal" :in-theory (theory 'fn-rtc-landed-thy))))

(defthm fn-rtc-landed-outcome
  (equal (fn-rtc-e-outcome (fn-rtc-landed e s)) (fn-rtc-e-outcome e))
  :hints (("Goal" :in-theory (theory 'fn-rtc-landed-thy))))

(defthm fn-rtc-landed-fields
  (and (equal (fn-rtc-key (fn-rtc-landed e s)) (fn-rtc-key e))
       (equal (fn-rtc-completionp (fn-rtc-landed e s)) (fn-rtc-completionp e))
       (equal (fn-rtc-e-kind (fn-rtc-landed e s)) (fn-rtc-e-kind e))
       (equal (fn-rtc-e-id (fn-rtc-landed e s)) (fn-rtc-e-id e))
       (equal (fn-rtc-e-inc (fn-rtc-landed e s)) (fn-rtc-e-inc e))
       (equal (fn-rtc-e-outcome (fn-rtc-landed e s)) (fn-rtc-e-outcome e)))
  :rule-classes nil
  :hints (("Goal" :use (fn-rtc-landed-key fn-rtc-landed-completionp fn-rtc-landed-kind fn-rtc-landed-id
                        fn-rtc-landed-inc fn-rtc-landed-outcome))))

(defthm fn-rtc-e-data-of-landed
  (implies (and (fn-rtc-completionp e)
                (equal u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))) u
                (member-eq (fn-rtc-get 0 u) *fn-rtc-in-kinds*)
                (member-eq (fn-rtc-get 0 (fn-rtc-e-outcome e)) '(:done :short)))
           (equal (fn-rtc-e-data (fn-rtc-landed e s))
                  (take (nfix (fn-rtc-get 1 (fn-rtc-e-outcome e)))
                        (nthcdr (fn-rtc-h-off (fn-rtc-u-hd u)) (fn-rtc-bytes (fn-rtc-h-buf (fn-rtc-u-hd u)) s)))))
  :hints (("Goal" :in-theory (disable fn-rtc-find-use fn-rtc-key fn-rtc-completionp))))

(defthm fn-rtc-octets-n-p-of-take-nthcdr
  (implies (and (fn-cbor-octet-listp b) (natp off) (natp n))
           (equal (fn-rtc-octets-n-p (take n (nthcdr off b)) n)
                  (or (zp n) (<= (+ off n) (len b)))))
  :hints (("Goal" :in-theory (disable fn-rtc-octets-n-p-of-take)
           :use ((:instance fn-rtc-octets-n-p-of-take (b (nthcdr off b)))))))

(defthm fn-rtc-st-p-bytes-octets
  (implies (fn-rtc-st-p s)
           (and (fn-cbor-octet-listp (fn-rtc-bytes h s))
                (true-listp (fn-rtc-bytes h s))))
  :hints (("Goal" :in-theory (enable fn-rtc-st-p-is-shapep)
           :use ((:instance fn-rtc-c-shapep-buffer)))))

(defthm fn-rtc-x-delivered-outcome-is
  (implies (and (fn-rtc-st-p s) (fn-rtc-completionp e)
                (equal u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))) u)
           (equal (fn-rtc-x-delivered-outcome u e (len (fn-rtc-bytes (fn-rtc-h-buf (fn-rtc-u-hd u)) s)))
                  (fn-rtc-delivered-outcome u (fn-rtc-landed e s))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-x-delivered-outcome fn-rtc-delivered-outcome)
                                  (fn-rtc-find-use fn-rtc-key fn-rtc-completionp fn-rtc-landed fn-rtc-e-data))
           :use ((:instance fn-rtc-st-p-bytes-octets (h (fn-rtc-h-buf (fn-rtc-u-hd u))))))))

(defthm fn-rtc-x-delivered-in-ok
  (implies (and (member-eq (fn-rtc-get 0 u) *fn-rtc-in-kinds*)
                (member-eq (fn-rtc-get 0 (fn-rtc-x-delivered-outcome u e fl)) '(:done :short)))
           (and (member-eq (fn-rtc-get 0 (fn-rtc-e-outcome e)) '(:done :short))
                (natp (fn-rtc-get 1 (fn-rtc-e-outcome e)))
                (or (zp (fn-rtc-get 1 (fn-rtc-e-outcome e)))
                    (<= (+ (fn-rtc-h-off (fn-rtc-u-hd u)) (fn-rtc-get 1 (fn-rtc-e-outcome e))) fl))))
  :hints (("Goal" :in-theory (enable fn-rtc-x-delivered-outcome)))
  :rule-classes nil)

(defthm fn-rtc-landed-splice-is-identity
  (implies (and (fn-cbor-octet-listp b) (true-listp b)
                (member-eq (fn-rtc-get 0 u) *fn-rtc-in-kinds*)
                (member-eq (fn-rtc-get 0 (fn-rtc-x-delivered-outcome u e (len b))) '(:done :short)))
           (equal (fn-rtc-splice b (fn-rtc-h-off (fn-rtc-u-hd u))
                                 (take (nfix (fn-rtc-get 1 (fn-rtc-e-outcome e)))
                                       (nthcdr (fn-rtc-h-off (fn-rtc-u-hd u)) b)))
                  b))
  :hints (("Goal" :in-theory (disable fn-rtc-splice fn-rtc-x-delivered-outcome)
           :use ((:instance fn-rtc-x-delivered-in-ok (fl (len b)))
                 (:instance fn-rtc-splice-landed-identity (off (fn-rtc-h-off (fn-rtc-u-hd u)))
                            (n (fn-rtc-get 1 (fn-rtc-e-outcome e))))))))

(defthm fn-rtc-delivered-outcome-of-landed
  (implies (and (fn-rtc-st-p s) (fn-rtc-completionp e)
                (equal u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))) u)
           (equal (fn-rtc-delivered-outcome u (fn-rtc-landed e s))
                  (fn-rtc-x-delivered-outcome u e (len (fn-rtc-bytes (fn-rtc-h-buf (fn-rtc-u-hd u)) s)))))
  :hints (("Goal" :use fn-rtc-x-delivered-outcome-is
           :in-theory (union-theories (theory 'minimal-theory) '()))))



(defthm fn-rtc-lease-return-landed-bytes
  (implies (and (fn-rtc-st-p s) (fn-rtc-completionp e)
                (equal u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))) u)
           (equal (fn-rtc-get 2 (fn-rtc-lease-return u (fn-rtc-landed e s)
                                                     (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s)
                                                     s1))
                  (fn-rtc-get 2 (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-lease-return)
                                  (fn-rtc-find-use fn-rtc-key fn-rtc-completionp fn-rtc-splice
                                   fn-rtc-delivered-outcome fn-rtc-x-delivered-outcome fn-rtc-landed
                                   fn-rtc-current-p fn-rtc-slot fn-rtc-s-status fn-rtc-st-p
                                   fn-rtc-h-buf fn-rtc-h-off fn-rtc-u-hd fn-rtc-b-gen fn-rtc-e-outcome
                                   fn-rtc-x-delivered-outcome-is fn-rtc-get fn-rtc-e-data fn-rtc-e-data-of-landed fn-rtc-landed-splice-is-identity))
           :use ((:instance fn-rtc-st-p-bytes-octets (h (fn-rtc-h-buf (fn-rtc-u-hd u))))
                 (:instance fn-rtc-x-delivered-in-ok
                            (fl (len (fn-rtc-bytes (fn-rtc-h-buf (fn-rtc-u-hd u)) s))))
                 (:instance fn-rtc-e-data-of-landed)
                 (:instance fn-rtc-landed-splice-is-identity
                            (b (fn-rtc-bytes (fn-rtc-h-buf (fn-rtc-u-hd u)) s)))))))

(defthm fn-rtc-lease-return-landed
  (implies (and (fn-rtc-st-p s) (fn-rtc-completionp e)
                (equal u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))) u)
           (equal (fn-rtc-lease-return u (fn-rtc-landed e s)
                                       (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s) s1)
                  (let* ((b (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s))
                         (o (fn-rtc-b-owner b))
                         (rid (nfix (fn-rtc-get 1 o))) (rinc (fn-rtc-get 2 o))
                         (back (and (fn-rtc-current-p rid rinc s1)
                                    (member-eq (fn-rtc-s-status (fn-rtc-slot rid s1)) '(:live :closing)))))
                    (list (+ 1 (fn-rtc-b-gen b)) (if back (list :workspace rid rinc) '(:free))
                          (fn-rtc-b-bytes b)))))
  :hints (("Goal" :use fn-rtc-lease-return-landed-bytes
           :in-theory (e/d (fn-rtc-lease-return)
                           (fn-rtc-lease-return-landed-bytes fn-rtc-find-use fn-rtc-key fn-rtc-completionp
                            fn-rtc-landed fn-rtc-delivered-outcome fn-rtc-splice fn-rtc-current-p
                            fn-rtc-delivered-outcome-of-landed)))))

(defthm fn-rtc-x-end-lease-is
  (implies (and (fn-rtc-st-p s) (fn-rtc-completionp e)
                (equal u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))) u)
           (equal (fn-rtc-x-end-lease u (fn-rtc-with-uses x s))
                  (fn-rtc-end-lease u (fn-rtc-landed e s) (fn-rtc-with-uses x s))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-x-end-lease fn-rtc-end-lease fn-rtc-st-uses fn-rtc-st-owner
                                   fn-rtc-st-slot fn-rtc-st-gen fn-rtc-st-set-meta)
                                  (fn-rtc-find-use fn-rtc-key fn-rtc-completionp fn-rtc-landed
                                   fn-rtc-lease-return fn-rtc-lease-return-landed-bytes
                                   fn-rtc-delivered-outcome-of-landed fn-rtc-current-p fn-rtc-h-buf fn-rtc-u-hd fn-rtc-h-gen fn-rtc-handlep fn-rtc-holds-p)))))

(defthm fn-rtc-x-end-use-is
  (implies (fn-rtc-st-p fn-rtc-st)
           (equal (fn-rtc-x-end-use e fn-rtc-st) (fn-rtc-end-use fn-rtc-st (fn-rtc-landed e fn-rtc-st))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-x-end-use fn-rtc-end-use fn-rtc-st-uses fn-rtc-st-set-uses)
                                  (fn-rtc-find-use fn-rtc-key fn-rtc-completionp fn-rtc-landed
                                   fn-rtc-end-lease fn-rtc-x-end-lease fn-rtc-retire-drained
                                   fn-rtc-x-retire-drained fn-rtc-e-id)))))


(defthm fn-rtc-st-p-of-spec-end-use
  (implies (fn-rtc-st-p fn-rtc-st)
           (fn-rtc-st-p (fn-rtc-end-use fn-rtc-st (fn-rtc-landed e fn-rtc-st))))
  :hints (("Goal" :use (fn-rtc-x-end-use-is fn-rtc-x-end-use-keeps-st-p)
           :in-theory (union-theories (theory 'minimal-theory) '()))))

(defthm fn-rtc-acts-on-p-of-landed
  (equal (fn-rtc-acts-on-p s (fn-rtc-landed e s)) (fn-rtc-acts-on-p s e))
  :hints (("Goal" :in-theory (e/d (fn-rtc-acts-on-p) (fn-rtc-landed fn-rtc-find-use fn-rtc-key fn-rtc-completionp fn-rtc-e-kind fn-rtc-e-id fn-rtc-e-inc fn-rtc-e-outcome)))))

(defthm fn-rtc-st-fill-is-len-bytes
  (equal (fn-rtc-st-fill h fn-rtc-st) (len (fn-rtc-bytes h fn-rtc-st)))
  :hints (("Goal" :in-theory (enable fn-rtc-st-fill))))

(defthm fn-rtc-st-config-is
  (equal (fn-rtc-st-config fn-rtc-st) (fn-rtc-config fn-rtc-st))
  :hints (("Goal" :in-theory (enable fn-rtc-st-config))))

(defthm fn-rtc-st-uses-is
  (equal (fn-rtc-st-uses fn-rtc-st) (fn-rtc-uses fn-rtc-st))
  :hints (("Goal" :in-theory (enable fn-rtc-st-uses))))

(defthm fn-rtc-x-step*-is
  (implies (fn-rtc-st-p fn-rtc-st)
           (equal (fn-rtc-x-step* e q fn-rtc-st)
                  (fn-rtc-step* fn-rtc-st (fn-rtc-landed e fn-rtc-st) q)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-x-step* fn-rtc-step*)
                                  (fn-rtc-landed fn-rtc-end-use fn-rtc-find-use fn-rtc-key
                                   fn-rtc-delivered-outcome fn-rtc-x-delivered-outcome
                                   fn-rtc-accept-branch fn-rtc-close-branch fn-rtc-deliver fn-rtc-rearm
                                   fn-rtc-get nfix member-equal mv-nth fn-rtc-e-kind fn-rtc-e-id
                                   fn-rtc-e-inc fn-rtc-e-outcome fn-rtc-use-bound fn-rtc-nslots
                                   fn-rtc-nbufs fn-rtc-u-hd fn-rtc-h-buf fn-rtc-h-len)))))

(defthm fn-rtc-x-step-is
  (implies (fn-rtc-st-p fn-rtc-st)
           (equal (fn-rtc-x-step e q fn-rtc-st)
                  (fn-rtc-step fn-rtc-st (fn-rtc-landed e fn-rtc-st) q)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-x-step fn-rtc-step) (fn-rtc-x-step* fn-rtc-step* fn-rtc-landed)))))

(defthm fn-rtc-x-init-is
  (implies (fn-rtc-st-cfg-okp cfg)
           (equal (fn-rtc-x-init cfg fn-rtc-st) (fn-rtc-init cfg)))
  :hints (("Goal" :in-theory (enable fn-rtc-x-init fn-rtc-init fn-rtc-st-init))))
