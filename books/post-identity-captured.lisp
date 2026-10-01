; Captured-row semantic confirmation over retained provider/holder tokens.
; The actual owner boundary must join provider and holder lease invariants.
; No independent resource account: every activation consumes the caller's
; remaining scheduling fuel.  Group tails and strings are retained aliases.
(in-package "ACL2")
(include-book "octets-stobj")
(include-book "held-record")
(include-book "post-identity-source-cursor-invariants")
(include-book "pagestore-digest-byte-cursor")
(include-book "reclaim-tombstone")

(defun fn-pic-at (i x)
  (declare (xargs :guard (natp i)))
  (if (zp i) (if (consp x) (car x) nil)
    (if (consp x) (fn-pic-at (1- i) (cdr x)) nil)))

(defun fn-pic-groups-begin (left right)
  (declare (xargs :guard t))
  (list :continue left right 0))

(defun fn-pic-groups-step (s)
  (declare (xargs :guard t))
  (let ((word (fn-pic-at 0 s))
        (left (fn-pic-at 1 s)) (right (fn-pic-at 2 s))
        (i (nfix (fn-pic-at 3 s))))
    (if (not (equal word :continue)) s
      (cond ((and (null left) (null right)) (list :equal left right i))
            ((or (null left) (null right)) (list :different left right i))
            ((not (and (consp left) (consp right)
                       (stringp (car left)) (stringp (car right))))
             (list :invalid-groups left right i))
            ((not (equal (length (car left)) (length (car right))))
             (list :different left right i))
            ((< (length (car left)) i) (list :invalid-groups left right i))
            ((equal i (length (car left)))
             (list :continue (cdr left) (cdr right) 0))
            ((equal (char (car left) i) (char (car right) i))
             (list :continue left right (1+ i)))
            (t (list :different left right i))))))

; Proof-only suffix denotation, never a served operation.
(defun fn-pic-string-tail-equal (a b i)
  (equal (nthcdr (nfix i) (coerce a 'list))
         (nthcdr (nfix i) (coerce b 'list))))

(defun fn-pic-groups-value (s)
  (let ((left (fn-pic-at 1 s)) (right (fn-pic-at 2 s))
        (i (nfix (fn-pic-at 3 s))))
    (if (and (consp left) (consp right)
             (stringp (car left)) (stringp (car right)))
        (and (fn-pic-string-tail-equal (car left) (car right) i)
             (equal (cdr left) (cdr right)))
      (equal left right))))

(defun fn-pic-groups-advance (s fuel)
  (declare (xargs :guard t :measure (nfix fuel)))
  (if (or (zp (nfix fuel)) (not (equal (fn-pic-at 0 s) :continue)))
      (mv (if (equal (fn-pic-at 0 s) :continue) :yield (fn-pic-at 0 s))
          s (nfix fuel))
    (fn-pic-groups-advance (fn-pic-groups-step s) (1- (nfix fuel)))))

(defthm fn-pic-groups-advance-fuel-bounded
  (and (natp (mv-nth 2 (fn-pic-groups-advance s fuel)))
       (<= (mv-nth 2 (fn-pic-groups-advance s fuel)) (nfix fuel)))
  :hints (("Goal" :induct (fn-pic-groups-advance s fuel))))

(defthm fn-pic-groups-zero-fuel-yields-unchanged
  (implies (equal (fn-pic-at 0 s) :continue)
           (and (equal (mv-nth 0 (fn-pic-groups-advance s 0)) :yield)
                (equal (mv-nth 1 (fn-pic-groups-advance s 0)) s))))

(local
 (defthm fn-pic-coerce-injective
   (implies (and (stringp a) (stringp b))
            (equal (equal (coerce a 'list) (coerce b 'list)) (equal a b)))
   :hints (("Goal" :in-theory (disable coerce-inverse-2)
            :use ((:instance coerce-inverse-2 (x a))
                  (:instance coerce-inverse-2 (x b)))))))

(defthm fn-pic-groups-begin-denotes-exact-equality
  (equal (fn-pic-groups-value (fn-pic-groups-begin left right))
         (equal left right))
  :hints (("Goal" :in-theory (enable fn-pic-groups-begin fn-pic-groups-value
                                   fn-pic-string-tail-equal fn-pic-at))))

(local
 (defthm fn-pic-coerce-true-listp
   (true-listp (coerce s 'list))
   :hints (("Goal" :use (:instance completion-of-coerce (x s) (y 'list))))))
(local
 (defthm fn-pic-tail-at-end
   (implies (and (true-listp x) (natp i) (<= (len x) i))
            (equal (nthcdr i x) nil))
   :hints (("Goal" :induct (nthcdr i x) :in-theory (enable nthcdr)))))
(local
 (defun fn-pic-pair-ind (i x y)
   (if (zp i) (list x y) (fn-pic-pair-ind (1- i) (cdr x) (cdr y)))))
(local
 (defthm fn-pic-equal-tail-step
   (implies (and (natp i) (< i (len x)) (< i (len y))
                 (equal (nth i x) (nth i y)))
            (equal (equal (nthcdr i x) (nthcdr i y))
                   (equal (nthcdr (1+ i) x) (nthcdr (1+ i) y))))
   :hints (("Goal" :induct (fn-pic-pair-ind i x y)
            :in-theory (enable nthcdr nth)))))
(local
 (defthm fn-pic-string-tail-zero
   (implies (and (stringp a) (stringp b))
            (equal (fn-pic-string-tail-equal a b 0) (equal a b)))))
(local
 (defthm fn-pic-string-tail-end
   (implies (and (stringp a) (stringp b) (equal (length a) (length b))
                 (equal (nfix i) (length a)))
            (fn-pic-string-tail-equal a b i))
   :hints (("Goal" :in-theory (e/d (fn-pic-string-tail-equal length) (nthcdr))))))
(local
 (defthm fn-pic-string-tail-step
   (implies (and (stringp a) (stringp b) (natp i)
                 (< i (length a)) (< i (length b))
                 (equal (char a i) (char b i)))
            (equal (fn-pic-string-tail-equal a b (1+ i))
                   (fn-pic-string-tail-equal a b i)))
   :hints (("Goal" :in-theory (e/d (fn-pic-string-tail-equal char length)
                                   (nthcdr nth fn-pic-coerce-injective))))))
(local
 (defthm fn-pic-empty-list
   (implies (and (true-listp x) (equal (len x) 0)) (equal x nil))
   :rule-classes nil))
(local
 (defthm fn-pic-empty-string
   (implies (and (stringp s) (equal (length s) 0))
            (equal (coerce s 'list) nil))
   :hints (("Goal" :use (:instance fn-pic-empty-list (x (coerce s 'list)))))))
(local
 (defthm fn-pic-empty-strings-equal
   (implies (and (stringp a) (stringp b)
                 (equal (length a) 0) (equal (length b) 0))
            (equal (equal a b) t))
   :hints (("Goal" :in-theory (disable fn-pic-coerce-injective)
            :use (:instance fn-pic-coerce-injective)))))

(defthm fn-pic-groups-step-preserves-value
  (implies (equal (fn-pic-at 0 (fn-pic-groups-step s)) :continue)
           (equal (fn-pic-groups-value (fn-pic-groups-step s))
                  (fn-pic-groups-value s)))
  :hints (("Goal" :in-theory (e/d (fn-pic-groups-step fn-pic-groups-value fn-pic-at)
                                  (fn-pic-string-tail-equal length char)))))

(defthm fn-pic-groups-step-equal-is-value
  (implies (and (equal (fn-pic-at 0 s) :continue)
                (equal (fn-pic-at 0 (fn-pic-groups-step s)) :equal))
           (fn-pic-groups-value s)))

(defthm fn-pic-groups-advance-equal-is-value
  (implies (and (equal (fn-pic-at 0 s) :continue)
                (equal (mv-nth 0 (fn-pic-groups-advance s fuel)) :equal))
           (fn-pic-groups-value s))
  :hints (("Goal" :induct (fn-pic-groups-advance s fuel)
           :in-theory (disable fn-pic-at fn-pic-groups-step fn-pic-groups-value))
          ("Subgoal *1/2"
           :cases ((equal (fn-pic-at 0 (fn-pic-groups-step s)) :continue)))))

(defthm fn-pic-groups-completion-confirms-exact-groups
  (implies (equal (mv-nth 0 (fn-pic-groups-advance
                            (fn-pic-groups-begin left right) fuel)) :equal)
           (equal left right))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-pic-groups-advance-equal-is-value
                                 (s (fn-pic-groups-begin left right)))
                       (:instance fn-pic-groups-begin-denotes-exact-equality))
           :in-theory (e/d (fn-pic-groups-begin) (fn-pic-groups-advance
                             fn-pic-groups-value fn-pic-groups-advance-equal-is-value
                             fn-pic-groups-begin-denotes-exact-equality)))))

; Logical validity predicate: carried by the comparison theorem, never
; evaluated on a served continuation or used to rescan retained groups.
(defun fn-pic-string-listp (x)
  (if (consp x) (and (stringp (car x)) (fn-pic-string-listp (cdr x)))
    (null x)))
(defun fn-pic-groups-validp (s)
  (let ((left (fn-pic-at 1 s)) (right (fn-pic-at 2 s)) (i (fn-pic-at 3 s)))
    (and (fn-pic-string-listp left) (fn-pic-string-listp right) (natp i)
         (if (and (consp left) (consp right))
             (and (<= i (length (car left))) (<= i (length (car right))))
           (equal i 0)))))

(defthm fn-pic-groups-step-preserves-validp
  (implies (and (fn-pic-groups-validp s)
                (equal (fn-pic-at 0 (fn-pic-groups-step s)) :continue))
           (fn-pic-groups-validp (fn-pic-groups-step s)))
  :hints (("Goal" :in-theory (enable fn-pic-groups-validp fn-pic-groups-step fn-pic-at))))
(local
 (defthm fn-pic-len-tail
   (implies (natp i) (equal (len (nthcdr i x)) (nfix (- (len x) i))))
   :hints (("Goal" :induct (nthcdr i x) :in-theory (enable nthcdr)))))
(local
 (defthm fn-pic-string-tail-different-length
   (implies (and (stringp a) (stringp b) (natp i)
                 (<= i (length a)) (<= i (length b))
                 (not (equal (length a) (length b))))
            (not (fn-pic-string-tail-equal a b i)))
   :hints (("Goal" :in-theory (e/d (fn-pic-string-tail-equal length)
                                   (nthcdr fn-pic-len-tail fn-pic-coerce-injective))
            :use ((:instance fn-pic-len-tail (x (coerce a 'list)))
                  (:instance fn-pic-len-tail (x (coerce b 'list))))))))
(local
 (defthm fn-pic-car-tail
   (equal (car (nthcdr i x)) (nth i x))
   :hints (("Goal" :induct (nthcdr i x) :in-theory (enable nthcdr nth)))))
(local
 (defthm fn-pic-string-tail-different-char
   (implies (and (stringp a) (stringp b) (natp i)
                 (not (equal (char a i) (char b i))))
            (not (fn-pic-string-tail-equal a b i)))
   :hints (("Goal" :in-theory (e/d (fn-pic-string-tail-equal char)
                                   (nthcdr fn-pic-car-tail fn-pic-coerce-injective))
            :use ((:instance fn-pic-car-tail (x (coerce a 'list)))
                  (:instance fn-pic-car-tail (x (coerce b 'list))))))))
(defthm fn-pic-groups-step-different-is-not-value
  (implies (and (fn-pic-groups-validp s) (equal (fn-pic-at 0 s) :continue)
                (equal (fn-pic-at 0 (fn-pic-groups-step s)) :different))
           (not (fn-pic-groups-value s)))
  :hints (("Goal" :in-theory (e/d (fn-pic-groups-validp fn-pic-groups-step
                                   fn-pic-groups-value fn-pic-at)
                                  (fn-pic-string-tail-equal length char)))))
(defthm fn-pic-groups-advance-different-is-not-value
  (implies (and (fn-pic-groups-validp s) (equal (fn-pic-at 0 s) :continue)
                (equal (mv-nth 0 (fn-pic-groups-advance s fuel)) :different))
           (not (fn-pic-groups-value s)))
  :hints (("Goal" :induct (fn-pic-groups-advance s fuel)
           :in-theory (disable fn-pic-at fn-pic-groups-step fn-pic-groups-value
                               fn-pic-groups-validp))
          ("Subgoal *1/2"
           :cases ((equal (fn-pic-at 0 (fn-pic-groups-step s)) :continue)))))
(defthm fn-pic-groups-begin-is-valid
  (implies (and (fn-pic-string-listp left) (fn-pic-string-listp right))
           (fn-pic-groups-validp (fn-pic-groups-begin left right))))
(local
 (defthm fn-pic-equal-tails-step-does-not-differ
   (implies (and (equal (fn-pic-at 1 s) (fn-pic-at 2 s))
                 (equal (fn-pic-at 0 s) :continue))
     (and (not (equal (fn-pic-at 0 (fn-pic-groups-step s)) :different))
          (implies (equal (fn-pic-at 0 (fn-pic-groups-step s)) :continue)
                   (equal (fn-pic-at 1 (fn-pic-groups-step s))
                          (fn-pic-at 2 (fn-pic-groups-step s))))))
   :hints (("Goal" :in-theory (enable fn-pic-groups-step fn-pic-at)))))
(local
 (defthm fn-pic-equal-tails-advance-does-not-differ
   (implies (and (equal (fn-pic-at 1 s) (fn-pic-at 2 s))
                 (equal (fn-pic-at 0 s) :continue))
     (not (equal (mv-nth 0 (fn-pic-groups-advance s fuel)) :different)))
   :hints (("Goal" :induct (fn-pic-groups-advance s fuel)
                   :in-theory (disable fn-pic-groups-step fn-pic-at))
           ("Subgoal *1/2" :cases ((equal (fn-pic-at 0 (fn-pic-groups-step s)) :continue))))))
(defthm fn-pic-groups-completion-rejects-different-groups
  (implies (equal (mv-nth 0 (fn-pic-groups-advance
                            (fn-pic-groups-begin left right) fuel)) :different)
           (not (equal left right)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-pic-equal-tails-advance-does-not-differ
                           (s (fn-pic-groups-begin left right))))
           :in-theory (e/d (fn-pic-groups-begin fn-pic-at)
             (fn-pic-groups-advance fn-pic-groups-step fn-pic-equal-tails-advance-does-not-differ)))))

; The inverse describes a source as [K,A) followed by [B,N).  The same
; descriptor describes a whole payload with K=A=B=0.  Fixed-width scalar
; mapping is shared by comparison and the existing BLAKE3 cursor adapter.
(defun fn-pic-spanp (d n)
  (declare (xargs :guard t))
  (let ((k (fn-pic-at 0 d)) (a (fn-pic-at 1 d)) (b (fn-pic-at 2 d)))
    (and (consp d) (consp (cdr d)) (consp (cddr d))
         (natp k) (natp a) (natp b) (natp n)
         (<= k a) (<= a b) (<= b n))))
(defun fn-pic-span-length (d n)
  (declare (xargs :guard t))
  (+ (nfix (- (nfix (fn-pic-at 1 d)) (nfix (fn-pic-at 0 d))))
     (nfix (- (nfix n) (nfix (fn-pic-at 2 d))))))
(defun fn-pic-span-offset (d i)
  (declare (xargs :guard t))
  (let ((k (nfix (fn-pic-at 0 d))) (a (nfix (fn-pic-at 1 d)))
        (b (nfix (fn-pic-at 2 d))) (i (nfix i)))
    (if (< i (nfix (- a k))) (+ k i)
      (+ b (- i (nfix (- a k)))))))
(defun fn-pic-span-value (d xs)
  ; Ghost denotation only: this operation never executes on the served path.
  (append (take (nfix (- (nfix (fn-pic-at 1 d)) (nfix (fn-pic-at 0 d))))
                (nthcdr (nfix (fn-pic-at 0 d)) xs))
          (nthcdr (nfix (fn-pic-at 2 d)) xs)))
(defthm fn-pic-span-offset-is-within-source
  (implies (and (fn-pic-spanp d n) (natp i) (< i (fn-pic-span-length d n)))
           (and (natp (fn-pic-span-offset d i))
                (< (fn-pic-span-offset d i) n)))
  :hints (("Goal" :in-theory (enable fn-pic-spanp fn-pic-span-length
                                   fn-pic-span-offset))))

(local
 (defthm fn-pic-nth-append
   (implies (natp i)
            (equal (nth i (append x y))
                   (if (< i (len x)) (nth i x) (nth (- i (len x)) y))))
   :hints (("Goal" :induct (nth i x) :in-theory (enable nth binary-append)))))
(local
 (defun fn-pic-take-ind (n i x)
   (if (or (zp n) (zp i)) x (fn-pic-take-ind (1- n) (1- i) (cdr x)))))
(local
 (defthm fn-pic-nth-take
   (implies (and (natp n) (natp i) (< i n))
            (equal (nth i (take n x)) (nth i x)))
   :hints (("Goal" :induct (fn-pic-take-ind n i x) :in-theory (enable nth take))
           ("Subgoal *1/1" :expand ((take n x))))))
(local
 (defthm fn-pic-len-take
   (implies (natp n) (equal (len (take n x)) n))))
(local
 (defthm fn-pic-nth-tail
   (implies (and (natp i) (natp j))
            (equal (nth i (nthcdr j x)) (nth (+ i j) x)))
   :hints (("Goal" :induct (nthcdr j x) :in-theory (enable nth nthcdr)))))
(defthm fn-pic-span-byte-is-denoted-byte
  (implies (and (fn-pic-spanp d (len xs)) (natp i)
                (< i (fn-pic-span-length d (len xs))))
           (equal (nth i (fn-pic-span-value d xs))
                  (nth (fn-pic-span-offset d i) xs)))
  :hints (("Goal" :in-theory (e/d (fn-pic-spanp fn-pic-span-length
                                   fn-pic-span-value fn-pic-span-offset)
                                  (nth nthcdr take)))))

; At most one BLAKE3 block is materialized.  COUNT is a demand issued by
; the existing digest continuation, funded from the caller's remaining
; fuel.  fn-octets is read-only; no whole input/list/source allocation.
(defun fn-pic-incoming-block (d start count fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (fn-pic-spanp d (fn-octets-len fn-octets))
                              (natp start) (natp count) (<= count 64)
                              (<= (+ start count)
                                  (fn-pic-span-length d (fn-octets-len fn-octets))))
                  :measure (nfix count)))
  (if (zp count) nil
    (cons (fn-octets-get (fn-pic-span-offset d start) fn-octets)
          (fn-pic-incoming-block d (1+ start) (1- count) fn-octets))))

(defthm fn-pic-incoming-block-length
  (equal (len (fn-pic-incoming-block d start count fn-octets)) (nfix count))
  :hints (("Goal" :induct (fn-pic-incoming-block d start count fn-octets))))

(local
 (defthm fn-pic-cdr-tail
   (implies (natp i) (equal (cdr (nthcdr i x)) (nthcdr (1+ i) x)))
   :hints (("Goal" :induct (nthcdr i x) :in-theory (enable nthcdr)))))

; The host-callable block reader returns exactly the virtual source slice
; that the existing digest cursor's pgs-dcs-blockp premise requires.
(defthm fn-pic-incoming-block-is-denoted-slice
  (implies (and (fn-pic-spanp d (len fn-octets)) (natp start) (natp count)
                (<= (+ start count) (fn-pic-span-length d (len fn-octets))))
           (equal (fn-pic-incoming-block d start count fn-octets)
                  (take count (nthcdr start (fn-pic-span-value d fn-octets)))))
  :hints (("Goal" :induct (fn-pic-incoming-block d start count fn-octets)
           :in-theory (e/d (fn-pic-incoming-block fn-octets-get take)
                            (fn-pic-span-value fn-pic-span-offset fn-pic-spanp
                             fn-pic-span-length nth nthcdr))
           :expand ((take count (nthcdr start (fn-pic-span-value d fn-octets)))))))

; Captured SAME controller. Only the provider-selected held reference enters
; BEGIN. The program boundary validates provider/holder leases on every resume.
; Variable payloads, agents and group lists are retained aliases or spans.
(defmacro fn-pic-get (field c)
  (list 'fn-pic-at (cdr (assoc-eq field '((phase . 0) (selected . 1) (grant . 2)
    (held . 3) (incoming-token . 4) (incoming-n . 5) (held-n . 6)
    (msgid . 7) (groups . 8) (parser . 9) (agent . 10) (incoming-desc . 11)
    (held-desc . 12) (pos . 13) (cached . 14) (result . 15)
    (digest-base . 16) (digest-desc . 17) (digest . 18) (group-cursor . 19)
    (block-start . 20) (block-count . 21) (block . 22)))) c))
(defmacro fn-pic-set (field value c)
  (list 'update-nth (cdr (assoc-eq field '((phase . 0) (selected . 1) (grant . 2)
    (held . 3) (incoming-token . 4) (incoming-n . 5) (held-n . 6)
    (msgid . 7) (groups . 8) (parser . 9) (agent . 10) (incoming-desc . 11)
    (held-desc . 12) (pos . 13) (cached . 14) (result . 15)
    (digest-base . 16) (digest-desc . 17) (digest . 18) (group-cursor . 19)
    (block-start . 20) (block-count . 21) (block . 22)))) value c))
(defun fn-pic-finish (result c)
  (declare (xargs :guard (true-listp c)))
  (fn-pic-set phase :done (fn-pic-set result result c)))
(defun fn-pic-begin (selected grant held incoming-token incoming-n msgid binding groups)
  (declare (xargs :guard (natp incoming-n)))
  ; Gate precedes every held payload/group projection.
  (let* ((gate (fn-ab-held-binding-action msgid binding held))
         (c (list :held-length selected grant held incoming-token incoming-n 0
                  msgid groups nil '(:agent 0 0) nil nil 0 nil :pending
                  9 '(0 0 0) nil nil 0 0 nil)))
    (if (equal gate :same-binding) c (fn-pic-finish gate c))))
(defun fn-pic-parser (c)
  (declare (xargs :guard t))
  (let ((p (fn-pic-get parser c))) (if (true-listp p) p nil)))
(defun fn-pic-start-parser (mode phase c)
  (declare (xargs :guard (true-listp c)))
  (fn-pic-set phase phase
    (fn-pic-set parser
      (fn-psc-begin mode (if (equal mode :source-held)
                            (nfix (fn-pic-get held-n c))
                          (nfix (fn-pic-get incoming-n c)))
                    (fn-pic-get msgid c)
                    (let ((a (fn-pic-get agent c))) (if (true-listp a) a nil))
                    (nfix (fn-pic-get incoming-n c))) c)))
(defun fn-pic-source-result (r n)
  (declare (xargs :guard t))
  (let ((d (list (fn-pic-at 1 r) (fn-pic-at 2 r) (fn-pic-at 3 r))))
    (if (and (equal (fn-pic-at 0 r) :source) (fn-pic-spanp d n)) d nil)))
(defun fn-pic-groups-start (c)
  (declare (xargs :guard (true-listp c)))
  (fn-pic-set phase :groups
    (fn-pic-set group-cursor
      (fn-pic-groups-begin (fn-pic-get groups c)
                           (fn-record-groups (fn-pic-get held c))) c)))
(defun fn-pic-compare-start (c)
  (declare (xargs :guard (true-listp c)))
  (let* ((id (fn-pic-get incoming-desc c)) (hd (fn-pic-get held-desc c))
         (both (and id hd))
         (id (if both id '(0 0 0))) (hd (if both hd '(0 0 0)))
         (c (fn-pic-set incoming-desc id (fn-pic-set held-desc hd c))))
    (if (not (equal (fn-pic-span-length id (fn-pic-get incoming-n c))
                    (fn-pic-span-length hd (fn-pic-get held-n c))))
        (fn-pic-finish :conflict c)
      (fn-pic-set phase :compare-incoming (fn-pic-set pos 0 c)))))
(defun fn-pic-hash-start (sourcep c)
  (declare (xargs :guard (true-listp c)))
  (fn-pic-set phase :digest-begin
    (fn-pic-set digest-base (if sourcep 41 9)
      (fn-pic-set digest-desc (if sourcep (fn-pic-get incoming-desc c) '(0 0 0)) c))))

(defun fn-pic-demand (c)
  (declare (xargs :guard t))
  (let* ((phase (fn-pic-get phase c)) (i (nfix (fn-pic-get pos c)))
         (d (fn-pic-get incoming-desc c)))
    (case phase
      (:done :none)
      (:held-length :held-length)
      ((:agent :source-incoming :source-held) (fn-psc-demand (fn-pic-parser c)))
      (:magic (if (< i 8) (list :held i) :control))
      (:tomb-flag '(:held 8))
      (:tomb-agent-held
        (if (< i (nfix (- (nfix (fn-pic-get held-n c)) *fn-rcl-tombstone-fixed*)))
            (list :held (+ *fn-rcl-tombstone-fixed* i)) :control))
      (:tomb-agent-incoming
        (list :incoming (+ (nfix (fn-pic-at 1 (fn-pic-get agent c))) i)))
      (:compare-incoming
        (if (< i (fn-pic-span-length d (fn-pic-get incoming-n c)))
            (list :incoming (fn-pic-span-offset d i)) :control))
      (:compare-held (list :held (fn-pic-span-offset (fn-pic-get held-desc c) i)))
      (:digest-begin (list :digest-begin (fn-pic-get digest-desc c)))
      (:digest-next :digest-next)
      (:digest-read
        (if (< i (nfix (fn-pic-get block-count c)))
            (list :incoming (fn-pic-span-offset (fn-pic-get digest-desc c)
                             (+ (nfix (fn-pic-get block-start c)) i))) :control))
      (:digest-commit (list :digest-step (fn-pic-get block c)))
      (:digest-compare
        (if (< i 32) (list :held (+ (nfix (fn-pic-get digest-base c)) i)) :control))
      (:groups :control)
      (otherwise :invalid))))

; Every byte observation binds the original token and exact requested offset.
; The boundary supplies observations from the readonly concrete stobj APIs.
(defun fn-pic-observation-okp (c demand observation)
  (declare (xargs :guard t))
  (let ((kind (fn-pic-at 0 demand)) (i (fn-pic-at 1 demand))
        (tag (fn-pic-at 0 observation)))
    (cond
      ((equal demand :control) (equal observation :control))
      ((equal demand :held-length)
       (and (equal tag :payload-length)
            (equal (fn-pic-at 1 observation) (fn-pic-get selected c))
            (equal (fn-pic-at 2 observation) (fn-pic-get grant c))
            (equal (fn-pic-at 3 observation) (fn-record-payload (fn-pic-get held c)))
            (natp (fn-pic-at 4 observation))))
      ((equal kind :held)
       (and (equal tag :payload-byte)
            (equal (fn-pic-at 1 observation) (fn-pic-get selected c))
            (equal (fn-pic-at 2 observation) (fn-pic-get grant c))
            (equal (fn-pic-at 3 observation) (fn-record-payload (fn-pic-get held c)))
            (equal (fn-pic-at 4 observation) i)
            (natp i) (< i (nfix (fn-pic-get held-n c)))
            (unsigned-byte-p 8 (fn-pic-at 5 observation))))
      ((equal kind :incoming)
       (and (equal tag :incoming-byte)
            (equal (fn-pic-at 1 observation) (fn-pic-get incoming-token c))
            (equal (fn-pic-at 2 observation) i)
            (natp i) (< i (nfix (fn-pic-get incoming-n c)))
            (unsigned-byte-p 8 (fn-pic-at 3 observation))))
      ((equal kind :digest-begin) (equal observation :digest-started))
      ((equal demand :digest-next)
       (or (and (equal tag :digest-demand)
                (natp (fn-pic-at 1 observation)) (natp (fn-pic-at 2 observation))
                (<= (fn-pic-at 2 observation) 64)
                (<= (+ (fn-pic-at 1 observation) (fn-pic-at 2 observation))
                    (fn-pic-span-length (fn-pic-get digest-desc c) (fn-pic-get incoming-n c))))
           (and (equal tag :digest-result) (true-listp (fn-pic-at 1 observation))
                (equal (len (fn-pic-at 1 observation)) 32))))
      ((equal kind :digest-step) (equal observation :digest-stepped))
      (t nil))))
(defun fn-pic-observed-byte (d observation)
  (declare (xargs :guard t))
  (if (equal (fn-pic-at 0 d) :held) (fn-pic-at 5 observation)
    (fn-pic-at 3 observation)))

(defun fn-pic-block-add (c byte)
  (declare (xargs :guard (true-listp c)))
  (fn-pic-set pos (+ 1 (nfix (fn-pic-get pos c)))
    (fn-pic-set block (cons byte (fn-pic-get block c)) c)))

(defun fn-pic-feed (c observation)
  (declare (xargs :guard (true-listp c)
                  :guard-hints (("Goal" :in-theory
                    (disable fn-pic-at fn-pic-demand fn-pic-observation-okp
                      fn-pic-observed-byte fn-pic-source-result fn-pic-spanp
                      fn-pic-span-length fn-pic-span-offset fn-pic-groups-step)))))
  (let* ((phase (fn-pic-get phase c)) (demand (fn-pic-demand c))
         (i (nfix (fn-pic-get pos c)))
         (byte (fn-pic-observed-byte demand observation)))
    (cond
      ((equal phase :done) c)
      ((not (fn-pic-observation-okp c demand observation))
       (fn-pic-finish :refused c))
      ((equal phase :held-length)
       (fn-pic-start-parser :agent :agent
         (fn-pic-set held-n (fn-pic-at 4 observation) c)))
      ((member-eq phase '(:agent :source-incoming :source-held))
       (let* ((p (fn-psc-step (fn-pic-parser c) byte))
              (r (fn-psc-result p)) (c (fn-pic-set parser p c)))
         (cond ((equal r :pending) c)
               ((equal phase :agent)
                (fn-pic-start-parser :source-incoming :source-incoming
                  (fn-pic-set agent
                    (if (and (equal (fn-pic-at 0 r) :agent)
                             (natp (fn-pic-at 1 r)) (natp (fn-pic-at 2 r))
                             (<= (fn-pic-at 1 r) (fn-pic-at 2 r))
                             (<= (fn-pic-at 2 r) (nfix (fn-pic-get incoming-n c))))
                        (list :agent (fn-pic-at 1 r) (fn-pic-at 2 r)) '(:agent 0 0)) c)))
               ((equal phase :source-incoming)
                (let ((c (fn-pic-set incoming-desc
                           (fn-pic-source-result r (fn-pic-get incoming-n c)) c)))
                  (if (< (nfix (fn-pic-get held-n c)) *fn-rcl-tombstone-fixed*)
                      (fn-pic-start-parser :source-held :source-held c)
                    (fn-pic-set phase :magic (fn-pic-set pos 0 c)))))
               (t (fn-pic-compare-start
                    (fn-pic-set held-desc (fn-pic-source-result r (fn-pic-get held-n c)) c))))))
      ((equal phase :magic)
       (cond ((>= i 8) (fn-pic-set phase :tomb-flag c))
             ((equal byte (nth i *fn-rcl-magic*)) (fn-pic-set pos (+ i 1) c))
             (t (fn-pic-start-parser :source-held :source-held c))))
      ((equal phase :tomb-flag)
       (if (and (equal byte 1) (fn-pic-get incoming-desc c)
                (equal (- (nfix (fn-pic-at 2 (fn-pic-get agent c)))
                           (nfix (fn-pic-at 1 (fn-pic-get agent c))))
                       (- (nfix (fn-pic-get held-n c)) *fn-rcl-tombstone-fixed*)))
           (fn-pic-set phase :tomb-agent-held (fn-pic-set pos 0 c))
         (fn-pic-hash-start nil c)))
      ((equal phase :tomb-agent-held)
       (if (equal demand :control) (fn-pic-hash-start t c)
         (fn-pic-set phase :tomb-agent-incoming (fn-pic-set cached byte c))))
      ((equal phase :tomb-agent-incoming)
       (if (equal byte (fn-pic-get cached c))
           (fn-pic-set phase :tomb-agent-held (fn-pic-set pos (+ i 1) c))
         (fn-pic-hash-start nil c)))
      ((equal phase :compare-incoming)
       (if (equal demand :control) (fn-pic-groups-start c)
         (fn-pic-set phase :compare-held (fn-pic-set cached byte c))))
      ((equal phase :compare-held)
       (if (equal byte (fn-pic-get cached c))
           (fn-pic-set phase :compare-incoming (fn-pic-set pos (+ i 1) c))
         (fn-pic-finish :conflict c)))
      ((equal phase :digest-begin) (fn-pic-set phase :digest-next c))
      ((equal phase :digest-next)
       (if (equal (fn-pic-at 0 observation) :digest-result)
           (fn-pic-set phase :digest-compare (fn-pic-set pos 0
             (fn-pic-set digest (fn-pic-at 1 observation) c)))
         (fn-pic-set phase :digest-read (fn-pic-set pos 0
           (fn-pic-set block-start (fn-pic-at 1 observation)
             (fn-pic-set block-count (fn-pic-at 2 observation) (fn-pic-set block nil c)))))))
      ((equal phase :digest-read)
       (if (equal demand :control) (fn-pic-set phase :digest-commit c)
         (fn-pic-block-add c byte)))
      ((equal phase :digest-commit) (fn-pic-set phase :digest-next c))
      ((equal phase :digest-compare)
       (cond ((equal demand :control) (fn-pic-groups-start c))
             ((equal byte (fn-pic-at i (fn-pic-get digest c))) (fn-pic-set pos (+ i 1) c))
             (t (fn-pic-finish :conflict c))))
      ((equal phase :groups)
       (let* ((g (fn-pic-groups-step (fn-pic-get group-cursor c)))
              (status (fn-pic-at 0 g)))
         (if (equal status :continue) (fn-pic-set group-cursor g c)
           (fn-pic-finish (case status (:equal :duplicate) (:different :conflict)
                                (otherwise :recovery-required)) (fn-pic-set group-cursor g c)))))
      (t (fn-pic-finish :refused c)))))

; The effect feeder and concrete incoming reader share the caller's fuel.
; Held/digest effects are supplied only by the ACL2 program boundary.
(defun fn-pic-feed-funded (c observation fuel)
  (declare (xargs :guard (and (true-listp c) (natp fuel))))
  (if (zp fuel) (mv :yield c fuel)
    (let ((next (fn-pic-feed c observation)))
      (mv (if (equal (fn-pic-get phase next) :done) (fn-pic-get result next) :continue)
          next (- fuel 1)))))
(defun fn-pic-next (c fuel fn-octets)
  (declare (xargs :stobjs fn-octets :guard (and (true-listp c) (natp fuel))))
  (let* ((d (fn-pic-demand c)) (i (fn-pic-at 1 d)))
    (cond ((equal d :none) (mv (fn-pic-get result c) c fuel))
          ((zp fuel) (mv :yield c fuel))
          ((not (equal (nfix (fn-pic-get incoming-n c)) (fn-octets-len fn-octets)))
           (mv :refused (fn-pic-finish :refused c) (- fuel 1)))
          ((equal d :control) (fn-pic-feed-funded c :control fuel))
          ((equal (fn-pic-at 0 d) :incoming)
           (cond ((< fuel 2) (mv :yield c fuel))
                 ((not (and (natp i) (< i (fn-octets-len fn-octets))))
                  (mv :refused (fn-pic-finish :refused c) (- fuel 1)))
                 (t (fn-pic-feed-funded c
                      (list :incoming-byte (fn-pic-get incoming-token c) i
                            (fn-octets-get i fn-octets)) (- fuel 1)))))
          (t (mv :demand c fuel)))))

(defthm fn-pic-feed-funded-zero-yields-unchanged
  (equal (mv-list 3 (fn-pic-feed-funded c observation 0)) (list :yield c 0)))
(defthm fn-pic-feed-funded-fuel-bounded
  (implies (natp fuel)
    (and (natp (mv-nth 2 (fn-pic-feed-funded c observation fuel)))
         (<= (mv-nth 2 (fn-pic-feed-funded c observation fuel)) fuel)))
  :hints (("Goal" :in-theory (e/d (fn-pic-feed-funded) (fn-pic-feed fn-pic-at)))))

; Digest effects use the existing page byte cursor. A block is accumulated
; one concrete incoming-byte observation per funded step, at most64 bytes.
; Only the fixed-value little-endian formatter executes at block commit.
(defun fn-pic-digest-scalar-guardp (n pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :guard (natp n)))
  (and (equal (pgs-dc-total pgs-digest-state) (pgs-dcb-word-count n))
       (<= (pgs-dc-start pgs-digest-state) (pgs-dc-pos pgs-digest-state))
       (<= (pgs-dc-pos pgs-digest-state) (pgs-dc-end pgs-digest-state))
       (<= (pgs-dc-end pgs-digest-state) (pgs-dc-total pgs-digest-state))
       (<= (* 8 (pgs-dc-pos pgs-digest-state)) n)))
(defun fn-pic-reverse-block (x n acc)
  (declare (xargs :guard t :measure (nfix n)))
  (if (or (zp (nfix n)) (not (consp x))) acc
    (fn-pic-reverse-block (cdr x) (- (nfix n) 1) (cons (car x) acc))))
(defun fn-pic-digest-block (c)
  (declare (xargs :guard t))
  (fn-b3-words 16 (fn-pic-reverse-block (fn-pic-get block c) 64 nil)))
(defun fn-pic-digest-effect (c fuel pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state
                  :guard (and (true-listp c) (natp fuel))
                  :guard-hints (("Goal" :in-theory (enable fn-pic-digest-scalar-guardp)))))
  (let* ((phase (fn-pic-get phase c))
         (n (fn-pic-span-length (fn-pic-get digest-desc c) (fn-pic-get incoming-n c))))
    (cond ((zp fuel) (mv :yield nil fuel pgs-digest-state))
          ((equal phase :digest-begin)
           (let ((pgs-digest-state
                  (pgs-dcb-begin 0 0 n (fn-pic-get selected c) (fn-pic-get grant c) pgs-digest-state)))
             (mv :ready :digest-started (- fuel 1) pgs-digest-state)))
          ((not (and (equal (pgs-dc-capture pgs-digest-state) (fn-pic-get selected c))
                     (equal (pgs-dc-lease pgs-digest-state) (fn-pic-get grant c))
                     (fn-pic-digest-scalar-guardp n pgs-digest-state)))
           (mv :refused nil (- fuel 1) pgs-digest-state))
          ((equal phase :digest-next)
           (if (eq (pgs-dc-mode pgs-digest-state) :done)
               (mv :ready (list :digest-result (pgs-dcb-result-octets pgs-digest-state))
                   (- fuel 1) pgs-digest-state)
             (mv :ready (list :digest-demand (pgs-dcb-next-byte-offset pgs-digest-state)
                              (pgs-dcb-read-demand n pgs-digest-state))
                 (- fuel 1) pgs-digest-state)))
          ((equal phase :digest-commit)
           (mv-let (status pgs-digest-state)
             (pgs-dcb-step n (fn-pic-digest-block c) pgs-digest-state)
             (if (member-eq status '(:continue :done))
                 (mv :ready :digest-stepped (- fuel 1) pgs-digest-state)
               (mv :refused nil (- fuel 1) pgs-digest-state))))
          (t (mv :refused nil (- fuel 1) pgs-digest-state)))))

(local
 (defthm fn-pic-at-is-nth
   (implies (natp i) (equal (fn-pic-at i x) (nth i x)))
   :hints (("Goal" :induct (fn-pic-at i x) :in-theory (enable fn-pic-at nth)))))

; Proof-only collector denotation. The live block is bounded by64 bytes;
; neither this predicate nor its virtual-message construction is served.
(defun fn-pic-block-prefixp (c incoming)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((d (fn-pic-get digest-desc c)) (start (fn-pic-get block-start c))
         (i (fn-pic-get pos c)) (count (fn-pic-get block-count c)))
    (and (fn-pic-spanp d (len incoming)) (natp start) (natp i) (natp count)
         (<= i count) (<= count 64)
         (<= (+ start count) (fn-pic-span-length d (len incoming)))
         (equal (fn-pic-get block c)
                (revappend (take i (nthcdr start (fn-pic-span-value d incoming))) nil)))))
(local
 (defun fn-pic-rev-take-ind (i x acc)
   (if (zp i) acc
     (fn-pic-rev-take-ind (- i 1) (cdr x) (cons (car x) acc)))))
(local
 (defthm fn-pic-rev-take-successor
   (implies (natp i)
     (equal (revappend (take (+ i 1) x) acc)
            (cons (nth i x) (revappend (take i x) acc))))
   :hints (("Goal" :induct (fn-pic-rev-take-ind i x acc)
                   :in-theory (e/d (take revappend nth) (revappend-removal))))))

; This is the actual collector update used by FN-PIC-FEED. Its premise
; ties the supplied byte to the immutable virtual source, rather than merely
; asserting that it is an octet or that the eventual hash has length32.
(defthm fn-pic-block-add-preserves-prefix
  (implies (and (fn-pic-block-prefixp c incoming)
                (< (fn-pic-get pos c) (fn-pic-get block-count c))
                (equal byte
                  (nth (+ (fn-pic-get block-start c) (fn-pic-get pos c))
                       (fn-pic-span-value (fn-pic-get digest-desc c) incoming))))
           (fn-pic-block-prefixp (fn-pic-block-add c byte) incoming))
  :hints (("Goal"
           :use ((:instance fn-pic-rev-take-successor
                   (i (fn-pic-get pos c)) (acc nil)
                   (x (nthcdr (fn-pic-get block-start c)
                        (fn-pic-span-value (fn-pic-get digest-desc c) incoming))))
                 (:instance fn-pic-nth-tail
                   (i (fn-pic-get pos c)) (j (fn-pic-get block-start c))
                   (x (fn-pic-span-value (fn-pic-get digest-desc c) incoming))))
           :in-theory (e/d (fn-pic-block-prefixp fn-pic-block-add)
                            (fn-pic-at fn-pic-span-value fn-pic-spanp fn-pic-span-length
                             fn-pic-span-offset fn-pic-span-byte-is-denoted-byte
                             nth nthcdr take revappend)))))
(local
 (defthm fn-pic-reverse-block-is-revappend
   (implies (and (true-listp x) (natp n) (<= (len x) n))
            (equal (fn-pic-reverse-block x n acc) (revappend x acc)))
   :hints (("Goal" :induct (fn-pic-reverse-block x n acc)
                   :in-theory (e/d (fn-pic-reverse-block revappend) (revappend-removal))))))
(local
 (defthm fn-pic-revappend-twice
   (equal (revappend (revappend x y) z) (revappend y (append x z)))
   :hints (("Goal" :induct (revappend x y) :in-theory (e/d (revappend binary-append) (revappend-removal))))))
(local (defthm fn-pic-take-true-listp (true-listp (take n x))))
(local (defthm fn-pic-revappend-true-listp
         (implies (true-listp y) (true-listp (revappend x y)))))
(local (defthm fn-pic-len-revappend
         (equal (len (revappend x y)) (+ (len x) (len y)))))
(local
 (defthm fn-pic-reverse-bounded-prefix
   (implies (and (equal block (revappend xs nil)) (true-listp xs) (<= (len xs) 64))
            (equal (fn-pic-reverse-block block 64 nil) xs))
   :hints (("Goal" :in-theory (disable fn-pic-reverse-block)))))
(defthm fn-pic-reverse-completed-block-is-denoted-slice
  (implies (and (fn-pic-block-prefixp c incoming)
                (equal (fn-pic-get pos c) (fn-pic-get block-count c)))
    (equal (fn-pic-reverse-block (fn-pic-get block c) 64 nil)
           (take (fn-pic-get block-count c)
             (nthcdr (fn-pic-get block-start c)
               (fn-pic-span-value (fn-pic-get digest-desc c) incoming)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-pic-reverse-bounded-prefix
                   (block (fn-pic-get block c))
                   (xs (take (fn-pic-get pos c)
                         (nthcdr (fn-pic-get block-start c)
                           (fn-pic-span-value (fn-pic-get digest-desc c) incoming))))))
           :in-theory (e/d (fn-pic-block-prefixp)
             (fn-pic-at fn-pic-span-value fn-pic-spanp fn-pic-span-length
              fn-pic-span-byte-is-denoted-byte fn-pic-span-offset fn-pic-reverse-block
              nth nthcdr take revappend binary-append)))))
; The formatter called by DIGEST-EFFECT is exactly the supplied16-word
; block required by pgs-dcs-blockp for this immutable virtual message.
(defthm fn-pic-digest-block-is-denoted-block
  (implies (and (fn-pic-block-prefixp c incoming)
                (equal (fn-pic-get pos c) (fn-pic-get block-count c)))
    (equal (fn-pic-digest-block c)
      (fn-b3-words 16 (take (fn-pic-get block-count c)
        (nthcdr (fn-pic-get block-start c)
          (fn-pic-span-value (fn-pic-get digest-desc c) incoming))))))
  :rule-classes nil
  :hints (("Goal" :use fn-pic-reverse-completed-block-is-denoted-slice
                   :in-theory (e/d (fn-pic-digest-block)
                     (fn-pic-reverse-block fn-b3-words fn-pic-block-prefixp
                      fn-pic-span-value nthcdr take)))))

; Atomic digest effect+feedback. Reserve one transition unit before the
; mutating digest step so a yield cannot repeat an already-consumed block.
(defun fn-pic-digest-next (c fuel pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state
                  :guard (and (true-listp c) (natp fuel))))
  (if (< fuel 2) (mv :yield c fuel pgs-digest-state)
    (mv-let (status observation left pgs-digest-state)
      (fn-pic-digest-effect c (- fuel 1) pgs-digest-state)
      (if (and (equal status :ready) (natp left) (<= left (- fuel 1)))
          (mv-let (word next remaining)
            (fn-pic-feed-funded c observation (+ 1 left))
            (mv word next remaining pgs-digest-state))
        (mv status c (+ 1 (nfix left)) pgs-digest-state)))))

; Carried authorization subject only. This fixed list retains aliases; its
; equality occurs in proofs/tests, never as runtime held/group revalidation.
(defun fn-pic-captured-context (c)
  (declare (xargs :guard t))
  (list (fn-pic-get selected c) (fn-pic-get grant c) (fn-pic-get held c)
        (fn-pic-get incoming-token c) (fn-pic-get incoming-n c)
        (fn-pic-get msgid c) (fn-pic-get groups c)))
(local
 (defthm fn-pic-context-of-update-other-field
   (implies (and (natp i) (not (member-equal i '(1 2 3 4 5 7 8))))
            (equal (fn-pic-captured-context (update-nth i value c))
                   (fn-pic-captured-context c)))
   :hints (("Goal" :in-theory (e/d (fn-pic-captured-context) (fn-pic-at update-nth nth))))))
(defthm fn-pic-feed-preserves-captured-row-and-input
  (equal (fn-pic-captured-context (fn-pic-feed c observation))
         (fn-pic-captured-context c))
  :hints (("Goal" :in-theory
            (e/d (fn-pic-feed fn-pic-finish fn-pic-start-parser fn-pic-groups-start
                   fn-pic-compare-start fn-pic-hash-start fn-pic-block-add)
                 (fn-pic-captured-context fn-pic-at fn-pic-demand fn-pic-observation-okp
                  fn-pic-observed-byte fn-pic-parser fn-pic-source-result
                  fn-pic-spanp fn-pic-span-length fn-pic-span-offset fn-pic-groups-step
                  nth update-nth nfix)))))

; These are the actual readonly incoming and mutating digest entry subjects,
; rather than only a property of the subordinate effect feeder.
(defthm fn-pic-next-preserves-captured-row-and-input
  (equal (fn-pic-captured-context (mv-nth 1 (fn-pic-next c fuel fn-octets)))
         (fn-pic-captured-context c))
  :hints (("Goal" :in-theory
            (e/d (fn-pic-next fn-pic-feed-funded fn-pic-finish)
                 (fn-pic-feed fn-pic-captured-context fn-pic-at fn-pic-demand
                  fn-pic-observation-okp fn-octets-get nth update-nth)))))
(defthm fn-pic-digest-next-preserves-captured-row-and-input
  (equal (fn-pic-captured-context
           (mv-nth 1 (fn-pic-digest-next c fuel pgs-digest-state)))
         (fn-pic-captured-context c))
  :hints (("Goal" :in-theory
            (e/d (fn-pic-digest-next fn-pic-feed-funded)
                 (fn-pic-feed fn-pic-digest-effect fn-pic-captured-context)))))
(defthm fn-pic-next-fuel-bounded
  (implies (natp fuel)
    (and (natp (mv-nth 2 (fn-pic-next c fuel fn-octets)))
         (<= (mv-nth 2 (fn-pic-next c fuel fn-octets)) fuel)))
  :hints (("Goal" :in-theory
            (e/d (fn-pic-next fn-pic-feed-funded)
                 (fn-pic-feed fn-pic-at fn-pic-demand
                  fn-pic-finish fn-octets-get)))))
(defthm fn-pic-digest-next-fuel-bounded
  (implies (natp fuel)
    (and (natp (mv-nth 2 (fn-pic-digest-next c fuel pgs-digest-state)))
         (<= (mv-nth 2 (fn-pic-digest-next c fuel pgs-digest-state)) fuel)))
  :hints (("Goal" :in-theory
            (e/d (fn-pic-digest-next fn-pic-digest-effect fn-pic-feed-funded)
                 (fn-pic-feed fn-pic-at fn-pic-span-length
                  fn-pic-digest-scalar-guardp fn-pic-digest-block
                  pgs-dcb-begin pgs-dcb-step pgs-dcb-next-byte-offset
                  pgs-dcb-read-demand pgs-dcb-result-octets)))))
