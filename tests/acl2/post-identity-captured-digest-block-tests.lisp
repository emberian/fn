(in-package "ACL2")
(include-book "../../books/post-identity-captured-digest-block")

; Literal ghost fixture constructors only; no served helper or guard claim.
(defun-nx pic-rft-collector (msg start count pos bytes)
  (fn-pic-set digest-desc '(0 0 0)
    (fn-pic-set block-start start (fn-pic-set block-count count
      (fn-pic-set pos pos (fn-pic-set block bytes
        (fn-pic-set incoming-n (len msg) (make-list 23 :initial-element nil))))))))
(defun-nx pic-rft-block-state (pos end)
  (declare (xargs :stobjs nil :verify-guards nil))
  (update-pgs-dc-mode :chunk (update-pgs-dc-pos pos
    (update-pgs-dc-end end (create-pgs-digest-state)))))

(defthm pic-rft-collector-positive
  (let* ((msg '(65 66 67))
         (c (pic-rft-collector msg 0 3 3 '(67 66 65)))
         (cursor (pic-rft-block-state 0 1)))
    (and (fn-pic-block-prefixp c msg)
         (equal (fn-pic-get pos c) (fn-pic-get block-count c))
         (natp (pgs-dc-pos cursor))
         (natp (pgs-dc-end cursor))
         (equal (fn-pic-get block-start c) (pgs-dcb-next-byte-offset cursor))
         (equal (fn-pic-get block-count c) (pgs-dcb-read-demand (len msg) cursor))
         (pgs-dcs-blockp (fn-pic-digest-block c) msg cursor)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (pic-rft-collector pic-rft-block-state
    fn-pic-block-prefixp pgs-dcs-blockp pgs-dcr-span fn-pic-span-value
    pgs-dcb-next-byte-offset pgs-dcb-read-demand pgs-dc-needs-block pgs-dc-pos pgs-dc-end)
    ((:executable-counterpart pgs-dcb-next-byte-offset)
     (:executable-counterpart pgs-dcb-read-demand)
     (:executable-counterpart pgs-dc-needs-block)
     (:executable-counterpart pgs-dc-pos) (:executable-counterpart pgs-dc-end))))))

(defthm pic-rft-collector-prefix-removal-corrupted-buffer
  (let* ((msg '(65 66 67))
         (c (pic-rft-collector msg 0 3 3 '(0 0 0)))
         (cursor (pic-rft-block-state 0 1)))
    (and (not (fn-pic-block-prefixp c msg))
         (equal (fn-pic-get pos c) (fn-pic-get block-count c))
         (natp (pgs-dc-pos cursor))
         (natp (pgs-dc-end cursor))
         (equal (fn-pic-get block-start c) (pgs-dcb-next-byte-offset cursor))
         (equal (fn-pic-get block-count c) (pgs-dcb-read-demand (len msg) cursor))
         (not (pgs-dcs-blockp (fn-pic-digest-block c) msg cursor))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (pic-rft-collector pic-rft-block-state
    fn-pic-block-prefixp pgs-dcs-blockp pgs-dcr-span fn-pic-span-value
    pgs-dcb-next-byte-offset pgs-dcb-read-demand pgs-dc-needs-block pgs-dc-pos pgs-dc-end)
    ((:executable-counterpart pgs-dcb-next-byte-offset)
     (:executable-counterpart pgs-dcb-read-demand)
     (:executable-counterpart pgs-dc-needs-block)
     (:executable-counterpart pgs-dc-pos) (:executable-counterpart pgs-dc-end))))))

(defthm pic-rft-collector-completion-removal
  (let* ((msg '(65 66 67))
         (c (pic-rft-collector msg 0 3 2 '(66 65)))
         (cursor (pic-rft-block-state 0 1)))
    (and (fn-pic-block-prefixp c msg)
         (not (equal (fn-pic-get pos c) (fn-pic-get block-count c)))
         (natp (pgs-dc-pos cursor))
         (natp (pgs-dc-end cursor))
         (equal (fn-pic-get block-start c) (pgs-dcb-next-byte-offset cursor))
         (equal (fn-pic-get block-count c) (pgs-dcb-read-demand (len msg) cursor))
         (not (pgs-dcs-blockp (fn-pic-digest-block c) msg cursor))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (pic-rft-collector pic-rft-block-state
    fn-pic-block-prefixp pgs-dcs-blockp pgs-dcr-span fn-pic-span-value
    pgs-dcb-next-byte-offset pgs-dcb-read-demand pgs-dc-needs-block pgs-dc-pos pgs-dc-end)
    ((:executable-counterpart pgs-dcb-next-byte-offset)
     (:executable-counterpart pgs-dcb-read-demand)
     (:executable-counterpart pgs-dc-needs-block)
     (:executable-counterpart pgs-dc-pos) (:executable-counterpart pgs-dc-end))))))

(defthm pic-rft-collector-position-natural-removal-corrupted-cursor
  (let* ((msg '(65 66 67 68 69))
         (c (pic-rft-collector msg 1 4 4 '(69 68 67 66)))
         (cursor (pic-rft-block-state 1/8 1)))
    (and (fn-pic-block-prefixp c msg)
         (equal (fn-pic-get pos c) (fn-pic-get block-count c))
         (not (natp (pgs-dc-pos cursor)))
         (natp (pgs-dc-end cursor))
         (equal (fn-pic-get block-start c) (pgs-dcb-next-byte-offset cursor))
         (equal (fn-pic-get block-count c) (pgs-dcb-read-demand (len msg) cursor))
         (not (pgs-dcs-blockp (fn-pic-digest-block c) msg cursor))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (pic-rft-collector pic-rft-block-state
    fn-pic-block-prefixp pgs-dcs-blockp pgs-dcr-span fn-pic-span-value
    pgs-dcb-next-byte-offset pgs-dcb-read-demand pgs-dc-needs-block pgs-dc-pos pgs-dc-end)
    ((:executable-counterpart pgs-dcb-next-byte-offset)
     (:executable-counterpart pgs-dcb-read-demand)
     (:executable-counterpart pgs-dc-needs-block)
     (:executable-counterpart pgs-dc-pos) (:executable-counterpart pgs-dc-end))))))

(defthm pic-rft-collector-end-natural-removal-corrupted-cursor
  (let* ((msg '(65 66 67 68 69))
         (c (pic-rft-collector msg 0 1 1 '(65)))
         (cursor (pic-rft-block-state 0 1/8)))
    (and (fn-pic-block-prefixp c msg)
         (equal (fn-pic-get pos c) (fn-pic-get block-count c))
         (natp (pgs-dc-pos cursor))
         (not (natp (pgs-dc-end cursor)))
         (equal (fn-pic-get block-start c) (pgs-dcb-next-byte-offset cursor))
         (equal (fn-pic-get block-count c) (pgs-dcb-read-demand (len msg) cursor))
         (not (pgs-dcs-blockp (fn-pic-digest-block c) msg cursor))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (pic-rft-collector pic-rft-block-state
    fn-pic-block-prefixp pgs-dcs-blockp pgs-dcr-span fn-pic-span-value
    pgs-dcb-next-byte-offset pgs-dcb-read-demand pgs-dc-needs-block pgs-dc-pos pgs-dc-end)
    ((:executable-counterpart pgs-dcb-next-byte-offset)
     (:executable-counterpart pgs-dcb-read-demand)
     (:executable-counterpart pgs-dc-needs-block)
     (:executable-counterpart pgs-dc-pos) (:executable-counterpart pgs-dc-end))))))

(defthm pic-rft-collector-start-agreement-removal-mutated-demand
  (let* ((msg '(1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16))
         (c (pic-rft-collector msg 0 8 8 '(8 7 6 5 4 3 2 1)))
         (cursor (pic-rft-block-state 1 2)))
    (and (fn-pic-block-prefixp c msg)
         (equal (fn-pic-get pos c) (fn-pic-get block-count c))
         (natp (pgs-dc-pos cursor))
         (natp (pgs-dc-end cursor))
         (not (equal (fn-pic-get block-start c) (pgs-dcb-next-byte-offset cursor)))
         (equal (fn-pic-get block-count c) (pgs-dcb-read-demand (len msg) cursor))
         (not (pgs-dcs-blockp (fn-pic-digest-block c) msg cursor))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (pic-rft-collector pic-rft-block-state
    fn-pic-block-prefixp pgs-dcs-blockp pgs-dcr-span fn-pic-span-value
    pgs-dcb-next-byte-offset pgs-dcb-read-demand pgs-dc-needs-block pgs-dc-pos pgs-dc-end)
    ((:executable-counterpart pgs-dcb-next-byte-offset)
     (:executable-counterpart pgs-dcb-read-demand)
     (:executable-counterpart pgs-dc-needs-block)
     (:executable-counterpart pgs-dc-pos) (:executable-counterpart pgs-dc-end))))))

(defthm pic-rft-collector-count-agreement-removal-mutated-demand
  (let* ((msg '(65 66 67))
         (c (pic-rft-collector msg 0 2 2 '(66 65)))
         (cursor (pic-rft-block-state 0 1)))
    (and (fn-pic-block-prefixp c msg)
         (equal (fn-pic-get pos c) (fn-pic-get block-count c))
         (natp (pgs-dc-pos cursor))
         (natp (pgs-dc-end cursor))
         (equal (fn-pic-get block-start c) (pgs-dcb-next-byte-offset cursor))
         (not (equal (fn-pic-get block-count c) (pgs-dcb-read-demand (len msg) cursor)))
         (not (pgs-dcs-blockp (fn-pic-digest-block c) msg cursor))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (pic-rft-collector pic-rft-block-state
    fn-pic-block-prefixp pgs-dcs-blockp pgs-dcr-span fn-pic-span-value
    pgs-dcb-next-byte-offset pgs-dcb-read-demand pgs-dc-needs-block pgs-dc-pos pgs-dc-end)
    ((:executable-counterpart pgs-dcb-next-byte-offset)
     (:executable-counterpart pgs-dcb-read-demand)
     (:executable-counterpart pgs-dc-needs-block)
     (:executable-counterpart pgs-dc-pos) (:executable-counterpart pgs-dc-end))))))

(defthm pic-rft-collector-improper-source-weakened-positive
  (let* ((msg '(65 66 . improper))
         (c (pic-rft-collector msg 0 2 2 '(66 65)))
         (cursor (pic-rft-block-state 0 1)))
    (and (fn-pic-block-prefixp c msg)
         (equal (fn-pic-get pos c) (fn-pic-get block-count c))
         (natp (pgs-dc-pos cursor))
         (natp (pgs-dc-end cursor))
         (equal (fn-pic-get block-start c) (pgs-dcb-next-byte-offset cursor))
         (equal (fn-pic-get block-count c) (pgs-dcb-read-demand (len msg) cursor))
         (not (true-listp msg))
         (pgs-dcs-blockp (fn-pic-digest-block c) msg cursor)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (pic-rft-collector pic-rft-block-state
    fn-pic-block-prefixp pgs-dcs-blockp pgs-dcr-span fn-pic-span-value
    pgs-dcb-next-byte-offset pgs-dcb-read-demand pgs-dc-needs-block pgs-dc-pos pgs-dc-end)
    ((:executable-counterpart pgs-dcb-next-byte-offset)
     (:executable-counterpart pgs-dcb-read-demand)
     (:executable-counterpart pgs-dc-needs-block)
     (:executable-counterpart pgs-dc-pos) (:executable-counterpart pgs-dc-end))))))

(defthm pic-rft-collector-two-span-full-block-positive
  (let* ((incoming (append '(65 66 67 68 69 70 71 72) (make-list 72 :initial-element 9)))
         (d '(1 4 7)) (msg (fn-pic-span-value d incoming))
         (c (fn-pic-set digest-desc d
              (pic-rft-collector incoming 0 64 64
                (revappend (take 64 (nthcdr 0 msg)) nil))))
         (cursor (pic-rft-block-state 0 10)))
    (and (fn-pic-block-prefixp c incoming)
         (equal (fn-pic-get pos c) (fn-pic-get block-count c))
         (natp (pgs-dc-pos cursor)) (natp (pgs-dc-end cursor))
         (equal (fn-pic-get block-start c) (pgs-dcb-next-byte-offset cursor))
         (equal (fn-pic-get block-count c) (pgs-dcb-read-demand (len msg) cursor))
         (pgs-dcs-blockp (fn-pic-digest-block c) msg cursor)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable pic-rft-collector pic-rft-block-state
    fn-pic-block-prefixp pgs-dcs-blockp pgs-dcr-span fn-pic-span-value))))

(defthm pic-rft-collector-two-span-short-tail-positive
  (let* ((incoming (append '(65 66 67 68 69 70 71 72) (make-list 72 :initial-element 9)))
         (d '(1 4 7)) (msg (fn-pic-span-value d incoming))
         (c (fn-pic-set digest-desc d
              (pic-rft-collector incoming 64 12 12
                (revappend (take 12 (nthcdr 64 msg)) nil))))
         (cursor (pic-rft-block-state 8 10)))
    (and (fn-pic-block-prefixp c incoming)
         (equal (fn-pic-get pos c) (fn-pic-get block-count c))
         (natp (pgs-dc-pos cursor)) (natp (pgs-dc-end cursor))
         (equal (fn-pic-get block-start c) (pgs-dcb-next-byte-offset cursor))
         (equal (fn-pic-get block-count c) (pgs-dcb-read-demand (len msg) cursor))
         (pgs-dcs-blockp (fn-pic-digest-block c) msg cursor)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable pic-rft-collector pic-rft-block-state
    fn-pic-block-prefixp pgs-dcs-blockp pgs-dcr-span fn-pic-span-value))))

(defthm pic-rft-next-prefix-positive
  (let* ((incoming '(65 66 67))
         (c (fn-pic-set phase :digest-read (pic-rft-collector incoming 0 3 0 nil)))
         (next (mv-nth 1 (fn-pic-next c 2 incoming))))
    (and (fn-pic-block-prefixp c incoming)
         (equal (fn-pic-get phase c) :digest-read)
         (fn-pic-block-prefixp next incoming)
         (equal (fn-pic-get pos next) 1)
         (equal (fn-pic-get block next) '(65))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable pic-rft-collector fn-pic-block-prefixp))))

(defthm pic-rft-next-prefix-removal-corrupted-buffer
  (let* ((incoming '(65 66 67))
         (c (fn-pic-set phase :digest-read (pic-rft-collector incoming 0 3 1 nil)))
         (next (mv-nth 1 (fn-pic-next c 2 incoming))))
    (and (not (fn-pic-block-prefixp c incoming))
         (equal (fn-pic-get phase c) :digest-read)
         (not (fn-pic-block-prefixp next incoming))
         (equal (fn-pic-get pos next) 2)
         (equal (fn-pic-get block next) '(66))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable pic-rft-collector fn-pic-block-prefixp))))

; The comparator's reachable tombstone-agent phase shares POS but does not
; collect digest bytes: the digest-read premise is essential to this theorem.
(defthm pic-rft-next-phase-removal-tombstone-agent
  (let* ((incoming '(65 66 67))
         (c (fn-pic-set phase :tomb-agent-incoming
              (fn-pic-set cached 65 (fn-pic-set agent '(:agent 0 3)
                (pic-rft-collector incoming 0 3 0 nil)))))
         (next (mv-nth 1 (fn-pic-next c 2 incoming))))
    (and (fn-pic-block-prefixp c incoming)
         (not (equal (fn-pic-get phase c) :digest-read))
         (not (fn-pic-block-prefixp next incoming))
         (equal (fn-pic-get phase next) :tomb-agent-held)
         (equal (fn-pic-get pos next) 1)
         (equal (fn-pic-get block next) nil)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable pic-rft-collector fn-pic-block-prefixp))))

; Ghost fixture for actual demand entry, no served allocation or guard claim.
(defun-nx pic-rft-demand-cursor (n pos)
  (declare (xargs :stobjs nil :verify-guards nil))
  (update-pgs-dc-mode :chunk (update-pgs-dc-pos pos (pgs-dcb-begin 0 0 n nil nil (create-pgs-digest-state)))))

(defthm pic-rft-demand-positive
  (let* ((incoming '(65 66 67))
         (c (fn-pic-set phase :digest-next (pic-rft-collector incoming 0 0 0 nil)))
         (cursor (pic-rft-demand-cursor 3 0))
         (next (mv-nth 1 (fn-pic-digest-next c 2 cursor))))
    (and (equal (fn-pic-get phase c) :digest-next)
         (fn-pic-spanp (fn-pic-get digest-desc c) (len incoming))
         (equal (fn-pic-get incoming-n c) (len incoming))
         (equal (fn-pic-get phase next) :digest-read)
         (and (fn-pic-block-prefixp next incoming)
             (equal (fn-pic-get block-start next) (pgs-dcb-next-byte-offset cursor))
             (equal (fn-pic-get block-count next)
               (pgs-dcb-read-demand (len (fn-pic-span-value (fn-pic-get digest-desc c) incoming)) cursor))
             (equal (mv-nth 3 (fn-pic-digest-next c 2 cursor)) cursor))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (pic-rft-collector pic-rft-demand-cursor
    fn-pic-digest-next fn-pic-digest-effect fn-pic-digest-scalar-guardp
    fn-pic-feed-funded fn-pic-feed fn-pic-demand fn-pic-observation-okp
    fn-pic-block-prefixp pgs-dcb-next-byte-offset pgs-dcb-read-demand
    pgs-dc-needs-block pgs-dc-pos pgs-dc-end)
    ((:executable-counterpart fn-pic-digest-next)
     (:executable-counterpart fn-pic-digest-effect)
     (:executable-counterpart fn-pic-digest-scalar-guardp)
     (:executable-counterpart pgs-dcb-next-byte-offset)
     (:executable-counterpart pgs-dcb-read-demand)
     (:executable-counterpart pgs-dc-needs-block)
     (:executable-counterpart pgs-dc-pos) (:executable-counterpart pgs-dc-end))))))

(defthm pic-rft-demand-phase-removal
  (let* ((incoming '(65 66 67))
         (c (fn-pic-set phase :digest-read (pic-rft-collector incoming 0 3 1 nil)))
         (cursor (pic-rft-demand-cursor 3 0))
         (next (mv-nth 1 (fn-pic-digest-next c 2 cursor))))
    (and (not (equal (fn-pic-get phase c) :digest-next))
         (fn-pic-spanp (fn-pic-get digest-desc c) (len incoming))
         (equal (fn-pic-get incoming-n c) (len incoming))
         (equal (fn-pic-get phase next) :digest-read)
         (not (and (fn-pic-block-prefixp next incoming)
             (equal (fn-pic-get block-start next) (pgs-dcb-next-byte-offset cursor))
             (equal (fn-pic-get block-count next)
               (pgs-dcb-read-demand (len (fn-pic-span-value (fn-pic-get digest-desc c) incoming)) cursor))
             (equal (mv-nth 3 (fn-pic-digest-next c 2 cursor)) cursor)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (pic-rft-collector pic-rft-demand-cursor
    fn-pic-digest-next fn-pic-digest-effect fn-pic-digest-scalar-guardp
    fn-pic-feed-funded fn-pic-feed fn-pic-demand fn-pic-observation-okp
    fn-pic-block-prefixp pgs-dcb-next-byte-offset pgs-dcb-read-demand
    pgs-dc-needs-block pgs-dc-pos pgs-dc-end)
    ((:executable-counterpart fn-pic-digest-next)
     (:executable-counterpart fn-pic-digest-effect)
     (:executable-counterpart fn-pic-digest-scalar-guardp)
     (:executable-counterpart pgs-dcb-next-byte-offset)
     (:executable-counterpart pgs-dcb-read-demand)
     (:executable-counterpart pgs-dc-needs-block)
     (:executable-counterpart pgs-dc-pos) (:executable-counterpart pgs-dc-end))))))

(defthm pic-rft-demand-span-removal-corrupted-descriptor
  (let* ((incoming '(65 66 67))
         (c (fn-pic-set phase :digest-next (fn-pic-set digest-desc '(0 4 2) (pic-rft-collector incoming 0 0 0 nil))))
         (cursor (pic-rft-demand-cursor 5 0))
         (next (mv-nth 1 (fn-pic-digest-next c 2 cursor))))
    (and (equal (fn-pic-get phase c) :digest-next)
         (not (fn-pic-spanp (fn-pic-get digest-desc c) (len incoming)))
         (equal (fn-pic-get incoming-n c) (len incoming))
         (equal (fn-pic-get phase next) :digest-read)
         (not (and (fn-pic-block-prefixp next incoming)
             (equal (fn-pic-get block-start next) (pgs-dcb-next-byte-offset cursor))
             (equal (fn-pic-get block-count next)
               (pgs-dcb-read-demand (len (fn-pic-span-value (fn-pic-get digest-desc c) incoming)) cursor))
             (equal (mv-nth 3 (fn-pic-digest-next c 2 cursor)) cursor)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (pic-rft-collector pic-rft-demand-cursor
    fn-pic-digest-next fn-pic-digest-effect fn-pic-digest-scalar-guardp
    fn-pic-feed-funded fn-pic-feed fn-pic-demand fn-pic-observation-okp
    fn-pic-block-prefixp pgs-dcb-next-byte-offset pgs-dcb-read-demand
    pgs-dc-needs-block pgs-dc-pos pgs-dc-end)
    ((:executable-counterpart fn-pic-digest-next)
     (:executable-counterpart fn-pic-digest-effect)
     (:executable-counterpart fn-pic-digest-scalar-guardp)
     (:executable-counterpart pgs-dcb-next-byte-offset)
     (:executable-counterpart pgs-dcb-read-demand)
     (:executable-counterpart pgs-dc-needs-block)
     (:executable-counterpart pgs-dc-pos) (:executable-counterpart pgs-dc-end))))))

(defthm pic-rft-demand-extent-removal-mutated-context
  (let* ((incoming '(65 66 67))
         (c (fn-pic-set phase :digest-next (fn-pic-set incoming-n 4 (pic-rft-collector incoming 0 0 0 nil))))
         (cursor (pic-rft-demand-cursor 4 0))
         (next (mv-nth 1 (fn-pic-digest-next c 2 cursor))))
    (and (equal (fn-pic-get phase c) :digest-next)
         (fn-pic-spanp (fn-pic-get digest-desc c) (len incoming))
         (not (equal (fn-pic-get incoming-n c) (len incoming)))
         (equal (fn-pic-get phase next) :digest-read)
         (not (and (fn-pic-block-prefixp next incoming)
             (equal (fn-pic-get block-start next) (pgs-dcb-next-byte-offset cursor))
             (equal (fn-pic-get block-count next)
               (pgs-dcb-read-demand (len (fn-pic-span-value (fn-pic-get digest-desc c) incoming)) cursor))
             (equal (mv-nth 3 (fn-pic-digest-next c 2 cursor)) cursor)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (pic-rft-collector pic-rft-demand-cursor
    fn-pic-digest-next fn-pic-digest-effect fn-pic-digest-scalar-guardp
    fn-pic-feed-funded fn-pic-feed fn-pic-demand fn-pic-observation-okp
    fn-pic-block-prefixp pgs-dcb-next-byte-offset pgs-dcb-read-demand
    pgs-dc-needs-block pgs-dc-pos pgs-dc-end)
    ((:executable-counterpart fn-pic-digest-next)
     (:executable-counterpart fn-pic-digest-effect)
     (:executable-counterpart fn-pic-digest-scalar-guardp)
     (:executable-counterpart pgs-dcb-next-byte-offset)
     (:executable-counterpart pgs-dcb-read-demand)
     (:executable-counterpart pgs-dc-needs-block)
     (:executable-counterpart pgs-dc-pos) (:executable-counterpart pgs-dc-end))))))
