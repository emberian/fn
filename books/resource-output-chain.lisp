; PRF-1259: proof-only free-chain witness for actual output custody methods.
; No served-path scan, no executable admission authority. A witness names
; reusable idle rows and their exact terminating links; installation
; completeness (every reusable row occurs) is a separate obligation.
(in-package "ACL2")
(include-book "resource-output")

(defun fn-rlo-chain-rows-p (rows count phases gens ids)
 (declare (xargs :guard t :verify-guards nil))
 (if (atom rows) (equal rows nil)
  (let ((slot (car rows)))
   (and (natp slot) (<= 2 slot) (< slot count)
        (equal (nth slot phases) 0)
        (natp (nth slot gens)) (< (nth slot gens) *fn-rl-word-max*)
        (equal (nth slot ids) (if (consp (cdr rows)) (cadr rows) 0))
        (not (member-equal slot (cdr rows)))
        (fn-rlo-chain-rows-p (cdr rows) count phases gens ids)))))

(defun-nx fn-rlo-free-chainp (rows ledger)
 (declare (xargs :guard t :verify-guards nil))
 (and (equal (fn-rl-next ledger) (if (consp rows) (car rows) 0))
      (fn-rlo-chain-rows-p rows (fn-rl-count ledger)
       (nth 3 ledger) (nth 4 ledger) (nth 14 ledger))))

(defun fn-rlo-free-range (start count)
 (declare (xargs :guard t :verify-guards nil :measure (nfix (- (nfix count) (nfix start)))))
 (if (and (natp start) (natp count) (< start count))
     (cons start (fn-rlo-free-range (+ 1 start) count)) nil))

(defun fn-rlo-reusable-range-p (start count phases gens)
 (declare (xargs :guard t :verify-guards nil :measure (nfix (- (nfix count) (nfix start)))))
 (if (and (natp start) (natp count) (< start count))
     (and (equal (nth start phases) 0)
          (natp (nth start gens)) (< (nth start gens) *fn-rl-word-max*)
          (fn-rlo-reusable-range-p (+ 1 start) count phases gens)) t))

(encapsulate ()
(local (defthm fn-rlo-chain-frame-phase-generation
 (implies (and (natp slot) (not (member-equal slot rows)))
  (equal (fn-rlo-chain-rows-p rows count (update-nth slot phase phases)
           (update-nth slot gen gens) ids)
         (fn-rlo-chain-rows-p rows count phases gens ids)))
 :hints (("Goal" :induct (fn-rlo-chain-rows-p rows count phases gens ids)
  :in-theory (enable fn-rlo-chain-rows-p)))))

(local (defthm fn-rlo-chain-pop-head
 (implies (and (consp rows) (fn-rlo-chain-rows-p rows count phases gens ids))
  (fn-rlo-chain-rows-p (cdr rows) count (update-nth (car rows) phase phases)
           (update-nth (car rows) gen gens) ids))
 :hints (("Goal" :use ((:instance fn-rlo-chain-frame-phase-generation
  (slot (car rows)) (rows (cdr rows))))
  :in-theory (e/d (fn-rlo-chain-rows-p) (fn-rlo-chain-frame-phase-generation update-nth member-equal))))))

(local (defthm fn-rlo-chain-charge-frame
 (implies (member-equal field '(2 3 4 14 20))
  (equal (nth field (fn-rl-charge-from i slot demand ledger)) (nth field ledger)))
 :hints (("Goal" :induct (fn-rl-charge-from i slot demand ledger)
  :in-theory (e/d (fn-rl-charge-from fn-rl-update-ci) (nth update-nth))))))

(local (defthm fn-rlo-issue-chain-columns
 (implies (eq (car (fn-rlo-issue cid cgen opgen dependency ledger)) :drawn)
  (let* ((slot (fn-rl-next ledger))
         (after (mv-nth 2 (fn-rlo-issue cid cgen opgen dependency ledger))))
   (and (natp slot)
    (equal (nth 2 after) (nth 2 ledger))
    (equal (nth 3 after) (update-nth slot 1 (nth 3 ledger)))
    (equal (nth 4 after) (update-nth slot (+ 1 (nth slot (nth 4 ledger))) (nth 4 ledger)))
    (equal (nth 14 after) (nth 14 ledger))
    (equal (fn-rl-next after) (nth slot (nth 14 ledger))))))
 :hints (("Goal" :in-theory
  (e/d (fn-rlo-issue fn-rl-draw fn-rl-charge fn-rl-slotp fn-rl-count
        fn-rl-next fn-rl-idsi fn-rl-gensi fn-rl-phasesi)
       (fn-rlo-ready-p fn-rlo-resident-vector fn-rl-file-limit
        fn-rl-fits-from fn-rl-charge-from nth update-nth))))))

(local (defthm fn-rlo-chain-members-idle
 (implies (and (fn-rlo-chain-rows-p rows count phases gens ids)
               (member-equal slot rows))
  (equal (nth slot phases) 0))
 :hints (("Goal" :induct (fn-rlo-chain-rows-p rows count phases gens ids)
  :in-theory (enable fn-rlo-chain-rows-p)))))

(local (defthm fn-rlo-chain-release-frame
 (implies (member-equal field '(2 3 4 14 20))
  (equal (nth field (fn-rl-release-from i slot mask ledger)) (nth field ledger)))
 :hints (("Goal" :induct (fn-rl-release-from i slot mask ledger)
  :in-theory (e/d (fn-rl-release-from fn-rl-update-ci) (nth update-nth))))))

(local (defthm fn-rlo-settled-chain-columns
 (implies (eq (car (fn-rlo-settle-ready slot ledger)) :settled)
  (let ((after (mv-nth 1 (fn-rlo-settle-ready slot ledger))))
   (and (natp slot)
    (< slot (nth 2 ledger))
    (equal (nth slot (nth 3 ledger)) 1)
    (equal (nth 2 after) (nth 2 ledger))
    (equal (nth 3 after) (update-nth slot 0 (nth 3 ledger)))
    (equal (nth 4 after) (nth 4 ledger))
    (equal (nth 14 after)
     (if (< (nth slot (nth 4 ledger)) *fn-rl-word-max*)
       (update-nth slot (nth 20 ledger) (nth 14 ledger)) (nth 14 ledger)))
    (equal (nth 20 after)
     (if (< (nth slot (nth 4 ledger)) *fn-rl-word-max*) slot (nth 20 ledger))))))
 :hints (("Goal" :in-theory
  (e/d (fn-rlo-settle-ready fn-rl-settle fn-rl-slotp fn-rl-count
        fn-rl-next fn-rl-idsi fn-rl-gensi fn-rl-phasesi fn-rl-elensi fn-rl-trailersi)
       (fn-rl-release-from nth update-nth))))))

(local (defthm fn-rlo-chain-frame-phase-link
 (implies (and (natp slot) (not (member-equal slot rows)))
  (equal (fn-rlo-chain-rows-p rows count (update-nth slot phase phases)
           gens (update-nth slot link ids))
         (fn-rlo-chain-rows-p rows count phases gens ids)))
 :hints (("Goal" :induct (fn-rlo-chain-rows-p rows count phases gens ids)
  :in-theory (enable fn-rlo-chain-rows-p)))))

(local (defthm fn-rlo-chain-frame-phase
 (implies (and (natp slot) (not (member-equal slot rows)))
  (equal (fn-rlo-chain-rows-p rows count (update-nth slot phase phases) gens ids)
         (fn-rlo-chain-rows-p rows count phases gens ids)))
 :hints (("Goal" :induct (fn-rlo-chain-rows-p rows count phases gens ids)
  :in-theory (enable fn-rlo-chain-rows-p)))))

(local (defthm fn-rlo-settled-chain-is-returned-row
 (implies (and (fn-rlo-free-chainp rows ledger) (<= 2 slot)
               (natp (fn-rl-gensi slot ledger))
               (eq (car (fn-rlo-settle-ready slot ledger)) :settled))
  (fn-rlo-free-chainp
   (if (< (fn-rl-gensi slot ledger) *fn-rl-word-max*) (cons slot rows) rows)
   (mv-nth 1 (fn-rlo-settle-ready slot ledger))))
 :hints (("Goal"
  :use ((:instance fn-rlo-settled-chain-columns)
        (:instance fn-rlo-chain-members-idle (count (nth 2 ledger))
           (phases (nth 3 ledger)) (gens (nth 4 ledger)) (ids (nth 14 ledger)))
        (:instance fn-rlo-chain-frame-phase-link (count (nth 2 ledger))
           (phases (nth 3 ledger)) (gens (nth 4 ledger)) (ids (nth 14 ledger))
           (phase 0) (link (nth 20 ledger)))
        (:instance fn-rlo-chain-frame-phase (count (nth 2 ledger))
           (phases (nth 3 ledger)) (gens (nth 4 ledger)) (ids (nth 14 ledger)) (phase 0)))
  :in-theory (e/d (fn-rlo-free-chainp fn-rlo-chain-rows-p fn-rl-count fn-rl-next fn-rl-gensi)
   (fn-rlo-settled-chain-columns fn-rlo-chain-members-idle
    fn-rlo-chain-frame-phase-link fn-rlo-chain-frame-phase fn-rlo-settle-ready update-nth nth member-equal))))))

(local (defthm fn-rlo-live-has-reusable-row-domain
 (implies (fn-rlo-livep token opgen ledger)
  (and (<= 2 (caddr token)) (natp (fn-rl-gensi (caddr token) ledger))))
 :hints (("Goal" :in-theory (e/d (fn-rlo-livep fn-rlo-tokenp) (fn-rlo-ready-p fn-rl-gensi fn-rl-count fn-rl-phasesi fn-rl-cidsi fn-rl-filesi fn-rl-eoffsi))))))

(local (defthm fn-rlo-elens-gens-frame
 (equal (fn-rl-gensi i (update-fn-rl-elensi slot val ledger)) (fn-rl-gensi i ledger))
 :hints (("Goal" :in-theory (e/d (fn-rl-gensi update-fn-rl-elensi) (nth update-nth))))))

(local (defthm fn-rlo-trailers-gens-frame
 (equal (fn-rl-gensi i (update-fn-rl-trailersi slot val ledger)) (fn-rl-gensi i ledger))
 :hints (("Goal" :in-theory (e/d (fn-rl-gensi update-fn-rl-trailersi) (nth update-nth))))))

(local (defthm fn-rlo-free-chain-elens-frame
 (equal (fn-rlo-free-chainp rows (update-fn-rl-elensi slot value ledger))
        (fn-rlo-free-chainp rows ledger))
 :hints (("Goal" :in-theory (e/d (fn-rlo-free-chainp fn-rl-next fn-rl-count update-fn-rl-elensi)
  (fn-rlo-chain-rows-p nth update-nth))))))

(local (defthm fn-rlo-free-chain-trailers-frame
 (equal (fn-rlo-free-chainp rows (update-fn-rl-trailersi slot value ledger))
        (fn-rlo-free-chainp rows ledger))
 :hints (("Goal" :in-theory (e/d (fn-rlo-free-chainp fn-rl-next fn-rl-count update-fn-rl-trailersi)
  (fn-rlo-chain-rows-p nth update-nth))))))

(local (defthm fn-rlo-chain-head-link
 (implies (and (consp rows) (fn-rlo-chain-rows-p rows count phases gens ids))
  (equal (nth (car rows) ids) (if (consp (cdr rows)) (cadr rows) 0)))
 :hints (("Goal" :in-theory (enable fn-rlo-chain-rows-p)))))
(local (defthm fn-rlo-drawn-head-not-zero
 (implies (eq (car (fn-rlo-issue cid cgen opgen dependency ledger)) :drawn)
          (not (equal (fn-rl-next ledger) 0)))
 :hints (("Goal" :in-theory (e/d (fn-rlo-issue)
  (fn-rlo-ready-p fn-rl-next fn-rl-count fn-rl-idsi fn-rl-file-limit fn-rl-draw
   update-fn-rl-next update-fn-rl-cidsi update-fn-rl-filesi update-fn-rl-eoffsi update-fn-rl-elensi update-fn-rl-trailersi))))))

(defthm fn-rlo-issued-chain-is-tail
 (implies (and (fn-rlo-free-chainp rows ledger)
               (eq (car (fn-rlo-issue cid cgen opgen dependency ledger)) :drawn))
  (fn-rlo-free-chainp (cdr rows)
    (mv-nth 2 (fn-rlo-issue cid cgen opgen dependency ledger))))
 :hints (("Goal"
  :use ((:instance fn-rlo-issue-chain-columns)
        (:instance fn-rlo-drawn-head-not-zero)
        (:instance fn-rlo-chain-head-link (count (nth 2 ledger)) (phases (nth 3 ledger)) (gens (nth 4 ledger)) (ids (nth 14 ledger)))
        (:instance fn-rlo-chain-pop-head (count (nth 2 ledger))
           (phases (nth 3 ledger)) (gens (nth 4 ledger)) (ids (nth 14 ledger))
           (phase 1) (gen (+ 1 (nth (fn-rl-next ledger) (nth 4 ledger))))))
  :in-theory (e/d (fn-rlo-free-chainp fn-rl-count fn-rl-next)
   (fn-rlo-issue-chain-columns fn-rlo-chain-pop-head fn-rlo-chain-head-link fn-rlo-drawn-head-not-zero fn-rlo-issue fn-rlo-chain-rows-p fn-rl-draw fn-rlo-ready-p
    update-nth nth fn-rl-idsi fn-rl-file-limit fn-rlo-resident-vector)))))
(defthm fn-rlo-output-settled-chain
 (implies (and (fn-rlo-free-chainp rows ledger)
               (eq (car (fn-rlo-output token opgen receipt ledger)) :settled))
  (fn-rlo-free-chainp
   (if (< (fn-rl-gensi (caddr token) ledger) *fn-rl-word-max*) (cons (caddr token) rows) rows)
   (mv-nth 1 (fn-rlo-output token opgen receipt ledger))))
 :hints (("Goal"
  :use ((:instance fn-rlo-live-has-reusable-row-domain)
        (:instance fn-rlo-settled-chain-is-returned-row
       (slot (caddr token)) (ledger (update-fn-rl-elensi (caddr token) 1 ledger))))
  :in-theory (e/d (fn-rlo-output)
   (fn-rlo-settled-chain-is-returned-row fn-rlo-live-has-reusable-row-domain fn-rlo-free-chainp fn-rlo-settle-ready fn-rlo-livep fn-rlo-tokenp update-fn-rl-elensi update-fn-rl-trailersi fn-rl-gensi nth update-nth)))))

(defthm fn-rlo-physical-settled-chain
 (implies (and (fn-rlo-free-chainp rows ledger)
               (eq (car (fn-rlo-physical token opgen receipt ledger)) :settled))
  (fn-rlo-free-chainp
   (if (< (fn-rl-gensi (caddr token) ledger) *fn-rl-word-max*) (cons (caddr token) rows) rows)
   (mv-nth 1 (fn-rlo-physical token opgen receipt ledger))))
 :hints (("Goal"
  :use ((:instance fn-rlo-live-has-reusable-row-domain)
        (:instance fn-rlo-settled-chain-is-returned-row
       (slot (caddr token)) (ledger (update-fn-rl-trailersi (caddr token) 1 ledger))))
  :in-theory (e/d (fn-rlo-physical)
   (fn-rlo-settled-chain-is-returned-row fn-rlo-live-has-reusable-row-domain fn-rlo-free-chainp fn-rlo-settle-ready fn-rlo-livep fn-rlo-tokenp update-fn-rl-elensi update-fn-rl-trailersi fn-rl-gensi nth update-nth)))))
)

(encapsulate ()
(local (defthm fn-rlo-free-init-column-frame
 (implies (and (natp field) (not (equal field 14)))
  (equal (nth field (fn-rlo-free-init start ledger)) (nth field ledger)))
 :hints (("Goal" :induct (fn-rlo-free-init start ledger)
  :in-theory (e/d (fn-rlo-free-init fn-rl-count update-fn-rl-idsi) (nth update-nth))))))

(local (defthm fn-rlo-ids-update-read
 (implies (and (natp row) (natp slot))
  (equal (fn-rl-idsi row (update-fn-rl-idsi slot value ledger))
         (if (equal row slot) value (fn-rl-idsi row ledger))))
 :hints (("Goal" :in-theory (e/d (fn-rl-idsi update-fn-rl-idsi) (nth update-nth))))))

(local (defthm fn-rlo-ids-update-count
 (equal (fn-rl-count (update-fn-rl-idsi slot value ledger)) (fn-rl-count ledger))
 :hints (("Goal" :in-theory (e/d (fn-rl-count update-fn-rl-idsi) (nth update-nth))))))

(local (defthm fn-rlo-free-init-earlier-link
 (implies (and (natp start) (natp row) (< row start))
  (equal (fn-rl-idsi row (fn-rlo-free-init start ledger)) (fn-rl-idsi row ledger)))
 :hints (("Goal" :induct (fn-rlo-free-init start ledger)
  :in-theory (e/d (fn-rlo-free-init fn-rl-count fn-rl-idsi update-fn-rl-idsi) (nth update-nth))))))

(local (defthm fn-rlo-free-init-link-at
 (implies (and (natp start) (natp row) (natp (fn-rl-count ledger))
               (<= start row) (< row (fn-rl-count ledger)))
  (equal (fn-rl-idsi row (fn-rlo-free-init start ledger))
   (if (< (+ 1 row) (fn-rl-count ledger)) (+ 1 row) 0)))
 :hints (("Goal" :induct (fn-rlo-free-init start ledger)
  :in-theory (e/d (fn-rlo-free-init) (fn-rl-count fn-rl-idsi update-fn-rl-idsi nth update-nth))))))

(local (defthm fn-rlo-free-range-member-bounds
 (implies (member-equal slot (fn-rlo-free-range start count))
  (and (natp slot) (<= start slot) (< slot count)))
 :hints (("Goal" :induct (fn-rlo-free-range start count)
  :in-theory (enable fn-rlo-free-range)))))

(local (defthm fn-rlo-free-range-head
 (equal (car (fn-rlo-free-range start count))
        (if (and (natp start) (natp count) (< start count)) start nil))
 :hints (("Goal" :in-theory (enable fn-rlo-free-range)))))

(local (defthm fn-rlo-free-range-no-earlier-member
 (implies (< slot start) (not (member-equal slot (fn-rlo-free-range start count))))
 :hints (("Goal" :use fn-rlo-free-range-member-bounds
 :in-theory (disable fn-rlo-free-range fn-rlo-free-range-member-bounds)))))

(local (defthm fn-rlo-free-range-consp
 (equal (consp (fn-rlo-free-range start count))
        (and (natp start) (natp count) (< start count)))
 :hints (("Goal" :in-theory (enable fn-rlo-free-range)))))

(local (defthm fn-rlo-initialized-range-rows
 (implies (and (natp start) (natp row) (natp (fn-rl-count ledger))
               (<= start row) (<= 2 row)
               (fn-rlo-reusable-range-p row (fn-rl-count ledger) (nth 3 ledger) (nth 4 ledger)))
  (fn-rlo-chain-rows-p (fn-rlo-free-range row (fn-rl-count ledger))
                      (fn-rl-count ledger) (nth 3 ledger) (nth 4 ledger)
                      (nth 14 (fn-rlo-free-init start ledger))))
 :hints (("Goal" :induct (fn-rlo-free-range row (fn-rl-count ledger))
 :in-theory (e/d (fn-rlo-free-range fn-rlo-reusable-range-p fn-rlo-chain-rows-p)
  (fn-rlo-free-init fn-rl-count fn-rl-idsi nth update-nth)))
 ("Subgoal *1/1" :use ((:instance fn-rlo-free-init-link-at))
  :in-theory (e/d (fn-rl-idsi fn-rlo-free-range fn-rlo-reusable-range-p fn-rlo-chain-rows-p)
    (fn-rlo-free-init-link-at fn-rlo-free-init fn-rl-count nth update-nth))))))

(local (defthm fn-rlo-free-init-establishes-chain
 (implies (and (natp (fn-rl-count ledger))
               (fn-rlo-reusable-range-p 2 (fn-rl-count ledger) (nth 3 ledger) (nth 4 ledger)))
  (fn-rlo-free-chainp
   (fn-rlo-free-range 2 (fn-rl-count ledger))
   (update-fn-rl-next (if (< 2 (fn-rl-count ledger)) 2 0) (fn-rlo-free-init 2 ledger))))
 :hints (("Goal" :use ((:instance fn-rlo-initialized-range-rows (start 2) (row 2)))
  :in-theory (e/d (fn-rlo-free-chainp fn-rl-count fn-rl-next update-fn-rl-next)
   (fn-rlo-initialized-range-rows fn-rlo-free-init fn-rlo-chain-rows-p
    fn-rlo-free-range fn-rlo-reusable-range-p nth update-nth))))))

(local (defthm fn-rl-nth-member
  (implies (and (natp i) (< i (len xs)))
           (member-equal (nth i xs) xs))
  :hints (("Goal" :induct (nth i xs)))))

(local (defthm fn-rl-resize-zero-members
  (implies (member-equal x (resize-list nil n 0))
           (equal x 0))
  :rule-classes :forward-chaining
  :hints (("Goal" :induct (resize-list nil n 0)))))

(local (defthm fn-rl-len-resize
  (equal (len (resize-list xs n d)) (nfix n))))

(local (defthm fn-rl-nth-resize-zero
  (implies (and (natp i) (< i (nfix n)))
           (equal (nth i (resize-list nil n 0)) 0))
  :hints (("Goal" :use (:instance fn-rl-nth-member
                                  (xs (resize-list nil n 0)))
           :in-theory (disable fn-rl-nth-member resize-list nth)))))

(local (defthm fn-rlo-fresh-columns-reusable
 (implies (and (natp start) (<= 2 start) (natp count))
  (fn-rlo-reusable-range-p start count
    (update-nth 1 2 (update-nth 0 1 (resize-list nil count 0)))
    (update-nth 1 1 (update-nth 0 1 (resize-list nil count 0)))))
 :hints (("Goal" :induct (fn-rlo-free-range start count)
  :in-theory (e/d (fn-rlo-reusable-range-p) (nth update-nth resize-list))))))

(local (defthm fn-rlo-fresh-bank-establishes-free-chain
 (implies (and (fn-rl-freshp ledger)
               (eq (car (fn-rl-install budget baseline reserve slots ledger)) :installed))
  (let ((after (mv-nth 1 (fn-rl-install budget baseline reserve slots ledger))))
   (fn-rlo-free-chainp (fn-rlo-free-range 2 slots)
     (update-fn-rl-next (if (< 2 slots) 2 0) (fn-rlo-free-init 2 after)))))
 :hints (("Goal"
  :use ((:instance fn-rl-install-free-columns (nslots slots))
        (:instance fn-rlo-free-init-establishes-chain
          (ledger (mv-nth 1 (fn-rl-install budget baseline reserve slots ledger)))))
  :in-theory (disable fn-rl-install fn-rl-freshp fn-rlo-free-init fn-rlo-free-chainp
    fn-rlo-reusable-range-p fn-rlo-free-range fn-rl-count nth update-nth)))))

(local (defthm fn-rlo-free-chain-file-limit-frame
 (equal (fn-rlo-free-chainp rows (update-fn-rl-file-limit value ledger)) (fn-rlo-free-chainp rows ledger))
 :hints (("Goal" :in-theory (e/d (fn-rlo-free-chainp fn-rl-next fn-rl-count update-fn-rl-file-limit)
  (fn-rlo-chain-rows-p nth update-nth))))))

(local (defthm fn-rlo-free-chain-mode-frame
 (equal (fn-rlo-free-chainp rows (update-fn-rl-mode value ledger)) (fn-rlo-free-chainp rows ledger))
 :hints (("Goal" :in-theory (e/d (fn-rlo-free-chainp fn-rl-next fn-rl-count update-fn-rl-mode)
  (fn-rlo-chain-rows-p nth update-nth))))))

(local (defthm fn-rl-installed-zero-count
 (implies (eq (car (fn-rl-install budget baseline reserve slots ledger)) :installed)
          (equal (fn-rl-count ledger) 0))
 :hints (("Goal" :in-theory (e/d (fn-rl-install)
  (fn-rl-count fn-rl-profile-representable-p fn-rv-vectorp fn-rv-install fn-rl-resize-all
   fn-rl-store-words-from fn-rl-draw fn-rl-open))))))

(local (defthm fn-rlo-startup-not-installed
 (implies (not (eq (car (fn-orv-startup-grant dynamic store-need cold policy slots)) :hold))
          (not (eq (cadr (fn-orv-startup-grant dynamic store-need cold policy slots)) :installed)))
 :hints (("Goal" :in-theory (e/d (fn-orv-startup-grant)
   (fn-orv-policy-p fn-native-config-cold-resources-wfp fn-crv-nth fn-orv-bookkeeping-octets))))))

(local (defthm fn-rlo-install-base-domain
 (implies (eq (car (fn-rlo-install dynamic store-need cold policy slots ledger)) :installed)
  (let ((grant (fn-orv-startup-grant dynamic store-need cold policy slots)))
   (and (fn-rl-freshp ledger) (natp slots) (< 2 slots)
    (eq (car (fn-rl-install (fn-rlo-resident-vector (nth 1 grant))
       (fn-rlo-resident-vector (nth 3 grant)) (fn-rlo-resident-vector (nth 2 grant)) slots ledger)) :installed))))
 :hints (("Goal" :use ((:instance fn-rl-installed-zero-count
  (budget (fn-rlo-resident-vector (nth 1 (fn-orv-startup-grant dynamic store-need cold policy slots))))
  (baseline (fn-rlo-resident-vector (nth 3 (fn-orv-startup-grant dynamic store-need cold policy slots))))
  (reserve (fn-rlo-resident-vector (nth 2 (fn-orv-startup-grant dynamic store-need cold policy slots))))))
 :in-theory (e/d (fn-rlo-install fn-orv-startup-grant)
  (fn-rl-freshp fn-rl-wfp fn-rl-count fn-rl-install fn-rlo-free-init fn-rl-file-limit
   fn-rlo-resident-vector fn-orv-policy-p fn-native-config-cold-resources-wfp fn-crv-nth
   fn-orv-bookkeeping-octets update-fn-rl-next update-fn-rl-file-limit update-fn-rl-mode))))))

(defthm fn-rlo-install-establishes-free-chain
 (implies (eq (car (fn-rlo-install dynamic store-need cold policy slots ledger)) :installed)
  (fn-rlo-free-chainp (fn-rlo-free-range 2 slots)
      (mv-nth 1 (fn-rlo-install dynamic store-need cold policy slots ledger))))
 :hints (("Goal"
 :use ((:instance fn-rlo-install-base-domain)
       (:instance fn-rlo-startup-not-installed)
       (:instance fn-rlo-fresh-bank-establishes-free-chain
        (budget (fn-rlo-resident-vector (nth 1 (fn-orv-startup-grant dynamic store-need cold policy slots))))
        (baseline (fn-rlo-resident-vector (nth 3 (fn-orv-startup-grant dynamic store-need cold policy slots))))
        (reserve (fn-rlo-resident-vector (nth 2 (fn-orv-startup-grant dynamic store-need cold policy slots))))))
 :in-theory (e/d (fn-rlo-install)
   (fn-rlo-install-base-domain fn-rlo-startup-not-installed fn-rlo-fresh-bank-establishes-free-chain fn-rlo-free-chainp fn-rl-next fn-rl-count update-fn-rl-file-limit update-fn-rl-mode fn-rl-install fn-rl-freshp fn-rl-wfp
    fn-rlo-resident-vector fn-orv-startup-grant fn-rlo-free-init fn-rlo-chain-rows-p fn-rlo-free-range
    update-fn-rl-next nth update-nth)))))
)

(in-theory (disable fn-rlo-free-chainp fn-rlo-chain-rows-p fn-rlo-free-range fn-rlo-reusable-range-p))
