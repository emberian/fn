; Teeth for books/resource-vector-exec (deputy-1, 2026-10-01; Codex review
; r06 F4 and F8): the typed ledger installed from a small profile, a draw
; and its token, a settle, the replayed token :stale, an unrepresentable
; profile REFUSED before any store, the abstraction read back as the
; logical bank and compared, ON THESE VALUES, with the logical transitions.
; These are evaluations, not the correspondence theorems (which the book
; states as NEXT: PRF-1211 stays planned).
(in-package "ACL2")
(include-book "../../books/resource-vector-exec")
(include-book "std/testing/assert-bang" :dir :system)

(defconst *rxt-mib* 1048576)
(defconst *rxt-budget* (list (* 256 *rxt-mib*) (* 4096 *rxt-mib*) 64 8 1000 1000000 100 10000 1000000))
(defconst *rxt-baseline* (list (* 160 *rxt-mib*) 0 1 1 0 0 0 0 0))
(defconst *rxt-reserve* (list (* 16 *rxt-mib*) (* 512 *rxt-mib*) 2 1 0 1 1 0 100000))
(defconst *rxt-read* (list 65536 0 0 0 1 0 0 0 1000))

;; A budget word past u64 is refused by name, and nothing is stored.
(defconst *rxt-too-big* (list (expt 2 64) 0 0 0 0 0 0 0 0))
(assert! (not (fn-rl-words-representable-p *rxt-too-big*)))
(assert! (fn-rl-words-representable-p *rxt-budget*))

(make-event
 (mv-let (w fn-resource-ledger)
   (fn-rl-install *rxt-too-big* *rxt-baseline* *rxt-reserve* 8 fn-resource-ledger)
   (if (and (eq w :unrepresentable-profile)
            (equal (fn-rl-count fn-resource-ledger) 0)
            (equal (fn-rl-budgeti 0 fn-resource-ledger) 0))
       (mv nil '(value-triple :unrepresentable-refused) state fn-resource-ledger)
     (mv t nil state fn-resource-ledger))))

;; A profile the baseline and reserve do not fit is refused before any store.
(make-event
 (mv-let (w fn-resource-ledger)
   (fn-rl-install *rxt-baseline* *rxt-baseline* *rxt-reserve* 8 fn-resource-ledger)
   (if (and (eq w :resources-unavailable) (equal (fn-rl-count fn-resource-ledger) 0))
       (mv nil '(value-triple :unfunded-refused-before-any-store) state fn-resource-ledger)
     (mv t nil state fn-resource-ledger))))

;; The small profile installs; its abstraction is the logical root.
(make-event
 (mv-let (w fn-resource-ledger)
   (fn-rl-install *rxt-budget* *rxt-baseline* *rxt-reserve* 8 fn-resource-ledger)
   (if (and (eq w :installed)
            (fn-rl-wfp fn-resource-ledger)
            (equal (fn-rl-bank fn-resource-ledger)
                   (cadr (fn-rv-install *rxt-budget* *rxt-baseline* *rxt-reserve* 8)))
            (fn-rv-okp (fn-rl-bank fn-resource-ledger)))
       (mv nil '(value-triple :installed-as-the-logical-root) state fn-resource-ledger)
     (mv t nil state fn-resource-ledger))))

;; A second install is refused (:already-installed): the generations are
;; never reset, so no old token can name a new draw (Codex r18 F2).
(make-event
 (let ((before (fn-rl-bank fn-resource-ledger)))
   (mv-let (w fn-resource-ledger)
     (fn-rl-install *rxt-budget* *rxt-baseline* *rxt-reserve* 2 fn-resource-ledger)
     (if (and (eq w :already-installed) (equal (fn-rl-bank fn-resource-ledger) before))
         (mv nil '(value-triple :installs-once) state fn-resource-ledger)
       (mv t nil state fn-resource-ledger)))))

;; A draw at slot 2 answers token 1; the abstraction is the logical draw.
(make-event
 (let ((before (fn-rl-bank fn-resource-ledger)))
   (mv-let (w g fn-resource-ledger)
     (fn-rl-draw 2 *rxt-read* fn-resource-ledger)
     (if (and (eq w :drawn) (equal g 1)
              (equal (fn-rl-bank fn-resource-ledger) (cadr (fn-rv-draw before 2 *rxt-read*)))
              (equal g (caddr (fn-rv-draw before 2 *rxt-read*))))
         (mv nil '(value-triple :drawn-as-the-logical-draw) state fn-resource-ledger)
       (mv t nil state fn-resource-ledger)))))

;; The settle with its token; the replayed token after a second draw is
;; :stale and changes nothing.
(make-event
 (let ((before (fn-rl-bank fn-resource-ledger)))
   (mv-let (w fn-resource-ledger)
     (fn-rl-settle 2 1 fn-resource-ledger)
     (if (and (eq w :settled)
              (equal (fn-rl-bank fn-resource-ledger) (cadr (fn-rv-settle before 2 1))))
         (mv nil '(value-triple :settled-as-the-logical-settle) state fn-resource-ledger)
       (mv t nil state fn-resource-ledger)))))

(make-event
 (mv-let (w g fn-resource-ledger)
   (fn-rl-draw 2 *rxt-read* fn-resource-ledger)
   (let ((again (fn-rl-bank fn-resource-ledger)))
     (mv-let (w2 fn-resource-ledger)
       (fn-rl-settle 2 1 fn-resource-ledger)
       (if (and (eq w :drawn) (equal g 2) (eq w2 :stale)
                (equal (fn-rl-bank fn-resource-ledger) again))
           (mv nil '(value-triple :replayed-token-stale) state fn-resource-ledger)
         (mv t nil state fn-resource-ledger))))))
