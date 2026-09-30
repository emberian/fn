; Actual issuer/worker/initializer source association; no native INIT authority.
(in-package "ACL2")
(include-book "decoded-window-initial-array-payload")
(include-book "decoded-window-initial-write-domains")
(include-book "decoded-window-read")
(include-book "decoded-window-lease")

; Constructor carry only. This is proof-only: no served whole-array scan.
; The bound is the selected UB8 installed-capacity qualifier, not a data cap.
(defun-nx fn-pioz-capacity-profilep (cwin ctab cout)
 (and (fn-octets$cp cwin) (fn-octets$cp ctab) (fn-octets$cp cout)
      (< (fn-octets$c-buf-length cwin) 17592186044416)
      (< (fn-octets$c-buf-length ctab) 17592186044416)
      (< (fn-octets$c-buf-length cout) 17592186044416)))

(defthm fn-pioz-admit-establishes-exact-source-token
 (implies (equal (mv-nth 0 (fn-pwz-admit ledger descriptor demand)) :admitted)
  (let ((token (mv-nth 1 (fn-pwz-admit ledger descriptor demand))))
   (and (fn-pwz-tokenp token)
        (equal token (cons :decoded-window (cons (fn-prl-nth 2 ledger) descriptor)))
        (equal (cddr token) descriptor))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :in-theory (e/d (fn-pwz-admit fn-pwz-tokenp fn-prl-build fn-prs-issue)
   (fn-pwz-descriptorp fn-prs-fundedp fn-prs-plus fn-prs-vectorp fn-prl-nth fn-prl-binding)))))

(local (defthm fn-pioz-nth-unfolds
 (implies (natp n) (equal (fn-prl-nth n x) (nth n x)))
 :hints (("Goal" :induct (fn-prl-nth n x) :in-theory (enable fn-prl-nth nth)))))
(local (defthm fn-pioz-token-fields-unfolds
 (implies (fn-pwx-tokenp token)
  (and (natp (nth 1 token))
       (member-equal (nth 0 token) '(:window :decoded-window))))
 :hints (("Goal" :in-theory (enable fn-pwx-tokenp fn-pwz-tokenp)))))
(local (defthm fn-pioz-worker-fields-unfolds
 (implies (fn-pwx-rowp w) (natp (nth 0 w)))
 :hints (("Goal" :in-theory (enable fn-pwx-rowp)))))
(local (defthm fn-pioz-assigned-row-unfolds
 (implies (and (natp slot) (fn-pwx-tokenp token))
          (fn-pwx-rowp (list slot (nth 1 token) :running token)))
 :hints (("Goal" :in-theory (e/d (fn-pwx-rowp) (fn-pwx-tokenp fn-pwz-tokenp))))))
(local (defthm fn-pioz-head-binding-unfolds
 (equal (fn-prl-binding token (cons (cons token row) rows)) (cons token row))
 :hints (("Goal" :in-theory (enable fn-prl-binding)))))
(defthm fn-pioz-assigned-worker-holds-same-token-and-charge
 (implies (equal (mv-nth 0 (fn-pwx-acquire ledger w token)) :assigned)
  (let ((w1 (mv-nth 1 (fn-pwx-acquire ledger w token)))
        (l1 (mv-nth 2 (fn-pwx-acquire ledger w token))))
   (and (fn-pwx-work-permittedp l1 w1 token)
        (equal (fn-prl-nth 1 l1) (fn-prl-nth 1 ledger))
        (equal (fn-prl-nth 0 l1) (fn-prl-nth 0 ledger))
        (equal (fn-prl-baseline l1) (fn-prl-baseline ledger))
        (equal (fn-prl-nth 0 (cdr (fn-prl-binding token (fn-prl-nth 3 l1))))
               (fn-prl-nth 0 (cdr (fn-prl-binding token (fn-prl-nth 3 ledger))))))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :use (fn-pioz-worker-fields-unfolds
        (:instance fn-pioz-assigned-row-unfolds (slot (fn-prl-nth 0 w))))
  :in-theory (e/d (fn-pwx-acquire fn-pwx-work-permittedp fn-pwx-boundp
                   fn-prw-phase fn-prl-build fn-prl-baseline)
    (fn-prl-nth fn-prl-binding fn-prl-remove fn-pwx-rowp fn-pwx-tokenp fn-pwz-tokenp fn-prw-descriptorp)))))
(defthm fn-pioz-begin-retains-exact-request-and-digest-roots
 (let* ((r (fn-pwz-begin token incarnation hash zin win tab out))
        (s (nth 1 (mv-nth 0 r))) (h (mv-nth 1 r)))
  (and (equal (pgs-dc-lease h) token)
       (equal (pgs-dc-capture h) (fn-ews-capture s))
       (equal (nth 15 h) (nth 15 hash))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :use (:instance fn-pwz-actual-begin-retains-digest-frame-array
         (pgs-digest-state hash) (fn-zin-st zin) (fn-zin-win win) (fn-zin-tab tab) (fn-zin-out out))
  :in-theory (e/d (fn-pwz-begin fn-ewz-begin fn-ews-begin pgs-dcb-begin pgs-dc-begin
                   pgs-dc-lease pgs-dc-capture fn-ewz-state)
   (fn-pwz-nth fn-pwz-dictionary fn-pzw-initialize fn-ewp-begin fn-ews-capture
    pgs-dcb-word-count fn-pzd-budget fn-pzw-stored-admissiblep nfix natp min nth update-nth)))))

(defthm fn-pioz-initial-capacities-preserve-selected-profile
 (implies (fn-pioz-capacity-profilep cwin ctab cout)
  (let ((r (fn-piwc-begin token incarnation hash zin cwin ctab cout)))
   (and (< (fn-octets$c-buf-length (mv-nth 3 r)) 17592186044416)
        (< (fn-octets$c-buf-length (mv-nth 4 r)) 17592186044416)
        (< (fn-octets$c-buf-length (mv-nth 5 r)) 17592186044416))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :use (:instance fn-piwc-begin-keeps-initial-capacities (pgs-digest-state hash) (fn-zin-st zin))
  :in-theory (e/d (fn-pioz-capacity-profilep max)
   (fn-piwc-begin fn-octets$c-buf-length fn-octets$cp (:e fn-piwc-begin))))))

(defthm fn-pioz-assigned-worker-retains-source-file
 (implies (equal (mv-nth 0 (fn-pwx-acquire ledger w token)) :assigned)
  (fn-prl-file-heldp (fn-prl-nth 2 token)
    (fn-prl-nth 3 (mv-nth 2 (fn-pwx-acquire ledger w token)))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :in-theory (e/d (fn-pwx-acquire fn-prl-build fn-prl-file-heldp)
    (fn-pwx-rowp fn-pwx-tokenp fn-prw-phase fn-prl-binding fn-prl-remove)))))

; Complete constructor relation for the actual six-result subject.  This is
; a REQUIRED component of a future installed producer, not a new issuer.
; It intentionally says nothing about the sufficiency of supplied DEMAND,
; native backing type, caller inlining, frames, GC or retained-alias release.
(defun-nx fn-pioz-initial-relation
 (ledger descriptor demand w incarnation hash zin cwin ctab cout awin atab aout)
 (let* ((a (fn-pwz-admit ledger descriptor demand)) (token (mv-nth 1 a))
        (x (fn-pwx-acquire (mv-nth 2 a) w token))
        (l1 (mv-nth 2 x)) (w1 (mv-nth 1 x))
        (rc (fn-piwc-begin token incarnation hash zin cwin ctab cout))
        (ra (fn-pwz-begin token incarnation hash zin awin atab aout)))
  (and (fn-pwz-tokenp token)
       (equal token (cons :decoded-window (cons (fn-prl-nth 2 ledger) descriptor)))
       (equal (cddr token) descriptor)
       (fn-pwx-work-permittedp l1 w1 token)
       (equal (fn-prl-nth 1 l1) (fn-prl-nth 1 (mv-nth 2 a)))
       (equal (fn-prl-nth 0 l1) (fn-prl-nth 0 (mv-nth 2 a)))
       (equal (fn-prl-baseline l1) (fn-prl-baseline (mv-nth 2 a)))
       (equal (fn-prl-nth 0 (cdr (fn-prl-binding token (fn-prl-nth 3 l1))))
              (fn-prl-nth 0 (cdr (fn-prl-binding token (fn-prl-nth 3 (mv-nth 2 a))))))
       (fn-prl-file-heldp (fn-prl-nth 2 token) (fn-prl-nth 3 l1))
       (equal (mv-nth 0 rc) (mv-nth 0 ra))
       (equal (mv-nth 1 rc) (mv-nth 1 ra))
       (equal (mv-nth 2 rc) (mv-nth 2 ra))
       (fn-octets$corr (mv-nth 3 rc) (mv-nth 3 ra))
       (fn-octets$corr (mv-nth 4 rc) (mv-nth 4 ra))
       (fn-octets$corr (mv-nth 5 rc) (mv-nth 5 ra))
       (fn-pwz-plan-matches-token (mv-nth 0 ra) token)
       (equal (pgs-dc-lease (mv-nth 1 ra)) token)
       (equal (pgs-dc-capture (mv-nth 1 ra)) (fn-ews-capture (nth 1 (mv-nth 0 ra))))
       (equal (nth 15 (mv-nth 1 ra)) (nth 15 hash))
       (equal (fn-octets$c-buf-length (mv-nth 3 rc)) (max 65536 (fn-octets$c-buf-length cwin)))
       (equal (fn-octets$c-buf-length (mv-nth 4 rc)) (max 3494 (fn-octets$c-buf-length ctab)))
       (equal (fn-octets$c-buf-length (mv-nth 5 rc)) (max 64 (fn-octets$c-buf-length cout)))
       (equal (fn-octets$c-fill (mv-nth 3 rc)) 65536)
       (equal (fn-octets$c-fill (mv-nth 4 rc)) 3494)
       (equal (fn-octets$c-fill (mv-nth 5 rc)) 0)
       (<= (+ (fn-octets$c-buf-length (mv-nth 3 rc))
              (fn-octets$c-buf-length (mv-nth 4 rc))
              (fn-octets$c-buf-length (mv-nth 5 rc)))
           (fn-pib-initial-retained-and-requested-payload
             (fn-octets$c-buf-length cwin) (fn-octets$c-buf-length ctab) (fn-octets$c-buf-length cout)))
       (implies (fn-pioz-capacity-profilep cwin ctab cout)
                (and (< (fn-octets$c-buf-length (mv-nth 3 rc)) 17592186044416)
                     (< (fn-octets$c-buf-length (mv-nth 4 rc)) 17592186044416)
                     (< (fn-octets$c-buf-length (mv-nth 5 rc)) 17592186044416))))))

(local (defthm fn-pioz-assigned-admission-requires-actual-issue
 (implies (equal (mv-nth 0 (fn-pwx-acquire (mv-nth 2 (fn-pwz-admit ledger descriptor demand))
              w (mv-nth 1 (fn-pwz-admit ledger descriptor demand)))) :assigned)
          (equal (mv-nth 0 (fn-pwz-admit ledger descriptor demand)) :admitted))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :in-theory (e/d (fn-pwz-admit fn-pwx-acquire)
  (fn-prs-issue fn-prl-build fn-pwx-rowp fn-pwx-tokenp fn-prw-phase
   fn-prl-binding fn-prl-nth fn-pwz-descriptorp fn-prs-vectorp))))))

(local (defthm fn-pioz-source-boundary-with-explicit-admission
 (implies
  (and (equal (mv-nth 0 (fn-pwz-admit ledger descriptor demand)) :admitted)
       (equal (mv-nth 0 (fn-pwx-acquire (mv-nth 2 (fn-pwz-admit ledger descriptor demand))
                            w (mv-nth 1 (fn-pwz-admit ledger descriptor demand)))) :assigned)
       (fn-octets$cp cwin) (fn-octets$cp ctab) (fn-octets$cp cout))
  (fn-pioz-initial-relation ledger descriptor demand w incarnation hash zin cwin ctab cout awin atab aout))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use (fn-pioz-admit-establishes-exact-source-token
       (:instance fn-pioz-assigned-worker-holds-same-token-and-charge
        (ledger (mv-nth 2 (fn-pwz-admit ledger descriptor demand)))
        (token (mv-nth 1 (fn-pwz-admit ledger descriptor demand))))
       (:instance fn-pioz-assigned-worker-retains-source-file
        (ledger (mv-nth 2 (fn-pwz-admit ledger descriptor demand)))
        (token (mv-nth 1 (fn-pwz-admit ledger descriptor demand))))
       (:instance fn-piwc-begin-refines-actual-begin-from-typed-arrays
        (token (mv-nth 1 (fn-pwz-admit ledger descriptor demand))) (pgs-digest-state hash) (fn-zin-st zin))
       (:instance fn-pwz-begin-captures-typed-request
        (token (mv-nth 1 (fn-pwz-admit ledger descriptor demand)))
        (pgs-digest-state hash) (fn-zin-st zin) (fn-zin-win awin) (fn-zin-tab atab) (fn-zin-out aout))
       (:instance fn-pioz-begin-retains-exact-request-and-digest-roots
        (token (mv-nth 1 (fn-pwz-admit ledger descriptor demand))) (win awin) (tab atab) (out aout))
       (:instance fn-piwc-begin-keeps-initial-capacities
        (token (mv-nth 1 (fn-pwz-admit ledger descriptor demand))) (pgs-digest-state hash) (fn-zin-st zin))
       (:instance fn-pib-actual-begin-retained-payload-bound
        (token (mv-nth 1 (fn-pwz-admit ledger descriptor demand))))
       (:instance fn-pioz-initial-capacities-preserve-selected-profile
        (token (mv-nth 1 (fn-pwz-admit ledger descriptor demand)))))
 :in-theory (e/d (fn-pioz-initial-relation)
  (fn-pwz-admit fn-pwx-acquire fn-pwz-tokenp fn-piwc-begin fn-pwz-begin
   fn-octets$cp fn-octets$corr fn-octets$c-buf-length fn-octets$c-fill
   fn-prl-nth fn-prl-binding fn-prl-baseline fn-prl-file-heldp fn-pwx-work-permittedp
   fn-pwz-plan-matches-token pgs-dc-lease pgs-dc-capture fn-ews-capture
   fn-pioz-capacity-profilep fn-pib-initial-retained-and-requested-payload max
   fn-pioz-nth-unfolds (:e fn-piwc-begin) (:e fn-pwz-begin)))))))

; Successful assignment of the ACTUAL admission result already implies
; actual admission.  The redundant explicit admission premise is removed.
(defthm fn-pioz-actual-issued-assigned-begin-source-boundary
 (implies
  (and (equal (mv-nth 0 (fn-pwx-acquire (mv-nth 2 (fn-pwz-admit ledger descriptor demand))
                            w (mv-nth 1 (fn-pwz-admit ledger descriptor demand)))) :assigned)
       (fn-octets$cp cwin) (fn-octets$cp ctab) (fn-octets$cp cout))
  (fn-pioz-initial-relation ledger descriptor demand w incarnation hash zin cwin ctab cout awin atab aout))
 :rule-classes nil
 :hints (("Goal" :use (fn-pioz-source-boundary-with-explicit-admission
                       fn-pioz-assigned-admission-requires-actual-issue)
 :in-theory (disable fn-pwz-admit fn-pwx-acquire fn-octets$cp fn-pioz-initial-relation))))
