; PRF-1132: actual initializer source events, not native allocation adequacy.

(in-package "ACL2")

(include-book "decoded-window-initial-source-trace")

(defun fn-piw-constructor-cells (trace)
 (if (consp trace)
   (+ (if (eq (caar trace) :constructor) (nfix (cadar trace)) 0)
      (fn-piw-constructor-cells (cdr trace))) 0))

(defun fn-piw-borrow-count (op trace)
 (if (consp trace)
   (+ (if (and (eq (caar trace) :borrow) (equal (cadar trace) op)) 1 0)
      (fn-piw-borrow-count op (cdr trace))) 0))

(defthm fn-piw-constructor-cells-append
 (equal (fn-piw-constructor-cells (append a b))
        (+ (fn-piw-constructor-cells a) (fn-piw-constructor-cells b))))

(defthm fn-piw-borrow-count-append
 (equal (fn-piw-borrow-count op (append a b))
        (+ (fn-piw-borrow-count op a) (fn-piw-borrow-count op b))))

(defthm fn-piw-profile-explicit-constructor-cells
 (and (equal (fn-piw-constructor-cells (cdr (fn-pzt-pzd-budget c n))) 0)
      (equal (fn-piw-constructor-cells (cdr (fn-pzt-pzw-stored-admissiblep c n))) 0))
 :hints (("Goal" :in-theory
   (e/d (fn-pzt-pzd-budget fn-pzt-pzw-stored-admissiblep
         fn-pzt-pzw-stored-allowance fn-pzt-zin-stored-allowance)
        (nfix min max natp)))))

(defthm fn-piw-ewp-state-explicit-constructor-cells
 (equal (fn-piw-constructor-cells (cdr (fn-piw-ewp-state phase file eoff elen woff wn expected pos ticket incarnation lease poff plen offset))) 14)
 :hints (("Goal" :do-not '(preprocess) :in-theory
   (e/d (fn-piw-ewp-state) (fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-ewp-begin-explicit-constructor-cells
 (equal (fn-piw-constructor-cells (cdr (fn-piw-ewp-begin file eoff elen poff plen offset ticket incarnation lease expected))) 14)
 :hints (("Goal" :do-not '(preprocess) :in-theory
   (e/d (fn-piw-ewp-begin) (fn-piw-ewp-state fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-ews-capture-explicit-constructor-cells
 (equal (fn-piw-constructor-cells (cdr (fn-piw-ews-capture s))) 12)
 :hints (("Goal" :do-not '(preprocess) :in-theory
   (e/d (fn-piw-ews-capture) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-pgs-dc-begin-explicit-constructor-cells
 (equal (fn-piw-constructor-cells (cdr (fn-piw-pgs-dc-begin sel base nb capture lease pgs-digest-state))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory
   (e/d (fn-piw-pgs-dc-begin) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-pgs-dcb-word-count-explicit-constructor-cells
 (equal (fn-piw-constructor-cells (cdr (fn-piw-pgs-dcb-word-count byte-total))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory
   (e/d (fn-piw-pgs-dcb-word-count) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-pgs-dcb-begin-explicit-constructor-cells
 (equal (fn-piw-constructor-cells (cdr (fn-piw-pgs-dcb-begin sel base byte-total capture lease pgs-digest-state))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory
   (e/d (fn-piw-pgs-dcb-begin) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-zin-reset-loop-explicit-constructor-cells
 (equal (fn-piw-constructor-cells (cdr (fn-piw-zin-reset-loop i fn-zin-st))) 0)
 :hints (("Goal" :induct (fn-piw-zin-reset-loop i fn-zin-st) :in-theory
   (e/d (fn-piw-zin-reset-loop) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-zin-reset-explicit-constructor-cells
 (equal (fn-piw-constructor-cells (cdr (fn-piw-zin-reset fn-zin-st))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory
   (e/d (fn-piw-zin-reset) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-zin-payload-ready-explicit-constructor-cells
 (equal (fn-piw-constructor-cells (cdr (fn-piw-zin-payload-ready dict fn-zin-win fn-zin-tab))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory
   (e/d (fn-piw-zin-payload-ready) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-pzw-initialize-explicit-constructor-cells
 (equal (fn-piw-constructor-cells (cdr (fn-piw-pzw-initialize dict fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory
   (e/d (fn-piw-pzw-initialize) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-ews-begin-explicit-constructor-cells
 (equal (fn-piw-constructor-cells (cdr (fn-piw-ews-begin file eoff elen poff plen offset ticket incarnation lease expected pgs-digest-state))) 26)
 :hints (("Goal" :do-not '(preprocess) :in-theory
   (e/d (fn-piw-ews-begin) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-ewz-state-explicit-constructor-cells
 (equal (fn-piw-constructor-cells (cdr (fn-piw-ewz-state mode plan n offset wanted budget ip end status))) 9)
 :hints (("Goal" :do-not '(preprocess) :in-theory
   (e/d (fn-piw-ewz-state) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-ewz-begin-explicit-constructor-cells
 (equal (fn-piw-constructor-cells (cdr (fn-piw-ewz-begin file eoff elen poff compressed decoded offset ticket incarnation lease expected dict pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))) 35)
 :hints (("Goal" :do-not '(preprocess) :in-theory
   (e/d (fn-piw-ewz-begin) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-pwz-begin-explicit-constructor-cells
 (equal (fn-piw-constructor-cells (cdr (fn-piw-pwz-begin token incarnation pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))) 35)
 :hints (("Goal" :do-not '(preprocess) :in-theory
   (e/d (fn-piw-pwz-begin) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin nfix natp min fn-zin-set binary-append)))))


(defthm fn-piw-reset-loop-source-field-writes
 (equal (fn-piw-borrow-count 'fn-zin-set (cdr (fn-piw-zin-reset-loop i fn-zin-st)))
        (if (and (natp i) (< i 18)) (- 18 i) 0))
 :hints (("Goal" :induct (fn-piw-zin-reset-loop i fn-zin-st)
  :in-theory (e/d (fn-piw-zin-reset-loop) (fn-zin-set binary-append)))))

(defthm fn-piw-profile-source-init-sites
 (and (equal (fn-piw-borrow-count 'fn-zin-set (cdr (fn-pzt-pzd-budget c n))) 0)
      (equal (fn-piw-borrow-count 'fn-zin-set (cdr (fn-pzt-pzw-stored-admissiblep c n))) 0)
      (equal (fn-pzt-count :ceiling (cdr (fn-pzt-pzd-budget c n))) 0)
      (equal (fn-pzt-count :ceiling (cdr (fn-pzt-pzw-stored-admissiblep c n))) 0))
 :hints (("Goal" :in-theory
  (e/d (fn-pzt-pzd-budget fn-pzt-pzw-stored-admissiblep fn-pzt-pzw-stored-allowance fn-pzt-zin-stored-allowance)
       (nfix min max natp)))))

(defthm fn-piw-ewp-state-source-setter-count
 (equal (fn-piw-borrow-count 'fn-zin-set (cdr (fn-piw-ewp-state phase file eoff elen woff wn expected pos ticket incarnation lease poff plen offset))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory
  (e/d (fn-piw-ewp-state) (fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-ewp-begin-source-setter-count
 (equal (fn-piw-borrow-count 'fn-zin-set (cdr (fn-piw-ewp-begin file eoff elen poff plen offset ticket incarnation lease expected))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory
  (e/d (fn-piw-ewp-begin) (fn-piw-ewp-state fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-ews-capture-source-setter-count
 (equal (fn-piw-borrow-count 'fn-zin-set (cdr (fn-piw-ews-capture s))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory
  (e/d (fn-piw-ews-capture) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-pgs-dc-begin-source-setter-count
 (equal (fn-piw-borrow-count 'fn-zin-set (cdr (fn-piw-pgs-dc-begin sel base nb capture lease pgs-digest-state))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory
  (e/d (fn-piw-pgs-dc-begin) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-pgs-dcb-word-count-source-setter-count
 (equal (fn-piw-borrow-count 'fn-zin-set (cdr (fn-piw-pgs-dcb-word-count byte-total))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory
  (e/d (fn-piw-pgs-dcb-word-count) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-pgs-dcb-begin-source-setter-count
 (equal (fn-piw-borrow-count 'fn-zin-set (cdr (fn-piw-pgs-dcb-begin sel base byte-total capture lease pgs-digest-state))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory
  (e/d (fn-piw-pgs-dcb-begin) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-zin-reset-source-setter-count
 (equal (fn-piw-borrow-count 'fn-zin-set (cdr (fn-piw-zin-reset fn-zin-st))) 20)
 :hints (("Goal" :do-not '(preprocess) :in-theory
  (e/d (fn-piw-zin-reset) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-zin-payload-ready-source-setter-count
 (equal (fn-piw-borrow-count 'fn-zin-set (cdr (fn-piw-zin-payload-ready dict fn-zin-win fn-zin-tab))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory
  (e/d (fn-piw-zin-payload-ready) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-pzw-initialize-source-setter-count
 (equal (fn-piw-borrow-count 'fn-zin-set (cdr (fn-piw-pzw-initialize dict fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))) 21)
 :hints (("Goal" :do-not '(preprocess) :in-theory
  (e/d (fn-piw-pzw-initialize) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-ews-begin-source-setter-count
 (equal (fn-piw-borrow-count 'fn-zin-set (cdr (fn-piw-ews-begin file eoff elen poff plen offset ticket incarnation lease expected pgs-digest-state))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory
  (e/d (fn-piw-ews-begin) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-ewz-state-source-setter-count
 (equal (fn-piw-borrow-count 'fn-zin-set (cdr (fn-piw-ewz-state mode plan n offset wanted budget ip end status))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory
  (e/d (fn-piw-ewz-state) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-ewz-begin-source-setter-count
 (equal (fn-piw-borrow-count 'fn-zin-set (cdr (fn-piw-ewz-begin file eoff elen poff compressed decoded offset ticket incarnation lease expected dict pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))) 21)
 :hints (("Goal" :do-not '(preprocess) :in-theory
  (e/d (fn-piw-ewz-begin) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-pwz-begin-source-setter-count
 (equal (fn-piw-borrow-count 'fn-zin-set (cdr (fn-piw-pwz-begin token incarnation pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))) 21)
 :hints (("Goal" :do-not '(preprocess) :in-theory
  (e/d (fn-piw-pwz-begin) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-ewp-state-source-ceiling-count
 (equal (fn-pzt-count :ceiling (cdr (fn-piw-ewp-state phase file eoff elen woff wn expected pos ticket incarnation lease poff plen offset))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory
  (e/d (fn-piw-ewp-state) (fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-ewp-begin-source-ceiling-count
 (equal (fn-pzt-count :ceiling (cdr (fn-piw-ewp-begin file eoff elen poff plen offset ticket incarnation lease expected))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory
  (e/d (fn-piw-ewp-begin) (fn-piw-ewp-state fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-ews-capture-source-ceiling-count
 (equal (fn-pzt-count :ceiling (cdr (fn-piw-ews-capture s))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory
  (e/d (fn-piw-ews-capture) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-pgs-dc-begin-source-ceiling-count
 (equal (fn-pzt-count :ceiling (cdr (fn-piw-pgs-dc-begin sel base nb capture lease pgs-digest-state))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory
  (e/d (fn-piw-pgs-dc-begin) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-pgs-dcb-word-count-source-ceiling-count
 (equal (fn-pzt-count :ceiling (cdr (fn-piw-pgs-dcb-word-count byte-total))) 1)
 :hints (("Goal" :do-not '(preprocess) :in-theory
  (e/d (fn-piw-pgs-dcb-word-count) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-pgs-dcb-begin-source-ceiling-count
 (equal (fn-pzt-count :ceiling (cdr (fn-piw-pgs-dcb-begin sel base byte-total capture lease pgs-digest-state))) 3)
 :hints (("Goal" :do-not '(preprocess) :in-theory
  (e/d (fn-piw-pgs-dcb-begin) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-zin-reset-loop-source-ceiling-count
 (equal (fn-pzt-count :ceiling (cdr (fn-piw-zin-reset-loop i fn-zin-st))) 0)
 :hints (("Goal" :induct (fn-piw-zin-reset-loop i fn-zin-st) :in-theory
  (e/d (fn-piw-zin-reset-loop) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-zin-reset-source-ceiling-count
 (equal (fn-pzt-count :ceiling (cdr (fn-piw-zin-reset fn-zin-st))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory
  (e/d (fn-piw-zin-reset) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-zin-payload-ready-source-ceiling-count
 (equal (fn-pzt-count :ceiling (cdr (fn-piw-zin-payload-ready dict fn-zin-win fn-zin-tab))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory
  (e/d (fn-piw-zin-payload-ready) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-pzw-initialize-source-ceiling-count
 (equal (fn-pzt-count :ceiling (cdr (fn-piw-pzw-initialize dict fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory
  (e/d (fn-piw-pzw-initialize) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-ews-begin-source-ceiling-count
 (equal (fn-pzt-count :ceiling (cdr (fn-piw-ews-begin file eoff elen poff plen offset ticket incarnation lease expected pgs-digest-state))) 3)
 :hints (("Goal" :do-not '(preprocess) :in-theory
  (e/d (fn-piw-ews-begin) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-ewz-state-source-ceiling-count
 (equal (fn-pzt-count :ceiling (cdr (fn-piw-ewz-state mode plan n offset wanted budget ip end status))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory
  (e/d (fn-piw-ewz-state) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-ewz-begin-source-ceiling-count
 (equal (fn-pzt-count :ceiling (cdr (fn-piw-ewz-begin file eoff elen poff compressed decoded offset ticket incarnation lease expected dict pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))) 3)
 :hints (("Goal" :do-not '(preprocess) :in-theory
  (e/d (fn-piw-ewz-begin) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-pwz-begin-source-ceiling-count
 (equal (fn-pzt-count :ceiling (cdr (fn-piw-pwz-begin token incarnation pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))) 3)
 :hints (("Goal" :do-not '(preprocess) :in-theory
  (e/d (fn-piw-pwz-begin) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin nfix natp min fn-zin-set binary-append)))))


(defun fn-piw-reserve-octets (trace)
 (if (consp trace)
  (+ (if (and (eq (caar trace) :borrow)
              (member-eq (cadar trace) '(fn-zin-out-reserve fn-zin-win-reserve fn-zin-tab-reserve)))
       (nfix (car (caddar trace))) 0)
     (fn-piw-reserve-octets (cdr trace))) 0))

(defthm fn-piw-reserve-octets-append
 (equal (fn-piw-reserve-octets (append a b))
        (+ (fn-piw-reserve-octets a) (fn-piw-reserve-octets b))))

(defthm fn-piw-profile-reserve-octets
 (and (equal (fn-piw-reserve-octets (cdr (fn-pzt-pzd-budget c n))) 0)
      (equal (fn-piw-reserve-octets (cdr (fn-pzt-pzw-stored-admissiblep c n))) 0))
 :hints (("Goal" :in-theory
  (e/d (fn-pzt-pzd-budget fn-pzt-pzw-stored-admissiblep fn-pzt-pzw-stored-allowance fn-pzt-zin-stored-allowance)
       (nfix min max natp)))))

(defthm fn-piw-ewp-state-source-reserve-octets
 (equal (fn-piw-reserve-octets (cdr (fn-piw-ewp-state phase file eoff elen woff wn expected pos ticket incarnation lease poff plen offset))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory
  (e/d (fn-piw-ewp-state) (fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-ewp-begin-source-reserve-octets
 (equal (fn-piw-reserve-octets (cdr (fn-piw-ewp-begin file eoff elen poff plen offset ticket incarnation lease expected))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory
  (e/d (fn-piw-ewp-begin) (fn-piw-ewp-state fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-ews-capture-source-reserve-octets
 (equal (fn-piw-reserve-octets (cdr (fn-piw-ews-capture s))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory
  (e/d (fn-piw-ews-capture) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-pgs-dc-begin-source-reserve-octets
 (equal (fn-piw-reserve-octets (cdr (fn-piw-pgs-dc-begin sel base nb capture lease pgs-digest-state))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory
  (e/d (fn-piw-pgs-dc-begin) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-pgs-dcb-word-count-source-reserve-octets
 (equal (fn-piw-reserve-octets (cdr (fn-piw-pgs-dcb-word-count byte-total))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory
  (e/d (fn-piw-pgs-dcb-word-count) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-pgs-dcb-begin-source-reserve-octets
 (equal (fn-piw-reserve-octets (cdr (fn-piw-pgs-dcb-begin sel base byte-total capture lease pgs-digest-state))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory
  (e/d (fn-piw-pgs-dcb-begin) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-zin-reset-loop-source-reserve-octets
 (equal (fn-piw-reserve-octets (cdr (fn-piw-zin-reset-loop i fn-zin-st))) 0)
 :hints (("Goal" :induct (fn-piw-zin-reset-loop i fn-zin-st) :in-theory
  (e/d (fn-piw-zin-reset-loop) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-zin-reset-source-reserve-octets
 (equal (fn-piw-reserve-octets (cdr (fn-piw-zin-reset fn-zin-st))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory
  (e/d (fn-piw-zin-reset) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-zin-payload-ready-source-reserve-octets
 (equal (fn-piw-reserve-octets (cdr (fn-piw-zin-payload-ready dict fn-zin-win fn-zin-tab))) 69030)
 :hints (("Goal" :do-not '(preprocess) :in-theory
  (e/d (fn-piw-zin-payload-ready) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-pzw-initialize-source-reserve-octets
 (equal (fn-piw-reserve-octets (cdr (fn-piw-pzw-initialize dict fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))) 69094)
 :hints (("Goal" :do-not '(preprocess) :in-theory
  (e/d (fn-piw-pzw-initialize) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-ews-begin-source-reserve-octets
 (equal (fn-piw-reserve-octets (cdr (fn-piw-ews-begin file eoff elen poff plen offset ticket incarnation lease expected pgs-digest-state))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory
  (e/d (fn-piw-ews-begin) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-ewz-state-source-reserve-octets
 (equal (fn-piw-reserve-octets (cdr (fn-piw-ewz-state mode plan n offset wanted budget ip end status))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory
  (e/d (fn-piw-ewz-state) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-begin fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-ewz-begin-source-reserve-octets
 (equal (fn-piw-reserve-octets (cdr (fn-piw-ewz-begin file eoff elen poff compressed decoded offset ticket incarnation lease expected dict pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))) 69094)
 :hints (("Goal" :do-not '(preprocess) :in-theory
  (e/d (fn-piw-ewz-begin) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-pwz-begin nfix natp min fn-zin-set binary-append)))))

(defthm fn-piw-pwz-begin-source-reserve-octets
 (equal (fn-piw-reserve-octets (cdr (fn-piw-pwz-begin token incarnation pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))) 69094)
 :hints (("Goal" :do-not '(preprocess) :in-theory
  (e/d (fn-piw-pwz-begin) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin nfix natp min fn-zin-set binary-append)))))


(defun fn-piw-fill-octets (trace)
 (if (consp trace)
  (+ (if (eq (caar trace) :borrow)
      (cond ((member-eq (cadar trace) '(fn-zin-win-append-octet fn-zin-tab-append-octet)) 1)
            ((member-eq (cadar trace) '(fn-zin-win-append-back fn-zin-tab-append-back))
             (nfix (cadr (caddar trace))))
            ((eq (cadar trace) 'fn-zin-win-append-list) (len (car (caddar trace))))
            (t 0)) 0)
     (fn-piw-fill-octets (cdr trace))) 0))

(defthm fn-piw-fill-octets-append
 (equal (fn-piw-fill-octets (append a b))
        (+ (fn-piw-fill-octets a) (fn-piw-fill-octets b))))

(local (defthm fn-piw-len-nthcdr
 (equal (len (nthcdr n xs)) (nfix (- (len xs) (nfix n))))
 :hints (("Goal" :induct (nthcdr n xs) :in-theory (enable nthcdr)))))

(defthm fn-piw-profile-fill-octets
 (and (equal (fn-piw-fill-octets (cdr (fn-pzt-pzd-budget c n))) 0)
      (equal (fn-piw-fill-octets (cdr (fn-pzt-pzw-stored-admissiblep c n))) 0))
 :hints (("Goal" :in-theory
  (e/d (fn-pzt-pzd-budget fn-pzt-pzw-stored-admissiblep fn-pzt-pzw-stored-allowance fn-pzt-zin-stored-allowance)
       (nfix min max natp)))))

(defthm fn-piw-ewp-state-source-fill-octets
 (equal (fn-piw-fill-octets (cdr (fn-piw-ewp-state phase file eoff elen woff wn expected pos ticket incarnation lease poff plen offset))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory (e/d (fn-piw-ewp-state) (fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin fn-zin-set binary-append nfix natp min fn-zin-win-clear fn-zin-win-reserve fn-zin-win-append-octet fn-zin-win-append-back fn-zin-win-append-list fn-zin-tab-clear fn-zin-tab-reserve fn-zin-tab-append-octet fn-zin-tab-append-back fn-zin-out-clear fn-zin-out-reserve (:e fn-zin-win-append-back) (:e fn-zin-tab-append-back) (:e fn-octets$a-append-back))))))

(defthm fn-piw-ewp-begin-source-fill-octets
 (equal (fn-piw-fill-octets (cdr (fn-piw-ewp-begin file eoff elen poff plen offset ticket incarnation lease expected))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory (e/d (fn-piw-ewp-begin) (fn-piw-ewp-state fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin fn-zin-set binary-append nfix natp min fn-zin-win-clear fn-zin-win-reserve fn-zin-win-append-octet fn-zin-win-append-back fn-zin-win-append-list fn-zin-tab-clear fn-zin-tab-reserve fn-zin-tab-append-octet fn-zin-tab-append-back fn-zin-out-clear fn-zin-out-reserve (:e fn-zin-win-append-back) (:e fn-zin-tab-append-back) (:e fn-octets$a-append-back))))))

(defthm fn-piw-ews-capture-source-fill-octets
 (equal (fn-piw-fill-octets (cdr (fn-piw-ews-capture s))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory (e/d (fn-piw-ews-capture) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin fn-zin-set binary-append nfix natp min fn-zin-win-clear fn-zin-win-reserve fn-zin-win-append-octet fn-zin-win-append-back fn-zin-win-append-list fn-zin-tab-clear fn-zin-tab-reserve fn-zin-tab-append-octet fn-zin-tab-append-back fn-zin-out-clear fn-zin-out-reserve (:e fn-zin-win-append-back) (:e fn-zin-tab-append-back) (:e fn-octets$a-append-back))))))

(defthm fn-piw-pgs-dc-begin-source-fill-octets
 (equal (fn-piw-fill-octets (cdr (fn-piw-pgs-dc-begin sel base nb capture lease pgs-digest-state))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory (e/d (fn-piw-pgs-dc-begin) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin fn-zin-set binary-append nfix natp min fn-zin-win-clear fn-zin-win-reserve fn-zin-win-append-octet fn-zin-win-append-back fn-zin-win-append-list fn-zin-tab-clear fn-zin-tab-reserve fn-zin-tab-append-octet fn-zin-tab-append-back fn-zin-out-clear fn-zin-out-reserve (:e fn-zin-win-append-back) (:e fn-zin-tab-append-back) (:e fn-octets$a-append-back))))))

(defthm fn-piw-pgs-dcb-word-count-source-fill-octets
 (equal (fn-piw-fill-octets (cdr (fn-piw-pgs-dcb-word-count byte-total))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory (e/d (fn-piw-pgs-dcb-word-count) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin fn-zin-set binary-append nfix natp min fn-zin-win-clear fn-zin-win-reserve fn-zin-win-append-octet fn-zin-win-append-back fn-zin-win-append-list fn-zin-tab-clear fn-zin-tab-reserve fn-zin-tab-append-octet fn-zin-tab-append-back fn-zin-out-clear fn-zin-out-reserve (:e fn-zin-win-append-back) (:e fn-zin-tab-append-back) (:e fn-octets$a-append-back))))))

(defthm fn-piw-pgs-dcb-begin-source-fill-octets
 (equal (fn-piw-fill-octets (cdr (fn-piw-pgs-dcb-begin sel base byte-total capture lease pgs-digest-state))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory (e/d (fn-piw-pgs-dcb-begin) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin fn-zin-set binary-append nfix natp min fn-zin-win-clear fn-zin-win-reserve fn-zin-win-append-octet fn-zin-win-append-back fn-zin-win-append-list fn-zin-tab-clear fn-zin-tab-reserve fn-zin-tab-append-octet fn-zin-tab-append-back fn-zin-out-clear fn-zin-out-reserve (:e fn-zin-win-append-back) (:e fn-zin-tab-append-back) (:e fn-octets$a-append-back))))))

(defthm fn-piw-zin-reset-loop-source-fill-octets
 (equal (fn-piw-fill-octets (cdr (fn-piw-zin-reset-loop i fn-zin-st))) 0)
 :hints (("Goal" :induct (fn-piw-zin-reset-loop i fn-zin-st) :in-theory (e/d (fn-piw-zin-reset-loop) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin fn-zin-set binary-append nfix natp min fn-zin-win-clear fn-zin-win-reserve fn-zin-win-append-octet fn-zin-win-append-back fn-zin-win-append-list fn-zin-tab-clear fn-zin-tab-reserve fn-zin-tab-append-octet fn-zin-tab-append-back fn-zin-out-clear fn-zin-out-reserve (:e fn-zin-win-append-back) (:e fn-zin-tab-append-back) (:e fn-octets$a-append-back))))))

(defthm fn-piw-zin-reset-source-fill-octets
 (equal (fn-piw-fill-octets (cdr (fn-piw-zin-reset fn-zin-st))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory (e/d (fn-piw-zin-reset) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin fn-zin-set binary-append nfix natp min fn-zin-win-clear fn-zin-win-reserve fn-zin-win-append-octet fn-zin-win-append-back fn-zin-win-append-list fn-zin-tab-clear fn-zin-tab-reserve fn-zin-tab-append-octet fn-zin-tab-append-back fn-zin-out-clear fn-zin-out-reserve (:e fn-zin-win-append-back) (:e fn-zin-tab-append-back) (:e fn-octets$a-append-back))))))

(defthm fn-piw-zin-payload-ready-source-fill-octets
 (equal (fn-piw-fill-octets (cdr (fn-piw-zin-payload-ready dict fn-zin-win fn-zin-tab))) 69030)
 :hints (("Goal" :do-not '(preprocess) :in-theory (e/d (fn-piw-zin-payload-ready) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin fn-zin-set binary-append fn-zin-win-clear fn-zin-win-reserve fn-zin-win-append-octet fn-zin-win-append-back fn-zin-win-append-list fn-zin-tab-clear fn-zin-tab-reserve fn-zin-tab-append-octet fn-zin-tab-append-back fn-zin-out-clear fn-zin-out-reserve (:e fn-zin-win-append-back) (:e fn-zin-tab-append-back) (:e fn-octets$a-append-back))))))

(defthm fn-piw-pzw-initialize-source-fill-octets
 (equal (fn-piw-fill-octets (cdr (fn-piw-pzw-initialize dict fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))) 69030)
 :hints (("Goal" :do-not '(preprocess) :in-theory (e/d (fn-piw-pzw-initialize) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin fn-zin-set binary-append nfix natp min fn-zin-win-clear fn-zin-win-reserve fn-zin-win-append-octet fn-zin-win-append-back fn-zin-win-append-list fn-zin-tab-clear fn-zin-tab-reserve fn-zin-tab-append-octet fn-zin-tab-append-back fn-zin-out-clear fn-zin-out-reserve (:e fn-zin-win-append-back) (:e fn-zin-tab-append-back) (:e fn-octets$a-append-back))))))

(defthm fn-piw-ews-begin-source-fill-octets
 (equal (fn-piw-fill-octets (cdr (fn-piw-ews-begin file eoff elen poff plen offset ticket incarnation lease expected pgs-digest-state))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory (e/d (fn-piw-ews-begin) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ewz-state fn-piw-ewz-begin fn-piw-pwz-begin fn-zin-set binary-append nfix natp min fn-zin-win-clear fn-zin-win-reserve fn-zin-win-append-octet fn-zin-win-append-back fn-zin-win-append-list fn-zin-tab-clear fn-zin-tab-reserve fn-zin-tab-append-octet fn-zin-tab-append-back fn-zin-out-clear fn-zin-out-reserve (:e fn-zin-win-append-back) (:e fn-zin-tab-append-back) (:e fn-octets$a-append-back))))))

(defthm fn-piw-ewz-state-source-fill-octets
 (equal (fn-piw-fill-octets (cdr (fn-piw-ewz-state mode plan n offset wanted budget ip end status))) 0)
 :hints (("Goal" :do-not '(preprocess) :in-theory (e/d (fn-piw-ewz-state) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-begin fn-piw-pwz-begin fn-zin-set binary-append nfix natp min fn-zin-win-clear fn-zin-win-reserve fn-zin-win-append-octet fn-zin-win-append-back fn-zin-win-append-list fn-zin-tab-clear fn-zin-tab-reserve fn-zin-tab-append-octet fn-zin-tab-append-back fn-zin-out-clear fn-zin-out-reserve (:e fn-zin-win-append-back) (:e fn-zin-tab-append-back) (:e fn-octets$a-append-back))))))

(defthm fn-piw-ewz-begin-source-fill-octets
 (equal (fn-piw-fill-octets (cdr (fn-piw-ewz-begin file eoff elen poff compressed decoded offset ticket incarnation lease expected dict pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))) 69030)
 :hints (("Goal" :do-not '(preprocess) :in-theory (e/d (fn-piw-ewz-begin) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-pwz-begin fn-zin-set binary-append nfix natp min fn-zin-win-clear fn-zin-win-reserve fn-zin-win-append-octet fn-zin-win-append-back fn-zin-win-append-list fn-zin-tab-clear fn-zin-tab-reserve fn-zin-tab-append-octet fn-zin-tab-append-back fn-zin-out-clear fn-zin-out-reserve (:e fn-zin-win-append-back) (:e fn-zin-tab-append-back) (:e fn-octets$a-append-back))))))

(defthm fn-piw-pwz-begin-source-fill-octets
 (equal (fn-piw-fill-octets (cdr (fn-piw-pwz-begin token incarnation pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))) 69030)
 :hints (("Goal" :do-not '(preprocess) :in-theory (e/d (fn-piw-pwz-begin) (fn-piw-ewp-state fn-piw-ewp-begin fn-piw-ews-capture fn-piw-pgs-dc-begin fn-piw-pgs-dcb-word-count fn-piw-pgs-dcb-begin fn-piw-zin-reset-loop fn-piw-zin-reset fn-piw-zin-payload-ready fn-piw-pzw-initialize fn-piw-ews-begin fn-piw-ewz-state fn-piw-ewz-begin fn-zin-set binary-append nfix natp min fn-zin-win-clear fn-zin-win-reserve fn-zin-win-append-octet fn-zin-win-append-back fn-zin-win-append-list fn-zin-tab-clear fn-zin-tab-reserve fn-zin-tab-append-octet fn-zin-tab-append-back fn-zin-out-clear fn-zin-out-reserve (:e fn-zin-win-append-back) (:e fn-zin-tab-append-back) (:e fn-octets$a-append-back))))))

; The subject is the actual host-called initializer. Observer conses,
; multiple-value model lists and borrowed buffers are not constructor charges.
(defthm fn-piw-actual-begin-source-roster
 (let* ((o (fn-piw-pwz-begin token incarnation pgs-digest-state fn-zin-st
                            fn-zin-win fn-zin-tab fn-zin-out))
        (trace (cdr o)))
  (and (equal (car o) (fn-pwz-begin token incarnation pgs-digest-state fn-zin-st
                                  fn-zin-win fn-zin-tab fn-zin-out))
       (equal (fn-piw-constructor-cells trace) 35)
       (equal (fn-piw-borrow-count 'fn-zin-set trace) 21)
       (equal (fn-pzt-count :ceiling trace) 3)
       (equal (fn-piw-reserve-octets trace) 69094)
       (equal (fn-piw-fill-octets trace) 69030)))
 :rule-classes nil
 :hints (("Goal" :in-theory (disable fn-piw-pwz-begin fn-pwz-begin))))
