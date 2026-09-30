; Arithmetic operand/result envelope, independent of native object pricing.
(in-package "ACL2")
(include-book "connection-operation-source-cost")
(local (include-book "arithmetic-5/top" :dir :system))
(local (defthm fn-copod-at-is-mv-nth
 (implies (natp n) (equal (fn-atsc-at n x) (mv-nth n x)))
 :hints (("Goal" :induct (fn-atsc-at n x) :in-theory (enable fn-atsc-at)))))
(defun fn-copod-fits (x domain)
 (declare (xargs :guard t)) (and (natp x) (natp domain) (<= x domain)))
(defun fn-copod-operationp (event domain)
 (declare (xargs :guard t))
 (let* ((op (fn-atsc-at 0 event)) (args (fn-atsc-at 1 event))
        (a (fn-atsc-at 0 args)) (b (fn-atsc-at 1 args)))
  (and (fn-omk-widthp event 2) (fn-omk-widthp args 2)
       (fn-copod-fits a domain) (fn-copod-fits b domain)
       (case op
        (:add (fn-copod-fits (+ a b) domain))
        (:subtract (fn-copod-fits (- a b) domain))
        (:multiply (fn-copod-fits (* a b) domain))
        (:floor (and (posp b) (fn-copod-fits (floor a b) domain)))
        (otherwise nil)))))
(defun fn-copod-operationsp (ops domain)
 (declare (xargs :guard t))
 (if (consp ops)
     (and (fn-copod-operationp (car ops) domain) (fn-copod-operationsp (cdr ops) domain))
   (null ops)))
(local (defthm fn-copod-append
 (implies (true-listp a)
  (equal (fn-copod-operationsp (fn-atsc-append a b) domain)
         (and (fn-copod-operationsp a domain) (fn-copod-operationsp b domain))))
 :hints (("Goal" :induct (fn-atsc-append a b)))))
(local (defthm fn-copod-at-fields
 (and (equal (fn-atsc-at 0 (list a b)) a) (equal (fn-atsc-at 1 (list a b)) b))
 :hints (("Goal" :in-theory (enable fn-atsc-at)))))
(local (defthm fn-copod-width2
 (fn-omk-widthp (list a b) 2) :hints (("Goal" :in-theory (enable fn-omk-widthp)))))
(local (defthm fn-copod-raw-fields
 (and (equal (fn-atsc-value (list value cells ops calls)) value)
      (equal (fn-atsc-ops (list value cells ops calls)) ops))
 :hints (("Goal" :in-theory (enable fn-atsc-value fn-atsc-ops fn-atsc-at)))))
(defthm fn-copod-checked-subtract-domain
 (fn-copod-operationsp (fn-atsc-ops (fn-atsc-add-room a b domain)) domain)
 :hints (("Goal" :in-theory (enable fn-atsc-add-room)))
 :rule-classes nil)
(local (defthm fn-copod-positive-floor-bound
 (implies (and (natp a) (posp b)) (<= (floor a b) a))
 :hints (("Goal" :nonlinearp t :do-not '(generalize eliminate-destructors)
  :use ((:instance linear-floor-bounds-1 (x a) (y b))) :in-theory (disable floor mod)))
 :rule-classes :linear))
(defthm fn-copod-checked-floor-domain
 (fn-copod-operationsp (fn-atsc-ops (fn-copc-times-room a b domain)) domain)
 :hints (("Goal" :in-theory (e/d (fn-copc-times-room) (floor mod))))
 :rule-classes nil)
(local (defthm fn-copod-operations-true-list
 (implies (fn-copod-operationsp ops domain) (true-listp ops))
 :hints (("Goal" :induct (fn-copod-operationsp ops domain)))
 :rule-classes :forward-chaining))
(local (defthm fn-copod-subtrace
 (fn-copod-operationsp (fn-atsc-ops (fn-atsc-add-room a b domain)) domain)
 :hints (("Goal" :use fn-copod-checked-subtract-domain))))
(local (defthm fn-copod-floortrace
 (fn-copod-operationsp (fn-atsc-ops (fn-copc-times-room a b domain)) domain)
 :hints (("Goal" :use fn-copod-checked-floor-domain))))
(local (defthm fn-copod-add-event
 (implies (fn-aed-add-roomp a b domain)
  (fn-copod-operationp (list :add (list a b)) domain))
 :hints (("Goal" :in-theory (enable fn-aed-add-roomp)))))
(local (defthm fn-copod-multiply-event
 (implies (fn-cop-times-roomp a b domain)
  (fn-copod-operationp (list :multiply (list a b)) domain))
 :hints (("Goal" :nonlinearp t :do-not '(generalize eliminate-destructors)
  :cases ((equal b 0))
  :use ((:instance linear-floor-bounds-1 (x domain) (y b)))
  :in-theory (e/d (fn-cop-times-roomp) (floor mod))))))
(local (defthm fn-copod-subtrace-proper
 (true-listp (fn-atsc-ops (fn-atsc-add-room a b domain)))))
(local (defthm fn-copod-floortrace-proper
 (true-listp (fn-atsc-ops (fn-copc-times-room a b domain)))))
(local (defthm fn-copod-append-proper
 (implies (true-listp b) (true-listp (fn-atsc-append a b)))
 :hints (("Goal" :induct (fn-atsc-append a b)))))
(local (defthm fn-copod-times-nats
 (implies (fn-cop-times-roomp a b domain) (and (natp a) (natp b) (natp domain)))
 :hints (("Goal" :in-theory (enable fn-cop-times-roomp)))
 :rule-classes :forward-chaining))
(defthm fn-copod-body-demand-material-operators-fit
 (fn-copod-operationsp
   (fn-atsc-ops (fn-copc-body-demand base per-input input per-level levels domain)) domain)
 :hints (("Goal" :in-theory
  (disable fn-atsc-add-room fn-aed-add-roomp fn-copc-times-room fn-cop-times-roomp
           fn-atsc-value fn-atsc-ops fn-atsc-sites fn-copod-operationp fn-atsc-append floor mod)))
 :rule-classes nil)
(local (defthm fn-copod-pack-ops
 (equal (fn-atsc-ops (fn-copc-pack value ops calls)) ops)
 :hints (("Goal" :in-theory (enable fn-copc-pack fn-atsc-ops fn-atsc-at)))))
(local (defthm fn-copod-vector-trace-proper
 (true-listp (fn-atsc-ops (fn-copc-vector-room used charged demand domain fuel)))
 :hints (("Goal" :induct (fn-copc-vector-room used charged demand domain fuel)
   :in-theory (disable fn-atsc-add-room fn-atsc-value fn-atsc-ops fn-atsc-sites fn-atsc-append)))))
(defthm fn-copod-vector-room-material-operators-fit
 (implies (and (natp fuel) (natp domain) (<= fuel domain))
  (fn-copod-operationsp
   (fn-atsc-ops (fn-copc-vector-room used charged demand domain fuel)) domain))
 :hints (("Goal" :induct (fn-copc-vector-room used charged demand domain fuel)
   :in-theory (disable fn-atsc-add-room fn-aed-add-roomp fn-atsc-value fn-atsc-ops
                       fn-atsc-sites fn-atsc-append)))
 :rule-classes nil)
(local (defthm fn-copod-vector-room-fit
 (implies (and (natp fuel) (natp domain) (<= fuel domain))
  (fn-copod-operationsp
   (fn-atsc-ops (fn-copc-vector-room used charged demand domain fuel)) domain))
 :hints (("Goal" :use fn-copod-vector-room-material-operators-fit))))
(defthm fn-copod-issuer-domain-material-operators-fit
 (implies (and (natp domain) (<= 5 domain))
  (fn-copod-operationsp (fn-atsc-ops (fn-copc-issuer-domain ledger demand domain)) domain))
 :hints (("Goal" :in-theory (disable fn-copc-vector-room fn-atsc-value fn-atsc-ops
                                   fn-atsc-sites fn-atsc-append)))
 :rule-classes nil)
(local (defthm fn-copod-octets-trace-proper
 (true-listp (fn-atsc-ops (fn-copc-octets-left x fuel)))
 :hints (("Goal" :induct (fn-copc-octets-left x fuel)))))
(defthm fn-copod-octets-left-material-operators-fit
 (implies (and (natp fuel) (natp domain) (<= fuel domain))
  (fn-copod-operationsp (fn-atsc-ops (fn-copc-octets-left x fuel)) domain))
 :hints (("Goal" :induct (fn-copc-octets-left x fuel)))
 :rule-classes nil)
(defthm fn-copod-octets-match-material-operators-fit
 (implies (and (natp fuel) (natp domain) (<= fuel domain))
  (fn-copod-operationsp (fn-atsc-ops (fn-copc-octets-match x y fuel)) domain))
 :hints (("Goal" :induct (fn-copc-octets-match x y fuel)))
 :rule-classes nil)
(local (defthm fn-copod-left-range
 (implies (natp fuel)
  (and (natp (mv-nth 1 (fn-cop-octets-left x fuel)))
       (<= (mv-nth 1 (fn-cop-octets-left x fuel)) fuel)))
 :hints (("Goal" :use fn-cop-octets-left-bounded :in-theory (disable fn-cop-octets-left)))
 :rule-classes :rewrite))
(local (defthm fn-copod-octets-fit
 (implies (and (natp fuel) (natp domain) (<= fuel domain))
  (fn-copod-operationsp (fn-atsc-ops (fn-copc-octets-left x fuel)) domain))
 :hints (("Goal" :use fn-copod-octets-left-material-operators-fit))))
(local (defthm fn-copod-left-linear
 (implies (natp fuel) (<= (mv-nth 1 (fn-cop-octets-left x fuel)) fuel))
 :hints (("Goal" :use fn-copod-left-range :in-theory (disable fn-cop-octets-left)))
 :rule-classes :linear))
(defthm fn-copod-input-left-material-operators-fit
 (implies (and (natp fuel) (natp domain) (<= fuel domain))
  (fn-copod-operationsp (fn-atsc-ops (fn-copc-input-left kind family address peer fuel)) domain))
 :hints (("Goal" :in-theory (disable fn-copc-octets-left fn-cop-octets-left fn-atsc-value
                                   fn-atsc-ops fn-atsc-sites fn-atsc-append)))
 :rule-classes nil)
(local (defthm fn-copod-input-range
 (implies (natp fuel)
  (and (natp (mv-nth 1 (fn-cop-input-left kind family address peer fuel)))
       (<= (mv-nth 1 (fn-cop-input-left kind family address peer fuel)) fuel)))
 :hints (("Goal" :in-theory (disable fn-cop-octets-left)))))
(local (defthm fn-copod-input-linear
 (implies (natp fuel) (<= (mv-nth 1 (fn-cop-input-left kind family address peer fuel)) fuel))
 :hints (("Goal" :use fn-copod-input-range :in-theory (disable fn-cop-input-left)))
 :rule-classes :linear))
(local (defthm fn-copod-input-proper
 (true-listp (fn-atsc-ops (fn-copc-input-left kind family address peer fuel)))
 :hints (("Goal" :in-theory (disable fn-copc-octets-left fn-atsc-ops fn-atsc-sites fn-atsc-value fn-atsc-append)))))
(local (defthm fn-copod-body-proper
 (true-listp (fn-atsc-ops (fn-copc-body-demand base per-input input per-level levels domain)))
 :hints (("Goal" :use fn-copod-body-demand-material-operators-fit
 :in-theory (disable fn-copc-body-demand fn-atsc-ops)))))
(local (defthm fn-copod-input-fit
 (implies (and (natp fuel) (natp domain) (<= fuel domain))
  (fn-copod-operationsp (fn-atsc-ops (fn-copc-input-left kind family address peer fuel)) domain))
 :hints (("Goal" :use fn-copod-input-left-material-operators-fit))))
(local (defthm fn-copod-body-fit
 (fn-copod-operationsp
   (fn-atsc-ops (fn-copc-body-demand base per-input input per-level levels domain)) domain)
 :hints (("Goal" :use fn-copod-body-demand-material-operators-fit))))
(defthm fn-copod-evaluate-material-operators-fit
 (fn-copod-operationsp
   (fn-atsc-ops (fn-copc-evaluate installation kind family address peer depth))
   (fn-omk-at 4 installation))
 :hints (("Goal" :in-theory
  (disable fn-copc-input-left fn-cop-input-left fn-copc-times-room fn-cop-times-roomp
           fn-copc-body-demand fn-cop-body-demand fn-atsc-value fn-atsc-ops
           fn-atsc-sites fn-atsc-append floor mod)))
 :rule-classes nil)
