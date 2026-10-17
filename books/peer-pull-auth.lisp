; fn: a pull credential independent of the outbound feed (PKT-431).
; This is an extension row, so peer set preserves it and peer add replaces
; it with the rest of the record. Absent means the legacy outbound policy;
; an empty profile explicitly means anonymous, never inheritance.
(in-package "ACL2")
(include-book "peer-config")
(include-book "peer-carriage-rows")
(local (in-theory (disable (tau-system))))

(defun fn-pull-auth-row (name profile allow-clear)
  (declare (xargs :guard t))
  (fn-cfg-row-make name *fn-pcb-pull-auth-slot* profile
                   (if allow-clear 1 0)))

(defun fn-pull-auth-of-rows (rows)
  (declare (xargs :guard t))
  (let ((pa (fn-cfg-peer-slot rows *fn-pcb-pull-auth-slot*))
        (oa (fn-cfg-peer-slot rows "outbound-auth-profile")))
    (cond (pa (if (equal (fn-cfg-row-c pa) "") nil
                (list :authinfo (fn-cfg-row-c pa) (equal (fn-cfg-row-n pa) 1))))
          ((and oa (stringp (fn-cfg-row-c oa)))
           (list :authinfo (fn-cfg-row-c oa) (equal (fn-cfg-row-n oa) 1)))
          (t nil))))

(local
 (defthm fn-pulla-slot-of-append
   (implies slot
            (equal (fn-cfg-peer-slot (append a b) slot)
                   (or (fn-cfg-peer-slot a slot) (fn-cfg-peer-slot b slot))))
   :hints (("Goal" :in-theory (enable fn-cfg-peer-slot fn-cfg-row-b
                                      fn-cfg-ag-car fn-cfg-ag-cdr)))))

(local
 (defthm fn-pulla-kept-slot
   (equal (fn-cfg-peer-slot
           (fn-pcb-kept-rows rows (list (fn-pull-auth-row name profile allow-clear)))
           "pull-auth-profile") nil)
   :hints (("Goal"
            :induct (fn-pcb-kept-rows rows (list (fn-pull-auth-row name profile allow-clear)))
            :in-theory (enable fn-pcb-kept-rows fn-pcb-row-supersededp
                               fn-pcb-budget-slotp fn-pcb-slot-memberp
                               fn-cfg-peer-slot fn-cfg-row-b fn-cfg-row-make
                               fn-cfg-ag-car fn-cfg-ag-cdr)))))

(local
 (defthm fn-pulla-row-fields
   (and (consp (fn-pull-auth-row name profile allow-clear))
        (equal (fn-cfg-row-b (fn-pull-auth-row name profile allow-clear))
               "pull-auth-profile")
        (equal (fn-cfg-row-c (fn-pull-auth-row name profile allow-clear)) profile)
        (equal (fn-cfg-row-n (fn-pull-auth-row name profile allow-clear))
               (if allow-clear 1 0)))))

; Extension replaces the prior pull policy, including an explicit anonymous
; choice, without consulting either presence or contents of outbound rows.
(defthm fn-pull-auth-after-extension
  (equal (fn-pull-auth-of-rows
          (fn-pcb-extend-rows rows (list (fn-pull-auth-row name profile allow-clear))))
         (if (equal profile "") nil
           (list :authinfo profile (if allow-clear t nil))))
  :hints (("Goal" :in-theory (e/d (fn-pcb-extend-rows fn-cfg-peer-slot)
                                  (fn-pull-auth-row)))))

(in-theory (disable fn-pull-auth-row fn-pull-auth-of-rows))
