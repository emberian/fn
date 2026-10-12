; Named immutable launch coordinates beside the live capacity.
(in-package "ACL2")
(include-book "acceptance-alloc")
(include-book "defrecord")
(include-book "heap-command")
(include-book "runtime-contract-host-pool")
(fn-defrecord fn-menv
 :constructor (fn-menv-make resident output peer workers cache-limit root bp-terms core nursery)
 :fields ((fn-menv-resident t) (fn-menv-output t) (fn-menv-peer t) (fn-menv-workers t)
          (fn-menv-cache-limit t) (fn-menv-root t) (fn-menv-bp-terms t)
          (fn-menv-core t) (fn-menv-nursery t)))
(defun fn-adm-installed-lease-octets (profile cfg quantum)
 (declare (xargs :guard t))
 (let ((c (fn-hl-rtc-config profile cfg quantum 1 0 0)))
  (* (fn-rtc-npool c) (fn-rtc-capl c))))

; The slot/mstate arrays and buffer metadata are permanent too. Their
; original fixed connection term remains charged beside the octet bank.
(defun fn-adm-installed-lease-allocation (profile cfg quantum)
 (declare (xargs :guard t))
 (+ (fn-adm-installed-lease-octets profile cfg quantum)
    (* (fn-mm-cfg-connections cfg) (fn-mm-connection-fixed profile cfg))))

; The first search sizes the physical bank. The second searches reader
; capacity with that exact bank charged as fixed runtime. Reader capacity
; can later change without changing the installed bank or its charge.
(defun fn-adm-lease-startup-bank-cfg (profile img cfg limit tot)
 (declare (xargs :guard t))
 (fn-adm-cfg-at cfg (fn-adm-installed-capacity profile img cfg limit tot)))

(defun fn-adm-lease-startup-cfg (profile img cfg limit tot quantum)
 (declare (xargs :guard t))
 (fn-adm-retained-runtime-cfg cfg
  (if (natp quantum)
   (fn-adm-installed-lease-allocation profile
    (fn-adm-lease-startup-bank-cfg profile img cfg limit tot) quantum) 0)))

(defthm fn-adm-startup-bank-charge-by-definition
 (equal (fn-mm-cfg-cold (fn-adm-lease-startup-cfg profile img cfg limit tot quantum))
  (+ (fn-mm-cfg-cold cfg)
     (if (natp quantum)
      (fn-adm-installed-lease-allocation profile
       (fn-adm-lease-startup-bank-cfg profile img cfg limit tot) quantum) 0)))
 :hints (("Goal" :in-theory (e/d
  (fn-adm-lease-startup-cfg fn-adm-retained-runtime-cfg fn-mm-cfg-cold fn-mm-nat)
  (fn-adm-installed-lease-allocation fn-adm-lease-startup-bank-cfg)))))
