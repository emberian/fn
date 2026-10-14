; Actual callback output and complete STATE projection boundaries.
; Installed source/physical authority remains a separate caller obligation.
(in-package "ACL2")

(include-book "owner-connection-callbacks")

(local
 (defthm fn-ocb-get-of-other-put
   (implies (not (equal key written))
            (equal (f-get-global key (f-put-global written value state))
                   (f-get-global key state)))
   :hints (("Goal" :in-theory (enable get-global put-global)))))

(local
 (defthm fn-ocb-bound-of-other-put
   (implies (not (equal key written))
            (equal (boundp-global key (f-put-global written value state))
                   (boundp-global key state)))
   :hints (("Goal" :in-theory (enable boundp-global put-global)))))







(local
 (defthm fn-ocb-get-of-same-put
   (equal (f-get-global key (f-put-global key value state)) value)
   :hints (("Goal" :in-theory (enable get-global put-global)))))

(local
 (defthm fn-ocb-bound-of-other-install
   (implies (not (equal key 'fn-owner))
            (equal (boundp-global key (fn-owner-install-ocfg oc state))
                   (boundp-global key state)))
   :hints (("Goal" :in-theory
            (e/d (fn-owner-install-ocfg)
                 (boundp-global get-global put-global))))))





;; M28 (R4 follow-up): installing the configured owner leaves the owner's credits unchanged.
(local
 (defthm m28-credits-of-install-ocfg
  (equal (fn-owner-credits (fn-owner-install-ocfg oc state)) (fn-owner-credits state))
  :hints (("Goal" :in-theory (enable fn-owner-credits fn-owner-install-ocfg fn-owner-credit-reserve)))))

(defthm fn-owner-callback-close-complete-effects
  (let* ((oc (fn-owner-ocfg state))
         (next (fn-ocfg-close oc id))
         (credits (fn-mca-close (fn-owner-credits state) id))
         (actual (mv-nth 2 (fn-owner-callback-close id fn-arena state))))
    (and (equal (mv-nth 0 (fn-owner-callback-close id fn-arena state)) nil)
         (equal (mv-nth 1 (fn-owner-callback-close id fn-arena state)) :closed)
         (equal (fn-owner-ocfg actual) next)
         (equal (f-get-global 'fn-owner-credits actual) credits)
         (equal (fn-owner-obligation-view actual) (fn-owner-obligation-view state))))
  :hints (("Goal" :in-theory
           (e/d (fn-owner-callback-close fn-owner-ocfg fn-owner-put-credits)
                (get-global put-global boundp-global
                 fn-owner-credits fn-owner-credit-reserve)))))

(defthm fn-owner-callback-close-other-global-frame
  (implies (and (not (equal key 'fn-owner))
                (not (equal key 'fn-owner-credits)))
           (equal (f-get-global key
                    (mv-nth 2 (fn-owner-callback-close id fn-arena state)))
                  (f-get-global key state)))
  :hints (("Goal" :in-theory
           (enable fn-owner-callback-close fn-owner-put-credits
                   fn-owner-install-ocfg fn-owner-ocfg))))

(defthm fn-owner-callback-fault-complete-effects
  (let* ((owner (fn-owner-core state))
         (knownp (if (fn-own-find-conn id (fn-own-conns owner)) t nil))
         (result (fn-ocfg-fault (fn-owner-ocfg state) id))
         (effects (car result))
         (actual (mv-nth 2 (fn-owner-callback-fault id state))))
    (and (equal (mv-nth 0 (fn-owner-callback-fault id state)) nil)
         (equal (mv-nth 1 (fn-owner-callback-fault id state))
                (if knownp :faulted :unknown))
         (equal (fn-owner-ocfg actual) (cdr result))
         (equal (f-get-global 'fn-owner-effects actual) effects)
         (equal (f-get-global 'fn-owner-output actual)
                (fn-served-reply-octets effects))
         (equal (f-get-global 'fn-owner-closep actual)
                (fn-served-closingp effects))
         (equal (f-get-global 'fn-owner-starttlsp actual)
                (if (fn-served-starttlsp effects) t nil))
         (equal (f-get-global 'fn-owner-submittedp actual)
                (if (fn-served-submission effects) t nil))
         (equal (f-get-global 'fn-owner-credits actual)
                (fn-mca-close (fn-owner-credits state) id))
         (equal (fn-owner-obligation-view actual) (fn-owner-obligation-view state))))
  :hints (("Goal" :in-theory
           (e/d (fn-owner-callback-fault fn-owner-callback-install-effects
                 fn-owner-install-served-effects fn-owner-put-credits
                 fn-owner-ocfg fn-owner-credits fn-owner-credit-reserve)
                (get-global put-global boundp-global fn-ocfg-fault
                 fn-served-reply-octets fn-served-closingp
                 fn-served-starttlsp fn-served-submission)))))

; The served held exposure subject installs its decision, including the bank.
; This is the concrete projection equation; no reference-only twin survives.
(local (defthm fn-ocb-bound-of-same-put
 (boundp-global key (f-put-global key value state))
 :hints (("Goal" :in-theory (enable boundp-global put-global)))))

(defthm fn-owner-held-callback-exposure-open-installed-coordinates-unfolds
 (let* ((peer0 (and peer-octets (fn-store-octets->string peer-octets)))
        (peer (if (equal peer0 :bad) nil peer0))
        (id (fn-own-next-id (fn-owner-core state)))
        (decision
         (if rearm
           (fn-adm-transport-rearm :exposure (fn-owner-ocfg state)
             (fn-owner-exposure-state state) (fn-owner-callback-exposure-limits state)
             (fn-owner-auth state) peer (cons family address) (fn-owner-exposure-now state)
             (fn-owner-memory-held-bank state) old-id
             (fn-owner-held-callback-configured state) (fn-owner-memory-capacity-read state))
           (fn-adm-exposure-open (fn-owner-ocfg state) (fn-owner-exposure-state state)
             (fn-owner-callback-exposure-limits state) (fn-owner-auth state) peer
             (cons family address) (fn-owner-exposure-now state)
             (fn-owner-memory-held-bank state) (fn-owner-held-callback-configured state)
             (fn-owner-memory-capacity-read state))))
        (r (fn-exp-at 1 decision))
        (actual (mv-nth 2 (fn-owner-held-callback-exposure-open
                            family address peer-octets rearm old-id state))))
   (and (equal (mv-nth 0 (fn-owner-held-callback-exposure-open
                           family address peer-octets rearm old-id state)) nil)
        (equal (mv-nth 1 (fn-owner-held-callback-exposure-open
                           family address peer-octets rearm old-id state))
               (if (equal (car decision) :admit) (fn-exp-open-id r) nil))
        (equal (fn-owner-memory-held-bank actual) (fn-exp-at 2 decision))
        (equal (fn-owner-ocfg actual) (fn-exp-open-ocfg r))
        (equal (f-get-global 'fn-owner-exposure actual) (fn-exp-open-state r))
        (equal (f-get-global 'fn-owner-log-line actual)
               (if (equal (car decision) :admit)
                   (fn-olog-socket-connection-line (fn-ocfg-owner (fn-exp-open-ocfg r))
                     id (and peer peer-octets) family address)
                 (f-get-global 'fn-owner-log-line state)))))
 :rule-classes nil
 :hints (("Goal" :in-theory
  (e/d (fn-owner-held-callback-exposure-open fn-owner-memory-held-install
        fn-owner-memory-held-bank fn-owner-callback-install-effects
        fn-owner-install-served-effects fn-owner-ocfg fn-owner-core
        fn-owner-install-ocfg)
       (get-global put-global boundp-global
        fn-adm-exposure-open fn-adm-transport-rearm fn-owner-held-callback-configured
        fn-owner-memory-capacity-read fn-owner-callback-exposure-limits
        fn-owner-exposure-state fn-owner-exposure-now fn-owner-auth
        fn-store-octets->string fn-exp-at fn-exp-open-id fn-exp-open-ocfg
        fn-exp-open-state fn-exp-open-effects fn-exp-open-refusal
        fn-olog-socket-connection-line fn-owner-installed-owner-bound)))))
