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
 (defthm fn-ocb-reader-capture-of-install
   (equal (fn-owner-reader-views (fn-owner-install-ocfg oc fn-owner-st))
          (fn-owner-reader-views state))
   :hints (("Goal" :in-theory
            (enable fn-owner-reader-views fn-owner-install-ocfg)))))

(local
 (defthm fn-ocb-auth-of-install
   (equal (fn-owner-auth (fn-owner-install-ocfg oc fn-owner-st))
          (fn-owner-auth state))
   :hints (("Goal" :in-theory
            (enable fn-owner-auth fn-owner-install-ocfg)))))

(local
 (defthm fn-ocb-credits-of-install
   (equal (fn-owner-credits (fn-owner-install-ocfg oc fn-owner-st))
          (fn-owner-credits state))
   :hints (("Goal" :in-theory
            (e/d (fn-owner-credits fn-owner-credit-reserve
                  fn-owner-install-ocfg)
                 (get-global put-global boundp-global))))))

(local
 (defthm fn-ocb-get-of-same-put
   (equal (f-get-global key (f-put-global key value state)) value)
   :hints (("Goal" :in-theory (enable get-global put-global)))))

(local
 (defthm fn-ocb-bound-of-other-install
   (implies (not (equal key 'fn-owner))
            (equal (boundp-global key (fn-owner-install-ocfg oc fn-owner-st))
                   (boundp-global key state)))
   :hints (("Goal" :in-theory
            (e/d (fn-owner-install-ocfg)
                 (boundp-global get-global put-global))))))

(local
 (defthm fn-ocb-reader-capture-of-other-put
   (implies (not (equal key 'fn-owner-reader-views))
            (equal (fn-owner-reader-views (f-put-global key value state))
                   (fn-owner-reader-views state)))
   :hints (("Goal" :in-theory
            (e/d (fn-owner-reader-views) (get-global put-global boundp-global))))))

(local
 (defthm fn-ocb-auth-of-other-put
   (implies (not (equal key 'fn-owner-auth))
            (equal (fn-owner-auth (f-put-global key value state))
                   (fn-owner-auth state)))
   :hints (("Goal" :in-theory
            (e/d (fn-owner-auth) (get-global put-global boundp-global))))))

(defthm fn-owner-callback-close-complete-effects
  (let* ((oc (fn-owner-ocfg fn-owner-st))
         (next (fn-ocfg-close oc id))
         (credits (fn-mca-close (fn-owner-credits state) id))
         (actual (mv-nth 2 (fn-owner-callback-close id fn-arena fn-owner-st state))))
    (and (equal (mv-nth 0 (fn-owner-callback-close id fn-arena fn-owner-st state)) nil)
         (equal (mv-nth 1 (fn-owner-callback-close id fn-arena fn-owner-st state)) :closed)
         (equal (fn-owner-ocfg actual) next)
         (equal (f-get-global 'fn-owner-credits actual) credits)
         (equal (fn-owner-obligation-view actual) (fn-owner-obligation-view state))))
  :hints (("Goal" :in-theory
           (e/d (fn-owner-callback-close  fn-owner-put-credits)
                (get-global put-global boundp-global
                 fn-owner-credits fn-owner-credit-reserve)))))

(defthm fn-owner-callback-close-other-global-frame
  (implies (and (not (equal key 'fn-owner))
                (not (equal key 'fn-owner-credits)))
           (equal (f-get-global key
                    (mv-nth 2 (fn-owner-callback-close id fn-arena fn-owner-st state)))
                  (f-get-global key state)))
  :hints (("Goal" :in-theory
           (enable fn-owner-callback-close fn-owner-put-credits
                   fn-owner-install-ocfg ))))

(defthm fn-owner-callback-fault-complete-effects
  (let* ((owner (fn-owner-core fn-owner-st))
         (knownp (if (fn-own-find-conn id (fn-own-conns owner)) t nil))
         (result (fn-ocfg-fault (fn-owner-ocfg fn-owner-st) id))
         (effects (car result))
         (actual (mv-nth 2 (fn-owner-callback-fault id fn-owner-st state))))
    (and (equal (mv-nth 0 (fn-owner-callback-fault id fn-owner-st state)) nil)
         (equal (mv-nth 1 (fn-owner-callback-fault id fn-owner-st state))
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
                  fn-owner-credits fn-owner-credit-reserve)
                (get-global put-global boundp-global fn-ocfg-fault
                 fn-served-reply-octets fn-served-closingp
                 fn-served-starttlsp fn-served-submission)))))

(defthm fn-owner-callback-reader-open-reference-effects
  (implies
   (fn-ocl-relation
     (fn-ocfg-at-reader-view (fn-owner-ocfg fn-owner-st) (fn-owner-reader-views state)))
   (let* ((oc (fn-owner-ocfg fn-owner-st))
          (views (fn-owner-reader-views state))
          (working (fn-own-view (fn-ocfg-owner oc)))
          (selected (fn-ocfg-at-reader-view oc views))
          (opened (fn-ocfg-open selected (fn-owner-auth state)))
          (id (fn-own-next-id (fn-ocfg-owner selected)))
          (next (if (consp views) (fn-ocfg-with-view (cdr opened) working)
                  (cdr opened)))
          (actual (mv-nth 2 (fn-owner-callback-open fn-owner-st state))))
     (and (equal (mv-nth 0 (fn-owner-callback-open fn-owner-st state)) nil)
          (equal (mv-nth 1 (fn-owner-callback-open fn-owner-st state))
                 (if (fn-own-find-conn id
                       (fn-own-conns (fn-ocfg-owner (cdr opened)))) id nil))
          (equal (fn-owner-ocfg actual) next)
          (equal (f-get-global 'fn-owner-effects actual) (car opened))
          (equal (f-get-global 'fn-owner-output actual)
                 (fn-served-reply-octets (car opened)))
          (equal (f-get-global 'fn-owner-closep actual)
                 (fn-served-closingp (car opened)))
          (equal (f-get-global 'fn-owner-starttlsp actual)
                 (if (fn-served-starttlsp (car opened)) t nil))
          (equal (f-get-global 'fn-owner-submittedp actual)
                 (if (fn-served-submission (car opened)) t nil))
          (equal (f-get-global 'fn-owner-log-line actual)
                 (fn-olog-connection-line (fn-ocfg-owner (cdr opened)) id nil))
          (equal (fn-owner-reader-views actual) views)
          (equal (fn-owner-obligation-view actual) (fn-owner-obligation-view state))
          (equal (f-get-global 'fn-owner-credits actual)
                 (f-get-global 'fn-owner-credits state)))))
  :hints (("Goal"
           :use ((:instance fn-ocar-ocfg-open-is-ocfg-open-under-ocl-relation
                   (oc (fn-ocfg-at-reader-view
                         (fn-owner-ocfg fn-owner-st) (fn-owner-reader-views state)))
                   (acfg (fn-owner-auth state))))
           :in-theory
           (e/d (fn-owner-callback-open fn-owner-callback-open-at
                 fn-owner-callback-at-reader-view fn-owner-callback-at-working-view
                 fn-owner-callback-install-effects fn-owner-install-served-effects
                  fn-owner-core fn-ocfg-at-reader-view
                 )
                (fn-ocl-relation fn-ocar-ocfg-open fn-ocfg-open
                 fn-ocfg-with-view get-global put-global boundp-global
                 fn-served-reply-octets fn-served-closingp
                 fn-served-starttlsp fn-served-submission
                 fn-olog-connection-line fn-own-with-view
                 fn-owner-reader-views fn-owner-auth)))))

(defthm fn-owner-callback-peer-open-complete-effects
  (let* ((peer (fn-store-octets->string peer-octets))
         (id (fn-own-next-id (fn-owner-core fn-owner-st)))
         (opened (fn-ocfg-open-peer (fn-owner-ocfg fn-owner-st) peer (fn-owner-auth state)))
         (actual (mv-nth 2 (fn-owner-callback-open-peer peer-octets fn-owner-st state))))
    (and
     (equal (mv-nth 0 (fn-owner-callback-open-peer peer-octets fn-owner-st state)) nil)
     (if (equal peer :bad)
         (and (equal (mv-nth 1 (fn-owner-callback-open-peer peer-octets fn-owner-st state)) nil)
              (equal actual state))
       (and
        (equal (mv-nth 1 (fn-owner-callback-open-peer peer-octets fn-owner-st state))
               (if (fn-own-find-conn id
                     (fn-own-conns (fn-ocfg-owner (cdr opened)))) id nil))
        (equal (fn-owner-ocfg actual) (cdr opened))
        (equal (f-get-global 'fn-owner-effects actual) (car opened))
        (equal (f-get-global 'fn-owner-output actual)
               (fn-served-reply-octets (car opened)))
        (equal (f-get-global 'fn-owner-closep actual)
               (fn-served-closingp (car opened)))
        (equal (f-get-global 'fn-owner-starttlsp actual)
               (if (fn-served-starttlsp (car opened)) t nil))
        (equal (f-get-global 'fn-owner-submittedp actual)
               (if (fn-served-submission (car opened)) t nil))
        (equal (f-get-global 'fn-owner-log-line actual)
               (fn-olog-connection-line (fn-ocfg-owner (cdr opened)) id peer-octets))
        (equal (fn-owner-obligation-view actual) (fn-owner-obligation-view state))
        (equal (fn-owner-reader-views actual) (fn-owner-reader-views state))
        (equal (f-get-global 'fn-owner-credits actual)
               (f-get-global 'fn-owner-credits state))))))
  :hints (("Goal" :in-theory
           (e/d (fn-owner-callback-open-peer fn-owner-callback-install-effects
                 fn-owner-install-served-effects  fn-owner-core
                 fn-owner-credits fn-owner-credit-reserve)
                (get-global put-global boundp-global fn-ocfg-open-peer
                 fn-olog-connection-line fn-owner-reader-views fn-owner-auth
                 fn-store-octets->string
                 fn-served-reply-octets fn-served-closingp
                 fn-served-starttlsp fn-served-submission)))))

(defthm fn-owner-callback-exposure-open-reference-effects
  (implies
   (fn-ocl-relation (fn-owner-ocfg fn-owner-st))
   (let* ((peer0 (and peer-octets (fn-store-octets->string peer-octets)))
          (peer (if (equal peer0 :bad) nil peer0))
          (id (fn-own-next-id (fn-owner-core fn-owner-st)))
          (r (fn-exp-open (fn-owner-ocfg fn-owner-st) (fn-owner-exposure-state state)
               (fn-owner-callback-exposure-limits fn-owner-st state) (fn-owner-auth state)
               peer (cons family address) (fn-owner-exposure-now fn-owner-st)))
          (effects (fn-exp-open-effects r))
          (actual (mv-nth 2 (fn-owner-callback-exposure-open
                              family address peer-octets fn-owner-st state))))
     (and
      (equal (mv-nth 0 (fn-owner-callback-exposure-open
                         family address peer-octets fn-owner-st state)) nil)
      (equal (mv-nth 1 (fn-owner-callback-exposure-open
                         family address peer-octets fn-owner-st state)) (fn-exp-open-id r))
      (equal (fn-owner-ocfg actual) (fn-exp-open-ocfg r))
      (equal (f-get-global 'fn-owner-exposure actual) (fn-exp-open-state r))
      (equal (fn-owner-obligation-view actual) (fn-owner-obligation-view state))
      (equal (fn-owner-reader-views actual) (fn-owner-reader-views state))
      (equal (f-get-global 'fn-owner-credits actual)
             (f-get-global 'fn-owner-credits state))
      (if (fn-exp-open-id r)
          (and
           (equal (f-get-global 'fn-owner-effects actual) effects)
           (equal (f-get-global 'fn-owner-output actual) (fn-served-reply-octets effects))
           (equal (f-get-global 'fn-owner-closep actual) (fn-served-closingp effects))
           (equal (f-get-global 'fn-owner-starttlsp actual)
                  (if (fn-served-starttlsp effects) t nil))
           (equal (f-get-global 'fn-owner-submittedp actual)
                  (if (fn-served-submission effects) t nil))
           (equal (f-get-global 'fn-owner-log-line actual)
                  (fn-olog-connection-line (fn-ocfg-owner (fn-exp-open-ocfg r))
                    id (and peer peer-octets))))
        (and
         (equal (f-get-global 'fn-owner-effects actual) nil)
         (equal (f-get-global 'fn-owner-output actual) (fn-exp-open-refusal r))
         (equal (f-get-global 'fn-owner-closep actual)
                (and (fn-exp-open-refusal r) t))
         (equal (f-get-global 'fn-owner-starttlsp actual) nil)
         (equal (f-get-global 'fn-owner-submittedp actual) nil)
         (equal (f-get-global 'fn-owner-log-line actual)
                (f-get-global 'fn-owner-log-line state)))))))
  :hints (("Goal"
           :use ((:instance fn-ocar-exp-open-is-exp-open-under-ocl-relation
                   (oc (fn-owner-ocfg fn-owner-st))
                   (xs (fn-owner-exposure-state state))
                   (lim (fn-owner-callback-exposure-limits fn-owner-st state))
                   (acfg (fn-owner-auth state))
                   (peer (let ((p (and peer-octets (fn-store-octets->string peer-octets))))
                           (if (equal p :bad) nil p)))
                   (address (cons family address))
                   (now (fn-owner-exposure-now fn-owner-st))))
           :in-theory
           (e/d (fn-owner-callback-exposure-open fn-owner-callback-install-effects
                 fn-owner-install-served-effects  fn-owner-core
                 fn-owner-credits fn-owner-credit-reserve)
                (fn-ocl-relation fn-ocar-exp-open fn-exp-open
                 get-global put-global boundp-global fn-olog-connection-line
                 fn-owner-reader-views fn-owner-auth
                 fn-owner-callback-exposure-limits fn-owner-exposure-state
                 fn-owner-exposure-now fn-store-octets->string
                 fn-exp-open-ocfg fn-exp-open-state fn-exp-open-id
                 fn-exp-open-effects fn-exp-open-refusal
                 fn-served-reply-octets fn-served-closingp
                 fn-served-starttlsp fn-served-submission)))))
