; Caller retains continuous owner exclusion through recheck/adoption/attachment.
; Every resumed call rechecks actual authority again.
; Actual incoming source/attachment producer. No host-supplied context, source,
; frontier, demand or prepared controller is accepted by the public ABI.
(in-package "ACL2")
(logic)
(include-book "../books/index-incoming-request")
(include-book "../books/owner-incoming-freshness")
(include-book "../books/receiver-query-freshness")
(include-book "../books/payload-arena")
(include-book "../books/incoming-copy-association")

(defun fn-iiq-freshness-matches-context (saved context)
 (declare (xargs :guard t))
 (and (eq (fn-cp-nth 0 saved) :incoming-freshness)
      (eq (fn-cp-nth 1 saved) :awaiting-query)
      (null (fn-cp-nth 11 saved))
      (fn-iiq-context-ready-p context)
      (fn-iaf-holder= (fn-cp-nth 2 saved) (fn-cp-nth 1 context))
      (equal (fn-cp-nth 3 saved) (fn-cp-nth 2 context))
      (fn-iaf-octets= 32 (fn-cp-nth 4 saved)
                        (fn-cp-nth 1 (fn-cp-nth 9 context)))))

; Internal result constructor only. The actual producer invokes it solely
; with the token returned by the successful child+pool adoption below.
(defun fn-iiq-attached-freshness (saved token)
 (declare (xargs :guard t))
 (list (fn-cp-nth 0 saved) :query-attached (fn-cp-nth 2 saved)
       (fn-cp-nth 3 saved) (fn-cp-nth 4 saved) (fn-cp-nth 5 saved)
       (fn-cp-nth 6 saved) (fn-cp-nth 7 saved) (fn-cp-nth 8 saved)
       (fn-cp-nth 9 saved) (fn-cp-nth 10 saved) token))

(include-book "../books/index-incoming-input-source")

(defun fn-iiq-input-source= (x y)
 (declare (xargs :guard t))
 (and (eq (fn-cp-nth 0 x) :incoming-input-source)
      (eq (fn-cp-nth 0 y) :incoming-input-source)
      (fn-iaf-holder= (fn-cp-nth 1 x) (fn-cp-nth 1 y))
      (equal (fn-cp-nth 1 (fn-cp-nth 2 x)) (fn-cp-nth 1 (fn-cp-nth 2 y)))
      (equal (fn-cp-nth 2 (fn-cp-nth 2 x)) (fn-cp-nth 2 (fn-cp-nth 2 y)))
      (equal (fn-cp-nth 3 x) (fn-cp-nth 3 y))
      (equal (fn-cp-nth 4 x) (fn-cp-nth 4 y))))

; Internal reconstruction only: SOURCE is the immediately preceding actual
; producer result. An already retained source is never replaced by a resume.
(defun fn-iiq-keep-input-source (source fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard t))
 (let* ((receipt (fn-ibp-request-pending fn-index-backing))
        (request (fn-iiq-receipt-request receipt))
        (old (fn-cp-nth 9 request)))
  (cond (old (mv (if (fn-iiq-input-source= old source) :source-kept :recovery-required)
                 fn-index-backing))
   (t
    (let ((request (list (fn-cp-nth 0 request) (fn-cp-nth 1 request)
                  (fn-cp-nth 2 request) (fn-cp-nth 3 request) (fn-cp-nth 4 request)
                  (fn-cp-nth 5 request) (fn-cp-nth 6 request) (fn-cp-nth 7 request)
                  (fn-cp-nth 8 request) source)))
     (mv :source-kept
      (update-fn-ibp-request-pending
       (list (fn-cp-nth 0 receipt) (fn-cp-nth 1 receipt) (fn-cp-nth 2 receipt)
             (fn-cp-nth 3 receipt) (fn-cp-nth 4 receipt) (fn-cp-nth 5 receipt)
             request (fn-cp-nth 7 receipt) (fn-cp-nth 8 receipt) (fn-cp-nth 9 receipt))
       fn-index-backing)))))))

; Internal suffix ONLY after the actual operation issuer returns demand and
; scratch. Its vector arguments are not a native/public admission interface.
(defun fn-owner-index-incoming-begin-issued
 (context publication gen-token demand scratch fuel fn-input-copy fn-mio$c fn-arena fn-page-read-pool state)
 (declare (xargs :stobjs (fn-input-copy fn-mio$c fn-arena fn-page-read-pool state)
                 :guard (natp fuel) :verify-guards nil)
          (ignore fn-arena))
 (if (not (fn-iiq-freshness-matches-context
           (fn-owner-incoming-freshness-state state) context))
     (mv nil :recapture-required nil fuel fn-mio$c fn-page-read-pool state)
  (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
   (word nonce fn-index-backing fn-page-read-pool)
   (fn-iiq-reserve-or-resume context publication gen-token demand fn-index-backing fn-page-read-pool)
   (if (not (eq word :reserved))
       (mv nil word nil fuel fn-mio$c fn-page-read-pool state)
    (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
     (word fn-index-backing fn-page-read-pool)
     (fn-iiq-reserve-scratch nonce scratch fn-index-backing fn-page-read-pool)
     (if (not (eq word :reserved))
         (mv nil word nil fuel fn-mio$c fn-page-read-pool state)
      (mv-let (source-word source)
       (fn-iiq-completed-input-source context fn-input-copy fn-page-read-pool)
       (if (not (eq source-word :source-current))
           (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
            (attempted)
            (fn-iiq-attempted-token fn-index-backing)
            (mv (if attempted :incoming-source-uncertain nil)
                (if attempted :recovery-required source-word) attempted fuel
                fn-mio$c fn-page-read-pool state))
        (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
         (keep-word attempted fn-index-backing)
         (mv-let (keep-word fn-index-backing)
          (fn-iiq-keep-input-source source fn-index-backing)
          (mv keep-word (fn-iiq-attempted-token fn-index-backing) fn-index-backing))
         (if (not (eq keep-word :source-kept))
             (mv :incoming-source-changed keep-word attempted fuel fn-mio$c fn-page-read-pool state)
      (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
       (word left fn-index-backing)
       (fn-iiq-retain-generation fuel fn-index-backing)
       (if (not (eq word :retained))
           (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
            (attempted)
            (fn-iiq-attempted-token fn-index-backing)
            (mv (if attempted :incoming-adoption-uncertain nil) word attempted left
                fn-mio$c fn-page-read-pool state))
        (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
         (word token left fn-index-backing fn-page-read-pool)
         (fn-iiq-adopt-pending left fn-index-backing fn-page-read-pool)
         (if (not (eq word :captured))
             (mv (if (eq word :recovery-required) :incoming-adoption-uncertain nil)
                 word token left fn-mio$c fn-page-read-pool state)
           (let* ((saved (fn-owner-incoming-freshness-state state))
                  (current (fn-owner-incoming-context-read fn-page-read-pool state)))
            (if (not (and (fn-ibp-query-tokenp token)
                          (fn-iiq-freshness-matches-context saved current)))
                (mv :incoming-authority-lost :recovery-required token left
                    fn-mio$c fn-page-read-pool state)
              (let ((state (f-put-global 'fn-owner-incoming-freshness
                            (fn-iiq-attached-freshness saved token) state)))
               (mv nil :captured token left fn-mio$c fn-page-read-pool state))))))))))))))))))

; The actual public producer derives authority and publication internally.
; Current source read authenticates actual registered live/current generation.
; Missing constructor/scratch/runtime installation remains unavailable.
(defun fn-owner-index-incoming-begin (fuel fn-input-copy fn-mio$c fn-arena fn-page-read-pool state)
 (declare (xargs :stobjs (fn-input-copy fn-mio$c fn-arena fn-page-read-pool state)
                 :guard (natp fuel) :verify-guards nil))
 (cond
  ((not (boundp-global 'fn-owner state))
   (mv nil :authority-unavailable nil fuel fn-mio$c fn-page-read-pool state))
  ((not (fn-iiq-freshness-matches-context (fn-owner-incoming-freshness-state state)
           (fn-owner-incoming-context-read fn-page-read-pool state)))
   (mv nil :recapture-required nil fuel fn-mio$c fn-page-read-pool state))
  (t
   (mv-let (word fn-page-read-pool state)
    (fn-owner-incoming-authority-recheck fn-page-read-pool state)
    (if (not (eq word :authority-current))
        (mv nil word nil fuel fn-mio$c fn-page-read-pool state)
     (mv-let (word publication left)
      (fn-mio-current-publication-read fuel fn-mio$c)
      (if (not (eq word :published))
          (mv nil word nil left fn-mio$c fn-page-read-pool state)
       (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
        (word demand scratch)
        (fn-iiq-installed-runtime-source fn-index-backing)
        (if (not (eq word :ready))
            (mv nil :unavailable nil left fn-mio$c fn-page-read-pool state)
          (let* ((association (fn-ibp-current-publication fn-mio$c))
                 (gen-token (fn-omk-at 1 association))
                 (context (fn-owner-incoming-context-read fn-page-read-pool state)))
           (fn-owner-index-incoming-begin-issued context publication gen-token demand scratch
            left fn-input-copy fn-mio$c fn-arena fn-page-read-pool state)))))))))))

(verify-guards fn-owner-index-incoming-begin-issued
 :hints (("Goal" :in-theory (disable fn-iiq-reserve-or-resume fn-iiq-reserve-scratch
  fn-iiq-retain-generation fn-iiq-adopt-pending fn-mio$cp fn-index-backingp))))
(verify-guards fn-owner-index-incoming-begin
 :hints (("Goal" :in-theory (disable fn-owner-incoming-authority-recheck
  fn-mio-current-publication-read fn-owner-index-incoming-begin-issued fn-mio$cp))))

(defthm fn-owner-index-incoming-captured-attaches-exact-returned-token
 (implies
  (equal (mv-nth 1 (fn-owner-index-incoming-begin-issued context publication gen-token
                   demand scratch fuel fn-input-copy fn-mio$c fn-arena fn-page-read-pool state)) :captured)
  (equal
   (fn-cp-nth 11 (fn-owner-incoming-freshness-state
    (mv-nth 6 (fn-owner-index-incoming-begin-issued context publication gen-token
               demand scratch fuel fn-input-copy fn-mio$c fn-arena fn-page-read-pool state))))
   (mv-nth 2 (fn-owner-index-incoming-begin-issued context publication gen-token
              demand scratch fuel fn-input-copy fn-mio$c fn-arena fn-page-read-pool state))))
 :rule-classes nil
 :hints (("Goal" :in-theory
  (e/d (fn-owner-incoming-freshness-state fn-iiq-attached-freshness)
       (fn-iiq-reserve-or-resume fn-iiq-reserve-scratch fn-iiq-retain-generation
        fn-iiq-adopt-pending fn-owner-incoming-context-read fn-cp-nth)))))
