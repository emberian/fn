(in-package "ACL2")
(include-book "index-reader-request")
(include-book "index-reader-render-slot")
; Private bounded directory action. Both actions derive the SAME slot context;
; no tuple crosses the borrowed child scope.
(defun fn-irc-node-render-action (token operation fuel slot depth fn-ibp-node fn-render-holder)
 (declare (xargs :stobjs (fn-ibp-node fn-render-holder) :measure (nfix depth)
                 :guard (and (fn-ibp-query-tokenp token) (natp fuel)
                             (natp slot) (natp depth)
                             (member-eq operation '(:intent :install)))
                 :verify-guards nil))
 (cond
  ((<= fuel depth) (mv :yield fuel fn-ibp-node fn-render-holder))
  ((zp depth)
   (if (not (fn-ibp-node-children-boundp 'fn-ibp-query-segment fn-ibp-node))
       (mv :unavailable fuel fn-ibp-node fn-render-holder)
    (stobj-let ((fn-ibp-query-segment
                 (fn-ibp-node-children-get 'fn-ibp-query-segment fn-ibp-node
                                           (create-fn-ibp-query-segment))))
     (word fn-ibp-query-segment fn-render-holder)
     (if (eq operation :intent)
         (mv-let (word fn-ibp-query-segment)
          (fn-irc-slot-render-intent token fn-ibp-query-segment)
          (mv word fn-ibp-query-segment fn-render-holder))
       (fn-irc-slot-render-install token fn-ibp-query-segment fn-render-holder))
     (mv word (- fuel 1) fn-ibp-node fn-render-holder))))
  ((equal (mod slot 2) 0)
   (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-left fn-ibp-node))
       (mv :unavailable fuel fn-ibp-node fn-render-holder)
    (stobj-let ((fn-ibp-node-left
                 (fn-ibp-node-children-get 'fn-ibp-node-left fn-ibp-node
                                           (create-fn-ibp-node-left))))
     (word left fn-ibp-node-left fn-render-holder)
     (fn-irc-node-render-action token operation (- fuel 1) (floor slot 2)
                                (- depth 1) fn-ibp-node-left fn-render-holder)
     (mv word left fn-ibp-node fn-render-holder))))
  (t
   (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-right fn-ibp-node))
       (mv :unavailable fuel fn-ibp-node fn-render-holder)
    (stobj-let ((fn-ibp-node-right
                 (fn-ibp-node-children-get 'fn-ibp-node-right fn-ibp-node
                                           (create-fn-ibp-node-right))))
     (word left fn-ibp-node-right fn-render-holder)
     (fn-irc-node-render-action token operation (- fuel 1) (floor slot 2)
                                (- depth 1) fn-ibp-node-right fn-render-holder)
     (mv word left fn-ibp-node fn-render-holder))))))
(verify-guards fn-irc-node-render-action)

; Host-called token-only constructor. Preflight covers five authorization
; traversals plus intent and installation, before the first mutation.
(defun fn-irc-registered-render-install (token fuel fn-mio$c fn-render-holder)
 (declare (xargs :stobjs (fn-mio$c fn-render-holder) :guard (natp fuel) :verify-guards nil))
 (cond
  ((fn-rh-live fn-render-holder) (mv :busy fuel fn-mio$c fn-render-holder))
  ((not (fn-ibp-query-tokenp token)) (mv :stale fuel fn-mio$c fn-render-holder))
  (t
   (mv-let (enough fn-mio$c)
    (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
     (enough)
     (<= (* 7 (+ 1 (fn-ibp-slot-depth fn-index-backing))) fuel)
     (mv enough fn-mio$c))
    (if (not enough) (mv :yield fuel fn-mio$c fn-render-holder)
     (mv-let (authorized control receipt left)
      (fn-irr-registered-read token fuel fn-mio$c)
      (declare (ignore control receipt))
      (if (not (and (eq authorized :authorized) (natp left)))
          (mv authorized left fn-mio$c fn-render-holder)
       (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
        (word after fn-index-backing fn-render-holder)
        (let ((depth (fn-ibp-slot-depth fn-index-backing)))
         (stobj-let ((fn-ibp-node (fn-ibp-registry fn-index-backing)))
          (word after fn-ibp-node fn-render-holder)
          (mv-let (intent after-intent fn-ibp-node fn-render-holder)
           (fn-irc-node-render-action token :intent left (1- (nth 2 token)) depth
                                      fn-ibp-node fn-render-holder)
           (if (not (and (eq intent :render-intent-recorded) (natp after-intent)))
               (mv intent after-intent fn-ibp-node fn-render-holder)
            (fn-irc-node-render-action token :install after-intent (1- (nth 2 token)) depth
                                       fn-ibp-node fn-render-holder)))
          (mv word after fn-index-backing fn-render-holder)))
        (mv word after fn-mio$c fn-render-holder)))))))))

(verify-guards fn-irc-registered-render-install
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-ibp-query-tokenp)
   (fn-irr-registered-read fn-irc-node-render-action fn-irc-slot-sourcep
    fn-irr-context-matchesp fn-irr-publication-coordinatesp
    fn-irr-receipt-committedp fn-irr-node-render-control)))))
