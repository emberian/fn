(in-package "ACL2")
(include-book "../../books/config-owner-advance-invariants")
(include-book "config-owner-live-tests")
(include-book "std/testing/must-fail" :dir :system)

(defconst *ocla-t-advanced* (fn-ocfg-advance *ocl-t-new-open* 0))
(assert-event
 (not (equal (fn-ocfg-owner *ocla-t-advanced*)
             (fn-ocfg-owner *ocl-t-new-open*))))
(assert-event (fn-ocl-relation *ocla-t-advanced*))
(assert-event
 (equal (fn-ocfg-conn-config *ocla-t-advanced* 0)
        (fn-ocfg-config *ocl-t-new-open*)))
(assert-event
 (member-equal "fn.live" (fn-ocfg-served *ocla-t-advanced* 0)))
(defconst *ocla-t-live-group-command*
  (append (fn-nntp-string-octets "GROUP fn.live") '(13 10)))
(assert-event
 (not (equal (car (fn-ocfg-read *ocl-t-new-open* 0
                                 *ocla-t-live-group-command*))
             (car (fn-ocfg-read *ocla-t-advanced* 0
                                 *ocla-t-live-group-command*)))))
(assert-event
 (equal (fn-own-conn-archive
         (fn-own-find-conn 0
          (fn-own-conns (fn-ocfg-owner *ocla-t-advanced*))))
        (fn-own-view-archive (fn-own-view
                              (fn-ocfg-owner *ocl-t-new-open*)))))

; The pre-strengthening historical relation admitted two open records with
; one identifier.  ADVANCE changes the first, then changes the shared pin;
; the second still has the old archive.  Fresh owner allocation never creates
; this state, but a preservation theorem must exclude it explicitly.
(defconst *ocla-t-duplicate*
  (let* ((o (fn-ocfg-owner *ocl-t-new-open*))
         (old (fn-own-find-conn 0 (fn-own-conns o))))
    (fn-ocfg-make
     (fn-own-set-conns o (cons old (fn-own-conns o)))
     (fn-ocfg-config *ocl-t-new-open*)
     (fn-ocfg-pins *ocl-t-new-open*) nil)))
(assert-event (not (fn-ocl-relation *ocla-t-duplicate*)))
(assert-event
 (fn-ocl-conns-historyp *ocla-t-duplicate*
                        (fn-own-conns (fn-ocfg-owner *ocla-t-duplicate*))))
(assert-event
 (fn-ocfg-conns-pinnedp
  (fn-own-conns (fn-ocfg-owner *ocla-t-duplicate*))
  (fn-ocfg-pins *ocla-t-duplicate*)))
(assert-event
 (not (fn-ocl-unique-conn-idsp
       (fn-own-conns (fn-ocfg-owner *ocla-t-duplicate*)))))
(assert-event
 (not (fn-ocl-relation (fn-ocfg-advance *ocla-t-duplicate* 0))))
(local
 (must-fail
  (defthm fn-ocl-advance-without-historical-relation
    (fn-ocl-relation (fn-ocfg-advance oc id))
    :rule-classes nil)))
