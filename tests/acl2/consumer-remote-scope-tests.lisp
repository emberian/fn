(in-package "ACL2")
(include-book "../../books/consumer-remote-scope-model")
(include-book "consumer-remote-ingress-tests")

; A bounded fixture driver, not a served operation ceiling. Exhaustion returns
; the exact retained cursor; the service scheduler must resume it later.
(defun fn-crst-run (fuel result key g)
 (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
 (if (or (zp fuel) (not (eq (fn-cp-nth 0 result) :yield))) result
  (fn-crst-run (1- fuel) (fn-crs-tick (fn-cp-nth 1 result) key g) key g)))

(defun fn-crst-config (table closed)
 (declare (xargs :guard t))
 (fn-inj-make-config-full t nil '((97) (98) (113)) 4096
                         (list nil nil nil table) closed))

(defun fn-crst-ingress ()
 (declare (xargs :guard t :verify-guards nil))
 (fn-cre-ingress (fn-crit-request :register '(97) '(99) '((97) (98)) nil 0)
                 t 3 (fn-crat-cp) 3 (fn-cp-nth 3 (fn-crat-cp)) (fn-crat-pub)))

(assert-event
 (let* ((i (fn-crst-ingress)) (key (fn-crs-key i 7))
        (start (fn-crs-begin i 7 (fn-crst-config '(("z" "*" "*" 3) ("a" "a,b" "*" 3)) nil)
                            '((97) (98))))
        (first (fn-crst-run 1 start key 3))
        (end (fn-crst-run 80 first key 3))
        (answer (fn-crs-finish (fn-cp-nth 1 end) key)))
  (and (eq (car first) :yield) (equal (fn-cp-nth 3 (fn-cp-nth 1 first)) :access)
       (eq (car end) :ready) (equal (fn-cp-nth 1 answer) '((97) (98)))
       (equal (fn-cp-nth 3 answer) 2)
       (equal (fn-caac-list-carry (fn-cp-nth 2 answer)) (fn-scs-summary '((97) (98)))))))

; First-match account READ precedes a permissive later row. An unserved or
; denied group is the same refusal and returns no partial definition.
(assert-event
 (let* ((i (fn-crst-ingress)) (key (fn-crs-key i 7))
        (c (fn-crst-config '(("a" "a" "*" 3) ("a" "*" "*" 3)) nil)))
  (and (equal (fn-crst-run 80 (fn-crs-begin i 7 c '((97) (98))) key 3) '(:refused :read-scope))
       (equal (fn-crst-run 80 (fn-crs-begin i 7 c '((120))) key 3) '(:refused :read-scope)))))

; One moderator cell per tick. Shared queue is visible only if the login
; moderates every queued group, exactly fn-mod-queue-hiddenp's semantics.
(assert-event
 (let* ((i (fn-crst-ingress)) (key (fn-crs-key i 7))
        (allowed '((:moderated (97) (113) ((122) (97)))
                   (:moderated (98) (113) ((98) (97)))))
        (denied '((:moderated (97) (113) ((97)))
                  (:moderated (98) (113) ((98)))))
        (ok (fn-crst-run 80 (fn-crs-begin i 7 (fn-crst-config nil allowed) '((113))) key 3)))
  (and (not (fn-mod-queue-hiddenp '(113) allowed '(97)))
       (fn-mod-queue-hiddenp '(113) denied '(97))
       (eq (car ok) :ready)
       (equal (fn-crst-run 80 (fn-crs-begin i 7 (fn-crst-config nil denied) '((113))) key 3)
              '(:refused :read-scope)))))

(assert-event
 (let* ((i (fn-crst-ingress)) (key (fn-crs-key i 7))
        (start (fn-crs-begin i 7 (fn-crst-config nil nil) '((97) (98))))
        (changed (fn-crs-key i 8)))
  (and (equal (fn-crs-tick (fn-cp-nth 1 start) changed 3) '(:refused :scope-changed))
       (equal (fn-crs-finish (fn-cp-nth 1 start) key) '(:refused :scope-incomplete))
       (equal (fn-crst-run 80 (fn-crs-begin i 7 (fn-crst-config nil nil) '((98) (97))) key 3)
              '(:refused :query))
       (equal (fn-crst-run 80 (fn-crs-begin i 7 (fn-crst-config nil nil) '((97) (97))) key 3)
              '(:refused :query))
       (equal (fn-crst-run 80 start key 1) '(:refused :query)))))

;@positive fn-crs-tick-is-current-read-and-moderation-projection
; Reachable positive witnesses span every producer phase, including scanning
; two access rows and two moderators of a shared queue.
(defun fn-crst-projection-witness (fuel answer key g)
 (declare (xargs :guard (natp fuel) :verify-guards nil :measure (nfix fuel)))
 (if (or (zp fuel) (not (eq (fn-cp-nth 0 answer) :yield))) t
  (let ((s (fn-cp-nth 1 answer)))
   (and (fn-crsm-domainp s) (equal key (fn-cp-nth 1 s))
        (equal (fn-crsm-answer (fn-crs-tick s key g) g) (fn-crsm-observe s g))
        (fn-crst-projection-witness (1- fuel) (fn-crs-tick s key g) key g)))))

(assert-event
 (let* ((i (fn-crst-ingress)) (key (fn-crs-key i 7))
        (start (fn-crs-begin i 7
                (fn-crst-config '(("z" "*" "*" 3) ("a" "q" "*" 3))
                  '((:moderated (97) (113) ((122) (97)))
                    (:moderated (98) (113) ((98) (97))))) '((113))))
        (end (fn-crst-run 80 start key 3)))
  (and (fn-crst-projection-witness 80 start key 3)
       (eq (car end) :ready) (fn-crsm-domainp (fn-cp-nth 1 end))
       (equal key (fn-cp-nth 1 (fn-cp-nth 1 end)))
       (equal (fn-crsm-answer (fn-crs-tick (fn-cp-nth 1 end) key 3) 3)
              (fn-crsm-observe (fn-cp-nth 1 end) 3)))))

;@hypothesis-removal fn-crs-tick-is-current-read-and-moderation-projection current-key
(assert-event
 (let* ((i (fn-crst-ingress)) (key (fn-crs-key i 7))
        (s (fn-cp-nth 1 (fn-crs-begin i 7 (fn-crst-config nil nil) '((97)))))
        (changed (fn-crs-key i 8)))
  (and (fn-crsm-domainp s) (not (equal changed (fn-cp-nth 1 s)))
       (not (equal (fn-crsm-answer (fn-crs-tick s changed 3) 3) (fn-crsm-observe s 3)))
       (equal key (fn-cp-nth 1 s)))))

;@hypothesis-removal fn-crs-tick-is-current-read-and-moderation-projection carried-domain
; Corrupted-state witness: absent login violates the maintained nonempty
; named-account field while retaining the exact key hypothesis.
(assert-event
 (let* ((key '(:remote-source 3 nil 1 nil 7))
        (closed '((:moderated (97) (113) (nil))))
        (s (fn-crs-state key nil :closed nil nil '((113)) '((113)) closed
                        closed nil nil 0 nil nil nil nil 0)))
  (and (equal key (fn-cp-nth 1 s)) (not (fn-crsm-domainp s))
       (not (equal (fn-crsm-answer (fn-crs-tick s key 3) 3) (fn-crsm-observe s 3))))))
