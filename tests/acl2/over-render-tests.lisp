; OVER five-row fixtures over the runtime-contract pool: column, cross-post,
; payload-parse, tombstone, visibility, framing and greedy-capacity controls.
(in-package "ACL2")
(include-book "over-render-lease-tests")
(set-ignore-ok t)
(defconst *ovrt-p0* (append (fn-record-string-octets "Subject: a") '(13 10 13 10 65 13 10)))

(defconst *ovrt-p1* (append (fn-record-string-octets "Subject: bb") '(13 10 13 10 66 13 10)))

(defconst *ovrt-p2* (append (fn-record-string-octets "Subject: ccc") '(13 10 13 10 67 13 10 67 13 10)))

(defconst *ovrt-p3* (append (fn-record-string-octets "Subject: plain") '(13 10 13 10 68 13 10)))

(defconst *ovrt-p4* (append *fn-rcl-magic* (make-list 137 :initial-element 0)))

(defconst *ovrt-w0* (fn-record-make 0 1 1 "<a@x>" *ovrt-p0* '("fn.test") "o" "s" "e" 1 5))

(defconst *ovrt-w1* (fn-record-make 1 2 2 "<b@x>" *ovrt-p1* '("fn.test" "fn.other") "o" "s" "e" 1 5))

(defconst *ovrt-w2* (fn-record-make 2 3 3 "<c@x>" *ovrt-p2* '("fn.test") "o" "s" "e" 1 5))

(defconst *ovrt-w3* (fn-record-make 3 4 4 "<d@x>" *ovrt-p3* '("fn.test") "o" "s" "e" 1 5))

(defconst *ovrt-w4* (fn-record-make 4 5 5 "<e@x>" *ovrt-p4* '("fn.test") "o" "s" "e" 1 5))

(defun ovrt-held (w handle numbers)
  (fn-held-make (fn-record-sequence w) (fn-record-txid w) (fn-record-generation w)
                (fn-record-msgid w) handle (fn-record-groups w) (fn-record-obligation-id w)
                (fn-record-content-subject w) (fn-record-release-evidence w)
                (fn-record-charge w) (fn-record-stamp w)
                (fn-held-facts-of (fn-record-payload w))
                (fn-held-context-of (fn-record-payload w) nil 0) numbers nil))

(defconst *ovrt-a* (list *ovrt-p0* *ovrt-p1* *ovrt-p2* *ovrt-p3* *ovrt-p4*))

(defconst *ovrt-r0* (fn-cat-assign (ovrt-held *ovrt-w0* 0 nil) nil))

(defconst *ovrt-r1* (fn-cat-assign (ovrt-held *ovrt-w1* 1 nil) (list *ovrt-r0*)))

(defconst *ovrt-r2* (fn-cat-assign (ovrt-held *ovrt-w2* 2 nil) (list *ovrt-r0* *ovrt-r1*)))

(defconst *ovrt-r3* (fn-cat-assign (fn-held-plain *ovrt-w3* 3) (list *ovrt-r0* *ovrt-r1* *ovrt-r2*)))

(defconst *ovrt-r4* (fn-cat-assign (ovrt-held *ovrt-w4* 4 nil) (list *ovrt-r0* *ovrt-r1* *ovrt-r2* *ovrt-r3*)))

(defconst *ovrt-c* (list *ovrt-r0* *ovrt-r1* *ovrt-r2* *ovrt-r3* *ovrt-r4*))

(defconst *ovrt-server* '(110 102))

(defun ovrt-probe (group number server v prefix fn-rtc-st fn-arena fn-cat)
  (declare (xargs :stobjs (fn-rtc-st fn-arena fn-cat) :verify-guards nil))
  (mv-let (id inc fn-rtc-st) (pc1-boot 1000 nil fn-rtc-st)
    (declare (ignore id inc))
    (mv-let (sig j fn-rtc-st) (fn-dsw-append 0 0 prefix fn-rtc-st)
      (declare (ignore sig))
      (mv-let (sig end fn-rtc-st)
        (fn-ovr-put-probe group number server v 0 j 1000 fn-rtc-st fn-arena fn-cat)
        (let ((ref (fn-ovr-probe-octets group number server v fn-arena fn-cat)))
          (mv (list (and (eq sig :done)
                         (equal (fn-ovr-st-view 0 0 end fn-rtc-st) (append prefix ref)))
                    (equal (fn-ovr-probe-len group number server v fn-arena fn-cat) (len ref))
                    (len ref)) fn-rtc-st))))))
(defmacro ovrt-probe-local (group number server v prefix)
  `(with-local-stobj fn-arena
     (mv-let (r fn-arena)
       (with-local-stobj fn-cat
         (mv-let (r fn-arena fn-cat)
           (mv-let (fn-arena fn-cat) (pc1-seed *ovrt-a* *ovrt-c* fn-arena fn-cat)
             (with-local-stobj fn-rtc-st
               (mv-let (r fn-rtc-st)
                 (ovrt-probe ,group ,number ,server ,v ,prefix fn-rtc-st fn-arena fn-cat)
                 (mv r fn-arena fn-cat))))
           (mv r fn-arena))) r)))
(defun ovrt-probe-scene (group number server v prefix)
 (declare (xargs :verify-guards nil))
 (ovrt-probe-local group number server v prefix))
(assert-event
 (let ((r (ovrt-probe-scene "fn.test" 1 *ovrt-server* 6 '(1 2))))
   (and (car r) (cadr r) (posp (caddr r)))))
(assert-event
 (let ((r (ovrt-probe-scene "fn.test" 2 *ovrt-server* 6 nil)))
   (and (car r) (cadr r) (posp (caddr r)))))
(assert-event
 (let ((r (ovrt-probe-scene "fn.other" 1 *ovrt-server* 6 nil)))
   (and (car r) (cadr r) (posp (caddr r)))))
(assert-event
 (let ((r (ovrt-probe-scene "fn.test" 4 *ovrt-server* 6 '(9))))
   (and (car r) (cadr r) (posp (caddr r)))))
(assert-event
 (let ((r (ovrt-probe-scene "fn.test" 5 *ovrt-server* 6 '(9))))
   (and (car r) (cadr r) (zp (caddr r)))))
(assert-event
 (let ((r (ovrt-probe-scene "fn.test" 3 nil 6 nil)))
   (and (car r) (cadr r) (posp (caddr r)))))
(assert-event
 (let ((r (ovrt-probe-scene "fn.test" 9 *ovrt-server* 6 nil)))
   (and (car r) (cadr r) (zp (caddr r)))))
(assert-event
 (let ((r (ovrt-probe-scene "fn.test" 3 *ovrt-server* 2 nil)))
   (and (car r) (cadr r) (zp (caddr r)))))
; Each scene obtains a fresh workspace through the actual host driver.
(defun ovrt-pool-sweep (cur w cap fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil :measure (nfix cap)
                  :hints (("Goal" :in-theory (fn-dss-measure-theory)))))
  (let* ((r (pc1-run-scene :quantum nil 1000 cur w 0 cap 1000 30 1000 1000
                         (fn-article-limits 10 10 1000) *ovrt-a* *ovrt-c*))
         (checks (take 5 r)))
    (and (pc1-positive (nth 0 checks)) (pc1-positive (nth 1 checks))
         (pc1-positive (nth 2 checks)) (pc1-positive (nth 3 checks))
         (pc1-positive (nth 4 checks))
         (if (zp cap) t (ovrt-pool-sweep cur w (- cap 1) fn-arena fn-cat)))))
; The sweep's observers own their local arena/catalog; these formals carry
; no data and are used only to expose ACL2's declared stobj return discipline.
(defmacro ovrt-sweep-local (cur w)
 `(with-local-stobj fn-arena
    (mv-let (r fn-arena)
      (with-local-stobj fn-cat
        (mv-let (r fn-cat)
          (mv (ovrt-pool-sweep ,cur ,w 400 fn-arena fn-cat) fn-cat)
          (mv r fn-arena))) r)))
(defun ovrt-sweep-scene (cur w)
 (declare (xargs :verify-guards nil))
 (ovrt-sweep-local cur w))
(assert-event (ovrt-sweep-scene (fn-ovw-cursor "fn.test" 1 5 6 nil t *ovrt-server*) 1))
(assert-event (ovrt-sweep-scene (fn-ovw-cursor "fn.test" 1 5 6 t t *ovrt-server*) 7))
(assert-event (ovrt-sweep-scene (fn-ovw-cursor "fn.test" 1 5 6 nil t nil) 2))
(assert-event (ovrt-sweep-scene (fn-ovw-cursor "fn.test" 3 5 6 nil t *ovrt-server*) 2))
(assert-event (ovrt-sweep-scene (fn-ovw-cursor "fn.other" 1 1 6 nil t *ovrt-server*) 2))
(assert-event (ovrt-sweep-scene (fn-ovw-cursor "fn.test" 7 9 6 t t nil) 2))
(assert-event (ovrt-sweep-scene (fn-ovw-cursor "fn.test" 4 5 6 nil t *ovrt-server*) 1))
(assert-event (ovrt-sweep-scene (fn-ovw-cursor "fn.test" 5 3 6 nil t *ovrt-server*) 1))
