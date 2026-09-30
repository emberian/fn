; Actual capacity preparation before the retained writer enters growth.
; One tick doubles at most one scalar. This controller does not issue source
; or INITIAL authority: its host initializer must read the actual installed
; source and retained metadata inside the same owner operation.
(in-package "ACL2")
(include-book "history-image-producer")

; phase,count,pool,need,cap,column-cap,source4,maintenance,stage,node,salt,
; frozen-trail,actual HPI continuation (only after preparation completes).
(defun fn-hpip-shapep (c)
  (declare (xargs :guard t))
  (and (fn-omk-widthp c 13)
       (unsigned-byte-p 61 (fn-omk-at 1 c))
       (unsigned-byte-p 64 (fn-omk-at 2 c))
       (natp (fn-omk-at 3 c)) (< (fn-omk-at 3 c) 1125899906842625)
       (natp (fn-omk-at 4 c)) (< (fn-omk-at 4 c) 2251799813685248)))

(defun fn-hpip-begin (count pool source4 maintenance stage node salt trail)
  (declare (xargs :guard t))
  (if (not (and (unsigned-byte-p 61 count) (unsigned-byte-p 64 pool)
                (equal (mod pool 8) 0)
                (or (< 0 count) (equal pool 0))))
      (mv :refused nil)
    (mv-let (need cap) (fn-hcc-cap-begin (* 8 count))
      (mv :continue (list :column count pool need cap 0 source4 maintenance stage
                          node salt trail nil)))))

(defun fn-hpip-tick (c)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory
                                 (enable fn-hpip-shapep unsigned-byte-p)))))
  (cond
   ((not (fn-hpip-shapep c)) (mv :refused c nil))
   ((eq (fn-omk-at 0 c) :prepared)
    (mv :prepared c (fn-omk-at 12 c)))
   ((not (member-eq (fn-omk-at 0 c) '(:column :pool)))
    (mv :refused c nil))
   (t
    (mv-let (word cap) (fn-hcc-cap-tick (fn-omk-at 3 c) (fn-omk-at 4 c))
      (cond
       ((eq word :continue)
        (mv :continue (fn-hpi-set 4 cap c) nil))
       ((not (eq word :done)) (mv :refused c nil))
       ((eq (fn-omk-at 0 c) :column)
        (mv-let (need pool-cap) (fn-hcc-cap-begin (fn-omk-at 2 c))
          (mv :continue
              (fn-hpi-set 0 :pool
                (fn-hpi-set 3 need (fn-hpi-set 4 pool-cap (fn-hpi-set 5 cap c))))
              nil)))
       (t
        (let* ((writer (fn-hpi-begin
                         (fn-omk-at 1 c) (fn-omk-at 2 c)
                         (fn-omk-at 5 c) cap (fn-omk-at 6 c)
                         (fn-omk-at 7 c) (fn-omk-at 8 c)
                         (fn-osj-native-offset-max)
                         (fn-omk-at 9 c) (fn-omk-at 10 c) (fn-omk-at 11 c)))
               (word (if (eq (fn-omk-at 0 writer) :need-growth) :prepared :refused)))
          (mv word (fn-hpi-set 0 word (fn-hpi-set 12 writer c)) writer))))))))

(in-theory (disable fn-hpip-shapep fn-hpip-begin fn-hpip-tick))
