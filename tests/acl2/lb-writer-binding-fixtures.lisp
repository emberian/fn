; Real-source small writer states for A1's native positive controls.
(in-package "ACL2")
(include-book "lb-recognizer-repair-fixtures")
(include-book "../../books/lb-log-reclaim-properties")
(include-book "../../books/lb-log-reclaim-domains")

(verify-guards fn-lbr13-held)

(defconst *fn-lbw-payload-b*
 '(83 117 98 106 101 99 116 58 32 98 13 10 13 10 98 13 10))

(defun fn-lbw-second-held ()
 (declare (xargs :guard t))
 (car (last
  (fn-cat$a-commit
   (fn-held-plain
    (fn-record-make 1 2 0 "<lb-second@fn.test>" *fn-lbw-payload-b*
                    '("fn.test") "o" "s" "e" 1 3) 1)
   (list (fn-lbr13-held))))))

(defun fn-lbw-two-rows ()
 (declare (xargs :guard t))
 (list (fn-lbr13-held) (fn-lbw-second-held)))

(defun fn-lbw-incoming-held ()
 (declare (xargs :guard t))
 (fn-held-plain
  (fn-record-make 2 3 0 "<lb-third@fn.test>" *fn-lbw-payload-b*
                  '("fn.test") "o" "s" "e" 1 7) 2))

(defun fn-lbw-two-log ()
 (declare (xargs :guard t))
 (fn-lb-log-model-append (fn-lbw-second-held) *fn-lbw-payload-b* 1
  (fn-lb-log-model-append (fn-lbr13-held) *fn-lbr13-payload* 1 nil)))

(defun fn-lbw-arena-good (fn-arena)
 (declare (xargs :stobjs fn-arena :guard t))
 (let* ((fn-arena (fn-arena-clear fn-arena))
        (fn-arena (fn-arena-seal-list *fn-lbr13-payload* fn-arena)))
  (fn-arena-seal-list *fn-lbw-payload-b* fn-arena)))

(defun fn-lbw-arena-swapped (fn-arena)
 (declare (xargs :stobjs fn-arena :guard t))
 (let* ((fn-arena (fn-arena-clear fn-arena))
        (fn-arena (fn-arena-seal-list *fn-lbw-payload-b* fn-arena)))
  (fn-arena-seal-list *fn-lbw-payload-b* fn-arena)))

(defun fn-lbw-tombstone-record ()
 (declare (xargs :guard t))
 (fn-record-make 0 1 0 "<lb-repair@fn.test>"
  (fn-rcl-tombstone-of *fn-lbr13-payload*
                      (fn-record-string-octets "<lb-repair@fn.test>"))
  '("fn.test") "o" "s" "e" 1 5))

(defun fn-lbw-reclaim-input ()
 (declare (xargs :guard t))
 (list (fn-lbw-tombstone-record) (fn-lbw-second-held)))
