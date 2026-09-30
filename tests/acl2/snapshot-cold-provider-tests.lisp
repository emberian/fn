(in-package "ACL2")
(include-book "../../books/snapshot-cold-provider")
; Only the outer issued-byte fence is exercised here. This fixture is not
; authenticated history evidence or a whole cold-codec completion claim.
(defconst *ocbt-h* '(:hrs-handle 7 (:pgs-commit 1 1 1 10 nil) 123 2
                      (16 16 16 16 32768) (1 2 3 4 5) 10))
(defconst *ocbt-source* '(9 (17 2) 1 0))
(defconst *ocbt-child* '(:need-byte 16384 :span-body 16384))
(defconst *ocbt-c*
  (mv-let (word next)
    (fn-ocb-request (fn-ocb-begin *ocbt-h* *ocbt-source* :resource) *ocbt-child*)
    (declare (ignore word)) next))
(defconst *ocbt-byte* '(:byte (9 (17 2) 1 0) :span-body 0 6 0 83))
(assert-event
 (mv-let (word next) (fn-ocb-complete *ocbt-c* *ocbt-source* *ocbt-child* *ocbt-byte*)
  (and (equal (fn-ocb-demand *ocbt-c*)
             '(:need-byte (9 (17 2) 1 0) :span-body 0 6 0))
      (equal word '(:supply 16384 83)) (equal (fn-omk-at 3 next) 1))))
(assert-event
 (let ((stale '(:byte (9 (17 2) 1 0) :span-body 1 6 0 83)))
   (mv-let (word next) (fn-ocb-complete *ocbt-c* *ocbt-source* *ocbt-child* stale)
     (and (not (equal (car word) :supply)) (equal next *ocbt-c*)))))
(assert-event
 (let ((child '(:need-byte 16384 :span-body 16385)))
   (mv-let (word next) (fn-ocb-complete *ocbt-c* *ocbt-source* child *ocbt-byte*)
     (and (not (fn-ocb-child-matchp *ocbt-child* child))
          (not (equal (car word) :supply)) (equal next *ocbt-c*)))))
(assert-event
 (mv-let (word done) (fn-ocb-complete *ocbt-c* *ocbt-source* *ocbt-child* *ocbt-byte*)
   (declare (ignore word))
   (mv-let (duplicate next) (fn-ocb-complete done *ocbt-source* *ocbt-child* *ocbt-byte*)
     (and (not (equal (car duplicate) :supply)) (equal next done)))))

; Actual new-key begin over a borrowed Message-ID span, distinct target salt.
(defconst *ocb-key-node*
  (fn-hdc-pair (fn-hdc-atom 0)
   (fn-hdc-pair (fn-hdc-atom 1)
    (fn-hdc-pair (fn-hdc-atom 2)
     (fn-hdc-pair (fn-hdc-span 3 0 8 1) (fn-hdc-atom nil))))))
(defconst *ocb-key-begin*
  (fn-omk-begin (list :decoded *ocb-key-node*) 17 '(7 (11 1) 1 0) :resource))
(defconst *ocb-key-cursor* (cadr *ocb-key-begin*))
(assert-event (and (equal (car *ocb-key-begin*) :begun)
                  (fn-omk-guardp *ocb-key-cursor*)
                  (equal (fn-ocb-key-child *ocb-key-cursor*) '(:need-byte 8 :key 0))
                  (equal (fn-ocb-key-observation *ocb-key-cursor* '(:supply 8 42))
                         '(:byte (7 (11 1) 1 0) 8 42))
                  (equal (car (fn-omk-tick *ocb-key-cursor*
                    (fn-ocb-key-observation *ocb-key-cursor* '(:supply 8 42)))) :continue)))
(assert-event (and (fn-omk-guardp *ocb-key-cursor*)
                  (equal (fn-ocb-key-observation *ocb-key-cursor* '(:supply 9 42))
                         '(:refused :key-byte))))

; The ref-aware cursor's issued MID character rides the same unchanged fence.
(defconst *ocb-mid-child* '(:need-byte 8 :mid-character 0))
(defconst *ocb-mid-c*
 (mv-let (word next)
  (fn-ocb-request (fn-ocb-begin *ocbt-h* *ocbt-source* :resource) *ocb-mid-child*)
  (declare (ignore word)) next))
(assert-event
 (mv-let (word next)
  (fn-ocb-complete *ocb-mid-c* *ocbt-source* *ocb-mid-child*
                  '(:byte (9 (17 2) 1 0) :mid-character 0 5 8 65))
  (and (fn-ocb-childp *ocb-mid-child*)
       (equal (fn-ocb-demand *ocb-mid-c*)
              '(:need-byte (9 (17 2) 1 0) :mid-character 0 5 8))
       (equal word '(:supply 8 65)) (equal (fn-omk-at 3 next) 1))))
(assert-event
 (mv-let (word next)
  (fn-ocb-complete *ocb-mid-c* *ocbt-source* '(:need-byte 8 :mid-character 1)
                  '(:byte (9 (17 2) 1 0) :mid-character 0 5 8 65))
  (and (not (fn-ocb-child-matchp *ocb-mid-child* '(:need-byte 8 :mid-character 1)))
       (not (equal (car word) :supply)) (equal next *ocb-mid-c*))))
