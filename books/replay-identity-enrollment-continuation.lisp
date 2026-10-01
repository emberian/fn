; Actual old gate ordering and once-produced STXE parse, with the retained
; revoked enrollment work delegated to its byte/cell continuation. This new
; caller is not activated before its typed/public/custody/funding boundary.
(in-package "ACL2")
(include-book "replay-identity-continuation")
(include-book "replay-revoked-enrollment")

(defun fn-rpx-enrolled-begin (ctx event source enrollment)
 (declare (xargs :guard t :verify-guards nil))
 (cond
  ((not (equal (fn-stxk-context-kind ctx) :ok))
   (fn-rpx-complete ctx event source nil nil ctx :none nil nil))
  ((not (equal (fn-store-event-sequence event) (fn-stxk-context-next ctx)))
   (fn-rpx-complete ctx event source nil nil
                    (fn-stxk-fault ctx :sequence) :none nil nil))
  (t
   (let ((wire (fn-replay-identity-wire event)))
    (cond
     ((fn-stxk-p wire)
      (fn-rpx-state :snapshot ctx event source wire nil
       (fn-rsc-begin (fn-stxk-keyring-generation wire)
                     (fn-stxk-context-snapshots ctx) source) nil))
     ((fn-stxe-p wire)
      (fn-rpx-state :verdict ctx event source wire nil
       (fn-rsc-begin (fn-stxe-keyring-generation wire)
                     (fn-stxk-context-snapshots ctx) source) nil))
     ((not (fn-stxa-p wire))
      (fn-rpx-complete ctx event source wire nil
                       (fn-replay-identity-advance ctx) :none nil nil))
     (t
      (let* ((evidence (fn-rpe-produce wire))
             (child (fn-stmt-value (fn-rpe-result evidence)))
             (sizes (fn-rpe-lengths evidence)))
       (cond
        ((fn-rpe-carried-bindsp evidence)
         (fn-rpx-state :done ctx event source wire evidence nil
          (fn-rpx-verdict-result (fn-replay-apply-carried-verdict ctx child)
                                 child sizes)))
        ((fn-rpe-revoked-bindsp evidence)
         (fn-rpx-state :revoked ctx event source wire evidence
          (fn-rse-revoked-begin ctx child
            (fn-hsig-article-event-carrier-keys wire) enrollment source) nil))
        (t
         (fn-rpx-state :composite-snapshot ctx event source wire evidence
          (fn-rsc-begin (fn-stxa-keyring-generation wire)
                        (fn-stxk-context-snapshots ctx) source) nil))))))))))

(defun fn-rpx-enrolled-step (s)
 (declare (xargs :guard t :verify-guards nil))
 (if (not (fn-rsc-widthp 8 s)) (mv :refused s)
  (if (not (eq (fn-rsc-at 0 s) :revoked)) (fn-rpx-step s)
   (mv-let (word next) (fn-rse-revoked-step (fn-rsc-at 6 s))
    (cond
     ((eq word :refused) (mv :refused s))
     ((eq word :done)
      (let ((evidence (fn-rsc-at 5 s)))
       (mv :done (fn-rpx-state :done (fn-rsc-at 1 s) (fn-rsc-at 2 s)
        (fn-rsc-at 3 s) (fn-rsc-at 4 s) evidence nil
        (fn-rpx-verdict-result (fn-rsc-at 8 next)
          (fn-stmt-value (fn-rpe-result evidence)) (fn-rpe-lengths evidence))))))
     (t (mv :working (fn-rpx-state :revoked (fn-rsc-at 1 s) (fn-rsc-at 2 s)
         (fn-rsc-at 3 s) (fn-rsc-at 4 s) (fn-rsc-at 5 s) next nil))))))))

(verify-guards fn-rpx-enrolled-begin
 :hints (("Goal" :in-theory
  (disable fn-rpe-produce fn-rpe-result fn-rpe-lengths fn-rpe-carried-bindsp
           fn-rpe-revoked-bindsp fn-rpx-state fn-rpx-complete
           fn-rpx-verdict-result fn-rsc-begin fn-rse-revoked-begin))))
(verify-guards fn-rpx-enrolled-step
 :hints (("Goal" :in-theory
  (disable fn-rpx-step fn-rse-revoked-step fn-rsc-at fn-rsc-widthp
           fn-rpx-state fn-rpx-verdict-result fn-rpe-result fn-rpe-lengths))))
