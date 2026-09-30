; Actual segment lifecycle with deliberately synthetic grant/publication.
; No admission, publication correspondence or native activation claim.
(in-package "ACL2")
(include-book "../../books/index-connection-holder")
(defun fn-ich-test-lifecycle (fn-ibp-connection-segment)
 (declare (xargs :stobjs fn-ibp-connection-segment :guard t))
 (let ((fn-ibp-connection-segment (update-fn-ich-segment-id 1 fn-ibp-connection-segment)))
 (mv-let (a fn-ibp-connection-segment) (fn-ich-reserve '(:connection-holder 17 1 0) 100000000000000000000 :test-grant fn-ibp-connection-segment)
 (mv-let (b fn-ibp-connection-segment) (fn-ich-attach '(:connection-holder 17 1 0) '(:publication-pin (:index-generation 9 2 3) (:test-published-source old)) fn-ibp-connection-segment)
 (mv-let (c fn-ibp-connection-segment) (fn-ich-attach '(:connection-holder 17 1 0) :different-source fn-ibp-connection-segment)
 (mv-let (d fn-ibp-connection-segment) (fn-ich-alias '(:connection-holder 17 1 0) :acquire fn-ibp-connection-segment)
 (mv-let (e fn-ibp-connection-segment) (fn-ich-close 1 '(:connection-holder 17 1 0) fn-ibp-connection-segment)
 (mv-let (f fn-ibp-connection-segment) (fn-ich-close 100000000000000000000 '(:connection-holder 17 1 0) fn-ibp-connection-segment)
 (mv-let (g fn-ibp-connection-segment) (fn-ich-alias '(:connection-holder 17 1 0) :acquire fn-ibp-connection-segment)
 (mv-let (held held-pin held-grant) (fn-ich-release-ready '(:connection-holder 17 1 0) fn-ibp-connection-segment)
 (let ((before-row (fn-ich-row '(:connection-holder 17 1 0) fn-ibp-connection-segment)))
  (mv-let (early early-grant fn-ibp-connection-segment) (fn-ich-release-finish '(:connection-holder 17 1 0) fn-ibp-connection-segment)
   (let ((unchanged (equal before-row (fn-ich-row '(:connection-holder 17 1 0) fn-ibp-connection-segment))))
    (mv-let (returned fn-ibp-connection-segment) (fn-ich-alias '(:connection-holder 17 1 0) :return fn-ibp-connection-segment)
     (mv-let (ready ready-pin ready-grant) (fn-ich-release-ready '(:connection-holder 17 1 0) fn-ibp-connection-segment)
      (mv-let (released grant fn-ibp-connection-segment) (fn-ich-release-finish '(:connection-holder 17 1 0) fn-ibp-connection-segment)
       (mv-let (duplicate duplicate-grant fn-ibp-connection-segment) (fn-ich-release-finish '(:connection-holder 17 1 0) fn-ibp-connection-segment)
        (mv-let (recycled fn-ibp-connection-segment) (fn-ich-reserve '(:connection-holder 18 1 0) 7 :next-grant fn-ibp-connection-segment)
         (let ((old-row (fn-ich-row '(:connection-holder 17 1 0) fn-ibp-connection-segment)))
          (mv-let (late fn-ibp-connection-segment) (fn-ich-close 100000000000000000000 '(:connection-holder 17 1 0) fn-ibp-connection-segment)
           (mv (list a b c d e f g held held-pin held-grant early early-grant unchanged
                     returned ready ready-pin ready-grant released grant duplicate duplicate-grant
                     recycled old-row late (fn-ich-active fn-ibp-connection-segment) (fn-ich-row '(:connection-holder 18 1 0) fn-ibp-connection-segment))
               fn-ibp-connection-segment)))))))))))))))))))))
(defun fn-ich-test-result ()
 (declare (xargs :guard t))
 (with-local-stobj fn-ibp-connection-segment
  (mv-let (result fn-ibp-connection-segment) (fn-ich-test-lifecycle fn-ibp-connection-segment) result)))
(assert-event
 (equal (fn-ich-test-result)
  '(:reserved :attached :stale :acquired :stale :closing :stale
    :held nil nil :stale nil t :returned :ready
    (:publication-pin (:index-generation 9 2 3) (:test-published-source old))
    :test-grant :released :test-grant :stale nil :reserved nil :stale 1
    (:connection-holder (:connection-holder 18 1 0) 7 nil :reserved :next-grant 0))))

(defun fn-ich-test-source (fn-ibp-connection-segment)
 (declare (xargs :stobjs fn-ibp-connection-segment :guard t))
 (let ((fn-ibp-connection-segment
         (update-fn-ich-segment-id 3 fn-ibp-connection-segment)))
  (mv-let (a fn-ibp-connection-segment)
   (fn-ich-reserve '(:connection-holder 500 3 63) 42 :source-grant
                   fn-ibp-connection-segment)
   (mv-let (before before-pin)
    (fn-ich-source 42 '(:connection-holder 500 3 63) fn-ibp-connection-segment)
    (mv-let (b fn-ibp-connection-segment)
     (fn-ich-attach '(:connection-holder 500 3 63)
                    '(:publication-pin (:index-generation 8 1 1) :old-view)
                    fn-ibp-connection-segment)
     (mv-let (right right-pin)
      (fn-ich-source 42 '(:connection-holder 500 3 63) fn-ibp-connection-segment)
      (mv-let (wrong wrong-pin)
       (fn-ich-source 43 '(:connection-holder 500 3 63) fn-ibp-connection-segment)
       (mv-let (stale stale-pin)
        (fn-ich-source 42 '(:connection-holder 499 3 63) fn-ibp-connection-segment)
        (mv-let (foreign foreign-pin)
         (fn-ich-source 42 '(:connection-holder 500 4 63) fn-ibp-connection-segment)
         (mv (list a before before-pin b right right-pin wrong wrong-pin
                   stale stale-pin foreign foreign-pin)
             fn-ibp-connection-segment))))))))))
(defun fn-ich-test-source-result ()
 (declare (xargs :guard t))
 (with-local-stobj fn-ibp-connection-segment
  (mv-let (result fn-ibp-connection-segment)
   (fn-ich-test-source fn-ibp-connection-segment) result)))
(assert-event
 (equal (fn-ich-test-source-result)
  '(:reserved :stale nil :attached :current
    (:publication-pin (:index-generation 8 1 1) :old-view)
    :stale nil :stale nil :stale nil)))

; Corrupted-state witness: a tag saying RELEASED is not a free slot. Keep
; contradictory pin/alias/grant evidence instead of silently overwriting it.
(defun fn-ich-test-corrupt-free (fn-ibp-connection-segment)
 (declare (xargs :stobjs fn-ibp-connection-segment :guard t))
 (let* ((old '(:connection-holder (:connection-holder 1 1 0)
                5 :still-pinned :released :still-charged 1))
        (fn-ibp-connection-segment
         (update-fn-ich-segment-id 1 fn-ibp-connection-segment))
        (fn-ibp-connection-segment
         (update-fn-ich-rowsi 0 old fn-ibp-connection-segment)))
  (mv-let (word fn-ibp-connection-segment)
   (fn-ich-reserve '(:connection-holder 2 1 0) 6 :new-grant
                   fn-ibp-connection-segment)
   (mv (and (equal word :stale)
            (equal (fn-ich-rowsi 0 fn-ibp-connection-segment) old)
            (equal (fn-ich-active fn-ibp-connection-segment) 0))
       fn-ibp-connection-segment))))
(defun fn-ich-test-corrupt-free-result ()
 (declare (xargs :guard t))
 (with-local-stobj fn-ibp-connection-segment
  (mv-let (ok fn-ibp-connection-segment)
   (fn-ich-test-corrupt-free fn-ibp-connection-segment) ok)))
(assert-event (fn-ich-test-corrupt-free-result))

(assert-event
 (and (not (fn-ich-tokenp '(:connection-holder 1 1 64)))
      (not (fn-ich-tokenp '(:connection-holder 1 1 -1)))
      (not (fn-ich-tokenp '(:connection-holder 0 1 0)))
      (not (fn-ich-tokenp '(:connection-holder 1 0 0)))
      (not (fn-ich-tokenp '(:connection-holder 1 1 0 :extra)))
      (not (fn-ich-tokenp '(:connection-holder 1 1 . 0)))))
