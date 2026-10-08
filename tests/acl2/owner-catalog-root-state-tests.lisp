(in-package "ACL2")
(include-book "../../books/owner-catalog-root-state")
(include-book "../../books/defkeystone")

(defteeth fn-ocr-reserve-preserves-issued-invariant
  :claim (((valid (fn-ocr-invariantp r issued)))
          (fn-ocr-invariantp (mv-nth 2 (fn-ocr-reserve r))
                            (cons (mv-nth 1 (fn-ocr-reserve r)) issued)))
  :subject fn-ocr-reserve
  :witness ((r '(2 :catalog-root 1)) (issued '((:catalog-root 0) (:catalog-root 1))))
  :breaks ((valid ((r '(-1 . :unissued)) (issued nil))))
  :mutations ((reset-counter (:conclusion
                (fn-ocr-invariantp (fn-ocr-initial)
                                  (cons (mv-nth 1 (fn-ocr-reserve r)) issued)))
               ((r '(2 :catalog-root 1)) (issued '((:catalog-root 0))))
               :fault "resetting the counter forgets issued tokens")))

(defteeth fn-ocr-reserve-never-reuses-an-earlier-token
  :claim (((earlier-issued (and (natp (fn-ocr-counter r)) (natp earlier)
                                (< earlier (fn-ocr-counter r)))))
          (not (equal (mv-nth 1 (fn-ocr-reserve r))
                      (mv-nth 0 (fn-cri-reserve earlier)))))
  :subject fn-ocr-reserve
  :witness ((r '(2 :catalog-root 1)) (earlier 0))
  :breaks ((earlier-issued ((r '(0 . :unissued)) (earlier 0))))
  :mutations ((reuse-after-reset (:conclusion
               (not (equal (mv-nth 1 (fn-ocr-reserve (fn-ocr-initial)))
                           (mv-nth 0 (fn-cri-reserve earlier)))))
               ((r '(2 :catalog-root 1)) (earlier 0))
               :fault "recovery resets the spent counter")))

(defteeth fn-ocr-corrupt-counter-refuses-without-reset
  :claim (((corrupt (not (natp (fn-ocr-counter r)))))
          (and (equal (mv-nth 0 (fn-ocr-reserve r)) :corrupt-catalog-root-counter)
               (equal (mv-nth 1 (fn-ocr-reserve r)) nil)
               (equal (mv-nth 2 (fn-ocr-reserve r)) r)))
  :subject fn-ocr-reserve
  :witness ((r '(-1 . :unissued)))
  :breaks ((corrupt ((r '(0 . :unissued)))))
  :mutations ((silent-reset (:conclusion
               (equal (mv-nth 2 (fn-ocr-reserve r)) (fn-ocr-initial)))
               ((r '(-1 . :unissued))) :fault "a corrupt counter silently resets")))

(assert-event (equal (mv-list 3 (fn-ocr-current (fn-ocr-initial)))
                     '(nil (:catalog-root 0) (1 :catalog-root 0))))
(assert-event (equal (mv-list 3 (fn-ocr-current '(3 :catalog-root 2)))
                     '(nil (:catalog-root 2) (3 :catalog-root 2))))
(assert-event (equal (mv-list 3 (fn-ocr-current '(3)))
                     '(:corrupt-catalog-root-incarnation nil (3))))
(defteeth fn-ocr-recovery-frame-prevents-token-reuse
  :claim (((preserved (equal recovered r))
           (earlier-issued (and (natp (fn-ocr-counter r)) (natp earlier)
                                (< earlier (fn-ocr-counter r)))))
          (not (equal (mv-nth 1 (fn-ocr-reserve recovered))
                      (mv-nth 0 (fn-cri-reserve earlier)))))
  :subject fn-ocr-reserve
  :witness ((r '(3 :catalog-root 2)) (recovered '(3 :catalog-root 2)) (earlier 0))
  :breaks ((preserved ((r '(3 :catalog-root 2)) (recovered '(0 . :unissued)) (earlier 0)))
           (earlier-issued ((r '(0 . :unissued)) (recovered '(0 . :unissued)) (earlier 0))))
  :mutations ((reset-after-recovery (:conclusion
                (not (equal (mv-nth 1 (fn-ocr-reserve (fn-ocr-initial)))
                            (mv-nth 0 (fn-cri-reserve earlier)))))
               ((r '(3 :catalog-root 2)) (recovered '(3 :catalog-root 2)) (earlier 0))
               :fault "resetting a successfully framed counter reissues token zero")))

(defteeth-check (fn-ocr-reserve-preserves-issued-invariant
                 fn-ocr-reserve-never-reuses-an-earlier-token
                 fn-ocr-corrupt-counter-refuses-without-reset
                 fn-ocr-recovery-frame-prevents-token-reuse))
