; Pointwise refinement of repeated private window capture to source octets.
(in-package "ACL2")
(include-book "extent-window-capture")
(include-book "octet-window")

(local
 (defthm ewr-double-minus
   (implies (acl2-numberp x) (equal (- (- x)) x))))

; MSG is proof-only: the immutable protected prefix, never constructed by
; the executable reader. The bounded input buffer is its current block.
; An already captured byte is retained; a newly encountered byte is exactly
; its source byte. Universal J gives the complete requested window once the
; scan reaches ELEN and WOFF+WN <= ELEN.
(defthm fn-ewb-capture-extends-faithful-window
  (implies
    (and (natp j) (natp (nth 4 s)) (natp (nth 5 s)) (natp (nth 7 s))
         (equal (nth 0 s) :scan) (< j (nth 5 s))
         (< (+ (nth 4 s) j) (+ (nth 7 s) (fn-ewp-demand s)))
         (equal fn-octets (fn-shr-win (nth 7 s) (fn-ewp-demand s) msg))
         (implies (< (+ (nth 4 s) j) (nth 7 s))
                  (equal (nth j (nth 0 fn-ew-buffer))
                         (nth (+ (nth 4 s) j) msg))))
    (equal (nth j (nth 0 (fn-ewb-capture s fn-octets fn-ew-buffer)))
           (nth (+ (nth 4 s) j) msg)))
  :hints (("Goal"
           :use (fn-ewp-demand-bounded
                 (:instance fn-ewb-capture-exact-output-and-effects))
           :in-theory (e/d (fn-ewp-window-span nfix)
                            (fn-ewb-capture fn-ewp-demand nth fn-ewb-capture-exact-output-and-effects)))))
