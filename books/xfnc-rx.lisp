; Counted FNCT input for XFNC (e-surface.md sections 5 and 13.4).
(in-package "ACL2")
(include-book "fnct-pool")
(fn2-book-layer :e)

;; The caller supplies the pinned request/discard bounds and terminal input
;; observation. For a request, POS is the first body byte and LEFT is the
;; complete outer length. For discard, POS is the next byte and LEFT is the
;; remaining extent. The caller retains the request bytes across compaction,
;; rebasing POS, or releases discarded prefixes as it receives more.
(defun fn2-xfnc-rx-plan (discard pos left fill cap request-max discard-max terminal)
  (declare (xargs :guard t))
  (cond ((or terminal
             (not (and (natp pos) (natp left) (natp fill) (natp cap)
                       (natp request-max) (natp discard-max)
                       (<= pos fill) (<= fill cap) (<= request-max discard-max)))
             (> left discard-max))
         (mv :close 0 0))
        ((or discard (> left request-max))
         (let* ((count (min (nfix left)
                            (min (nfix (- (nfix fill) (nfix pos))) *fn2-pool-block-bytes*)))
                (next (+ (nfix pos) count))
                (remaining (- (nfix left) count)))
           (mv (cond ((zp remaining) :discarded)
                     ((equal next fill) :discard-need-more)
                     (t :discard-more))
               next remaining)))
        ((or (> left cap) (> left (+ *fn2-pool-block-bytes* *fn2-fnct-trailer-octets*)))
         (mv :capacity 0 0))
        ((<= (+ (nfix pos) (nfix left)) fill)
         (mv :validate (+ (nfix pos) (nfix left)) 0))
        ((equal fill cap)
         (mv :compact pos left))
        (t (mv :need-more pos left))))

;; Use the declared remote carrier bindings. This first actor seam admits
;; only register and read; locality and grants belong to the actor.
(defun fn2-xfnc-peer-verb (kind code)
  (declare (xargs :guard t))
  (let ((binding (list kind code)))
    (cond ((equal binding (fn2-consumer-remote-binding 'register)) :register)
          ((equal binding (fn2-consumer-remote-binding 'read)) :read)
          (t :none))))

;; POS, LEFT, SLOT, GEN and the connection owner SCALARS remain the caller's
;; handle. On :ready, NEXT is the first suffix octet and VERB is the one
;; admitted by this seam. The frame is the exact [POS,NEXT) span of that
;; handle. Finish the actor handoff before advancing or compacting RX.
;; :frame, :access and :capacity yield no handoff. :discarded supplies the
;; exact end for a refusal; it never supplies a frame to the actor.
(defun fn2-xfnc-rx-step (base row slot gen conn-kind conn conn-gen discard pos left
                        request-max discard-max terminal fn2-fields fn2-digests fn2-b3 fn2-pool)
  (declare (xargs :stobjs (fn2-fields fn2-digests fn2-b3 fn2-pool)
                  :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
  (b* (((unless (eq (fn2-pool-workspace-code slot gen conn-kind conn conn-gen fn2-pool) :ok))
        (mv :access 0 0 :none fn2-fields fn2-digests fn2-b3))
       ((mv mode next remaining)
        (fn2-xfnc-rx-plan discard pos left (fn2-pool-fill-value slot fn2-pool)
                         (fn2-fnct-cap slot fn2-pool) request-max discard-max terminal))
       ((unless (eq mode :validate))
        (mv mode next remaining :none fn2-fields fn2-digests fn2-b3))
       ((mv opened kind payload-length fn2-fields fn2-digests fn2-b3)
        (fn2-fnct-open-pool-span base row slot gen pos next conn-kind conn conn-gen
                                fn2-fields fn2-digests fn2-b3 fn2-pool))
       ((when (eq opened :bounds)) (mv :capacity 0 0 :none fn2-fields fn2-digests fn2-b3))
       ((unless (and (eq opened :ok) (equal kind *fn2-fnct-request-kind*)
                     (posp payload-length) (natp base)
                     (< base (fn2-fields-rows fn2-fields))))
        (mv :frame 0 0 :none fn2-fields fn2-digests fn2-b3))
       (payload-start (+ (nfix pos) *fn2-fnct-header-octets*))
       ((mv head-code head-end fn2-fields)
        (fn2-fnct-k4-head-decode base slot gen payload-start (+ 1 payload-start)
                                conn-kind conn conn-gen fn2-fields fn2-pool))
       (verb (fn2-xfnc-peer-verb kind (fn2-fields-value base fn2-fields)))
       ((unless (and (eq head-code :ok) (equal head-end (+ 1 payload-start)) (not (eq verb :none))))
        (mv :frame 0 0 :none fn2-fields fn2-digests fn2-b3)))
    (mv :ready next 0 verb fn2-fields fn2-digests fn2-b3)))

(fn2-pool-block-shape fn2-xfnc-rx-step-shape
  (fn2-xfnc-rx-step base row slot gen conn-kind conn conn-gen discard pos left request-max discard-max terminal
                   fn2-fields fn2-digests fn2-b3 fn2-pool)
  (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
       (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests)
       (fn2-b3p fn2-b3) (fn2-b3-wfp fn2-b3) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
  ((fn2-fields 4) (fn2-digests 5) (fn2-b3 6))
  (("Goal" :in-theory (e/d (fn2-xfnc-rx-step)
                           (fn2-xfnc-rx-plan fn2-xfnc-peer-verb fn2-pool-workspace-code
                            fn2-fieldsp fn2-fields-wfp fn2-digestsp fn2-digests-wfp fn2-b3p fn2-b3-wfp
                            fn2-poolp fn2-pool-wfp fn2-pool-rows)))))
(in-theory (disable fn2-xfnc-rx-step))
