; The owner-table bridge for the bounded live FNFD port.  Host code must call
; this subject (or a named equation to it) before it writes a feed command.
(in-package "ACL2")
(include-book "owner-feed")
(include-book "feed-totality")

(defthm fn-own-feed-port-peer-refusal-preserves-table
  (implies (and (fn-own-feed-entry-of peer tbl)
                (not (and
                      (fn-feedp
                       (fn-own-feed-entry-feed (fn-own-feed-entry-of peer tbl)))
                      (fn-feed-records-portp
                       (fn-feed-live-records
                        (fn-own-feed-entry-feed (fn-own-feed-entry-of peer tbl))
                        event)))))
           (equal (fn-own-feed-port-peer peer tbl event)
                  (fn-own-feed-port-result :refused tbl nil nil)))
  :hints (("Goal"
           :use ((:instance fn-feed-live-port-step-refusal-preserves-work
                            (f (fn-own-feed-entry-feed
                                (fn-own-feed-entry-of peer tbl)))
                            (event event)))
           :in-theory (e/d (fn-own-feed-port-peer)
                            (fn-feed-live-port-step
                             fn-feed-live-port-step-refusal-preserves-work
                             fn-frame-item fn-own-feed-entry-of)))))

(defthm fn-own-feed-port-peer-ready-is-live-port-step
  (implies (and (fn-own-feed-entry-of peer tbl)
                (fn-feedp
                 (fn-own-feed-entry-feed (fn-own-feed-entry-of peer tbl)))
                (fn-feed-records-portp
                 (fn-feed-live-records
                  (fn-own-feed-entry-feed (fn-own-feed-entry-of peer tbl))
                  event)))
           (equal (fn-own-feed-port-peer peer tbl event)
                  (fn-own-feed-port-result
                   :accepted
                   (fn-own-feed-put
                    peer (fn-own-feed-entry-record (fn-own-feed-entry-of peer tbl))
                    (fn-feed-live-next
                     (fn-own-feed-entry-feed (fn-own-feed-entry-of peer tbl))
                     event)
                    tbl)
                   (fn-feed-live-records
                    (fn-own-feed-entry-feed (fn-own-feed-entry-of peer tbl)) event)
                   (let ((effects (fn-feed-live-effects
                                   (fn-own-feed-entry-feed
                                    (fn-own-feed-entry-of peer tbl)) event)))
                     (if (null effects) nil (list (cons peer effects)))))))
  :hints (("Goal"
           :use ((:instance fn-feed-live-port-step-accepted-unfolds
                            (f (fn-own-feed-entry-feed
                                (fn-own-feed-entry-of peer tbl)))
                            (event event)))
           :in-theory (e/d (fn-own-feed-port-peer)
                            (fn-feed-live-port-step
                             fn-feed-live-port-step-accepted-unfolds
                             fn-frame-item fn-own-feed-entry-of)))))

; Named event projections identify the functions the owner adapters use for
; tick, reply, loss and restart; the event and returned records are not host
; reconstructions.
(defthm fn-own-feed-port-tick-is-port-peer
  (equal (fn-own-feed-port-tick-peer peer tbl obs)
         (fn-own-feed-port-peer peer tbl (list :tick obs)))
  :hints (("Goal" :in-theory (enable fn-own-feed-port-tick-peer))))

(defthm fn-own-feed-port-observe-is-port-peer
  (equal (fn-own-feed-port-observe-peer peer tbl response article obs)
         (fn-own-feed-port-peer peer tbl (list :reply response article obs)))
  :hints (("Goal" :in-theory (enable fn-own-feed-port-observe-peer))))

(defthm fn-own-feed-port-lost-is-port-peer
  (equal (fn-own-feed-port-lost-peer peer tbl obs)
         (fn-own-feed-port-peer peer tbl (list :lost obs)))
  :hints (("Goal" :in-theory (enable fn-own-feed-port-lost-peer))))

(defthm fn-own-feed-port-restart-is-port-peer
  (equal (fn-own-feed-port-restart-peer peer tbl)
         (fn-own-feed-port-peer peer tbl (list :restart)))
  :hints (("Goal" :in-theory (enable fn-own-feed-port-restart-peer))))

; Restart is an all-or-nothing port transaction across the configured peers.
; The original table is carried separately so a late refusal cannot expose an
; earlier peer's restart or journal records to the host.
(defun fn-own-feed-port-restart-fold (names current original)
  (declare (xargs :guard t))
  (if (consp names)
      (let ((one (fn-own-feed-port-restart-peer (car names) current)))
        (if (not (equal (fn-own-feed-port-status one) :accepted))
            (fn-own-feed-port-result :refused original nil nil)
          (let ((rest (fn-own-feed-port-restart-fold
                       (cdr names) (fn-own-feed-port-table one) original)))
            (if (not (equal (fn-own-feed-port-status rest) :accepted))
                (fn-own-feed-port-result :refused original nil nil)
              (fn-own-feed-port-result
               :accepted
               (fn-own-feed-port-table rest)
               (append (fn-own-feed-port-records one)
                       (fn-own-feed-port-records rest))
               nil)))))
    (fn-own-feed-port-result :accepted current nil nil)))

(defthm fn-own-feed-port-restart-fold-refusal-preserves-original
  (implies (equal (fn-own-feed-port-status
                   (fn-own-feed-port-restart-fold names current original))
                  :refused)
           (equal (fn-own-feed-port-restart-fold names current original)
                  (fn-own-feed-port-result :refused original nil nil)))
  :hints (("Goal" :induct (fn-own-feed-port-restart-fold
                            names current original)
           :in-theory (enable fn-own-feed-port-restart-fold
                              fn-own-feed-port-status))))

(defthm fn-own-feed-port-restart-fold-accepted-cons-unfolds
  (let* ((one (fn-own-feed-port-restart-peer (car names) current))
         (rest (fn-own-feed-port-restart-fold
                (cdr names) (fn-own-feed-port-table one) original)))
    (implies (and (consp names)
                  (equal (fn-own-feed-port-status one) :accepted)
                  (equal (fn-own-feed-port-status rest) :accepted))
             (equal (fn-own-feed-port-restart-fold names current original)
                    (fn-own-feed-port-result
                     :accepted (fn-own-feed-port-table rest)
                     (append (fn-own-feed-port-records one)
                             (fn-own-feed-port-records rest)) nil))))
  :hints (("Goal" :in-theory (enable fn-own-feed-port-restart-fold))))

(in-theory (disable fn-own-feed-port-peer-refusal-preserves-table
                    fn-own-feed-port-peer-ready-is-live-port-step
                    fn-own-feed-port-restart-fold-refusal-preserves-original))
