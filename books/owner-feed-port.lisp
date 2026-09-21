; The owner-table bridge for the bounded live FNFD port.  Host code must call
; this subject (or a named equation to it) before it writes a feed command.
(in-package "ACL2")
(include-book "owner-feed")
(include-book "feed-totality")

(defthm fn-own-feed-port-peer-refusal-preserves-table
  (implies (and (fn-own-feed-entry-of peer tbl)
                (not (equal
                      (fn-feed-port-step-status
                       (fn-feed-live-port-step
                        (fn-own-feed-entry-feed (fn-own-feed-entry-of peer tbl))
                        event))
                      :accepted)))
           (and (equal (fn-own-feed-port-status
                        (fn-own-feed-port-peer peer tbl event))
                       :refused)
                (equal (fn-own-feed-port-table
                        (fn-own-feed-port-peer peer tbl event))
                       tbl)
                (equal (fn-own-feed-port-records
                        (fn-own-feed-port-peer peer tbl event)) nil)
                (equal (fn-own-feed-port-effects
                        (fn-own-feed-port-peer peer tbl event)) nil)))
  :hints (("Goal" :in-theory (enable fn-own-feed-port-peer
                                      fn-own-feed-port-status
                                      fn-own-feed-port-table
                                      fn-own-feed-port-records
                                      fn-own-feed-port-effects))))

(defthm fn-own-feed-port-peer-ready-is-live-port-step
  (implies (and (fn-own-feed-entry-of peer tbl)
                (fn-feedp
                 (fn-own-feed-entry-feed (fn-own-feed-entry-of peer tbl)))
                (fn-feed-records-portp
                 (fn-feed-live-records
                  (fn-own-feed-entry-feed (fn-own-feed-entry-of peer tbl))
                  event)))
           (and (equal (fn-own-feed-port-status
                        (fn-own-feed-port-peer peer tbl event))
                       :accepted)
                (equal (fn-own-feed-port-table
                        (fn-own-feed-port-peer peer tbl event))
                       (fn-own-feed-put
                        peer (fn-own-feed-entry-record
                              (fn-own-feed-entry-of peer tbl))
                        (fn-feed-live-next
                         (fn-own-feed-entry-feed (fn-own-feed-entry-of peer tbl))
                         event)
                        tbl))
                (equal (fn-own-feed-port-records
                        (fn-own-feed-port-peer peer tbl event))
                       (fn-feed-live-records
                        (fn-own-feed-entry-feed (fn-own-feed-entry-of peer tbl))
                        event))
                (equal (fn-own-feed-port-effects
                        (fn-own-feed-port-peer peer tbl event))
                       (let ((effects (fn-feed-live-effects
                                       (fn-own-feed-entry-feed
                                        (fn-own-feed-entry-of peer tbl)) event)))
                         (if (null effects) nil (list (cons peer effects)))))))
  :hints (("Goal"
           :use ((:instance fn-feed-live-port-step-accepted-unfolds
                            (f (fn-own-feed-entry-feed
                                (fn-own-feed-entry-of peer tbl)))
                            (event event)))
           :in-theory (e/d (fn-own-feed-port-peer
                             fn-own-feed-port-status fn-own-feed-port-table
                             fn-own-feed-port-records fn-own-feed-port-effects
                             fn-own-feed-port-result)
                            (fn-feed-live-port-step
                             fn-feed-live-port-step-accepted-unfolds)))))

; Named event projections identify the functions the owner adapters use for
; tick, reply, loss and restart; the event and returned records are not host
; reconstructions.
(defthm fn-own-feed-port-tick-is-port-peer
  (equal (fn-own-feed-port-tick-peer peer tbl obs)
         (fn-own-feed-port-peer peer tbl (list :tick obs))))

(defthm fn-own-feed-port-observe-is-port-peer
  (equal (fn-own-feed-port-observe-peer peer tbl response article obs)
         (fn-own-feed-port-peer peer tbl (list :reply response article obs))))

(defthm fn-own-feed-port-lost-is-port-peer
  (equal (fn-own-feed-port-lost-peer peer tbl obs)
         (fn-own-feed-port-peer peer tbl (list :lost obs))))

(defthm fn-own-feed-port-restart-is-port-peer
  (equal (fn-own-feed-port-restart-peer peer tbl)
         (fn-own-feed-port-peer peer tbl (list :restart))))

(in-theory (disable fn-own-feed-port-peer-refusal-preserves-table
                    fn-own-feed-port-peer-ready-is-live-port-step))
