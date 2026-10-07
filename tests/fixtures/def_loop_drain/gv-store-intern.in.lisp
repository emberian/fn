(in-package "ACL2")
(include-book "def-loop-fixture-dep")

(defun fn-intern-events-loop (ws keyring generation acc fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (fn-prin-keyringp keyring) (natp generation))))
  (if (atom ws)
      (mv (fn-ag-rev-onto acc nil) fn-arena)
    (mv-let (row fn-arena)
      (fn-intern-event (car ws) keyring generation fn-arena)
      (if (eq row :bad)
          (mv :bad fn-arena)
        (fn-intern-events-loop (cdr ws) keyring generation (cons row acc) fn-arena)))))

(defun fn-intern-events (ws keyring generation fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (fn-prin-keyringp keyring) (natp generation))
                  :verify-guards nil))
  (mbe :logic
       (if (atom ws)
           (mv nil fn-arena)
         (mv-let (row fn-arena)
           (fn-intern-event (car ws) keyring generation fn-arena)
           (if (eq row :bad)
               (mv :bad fn-arena)
             (mv-let (rest fn-arena)
               (fn-intern-events (cdr ws) keyring generation fn-arena)
               (if (eq rest :bad)
                   (mv :bad fn-arena)
                 (mv (cons row rest) fn-arena))))))
       :exec (fn-intern-events-loop ws keyring generation nil fn-arena)))

(defthm fn-intern-events-loop-is-rev-onto
  (equal (fn-intern-events-loop ws keyring generation acc fn-arena)
         (mv-let (r a) (fn-intern-events ws keyring generation fn-arena)
           (mv (if (eq r :bad) :bad (fn-ag-rev-onto acc r)) a)))
  :hints (("Goal" :induct (fn-intern-events-loop ws keyring generation acc fn-arena)
                  :in-theory (disable fn-intern-event))))

(verify-guards fn-intern-events
  :hints (("Goal" :in-theory (disable fn-intern-event))))

(defthm fn-intern-events-arena-p
  (implies (and (fn-arena-p fn-arena) (fn-wire-event-listp ws))
           (fn-arena-p (mv-nth 1 (fn-intern-events ws keyring generation fn-arena))))
  :hints (("Goal" :induct (fn-intern-events ws keyring generation fn-arena)
           :in-theory (e/d (fn-intern-events)
                           (fn-intern-event fn-intern-event-arena fn-wire-event-p
                            fn-record-p fn-stxa-p fn-arena-p)))))

(local (defthm fn-rows-handles-inp-survives-intern-events
  (implies (and (fn-arena-p fn-arena) (fn-wire-event-listp ws) (fn-rows-handles-inp rows fn-arena))
           (fn-rows-handles-inp rows (mv-nth 1 (fn-intern-events ws keyring generation fn-arena))))
  :hints (("Goal" :induct (fn-intern-events ws keyring generation fn-arena)
           :in-theory (e/d (fn-intern-events)
                           (fn-intern-event fn-rows-handles-inp fn-intern-event-arena
                            fn-wire-event-p fn-record-p fn-stxa-p fn-arena-p))))))

(local (defthm fn-intern-events-step-handle
  (implies (and (fn-arena-p fn-arena) (natp generation) (fn-wire-event-p w)
                (fn-wire-event-listp ws)
                (not (equal (car (fn-intern-event w keyring generation fn-arena)) :bad)))
           (fn-rows-handles-inp
            (list (car (fn-intern-event w keyring generation fn-arena)))
            (mv-nth 1 (fn-intern-events ws keyring generation
                                        (mv-nth 1 (fn-intern-event w keyring generation fn-arena))))))
  :hints (("Goal" :in-theory (disable fn-intern-event fn-intern-events fn-rows-handles-inp
                                      fn-intern-event-handle-in
                                      fn-rows-handles-inp-survives-intern-events)
           :use ((:instance fn-intern-event-handle-in)
                 (:instance fn-rows-handles-inp-survives-intern-events
                  (rows (list (car (fn-intern-event w keyring generation fn-arena))))
                  (fn-arena (mv-nth 1 (fn-intern-event w keyring generation fn-arena)))))))))

(defthm fn-intern-events-handles-in
  (implies (and (fn-arena-p fn-arena) (natp generation) (fn-wire-event-listp ws)
                (not (equal (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)) :bad)))
           (fn-rows-handles-inp (mv-nth 0 (fn-intern-events ws keyring generation fn-arena))
                                (mv-nth 1 (fn-intern-events ws keyring generation fn-arena))))
  :hints (("Goal" :induct (fn-intern-events ws keyring generation fn-arena)
           :in-theory (e/d (fn-intern-events)
                           (fn-intern-event fn-intern-event-arena fn-row-handle-inp
                            fn-wire-event-p)))))

(local (defthm fn-row-wire-of-survives-intern-events
  (implies (and (fn-arena-p fn-arena) (fn-wire-event-listp ws)
                (fn-rows-handles-inp (list row) fn-arena))
           (equal (fn-row-wire-of row (mv-nth 1 (fn-intern-events ws keyring generation fn-arena)))
                  (fn-row-wire-of row fn-arena)))
  :hints (("Goal" :induct (fn-intern-events ws keyring generation fn-arena)
           :in-theory (e/d (fn-intern-events)
                           (fn-intern-event fn-rows-handles-inp fn-row-wire-of fn-intern-event-arena))))))

(local (defthm fn-intern-events-step-wire
  (implies (and (fn-arena-p fn-arena) (natp generation) (fn-wire-event-p w)
                (fn-wire-event-listp ws)
                (not (equal (car (fn-intern-event w keyring generation fn-arena)) :bad)))
           (equal (fn-row-wire-of
                   (car (fn-intern-event w keyring generation fn-arena))
                   (mv-nth 1 (fn-intern-events ws keyring generation
                                               (mv-nth 1 (fn-intern-event w keyring generation fn-arena)))))
                  w))
  :hints (("Goal" :in-theory (disable fn-intern-event fn-intern-events fn-rows-handles-inp
                                      fn-row-wire-of fn-intern-event-arena
                                      fn-intern-event-handle-in fn-intern-event-materializes
                                      fn-row-wire-of-survives-intern-events)
           :use ((:instance fn-intern-event-handle-in)
                 (:instance fn-intern-event-materializes)
                 (:instance fn-row-wire-of-survives-intern-events
                  (row (car (fn-intern-event w keyring generation fn-arena)))
                  (fn-arena (mv-nth 1 (fn-intern-event w keyring generation fn-arena)))))))))

(defthm fn-intern-events-materializes
  (implies (and (fn-arena-p fn-arena) (natp generation) (fn-wire-event-listp ws)
                (not (equal (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)) :bad)))
           (equal (fn-rows-wire-of (mv-nth 0 (fn-intern-events ws keyring generation fn-arena))
                                   (mv-nth 1 (fn-intern-events ws keyring generation fn-arena)))
                  ws))
  :hints (("Goal" :induct (fn-intern-events ws keyring generation fn-arena)
           :in-theory (e/d (fn-intern-events fn-rows-wire-of)
                           (fn-intern-event fn-row-wire-of fn-rows-handles-inp
                            fn-intern-event-arena fn-wire-event-p)))))

(defthm fn-intern-events-are-store-events
  (implies (and (natp generation)
                (not (equal (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)) :bad)))
           (fn-sf-record-valuesp (mv-nth 0 (fn-intern-events ws keyring generation fn-arena))))
  :hints (("Goal" :induct (fn-intern-events ws keyring generation fn-arena)
           :in-theory (e/d (fn-intern-events fn-sf-record-valuesp)
                           (fn-intern-event fn-intern-event-arena fn-store-event-p)))))

(defthm fn-intern-events-keep-coordinates
  (implies (and (natp generation)
                (not (equal (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)) :bad)))
           (equal (fn-row-coordinates (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)))
                  (fn-wire-coordinates ws)))
  :hints (("Goal" :induct (fn-intern-events ws keyring generation fn-arena)
           :in-theory (e/d (fn-intern-events)
                           (fn-intern-event fn-intern-event-arena fn-store-event-p
                            fn-store-event-sequence fn-store-event-txid
                            fn-store-event-generation fn-store-event-kind
                            fn-wire-event-sequence fn-wire-event-txid
                            fn-wire-event-generation fn-wire-event-kind)))))

(local (defthm fn-rows-contexts-okp-survives-intern-events
  (implies (and (fn-arena-p fn-arena) (fn-wire-event-listp ws) (fn-rows-handles-inp rows fn-arena)
                (fn-rows-contexts-okp rows keyring generation fn-arena))
           (fn-rows-contexts-okp rows keyring generation
                                 (mv-nth 1 (fn-intern-events ws k2 g2 fn-arena))))
  :hints (("Goal" :induct (fn-intern-events ws k2 g2 fn-arena)
           :in-theory (e/d (fn-intern-events)
                           (fn-intern-event fn-rows-handles-inp fn-rows-contexts-okp
                            fn-intern-event-arena))))))

(local (defthm fn-intern-events-step-context
  (implies (and (fn-arena-p fn-arena) (natp generation) (fn-wire-event-p w)
                (fn-wire-event-listp ws)
                (not (equal (car (fn-intern-event w keyring generation fn-arena)) :bad)))
           (fn-rows-contexts-okp
            (list (car (fn-intern-event w keyring generation fn-arena)))
            keyring generation
            (mv-nth 1 (fn-intern-events ws keyring generation
                                        (mv-nth 1 (fn-intern-event w keyring generation fn-arena))))))
  :hints (("Goal" :in-theory (disable fn-intern-event fn-intern-events fn-rows-handles-inp
                                      fn-rows-contexts-okp fn-intern-event-arena
                                      fn-intern-event-handle-in fn-intern-event-context-okp
                                      fn-rows-contexts-okp-survives-intern-events)
           :use ((:instance fn-intern-event-handle-in)
                 (:instance fn-intern-event-context-okp)
                 (:instance fn-rows-contexts-okp-survives-intern-events
                  (rows (list (car (fn-intern-event w keyring generation fn-arena))))
                  (k2 keyring) (g2 generation)
                  (fn-arena (mv-nth 1 (fn-intern-event w keyring generation fn-arena)))))))))

(defthm fn-intern-events-contexts-okp
  (implies (and (fn-arena-p fn-arena) (natp generation) (fn-wire-event-listp ws)
                (not (equal (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)) :bad)))
           (fn-rows-contexts-okp (mv-nth 0 (fn-intern-events ws keyring generation fn-arena))
                                 keyring generation
                                 (mv-nth 1 (fn-intern-events ws keyring generation fn-arena))))
  :hints (("Goal" :induct (fn-intern-events ws keyring generation fn-arena)
           :in-theory (e/d (fn-intern-events)
                           (fn-intern-event fn-row-context-okp fn-rows-handles-inp
                            fn-rows-contexts-okp fn-intern-event-arena fn-wire-event-p)))))
