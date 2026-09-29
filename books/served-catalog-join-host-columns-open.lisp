; served-catalog-join-host-columns-open.lisp -- fn-sjh-colsp established at
; the host's opens (lane join-f2-2, 2026-09-29; PRF-302).
;
; The open interns the decoded journal into the cleared arena
; (books/store-intern.lisp fn-intern-events): each row's decided column is the
; column of the payload it seals (fn-scol-intern-list-facts), and the rows
; materialize to the events (fn-intern-events-materializes), so every row's
; column is its bytes' (fn-sjh-col-intern-events-history-okp); the catalog
; loaded from them then satisfies fn-sjh-colsp.  The checkpoint open names the
; checkpoint rows' column facts, as fn-sjh-okp-at-recover names their other
; facts.

(in-package "ACL2")

(include-book "served-catalog-join-host-columns")
(include-book "served-catalog-join-host-open")
(include-book "served-catalog-join-host-identity-finish") ; fn-sjh-idf-loaded-event-kind

(local (in-theory (disable (tau-system))))

; -----------------------------------------------------------------------------
; The opens: the intern decides each row's column from the bytes it seals.


(defun-nx fn-sjh-col-row-matchp (r w)
  (and (implies (fn-held-p r)
                (equal (fn-held-facts r) (fn-held-facts-of (fn-record-payload w))))
       (implies (fn-hstxa-p r)
                (equal (fn-held-facts (fn-hstxa-held r))
                       (fn-held-facts-of (fn-record-payload (fn-replay-composite-record w)))))))

(defun-nx fn-sjh-col-facts-match (rows ws)
  (if (consp rows)
      (and (consp ws)
           (fn-sjh-col-row-matchp (car rows) (car ws))
           (fn-sjh-col-facts-match (cdr rows) (cdr ws)))
    t))


(defthm fn-sjh-col-intern-event-row
  (equal (car (fn-intern-event w keyring generation fn-arena))
         (cond ((fn-record-p w) (car (fn-cat-intern-list w keyring generation fn-arena)))
               ((fn-stxa-p w)
                (if (fn-record-p (fn-replay-composite-record w))
                    (fn-hstxa-make w (car (fn-cat-intern-list (fn-replay-composite-record w)
                                                              keyring generation fn-arena)))
                  :bad))
               ((fn-wire-event-p w) w)
               (t :bad)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-intern-event mv-nth car-cons cdr-cons (:e zp) (:e nfix) default-car)
                                             (theory 'minimal-theory)))))

(defthm fn-sjh-col-wire-event-is-neither
  (implies (fn-wire-event-p w)
           (and (not (fn-held-p w)) (not (fn-hstxa-p w))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-wire-event-p) (theory 'minimal-theory))
           :use ((:instance fn-held-is-no-wire-event (x w))
                 (:instance fn-hstxa-is-no-wire-event (x w))))))


(defthm fn-sjh-col-intern-list-car-facts
  (equal (fn-held-facts (car (fn-cat-intern-list w keyring generation fn-arena)))
         (fn-held-facts-of (fn-record-payload w)))
  :hints (("Goal" :in-theory (union-theories '(mv-nth (:e zp) default-car) (theory 'minimal-theory))
           :use ((:instance fn-scol-intern-list-facts)))))

(defthm fn-sjh-col-intern-list-car-held
  (implies (and (fn-record-p w) (natp generation))
           (and (fn-held-p (car (fn-cat-intern-list w keyring generation fn-arena)))
                (not (fn-hstxa-p (car (fn-cat-intern-list w keyring generation fn-arena))))))
  :hints (("Goal" :in-theory (union-theories '(mv-nth (:e zp) default-car) (theory 'minimal-theory))
           :use ((:instance fn-held-p-of-intern-list)
                 (:instance fn-sjh-hstxa-is-not-held (x (car (fn-cat-intern-list w keyring generation fn-arena))))))))


(defthm fn-sjh-col-intern-event-row-matchp
  (implies (and (natp generation)
                (not (equal (car (fn-intern-event w keyring generation fn-arena)) :bad)))
           (fn-sjh-col-row-matchp (car (fn-intern-event w keyring generation fn-arena)) w))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-sjh-col-row-matchp fn-hstxa-accessors-of-make
                                        fn-sjh-col-intern-list-car-facts)
                                      (theory 'minimal-theory))
           :cases ((fn-record-p w) (fn-stxa-p w))
           :use ((:instance fn-sjh-col-intern-event-row)
                 (:instance fn-sjh-col-wire-event-is-neither)
                 (:instance fn-sjh-col-intern-list-car-held)
                 (:instance fn-sjh-col-intern-list-car-held (w (fn-replay-composite-record w)))
                 (:instance fn-sjh-hstxa-is-not-held
                            (x (fn-hstxa-make w (car (fn-cat-intern-list (fn-replay-composite-record w)
                                                                         keyring generation fn-arena)))))
                 (:instance fn-hstxa-p-of-make
                            (stxa w)
                            (held (car (fn-cat-intern-list (fn-replay-composite-record w)
                                                           keyring generation fn-arena))))))))

(defthm fn-sjh-col-intern-events-facts-match
  (implies (and (natp generation)
                (not (equal (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)) :bad)))
           (fn-sjh-col-facts-match (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)) ws))
  :hints (("Goal" :induct (fn-intern-events ws keyring generation fn-arena)
           :in-theory (e/d (fn-intern-events fn-sjh-col-facts-match)
                           (fn-intern-event fn-intern-event-arena fn-sjh-col-row-matchp)))
          ("Subgoal *1/2" :use ((:instance fn-sjh-col-intern-event-row-matchp (w (car ws)))))))

(defthm fn-sjh-col-payload-of-held-wire
  (equal (fn-record-payload (fn-held-wire h p)) p)
  :hints (("Goal" :in-theory (enable fn-held-wire))))

(defthm fn-sjh-col-held-row-okp
  (implies (and (fn-held-p h)
                (fn-row-handle-inp h fn-arena)
                (equal (fn-held-facts h)
                       (fn-held-facts-of (fn-record-payload (fn-row-wire-of h fn-arena)))))
           (fn-scol-row-okp h fn-arena))
  :hints (("Goal" :in-theory (e/d (fn-scol-row-okp fn-row-wire-of fn-row-bytes fn-nntp-payload-bytes
                                   fn-row-handle-inp)
                                  (fn-held-p fn-held-wire fn-held-facts-of fn-hstxa-p)))))


(defthm fn-sjh-col-hstxa-is-not-cat-row
  (implies (fn-hstxa-p r) (not (fn-cat-rowp r)))
  :hints (("Goal" :in-theory (e/d (fn-cat-rowp fn-held-shapep) (fn-hstxa-p))
           :use ((:instance fn-hstxa-p-forward-shape (x r))))))
(defthm fn-sjh-col-cat-row-store-event-is-held
  (implies (and (fn-store-event-p r) (fn-cat-rowp r))
           (fn-held-p r))
  :hints (("Goal" :in-theory (e/d (fn-scj-load-h) (fn-held-p fn-hstxa-p fn-cat-rowp fn-store-event-p))
           :use ((:instance fn-sjh-idf-loaded-event-kind)
                 (:instance fn-scjs-hstxa-shape)))))

(defthm fn-sjh-col-composite-store-event-is-hstxa
  (implies (and (fn-store-event-p r) (fn-sca-composite-shapep r))
           (fn-hstxa-p r))
  :hints (("Goal" :in-theory (e/d (fn-scj-load-h fn-sca-composite-shapep)
                                  (fn-held-p fn-hstxa-p fn-cat-rowp fn-store-event-p))
           :use ((:instance fn-sjh-idf-loaded-event-kind)
                 (:instance fn-held-p-forward-natural-head (x r))
                 (:instance fn-held-p-implies-cat-rowp (x r))))))

(defthm fn-sjh-col-held-not-composite
  (implies (fn-held-p r) (not (fn-sca-composite-shapep r)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-sca-composite-shapep) (fn-held-p fn-cat-rowp))
           :use ((:instance fn-held-p-forward-natural-head (x r))))))


(defthm fn-sjh-col-row-history-okp
  (implies (and (fn-store-event-p r)
                (fn-sjh-col-row-matchp r (fn-row-wire-of r fn-arena))
                (fn-row-composite-okp r fn-arena)
                (fn-rows-handles-inp (list r) fn-arena))
           (and (or (not (fn-cat-rowp r)) (fn-scol-row-okp r fn-arena))
                (or (not (fn-sca-composite-shapep r)) (fn-scol-row-okp (fn-hstxa-held r) fn-arena))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :cases ((fn-held-p r) (fn-hstxa-p r))
           :expand ((fn-rows-handles-inp (list r) fn-arena) (fn-rows-handles-inp nil fn-arena))
           :in-theory (union-theories '(fn-sjh-col-row-matchp fn-row-composite-okp fn-rows-handles-inp
                                        (:e fn-rows-handles-inp) fn-row-wire-of car-cons cdr-cons)
                                      (theory 'minimal-theory))
           :use ((:instance fn-sjh-col-cat-row-store-event-is-held)
                 (:instance fn-sjh-col-composite-store-event-is-hstxa)
                 (:instance fn-sjh-col-held-not-composite)
                 (:instance fn-sjh-col-hstxa-is-not-cat-row)
                 (:instance fn-hstxa-is-not-held (x r))
                 (:instance fn-hstxa-p-fields (x r))
                 (:instance fn-sjh-col-held-row-okp (h r))
                 (:instance fn-sjh-col-held-row-okp (h (fn-hstxa-held r)))))))

(defthm fn-sjh-col-rows-handles-inp-of-cons
  (equal (fn-rows-handles-inp (cons r rs) fn-arena)
         (and (fn-rows-handles-inp (list r) fn-arena) (fn-rows-handles-inp rs fn-arena)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-rows-handles-inp))))


(defthm fn-sjh-col-history-okp-of-match
  (implies (and (fn-sjh-col-facts-match rows (fn-rows-wire-of rows fn-arena))
                (fn-rows-composites-okp rows fn-arena)
                (fn-rows-handles-inp rows fn-arena)
                (fn-sf-record-valuesp rows))
           (fn-scol-history-okp rows fn-arena))
  :hints (("Goal" :induct (len rows)
           :in-theory (union-theories '(fn-sjh-col-facts-match fn-scol-history-okp fn-rows-wire-of
                                        fn-rows-composites-okp fn-sf-record-valuesp car-cons cdr-cons cons-car-cdr
                                        len (:e fn-scol-history-okp))
                                      (theory 'minimal-theory)))
          ("Subgoal *1/1" :use ((:instance fn-sjh-col-row-history-okp (r (car rows)))
                                (:instance fn-sjh-col-rows-handles-inp-of-cons (r (car rows)) (rs (cdr rows)))))))

(defthm fn-sjh-col-load-h-handle
  (implies (and (fn-store-event-p r)
                (fn-rows-handles-inp (list r) fn-arena)
                (fn-scj-load-h r))
           (fn-scol-handles-below (list (fn-scj-load-h r)) (len fn-arena)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-sjh-load-h-of-held fn-rows-handles-inp car-cons cdr-cons
                                        (:e fn-rows-handles-inp) fn-row-handle-inp fn-sjh-col-handles-below-singleton
                                        fn-arena-count-is-len fn-scj-load-h nfix natp (:type-prescription len))
                                      (theory 'minimal-theory))
           :expand ((fn-rows-handles-inp (list r) fn-arena))
           :use ((:instance fn-sjh-idf-loaded-event-kind)
                 (:instance fn-sjh-col-hstxa-is-not-cat-row)
                 (:instance fn-hstxa-is-not-held (x r))
                 (:instance fn-sjh-col-held-not-composite)
                 (:instance fn-held-p-implies-cat-rowp (x r))))))

(defthm fn-sjh-col-handles-below-of-load-held-row
  (implies (and (fn-scol-handles-below fn-cat n)
                (implies (fn-scj-load-h r) (fn-scol-handles-below (list (fn-scj-load-h r)) n)))
           (fn-scol-handles-below (fn-sca-load-held-row r view-index fn-cat) n))
  :hints (("Goal" :in-theory (e/d (fn-scj-load-held-row-is)
                                  (fn-scj-load-h fn-cat-commit fn-held-with-withdrawn fn-midx-lookup
                                   fn-scol-handles-below fn-sca-load-held-row)))))


(defthm fn-sjh-col-handles-below-of-load-from
  (implies (and (fn-scol-handles-below fn-cat (len fn-arena))
                (fn-rows-handles-inp rows fn-arena)
                (fn-sf-record-valuesp rows))
           (fn-scol-handles-below (fn-sca-load-held-rows-from rows view-index fn-cat) (len fn-arena)))
  :hints (("Goal" :induct (fn-sca-load-held-rows-from rows view-index fn-cat)
           :in-theory (union-theories '(fn-sca-load-held-rows-from fn-sf-record-valuesp car-cons cdr-cons cons-car-cdr)
                                      (theory 'minimal-theory)))
          ("Subgoal *1/2" :use ((:instance fn-sjh-col-load-h-handle (r (car rows)))
                                (:instance fn-sjh-col-rows-handles-inp-of-cons (r (car rows)) (rs (cdr rows)))
                                (:instance fn-sjh-col-handles-below-of-load-held-row (r (car rows))
                                           (n (len fn-arena)))))
          ("Subgoal *1/1" :use ((:instance fn-sjh-col-load-h-handle (r (car rows)))
                                (:instance fn-sjh-col-rows-handles-inp-of-cons (r (car rows)) (rs (cdr rows)))
                                (:instance fn-sjh-col-handles-below-of-load-held-row (r (car rows))
                                           (n (len fn-arena)))))))

(defthm fn-sjh-col-cat-clear-is-nil
  (equal (fn-cat-clear fn-cat) nil)
  :hints (("Goal" :in-theory (enable fn-cat-clear fn-cat$a-clear))))

(defthm fn-sjh-col-handles-below-of-clear
  (fn-scol-handles-below (fn-cat-clear fn-cat) n)
  :hints (("Goal" :in-theory (enable fn-cat-clear fn-cat$a-clear fn-scol-handles-below))))

(defthm fn-sjh-col-load-held-rows-colsp
  (implies (and (fn-arena-p fn-arena)
                (fn-scol-history-okp rows fn-arena)
                (fn-rows-handles-inp rows fn-arena)
                (fn-sf-record-valuesp rows))
           (fn-sjh-colsp nil fn-arena (fn-sca-load-held-rows rows view-index fn-arena fn-cat)))
  :hints (("Goal" :in-theory (union-theories '(fn-sjh-colsp fn-sca-load-held-rows fn-sjh-col-handles-below-of-clear fn-sjh-col-cat-clear-is-nil fn-scol-handles-below)
                                             (theory 'minimal-theory))
           :use ((:instance fn-scol-okp-of-load-held-rows)
                 (:instance fn-sjh-col-handles-below-of-load-from (fn-cat (fn-cat-clear fn-cat)))))))

; KEYSTONE (the columns at the checkpoint open and recovery): the owner
; fn-owner-install-extended installs from a checkpoint's rows PREFIX and the
; replayed SUFFIX, the catalog loaded from them; the rows' column facts are
; the checkpoint image's (named, as fn-sjh-okp-at-recover names the rows'
; other facts; the full open below discharges them from the intern).
(defthm fn-sjh-colsp-at-recover
  (let* ((oc (fn-ock-recover-extended
              (fn-sco-extend (fn-sco-capture configs prefix) configs suffix)
              configs frontier max-conns))
         (o (fn-ocfg-owner oc))
         (rows (fn-sf-records (fn-sn-files (fn-own-store o)))))
    (implies (and (not (equal oc :fault))
                  (fn-arena-p fn-arena)
                  (fn-rows-handles-inp (append prefix suffix) fn-arena)
                  (fn-rows-composites-okp (append prefix suffix) fn-arena)
                  (fn-scol-history-okp (append prefix suffix) fn-arena))
             (fn-sjh-colsp nil fn-arena
                           (fn-sca-load-held-rows rows (fn-own-view-index (fn-own-view o)) fn-arena fn-cat))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '() (theory 'minimal-theory))
           :use ((:instance fn-sca-ocl-relation-at-recover
                            (view-index (fn-own-view-index
                                         (fn-own-view (fn-ocfg-owner
                                                       (fn-ock-recover-extended
                                                        (fn-sco-extend (fn-sco-capture configs prefix) configs suffix)
                                                        configs frontier max-conns))))))
                 (:instance fn-ock-recover-installs-ocl-relation)
                 (:instance fn-sca-ocl-store-rows-are-values
                            (oc (fn-ock-recover-extended
                                 (fn-sco-extend (fn-sco-capture configs prefix) configs suffix)
                                 configs frontier max-conns)))
                 (:instance fn-sjh-col-load-held-rows-colsp
                            (rows (append prefix suffix))
                            (view-index (fn-own-view-index
                                         (fn-own-view (fn-ocfg-owner
                                                       (fn-ock-recover-extended
                                                        (fn-sco-extend (fn-sco-capture configs prefix) configs suffix)
                                                        configs frontier max-conns))))))))))

(defthm fn-sjh-col-intern-events-history-okp
  (let ((rows (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)))
        (arena (mv-nth 1 (fn-intern-events ws keyring generation fn-arena))))
    (implies (and (fn-arena-p fn-arena) (natp generation) (fn-wire-event-listp ws)
                  (not (equal rows :bad)))
             (fn-scol-history-okp rows arena)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '() (theory 'minimal-theory))
           :use ((:instance fn-sjh-col-intern-events-facts-match)
                 (:instance fn-intern-events-materializes)
                 (:instance fn-sca-intern-events-composites-okp)
                 (:instance fn-intern-events-handles-in)
                 (:instance fn-intern-events-are-store-events)
                 (:instance fn-sjh-col-history-okp-of-match
                            (rows (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)))
                            (fn-arena (mv-nth 1 (fn-intern-events ws keyring generation fn-arena))))))))


(defthm fn-sjh-col-arena-p-of-clear
  (fn-arena-p (fn-arena-clear fn-arena))
  :hints (("Goal" :in-theory (enable fn-arena-clear))))

; KEYSTONE (the columns at the full open): the rows the open interns from the
; decoded journal into the cleared arena, the catalog loaded from them.
(defthm fn-sjh-colsp-at-full-open
  (let* ((arena0 (fn-arena-clear fn-arena))
         (rows (mv-nth 0 (fn-intern-events ws nil 0 arena0)))
         (arena (mv-nth 1 (fn-intern-events ws nil 0 arena0)))
         (oc (fn-ock-recover-extended
              (fn-sco-extend (fn-sco-capture configs nil) configs rows)
              configs frontier max-conns))
         (o (fn-ocfg-owner oc)))
    (implies (and (true-listp ws)
                  (not (equal rows :bad))
                  (not (equal oc :fault)))
             (fn-sjh-colsp nil arena
                           (fn-sca-load-held-rows (fn-sf-records (fn-sn-files (fn-own-store o)))
                                                  (fn-own-view-index (fn-own-view o))
                                                  arena fn-cat))))
  :hints (("Goal" :use ((:instance fn-sjh-colsp-at-recover
                                   (prefix nil)
                                   (suffix (mv-nth 0 (fn-intern-events ws nil 0 (fn-arena-clear fn-arena))))
                                   (fn-arena (mv-nth 1 (fn-intern-events ws nil 0 (fn-arena-clear fn-arena)))))
                        (:instance fn-sca-intern-events-accepts-wire-events
                                   (keyring nil) (generation 0) (fn-arena (fn-arena-clear fn-arena)))
                        (:instance fn-intern-events-arena-p
                                   (keyring nil) (generation 0) (fn-arena (fn-arena-clear fn-arena)))
                        (:instance fn-intern-events-handles-in
                                   (keyring nil) (generation 0) (fn-arena (fn-arena-clear fn-arena)))
                        (:instance fn-sca-intern-events-composites-okp
                                   (keyring nil) (generation 0) (fn-arena (fn-arena-clear fn-arena)))
                        (:instance fn-sjh-col-intern-events-history-okp
                                   (keyring nil) (generation 0) (fn-arena (fn-arena-clear fn-arena))))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(binary-append fn-sjh-col-arena-p-of-clear
                                        (:executable-counterpart natp)
                                        (:executable-counterpart consp))))))


