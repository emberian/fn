; The served LIST cursor answers the available-command model's reply.
; fn-lst-active-command / fn-lst-counts-command (the generated available
; dispatcher's LIST forms) start a cursor whose reference body
; (fn-lst-groups-reference, books/list-metadata-cursor) is the body
; fn-av-nntp-list-active-cat / fn-av-nntp-list-counts-command-cat render:
; both read each group's summary as fn-scat-available-summary, so the
; equality holds with no premise on the catalog. Logical only.
; The numbered walk the cursor used to run is fn-lst-probe-summary;
; fn-lst-available-summary-is-probe ties the carried summary to it.
(in-package "ACL2")
(include-book "served-query-plan")
(include-book "served-available-commands")

(local (in-theory (disable (tau-system))))

; The summary the LIST cursor's numbered probes settle on for GROUP whose
; allocation watermark is NEXT, at view V: executable, for fixtures.
(defun fn-lst-probe-summary (group next v fn-cat)
  (declare (xargs :stobjs fn-cat :verify-guards nil))
  (let* ((next (nfix next))
         (high (if (posp next) (- next 1) 0))
         (numbers (fn-scat-available-numbers group 1 high (nfix v) fn-cat)))
    (if (consp numbers)
        (list (len numbers) (car numbers) (fn-scat-available-last numbers))
      (list 0 next high))))

; Induction scheme over a group list.
(defun fn-lar-groups-induct (groups)
  (declare (xargs :guard t))
  (if (consp groups) (fn-lar-groups-induct (cdr groups)) groups))

(local
 (defthm fn-lar-numbers-true-listp
   (true-listp (fn-scat-available-numbers group low high v fn-cat))
   :hints (("Goal" :in-theory (enable fn-scat-available-numbers)))))

(local
 (defthm fn-lar-numbers-positive
   (implies (and (natp low) (< 0 low) (consp (fn-scat-available-numbers group low high v fn-cat)))
            (< 0 (car (fn-scat-available-numbers group low high v fn-cat))))
   :hints (("Goal" :in-theory (enable fn-scat-available-numbers)
            :induct (fn-scat-available-numbers group low high v fn-cat)))))

(local
 (defthm fn-lar-numbers-empty
   (implies (and (natp low) (natp high) (< high low))
            (equal (fn-scat-available-numbers group low high v fn-cat) nil))
   :hints (("Goal" :in-theory (enable fn-scat-available-numbers)))))

(local (defthm fn-lar-len-of-consp (implies (consp x) (< 0 (len x))) :rule-classes :linear))

(local
 (defthm fn-lar-append-pieces-append
   (equal (fn-nntp-append-pieces (append a b))
          (append (fn-nntp-append-pieces a) (fn-nntp-append-pieces b)))
   :hints (("Goal" :in-theory (enable fn-nntp-append-pieces)))))


(local
 (defthm fn-lar-env-fields
   (and (equal (fn-cur-at 1 (fn-lst-env archive closed statusp countsp patterns filteredp v)) closed)
        (equal (fn-cur-at 2 (fn-lst-env archive closed statusp countsp patterns filteredp v)) statusp)
        (equal (fn-cur-at 3 (fn-lst-env archive closed statusp countsp patterns filteredp v)) countsp)
        (equal (fn-cur-at 4 (fn-lst-env archive closed statusp countsp patterns filteredp v)) patterns)
        (equal (fn-cur-at 5 (fn-lst-env archive closed statusp countsp patterns filteredp v)) filteredp)
        (equal (fn-cur-at 6 (fn-lst-env archive closed statusp countsp patterns filteredp v)) (nfix v))
        (equal (fn-cur-at 0 (fn-lst-env archive closed statusp countsp patterns filteredp v)) archive))
   :hints (("Goal" :in-theory (enable fn-lst-env fn-cur-at)))))


(local
 (defthm fn-lar-active-line-is-lst-line
   (equal (fn-av-scat-active-line archive group v fn-cat)
          (fn-lst-line group (fn-scat-available-summary archive group v fn-cat) nil "y"))
   :hints (("Goal" :in-theory (e/d (fn-lst-line fn-nntp-append-pieces fn-av-scat-active-line)
                                   (fn-nntp-decimal-field fn-scat-available-summary))))))

(local
 (defthm fn-lar-status-line-is-lst-line
   (equal (fn-av-scat-active-status-line archive group closed v fn-cat)
          (fn-lst-line group (fn-scat-available-summary archive group v fn-cat) nil
                       (fn-nntp-closed-status (fn-nntp-string-octets group) closed)))
   :hints (("Goal" :in-theory (e/d (fn-lst-line fn-nntp-append-pieces fn-av-scat-active-status-line)
                                   (fn-nntp-decimal-field fn-scat-available-summary
                                    fn-nntp-closed-status fn-nntp-string-octets))))))

(defthm fn-lst-groups-reference-is-active-lines
  (implies (natp v)
           (equal (fn-lst-groups-reference
                   (fn-lst-env archive closed statusp nil patterns filteredp v) groups fn-cat)
                  (append (fn-nntp-stuff-lines
                           (fn-av-scat-active-lines
                            archive (if filteredp (fn-nntp-filter-groups-by-wildmat patterns groups) groups)
                            closed statusp v fn-cat))
                          '(46 13 10))))
  :hints (("Goal" :induct (fn-lar-groups-induct groups)
           :in-theory (e/d (fn-lst-groups-reference fn-lst-group-reference fn-lst-row-reference
                            fn-lst-row-status fn-lar-groups-induct fn-lst-group-summary fn-av-scat-active-lines
                            fn-nntp-filter-groups-by-wildmat fn-nntp-stuff-lines)
                           (fn-lst-line fn-scat-available-summary
                            fn-lst-env fn-nntp-closed-status fn-av-scat-active-line
                            fn-av-scat-active-status-line
                            fn-nntp-group-matches-parsed-wildmatp)))))

(local
 (defthm fn-lar-counts-line-is-lst-line
   (equal (fn-nntp-counts-summary-line group summary closed)
          (fn-lst-line group summary t
                       (fn-nntp-closed-status (fn-nntp-string-octets group) closed)))
   :hints (("Goal" :in-theory (e/d (fn-lst-line fn-nntp-append-pieces fn-nntp-counts-summary-line)
                                   (fn-nntp-decimal-field fn-nntp-closed-status fn-nntp-string-octets))))))

(defthm fn-lst-groups-reference-is-counts-lines
  (implies (natp v)
           (equal (fn-lst-groups-reference
                   (fn-lst-env archive closed statusp t patterns filteredp v) groups fn-cat)
                  (append (fn-nntp-stuff-lines
                           (fn-av-scat-counts-lines
                            archive (if filteredp (fn-nntp-filter-groups-by-wildmat patterns groups) groups)
                            closed v fn-cat))
                          '(46 13 10))))
  :hints (("Goal" :induct (fn-lar-groups-induct groups)
           :in-theory (e/d (fn-lst-groups-reference fn-lst-group-reference fn-lst-row-reference
                            fn-lst-row-status fn-lar-groups-induct fn-lst-group-summary fn-av-scat-counts-lines
                            fn-nntp-filter-groups-by-wildmat fn-nntp-stuff-lines)
                           (fn-lst-line fn-scat-available-summary
                            fn-lst-env fn-nntp-closed-status fn-nntp-counts-summary-line
                            fn-nntp-group-matches-parsed-wildmatp)))))

(local
 (defthm fn-lar-multi-octets
   (equal (fn-served-reply-octets (fn-nntp-result-effects (fn-nntp-multi session initial lines)))
          (append (fn-nntp-crlf (fn-nntp-string-octets initial))
                  (fn-nntp-stuff-lines lines) '(46 13 10)))
   :hints (("Goal" :in-theory (enable fn-served-reply-octets fn-nntp-multi fn-nntp-make-result
                                      fn-nntp-result-effects fn-nntp-reply-effect fn-srb-effect-octets)))))

(local
 (defthm fn-lar-single-octets
   (equal (fn-qplan-cw-octets (fn-nntp-result-effects (fn-nntp-single session text)) wl fn-arena fn-cat)
          (fn-served-reply-octets (fn-nntp-result-effects (fn-nntp-single session text))))
   :hints (("Goal" :in-theory (enable fn-qplan-cw-octets fn-served-reply-octets fn-nntp-single
                                      fn-nntp-make-result fn-nntp-result-effects fn-nntp-reply-effect
                                      fn-lst-effectp fn-splan-cursor-effectp)))))

(local (defthm fn-lar-append-assoc
         (equal (append (append x y) z) (append x (append y z)))))

; KEYSTONE (lane served): the generated available dispatcher's LIST ACTIVE
; form answers the available-command model, its plan read with the LIST
; cursor as its completion; fn-qplan-cw-drain-is-a-prefix carries this to
; what the host writes.
(defthm fn-lst-active-command-is-av-list-active
  (implies (natp v)
           (and (equal (fn-nntp-result-session (fn-lst-active-command session archive closed args v fn-cat))
                       (fn-nntp-result-session (fn-av-nntp-list-active-cat session archive closed args v fn-cat)))
                (equal (fn-qplan-cw-octets
                        (fn-nntp-result-effects (fn-lst-active-command session archive closed args v fn-cat))
                        wl fn-arena fn-cat)
                       (fn-served-reply-octets
                        (fn-nntp-result-effects (fn-av-nntp-list-active-cat session archive closed args v fn-cat))))))
  :hints (("Goal" :in-theory (e/d (fn-lst-active-command fn-av-nntp-list-active-cat fn-lst-result
                                   fn-nntp-make-result fn-nntp-result-session)
                                  (fn-nntp-multi fn-nntp-single fn-lst-groups-reference
                                   fn-av-scat-active-lines fn-lst-env fn-nntp-crlf fn-nntp-string-octets
                                   fn-nntp-stuff-lines fn-nntp-result-effects fn-qplan-cw-octets
                                   fn-served-reply-octets fn-wildmat-parse))
           :use ((:instance fn-lst-result-cw-octets (statusp (consp closed)) (countsp nil)
                            (patterns nil) (filteredp nil))
                 (:instance fn-lst-result-cw-octets (statusp (consp closed)) (countsp nil)
                            (patterns (fn-wildmat-result-value (fn-wildmat-parse (car (cdr args)))))
                            (filteredp t))))))

(defthm fn-lst-counts-command-is-av-list-counts
  (implies (natp v)
           (and (equal (fn-nntp-result-session (fn-lst-counts-command session archive closed args v fn-cat))
                       (fn-nntp-result-session (fn-av-nntp-list-counts-command-cat session archive closed args v fn-cat)))
                (equal (fn-qplan-cw-octets
                        (fn-nntp-result-effects (fn-lst-counts-command session archive closed args v fn-cat))
                        wl fn-arena fn-cat)
                       (fn-served-reply-octets
                        (fn-nntp-result-effects (fn-av-nntp-list-counts-command-cat session archive closed args v fn-cat))))))
  :hints (("Goal" :in-theory (e/d (fn-lst-counts-command fn-av-nntp-list-counts-command-cat fn-lst-result
                                   fn-nntp-make-result fn-nntp-result-session)
                                  (fn-nntp-multi fn-nntp-single fn-lst-groups-reference
                                   fn-av-scat-counts-lines fn-lst-env fn-nntp-crlf fn-nntp-string-octets
                                   fn-nntp-stuff-lines fn-nntp-result-effects fn-qplan-cw-octets
                                   fn-served-reply-octets fn-wildmat-parse))
           :use ((:instance fn-lst-result-cw-octets (statusp t) (countsp t)
                            (patterns nil) (filteredp nil))
                 (:instance fn-lst-result-cw-octets (statusp t) (countsp t)
                            (patterns (fn-wildmat-result-value (fn-wildmat-parse (car args))))
                            (filteredp t))))))

(in-theory (disable fn-lst-probe-summary))
