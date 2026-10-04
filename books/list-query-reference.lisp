; Disabled residual model for the actual LIST controller. No completion walk
; or model accessor below is called by the served path. Snapshot stability
; relates this model across catalog transitions separately.
(in-package "ACL2")
(include-book "served-query-plan")

(local (in-theory (disable (tau-system))))

(defun-nx fn-lst-status-reference (detail)
  (let ((tail (fn-cur-at 0 detail))
        (octets (fn-cur-at 1 detail))
        (moderated (fn-cur-at 2 detail)))
    (if (fn-nntp-closed-memberp octets tail) "n"
      (if (or moderated (fn-nntp-moderated-memberp octets tail)) "m" "y"))))

(defun-nx fn-lst-group-reference (env group fn-cat)
  (let* ((archive (fn-cur-at 0 env))
         (closed (fn-cur-at 1 env))
         (countsp (fn-cur-at 3 env))
         (next (nfix (fn-next-number group (fn-state-nexts archive))))
         (summary (fn-gsc-reference
                   (fn-gsc-start group (if (posp next) (1- next) 0) next
                                 (nfix (fn-cur-at 6 env))) fn-cat)))
    (fn-nntp-stuff-lines
     (list (fn-lst-line group summary countsp
                       (if (or (fn-cur-at 2 env) countsp)
                           (fn-nntp-closed-status (fn-nntp-string-octets group) closed)
                         "y"))))))

(defun-nx fn-lst-groups-reference (env groups fn-cat)
  (if (consp groups)
      (append
       (if (or (not (fn-cur-at 5 env))
               (fn-nntp-group-matches-parsed-wildmatp (fn-cur-at 4 env) (car groups)))
           (fn-lst-group-reference env (car groups) fn-cat) nil)
       (fn-lst-groups-reference env (cdr groups) fn-cat))
    '(46 13 10)))

(defun-nx fn-lst-progress-reference (progress fn-cat)
  (if (not progress) nil
    (let* ((env (fn-cur-at 0 progress))
           (phase (fn-cur-at 1 progress))
           (groups (fn-cur-at 2 progress))
           (group (fn-cur-at 3 progress))
           (detail (fn-cur-at 4 progress))
           (summary (fn-cur-at 5 progress))
           (closed (fn-cur-at 1 env))
           (statusp (fn-cur-at 2 env))
           (countsp (fn-cur-at 3 env))
           (v (nfix (fn-cur-at 6 env)))
           (future (fn-lst-groups-reference env groups fn-cat)))
      (cond
       ((eq phase :group) future)
       ((eq phase :match)
        (append (if (fn-wmc-value detail) (fn-lst-group-reference env group fn-cat) nil)
                future))
       ((eq phase :next)
        (let* ((next (nfix (fn-next-number group detail)))
               (s (fn-gsc-reference (fn-gsc-start group (if (posp next) (1- next) 0) next v) fn-cat)))
          (append (fn-nntp-stuff-lines
                   (list (fn-lst-line group s countsp
                           (if (or statusp countsp)
                               (fn-nntp-closed-status (fn-nntp-string-octets group) closed)
                             "y")))) future)))
       ((eq phase :summary)
        (append (fn-nntp-stuff-lines
                 (list (fn-lst-line group (fn-gsc-reference detail fn-cat) countsp
                         (if (or statusp countsp)
                             (fn-nntp-closed-status (fn-nntp-string-octets group) closed)
                           "y")))) future))
       ((eq phase :status)
        (append (fn-nntp-stuff-lines
                 (list (fn-lst-line group summary countsp (fn-lst-status-reference detail)))) future))
       ((eq phase :row)
        (append (fn-nntp-stuff-lines (list (fn-lst-line group summary countsp detail))) future))
       (t '(46 13 10))))))

(defun-nx fn-lst-remaining (cur fn-cat)
  (append (fn-cur-pending cur)
          (fn-lst-progress-reference (fn-cur-progress cur) fn-cat)))

(defun-nx fn-qplan-query-rest-remaining (effects w fn-arena fn-cat)
  (if (consp effects)
      (let ((effect (car effects)))
        (append
         (if (fn-lst-effectp effect) (fn-lst-remaining (fn-cur-at 1 effect) fn-cat)
           (if (fn-nnw-meta-effectp effect)
               (fn-nnw-stream-remaining (fn-cur-at 1 effect) fn-arena fn-cat)
             (if (fn-ovw-cursor-effectp effect)
                 (fn-ovw-run (fn-cur-at 1 effect) w fn-arena fn-cat)
               (fn-srb-effect-octets effect))))
         (fn-qplan-query-rest-remaining (cdr effects) w fn-arena fn-cat)))
    nil))

(defun-nx fn-qplan-query-remaining (plan w fn-arena fn-cat)
  (append (fn-splan-cur plan)
          (fn-qplan-query-rest-remaining (fn-splan-rest plan) w fn-arena fn-cat)))

(in-theory (disable fn-lst-status-reference fn-lst-group-reference fn-lst-groups-reference
                    fn-lst-progress-reference fn-lst-remaining fn-qplan-query-rest-remaining fn-qplan-query-remaining))
