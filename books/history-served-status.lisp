; Native status/health folds use resident columns, including default arms.
(in-package "ACL2")
(include-book "native-status-columns")
(include-book "history-served-cache")

(defthm fn-hist-resident-debt-is-record-debt
 (implies (equal hist (fn-sf-records (fn-sn-files s)))
  (equal (fn-hist-debt-served '(0 . 0) hist) (fn-cvec-record-debt hist)))
 :hints (("Goal" :use ((:instance fn-hist-debt-carried-is-debt-extend (cache '(0 . 0))))
 :in-theory (e/d (fn-hist-debt-served-is-carried fn-hist-cache-ready-p
                  fn-cvec-debt-extend fn-cvec-record-debt)
                 (fn-hist-debt-carried fn-hist-debt-served fn-cvec-debt-from fn-sf-records)))))


(defthm fn-hist-resident-bytes-is-bytes-extend
 (implies (and (fn-hist-of-storep hist s)
               (fn-hist-cache-ready-p cache (fn-hist-count hist) t))
  (equal (fn-hist-bytes-served cache hist)
         (fn-sbud-bytes-extend cache (fn-sf-records (fn-sn-files s)))))
 :hints (("Goal"
 :use ((:instance fn-hist-bytes-served-is-carried)
       (:instance fn-hist-bytes-carried-is-bytes-extend (fn-hist hist)))
 :in-theory '(fn-hist-of-storep))))

(defun fn-nls-report-resident (kind profile s bytes seen cfg pins obs fn-arena fn-hist)
 (declare (xargs :stobjs (fn-arena fn-hist) :guard t))
 (cond
   ((equal kind :peers)
    (ec-call (fn-native-admin-peer-budget-report (ec-call (fn-cfg-peers (ec-call (fn-cfg-value cfg)))))))
   ((equal kind :control)
    (ec-call (fn-native-admin-control-report (ec-call (fn-cfg-authorities (ec-call (fn-cfg-value cfg)))))))
   ; PRF-164: `account list' (books/accounts.lisp, no digest or verifier).
   ((equal kind :accounts) (ec-call (fn-acct-kinds-list-report (ec-call (fn-cfg-value cfg)))))
   ; Row Q10c: `consumer show', the consumer rows' lines alone.
   ((equal kind :consumers) (ec-call (fn-acct-consumers-list-report (ec-call (fn-cfg-value cfg)))))
   ((equal kind :pins) (ec-call (fn-nls-pins-line s pins)))
   ((equal kind :obligations)
    (append (ec-call (fn-nls-text "obligations="))
            (ec-call (fn-nls-nat (len (ec-call (fn-retain-pins (ec-call (fn-nls-retention s)))))))
            (ec-call (fn-nls-field "reserved" (ec-call (fn-retain-reserved (ec-call (fn-nls-retention s))))))
            *fn-nls-lf*
            (ec-call (fn-nls-obligation-lines (ec-call (fn-retain-pins (ec-call (fn-nls-retention s))))))))
   (t
    (append (ec-call (fn-nls-counts-words seen))
            (ec-call (fn-nls-text " ")) (ec-call (fn-nls-orphan-words obs))
            (ec-call (fn-nls-text " unsigned-legacy-experiment")) *fn-nls-lf*
            (ec-call (fn-nls-text "profile"))
            (ec-call (fn-nls-profile-words (ec-call (fn-bs-profile-report profile)))) *fn-nls-lf*
            (ec-call (fn-nls-open-cost-words profile)) *fn-nls-lf*
            (ec-call (fn-nls-headroom-words (ec-call (fn-sbud-headroom-at profile s bytes)))) *fn-nls-lf*
            (ec-call (fn-nls-capacity-words (ec-call (fn-sbud-headroom-at profile s bytes)))) *fn-nls-lf*
            (ec-call (fn-nls-reserve-words
             (ec-call (fn-cvec-report profile (ec-call (fn-sbud-used s)) bytes
                             (ec-call (fn-hist-debt-served '(0 . 0) fn-hist))))))
            *fn-nls-lf*
            (ec-call (fn-nls-open-words obs)) *fn-nls-lf*
            (ec-call (fn-nls-reclaim-words s cfg obs fn-arena)) *fn-nls-lf*
            (ec-call (fn-nls-checkpoint-file-words obs)) *fn-nls-lf*
            (ec-call (fn-nls-pins-line s pins))))))

(defthm fn-nls-report-resident-is-reference
 (implies (and (fn-hist-of-storep hist s) )
  (equal (fn-nls-report-resident kind profile s bytes seen cfg pins obs fn-arena hist) (fn-nls-report kind profile s bytes seen cfg pins obs fn-arena)))
 :hints (("Goal" :use ((:instance fn-hist-resident-debt-is-record-debt (s s)))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nls-report-resident fn-nls-report fn-hist-of-storep
 fn-hist-resident-bytes-is-bytes-extend
 fn-hist-resident-debt-is-record-debt )))))
(in-theory (disable fn-nls-report-resident))

(defun fn-nsc-report-resident (kind profile s bytes seen cfg pins obs fn-arena fn-cat fn-hist)
 (declare (xargs :stobjs (fn-arena fn-cat fn-hist) :guard t))
 (if (member-equal kind '(:peers :control :accounts :consumers :pins :obligations))
      (ec-call (fn-nls-report-resident kind profile s bytes seen cfg pins obs fn-arena fn-hist))
    (append (ec-call (fn-nls-counts-words seen))
            (ec-call (fn-nls-text " ")) (ec-call (fn-nls-orphan-words obs))
            (ec-call (fn-nls-text " unsigned-legacy-experiment")) *fn-nls-lf*
            (ec-call (fn-nls-text "profile"))
            (ec-call (fn-nls-profile-words (ec-call (fn-bs-profile-report profile)))) *fn-nls-lf*
            (ec-call (fn-nls-open-cost-words profile)) *fn-nls-lf*
            (ec-call (fn-nls-headroom-words (ec-call (fn-sbud-headroom-at profile s bytes)))) *fn-nls-lf*
            (ec-call (fn-nls-capacity-words (ec-call (fn-sbud-headroom-at profile s bytes)))) *fn-nls-lf*
            (ec-call (fn-nls-reserve-words
             (ec-call (fn-cvec-report profile (ec-call (fn-sbud-used s)) bytes
                             (ec-call (fn-hist-debt-served '(0 . 0) fn-hist))))))
            *fn-nls-lf*
            (ec-call (fn-nls-open-words obs)) *fn-nls-lf*
            (ec-call (fn-nsc-reclaim-words s cfg obs fn-arena fn-cat)) *fn-nls-lf*
            (ec-call (fn-nls-checkpoint-file-words obs)) *fn-nls-lf*
            (ec-call (fn-nls-pins-line s pins)))))

(defthm fn-nsc-report-resident-is-reference
 (implies (and (fn-hist-of-storep hist s) )
  (equal (fn-nsc-report-resident kind profile s bytes seen cfg pins obs fn-arena fn-cat hist) (fn-nsc-report kind profile s bytes seen cfg pins obs fn-arena fn-cat)))
 :hints (("Goal" :use ((:instance fn-hist-resident-debt-is-record-debt (s s)))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nsc-report-resident fn-nsc-report fn-hist-of-storep
 fn-hist-resident-bytes-is-bytes-extend
 fn-hist-resident-debt-is-record-debt fn-nls-report-resident-is-reference)))))
(in-theory (disable fn-nsc-report-resident))

(defun fn-nsc-live-report-resident (kind profile oc cache obs fn-arena fn-cat fn-hist)
 (declare (xargs :stobjs (fn-arena fn-cat fn-hist) :guard t))
 (let ((s (ec-call (fn-own-store (ec-call (fn-ocfg-owner oc))))))
    (ec-call (fn-nsc-report-resident kind profile s
                   (ec-call (fn-hist-bytes-served cache fn-hist))
                   (ec-call (fn-nls-view-seen (ec-call (fn-own-view (ec-call (fn-ocfg-owner oc))))))
                   (ec-call (fn-ocfg-config oc)) (ec-call (fn-ocfg-pins oc)) obs fn-arena fn-cat fn-hist))))

(defthm fn-nsc-live-report-resident-is-reference
 (implies (and (fn-hist-of-storep hist (fn-own-store (fn-ocfg-owner oc))) (fn-hist-cache-ready-p cache (fn-hist-count hist) t))
  (equal (fn-nsc-live-report-resident kind profile oc cache obs fn-arena fn-cat hist) (fn-nsc-live-report kind profile oc cache obs fn-arena fn-cat)))
 :hints (("Goal" :use ((:instance fn-hist-resident-debt-is-record-debt (s (fn-own-store (fn-ocfg-owner oc))))
       (:instance fn-hist-resident-bytes-is-bytes-extend (s (fn-own-store (fn-ocfg-owner oc)))))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nsc-live-report-resident fn-nsc-live-report fn-hist-of-storep
 fn-hist-resident-bytes-is-bytes-extend
 fn-hist-resident-debt-is-record-debt fn-nls-report-resident-is-reference fn-nsc-report-resident-is-reference)))))
(in-theory (disable fn-nsc-live-report-resident))

(defun fn-nh-live-report-resident (profile oc cache min disk ckpt fn-hist)
 (declare (xargs :stobjs (fn-hist) :guard t))
 (let ((s (ec-call (fn-own-store (ec-call (fn-ocfg-owner oc))))))
    (ec-call (fn-nh-render
     (ec-call (fn-nh-verdict nil
                    (ec-call (fn-nh-store-inputs
                     profile s (ec-call (fn-hist-bytes-served cache fn-hist))
                     (ec-call (fn-ocfg-config oc))))
                    min (ec-call (fn-own-feeds (ec-call (fn-ocfg-owner oc)))) disk ckpt))))))

(defthm fn-nh-live-report-resident-is-reference
 (implies (and (fn-hist-of-storep hist (fn-own-store (fn-ocfg-owner oc))) (fn-hist-cache-ready-p cache (fn-hist-count hist) t))
  (equal (fn-nh-live-report-resident profile oc cache min disk ckpt hist) (fn-nh-live-report profile oc cache min disk ckpt)))
 :hints (("Goal" :use ((:instance fn-hist-resident-debt-is-record-debt (s (fn-own-store (fn-ocfg-owner oc))))
       (:instance fn-hist-resident-bytes-is-bytes-extend (s (fn-own-store (fn-ocfg-owner oc)))))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nh-live-report-resident fn-nh-live-report fn-hist-of-storep
 fn-hist-resident-bytes-is-bytes-extend
 fn-hist-resident-debt-is-record-debt fn-nls-report-resident-is-reference fn-nsc-report-resident-is-reference fn-nsc-live-report-resident-is-reference)))))
(in-theory (disable fn-nh-live-report-resident))

(defun fn-nsc-answer-report-resident (kind profile oc cache obs min disk fn-arena fn-cat fn-hist)
 (declare (xargs :stobjs (fn-arena fn-cat fn-hist) :guard t))
 (if (equal kind :health)
      (ec-call (fn-nh-live-report-resident profile oc cache min disk (ec-call (fn-nls-obs-checkpoint-deferred obs)) fn-hist))
    (ec-call (fn-nsc-live-report-resident kind profile oc cache obs fn-arena fn-cat fn-hist))))

(defthm fn-nsc-answer-report-resident-is-reference
 (implies (and (fn-hist-of-storep hist (fn-own-store (fn-ocfg-owner oc))) (fn-hist-cache-ready-p cache (fn-hist-count hist) t))
  (equal (fn-nsc-answer-report-resident kind profile oc cache obs min disk fn-arena fn-cat hist) (fn-nsc-answer-report kind profile oc cache obs min disk fn-arena fn-cat)))
 :hints (("Goal" :use ((:instance fn-hist-resident-debt-is-record-debt (s (fn-own-store (fn-ocfg-owner oc))))
       (:instance fn-hist-resident-bytes-is-bytes-extend (s (fn-own-store (fn-ocfg-owner oc)))))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nsc-answer-report-resident fn-nsc-answer-report fn-hist-of-storep
 fn-hist-resident-bytes-is-bytes-extend
 fn-hist-resident-debt-is-record-debt fn-nls-report-resident-is-reference fn-nsc-report-resident-is-reference fn-nsc-live-report-resident-is-reference fn-nh-live-report-resident-is-reference)))))
(in-theory (disable fn-nsc-answer-report-resident))
