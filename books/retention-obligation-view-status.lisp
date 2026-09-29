; Exact status report substitution: count is carried, every other octet/effect
; stays the existing report's. No refresh, rebuild, or ledger test at read.
(in-package "ACL2")
(include-book "native-status-columns")
(include-book "retention-obligation-view")
(include-book "owner-reader-view")

(defun fn-rov-pins-line (s pins count)
  (declare (xargs :guard t :verify-guards nil))
  (append (fn-nls-text "pins=") (fn-nls-nat count)
          (fn-nls-field "reserved" (fn-retain-reserved (fn-nls-retention s)))
          (fn-nls-field "connections" (len pins)) *fn-nls-lf*
          (fn-nls-connection-lines pins)))

(defun fn-rov-report (kind profile s bytes seen cfg pins obs count fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard t :verify-guards nil))
  (cond ((equal kind :pins) (fn-rov-pins-line s pins count))
        ((equal kind :obligations)
         (append (fn-nls-text "obligations=") (fn-nls-nat count)
                 (fn-nls-field "reserved" (fn-retain-reserved (fn-nls-retention s)))
                 *fn-nls-lf* (fn-nls-obligation-lines (fn-retain-pins (fn-nls-retention s)))))
        ((member-equal kind '(:peers :control :accounts))
         (fn-nls-report kind profile s bytes seen cfg pins obs fn-arena))
        (t
         (append (fn-nls-counts-words seen) (fn-nls-text " ") (fn-nls-orphan-words obs)
                 (fn-nls-text " unsigned-legacy-experiment") *fn-nls-lf*
                 (fn-nls-text "profile") (fn-nls-profile-words (fn-bs-profile-report profile)) *fn-nls-lf*
                 (fn-nls-open-cost-words profile) *fn-nls-lf*
                 (fn-nls-headroom-words (fn-sbud-headroom-at profile s bytes)) *fn-nls-lf*
                 (fn-nls-capacity-words (fn-sbud-headroom-at profile s bytes)) *fn-nls-lf*
                 (fn-nls-reserve-words (fn-cvec-report profile (fn-sbud-used s) bytes
                                         (fn-cvec-record-debt (fn-sf-records (fn-sn-files s))))) *fn-nls-lf*
                 (fn-nls-open-words obs) *fn-nls-lf*
                 (fn-nsc-reclaim-words s cfg obs fn-arena fn-cat) *fn-nls-lf*
                 (fn-nls-checkpoint-file-words obs) *fn-nls-lf*
                 (fn-rov-pins-line s pins count)))))

(defthm fn-rov-report-is-nsc-report
  (implies (equal count (len (fn-retain-pins (fn-nls-retention s))))
           (equal (fn-rov-report kind profile s bytes seen cfg pins obs count fn-arena fn-cat)
                  (fn-nsc-report kind profile s bytes seen cfg pins obs fn-arena fn-cat)))
  :hints (("Goal" :in-theory '(fn-rov-report fn-rov-pins-line fn-nls-pins-line
                               fn-nsc-report fn-nls-report member-equal))))

(defun fn-rov-live-report (kind profile oc cache obs count fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard t :verify-guards nil))
  (let ((s (fn-own-store (fn-ocfg-owner oc))))
    (fn-rov-report kind profile s
      (fn-sbud-bytes-extend cache (fn-sf-records (fn-sn-files s)))
      (fn-nls-view-seen (fn-own-view (fn-ocfg-owner oc)))
      (fn-ocfg-config oc) (fn-ocfg-pins oc) obs count fn-arena fn-cat)))

(defun fn-rov-answer-report (kind profile oc cache obs min disk count fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard t :verify-guards nil))
  (if (equal kind :health)
      (fn-nh-live-report profile oc cache min disk (fn-nls-obs-checkpoint-deferred obs))
    (fn-rov-live-report kind profile oc cache obs count fn-arena fn-cat)))

(defthm fn-rov-answer-report-is-answer-report
  (implies (equal count (len (fn-retain-pins
                             (fn-nls-retention (fn-own-store (fn-ocfg-owner oc))))))
           (equal (fn-rov-answer-report kind profile oc cache obs min disk count fn-arena fn-cat)
                  (fn-nsc-answer-report kind profile oc cache obs min disk fn-arena fn-cat)))
  :hints (("Goal" :in-theory '(fn-rov-answer-report fn-rov-live-report
                               fn-nsc-answer-report fn-nsc-live-report
                               fn-rov-report-is-nsc-report))))

(defthm fn-rov-answer-report-from-corresponding-view
  (implies (fn-rov-correspondp view
             (fn-retain-pins (fn-nls-retention (fn-own-store (fn-ocfg-owner oc)))))
           (equal (fn-rov-answer-report kind profile oc cache obs min disk
                                         (fn-rov-count view) fn-arena fn-cat)
                  (fn-nsc-answer-report kind profile oc cache obs min disk fn-arena fn-cat)))
  :hints (("Goal" :in-theory '(fn-rov-answer-report-is-answer-report
                               fn-rov-count-is-pin-count))))

(defthm fn-rov-reader-view-keeps-retention
  (equal (fn-nls-retention
          (fn-own-store (fn-ocfg-owner (fn-ocfg-at-reader-view oc readers))))
         (fn-nls-retention (fn-own-store (fn-ocfg-owner oc))))
  :hints (("Goal" :in-theory (enable fn-ocfg-at-reader-view))))

(defthm fn-rov-answer-report-at-reader-view-from-corresponding-view
  (implies (fn-rov-correspondp view
             (fn-retain-pins (fn-nls-retention (fn-own-store (fn-ocfg-owner oc)))))
           (equal (fn-rov-answer-report kind profile (fn-ocfg-at-reader-view oc readers)
                    cache obs min disk (fn-rov-count view) fn-arena fn-cat)
                  (fn-nsc-answer-report kind profile (fn-ocfg-at-reader-view oc readers)
                    cache obs min disk fn-arena fn-cat)))
  :hints (("Goal" :in-theory '(fn-rov-answer-report-from-corresponding-view
                               fn-rov-reader-view-keeps-retention))))

(in-theory (disable fn-rov-report fn-rov-live-report fn-rov-answer-report fn-rov-pins-line))
