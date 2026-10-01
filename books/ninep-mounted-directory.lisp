; Actual registered mount source plus bounded immutable group buckets.
; No supplied root, flat snapshot, current configuration or HISTORY alias.
(in-package "ACL2")
(include-book "ninep-mount")
(include-book "ninep-group-buckets")

(defun fn-9pm-source-read (fuel fn-ninep-session fn-mio$c)
 (declare (xargs :stobjs (fn-ninep-session fn-mio$c) :guard (natp fuel)))
 (let* ((intent (fn-9ps-mount-intent fn-ninep-session))
        (generation (fn-omk-at 2 intent)))
  (if (not (and (eq (fn-9ps-phase fn-ninep-session) :base)
                (eq (fn-9ps-mount-phase fn-ninep-session) :held)
                (fn-9ps-mount-token fn-ninep-session)
                (eq (fn-omk-at 0 intent) :ninep-mount-intent)
                (equal (fn-omk-at 1 intent) (fn-9ps-mount-token fn-ninep-session))
                (fn-ibp-generation-tokenp generation)))
      (mv :mount-unavailable nil fuel)
    (mv-let (word row left) (fn-mio-generation-read generation fuel fn-mio$c)
     (cond ((eq word :yield) (mv :yield nil left))
           ((not (and (eq word :present)
                      (equal (fn-omk-at 1 row) generation)
                      (member-eq (fn-omk-at 7 row) '(:live :retiring))
                      (posp (fn-omk-at 4 row))
                      (fn-omk-widthp (fn-omk-at 2 row) 19)
                      (eq (fn-omk-at 0 (fn-omk-at 2 row)) :index-publication)))
            (mv :recovery-required nil left))
           (t (mv :source (fn-omk-at 2 row) left)))))))

; Borrow immutable actual ownerView.slot5 from the registered Pub19.slot16.
; These are maintained visible buckets; configured empty groups require a
; separate captured configuration association and are not synthesized here.
(defun fn-9pm-source-buckets (publication)
 (declare (xargs :guard t))
 (fn-omk-at 5 (fn-ipub-visibility-source publication)))

(defun fn-9pm-groups-begin (publication)
 (declare (xargs :guard t))
 (fn-9pb-groups-begin (fn-9pm-source-buckets publication)))

(defun fn-9pm-group-walk-begin (publication begin count)
 (declare (xargs :guard t))
 (fn-9pb-group-walk-begin (fn-9pm-source-buckets publication) begin count))

(defthm fn-9pm-source-read-has-actual-registered-pin
 (let* ((intent (fn-9ps-mount-intent fn-ninep-session))
        (read (fn-mio-generation-read (fn-omk-at 2 intent) fuel fn-mio$c)))
  (implies (eq (mv-nth 0 (fn-9pm-source-read fuel fn-ninep-session fn-mio$c)) :source)
   (and (eq (mv-nth 0 read) :present)
        (equal (mv-nth 1 (fn-9pm-source-read fuel fn-ninep-session fn-mio$c))
               (fn-omk-at 2 (mv-nth 1 read)))
        (posp (fn-omk-at 4 (mv-nth 1 read)))
        (equal (fn-omk-at 1 (mv-nth 1 read)) (fn-omk-at 2 intent))
        (eq (fn-9ps-mount-phase fn-ninep-session) :held)
        (equal (fn-omk-at 1 intent) (fn-9ps-mount-token fn-ninep-session)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-9pm-source-read)
                                (fn-mio-generation-read fn-ibp-generation-tokenp
                                 fn-omk-at fn-omk-widthp)))))
