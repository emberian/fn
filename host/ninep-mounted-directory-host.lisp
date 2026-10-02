; Actual retained generation source, read-only ordinary host boundary.
; Entry executes inside the genuine funded ninep provider operation; it is
; not a constructor permit and never takes a publication/root from native.
(in-package "ACL2")
(include-book "../books/ninep-mounted-directory")
(include-book "../books/definterface")

(defun fn-ninep-mounted-source (fuel fn-ninep-session fn-mio$c state)
 (declare (xargs :stobjs (fn-ninep-session fn-mio$c state) :guard (natp fuel)))
 (mv-let (word publication left)
  (fn-9pm-source-read fuel fn-ninep-session fn-mio$c)
  (mv word publication left state)))

; This boundary returns only the actual source-derived enumeration cursor.
; The caller retains it in the owned fid continuation. Publication is never
; supplied by host, even when an old mount survives a newer writer publication.
(defun fn-ninep-mounted-groups-begin (fuel fn-ninep-session fn-mio$c state)
 (declare (xargs :stobjs (fn-ninep-session fn-mio$c state) :guard (natp fuel)))
 (mv-let (word publication left)
  (fn-9pm-source-read fuel fn-ninep-session fn-mio$c)
  (if (eq word :source)
      (mv :directory (fn-9pm-groups-begin publication) left state)
    (mv word nil left state))))

(defthm fn-ninep-mounted-source-complete-boundary
 (equal (fn-ninep-mounted-source fuel fn-ninep-session fn-mio$c state)
        (list (mv-nth 0 (fn-9pm-source-read fuel fn-ninep-session fn-mio$c))
              (mv-nth 1 (fn-9pm-source-read fuel fn-ninep-session fn-mio$c))
              (mv-nth 2 (fn-9pm-source-read fuel fn-ninep-session fn-mio$c)) state))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-ninep-mounted-source) (fn-9pm-source-read)))))
(defthm fn-ninep-mounted-groups-begin-complete-boundary
 (let ((result (fn-9pm-source-read fuel fn-ninep-session fn-mio$c)))
  (equal (fn-ninep-mounted-groups-begin fuel fn-ninep-session fn-mio$c state)
   (list (if (eq (mv-nth 0 result) :source) :directory (mv-nth 0 result))
         (if (eq (mv-nth 0 result) :source) (fn-9pm-groups-begin (mv-nth 1 result)) nil)
         (mv-nth 2 result) state)))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-ninep-mounted-groups-begin)
                                  (fn-9pm-source-read fn-9pm-groups-begin)))))

(definterface fn-ninep-mounted-source :class :common-lisp-compliant :kinds ((fuel natp)))
(definterface fn-ninep-mounted-groups-begin :class :common-lisp-compliant :kinds ((fuel natp)))
