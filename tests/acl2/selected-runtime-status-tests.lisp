(in-package "ACL2")
(include-book "../../books/selected-runtime-status")
(include-book "../../books/legacy-parser-cursor")
(defthm fn-srtt-status-literals
 (and (equal (fn-srt-status t :ready nil) :ready)
      (equal (fn-srt-status nil :ready nil) :unavailable)
      (equal (fn-srt-status t :refused nil) :refused)
      (equal (fn-srt-status t :ready t) :fault))
 :rule-classes nil)
