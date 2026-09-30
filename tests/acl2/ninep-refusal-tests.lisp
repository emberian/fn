(in-package "ACL2")
(include-book "../../books/ninep-refusal")

(defthm ninep-refusal-complete-positive
 (and (fn-9p-profile-msizep 26) (natp 513) (< 513 65535)
      (equal (fn-9p-refusal-reply 26 513 :mount-unavailable)
       '(:refused :mount-unavailable
          (26 0 0 0 107 1 2 17 0 109 111 117 110 116 32 117 110 97 118 97 105 108 97 98 108 101)))) :rule-classes nil)

(defthm ninep-refusal-read-only-literal
 (equal (fn-9p-refusal-reply 18 0 :read-only)
  '(:refused :read-only (18 0 0 0 107 0 0 9 0 114 101 97 100 32 111 110 108 121))) :rule-classes nil)

(defthm ninep-refusal-too-small-retains-refusal
 (and (fn-9p-profile-msizep 25) (natp 513) (< 513 65535)
      (consp (fn-9p-refusal-text :mount-unavailable))
      (not (<= 26 25))
      (equal (fn-9p-refusal-reply 25 513 :mount-unavailable)
             '(:close :msize-too-small))) :rule-classes nil)

(defthm ninep-refusal-notag-refuses
 (and (fn-9p-profile-msizep 26) (natp 65535)
      (consp (fn-9p-refusal-text :mount-unavailable))
      (not (< 65535 65535))
      (equal (fn-9p-refusal-reply 26 65535 :mount-unavailable)
             '(:close :invalid-refusal))) :rule-classes nil)

; Hypothesis removal: without the affirmative :refused verdict, even the
; scalar fit conclusion is false. This is a refused invalid-profile input,
; not evidence that an installed supported profile may be negative.
(defthm ninep-refusal-fit-needs-refused-verdict
 (and (not (equal (car (fn-9p-refusal-reply -1 0 :read-only)) :refused))
      (not (and
             (<= (len (caddr (fn-9p-refusal-reply -1 0 :read-only))) -1)
             (<= (len (caddr (fn-9p-refusal-reply -1 0 :read-only))) 26))))
 :rule-classes nil)
