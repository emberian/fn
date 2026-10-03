(in-package "ACL2")
(include-book "../../books/native-init-resume")

(defconst *nirt-first* (fn-cfg-encode *fn-cfg-default-record*))
(defconst *nirt-later-stamp*
  (fn-clock-observation 812345000000 812345678901 250 t))
(defconst *nirt-later-record*
  (fn-cfg-record-make 0 0 1 *fn-cfg-default-change* *nirt-later-stamp*))
(defconst *nirt-later* (fn-cfg-encode *nirt-later-record*))

; Reachable encoded initial records with different real clock readings;
; complete literal keystone premises and conclusion.
(assert-event
 (and (equal (fn-cfg-decode-exact *nirt-first*)
             (fn-record-parse-ok
              (fn-cfg-record-make 0 0 1 *fn-cfg-default-change* *fn-cfg-default-stamp*) nil))
      (equal (fn-cfg-decode-exact *nirt-later*)
             (fn-record-parse-ok *nirt-later-record* nil))
      (equal (fn-nir-resume-decision '(:sealed) '(:sealed) *nirt-first* *nirt-later* '("00000001.cfg" "00000002.cfg"))
             '(:accepted :resume))))

; Requested-decode omission: every retained premise holds; bad bytes fault.
(assert-event
 (and (not (equal (fn-cfg-decode-exact '(0))
                  (fn-record-parse-ok
                   (fn-cfg-record-make 0 0 1 *fn-cfg-default-change* *fn-cfg-default-stamp*) nil)))
      (equal (fn-cfg-decode-exact *nirt-later*)
             (fn-record-parse-ok *nirt-later-record* nil))
      (not (equal (fn-nir-resume-decision '(:sealed) '(:sealed) '(0) *nirt-later* nil)
                  '(:accepted :resume)))))
; Recorded-decode omission: different initial groups, valid exact encoding.
(defconst *nirt-changed-record*
  (fn-cfg-record-make 0 0 1
                      (cons (fn-cfg-create-group "fn.extra" "") *fn-cfg-default-change*)
                      *nirt-later-stamp*))
(defconst *nirt-changed* (fn-cfg-encode *nirt-changed-record*))
(assert-event
 (and (equal (fn-cfg-decode-exact *nirt-first*)
             (fn-record-parse-ok
              (fn-cfg-record-make 0 0 1 *fn-cfg-default-change* *fn-cfg-default-stamp*) nil))
      (not (equal (fn-cfg-decode-exact *nirt-changed*)
                  (fn-record-parse-ok *nirt-later-record* nil)))
      (not (equal (fn-nir-resume-decision '(:sealed) '(:sealed) *nirt-first* *nirt-changed* nil)
                  '(:accepted :resume)))))

; Absence is legal as the not-yet-published generation-one record.
(assert-event (equal (fn-nir-resume-decision '(:sealed) '(:sealed) *nirt-first* nil nil)
                     '(:accepted :resume)))
(assert-event (equal (fn-nir-resume-decision '(:requested) '(:recorded) *nirt-first* *nirt-first* nil)
                     '(:refused :profile-mismatch)))
(assert-event (equal (fn-nir-resume-decision '(:sealed) '(:sealed) *nirt-first* '(0) nil)
                     '(:fault :recorded-initial-record-invalid)))
(assert-event (equal (fn-nir-resume-decision '(:sealed) '(:sealed) *nirt-first* *nirt-changed* nil)
                     '(:refused :initial-groups-mismatch)))
(assert-event (equal (fn-nir-resume-decision '(:sealed) '(:sealed) *nirt-first* nil '("00000002.cfg"))
                     '(:fault :missing-initial-record)))
(assert-event (eq (symbol-class 'fn-nir-resume-decision (w state)) :common-lisp-compliant))
(assert-event (eq (symbol-class 'fn-nir-initial-recordp (w state)) :common-lisp-compliant))
(assert-event (eq (symbol-class 'fn-nir-resume-line (w state)) :common-lisp-compliant))

; Distinct-change keystone: full premises and conclusion.
(assert-event
 (and (equal (fn-cfg-decode-exact *nirt-first*)
             (fn-record-parse-ok *fn-cfg-default-record* nil))
      (equal (fn-cfg-decode-exact *nirt-changed*)
             (fn-record-parse-ok *nirt-changed-record* nil))
      (not (equal *fn-cfg-default-change* (fn-cfg-record-change *nirt-changed-record*)))
      (equal (fn-nir-resume-decision '(:sealed) '(:sealed) *nirt-first* *nirt-changed* nil)
             '(:refused :initial-groups-mismatch))))
; Requested decode omitted, every retained premise holds; corrupted request.
(assert-event
 (and (not (equal (fn-cfg-decode-exact '(0))
                  (fn-record-parse-ok *fn-cfg-default-record* nil)))
      (equal (fn-cfg-decode-exact *nirt-changed*)
             (fn-record-parse-ok *nirt-changed-record* nil))
      (not (equal *fn-cfg-default-change* (fn-cfg-record-change *nirt-changed-record*)))
      (not (equal (fn-nir-resume-decision '(:sealed) '(:sealed) '(0) *nirt-changed* nil)
                  '(:refused :initial-groups-mismatch)))))
; Recorded decode omitted, every retained premise holds; corrupted record.
(assert-event
 (and (equal (fn-cfg-decode-exact *nirt-first*)
             (fn-record-parse-ok *fn-cfg-default-record* nil))
      (not (equal (fn-cfg-decode-exact '(0))
                  (fn-record-parse-ok *nirt-changed-record* nil)))
      (not (equal *fn-cfg-default-change* (fn-cfg-record-change *nirt-changed-record*)))
      (not (equal (fn-nir-resume-decision '(:sealed) '(:sealed) *nirt-first* '(0) nil)
                  '(:refused :initial-groups-mismatch)))))
; Distinctness omitted, every retained decode premise holds: resume accepted.
(assert-event
 (and (equal (fn-cfg-decode-exact *nirt-first*)
             (fn-record-parse-ok *fn-cfg-default-record* nil))
      (equal (fn-cfg-decode-exact *nirt-later*)
             (fn-record-parse-ok *nirt-later-record* nil))
      (not (not (equal *fn-cfg-default-change* (fn-cfg-record-change *nirt-later-record*))))
      (not (equal (fn-nir-resume-decision '(:sealed) '(:sealed) *nirt-first* *nirt-later* nil)
                  '(:refused :initial-groups-mismatch)))))
