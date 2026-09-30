; INTERNAL OUTGOING evaluator. The registered current source/pool caller must
; establish the exact fixed scalar coordinate arguments. Native code never
; supplies INSTALLATION, association, source revision, or tariffs.
(in-package "ACL2")
(include-book "connection-operation-cost")
; Installation12: own tag, shared serial, association6, qualified source
; revision scalar, immediate domain, grant5, BODY base/per-window/per-level,
; maximum window quantum, installed storage capacity, operation kind.
; There is no authoritative constructor/installer in this book.
(defun fn-outgoing-operation-evaluate
 (installation operation window capacity depth serial association source-revision)
 (declare (xargs :guard t))
 (let ((domain (fn-omk-at 4 installation))
       (quantum (fn-omk-at 9 installation)))
  (cond
   ((not (and (fn-omk-widthp installation 12)
               (eq (fn-omk-at 0 installation) :outgoing-operation-installation)
               (member-eq operation '(:window :observe :return))
               (eq operation (fn-omk-at 11 installation))
               (natp serial) (eql serial (fn-omk-at 1 installation))
               (fn-omk-widthp association 6)
               (equal association (fn-omk-at 2 installation))
               (natp source-revision)
               (eql source-revision (fn-omk-at 3 installation))
               (natp domain) (natp quantum) (<= quantum domain)
               (natp capacity) (<= capacity domain)
               (eql capacity (fn-omk-at 10 installation))
               (natp depth) (< depth domain)
               (fn-prs-vectorp (fn-omk-at 5 installation))))
    (mv :outgoing-source-unavailable nil 0 0 0))
   ((not (and (natp window) (<= window quantum) (<= window capacity)))
    (mv :refused nil 0 0 quantum))
   (t
    (let ((levels (+ 1 depth)))
     (if (not (fn-cop-times-roomp 8 levels domain))
         (mv :outgoing-source-unavailable nil 0 0 quantum)
      (mv-let (word body)
       (fn-cop-body-demand (fn-omk-at 6 installation)
                          (fn-omk-at 7 installation) window
                          (fn-omk-at 8 installation) levels domain)
       (if (eq word :derived)
           (mv :derived (fn-omk-at 5 installation) (* 8 levels) body quantum)
        (mv :outgoing-source-unavailable nil 0 0 quantum)))))))))

; Fixed scalar coordinate fence BEFORE any association equality. Six cons
; cells alone do not bound recursive EQUAL or immediate arithmetic.
; Actual producer must separately establish source/pool authority.
(defun fn-outgoing-current-evaluate
 (installation operation window capacity depth serial association source-revision)
 (declare (xargs :guard t))
 (let ((domain (fn-omk-at 4 installation)))
  (if (not (and (natp domain)
                (natp serial) (< serial domain)
                (natp source-revision) (<= source-revision domain)
                (fn-cop-vector-room '(0 0 0 0 0 0) association
                                    '(0 0 0 0 0 0) domain 6)
                (fn-cop-vector-room '(0 0 0 0 0 0) (fn-omk-at 2 installation)
                                    '(0 0 0 0 0 0) domain 6)
                (fn-cop-vector-room '(0 0 0 0 0) (fn-omk-at 5 installation)
                                    '(0 0 0 0 0) domain 5)))
      (mv :outgoing-source-unavailable nil 0 0 0)
   (fn-outgoing-operation-evaluate installation operation window capacity
                                  depth serial association source-revision))))
