(in-package "ACL2")
(include-book "../../books/tcpcl-spool")
(include-book "std/testing/must-fail" :dir :system)

(defconst *t-tcl-stage*
  '(46 105 110 99 111 109 105 110 103 45
    49 50 51 45
    48 49 50 51 52 53 54 55 56 57 97 98
    99 100 101 102 48 49 50 51 52 53 54 55))
(defconst *t-tcl-final* '(112 97 115 115 105 118 101 45 48 46 98 117 110 100 108 101))

(assert-event (fn-tcl-spool-stage-namep *t-tcl-stage*))
(assert-event (equal (fn-tcl-spool-entry-action *t-tcl-stage* :regular) :remove))
(assert-event (equal (fn-tcl-spool-entry-action *t-tcl-stage* :other) :fault))
(assert-event (equal (fn-tcl-spool-entry-action *t-tcl-final* :regular) :keep))

; The crash is after data staging and before publication/ack release.  Recovery
; removes only the hidden record and retains an authoritative completed file.
(defconst *t-tcl-cut*
  (fn-tcl-spool-crash-before-publish
   (fn-tcl-spool-stage-data
    (cons *t-tcl-stage* :regular)
    (fn-tcl-spool-state (list (cons *t-tcl-final* :regular)) nil :ready))))
(defconst *t-tcl-recovered* (fn-tcl-spool-recover *t-tcl-cut*))
(assert-event (equal (fn-tcl-spool-status *t-tcl-recovered*) :ready))
(assert-event (not (fn-tcl-spool-ackp *t-tcl-recovered*)))
(assert-event (equal (fn-tcl-spool-entries *t-tcl-recovered*)
                     (list (cons *t-tcl-final* :regular))))

; Dropping the regular-file hypothesis changes the conclusion and preserves
; the unexplained entry, rather than following or deleting it.
(must-fail
 (defthm fn-tcl-spool-recovery-removes-a-nonregular-stage
   (implies (fn-tcl-spool-stage-namep stage)
            (equal (fn-tcl-spool-status
                    (fn-tcl-spool-recover
                     (fn-tcl-spool-state
                      (list (cons stage :other)) nil :recovery)))
                   :ready))))
(assert-event
 (equal (fn-tcl-spool-entries
         (fn-tcl-spool-recover
          (fn-tcl-spool-state
           (list (cons *t-tcl-stage* :other)) nil :recovery)))
        (list (cons *t-tcl-stage* :other))))

; Malformed use of the reserved prefix is a fault, while an unrelated hidden
; name is outside this recovery namespace and is retained.
(assert-event
 (equal (fn-tcl-spool-entry-action
         '(46 105 110 99 111 109 105 110 103 45 98 97 100) :regular)
        :fault))
(assert-event
 (equal (fn-tcl-spool-entry-action '(46 107 101 101 112) :regular) :keep))
