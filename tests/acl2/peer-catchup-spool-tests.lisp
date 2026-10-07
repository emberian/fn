(in-package "ACL2")
(include-book "../../books/peer-catchup-spool")
(include-book "../../books/peer-catchup-spool-body")
(include-book "../../books/defkeystone")

(defun csp-test-state (limit window)
  ; The state fn-csp-begin returns, its session replaced by the ready one the
  ; auth exchange would have produced (that exchange is the session's, not the
  ; controller's).
  (let* ((cursor (fn-cu-fresh-cursor (fn-record-string-octets "remote")))
         (round (fn-cu-begin cursor (fn-record-string-octets "fn.test")))
         (session (fn-cu-session (fn-fc-make-state (fn-fwi-initial-state) nil :ready 0 :clear)
                                round nil :clear)))
    (fn-csp-with (car (fn-csp-begin nil cursor nil limit window)) :session session)))

(defun csp-test-wire (body lines claim)
  (append (fn-cu-initial-line 1 1 claim) '(13 10)
            (fn-cu-record-header "<a@x>" lines) '(13 10) body '(46 13 10)))

(defun csp-test-drive (s effects wire disk local journals fuel stop)
  ; Test-only materialized witness. Actual consumer never retains these lists.
  (declare (xargs :mode :program))
  (cond
   ((zp fuel) (list :exhausted s local journals disk))
   ; STOP a mode keyword: return the state the first time it is in that mode
   ; (:offer: as its IHAVE leaves), its effects drained and (for the replay
   ; modes) a window pending.
   ((and (keywordp stop) (eq (fn-csp-mode s) stop)
         (or (eq stop :offer) (not (consp effects)))
         (or (not (member-eq stop '(:replay-header :replay-body)))
             (consp (fn-csp-pending s))))
    (list :at s))
   ; STOP: return the state just before the first settling reply is owed.
   ((and stop (consp effects) (eq (car (car effects)) :local)
         (let ((c (fn-csp-conn (cadr (car effects)) s)))
           (and (consp c) (eq (cdr c) :verdict))))
    (list :verdict-owed s (cadr (car effects))))
   ((consp effects)
    (let* ((effect (car effects)) (kind (car effect))
           (disk (if (eq kind :spool-write)
                     (append (take (cadr effect) disk) (caddr effect)) disk))
           (local (if (eq kind :local) (append local (cddr effect)) local))
           (journals (if (eq kind :journal) (cons (cdr effect) journals) journals))
           (event
            (case kind
              (:spool-write (list :spool-written :ok (len (caddr effect))))
              (:spool-hash (list :digest (fn-blake3-stobj (take (caddr effect) (nthcdr (cadr effect) disk)))))
              (:spool-read (list :spool-read :ok (caddr effect) (take (caddr effect) (nthcdr (cadr effect) disk))))
              (:open-local (list* :local (cadr effect) '(50 48 48 32 111 107 13 10)))
              (:local (let ((c (fn-csp-conn (cadr effect) s)))
                        (cond ((and (consp c) (eq (cdr c) :await335))
                               (list* :local (cadr effect) '(51 51 53 32 111 107 13 10)))
                              ((and (consp c) (eq (cdr c) :streaming))
                               (list :local-window (cadr effect)))
                              ((and (consp c) (eq (cdr c) :verdict))
                               (list* :local (cadr effect) '(50 51 53 32 111 107 13 10)))
                              (t '(:lost)))))
              (otherwise nil))))
      (if event
          (let ((pair (fn-csp-step s event)))
            (csp-test-drive (car pair) (append (cdr effects) (cadr pair)) wire disk local journals (1- fuel) stop))
        (csp-test-drive s (cdr effects) wire disk local journals (1- fuel) stop))))
   ((member-eq (fn-csp-mode s) '(:done :failed))
    (list (fn-csp-mode s) s local journals disk))
   ((fn-csp-tick-p s)
    (let ((pair (fn-csp-step s '(:tick))))
      (csp-test-drive (car pair) (cadr pair) wire disk local journals (1- fuel) stop)))
   ((consp wire)
    (let* ((n (min 512 (len wire)))
           (pair (fn-csp-step s (cons :remote (take n wire)))))
      (csp-test-drive (car pair) (cadr pair) (nthcdr n wire) disk local journals (1- fuel) stop)))
   (t (list :stuck s local journals disk))))

(defconst *csp-test-article* '(46 120 13 10 13 10))
(defconst *csp-test-chain*
  (fn-cu-chain-step *fn-cu-zero-chain* (fn-record-string-octets "<a@x>") *csp-test-article*))
(defconst *csp-test-result*
  (csp-test-drive (csp-test-state 4096 2) nil
                 (csp-test-wire '(46 46 120 13 10 13 10) 2 *csp-test-chain*) nil nil nil 200 nil))
(assert-event (eq (car *csp-test-result*) :done))
(assert-event
 (equal (nth 2 *csp-test-result*)
        (append (fn-pull-command (list (fn-record-string-octets "IHAVE") (fn-record-string-octets "<a@x>")))
                '(46 46 120 13 10 13 10 46 13 10))))
(assert-event (equal (len (nth 3 *csp-test-result*)) 1))
(assert-event
 (equal (fn-cu-cursor-position (car (nth 3 *csp-test-result*))) 1))
(assert-event
 (equal (fn-cu-cursor-chain (car (nth 3 *csp-test-result*))) *csp-test-chain*))
(assert-event
 (let ((r (csp-test-drive (csp-test-state 4096 2) nil
                         (csp-test-wire '(120 120 13 10 13 10) 2 *csp-test-chain*) nil nil nil 200 nil)))
   (and (eq (car r) :failed) (not (nth 2 r)) (not (nth 3 r))
        (equal (fn-cu-r-refusal (fn-cu-s-round (fn-csp-session (cadr r)))) :digest-mismatch))))
(assert-event
 (let ((r (csp-test-drive (csp-test-state 1 2) nil
                         (csp-test-wire '(46 46 120 13 10 13 10) 2 *csp-test-chain*) nil nil nil 200 nil)))
   (and (eq (car r) :failed) (not (nth 2 r)) (not (nth 3 r))
        (equal (fn-cu-r-refusal (fn-cu-s-round (fn-csp-session (cadr r)))) :spool-quota))))
(assert-event
 (let* ((article (append (make-list 1025 :initial-element 120) '(13 10)))
        (claim (fn-cu-chain-step *fn-cu-zero-chain* (fn-record-string-octets "<a@x>") article))
        (r (csp-test-drive (csp-test-state 4096 2) nil (csp-test-wire article 1 claim) nil nil nil 200 nil)))
   (and (eq (car r) :done) (equal (len (nth 3 r)) 1)
        (equal (nth 2 r)
               (append (fn-pull-command (list (fn-record-string-octets "IHAVE") (fn-record-string-octets "<a@x>")))
                       article '(46 13 10))))))

; Teeth: fn-csp-step-keeps-window. Positive: a full 512-octet peer window is
; admitted into a windowed state and the result is windowed with that window.
(assert-event
 (let* ((s (csp-test-state 4096 2))
        (bytes (make-list 512 :initial-element 120))
        (s2 (car (fn-csp-step s (cons :remote bytes)))))
   (and (fn-csp-windowp s) (fn-csp-windowp s2)
        (equal (fn-csp-pending s2) bytes))))
; A 513-octet window is not retained: the round fails by name.
(assert-event
 (let* ((s2 (car (fn-csp-step (csp-test-state 4096 2)
                              (cons :remote (make-list 513 :initial-element 120))))))
   (and (fn-csp-windowp s2) (eq (fn-csp-mode s2) :failed)
        (equal (fn-cu-r-refusal (fn-cu-s-round (fn-csp-session s2))) :malformed))))
; Hypothesis removal: from a state already holding 600 pending octets, a step
; can leave it unwindowed, so the hypothesis is not redundant.
(assert-event
 (let* ((s (fn-csp-with (csp-test-state 4096 2) :mode :write :count 0
                       :resume :body :pending (make-list 600 :initial-element 120)))
        (s2 (car (fn-csp-step s '(:spool-written :ok 0)))))
   (and (not (fn-csp-windowp s)) (not (fn-csp-windowp s2)))))
; Teeth: fn-csp-write-spools-whole-or-fails-by-name, the whole-write disjunct.
(assert-event
 (let* ((s (csp-test-state 4096 2))
        (r (fn-csp-write s '(1 2 3) :body)))
   (and (equal (cadr r) '((:spool-write 0 (1 2 3))))
        (equal (fn-csp-offset (car r)) 3) (equal (fn-csp-count (car r)) 3)
        (eq (fn-csp-mode (car r)) :write) (eq (fn-csp-resume (car r)) :body))))
; ... and the named-refusal disjunct: one octet over the funded limit.
(assert-event
 (let* ((s (fn-csp-with (csp-test-state 4 2) :offset 2))
        (r (fn-csp-write s '(1 2 3) :body)))
   (and (eq (fn-csp-mode (car r)) :failed) (equal (cadr r) '((:close)))
        (equal (fn-cu-r-refusal (fn-cu-s-round (fn-csp-session (car r)))) :spool-quota))))

; The keystones' declared teeth (TEETH CONTRACT v1), from the witnesses above.
(defconst *csp-teeth-s* (csp-test-state 4096 2))
(defconst *csp-teeth-window* (cons :remote (make-list 512 :initial-element 120)))
(defconst *csp-teeth-wide*
  (fn-csp-with (csp-test-state 4096 2) :mode :write :count 0
               :resume :body :pending (make-list 600 :initial-element 120)))
(defconst *csp-teeth-over* (fn-csp-with (csp-test-state 4 2) :offset 2))

(defteeth fn-csp-step-keeps-window
  :claim (((windowed (fn-csp-windowp s)))
          (fn-csp-windowp (car (fn-csp-step s event))))
  :subject fn-csp-step
  :witness ((s *csp-teeth-s*) (event *csp-teeth-window*))
  :breaks ((windowed ((s *csp-teeth-wide*) (event '(:spool-written :ok 0)))))
  :mutations ((short-window
               (:conclusion (< (len (fn-csp-pending (car (fn-csp-step s event)))) 512))
               ((s *csp-teeth-s*) (event *csp-teeth-window*))
               :fault "a window bound one octet below the 512-octet quantum the host reads")))

(defteeth fn-csp-write-spools-whole-or-fails-by-name
  :claim (()
          (let* ((r (fn-csp-write s emission resume))
                 (s2 (car r)) (effects (cadr r))
                 (bytes (fn-pull-list emission)))
            (or (and (equal (fn-csp-mode s2) :failed)
                     (equal (fn-cu-r-refusal (fn-cu-s-round (fn-csp-session s2))) :spool-quota)
                     (equal effects '((:close))))
                (and (atom bytes) (equal effects nil)
                     (equal (fn-csp-offset s2) (fn-csp-offset s)))
                (and (equal effects (list (list :spool-write (fn-csp-offset s) bytes)))
                     (equal (fn-csp-offset s2) (+ (fn-csp-offset s) (len bytes)))
                     (<= (fn-csp-offset s2) (fn-csp-limit s))
                     (equal (fn-csp-count s2) (len bytes))
                     (equal (fn-csp-mode s2) :write)
                     (equal (fn-csp-resume s2) resume)))))
  :subject fn-csp-write
  :witness ((s *csp-teeth-s*) (emission '(1 2 3)) (resume :body))
  :breaks ()
  :mutations ((never-refused
               (:conclusion
                (let* ((r (fn-csp-write s emission resume))
                       (s2 (car r)) (effects (cadr r))
                       (bytes (fn-pull-list emission)))
                  (or (and (atom bytes) (equal effects nil)
                           (equal (fn-csp-offset s2) (fn-csp-offset s)))
                      (and (equal effects (list (list :spool-write (fn-csp-offset s) bytes)))
                           (equal (fn-csp-offset s2) (+ (fn-csp-offset s) (len bytes)))
                           (<= (fn-csp-offset s2) (fn-csp-limit s))
                           (equal (fn-csp-count s2) (len bytes))
                           (equal (fn-csp-mode s2) :write)
                           (equal (fn-csp-resume s2) resume)))))
               ((s *csp-teeth-over*) (emission '(1 2 3)) (resume :body))
               :fault "an emission over the funded spool limit that is spooled (or cut) instead of failing the round by name")
              (offset-kept
               (:conclusion
                (let* ((r (fn-csp-write s emission resume))
                       (s2 (car r)) (effects (cadr r))
                       (bytes (fn-pull-list emission)))
                  (or (and (equal (fn-csp-mode s2) :failed)
                           (equal (fn-cu-r-refusal (fn-cu-s-round (fn-csp-session s2))) :spool-quota)
                           (equal effects '((:close))))
                      (and (atom bytes) (equal effects nil)
                           (equal (fn-csp-offset s2) (fn-csp-offset s)))
                      (and (equal effects (list (list :spool-write (fn-csp-offset s) bytes)))
                           (equal (fn-csp-offset s2) (fn-csp-offset s))
                           (<= (fn-csp-offset s2) (fn-csp-limit s))
                           (equal (fn-csp-count s2) (len bytes))
                           (equal (fn-csp-mode s2) :write)
                           (equal (fn-csp-resume s2) resume)))))
               ((s *csp-teeth-s*) (emission '(1 2 3)) (resume :body))
               :fault "a spool write that leaves the offset in place, so the next emission overwrites it")))


; Teeth: the verdict keystones.  The witness is a REACHABLE state: the
; controller begun by fn-csp-begin, driven through the open greeting, the
; IHAVE, the 335, the body and the terminator of one record, stopped where the
; terminator's settling reply is owed (conn j holds (msgid . :verdict), the
; batch drained, no other binding).
(defconst *csp-v-run*
  (csp-test-drive (csp-test-state 4096 2) nil
                  (csp-test-wire '(46 46 120 13 10 13 10) 2 *csp-test-chain*)
                  nil nil nil 200 t))
(assert-event (eq (car *csp-v-run*) :verdict-owed))
(defconst *csp-v-s* (cadr *csp-v-run*))
(defconst *csp-v-j* (caddr *csp-v-run*))
(defconst *csp-v-msgid* (car (fn-csp-conn *csp-v-j* *csp-v-s*)))
(defconst *csp-v-235* '(50 51 53 32 111 107 13 10))
(defconst *csp-v-437* '(52 51 55 32 120 13 10))
(defconst *csp-v-436* '(52 51 54 32 120 13 10))

(defun csp-test-with-phase (s phase)
  ; The same round under a session still in PHASE (not :ready).
  (fn-csp-with s :session (fn-cu-session (fn-fc-make-state (fn-fwi-initial-state) nil phase 0 :clear)
                                         (fn-cu-s-round (fn-csp-session s)) nil :clear)))

(defteeth fn-csp-step-settles-one-verdict-exactly-once
  :claim (((ready (fn-cu-session-readyp (fn-csp-session s)))
           (octets (fn-pull-octetsp octets))
           (live (not (member-eq (fn-csp-mode s) '(:failed :done))))
           (bound (equal (fn-csp-conn j s) (cons msgid :verdict))))
          (let* ((pair (fn-csp-step s (list* :local j octets)))
                 (s2 (car pair))
                 (r (fn-cu-s-round (fn-csp-session s)))
                 (r2 (fn-cu-s-round (fn-csp-session s2))))
            (if (member-equal (fn-pull-local-code octets) '(235 437))
                (and (equal (fn-cu-r-counts r2)
                            (fn-cu-count (fn-cu-r-counts r)
                                         (if (equal (fn-pull-local-code octets) 235) 0 2)))
                     (equal (fn-csp-conns s2)
                            (fn-csp-conns-set (fn-csp-conns s) j :free))
                     (implies (not (and (eq (fn-csp-mode s) :drain)
                                        (fn-csp-conns-idlep-but (fn-csp-conns s) (nfix j))))
                              (and (equal (fn-cu-r-position r2) (fn-cu-r-position r))
                                   (equal (fn-csp-replay s2) (fn-csp-replay s))
                                   (equal (fn-csp-offset s2) (fn-csp-offset s))
                                   (equal (fn-csp-mode s2) (fn-csp-mode s))
                                   (equal (cadr pair) nil))))
              (and (equal (fn-cu-r-counts r2) (fn-cu-r-counts r))
                   (equal (fn-csp-mode s2) :failed)
                   (equal (fn-cu-r-refusal r2)
                          (if (equal (fn-pull-local-code octets) 436)
                              :local-deferred :local-refused))))))
  :subject fn-csp-step
  :witness ((s *csp-v-s*) (j *csp-v-j*) (octets *csp-v-235*) (msgid *csp-v-msgid*))
  :breaks ((ready ((s (csp-test-with-phase *csp-v-s* :tls))))
           (octets ((octets '(50 51 53 32 111 107 13 10 a))))
           (live ((s (fn-csp-with *csp-v-s* :mode :failed))))
           (bound ((s (fn-csp-with *csp-v-s* :conns
                                   (fn-csp-conns-set (fn-csp-conns *csp-v-s*) *csp-v-j* :free))))))
  :mutations ((wrong-class
               (:conclusion
                (let* ((pair (fn-csp-step s (list* :local j octets)))
                       (r (fn-cu-s-round (fn-csp-session s)))
                       (r2 (fn-cu-s-round (fn-csp-session (car pair)))))
                  (equal (fn-cu-r-counts r2) (fn-cu-count (fn-cu-r-counts r) 1))))
               ((s *csp-v-s*) (j *csp-v-j*) (octets *csp-v-235*) (msgid *csp-v-msgid*))
               :fault "a settling 235 that moves the duplicate class's count, so a record is counted under the wrong verdict")
              (failed-round-settles
               (:hypothesis live (not (eq (fn-csp-mode s) :done)))
               ((s (fn-csp-with *csp-v-s* :mode :failed)) (j *csp-v-j*)
                (octets *csp-v-235*) (msgid *csp-v-msgid*))
               :fault "a reply after the round failed that is still allowed to settle a record")))

(defteeth fn-csp-step-final-verdict-journals
  :claim (((ready (fn-cu-session-readyp (fn-csp-session s)))
           (octets (fn-pull-octetsp octets))
           (bound (equal (fn-csp-conn j s) (cons msgid :verdict)))
           (code (member-equal (fn-pull-local-code octets) '(235 437)))
           (drained (eq (fn-csp-mode s) :drain))
           (last (fn-csp-conns-idlep-but (fn-csp-conns s) (nfix j))))
          (let* ((pair (fn-csp-step s (list* :local j octets)))
                 (s2 (car pair))
                 (effs (cadr pair))
                 (r (fn-cu-s-round (fn-csp-session s)))
                 (r2 (fn-cu-s-round (fn-csp-session s2))))
            (and (consp effs)
                 (eq (car (car effs)) :journal)
                 (equal (cdr (car effs)) (fn-cu-round-cursor r2))
                 (not (member-eq :journal (strip-cars (cdr effs))))
                 (not (member-eq :local (strip-cars effs)))
                 (equal (fn-cu-r-counts r2)
                        (fn-cu-count (fn-cu-r-counts r)
                                     (if (equal (fn-pull-local-code octets) 235)
                                         0 2)))
                 (equal (fn-csp-conns s2)
                        (fn-csp-conns-set (fn-csp-conns s) j :free)))))
  :subject fn-csp-step
  :witness ((s *csp-v-s*) (j *csp-v-j*) (octets *csp-v-235*) (msgid *csp-v-msgid*))
  :breaks ((ready ((s (csp-test-with-phase *csp-v-s* :tls))))
           (octets ((octets '(50 51 53 32 111 107 13 10 a))))
           (bound ((s (fn-csp-with *csp-v-s* :conns
                                   (fn-csp-conns-set (fn-csp-conns *csp-v-s*) *csp-v-j* :free)))))
           (code ((octets *csp-v-436*)))
           (drained ((s (fn-csp-with *csp-v-s* :mode :header))))
           (last ((s (fn-csp-with *csp-v-s* :conns
                                  (fn-csp-conns-set (fn-csp-conns *csp-v-s*) 1
                                                    (cons *csp-v-msgid* :verdict)))))))
  :mutations ((journal-lost
               (:conclusion
                (let* ((pair (fn-csp-step s (list* :local j octets))))
                  (null (cadr pair))))
               ((s *csp-v-s*) (j *csp-v-j*) (octets *csp-v-235*) (msgid *csp-v-msgid*))
               :fault "the last verdict of a drained batch settles its record but the batch's cursor is never journaled")
              (journals-undrained
               (:hypothesis drained (member-eq (fn-csp-mode s) '(:drain :header)))
               ((s (fn-csp-with *csp-v-s* :mode :header)) (j *csp-v-j*)
                (octets *csp-v-235*) (msgid *csp-v-msgid*))
               :fault "a verdict that is treated as closing the batch while the spool cursor is still reading records")))

; Teeth: fn-csp-window-bounds-in-flight.  The witness is the reachable
; verdict-owed state of a two-connection window with one record in flight; a
; tick leaves it, so the bound is attained (one binding of W = 2).
(defteeth fn-csp-window-bounds-in-flight
  :claim (((window (equal (fn-csp-window s) w))
           (table (equal (len (fn-csp-conns s)) w))
           (slot (< (nfix (fn-csp-slot s)) w)))
          (let ((s2 (car (fn-csp-step s event))))
            (and (equal (fn-csp-window s2) w)
                 (equal (len (fn-csp-conns s2)) w)
                 (< (nfix (fn-csp-slot s2)) w)
                 (<= (fn-csp-conns-bound (fn-csp-conns s2)) w))))
  :subject fn-csp-step
  :witness ((s *csp-v-s*) (w 2) (event '(:tick)))
  :breaks ((window ((s (fn-csp-with *csp-v-s* :window 3))))
           (table ((s (fn-csp-with *csp-v-s* :conns (list :free :free :free)))))
           (slot ((s (fn-csp-with *csp-v-s* :mode :terminator :slot 5)))))
  :mutations ((nothing-in-flight
               (:conclusion
                (let ((s2 (car (fn-csp-step s event))))
                  (<= (fn-csp-conns-bound (fn-csp-conns s2)) 0)))
               ((s *csp-v-s*) (w 2) (event '(:tick)))
               :fault "a bound that admits no record in flight, so the window would not carry the pipelined offers it exists for")))

; Teeth: the body keystones (K1).  The witnesses are REACHABLE states, the
; controller begun by fn-csp-begin and driven with the drive above: stopped
; with a body window pending in the replay (conn 0 holds (msgid . :streaming),
; the window leaves as a :local effect on the next tick), and stopped as the
; IHAVE leaves (conn 0 holds (msgid . :await335); the local node's 335
; reply is what makes it stream).
(defconst *csp-k1-wire* (csp-test-wire '(46 46 120 13 10 13 10) 2 *csp-test-chain*))
(defconst *csp-k1-body*
  (cadr (csp-test-drive (csp-test-state 4096 2) nil *csp-k1-wire* nil nil nil 200 :replay-body)))
(defconst *csp-k1-term*
  (cadr (csp-test-drive (csp-test-state 4096 2) nil *csp-k1-wire* nil nil nil 200 :terminator)))
(defconst *csp-k1-offer*
  (cadr (csp-test-drive (csp-test-state 4096 2) nil *csp-k1-wire* nil nil nil 200 :offer)))
(defconst *csp-k1-body-octets*
  (cddr (car (cadr (fn-csp-step *csp-k1-body* '(:tick))))))
(defconst *csp-k1-335* '(51 51 53 32 111 107 13 10))
(defconst *csp-k1-msgid* (car (fn-csp-conn 0 *csp-k1-offer*)))
(assert-event (and (fn-csp-body-inv *csp-k1-body*) (fn-csp-body-inv *csp-k1-term*)
                   (fn-csp-body-inv *csp-k1-offer*)
                   (eq (fn-csp-mode *csp-k1-body*) :replay-body)
                   (eq (fn-csp-mode *csp-k1-term*) :terminator)
                   (eq (fn-csp-mode *csp-k1-offer*) :offer)))
; The terminator is a :local effect on the streaming slot, too.
(assert-event
 (equal (car (cadr (fn-csp-step *csp-k1-term* '(:tick))))
        (list* :local 0 '(46 13 10))))

(defteeth fn-csp-body-only-after-its-335
  :claim (((inv (fn-csp-body-inv s))
           (eff (member-equal (cons :local (cons j octets))
                              (cadr (fn-csp-step s event)))))
          (let ((s2 (car (fn-csp-step s event))))
            (or (and (natp j)
                     (equal (fn-csp-conn j s) :free)
                     (equal (fn-csp-mode s2) :offer)
                     (equal (fn-csp-slot s2) j)
                     (equal (fn-csp-conn j s2) (cons (fn-csp-msgid s2) :await335))
                     (equal octets (fn-cu-ihave (cons (fn-csp-msgid s2) nil))))
                (and (natp j)
                     (member-eq (fn-csp-mode s) '(:replay-body :terminator))
                     (equal (fn-csp-slot s) j)
                     (equal (fn-csp-conn j s) (cons (fn-csp-msgid s) :streaming))))))
  :subject fn-csp-step
  :witness ((s *csp-k1-body*) (event '(:tick)) (j 0) (octets *csp-k1-body-octets*))
  :breaks ((inv ((s (fn-csp-with *csp-k1-body* :conns (list :free :unopened)))))
           (eff ((j 1))))
  :mutations ((body-before-the-335
               (:conclusion
                (equal (fn-csp-conn j s) (cons (fn-csp-msgid s) :await335)))
               ((s *csp-k1-body*) (event '(:tick)) (j 0) (octets *csp-k1-body-octets*))
               :fault "a body window written on the connection whose IHAVE still awaits its 335")))

(defteeth fn-csp-streaming-only-from-335
  :claim (((nat (natp k))
           (post (equal (fn-csp-conn k (car (fn-csp-step s event))) (cons m :streaming))))
          (or (equal (fn-csp-conn k s) (cons m :streaming))
              (and (equal (fn-csp-conn k s) (cons m :await335))
                   (equal (car (fn-pull-list event)) :local)
                   (equal (nfix (nth 1 event)) k)
                   (equal (fn-pull-local-code (fn-csp-local-event-octets event)) 335)
                   (eq (fn-csp-mode s) :offer)
                   (equal (fn-csp-slot s) k))))
  :subject fn-csp-step
  :witness ((s *csp-k1-offer*) (event (list* :local 0 *csp-k1-335*)) (k 0) (m *csp-k1-msgid*))
  :breaks ((nat ((k -1)) :logical "a negative index is outside the guard of fn-csp-conn (natp); read through nfix it names connection 0")
           (post ((event '(:tick)))))
  :mutations ((streaming-is-never-new
               (:conclusion (equal (fn-csp-conn k s) (cons m :streaming)))
               ((s *csp-k1-offer*) (event (list* :local 0 *csp-k1-335*)) (k 0) (m *csp-k1-msgid*))
               :fault "a model in which no reply ever starts a body, so the offer could never proceed")))

; Teeth: fn-csp-journals-only-a-settled-batch.  The witness is the reachable
; verdict-owed state of the verdict teeth above (mode :drain, offset = replay,
; one binding outstanding) and the terminator's settling 235: the step that
; frees the last binding finishes the batch and journals it.
(assert-event (and (fn-csp-drain-inv *csp-v-s*) (eq (fn-csp-mode *csp-v-s*) :drain)
                   (<= (nfix (fn-csp-offset *csp-v-s*)) (nfix (fn-csp-replay *csp-v-s*)))))

(defteeth fn-csp-journals-only-a-settled-batch
  :claim (((inv (fn-csp-drain-inv s))
           (journals (member-eq :journal (strip-cars (cadr (fn-csp-step s event))))))
          (let* ((pair (fn-csp-step s event))
                 (effs (cadr pair))
                 (s2 (car pair)))
            (and (<= (nfix (fn-csp-offset s)) (nfix (fn-csp-replay s)))
                 (consp effs)
                 (eq (car (car effs)) :journal)
                 (equal (cdr (car effs))
                        (fn-cu-round-cursor (fn-cu-s-round (fn-csp-session s2))))
                 (not (member-eq :journal (strip-cars (cdr effs))))
                 (member-eq (fn-csp-mode s2) '(:done :status))
                 (fn-csp-conns-idlep (fn-csp-conns s2)))))
  :subject fn-csp-step
  :witness ((s *csp-v-s*) (event (list* :local *csp-v-j* *csp-v-235*)))
  :breaks ((inv ((s (fn-csp-with *csp-v-s* :offset (+ 1 (fn-csp-replay *csp-v-s*))))))
           (journals ((s (fn-csp-with *csp-v-s* :conns
                                      (fn-csp-conns-set (fn-csp-conns *csp-v-s*) 1
                                                        (cons *csp-v-msgid* :verdict)))))))
  :mutations ((journals-with-a-verdict-outstanding
               (:conclusion
                (not (fn-csp-conns-idlep (fn-csp-conns (car (fn-csp-step s event))))))
               ((s *csp-v-s*) (event (list* :local *csp-v-j* *csp-v-235*)))
               :fault "a controller that journals the batch's cursor while a connection still holds a binding whose verdict is owed")
              (journals-and-keeps-draining
               (:conclusion
                (eq (fn-csp-mode (car (fn-csp-step s event))) :drain))
               ((s *csp-v-s*) (event (list* :local *csp-v-j* *csp-v-235*)))
               :fault "a controller that journals the cursor but stays in :drain, so the batch would be journaled again")))
