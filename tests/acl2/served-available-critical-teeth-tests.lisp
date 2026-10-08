; Critical restricted-dispatch witnesses.  The archive is produced by three
; acceptance prepare/complete transitions, then a real served open selects it.
(in-package "ACL2")
(include-book "served-available-access-tests")
(include-book "../../books/defkeystone")
(defconst *s11av-archive*
 (fn-accept-complete
  (fn-accept-prepare
   (fn-accept-complete
    (fn-accept-prepare
     (fn-accept-complete
      (fn-accept-prepare (fn-initial-state '("fn.test" "fn.other"))
                         1 "<a@x>" 0 '("fn.test") 5) 0 1 :durable)
     2 "<b@x>" 1 '("fn.test" "fn.other") 5) 1 2 :durable)
   3 "<c@x>" 2 '("fn.test") 5) 2 3 :durable))
(assert-event (and (fn-nntp-projectionp *s11av-archive*)
                   (equal (len (fn-state-articles *s11av-archive*)) 3)))
(defun s11av-open (config)
 (fn-served-result-conn
  (fn-served-pin-group-index
   (fn-served-open *s11av-archive* 510 8192 config *avac-obs* *avac-obs* (fn-auth-open-config))
   (fn-gidx-build (fn-state-articles *s11av-archive*)))))
(defconst *s11av-conn* (s11av-open *avac-config*))
(defconst *s11av-index* (fn-served-conn-pinned-index *s11av-conn*))
(defconst *s11av-cache*
 (fn-gacc-prepare "fn.other" *s11av-archive* (fn-gidx-pin-control *s11av-index*) nil))
(defconst *s11av-forged*
 (list (fn-gacc-entry "fn.other" *s11av-archive* (fn-gidx-pin-control *s11av-index*)
                      (cons *s11av-archive* *s11av-index*))))
(defun s11av-unrestricted ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-arena
  (mv-let (conn fn-arena)
   (let ((fn-arena (fn-arn-seal-many *avac-a* fn-arena)))
    (mv (fn-served-result-conn
         (fn-scar-dispatch-core (s11av-open *avac-config-none*)
          (avac-event "GROUP fn.test") nil nil fn-arena)) fn-arena))
   conn)))
(defun s11av-load-cat (rows fn-cat)
 (declare (xargs :stobjs fn-cat :verify-guards nil))
 (if (consp rows) (let ((fn-cat (fn-cat-commit (car rows) fn-cat))) (s11av-load-cat (cdr rows) fn-cat)) fn-cat))
(defun s11av-dispatch-drop-effects (conn event live lver arts cache fn-arena fn-cat) (declare (xargs :stobjs (fn-arena fn-cat) :guard (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat) :verify-guards nil)) (let* ((v (fn-scr-view-of (fn-served-pinned-version (fn-served-conn-pinned conn)) fn-cat)) (r (fn-av-scr-auth-step (fn-served-conn-session conn) live lver arts cache (fn-served-conn-archive conn) (fn-served-conn-pinned-index conn) (fn-served-conn-verdicts conn) (fn-served-conn-config conn) (fn-served-conn-observation conn) (fn-served-conn-injection conn) event v fn-arena fn-cat)) (effects nil) (submission (fn-post-result-submission r)) (wire (fn-served-conn-wire conn)) (wire2 (if (fn-post-offeredp effects) (fn-wire-result-state (fn-wire-begin-article-with-line-limit wire (fn-wire-article-line-limit wire))) wire))) (fn-served-make-result (fn-served-make-conn-live wire2 (fn-post-result-session r) (fn-served-conn-archive conn) (fn-served-conn-config conn) (fn-served-conn-observation conn) (fn-served-conn-injection conn) (fn-served-conn-verdicts conn) (fn-served-conn-group-index conn) (fn-served-conn-control conn) (fn-served-conn-pinned conn) (fn-served-conn-live conn)) (mbe :logic (append effects (if submission (list (fn-served-submit-effect submission (fn-served-login (fn-served-conn-session conn)) (fn-served-account (fn-served-conn-session conn)))) nil)) :exec (fn-ag-append effects (if submission (list (fn-served-submit-effect submission (fn-served-login (fn-served-conn-session conn)) (fn-served-account (fn-served-conn-session conn)))) nil))))))
(defthm s11av-auth-delegate-positive
 (and (fn-gacc-okp *s11av-cache*) (fn-auth-access-read (fn-served-conn-session *s11av-conn*) *avac-config*) (equal (fn-av-scr-auth-delegate (fn-served-conn-session *s11av-conn*) nil 3 nil *s11av-cache* *s11av-archive* *s11av-index* nil *avac-config* *avac-obs* *avac-obs* (avac-event "STAT <a@x>") 3 *avac-a* *avac-c*) (fn-scar-auth-delegate-pinned (fn-served-conn-session *s11av-conn*) nil nil *s11av-archive* *s11av-index* nil *avac-config* *avac-obs* *avac-obs* (avac-event "STAT <a@x>") *avac-a*)))
 :rule-classes nil)
(defthm s11av-auth-delegate-cache
 (and (fn-auth-access-read (fn-served-conn-session *s11av-conn*) *avac-config*) (not (fn-gacc-okp *s11av-forged*)) (not (equal (fn-av-scr-auth-delegate (fn-served-conn-session *s11av-conn*) nil 3 nil *s11av-forged* *s11av-archive* *s11av-index* nil *avac-config* *avac-obs* *avac-obs* (avac-event "STAT <a@x>") 3 *avac-a* *avac-c*) (fn-scar-auth-delegate-pinned (fn-served-conn-session *s11av-conn*) nil nil *s11av-archive* *s11av-index* nil *avac-config* *avac-obs* *avac-obs* (avac-event "STAT <a@x>") *avac-a*))))
 :rule-classes nil)
(defthm s11av-auth-delegate-rule
 (and (fn-gacc-okp nil) (not (fn-auth-access-read (fn-served-conn-session (s11av-unrestricted)) *avac-config-none*)) (not (equal (fn-av-scr-auth-delegate (fn-served-conn-session (s11av-unrestricted)) nil 3 nil nil *s11av-archive* *s11av-index* nil *avac-config-none* *avac-obs* *avac-obs* (avac-event "OVER 1-3") 3 *avac-a* *avac-c*) (fn-scar-auth-delegate-pinned (fn-served-conn-session (s11av-unrestricted)) nil nil *s11av-archive* *s11av-index* nil *avac-config-none* *avac-obs* *avac-obs* (avac-event "OVER 1-3") *avac-a*))))
 :rule-classes nil)
(defthm s11av-auth-delegate-mutation
 (and (fn-gacc-okp *s11av-cache*) (fn-auth-access-read (fn-served-conn-session *s11av-conn*) *avac-config*) (not (equal (avac-prefix-auth-delegate (fn-served-conn-session *s11av-conn*) nil 3 nil *s11av-cache* *s11av-archive* *s11av-index* nil *avac-config* *avac-obs* *avac-obs* (avac-event "STAT <a@x>") 3 *avac-a* *avac-c*) (fn-scar-auth-delegate-pinned (fn-served-conn-session *s11av-conn*) nil nil *s11av-archive* *s11av-index* nil *avac-config* *avac-obs* *avac-obs* (avac-event "STAT <a@x>") *avac-a*))))
 :rule-classes nil)
(defteeth fn-av-scr-auth-delegate-restricted-is-reference
 :subject fn-av-scr-auth-delegate
 :claim (((cache (fn-gacc-okp cache)) (restricted (fn-auth-access-read as config))) (equal (fn-av-scr-auth-delegate as live lver arts cache archive index verdicts config observation injection wire-event v fn-arena fn-cat) (fn-scar-auth-delegate-pinned as live arts archive index verdicts config observation injection wire-event fn-arena)))
 :witness ((as (fn-served-conn-session *s11av-conn*)) (live nil) (lver 3) (arts nil) (cache *s11av-cache*) (archive *s11av-archive*) (index *s11av-index*) (verdicts nil) (config *avac-config*) (observation *avac-obs*) (injection *avac-obs*) (wire-event (avac-event "STAT <a@x>")) (v 3)  )
 
 :breaks ((cache ((as (fn-served-conn-session *s11av-conn*)) (live nil) (lver 3) (arts nil) (cache *s11av-forged*) (archive *s11av-archive*) (index *s11av-index*) (verdicts nil) (config *avac-config*) (observation *avac-obs*) (injection *avac-obs*) (wire-event (avac-event "STAT <a@x>")) (v 3)  ) )
 (restricted ((as (fn-served-conn-session (s11av-unrestricted))) (live nil) (lver 3) (arts nil) (cache nil) (archive *s11av-archive*) (index *s11av-index*) (verdicts nil) (config *avac-config-none*) (observation *avac-obs*) (injection *avac-obs*) (wire-event (avac-event "OVER 1-3")) (v 3)  ) ))
 :mutations ((access-route-skipped (:conclusion (equal (avac-prefix-auth-delegate as live lver arts cache archive index verdicts config observation injection wire-event v fn-arena fn-cat) (fn-scar-auth-delegate-pinned as live arts archive index verdicts config observation injection wire-event fn-arena))) ()
 :fault "available dispatch bypasses the restricted reference route" ))
 :stobjs ((fn-arena (fn-arn-seal-many *avac-a* fn-arena))
          (fn-cat (s11av-load-cat *avac-c* fn-cat))))
(defthm s11av-dispatch-core-positive
 (and (fn-gacc-okp *s11av-cache*) (fn-auth-access-read (fn-served-conn-session *s11av-conn*) (fn-served-conn-config *s11av-conn*)) (equal (fn-av-scr-dispatch-core *s11av-conn* (avac-event "STAT <a@x>") nil 3 nil *s11av-cache* *avac-a* *avac-c*) (fn-scar-dispatch-core *s11av-conn* (avac-event "STAT <a@x>") nil nil *avac-a*)))
 :rule-classes nil)
(defthm s11av-dispatch-core-cache
 (and (fn-auth-access-read (fn-served-conn-session *s11av-conn*) (fn-served-conn-config *s11av-conn*)) (not (fn-gacc-okp *s11av-forged*)) (not (equal (fn-av-scr-dispatch-core *s11av-conn* (avac-event "STAT <a@x>") nil 3 nil *s11av-forged* *avac-a* *avac-c*) (fn-scar-dispatch-core *s11av-conn* (avac-event "STAT <a@x>") nil nil *avac-a*))))
 :rule-classes nil)
(defthm s11av-dispatch-core-rule
 (and (fn-gacc-okp nil) (not (fn-auth-access-read (fn-served-conn-session (s11av-unrestricted)) (fn-served-conn-config (s11av-unrestricted)))) (not (equal (fn-av-scr-dispatch-core (s11av-unrestricted) (avac-event "OVER 1-3") nil 3 nil nil *avac-a* *avac-c*) (fn-scar-dispatch-core (s11av-unrestricted) (avac-event "OVER 1-3") nil nil *avac-a*))))
 :rule-classes nil)
(defthm s11av-dispatch-core-mutation
 (and (fn-gacc-okp *s11av-cache*) (fn-auth-access-read (fn-served-conn-session *s11av-conn*) (fn-served-conn-config *s11av-conn*)) (not (equal (s11av-dispatch-drop-effects *s11av-conn* (avac-event "STAT <a@x>") nil 3 nil *s11av-cache* *avac-a* *avac-c*) (fn-scar-dispatch-core *s11av-conn* (avac-event "STAT <a@x>") nil nil *avac-a*))))
 :rule-classes nil)
(defteeth fn-av-scr-dispatch-core-restricted-is-reference
 :subject fn-av-scr-dispatch-core
 :claim (((cache (fn-gacc-okp cache)) (restricted (fn-auth-access-read (fn-served-conn-session conn) (fn-served-conn-config conn)))) (equal (fn-av-scr-dispatch-core conn event live lver arts cache fn-arena fn-cat) (fn-scar-dispatch-core conn event live arts fn-arena)))
 :witness ((conn *s11av-conn*) (event (avac-event "STAT <a@x>")) (live nil) (lver 3) (arts nil) (cache *s11av-cache*)  )
 
 :breaks ((cache ((conn *s11av-conn*) (event (avac-event "STAT <a@x>")) (live nil) (lver 3) (arts nil) (cache *s11av-forged*)  ) )
 (restricted ((conn (s11av-unrestricted)) (event (avac-event "OVER 1-3")) (live nil) (lver 3) (arts nil) (cache nil)  ) ))
 :mutations ((reply-dropped (:conclusion (equal (s11av-dispatch-drop-effects conn event live lver arts cache fn-arena fn-cat) (fn-scar-dispatch-core conn event live arts fn-arena))) ()
 :fault "dispatch computes the restricted result but drops its reply effects" ))
 :stobjs ((fn-arena (fn-arn-seal-many *avac-a* fn-arena))
          (fn-cat (s11av-load-cat *avac-c* fn-cat))))
(defteeth-check (fn-av-scr-auth-delegate-restricted-is-reference fn-av-scr-dispatch-core-restricted-is-reference))
