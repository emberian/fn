; fn: `peer feed NAME pause|resume' (books/feed-pause.lisp), its test book.
;
; Order: the admin plan the operator's words make, the deltas it publishes
; over a live table, the pause they leave, then the teeth of each keystone.

(in-package "ACL2")
(include-book "../../books/native-admin")

(defun fpt-argv (words)
  (if (consp words)
      (cons (fn-record-string-octets (car words)) (fpt-argv (cdr words)))
    nil))

(defconst *fpt-peers*
  (list (list "relay" "path-identity" "relay.example" 0)
        (list "relay" "outbound-streaming" "" 1)
        (list "other" "path-identity" "other.example" 0)))

(defconst *fpt-v*
  (fn-cfg-value-make nil 0 nil nil nil *fpt-peers* nil nil nil nil))

(defconst *fpt-pause*
  (fn-native-admin-plan (fpt-argv '("peer" "feed" "relay" "pause"))))
(defconst *fpt-resume*
  (fn-native-admin-plan (fpt-argv '("peer" "feed" "relay" "resume"))))

(assert-event (equal (fn-native-admin-result-status *fpt-pause*) :accepted))
(assert-event (equal (fn-native-admin-result-kind *fpt-pause*) :extend-peer))
(assert-event (equal (fn-native-admin-result-status *fpt-resume*) :accepted))
; Any other word, or arity, is refused by name.
(assert-event
 (equal (fn-native-admin-result-reason
         (fn-native-admin-plan (fpt-argv '("peer" "feed" "relay" "stop"))))
        :feed))
(assert-event
 (equal (fn-native-admin-result-status
         (fn-native-admin-plan (fpt-argv '("peer" "feed" "relay"))))
        :refused))

; The first pause adds one row and removes nothing.
(defconst *fpt-pause-deltas*
  (fn-native-admin-plan-deltas-over *fpt-pause* *fpt-peers*))
(assert-event
 (equal *fpt-pause-deltas*
        (list (fn-cfg-add-peer-rows "relay"
                                    (list (list "relay" "outbound-paused" "" 1))))))
(defconst *fpt-paused-v* (fn-cfg-apply *fpt-v* 1 nil *fpt-pause-deltas*))
(assert-event (fn-fps-pausedp "relay" (fn-cfg-peers *fpt-paused-v*)))
(assert-event (not (fn-fps-pausedp "other" (fn-cfg-peers *fpt-paused-v*))))
; The worker's links: the paused feed is not one of them.
(assert-event
 (equal (fn-fps-live-names '("relay" "other") (fn-cfg-peers *fpt-paused-v*))
        '("other")))

; Resume from the paused table: the pause row goes, the resume row comes.
(defconst *fpt-resume-deltas*
  (fn-native-admin-plan-deltas-over *fpt-resume* (fn-cfg-peers *fpt-paused-v*)))
(assert-event
 (equal *fpt-resume-deltas*
        (list (fn-cfg-add-peer-rows "relay"
                                    (list (list "relay" "outbound-paused" "" 0)))
              (fn-cfg-remove-peer-rows "relay"
                                       (list (list "relay" "outbound-paused" "" 1))))))
(defconst *fpt-resumed-v* (fn-cfg-apply *fpt-paused-v* 2 nil *fpt-resume-deltas*))
(assert-event (not (fn-fps-pausedp "relay" (fn-cfg-peers *fpt-resumed-v*))))
(assert-event
 (equal (fn-fps-live-names '("relay" "other") (fn-cfg-peers *fpt-resumed-v*))
        '("relay" "other")))
; The group holds one pause row, never both.
(assert-event
 (equal (len (fn-cfg-rows-with-key (fn-cfg-peers *fpt-resumed-v*) "relay"))
        (+ 1 (len (fn-cfg-rows-with-key *fpt-peers* "relay")))))
; The other rows of the group are untouched.
(assert-event
 (subsetp-equal (fn-cfg-rows-with-key *fpt-peers* "relay")
                (fn-cfg-rows-with-key (fn-cfg-peers *fpt-resumed-v*) "relay")))

; -----------------------------------------------------------------------------
; Teeth: fn-fps-deltas-set-the-pause
;
; (implies (consp (fn-cfg-rows-with-key (fn-cfg-peers v) name))
;          (equal (fn-fps-pausedp name (fn-cfg-peers (fn-cfg-apply v gen stamp
;                    (fn-fps-deltas name pausep (fn-cfg-peers v)))))
;                 (if pausep t nil)))

; Reachable positive witness, both values of PAUSEP (the admin plans above
; are these deltas): the antecedent and the conclusion.
(assert-event
 (and (consp (fn-cfg-rows-with-key (fn-cfg-peers *fpt-v*) "relay"))
      (equal (fn-fps-pausedp
              "relay" (fn-cfg-peers
                       (fn-cfg-apply *fpt-v* 1 nil
                                     (fn-fps-deltas "relay" t (fn-cfg-peers *fpt-v*)))))
             t)
      (equal (fn-fps-pausedp
              "relay" (fn-cfg-peers
                       (fn-cfg-apply *fpt-paused-v* 1 nil
                                     (fn-fps-deltas "relay" nil
                                                    (fn-cfg-peers *fpt-paused-v*)))))
             nil)))

; Hypothesis removal: a peer the table does not hold.  The hypothesis fails,
; and the conclusion fails for a pause (nothing is published, nothing paused).
(assert-event
 (and (not (consp (fn-cfg-rows-with-key (fn-cfg-peers *fpt-v*) "absent")))
      (null (fn-fps-deltas "absent" t (fn-cfg-peers *fpt-v*)))
      (not (equal (fn-fps-pausedp
                   "absent" (fn-cfg-peers
                             (fn-cfg-apply *fpt-v* 1 nil
                                           (fn-fps-deltas "absent" t
                                                          (fn-cfg-peers *fpt-v*)))))
                  t))))

; -----------------------------------------------------------------------------
; Teeth: fn-fps-live-names-are-the-unpaused-feeds (no hypothesis): a member
; of NAMES that is paused is absent; one that is not is present.
(assert-event
 (and (member-equal "relay" '("relay" "other"))
      (fn-fps-pausedp "relay" (fn-cfg-peers *fpt-paused-v*))
      (not (member-equal "relay" (fn-fps-live-names '("relay" "other")
                                                    (fn-cfg-peers *fpt-paused-v*))))
      (member-equal "other" (fn-fps-live-names '("relay" "other")
                                               (fn-cfg-peers *fpt-paused-v*)))))
