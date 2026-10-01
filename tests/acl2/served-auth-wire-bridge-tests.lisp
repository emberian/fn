; Literal PRF-1123 framing and held-pipeline witnesses.
(in-package "ACL2")
(include-book "../../books/served-auth-wire-bridge")
(include-book "accounts-wire-tests")

(bpr-lift fn-served-step 2)
(defconst *sawt-conn*
 (fn-served-result-conn
  (fn-served-open *awt-archive* 510 65536 *awt-config* *awt-obs* *awt-obs*
                  *awt-protected*)))
(defconst *sawt-tls-conn* (update-nth 1 *awt-prot-tls* *sawt-conn*))
(defconst *sawt-381-conn*
 (fn-served-result-conn
  (in-arena-fn-served-step nil *sawt-tls-conn*
   (append (awt-line *awt-redeem*) '(13 10)))))
(defconst *sawt-line* (awt-line *awt-redeem*))
(defconst *sawt-pass* (append (awt-line *awt-pass*) '(13 10)))
(defconst *sawt-suffix* (append (awt-line "DATE") '(13 10)))
(defconst *sawt-closed*
 (update-nth 1
  (fn-auth-with-base *awt-prot*
   (fn-peer-with-base (fn-auth-session-base *awt-prot*)
    (fn-post-make-session
     (update-nth 0 nil (fn-post-session-base
                        (fn-peer-session-base (fn-auth-session-base *awt-prot*))))
     nil)))
  *sawt-conn*))
(defconst *sawt-repin*
 (update-nth 11
  (fn-served-live-make 1 nil (fn-initial-state '("fn.other")) nil nil nil nil)
  (update-nth 1 *awt-open-s* *sawt-conn*)))
(assert-event (and (fn-served-connp *sawt-conn*)
                   (fn-auth-sessionp (fn-served-conn-session *sawt-381-conn*))
                   (fn-auth-redeem-statep
                    (fn-auth-session-pending (fn-served-conn-session *sawt-381-conn*)))))

; Full literal framing antecedent and full-result equality.
(defthm
  sawt-command-wire-positive
  (let*
    ((c
       (fn-served-conn-with-wire
         *sawt-conn*
         (fn-wire-make-state :command nil 0 nil nil 0 510 65536)))
     (r (fn-served-dispatch-core c (list :command *sawt-line*) nil)))
    (and
      (and
        (fn-wire-statep (fn-served-conn-wire c))
        (fn-wire-line-contentp *sawt-line*)
        (<= (len *sawt-line*) 510)
        (not (fn-served-haltedp *sawt-conn*))
        (not (fn-served-advance-eventp (list :command *sawt-line*))))
      (equal (fn-served-step c (append *sawt-line* (quote (13 10))) nil) r)))
  :rule-classes
  nil)

; Corrupted-state removal: wire-state. Every other hypothesis holds.
(defthm
  sawt-command-wire-without-wire-state
  (let*
    ((c
       (fn-served-conn-with-wire
         *sawt-conn*
         (fn-wire-make-state :command nil 0 nil nil 0 510 -1)))
     (r (fn-served-dispatch-core c (list :command *sawt-line*) nil)))
    (and
      (fn-wire-line-contentp *sawt-line*)
      (<= (len *sawt-line*) 510)
      (not (fn-served-haltedp *sawt-conn*))
      (not (fn-served-advance-eventp (list :command *sawt-line*)))
      (not (fn-wire-statep (fn-served-conn-wire c)))
      (not (equal (fn-served-step c (append *sawt-line* (quote (13 10))) nil) r))))
  :rule-classes
  nil)

; Session/input removal: plain-line. Every other hypothesis holds.
(defthm
  sawt-command-wire-without-plain-line
  (let*
    ((c
       (fn-served-conn-with-wire
         *sawt-conn*
         (fn-wire-make-state :command nil 0 nil nil 0 510 65536)))
     (r
       (fn-served-dispatch-core
         c
         (list :command (append *sawt-line* (quote (13 10)) (awt-line "DATE")))
         nil)))
    (and
      (fn-wire-statep (fn-served-conn-wire c))
      (<= (len (append *sawt-line* (quote (13 10)) (awt-line "DATE"))) 510)
      (not (fn-served-haltedp *sawt-conn*))
      (not
        (fn-served-advance-eventp
          (list :command (append *sawt-line* (quote (13 10)) (awt-line "DATE")))))
      (not (fn-wire-line-contentp (append *sawt-line* (quote (13 10)) (awt-line "DATE"))))
      (not
        (equal
          (fn-served-step
            c
            (append (append *sawt-line* (quote (13 10)) (awt-line "DATE")) (quote (13 10)))
            nil)
          r))))
  :rule-classes
  nil)

; Session/input removal: line-limit. Every other hypothesis holds.
(defthm
  sawt-command-wire-without-line-limit
  (let*
    ((c
       (fn-served-conn-with-wire
         *sawt-conn*
         (fn-wire-make-state :command nil 0 nil nil 0 1 65536)))
     (r (fn-served-dispatch-core c (list :command *sawt-line*) nil)))
    (and
      (fn-wire-statep (fn-served-conn-wire c))
      (fn-wire-line-contentp *sawt-line*)
      (not (fn-served-haltedp *sawt-conn*))
      (not (fn-served-advance-eventp (list :command *sawt-line*)))
      (not (<= (len *sawt-line*) 1))
      (not (equal (fn-served-step c (append *sawt-line* (quote (13 10))) nil) r))))
  :rule-classes
  nil)

; Session/input removal: halted. Every other hypothesis holds.
(defthm
  sawt-command-wire-without-halted
  (let*
    ((c
       (fn-served-conn-with-wire
         *sawt-closed*
         (fn-wire-make-state :command nil 0 nil nil 0 510 65536)))
     (r (fn-served-dispatch-core c (list :command *sawt-line*) nil)))
    (and
      (fn-wire-statep (fn-served-conn-wire c))
      (fn-wire-line-contentp *sawt-line*)
      (<= (len *sawt-line*) 510)
      (not (fn-served-advance-eventp (list :command *sawt-line*)))
      (not (not (fn-served-haltedp *sawt-closed*)))
      (not (equal (fn-served-step c (append *sawt-line* (quote (13 10))) nil) r))))
  :rule-classes
  nil)

; Session/input removal: advance-event. Every other hypothesis holds.
(defthm
  sawt-command-wire-without-advance-event
  (let*
    ((c
       (fn-served-conn-with-wire
         *sawt-repin*
         (fn-wire-make-state :command nil 0 nil nil 0 510 65536)))
     (r (fn-served-dispatch-core c (list :command (awt-line "GROUP fn.letters")) nil)))
    (and
      (fn-wire-statep (fn-served-conn-wire c))
      (fn-wire-line-contentp (awt-line "GROUP fn.letters"))
      (<= (len (awt-line "GROUP fn.letters")) 510)
      (not (fn-served-haltedp *sawt-repin*))
      (not (not (fn-served-advance-eventp (list :command (awt-line "GROUP fn.letters")))))
      (not
        (equal (fn-served-step c (append (awt-line "GROUP fn.letters") (quote (13 10))) nil) r))))
  :rule-classes
  nil)

; Actual served redemption prefix enters the owner hold. Complete literal antecedent/conclusion.
(defthm
  sawt-held-prefix-positive
  (and
    (fn-served-tls-handshakingp
      (fn-served-result-conn (fn-served-step *sawt-381-conn* *sawt-pass* nil)))
    (equal
      (fn-served-step *sawt-381-conn* (append *sawt-pass* *sawt-suffix*) nil)
      (fn-served-step *sawt-381-conn* *sawt-pass* nil)))
  :rule-classes
  nil)

; Without the hold, DATE after the 381 prefix is actually processed.
(defthm
  sawt-without-held-prefix
  (and
    (not
      (fn-served-tls-handshakingp
        (fn-served-result-conn
          (fn-served-step *sawt-tls-conn* (append (awt-line *awt-redeem*) (quote (13 10))) nil))))
    (not
      (equal
        (fn-served-step
          *sawt-tls-conn*
          (append (append (awt-line *awt-redeem*) (quote (13 10))) *sawt-suffix*)
          nil)
        (fn-served-step *sawt-tls-conn* (append (awt-line *awt-redeem*) (quote (13 10))) nil))))
  :rule-classes
  nil)
