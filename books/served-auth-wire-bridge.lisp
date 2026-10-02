; PKT-390 / PRF-1123: command framing bridges actual served reads to auth dispatch.

(in-package "ACL2")

(include-book "served")

(local
  (defun
    fn-saw-command-induction
    (xs rev n)
    (declare (xargs :measure (acl2-count xs) :guard (acl2-numberp n)))
    (if (consp xs) (fn-saw-command-induction (cdr xs) (cons (car xs) rev) (+ 1 n)) (list rev n))))

(local (verify-guards fn-saw-command-induction))

(local
  (defthm
    fn-saw-with-wire-overwrite-by-definition
    (equal
      (fn-served-conn-with-wire (fn-served-conn-with-wire conn w1) w2)
      (fn-served-conn-with-wire conn w2))
    :hints
    (("Goal" :in-theory (enable fn-served-conn-with-wire)))))

(local
  (defthm
    fn-saw-served-feed-reconstructs
    (equal
      (fn-served-make-result
        (fn-served-result-conn (fn-served-feed conn xs fn-arena))
        (fn-served-result-effects (fn-served-feed conn xs fn-arena)))
      (fn-served-feed conn xs fn-arena))
    :hints
    (("Goal"
       :expand
       ((fn-served-feed conn xs fn-arena))
       :in-theory
       (disable fn-served-feed-byte fn-served-feed)))))

(local
  (defthm
    fn-saw-command-content-feed-is-silent
    (implies
      (and
        (fn-wire-line-contentp xs)
        (natp n)
        (natp line-limit)
        (<= (+ n (len xs)) line-limit)
        (not (fn-served-haltedp conn)))
      (equal
        (fn-served-feed
          (fn-served-conn-with-wire
            conn
            (fn-wire-make-state :command rev n nil nil 0 line-limit body-limit))
          xs
          fn-arena)
        (fn-served-make-result
          (fn-served-conn-with-wire
            conn
            (fn-wire-make-state
              :command
              (fn-ag-rev-onto xs rev)
              (+ n (len xs))
              nil
              nil
              0
              line-limit
              body-limit))
          nil)))
    :hints
    (("Goal"
       :induct
       (fn-saw-command-induction xs rev n)
       :expand
       ((fn-served-feed
          (fn-served-conn-with-wire
            conn
            (fn-wire-make-state :command rev n nil nil 0 line-limit body-limit))
          xs
          fn-arena))
       :in-theory
       (e/d
         (fn-served-feed
           fn-served-feed-byte
           fn-served-dispatch-events
           fn-wire-feed-byte
           fn-wire-take-octet
           fn-wire-line-contentp
           fn-served-closed-wirep
           fn-ag-rev-onto)
         (fn-served-conn-with-wire
           fn-served-haltedp
           fn-served-dispatch
           fn-wire-close
           fn-wire-statep
           fn-wire-octetp
           fn-wire-after-line
           fn-wire-make-state
           fn-wire-make-result
           fn-served-make-result
           fn-served-make-conn-live))))))

(local
  (defthm
    fn-saw-served-dispatch-reconstructs
    (equal
      (fn-served-make-result
        (fn-served-result-conn (fn-served-dispatch conn event fn-arena))
        (fn-served-result-effects (fn-served-dispatch conn event fn-arena)))
      (fn-served-dispatch conn event fn-arena))
    :hints
    (("Goal"
       :in-theory
       (e/d
         (fn-served-dispatch fn-served-dispatch-core)
         (fn-auth-step-pinned
           fn-served-advance-eventp
           fn-served-selectedp
           fn-served-repin
           fn-post-offeredp
           fn-served-make-result
           fn-served-make-conn-live
           fn-post-result-effects
           fn-post-result-session
           fn-post-result-submission
           fn-wire-begin-article-with-line-limit))))))

(local
  (defthm
    fn-saw-command-crlf-dispatches-the-held-line-by-definition
    (let*
      ((clear (fn-wire-make-state :command nil 0 nil nil 0 line-limit body-limit))
       (p
         (fn-served-dispatch
           (fn-served-conn-with-wire conn clear)
           (list :command (fn-wire-reverse-octets rev))
           fn-arena)))
      (implies
        (and (not (fn-served-haltedp conn)) (true-listp (fn-served-result-effects p)))
        (equal
          (fn-served-feed
            (fn-served-conn-with-wire
              conn
              (fn-wire-make-state :command rev n nil nil 0 line-limit body-limit))
            (quote (13 10))
            fn-arena)
          p)))
    :hints
    (("Goal"
       :expand
       ((:free (c) (fn-served-feed c (quote (13 10)) fn-arena))
        (:free (c) (fn-served-feed c (quote (10)) fn-arena))
        (:free (c) (fn-served-feed c nil fn-arena)))
       :in-theory
       (e/d
         (fn-served-feed-byte
           fn-wire-feed-byte
           fn-wire-after-line
           fn-served-dispatch-events
           fn-served-closed-wirep
           fn-wire-command-event)
         (fn-served-conn-with-wire
           fn-served-haltedp
           fn-served-dispatch
           fn-wire-reverse-octets
           fn-wire-close
           fn-wire-make-state
           fn-wire-make-result
           fn-served-make-result
           fn-served-feed))))))

(local
  (defthm
    fn-saw-rev-onto-is-revappend
    (equal (fn-ag-rev-onto xs acc) (revappend xs acc))
    :hints
    (("Goal" :induct (fn-ag-rev-onto xs acc) :in-theory (enable fn-ag-rev-onto revappend)))))

(local
  (defthm
    fn-saw-command-line-feed-reaches-its-dispatch
    (let*
      ((clear (fn-wire-make-state :command nil 0 nil nil 0 line-limit body-limit))
       (c (fn-served-conn-with-wire conn clear))
       (p (fn-served-dispatch c (list :command line) fn-arena)))
      (implies
        (and
          (fn-wire-line-contentp line)
          (natp line-limit)
          (<= (len line) line-limit)
          (not (fn-served-haltedp conn))
          (true-listp (fn-served-result-effects p)))
        (equal (fn-served-feed c (append line (quote (13 10))) fn-arena) p)))
    :rule-classes
    nil
    :hints
    (("Goal"
       :use
       ((:instance
          fn-served-feed-of-append
          (conn
            (fn-served-conn-with-wire
              conn
              (fn-wire-make-state :command nil 0 nil nil 0 line-limit body-limit)))
          (left line)
          (right (quote (13 10))))
        (:instance fn-saw-command-content-feed-is-silent (xs line) (rev nil) (n 0))
        (:instance
          fn-saw-command-crlf-dispatches-the-held-line-by-definition
          (rev (fn-ag-rev-onto line nil))
          (n (len line))))
       :in-theory
       (e/d
         (fn-saw-rev-onto-is-revappend)
         (fn-served-feed
           fn-served-dispatch
           fn-served-conn-with-wire
           fn-served-haltedp
           fn-wire-line-contentp
           fn-saw-command-content-feed-is-silent
           fn-saw-command-crlf-dispatches-the-held-line-by-definition
           fn-wire-make-state
           fn-served-make-result))))))

(local
  (defthm
    fn-saw-append-nil
    (equal (append xs nil) (true-list-fix xs))
    :hints
    (("Goal" :in-theory (enable binary-append true-list-fix)))))

(local
  (defthm
    fn-saw-true-list-fix-identity
    (implies (true-listp xs) (equal (true-list-fix xs) xs))
    :hints
    (("Goal" :induct (true-list-fix xs) :in-theory (enable true-list-fix)))))

(local
  (defthm
    fn-saw-command-wire-limit-is-natural
    (implies
      (fn-wire-statep (fn-wire-make-state :command nil 0 nil nil 0 line-limit body-limit))
      (natp line-limit))
    :hints
    (("Goal" :in-theory (enable fn-wire-statep)))))

(local
 (defthm fn-saw-dispatch-effects-are-a-true-list
  (true-listp (fn-served-result-effects (fn-served-dispatch conn event fn-arena)))
  :hints (("Goal" :in-theory
   (e/d (fn-served-dispatch fn-served-dispatch-core)
        (fn-auth-step-pinned fn-served-repin fn-served-selectedp fn-post-result-effects
         fn-post-result-submission fn-post-result-session fn-wire-begin-article-with-line-limit))))))

(local
 (defthm fn-saw-command-dispatch-core-keeps-wire-open
  (let ((c (fn-served-conn-with-wire conn
             (fn-wire-make-state :command nil 0 nil nil 0 line-limit body-limit))))
   (not (fn-served-closed-wirep
          (fn-served-conn-wire
           (fn-served-result-conn (fn-served-dispatch-core c event fn-arena))))))
  :hints (("Goal" :in-theory
   (e/d (fn-served-dispatch-core fn-served-closed-wirep
         fn-wire-begin-article-with-line-limit)
        (fn-auth-step-pinned fn-post-result-effects fn-post-result-submission
         fn-post-result-session fn-post-offeredp fn-wire-begin-article-admissiblep
         fn-wire-article-line-limit))))))

; A complete-result refinement: auth dispatch still owns its effects, submissions
; and phase changes. This bridge supplies the actual host's byte framing.
(defthm fn-saw-command-wire-is-auth-dispatch
 (let* ((c (fn-served-conn-with-wire conn
             (fn-wire-make-state :command nil 0 nil nil 0 line-limit body-limit)))
        (r (fn-served-dispatch-core c (list :command line) fn-arena)))
  (implies
   (and (fn-wire-statep (fn-served-conn-wire c))
        (fn-wire-line-contentp line)
        (<= (len line) line-limit)
        (not (fn-served-haltedp conn))
        (not (fn-served-advance-eventp (list :command line))))
   (equal (fn-served-step c (append line '(13 10)) fn-arena) r)))
 :rule-classes nil
 :hints (("Goal"
  :use (fn-saw-command-line-feed-reaches-its-dispatch
        (:instance fn-saw-dispatch-effects-are-a-true-list
         (conn (fn-served-conn-with-wire conn
                 (fn-wire-make-state :command nil 0 nil nil 0 line-limit body-limit)))
         (event (list :command line)))
        (:instance fn-saw-command-dispatch-core-keeps-wire-open
         (event (list :command line)))
        (:instance fn-saw-served-dispatch-reconstructs
         (conn (fn-served-conn-with-wire conn
                 (fn-wire-make-state :command nil 0 nil nil 0 line-limit body-limit)))
         (event (list :command line)))
        fn-saw-command-wire-limit-is-natural)
  :in-theory
  (union-theories
   '(fn-served-step fn-served-closed-wirep fn-served-dispatch-without-advance-is-core
     fn-served-conn-fields-of-with-wire fn-wire-state-mode-of-fn-wire-make-state
     fn-served-result-effects-of-fn-served-make-result
     fn-served-result-conn-of-fn-served-make-result
     fn-saw-append-nil fn-saw-true-list-fix-identity)
   (theory 'minimal-theory)))))

(local
 (defthm fn-saw-feed-effects-are-a-true-list
  (true-listp (fn-served-result-effects (fn-served-feed conn octets fn-arena)))
  :hints (("Goal" :induct (fn-served-feed conn octets fn-arena)
   :in-theory (e/d (fn-served-feed) (fn-served-feed-byte fn-served-haltedp fn-served-closed-wirep))))))

; An owner-held redemption / TLS prefix answers no pipelined suffix. The
; hypothesis names the actual prefix result, not an invented model phase.
(defthm fn-saw-held-read-prefix-stops-the-pipeline
 (implies
  (fn-served-tls-handshakingp
   (fn-served-result-conn (fn-served-step conn prefix fn-arena)))
  (equal (fn-served-step conn (append prefix suffix) fn-arena)
         (fn-served-step conn prefix fn-arena)))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-served-feed-of-append (left prefix) (right suffix)))
  :in-theory (e/d (fn-served-step)
                   (fn-served-feed fn-served-feed-of-append fn-wire-statep
                    fn-served-closed-wirep fn-served-tls-handshakingp)))))
