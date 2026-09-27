; fn: one-pass configured-owner receive with physical prefix ownership.
;
; The native host calls fn-ocfg-read-tls-prefix once per observed socket
; region.  It lifts fn-served-step-counted through the same fn-own-finish-read
; bookkeeping as fn-own-read, so framing, dispatch and owner mutation execute
; once while the host also receives the exact physical prefix count.

(in-package "ACL2")
(include-book "owner-config")
(include-book "served-tls-prefix")

; (:fn-own-tls-result consumed effects configured-owner repinned): REPINNED
; is whether the read moved the connection's pin (NNT-042; fn-own-result-repinned).
(defun fn-own-tls-make-result (consumed effects owner repinned)
  (declare (xargs :guard t))
  (list :fn-own-tls-result consumed effects owner repinned))

(defun fn-own-tls-result-repinned (result)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr result))))))

(defun fn-own-tls-result-consumed (result)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr result)))

(defun fn-own-tls-result-effects (result)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr result))))

(defun fn-own-tls-result-owner (result)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr result)))))

(defun fn-own-tls-served-conn (o conn)
  (declare (xargs :guard t))
  (fn-own-served-conn o conn (fn-own-conn-live-session o conn)))

(defthm fn-own-tls-served-conn-keeps-reader-pins
  (and (equal (fn-served-conn-verdicts (fn-own-tls-served-conn o conn))
              (fn-own-conn-verdicts conn))
       (equal (fn-served-conn-index (fn-own-tls-served-conn o conn))
              (fn-own-conn-index conn)))
  :hints (("Goal" :in-theory (enable fn-own-tls-served-conn fn-own-served-conn))))

(defun fn-own-read-tls-prefix (o id octets fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (let ((conn (fn-own-find-conn id (fn-own-conns o))))
    (if conn
        (let* ((counted
                 (fn-served-step-counted-fast
                  (fn-own-tls-served-conn o conn) octets fn-arena))
               (result
                 (fn-own-finish-read
                  o conn (fn-served-counted-result counted))))
          (fn-own-tls-make-result
           (fn-served-counted-consumed counted) (car result) (cdr result)
           (fn-own-result-repinned (fn-served-counted-result counted))))
      (fn-own-tls-make-result (len octets) nil o nil))))

(defun fn-ocfg-read-tls-prefix (oc id octets fn-arena)
  (declare (xargs :stobjs fn-arena :guard (fn-wire-octet-listp octets)))
  (let ((result (fn-own-read-tls-prefix (fn-ocfg-owner oc) id octets fn-arena)))
    (fn-own-tls-make-result
     (fn-own-tls-result-consumed result)
     (fn-own-tls-result-effects result)
     (fn-ocfg-with-read-owner oc id (fn-own-tls-result-owner result)
                              (fn-own-tls-result-repinned result))
     (fn-own-tls-result-repinned result))))

(defthm fn-own-read-tls-prefix-consumed-is-bounded
  (<= (fn-own-tls-result-consumed
       (fn-own-read-tls-prefix o id octets fn-arena))
      (len octets))
  :rule-classes :linear
  :hints (("Goal"
           :in-theory (enable fn-own-read-tls-prefix
                              fn-own-tls-make-result
                              fn-own-tls-result-consumed)
           :use ((:instance fn-served-step-counted-fast-consumed-is-bounded
                            (conn
                             (fn-own-tls-served-conn
                              o (fn-own-find-conn id (fn-own-conns o)))))))))

; The actual host-call transition returns exactly fn-ocfg-read's effects and
; configured-owner state over the octets it consumed.  The counted transition
; is a single execution; this theorem relates its result to the pre-existing
; semantic entry point.  Since PKT-600 (PRF-213) the read also yields after an
; octet that completed a submission, so what it consumed is a prefix of the
; region; the host feeds the rest as the next read (host/native/owner.lisp,
; the serve loop's retained offset).  Before, it was
; `fn-ocfg-read-tls-prefix-is-full-read' over the whole region, and every
; submission after the first one in a region was lost.
; The wire hypothesis is the domain `fn-served-step-counted-fast-is-reference'
; (books/served-tls-prefix).  Carrying it through the historical configured-owner
; relation remains a separate proof obligation; the static `fn-ocfg-statep'
; is not a valid premise after a live domain or capacity change.
(defthm fn-ocfg-read-tls-prefix-is-read-of-consumed-prefix
  (implies
   (fn-wire-statep
    (fn-own-conn-wire
     (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc)))))
   (let* ((tls-result (fn-ocfg-read-tls-prefix oc id octets fn-arena))
          (full-result
           (fn-ocfg-read oc id (take (fn-own-tls-result-consumed tls-result)
                                     octets) fn-arena)))
     (and (equal (fn-own-tls-result-effects tls-result)
                 (car full-result))
          (equal (fn-own-tls-result-owner tls-result)
                 (cdr full-result))
          ; NNT-042: and the same answer to "did the pin move", over the
          ; same consumed prefix
          (equal (fn-own-tls-result-repinned tls-result)
                 (fn-own-read-repinned (fn-ocfg-owner oc) id
                                       (take (fn-own-tls-result-consumed tls-result)
                                             octets) fn-arena)))))
  :hints (("Goal"
           ; both sides finish the same served result; nothing past it opens
           :in-theory (e/d (fn-ocfg-read-tls-prefix fn-own-read-repinned
                            fn-own-read-tls-prefix
                            fn-own-tls-make-result
                            fn-own-tls-result-consumed
                            fn-own-tls-result-effects
                            fn-own-tls-result-owner
                            fn-own-tls-result-repinned
                            fn-ocfg-read
                            fn-own-read fn-own-read-full
                            fn-own-tls-served-conn)
                           (fn-own-finish-read fn-ocfg-with-read-owner
                            fn-own-result-repinned))
           :use ((:instance fn-served-step-counted-fast-is-reference
                            (conn
                             (fn-own-tls-served-conn
                              (fn-ocfg-owner oc)
                              (fn-own-find-conn
                               id (fn-own-conns (fn-ocfg-owner oc))))))
                 (:instance fn-served-step-counted-result-is-step-of-consumed-prefix
                            (conn
                             (fn-own-tls-served-conn
                              (fn-ocfg-owner oc)
                              (fn-own-find-conn
                               id (fn-own-conns (fn-ocfg-owner oc))))))))))

; KEYSTONE (PRF-213): the read the host calls on every socket region hands
; the owner at most one submission, so the one fn-own-finish-read enqueues
; (fn-served-submission, the first) is all of it; the rest of a pipelined
; region is the next read's.  The hypothesis is the served invariant of the
; connection the read runs on, the premise fn-oag-served-post-names-the-
; pinned-agent (books/owner-agent.lisp) states the same way.
(defthm fn-ocfg-read-tls-prefix-carries-at-most-one-submission
  (let ((conn (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc)))))
    (implies (fn-served-connp (fn-own-tls-served-conn (fn-ocfg-owner oc) conn))
             (<= (len (fn-served-submissions
                       (fn-own-tls-result-effects
                        (fn-ocfg-read-tls-prefix oc id octets fn-arena))))
                 1)))
  :rule-classes :linear
  :hints (("Goal"
           :in-theory (e/d (fn-ocfg-read-tls-prefix
                            fn-own-read-tls-prefix
                            fn-own-tls-make-result
                            fn-own-tls-result-effects
                            fn-own-finish-read)
                           (fn-served-step-counted-fast fn-served-step-counted
                            fn-served-connp fn-own-tls-served-conn
                            fn-served-step-counted-carries-at-most-one-submission))
           :use ((:instance fn-served-connp-is-wire-state
                            (c (fn-own-tls-served-conn
                                (fn-ocfg-owner oc)
                                (fn-own-find-conn
                                 id (fn-own-conns (fn-ocfg-owner oc))))))
                 (:instance fn-served-step-counted-fast-is-reference
                            (conn
                             (fn-own-tls-served-conn
                              (fn-ocfg-owner oc)
                              (fn-own-find-conn
                               id (fn-own-conns (fn-ocfg-owner oc))))))
                 (:instance fn-served-step-counted-carries-at-most-one-submission
                            (conn
                             (fn-own-tls-served-conn
                              (fn-ocfg-owner oc)
                              (fn-own-find-conn
                               id (fn-own-conns (fn-ocfg-owner oc))))))))))

(in-theory (disable fn-own-tls-make-result
                    fn-own-tls-result-consumed
                    fn-own-tls-result-effects
                    fn-own-tls-result-owner
                    fn-own-tls-result-repinned
                    fn-own-tls-served-conn
                    fn-own-read-tls-prefix
                    fn-ocfg-read-tls-prefix))
