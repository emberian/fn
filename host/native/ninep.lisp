;;; Bounded 9P transport adapter. Core owns ranges, fields, lookup and replies.
;;; Internal driver only until the complete installed operation family joins.
;;; No whole-view adapter, Lisp reader, host wire decoder or host qid allocator.
(in-package "ACL2")

(defun fnn-ninep-copy-observed (octets buffer)
  "Move actual received octets into the already funded concrete input."
  (loop for byte across octets
        do (setq buffer (fn-octets-append-octet byte buffer)))
  buffer)

(defun fnn-ninep-drive-internal (fd transport buffer session seconds)
  "Drive the actual core connection cursor on an already issued connection.
Each core step is a distinct bounded allocation operation. The caller must
provide its genuine installed operation admission before invoking this driver;
the public start below is still unavailable. I/O holds response/source custody,
and never an allocating-turn receipt or extent lock, while writes wait."
  (let ((terminal nil))
    (unwind-protect
        (loop
          (multiple-value-bind (action next next-session ignored-state)
              (fn-ninep-transport-step transport buffer session *the-live-state*)
            (declare (ignore ignored-state))
            (setq transport next session next-session)
            ;; These are core instructions, not host decisions about the wire.
            (case (first action)
              (:yield nil)
              (:receive
               (let ((observed (fnn-recv fd seconds (second action))))
                 (when (or (eq observed :timeout) (zerop (length observed)))
                   (setq terminal :disconnected)
                   (return terminal))
                 (setq buffer (fnn-ninep-copy-observed observed buffer))))
              (:send
               ;; Fixed control replies currently; future provider output must
               ;; already be a funded bounded chunk selected by the core.
               (let ((response (fnn-octets (second action))))
                 (fnn-send-all fd response seconds)
                 (setq response nil))
               ;; Full I/O return, after the local response alias is gone.
               ;; A partial/failed send escapes without this source epilogue.
               (multiple-value-bind (word next next-buffer next-session ignored-state)
                   (fn-ninep-transport-reply-returned
                    transport buffer session *the-live-state*)
                 (declare (ignore ignored-state))
                 (unless (eq word :returned)
                   (fnn-fault "9P reply return: ~s" word))
                 (setq transport next buffer next-buffer session next-session)))
              (:close (setq terminal :closed) (return terminal))
              (:provider
               ;; Current mount-specific provider producer remains separate.
               ;; Do not turn a Pub19 shape, pointer or supplied callback into
               ;; directory/article authority here.
               (setq terminal :provider-unavailable)
               (return terminal))
              ((:await-return :await-mount-return)
               ;; Actual worker/query return must advance the retained state.
               ;; Socket completion and NIL aliases cannot settle it.
               (setq terminal :await-custody-return)
               (return terminal))
              (otherwise
               (fnn-fault "9P transport action: ~s" action)))))
      ;; Disconnect only marks actual requests/fids for bounded draining. It
      ;; never clears a mount, refunds its PRS debit or fabricates completion.
      (setq session (fn-9ps-drain-begin session)))
    (values terminal transport buffer session)))

(defun fnn-ninep-start (port pool)
  "Actual common-source preflight before any listener/session constructor.
The current core cannot issue a complete ninep-readonly startup operation.
This is an explicit unavailable public entry, not a positive listener claim."
  (multiple-value-bind (word plan ignored-pool ignored-state)
      (fn-ninep-runtime-start port pool *the-live-state*)
    (declare (ignore ignored-pool ignored-state))
    ;; No source result today denotes a granted listener. Do not accept a
    ;; shaped plan or a non-NIL family as a constructor permission.
    (values word plan)))
