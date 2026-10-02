(defmacro fnn-with-roster ((service) &body body)
  `(sb-thread:with-mutex ((fnn-owner-service-roster ,service)) ,@body))

(defun fnn-owner-stop-service-locked (service exit-code &optional answering)
  "Fence while the owner mutex is held; the first terminal outcome wins.

ANSWERING is the socket of the connection whose own ACL2 reply reported the
stop, or nil.  It is not shut down here: its worker still owes that reply (the
uncertain `441 ... do not repost'), sends it after the mutex is released and
then closes the connection itself.  Setting STOPPING under this mutex is the
fence; no semantic action of any worker, that one included, can run after it
(fnn-owner-serialized refuses once STOPPING is set).

ANSWERING is also remembered in SPARING (PKT-562): a later stop -- the run's
cleanup stop, which passes no ANSWERING -- spares it too, so it cannot shut
the socket while that worker is still writing its reply."
  (let ((first-stop nil))
    ;; Install the irreversible service fence before any fallible core drain.
    ;; Lifecycle failure retains debt; it cannot reopen semantic admission.
    (fnn-with-roster (service)
      (unless (fnn-owner-service-stopping service)
        (setf (fnn-owner-service-stopping service) t
              (fnn-owner-service-exit-code service) exit-code
              first-stop t)))
    (unwind-protect
        (when first-stop (fnn-payload-lifecycle-drain service))
      ;; Signal cleanup even when lifecycle drain raises or escapes.
  (let ((sparing (sb-thread:with-mutex ((fnn-owner-service-commit-lock service))
                   (when answering
                     (pushnew answering (fnn-owner-service-sparing service)))
                   (copy-list (fnn-owner-service-sparing service)))))
  (let ((listener (fnn-owner-service-listener service)))
    (when listener
      ;; close(2) in another thread does not reliably wake a blocked accept(2)
      ;; on Linux.  Shutdown first so the accept loop observes a socket error,
      ;; sees STOPPING while this mutex is still held, and returns.
      (ignore-errors
        (sb-bsd-sockets:socket-shutdown listener :direction :io))))
  ;; Wake every client before command cleanup waits for its worker.  Shared
  ;; journals and Store state remain open until all workers have returned.
  ;; Only the worker that cached the socket fd may close it; shutdown wakes its
  ;; raw read without making that integer available for reuse underneath it.
  (dolist (socket (fnn-with-roster (service)
                    (copy-list (fnn-owner-service-clients service))))
    (unless (member socket sparing)
      (ignore-errors
        (sb-bsd-sockets:socket-shutdown socket :direction :io)))))
  ;; The committer thread wakes, finds the owner stopping and returns.
  (sb-thread:with-mutex ((fnn-owner-service-commit-lock service))
    (sb-thread:condition-broadcast (fnn-owner-service-commit-ready service)))
  ;; PRF-252: a sleeping consumer wait wakes, finds the owner stopping and
  ;; is answered (its next step is refused by fnn-owner-serialized).
  (fnn-owner-signal-commit service)
  ;; Hooks only signal external listeners/clients.  They run inside the same
  ;; first-terminal boundary and must be idempotent and nonblocking.
  (dolist (hook (fnn-owner-service-stop-hooks service))
    (ignore-errors (funcall hook service))))))
