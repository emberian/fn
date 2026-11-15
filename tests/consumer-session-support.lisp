; Shared real control-session producer; no assertions or seeded publications.
(in-package "ACL2")
(include-book "../books/cns")
(include-book "../books/owed-conn")
(include-book "../books/owed-cursor")
(include-book "../books/assembly-attach")
(include-book "fnct-client")
(include-book "std/util/bstar" :dir :system)

; The posting profile (owed-cursor.lisp's, local.test is group 1, T 2) with
; two control connections: one consumer request (fn2-txn's share 1), and two
; consumer requests with T 3 (fn2-txn's share 1 again). Two consumer requests
; under T 2 leave fn2-txn no row: posting is not served and an append is
; refused with D's word refused (fn2-ccu-unposting-answered), where it used to park
; on a transaction row that never exists, its request never answered.
(defconst *fn2-ccu-profile*
  (put-assoc-equal :cns 1
    (put-assoc-equal :control-connections 2
      (put-assoc-equal :extent-slots 128 *fn2-cursor-profile*))))
(defconst *fn2-ccu-profile-2*
  (put-assoc-equal :cns 2 (put-assoc-equal :t 3 *fn2-ccu-profile*)))
(defconst *fn2-ccu-profile-2-unposting*
  (put-assoc-equal :cns 2 *fn2-ccu-profile*))

(defun fn2-ccu-cat (frames)
  (declare (xargs :verify-guards nil))
  (if (atom frames) nil (append (car frames) (fn2-ccu-cat (cdr frames)))))
(defun fn2-ccu-lens (frames)
  (declare (xargs :verify-guards nil))
  (if (atom frames) nil (cons (len (car frames)) (fn2-ccu-lens (cdr frames)))))
(defun fn2-ccu-client (frames)
  (declare (xargs :verify-guards nil))
  (list (fn2-ccu-cat frames) (fn2-ccu-lens frames) nil nil))

; A control connection admitted at capability CAP, then FRAMES on it, each
; its own receive, the last a stop: (mv status wire fn2-core). The clients
; before CAP are done (no input).
(defun fn2-ccu-done-clients (n)
  (declare (xargs :verify-guards nil))
  (if (zp n) nil (cons (list nil nil nil nil) (fn2-ccu-done-clients (- n 1)))))
(defun fn2-ccu-session-store (cap frames store fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((fn2-core (fn2-listener-take-credit *fn2-ctl-admission-ordinal* fn2-core))
       ((mv acode fn2-core) (fn2-machine-admit-fn2-ctl cap (+ 77 cap) 3 0 fn2-core))
       ((unless (eq acode :ok)) (mv (list :admit acode) nil nil fn2-core))
       ((mv wake fn2-core) (fn2-machine-take-wake fn2-core))
       (fn2-core (fn2-exec-wake wake fn2-core))
       (clients (append (fn2-ccu-done-clients cap) (list (fn2-ccu-client frames))))
       ((mv status clients store fn2-core) (fn2-cw-loop 40000 0 (+ 1 cap) clients store fn2-core)))
    (mv status (car (nth cap (fn2-cw-results clients))) store fn2-core)))

; Existing callers start a new empty adapter device. Recovery/FETCH callers
; must retain the actual device returned by the producer/recovery loop.
(defun fn2-ccu-session (cap frames fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (fn2-ccu-session-store cap frames nil fn2-core))
