(in-package "ACL2")
(include-book "../../books/peer-flight-startup")
(include-book "../../books/defkeystone")
(include-book "std/testing/assert-bang" :dir :system)
(defconst *pfrst-peer* '(32768 65536 2 1 32768 20))
(defconst *pfrst-core* '(83886080 . 67108864))
(defconst *pfrst-plan*
 (fn-prstartup-default-plan-with-peer 268435456 67108864 nil *pfrst-core* 0 nil nil 0
                                     "/tmp/store" 4 8 256 *pfrst-peer* nil nil))
(assert-event
 (and (fn-prstartup-planp *pfrst-plan*)
      (equal (fn-pfr-at 0 (fn-prstartup-peer-grant 268435456 nil *pfrst-core* 0 nil 0
                                                *pfrst-plan* *pfrst-peer* nil nil)) :hold)
      (equal (+ (fn-prstartup-peer-protected nil *pfrst-core* 0 nil 0 *pfrst-plan* nil nil)
                (fn-pfr-at 0 *pfrst-peer*)) 268435456)))
(assert-event
 (equal (fn-prstartup-default-plan-with-peer 268435456 67108864 nil *pfrst-core* 0 nil nil 0
                                            "/tmp/store" 4 8 256 nil nil nil)
        (fn-prstartup-plan 268435456 67108864
                           (fn-prstartup-protected nil *pfrst-core* 0 nil 0 nil)
                           "/tmp/store" 4 (fn-heap-stack-octets nil) *fn-heap-thread-runtime-octets*
                           8 256 (fn-prstartup-read-reserve (fn-prstartup-read-extent nil) 4))))
(assert-event
 (and (equal (fn-prstartup-status
  (fn-prstartup-default-plan-with-peer 268435456 67108864 nil *pfrst-core* 0 nil nil 0
                                       "/tmp/store" 4 8 256 '(bad) nil nil)) :refused)
      (equal (fn-pfr-at 0 (fn-prstartup-peer-grant 268435456 nil *pfrst-core* 0 nil 0 nil *pfrst-peer* nil nil)) :refused)))

(assert-event
 (and (fn-pfr-operation-observes-p :run)
      (not (fn-pfr-operation-observes-p :status))
      (equal (fn-prstartup-peer-native-capture 268435456 nil *pfrst-core* 0 nil 0
               *pfrst-plan* *pfrst-peer* nil nil)
             (list 268435456
                   (fn-prstartup-peer-protected nil *pfrst-core* 0 nil 0 *pfrst-plan* nil nil)
                   *pfrst-peer* (fn-heap-stack-octets nil) *fn-heap-thread-runtime-octets*))
      (not (fn-prstartup-peer-native-capture 268435456 nil *pfrst-core* 0 nil 0
               nil *pfrst-peer* nil nil))))

(assert-event
 (let* ((need (fn-heap-reservation-octets 256 *pfrst-core* (fn-heap-stack-kib nil)
                    (+ (fn-heap-thread-count 0) 1)))
        (yes (fn-prstartup-peer-native-grant 268435456 nil *pfrst-core* 0 nil 0
                    *pfrst-plan* *pfrst-peer* (list need) nil 4 8 "/tmp/store" nil))
        (no (fn-prstartup-peer-native-grant 268435456 nil *pfrst-core* 0 nil 0
                    *pfrst-plan* *pfrst-peer* (list (1- need)) nil 4 8 "/tmp/store" nil)))
  (and (equal (car yes) :hold)
       (equal (cadr yes) (fn-prstartup-peer-native-capture 268435456 nil *pfrst-core* 0 nil 0
                          *pfrst-plan* *pfrst-peer* nil nil))
       (equal no '(:refused :peer-native-reservation-not-held)))))

; A policy file changed after launch cannot add a second unfunded worker.
(assert-event
 (let* ((need (fn-heap-reservation-octets 256 *pfrst-core* (fn-heap-stack-kib nil)
                    (+ (fn-heap-thread-count 0) 1)))
        (changed (update-nth 3 2 *pfrst-peer*))
        (grant (fn-prstartup-peer-native-grant 268435456 nil *pfrst-core* 0 nil 0
                    *pfrst-plan* changed (list need) nil 4 8 "/tmp/store" nil)))
  (and (fn-pfr-policy-p changed)
       (equal (car (fn-prstartup-peer-grant 268435456 nil *pfrst-core* 0 nil 0
                    *pfrst-plan* changed nil nil)) :hold)
       (equal grant '(:refused :peer-native-reservation-not-held))
       (stringp (fn-prstartup-peer-native-refusal-line grant)))))

;; L-RUN-LAUNCH, K-L4: the owner starts what the probe launched.  The witnesses are the heap-command teeth's
;; (tests/acl2/heap-command-tests.lisp): fn-core's probe with the peer flight the run funds.
(defconst *pfrst-sv-profile*
  '((102 110 45 115 116 111 114 101 45 49 48) 16384 8388608 196608 32768 16 256 128 1048576 1048576 1048576
    1048576 1048576 64 256 16384))
(defconst *pfrst-sv-peer* '(11728 917504 2 1 458752 33554432))
(defconst *pfrst-sv-core-img* '(81046496 30081024 1376256))
(defconst *pfrst-sv-core* '(81046496 . 30081024))
(defconst *pfrst-sv-host-img* '(248946304 30081024 1310720))
(defconst *pfrst-sv-host-core* '(248946304 . 136689072))
(defconst *pfrst-sv-tot* '(0 0 0 0 0 0 0 0 :RESIDENT))
(defconst *pfrst-sv-nursery* 8388608)
(defun pfrst-mib (n) (* n 1048576))
(defun pfrst-sv-pools (profile peer workers cache-limit root)
  (fn-mo-serve-pools profile nil nil peer workers cache-limit root))
;; the probe's decision at fn-core with 256 MiB resident, and the space the owner starts in
(defconst *pfrst-sv-d*
  (fn-mo-serve-decide *pfrst-sv-profile* *pfrst-sv-core-img* 8388608 nil nil 119 (list (pfrst-mib 256)) nil
                      *pfrst-sv-core* *pfrst-sv-nursery* *pfrst-sv-tot*
                      (pfrst-sv-pools *pfrst-sv-profile* *pfrst-sv-peer* 4 8 "/x")
                      (fn-mo-serve-pool-threads nil *pfrst-sv-peer*)))
(defconst *pfrst-sv-dyn* (* *fn-heap-mib* (cadr *pfrst-sv-d*)))
(defconst *pfrst-sv-trigger* (fn-heap-nursery-trigger *pfrst-sv-dyn* *pfrst-sv-nursery*))
(defconst *pfrst-sv-owner* '(81046496 . 70000000))
(defun pfrst-sv-plan (protected)
  (fn-prstartup-plan *pfrst-sv-dyn* 60000000 protected "/x" 4 (fn-heap-stack-octets *pfrst-sv-profile*)
                     *fn-heap-thread-runtime-octets* 8 256
                     (fn-prstartup-read-reserve (fn-prstartup-read-extent *pfrst-sv-profile*) 4)))

;; The owner's DEFAULT pool plan is admitted at the launched space and its native peer grant holds ...
(assert-event
 (let ((plan (fn-prstartup-default-plan-with-peer
              *pfrst-sv-dyn* 60000000 *pfrst-sv-profile* *pfrst-sv-owner* *pfrst-sv-trigger* nil nil 31 "/x" 4 8 256
              *pfrst-sv-peer* nil (list (pfrst-mib 256)))))
   (and (equal (car *pfrst-sv-d*) :heap)
        (equal (car plan) :admitted)
        (equal (car (fn-prstartup-peer-native-grant
                     *pfrst-sv-dyn* *pfrst-sv-profile* *pfrst-sv-owner* *pfrst-sv-trigger* nil 31 plan
                     *pfrst-sv-peer* (list (pfrst-mib 2048)) nil 4 8 "/x" (list (pfrst-mib 256))))
               :hold))))
;; ... and the protected runtime it was admitted at is within the profile's bound, strictly (the launch is
;; smaller than the whole store the profile admits, which at fn-core's 256 MiB the plan cannot be held to).
(assert-event
 (let ((limit (fn-prstartup-serve-limit *pfrst-sv-profile* nil *pfrst-sv-peer* 4 8 "/x" (list (pfrst-mib 256)))))
   (and (natp limit)
        (< (fn-prstartup-serve-protected *pfrst-sv-profile* *pfrst-sv-owner* *pfrst-sv-trigger* nil 31 nil limit)
           (fn-prstartup-protected *pfrst-sv-profile* *pfrst-sv-owner* *pfrst-sv-trigger* nil 31 nil)))))
;; Held to the profile's bound the same plan is refused: the heap the probe launched does not hold it.
(assert-event
 (equal (pfrst-sv-plan (+ (fn-prstartup-protected *pfrst-sv-profile* *pfrst-sv-owner* *pfrst-sv-trigger* nil 31 nil)
                          (nfix (car *pfrst-sv-peer*))))
        '(:refused :default-pool-heap-not-held)))


(defkeystone pfrst-serve-startup-admits-the-pool
  (implies (and (equal (car (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer))) :heap)
                (equal (fn-heap-core-file owner) (fn-heap-core-file core))
                (and (natp occupied) (<= occupied (fn-heap-core-dynamic owner)))
                (and (natp (fn-mm-least-observation resident-o))
                     (<= (fn-mm-least-observation resident-o) (fn-mm-least-observation resident)))
                (or (not peer) (fn-pfr-policy-p peer))
                (or (not output) (fn-orv-policy-p output))
                (and (stringp root) (posp workers) (natp cache-limit) (natp fd-limit))
                (<= (max 8 (+ 1 cache-limit)) fd-limit)
                (fn-crl-table-supportedp (max 8 (+ 1 cache-limit))))
           (and (equal (car (fn-prstartup-default-plan-with-peer (* *fn-heap-mib* (nfix (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer))))) occupied profile owner (fn-heap-nursery-trigger (* *fn-heap-mib* (nfix (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer))))) nursery) nil output
                                                   max-connections root workers cache-limit fd-limit
                                                   peer observed resident-o)) :admitted)
                (implies peer (equal (car (fn-prstartup-peer-native-grant (* *fn-heap-mib* (nfix (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer))))) profile owner (fn-heap-nursery-trigger (* *fn-heap-mib* (nfix (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer))))) nursery) output max-connections (fn-prstartup-default-plan-with-peer (* *fn-heap-mib* (nfix (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer))))) occupied profile owner (fn-heap-nursery-trigger (* *fn-heap-mib* (nfix (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer))))) nursery) nil output
                                                   max-connections root workers cache-limit fd-limit
                                                   peer observed resident-o) peer
                                                    address observed workers cache-limit root resident-o)) :hold))))
  :rule-classes nil
  :restates fn-mo-serve-startup-admits-the-pool
  :hyps (accepted same-core occupied-held owner-observed peer-valid output-valid pool-shape table-fits table-supported)
  :subject fn-mo-serve-decide
  :witness ((profile *pfrst-sv-profile*) (img *pfrst-sv-core-img*) (trigger 8388608) (live nil) (config 119) (resident (list (pfrst-mib 256))) (address (list (pfrst-mib 2048))) (core *pfrst-sv-core*) (nursery *pfrst-sv-nursery*) (tot *pfrst-sv-tot*) (output nil) (peer *pfrst-sv-peer*) (workers 4) (cache-limit 8) (root "/x") (owner (cons 81046496 70000000)) (occupied 60000000) (max-connections 31) (observed nil) (fd-limit 256) (resident-o (list (pfrst-mib 256))))
  :breaks ((accepted ((profile *pfrst-sv-profile*) (img *pfrst-sv-host-img*) (trigger 8388608) (live nil) (config 119) (resident (list (pfrst-mib 1024))) (address (list (pfrst-mib 1100))) (core *pfrst-sv-host-core*) (nursery *pfrst-sv-nursery*) (tot *pfrst-sv-tot*) (output nil) (peer *pfrst-sv-peer*) (workers 4) (cache-limit 8) (root "/x") (owner *pfrst-sv-host-core*) (occupied 60000000) (max-connections 31) (observed nil) (fd-limit 256) (resident-o (list (pfrst-mib 1024)))))
           (same-core ((profile *pfrst-sv-profile*) (img *pfrst-sv-core-img*) (trigger 8388608) (live nil) (config 119) (resident (list (pfrst-mib 256))) (address (list (pfrst-mib 2048))) (core *pfrst-sv-core*) (nursery *pfrst-sv-nursery*) (tot *pfrst-sv-tot*) (output nil) (peer *pfrst-sv-peer*) (workers 4) (cache-limit 8) (root "/x") (owner (cons 999999999999 999999999999)) (occupied 60000000) (max-connections 31) (observed nil) (fd-limit 256) (resident-o (list (pfrst-mib 256)))))
           (occupied-held ((profile *pfrst-sv-profile*) (img *pfrst-sv-core-img*) (trigger 8388608) (live nil) (config 119) (resident (list (pfrst-mib 256))) (address (list (pfrst-mib 2048))) (core *pfrst-sv-core*) (nursery *pfrst-sv-nursery*) (tot *pfrst-sv-tot*) (output nil) (peer *pfrst-sv-peer*) (workers 4) (cache-limit 8) (root "/x") (owner (cons 81046496 70000000)) (occupied 1000000000000) (max-connections 31) (observed nil) (fd-limit 256) (resident-o (list (pfrst-mib 256)))))
           (owner-observed ((profile *pfrst-sv-profile*) (img *pfrst-sv-core-img*) (trigger 8388608) (live nil) (config 119) (resident (list (pfrst-mib 256))) (address (list (pfrst-mib 2048))) (core *pfrst-sv-core*) (nursery *pfrst-sv-nursery*) (tot *pfrst-sv-tot*) (output nil) (peer *pfrst-sv-peer*) (workers 4) (cache-limit 8) (root "/x") (owner (cons 81046496 70000000)) (occupied 60000000) (max-connections 31) (observed nil) (fd-limit 256) (resident-o nil)))
           (peer-valid ((profile *pfrst-sv-profile*) (img *pfrst-sv-core-img*) (trigger 8388608) (live nil) (config 119) (resident (list (pfrst-mib 256))) (address (list (pfrst-mib 2048))) (core *pfrst-sv-core*) (nursery *pfrst-sv-nursery*) (tot *pfrst-sv-tot*) (output nil) (peer '(bad)) (workers 4) (cache-limit 8) (root "/x") (owner (cons 81046496 70000000)) (occupied 60000000) (max-connections 31) (observed nil) (fd-limit 256) (resident-o (list (pfrst-mib 256)))))
           (output-valid ((profile *pfrst-sv-profile*) (img *pfrst-sv-core-img*) (trigger 8388608) (live nil) (config 119) (resident (list (pfrst-mib 256))) (address (list (pfrst-mib 2048))) (core *pfrst-sv-core*) (nursery *pfrst-sv-nursery*) (tot *pfrst-sv-tot*) (output '(bad)) (peer *pfrst-sv-peer*) (workers 4) (cache-limit 8) (root "/x") (owner (cons 81046496 70000000)) (occupied 60000000) (max-connections 31) (observed nil) (fd-limit 256) (resident-o (list (pfrst-mib 256)))))
           (pool-shape ((profile *pfrst-sv-profile*) (img *pfrst-sv-core-img*) (trigger 8388608) (live nil) (config 119) (resident (list (pfrst-mib 256))) (address (list (pfrst-mib 2048))) (core *pfrst-sv-core*) (nursery *pfrst-sv-nursery*) (tot *pfrst-sv-tot*) (output nil) (peer *pfrst-sv-peer*) (workers 0) (cache-limit 8) (root "/x") (owner (cons 81046496 70000000)) (occupied 60000000) (max-connections 31) (observed nil) (fd-limit 256) (resident-o (list (pfrst-mib 256)))))
           (table-fits ((profile *pfrst-sv-profile*) (img *pfrst-sv-core-img*) (trigger 8388608) (live nil) (config 119) (resident (list (pfrst-mib 256))) (address (list (pfrst-mib 2048))) (core *pfrst-sv-core*) (nursery *pfrst-sv-nursery*) (tot *pfrst-sv-tot*) (output nil) (peer *pfrst-sv-peer*) (workers 4) (cache-limit 8) (root "/x") (owner (cons 81046496 70000000)) (occupied 60000000) (max-connections 31) (observed nil) (fd-limit 8) (resident-o (list (pfrst-mib 256)))))
           (table-supported ((profile *pfrst-sv-profile*) (img *pfrst-sv-core-img*) (trigger 8388608) (live nil) (config 119) (resident (list (pfrst-mib 4000000))) (address nil) (core *pfrst-sv-core*) (nursery *pfrst-sv-nursery*) (tot *pfrst-sv-tot*) (output nil) (peer *pfrst-sv-peer*) (workers 4) (cache-limit (expt 2 25)) (root "/x") (owner (cons 81046496 70000000)) (occupied 60000000) (max-connections 31) (observed nil) (fd-limit (expt 2 26)) (resident-o (list (pfrst-mib 4000000))))))
  :mutations ((protected-by-the-profile-bound
               (:conclusion
                (equal (car (fn-prstartup-plan (* *fn-heap-mib* (nfix (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer))))) occupied (+ (fn-prstartup-protected profile owner (fn-heap-nursery-trigger (* *fn-heap-mib* (nfix (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer))))) nursery) output max-connections observed) (if peer (nfix (fn-pfr-at 0 peer)) 0)) root workers
                                           (fn-heap-stack-octets profile) *fn-heap-thread-runtime-octets*
                                           cache-limit fd-limit
                                           (fn-prstartup-read-reserve (fn-prstartup-read-extent profile) workers))) :admitted))
               ((profile *pfrst-sv-profile*) (img *pfrst-sv-core-img*) (trigger 8388608) (live nil) (config 119) (resident (list (pfrst-mib 256))) (address (list (pfrst-mib 2048))) (core *pfrst-sv-core*) (nursery *pfrst-sv-nursery*) (tot *pfrst-sv-tot*) (output nil) (peer *pfrst-sv-peer*) (workers 4) (cache-limit 8) (root "/x") (owner (cons 81046496 70000000)) (occupied 60000000) (max-connections 31) (observed nil) (fd-limit 256) (resident-o (list (pfrst-mib 256))))
               :fault "the owner's pool plan held to today's profile-bound protected runtime, which refuses the launched heap"))
  :hints (("Goal" :by fn-mo-serve-startup-admits-the-pool)))

;; K-L4c (fn-mo-serve-output-pool-is-held): with a 16 MiB output pool the run funds, fn-core's probe at
;; 256 MiB launches, and the owner's output grant holds at the launched space: its store need and
;; the pool fit, and books/output-reservation.lisp's grant is :hold.  Tooth: the need at the profile's
;; bound alone (the store figure the grant was given before L-RUN-LAUNCH) does not fit that space.
(defconst *pfrst-sv-output* '(16777216 1048576))
(defconst *pfrst-sv-od*
  (fn-mo-serve-decide *pfrst-sv-profile* *pfrst-sv-core-img* 8388608 nil nil 119 (list (pfrst-mib 256)) nil
                      *pfrst-sv-core* *pfrst-sv-nursery* *pfrst-sv-tot*
                      (fn-mo-serve-pools *pfrst-sv-profile* nil *pfrst-sv-output* *pfrst-sv-peer* 4 8 "/x")
                      (fn-mo-serve-pool-threads nil *pfrst-sv-peer*)))
(defconst *pfrst-sv-odyn* (* *fn-heap-mib* (cadr *pfrst-sv-od*)))
(defconst *pfrst-sv-need*
  (fn-prstartup-serve-store-need *pfrst-sv-profile* *pfrst-sv-owner*
                                 (fn-heap-nursery-trigger *pfrst-sv-odyn* *pfrst-sv-nursery*)
                                 *pfrst-sv-output* *pfrst-sv-peer* 4 8 "/x" (list (pfrst-mib 256))))
(assert-event
 (and (equal (car *pfrst-sv-od*) :heap)
      (fn-orv-policy-p *pfrst-sv-output*)
      (<= (+ *pfrst-sv-need* (car *pfrst-sv-output*)) *pfrst-sv-odyn*)
      (equal (car (fn-orv-startup-grant *pfrst-sv-odyn* *pfrst-sv-need* nil *pfrst-sv-output* 33)) :hold)))
(assert-event
 (< *pfrst-sv-odyn*
    (+ (fn-prstartup-protected *pfrst-sv-profile* *pfrst-sv-owner*
                               (fn-heap-nursery-trigger *pfrst-sv-odyn* *pfrst-sv-nursery*) nil 31 nil)
       (car *pfrst-sv-output*))))

(defkeystone pfrst-serve-output-pool-is-held
  (implies (and (equal (car (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer))) :heap)
                (equal (fn-heap-core-file owner) (fn-heap-core-file core))
                (and (natp (fn-mm-least-observation resident-o))
                     (<= (fn-mm-least-observation resident-o) (fn-mm-least-observation resident))))
           (<= (+ (fn-prstartup-serve-store-need profile owner (fn-heap-nursery-trigger (* *fn-heap-mib* (nfix (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer))))) nursery)
                                                 output peer workers cache-limit root resident-o)
                  (nfix (fn-crv-nth 0 output)))
               (* *fn-heap-mib* (nfix (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))))))
  :rule-classes nil
  :restates fn-mo-serve-output-pool-is-held
  :hyps (accepted same-core owner-observed)
  :subject fn-prstartup-serve-store-need
  :witness ((profile *pfrst-sv-profile*) (img *pfrst-sv-core-img*) (trigger 8388608) (live nil) (config 119)
            (resident (list (pfrst-mib 256))) (address nil) (core *pfrst-sv-core*) (nursery *pfrst-sv-nursery*)
            (tot *pfrst-sv-tot*) (output *pfrst-sv-output*) (peer *pfrst-sv-peer*) (workers 4) (cache-limit 8)
            (root "/x") (owner *pfrst-sv-owner*) (resident-o (list (pfrst-mib 256))))
  :breaks ((accepted ((profile *pfrst-sv-profile*) (img *pfrst-sv-host-img*) (trigger 8388608) (live nil) (config 119)
                      (resident (list (pfrst-mib 256))) (address nil) (core *pfrst-sv-host-core*) (nursery *pfrst-sv-nursery*)
                      (tot *pfrst-sv-tot*) (output *pfrst-sv-output*) (peer *pfrst-sv-peer*) (workers 4) (cache-limit 8)
                      (root "/x") (owner *pfrst-sv-host-core*) (resident-o (list (pfrst-mib 256))))
            :logical "a refused decision's second field is its reason, not a figure, so the conclusion is evaluated for its logical value")
           (same-core ((profile *pfrst-sv-profile*) (img *pfrst-sv-core-img*) (trigger 8388608) (live nil) (config 119)
                       (resident (list (pfrst-mib 256))) (address nil) (core *pfrst-sv-core*) (nursery *pfrst-sv-nursery*)
                       (tot *pfrst-sv-tot*) (output *pfrst-sv-output*) (peer *pfrst-sv-peer*) (workers 4) (cache-limit 8)
                       (root "/x") (owner (cons 999999999999 999999999999)) (resident-o (list (pfrst-mib 256)))))
           (owner-observed ((profile *pfrst-sv-profile*) (img *pfrst-sv-core-img*) (trigger 8388608) (live nil) (config 119)
                            (resident (list (pfrst-mib 256))) (address nil) (core *pfrst-sv-core*) (nursery *pfrst-sv-nursery*)
                            (tot *pfrst-sv-tot*) (output *pfrst-sv-output*) (peer *pfrst-sv-peer*) (workers 4) (cache-limit 8)
                            (root "/x") (owner *pfrst-sv-owner*) (resident-o (list (pfrst-mib 100000))))))
  :mutations ((need-at-the-profile-bound
               (:conclusion (<= (+ (fn-prstartup-protected profile owner (fn-heap-nursery-trigger (* *fn-heap-mib* (nfix (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer))))) nursery) nil 31 nil)
                                   (nfix (fn-crv-nth 0 output)))
                                (* *fn-heap-mib* (nfix (cadr (fn-mo-serve-decide profile img trigger live nil config resident address core nursery tot (fn-mo-serve-pools profile nil output peer workers cache-limit root) (fn-mo-serve-pool-threads nil peer)))))))
               ((profile *pfrst-sv-profile*) (img *pfrst-sv-core-img*) (trigger 8388608) (live nil) (config 119)
                (resident (list (pfrst-mib 256))) (address nil) (core *pfrst-sv-core*) (nursery *pfrst-sv-nursery*)
                (tot *pfrst-sv-tot*) (output *pfrst-sv-output*) (peer *pfrst-sv-peer*) (workers 4) (cache-limit 8)
                (root "/x") (owner *pfrst-sv-owner*) (resident-o (list (pfrst-mib 256))))
               :fault "the output grant given the profile's whole store (the figure before L-RUN-LAUNCH), which the launched space does not hold"))
  :hints (("Goal" :by fn-mo-serve-output-pool-is-held)))
