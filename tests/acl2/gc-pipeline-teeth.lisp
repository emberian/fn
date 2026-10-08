; Generated claims bind to the signed formulas; witnesses run under guards.
(in-package "ACL2")
(include-book "gc-pipeline-tests")
(include-book "../../books/owner-commit-durability")
(include-book "../../books/defkeystone")

(defteeth fn-lgk-append-behind-safe
 :claim (((:invariant (fn-lgk-pipe-okp p h))) (let ((q (fn-lgk-behind-state p unit extent)))
      (and (fn-lgk-pipe-okp q h) (equal (fn-lgk-pipe-d q) (fn-lgk-pipe-d p))
           (<= (fn-lgk-pipe-acked q) (fn-lgk-pipe-d q)))))
 :subject fn-lgk-append-behind
 :witness ((p (nth 0 *gc-preappend*)) (h (nth 3 *gc-preappend*)) (unit 512) (extent 65536))
 :breaks ((:invariant ((p (nth 0 *gc-early-ack*)) (h (nth 3 *gc-early-ack*)) (unit 512) (extent 65536))))
 :mutations ((:early-release (:conclusion (equal (fn-lgk-pipe-acked (fn-lgk-behind-state p unit extent)) (len h))) ((p (nth 0 *gc-preappend*)) (h (nth 3 *gc-preappend*)) (unit 512) (extent 65536)) :fault "Releasing the appended tail before its own barrier.")))

(defteeth fn-lgk-pipe-fence-safe
 :claim (((:invariant (fn-lgk-pipe-okp p h))) (let ((q (fn-lgk-pipe-fence p unit)))
      (and (fn-lgk-pipe-okp q h) (<= (fn-lgk-pipe-d p) (fn-lgk-pipe-d q))
           (<= (fn-lgk-pipe-acked q) (fn-lgk-pipe-d q)))))
 :subject fn-lgk-pipe-fence
 :witness ((p (nth 0 *gc-pipelined*)) (h (nth 3 *gc-pipelined*)) (unit 512))
 :breaks ((:invariant ((p (nth 0 *gc-early-ack*)) (h (nth 3 *gc-early-ack*)) (unit 512))))
 :mutations ((:early-release (:conclusion (equal (fn-lgk-pipe-d (fn-lgk-pipe-fence p unit)) (len h))) ((p (nth 0 *gc-pipelined*)) (h (nth 3 *gc-pipelined*)) (unit 512)) :fault "Releasing the appended tail before its own barrier.")))

(defteeth fn-ocp-gc-linkedp-initially
 :claim (((:invariant (fn-ocp-gc-profilep unit extent bmax omax))) (fn-ocp-gc-linkedp (fn-ocp-gc-init unit extent bmax omax)))
 :subject fn-ocp-gc-init
 :witness ((unit 512) (extent 65536) (bmax 2) (omax 4096))
 :breaks ((:invariant ((unit 0) (extent 65536) (bmax 2) (omax 4096))))
 :mutations (:not-applicable "The construction has no release effect; its invalid-input removal is checked below."))

(defteeth fn-ocp-gc-linkedp-preserved
 :claim (((:invariant (fn-ocp-gc-linkedp x))) (fn-ocp-gc-linkedp (fn-ocp-gc-host-step x event)))
 :subject fn-ocp-gc-host-step
 :witness ((x *gc-preappend*) (event '(:append-issue)))
 :breaks ((:invariant ((x *gc-early-ack*) (event '(:reader)))))
 :mutations ((:early-release (:conclusion (equal (fn-lgk-pipe-acked (nth 0 (fn-ocp-gc-host-step x event))) (len (nth 3 x)))) ((x *gc-preappend*) (event '(:append-issue))) :fault "Releasing the appended tail before its own barrier.")))

(defteeth fn-ocp-gc-reveals-are-durable
 :claim (((:invariant (fn-ocp-gc-linkedp x))) (fn-ocp-gc-reveals-okp (fn-ocp-gc-host-step x event)))
 :subject fn-ocp-gc-host-step
 :witness ((x *gc-pipelined*) (event '(:reader)))
 :breaks ((:invariant ((x *gc-bad-view*) (event '(:reader)))))
 :mutations ((:early-release (:conclusion (equal (nth 8 (fn-ocp-gc-host-step x event)) (list (fn-ocvm-w (nth 2 x))))) ((x *gc-pipelined*) (event '(:reader))) :fault "Releasing the appended tail before its own barrier.")))

(defteeth fn-ocp-gc-failure-fences-both-batches
 :claim (((:invariant (fn-ocp-gc-failure-hyp x))) (fn-ocp-gc-failure-okp x events))
 :subject fn-ocp-gc-host-step
 :witness ((x *gc-pipelined*) (events *gc-late-events*))
 :breaks ((:invariant ((x *gc-resolved*) (events nil))))
 :mutations ((:early-release (:conclusion (equal (nth 9 (fn-ocp-gc-host-step x '(:io :current :uncertain))) '(:rendered :rendered))) ((x *gc-pipelined*) (events *gc-late-events*)) :fault "Releasing the appended tail before its own barrier.")))

(defteeth fn-olr-gc-membership-and-profile-bounds
 :claim (((:invariant (fn-olr-gc-membership-hyp h p record txid count octets bmax omax unit))) (fn-olr-gc-membership-okp h p record txid count octets bmax omax unit))
 :subject fn-lgk-pipe-take
 :witness ((h (nth 3 *gc-a*)) (p (nth 0 *gc-a*)) (record '(67)) (txid 3) (count 0) (octets 0) (bmax 2) (omax 4096) (unit 512))
 :breaks ((:invariant ((h (nth 3 *gc-preappend*)) (p (nth 0 *gc-preappend*)) (record '(68)) (txid 4) (count 0) (octets 5) (bmax 1) (omax 4096) (unit 512))))
 :mutations (:not-applicable "The construction has no release effect; its invalid-input removal is checked below."))

(value-triple :seven-keystone-teeth-bound-and-evaluated)
