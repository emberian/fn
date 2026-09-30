; A-SELECTED-RUNTIME-NATIVE-CONSTRUCTORS. Exact native owned-object requests.
; Not allocator/TLAB reservation, XEP/caller frames, first-use globals, GC,
; socket/TLS/input buffers, core-issued token construction or whole operation.
; PRF-1153. The host never converts these rows into an admission authority.
(in-package "ACL2")

(defconst *fn-srnc-runtime*
 '("SBCL" "2.6.8" "X86-64" "Linux" 8 16
   "b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5"
   "1024f0a505044cae4de084e77a654aade844dfa546b51cc90dc9e2a09c903aba"
   :fresh-native-compile
   ((inhibit-warnings 3) (speed 3) (space 1) (safety 0) (debug 1) (compilation-speed 0))))
(defun fn-srnc-runtime-p (runtime)
 (declare (xargs :guard t)) (equal runtime *fn-srnc-runtime*))
(defun fn-srnc-unit-row (unit)
 (declare (xargs :guard t))
 (case unit
  (:service-owned
   '("6f821e8382c321167133b8927c8021a266d973f22e0c77cc0910c0f3c7758227" 848))
  (:node
   '("c2aaadeb0fd357439c53432e5f68d4f731ec3fdfccfbf57f3a3df67ed4043ee7" 48))
  (:mux
   '("f5467b87aa5694295f94f83d96b5f82c671f48f8b3e9d4949bb407616d8278f2" 256))
  (:fixed-fault
   '("74534be69b34f36febcd54c0a5d59ff85ccd91ccc320b8a2e2497d135196b384" 80))
  (:collector-installation
   '("eddb37b731320ad116e92db517cc05eec041896f785d5e4a51b832c2b4d5134b" 64))
  (:collector-binding
   '("3987ee7f4984169d94a6c861c3008d9c3755a0dc1fa78a74dc6379378dfbdba2" 48))
  (:collector-bound-factory
   '(("08c86911ef661c94bce815cd46fa67438c6954cb52f4c985100b44247772de3a"
      "3987ee7f4984169d94a6c861c3008d9c3755a0dc1fa78a74dc6379378dfbdba2"
      "eddb37b731320ad116e92db517cc05eec041896f785d5e4a51b832c2b4d5134b") 112))
  (otherwise nil)))
(defun fn-srnc-unit-coordinate-p (unit source runtime)
 (declare (xargs :guard t))
 (let ((row (fn-srnc-unit-row unit)))
  (and (consp row) (equal source (car row)) (fn-srnc-runtime-p runtime))))
(defun fn-srnc-unit-request (unit)
 (declare (xargs :guard t))
 (let ((row (fn-srnc-unit-row unit))) (if (consp row) (cadr row) 0)))
(defun fn-srnc-unit-status (unit source runtime)
 (declare (xargs :guard t))
 (if (fn-srnc-unit-coordinate-p unit source runtime) :native-owned-row :unavailable))

; The unit is the complete owned-object request of this finite constructor
; family, not a PRIMARY SERVICE object alone: 432 +3*32+2*32+2*128 =848.
; Hash default pairs are a shared existing image root, charged separately.
; Fault provenance is an existing cause pointer; arbitrary cause construction
; is not bounded by this condition's fixed-object row.
(encapsulate
 (((fn-assume-srnc-owned-object-octets * * *) => *))
 (local
  (defun fn-assume-srnc-owned-object-octets (unit source runtime)
   (declare (ignore unit source runtime)) 0))
 (defthm fn-assume-srnc-owned-object-octets-natural
  (natp (fn-assume-srnc-owned-object-octets unit source runtime))
  :rule-classes :type-prescription)
 (defthm fn-assume-srnc-exact-native-owned-request-bound
  (implies (fn-srnc-unit-coordinate-p unit source runtime)
   (<= (fn-assume-srnc-owned-object-octets unit source runtime)
       (fn-srnc-unit-request unit)))
  :hints (("Goal" :in-theory (enable fn-srnc-unit-coordinate-p
                                    fn-srnc-unit-request fn-srnc-unit-row)))
  :rule-classes nil))

; Native nodes point to already-issued core tokens. This counts BOTH live and
; retiring nodes, never subtracts a closing node before actual release, and
; includes the retained service and current mux object. It does not count a
; token pointer as a second newly allocated token or infer release from GC.
(defun fn-srnc-connection-owned-census (live retiring pending faults)
 (declare (xargs :guard (and (natp live) (natp retiring) (natp pending) (natp faults))))
 (+ 848 256 (* 48 (+ (nfix live) (nfix retiring) (nfix pending))) (* 80 (nfix faults))))

(defthm fn-srnc-connection-owned-census-natural
 (natp (fn-srnc-connection-owned-census live retiring pending faults))
 :hints (("Goal" :in-theory (enable fn-srnc-connection-owned-census)))
 :rule-classes :type-prescription)

; Conditional finite repin envelope: service baseline, one mux, BOTH old/new
; nodes, and one fixed fault object coexist. Core tokens and other families
; are joined by the operation owner, never silently assigned zero here.
(defthm fn-srnc-repin-native-owned-object-request-bound
 (implies
  (and (fn-srnc-unit-coordinate-p :service-owned service-source runtime)
       (fn-srnc-unit-coordinate-p :node node-source runtime)
       (fn-srnc-unit-coordinate-p :mux mux-source runtime)
       (fn-srnc-unit-coordinate-p :fixed-fault fault-source runtime))
  (<= (+ (fn-assume-srnc-owned-object-octets :service-owned service-source runtime)
         (* 2 (fn-assume-srnc-owned-object-octets :node node-source runtime))
         (fn-assume-srnc-owned-object-octets :mux mux-source runtime)
         (fn-assume-srnc-owned-object-octets :fixed-fault fault-source runtime))
      1280))
 :hints (("Goal"
  :use ((:instance fn-assume-srnc-exact-native-owned-request-bound
                   (unit :service-owned) (source service-source))
        (:instance fn-assume-srnc-exact-native-owned-request-bound
                   (unit :node) (source node-source))
        (:instance fn-assume-srnc-exact-native-owned-request-bound
                   (unit :mux) (source mux-source))
        (:instance fn-assume-srnc-exact-native-owned-request-bound
                   (unit :fixed-fault) (source fault-source)))
  :in-theory (enable fn-srnc-unit-request fn-srnc-unit-row)))
 :rule-classes nil)

; Callable pure unit-family producer for the operation builder. A row is only
; an owned-native-object subtotal. No caller may treat this word as ADMITTED.
(defun fn-srnc-connection-owned-request
 (live retiring pending faults service-source node-source mux-source fault-source runtime)
 (declare (xargs :guard t))
 (if (and (natp live) (natp retiring) (natp pending) (natp faults)
          (fn-srnc-unit-coordinate-p :service-owned service-source runtime)
          (fn-srnc-unit-coordinate-p :node node-source runtime)
          (fn-srnc-unit-coordinate-p :mux mux-source runtime)
          (fn-srnc-unit-coordinate-p :fixed-fault fault-source runtime))
     (mv :native-owned-row (fn-srnc-connection-owned-census live retiring pending faults))
   (mv :unavailable nil)))

; One preallocated observation carrier is an installation root, not one per GC
; or per connection. Collector operation/authorization is outside this book.
(defun fn-srnc-installation-owned-census (services collectors)
 (declare (xargs :guard (and (natp services) (natp collectors))))
 (+ (* 848 (nfix services)) (* 64 (nfix collectors))))

; The actual binding factory creates exactly one sample. Count it once;
; callback selection/frame/error scratch remains its own installation term.
(defun fn-srnc-bound-installation-owned-census (services bindings)
 (declare (xargs :guard (and (natp services) (natp bindings))))
 (+ (* 848 (nfix services)) (* 112 (nfix bindings))))
