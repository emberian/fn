;; TLS admission is a bounded token partition. The connection retains its RX
;; range, operation and timer until terminal harvest; releasing a token never
;; releases a still-live external loan.
(in-package "ACL2")
(include-book "machines-a")
(include-book "core-children")
(include-book "machine-arms")
(fn2-book-layer :d)

(defconst *fn2-tls-io-bytes* 1024)
(defconst *fn2-tls-minimum-version* #x0303) ; TLS 1.2, with TLS 1.3 preferred by OpenSSL

(defun fn2-tls-setting (key default profile)
  (declare (xargs :guard t))
  (let ((value (fn2-profile-get key profile))) (if (null value) default value)))
(defun fn2-tls-pathp (path)
 (declare (xargs :guard t))
 (and (stringp path) (< 0 (length path)) (<= (length path) 4096)
      (not (member (code-char 0) (coerce path 'list)))))
(defun fn2-tls-requested-p (profile)
 (declare (xargs :guard t))
 (or (not (null (fn2-profile-get :tls-certificate profile)))
     (not (null (fn2-profile-get :tls-key profile)))))
(defun fn2-tls-profilep (profile)
  (declare (xargs :guard t))
  (let ((slots (fn2-tls-setting :tls-handshakes 16 profile))
        (window (fn2-tls-setting :tls-window 16384 profile))
        (timeout (fn2-tls-setting :tls-handshake-ms 10000 profile)))
    (and (or (not (fn2-tls-requested-p profile))
             (and (fn2-tls-pathp (fn2-profile-get :tls-certificate profile))
                  (fn2-tls-pathp (fn2-profile-get :tls-key profile))))
         (posp slots) (unsigned-byte-p 16 slots)
         ;; BIO APIs take signed C int lengths; no implicit narrowing.
         (posp window) (unsigned-byte-p 31 window)
         (posp timeout) (unsigned-byte-p 32 timeout))))
(defun fn2-tls-admission-capacity (profile)
  (declare (xargs :guard t))
  (if (and (fn2-tls-profilep profile) (fn2-tls-requested-p profile))
      (nfix (fn2-tls-setting :tls-handshakes 16 profile)) 0))
(defthm fn2-tls-admission-capacity-natp
  (natp (fn2-tls-admission-capacity profile)) :rule-classes :type-prescription)

(defcolumns fn2-tls-config ((enabled :bool) (window :u32) (timeout-ms :u32)))
(defun fn2-tls-config-from (profile fn2-tls-config)
  (declare (xargs :stobjs fn2-tls-config :guard (fn2-tls-profilep profile)))
  (let* ((fn2-tls-config (fn2-tls-config-init 1 fn2-tls-config))
         (window (fn2-tls-setting :tls-window 16384 profile))
         (timeout (fn2-tls-setting :tls-handshake-ms 10000 profile)))
    (fn2-tls-config-put 0
      (enabled (if (fn2-tls-requested-p profile) 1 0))
      (window (if (unsigned-byte-p 32 window) window 16384))
      (timeout-ms (if (unsigned-byte-p 32 timeout) timeout 10000)))))
(defthm fn2-tls-config-from-type
  (implies (fn2-tls-configp fn2-tls-config)
           (fn2-tls-configp (fn2-tls-config-from profile fn2-tls-config))))
(defthm fn2-tls-config-from-wfp
  (fn2-tls-config-wfp (fn2-tls-config-from profile fn2-tls-config)))
(in-theory (disable fn2-tls-config-from fn2-tls-profilep fn2-tls-admission-capacity))
(defcorechild fn2-core-tls-config fn2-tls-config
 :init (fn2-tls-config-from profile fn2-tls-config) :profilep (fn2-tls-profilep profile)
 :why "STARTTLS enablement, bounded BIO storage and handshake deadline from the supported profile.")

(defmachine fn2-tls-admit
 :phases (:free :held :draining :retired)
 :fields ((conn :link) (conn-gen :u60) (next-free :link) (stopped :bool))
 :holds ((:held :tls-slot) (:draining :tls-slot))
 :budget (:bytes 0 :steps 32 :descriptors 0)
 :capacity (fn2-tls-admission-capacity profile)
 :taken (:phase :held :rows :tls-slot :ranges () :copy (conn conn-gen) :clear (stopped))
 :initial ((generation fn2-machine-initial-generation)
           (ready-prev *fn2-none*) (ready-next *fn2-none*) (conn *fn2-none*)
           (next-free fn2-machine-initial-next-free))
 :arms ((:free) (:held) (:draining) (:retired))
 :observes ())
(defmachine-registry fn2-tls-admit)
