; Resident supported-profile settings; no durable namespace ceiling.
(in-package "ACL2")
(include-book "compress-policy")
(include-book "columns")
(include-book "core-children")
(fn2-book-layer :d)



(defcolumns fn2-compress-config
 ((enabled :bool) (input-quantum :u32) (output-quantum :u32)
  (ratio :u32) (burst :u32)))
(defun fn2-compress-config-from (profile fn2-compress-config)
 (declare (xargs :stobjs fn2-compress-config :guard (fn2-compress-profilep profile)))
 (let* ((fn2-compress-config (fn2-compress-config-init 1 fn2-compress-config))
        (iq (fn2-profile-get :compress-input-quantum profile))
        (oq (fn2-profile-get :compress-output-quantum profile))
        (ratio (fn2-profile-get :compress-expansion-ratio profile))
        (burst (fn2-profile-get :compress-expansion-burst profile)))
  (fn2-compress-config-put 0
   (enabled (if (fn2-profile-get :compress-enabled profile) 1 0))
   (input-quantum (if (unsigned-byte-p 32 iq) iq 0))
   (output-quantum (if (unsigned-byte-p 32 oq) oq 0))
   (ratio (if (unsigned-byte-p 32 ratio) ratio 0))
   (burst (if (unsigned-byte-p 32 burst) burst 0)))))
(defthm fn2-compress-config-from-type
 (implies (fn2-compress-configp fn2-compress-config)
  (fn2-compress-configp (fn2-compress-config-from profile fn2-compress-config))))
(defthm fn2-compress-config-from-wfp
 (fn2-compress-config-wfp (fn2-compress-config-from profile fn2-compress-config)))
(in-theory (disable fn2-compress-config-from fn2-compress-profilep))
(defcorechild fn2-core-compress-config fn2-compress-config
 :init (fn2-compress-config-from profile fn2-compress-config)
 :profilep (fn2-compress-profilep profile)
 :why "COMPRESS admission and two-span work/expansion policy from the supported profile.")
