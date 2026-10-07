; Separate congruent command-receive backing while the owner's incoming
; POST octets are retained by a query. Never copies the held POST payload.
; Installed receive quantum is existing connection-budget policy (D27).
(in-package "ACL2")
(include-book "octets-stobj")
(include-book "connection-budget")
(include-book "cold-read-layout")

(include-book "def-buffer")
(def-buffer fn-octets-rx)


(defun fn-rxb-append-byte (limits byte fn-octets-rx)
  (declare (xargs :stobjs fn-octets-rx :guard (unsigned-byte-p 8 byte)))
  (if (>= (fn-octets-rx-len fn-octets-rx) (fn-cbud-step-read-octets limits))
      (mv :receive-quantum-full fn-octets-rx)
    (let ((fn-octets-rx (fn-octets-rx-append-octet byte fn-octets-rx)))
      (mv :received fn-octets-rx))))

; Selected layout component ONLY. Permanent backing must be preallocated
; before activation and retained in U. Source vector is an independent live
; overlap; caller/frame/allocator primitive workspace is not counted here.
(defun fn-rxb-layout-components (limits)
  (declare (xargs :guard t))
  (let ((q (fn-cbud-step-read-octets limits)))
    (list (* 2 (+ (fn-crl-array-octets *fn-cbud-read-quantum* 1)
                   (fn-crl-array-octets 2 8)))
          (* 2 (fn-crl-array-octets q 1)))))

(defthm fn-rxb-append-byte-is-bounded-receive-transition
  (let ((result (fn-rxb-append-byte limits byte fn-octets-rx)))
    (and (equal (mv-nth 0 result)
                (if (>= (len fn-octets-rx) (fn-cbud-step-read-octets limits))
                    :receive-quantum-full :received))
         (equal (mv-nth 1 result)
                (if (>= (len fn-octets-rx) (fn-cbud-step-read-octets limits))
                    fn-octets-rx
                  (append fn-octets-rx (list byte))))))
  :hints (("Goal" :in-theory (enable fn-rxb-append-byte fn-octets$a-len
                                    fn-octets$a-append-octet))))

 ; Resource side of the registered RX append export. Its :exec is exactly
; fn-octets$c-append-octet above. Capacity is physical carried state, not
; reconstructed from the rows-only logical octet value. Actual installed
; capacity and its retained U charge are owed by the startup/pool boundary.
(defthm fn-rxb-installed-capacity-append-does-not-resize
  (implies (and (<= *fn-cbud-read-quantum* (fn-octets$c-buf-length fn-octets$c))
                (< (fn-octets$c-fill fn-octets$c)
                   (fn-cbud-step-read-octets limits)))
           (and (equal (fn-octets$c-buf-length
                         (fn-octets$c-append-octet byte fn-octets$c))
                       (fn-octets$c-buf-length fn-octets$c))
                (equal (fn-octets$c-fill
                         (fn-octets$c-append-octet byte fn-octets$c))
                       (+ 1 (fn-octets$c-fill fn-octets$c)))))
  :hints (("Goal" :in-theory (enable fn-octets$c-append-octet))))

(in-theory (disable fn-rxb-append-byte fn-rxb-layout-components))
