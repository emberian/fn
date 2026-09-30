; Separate congruent command-receive backing while the owner's incoming
; POST octets are retained by a query. Never copies the held POST payload.
; Installed receive quantum is existing connection-budget policy (D27).
(in-package "ACL2")
(include-book "octets-stobj")
(include-book "connection-budget")
(include-book "cold-read-layout")

(defabsstobj fn-octets-rx
  :foundation fn-octets$c
  :recognizer (fn-octets-rx-p :logic fn-octets$ap :exec fn-octets$cp)
  :creator (create-fn-octets-rx :logic create-fn-octets$a :exec create-fn-octets$c)
  :exports ((fn-octets-rx-len :logic fn-octets$a-len :exec fn-octets$c-len)
            (fn-octets-rx-get :logic fn-octets$a-get :exec fn-octets$c-get)
            (fn-octets-rx-put :logic fn-octets$a-put :exec fn-octets$c-put :protect t)
            (fn-octets-rx-append-octet :logic fn-octets$a-append-octet
                                        :exec fn-octets$c-append-octet :protect t)
            (fn-octets-rx-clear :logic fn-octets$a-clear :exec fn-octets$c-clear)
            (fn-octets-rx-reserve :logic fn-octets$a-reserve :exec fn-octets$c-reserve
                                   :protect t)
            (fn-octets-rx-list :logic fn-octets$a-list :exec fn-octets$c-list)
            (fn-octets-rx-from-list :logic fn-octets$a-from-list
                                     :exec fn-octets$c-from-list :protect t)
            (fn-octets-rx-append-list :logic fn-octets$a-append-list
                                       :exec fn-oct-write-list :protect t)
            (fn-octets-rx-append-back :logic fn-octets$a-append-back
                                       :exec fn-octets$c-append-back :protect t)
            (fn-octets-rx-get-word :logic fn-octets$a-get-word :exec fn-octets$c-get-word)
            (fn-octets-rx-append-word :logic fn-octets$a-append-word
                                       :exec fn-octets$c-append-word :protect t))
  :congruent-to fn-octets)


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

(in-theory (disable fn-rxb-append-byte fn-rxb-layout-components))
