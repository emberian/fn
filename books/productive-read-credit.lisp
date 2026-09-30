; Actual denied-credit read preserves queued submissions while closing.
; Source proof discovery only; complete removal teeth and qualification open.
(in-package "ACL2")
(include-book "owner-credits")

(defthm fn-pcr-denied-read-retains-every-queued-submission
 (let* ((r0 (fn-oas-read-span oc views id i end cache s slots fn-octets fn-arena fn-cat))
        (r1 (fn-mca-refused-read oc views id i end cache s fn-octets fn-arena fn-cat))
        (p (car (fn-mca-read-span credits oc views id i end cache s slots reserve
                                 fn-octets fn-arena fn-cat))))
  (implies
   (and (not (equal (car (fn-mcr-resize credits (fn-mca-conn-key id)
                          (fn-mca-need (fn-own-tls-result-owner r0) id reserve))) :ok))
        (not (equal (car (fn-mcr-resize credits (fn-mca-conn-key id)
                          (fn-mca-need (fn-own-tls-result-owner r1) id reserve))) :ok)))
   (and (equal (fn-own-queue (fn-ocfg-owner (fn-own-tls-result-owner p)))
               (fn-own-queue (fn-ocfg-owner oc)))
        (equal (fn-own-tls-result-effects p)
               (list (fn-nntp-reply-effect *fn-oas-busy-line*) (fn-nntp-close-effect)))
        (equal (fn-own-tls-result-consumed p) (- end i)))))
 :rule-classes nil
 :hints (("Goal" :in-theory
          (e/d (fn-mca-read-span fn-mca-shut-read)
               (fn-oas-read-span fn-mca-refused-read fn-mcr-resize fn-mca-need
                fn-mca-conn-key fn-oas-owner-closed)))))
