(local
 (defthm fn-lgk-pipe-kernel-take-keeps-representation
   (equal (fn-lgk-pipe-countedp
           (cadr (fn-lgk-pipe-kernel-take ks record txid count octets bmax omax unit)))
          (fn-lgk-pipe-countedp ks))
   :hints (("Goal" :in-theory
            (e/d (fn-lgk-pipe-kernel-take fn-lgk-pipe-countedp fn-lgc-take fn-olr-take
                    fn-lgc-prepare fn-lgk-prepare fn-lgc-make fn-lgk-make
                    fn-lgc-count fn-lgk-committed nth)
             (fn-olr-entry-octets fn-lgk-next-txid fn-lgk-phase
              fn-lgc-next-txid fn-lgc-phase fn-lg-pack-len))))))
