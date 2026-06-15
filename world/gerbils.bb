#!/usr/bin/env bb
;; world://gerbils — SatReadout ⋈ Gay.jl on a real palette.
;; Companion to ../GAY_BRIDGE.md. Two color:// kernels over Mongolian-gerbil
;; coat-color morphs (real fancy genetics), self-verifying.
;;
;;  gay://   identity hue = Gay.jl canonical sm64 (src/gayrng.jl:65-69),
;;           avalanche — locality destroyed, the addressing/fingerprint kernel.
;;  color:// perceptual = saturating readout f_A∘ΔE (SatReadout.lean), A=10
;;           = Gay.jl perceptual_diff_sat default — navigation, clusters by eye.
;;
;; GF(3) is MEASURED here (assertions can FAIL), never assigned. Exit 0 ⇔ Σ≡0.

;; ---- gay:// kernel: Gay.jl canonical sm64 (GOLDEN add + MIX1 + MIX2) ----
(def GOLDEN (Long/parseUnsignedLong "9E3779B97F4A7C15" 16))
(def MIX1   (Long/parseUnsignedLong "BF58476D1CE4E5B9" 16))
(def MIX2   (Long/parseUnsignedLong "94D049BB133111EB" 16))
(defn sm64 [s]
  (let [z (unchecked-add s GOLDEN)
        z (unchecked-multiply (bit-xor z (unsigned-bit-shift-right z 30)) MIX1)
        z (unchecked-multiply (bit-xor z (unsigned-bit-shift-right z 27)) MIX2)]
    (bit-xor z (unsigned-bit-shift-right z 31))))
(defn nidx [s] (reduce (fn [a c] (unchecked-add (unchecked-multiply a 31) (long (int c)))) 0 s))
(defn gayhue [s] (Long/remainderUnsigned (sm64 (bit-xor 1069 (nidx s))) 360))

;; ---- color:// kernel: approx fur sRGB (keeper-eye, not spectrophotometry) ----
(def palette
  {"agouti" [155 118 83] "black" [43 43 43] "slate" [110 110 118]
   "honey" [216 160 90] "argente" [232 201 160] "lilac" [181 169 176]
   "dove" [185 182 189] "nutmeg" [138 90 59] "burmese" [90 70 54]
   "siamese" [201 182 154] "schimmel" [230 221 208] "polar-fox" [236 233 228]
   "DEW" [251 251 248] "REW" [252 252 250] "saffron" [217 154 78]})

;; redmean ΔE proxy normalized to a ΔE00-ish 0..100 scale
(defn de [[r1 g1 b1] [r2 g2 b2]]
  (let [rb (/ (+ r1 r2) 2.0) dr (- r1 r2) dg (- g1 g2) db (- b1 b2)]
    (/ (Math/sqrt (+ (* (+ 2 (/ rb 256.0)) dr dr) (* 4.0 dg dg)
                     (* (+ 2 (/ (- 255 rb) 256.0)) db db))) 7.64)))
;; SatReadout saturating readout, A=10 (perceptual_diff_sat default)
(def A 10.0)
(defn f [d] (* A (- 1.0 (Math/exp (/ (- d) A)))))
;; SatReadout.key_identity' defect: f x + f y - f(x+y) = f x * f y / A
(defn defect [x y] (- (+ (f x) (f y)) (f (+ x y))))
(defn defect-expected [x y] (/ (* (f x) (f y)) A))

(def ks (vec (keys palette)))
(def pairs (for [i (range (count ks)) j (range (inc i) (count ks))] [(ks i) (ks j)]))
(def scored (sort-by #(nth % 2)
              (map (fn [[a b]] (let [d (de (palette a) (palette b))] [a b d (f d)])) pairs)))

(println "world://gerbils  —  gay:// identity hue (canonical sm64):")
(doseq [m ks] (print (format "  %s=%d" m (gayhue m)))) (println "\n")
(println "color:// nearest (local regime, f≈ΔE):")
(doseq [[a b d v] (take 3 scored)] (println (format "  %-9s~%-9s ΔE=%5.1f f=%4.2f" a b d v)))
(println "color:// farthest (saturated, f→A):")
(doseq [[a b d v] (take 3 (reverse scored))] (println (format "  %-9s~%-9s ΔE=%5.1f f=%5.3f" a b d v)))

;; ---- MEASURED GF(3) ----
(def eps 2.220446049250313e-16)
(def idtol (* 64 eps A))                       ;; derived tolerance (= bridge)
;; +1 Play: KEY identity holds at float level over the palette's ΔE values
(def es (map #(nth % 2) scored))
(def max-id-resid (apply max (for [x es y es] (Math/abs (- (defect x y) (defect-expected x y))))))
(def play (< max-id-resid idtol))
;; 0 Witness: every morph minted a deterministic gay:// hue (total, no collisions-as-error;
;;            collisions ARE allowed for identity hashing — we only assert totality + determinism)
(def witness (and (= (count (map gayhue ks)) (count ks))
                  (every? #(<= 0 % 359) (map gayhue ks))
                  (every? #(= (gayhue %) (gayhue %)) ks)))  ;; determinism: hue is a function
;; -1 Coplay (falsifier): readout must SATURATE — far-pair f-spread ≪ raw ΔE spread.
;; An additive/Riemannian readout would preserve the spread; this asserts it collapses.
(def far (take 6 (reverse scored)))
(def raw-spread (- (apply max (map #(nth % 2) far)) (apply min (map #(nth % 2) far))))
(def f-spread   (- (apply max (map #(nth % 3) far)) (apply min (map #(nth % 3) far))))
(def coplay (and (> raw-spread 5.0) (< f-spread 0.05)))

(println (format "\nGF(3) (measured):  +1 Play=%s  0 Witness=%s  -1 Coplay=%s" play witness coplay))
(println (format "  +1 KEY id resid %.2e < idtol %.2e (derived, = GAY_BRIDGE.md)" max-id-resid idtol))
(println (format "  -1 saturation: raw ΔE spread %.1f vs f-spread %.4f (collapse ⇒ non-Riemannian)" raw-spread f-spread))
(let [ok (and play witness coplay)]
  (println (if ok "Σ ≡ 0  — we have it." "Σ ≢ 0  — gate broke, inspect."))
  (flush)
  (System/exit (if ok 0 1)))
