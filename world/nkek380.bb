#!/usr/bin/env bb
;; NKEK +380 compliance gate — the TOP of the maintain/dial stack, grounded in
;; nkek.gov.ua's Національний план нумерації (наказ №758/2023) + the RF-blocklist
;; (Положення НКЕК №426/2023, додаток 1). Every gosip REGISTER/INVITE for a +380
;; number passes this first: valid E.164 structure, an ALLOCATED NDC, and NOT on
;; the Russian-Federation-allocated blocklist. Runnable/testable (pure logic).
;;
;; E.164 UA: +380 · NDC(2) · SN(7)  = "+380" + 9 digits.
(def GOLD (Long/parseUnsignedLong "9E3779B97F4A7C15" 16))
(def MIX1 (Long/parseUnsignedLong "BF58476D1CE4E5B9" 16))
(def MIX2 (Long/parseUnsignedLong "94D049BB133111EB" 16))
(defn sm64 [s] (let [z (unchecked-add s GOLD)
        z (unchecked-multiply (bit-xor z (unsigned-bit-shift-right z 30)) MIX1)
        z (unchecked-multiply (bit-xor z (unsigned-bit-shift-right z 27)) MIX2)]
    (bit-xor z (unsigned-bit-shift-right z 31))))
(defn hue [s] (Long/remainderUnsigned (sm64 (bit-xor 1069 (reduce (fn [a c] (unchecked-add (unchecked-multiply a 31) (long (int c)))) 0 s))) 360))

;; Mobile NDCs (operators: Kyivstar 67/68/96/97/98, Vodafone 50/66/95/99, lifecell 63/73/93, 3Mob/others)
(def mobile-ndc #{"39" "50" "63" "66" "67" "68" "73" "89" "91" "92" "93" "94" "95" "96" "97" "98" "99"})
;; Geographic NDCs (sample of real UA area codes per the plan — Kyiv 44, Lviv 32, Odesa 48, Kharkiv 57, Dnipro 56, …)
(def geo-ndc #{"44" "32" "48" "57" "56" "61" "62" "31" "33" "34" "35" "36" "37" "38" "41" "43" "45" "46" "47" "51" "52" "53" "54" "55" "58" "59" "64" "65" "69"})
;; NKEK RF-blocklist SAMPLE (placeholder for Положення №426 додаток 1 — codes the
;; RF allocated for occupied territories, ordered BLOCKED). Real list = the *.xls.
;; Encoded as NDC+prefix patterns; here a representative occupied-territory set.
;; Crimea occupied-territory area codes (0652 Simferopol, 0654 Yalta, 0692 Sevastopol)
;; that the RF re-allocated and NKEK orders BLOCKED — encoded as NDC+first-SN-digit.
;; These sit INSIDE allocated geographic NDCs (65/69), so they pass allocation yet
;; must still be refused. Sample only; authoritative list = NKEK №426 дод.1 *.xls.
(def rf-blocked-prefixes #{"652" "654" "692"})

(defn validate [num]
  (let [m (re-matches #"\+380(\d{2})(\d{7})" num)]
    (if (nil? m)
      {:num num :valid? false :kind :malformed :trit -1 :reason "not +380·NDC(2)·SN(7)"}
      (let [[_ ndc sn] m
            kind (cond (mobile-ndc ndc) :mobile (geo-ndc ndc) :geographic :else :unallocated)
            blocked? (boolean (rf-blocked-prefixes (str ndc (subs sn 0 1))))]
        (cond
          blocked?              {:num num :valid? false :kind kind :ndc ndc :trit -1 :reason "RF-blocklist (NKEK №426 дод.1) — REFUSE"}
          (= kind :unallocated) {:num num :valid? false :kind kind :ndc ndc :trit -1 :reason (str "NDC " ndc " not in National Numbering Plan")}
          :else                 {:num num :valid? true  :kind kind :ndc ndc :trit 0  :hue (hue num)
                                 :sip-user num :reason "compliant — clear to REGISTER/INVITE via gosip"})))))

(def tests ["+380501234567"   ; Vodafone mobile
            "+380671234567"   ; Kyivstar mobile
            "+380441234567"   ; Kyiv geographic
            "+380321234567"   ; Lviv geographic
            "+380652000000"   ; Simferopol 0652 — allocated NDC 65 BUT RF-blocked prefix → refuse
            "+380101234567"   ; NDC 10 unallocated
            "+38050123"       ; malformed (too short)
            "+15551234567"])  ; not Ukraine

(println "NKEK +380 compliance gate (top of the maintain/dial stack):")
(doseq [n tests]
  (let [r (validate n)]
    (println (format "  %-15s valid=%-5s kind=%-12s trit=%2d  %s%s"
                     (:num r) (:valid? r) (name (:kind r)) (:trit r)
                     (if (:hue r) (format "hue=%3d " (:hue r)) "")
                     (:reason r)))))
;; GF(3): the gate is the 0/witness leg. A clear number (0) hands to the dialer
;; (+1 INVITE/dialog via gosip) and the CDR/response reconciliation (-1 coplay).
(let [clear (filter #(:valid? (validate %)) tests)]
  (println (format "\n%d/%d clear to dial; %d refused (malformed/unallocated/RF-blocked)."
                   (count clear) (count tests) (- (count tests) (count clear))))
  (println "Σ-leg: NKEK-validate = 0 (witness) · gosip INVITE = +1 (generate) · response/CDR = -1 (coplay)."))
