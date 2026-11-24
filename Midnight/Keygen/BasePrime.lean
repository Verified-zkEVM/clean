import CompPoly.Fields.PrattCertificate

/-! The BLS12-381 base field is prime: CompElliptic's short-Weierstrass curves need a field,
and CompPoly has only the scalar field. A Pratt certificate, checked by the kernel. -/

namespace Midnight.Keygen

/-- The BLS12-381 base-field characteristic. -/
def basePrime : Nat :=
  4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787

private theorem prime_51376543 : Nat.Prime 51376543 := by
  refine PrattCertificate'.out ⟨3, (by reduce_mod_char), ?_⟩
  refine .split [2, 3, 7, 151, 8101] (fun r hr => ?_) (by norm_num)
  simp at hr
  rcases hr with hr | hr | hr | hr | hr <;> subst r
  · exact .prime 2 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 7 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 151 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 8101 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)

private theorem prime_52437899 : Nat.Prime 52437899 := by
  refine PrattCertificate'.out ⟨2, (by reduce_mod_char), ?_⟩
  refine .split [2, 43, 609743] (fun r hr => ?_) (by norm_num)
  simp at hr
  rcases hr with hr | hr | hr <;> subst r
  · exact .prime 2 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 43 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 609743 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)

private theorem prime_475709467 : Nat.Prime 475709467 := by
  refine PrattCertificate'.out ⟨2, (by reduce_mod_char), ?_⟩
  refine .split [2, 3, 47, 1686913] (fun r hr => ?_) (by norm_num)
  simp at hr
  rcases hr with hr | hr | hr | hr <;> subst r
  · exact .prime 2 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 47 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 1686913 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)

private theorem prime_927093389 : Nat.Prime 927093389 := by
  refine PrattCertificate'.out ⟨3, (by reduce_mod_char), ?_⟩
  refine .split [2 ^ 2, 13, 409, 43591] (fun r hr => ?_) (by norm_num)
  simp at hr
  rcases hr with hr | hr | hr | hr <;> subst r
  · exact .prime 2 2 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 13 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 409 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 43591 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)

private theorem prime_13090036741 : Nat.Prime 13090036741 := by
  refine PrattCertificate'.out ⟨10, (by reduce_mod_char), ?_⟩
  refine .split [2 ^ 2, 3, 5, 11, 47, 421987] (fun r hr => ?_) (by norm_num)
  simp at hr
  rcases hr with hr | hr | hr | hr | hr | hr <;> subst r
  · exact .prime 2 2 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 5 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 11 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 47 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 421987 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)

private theorem prime_43670061551 : Nat.Prime 43670061551 := by
  refine PrattCertificate'.out ⟨7, (by reduce_mod_char), ?_⟩
  refine .split [2, 5 ^ 2, 17, 51376543] (fun r hr => ?_) (by norm_num)
  simp at hr
  rcases hr with hr | hr | hr | hr <;> subst r
  · exact .prime 2 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 5 2 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 17 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 51376543 1 _ prime_51376543
      (by reduce_mod_char; decide) (by norm_num)

private theorem prime_9272813673901 : Nat.Prime 9272813673901 := by
  refine PrattCertificate'.out ⟨2, (by reduce_mod_char), ?_⟩
  refine .split [2 ^ 2, 3, 5 ^ 2, 7, 7577, 582767] (fun r hr => ?_) (by norm_num)
  simp at hr
  rcases hr with hr | hr | hr | hr | hr | hr <;> subst r
  · exact .prime 2 2 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 5 2 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 7 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 7577 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 582767 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)

private theorem prime_64881703735777 : Nat.Prime 64881703735777 := by
  refine PrattCertificate'.out ⟨5, (by reduce_mod_char), ?_⟩
  refine .split [2 ^ 5, 3 ^ 7, 927093389] (fun r hr => ?_) (by norm_num)
  simp at hr
  rcases hr with hr | hr | hr <;> subst r
  · exact .prime 2 5 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3 7 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 927093389 1 _ prime_927093389
      (by reduce_mod_char; decide) (by norm_num)

private theorem prime_1928745244171409 : Nat.Prime 1928745244171409 := by
  refine PrattCertificate'.out ⟨3, (by reduce_mod_char), ?_⟩
  refine .split [2 ^ 4, 13, 9272813673901] (fun r hr => ?_) (by norm_num)
  simp at hr
  rcases hr with hr | hr | hr <;> subst r
  · exact .prime 2 4 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 13 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 9272813673901 1 _ prime_9272813673901
      (by reduce_mod_char; decide) (by norm_num)

private theorem prime_7259797099061183477 : Nat.Prime 7259797099061183477 := by
  refine PrattCertificate'.out ⟨2, (by reduce_mod_char), ?_⟩
  refine .split [2 ^ 2, 941, 1928745244171409] (fun r hr => ?_) (by norm_num)
  simp at hr
  rcases hr with hr | hr | hr <;> subst r
  · exact .prime 2 2 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 941 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 1928745244171409 1 _ prime_1928745244171409
      (by reduce_mod_char; decide) (by norm_num)

private theorem prime_2584487767265781317813 : Nat.Prime 2584487767265781317813 := by
  refine PrattCertificate'.out ⟨2, (by reduce_mod_char), ?_⟩
  refine .split [2 ^ 2, 89, 7259797099061183477] (fun r hr => ?_) (by norm_num)
  simp at hr
  rcases hr with hr | hr | hr <;> subst r
  · exact .prime 2 2 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 89 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 7259797099061183477 1 _ prime_7259797099061183477
      (by reduce_mod_char; decide) (by norm_num)

private theorem prime_3819663927398918131021 : Nat.Prime 3819663927398918131021 := by
  refine PrattCertificate'.out ⟨6, (by reduce_mod_char), ?_⟩
  refine .split [2 ^ 2, 3 ^ 2, 5, 19, 113, 755057, 13090036741] (fun r hr => ?_) (by norm_num)
  simp at hr
  rcases hr with hr | hr | hr | hr | hr | hr | hr <;> subst r
  · exact .prime 2 2 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3 2 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 5 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 19 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 113 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 755057 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 13090036741 1 _ prime_13090036741
      (by reduce_mod_char; decide) (by norm_num)

private theorem prime_92691255082156974996979 : Nat.Prime 92691255082156974996979 := by
  refine PrattCertificate'.out ⟨3, (by reduce_mod_char), ?_⟩
  refine .split [2, 3, 31, 467, 16447, 64881703735777] (fun r hr => ?_) (by norm_num)
  simp at hr
  rcases hr with hr | hr | hr | hr | hr | hr <;> subst r
  · exact .prime 2 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 31 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 467 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 16447 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 64881703735777 1 _ prime_64881703735777
      (by reduce_mod_char; decide) (by norm_num)

private theorem prime_1125266252156850182658904441386709967 : Nat.Prime 1125266252156850182658904441386709967 := by
  refine PrattCertificate'.out ⟨5, (by reduce_mod_char), ?_⟩
  refine .split [2, 3373, 43670061551, 3819663927398918131021] (fun r hr => ?_) (by norm_num)
  simp at hr
  rcases hr with hr | hr | hr | hr <;> subst r
  · exact .prime 2 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3373 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 43670061551 1 _ prime_43670061551
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3819663927398918131021 1 _ prime_3819663927398918131021
      (by reduce_mod_char; decide) (by norm_num)

private theorem prime_15778400344354997994418419698270088123916926905054652752758194827714659 : Nat.Prime 15778400344354997994418419698270088123916926905054652752758194827714659 := by
  refine PrattCertificate'.out ⟨2, (by reduce_mod_char), ?_⟩
  refine .split [2, 3, 53, 475709467, 92691255082156974996979, 1125266252156850182658904441386709967] (fun r hr => ?_) (by norm_num)
  simp at hr
  rcases hr with hr | hr | hr | hr | hr | hr <;> subst r
  · exact .prime 2 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 53 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 475709467 1 _ prime_475709467
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 92691255082156974996979 1 _ prime_92691255082156974996979
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 1125266252156850182658904441386709967 1 _ prime_1125266252156850182658904441386709967
      (by reduce_mod_char; decide) (by norm_num)

private theorem prime_4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787 : Nat.Prime 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787 := by
  refine PrattCertificate'.out ⟨2, (by reduce_mod_char), ?_⟩
  refine .split [2, 3 ^ 2, 11, 23, 47, 10177, 859267, 52437899, 2584487767265781317813, 15778400344354997994418419698270088123916926905054652752758194827714659] (fun r hr => ?_) (by norm_num)
  simp at hr
  rcases hr with hr | hr | hr | hr | hr | hr | hr | hr | hr | hr <;> subst r
  · exact .prime 2 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3 2 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 11 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 23 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 47 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 10177 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 859267 1 _ (by pratt)
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 52437899 1 _ prime_52437899
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 2584487767265781317813 1 _ prime_2584487767265781317813
      (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 15778400344354997994418419698270088123916926905054652752758194827714659 1 _ prime_15778400344354997994418419698270088123916926905054652752758194827714659
      (by reduce_mod_char; decide) (by norm_num)

theorem basePrime_prime : Nat.Prime basePrime := prime_4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787

instance : Fact (Nat.Prime basePrime) := ⟨basePrime_prime⟩

end Midnight.Keygen
