/-
Poseidon reference vectors generated with iden3/circomlibjs.

Source commit: 48b3ab37013c5ed21e9ff8a80a5b010795c97094
Reference constants SHA-256: 354f31bbed9d9a8b884d8f2181e339cb425b6e3e4cc7240bd3dd22f0070f3f2c
Optimized constants SHA-256: da1b82330e196f931d30dd304b3ec547fe041c2fac2226c7204e286a5db27ed0
Inputs for arity n are [1, 2, ..., n].

DO NOT EDIT BY HAND. Regenerate with:
  node scripts/generate_poseidon_vectors.mjs --circomlibjs <checkout>
Check a generated file with the same command plus `--check`.
-/
module

public import Clean.Specs.PoseidonOptimized

public meta import Clean.Specs.PoseidonOptimized

@[expose] public section

namespace Specs.PoseidonOptimized

open Specs.Poseidon (F)

example : poseidon params_t5 #v[(1 : F), 2, 3, 4] =
    (18821383157269793795438455681495246036402687001665670618754263018637548127333 : F) := by
  native_decide

example : poseidon params_t6 #v[(1 : F), 2, 3, 4, 5] =
    (6183221330272524995739186171720101788151706631170188140075976616310159254464 : F) := by
  native_decide

example : poseidon params_t7 #v[(1 : F), 2, 3, 4, 5, 6] =
    (20400040500897583745843009878988256314335038853985262692600694741116813247201 : F) := by
  native_decide

example : poseidon params_t8 #v[(1 : F), 2, 3, 4, 5, 6, 7] =
    (12748163991115452309045839028154629052133952896122405799815156419278439301912 : F) := by
  native_decide

example : poseidon params_t9 #v[(1 : F), 2, 3, 4, 5, 6, 7, 8] =
    (18604317144381847857886385684060986177838410221561136253933256952257712543953 : F) := by
  native_decide

example : poseidon params_t10 #v[(1 : F), 2, 3, 4, 5, 6, 7, 8, 9] =
    (13589767895268936107593642967621470491511464502761040466226072462545218539640 : F) := by
  native_decide

example : poseidon params_t11 #v[(1 : F), 2, 3, 4, 5, 6, 7, 8, 9, 10] =
    (3657500514307717306974218405144578736633140001277925127187636780142269815841 : F) := by
  native_decide

example : poseidon params_t12 #v[(1 : F), 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] =
    (3572015662710076994097916907865950486270383304442561406230608893458731714472 : F) := by
  native_decide

example : poseidon params_t13 #v[(1 : F), 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] =
    (2501997477381648492950318384533644783248002172679259592360114615426357826485 : F) := by
  native_decide

example : poseidon params_t14 #v[(1 : F), 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] =
    (7041832639553862712666971417715061873827921493498355005117622707743491651590 : F) := by
  native_decide

example : poseidon params_t15 #v[(1 : F), 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] =
    (8354478399926161176778659061636406690034081872658507739535256090879947077494 : F) := by
  native_decide

example : poseidon params_t16 #v[(1 : F), 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] =
    (4203130618016961831408770638653325366880478848856764494148034853759773445968 : F) := by
  native_decide

example : poseidon params_t17 #v[(1 : F), 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] =
    (9989051620750914585850546081941653841776809718687451684622678807385399211877 : F) := by
  native_decide

end Specs.PoseidonOptimized
