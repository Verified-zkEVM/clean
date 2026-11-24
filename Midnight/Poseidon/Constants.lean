import Midnight.Field

/-
Copyright (C) Midnight Foundation
SPDX-License-Identifier: Apache-2.0
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software distributed
under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
CONDITIONS OF ANY KIND, either express or implied. See the License for the
specific language governing permissions and limitations under the License.

Canonical constants transcribed from circuits/src/hash/poseidon/constants/blstrs.rs
at midnight-zk 1e39c120d05200373285fba0e69766e40292b470.
Each Rust `Fq::from_raw([a,b,c,d])` is the canonical integer
`a + 2^64*b + 2^128*c + 2^192*d`, converted to Midnight.F here.
These are public algorithm constants, never extracted from a keygen capture.
Source file SHA256: 17832d6a7c806945dd87d52d92e282065a26cd5e8b1e83dab40bf4e6e48a43af
Parameter generation described by upstream:
  sage generate_parameters_grain.sage 1 0 255 3 8 60
    0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
-/
namespace Midnight.Poseidon

def width : Nat := 3
def circuitSkips : Nat := 5

def mdsNat : Array (Array Nat) := #[
  #[0x1b8114c381b922fd5d6d241210e2d8a68ad5744053ba9e776118de4107b51ace, 0x3df32e4cc4cb2ed20e5d21899cf5331775990ccaec4c09b4e3717213fcc0d763, 0x3f05c4df7a6664dabe258779bf548eb4007f33601591080b3ecd34aea0e1edc1],
  #[0x404d21073985d14e432a4ad76d3fae06ca74314b950fe7b1d7f501cd31a8b374, 0x0b2cc8704264c6bd81bc620e9e524d4b73e9b2317679422ff7fa1603955649f1, 0x0fdf664da55059fa5a9388c641035d496d0bb519834348b4e2a8fc8c637f1a1f],
  #[0x5e1d3dbecda6214343e24a47f45c5d033197ad01b65a730af95dc57e90c49140, 0x6bd72f9cfc53af9d931896e77ea5c61244cb6d5fae8954f37dc7b9002f5aa78a, 0x4997c5aa3a5fa07bcaf880a9054bef831effbd9cd58e46d9bb4fb88ef99de0db]
]

def mds : Array (Array F) := mdsNat.map (·.map (fun (n : Nat) => (n : F)))

end Midnight.Poseidon
