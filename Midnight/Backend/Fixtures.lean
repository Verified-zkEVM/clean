import Midnight.Configuration

/-! Frozen configurations, independent of the Clean frontend and the backend. Each is the `CS`
that a direct `ConfigM` port of the Rust `configure` produced at commit a96290a87, printed as a
literal; `Backend.Checks` compares the compiled frontend programs with these. -/
namespace Midnight.Backend.Fixtures
open Midnight.Keygen

/-- `SHA256.configured`: `ZkStdLib::configure`, default architecture plus sha2_256. -/
def sha256 : CS :=
  { numFixed := 16,
    numAdvice := 8,
    numInstance := 2,
    numSelectors := 16,
    adviceQueries :=
      #[(0, 0),
        (1, 0),
        (2, 0),
        (3, 0),
        (4, 0),
        (0, 1),
        (1, 1),
        (2, 1),
        (5, 0),
        (6, 0),
        (7, 0),
        (3, (-1)),
        (4, (-1)),
        (0, (-1)),
        (1, (-1)),
        (3, 1),
        (4, 1),
        (6, (-1)),
        (6, 1),
        (2, (-1)),
        (7, (-1)),
        (5, (-1)),
        (5, 1),
        (7, 1)],
    fixedQueries :=
      #[(9, 0),
        (4, 0),
        (5, 0),
        (6, 0),
        (7, 0),
        (8, 0),
        (0, 0),
        (1, 0),
        (2, 0),
        (3, 0),
        (10, 0),
        (11, 0),
        (12, 0),
        (13, 0),
        (14, 0),
        (15, 0)],
    instanceQueries := #[(0, 0), (1, 0)],
    permutation :=
      #[⟨.fixed, 9⟩,
        ⟨.advice, 0⟩,
        ⟨.advice, 1⟩,
        ⟨.advice, 2⟩,
        ⟨.advice, 3⟩,
        ⟨.advice, 4⟩,
        ⟨.instance, 0⟩,
        ⟨.instance, 1⟩,
        ⟨.advice, 5⟩],
    constantColumns := #[],
    gates :=
      #[{ name := "arith_gate",
          selector := ⟨0, true⟩,
          queries :=
            #[(.advice ⟨0⟩ 0),
              (.advice ⟨1⟩ 0),
              (.advice ⟨2⟩ 0),
              (.advice ⟨3⟩ 0),
              (.advice ⟨4⟩ 0),
              (.advice ⟨0⟩ 1),
              (.fixed ⟨4⟩ 0),
              (.fixed ⟨5⟩ 0),
              (.fixed ⟨6⟩ 0),
              (.fixed ⟨7⟩ 0),
              (.fixed ⟨8⟩ 0),
              (.fixed ⟨0⟩ 0),
              (.fixed ⟨1⟩ 0),
              (.fixed ⟨2⟩ 0),
              (.fixed ⟨3⟩ 0)],
          constraints :=
            #[("",
                (.add
                 (.add
                  (.add
                   (.add
                    (.add
                     (.add
                      (.add
                       (.add
                        (.var (.fixed ⟨3⟩ 0))
                        (.mul (.var (.fixed ⟨4⟩ 0)) (.var (.advice ⟨0⟩ 0))))
                       (.mul (.var (.fixed ⟨5⟩ 0)) (.var (.advice ⟨1⟩ 0))))
                      (.mul (.var (.fixed ⟨6⟩ 0)) (.var (.advice ⟨2⟩ 0))))
                     (.mul (.var (.fixed ⟨7⟩ 0)) (.var (.advice ⟨3⟩ 0))))
                    (.mul (.var (.fixed ⟨8⟩ 0)) (.var (.advice ⟨4⟩ 0))))
                   (.mul (.var (.fixed ⟨0⟩ 0)) (.var (.advice ⟨0⟩ 1))))
                  (.mul
                   (.mul (.var (.fixed ⟨1⟩ 0)) (.var (.advice ⟨0⟩ 0)))
                   (.var (.advice ⟨1⟩ 0))))
                 (.mul
                  (.mul (.var (.fixed ⟨2⟩ 0)) (.var (.advice ⟨0⟩ 0)))
                  (.var (.advice ⟨2⟩ 0)))))],
          raw := false,
          rows := false },
        { name := "12_minus_34",
          selector := ⟨1, true⟩,
          queries := #[(.advice ⟨1⟩ 0), (.advice ⟨2⟩ 0), (.advice ⟨3⟩ 0), (.advice ⟨4⟩ 0)],
          constraints :=
            #[("",
                (.add
                 (.add
                  (.add (.var (.advice ⟨1⟩ 0)) (.var (.advice ⟨2⟩ 0)))
                  (.mul
                   (.const
                    52435875175126190479447740508185965837690552500527637822603658699938581184512)
                   (.var (.advice ⟨3⟩ 0))))
                 (.mul
                  (.const
                   52435875175126190479447740508185965837690552500527637822603658699938581184512)
                  (.var (.advice ⟨4⟩ 0)))))],
          raw := false,
          rows := false },
        { name := "parallel_add_gate",
          selector := ⟨2, true⟩,
          queries :=
            #[(.advice ⟨0⟩ 0),
              (.advice ⟨0⟩ 1),
              (.fixed ⟨4⟩ 0),
              (.advice ⟨1⟩ 0),
              (.advice ⟨1⟩ 1),
              (.fixed ⟨5⟩ 0),
              (.advice ⟨2⟩ 0),
              (.advice ⟨2⟩ 1),
              (.fixed ⟨6⟩ 0)],
          constraints :=
            #[("",
                (.add
                 (.add (.var (.advice ⟨0⟩ 0)) (.var (.fixed ⟨4⟩ 0)))
                 (.mul
                  (.const
                   52435875175126190479447740508185965837690552500527637822603658699938581184512)
                  (.var (.advice ⟨0⟩ 1))))),
              ("",
                (.add
                 (.add (.var (.advice ⟨1⟩ 0)) (.var (.fixed ⟨5⟩ 0)))
                 (.mul
                  (.const
                   52435875175126190479447740508185965837690552500527637822603658699938581184512)
                  (.var (.advice ⟨1⟩ 1))))),
              ("",
                (.add
                 (.add (.var (.advice ⟨2⟩ 0)) (.var (.fixed ⟨6⟩ 0)))
                 (.mul
                  (.const
                   52435875175126190479447740508185965837690552500527637822603658699938581184512)
                  (.var (.advice ⟨2⟩ 1)))))],
          raw := false,
          rows := false },
        { name := "Maj(A, B, C)",
          selector := ⟨5, true⟩,
          queries :=
            #[(.advice ⟨3⟩ (-1)),
              (.advice ⟨4⟩ (-1)),
              (.advice ⟨3⟩ 0),
              (.advice ⟨0⟩ (-1)),
              (.advice ⟨0⟩ 0),
              (.advice ⟨0⟩ 1),
              (.advice ⟨1⟩ (-1)),
              (.advice ⟨1⟩ 0),
              (.advice ⟨1⟩ 1)],
          constraints :=
            #[("Maj",
                (.add
                 (.add
                  (.add (.var (.advice ⟨3⟩ (-1))) (.var (.advice ⟨4⟩ (-1))))
                  (.var (.advice ⟨3⟩ 0)))
                 (.mul
                  (.const
                   52435875175126190479447740508185965837690552500527637822603658699938581184512)
                  (.add
                   (.add
                    (.add
                     (.mul (.const 4398046511104) (.var (.advice ⟨1⟩ (-1))))
                     (.mul (.const 1048576) (.var (.advice ⟨1⟩ 0))))
                    (.var (.advice ⟨1⟩ 1)))
                   (.mul
                    (.const 2)
                    (.add
                     (.add
                      (.mul (.const 4398046511104) (.var (.advice ⟨0⟩ (-1))))
                      (.mul (.const 1048576) (.var (.advice ⟨0⟩ 0))))
                     (.var (.advice ⟨0⟩ 1))))))))],
          raw := false,
          rows := false },
        { name := "half Ch(E, F, G)",
          selector := ⟨6, true⟩,
          queries :=
            #[(.advice ⟨3⟩ (-1)),
              (.advice ⟨4⟩ (-1)),
              (.advice ⟨0⟩ (-1)),
              (.advice ⟨0⟩ 0),
              (.advice ⟨0⟩ 1),
              (.advice ⟨1⟩ (-1)),
              (.advice ⟨1⟩ 0),
              (.advice ⟨1⟩ 1),
              (.advice ⟨2⟩ 0),
              (.advice ⟨3⟩ 0),
              (.advice ⟨4⟩ 0)],
          constraints :=
            #[("Half-Ch spreadded",
                (.add
                 (.add (.var (.advice ⟨3⟩ (-1))) (.var (.advice ⟨4⟩ (-1))))
                 (.mul
                  (.const
                   52435875175126190479447740508185965837690552500527637822603658699938581184512)
                  (.add
                   (.add
                    (.add
                     (.mul (.const 4398046511104) (.var (.advice ⟨1⟩ (-1))))
                     (.mul (.const 1048576) (.var (.advice ⟨1⟩ 0))))
                    (.var (.advice ⟨1⟩ 1)))
                   (.mul
                    (.const 2)
                    (.add
                     (.add
                      (.mul (.const 4398046511104) (.var (.advice ⟨0⟩ (-1))))
                      (.mul (.const 1048576) (.var (.advice ⟨0⟩ 0))))
                     (.var (.advice ⟨0⟩ 1)))))))),
              ("Half Ch sum (2 terms)",
                (.add
                 (.add (.var (.advice ⟨2⟩ 0)) (.var (.advice ⟨3⟩ 0)))
                 (.mul
                  (.const
                   52435875175126190479447740508185965837690552500527637822603658699938581184512)
                  (.var (.advice ⟨4⟩ 0)))))],
          raw := false,
          rows := false },
        { name := "Σ₀(A)",
          selector := ⟨7, true⟩,
          queries :=
            #[(.advice ⟨3⟩ (-1)),
              (.advice ⟨4⟩ (-1)),
              (.advice ⟨3⟩ 0),
              (.advice ⟨4⟩ 0),
              (.advice ⟨0⟩ (-1)),
              (.advice ⟨0⟩ 0),
              (.advice ⟨0⟩ 1),
              (.advice ⟨1⟩ (-1)),
              (.advice ⟨1⟩ 0),
              (.advice ⟨1⟩ 1)],
          constraints :=
            #[("Sigma_0",
                (.add
                 (.add
                  (.add
                   (.add
                    (.add
                     (.add
                      (.mul (.const 1152921504606846976) (.var (.advice ⟨4⟩ 0)))
                      (.mul (.const 1099511627776) (.var (.advice ⟨3⟩ (-1)))))
                     (.mul (.const 4194304) (.var (.advice ⟨4⟩ (-1)))))
                    (.var (.advice ⟨3⟩ 0)))
                   (.add
                    (.add
                     (.add
                      (.mul (.const 4398046511104) (.var (.advice ⟨3⟩ 0)))
                      (.mul (.const 274877906944) (.var (.advice ⟨4⟩ 0))))
                     (.mul (.const 262144) (.var (.advice ⟨3⟩ (-1)))))
                    (.var (.advice ⟨4⟩ (-1)))))
                  (.add
                   (.add
                    (.add
                     (.mul (.const 70368744177664) (.var (.advice ⟨4⟩ (-1))))
                     (.mul (.const 16777216) (.var (.advice ⟨3⟩ 0))))
                    (.mul (.const 1048576) (.var (.advice ⟨4⟩ 0))))
                   (.var (.advice ⟨3⟩ (-1)))))
                 (.mul
                  (.const
                   52435875175126190479447740508185965837690552500527637822603658699938581184512)
                  (.add
                   (.add
                    (.add
                     (.mul (.const 4398046511104) (.var (.advice ⟨0⟩ (-1))))
                     (.mul (.const 1048576) (.var (.advice ⟨0⟩ 0))))
                    (.var (.advice ⟨0⟩ 1)))
                   (.mul
                    (.const 2)
                    (.add
                     (.add
                      (.mul (.const 4398046511104) (.var (.advice ⟨1⟩ (-1))))
                      (.mul (.const 1048576) (.var (.advice ⟨1⟩ 0))))
                     (.var (.advice ⟨1⟩ 1))))))))],
          raw := false,
          rows := false },
        { name := "Σ₁(E)",
          selector := ⟨8, true⟩,
          queries :=
            #[(.advice ⟨3⟩ (-1)),
              (.advice ⟨4⟩ (-1)),
              (.advice ⟨3⟩ 0),
              (.advice ⟨4⟩ 0),
              (.advice ⟨3⟩ 1),
              (.advice ⟨0⟩ (-1)),
              (.advice ⟨0⟩ 0),
              (.advice ⟨0⟩ 1),
              (.advice ⟨1⟩ (-1)),
              (.advice ⟨1⟩ 0),
              (.advice ⟨1⟩ 1)],
          constraints :=
            #[("Sigma_1",
                (.add
                 (.add
                  (.add
                   (.add
                    (.add
                     (.add
                      (.add
                       (.mul (.const 4503599627370496) (.var (.advice ⟨3⟩ 1)))
                       (.mul (.const 274877906944) (.var (.advice ⟨3⟩ (-1)))))
                      (.mul (.const 16384) (.var (.advice ⟨4⟩ (-1)))))
                     (.mul (.const 1024) (.var (.advice ⟨3⟩ 0))))
                    (.var (.advice ⟨4⟩ 0)))
                   (.add
                    (.add
                     (.add
                      (.add
                       (.mul (.const 18014398509481984) (.var (.advice ⟨4⟩ 0)))
                       (.mul (.const 4398046511104) (.var (.advice ⟨3⟩ 1))))
                      (.mul (.const 268435456) (.var (.advice ⟨3⟩ (-1)))))
                     (.mul (.const 16) (.var (.advice ⟨4⟩ (-1)))))
                    (.var (.advice ⟨3⟩ 0))))
                  (.add
                   (.add
                    (.add
                     (.add
                      (.mul (.const 1099511627776) (.var (.advice ⟨4⟩ (-1))))
                      (.mul (.const 68719476736) (.var (.advice ⟨3⟩ 0))))
                     (.mul (.const 67108864) (.var (.advice ⟨4⟩ 0))))
                    (.mul (.const 16384) (.var (.advice ⟨3⟩ 1))))
                   (.var (.advice ⟨3⟩ (-1)))))
                 (.mul
                  (.const
                   52435875175126190479447740508185965837690552500527637822603658699938581184512)
                  (.add
                   (.add
                    (.add
                     (.mul (.const 4398046511104) (.var (.advice ⟨0⟩ (-1))))
                     (.mul (.const 1048576) (.var (.advice ⟨0⟩ 0))))
                    (.var (.advice ⟨0⟩ 1)))
                   (.mul
                    (.const 2)
                    (.add
                     (.add
                      (.mul (.const 4398046511104) (.var (.advice ⟨1⟩ (-1))))
                      (.mul (.const 1048576) (.var (.advice ⟨1⟩ 0))))
                     (.var (.advice ⟨1⟩ 1))))))))],
          raw := false,
          rows := false },
        { name := "σ₀(W)",
          selector := ⟨9, true⟩,
          queries :=
            #[(.advice ⟨3⟩ (-1)),
              (.advice ⟨4⟩ (-1)),
              (.advice ⟨2⟩ 0),
              (.advice ⟨3⟩ 0),
              (.advice ⟨4⟩ 0),
              (.advice ⟨2⟩ 1),
              (.advice ⟨3⟩ 1),
              (.advice ⟨4⟩ 1),
              (.advice ⟨0⟩ (-1)),
              (.advice ⟨0⟩ 0),
              (.advice ⟨0⟩ 1),
              (.advice ⟨1⟩ (-1)),
              (.advice ⟨1⟩ 0),
              (.advice ⟨1⟩ 1)],
          constraints :=
            #[("sigma_0",
                (.add
                 (.add
                  (.add
                   (.add
                    (.add
                     (.add
                      (.add
                       (.add
                        (.add
                         (.mul (.const 17179869184) (.var (.advice ⟨3⟩ (-1))))
                         (.mul (.const 4294967296) (.var (.advice ⟨4⟩ (-1)))))
                        (.mul (.const 1073741824) (.var (.advice ⟨2⟩ 0))))
                       (.mul (.const 268435456) (.var (.advice ⟨3⟩ 0))))
                      (.mul (.const 16384) (.var (.advice ⟨4⟩ 0))))
                     (.mul (.const 256) (.var (.advice ⟨2⟩ 1))))
                    (.var (.advice ⟨3⟩ 1)))
                   (.add
                    (.add
                     (.add
                      (.add
                       (.add
                        (.add
                         (.add
                          (.mul (.const 72057594037927936) (.var (.advice ⟨3⟩ 1)))
                          (.mul (.const 1125899906842624) (.var (.advice ⟨4⟩ 1))))
                         (.mul (.const 67108864) (.var (.advice ⟨3⟩ (-1)))))
                        (.mul (.const 16777216) (.var (.advice ⟨4⟩ (-1)))))
                       (.mul (.const 4194304) (.var (.advice ⟨2⟩ 0))))
                      (.mul (.const 1048576) (.var (.advice ⟨3⟩ 0))))
                     (.mul (.const 64) (.var (.advice ⟨4⟩ 0))))
                    (.var (.advice ⟨2⟩ 1))))
                  (.add
                   (.add
                    (.add
                     (.add
                      (.add
                       (.add
                        (.add
                         (.mul (.const 4611686018427387904) (.var (.advice ⟨3⟩ 0)))
                         (.mul (.const 281474976710656) (.var (.advice ⟨4⟩ 0))))
                        (.mul (.const 4398046511104) (.var (.advice ⟨2⟩ 1))))
                       (.mul (.const 17179869184) (.var (.advice ⟨3⟩ 1))))
                      (.mul (.const 268435456) (.var (.advice ⟨4⟩ 1))))
                     (.mul (.const 16) (.var (.advice ⟨3⟩ (-1)))))
                    (.mul (.const 4) (.var (.advice ⟨4⟩ (-1)))))
                   (.var (.advice ⟨2⟩ 0))))
                 (.mul
                  (.const
                   52435875175126190479447740508185965837690552500527637822603658699938581184512)
                  (.add
                   (.add
                    (.add
                     (.mul (.const 4398046511104) (.var (.advice ⟨0⟩ (-1))))
                     (.mul (.const 1048576) (.var (.advice ⟨0⟩ 0))))
                    (.var (.advice ⟨0⟩ 1)))
                   (.mul
                    (.const 2)
                    (.add
                     (.add
                      (.mul (.const 4398046511104) (.var (.advice ⟨1⟩ (-1))))
                      (.mul (.const 1048576) (.var (.advice ⟨1⟩ 0))))
                     (.var (.advice ⟨1⟩ 1))))))))],
          raw := false,
          rows := false },
        { name := "σ₁(W)",
          selector := ⟨10, true⟩,
          queries :=
            #[(.advice ⟨3⟩ (-1)),
              (.advice ⟨4⟩ (-1)),
              (.advice ⟨2⟩ 0),
              (.advice ⟨3⟩ 0),
              (.advice ⟨4⟩ 0),
              (.advice ⟨2⟩ 1),
              (.advice ⟨3⟩ 1),
              (.advice ⟨4⟩ 1),
              (.advice ⟨0⟩ (-1)),
              (.advice ⟨0⟩ 0),
              (.advice ⟨0⟩ 1),
              (.advice ⟨1⟩ (-1)),
              (.advice ⟨1⟩ 0),
              (.advice ⟨1⟩ 1)],
          constraints :=
            #[("sigma_1",
                (.add
                 (.add
                  (.add
                   (.add
                    (.add
                     (.add
                      (.add
                       (.mul (.const 1048576) (.var (.advice ⟨3⟩ (-1))))
                       (.mul (.const 262144) (.var (.advice ⟨4⟩ (-1)))))
                      (.mul (.const 65536) (.var (.advice ⟨2⟩ 0))))
                     (.mul (.const 16384) (.var (.advice ⟨3⟩ 0))))
                    (.var (.advice ⟨4⟩ 0)))
                   (.add
                    (.add
                     (.add
                      (.add
                       (.add
                        (.add
                         (.add
                          (.mul (.const 1125899906842624) (.var (.advice ⟨4⟩ 0)))
                          (.mul (.const 17592186044416) (.var (.advice ⟨2⟩ 1))))
                         (.mul (.const 68719476736) (.var (.advice ⟨3⟩ 1))))
                        (.mul (.const 1073741824) (.var (.advice ⟨4⟩ 1))))
                       (.mul (.const 64) (.var (.advice ⟨3⟩ (-1)))))
                      (.mul (.const 16) (.var (.advice ⟨4⟩ (-1)))))
                     (.mul (.const 4) (.var (.advice ⟨2⟩ 0))))
                    (.var (.advice ⟨3⟩ 0))))
                  (.add
                   (.add
                    (.add
                     (.add
                      (.add
                       (.add
                        (.add
                         (.mul (.const 4611686018427387904) (.var (.advice ⟨2⟩ 0)))
                         (.mul (.const 1152921504606846976) (.var (.advice ⟨3⟩ 0))))
                        (.mul (.const 70368744177664) (.var (.advice ⟨4⟩ 0))))
                       (.mul (.const 1099511627776) (.var (.advice ⟨2⟩ 1))))
                      (.mul (.const 4294967296) (.var (.advice ⟨3⟩ 1))))
                     (.mul (.const 67108864) (.var (.advice ⟨4⟩ 1))))
                    (.mul (.const 4) (.var (.advice ⟨3⟩ (-1)))))
                   (.var (.advice ⟨4⟩ (-1)))))
                 (.mul
                  (.const
                   52435875175126190479447740508185965837690552500527637822603658699938581184512)
                  (.add
                   (.add
                    (.add
                     (.mul (.const 4398046511104) (.var (.advice ⟨0⟩ (-1))))
                     (.mul (.const 1048576) (.var (.advice ⟨0⟩ 0))))
                    (.var (.advice ⟨0⟩ 1)))
                   (.mul
                    (.const 2)
                    (.add
                     (.add
                      (.mul (.const 4398046511104) (.var (.advice ⟨1⟩ (-1))))
                      (.mul (.const 1048576) (.var (.advice ⟨1⟩ 0))))
                     (.var (.advice ⟨1⟩ 1))))))))],
          raw := false,
          rows := false },
        { name := "11-11-10 decomposition",
          selector := ⟨11, true⟩,
          queries := #[(.advice ⟨6⟩ (-1)), (.advice ⟨6⟩ 0), (.advice ⟨6⟩ 1), (.advice ⟨2⟩ (-1))],
          constraints :=
            #[("11-11-10 decomposition",
                (.add
                 (.add
                  (.add
                   (.mul (.const 2097152) (.var (.advice ⟨6⟩ (-1))))
                   (.mul (.const 1024) (.var (.advice ⟨6⟩ 0))))
                  (.var (.advice ⟨6⟩ 1)))
                 (.mul
                  (.const
                   52435875175126190479447740508185965837690552500527637822603658699938581184512)
                  (.var (.advice ⟨2⟩ (-1))))))],
          raw := false,
          rows := false },
        { name := "10-9-11-2 decomposition",
          selector := ⟨12, true⟩,
          queries :=
            #[(.advice ⟨6⟩ (-1)),
              (.advice ⟨7⟩ (-1)),
              (.advice ⟨6⟩ 0),
              (.advice ⟨7⟩ 0),
              (.advice ⟨0⟩ (-1)),
              (.advice ⟨1⟩ (-1)),
              (.advice ⟨0⟩ 0),
              (.advice ⟨1⟩ 0),
              (.advice ⟨2⟩ (-1)),
              (.advice ⟨2⟩ 0)],
          constraints :=
            #[("10_9_11_2 decomposition plain",
                (.add
                 (.add
                  (.add
                   (.add
                    (.mul (.const 4194304) (.var (.advice ⟨6⟩ (-1))))
                    (.mul (.const 8192) (.var (.advice ⟨7⟩ (-1)))))
                   (.mul (.const 4) (.var (.advice ⟨6⟩ 0))))
                  (.var (.advice ⟨7⟩ 0)))
                 (.mul
                  (.const
                   52435875175126190479447740508185965837690552500527637822603658699938581184512)
                  (.var (.advice ⟨2⟩ (-1)))))),
              ("10_9_11_2 decomposition sprdd",
                (.add
                 (.add
                  (.add
                   (.add
                    (.mul (.const 17592186044416) (.var (.advice ⟨0⟩ (-1))))
                    (.mul (.const 67108864) (.var (.advice ⟨1⟩ (-1)))))
                   (.mul (.const 16) (.var (.advice ⟨0⟩ 0))))
                  (.var (.advice ⟨1⟩ 0)))
                 (.mul
                  (.const
                   52435875175126190479447740508185965837690552500527637822603658699938581184512)
                  (.var (.advice ⟨2⟩ 0)))))],
          raw := false,
          rows := false },
        { name := "7-12-2-5-6 decomposition",
          selector := ⟨13, true⟩,
          queries :=
            #[(.advice ⟨6⟩ (-1)),
              (.advice ⟨7⟩ (-1)),
              (.advice ⟨6⟩ 0),
              (.advice ⟨7⟩ 0),
              (.advice ⟨6⟩ 1),
              (.advice ⟨0⟩ (-1)),
              (.advice ⟨1⟩ (-1)),
              (.advice ⟨0⟩ 0),
              (.advice ⟨1⟩ 0),
              (.advice ⟨0⟩ 1),
              (.advice ⟨2⟩ (-1)),
              (.advice ⟨2⟩ 0)],
          constraints :=
            #[("7_12_2_5_6 decomposition plain",
                (.add
                 (.add
                  (.add
                   (.add
                    (.add
                     (.mul (.const 33554432) (.var (.advice ⟨6⟩ (-1))))
                     (.mul (.const 8192) (.var (.advice ⟨7⟩ (-1)))))
                    (.mul (.const 2048) (.var (.advice ⟨6⟩ 0))))
                   (.mul (.const 64) (.var (.advice ⟨7⟩ 0))))
                  (.var (.advice ⟨6⟩ 1)))
                 (.mul
                  (.const
                   52435875175126190479447740508185965837690552500527637822603658699938581184512)
                  (.var (.advice ⟨2⟩ (-1)))))),
              ("7_12_2_5_6 decomposition sprdd",
                (.add
                 (.add
                  (.add
                   (.add
                    (.add
                     (.mul (.const 1125899906842624) (.var (.advice ⟨0⟩ (-1))))
                     (.mul (.const 67108864) (.var (.advice ⟨1⟩ (-1)))))
                    (.mul (.const 4194304) (.var (.advice ⟨0⟩ 0))))
                   (.mul (.const 4096) (.var (.advice ⟨1⟩ 0))))
                  (.var (.advice ⟨0⟩ 1)))
                 (.mul
                  (.const
                   52435875175126190479447740508185965837690552500527637822603658699938581184512)
                  (.var (.advice ⟨2⟩ 0)))))],
          raw := false,
          rows := false },
        { name := "12-1x3-7-3-4-3 decomposition",
          selector := ⟨14, true⟩,
          queries :=
            #[(.advice ⟨6⟩ (-1)),
              (.advice ⟨7⟩ (-1)),
              (.advice ⟨6⟩ 0),
              (.advice ⟨7⟩ 0),
              (.advice ⟨6⟩ 1),
              (.advice ⟨5⟩ (-1)),
              (.advice ⟨5⟩ 0),
              (.advice ⟨5⟩ 1),
              (.advice ⟨2⟩ (-1))],
          constraints :=
            #[("12_1x3_7_3_4_3 decomposition ",
                (.add
                 (.add
                  (.add
                   (.add
                    (.add
                     (.add
                      (.add
                       (.add
                        (.mul (.const 1048576) (.var (.advice ⟨6⟩ (-1))))
                        (.mul (.const 524288) (.var (.advice ⟨5⟩ (-1)))))
                       (.mul (.const 262144) (.var (.advice ⟨5⟩ 0))))
                      (.mul (.const 131072) (.var (.advice ⟨5⟩ 1))))
                     (.mul (.const 1024) (.var (.advice ⟨7⟩ (-1)))))
                    (.mul (.const 128) (.var (.advice ⟨6⟩ 0))))
                   (.mul (.const 8) (.var (.advice ⟨7⟩ 0))))
                  (.var (.advice ⟨6⟩ 1)))
                 (.mul
                  (.const
                   52435875175126190479447740508185965837690552500527637822603658699938581184512)
                  (.var (.advice ⟨2⟩ (-1)))))),
              ("W.1a 1-bit check",
                (.mul
                 (.var (.advice ⟨5⟩ (-1)))
                 (.add
                  (.var (.advice ⟨5⟩ (-1)))
                  (.mul
                   (.const
                    52435875175126190479447740508185965837690552500527637822603658699938581184512)
                   (.const 1))))),
              ("W.1b 1-bit check",
                (.mul
                 (.var (.advice ⟨5⟩ 0))
                 (.add
                  (.var (.advice ⟨5⟩ 0))
                  (.mul
                   (.const
                    52435875175126190479447740508185965837690552500527637822603658699938581184512)
                   (.const 1))))),
              ("W.1c 1-bit check",
                (.mul
                 (.var (.advice ⟨5⟩ 1))
                 (.add
                  (.var (.advice ⟨5⟩ 1))
                  (.mul
                   (.const
                    52435875175126190479447740508185965837690552500527637822603658699938581184512)
                   (.const 1)))))],
          raw := false,
          rows := false },
        { name := "add mod 2^32",
          selector := ⟨15, true⟩,
          queries :=
            #[(.advice ⟨3⟩ (-1)),
              (.advice ⟨4⟩ (-1)),
              (.advice ⟨3⟩ 0),
              (.advice ⟨4⟩ 0),
              (.advice ⟨2⟩ 1),
              (.advice ⟨3⟩ 1),
              (.advice ⟨4⟩ 1),
              (.advice ⟨7⟩ 1),
              (.advice ⟨2⟩ (-1))],
          constraints :=
            #[("add_mod_2_32",
                (.add
                 (.add
                  (.add
                   (.add
                    (.add
                     (.add
                      (.add (.var (.advice ⟨3⟩ (-1))) (.var (.advice ⟨4⟩ (-1))))
                      (.var (.advice ⟨3⟩ 0)))
                     (.var (.advice ⟨4⟩ 0)))
                    (.var (.advice ⟨2⟩ 1)))
                   (.var (.advice ⟨3⟩ 1)))
                  (.var (.advice ⟨4⟩ 1)))
                 (.mul
                  (.const
                   52435875175126190479447740508185965837690552500527637822603658699938581184512)
                  (.add
                   (.var (.advice ⟨2⟩ (-1)))
                   (.mul (.var (.advice ⟨7⟩ 1)) (.mul (.const 4294967296) (.const 1)))))))],
          raw := false,
          rows := false }],
    lookups :=
      #[{ name := "pow2range column check",
          selector := (.var (.selector ⟨3, false⟩)),
          inputs := #[#[(.var (.fixed ⟨10⟩ 0)), (.var (.advice ⟨1⟩ 0))]],
          table := #[(.var (.fixed ⟨11⟩ 0)), (.var (.fixed ⟨12⟩ 0))] },
        { name := "plain-spreaded lookup",
          selector := (.var (.selector ⟨4, false⟩)),
          inputs :=
            #[#[(.var (.fixed ⟨0⟩ 0)), (.var (.advice ⟨6⟩ 0)), (.var (.advice ⟨0⟩ 0))],
              #[(.var (.fixed ⟨1⟩ 0)), (.var (.advice ⟨7⟩ 0)), (.var (.advice ⟨1⟩ 0))]],
          table := #[(.var (.fixed ⟨13⟩ 0)), (.var (.fixed ⟨14⟩ 0)), (.var (.fixed ⟨15⟩ 0))] }],
    trashcans := #[],
    currentQueries :=
      #[(.advice ⟨3⟩ (-1)),
        (.advice ⟨4⟩ (-1)),
        (.advice ⟨3⟩ 0),
        (.advice ⟨4⟩ 0),
        (.advice ⟨2⟩ 1),
        (.advice ⟨3⟩ 1),
        (.advice ⟨4⟩ 1),
        (.advice ⟨7⟩ 1),
        (.advice ⟨2⟩ (-1))],
    lookupClosures :=
      #[({ name := "pow2range column check",
            selector := (.var (.selector ⟨3, false⟩)),
            inputs := #[#[(.var (.fixed ⟨10⟩ 0)), (.var (.advice ⟨1⟩ 0))]],
            table := #[(.var (.fixed ⟨11⟩ 0)), (.var (.fixed ⟨12⟩ 0))] },
          #[(.fixed ⟨10⟩ 0), (.advice ⟨1⟩ 0)],
          false),
        ({ name := "plain-spreaded lookup",
            selector := (.var (.selector ⟨4, false⟩)),
            inputs :=
              #[#[(.var (.fixed ⟨0⟩ 0)), (.var (.advice ⟨6⟩ 0)), (.var (.advice ⟨0⟩ 0))],
                #[(.var (.fixed ⟨1⟩ 0)), (.var (.advice ⟨7⟩ 0)), (.var (.advice ⟨1⟩ 0))]],
            table := #[(.var (.fixed ⟨13⟩ 0)), (.var (.fixed ⟨14⟩ 0)), (.var (.fixed ⟨15⟩ 0))] },
          #[(.fixed ⟨0⟩ 0),
            (.fixed ⟨1⟩ 0),
            (.advice ⟨6⟩ 0),
            (.advice ⟨7⟩ 0),
            (.advice ⟨0⟩ 0),
            (.advice ⟨1⟩ 0)],
          false)],
    rejectedLookups := #[],
    gateClosures :=
      #[("arith_gate",
          #[(.advice ⟨0⟩ 0),
            (.advice ⟨1⟩ 0),
            (.advice ⟨2⟩ 0),
            (.advice ⟨3⟩ 0),
            (.advice ⟨4⟩ 0),
            (.advice ⟨0⟩ 1),
            (.fixed ⟨4⟩ 0),
            (.fixed ⟨5⟩ 0),
            (.fixed ⟨6⟩ 0),
            (.fixed ⟨7⟩ 0),
            (.fixed ⟨8⟩ 0),
            (.fixed ⟨0⟩ 0),
            (.fixed ⟨1⟩ 0),
            (.fixed ⟨2⟩ 0),
            (.fixed ⟨3⟩ 0)],
          #[(.advice ⟨0⟩ 0),
            (.advice ⟨1⟩ 0),
            (.advice ⟨2⟩ 0),
            (.advice ⟨3⟩ 0),
            (.advice ⟨4⟩ 0),
            (.advice ⟨0⟩ 1),
            (.fixed ⟨4⟩ 0),
            (.fixed ⟨5⟩ 0),
            (.fixed ⟨6⟩ 0),
            (.fixed ⟨7⟩ 0),
            (.fixed ⟨8⟩ 0),
            (.fixed ⟨0⟩ 0),
            (.fixed ⟨1⟩ 0),
            (.fixed ⟨2⟩ 0),
            (.fixed ⟨3⟩ 0)],
          true),
        ("12_minus_34",
          #[(.advice ⟨1⟩ 0), (.advice ⟨2⟩ 0), (.advice ⟨3⟩ 0), (.advice ⟨4⟩ 0)],
          #[(.advice ⟨1⟩ 0), (.advice ⟨2⟩ 0), (.advice ⟨3⟩ 0), (.advice ⟨4⟩ 0)],
          true),
        ("parallel_add_gate",
          #[(.advice ⟨0⟩ 0),
            (.advice ⟨0⟩ 1),
            (.fixed ⟨4⟩ 0),
            (.advice ⟨1⟩ 0),
            (.advice ⟨1⟩ 1),
            (.fixed ⟨5⟩ 0),
            (.advice ⟨2⟩ 0),
            (.advice ⟨2⟩ 1),
            (.fixed ⟨6⟩ 0)],
          #[(.advice ⟨0⟩ 0),
            (.advice ⟨0⟩ 1),
            (.fixed ⟨4⟩ 0),
            (.advice ⟨1⟩ 0),
            (.advice ⟨1⟩ 1),
            (.fixed ⟨5⟩ 0),
            (.advice ⟨2⟩ 0),
            (.advice ⟨2⟩ 1),
            (.fixed ⟨6⟩ 0)],
          true),
        ("Maj(A, B, C)",
          #[(.advice ⟨3⟩ (-1)),
            (.advice ⟨4⟩ (-1)),
            (.advice ⟨3⟩ 0),
            (.advice ⟨0⟩ (-1)),
            (.advice ⟨0⟩ 0),
            (.advice ⟨0⟩ 1),
            (.advice ⟨1⟩ (-1)),
            (.advice ⟨1⟩ 0),
            (.advice ⟨1⟩ 1)],
          #[(.advice ⟨3⟩ (-1)),
            (.advice ⟨4⟩ (-1)),
            (.advice ⟨3⟩ 0),
            (.advice ⟨0⟩ (-1)),
            (.advice ⟨0⟩ 0),
            (.advice ⟨0⟩ 1),
            (.advice ⟨1⟩ (-1)),
            (.advice ⟨1⟩ 0),
            (.advice ⟨1⟩ 1)],
          true),
        ("half Ch(E, F, G)",
          #[(.advice ⟨3⟩ (-1)),
            (.advice ⟨4⟩ (-1)),
            (.advice ⟨0⟩ (-1)),
            (.advice ⟨0⟩ 0),
            (.advice ⟨0⟩ 1),
            (.advice ⟨1⟩ (-1)),
            (.advice ⟨1⟩ 0),
            (.advice ⟨1⟩ 1),
            (.advice ⟨2⟩ 0),
            (.advice ⟨3⟩ 0),
            (.advice ⟨4⟩ 0)],
          #[(.advice ⟨3⟩ (-1)),
            (.advice ⟨4⟩ (-1)),
            (.advice ⟨0⟩ (-1)),
            (.advice ⟨0⟩ 0),
            (.advice ⟨0⟩ 1),
            (.advice ⟨1⟩ (-1)),
            (.advice ⟨1⟩ 0),
            (.advice ⟨1⟩ 1),
            (.advice ⟨2⟩ 0),
            (.advice ⟨3⟩ 0),
            (.advice ⟨4⟩ 0)],
          true),
        ("Σ₀(A)",
          #[(.advice ⟨3⟩ (-1)),
            (.advice ⟨4⟩ (-1)),
            (.advice ⟨3⟩ 0),
            (.advice ⟨4⟩ 0),
            (.advice ⟨0⟩ (-1)),
            (.advice ⟨0⟩ 0),
            (.advice ⟨0⟩ 1),
            (.advice ⟨1⟩ (-1)),
            (.advice ⟨1⟩ 0),
            (.advice ⟨1⟩ 1)],
          #[(.advice ⟨3⟩ (-1)),
            (.advice ⟨4⟩ (-1)),
            (.advice ⟨3⟩ 0),
            (.advice ⟨4⟩ 0),
            (.advice ⟨0⟩ (-1)),
            (.advice ⟨0⟩ 0),
            (.advice ⟨0⟩ 1),
            (.advice ⟨1⟩ (-1)),
            (.advice ⟨1⟩ 0),
            (.advice ⟨1⟩ 1)],
          true),
        ("Σ₁(E)",
          #[(.advice ⟨3⟩ (-1)),
            (.advice ⟨4⟩ (-1)),
            (.advice ⟨3⟩ 0),
            (.advice ⟨4⟩ 0),
            (.advice ⟨3⟩ 1),
            (.advice ⟨0⟩ (-1)),
            (.advice ⟨0⟩ 0),
            (.advice ⟨0⟩ 1),
            (.advice ⟨1⟩ (-1)),
            (.advice ⟨1⟩ 0),
            (.advice ⟨1⟩ 1)],
          #[(.advice ⟨3⟩ (-1)),
            (.advice ⟨4⟩ (-1)),
            (.advice ⟨3⟩ 0),
            (.advice ⟨4⟩ 0),
            (.advice ⟨3⟩ 1),
            (.advice ⟨0⟩ (-1)),
            (.advice ⟨0⟩ 0),
            (.advice ⟨0⟩ 1),
            (.advice ⟨1⟩ (-1)),
            (.advice ⟨1⟩ 0),
            (.advice ⟨1⟩ 1)],
          true),
        ("σ₀(W)",
          #[(.advice ⟨3⟩ (-1)),
            (.advice ⟨4⟩ (-1)),
            (.advice ⟨2⟩ 0),
            (.advice ⟨3⟩ 0),
            (.advice ⟨4⟩ 0),
            (.advice ⟨2⟩ 1),
            (.advice ⟨3⟩ 1),
            (.advice ⟨4⟩ 1),
            (.advice ⟨0⟩ (-1)),
            (.advice ⟨0⟩ 0),
            (.advice ⟨0⟩ 1),
            (.advice ⟨1⟩ (-1)),
            (.advice ⟨1⟩ 0),
            (.advice ⟨1⟩ 1)],
          #[(.advice ⟨3⟩ (-1)),
            (.advice ⟨4⟩ (-1)),
            (.advice ⟨2⟩ 0),
            (.advice ⟨3⟩ 0),
            (.advice ⟨4⟩ 0),
            (.advice ⟨2⟩ 1),
            (.advice ⟨3⟩ 1),
            (.advice ⟨4⟩ 1),
            (.advice ⟨0⟩ (-1)),
            (.advice ⟨0⟩ 0),
            (.advice ⟨0⟩ 1),
            (.advice ⟨1⟩ (-1)),
            (.advice ⟨1⟩ 0),
            (.advice ⟨1⟩ 1)],
          true),
        ("σ₁(W)",
          #[(.advice ⟨3⟩ (-1)),
            (.advice ⟨4⟩ (-1)),
            (.advice ⟨2⟩ 0),
            (.advice ⟨3⟩ 0),
            (.advice ⟨4⟩ 0),
            (.advice ⟨2⟩ 1),
            (.advice ⟨3⟩ 1),
            (.advice ⟨4⟩ 1),
            (.advice ⟨0⟩ (-1)),
            (.advice ⟨0⟩ 0),
            (.advice ⟨0⟩ 1),
            (.advice ⟨1⟩ (-1)),
            (.advice ⟨1⟩ 0),
            (.advice ⟨1⟩ 1)],
          #[(.advice ⟨3⟩ (-1)),
            (.advice ⟨4⟩ (-1)),
            (.advice ⟨2⟩ 0),
            (.advice ⟨3⟩ 0),
            (.advice ⟨4⟩ 0),
            (.advice ⟨2⟩ 1),
            (.advice ⟨3⟩ 1),
            (.advice ⟨4⟩ 1),
            (.advice ⟨0⟩ (-1)),
            (.advice ⟨0⟩ 0),
            (.advice ⟨0⟩ 1),
            (.advice ⟨1⟩ (-1)),
            (.advice ⟨1⟩ 0),
            (.advice ⟨1⟩ 1)],
          true),
        ("11-11-10 decomposition",
          #[(.advice ⟨6⟩ (-1)), (.advice ⟨6⟩ 0), (.advice ⟨6⟩ 1), (.advice ⟨2⟩ (-1))],
          #[(.advice ⟨6⟩ (-1)), (.advice ⟨6⟩ 0), (.advice ⟨6⟩ 1), (.advice ⟨2⟩ (-1))],
          true),
        ("10-9-11-2 decomposition",
          #[(.advice ⟨6⟩ (-1)),
            (.advice ⟨7⟩ (-1)),
            (.advice ⟨6⟩ 0),
            (.advice ⟨7⟩ 0),
            (.advice ⟨0⟩ (-1)),
            (.advice ⟨1⟩ (-1)),
            (.advice ⟨0⟩ 0),
            (.advice ⟨1⟩ 0),
            (.advice ⟨2⟩ (-1)),
            (.advice ⟨2⟩ 0)],
          #[(.advice ⟨6⟩ (-1)),
            (.advice ⟨7⟩ (-1)),
            (.advice ⟨6⟩ 0),
            (.advice ⟨7⟩ 0),
            (.advice ⟨0⟩ (-1)),
            (.advice ⟨1⟩ (-1)),
            (.advice ⟨0⟩ 0),
            (.advice ⟨1⟩ 0),
            (.advice ⟨2⟩ (-1)),
            (.advice ⟨2⟩ 0)],
          true),
        ("7-12-2-5-6 decomposition",
          #[(.advice ⟨6⟩ (-1)),
            (.advice ⟨7⟩ (-1)),
            (.advice ⟨6⟩ 0),
            (.advice ⟨7⟩ 0),
            (.advice ⟨6⟩ 1),
            (.advice ⟨0⟩ (-1)),
            (.advice ⟨1⟩ (-1)),
            (.advice ⟨0⟩ 0),
            (.advice ⟨1⟩ 0),
            (.advice ⟨0⟩ 1),
            (.advice ⟨2⟩ (-1)),
            (.advice ⟨2⟩ 0)],
          #[(.advice ⟨6⟩ (-1)),
            (.advice ⟨7⟩ (-1)),
            (.advice ⟨6⟩ 0),
            (.advice ⟨7⟩ 0),
            (.advice ⟨6⟩ 1),
            (.advice ⟨0⟩ (-1)),
            (.advice ⟨1⟩ (-1)),
            (.advice ⟨0⟩ 0),
            (.advice ⟨1⟩ 0),
            (.advice ⟨0⟩ 1),
            (.advice ⟨2⟩ (-1)),
            (.advice ⟨2⟩ 0)],
          true),
        ("12-1x3-7-3-4-3 decomposition",
          #[(.advice ⟨6⟩ (-1)),
            (.advice ⟨7⟩ (-1)),
            (.advice ⟨6⟩ 0),
            (.advice ⟨7⟩ 0),
            (.advice ⟨6⟩ 1),
            (.advice ⟨5⟩ (-1)),
            (.advice ⟨5⟩ 0),
            (.advice ⟨5⟩ 1),
            (.advice ⟨2⟩ (-1))],
          #[(.advice ⟨6⟩ (-1)),
            (.advice ⟨7⟩ (-1)),
            (.advice ⟨6⟩ 0),
            (.advice ⟨7⟩ 0),
            (.advice ⟨6⟩ 1),
            (.advice ⟨5⟩ (-1)),
            (.advice ⟨5⟩ 0),
            (.advice ⟨5⟩ 1),
            (.advice ⟨2⟩ (-1))],
          true),
        ("add mod 2^32",
          #[(.advice ⟨3⟩ (-1)),
            (.advice ⟨4⟩ (-1)),
            (.advice ⟨3⟩ 0),
            (.advice ⟨4⟩ 0),
            (.advice ⟨2⟩ 1),
            (.advice ⟨3⟩ 1),
            (.advice ⟨4⟩ 1),
            (.advice ⟨7⟩ 1),
            (.advice ⟨2⟩ (-1))],
          #[(.advice ⟨3⟩ (-1)),
            (.advice ⟨4⟩ (-1)),
            (.advice ⟨3⟩ 0),
            (.advice ⟨4⟩ 0),
            (.advice ⟨2⟩ 1),
            (.advice ⟨3⟩ 1),
            (.advice ⟨4⟩ 1),
            (.advice ⟨7⟩ 1),
            (.advice ⟨2⟩ (-1))],
          true)],
    prunedFrom := #[],
    selectorKinds :=
      #[true,
        true,
        true,
        false,
        false,
        true,
        true,
        true,
        true,
        true,
        true,
        true,
        true,
        true,
        true,
        true],
    minimumDegree := none,
    selectorFixedStart := none,
    errors := #[] }

/-- `Poseidon.configured`: the Poseidon-only architecture. -/
def poseidon : CS :=
  { numFixed := 13,
    numAdvice := 8,
    numInstance := 2,
    numSelectors := 6,
    adviceQueries :=
      #[(0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (0, 1), (1, 1), (2, 1), (5, 0), (6, 0), (7, 0)],
    fixedQueries :=
      #[(9, 0),
        (4, 0),
        (5, 0),
        (6, 0),
        (7, 0),
        (8, 0),
        (0, 0),
        (1, 0),
        (2, 0),
        (3, 0),
        (10, 0),
        (11, 0),
        (12, 0)],
    instanceQueries := #[(0, 0), (1, 0)],
    permutation :=
      #[⟨.fixed, 9⟩,
        ⟨.advice, 0⟩,
        ⟨.advice, 1⟩,
        ⟨.advice, 2⟩,
        ⟨.advice, 3⟩,
        ⟨.advice, 4⟩,
        ⟨.instance, 0⟩,
        ⟨.instance, 1⟩],
    constantColumns := #[],
    gates :=
      #[{ name := "arith_gate",
          selector := ⟨0, true⟩,
          queries :=
            #[(.advice ⟨0⟩ 0),
              (.advice ⟨1⟩ 0),
              (.advice ⟨2⟩ 0),
              (.advice ⟨3⟩ 0),
              (.advice ⟨4⟩ 0),
              (.advice ⟨0⟩ 1),
              (.fixed ⟨4⟩ 0),
              (.fixed ⟨5⟩ 0),
              (.fixed ⟨6⟩ 0),
              (.fixed ⟨7⟩ 0),
              (.fixed ⟨8⟩ 0),
              (.fixed ⟨0⟩ 0),
              (.fixed ⟨1⟩ 0),
              (.fixed ⟨2⟩ 0),
              (.fixed ⟨3⟩ 0)],
          constraints :=
            #[("",
                (.add
                 (.add
                  (.add
                   (.add
                    (.add
                     (.add
                      (.add
                       (.add
                        (.var (.fixed ⟨3⟩ 0))
                        (.mul (.var (.fixed ⟨4⟩ 0)) (.var (.advice ⟨0⟩ 0))))
                       (.mul (.var (.fixed ⟨5⟩ 0)) (.var (.advice ⟨1⟩ 0))))
                      (.mul (.var (.fixed ⟨6⟩ 0)) (.var (.advice ⟨2⟩ 0))))
                     (.mul (.var (.fixed ⟨7⟩ 0)) (.var (.advice ⟨3⟩ 0))))
                    (.mul (.var (.fixed ⟨8⟩ 0)) (.var (.advice ⟨4⟩ 0))))
                   (.mul (.var (.fixed ⟨0⟩ 0)) (.var (.advice ⟨0⟩ 1))))
                  (.mul
                   (.mul (.var (.fixed ⟨1⟩ 0)) (.var (.advice ⟨0⟩ 0)))
                   (.var (.advice ⟨1⟩ 0))))
                 (.mul
                  (.mul (.var (.fixed ⟨2⟩ 0)) (.var (.advice ⟨0⟩ 0)))
                  (.var (.advice ⟨2⟩ 0)))))],
          raw := false,
          rows := false },
        { name := "12_minus_34",
          selector := ⟨1, true⟩,
          queries := #[(.advice ⟨1⟩ 0), (.advice ⟨2⟩ 0), (.advice ⟨3⟩ 0), (.advice ⟨4⟩ 0)],
          constraints :=
            #[("",
                (.add
                 (.add
                  (.add (.var (.advice ⟨1⟩ 0)) (.var (.advice ⟨2⟩ 0)))
                  (.mul
                   (.const
                    52435875175126190479447740508185965837690552500527637822603658699938581184512)
                   (.var (.advice ⟨3⟩ 0))))
                 (.mul
                  (.const
                   52435875175126190479447740508185965837690552500527637822603658699938581184512)
                  (.var (.advice ⟨4⟩ 0)))))],
          raw := false,
          rows := false },
        { name := "parallel_add_gate",
          selector := ⟨2, true⟩,
          queries :=
            #[(.advice ⟨0⟩ 0),
              (.advice ⟨0⟩ 1),
              (.fixed ⟨4⟩ 0),
              (.advice ⟨1⟩ 0),
              (.advice ⟨1⟩ 1),
              (.fixed ⟨5⟩ 0),
              (.advice ⟨2⟩ 0),
              (.advice ⟨2⟩ 1),
              (.fixed ⟨6⟩ 0)],
          constraints :=
            #[("",
                (.add
                 (.add (.var (.advice ⟨0⟩ 0)) (.var (.fixed ⟨4⟩ 0)))
                 (.mul
                  (.const
                   52435875175126190479447740508185965837690552500527637822603658699938581184512)
                  (.var (.advice ⟨0⟩ 1))))),
              ("",
                (.add
                 (.add (.var (.advice ⟨1⟩ 0)) (.var (.fixed ⟨5⟩ 0)))
                 (.mul
                  (.const
                   52435875175126190479447740508185965837690552500527637822603658699938581184512)
                  (.var (.advice ⟨1⟩ 1))))),
              ("",
                (.add
                 (.add (.var (.advice ⟨2⟩ 0)) (.var (.fixed ⟨6⟩ 0)))
                 (.mul
                  (.const
                   52435875175126190479447740508185965837690552500527637822603658699938581184512)
                  (.var (.advice ⟨2⟩ 1)))))],
          raw := false,
          rows := false },
        { name := "full_round_gate",
          selector := ⟨4, true⟩,
          queries :=
            #[(.advice ⟨0⟩ 0),
              (.advice ⟨3⟩ 0),
              (.advice ⟨1⟩ 0),
              (.advice ⟨4⟩ 0),
              (.advice ⟨2⟩ 0),
              (.advice ⟨5⟩ 0),
              (.advice ⟨0⟩ 1),
              (.advice ⟨1⟩ 1),
              (.advice ⟨2⟩ 1),
              (.fixed ⟨0⟩ 0),
              (.fixed ⟨1⟩ 0),
              (.fixed ⟨2⟩ 0)],
          constraints :=
            #[("",
                (.add
                 (.mul
                  (.var (.advice ⟨0⟩ 0))
                  (.mul (.var (.advice ⟨0⟩ 0)) (.var (.advice ⟨0⟩ 0))))
                 (.mul
                  (.const
                   52435875175126190479447740508185965837690552500527637822603658699938581184512)
                  (.var (.advice ⟨3⟩ 0))))),
              ("",
                (.add
                 (.mul
                  (.var (.advice ⟨1⟩ 0))
                  (.mul (.var (.advice ⟨1⟩ 0)) (.var (.advice ⟨1⟩ 0))))
                 (.mul
                  (.const
                   52435875175126190479447740508185965837690552500527637822603658699938581184512)
                  (.var (.advice ⟨4⟩ 0))))),
              ("",
                (.add
                 (.mul
                  (.var (.advice ⟨2⟩ 0))
                  (.mul (.var (.advice ⟨2⟩ 0)) (.var (.advice ⟨2⟩ 0))))
                 (.mul
                  (.const
                   52435875175126190479447740508185965837690552500527637822603658699938581184512)
                  (.var (.advice ⟨5⟩ 0))))),
              ("",
                (.add
                 (.add
                  (.add
                   (.add
                    (.var (.fixed ⟨0⟩ 0))
                    (.mul
                     (.const
                      52435875175126190479447740508185965837690552500527637822603658699938581184512)
                     (.var (.advice ⟨0⟩ 1))))
                   (.mul
                    (.const
                     12440513488882586407557540066179884648646530011544707182889396930153310132942)
                    (.mul
                     (.mul (.var (.advice ⟨0⟩ 0)) (.var (.advice ⟨0⟩ 0)))
                     (.var (.advice ⟨3⟩ 0)))))
                  (.mul
                   (.const
                    28020747150333089913259220781304558809551608596314918030152947066915898054499)
                   (.mul
                    (.mul (.var (.advice ⟨1⟩ 0)) (.var (.advice ⟨1⟩ 0)))
                    (.var (.advice ⟨4⟩ 0)))))
                 (.mul
                  (.const
                   28505902463311974130913002774524928623644005505993681602486681565155683331521)
                  (.mul
                   (.mul (.var (.advice ⟨2⟩ 0)) (.var (.advice ⟨2⟩ 0)))
                   (.var (.advice ⟨5⟩ 0)))))),
              ("",
                (.add
                 (.add
                  (.add
                   (.add
                    (.var (.fixed ⟨1⟩ 0))
                    (.mul
                     (.const
                      52435875175126190479447740508185965837690552500527637822603658699938581184512)
                     (.var (.advice ⟨1⟩ 1))))
                   (.mul
                    (.const
                     29084297485723905200880885323289986130569887053242706304266829364413965316980)
                    (.mul
                     (.mul (.var (.advice ⟨0⟩ 0)) (.var (.advice ⟨0⟩ 0)))
                     (.var (.advice ⟨3⟩ 0)))))
                  (.mul
                   (.const
                    5054565981041632243581284853746902850980503096245579875276544410572564089329)
                   (.mul
                    (.mul (.var (.advice ⟨1⟩ 0)) (.var (.advice ⟨1⟩ 0)))
                    (.var (.advice ⟨4⟩ 0)))))
                 (.mul
                  (.const
                   7179405695647424344643177657798954274869382720335107962712222495241823787551)
                  (.mul
                   (.mul (.var (.advice ⟨2⟩ 0)) (.var (.advice ⟨2⟩ 0)))
                   (.var (.advice ⟨5⟩ 0)))))),
              ("",
                (.add
                 (.add
                  (.add
                   (.add
                    (.var (.fixed ⟨2⟩ 0))
                    (.mul
                     (.const
                      52435875175126190479447740508185965837690552500527637822603658699938581184512)
                     (.var (.advice ⟨2⟩ 1))))
                   (.mul
                    (.const
                     42569072482279996318031820844820583094661593761988851871644829917446303682880)
                    (.mul
                     (.mul (.var (.advice ⟨0⟩ 0)) (.var (.advice ⟨0⟩ 0)))
                     (.var (.advice ⟨3⟩ 0)))))
                  (.mul
                   (.const
                    48777675531739959342114240072267441286903816384223937749440830379544192657290)
                   (.mul
                    (.mul (.var (.advice ⟨1⟩ 0)) (.var (.advice ⟨1⟩ 0)))
                    (.var (.advice ⟨4⟩ 0)))))
                 (.mul
                  (.const
                   33286996086728685078854749126251163286167502628080690207063928367301359689947)
                  (.mul
                   (.mul (.var (.advice ⟨2⟩ 0)) (.var (.advice ⟨2⟩ 0)))
                   (.var (.advice ⟨5⟩ 0))))))],
          raw := false,
          rows := false },
        { name := "partial_round_gate",
          selector := ⟨5, false⟩,
          queries :=
            #[(.advice ⟨0⟩ 0),
              (.advice ⟨1⟩ 0),
              (.advice ⟨2⟩ 0),
              (.advice ⟨3⟩ 0),
              (.advice ⟨4⟩ 0),
              (.advice ⟨5⟩ 0),
              (.advice ⟨6⟩ 0),
              (.advice ⟨7⟩ 0),
              (.fixed ⟨0⟩ 0),
              (.fixed ⟨1⟩ 0),
              (.fixed ⟨2⟩ 0),
              (.fixed ⟨3⟩ 0),
              (.fixed ⟨4⟩ 0),
              (.fixed ⟨5⟩ 0),
              (.fixed ⟨6⟩ 0),
              (.fixed ⟨7⟩ 0),
              (.advice ⟨0⟩ 1),
              (.advice ⟨1⟩ 1),
              (.advice ⟨2⟩ 1)],
          constraints := #[],
          raw := false,
          rows := false }],
    lookups :=
      #[{ name := "pow2range column check",
          selector := (.var (.selector ⟨3, false⟩)),
          inputs := #[#[(.var (.fixed ⟨10⟩ 0)), (.var (.advice ⟨1⟩ 0))]],
          table := #[(.var (.fixed ⟨11⟩ 0)), (.var (.fixed ⟨12⟩ 0))] }],
    trashcans :=
      #[{ name := "partial_round_gate",
          selector := ⟨5, false⟩,
          queries :=
            #[(.advice ⟨0⟩ 0),
              (.advice ⟨1⟩ 0),
              (.advice ⟨2⟩ 0),
              (.advice ⟨3⟩ 0),
              (.advice ⟨4⟩ 0),
              (.advice ⟨5⟩ 0),
              (.advice ⟨6⟩ 0),
              (.advice ⟨7⟩ 0),
              (.fixed ⟨0⟩ 0),
              (.fixed ⟨1⟩ 0),
              (.fixed ⟨2⟩ 0),
              (.fixed ⟨3⟩ 0),
              (.fixed ⟨4⟩ 0),
              (.fixed ⟨5⟩ 0),
              (.fixed ⟨6⟩ 0),
              (.fixed ⟨7⟩ 0),
              (.advice ⟨0⟩ 1),
              (.advice ⟨1⟩ 1),
              (.advice ⟨2⟩ 1)],
          constraints :=
            #[("",
                (.add
                 (.add
                  (.var (.fixed ⟨0⟩ 0))
                  (.mul
                   (.const
                    52435875175126190479447740508185965837690552500527637822603658699938581184512)
                   (.var (.advice ⟨0⟩ 1))))
                 (.add
                  (.add
                   (.add
                    (.add
                     (.add
                      (.add
                       (.add
                        (.mul
                         (.const
                      40276410782279108334863105369904789343040261455045516584779277825615697839985)
                         (.var (.advice ⟨0⟩ 0)))
                        (.mul
                         (.const
                      37527016513455530468277088833539226510789135770417315120855317098742889359215)
                         (.var (.advice ⟨1⟩ 0))))
                       (.mul
                        (.const
                      23990009175532390848383686641478884818239121606019298540653394434675622011304)
                        (.mul
                         (.var (.advice ⟨2⟩ 0))
                         (.mul
                          (.mul (.var (.advice ⟨2⟩ 0)) (.var (.advice ⟨2⟩ 0)))
                          (.mul (.var (.advice ⟨2⟩ 0)) (.var (.advice ⟨2⟩ 0)))))))
                      (.mul
                       (.const
                      23180151978504326669680984036118508621180775988903922469131210268215350444530)
                       (.mul
                        (.var (.advice ⟨3⟩ 0))
                        (.mul
                         (.mul (.var (.advice ⟨3⟩ 0)) (.var (.advice ⟨3⟩ 0)))
                         (.mul (.var (.advice ⟨3⟩ 0)) (.var (.advice ⟨3⟩ 0)))))))
                     (.mul
                      (.const
                      29479126442377740792305085857437384138015409209423896273007595542837761281189)
                      (.mul
                       (.var (.advice ⟨4⟩ 0))
                       (.mul
                        (.mul (.var (.advice ⟨4⟩ 0)) (.var (.advice ⟨4⟩ 0)))
                        (.mul (.var (.advice ⟨4⟩ 0)) (.var (.advice ⟨4⟩ 0)))))))
                    (.mul
                     (.const
                      37990615931907094420184937091556956528876595328335061740913699785965517240590)
                     (.mul
                      (.var (.advice ⟨5⟩ 0))
                      (.mul
                       (.mul (.var (.advice ⟨5⟩ 0)) (.var (.advice ⟨5⟩ 0)))
                       (.mul (.var (.advice ⟨5⟩ 0)) (.var (.advice ⟨5⟩ 0)))))))
                   (.mul
                    (.const
                     3075540889646953729606836824147910283102396481803053667698778232583469493556)
                    (.mul
                     (.var (.advice ⟨6⟩ 0))
                     (.mul
                      (.mul (.var (.advice ⟨6⟩ 0)) (.var (.advice ⟨6⟩ 0)))
                      (.mul (.var (.advice ⟨6⟩ 0)) (.var (.advice ⟨6⟩ 0)))))))
                  (.mul
                   (.const
                    28505902463311974130913002774524928623644005505993681602486681565155683331521)
                   (.mul
                    (.var (.advice ⟨7⟩ 0))
                    (.mul
                     (.mul (.var (.advice ⟨7⟩ 0)) (.var (.advice ⟨7⟩ 0)))
                     (.mul (.var (.advice ⟨7⟩ 0)) (.var (.advice ⟨7⟩ 0))))))))),
              ("",
                (.add
                 (.add
                  (.var (.fixed ⟨1⟩ 0))
                  (.mul
                   (.const
                    52435875175126190479447740508185965837690552500527637822603658699938581184512)
                   (.var (.advice ⟨1⟩ 1))))
                 (.add
                  (.add
                   (.add
                    (.add
                     (.add
                      (.add
                       (.add
                        (.mul
                         (.const
                      41216583078069907292136355165153270142521178992429414226155254333730607536733)
                         (.var (.advice ⟨0⟩ 0)))
                        (.mul
                         (.const
                      34853984525125276266590937240908152702715112008598809217765432339048892301352)
                         (.var (.advice ⟨1⟩ 0))))
                       (.mul
                        (.const
                      17548561380688843065348281029305916198268522889382278651903462232179510668048)
                        (.mul
                         (.var (.advice ⟨2⟩ 0))
                         (.mul
                          (.mul (.var (.advice ⟨2⟩ 0)) (.var (.advice ⟨2⟩ 0)))
                          (.mul (.var (.advice ⟨2⟩ 0)) (.var (.advice ⟨2⟩ 0)))))))
                      (.mul
                       (.const
                      22573484092096950280151461091492173066588738155952808584348937425179801521445)
                       (.mul
                        (.var (.advice ⟨3⟩ 0))
                        (.mul
                         (.mul (.var (.advice ⟨3⟩ 0)) (.var (.advice ⟨3⟩ 0)))
                         (.mul (.var (.advice ⟨3⟩ 0)) (.var (.advice ⟨3⟩ 0)))))))
                     (.mul
                      (.const
                      17799439645526593468527852005527707639891232191326421130080209212181800663685)
                      (.mul
                       (.var (.advice ⟨4⟩ 0))
                       (.mul
                        (.mul (.var (.advice ⟨4⟩ 0)) (.var (.advice ⟨4⟩ 0)))
                        (.mul (.var (.advice ⟨4⟩ 0)) (.var (.advice ⟨4⟩ 0)))))))
                    (.mul
                     (.const
                      43072347715431875659722495403924484570295794297555905065846140476197612812033)
                     (.mul
                      (.var (.advice ⟨5⟩ 0))
                      (.mul
                       (.mul (.var (.advice ⟨5⟩ 0)) (.var (.advice ⟨5⟩ 0)))
                       (.mul (.var (.advice ⟨5⟩ 0)) (.var (.advice ⟨5⟩ 0)))))))
                   (.mul
                    (.const
                     21762182386571606640672645248729054582240844218141454043565005480082460585677)
                    (.mul
                     (.var (.advice ⟨6⟩ 0))
                     (.mul
                      (.mul (.var (.advice ⟨6⟩ 0)) (.var (.advice ⟨6⟩ 0)))
                      (.mul (.var (.advice ⟨6⟩ 0)) (.var (.advice ⟨6⟩ 0)))))))
                  (.mul
                   (.const
                    7179405695647424344643177657798954274869382720335107962712222495241823787551)
                   (.mul
                    (.var (.advice ⟨7⟩ 0))
                    (.mul
                     (.mul (.var (.advice ⟨7⟩ 0)) (.var (.advice ⟨7⟩ 0)))
                     (.mul (.var (.advice ⟨7⟩ 0)) (.var (.advice ⟨7⟩ 0))))))))),
              ("",
                (.add
                 (.add
                  (.var (.fixed ⟨2⟩ 0))
                  (.mul
                   (.const
                    52435875175126190479447740508185965837690552500527637822603658699938581184512)
                   (.var (.advice ⟨3⟩ 0))))
                 (.add
                  (.add
                   (.mul
                    (.const
                     42569072482279996318031820844820583094661593761988851871644829917446303682880)
                    (.var (.advice ⟨0⟩ 0)))
                   (.mul
                    (.const
                     48777675531739959342114240072267441286903816384223937749440830379544192657290)
                    (.var (.advice ⟨1⟩ 0))))
                  (.mul
                   (.const
                    33286996086728685078854749126251163286167502628080690207063928367301359689947)
                   (.mul
                    (.var (.advice ⟨2⟩ 0))
                    (.mul
                     (.mul (.var (.advice ⟨2⟩ 0)) (.var (.advice ⟨2⟩ 0)))
                     (.mul (.var (.advice ⟨2⟩ 0)) (.var (.advice ⟨2⟩ 0))))))))),
              ("",
                (.add
                 (.add
                  (.var (.fixed ⟨3⟩ 0))
                  (.mul
                   (.const
                    52435875175126190479447740508185965837690552500527637822603658699938581184512)
                   (.var (.advice ⟨4⟩ 0))))
                 (.add
                  (.add
                   (.add
                    (.mul
                     (.const
                      15460822173785725787510766083057066620988948322919030231014542645107533362369)
                     (.var (.advice ⟨0⟩ 0)))
                    (.mul
                     (.const
                      17532068198837287192548063441235938928456800450058734482970684092419295703441)
                     (.var (.advice ⟨1⟩ 0))))
                   (.mul
                    (.const
                     30536090514433970940206888994283604712174418989908022047600262784049007297138)
                    (.mul
                     (.var (.advice ⟨2⟩ 0))
                     (.mul
                      (.mul (.var (.advice ⟨2⟩ 0)) (.var (.advice ⟨2⟩ 0)))
                      (.mul (.var (.advice ⟨2⟩ 0)) (.var (.advice ⟨2⟩ 0)))))))
                  (.mul
                   (.const
                    33286996086728685078854749126251163286167502628080690207063928367301359689947)
                   (.mul
                    (.var (.advice ⟨3⟩ 0))
                    (.mul
                     (.mul (.var (.advice ⟨3⟩ 0)) (.var (.advice ⟨3⟩ 0)))
                     (.mul (.var (.advice ⟨3⟩ 0)) (.var (.advice ⟨3⟩ 0))))))))),
              ("",
                (.add
                 (.add
                  (.var (.fixed ⟨4⟩ 0))
                  (.mul
                   (.const
                    52435875175126190479447740508185965837690552500527637822603658699938581184512)
                   (.var (.advice ⟨5⟩ 0))))
                 (.add
                  (.add
                   (.add
                    (.add
                     (.mul
                      (.const
                      51757916557095931492101637894700153753738985202877927051595743124655465049675)
                      (.var (.advice ⟨0⟩ 0)))
                     (.mul
                      (.const
                      16513270875002105355154055214392863859886533828870466617169669632972895048992)
                      (.var (.advice ⟨1⟩ 0))))
                    (.mul
                     (.const
                      35426167520291240455001880880580845749581081201345737315527923196315309304361)
                     (.mul
                      (.var (.advice ⟨2⟩ 0))
                      (.mul
                       (.mul (.var (.advice ⟨2⟩ 0)) (.var (.advice ⟨2⟩ 0)))
                       (.mul (.var (.advice ⟨2⟩ 0)) (.var (.advice ⟨2⟩ 0)))))))
                   (.mul
                    (.const
                     30536090514433970940206888994283604712174418989908022047600262784049007297138)
                    (.mul
                     (.var (.advice ⟨3⟩ 0))
                     (.mul
                      (.mul (.var (.advice ⟨3⟩ 0)) (.var (.advice ⟨3⟩ 0)))
                      (.mul (.var (.advice ⟨3⟩ 0)) (.var (.advice ⟨3⟩ 0)))))))
                  (.mul
                   (.const
                    33286996086728685078854749126251163286167502628080690207063928367301359689947)
                   (.mul
                    (.var (.advice ⟨4⟩ 0))
                    (.mul
                     (.mul (.var (.advice ⟨4⟩ 0)) (.var (.advice ⟨4⟩ 0)))
                     (.mul (.var (.advice ⟨4⟩ 0)) (.var (.advice ⟨4⟩ 0))))))))),
              ("",
                (.add
                 (.add
                  (.var (.fixed ⟨5⟩ 0))
                  (.mul
                   (.const
                    52435875175126190479447740508185965837690552500527637822603658699938581184512)
                   (.var (.advice ⟨6⟩ 0))))
                 (.add
                  (.add
                   (.add
                    (.add
                     (.add
                      (.mul
                       (.const
                      21416013269199706780655207523311618433421828314385182423308221541654338163111)
                       (.var (.advice ⟨0⟩ 0)))
                      (.mul
                       (.const
                      16124966132388516597090803080166171234527932877010453966457664182846667286567)
                       (.var (.advice ⟨1⟩ 0))))
                     (.mul
                      (.const
                      11536991632578856038169226946888068627873692153441762213164802460898458963278)
                      (.mul
                       (.var (.advice ⟨2⟩ 0))
                       (.mul
                        (.mul (.var (.advice ⟨2⟩ 0)) (.var (.advice ⟨2⟩ 0)))
                        (.mul (.var (.advice ⟨2⟩ 0)) (.var (.advice ⟨2⟩ 0)))))))
                    (.mul
                     (.const
                      35426167520291240455001880880580845749581081201345737315527923196315309304361)
                     (.mul
                      (.var (.advice ⟨3⟩ 0))
                      (.mul
                       (.mul (.var (.advice ⟨3⟩ 0)) (.var (.advice ⟨3⟩ 0)))
                       (.mul (.var (.advice ⟨3⟩ 0)) (.var (.advice ⟨3⟩ 0)))))))
                   (.mul
                    (.const
                     30536090514433970940206888994283604712174418989908022047600262784049007297138)
                    (.mul
                     (.var (.advice ⟨4⟩ 0))
                     (.mul
                      (.mul (.var (.advice ⟨4⟩ 0)) (.var (.advice ⟨4⟩ 0)))
                      (.mul (.var (.advice ⟨4⟩ 0)) (.var (.advice ⟨4⟩ 0)))))))
                  (.mul
                   (.const
                    33286996086728685078854749126251163286167502628080690207063928367301359689947)
                   (.mul
                    (.var (.advice ⟨5⟩ 0))
                    (.mul
                     (.mul (.var (.advice ⟨5⟩ 0)) (.var (.advice ⟨5⟩ 0)))
                     (.mul (.var (.advice ⟨5⟩ 0)) (.var (.advice ⟨5⟩ 0))))))))),
              ("",
                (.add
                 (.add
                  (.var (.fixed ⟨6⟩ 0))
                  (.mul
                   (.const
                    52435875175126190479447740508185965837690552500527637822603658699938581184512)
                   (.var (.advice ⟨7⟩ 0))))
                 (.add
                  (.add
                   (.add
                    (.add
                     (.add
                      (.add
                       (.mul
                        (.const
                      49312067300773142348143637644007756944161175278464826357343119536320139437898)
                        (.var (.advice ⟨0⟩ 0)))
                       (.mul
                        (.const
                      18048464036633869753218556016152804134446546727997311594407968562256775743561)
                        (.var (.advice ⟨1⟩ 0))))
                      (.mul
                       (.const
                        383932250696541742607310001569714138555014361290971921083431601725621863731)
                       (.mul
                        (.var (.advice ⟨2⟩ 0))
                        (.mul
                         (.mul (.var (.advice ⟨2⟩ 0)) (.var (.advice ⟨2⟩ 0)))
                         (.mul (.var (.advice ⟨2⟩ 0)) (.var (.advice ⟨2⟩ 0)))))))
                     (.mul
                      (.const
                      11536991632578856038169226946888068627873692153441762213164802460898458963278)
                      (.mul
                       (.var (.advice ⟨3⟩ 0))
                       (.mul
                        (.mul (.var (.advice ⟨3⟩ 0)) (.var (.advice ⟨3⟩ 0)))
                        (.mul (.var (.advice ⟨3⟩ 0)) (.var (.advice ⟨3⟩ 0)))))))
                    (.mul
                     (.const
                      35426167520291240455001880880580845749581081201345737315527923196315309304361)
                     (.mul
                      (.var (.advice ⟨4⟩ 0))
                      (.mul
                       (.mul (.var (.advice ⟨4⟩ 0)) (.var (.advice ⟨4⟩ 0)))
                       (.mul (.var (.advice ⟨4⟩ 0)) (.var (.advice ⟨4⟩ 0)))))))
                   (.mul
                    (.const
                     30536090514433970940206888994283604712174418989908022047600262784049007297138)
                    (.mul
                     (.var (.advice ⟨5⟩ 0))
                     (.mul
                      (.mul (.var (.advice ⟨5⟩ 0)) (.var (.advice ⟨5⟩ 0)))
                      (.mul (.var (.advice ⟨5⟩ 0)) (.var (.advice ⟨5⟩ 0)))))))
                  (.mul
                   (.const
                    33286996086728685078854749126251163286167502628080690207063928367301359689947)
                   (.mul
                    (.var (.advice ⟨6⟩ 0))
                    (.mul
                     (.mul (.var (.advice ⟨6⟩ 0)) (.var (.advice ⟨6⟩ 0)))
                     (.mul (.var (.advice ⟨6⟩ 0)) (.var (.advice ⟨6⟩ 0))))))))),
              ("",
                (.add
                 (.add
                  (.var (.fixed ⟨7⟩ 0))
                  (.mul
                   (.const
                    52435875175126190479447740508185965837690552500527637822603658699938581184512)
                   (.var (.advice ⟨2⟩ 1))))
                 (.add
                  (.add
                   (.add
                    (.add
                     (.add
                      (.add
                       (.add
                        (.mul
                         (.const
                      51042352737684322926421982719448027244098131173912330356286361328735472870963)
                         (.var (.advice ⟨0⟩ 0)))
                        (.mul
                         (.const
                      29390124884714250559401457937586375728515143848012653816777731013221302010465)
                         (.var (.advice ⟨1⟩ 0))))
                       (.mul
                        (.const
                      14193443826180214291995136727309819104154361382389237431794542473275951615294)
                        (.mul
                         (.var (.advice ⟨2⟩ 0))
                         (.mul
                          (.mul (.var (.advice ⟨2⟩ 0)) (.var (.advice ⟨2⟩ 0)))
                          (.mul (.var (.advice ⟨2⟩ 0)) (.var (.advice ⟨2⟩ 0)))))))
                      (.mul
                       (.const
                        383932250696541742607310001569714138555014361290971921083431601725621863731)
                       (.mul
                        (.var (.advice ⟨3⟩ 0))
                        (.mul
                         (.mul (.var (.advice ⟨3⟩ 0)) (.var (.advice ⟨3⟩ 0)))
                         (.mul (.var (.advice ⟨3⟩ 0)) (.var (.advice ⟨3⟩ 0)))))))
                     (.mul
                      (.const
                      11536991632578856038169226946888068627873692153441762213164802460898458963278)
                      (.mul
                       (.var (.advice ⟨4⟩ 0))
                       (.mul
                        (.mul (.var (.advice ⟨4⟩ 0)) (.var (.advice ⟨4⟩ 0)))
                        (.mul (.var (.advice ⟨4⟩ 0)) (.var (.advice ⟨4⟩ 0)))))))
                    (.mul
                     (.const
                      35426167520291240455001880880580845749581081201345737315527923196315309304361)
                     (.mul
                      (.var (.advice ⟨5⟩ 0))
                      (.mul
                       (.mul (.var (.advice ⟨5⟩ 0)) (.var (.advice ⟨5⟩ 0)))
                       (.mul (.var (.advice ⟨5⟩ 0)) (.var (.advice ⟨5⟩ 0)))))))
                   (.mul
                    (.const
                     30536090514433970940206888994283604712174418989908022047600262784049007297138)
                    (.mul
                     (.var (.advice ⟨6⟩ 0))
                     (.mul
                      (.mul (.var (.advice ⟨6⟩ 0)) (.var (.advice ⟨6⟩ 0)))
                      (.mul (.var (.advice ⟨6⟩ 0)) (.var (.advice ⟨6⟩ 0)))))))
                  (.mul
                   (.const
                    33286996086728685078854749126251163286167502628080690207063928367301359689947)
                   (.mul
                    (.var (.advice ⟨7⟩ 0))
                    (.mul
                     (.mul (.var (.advice ⟨7⟩ 0)) (.var (.advice ⟨7⟩ 0)))
                     (.mul (.var (.advice ⟨7⟩ 0)) (.var (.advice ⟨7⟩ 0)))))))))],
          raw := false,
          rows := false }],
    currentQueries :=
      #[(.advice ⟨0⟩ 0),
        (.advice ⟨1⟩ 0),
        (.advice ⟨2⟩ 0),
        (.advice ⟨3⟩ 0),
        (.advice ⟨4⟩ 0),
        (.advice ⟨5⟩ 0),
        (.advice ⟨6⟩ 0),
        (.advice ⟨7⟩ 0),
        (.fixed ⟨0⟩ 0),
        (.fixed ⟨1⟩ 0),
        (.fixed ⟨2⟩ 0),
        (.fixed ⟨3⟩ 0),
        (.fixed ⟨4⟩ 0),
        (.fixed ⟨5⟩ 0),
        (.fixed ⟨6⟩ 0),
        (.fixed ⟨7⟩ 0),
        (.advice ⟨0⟩ 1),
        (.advice ⟨1⟩ 1),
        (.advice ⟨2⟩ 1)],
    lookupClosures :=
      #[({ name := "pow2range column check",
            selector := (.var (.selector ⟨3, false⟩)),
            inputs := #[#[(.var (.fixed ⟨10⟩ 0)), (.var (.advice ⟨1⟩ 0))]],
            table := #[(.var (.fixed ⟨11⟩ 0)), (.var (.fixed ⟨12⟩ 0))] },
          #[(.fixed ⟨10⟩ 0), (.advice ⟨1⟩ 0)],
          false)],
    rejectedLookups := #[],
    gateClosures :=
      #[("arith_gate",
          #[(.advice ⟨0⟩ 0),
            (.advice ⟨1⟩ 0),
            (.advice ⟨2⟩ 0),
            (.advice ⟨3⟩ 0),
            (.advice ⟨4⟩ 0),
            (.advice ⟨0⟩ 1),
            (.fixed ⟨4⟩ 0),
            (.fixed ⟨5⟩ 0),
            (.fixed ⟨6⟩ 0),
            (.fixed ⟨7⟩ 0),
            (.fixed ⟨8⟩ 0),
            (.fixed ⟨0⟩ 0),
            (.fixed ⟨1⟩ 0),
            (.fixed ⟨2⟩ 0),
            (.fixed ⟨3⟩ 0)],
          #[(.advice ⟨0⟩ 0),
            (.advice ⟨1⟩ 0),
            (.advice ⟨2⟩ 0),
            (.advice ⟨3⟩ 0),
            (.advice ⟨4⟩ 0),
            (.advice ⟨0⟩ 1),
            (.fixed ⟨4⟩ 0),
            (.fixed ⟨5⟩ 0),
            (.fixed ⟨6⟩ 0),
            (.fixed ⟨7⟩ 0),
            (.fixed ⟨8⟩ 0),
            (.fixed ⟨0⟩ 0),
            (.fixed ⟨1⟩ 0),
            (.fixed ⟨2⟩ 0),
            (.fixed ⟨3⟩ 0)],
          true),
        ("12_minus_34",
          #[(.advice ⟨1⟩ 0), (.advice ⟨2⟩ 0), (.advice ⟨3⟩ 0), (.advice ⟨4⟩ 0)],
          #[(.advice ⟨1⟩ 0), (.advice ⟨2⟩ 0), (.advice ⟨3⟩ 0), (.advice ⟨4⟩ 0)],
          true),
        ("parallel_add_gate",
          #[(.advice ⟨0⟩ 0),
            (.advice ⟨0⟩ 1),
            (.fixed ⟨4⟩ 0),
            (.advice ⟨1⟩ 0),
            (.advice ⟨1⟩ 1),
            (.fixed ⟨5⟩ 0),
            (.advice ⟨2⟩ 0),
            (.advice ⟨2⟩ 1),
            (.fixed ⟨6⟩ 0)],
          #[(.advice ⟨0⟩ 0),
            (.advice ⟨0⟩ 1),
            (.fixed ⟨4⟩ 0),
            (.advice ⟨1⟩ 0),
            (.advice ⟨1⟩ 1),
            (.fixed ⟨5⟩ 0),
            (.advice ⟨2⟩ 0),
            (.advice ⟨2⟩ 1),
            (.fixed ⟨6⟩ 0)],
          true),
        ("full_round_gate",
          #[(.advice ⟨0⟩ 0),
            (.advice ⟨3⟩ 0),
            (.advice ⟨1⟩ 0),
            (.advice ⟨4⟩ 0),
            (.advice ⟨2⟩ 0),
            (.advice ⟨5⟩ 0),
            (.advice ⟨0⟩ 1),
            (.advice ⟨1⟩ 1),
            (.advice ⟨2⟩ 1),
            (.fixed ⟨0⟩ 0),
            (.fixed ⟨1⟩ 0),
            (.fixed ⟨2⟩ 0)],
          #[(.advice ⟨0⟩ 0),
            (.advice ⟨3⟩ 0),
            (.advice ⟨1⟩ 0),
            (.advice ⟨4⟩ 0),
            (.advice ⟨2⟩ 0),
            (.advice ⟨5⟩ 0),
            (.advice ⟨0⟩ 1),
            (.advice ⟨1⟩ 1),
            (.advice ⟨2⟩ 1),
            (.fixed ⟨0⟩ 0),
            (.fixed ⟨1⟩ 0),
            (.fixed ⟨2⟩ 0)],
          true),
        ("partial_round_gate",
          #[(.advice ⟨0⟩ 0),
            (.advice ⟨1⟩ 0),
            (.advice ⟨2⟩ 0),
            (.advice ⟨3⟩ 0),
            (.advice ⟨4⟩ 0),
            (.advice ⟨5⟩ 0),
            (.advice ⟨6⟩ 0),
            (.advice ⟨7⟩ 0),
            (.fixed ⟨0⟩ 0),
            (.fixed ⟨1⟩ 0),
            (.fixed ⟨2⟩ 0),
            (.fixed ⟨3⟩ 0),
            (.fixed ⟨4⟩ 0),
            (.fixed ⟨5⟩ 0),
            (.fixed ⟨6⟩ 0),
            (.fixed ⟨7⟩ 0),
            (.advice ⟨0⟩ 1),
            (.advice ⟨1⟩ 1),
            (.advice ⟨2⟩ 1)],
          #[(.advice ⟨0⟩ 0),
            (.advice ⟨1⟩ 0),
            (.advice ⟨2⟩ 0),
            (.advice ⟨3⟩ 0),
            (.advice ⟨4⟩ 0),
            (.advice ⟨5⟩ 0),
            (.advice ⟨6⟩ 0),
            (.advice ⟨7⟩ 0),
            (.fixed ⟨0⟩ 0),
            (.fixed ⟨1⟩ 0),
            (.fixed ⟨2⟩ 0),
            (.fixed ⟨3⟩ 0),
            (.fixed ⟨4⟩ 0),
            (.fixed ⟨5⟩ 0),
            (.fixed ⟨6⟩ 0),
            (.fixed ⟨7⟩ 0),
            (.advice ⟨0⟩ 1),
            (.advice ⟨1⟩ 1),
            (.advice ⟨2⟩ 1)],
          false)],
    prunedFrom := #[],
    selectorKinds := #[true, true, true, false, true, false],
    minimumDegree := none,
    selectorFixedStart := none,
    errors := #[] }

/-- The native and pow2range chips on 5 advice, 9 fixed and 2 instance columns, then one gate. -/
def native : CS :=
  { numFixed := 13,
    numAdvice := 5,
    numInstance := 2,
    numSelectors := 5,
    adviceQueries := #[(0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (0, 1), (1, 1), (2, 1)],
    fixedQueries :=
      #[(9, 0),
        (4, 0),
        (5, 0),
        (6, 0),
        (7, 0),
        (8, 0),
        (0, 0),
        (1, 0),
        (2, 0),
        (3, 0),
        (10, 0),
        (11, 0),
        (12, 0)],
    instanceQueries := #[(0, 0), (1, 0)],
    permutation :=
      #[⟨.fixed, 9⟩,
        ⟨.advice, 0⟩,
        ⟨.advice, 1⟩,
        ⟨.advice, 2⟩,
        ⟨.advice, 3⟩,
        ⟨.advice, 4⟩,
        ⟨.instance, 0⟩,
        ⟨.instance, 1⟩],
    constantColumns := #[],
    gates :=
      #[{ name := "arith_gate",
          selector := ⟨0, true⟩,
          queries :=
            #[(.advice ⟨0⟩ 0),
              (.advice ⟨1⟩ 0),
              (.advice ⟨2⟩ 0),
              (.advice ⟨3⟩ 0),
              (.advice ⟨4⟩ 0),
              (.advice ⟨0⟩ 1),
              (.fixed ⟨4⟩ 0),
              (.fixed ⟨5⟩ 0),
              (.fixed ⟨6⟩ 0),
              (.fixed ⟨7⟩ 0),
              (.fixed ⟨8⟩ 0),
              (.fixed ⟨0⟩ 0),
              (.fixed ⟨1⟩ 0),
              (.fixed ⟨2⟩ 0),
              (.fixed ⟨3⟩ 0)],
          constraints :=
            #[("",
                (.add
                 (.add
                  (.add
                   (.add
                    (.add
                     (.add
                      (.add
                       (.add
                        (.var (.fixed ⟨3⟩ 0))
                        (.mul (.var (.fixed ⟨4⟩ 0)) (.var (.advice ⟨0⟩ 0))))
                       (.mul (.var (.fixed ⟨5⟩ 0)) (.var (.advice ⟨1⟩ 0))))
                      (.mul (.var (.fixed ⟨6⟩ 0)) (.var (.advice ⟨2⟩ 0))))
                     (.mul (.var (.fixed ⟨7⟩ 0)) (.var (.advice ⟨3⟩ 0))))
                    (.mul (.var (.fixed ⟨8⟩ 0)) (.var (.advice ⟨4⟩ 0))))
                   (.mul (.var (.fixed ⟨0⟩ 0)) (.var (.advice ⟨0⟩ 1))))
                  (.mul
                   (.mul (.var (.fixed ⟨1⟩ 0)) (.var (.advice ⟨0⟩ 0)))
                   (.var (.advice ⟨1⟩ 0))))
                 (.mul
                  (.mul (.var (.fixed ⟨2⟩ 0)) (.var (.advice ⟨0⟩ 0)))
                  (.var (.advice ⟨2⟩ 0)))))],
          raw := false,
          rows := false },
        { name := "12_minus_34",
          selector := ⟨1, true⟩,
          queries := #[(.advice ⟨1⟩ 0), (.advice ⟨2⟩ 0), (.advice ⟨3⟩ 0), (.advice ⟨4⟩ 0)],
          constraints :=
            #[("",
                (.add
                 (.add
                  (.add (.var (.advice ⟨1⟩ 0)) (.var (.advice ⟨2⟩ 0)))
                  (.mul
                   (.const
                    52435875175126190479447740508185965837690552500527637822603658699938581184512)
                   (.var (.advice ⟨3⟩ 0))))
                 (.mul
                  (.const
                   52435875175126190479447740508185965837690552500527637822603658699938581184512)
                  (.var (.advice ⟨4⟩ 0)))))],
          raw := false,
          rows := false },
        { name := "parallel_add_gate",
          selector := ⟨2, true⟩,
          queries :=
            #[(.advice ⟨0⟩ 0),
              (.advice ⟨0⟩ 1),
              (.fixed ⟨4⟩ 0),
              (.advice ⟨1⟩ 0),
              (.advice ⟨1⟩ 1),
              (.fixed ⟨5⟩ 0),
              (.advice ⟨2⟩ 0),
              (.advice ⟨2⟩ 1),
              (.fixed ⟨6⟩ 0)],
          constraints :=
            #[("",
                (.add
                 (.add (.var (.advice ⟨0⟩ 0)) (.var (.fixed ⟨4⟩ 0)))
                 (.mul
                  (.const
                   52435875175126190479447740508185965837690552500527637822603658699938581184512)
                  (.var (.advice ⟨0⟩ 1))))),
              ("",
                (.add
                 (.add (.var (.advice ⟨1⟩ 0)) (.var (.fixed ⟨5⟩ 0)))
                 (.mul
                  (.const
                   52435875175126190479447740508185965837690552500527637822603658699938581184512)
                  (.var (.advice ⟨1⟩ 1))))),
              ("",
                (.add
                 (.add (.var (.advice ⟨2⟩ 0)) (.var (.fixed ⟨6⟩ 0)))
                 (.mul
                  (.const
                   52435875175126190479447740508185965837690552500527637822603658699938581184512)
                  (.var (.advice ⟨2⟩ 1)))))],
          raw := false,
          rows := false },
        { name := "end",
          selector := ⟨4, true⟩,
          queries := #[(.advice ⟨0⟩ 0)],
          constraints := #[("", (.var (.advice ⟨0⟩ 0)))],
          raw := false,
          rows := false }],
    lookups :=
      #[{ name := "pow2range column check",
          selector := (.var (.selector ⟨3, false⟩)),
          inputs := #[#[(.var (.fixed ⟨10⟩ 0)), (.var (.advice ⟨1⟩ 0))]],
          table := #[(.var (.fixed ⟨11⟩ 0)), (.var (.fixed ⟨12⟩ 0))] }],
    trashcans := #[],
    currentQueries := #[(.advice ⟨0⟩ 0)],
    lookupClosures :=
      #[({ name := "pow2range column check",
            selector := (.var (.selector ⟨3, false⟩)),
            inputs := #[#[(.var (.fixed ⟨10⟩ 0)), (.var (.advice ⟨1⟩ 0))]],
            table := #[(.var (.fixed ⟨11⟩ 0)), (.var (.fixed ⟨12⟩ 0))] },
          #[(.fixed ⟨10⟩ 0), (.advice ⟨1⟩ 0)],
          false)],
    rejectedLookups := #[],
    gateClosures :=
      #[("arith_gate",
          #[(.advice ⟨0⟩ 0),
            (.advice ⟨1⟩ 0),
            (.advice ⟨2⟩ 0),
            (.advice ⟨3⟩ 0),
            (.advice ⟨4⟩ 0),
            (.advice ⟨0⟩ 1),
            (.fixed ⟨4⟩ 0),
            (.fixed ⟨5⟩ 0),
            (.fixed ⟨6⟩ 0),
            (.fixed ⟨7⟩ 0),
            (.fixed ⟨8⟩ 0),
            (.fixed ⟨0⟩ 0),
            (.fixed ⟨1⟩ 0),
            (.fixed ⟨2⟩ 0),
            (.fixed ⟨3⟩ 0)],
          #[(.advice ⟨0⟩ 0),
            (.advice ⟨1⟩ 0),
            (.advice ⟨2⟩ 0),
            (.advice ⟨3⟩ 0),
            (.advice ⟨4⟩ 0),
            (.advice ⟨0⟩ 1),
            (.fixed ⟨4⟩ 0),
            (.fixed ⟨5⟩ 0),
            (.fixed ⟨6⟩ 0),
            (.fixed ⟨7⟩ 0),
            (.fixed ⟨8⟩ 0),
            (.fixed ⟨0⟩ 0),
            (.fixed ⟨1⟩ 0),
            (.fixed ⟨2⟩ 0),
            (.fixed ⟨3⟩ 0)],
          true),
        ("12_minus_34",
          #[(.advice ⟨1⟩ 0), (.advice ⟨2⟩ 0), (.advice ⟨3⟩ 0), (.advice ⟨4⟩ 0)],
          #[(.advice ⟨1⟩ 0), (.advice ⟨2⟩ 0), (.advice ⟨3⟩ 0), (.advice ⟨4⟩ 0)],
          true),
        ("parallel_add_gate",
          #[(.advice ⟨0⟩ 0),
            (.advice ⟨0⟩ 1),
            (.fixed ⟨4⟩ 0),
            (.advice ⟨1⟩ 0),
            (.advice ⟨1⟩ 1),
            (.fixed ⟨5⟩ 0),
            (.advice ⟨2⟩ 0),
            (.advice ⟨2⟩ 1),
            (.fixed ⟨6⟩ 0)],
          #[(.advice ⟨0⟩ 0),
            (.advice ⟨0⟩ 1),
            (.fixed ⟨4⟩ 0),
            (.advice ⟨1⟩ 0),
            (.advice ⟨1⟩ 1),
            (.fixed ⟨5⟩ 0),
            (.advice ⟨2⟩ 0),
            (.advice ⟨2⟩ 1),
            (.fixed ⟨6⟩ 0)],
          true),
        ("end", #[(.advice ⟨0⟩ 0)], #[(.advice ⟨0⟩ 0)], true)],
    prunedFrom := #[],
    selectorKinds := #[true, true, true, false, true],
    minimumDegree := none,
    selectorFixedStart := none,
    errors := #[] }

/-- pow2range over two advice columns, then one gate. -/
def rangeTwo : CS :=
  { numFixed := 3,
    numAdvice := 2,
    numInstance := 0,
    numSelectors := 2,
    adviceQueries := #[(0, 0), (1, 0)],
    fixedQueries := #[(0, 0), (1, 0), (2, 0)],
    instanceQueries := #[],
    permutation := #[],
    constantColumns := #[],
    gates :=
      #[{ name := "end",
          selector := ⟨1, true⟩,
          queries := #[(.advice ⟨0⟩ 0)],
          constraints := #[("", (.var (.advice ⟨0⟩ 0)))],
          raw := false,
          rows := false }],
    lookups :=
      #[{ name := "pow2range column check",
          selector := (.var (.selector ⟨0, false⟩)),
          inputs :=
            #[#[(.var (.fixed ⟨0⟩ 0)), (.var (.advice ⟨0⟩ 0))],
              #[(.var (.fixed ⟨0⟩ 0)), (.var (.advice ⟨1⟩ 0))]],
          table := #[(.var (.fixed ⟨1⟩ 0)), (.var (.fixed ⟨2⟩ 0))] }],
    trashcans := #[],
    currentQueries := #[(.advice ⟨0⟩ 0)],
    lookupClosures :=
      #[({ name := "pow2range column check",
            selector := (.var (.selector ⟨0, false⟩)),
            inputs :=
              #[#[(.var (.fixed ⟨0⟩ 0)), (.var (.advice ⟨0⟩ 0))],
                #[(.var (.fixed ⟨0⟩ 0)), (.var (.advice ⟨1⟩ 0))]],
            table := #[(.var (.fixed ⟨1⟩ 0)), (.var (.fixed ⟨2⟩ 0))] },
          #[(.fixed ⟨0⟩ 0), (.advice ⟨0⟩ 0), (.advice ⟨1⟩ 0)],
          false)],
    rejectedLookups := #[],
    gateClosures := #[("end", #[(.advice ⟨0⟩ 0)], #[(.advice ⟨0⟩ 0)], true)],
    prunedFrom := #[],
    selectorKinds := #[false, true],
    minimumDegree := none,
    selectorFixedStart := none,
    errors := #[] }

end Midnight.Backend.Fixtures
