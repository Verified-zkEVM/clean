mod common;

/// End-to-end test for FemtoCairo: circuit and trace exported from Lean,
/// with a preprocessed program table and a prover-supplied memory table.
///
/// Test program: 15 ADD instructions (all-immediate addressing mode), 64 program entries.
/// State: 16 rows (15 steps), from (pc=0,ap=0,fp=0) to (pc=60,ap=0,fp=0).
/// Tables: program (preprocessed, 64x2), memory (prover-supplied, 16x2).
#[test]
fn test_femtocairo_e2e() {
    let (circuit_json, trace_json) = common::run_lean_scripts(
        "FemtoCairoCircuitGen.lean",
        "output/femtocairo_circuit.json",
        "FemtoCairoTraceGen.lean",
        "output/femtocairo_trace.json",
    );

    common::prove_and_verify_from_json(&circuit_json, &trace_json);
}

/// End-to-end FemtoCairo test with memory-reading instructions.
///
/// Exercises AP-relative and FP-relative addressing modes with non-trivial memory values.
/// Test program: 7 instructions (ADD/MUL with AP-rel, FP-rel, and immediate modes), 32 program entries.
/// State: 8 rows (7 steps), from (pc=0,ap=0,fp=0) to (pc=28,ap=0,fp=0).
/// Tables: program (preprocessed, 32x2), memory (prover-supplied, 8x2).
#[test]
fn test_femtocairo_memory_e2e() {
    let (circuit_json, trace_json) = common::run_lean_scripts(
        "FemtoCairoMemoryCircuitGen.lean",
        "output/femtocairo_memory_circuit.json",
        "FemtoCairoMemoryTraceGen.lean",
        "output/femtocairo_memory_trace.json",
    );

    common::prove_and_verify_from_json(&circuit_json, &trace_json);
}
