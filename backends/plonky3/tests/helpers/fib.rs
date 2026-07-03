use clean_backend::parse_trace;
use p3_field::{Field, PrimeCharacteristicRing};

use crate::lean_runner::run_lean_script;

pub fn generate_trace_from_lean<F: Field + PrimeCharacteristicRing>(
    steps: usize,
    output_filename: &str,
) -> Result<Vec<Vec<F>>, Box<dyn std::error::Error>> {
    let output_path = format!("output/{}", output_filename);
    let steps_str = steps.to_string();
    let json_content = run_lean_script("FibTraceGen.lean", &[&steps_str], &output_path);
    let trace = parse_trace::<F>(&json_content);
    Ok(trace)
}
