#!/usr/bin/env node
/** Generate Lean Poseidon vectors with a pinned circomlibjs reference. */

import { execFileSync } from "node:child_process";
import { createHash } from "node:crypto";
import { readFileSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { pathToFileURL } from "node:url";

const SOURCE_COMMIT = "48b3ab37013c5ed21e9ff8a80a5b010795c97094";
const REFERENCE_CONSTANTS_SHA256 = "354f31bbed9d9a8b884d8f2181e339cb425b6e3e4cc7240bd3dd22f0070f3f2c";
const OPTIMIZED_CONSTANTS_SHA256 = "da1b82330e196f931d30dd304b3ec547fe041c2fac2226c7204e286a5db27ed0";

function argument(name) {
  const index = process.argv.indexOf(name);
  return index < 0 ? undefined : process.argv[index + 1];
}

function sha256(path) {
  return createHash("sha256").update(readFileSync(path)).digest("hex");
}

function verifySource(root) {
  const commit = execFileSync("git", ["-C", root, "rev-parse", "HEAD"], {
    encoding: "utf8",
  }).trim();
  if (commit !== SOURCE_COMMIT) {
    throw new Error(`circomlibjs commit is ${commit}; expected ${SOURCE_COMMIT}`);
  }
  const files = [
    ["src/poseidon_constants.json", REFERENCE_CONSTANTS_SHA256],
    ["src/poseidon_constants_opt.json", OPTIMIZED_CONSTANTS_SHA256],
  ];
  for (const [relativePath, expected] of files) {
    const actual = sha256(join(root, relativePath));
    if (actual !== expected) {
      throw new Error(`${relativePath} SHA-256 is ${actual}; expected ${expected}`);
    }
  }
}

function leanVector(arity) {
  const entries = Array.from({ length: arity }, (_, index) =>
    index === 0 ? "(1 : F)" : `${index + 1}`,
  );
  return `#v[${entries.join(", ")}]`;
}

async function generate(root) {
  verifySource(root);
  const referenceModule = await import(
    pathToFileURL(join(root, "src/poseidon_reference.js")).href
  );
  const optimizedModule = await import(
    pathToFileURL(join(root, "src/poseidon_opt.js")).href
  );
  const reference = await referenceModule.default();
  const optimized = await optimizedModule.default();

  const examples = [];
  for (let arity = 4; arity <= 16; arity += 1) {
    const inputs = Array.from({ length: arity }, (_, index) => index + 1);
    const referenceValue = reference.F.toObject(reference(inputs)).toString();
    const optimizedValue = optimized.F.toObject(optimized(inputs)).toString();
    if (referenceValue !== optimizedValue) {
      throw new Error(`reference/optimized mismatch at input arity ${arity}`);
    }
    examples.push(
      `example : poseidon params_t${arity + 1} ${leanVector(arity)} =\n` +
        `    (${referenceValue} : F) := by\n` +
        "  native_decide",
    );
  }

  return [
    "/-",
    "Poseidon reference vectors generated with iden3/circomlibjs.",
    "",
    `Source commit: ${SOURCE_COMMIT}`,
    `Reference constants SHA-256: ${REFERENCE_CONSTANTS_SHA256}`,
    `Optimized constants SHA-256: ${OPTIMIZED_CONSTANTS_SHA256}`,
    "Inputs for arity n are [1, 2, ..., n].",
    "",
    "DO NOT EDIT BY HAND. Regenerate with:",
    "  node scripts/generate_poseidon_vectors.mjs --circomlibjs <checkout>",
    "Check a generated file with the same command plus `--check`.",
    "-/",
    "module",
    "",
    "public import Clean.Specs.PoseidonOptimized",
    "",
    "public meta import Clean.Specs.PoseidonOptimized",
    "",
    "@[expose] public section",
    "",
    "namespace Specs.PoseidonOptimized",
    "",
    "open Specs.Poseidon (F)",
    "",
    ...examples.flatMap((example) => [example, ""]),
    "end Specs.PoseidonOptimized",
    "",
  ].join("\n");
}

const source = argument("--circomlibjs");
if (!source) {
  throw new Error("usage: generate_poseidon_vectors.mjs --circomlibjs <checkout> [--output <file>] [--check]");
}
const output = resolve(argument("--output") ?? "Clean/Specs/PoseidonReferenceVectors.lean");
const generated = await generate(resolve(source));
if (process.argv.includes("--check")) {
  if (readFileSync(output, "utf8") !== generated) {
    console.error(`${output} is not generated from the pinned circomlibjs source`);
    process.exit(1);
  }
  console.log(`${output} matches the pinned circomlibjs source`);
} else {
  writeFileSync(output, generated);
  console.log(`wrote ${output}`);
}
