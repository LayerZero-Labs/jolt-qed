//! expansion-parity: T1 expansion rows and I0(a) inline checks against a
//! Jolt checkout. See README.md for the checks and the output files.

// Link every inline crate so all registrations reach the inventory.
extern crate jolt_inlines_bigint as _;
extern crate jolt_inlines_blake2 as _;
extern crate jolt_inlines_blake3 as _;
extern crate jolt_inlines_grumpkin as _;
extern crate jolt_inlines_keccak256 as _;
extern crate jolt_inlines_ntt as _;
extern crate jolt_inlines_p256 as _;
extern crate jolt_inlines_secp256k1 as _;
extern crate jolt_inlines_sha2 as _;

mod cases;
mod inlines;
mod lean;
mod rows;

use std::collections::BTreeMap;
use std::io::{BufWriter, Write};
use std::path::PathBuf;

use jolt_program::expand::{expand_instruction, ExpansionAllocator, ExpansionError};
use jolt_riscv::{JoltInstructionRow, SourceInstruction, RV64IMAC_JOLT};
use serde::Deserialize;
use serde_json::{json, Value};

use crate::inlines::{AllocCase, TemplateRow};
use crate::rows::{allocator_is_fresh, allocator_state, expand, source_json, Annotator};

struct Args {
    jolt_dir: PathBuf,
    out: PathBuf,
    lean_root: Option<PathBuf>,
    seed: u64,
    random_per_kind: usize,
    skip_uniformity: bool,
    lean_chunk: usize,
}

fn parse_args() -> Result<Args, String> {
    let mut a = Args {
        jolt_dir: PathBuf::new(),
        out: PathBuf::new(),
        lean_root: None,
        seed: 0x7431_5eed,
        random_per_kind: 6,
        skip_uniformity: false,
        lean_chunk: 100,
    };
    let mut it = std::env::args().skip(1);
    let mut jolt = None;
    let mut out = None;
    while let Some(flag) = it.next() {
        let mut val = || it.next().ok_or(format!("{flag} needs a value"));
        match flag.as_str() {
            "--jolt-dir" => jolt = Some(PathBuf::from(val()?)),
            "--out" => out = Some(PathBuf::from(val()?)),
            "--lean-root" => a.lean_root = Some(PathBuf::from(val()?)),
            "--seed" => a.seed = val()?.parse().map_err(|e| format!("--seed: {e}"))?,
            "--random-per-kind" => {
                a.random_per_kind = val()?.parse().map_err(|e| format!("--random-per-kind: {e}"))?
            }
            "--lean-chunk" => {
                a.lean_chunk = val()?.parse().map_err(|e| format!("--lean-chunk: {e}"))?
            }
            "--skip-uniformity" => a.skip_uniformity = true,
            other => return Err(format!("unknown argument {other}")),
        }
    }
    a.jolt_dir = jolt
        .or_else(|| std::env::var_os("JOLT_DIR").map(PathBuf::from))
        .ok_or("--jolt-dir or JOLT_DIR is required")?;
    a.out = out.ok_or("--out is required")?;
    Ok(a)
}

/// One check in summary.json.
struct Check {
    name: &'static str,
    pass: bool,
    detail: Value,
}

#[derive(Deserialize)]
struct GoldenCase {
    name: String,
    input: SourceInstruction,
    output_sha256: String,
}

struct Emitter<W: Write> {
    out: W,
    lines: usize,
}

impl<W: Write> Emitter<W> {
    fn emit(&mut self, v: &Value) -> Result<(), String> {
        serde_json::to_writer(&mut self.out, v).map_err(|e| e.to_string())?;
        self.out.write_all(b"\n").map_err(|e| e.to_string())?;
        self.lines += 1;
        Ok(())
    }
}

/// A case for the shared-allocator run, with its fresh-allocator result.
struct SharedInput {
    name: String,
    group: &'static str,
    source: SourceInstruction,
    inline_name: Option<&'static str>,
    fresh: Result<Vec<JoltInstructionRow>, String>,
}

fn jolt_commit(dir: &PathBuf) -> String {
    std::process::Command::new("git")
        .arg("-C")
        .arg(dir)
        .args(["rev-parse", "HEAD"])
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .unwrap_or_else(|| "unknown".into())
}

fn run() -> Result<bool, String> {
    let args = parse_args()?;
    std::fs::create_dir_all(&args.out).map_err(|e| e.to_string())?;
    let commit = jolt_commit(&args.jolt_dir);
    rows::check_flag_lists()?;
    let ann = Annotator::new()?;
    let mut checks: Vec<Check> = Vec::new();
    let file = std::fs::File::create(args.out.join("rows.jsonl")).map_err(|e| e.to_string())?;
    let mut em = Emitter {
        out: BufWriter::new(file),
        lines: 0,
    };
    let mut shared_inputs: Vec<SharedInput> = Vec::new();
    let mut fresh_not_restored: Vec<String> = Vec::new();
    let mut group_counts: BTreeMap<&'static str, (usize, usize)> = BTreeMap::new();

    // ---- golden ----
    let golden_path = args
        .jolt_dir
        .join("crates/jolt-program/src/expand/fixtures/main_expand_parity_hashes.json");
    let golden: Vec<GoldenCase> = serde_json::from_str(
        &std::fs::read_to_string(&golden_path).map_err(|e| format!("{golden_path:?}: {e}"))?,
    )
    .map_err(|e| format!("golden fixture: {e}"))?;
    let mut golden_fail = Vec::new();
    let mut profile_disagree = Vec::new();
    for g in &golden {
        // Exactly Jolt's test: expand_instruction (no inline provider),
        // RV64IMAC_JOLT, a fresh allocator per case.
        let mut alloc = ExpansionAllocator::new();
        match expand_instruction(&g.input, &mut alloc, RV64IMAC_JOLT) {
            Ok(out) => {
                let rows: Vec<JoltInstructionRow> =
                    out.into_iter().map(JoltInstructionRow::from).collect();
                let h = rows::rows_sha256(&rows)?;
                if h != g.output_sha256 {
                    golden_fail.push(format!("{}: {h} != {}", g.name, g.output_sha256));
                }
                let mut alloc2 = ExpansionAllocator::new();
                let prod = expand(&g.input, &mut alloc2);
                if prod.as_ref().ok() != Some(&rows) {
                    profile_disagree.push(g.name.clone());
                }
            }
            Err(e) => golden_fail.push(format!("{}: error {e:?}", g.name)),
        }
    }
    for g in &golden {
        record_fresh(
            &ann,
            &mut em,
            &g.name,
            "golden",
            &g.input,
            None,
            &mut fresh_not_restored,
            &mut group_counts,
            &mut shared_inputs,
        )?;
    }
    checks.push(Check {
        name: "golden_fixture_hashes",
        pass: golden_fail.is_empty() && golden.len() == 360,
        detail: json!({"cases": golden.len(), "expected_cases": 360, "mismatches": golden_fail}),
    });
    checks.push(Check {
        name: "golden_profiles_agree",
        pass: profile_disagree.is_empty(),
        detail: json!({
            "note": "rows under RV64IMAC_JOLT without a provider equal the production rows under RV64IMAC_JOLT_ALL_INLINES",
            "disagreeing_cases": profile_disagree,
        }),
    });

    // ---- T1 groups ----
    let mut t1 = Vec::new();
    t1.push(("aliased", cases::register_group("aliased", 7, 7, 7)?));
    t1.push(("rd_zero", cases::register_group("rd_zero", 0, 5, 6)?));
    t1.push(("rs1_zero", cases::register_group("rs1_zero", 7, 0, 6)?));
    t1.push(("random", cases::random_group(args.seed, args.random_per_kind)?));
    t1.push(("native_kind", cases::register_group("native_kind", 9, 5, 6)?));
    #[cfg(feature = "zicsr-remaining")]
    t1.push(("csr", cases::csr_group()?));
    let (decoded_kinds, direct_kinds) = cases::kind_partition();
    for (group, cs) in &t1 {
        for c in cs {
            record_fresh(
                &ann,
                &mut em,
                &c.name,
                group,
                &c.input,
                None,
                &mut fresh_not_restored,
                &mut group_counts,
                &mut shared_inputs,
            )?;
        }
    }
    let random_n = t1.iter().find(|(g, _)| *g == "random").map_or(0, |(_, c)| c.len());
    checks.push(Check {
        name: "t1_case_generation",
        pass: random_n >= 400,
        detail: json!({
            "decoder_kinds": decoded_kinds.len(),
            "direct_kinds": direct_kinds.iter().map(|k| k.name()).collect::<Vec<_>>(),
            "random_cases": random_n,
            "seed": args.seed,
        }),
    });

    // ---- inline fixture rows ----
    let regs = inlines::registrations();
    for reg in &regs {
        for s in &inlines::SCENARIOS {
            let src = inlines::scenario_source(reg, s);
            record_fresh(
                &ann,
                &mut em,
                &format!("{}::{}", reg.name, s.name),
                "inline_fixture",
                &src,
                Some(reg.name),
                &mut fresh_not_restored,
                &mut group_counts,
                &mut shared_inputs,
            )?;
        }
    }
    checks.push(Check {
        name: "allocator_restored_fresh",
        pass: fresh_not_restored.is_empty(),
        detail: json!({
            "method": "Debug string equals ExpansionAllocator::new() after each successful expansion",
            "not_restored": fresh_not_restored,
        }),
    });

    // ---- shared allocator ----
    let mut shared_alloc = ExpansionAllocator::new();
    let mut shared_not_restored = Vec::new();
    let mut shared_differs = Vec::new();
    let mut shared_errors = 0usize;
    for si in &shared_inputs {
        let before_fresh = allocator_is_fresh(&shared_alloc);
        let result = expand(&si.source, &mut shared_alloc);
        let v = json!({
            "case": format!("{}@shared", si.name),
            "group": si.group,
            "source": source_json(&si.source, si.inline_name),
            "allocator": "shared",
            "result": ann.result_json(&result)?,
        });
        em.emit(&v)?;
        match &result {
            Ok(rows) => {
                if before_fresh && si.fresh.as_ref().ok() != Some(rows) {
                    shared_differs.push(si.name.clone());
                }
                if !allocator_is_fresh(&shared_alloc) {
                    shared_not_restored.push(json!({
                        "case": si.name, "state": allocator_state(&shared_alloc)
                    }));
                    shared_alloc = ExpansionAllocator::new();
                }
            }
            Err(_) => {
                shared_errors += 1;
                if !allocator_is_fresh(&shared_alloc) {
                    shared_not_restored.push(json!({
                        "case": si.name, "after_error": true,
                        "state": allocator_state(&shared_alloc)
                    }));
                    shared_alloc = ExpansionAllocator::new();
                }
            }
        }
    }
    checks.push(Check {
        name: "allocator_restored_shared",
        pass: shared_not_restored.is_empty() && shared_differs.is_empty(),
        detail: json!({
            "sequence_length": shared_inputs.len(),
            "errors": shared_errors,
            "not_restored": shared_not_restored,
            "rows_differ_from_fresh": shared_differs,
        }),
    });
    em.out.flush().map_err(|e| e.to_string())?;

    // ---- inline checks ----
    checks.push(Check {
        name: "inline_inventory",
        pass: regs.len() == 27,
        detail: json!({"registrations": regs.len(), "expected": 27,
                       "names": regs.iter().map(|r| r.name).collect::<Vec<_>>()}),
    });
    let fixture_path = args
        .jolt_dir
        .join("jolt-inlines/fixtures/fixtures/registered_inline_expand_parity_hashes.jsonl");
    let fixture = inlines::parse_fixture(
        &std::fs::read_to_string(&fixture_path).map_err(|e| format!("{fixture_path:?}: {e}"))?,
    )?;
    let fixture_errors = fixture.iter().filter(|c| c.error.is_some()).count();
    let (fx_fail, rd_zero_accept, computed) = inlines::check_fixture(&fixture);
    checks.push(Check {
        name: "inline_fixture_hashes",
        pass: fx_fail.is_empty() && fixture.len() == 108,
        detail: json!({"fixture_lines": fixture.len(), "computed": computed,
                       "fixture_lines_with_error": fixture_errors, "failures": fx_fail}),
    });

    let mut templates: Vec<(&'static str, AllocCase, Vec<TemplateRow>)> = Vec::new();
    let mut template_fail = Vec::new();
    let mut per_inline = serde_json::Map::new();
    let mut templates_json = Vec::new();
    for reg in &regs {
        let accepts_rd_zero = matches!(rd_zero_accept.get(reg.name), Some(Ok(())));
        let mut info = serde_json::Map::new();
        info.insert(
            "rd_zero".into(),
            match rd_zero_accept.get(reg.name) {
                Some(Ok(())) => json!("accepted"),
                Some(Err(e)) => json!({"rejected": e}),
                None => Value::Null,
            },
        );
        let mut tj = serde_json::Map::new();
        for case in [AllocCase::Normal, AllocCase::RdZero] {
            if case == AllocCase::RdZero && !accepts_rd_zero {
                tj.insert(case.name().into(), Value::Null);
                continue;
            }
            match inlines::build_template(reg, case) {
                Ok(t) => {
                    tj.insert(case.name().into(), json!({"rows": inlines::template_json(&t)}));
                    templates.push((reg.name, case, t));
                }
                Err(e) => {
                    template_fail.push(format!("{}::{}: {e}", reg.name, case.name()));
                    tj.insert(case.name().into(), json!({"error": e}));
                }
            }
        }
        templates_json.push(json!({
            "name": reg.name,
            "opcode": reg.opcode, "funct3": reg.funct3, "funct7": reg.funct7,
            "extension": format!("{:?}", reg.extension),
            "lean_file": format!("JoltBytecode/Inlines/Generated/{}.lean", lean::upper_camel(reg.name)),
            "lean_def": format!("JoltISA.Inlines.Generated.{}RowsAuto", lean::lower_camel(reg.name)),
            "cases": Value::Object(tj),
        }));
        per_inline.insert(reg.name.into(), Value::Object(info));
    }
    checks.push(Check {
        name: "inline_templates",
        pass: template_fail.is_empty(),
        detail: json!({"templates": templates.len(), "failures": template_fail}),
    });
    std::fs::write(
        args.out.join("inline_templates.json"),
        serde_json::to_string_pretty(&json!({
            "jolt_commit": commit,
            "triples": {"A": inlines::TRIPLE_A, "B": inlines::TRIPLE_B},
            "address": inlines::TEMPLATE_ADDRESS,
            "inlines": templates_json,
        }))
        .map_err(|e| e.to_string())?,
    )
    .map_err(|e| e.to_string())?;

    // Uniformity.
    let mut nonuniform = Vec::new();
    let mut uniformity = serde_json::Map::new();
    let mut total_triples = 0usize;
    let (_, uni_secs) = inlines::timed(|| {
        if args.skip_uniformity {
            return;
        }
        for (name, case, t) in &templates {
            let reg = regs.iter().find(|r| r.name == *name).expect("registration");
            let ((n, bad), secs) = inlines::timed(|| inlines::check_uniform(reg, *case, t));
            total_triples += n;
            uniformity.insert(
                format!("{name}::{}", case.name()),
                json!({"triples": n, "rows": t.len(), "seconds": secs, "first_difference": bad}),
            );
            if let Some(b) = bad {
                nonuniform.push(json!({"inline": name, "case": case.name(), "first_difference": b}));
            }
        }
    });
    checks.push(Check {
        name: "operand_uniformity",
        pass: !args.skip_uniformity && nonuniform.is_empty(),
        detail: json!({
            "skipped": args.skip_uniformity,
            "threads": rayon::current_num_threads(),
            "total_triples": total_triples,
            "seconds": uni_secs,
            "nonuniform": nonuniform,
            "per_template": Value::Object(uniformity),
        }),
    });

    // Write-before-read and write sets.
    let mut wbr_fail = Vec::new();
    let mut kinds_seen: BTreeMap<&'static str, Value> = BTreeMap::new();
    for (name, case, t) in &templates {
        let rows: Vec<JoltInstructionRow> =
            t.iter().map(|r| r.instantiate(inlines::TRIPLE_A)).collect();
        let w = inlines::write_before_read(&rows);
        let in_scope = inlines::IN_SCOPE.contains(name);
        let pool_bad = w["pool_reads_before_write"]
            .as_array()
            .map_or(0, |a| a.len());
        if in_scope && pool_bad > 0 {
            wbr_fail.push(format!("{name}::{}: {pool_bad} pool reads before write", case.name()));
        }
        for r in &rows {
            let k = r.instruction_kind.name();
            kinds_seen.entry(k).or_insert_with(|| {
                let jr = ann.row_json(r).unwrap_or(Value::Null);
                json!({
                    "rd": r.operands.rd.is_some(),
                    "rs1": r.operands.rs1.is_some(),
                    "rs2": r.operands.rs2.is_some(),
                    "circuit_flags": jr["circuit_flags"],
                    "instruction_flags": jr["instruction_flags"],
                })
            });
        }
        if let Some(Value::Object(info)) = per_inline.get_mut(*name) {
            info.insert(
                format!("{}_write_before_read", case.name()),
                json!({"in_scope": in_scope, "result": w}),
            );
            info.insert(format!("{}_writes", case.name()), inlines::write_sets(t));
            info.insert(format!("{}_rows", case.name()), json!(t.len()));
        }
    }
    checks.push(Check {
        name: "write_before_read_in_scope",
        pass: wbr_fail.is_empty(),
        detail: json!({"in_scope": inlines::IN_SCOPE, "failures": wbr_fail,
                       "row_kind_operands": kinds_seen}),
    });

    // Lean generation.
    if let Some(root) = &args.lean_root {
        let regenerate = "scripts/expansion-parity/run.sh";
        let mut files = Vec::new();
        let mut lean_fail = Vec::new();
        for reg in &regs {
            let cs: Vec<lean::CaseInput> = templates
                .iter()
                .filter(|(n, _, _)| *n == reg.name)
                .map(|(_, c, t)| lean::CaseInput {
                    case: *c,
                    template: t,
                })
                .collect();
            if cs.is_empty() {
                lean_fail.push(format!("{}: no template", reg.name));
                continue;
            }
            match lean::render_inline(reg.name, &cs, &commit, regenerate, args.lean_chunk) {
                Ok(r) => files.push(r),
                Err(e) => lean_fail.push(e),
            }
        }
        if lean_fail.is_empty() {
            lean::write_all(root, &files, &commit, regenerate)?;
        }
        checks.push(Check {
            name: "lean_generation",
            pass: lean_fail.is_empty() && files.len() == regs.len(),
            detail: json!({
                "files": files.iter().map(|f| json!({"module": f.module, "rows": f.rows})).collect::<Vec<_>>(),
                "chunk": args.lean_chunk,
                "failures": lean_fail,
            }),
        });
    }

    // ---- summary ----
    let all_pass = checks.iter().all(|c| c.pass);
    let summary = json!({
        "jolt_dir": args.jolt_dir,
        "jolt_commit": commit,
        "all_pass": all_pass,
        "rows_jsonl_lines": em.lines,
        "groups": group_counts.iter().map(|(g, (n, e))| (g.to_string(), json!({"cases": n, "errors": e}))).collect::<serde_json::Map<_, _>>(),
        "checks": checks.iter().map(|c| json!({"name": c.name, "pass": c.pass, "detail": c.detail})).collect::<Vec<_>>(),
        "inlines": Value::Object(per_inline),
    });
    std::fs::write(
        args.out.join("summary.json"),
        serde_json::to_string_pretty(&summary).map_err(|e| e.to_string())?,
    )
    .map_err(|e| e.to_string())?;

    println!("expansion-parity at a16z/jolt {commit}");
    println!("rows.jsonl: {} lines", em.lines);
    for (g, (n, e)) in &group_counts {
        println!("  group {g:15} {n:5} cases, {e:4} expansion errors");
    }
    for c in &checks {
        println!("[{}] {}", if c.pass { "PASS" } else { "FAIL" }, c.name);
        let brief = match c.name {
            "operand_uniformity" => format!(
                "{} triples in {:.1} s on {} threads; nonuniform: {}",
                c.detail["total_triples"],
                c.detail["seconds"].as_f64().unwrap_or(0.0),
                c.detail["threads"],
                c.detail["nonuniform"]
            ),
            "write_before_read_in_scope" => format!("failures: {}", c.detail["failures"]),
            "inline_fixture_hashes" => format!(
                "{} lines ({} with error), failures: {}",
                c.detail["fixture_lines"], c.detail["fixture_lines_with_error"], c.detail["failures"]
            ),
            "golden_fixture_hashes" => format!(
                "{} cases, mismatches: {}",
                c.detail["cases"], c.detail["mismatches"]
            ),
            _ => String::new(),
        };
        if !brief.is_empty() {
            println!("       {brief}");
        }
    }
    let rd_zero_rejected: Vec<&String> = rd_zero_accept
        .iter()
        .filter(|(_, r)| r.is_err())
        .map(|(n, _)| n)
        .collect();
    println!(
        "rd = x0 rejected by Jolt for {} inlines: {:?}",
        rd_zero_rejected.len(),
        rd_zero_rejected
    );
    println!("summary: {}", args.out.join("summary.json").display());
    println!("{}", if all_pass { "ALL CHECKS PASS" } else { "SOME CHECKS FAILED" });
    Ok(all_pass)
}

#[allow(clippy::too_many_arguments)]
fn record_fresh<W: Write>(
    ann: &Annotator,
    em: &mut Emitter<W>,
    name: &str,
    group: &'static str,
    source: &SourceInstruction,
    inline_name: Option<&'static str>,
    not_restored: &mut Vec<String>,
    counts: &mut BTreeMap<&'static str, (usize, usize)>,
    shared: &mut Vec<SharedInput>,
) -> Result<(), String> {
    let mut alloc = ExpansionAllocator::new();
    let result: Result<Vec<JoltInstructionRow>, ExpansionError> = expand(source, &mut alloc);
    let entry = counts.entry(group).or_insert((0, 0));
    entry.0 += 1;
    if result.is_err() {
        entry.1 += 1;
    } else if !allocator_is_fresh(&alloc) {
        not_restored.push(format!("{group}/{name}: {}", allocator_state(&alloc)));
    }
    em.emit(&json!({
        "case": name,
        "group": group,
        "source": source_json(source, inline_name),
        "allocator": "fresh",
        "result": ann.result_json(&result)?,
    }))?;
    shared.push(SharedInput {
        name: name.to_string(),
        group,
        source: source.clone(),
        inline_name,
        fresh: result.map_err(|e| format!("{e:?}")),
    });
    Ok(())
}

fn main() {
    match run() {
        Ok(true) => {}
        Ok(false) => std::process::exit(1),
        Err(e) => {
            eprintln!("expansion-parity: {e}");
            std::process::exit(2);
        }
    }
}
