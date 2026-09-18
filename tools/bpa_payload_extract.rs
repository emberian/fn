//! Bounded opaque-BP bundle payload extractor using the pinned upstream bp7 crate.
//! It implements no BP codec; the Bundle parser and canonical payload lookup are
//! copied directly from dtn7-rs's existing `dtnrecv` binary.
use bp7::*;
use std::convert::TryFrom;
use std::env;
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::path::PathBuf;
use std::process;

fn parse_size(text: &str, label: &str) -> usize {
    text.parse::<usize>().unwrap_or_else(|_| { eprintln!("invalid {label}"); process::exit(2) })
}

fn read_bounded(path: &PathBuf, limit: usize) -> Vec<u8> {
    let size = fs::metadata(path).unwrap_or_else(|_| { eprintln!("cannot stat input"); process::exit(2) }).len();
    if size > limit as u64 { eprintln!("input exceeds cap"); process::exit(2); }
    let file = File::open(path).unwrap_or_else(|_| { eprintln!("cannot open input"); process::exit(2) });
    let mut bytes = Vec::with_capacity(size as usize);
    file.take(limit as u64 + 1).read_to_end(&mut bytes).unwrap_or_else(|_| { eprintln!("cannot read input"); process::exit(2) });
    if bytes.len() > limit { eprintln!("input exceeds cap"); process::exit(2); }
    bytes
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 7 || args[1] != "--input" || args[3] != "--output" || args[5] != "--max-payload" {
        eprintln!("usage: fn-bpa-payload-extract --input BUNDLE --output ADU --max-payload N");
        process::exit(2);
    }
    let input = PathBuf::from(&args[2]);
    let output = PathBuf::from(&args[4]);
    let max_payload = parse_size(&args[6], "max payload");
    // The caller bounds the BP bundle itself before this helper is executed;
    // include bounded framing headroom rather than inventing a BP limit.
    let bundle = read_bounded(&input, max_payload.saturating_add(64 * 1024));
    let parsed: Bundle = Bundle::try_from(bundle).unwrap_or_else(|_| { eprintln!("invalid pinned bp7 bundle"); process::exit(2) });
    let payload = match parsed.extension_block_by_type(bp7::canonical::PAYLOAD_BLOCK) {
        Some(block) => match block.data() {
            bp7::canonical::CanonicalData::Data(data) => data,
            _ => { eprintln!("payload block is not byte data"); process::exit(2) }
        },
        None => { eprintln!("payload block missing"); process::exit(2) }
    };
    if payload.len() > max_payload { eprintln!("payload exceeds cap"); process::exit(2); }
    let mut destination = OpenOptions::new().write(true).create_new(true).open(&output)
        .unwrap_or_else(|_| { eprintln!("cannot create output"); process::exit(2) });
    destination.write_all(payload).unwrap_or_else(|_| { eprintln!("cannot write output"); process::exit(2) });
    destination.sync_all().unwrap_or_else(|_| { eprintln!("cannot fsync output"); process::exit(2) });
}
