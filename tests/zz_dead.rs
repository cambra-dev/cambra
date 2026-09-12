use std::collections::{HashMap, HashSet};
use std::path::Path;
use cambra::ccl::channels::ChannelFile;
use cambra::embed::Host;
use cambra::interpreter::Value;
const SCALE: i64 = 100_000_000;
fn ticker_row(field: &str, ticker: &str, value: i64) -> Value {
    Value::Record([("ticker".to_string(), Value::String(ticker.into())),
        (field.to_string(), Value::Int(value))].into_iter().collect())
}
#[test]
fn probe_dead() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs/asset_cart");
    let program = Path::new(dir).join("v0.cambra");
    let code = std::fs::read_to_string(&program).unwrap();
    let declared = ChannelFile::beside(&program).unwrap().unwrap();
    let mut host = Host::compile("v0.cambra", &code, &declared.channels).unwrap();

    let snap: serde_json::Value = serde_json::from_str(host.snapshot()).unwrap();
    let pane = snap["panes"].as_array().unwrap().iter()
        .find(|p| p["id"] == "post-conversion").unwrap();
    let mut kind_of: HashMap<u64, String> = HashMap::new();
    for n in pane["nodes"].as_array().unwrap() {
        kind_of.insert(n["nodeId"].as_u64().unwrap(), n["label"].as_str().unwrap_or("?").to_string());
    }

    let mut seen: HashSet<u64> = HashSet::new();
    let harvest = |h: &Host, seen: &mut HashSet<u64>| {
        let f: serde_json::Value = serde_json::from_str(&h.frame(false)).unwrap();
        for n in f["nodes"].as_array().unwrap() { seen.insert(n["nodeId"].as_u64().unwrap()); }
        for s in f["sources"].as_array().unwrap() {
            if let Some(id) = s["nodeId"].as_u64() { seen.insert(id); }
        }
    };
    let push = |h: &mut Host, s: &str, r: Value, seen: &mut HashSet<u64>| {
        h.push(s, [r]).unwrap();
        for _ in 0..8 { let t = h.tick(); harvest(h, seen); if !t.outputs.is_empty() { break; } }
    };
    push(&mut host, "cart_changes", ticker_row("qty", "BTC-USD", 2), &mut seen);
    push(&mut host, "cart_changes", ticker_row("qty", "ETH-USD", 5), &mut seen);
    push(&mut host, "cart_changes", ticker_row("qty", "SOL-USD", 7), &mut seen);
    for (i, t) in ["BTC-USD","ETH-USD","SOL-USD","DOGE-USD","XRP-USD","BTC-USD"].iter().enumerate() {
        push(&mut host, "price_updates", ticker_row("price", t, (80_000 + i as i64) * SCALE), &mut seen);
        push(&mut host, "view_requests", Value::Bool(true), &mut seen);
    }

    let mut never: HashMap<String, usize> = HashMap::new();
    let mut never_ids: Vec<u64> = Vec::new();
    for (id, kind) in &kind_of {
        if !seen.contains(id) { *never.entry(kind.clone()).or_default() += 1; never_ids.push(*id); }
    }
    let mut counts: Vec<(&String, &usize)> = never.iter().collect();
    counts.sort_by(|a, b| b.1.cmp(a.1));
    println!("PANE NODES: {}", kind_of.len());
    println!("EVER IN A FRAME: {}", kind_of.keys().filter(|k| seen.contains(k)).count());
    println!("NEVER: {}", never_ids.len());
    for (k, c) in counts { println!("  {c:>3}  {k}"); }
    never_ids.sort();
    println!("IDS: {:?}", &never_ids[..never_ids.len().min(40)]);
}
