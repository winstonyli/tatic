//! Transformer over rule lines `lhs -> rhs` (search note sections 79-81).
//!
//! `rulelm train DATA HELDOUT STEPS CKPT`: trains on DATA, logs the loss on a 5% split of DATA (a monitor only: renamed
//! and commuted copies of a rule are in both parts) and on HELDOUT (variants of rules kept out of training).
//! `rulelm sample CKPT N TEMP SEED [PREFIX]`: prints N sampled rule lines, each starting with PREFIX.
//! Env (train and sample must agree): `RULELM_WORDS=1` (one token per operator or leaf, rules in the prefix notation
//! of `scripts/rule_notation.py`; default one token per character), `RULELM_D` (width, 128), `RULELM_LAYERS` (4),
//! `RULELM_DROPOUT` (0.1). `RULELM_EVERY` (200) sets the evaluation interval; `RULELM_SAVE_BEST=1` keeps the checkpoint
//! with the lowest held-out loss instead of the last.
use burn::module::Module;
use burn::nn::attention::generate_autoregressive_mask;
use burn::nn::loss::CrossEntropyLossConfig;
use burn::nn::transformer::{TransformerEncoder, TransformerEncoderConfig, TransformerEncoderInput};
use burn::nn::{Embedding, EmbeddingConfig, Linear, LinearConfig};
use burn::optim::{AdamConfig, GradientsParams};
use burn::tensor::{Device, DeviceKind, Int, Tensor, TensorData};
use std::io::Write;
use std::time::Instant;

const PAD: usize = 0;

fn env_usize(k: &str, d: usize) -> usize {
    std::env::var(k).ok().and_then(|v| v.parse().ok()).unwrap_or(d)
}

fn words() -> bool {
    std::env::var("RULELM_WORDS").is_ok()
}

/// Token strings; id 0 is padding, token `i` has id `i + 1`. "\n" marks the start and end of a line.
fn vocab() -> &'static Vec<String> {
    static V: std::sync::OnceLock<Vec<String>> = std::sync::OnceLock::new();
    V.get_or_init(|| {
        if words() {
            ["\n", "add", "and", "or", "xor", "sub", "shl1", "x", "y", "z", "0", "-1", ">"].map(String::from).to_vec()
        } else {
            "\n -,()>0123456789abcdefghijklmnopqrstuvwxyz".chars().map(String::from).collect()
        }
    })
}

/// Tokens per line: the start marker, the rule, the end marker, padding.
fn l() -> usize {
    if words() { 24 } else { 50 }
}

fn tokens(s: &str) -> Vec<String> {
    if words() { s.split_whitespace().map(String::from).collect() } else { s.chars().map(String::from).collect() }
}

fn enc(t: &str) -> i32 {
    1 + vocab().iter().position(|v| v == t).unwrap_or_else(|| panic!("token outside the vocabulary: {t:?}")) as i32
}

fn encode(line: &str) -> Vec<i32> {
    let mut v: Vec<i32> = std::iter::once("\n".to_string()).chain(tokens(line)).chain(std::iter::once("\n".to_string())).map(|t| enc(&t)).collect();
    assert!(v.len() <= l(), "line too long: {line}");
    v.resize(l(), PAD as i32);
    v
}

#[derive(Module, Debug)]
struct Lm {
    tok: Embedding,
    pos: Embedding,
    enc: TransformerEncoder,
    out: Linear,
}

impl Lm {
    fn new(device: &Device) -> Self {
        let (d, v) = (env_usize("RULELM_D", 128), vocab().len() + 1);
        let dropout = std::env::var("RULELM_DROPOUT").ok().and_then(|x| x.parse().ok()).unwrap_or(0.1);
        Lm {
            tok: EmbeddingConfig::new(v, d).init(device),
            pos: EmbeddingConfig::new(l(), d).init(device),
            enc: TransformerEncoderConfig::new(d, 4 * d, 4, env_usize("RULELM_LAYERS", 4)).with_dropout(dropout).with_norm_first(true).init(device),
            out: LinearConfig::new(d, v).init(device),
        }
    }
    /// Logits `[batch, len, vocab]` for tokens `[batch, len]`, each position seeing only the earlier ones.
    fn forward(&self, tokens: Tensor<2, Int>) -> Tensor<3> {
        let [b, len] = tokens.dims();
        let device = tokens.device();
        let pos = Tensor::<1, Int>::arange(0..len as i64, &device).unsqueeze::<2>().expand([b, len]);
        let x = self.tok.forward(tokens) + self.pos.forward(pos);
        let mask = generate_autoregressive_mask(b, len, &device);
        self.out.forward(self.enc.forward(TransformerEncoderInput::new(x).mask_attn(mask)))
    }
    /// Mean cross-entropy of predicting each next token, ignoring padding.
    fn loss(&self, tokens: Tensor<2, Int>) -> Tensor<1> {
        let [b, len] = tokens.dims();
        let logits = self.forward(tokens.clone().slice([0..b, 0..len - 1]));
        let targets = tokens.slice([0..b, 1..len]);
        let v = vocab().len() + 1;
        CrossEntropyLossConfig::new().with_pad_tokens(Some(vec![PAD])).init(&logits.device()).forward(logits.reshape([b * (len - 1), v]), targets.reshape([b * (len - 1)]))
    }
}

fn batch(rows: &[&Vec<i32>], device: &Device) -> Tensor<2, Int> {
    let flat: Vec<i32> = rows.iter().flat_map(|r| r.iter().copied()).collect();
    Tensor::from_data(TensorData::new(flat, [rows.len(), l()]), device)
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn unit(&mut self) -> f32 {
        (self.next() >> 40) as f32 / (1u64 << 24) as f32
    }
}

fn lines(path: &str) -> Vec<Vec<i32>> {
    std::fs::read_to_string(path).unwrap().lines().filter(|x| x.contains(" -> ") || x.contains(" > ")).map(encode).collect()
}

fn mean_loss(model: &Lm, rows: &[Vec<i32>], device: &Device) -> f32 {
    let (mut sum, mut n) = (0.0, 0.0);
    for chunk in rows.chunks(128) {
        let refs: Vec<&Vec<i32>> = chunk.iter().collect();
        sum += model.loss(batch(&refs, device)).into_scalar::<f32>() * chunk.len() as f32;
        n += chunk.len() as f32;
    }
    sum / n
}

fn train(args: &[String]) {
    let device_plain = Device::vulkan(DeviceKind::DiscreteGpu(0));
    let device = device_plain.clone().autodiff();
    println!("device: {device:?}");
    let all = lines(&args[0]);
    let heldout = lines(&args[1]);
    let steps: usize = args[2].parse().unwrap();
    let (every, best_only) = (env_usize("RULELM_EVERY", 200), std::env::var("RULELM_SAVE_BEST").is_ok());
    let mut rng = Rng(0x9E3779B97F4A7C15);
    let (mut data, mut val) = (vec![], vec![]);
    for r in all {
        if rng.next() % 20 == 0 {
            val.push(r)
        } else {
            data.push(r)
        }
    }
    println!("train {} rows, monitor {}, held-out {}, {steps} steps", data.len(), val.len(), heldout.len());
    let mut model = Lm::new(&device);
    let mut opt = AdamConfig::new().init();
    let bsz = 128;
    let (t0, mut best) = (Instant::now(), f32::MAX);
    for step in 1..=steps {
        let rows: Vec<&Vec<i32>> = (0..bsz).map(|_| &data[rng.next() as usize % data.len()]).collect();
        let lr = 1e-3 * (step as f64 / 200.0).min(1.0) * (1.0 - step as f64 / steps as f64).max(0.05);
        let loss = model.loss(batch(&rows, &device));
        let l: f32 = loss.clone().into_scalar();
        let grads = GradientsParams::from_grads(loss.backward(), &model);
        model = opt.step(lr, model, grads);
        if step % every == 0 || step == steps {
            let valid = model.valid();
            let held = mean_loss(&valid, &heldout, &device_plain);
            println!("step {step}: train {l:.3}, monitor {:.3}, held-out {held:.3}, {:.0}s", mean_loss(&valid, &val, &device_plain), t0.elapsed().as_secs_f32());
            std::io::stdout().flush().unwrap();
            if !best_only || held < best {
                best = held;
                model.clone().save_file(&args[3]).unwrap();
            }
        }
    }
}

fn sample(args: &[String]) {
    let device = Device::vulkan(DeviceKind::DiscreteGpu(0));
    let n: usize = args[1].parse().unwrap();
    let temp: f32 = args[2].parse().unwrap();
    let mut rng = Rng(args[3].parse::<u64>().unwrap() * 2 + 1);
    let prefix = args.get(4).cloned().unwrap_or_default();
    let model = Lm::new(&device).load_file(&args[0]);
    let nl = "\n".to_string();
    let start: Vec<i32> = std::iter::once(nl.clone()).chain(tokens(&prefix)).map(|t| enc(&t)).collect();
    let mut rows: Vec<Vec<i32>> = vec![start.clone(); n];
    let v = vocab().len() + 1;
    for t in start.len()..l() {
        let padded: Vec<Vec<i32>> = rows.iter().map(|r| r.iter().copied().chain(std::iter::repeat(PAD as i32)).take(l()).collect()).collect();
        let refs: Vec<&Vec<i32>> = padded.iter().collect();
        let logits = model.forward(batch(&refs, &device)).slice([0..n, t - 1..t, 0..v]).into_data().to_vec::<f32>().unwrap();
        for (i, row) in rows.iter_mut().enumerate() {
            if row.len() > 1 && row.last() == Some(&enc(&nl)) {
                continue;
            }
            let lg = &logits[i * v..(i + 1) * v];
            let mx = lg[1..].iter().cloned().fold(f32::MIN, f32::max);
            let w: Vec<f32> = lg.iter().enumerate().map(|(k, x)| if k == PAD { 0.0 } else { ((x - mx) / temp).exp() }).collect();
            let mut u = rng.unit() * w.iter().sum::<f32>();
            let mut pick = v - 1;
            for (k, x) in w.iter().enumerate() {
                if u < *x {
                    pick = k;
                    break;
                }
                u -= x;
            }
            row.push(pick as i32);
        }
    }
    for r in rows {
        let toks: Vec<&str> = r.iter().skip(1).take_while(|&&c| c != enc(&nl)).map(|&c| vocab()[c as usize - 1].as_str()).collect();
        println!("{}", toks.join(if words() { " " } else { "" }));
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    match args.get(1).map(String::as_str) {
        Some("train") => train(&args[2..]),
        Some("sample") => sample(&args[2..]),
        _ => eprintln!("usage: rulelm train DATA HELDOUT STEPS CKPT | rulelm sample CKPT N TEMP SEED [PREFIX]"),
    }
}
