# Monkey

[![Rust](https://github.com/DerekStride/writing-an-interpreter-in-rust/actions/workflows/rust.yml/badge.svg)](https://github.com/DerekStride/writing-an-interpreter-in-rust/actions/workflows/rust.yml)

I'm following along the book ["Writing An Interpreter In Go" by Thorsten Ball](https://interpreterbook.com/) and
["Writing a Compiler in Go" by Thorsten Ball](https://compilerbook.com/) implementing a toy language call Monkey.

I am using Rust instead of Go to help learn the language.

## Results

```
➜ monkey cargo bench

running 5 tests
test tests::bench_compile ... bench:      22,297 ns/iter (+/- 1,732)
test tests::bench_eval    ... bench:  49,248,606 ns/iter (+/- 3,758,017)
test tests::bench_parse   ... bench:      24,604 ns/iter (+/- 1,191)
test tests::bench_rust    ... bench:           0 ns/iter (+/- 0)
test tests::bench_vm      ... bench:   1,466,072 ns/iter (+/- 97,031)

test result: ok. 0 passed; 0 failed; 0 ignored; 5 measured; 0 filtered out; finished in 17.81s

➜ monkey cargo run --bin=bench
    Finished dev [unoptimized + debuginfo] target(s) in 0.01s
     Running `target/debug/bench`
Running:
fibonacci(28);

Rust
Result: 317811
Duration: 0.3984s

Vm
Result: 317811
Duration: 7.276345s

Eval
Result: 317811
Duration: 111.487040s

Vm is 15.32x faster than Eval
```

Use the following commands to generate flamegraphs with `cargo flamegraph`

```
cargo flamegraph --dev --bin=flamegraph --root -o tmp/flamegraph-vm.svg -- --engine=vm
cargo flamegraph --dev --bin=flamegraph --root -o tmp/flamegraph-eval.svg -- --engine=eval
```
### Flamegraph for the Vm engine

<img width="1196" alt="Screen Shot 2022-01-08 at 3 04 52 PM" src="https://user-images.githubusercontent.com/6456191/148658249-64810578-aea0-49c9-b1c3-2349364d3ab4.png">

