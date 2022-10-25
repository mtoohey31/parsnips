ASM_DEPS=parsnips-asm/Cargo.toml Cargo.lock parsnips-asm/src/**
CLI_DEPS=parsnips-cli/Cargo.toml Cargo.lock parsnips-cli/src/**
EMU_DEPS=parsnips-emu/Cargo.toml Cargo.lock parsnips-emu/src/**
UTIL_DEPS=parsnips-util/Cargo.toml Cargo.lock parsnips-util/src/**
PARSER_DEPS=parsnips-parser/Cargo.toml Cargo.lock parsnips-parser/src/**

RUSTFLAGS:=--quiet

.PHONY: all
all: check-fmt test check-clippy build

.PHONY: ci
ci: check-fmt test build

.PHONY: check-fmt
check-fmt:
	rustfmt $(RUSTFLAGS) --check $$(find . \( \( -name target -o -name target-cov \) -prune -false \) -o -name '*.rs')

.PHONY: fmt
fmt:
	rustfmt $(RUSTFLAGS) $$(find . \( \( -name target -o -name target-cov \) -prune -false \) -o -name '*.rs')

.PHONY: check-clippy
check-clippy:
	cargo clippy $(RUSTFLAGS) --workspace --all-targets

.PHONY: test
test: test-parser test-asm test-emu test-web

.PHONY: test-parser
test-parser:
	cargo test $(RUSTFLAGS) -p parsnips-parser

.PHONY: test-asm
test-asm:
	cargo test $(RUSTFLAGS) -p parsnips-asm

.PHONY: test-emu
test-emu:
	cargo test $(RUSTFLAGS) -p parsnips-emu
# TODO: figure out how to make this quieter without it blowing up
	wasm-pack test --node --mode no-install parsnips-emu

.PHONY: test-web
test-web: parsnips-web/node_modules parsnips-web/node_modules/parsnips-emu
	cd parsnips-web && pnpm run check

.PHONY: build
build: parsnips-web/dist target/release/par

target/release/par: $(CLI_DEPS) $(EMU_DEPS) $(UTIL_DEPS) $(PARSER_DEPS)
	cargo build $(RUSTFLAGS) -p parsnips-cli --release

parsnips-emu/pkg: $(EMU_DEPS) $(UTIL_DEPS) $(PARSER_DEPS)
	cd parsnips-emu && wasm-pack build $(RUSTFLAGS) --target web --mode no-install
	rm -rf parsnips-web/node_modules/parsnips-emu

parsnips-web/node_modules/parsnips-emu: parsnips-emu/pkg
	mkdir -p parsnips-web/node_modules
	cp -r parsnips-emu/pkg parsnips-web/node_modules/parsnips-emu

parsnips-web/node_modules: parsnips-web/package.json parsnips-web/pnpm-lock.yaml
	cd parsnips-web && pnpm install --quiet

parsnips-web/dist: parsnips-emu/pkg parsnips-web/node_modules parsnips-web/node_modules/parsnips-emu parsnips-web/*.* parsnips-web/src/**
	cd parsnips-web && pnpm run build --logLevel warn

.PHONY: cov-parser
cov-parser: $(PARSER_DEPS)
	export LLVM_PROFILE_DIR="$$(mktemp -d)" && \
		LLVM_PROFILE_FILE="$$LLVM_PROFILE_DIR/%p-%m.profraw" RUSTFLAGS="-C instrument-coverage" cargo test $(RUSTFLAGS) --target-dir target-cov -p parsnips-parser && \
		grcov "$$LLVM_PROFILE_DIR/"* --binary-path target-cov/debug/deps -s . -t html --branch --ignore-not-existing -o cov && \
		rm -rf "$$LLVM_PROFILE_DIR"

.PHONY: cov-asm
cov-asm: $(ASM_DEPS) $(UTIL_DEPS) $(PARSER_DEPS)
	export LLVM_PROFILE_DIR="$$(mktemp -d)" && \
		LLVM_PROFILE_FILE="$$LLVM_PROFILE_DIR/%p-%m.profraw" RUSTFLAGS="-C instrument-coverage" cargo test $(RUSTFLAGS) --target-dir target-cov -p parsnips-asm && \
		grcov "$$LLVM_PROFILE_DIR/"* --binary-path target-cov/debug/deps -s . -t html --branch --ignore-not-existing -o cov && \
		rm -rf "$$LLVM_PROFILE_DIR"

.PHONY: cov-emu
cov-emu: $(EMU_DEPS) $(UTIL_DEPS) $(PARSER_DEPS)
	export LLVM_PROFILE_DIR="$$(mktemp -d)" && \
		LLVM_PROFILE_FILE="$$LLVM_PROFILE_DIR/%p-%m.profraw" RUSTFLAGS="-C instrument-coverage" cargo test $(RUSTFLAGS) --target-dir target-cov -p parsnips-emu && \
		grcov "$$LLVM_PROFILE_DIR/"* --binary-path target-cov/debug/deps -s . -t html --branch --ignore-not-existing -o cov && \
		rm -rf "$$LLVM_PROFILE_DIR"

.PHONY: clean
clean:
	rm -rf cov target target-cov parsnips-emu/pkg parsnips-web/{dist,node_modules}
