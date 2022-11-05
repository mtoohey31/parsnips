{
  description = "parsnips";

  inputs = {
    nixpkgs.url = "nixpkgs/nixpkgs-unstable";
    utils.url = "github:numtide/flake-utils";
    naersk = {
      url = "github:nix-community/naersk";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs = {
        nixpkgs.follows = "nixpkgs";
        flake-utils.follows = "utils";
      };
    };
  };

  outputs = { self, nixpkgs, utils, naersk, rust-overlay }: {
    overlays = rec {
      expects-naersk = final: prev: {
        parsnips = final.naersk.buildPackage {
          pname = "parsnips";
          root = ./.;
        };
      };

      default = final: prev: {
        inherit (prev.appendOverlays [
          naersk.overlay
          expects-naersk
        ]) parsnips;
      };
    };
  } // utils.lib.eachDefaultSystem (system: with import nixpkgs
    {
      overlays = [ self.overlays.default (import rust-overlay) ];
      inherit system;
    }; {
    packages.default = parsnips;

    devShells =
      let
        rust = rust-bin.stable.latest.minimal.override {
          extensions = [ "clippy" "llvm-tools-preview" "rustfmt" "rust-src" ];
          targets = [ "s390x-unknown-linux-gnu" "wasm32-unknown-unknown" ];
        };
        # adapted from: https://github.com/oxalica/rust-overlay/blob/master/docs/cross_compilation.md
        # using crossSystem in the initial nixpkgs import above seems to break
        # everything even if I make sure to use buildPackages everywhere...
        s390x-cc = (import nixpkgs {
          crossSystem = "s390x-linux";
          inherit system;
        }).stdenv.cc;
      in
      rec {
        ci = mkShell {
          depsBuildBuild = [
            rust
            s390x-cc
          ];

          nativeBuildInputs = [
            nodejs
            wasm-bindgen-cli
            wasm-pack
          ] ++ (with nodePackages; [
            pnpm
            prettier
          ]);

          CARGO_TARGET_S390X_UNKNOWN_LINUX_GNU_LINKER = "${s390x-cc.targetPrefix}cc";
          CARGO_TARGET_S390X_UNKNOWN_LINUX_GNU_RUNNER = "${qemu}/bin/qemu-s390x";
        };

        default = ci.overrideAttrs (oldAttrs: {
          nativeBuildInputs = oldAttrs.nativeBuildInputs ++ [
            cargo-watch
            rust-analyzer
            binaryen
            evcxr
            grcov
          ] ++ (with nodePackages; [
            svelte-language-server
            nodePackages."@tailwindcss/language-server"
            typescript
            typescript-language-server
          ]);

          # needed for rust-analyzer
          RUST_SRC_PATH = "${rust}/lib/rustlib/src/rust/library/alloc";
        });
      };
  });
}
