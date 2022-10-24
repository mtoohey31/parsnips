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
    { overlays = [ self.overlays.default (import rust-overlay) ]; inherit system; }; {
    packages.default = parsnips;

    devShells =
      let
        rust = rust-bin.stable.latest.default.override {
          extensions = [ "llvm-tools-preview" "rust-src" ];
          targets = [ "wasm32-unknown-unknown" ];
        };
      in
      rec {
        ci =
          mkShell {
            packages = [
              rust
              nodejs
              wasm-bindgen-cli
              wasm-pack
            ] ++ (with nodePackages; [
              pnpm
              prettier
            ]);
          };

        default = mkShell
          {
            packages = ci.nativeBuildInputs ++ [
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
            shellHook = ''
              export RUST_SRC_PATH="${rust}/lib/rustlib/src/rust/library/alloc"
            '';
          };
      };
  });
}
